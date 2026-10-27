module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3EZ
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3KUniq
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3dDual

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3E

open GoldAmL3

open scoped commutatorElement

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

omit [Finite D] in
theorem isElemAbelian_closure {S : Set D} (hcomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a)
    (hsq : ∀ a ∈ S, a * a = 1) : IsElemAbelian 2 (Subgroup.closure S) := by
  have h1 : ∀ a ∈ Subgroup.closure S, ∀ b ∈ S, a * b = b * a := by
    intro a ha b hb
    have : Subgroup.closure S ≤ Subgroup.centralizer ({b} : Set D) := by
      rw [Subgroup.closure_le]
      intro y hy
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hcomm _ hb _ hy
    exact ((Subgroup.mem_centralizer_iff.mp (this ha) b (Set.mem_singleton b))).symm
  have h2 : ∀ a ∈ Subgroup.closure S, ∀ b ∈ Subgroup.closure S, a * b = b * a := by
    intro a ha b hb
    have : Subgroup.closure S ≤ Subgroup.centralizer ({a} : Set D) := by
      rw [Subgroup.closure_le]
      intro y hy
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact h1 _ ha y hy
    exact ((Subgroup.mem_centralizer_iff.mp (this hb) a (Set.mem_singleton a)))
  refine ⟨⟨⟨fun a b => Subtype.ext (h2 a.1 a.2 b.1 b.2)⟩⟩, fun x hx => ?_⟩
  rw [pow_two]
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact hsq y hy
  | one => simp
  | mul y y' hy hy' ih ih' =>
    calc y * y' * (y * y') = y * (y' * y) * y' := by group
      _ = y * (y * y') * y' := by rw [h2 y' hy' y hy]
      _ = (y * y) * (y' * y') := by group
      _ = 1 := by rw [ih, ih', one_mul]
  | inv y hy ih =>
    calc y⁻¹ * y⁻¹ = (y * y)⁻¹ := by group
      _ = 1 := by rw [ih, inv_one]

namespace Ctx

theorem conjClosure_spec (c : Ctx A B z V) {ω : D} (hω : ω ∈ centerOf (A ⊓ B))
    (hω2 : ω * ω = 1) {y : D} (hy : y ∈ conjClosure (Subgroup.zpowers ω) A) :
    y ∈ pCoreOf 2 A ∧ (∀ q ∈ pCoreOf 2 A, q * y = y * q) ∧ y * y = 1 := by
  unfold conjClosure at hy
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨h, hh, w, hw, rfl⟩ := hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hωQ : ω ∈ pCoreOf 2 A := c.hyp.gold.centerOf_le_pCoreOf_left hω
    have hωk : ω ^ k ∈ pCoreOf 2 A := (pCoreOf 2 A).zpow_mem hωQ k
    refine ⟨pCoreOf_conj_mem hh hωk, fun q hq => ?_, ?_⟩
    · have hq' : h⁻¹ * q * h⁻¹⁻¹ ∈ pCoreOf 2 A := pCoreOf_conj_mem (A.inv_mem hh) hq
      have hc : (h⁻¹ * q * h⁻¹⁻¹) * ω ^ k = ω ^ k * (h⁻¹ * q * h⁻¹⁻¹) := by
        have hcω : (h⁻¹ * q * h⁻¹⁻¹) * ω = ω * (h⁻¹ * q * h⁻¹⁻¹) :=
          Subgroup.mem_centralizer_iff.mp hω.2 _ (c.Q_le_T hq')
        exact ((Commute.zpow_right (show Commute (h⁻¹ * q * h⁻¹⁻¹) ω from hcω) k)).eq
      calc q * (h * ω ^ k * h⁻¹) = h * ((h⁻¹ * q * h⁻¹⁻¹) * ω ^ k) * h⁻¹ := by group
        _ = h * (ω ^ k * (h⁻¹ * q * h⁻¹⁻¹)) * h⁻¹ := by rw [hc]
        _ = (h * ω ^ k * h⁻¹) * q := by group
    · have hk2 : ω ^ k * ω ^ k = 1 := by
        have hω2' : ω ^ 2 = 1 := by rw [pow_two]; exact hω2
        rcases zpow_eq_one_or_self hω2' k with e | e <;> rw [e]
        · simp
        · exact hω2
      calc h * ω ^ k * h⁻¹ * (h * ω ^ k * h⁻¹) = h * (ω ^ k * ω ^ k) * h⁻¹ := by group
        _ = 1 := by rw [hk2]; group
  | one => exact ⟨Subgroup.one_mem _, fun q _ => by simp, by simp⟩
  | mul x y _ _ ihx ihy =>
    refine ⟨(pCoreOf 2 A).mul_mem ihx.1 ihy.1, fun q hq => ?_, ?_⟩
    · calc q * (x * y) = (q * x) * y := by rw [mul_assoc]
        _ = (x * q) * y := by rw [ihx.2.1 q hq]
        _ = x * (q * y) := by rw [mul_assoc]
        _ = x * (y * q) := by rw [ihy.2.1 q hq]
        _ = (x * y) * q := by rw [mul_assoc]
    · have hxy : x * y = y * x := ihy.2.1 x ihx.1
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [hxy]
        _ = (x * x) * (y * y) := by group
        _ = 1 := by rw [ihx.2.2, ihy.2.2, one_mul]
  | inv x _ ih =>
    refine ⟨(pCoreOf 2 A).inv_mem ih.1, fun q hq => ?_, ?_⟩
    · have := ih.2.1 q hq
      calc q * x⁻¹ = x⁻¹ * (x * q) * x⁻¹ := by group
        _ = x⁻¹ * (q * x) * x⁻¹ := by rw [this]
        _ = x⁻¹ * q := by group
    · calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
        _ = 1 := by rw [ih.2.2, inv_one]

theorem goldHyp3_of_natural (c : Ctx A B z V) {ω z' : D} {V' : Subgroup D}
    (hω : ω ∈ centerOf (A ⊓ B)) (hω2 : ω * ω = 1) (hnat : IsNaturalAt A (A ⊓ B) z' V')
    (hzmem : z' ∈ conjClosure (Subgroup.zpowers ω) A) (hcen : ∀ y ∈ B, y * z' * y⁻¹ = z') :
    GoldHyp3 A B z' V' := by
  have hVC : ∀ v ∈ V', v ∈ pCoreOf 2 A ∧ (∀ q ∈ pCoreOf 2 A, q * v = v * q) ∧ v * v = 1 := by
    intro v hv
    refine c.conjClosure_spec hω hω2 ?_
    rw [hnat.V_eq] at hv
    have : conjClosure (Subgroup.zpowers z') A ≤ conjClosure (Subgroup.zpowers ω) A := by
      refine conjClosure_le fun h hh y hy => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact conjClosure_conj_mem hh (Subgroup.zpow_mem _ hzmem k)
    exact this hv
  have hK : ∀ v ∈ V', v ∈ Ksub A B := fun v hv =>
    (c.mem_K_iff).mpr ⟨(hVC v hv).1, fun u hu => (hVC v hv).2.1 u (c.U_le_Q hu)⟩
  refine ⟨c.hyp.gold, hnat, hcen, ?_⟩
  show IsElemAbelian 2 (Subgroup.closure {x | ∃ h ∈ B, ∃ v ∈ V', h * v * h⁻¹ = x})
  refine isElemAbelian_closure ?_ ?_
  · rintro _ ⟨h, hh, v, hv, rfl⟩ _ ⟨h', hh', v', hv', rfl⟩
    have hm : h⁻¹ * h' ∈ B := B.mul_mem (B.inv_mem hh) hh'
    have hw : (h⁻¹ * h') * v' * (h⁻¹ * h')⁻¹ ∈ Ksub A B := c.K_normal hm (hK v' hv')
    have hwQ := c.K_le_Q hw
    have hvw : v * ((h⁻¹ * h') * v' * (h⁻¹ * h')⁻¹) = ((h⁻¹ * h') * v' * (h⁻¹ * h')⁻¹) * v :=
      ((hVC v hv).2.1 _ hwQ).symm
    calc h * v * h⁻¹ * (h' * v' * h'⁻¹)
        = h * (v * ((h⁻¹ * h') * v' * (h⁻¹ * h')⁻¹)) * h⁻¹ := by group
      _ = h * (((h⁻¹ * h') * v' * (h⁻¹ * h')⁻¹) * v) * h⁻¹ := by rw [hvw]
      _ = h' * v' * h'⁻¹ * (h * v * h⁻¹) := by group
  · rintro _ ⟨h, hh, v, hv, rfl⟩
    calc h * v * h⁻¹ * (h * v * h⁻¹) = h * (v * v) * h⁻¹ := by group
      _ = 1 := by rw [(hVC v hv).2.2]; group

theorem critDist_eq_three_of_goldHyp3 (c : Ctx A B z V) {z' : D} {V' : Subgroup D}
    (h' : GoldHyp3 A B z' V') :
    critDist (A ⊔ B) A B V' = 3 := by
  have h3 := h'.three_le_critDist
  by_contra hne
  have h4 : 4 ≤ critDist (A ⊔ B) A B V' := by omega
  have hW' := h'.four_le_critDist_iff_le_coreIn.mp h4
  apply c.W_not_le_P
  intro w hw
  have hwT : w ∈ A ⊓ B := c.Q_le_T (c.W_le_Q hw)
  rw [h'.pCoreOf_eq_centralizerMod]
  refine ⟨hwT.2, ?_, fun u' hu' => ?_⟩
  · have hc : w * z' = z' * w := Subgroup.mem_centralizer_iff.mp h'.natural.z_mem.2 w hwT
    exact mem_normalizer_zpowers_of_mul_comm hc
  · have hu'W' : u' ∈ conjClosure (conjClosure V' B) A := le_conjClosure _ _ hu'
    have hu'K := hW' hu'W'
    have hcomm : ∀ w' ∈ conjClosure (conjClosure V' B) A, ∀ x ∈ Wsub A B V, w' * x = x * w' := by
      intro w' hw' x hx
      have hle : Wsub A B V ≤ Subgroup.centralizer ({w'} : Set D) := by
        refine conjClosure_le fun h hh u hu => ?_
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        have hconj : h⁻¹ * y * h⁻¹⁻¹ ∈ conjClosure (conjClosure V' B) A :=
          conjClosure_conj_mem (A.inv_mem hh) hw'
        have := c.hyp.comm_of_mem_coreIn (hW' hconj) u hu
        calc y * (h * u * h⁻¹) = h * ((h⁻¹ * y * h⁻¹⁻¹) * u) * h⁻¹ := by group
          _ = h * (u * (h⁻¹ * y * h⁻¹⁻¹)) * h⁻¹ := by rw [this.symm]
          _ = (h * u * h⁻¹) * y := by group
      exact Subgroup.mem_centralizer_iff.mp (hle hx) w' (Set.mem_singleton w')
    have := hcomm u' hu'W' w hw
    have e : w * u' * w⁻¹ * u'⁻¹ = 1 := by
      rw [← this]; group
    rw [e]
    exact Subgroup.one_mem _

end Ctx

namespace Gen

variable {c : Ctx A B z V} (g : Gen c)

include g in
theorem eq_zpowers_of_centerT_involution {ω : D} (hω : ω ∈ centerOf (A ⊓ B)) (hω2 : ω * ω = 1) :
    ω ∈ Subgroup.zpowers z := by
  by_contra hωz
  have hω1 : ω ≠ 1 := fun h => hωz (h ▸ Subgroup.one_mem _)
  have hmove : ∃ y ∈ A, y * ω * y⁻¹ ≠ ω := by
    by_contra hcon
    push Not at hcon
    exact hω1 (g.centerT_central_A hω hcon)
  have hω2' : ω ^ 2 = 1 := by rw [pow_two]; exact hω2
  obtain ⟨x, z', V', hxA, hx3, hxω, hz', hnat, hzmem⟩ :=
    exists_natural_data c.hyp.gold.vertex_left hω hω2' hmove
  have hz'T : z' ∈ centerOf (A ⊓ B) := hnat.z_mem
  have h' : GoldHyp3 A B z' V' :=
    c.goldHyp3_of_natural hω hω2 hnat hzmem (g.centerT_central_B hz'T)
  have hb' := c.critDist_eq_three_of_goldHyp3 h'
  have hU' := h'.card_conjClosure_eq_eight_of_critDist_eq_three hb'
  have hne : V ⊓ V' ≠ ⊥ :=
    GoldAmL3K.inf_ne_bot_of_critDist_eq_three c.hyp h' c.card_eq hU' c.crit_eq
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hy1' : y ≠ 1 := fun e => hy1 (Subtype.ext e)
  obtain ⟨a', ha', hay⟩ := exists_conj_eq_of_mem c.hyp.gold hnat (Subgroup.mem_inf.mp hy).2 hy1'
  have hz'V : z' ∈ V := by
    have : z' = a'⁻¹ * y * a'⁻¹⁻¹ := by rw [← hay]; group
    rw [this]
    exact c.V_normal (A.inv_mem ha') (Subgroup.mem_inf.mp hy).1
  have hτ : g.τ * z' * g.τ⁻¹ = z' := by
    have := Subgroup.mem_centralizer_iff.mp hz'T.2 g.τ g.τ_mem
    rw [this]; group
  have hz'z : z' = z := by
    rcases g.fix_tau hz'V hτ with e | e
    · exact absurd e hnat.z_ne
    · exact e
  have hcls : ∀ h ∈ A, h * ω * h⁻¹ ∈ conjClosure (Subgroup.zpowers ω) A := fun h hh =>
    mem_conjClosure hh (Subgroup.mem_zpowers ω)
  have hspec : ∀ a ∈ conjClosure (Subgroup.zpowers ω) A, ∀ b ∈ conjClosure (Subgroup.zpowers ω) A,
      a * b = b * a := fun a ha b hb =>
    ((c.conjClosure_spec hω hω2 ha).2.1 b (c.conjClosure_spec hω hω2 hb).1).symm
  have hωC : ω ∈ conjClosure (Subgroup.zpowers ω) A := le_conjClosure _ _ (Subgroup.mem_zpowers ω)
  have hxx : x * x ∈ A := A.mul_mem hxA hxA
  have hpC := hcls x hxA
  have hqC : x * x * ω * (x * x)⁻¹ ∈ conjClosure (Subgroup.zpowers ω) A := hcls (x * x) hxx
  have hR : (x * ω * x⁻¹) * (x * x * ω * (x * x)⁻¹) = z := by rw [← hz'z, hz']
  have hcx : x * ((x * ω * x⁻¹) * (x * x * ω * (x * x)⁻¹)) * x⁻¹ = x * z * x⁻¹ := by rw [hR]
  have hconj : (x * x * ω * (x * x)⁻¹) * ω = x * z * x⁻¹ := by
    rw [← hcx]
    have e1 : x * (x * ω * x⁻¹) * x⁻¹ = x * x * ω * (x * x)⁻¹ := by group
    have e2 : x * (x * x * ω * (x * x)⁻¹) * x⁻¹ = ω := by
      calc x * (x * x * ω * (x * x)⁻¹) * x⁻¹ = (x * x * x) * ω * (x * x * x)⁻¹ := by group
        _ = ω := by rw [hx3]; group
    calc (x * x * ω * (x * x)⁻¹) * ω
        = (x * (x * ω * x⁻¹) * x⁻¹) * (x * (x * x * ω * (x * x)⁻¹) * x⁻¹) := by rw [e1, e2]
      _ = x * ((x * ω * x⁻¹) * (x * x * ω * (x * x)⁻¹)) * x⁻¹ := by group
  have hzT : z ∈ centerOf (A ⊓ B) := c.hyp.natural.z_mem
  have hωzT : ω * z ∈ centerOf (A ⊓ B) := (centerOf (A ⊓ B)).mul_mem hω hzT
  have hωz_comm : ω * z = z * ω :=
    (Subgroup.mem_centralizer_iff.mp hω.2 z hzT.1).symm
  have hxfix : x * (ω * z) * x⁻¹ = ω * z := by
    have : x * (ω * z) * x⁻¹ = (x * ω * x⁻¹) * (x * z * x⁻¹) := by group
    rw [this, ← hconj]
    calc (x * ω * x⁻¹) * ((x * x * ω * (x * x)⁻¹) * ω)
        = ((x * ω * x⁻¹) * (x * x * ω * (x * x)⁻¹)) * ω := by group
      _ = z * ω := by rw [hR]
      _ = ω * z := hωz_comm.symm
  have hxo : orderOf x = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime (by rw [pow_three']; exact hx3) (fun h => hxω (by rw [h]; group))
  have hA3 := GoldAmN.inf_sup_zpowers_eq_right_vTriple
    c.hyp.gold.symm.amalgam.toIsGoldschmidtVTriple hxA hxo
  rw [inf_comm] at hA3
  have hAle : A ≤ Subgroup.centralizer ({ω * z} : Set D) := by
    rw [← hA3]
    refine sup_le (fun t ht => ?_) (Subgroup.zpowers_le.mpr ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (Subgroup.mem_centralizer_iff.mp hωzT.2 t ht).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (mul_eq_of_conj_eq hxfix).symm
  have hAfix : ∀ y ∈ A, y * (ω * z) * y⁻¹ = ω * z := by
    intro y hy
    have := Subgroup.mem_centralizer_iff.mp (hAle hy) (ω * z) (Set.mem_singleton _)
    rw [← this]; group
  have h1 := g.centerT_central_A hωzT hAfix
  apply hωz
  have : ω = z⁻¹ := mul_eq_one_iff_eq_inv.mp h1
  rw [this, c.inv_eq_self c.z_mem_V]
  exact Subgroup.mem_zpowers z

end Gen

end GoldAmL3E

end F6

end CFSG.Quasithin
