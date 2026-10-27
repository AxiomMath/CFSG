module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34OddF81

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.Vol2.Ch10.SecA (unipSL coe_unipSL unipSL_mulVec)

namespace Setup5_1_17Odd

variable {G : Type} [Group G] [Finite G] {T M L V H B D : Subgroup G} {n : ℕ}
variable (s : Setup5_1_17Odd G T M L V H B D n)
include s

theorem T_act_eq (hI : L2OddInnerFact) (c : OddCoord T L V n)
    (t : Subgroup.normalizer (V : Set G)) (ht : (t : G) ∈ T) (w : Fin 2 → c.K) :
    c.act t w = ![w 0 + (c.act t ![0, 1]) 0 * w 1, w 1] := by
  obtain ⟨l, hl, hlt⟩ := s.exists_inf_conj_eq hI ht
  obtain ⟨b, hb⟩ := c.unip ⟨l, s.L_le_normalizer_V hl.2⟩ hl
  have key : ∀ w, c.act t w = ![w 0 + b * w 1, w 1] := fun w => by
    rw [c.act_eq_of_conj_eq (h := ⟨l, s.L_le_normalizer_V hl.2⟩) hlt, hb, coe_unipSL,
      unipSL_mulVec]
  rw [key w, key ![0, 1]]
  simp

theorem mem_centralizer_iff_of_T (hI : L2OddInnerFact) (c : OddCoord T L V n)
    (t : Subgroup.normalizer (V : Set G)) (ht : (t : G) ∈ T) :
    (t : G) ∈ Subgroup.centralizer (V : Set G) ↔ (c.act t ![0, 1]) 0 = 0 := by
  rw [c.mem_centralizer_iff]
  constructor
  · intro h
    have := congrFun (h ![0, 1]) 0
    simpa using this
  · intro h w
    rw [s.T_act_eq hI c t ht, h, zero_mul, add_zero]
    funext i
    fin_cases i <;> rfl

theorem card_V : Nat.card V = 2 ^ n * 2 ^ n := by
  obtain ⟨c⟩ := s.nonempty_coord
  rw [Nat.card_congr (Equiv.ofBijective c.ε c.ε_bij), Nat.card_fun, c.card, Nat.card_fin, sq]

theorem card_Z₁ (hI : L2OddInnerFact) :
    Nat.card ↥(quasithinOmegaOneCenter T ⊓ V) = 2 ^ n := by
  obtain ⟨c⟩ := s.nonempty_coord
  rw [← c.card]
  refine Nat.card_congr (Equiv.ofBijective
    (fun z : ↥(quasithinOmegaOneCenter T ⊓ V) => c.ε ⟨z, z.2.2⟩ 0)
    ⟨fun z z' hzz => ?_, fun a => ?_⟩)
  · have h1 : c.ε ⟨z, z.2.2⟩ 1 = 0 := (s.mem_Z_iff hI c _).mp z.2.1
    have h1' : c.ε ⟨z', z'.2.2⟩ 1 = 0 := (s.mem_Z_iff hI c _).mp z'.2.1
    have he : c.ε ⟨z, z.2.2⟩ = c.ε ⟨z', z'.2.2⟩ := by
      funext i
      fin_cases i
      · exact hzz
      · exact h1.trans h1'.symm
    exact Subtype.ext (congrArg (fun v : ↥V => (v : G)) (c.ε_bij.1 he))
  · obtain ⟨v, hv⟩ := c.ε_bij.2 ![a, 0]
    have hvZ : (v : G) ∈ quasithinOmegaOneCenter T := (s.mem_Z_iff hI c v).mpr (by rw [hv]; rfl)
    refine ⟨⟨v, hvZ, v.2⟩, ?_⟩
    show c.ε ⟨v, v.2⟩ 0 = a
    rw [hv]
    rfl

theorem relIndex_centralizer_T_le (hI : L2OddInnerFact) :
    (Subgroup.centralizer (V : Set G)).relIndex T ≤ 2 ^ n := by
  obtain ⟨c⟩ := s.nonempty_coord
  have hTN := s.T_le_normalizer
  let tn : ↥T → Subgroup.normalizer (V : Set G) := fun t => ⟨t, hTN t.2⟩
  let f : ↥T → c.K := fun t => (c.act (tn t) ![0, 1]) 0
  have hf : ∀ t w, c.act (tn t) w = ![w 0 + f t * w 1, w 1] := fun t w =>
    s.T_act_eq hI c (tn t) t.2 w
  have hmul : ∀ t t' : ↥T, f (t * t') = f t + f t' := by
    intro t t'
    have h1 : c.act (tn (t * t')) ![0, 1] = c.act (tn t) (c.act (tn t') ![0, 1]) := by
      rw [← c.act_mul]
      rfl
    have h2 := congrFun h1 0
    rw [hf t (c.act (tn t') ![0, 1]), hf t' ![0, 1]] at h2
    simpa [add_comm] using h2
  have hone : f 1 = 0 := by
    have h1 : c.act (tn 1) ![0, 1] = ![0, 1] := c.act_one _
    have := congrFun h1 0
    simpa using this
  let β : ↥T →* Multiplicative c.K :=
    { toFun := fun t => Multiplicative.ofAdd (f t)
      map_one' := by rw [hone, ofAdd_zero]
      map_mul' := fun t t' => by rw [hmul, ofAdd_add] }
  have hker : β.ker = (Subgroup.centralizer (V : Set G)).subgroupOf T := by
    ext t
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf,
      s.mem_centralizer_iff_of_T hI c (tn t) t.2]
    show Multiplicative.ofAdd (f t) = 1 ↔ f t = 0
    rw [← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff]
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  calc Nat.card β.range ≤ Nat.card (Multiplicative c.K) := Subgroup.card_le_card_group _
    _ = 2 ^ n := by rw [Nat.card_congr Multiplicative.toAdd, c.card]

theorem card_inf_centralizer_le (hI : L2OddInnerFact) {t : G} (ht : t ∈ T)
    (htV : t ∉ Subgroup.centralizer (V : Set G)) :
    Nat.card ↥(V ⊓ Subgroup.centralizer ({t} : Set G)) ≤ 2 ^ n := by
  obtain ⟨c⟩ := s.nonempty_coord
  let tn : Subgroup.normalizer (V : Set G) := ⟨t, s.T_le_normalizer ht⟩
  have hb : (c.act tn ![0, 1]) 0 ≠ 0 := fun h0 =>
    htV ((s.mem_centralizer_iff_of_T hI c tn ht).mpr h0)
  have hfix : ∀ v : ↥(V ⊓ Subgroup.centralizer ({t} : Set G)), c.ε ⟨v, v.2.1⟩ 1 = 0 := by
    intro v
    have htv : (tn : G) * v * (tn : G)⁻¹ = v := by
      have := Subgroup.mem_centralizer_singleton_iff.mp v.2.2
      show t * v * t⁻¹ = v
      rw [← this, mul_inv_cancel_right]
    have h1 := (c.conj_eq_iff tn ⟨v, v.2.1⟩).mp htv
    rw [s.T_act_eq hI c tn ht] at h1
    have h2 := congrFun h1 0
    simp only [Matrix.cons_val_zero] at h2
    have h3 : (c.act tn ![0, 1]) 0 * c.ε ⟨v, v.2.1⟩ 1 = 0 := by linear_combination h2
    exact (mul_eq_zero.mp h3).resolve_left hb
  rw [← c.card]
  refine Nat.card_le_card_of_injective (fun v => c.ε ⟨v, v.2.1⟩ 0) fun v v' hvv => ?_
  have he : c.ε ⟨v, v.2.1⟩ = c.ε ⟨v', v'.2.1⟩ := by
    funext i
    fin_cases i
    · exact hvv
    · exact (hfix v).trans (hfix v').symm
  exact Subtype.ext (congrArg (fun v : ↥V => (v : G)) (c.ε_bij.1 he))

theorem exists_conj_le_T {E : Subgroup G} (hEN : E ≤ Subgroup.normalizer (V : Set G))
    (hE : IsPGroup 2 E) : ∃ x ∈ Subgroup.normalizer (V : Set G), conjSub x E ≤ T :=
  exists_conj_le_of_isSylowTwoOf (s.hyp.hyp.toHyp5_0_1.isSylowTwoOf s.T_le_normalizer) hEN hE

theorem relIndex_centralizer_le (hI : L2OddInnerFact) {E : Subgroup G}
    (hEN : E ≤ Subgroup.normalizer (V : Set G)) (hE : IsPGroup 2 E) :
    (Subgroup.centralizer (V : Set G)).relIndex E ≤ 2 ^ n := by
  obtain ⟨x, hxN, hxE⟩ := s.exists_conj_le_T hEN hE
  have h1 : (Subgroup.centralizer (V : Set G)).relIndex E =
      (Subgroup.centralizer (V : Set G)).relIndex (conjSub x E) := by
    rw [← Subgroup.relIndex_map_map_of_injective _ _
      (fun a b h => (MulAut.conj x).injective h : Function.Injective (MulAut.conj x).toMonoidHom)]
    change (conjSub x (Subgroup.centralizer (V : Set G))).relIndex (conjSub x E) = _
    rw [← conjSub_centralizer, F7.conjSub_eq_of_mem_normalizer hxN]
  rw [h1]
  exact (Subgroup.relIndex_le_of_le_right hxE (Subgroup.index_ne_zero_of_finite)).trans
    (s.relIndex_centralizer_T_le hI)

theorem le_relIndex_centralizer (hI : L2OddInnerFact) {E : Subgroup G}
    (hEN : E ≤ Subgroup.normalizer (V : Set G)) (hE : IsPGroup 2 E)
    (hEC : ¬ E ≤ Subgroup.centralizer (V : Set G)) :
    2 ^ n ≤ (Subgroup.centralizer (E : Set G)).relIndex V := by
  obtain ⟨e, heE, heC⟩ := Set.not_subset.mp hEC
  obtain ⟨x, hxN, hxE⟩ := s.exists_conj_le_T hEN hE
  have hxV := F7.conjSub_eq_of_mem_normalizer hxN
  have htT : x * e * x⁻¹ ∈ T := hxE (mul_mem_conjSub heE)
  have htC : x * e * x⁻¹ ∉ Subgroup.centralizer (V : Set G) := fun h => by
    apply heC
    have h' : x * e * x⁻¹ ∈ conjSub x (Subgroup.centralizer (V : Set G)) := by
      rw [← conjSub_centralizer, hxV]
      exact h
    have e' : x⁻¹ * (x * e * x⁻¹) * x = e := by group
    have := mem_conjSub.mp h'
    rwa [e'] at this
  have hcard : Nat.card ↥(Subgroup.centralizer (E : Set G) ⊓ V) ≤ 2 ^ n := by
    refine le_trans ?_ (s.card_inf_centralizer_le hI htT htC)
    have hmemV : ∀ v : ↥(Subgroup.centralizer (E : Set G) ⊓ V), x * (v : G) * x⁻¹ ∈ V := by
      intro v
      have := mul_mem_conjSub (g := x) v.2.2
      rwa [hxV] at this
    have hmemC : ∀ v : ↥(Subgroup.centralizer (E : Set G) ⊓ V),
        x * (v : G) * x⁻¹ ∈ Subgroup.centralizer ({x * e * x⁻¹} : Set G) := by
      intro v
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      have hve : e * v = v * e :=
        (Subgroup.mem_centralizer_iff.mp v.2.1 e heE)
      calc x * v * x⁻¹ * (x * e * x⁻¹) = x * (v * e) * x⁻¹ := by group
        _ = x * (e * v) * x⁻¹ := by rw [hve]
        _ = x * e * x⁻¹ * (x * v * x⁻¹) := by group
    refine Nat.card_le_card_of_injective
      (fun v => ⟨x * v * x⁻¹, Subgroup.mem_inf.mpr ⟨hmemV v, hmemC v⟩⟩) fun v v' hvv => ?_
    have h1 : x * (v : G) * x⁻¹ = x * v' * x⁻¹ :=
      congrArg (fun w : ↥(V ⊓ Subgroup.centralizer ({x * e * x⁻¹} : Set G)) => (w : G)) hvv
    exact Subtype.ext (by simpa using h1)
  have hmul := (Subgroup.centralizer (E : Set G)).relIndex_mul_card V
  rw [s.card_V] at hmul
  by_contra hlt
  push Not at hlt
  have h1 : (Subgroup.centralizer (E : Set G)).relIndex V *
      Nat.card ↥(Subgroup.centralizer (E : Set G) ⊓ V) < 2 ^ n * 2 ^ n :=
    calc _ ≤ (Subgroup.centralizer (E : Set G)).relIndex V * 2 ^ n := Nat.mul_le_mul_left _ hcard
      _ < 2 ^ n * 2 ^ n := Nat.mul_lt_mul_of_pos_right hlt (by positivity)
  omega

theorem relIndex_centralizer_conjSub_le (hI : L2OddInnerFact) (g : G) {E : Subgroup G}
    (hEN : E ≤ Subgroup.normalizer (conjSub g V : Set G)) (hE : IsPGroup 2 E) :
    (Subgroup.centralizer (conjSub g V : Set G)).relIndex E ≤ 2 ^ n := by
  have hEN' : conjSub g⁻¹ E ≤ Subgroup.normalizer (V : Set G) := by
    have := conjSub_le_normalizer (g := g⁻¹) hEN
    rwa [conjSub_conjSub_inv] at this
  have hE' : IsPGroup 2 (conjSub g⁻¹ E) := hE.map _
  have h1 : (Subgroup.centralizer (conjSub g V : Set G)).relIndex E =
      (Subgroup.centralizer (V : Set G)).relIndex (conjSub g⁻¹ E) := by
    rw [← Subgroup.relIndex_map_map_of_injective _ _
      (fun a b h => (MulAut.conj g⁻¹).injective h :
        Function.Injective (MulAut.conj g⁻¹).toMonoidHom)]
    change (conjSub g⁻¹ (Subgroup.centralizer (conjSub g V : Set G))).relIndex
      (conjSub g⁻¹ E) = _
    rw [← conjSub_centralizer, conjSub_conjSub_inv]
  rw [h1]
  exact s.relIndex_centralizer_le hI hEN' hE'

theorem le_relIndex_centralizer_conjSub (hI : L2OddInnerFact) (g : G) {E : Subgroup G}
    (hEN : E ≤ Subgroup.normalizer (conjSub g V : Set G)) (hE : IsPGroup 2 E)
    (hEC : ¬ E ≤ Subgroup.centralizer (conjSub g V : Set G)) :
    2 ^ n ≤ (Subgroup.centralizer (E : Set G)).relIndex (conjSub g V) := by
  have hEN' : conjSub g⁻¹ E ≤ Subgroup.normalizer (V : Set G) := by
    have := conjSub_le_normalizer (g := g⁻¹) hEN
    rwa [conjSub_conjSub_inv] at this
  have hE' : IsPGroup 2 (conjSub g⁻¹ E) := hE.map _
  have hEC' : ¬ conjSub g⁻¹ E ≤ Subgroup.centralizer (V : Set G) := fun h => by
    apply hEC
    have := conjSub_mono g h
    rwa [conjSub_inv_conjSub, ← conjSub_centralizer] at this
  have h1 : (Subgroup.centralizer (E : Set G)).relIndex (conjSub g V) =
      (Subgroup.centralizer (conjSub g⁻¹ E : Set G)).relIndex V := by
    rw [← Subgroup.relIndex_map_map_of_injective _ _
      (fun a b h => (MulAut.conj g⁻¹).injective h :
        Function.Injective (MulAut.conj g⁻¹).toMonoidHom)]
    change (conjSub g⁻¹ (Subgroup.centralizer (E : Set G))).relIndex
      (conjSub g⁻¹ (conjSub g V)) = _
    rw [← conjSub_centralizer, conjSub_conjSub_inv]
  rw [h1]
  exact s.le_relIndex_centralizer hI hEN' hE' hEC'

omit s in
theorem le_centralizer_of_isTISetUnder
    (hTI : IsTISetUnder (quasithinOmegaOneCenter T ⊓ V) ⊤) (hT : IsSylowTwoOf T ⊤) (g : G)
    {z : G} (hz : z ∈ conjSub g (quasithinOmegaOneCenter T ⊓ V)) (hz1 : z ≠ 1) {P : Subgroup G}
    (hP : IsPGroup 2 P) (hPz : P ≤ Subgroup.centralizer ({z} : Set G)) :
    P ≤ Subgroup.centralizer (conjSub g (quasithinOmegaOneCenter T ⊓ V) : Set G) := by
  set Z₁ := quasithinOmegaOneCenter T ⊓ V with hZ₁
  have hCN : Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (conjSub g Z₁ : Set G) := by
    intro c hc
    have hz₀ : g⁻¹ * z * g ∈ Z₁ := mem_conjSub.mp hz
    have hz₀1 : g⁻¹ * z * g ≠ 1 := fun h => hz1 (by
      have : z = g * (g⁻¹ * z * g) * g⁻¹ := by group
      rw [this, h]; group)
    have hcz : c * z = z * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    set c' := g⁻¹ * c * g with hc'
    have hc'N : c'⁻¹ ∈ Subgroup.normalizer (Z₁ : Set G) := by
      by_contra hn
      have hbot := hTI c'⁻¹ (Subgroup.mem_top _) hn
      have hmem : g⁻¹ * z * g ∈ Z₁ ⊓ CFSG.conjugate Z₁ c'⁻¹ := by
        refine ⟨hz₀, ?_⟩
        show g⁻¹ * z * g ∈ conjSub c'⁻¹⁻¹ Z₁
        rw [mem_conjSub]
        have e : c'⁻¹⁻¹⁻¹ * (g⁻¹ * z * g) * c'⁻¹⁻¹ = g⁻¹ * (c⁻¹ * z * c) * g := by
          rw [hc']; group
        have hcz' : c⁻¹ * z * c = z := by
          rw [mul_assoc, ← hcz, ← mul_assoc, inv_mul_cancel, one_mul]
        rw [e, hcz']
        exact hz₀
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hz₀1 hmem
    have hc'N' : c' ∈ Subgroup.normalizer (Z₁ : Set G) := by simpa using inv_mem hc'N
    rw [conjSub_normalizer, mem_conjSub]
    exact hc'N'
  have hTC : conjSub g T ≤ Subgroup.centralizer (conjSub g Z₁ : Set G) := by
    rw [conjSub_centralizer]
    exact conjSub_mono g Setup5_1_17Odd.T_le_centralizer_Z₁
  have hTz : conjSub g T ≤ Subgroup.centralizer ({z} : Set G) := fun t ht => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (hTC ht) z hz).symm
  have hsyl : IsSylowTwoOf (conjSub g T) (Subgroup.centralizer ({z} : Set G)) := by
    refine ⟨hTz, hT.2.1.map _, fun h2 => hT.2.2 ?_⟩
    have h1 : (conjSub g T).relIndex (Subgroup.centralizer ({z} : Set G)) ∣
        (conjSub g T).index :=
      Subgroup.relIndex_dvd_index_of_le hTz
    have h2' : (conjSub g T).index = T.index :=
      T.index_map_eq (MulAut.conj g).surjective (by
        intro x hx
        have : x = 1 := (MulAut.conj g).injective (by simpa using hx)
        rw [this]
        exact T.one_mem)
    show 2 ∣ T.relIndex ⊤
    rw [Subgroup.relIndex_top_right, ← h2']
    exact h2.trans h1
  obtain ⟨c, hc, hcP⟩ := exists_conj_le_of_isSylowTwoOf hsyl hPz hP
  intro x hx
  have h1 : c * x * c⁻¹ ∈ Subgroup.centralizer (conjSub g Z₁ : Set G) :=
    hTC (hcP (mul_mem_conjSub hx))
  have hcN := hCN hc
  rw [Subgroup.mem_centralizer_iff] at h1 ⊢
  intro w hw
  have hw' : c * w * c⁻¹ ∈ conjSub g Z₁ := (Subgroup.mem_normalizer_iff.mp hcN w).mp hw
  have h2 := h1 _ hw'
  have e1 : c * w * c⁻¹ * (c * x * c⁻¹) = c * (w * x) * c⁻¹ := by group
  have e2 : c * x * c⁻¹ * (c * w * c⁻¹) = c * (x * w) * c⁻¹ := by group
  rw [e1, e2] at h2
  simpa using h2

end Setup5_1_17Odd

end CFSG.Quasithin.H13
