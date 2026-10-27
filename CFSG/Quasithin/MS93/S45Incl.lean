module

public import CFSG.Quasithin.MS93.S46I469Grp
public import CFSG.Quasithin.MS93.S45Cen
public import CFSG.Quasithin.MS93.S45Phi3

public section

namespace CFSG.Quasithin.MS93.S45I

open CFSG.Quasithin CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.ML3 CFSG.Quasithin.MS93.S46
  CFSG.Assembly.LowTwoRank Matrix
open scoped commutatorElement Pointwise

section Generic

variable {F : Type} [Field F] {𝔾 : Type} [Group 𝔾]

theorem commutator_eq_bot_of_dual_layers {K Z W W' H : Subgroup 𝔾}
    {ψ : ↥K →* ↥(StatedSL 3 F)} (hsurj : Function.Surjective ψ)
    (hW : IsSumOfNaturalModulesVia K W Z ψ true 1)
    (hW' : IsSumOfNaturalModulesVia K W' Z ψ true 1) (hWW' : ⁅W, W'⁆ ≤ H)
    (hHK : H ≤ Subgroup.centralizer (K : Set 𝔾)) (hW'K : W' ≤ K) (hZW : ⁅Z, W⁆ = ⊥)
    (hZW' : ⁅Z, W'⁆ = ⊥) : ⁅W, W'⁆ = ⊥ := by
  classical
  set N := NatSec.ofIsSum hW with hN
  set N' := NatSec.ofIsSum hW' with hN'
  have hHW' : ⁅H, W'⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact Subgroup.le_centralizer_iff.mp (hW'K.trans (Subgroup.le_centralizer_iff.mp hHK))
  have hcent : ∀ c ∈ H, ∀ k : ↥K, (k : 𝔾) * c * (k : 𝔾)⁻¹ = c := by
    intro c hc k
    rw [Subgroup.mem_centralizer_iff.mp (hHK hc) k k.2, mul_inv_cancel_right]
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro v hv w hw
  rw [Subgroup.mem_bot]
  by_cases hvZ : v ∈ Z
  · rw [commutatorElement_eq_one_iff_mul_comm]
    exact commute_of_commutator_eq_bot hZW' hvZ hw
  have hc : N.coord v ≠ 0 := by rwa [Ne, N.coord_eq_zero_iff hv]
  have hinv : ∀ w ∈ W', ⁅v, w⁻¹⁆ = ⁅v, w⁆⁻¹ := by
    intro w hw
    have h1 := ML3.comm_mul_right hHW' hWW' hv hw (W'.inv_mem hw)
    rw [mul_inv_cancel, commutatorElement_one_right] at h1
    exact eq_inv_of_mul_eq_one_right h1.symm
  let P : Subgroup 𝔾 :=
    { carrier := {w | w ∈ W' ∧ ⁅v, w⁆ = 1}
      one_mem' := ⟨W'.one_mem, commutatorElement_one_right v⟩
      mul_mem' := fun {a b} ha hb => ⟨W'.mul_mem ha.1 hb.1, by
        rw [ML3.comm_mul_right hHW' hWW' hv ha.1 hb.1, ha.2, hb.2, mul_one]⟩
      inv_mem' := fun {a} ha => ⟨W'.inv_mem ha.1, by rw [hinv a ha.1, ha.2, inv_one]⟩ }
  have hZP : ∀ z ∈ Z, z ∈ P := by
    intro z hz
    refine ⟨hW'.2.1 hz, ?_⟩
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (commute_of_commutator_eq_bot hZW hz hv).symm
  have himg : N'.img P = ⊤ := by
    refine eq_top_of_forall_dualStab hc _ fun g hg y => ?_
    obtain ⟨k, rfl⟩ := toSL3_surjective hsurj g
    obtain ⟨w, hw, rfl⟩ := N'.exists_coord_eq y
    have hkw := N'.conj_mem k hw
    refine (N'.mem_img).mpr ⟨(k : 𝔾) * w * (k : 𝔾)⁻¹ * w⁻¹,
      ⟨W'.mul_mem hkw (W'.inv_mem hw), ?_⟩, W'.mul_mem hkw (W'.inv_mem hw), ?_⟩
    ·
      have hkv : N.coord ((k : 𝔾) * v * (k : 𝔾)⁻¹) = N.coord v := by
        rw [N.coord_conj k hv, natAct_true]
        exact hg
      set z := v⁻¹ * ((k : 𝔾) * v * (k : 𝔾)⁻¹) with hzdef
      have hz : z ∈ Z := N.inv_mul_mem_of_coord_eq hv (N.conj_mem k hv) hkv.symm
      have hkve : (k : 𝔾) * v * (k : 𝔾)⁻¹ = v * z := by rw [hzdef, mul_inv_cancel_left]
      have hzw : z * ((k : 𝔾) * w * (k : 𝔾)⁻¹) = ((k : 𝔾) * w * (k : 𝔾)⁻¹) * z :=
        commute_of_commutator_eq_bot hZW' hz hkw
      have e1 : ⁅v, (k : 𝔾) * w * (k : 𝔾)⁻¹⁆ = (k : 𝔾) * ⁅v, w⁆ * (k : 𝔾)⁻¹ := by
        rw [ML3.conj_commutatorElement, hkve]
        simp only [commutatorElement_def]
        calc v * ((k : 𝔾) * w * (k : 𝔾)⁻¹) * v⁻¹ * ((k : 𝔾) * w * (k : 𝔾)⁻¹)⁻¹
            = v * (z * ((k : 𝔾) * w * (k : 𝔾)⁻¹)) * z⁻¹ * v⁻¹ *
                ((k : 𝔾) * w * (k : 𝔾)⁻¹)⁻¹ := by rw [hzw]; group
          _ = v * z * ((k : 𝔾) * w * (k : 𝔾)⁻¹) * (v * z)⁻¹ *
                ((k : 𝔾) * w * (k : 𝔾)⁻¹)⁻¹ := by group
      rw [ML3.comm_mul_right hHW' hWW' hv hkw (W'.inv_mem hw), hinv w hw, e1,
        hcent _ (hWW' (Subgroup.commutator_mem_commutator hv hw)) k, mul_inv_cancel]
    · rw [N'.coord_mul hkw (W'.inv_mem hw), N'.coord_conj k hw, N'.coord_inv hw, natAct_true,
        sub_eq_add_neg]
  have hwc : N'.coord w ∈ N'.img P := by rw [himg]; trivial
  obtain ⟨p, hpP, hpW, hpc⟩ := (N'.mem_img).mp hwc
  have hpw : p⁻¹ * w ∈ Z := N'.inv_mul_mem_of_coord_eq hpW hw hpc
  have hwP : w ∈ P := by
    have := P.mul_mem hpP (hZP _ hpw)
    rwa [mul_inv_cancel_left] at this
  exact hwP.2

theorem mem_of_commutator_mem_of_dual_layers {K Z W₁ W₂ H : Subgroup 𝔾}
    {ψ : ↥K →* ↥(StatedSL 3 F)} (hsurj : Function.Surjective ψ)
    (h₁ : IsSumOfNaturalModulesVia K W₁ Z ψ true 1)
    (h₂ : IsSumOfNaturalModulesVia K W₂ Z ψ true 1)
    (hHK : H ≤ Subgroup.centralizer (K : Set 𝔾)) (hW₁K : W₁ ≤ K) (hW₂K : W₂ ≤ K)
    (hab : ⁅W₁, W₁⁆ = ⊥) (hZ₁ : ⁅Z, W₁⁆ = ⊥) (hZ₂ : ⁅Z, W₂⁆ = ⊥) (hne : ⁅W₁, W₂⁆ ≠ ⊥)
    {y : 𝔾} (hy : y ∈ W₁ ⊔ W₂) (hyc : ∀ w ∈ W₁ ⊔ W₂, ⁅y, w⁆ ∈ H) : y ∈ Z := by
  classical
  set N₁ := NatSec.ofIsSum h₁ with hN₁
  set N₂ := NatSec.ofIsSum h₂ with hN₂
  set W := W₁ ⊔ W₂ with hWdef
  have hWK : W ≤ K := sup_le hW₁K hW₂K
  have hKW : K ≤ Subgroup.normalizer (W : Set 𝔾) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have key : ∀ g ∈ K, ∀ x ∈ W, g * x * g⁻¹ ∈ W := by
      intro g hg x hx
      have hmap : W.map (MulAut.conj g).toMonoidHom = W := by
        rw [hWdef, Subgroup.map_sup]
        congr 1
        · exact (Subgroup.mem_normalizer_iff_map_conj_eq.mp (h₁.1 hg))
        · exact (Subgroup.mem_normalizer_iff_map_conj_eq.mp (h₂.1 hg))
      rw [← hmap]
      exact ⟨x, hx, rfl⟩
    refine ⟨key k hk x, fun h => ?_⟩
    have := key k⁻¹ (K.inv_mem hk) _ h
    simpa [mul_assoc] using this
  have hcent : ∀ c ∈ H, ∀ g ∈ K, g * c * g⁻¹ = c := by
    intro c hc g hg
    rw [Subgroup.mem_centralizer_iff.mp (hHK hc) g hg, mul_inv_cancel_right]
  have hcomm : ∀ c ∈ H, ∀ g ∈ K, g * c = c * g := fun c hc g hg =>
    (Subgroup.mem_centralizer_iff.mp (hHK hc) g hg)
  have hZW : ∀ z ∈ Z, ∀ w ∈ W, z * w = w * z := by
    intro z hz w hw
    have hz' : z ∈ Subgroup.centralizer (W : Set 𝔾) := by
      rw [hWdef]
      have h1 : W₁ ≤ Subgroup.centralizer (Z : Set 𝔾) :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
          (by rw [Subgroup.commutator_comm]; exact hZ₁))
      have h2 : W₂ ≤ Subgroup.centralizer (Z : Set 𝔾) :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
          (by rw [Subgroup.commutator_comm]; exact hZ₂))
      exact Subgroup.le_centralizer_iff.mp (sup_le h1 h2) hz
    exact (Subgroup.mem_centralizer_iff.mp hz' w hw).symm
  have hEmul : ∀ a b, a ∈ W → b ∈ W → (∀ w ∈ W, ⁅a, w⁆ ∈ H) → (∀ w ∈ W, ⁅b, w⁆ ∈ H) →
      ∀ w ∈ W, ⁅a * b, w⁆ ∈ H := by
    intro a b ha hb hac hbc w hw
    have e : ⁅a * b, w⁆ = a * ⁅b, w⁆ * a⁻¹ * ⁅a, w⁆ := by
      simp only [commutatorElement_def]; group
    rw [e, hcent _ (hbc w hw) a (hWK ha)]
    exact H.mul_mem (hbc w hw) (hac w hw)
  have hEinv : ∀ a, a ∈ W → (∀ w ∈ W, ⁅a, w⁆ ∈ H) → ∀ w ∈ W, ⁅a⁻¹, w⁆ ∈ H := by
    intro a ha hac w hw
    have e : ⁅a⁻¹, w⁆ = a⁻¹ * ⁅a, w⁆⁻¹ * a := by
      simp only [commutatorElement_def]; group
    rw [e]
    have := hcent _ (H.inv_mem (hac w hw)) a⁻¹ (K.inv_mem (hWK ha))
    rw [inv_inv] at this
    rw [this]
    exact H.inv_mem (hac w hw)
  let E : Subgroup 𝔾 :=
    { carrier := {e | e ∈ W ∧ ∀ w ∈ W, ⁅e, w⁆ ∈ H}
      one_mem' := ⟨W.one_mem, fun w _ => by rw [commutatorElement_one_left]; exact H.one_mem⟩
      mul_mem' := fun {a b} ha hb => ⟨W.mul_mem ha.1 hb.1, hEmul a b ha.1 hb.1 ha.2 hb.2⟩
      inv_mem' := fun {a} ha => ⟨W.inv_mem ha.1, hEinv a ha.1 ha.2⟩ }
  have hEK : ∀ k : ↥K, ∀ e ∈ E, (k : 𝔾) * e * (k : 𝔾)⁻¹ ∈ E := by
    intro k e he
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hKW k.2) e).mp he.1, fun w hw => ?_⟩
    have hw' : (k : 𝔾)⁻¹ * w * (k : 𝔾) ∈ W := by
      have := (Subgroup.mem_normalizer_iff.mp (hKW (K.inv_mem k.2)) w).mp hw
      simpa using this
    have e1 : ⁅(k : 𝔾) * e * (k : 𝔾)⁻¹, w⁆ =
        (k : 𝔾) * ⁅e, (k : 𝔾)⁻¹ * w * (k : 𝔾)⁆ * (k : 𝔾)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e1, hcent _ (he.2 _ hw') k k.2]
    exact he.2 _ hw'
  have hZE : ∀ z ∈ Z, z ∈ E := by
    intro z hz
    refine ⟨(le_sup_left : W₁ ≤ W) (h₁.2.1 hz), fun w hw => ?_⟩
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (hZW z hz w hw)]
    exact H.one_mem
  by_contra hyZ
  apply hne
  refine commutator_eq_bot_of_dual_layers hsurj h₁ h₂ ?_ hHK hW₂K hZ₁ hZ₂
  have hyW : y ∈ ((W₁ : Set 𝔾) * (W₂ : Set 𝔾)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left W₁ W₂ (hW₂K.trans h₁.1)]
    exact hy
  obtain ⟨a, ha, b, hb, rfl⟩ := hyW
  have hyE : a * b ∈ E := ⟨hy, hyc⟩
  by_cases hbZ : b ∈ Z
  ·
    have haE : a ∈ E := by
      have := E.mul_mem hyE (E.inv_mem (hZE b hbZ))
      rwa [mul_inv_cancel_right] at this
    have haZ : a ∉ Z := fun h => hyZ (Z.mul_mem h hbZ)
    rw [Subgroup.commutator_le]
    intro v hv w hw
    obtain ⟨u, huE, -, huv⟩ := N₁.exists_inv_mul_mem_of_invariant hsurj hEK haE ha haZ hv
    have hvE : v ∈ E := by
      have := E.mul_mem huE (hZE _ huv)
      rwa [mul_inv_cancel_left] at this
    exact hvE.2 w ((le_sup_right : W₂ ≤ W) hw)
  ·
    let E₂ : Subgroup 𝔾 :=
      { carrier := {b' | b' ∈ W₂ ∧ ∃ a' ∈ W₁, a' * b' ∈ E}
        one_mem' := ⟨W₂.one_mem, 1, W₁.one_mem, by rw [mul_one]; exact E.one_mem⟩
        mul_mem' := fun {x x'} hx hx' => by
          obtain ⟨hxW, a₁, ha₁, hx1⟩ := hx
          obtain ⟨hxW', a₂, ha₂, hx2⟩ := hx'
          refine ⟨W₂.mul_mem hxW hxW', a₁ * (x * a₂ * x⁻¹),
            W₁.mul_mem ha₁ ((Subgroup.mem_normalizer_iff.mp (h₁.1 (hW₂K hxW)) a₂).mp ha₂), ?_⟩
          have e : a₁ * (x * a₂ * x⁻¹) * (x * x') = (a₁ * x) * (a₂ * x') := by group
          rw [e]
          exact E.mul_mem hx1 hx2
        inv_mem' := fun {x} hx => by
          obtain ⟨hxW, a₁, ha₁, hx1⟩ := hx
          refine ⟨W₂.inv_mem hxW, x⁻¹ * a₁⁻¹ * x, ?_, ?_⟩
          · have := (Subgroup.mem_normalizer_iff.mp (h₁.1 (hW₂K (W₂.inv_mem hxW))) a₁⁻¹).mp
              (W₁.inv_mem ha₁)
            simpa using this
          · have e : x⁻¹ * a₁⁻¹ * x * x⁻¹ = (a₁ * x)⁻¹ := by group
            rw [e]
            exact E.inv_mem hx1 }
    have hE₂K : ∀ k : ↥K, ∀ x ∈ E₂, (k : 𝔾) * x * (k : 𝔾)⁻¹ ∈ E₂ := by
      intro k x hx
      obtain ⟨hxW, a₁, ha₁, hx1⟩ := hx
      refine ⟨(Subgroup.mem_normalizer_iff.mp (h₂.1 k.2) x).mp hxW,
        (k : 𝔾) * a₁ * (k : 𝔾)⁻¹, (Subgroup.mem_normalizer_iff.mp (h₁.1 k.2) a₁).mp ha₁, ?_⟩
      have e : (k : 𝔾) * a₁ * (k : 𝔾)⁻¹ * ((k : 𝔾) * x * (k : 𝔾)⁻¹) =
          (k : 𝔾) * (a₁ * x) * (k : 𝔾)⁻¹ := by group
      rw [e]
      exact hEK k _ hx1
    rw [Subgroup.commutator_le]
    intro v hv w hw
    obtain ⟨b', hb'E, -, hb'w⟩ :=
      N₂.exists_inv_mul_mem_of_invariant hsurj hE₂K ⟨hb, a, ha, hyE⟩ hb hbZ hw
    obtain ⟨hb'W, a', ha', hab'⟩ := hb'E
    set z := b'⁻¹ * w with hz
    have hwe : w = b' * z := by rw [hz, mul_inv_cancel_left]
    have hzv : z * v = v * z := hZW z hb'w v ((le_sup_left : W₁ ≤ W) hv)
    have hzb : z * b' = b' * z := hZW z hb'w b' ((le_sup_right : W₂ ≤ W) hb'W)
    have hva : v * a' = a' * v :=
      commute_of_commutator_eq_bot hab hv ha'
    have hc := hab'.2 v ((le_sup_left : W₁ ≤ W) hv)
    have e1 : ⁅v, w⁆ = a'⁻¹ * ⁅a' * b', v⁆⁻¹ * a' := by
      rw [hwe]
      simp only [commutatorElement_def]
      calc v * (b' * z) * v⁻¹ * (b' * z)⁻¹ = v * b' * (z * v⁻¹) * z⁻¹ * b'⁻¹ := by group
        _ = v * b' * (v⁻¹ * z) * z⁻¹ * b'⁻¹ := by
            rw [show z * v⁻¹ = v⁻¹ * z from (show Commute z v from hzv).inv_right.eq]
        _ = a'⁻¹ * (a' * v) * b' * v⁻¹ * b'⁻¹ := by group
        _ = a'⁻¹ * (v * a') * b' * v⁻¹ * b'⁻¹ := by rw [hva]
        _ = a'⁻¹ * (a' * b' * v * (a' * b')⁻¹ * v⁻¹)⁻¹ * a' := by group
    rw [e1]
    have := hcent _ (H.inv_mem hc) a'⁻¹ (K.inv_mem (hW₁K ha'))
    rw [inv_inv] at this
    rw [this]
    exact H.inv_mem hc


theorem frattiniIn_le_centralizer_of {V H : Subgroup 𝔾} [Finite V] (hV : IsPGroup 2 V) {y : 𝔾}
    (hHV : H ≤ V) (hHc : ∀ c ∈ H, ∀ v ∈ V, c * v = v * c) (hH2 : ∀ c ∈ H, c ^ 2 = 1)
    (hy : ∀ x ∈ V, ⁅y, x⁆ ∈ H) : frattiniIn V ≤ Subgroup.centralizer ({y} : Set 𝔾) := by
  have hc : ∀ w ∈ V, ∀ w' ∈ V, w * ⁅y, w'⁆ = ⁅y, w'⁆ * w := fun w hw w' hw' =>
    (hHc _ (hy w' hw') w hw).symm
  set f := S46.commHomOf V y hc with hf
  have hfa : ∀ v : ↥V, f v = ⁅y, (v : 𝔾)⁆ := fun v => rfl
  have hker : ∀ v : ↥V, f v = 1 → (v : 𝔾) ∈ Subgroup.centralizer ({y} : Set 𝔾) := by
    intro v hv
    rw [hfa, commutatorElement_eq_one_iff_mul_comm] at hv
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hv.symm
  refine (S45.frattiniIn_le_of (N := V ⊓ Subgroup.centralizer ({y} : Set 𝔾)) hV ?_ ?_).trans
    inf_le_right
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    refine ⟨Subgroup.commutator_le_self _ (Subgroup.commutator_mem_commutator ha hb), ?_⟩
    · have hmem : ⁅a, b⁆ ∈ V := Subgroup.commutator_le_self _ (Subgroup.commutator_mem_commutator ha hb)
      have e : (⟨⁅a, b⁆, hmem⟩ : ↥V) = ⁅(⟨a, ha⟩ : ↥V), ⟨b, hb⟩⁆ := rfl
      refine hker ⟨⁅a, b⁆, hmem⟩ ?_
      rw [e, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, hfa, hfa]
      exact hHc _ (hy a ha) _ (hHV (hy b hb))
  · intro v hv
    refine ⟨pow_mem hv 2, ?_⟩
    have e : (⟨v ^ 2, pow_mem hv 2⟩ : ↥V) = (⟨v, hv⟩ : ↥V) ^ 2 := rfl
    refine hker ⟨v ^ 2, pow_mem hv 2⟩ ?_
    rw [e, map_pow, hfa]
    exact hH2 _ (hy v hv)

end Generic

end CFSG.Quasithin.MS93.S45I

namespace CFSG.Quasithin.MS93.S45

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix Pointwise

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]

namespace Ctx

variable {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx M T L φ)
include c

variable {p p' : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ}

theorem mem_frattiniIn_of_commutator_mem (h14 : MS14AS) (hSQ : SQTKQuot) (hZV : c.HZV)
    (hQ4 : c.HQ4) (hQ2b : c.HQ2b) (hp : IsGoodPath _ p N) (hp' : IsGoodPath _ p' N) {a : ℕ}
    (ha : Even a) (h34 : 34 ≤ a) (haN : a + 30 ≤ N) (hpp' : ∀ i, i ≤ a + 2 → p' i = p i)
    (hU1 : Usup (puAmalgam c.hyp.le) (p (a + 2)) (p' (a + 3)) ≠ Usup _ (p (a + 2)) (p (a + 1)))
    (hU3 : Usup (puAmalgam c.hyp.le) (p (a + 2)) (p' (a + 3)) ⊓ Usup _ (p (a + 2)) (p (a + 1)) ≠
      Usup _ (p (a + 2)) (p (a + 3)) ⊓ Usup _ (p (a + 2)) (p (a + 1)))
    {y : (puAmalgam c.hyp.le).Universal}
    (hyV : y ∈ ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆)
    (hyc : ∀ x ∈ ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆,
      ⁅y, x⁆ ∈ ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ ⊓
        Subgroup.centralizer (Ltil c.hyp.le L (p a) : Set (puAmalgam c.hyp.le).Universal)) :
    y ∈ frattiniIn ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ := by
  have h := c.hyp
  have h20 := h.hyp20
  obtain ⟨hHl, -, hΦ, hCW, -⟩ := hQ2b p p' N hp hp' a ha h34 haN hpp' hU1 hU3
  have hα := c.isMVtx_of_isGoodPath hp (k := a) (by omega) ha
  have hγ := c.isMVtx_of_isGoodPath hp (k := a + 2) (by omega) (ha.add even_two)
  have hμ := c.isMVtx_of_isGoodPath hp (k := a + 4) (by omega) (ha.add (by decide))
  have hμ' := c.isMVtx_of_isGoodPath hp' (k := a + 4) (by omega) (ha.add (by decide))
  have hpa : p' a = p a := hpp' a (by omega)
  have hd2 : (puAmalgam h.le).treeGraph.dist (p a) (p (a + 2)) = 2 := by
    rw [hp.dist_eq' (i := a) (j := a + 2) (by omega) (by omega)]; omega
  obtain ⟨ψ, hψs, hψ, hT⟩ := c.exists_coord_qv hα (hp.adj a (by omega))
  obtain ⟨hsup2, hinf2, h₁m, h₂m⟩ :=
    c.mid_layer h14 hSQ hZV hQ4 hp ha (by omega) (by omega) hp' hpp' hU1 hU3 hψs hψ hT
  set Qα := Qv (puAmalgam h.le) (p a) with hQα
  set Lt := Ltil h.le L (p a) with hLt
  set V := ⁅Qα, Lt⁆ with hV
  set K := stab (puAmalgam h.le) (p a) with hK
  set Z := ZM (puAmalgam h.le) (p a) with hZ
  set Vc := Vcirc h.le L (p a) with hVc
  set Vh := Vc ⊔ Z with hVh
  set Wh := whv h (p a) (p (a + 2)) with hWh
  set W₁ := conjCl K (ZM _ (p (a + 4))) ⊔ Vh with hW₁
  set W₂ := conjCl K (ZM _ (p' (a + 4))) ⊔ Vh with hW₂
  set H := V ⊓ Subgroup.centralizer (Lt : Set (puAmalgam h.le).Universal) with hH
  have hQs : Qα ≤ K := qv_le_stab _ _
  have hKQ : K ≤ Subgroup.normalizer (Qα : Set _) := stab_le_normalizer_qv _ _
  have hLs : Lt ≤ K := ltil_le_stab h _
  have hKV : K ≤ Subgroup.normalizer (V : Set _) :=
    le_normalizer_commutator hKQ (stab_le_normalizer_ltil h _)
  have hVQ : V ≤ Qα := Subgroup.le_normalizer_iff_commutator_le_left.mp (hLs.trans hKQ)
  have hVK : V ≤ K := hVQ.trans hQs
  have hKZ : K ≤ Subgroup.normalizer (Z : Set _) := stab_le_normalizer_zm _ _
  have hKVc : K ≤ Subgroup.normalizer (Vc : Set _) := c.stab_le_normalizer_vcirc _
  have hVvQ : Vv (puAmalgam h.le) (p a) ≤ Qα := c.vv_le_qv' hα
  have hVcV : Vc ≤ V := Subgroup.commutator_mono hVvQ le_rfl
  have hWhC : Wh ≤ Subgroup.centralizer (Vh : Set _) :=
    (c.whv_le_centralizer_vv hγ hd2).trans (Subgroup.centralizer_le (c.vhat_le_vv hα))
  have hVhWh : Vh ≤ Wh := c.vhat_le_whv' hZV hp ha (by omega) (by omega)
  have hW₁Wh : W₁ ≤ Wh := le_sup_left.trans hsup2.le
  have hW₂Wh : W₂ ≤ Wh := le_sup_right.trans hsup2.le
  have hWhs : Wh ≤ K := (c.whv_le_qv_of_dist hγ hd2 (by simp)).trans hQs
  have hZc := zloc_le_centralizer_stab h c.full hα
  have hHZl : Hloc h.le L (p a) ≤ Zloc h.le L (p a) :=
    (Subgroup.commutator_mono (c.vcirc_le_vv _) le_rfl).trans (c.commutator_vv_qv_le_zloc hα)
  have hHK : H ≤ Subgroup.centralizer (K : Set _) := hHl.trans (hHZl.trans hZc)
  have hHVc : Hloc h.le L (p a) ≤ Vc :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hQs.trans hKVc)
  have hH2 : ∀ x ∈ H, x ^ 2 = 1 := fun x hx =>
    c.sq_eq_one_of_mem_vhat hZV hp ha h34 (by omega) ((le_sup_left : Vc ≤ Vh) (hHVc (hHl hx)))
  have hHc : ∀ x ∈ H, ∀ g ∈ K, x * g = g * x := fun x hx g hg =>
    (Subgroup.mem_centralizer_iff.mp (hHK hx) g hg).symm
  obtain ⟨hV2, hVf⟩ := c.isPGroup_commutator_qv_ltil hα
  have hyΦ := S45I.frattiniIn_le_centralizer_of hV2 (y := y) inf_le_left
    (fun x hx v hv => hHc x hx v (hVK hv)) hH2 fun x hx => hyc x hx
  have hyC : y ∈ V ⊓ Subgroup.centralizer (Vc : Set _) := by
    refine ⟨hyV, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    rw [← hΦ] at hv
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hyΦ hv))
  have hyW : y ∈ Wh := hCW hyC
  have hF9 := c.inf_whv_sup_vhat h14 hSQ hZV hQ4 hp hp' ha h34 haN hpp' hU1 hU3
  have hyWc : ∀ w ∈ W₁ ⊔ W₂, ⁅y, w⁆ ∈ H := by
    intro w hw
    rw [hsup2] at hw
    have hwmem : w ∈ ((V ⊓ Wh ⊔ Vh : Subgroup _) : Set _) := hF9.ge hw
    rw [Subgroup.coe_mul_of_left_le_normalizer_right (V ⊓ Wh) Vh
      (inf_le_left.trans (hVK.trans (le_normalizer_sup hKVc hKZ)))] at hwmem
    obtain ⟨v, hv, u, hu, rfl⟩ := hwmem
    have hyu : y * u = u * y := (Subgroup.mem_centralizer_iff.mp (hWhC hyW) u hu).symm
    have e : ⁅y, v * u⁆ = ⁅y, v⁆ := by
      simp only [commutatorElement_def]
      calc y * (v * u) * y⁻¹ * (v * u)⁻¹ = y * v * (u * y⁻¹) * u⁻¹ * v⁻¹ := by group
        _ = y * v * (y⁻¹ * u) * u⁻¹ * v⁻¹ := by
            rw [show u * y⁻¹ = y⁻¹ * u from ((show Commute y u from hyu).inv_left).eq.symm]
        _ = y * v * y⁻¹ * v⁻¹ := by group
    rw [e]
    exact hyc v (Subgroup.mem_inf.mp hv).1
  have hVhab : ⁅Vh, Vh⁆ = ⊥ :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr (hVhWh.trans hWhC)
  have hZQ4 : ∀ k ∈ K, ⁅ZM (puAmalgam h.le) (p (a + 4)),
      (ZM (puAmalgam h.le) (p (a + 4))).map (MulAut.conj k).toMonoidHom⁆ = ⊥ := by
    intro k hk
    rw [← zm_smul, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact (zm_le_centralizer_qv _ h20 hμ).trans
      (Subgroup.centralizer_le (hQ4 p N hp a ha (by omega) (by omega) k hk))
  have hZQ4' : ∀ k ∈ K, ⁅ZM (puAmalgam h.le) (p' (a + 4)),
      (ZM (puAmalgam h.le) (p' (a + 4))).map (MulAut.conj k).toMonoidHom⁆ = ⊥ := by
    intro k hk
    rw [← zm_smul, Subgroup.commutator_eq_bot_iff_le_centralizer]
    have hk' : k ∈ stab (puAmalgam h.le) (p' a) := by rw [hpa]; exact hk
    exact (zm_le_centralizer_qv _ h20 hμ').trans
      (Subgroup.centralizer_le (hQ4 p' N hp' a ha (by omega) (by omega) k hk'))
  have hpa2 : p' (a + 2) = p (a + 2) := hpp' (a + 2) le_rfl
  have hZ₁W : ZM (puAmalgam h.le) (p (a + 4)) ≤ Wh :=
    c.zm_le_whv_right hZV hp ha (by omega) (by omega)
  have hZ₂W : ZM (puAmalgam h.le) (p' (a + 4)) ≤ Wh := by
    have := c.zm_le_whv_right hZV hp' ha (by omega) (by omega)
    rwa [hpa, hpa2] at this
  have hab₁ : ⁅W₁, W₁⁆ = ⊥ := commutator_conjCl_sup_eq_bot (hZ₁W.trans hWhs) hZQ4 hVhab
    ((Subgroup.commutator_eq_bot_iff_le_centralizer).mpr ((le_sup_left.trans hW₁Wh).trans hWhC))
  have hab₂ : ⁅W₂, W₂⁆ = ⊥ := commutator_conjCl_sup_eq_bot (hZ₂W.trans hWhs) hZQ4' hVhab
    ((Subgroup.commutator_eq_bot_iff_le_centralizer).mpr ((le_sup_left.trans hW₂Wh).trans hWhC))
  have hZ₄W : ZM (puAmalgam h.le) (p (a - 4)) ≤ Wh := by
    have ha2 : Even (a - 2) := (Nat.even_sub (by omega)).mpr (iff_of_true ha (by decide))
    have hz := c.zm_le_vhat_left' hZV hp (a := a - 2) ha2 (by omega) (by omega)
    rw [show a - 2 - 2 = a - 4 by omega] at hz
    have e := c.whv_eq_of_isGoodPath hp (a := a) ha (by omega) (by omega)
    rw [hWh, e]
    exact hz.trans c.vhat_le_whv_self
  have hR : ⁅ZM (puAmalgam h.le) (p (a - 4)), ZM _ (p (a + 4))⁆ ≠ ⊥ := by
    have := c.critR_ne_bot_of_isGoodPath hp (a := a - 2)
      ((Nat.even_sub (by omega)).mpr (iff_of_true ha (by decide))) (by omega) (by omega)
    rwa [show a - 2 - 2 = a - 4 by omega, show a - 2 + 6 = a + 4 by omega] at this
  have hne : ⁅W₁, W₂⁆ ≠ ⊥ := by
    intro h0
    apply hR
    have hWab : ⁅Wh, Wh⁆ = ⊥ := by
      rw [← hsup2, eq_bot_iff]
      have hn : ∀ K : Subgroup (puAmalgam h.le).Universal,
          K ≤ Subgroup.normalizer ((⊥ : Subgroup (puAmalgam h.le).Universal) : Set _) :=
        fun K g _ => Subgroup.mem_normalizer_iff.mpr fun x => by simp
      refine commutator_sup_left_le (hn _) (hn _) ?_ ?_
      · rw [Subgroup.commutator_comm]
        refine commutator_sup_left_le (hn _) (hn _) ?_ ?_
        · rw [hab₁]
        · rw [Subgroup.commutator_comm, h0]
      · rw [Subgroup.commutator_comm]
        refine commutator_sup_left_le (hn _) (hn _) ?_ ?_
        · rw [h0]
        · rw [hab₂]
    exact le_bot_iff.mp ((Subgroup.commutator_mono hZ₄W hZ₁W).trans hWab.le)
  have hZ₁ : ⁅Vh, W₁⁆ = ⊥ := (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr
    (Subgroup.le_centralizer_iff.mp (hW₁Wh.trans hWhC))
  have hZ₂ : ⁅Vh, W₂⁆ = ⊥ := (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr
    (Subgroup.le_centralizer_iff.mp (hW₂Wh.trans hWhC))
  have hyVh : y ∈ Vh := S45I.mem_of_commutator_mem_of_dual_layers hψs h₁m h₂m hHK
    (hW₁Wh.trans hWhs) (hW₂Wh.trans hWhs) hab₁ hZ₁ hZ₂ hne (hsup2.symm ▸ hyW) hyWc
  have hUZ : Uloc h.le L (p a) ≤ Z := uloc_le_zm h c.full hα
  have hZQ : Z ≤ Qα := zm_le_qv_of_dist_lt _ hα (by simp [c.b8])
  have hUL : ⁅Uloc h.le L (p a), Lt⁆ = Uloc h.le L (p a) := c.commutator_uloc_ltil hα
  have hUVc : Uloc h.le L (p a) ≤ Vc := by
    rw [← hUL]
    exact Subgroup.commutator_mono (hUZ.trans (le_sup_right.trans (c.vhat_le_vv hα))) le_rfl
  have hUV : Uloc h.le L (p a) ≤ V := hUVc.trans hVcV
  have hUn : Uloc h.le L (p a) ≤ Subgroup.normalizer (Zloc h.le L (p a) : Set _) :=
    (hUZ.trans (hZQ.trans hQs)).trans (c.stab_le_normalizer_of_le_centralizer hZc)
  have hC1 : Zloc h.le L (p a) ⊓ V ≤ Hloc h.le L (p a) := by
    intro x hx
    refine hHl ⟨hx.2, ?_⟩
    rw [c.zloc_eq_zm_inf_centralizer hα] at hx
    exact hx.1.2
  have hVZ : Z ⊓ V ≤ Uloc h.le L (p a) ⊔ Hloc h.le L (p a) := by
    have e := zm_eq_uloc_sup_zloc h c.full hα
    calc Z ⊓ V = (Uloc h.le L (p a) ⊔ Zloc h.le L (p a)) ⊓ V := by rw [hZ, e]
      _ = Uloc h.le L (p a) ⊔ (Zloc h.le L (p a) ⊓ V) := sup_inf_eq_of_le hUV hUn
      _ ≤ Uloc h.le L (p a) ⊔ Hloc h.le L (p a) := sup_le_sup_left hC1 _
  have hVVh : (Vc ⊔ Z) ⊓ V ≤ Vc := by
    rw [sup_inf_eq_of_le hVcV (hVcV.trans (hVQ.trans (hQs.trans hKZ)))]
    exact sup_le le_rfl (hVZ.trans (sup_le hUVc hHVc))
  rw [hΦ]
  exact hVVh ⟨hyVh, hyV⟩

end Ctx

end CFSG.Quasithin.MS93.S45
