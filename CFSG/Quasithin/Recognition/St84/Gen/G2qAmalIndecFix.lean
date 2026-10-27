module

public import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalBorel

import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalIndecTorus2
import CFSG.Quasithin.Recognition.St84.Gen.G2qAmalIndecSplit
import CFSG.Quasithin.Recognition.St84.Gen.L2SectionHall
import CFSG.Quasithin.EmptyFaithful.S1422Center
import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Counting
import CFSG.CGT.PushingUpLit.Glue.NaturalIrred

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.Open CFSG.Quasithin CFSG.Quasithin.F1 CFSG.QuasithinUnique
open CFSG.LieType.BorelTits CFSG.CGT.Timmesfeld75
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {f : ℕ}

private theorem indecFix_commutator_mem_centerOf {X : Subgroup G} (hX : IsSpecialPGroup 2 ↥X)
    {x y : G} (hx : x ∈ X) (hy : y ∈ X) : ⁅x, y⁆ ∈ centerOf X := by
  rcases hX.2 with ⟨hcomm, -⟩ | ⟨hcomm, -, -⟩
  · have h : x * y = y * x :=
      congrArg Subtype.val (hcomm.is_comm.comm (⟨x, hx⟩ : ↥X) ⟨y, hy⟩)
    rw [commutatorElement_eq_one_iff_mul_comm.mpr h]
    exact one_mem _
  · let a : ↥X := ⟨x, hx⟩
    let b : ↥X := ⟨y, hy⟩
    have hmem : ⁅a, b⁆ ∈ Subgroup.center ↥X := by
      rw [← hcomm, commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    refine mem_centerOf_of_forall_comm (⁅a, b⁆).2 fun z hz => ?_
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hmem (⟨z, hz⟩ : ↥X))

private theorem indecFix_exists_borel_mulVec {F : Type} [Field F] {u v : Fin 2 → F}
    (hu : u 1 ≠ 0) (hv : v 1 ≠ 0) :
    ∃ g : SL(2, F), g ∈ borel F ∧ (g : Matrix (Fin 2) (Fin 2) F) *ᵥ u = v := by
  have hd : u 1 / v 1 ≠ 0 := div_ne_zero hu hv
  refine ⟨⟨!![u 1 / v 1, (v 0 - u 1 / v 1 * u 0) / u 1; 0, (u 1 / v 1)⁻¹], ?_⟩, ?_, ?_⟩
  · simp only [Matrix.det_fin_two_of, mul_zero, sub_zero]
    exact mul_inv_cancel₀ hd
  · exact mem_borel_iff.mpr (by simp)
  · funext i
    fin_cases i
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      field_simp
      ring
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      field_simp

private theorem indecFix_conj_mem_commutator {L : Subgroup G} {l k : G} (hl : l ∈ L)
    (hk : k ∈ ⁅pCoreOf 2 L, L⁆) : l * k * l⁻¹ ∈ ⁅pCoreOf 2 L, L⁆ := by
  have hkQ : k ∈ pCoreOf 2 L := commutator_pCoreOf_le_pCoreOf L hk
  have h : ⁅l, k⁆ ∈ ⁅pCoreOf 2 L, L⁆ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hl hkQ
  rw [show l * k * l⁻¹ = ⁅l, k⁆ * k by rw [commutatorElement_def]; group]
  exact mul_mem h hk

private theorem indecFix_le_left (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2)) : S ≤ L1 := by
  obtain ⟨c⟩ := hD.exists_coordRight hH h2
  exact hD.le_left hH c.one_le_f h1

private theorem indecFix_le_right (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h2 : IsL2Quot f (oTwoQuot ↥L2)) : S ≤ L2 := by
  obtain ⟨c⟩ := hD.exists_coordRight hH h2
  exact hD.le_right hH c.one_le_f h2

private theorem indecFix_comm_left (hD : G2qLocalData L1 L2 S f) {z y : G}
    (hz : z ∈ centerOf (pCoreOf 2 L1)) (hy : y ∈ L1) : y * z = z * y := by
  rw [hD.center_left] at hz
  exact mul_comm_of_mem_centerOf hz hy

private theorem indecFix_exists_mul_left (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2)) {s : G} (hs : s ∈ S) :
    ∃ x ∈ pCoreOf 2 L1, ∃ a ∈ pCoreOf 2 L2, s = x * a := by
  have hnorm : pCoreOf 2 L2 ≤ Subgroup.normalizer (pCoreOf 2 L1 : Set G) :=
    (hH.pCoreOf_le_right.trans (indecFix_le_left hH hD h1 h2)).trans
      (le_normalizer_pCoreOf 2 L1)
  rw [← hD.pCoreOf_left_sup_right hH h1 h2] at hs
  exact (mem_sup_iff_exists_mul_of_normalizes hnorm).mp hs

private theorem indecFix_exists_mul_right (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2)) {s : G} (hs : s ∈ S) :
    ∃ a ∈ pCoreOf 2 L2, ∃ x ∈ pCoreOf 2 L1, s = a * x := by
  have hnorm : pCoreOf 2 L1 ≤ Subgroup.normalizer (pCoreOf 2 L2 : Set G) :=
    (hH.pCoreOf_le_left.trans (indecFix_le_right hH hD h2)).trans (le_normalizer_pCoreOf 2 L2)
  rw [← hD.pCoreOf_left_sup_right hH h1 h2, sup_comm] at hs
  exact (mem_sup_iff_exists_mul_of_normalizes hnorm).mp hs

private theorem indecFix_exists_commutator_mul (c : G2qCoordRight L2 S f) {a : G}
    (ha : a ∈ pCoreOf 2 L2) : ∃ r ∈ ⁅pCoreOf 2 L2, L2⁆, ∃ w ∈ c.W, a = r * w := by
  have hnorm : c.W ≤ Subgroup.normalizer ((⁅pCoreOf 2 L2, L2⁆ : Subgroup G) : Set G) :=
    le_normalizer_of_forall_conj_mem_of_mem fun l hl k hk =>
      indecFix_conj_mem_commutator (pCoreOf_le 2 L2 (c.le_pCoreOf hl)) hk
  rw [← c.commutator_sup_W] at ha
  exact (mem_sup_iff_exists_mul_of_normalizes hnorm).mp ha

section Center

variable {F : Type} [Field F] {α : ↥L2 →* SL(2, F)}
  {β : ↥(centerOf (pCoreOf 2 L2)) →* Multiplicative (Fin 2 → F)}

private theorem indecFix_snd_of_mem_left (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2))
    (hα : Function.Surjective α) (hmem : ∀ x : ↥L2, (x : G) ∈ S ↔ α x ∈ utri F)
    (hβe : ∀ ℓ : ↥L2, ∀ u v : ↥(centerOf (pCoreOf 2 L2)), (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (β v) =
        (α ℓ : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u)))
    {z : G} (hz : z ∈ centerOf (pCoreOf 2 L1)) : natSecVec β z 1 = 0 := by
  have hzZ := hD.centerOf_pCoreOf_left_le_right hH h1 h2 hz
  apply mulVec_apply_one_eq_zero hα hmem
  intro x hx
  have hxz : (x : G) * z * (x : G)⁻¹ = z := by
    rw [indecFix_comm_left hD hz (indecFix_le_left hH hD h1 h2 hx), mul_inv_cancel_right]
  have key := natSecVec_conj hβe x hzZ (by rw [hxz]; exact hzZ)
  rw [hxz] at key
  exact key.symm

private theorem indecFix_mem_left_of_snd (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2)) [Fintype F]
    (hF : Nat.card F = 2 ^ f) (hα : Function.Surjective α)
    (hmem : ∀ x : ↥L2, (x : G) ∈ S ↔ α x ∈ utri F)
    (hβk : β.ker = (⊥ : Subgroup G).subgroupOf (centerOf (pCoreOf 2 L2)))
    (hβe : ∀ ℓ : ↥L2, ∀ u v : ↥(centerOf (pCoreOf 2 L2)), (v : G) = ℓ * u * ℓ⁻¹ →
      Multiplicative.toAdd (β v) =
        (α ℓ : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (β u)))
    {z : G} (hz : z ∈ centerOf (pCoreOf 2 L2)) (hz1 : natSecVec β z 1 = 0) :
    z ∈ centerOf (pCoreOf 2 L1) := by
  have hZ12 := hD.centerOf_pCoreOf_left_le_right hH h1 h2
  have hsnd := fun {y : G} (hy : y ∈ centerOf (pCoreOf 2 L1)) =>
    indecFix_snd_of_mem_left hH hD h1 h2 hα hmem hβe hy
  have hinj : ∀ {u v : G}, u ∈ centerOf (pCoreOf 2 L2) → v ∈ centerOf (pCoreOf 2 L2) →
      natSecVec β u = natSecVec β v → u = v := by
    intro u v hu hv h
    have h' := (natSecVec_eq_iff hβk hu hv).mp h
    rwa [Subgroup.mem_bot, inv_mul_eq_one] at h'
  let φ : ↥(centerOf (pCoreOf 2 L1)) → F := fun y => natSecVec β (y : G) 0
  have hφ : Function.Injective φ := by
    intro y y' h
    refine Subtype.ext (hinj (hZ12 y.2) (hZ12 y'.2) ?_)
    funext i
    fin_cases i
    · exact h
    · exact (hsnd y.2).trans (hsnd y'.2).symm
  have hcard : Nat.card F ≤ Nat.card ↥(centerOf (pCoreOf 2 L1)) := by
    rw [hF, card_centerOf_eq_card_center, hD.special_left.2.2]
  obtain ⟨y, hy⟩ := (hφ.bijective_of_nat_card_le hcard).2 (natSecVec β z 0)
  have hyz : (y : G) = z := by
    refine hinj (hZ12 y.2) hz ?_
    funext i
    fin_cases i
    · exact hy
    · exact (hsnd y.2).trans hz1.symm
  rw [← hyz]
  exact y.2

end Center

private theorem indecFix_mem_left_of_fix (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2)) {z : G}
    (hz : z ∈ centerOf (pCoreOf 2 L2)) (hfix : ∀ s ∈ S, s * z * s⁻¹ = z) :
    z ∈ centerOf (pCoreOf 2 L1) := by
  obtain ⟨c⟩ := hD.exists_coordRight hH h2
  letI := c.field
  letI := c.fintype
  obtain ⟨β, -, hβk, hβe⟩ := c.nat
  refine indecFix_mem_left_of_snd hH hD h1 h2 c.card c.surj c.memS hβk hβe hz ?_
  apply mulVec_apply_one_eq_zero c.surj c.memS
  intro x hx
  have key := natSecVec_conj hβe x hz (by rw [hfix x hx]; exact hz)
  rw [hfix x hx] at key
  exact key.symm

private theorem indecFix_commutator_inf_mem (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2)) {s y : G} (hs : s ∈ S)
    (hy1 : y ∈ pCoreOf 2 L1) (hy2 : y ∈ pCoreOf 2 L2) : ⁅s, y⁆ ∈ centerOf (pCoreOf 2 L2) := by
  obtain ⟨x, hx, a, ha, rfl⟩ := indecFix_exists_mul_left hH hD h1 h2 hs
  have hxL2 : x ∈ L2 := indecFix_le_right hH hD h2 (hH.pCoreOf_le_left hx)
  rw [show ⁅x * a, y⁆ = x * ⁅a, y⁆ * x⁻¹ * ⁅x, y⁆ by simp only [commutatorElement_def]; group]
  exact mul_mem (mem_centerOf_conj_of_mem_normalizer (le_normalizer_pCoreOf 2 L2 hxL2)
    (indecFix_commutator_mem_centerOf hD.special_right ha hy2))
    (hD.centerOf_pCoreOf_left_le_right hH h1 h2 (hD.commutator_mem_centerOf_left hx hy1))

private theorem indecFix_commutator_W_mem (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2))
    (c : G2qCoordRight L2 S f) {w y : G} (hw : w ∈ c.W) (hy1 : y ∈ pCoreOf 2 L1)
    (hy2 : y ∈ pCoreOf 2 L2) : ⁅w, y⁆ ∈ centerOf (pCoreOf 2 L1) := by
  have hwQ := c.le_pCoreOf hw
  have hwy : ⁅w, y⁆ ∈ centerOf (pCoreOf 2 L2) :=
    c.commutator_le (Subgroup.commutator_mem_commutator hw (pCoreOf_le 2 L2 hy2))
  refine indecFix_mem_left_of_fix hH hD h1 h2 hwy fun s hs => ?_
  have hsL2 : s ∈ L2 := indecFix_le_right hH hD h2 hs
  have hz1 : ⁅s, w⁆ ∈ centerOf (pCoreOf 2 L2) := c.commutator_le (by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hsL2 hw)
  have hz2 := indecFix_commutator_inf_mem hH hD h1 h2 hs hy1 hy2
  have hz2Q : ⁅s, y⁆ ∈ pCoreOf 2 L2 :=
    (show centerOf (pCoreOf 2 L2) ≤ pCoreOf 2 L2 from inf_le_left) hz2
  calc s * ⁅w, y⁆ * s⁻¹ = ⁅⁅s, w⁆ * w, ⁅s, y⁆ * y⁆ := by simp only [commutatorElement_def]; group
    _ = ⁅w, ⁅s, y⁆ * y⁆ := commutator_mul_left_eq_of_mem_centerOf hz1 hwQ (mul_mem hz2Q hy2)
    _ = ⁅w, y⁆ := commutator_mul_right_eq_of_mem_centerOf hz2 hwQ hy2

private theorem indecFix_commutator_mem_inf (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2))
    (hZR : centerOf (pCoreOf 2 L2) ≤ ⁅pCoreOf 2 L2, L2⁆) {s x : G} (hs : s ∈ S)
    (hx : x ∈ pCoreOf 2 L1) : ⁅s, x⁆ ∈ ⁅pCoreOf 2 L2, L2⁆ ⊓ pCoreOf 2 L1 := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · obtain ⟨a, ha, y, hy, rfl⟩ := indecFix_exists_mul_right hH hD h1 h2 hs
    have hxL2 : x ∈ L2 := indecFix_le_right hH hD h2 (hH.pCoreOf_le_left hx)
    have hyx := hD.centerOf_pCoreOf_left_le_right hH h1 h2 (hD.commutator_mem_centerOf_left hy hx)
    rw [show ⁅a * y, x⁆ = a * ⁅y, x⁆ * a⁻¹ * ⁅a, x⁆ by simp only [commutatorElement_def]; group]
    exact mul_mem (hZR (mem_centerOf_conj_of_mem_normalizer
      (le_normalizer_pCoreOf 2 L2 (pCoreOf_le 2 L2 ha)) hyx))
      (Subgroup.commutator_mem_commutator ha hxL2)
  · rw [commutatorElement_def]
    exact mul_mem (conj_mem_pCoreOf_of_mem (indecFix_le_left hH hD h1 h2 hs) hx) (inv_mem hx)

theorem G2qLocalData.commutator_mem_centerOf_left_of_mem_inf (hH : Hyp111 L1 L2 S)
    (hD : G2qLocalData L1 L2 S f) (h1 : IsL2Quot f (oTwoQuot ↥L1))
    (h2 : IsL2Quot f (oTwoQuot ↥L2))
    (hRab : ∀ a ∈ ⁅pCoreOf 2 L2, L2⁆, ∀ b ∈ ⁅pCoreOf 2 L2, L2⁆, a * b = b * a) :
    ∀ s ∈ S, ∀ y ∈ ⁅pCoreOf 2 L2, L2⁆ ⊓ pCoreOf 2 L1, ⁅s, y⁆ ∈ centerOf (pCoreOf 2 L1) := by
  intro s hs y hy
  obtain ⟨hyR, hy1⟩ := Subgroup.mem_inf.mp hy
  have hy2 : y ∈ pCoreOf 2 L2 := commutator_pCoreOf_le_pCoreOf L2 hyR
  obtain ⟨c⟩ := hD.exists_coordRight hH h2
  obtain ⟨x, hx, a, ha, rfl⟩ := indecFix_exists_mul_left hH hD h1 h2 hs
  obtain ⟨r, hr, w, hw, rfl⟩ := indecFix_exists_commutator_mul c ha
  have hwy := indecFix_commutator_W_mem hH hD h1 h2 c hw hy1 hy2
  have hrL1 : r ∈ L1 := indecFix_le_left hH hD h1 h2
    (hH.pCoreOf_le_right (commutator_pCoreOf_le_pCoreOf L2 hr))
  have hr' : r * ⁅w, y⁆ * r⁻¹ = ⁅w, y⁆ := by
    rw [indecFix_comm_left hD hwy hrL1, mul_inv_cancel_right]
  have hx' : x * ⁅w, y⁆ * x⁻¹ = ⁅w, y⁆ := by
    rw [indecFix_comm_left hD hwy (pCoreOf_le 2 L1 hx), mul_inv_cancel_right]
  have e : ⁅x * (r * w), y⁆ = ⁅w, y⁆ * ⁅x, y⁆ := by
    calc ⁅x * (r * w), y⁆ = x * (r * ⁅w, y⁆ * r⁻¹ * ⁅r, y⁆) * x⁻¹ * ⁅x, y⁆ := by
          simp only [commutatorElement_def]; group
      _ = x * ⁅w, y⁆ * x⁻¹ * ⁅x, y⁆ := by
          rw [hr', commutatorElement_eq_one_iff_mul_comm.mpr (hRab r hr y hyR), mul_one]
      _ = ⁅w, y⁆ * ⁅x, y⁆ := by rw [hx']
  rw [e]
  exact mul_mem hwy (hD.commutator_mem_centerOf_left hx hy1)

theorem G2qCoordRight.commutator_commutator_mem_centerOf_left (hH : Hyp111 L1 L2 S)
    (hD : G2qLocalData L1 L2 S f) (h1 : IsL2Quot f (oTwoQuot ↥L1))
    (h2 : IsL2Quot f (oTwoQuot ↥L2)) (c : G2qCoordRight L2 S f)
    (hsplit : ⁅pCoreOf 2 L2, L2⁆ ⊓ c.W = centerOf (pCoreOf 2 L2)) :
    ∀ s ∈ S, ∀ s' ∈ S, ∀ x ∈ pCoreOf 2 L1, ⁅s, ⁅s', x⁆⁆ ∈ centerOf (pCoreOf 2 L1) := by
  intro s hs s' hs' x hx
  have hZR : centerOf (pCoreOf 2 L2) ≤ ⁅pCoreOf 2 L2, L2⁆ := by
    rw [← hsplit]
    exact inf_le_left
  exact hD.commutator_mem_centerOf_left_of_mem_inf hH h1 h2
    (c.commute_of_commutator_inf_W_eq hD hsplit) s hs _
    (indecFix_commutator_mem_inf hH hD h1 h2 hZR hs' hx)

private theorem indecFix_fixed_mem_right (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2))
    (c : G2qCoordRight L2 S f) {y : G} (hy : y ∈ pCoreOf 2 L1)
    (hyl : ∀ l ∈ L1, ⁅l, y⁆ ∈ centerOf (pCoreOf 2 L1)) : y ∈ pCoreOf 2 L2 := by
  letI := c.field
  by_contra hyQ
  have hyS : y ∈ S := hH.pCoreOf_le_left hy
  have hyL2 : y ∈ L2 := indecFix_le_right hH hD h2 hyS
  obtain ⟨β, hβs, hβk, hβe⟩ := c.natW
  obtain ⟨t, ht⟩ := mem_utri_iff.mp ((c.memS ⟨y, hyL2⟩).mp hyS)
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [utriElt_zero] at ht
    exact hyQ ((c.ker _).mp ht)
  obtain ⟨a, ha, hav⟩ := exists_natSecVec_eq hβs ![0, 1]
  have haL1 : a ∈ L1 := indecFix_le_left hH hD h1 h2 (hH.pCoreOf_le_right ha)
  have hc : y * a * y⁻¹ ∈ pCoreOf 2 L2 := conj_mem_pCoreOf_of_mem hyL2 ha
  have hya : ⁅y, a⁆ ∈ c.W := by
    rw [← commutatorElement_inv]
    exact c.center_le (hD.centerOf_pCoreOf_left_le_right hH h1 h2 (inv_mem (hyl a haL1)))
  have key := natSecVec_commutator hβe ⟨y, hyL2⟩ ha hc
  rw [(natSecVec_eq_zero_iff hβk (c.le_pCoreOf hya)).mpr hya, ht, hav] at key
  have k := congrFun key 0
  rw [Pi.zero_apply, Pi.sub_apply, utriElt_mulVec_apply_zero] at k
  apply ht0
  simpa using k.symm

private theorem indecFix_fixed_mem_center_right (hH : Hyp111 L1 L2 S)
    (hD : G2qLocalData L1 L2 S f) (h1 : IsL2Quot f (oTwoQuot ↥L1))
    (h2 : IsL2Quot f (oTwoQuot ↥L2)) (c : G2qCoordRight L2 S f) {y : G}
    (hyl : ∀ l ∈ L1, ⁅l, y⁆ ∈ centerOf (pCoreOf 2 L1)) (hyW : y ∈ c.W) :
    y ∈ centerOf (pCoreOf 2 L2) :=
  c.mem_centerOf_of_commutator_mem hH hD h1 h2 hyW fun a ha => by
    rw [← commutatorElement_inv]
    exact inv_mem (hyl a (indecFix_le_left hH hD h1 h2 (hH.pCoreOf_le_right ha)))

private theorem indecFix_fixed_conj (hH : Hyp111 L1 L2 S) (hD : G2qLocalData L1 L2 S f)
    (h1 : IsL2Quot f (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2)) {b y : G}
    (hb : b ∈ bigB L1 L2 S) (hy : y ∈ pCoreOf 2 L1)
    (hyl : ∀ l ∈ L1, ⁅l, y⁆ ∈ centerOf (pCoreOf 2 L1)) :
    b * y * b⁻¹ ∈ pCoreOf 2 L1 ∧ ∀ l ∈ L1, ⁅l, b * y * b⁻¹⁆ ∈ centerOf (pCoreOf 2 L1) := by
  have hbQ := hH.bigB_le_normalizer_pCoreOf_left hb
  have hbL : b ∈ Subgroup.normalizer (L1 : Set G) := (hD.bigB_le_normalizer hH h1 h2 hb).1.1
  refine ⟨(Subgroup.mem_normalizer_iff.mp hbQ y).mp hy, fun l hl => ?_⟩
  have hl' : b⁻¹ * l * b ∈ L1 := by
    have h := (Subgroup.mem_normalizer_iff.mp (inv_mem hbL) l).mp hl
    simpa using h
  rw [show ⁅l, b * y * b⁻¹⁆ = b * ⁅b⁻¹ * l * b, y⁆ * b⁻¹ by
    simp only [commutatorElement_def]; group]
  exact mem_centerOf_conj_of_mem_normalizer hbQ (hyl _ hl')

private theorem indecFix_fixed_mem_center_left (hH : Hyp111 L1 L2 S)
    (hD : G2qLocalData L1 L2 S f) (h1 : IsL2Quot f (oTwoQuot ↥L1))
    (h2 : IsL2Quot f (oTwoQuot ↥L2)) {y : G} (hy : y ∈ pCoreOf 2 L1)
    (hyl : ∀ l ∈ L1, ⁅l, y⁆ ∈ centerOf (pCoreOf 2 L1)) (hyZ : y ∈ centerOf (pCoreOf 2 L2)) :
    y ∈ centerOf (pCoreOf 2 L1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hyZ1
  obtain ⟨c⟩ := hD.exists_coordRight hH h2
  letI := c.field
  letI := c.fintype
  obtain ⟨β, -, hβk, hβe⟩ := c.nat
  have hS2 := indecFix_le_right hH hD h2
  have hZ12 := hD.centerOf_pCoreOf_left_le_right hH h1 h2
  have hv : natSecVec β y 1 ≠ 0 := fun h =>
    hyZ1 (indecFix_mem_left_of_snd hH hD h1 h2 c.card c.surj c.memS hβk hβe hyZ h)
  have hall : ∀ z ∈ centerOf (pCoreOf 2 L2), ∀ l ∈ L1, ⁅l, z⁆ ∈ centerOf (pCoreOf 2 L1) := by
    intro z hz
    by_cases hz1 : natSecVec β z 1 = 0
    · have hzZ1 := indecFix_mem_left_of_snd hH hD h1 h2 c.card c.surj c.memS hβk hβe hz hz1
      intro l hl
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (indecFix_comm_left hD hzZ1 hl)]
      exact one_mem _
    · obtain ⟨g, hgB, hg⟩ := indecFix_exists_borel_mulVec hv hz1
      obtain ⟨b, rfl⟩ := c.surj g
      have hbB : (b : G) ∈ bigB L1 L2 S :=
        (le_sup_right.trans le_sup_left : borelOf L2 S ≤ bigB L1 L2 S)
          ((mem_borelOf_iff_alpha_mem_borel hS2 c.α c.surj c.memS b).mpr hgB)
      have hc : (b : G) * y * (b : G)⁻¹ ∈ centerOf (pCoreOf 2 L2) :=
        mem_centerOf_conj_of_mem_normalizer (hH.bigB_le_normalizer_pCoreOf_right hbB) hyZ
      have hconj : (b : G) * y * (b : G)⁻¹ = z := by
        have key := natSecVec_conj hβe b hyZ hc
        rw [hg] at key
        have h' := (natSecVec_eq_iff hβk hc hz).mp key
        rwa [Subgroup.mem_bot, inv_mul_eq_one] at h'
      rw [← hconj]
      exact (indecFix_fixed_conj hH hD h1 h2 hbB hy hyl).2
  have hL2 : L2 ≤ Subgroup.normalizer (centerOf (pCoreOf 2 L2) : Set G) :=
    le_normalizer_centerOf_of_le_normalizer (le_normalizer_pCoreOf 2 L2)
  have hN : L1 ⊔ L2 ⊔ S ≤ Subgroup.normalizer (centerOf (pCoreOf 2 L2) : Set G) := by
    refine sup_le (sup_le ?_ hL2) (hS2.trans hL2)
    refine le_normalizer_of_forall_conj_mem_of_mem fun l hl z hz => ?_
    rw [show l * z * l⁻¹ = ⁅l, z⁆ * z by rw [commutatorElement_def]; group]
    exact mul_mem (hZ12 (hall z hz l hl)) hz
  have hZQ : centerOf (pCoreOf 2 L2) ≤ pCoreOf 2 L2 := inf_le_left
  have hle := le_pCoreOf_of_le_normalizer 2
    (hZQ.trans ((pCoreOf_le 2 L2).trans (le_sup_right.trans le_sup_left))) hN
    ((pCoreOf_isPGroup 2 L2).to_le hZQ)
  rw [hH.o2] at hle
  apply hyZ1
  rw [Subgroup.mem_bot.mp (hle hyZ)]
  exact one_mem _

private theorem indecFix_exists_conj_mul (c : G2qCoordRight L2 S f) {y a : G}
    (hy : y ∈ pCoreOf 2 L2) (hyW : y ∉ c.W) (ha : a ∈ pCoreOf 2 L2) (haW : a ∉ c.W) :
    ∃ l ∈ L2, ∃ w ∈ c.W, a = l * y * l⁻¹ * w := by
  letI := c.field
  obtain ⟨β, -, hβk, hβe⟩ := c.natW
  have hu : natSecVec β y ≠ 0 := fun h => hyW ((natSecVec_eq_zero_iff hβk hy).mp h)
  have hv : natSecVec β a ≠ 0 := fun h => haW ((natSecVec_eq_zero_iff hβk ha).mp h)
  obtain ⟨g, hg⟩ := CFSG.CGT.PushingUpLit.Glue.exists_sl2_mulVec_eq_of_ne_zero hu hv
  obtain ⟨l, rfl⟩ := c.surj g
  have hc : (l : G) * y * (l : G)⁻¹ ∈ pCoreOf 2 L2 := conj_mem_pCoreOf_of_mem l.2 hy
  refine ⟨l, l.2, ((l : G) * y * (l : G)⁻¹)⁻¹ * a, ?_, by group⟩
  refine (natSecVec_eq_iff hβk hc ha).mp ?_
  rw [natSecVec_conj hβe l hy hc]
  exact hg

private theorem indecFix_commute_conj_mul (c : G2qCoordRight L2 S f) {y u l w' : G}
    (hy : y ∈ pCoreOf 2 L2) (hu : u ∈ c.W) (huy : u * y = y * u) (hl : l ∈ L2)
    (hw' : w' ∈ c.W) : l * y * l⁻¹ * w' * u = u * (l * y * l⁻¹ * w') := by
  have hz : ⁅l⁻¹, u⁆ ∈ centerOf (pCoreOf 2 L2) := c.commutator_le (by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator (inv_mem hl) hu)
  have hzy : y * ⁅l⁻¹, u⁆ = ⁅l⁻¹, u⁆ * y := mul_comm_of_mem_centerOf hz hy
  have h3 : ⁅l⁻¹, u⁆ * u * y = y * (⁅l⁻¹, u⁆ * u) := by
    calc ⁅l⁻¹, u⁆ * u * y = ⁅l⁻¹, u⁆ * (u * y) := mul_assoc _ _ _
      _ = ⁅l⁻¹, u⁆ * (y * u) := by rw [huy]
      _ = ⁅l⁻¹, u⁆ * y * u := (mul_assoc _ _ _).symm
      _ = y * ⁅l⁻¹, u⁆ * u := by rw [hzy]
      _ = y * (⁅l⁻¹, u⁆ * u) := mul_assoc _ _ _
  have hconj : l * y * l⁻¹ * u = u * (l * y * l⁻¹) := by
    calc l * y * l⁻¹ * u = l * (y * (⁅l⁻¹, u⁆ * u)) * l⁻¹ := by
          simp only [commutatorElement_def]; group
      _ = l * (⁅l⁻¹, u⁆ * u * y) * l⁻¹ := by rw [h3]
      _ = u * (l * y * l⁻¹) := by simp only [commutatorElement_def]; group
  calc l * y * l⁻¹ * w' * u = l * y * l⁻¹ * (w' * u) := mul_assoc _ _ _
    _ = l * y * l⁻¹ * (u * w') := by rw [c.commute_of_mem_W hw' hu]
    _ = l * y * l⁻¹ * u * w' := (mul_assoc _ _ _).symm
    _ = u * (l * y * l⁻¹) * w' := by rw [hconj]
    _ = u * (l * y * l⁻¹ * w') := mul_assoc _ _ _

private theorem indecFix_commutator_mem_of_fixed (hH : Hyp111 L1 L2 S)
    (hD : G2qLocalData L1 L2 S f) (h1 : IsL2Quot f (oTwoQuot ↥L1))
    (h2 : IsL2Quot f (oTwoQuot ↥L2)) (c : G2qCoordRight L2 S f) {y : G}
    (hy : y ∈ pCoreOf 2 L1) (hyl : ∀ l ∈ L1, ⁅l, y⁆ ∈ centerOf (pCoreOf 2 L1)) (hyW : y ∉ c.W)
    {t : G} (htL : t ∈ L1) (htB : t ∈ bigB L1 L2 S) {w : G} (hw : w ∈ c.W) :
    ⁅t, w⁆ ∈ centerOf (pCoreOf 2 L2) := by
  have hZ12 := hD.centerOf_pCoreOf_left_le_right hH h1 h2
  have hy2 := indecFix_fixed_mem_right hH hD h1 h2 c hy hyl
  have hwQ := c.le_pCoreOf hw
  have hw' : t * w * t⁻¹ ∈ c.W :=
    (Subgroup.mem_normalizer_iff.mp (c.bigB_le_normalizer_W hH htB) w).mp hw
  have hwL1 : w ∈ L1 := pCoreOf_le 2 L1 (c.W_le_pCoreOf_left hH hD h1 h2 hw)
  have hu : w⁻¹ * (t * w * t⁻¹) ∈ c.W := mul_mem (inv_mem hw) hw'
  have huy : w⁻¹ * (t * w * t⁻¹) * y = y * (w⁻¹ * (t * w * t⁻¹)) := by
    have hd : ⁅t, y⁆ ∈ centerOf (pCoreOf 2 L2) := hZ12 (hyl t htL)
    have hc : t * ⁅w, y⁆ * t⁻¹ = ⁅w, y⁆ := by
      rw [indecFix_comm_left hD (hyl w hwL1) htL, mul_inv_cancel_right]
    have key : ⁅t * w * t⁻¹, y⁆ = ⁅w, y⁆ := by
      calc ⁅t * w * t⁻¹, y⁆ = ⁅t * w * t⁻¹, ⁅t, y⁆ * y⁆ :=
            (commutator_mul_right_eq_of_mem_centerOf hd (c.le_pCoreOf hw') hy2).symm
        _ = t * ⁅w, y⁆ * t⁻¹ := by simp only [commutatorElement_def]; group
        _ = ⁅w, y⁆ := hc
    rw [commutatorElement_def, commutatorElement_def] at key
    calc w⁻¹ * (t * w * t⁻¹) * y =
          w⁻¹ * (t * w * t⁻¹ * y * (t * w * t⁻¹)⁻¹ * y⁻¹) * y * (t * w * t⁻¹) := by group
      _ = w⁻¹ * (w * y * w⁻¹ * y⁻¹) * y * (t * w * t⁻¹) := by rw [key]
      _ = y * (w⁻¹ * (t * w * t⁻¹)) := by group
  have huZ : w⁻¹ * (t * w * t⁻¹) ∈ centerOf (pCoreOf 2 L2) := by
    refine mem_centerOf_of_forall_comm (c.le_pCoreOf hu) fun a ha => ?_
    by_cases haW : a ∈ c.W
    · exact c.commute_of_mem_W haW hu
    · obtain ⟨l, hl, w', hw'', rfl⟩ := indecFix_exists_conj_mul c hy2 hyW ha haW
      exact indecFix_commute_conj_mul c hy2 hu huy hl hw''
  rw [show ⁅t, w⁆ = w * (w⁻¹ * (t * w * t⁻¹)) * w⁻¹ by rw [commutatorElement_def]; group]
  exact mem_centerOf_conj_of_mem_normalizer
    (le_normalizer_pCoreOf 2 L2 (pCoreOf_le 2 L2 hwQ)) huZ

private theorem indecFix_exists_mul_hall (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : G2qLocalData L1 L2 S f) (h1 : IsL2Quot f (oTwoQuot ↥L1))
    (h2 : IsL2Quot f (oTwoQuot ↥L2)) {H : Subgroup G} (hHB : H ≤ bigB L1 L2 S)
    (hSH : S ⊔ H = bigB L1 L2 S) (hSinfH : S ⊓ H = ⊥)
    (hHcard : Nat.card H = (2 ^ f - 1) * (2 ^ f - 1))
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) {h : G} (hh : h ∈ H) :
    ∃ t₁ ∈ H ⊓ L1, ∃ t₂ ∈ H ⊓ L2, h = t₁ * t₂ := by
  obtain ⟨hc1, -⟩ := hD.torus_left_of_hall hf hH h1 h2 hHB hSH hSinfH hHcard hHcomm
  obtain ⟨hc2, -⟩ := hD.torus_right_of_hall hf hH h1 h2 hHB hSH hSinfH hHcard hHcomm
  have hN : H ⊓ L2 ≤ Subgroup.normalizer ((H ⊓ L1 : Subgroup G) : Set G) := by
    refine le_normalizer_of_forall_conj_mem_of_mem fun g hg x hx => ?_
    rw [hHcomm g (Subgroup.mem_inf.mp hg).1 x (Subgroup.mem_inf.mp hx).1, mul_inv_cancel_right]
    exact hx
  have hinf : (H ⊓ L2) ⊓ (H ⊓ L1) = ⊥ := by
    rw [eq_bot_iff]
    intro t ht
    obtain ⟨ht2, ht1⟩ := Subgroup.mem_inf.mp ht
    obtain ⟨htH, htL2⟩ := Subgroup.mem_inf.mp ht2
    have htN : t ∈ Subgroup.normalizer (S : Set G) :=
      (hD.bigB_le_normalizer hH h1 h2 (hHB htH)).2
    have htB1 : t ∈ borelOf L1 S := by
      rw [borelOf_eq_inf_of_le (indecFix_le_left hH hD h1 h2)]
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp ht1).2, htN⟩
    have htB2 : t ∈ borelOf L2 S := by
      rw [borelOf_eq_inf_of_le (indecFix_le_right hH hD h2)]
      exact Subgroup.mem_inf.mpr ⟨htL2, htN⟩
    have htS : t ∈ S :=
      (hD.borelOf_inf_borelOf hH h1 h2).le (Subgroup.mem_inf.mpr ⟨htB1, htB2⟩)
    have h' : t ∈ S ⊓ H := Subgroup.mem_inf.mpr ⟨htS, htH⟩
    rwa [hSinfH] at h'
  have hcard := C5.card_sup_mul_card_inf_of_le_normalizer hN
  rw [hinf, Subgroup.card_bot, mul_one, hc1, hc2] at hcard
  have hsup : (H ⊓ L2) ⊔ (H ⊓ L1) = H :=
    Subgroup.eq_of_le_of_card_ge (sup_le inf_le_left inf_le_left)
      (le_of_eq (by rw [hcard, hHcard]))
  have hh' : h ∈ (H ⊓ L1) ⊔ (H ⊓ L2) := by
    rw [sup_comm, hsup]
    exact hh
  exact (mem_sup_iff_exists_mul_of_normalizes hN).mp hh'

private theorem indecFix_hall_commutator_mem (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : G2qLocalData L1 L2 S f) (h1 : IsL2Quot f (oTwoQuot ↥L1))
    (h2 : IsL2Quot f (oTwoQuot ↥L2)) (c : G2qCoordRight L2 S f) {y : G}
    (hy : y ∈ pCoreOf 2 L1) (hyl : ∀ l ∈ L1, ⁅l, y⁆ ∈ centerOf (pCoreOf 2 L1)) (hyW : y ∉ c.W)
    {H : Subgroup G} (hHB : H ≤ bigB L1 L2 S) (hSH : S ⊔ H = bigB L1 L2 S)
    (hSinfH : S ⊓ H = ⊥) (hHcard : Nat.card H = (2 ^ f - 1) * (2 ^ f - 1))
    (hHcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) {h : G} (hh : h ∈ H) {w : G}
    (hw : w ∈ c.W) : ⁅h, w⁆ ∈ centerOf (pCoreOf 2 L2) := by
  obtain ⟨t₁, ht₁, t₂, ht₂, rfl⟩ :=
    indecFix_exists_mul_hall hf hH hD h1 h2 hHB hSH hSinfH hHcard hHcomm hh
  obtain ⟨ht₁H, ht₁L⟩ := Subgroup.mem_inf.mp ht₁
  have hz : ⁅t₂, w⁆ ∈ centerOf (pCoreOf 2 L2) := c.commutator_le (by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_inf.mp ht₂).2 hw)
  rw [show ⁅t₁ * t₂, w⁆ = t₁ * ⁅t₂, w⁆ * t₁⁻¹ * ⁅t₁, w⁆ by
    simp only [commutatorElement_def]; group]
  exact mul_mem (mem_centerOf_conj_of_mem_normalizer
    (hH.bigB_le_normalizer_pCoreOf_right (hHB ht₁H)) hz)
    (indecFix_commutator_mem_of_fixed hH hD h1 h2 c hy hyl hyW ht₁L (hHB ht₁H) hw)

theorem G2qLocalData.mem_centerOf_left_of_fixed (hf : 2 ≤ f) (hH : Hyp111 L1 L2 S)
    (hD : G2qLocalData L1 L2 S f) (h1 : IsL2Quot f (oTwoQuot ↥L1))
    (h2 : IsL2Quot f (oTwoQuot ↥L2)) :
    ∀ x ∈ pCoreOf 2 L1, (∀ l ∈ L1, ⁅l, x⁆ ∈ centerOf (pCoreOf 2 L1)) →
      x ∈ centerOf (pCoreOf 2 L1) := by
  intro x hx hxl
  obtain ⟨c⟩ := hD.exists_coordRight hH h2
  have hxW : x ∈ c.W := by
    by_contra hxW
    obtain ⟨H, hHB, hSH, hSinfH, hHcard, hHcomm⟩ := hD.exists_hall_bigB hH h1 h2
    exact c.false_of_trivOTwoQuot_centralizes_W hf hH hD h1 h2 hHB hSH hSinfH hHcard hHcomm
      fun h hh w hw => indecFix_hall_commutator_mem hf hH hD h1 h2 c hx hxl hxW hHB hSH
        hSinfH hHcard hHcomm (Subgroup.mem_inf.mp hh).1 hw
  exact indecFix_fixed_mem_center_left hH hD h1 h2 hx hxl
    (indecFix_fixed_mem_center_right hH hD h1 h2 c hxl hxW)

end CFSG.Quasithin.F112R.St84

end
