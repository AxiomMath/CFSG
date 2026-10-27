module

public import CFSG.ClassicalGroups.Orthogonal.RootGroupSwap
public import CFSG.RankThree.GF2n.Stroth80.NonsingularPerp
public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaTransport

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.ClassicalGroups.F2Fixed CFSG.ClassicalGroups.Orthogonal QuadraticMap
open scoped Matrix

section Fixed

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem card_fixedSub_Lom_eq (hQ : (polarBilin Q).Nondegenerate)
    (h4 : 4 ≤ Module.finrank K V) {M : Type*} [AddCommGroup M] [DistribMulAction (Gom Q) M]
    {u u' : V} (hu : Q u = 0) (hu' : Q u' = 0) (huu' : polar Q u u' ≠ 0) :
    Nat.card (fixedSub M (Lom Q u : Set (Gom Q))) =
      Nat.card (fixedSub M (Lom Q u' : Set (Gom Q))) := by
  have hu'0 : u' ≠ 0 := by
    rintro rfl
    exact huu' (by simp)
  obtain ⟨w, hw1, hw2⟩ := exists_nonsingular_perp hQ h4 hu'0
  obtain ⟨w', hew, hfw, hQw, -⟩ := exists_perp_eichlerG_eq (e := u) (f := u') (w := w) hu' huu'
    hw1
  have hc : Q w' ≠ 0 := by rw [hQw]; exact hw2
  have key := eichlerG_pair_app_left (e := u) (f := u') (w := w') (t := polar Q u u') hu hu'
    rfl huu' hew hfw hc
  have h := card_fixedSub_Lom (M := M)
    (eichlerG Q u ((Q w' * polar Q u u')⁻¹ • w') * eichlerG Q u' w') u
  rw [key, Lom_smul (mul_ne_zero hc huu')] at h
  exact h.symm

theorem stroth_2_1_ii_omega_fixed_of_card (hQ : (polarBilin Q).Nondegenerate) {M : Type*}
    [AddCommGroup M] [Finite M] (h2 : ∀ x : M, x + x = 0) [DistribMulAction (Gom Q) M]
    {u u' : V} (hu : Q u = 0) (hu' : Q u' = 0) (huu' : polar Q u u' ≠ 0)
    (hdec : IsCompl (fixedSub M (Lom Q u : Set (Gom Q))) (fixedSub M (Lom Q u' : Set (Gom Q))))
    (hcard : Nat.card (fixedSub M (Lom Q u : Set (Gom Q))) =
      Nat.card (fixedSub M (Lom Q u' : Set (Gom Q))))
    {x : Gom Q} (hx : x ∈ Lom Q u') (hn : x.NonA2) :
    fixedSub M {x} = fixedSub M (Lom Q u' : Set (Gom Q)) ∧
      (comm M x).range = fixedSub M (Lom Q u' : Set (Gom Q)) ∧
      Nat.card M = Nat.card (fixedSub M (Lom Q u' : Set (Gom Q))) ^ 2 := by
  obtain ⟨w, hw, hQw, rfl⟩ := exists_eichler_of_nonA2 hu' hx hn
  exact pair_facts h2 (L₁ := Lom Q u) (L₂ := Lom Q u') hx (Eom_mul_self hw)
    (closure_Lom_insert_Eom hQ hu hu' huu' hw hQw) hdec hcard

end Fixed

section Transport

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K] [CharP K 2]
  {Q : QuadraticForm K (ι → K)} {X : Subgroup (GL ι K)} (E : ElemMatrixIso Q X)
  {Y : Type*} [Group Y] (φ : Y →* GL ι K) (hφ : φ.range = X)
  {M : Type*} [AddCommGroup M] [Finite M] [DistribMulAction Y M]

include hφ in
theorem stroth_2_1_ii_omega_fixed_of_hom (hQ : (polarBilin Q).Nondegenerate)
    (h2 : ∀ x : M, x + x = 0) (hker : ∀ y ∈ φ.ker, ∀ a : M, y • a = a)
    {u u' : ι → K} (hu : Q u = 0) (hu' : Q u' = 0) (huu' : polar Q u u' ≠ 0)
    {L₁ L₂ : Subgroup Y} (hL₁ : L₁.map φ = E.LomGL u) (hL₂ : L₂.map φ = E.LomGL u')
    (hdec : IsCompl (fixedSub M (L₁ : Set Y)) (fixedSub M (L₂ : Set Y)))
    (h4 : 4 ≤ Fintype.card ι)
    {y : Y} (hy : y ∈ L₂) (hn : ∃ v : ι → K, polar Q v ((φ y : Matrix ι ι K) *ᵥ v) ≠ 0) :
    fixedSub M {y} = fixedSub M (L₂ : Set Y) ∧ (comm M y).range = fixedSub M (L₂ : Set Y) ∧
      Nat.card M = Nat.card (fixedSub M (L₂ : Set Y)) ^ 2 := by
  have hk : ∀ y ∈ (viaMatrix X E.equiv φ hφ).ker, ∀ a : M, y • a = a := by
    intro y hy a
    rw [ker_viaMatrix] at hy
    exact hker y hy a
  have hΦ := viaMatrix_surjective (e := E.equiv) φ hφ
  letI : DistribMulAction (Gom Q) M := descendAction (viaMatrix X E.equiv φ hφ) hΦ hk
  have hsm : ∀ (z : Y) (a : M), viaMatrix X E.equiv φ hφ z • a = z • a := fun z a =>
    descendAction_smul (viaMatrix X E.equiv φ hφ) hΦ hk z a
  have hx : viaMatrix X E.equiv φ hφ y ∈ Lom Q u' := by
    have h1 : φ y ∈ E.LomGL u' := by
      rw [← hL₂]
      exact Subgroup.mem_map_of_mem φ hy
    obtain ⟨hA, hmem⟩ := mem_matrixOf_iff.1 h1
    exact hmem
  have hxn : (viaMatrix X E.equiv φ hφ y).NonA2 := by
    obtain ⟨v, hv⟩ := hn
    exact ⟨v, by rw [viaMatrix_app E φ hφ y v]; exact hv⟩
  have key := stroth_2_1_ii_omega_fixed_of_card hQ h2 hu hu' huu'
    (by rw [fixedSub_descend_Lom E φ hφ hker hL₁, fixedSub_descend_Lom E φ hφ hker hL₂];
        exact hdec)
    (card_fixedSub_Lom_eq hQ (by simpa using h4) hu hu' huu') hx hxn
  rw [fixedSub_descend_Lom E φ hφ hker hL₂] at key
  obtain ⟨k1, k2, k3⟩ := key
  have e1 : fixedSub M {viaMatrix X E.equiv φ hφ y} = fixedSub M {y} := by
    ext a
    simp only [mem_fixedSub, Set.mem_singleton_iff, forall_eq]
    rw [hsm]
  have e2 : comm M (viaMatrix X E.equiv φ hφ y) = comm M y := by
    ext a
    simp only [comm_apply]
    rw [hsm]
  rw [e1] at k1
  rw [e2] at k2
  exact ⟨k1, k2, k3⟩

end Transport

end CFSG.RankThree.GF2n.Stroth80
