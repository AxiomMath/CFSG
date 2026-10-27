module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaGroup

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne.AUTSL

namespace RecipeFieldOmega

section Minus

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {b c : K}

theorem congr_minusEquiv_of_mem_closure (hn4 : 4 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {f : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (n - 1) b c)))}
    (hf : f ∈ Subgroup.closure
      (LargeEvenPhiQ (n - 1) b c
        (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (n - 1) b c))))) :
    MulAut.congr (minusEquiv hn4 b c) f ∈ Subgroup.zpowers (AutOm.frobAut hn4 hirr) :=
  congr_mem_of_mem_closure _ (fun g hg => by
    obtain ⟨k, hk⟩ := congr_minusEquiv_of_mem_phi hn4 hirr hg
    rw [hk]
    exact Subgroup.npow_mem_zpowers _ k) hf

theorem ggRawInnField_omegaMinus (hn4 : 4 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {f : ℕ}
    (hf : Nat.card K = 2 ^ f) (hf1 : 1 ≤ f) {p : ℕ} (hp : p ≠ 1) :
    GGRawInnField p (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (n - 1) b c)))
      (LargeEvenInnSet _)
      (LargeEvenPhiQ (n - 1) b c
        (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (n - 1) b c)))) := by
  refine ggRawInnField_of_subgroup hp (inner _) coe_inner_eq_innSet (fun r => ⟨r, rfl⟩)
    fun φ hφ hφI => ?_
  obtain ⟨k, hk⟩ := congr_minusEquiv_of_mem_phi hn4 hirr hφ
  have hI := (mem_innSet_iff_congr (minusEquiv hn4 b c) φ).1 hφI
  have hmem : MulAut.congr (minusEquiv hn4 b c) φ ∈
      inner (matrixDerived (Qm n hn4 b c)) ⊓ Subgroup.zpowers (AutOm.frobAut hn4 hirr) :=
    ⟨hI, hk ▸ Subgroup.npow_mem_zpowers _ k⟩
  rw [AutOm.inner_inf_zpowers_frobAut hn4 hirr hf hf1, Subgroup.mem_bot] at hmem
  apply (MulAut.congr (minusEquiv hn4 b c)).injective
  rw [hmem, map_one]

theorem commutator_mem_inner_minus (hn4 : 4 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {f : ℕ} (hf : Nat.card K = 2 ^ f) (α β : MulAut (matrixDerived (Qm n hn4 b c))) :
    α * β * α⁻¹ * β⁻¹ ∈ inner (matrixDerived (Qm n hn4 b c)) := by
  refine commutator_mem_of_eq_mul (inner _) (Subgroup.zpowers (AutOm.frobAut hn4 hirr))
    (fun x hx y hy => ?_) (fun x _ d hd => (inner_normal _).conj_mem d hd x) (fun a => ?_) α β
  · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [← zpow_add, ← zpow_add, add_comm]
  · obtain ⟨ι, hι, k, h⟩ := AutOm.exists_inner_mul_frobAut_pow hn4 hirr hf a
    exact ⟨ι, hι, _, Subgroup.npow_mem_zpowers _ k, h⟩

theorem ggRawFieldCentral_omegaMinus (hn4 : 4 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {f : ℕ} (hf : Nat.card K = 2 ^ f) :
    GGRawFieldCentral (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (n - 1) b c)))
      (LargeEvenInnSet _)
      (LargeEvenPhiQ (n - 1) b c
        (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (n - 1) b c)))) :=
  ggRawFieldCentral_of_commutator_mem fun α β => by
    rw [mem_innSet_iff_congr (minusEquiv hn4 b c), map_mul, map_mul, map_mul, map_inv, map_inv]
    exact commutator_mem_inner_minus hn4 hirr hf _ _

theorem ggRawPCyclic_omegaMinus (hn4 : 4 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {f : ℕ} (hf : Nat.card K = 2 ^ f) {p : ℕ} :
    GGRawPCyclic p (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (n - 1) b c)))
      (LargeEvenInnSet _)
      (LargeEvenPhiQ (n - 1) b c
        (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (n - 1) b c)))) := by
  intro _ _
  set Θ := minusEquiv (K := K) hn4 b c
  have hIn := inner_normal (matrixDerived (Qm n hn4 b c))
  refine ⟨inner _, ⊤, coe_inner_eq_innSet, le_top, (inner_normal _).subgroupOf _,
    ⟨(MulAut.congr Θ).symm (AutOm.frobAut hn4 hirr), Subgroup.mem_top _, fun s _ => ?_⟩,
    fun α _ => Subgroup.mem_top α⟩
  obtain ⟨ι, hι, k, hk⟩ := AutOm.exists_inner_mul_frobAut_pow hn4 hirr hf (MulAut.congr Θ s)
  refine ⟨-(k : ℤ), (mem_innSet_iff_congr Θ _).2 ?_⟩
  rw [map_mul, map_zpow, MulEquiv.apply_symm_apply, hk, zpow_neg, zpow_natCast]
  have := hIn.conj_mem ι hι (AutOm.frobAut hn4 hirr ^ k)⁻¹
  rwa [inv_inv, mul_assoc] at this

end Minus

end RecipeFieldOmega

open RecipeFieldOmega

theorem largeEvenLabelAll_omegaMinus {lab : LargeEvenLabel} (ht : lab.tag = .twD)
    (h4 : 4 ≤ lab.rank) {P : LargeEvenRawCont}
    (hP : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], Nat.card K = 2 ^ lab.n → ∀ b c : K,
      (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
      P (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (lab.rank - 1) b c))) (LargeEvenInnSet _)
        (LargeEvenPhiQ (lab.rank - 1) b c
          (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (lab.rank - 1) b c))))) :
    LargeEvenLabelAll lab P := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht h4 hP ⊢
  subst ht
  intro Q hQ
  have h2 : l ≠ 2 := by omega
  have h3 : l ≠ 3 := by omega
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  simp only [h2, h3, ↓reduceIte] at hQ ⊢
  obtain ⟨K, _, _, hK, b, c, hbc, hQK⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  exact ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hQK, hP K hK b c hbc⟩

@[expose] def GGOmegaMinusLabel (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twD ∧ 4 ≤ lab.rank

theorem ggRawInnFieldOn_omegaMinus : GGRawInnFieldOn GGOmegaMinusLabel :=
  fun _ hp _ _ hlab ⟨ht, h4⟩ => largeEvenLabelAll_omegaMinus ht h4 fun _ _ _ _ hK _ _ hirr =>
    ggRawInnField_omegaMinus h4 hirr hK hlab.1 hp.one_lt.ne'

theorem ggRawFieldCentralOn_omegaMinus : GGRawFieldCentralOn GGOmegaMinusLabel :=
  fun _ _ ⟨ht, h4⟩ => largeEvenLabelAll_omegaMinus ht h4 fun _ _ _ _ hK _ _ hirr =>
    ggRawFieldCentral_omegaMinus h4 hirr hK

theorem ggRawPCyclicOn_omegaMinus : GGRawPCyclicOn fun _ => GGOmegaMinusLabel :=
  fun _ _ _ _ _ ⟨ht, h4⟩ => largeEvenLabelAll_omegaMinus ht h4 fun _ _ _ _ hK _ _ hirr =>
    ggRawPCyclic_omegaMinus h4 hirr hK

end CFSG.StandardType
