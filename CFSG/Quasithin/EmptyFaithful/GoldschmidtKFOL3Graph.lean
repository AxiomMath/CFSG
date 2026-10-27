module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFOdd168
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115OddL3AutFinal
public import CFSG.RankThree.PartOne.KF.F1322OmegaSeven

public section

namespace CFSG.Quasithin.SBd19F

open Matrix CFSG.RankThree.SubgroupLists CFSG.RankThree.PartOne.KF1322 CFSG.QuasithinUnique.Ch1
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

theorem le_omegaGL_of_isPerfect {K : Type*} [Field K] {σ : Type*} [Fintype σ] [DecidableEq σ]
    {M : Matrix σ σ K} {P : Subgroup (GL σ K)} [Group.IsPerfect P] (hP : P ≤ soGL M) :
    P ≤ omegaGL M := by
  rw [← Subgroup.commutator_eq_self (H := P)]
  exact Subgroup.commutator_mono hP hP

theorem eq_seven_of_perfect_card_168_soGL {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) {M : Matrix (Fin 3) (Fin 3) (ZMod p)} (hMt : Mᵀ = M) (hdet : M.det ≠ 0)
    {P : Subgroup (GL (Fin 3) (ZMod p))} [Group.IsPerfect P] (hP : P ≤ soGL M)
    (hcard : Nat.card P = 168) : p = 7 := by
  obtain ⟨e⟩ := nonempty_omegaGL_equiv_psl2 hp5 hMt hdet
  let eK : P.subgroupOf (omegaGL M) ≃* P :=
    Subgroup.subgroupOfEquivOfLe (le_omegaGL_of_isPerfect hP)
  have : Group.IsPerfect (P.subgroupOf (omegaGL M)) :=
    Group.IsPerfect.ofSurjective (f := eK.symm.toMonoidHom) eK.symm.surjective
  exact eq_seven_of_perfect_card_168_psl2 Fact.out (by omega) e
    (K := P.subgroupOf (omegaGL M)) (by rw [Nat.card_congr eK.toEquiv, hcard])

theorem eq_seven_of_le_range_soProj {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) {R : Matrix (Fin 3) (Fin 3) (ZMod p)} (hRt : Rᵀ = R) (hRdet : R.det ≠ 0)
    {K : Subgroup (projectiveSL 3 (ZMod p))} [Group.IsPerfect K] (hcard : Nat.card K = 168)
    (hle : K ≤ (soProj R).range) : p = 7 := by
  have hinj := soProj_injective (fun h : R = 0 => hRdet (by rw [h]; exact Matrix.det_zero))
  set K₁ := K.comap (soProj R)
  have hmap : K₁.map (soProj R) = K := Subgroup.map_comap_eq_self hle
  let e1 : K₁ ≃* K := (K₁.equivMapOfInjective _ hinj).trans (MulEquiv.subgroupCongr hmap)
  have h1 : Group.IsPerfect K₁ :=
    Group.IsPerfect.ofSurjective (f := e1.symm.toMonoidHom) e1.symm.surjective
  let ι : soForm R →* GL (Fin 3) (ZMod p) := SpecialLinearGroup.toGL.comp (soForm R).subtype
  have hι : Function.Injective ι :=
    SpecialLinearGroup.toGL_injective.comp (soForm R).subtype_injective
  have h2 : Group.IsPerfect (K₁.map ι) := Group.IsPerfect.map ι
  refine eq_seven_of_perfect_card_168_soGL hp5 hRt hRdet (P := K₁.map ι) ?_ ?_
  · rintro _ ⟨y, -, rfl⟩
    exact mem_soGL.mpr ⟨y.2, y.1.2⟩
  · rw [← Nat.card_congr (K₁.equivMapOfInjective ι hι).toEquiv, Nat.card_congr e1.toEquiv, hcard]

theorem eq_seven_of_fixed_graph {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) {A : GL (Fin 3) (ZMod p)} (hA : (A : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ = A)
    {K : Subgroup (projectiveSL 3 (ZMod p))} [Group.IsPerfect K] (hcard : Nat.card K = 168)
    (hK : ∀ x ∈ K,
      (LinearFlag.conjAut 3 (ZMod p) A * LinearFlag.dualAut 3 (ZMod p)) x = x) : p = 7 :=
  eq_seven_of_le_range_soProj hp5 (transpose_inv_of_transpose_eq' A hA)
    (Matrix.isUnits_det_units (A⁻¹)).ne_zero hcard fun x hx =>
      exists_mem_soForm_of_fixed A (hK x hx)

end CFSG.Quasithin.SBd19F
