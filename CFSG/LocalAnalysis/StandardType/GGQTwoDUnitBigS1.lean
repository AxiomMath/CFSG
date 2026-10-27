module

public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.ClassicalInvolution.Orders.OrthogonalCount
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.SectionRank.SignLines
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.StandardType.QTwo

open CFSG.Open CFSG.RankThree.Classical
open CFSG.RankThree.Classical2 (orthDerived)

abbrev qtwoDB44_Omega {n : ℕ} (Q : QuadraticForm (ZMod 2) (Fin n ⊕ Fin n → ZMod 2)) :
    Subgroup ((Fin n ⊕ Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n ⊕ Fin n → ZMod 2)) :=
  @orthDerived (ZMod 2) (Fin n ⊕ Fin n → ZMod 2) _ _ (Pi.Function.module _ _ _) Q

abbrev qtwoDB44_IsPlus {n : ℕ} (Q : QuadraticForm (ZMod 2) (Fin n ⊕ Fin n → ZMod 2)) : Prop :=
  @CFSG.GroupTheory.WeirSylow.IsPlusType (ZMod 2) _ (Fin n ⊕ Fin n → ZMod 2) _
    (Pi.Function.module _ _ _) Q

noncomputable def qtwoDB44_linEquiv (n : ℕ) :
    StatedSp n (ZMod 2) →*
      ((Fin n ⊕ Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n ⊕ Fin n → ZMod 2)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2)
    (Fin n ⊕ Fin n → ZMod 2)).toMonoidHom.comp (spLin n (ZMod 2))

theorem qtwoDB44_linEquiv_apply (n : ℕ) (y : StatedSp n (ZMod 2)) (x : Fin n ⊕ Fin n → ZMod 2) :
    qtwoDB44_linEquiv n y x = spEnd y x := by
  rfl

theorem qtwoDB44_linEquiv_injective (n : ℕ) : Function.Injective (qtwoDB44_linEquiv n) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2)
    (Fin n ⊕ Fin n → ZMod 2)).injective.comp (spLin_injective (r := n) (K := ZMod 2))

theorem qtwoDB44_exists_of_isometry (n : ℕ)
    (f : (Fin n ⊕ Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n ⊕ Fin n → ZMod 2))
    (hf : ∀ x y, spForm n (ZMod 2) (f x) (f y) = spForm n (ZMod 2) x y) :
    ∃ y : StatedSp n (ZMod 2), qtwoDB44_linEquiv n y = f := by
  let e : LinearMap.GeneralLinearGroup (ZMod 2) (Fin n ⊕ Fin n → ZMod 2) ≃*
      ((Fin n ⊕ Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n ⊕ Fin n → ZMod 2)) :=
    LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin n ⊕ Fin n → ZMod 2)
  have hmem : e.symm f ∈ (spLin n (ZMod 2)).range := by
    rw [range_spLin]
    rw [CFSG.LocalAnalysis.ComponentInitial.mem_sesqUnitaryGroup]
    intro x y
    exact hf x y
  obtain ⟨y, hy⟩ := hmem
  refine ⟨y, ?_⟩
  rw [qtwoDB44_linEquiv, MonoidHom.comp_apply, hy]
  change e (e.symm f) = f
  exact e.apply_symm_apply f

theorem qtwoDB44_linEquiv_mem_orthogonalGroup {n : ℕ}
    (Q : QuadraticForm (ZMod 2) (Fin n ⊕ Fin n → ZMod 2)) (y : StatedSp n (ZMod 2)) :
    qtwoDB44_linEquiv n y ∈ TauCeti.QuadraticMap.orthogonalGroup Q ↔
      ∀ x, Q (spEnd y x) = Q x := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  constructor
  · intro h x
    simpa only [qtwoDB44_linEquiv_apply] using h x
  · intro h x
    simpa only [qtwoDB44_linEquiv_apply] using h x

theorem qtwoDB44_orthogonalGroup_le_range {n : ℕ}
    {Q : QuadraticForm (ZMod 2) (Fin n ⊕ Fin n → ZMod 2)}
    (hQ : ∀ x y, QuadraticMap.polar Q x y = spForm n (ZMod 2) x y) :
    TauCeti.QuadraticMap.orthogonalGroup Q ≤ (qtwoDB44_linEquiv n).range := by
  intro f hf
  refine qtwoDB44_exists_of_isometry n f ?_
  intro x y
  calc
    spForm n (ZMod 2) (f x) (f y) = QuadraticMap.polar Q (f x) (f y) :=
      (hQ (f x) (f y)).symm
    _ = QuadraticMap.polar Q x y :=
      @CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem
        (ZMod 2) (Fin n ⊕ Fin n → ZMod 2) _ _
        (Pi.Function.module (Fin n ⊕ Fin n) (ZMod 2) (ZMod 2)) Q f hf x y
    _ = spForm n (ZMod 2) x y := hQ x y

theorem qtwoDB44_perfect_le_orthDerived {n : ℕ}
    {Q : QuadraticForm (ZMod 2) (Fin n ⊕ Fin n → ZMod 2)} {H : Subgroup (StatedSp n (ZMod 2))}
    (hperf : ⁅H, H⁆ = H) (hH : ∀ y ∈ H, ∀ x, Q (spEnd y x) = Q x) :
    ∀ y ∈ H, qtwoDB44_linEquiv n y ∈ qtwoDB44_Omega Q := by
  intro y hy
  have hle : H.map (qtwoDB44_linEquiv n) ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨z, hz, rfl⟩
    exact (qtwoDB44_linEquiv_mem_orthogonalGroup Q z).2 (hH z hz)
  have hy' : y ∈ ⁅H, H⁆ := by rwa [hperf]
  have hmem : qtwoDB44_linEquiv n y ∈ (⁅H, H⁆).map (qtwoDB44_linEquiv n) :=
    Subgroup.mem_map_of_mem (qtwoDB44_linEquiv n) hy'
  rw [Subgroup.map_commutator] at hmem
  exact Subgroup.commutator_mono hle hle hmem

theorem qtwoDB44_centralizer_preserves {n : ℕ}
    {Q : QuadraticForm (ZMod 2) (Fin n ⊕ Fin n → ZMod 2)}
    (hQ : ∀ x y, QuadraticMap.polar Q x y = spForm n (ZMod 2) x y)
    {h : StatedSp n (ZMod 2)} (hfix : ∀ x, spEnd h x = x → x = 0)
    (hQh : ∀ x, Q (spEnd h x) = Q x) {y : StatedSp n (ZMod 2)} (hy : y * h = h * y) :
    ∀ x, Q (spEnd y x) = Q x := by
  have hnegself : ∀ w : Fin n ⊕ Fin n → ZMod 2, -w = w := by
    intro w
    funext i
    exact CharTwo.neg_eq (w i)
  have hyb : ∀ u v, spForm n (ZMod 2) (spEnd y u) (spEnd y v) =
      spForm n (ZMod 2) u v := by
    intro u v
    rw [spEnd_apply, spEnd_apply, spForm_mulVec,
      CFSG.ClassicalInvolution.Models.SymplecticPairs.gram,
      CFSG.Open.StatedAPI.mem_statedSp_iff.mp y.2]
    rfl
  let D : (Fin n ⊕ Fin n → ZMod 2) → ZMod 2 := fun z => Q (spEnd y z) + Q z
  have hDadd : ∀ u v, D (u + v) = D u + D v := by
    intro u v
    dsimp [D]
    have h1 : spEnd y (u + v) = spEnd y u + spEnd y v :=
      map_add (spEnd y) u v
    have h2 : Q (spEnd y u + spEnd y v) =
        Q (spEnd y u) + Q (spEnd y v) +
          QuadraticMap.polar Q (spEnd y u) (spEnd y v) :=
      QuadraticMap.map_add Q (spEnd y u) (spEnd y v)
    have h3 : Q (u + v) = Q u + Q v + QuadraticMap.polar Q u v :=
      QuadraticMap.map_add Q u v
    rw [h1, h2, h3]
    have hp : QuadraticMap.polar Q (spEnd y u) (spEnd y v) =
        QuadraticMap.polar Q u v :=
      (hQ (spEnd y u) (spEnd y v)).trans ((hyb u v).trans (hQ u v).symm)
    rw [hp]
    ring_nf
    simp [CharTwo.two_eq_zero]
  have hTH : ∀ x, spEnd y (spEnd h x) = spEnd h (spEnd y x) := by
    intro x
    simpa only [spEnd_apply, Subgroup.coe_mul, Units.val_mul, Matrix.mulVec_mulVec] using
      congrArg (fun z : StatedSp n (ZMod 2) => spEnd z x) hy
  have hDinv : ∀ x, D (spEnd h x) = D x := by
    intro x
    dsimp [D]
    rw [hTH x, hQh (spEnd y x), hQh x]
  have hinj : Function.Injective
      (spEnd h + 1 : (Fin n ⊕ Fin n → ZMod 2) →ₗ[ZMod 2] _) := by
    intro u v huv
    have hzero : (spEnd h + 1) (u - v) = 0 := by
      have h1 : (spEnd h + 1) (u - v) = (spEnd h + 1) u - (spEnd h + 1) v :=
        LinearMap.map_sub (spEnd h + 1) u v
      rw [h1, huv, sub_self]
    have hzero' : spEnd h (u - v) + (u - v) = 0 := by simpa using hzero
    have hself : spEnd h (u - v) = (u - v) :=
      (eq_neg_of_add_eq_zero_left hzero').trans (hnegself (u - v))
    exact sub_eq_zero.mp (hfix (u - v) hself)
  have hsurj : Function.Surjective
      (spEnd h + 1 : (Fin n ⊕ Fin n → ZMod 2) →ₗ[ZMod 2] _) := by
    haveI : Finite (Fin n ⊕ Fin n → ZMod 2) := Finite.of_fintype _
    exact Finite.surjective_of_injective hinj
  intro x
  have hDzero : D x = 0 := by
    obtain ⟨z, hz⟩ := hsurj x
    rw [← hz]
    calc
      D ((spEnd h + 1) z) = D (spEnd h z + z) := by rfl
      _ = D (spEnd h z) + D z := hDadd (spEnd h z) z
      _ = D z + D z := by rw [hDinv z]
      _ = 0 := by
        rw [← two_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod 2) 2 (D z)]
        simp [CharTwo.two_eq_zero]
  change Q (spEnd y x) + Q x = 0 at hDzero
  exact CharTwo.add_eq_zero.mp hDzero

end CFSG.StandardType.QTwo

end
