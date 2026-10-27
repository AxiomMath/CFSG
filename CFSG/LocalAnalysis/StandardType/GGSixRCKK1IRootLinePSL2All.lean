module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IRootLine

public section

namespace CFSG.StandardType.RCKK1I

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.RCKRP
  CFSG.StandardType.LieOddCover
open CFSG.Open (StatedLieTag StatedLieAdmissible)
open CFSG.StandardType.RCKSmall (RCKSmallTag)

private theorem rckRLt2a_line_scalars {f : ℕ} {i j : Fin 2} (hij : i ≠ j) {γ : Fin 1 → ℤ}
    (hγ : SpecialLinear.toStd 1 γ = Pi.single i 1 - Pi.single j 1) :
    ∃ ε : Multiplicative (GaloisField 2 f) ≃*
        (SpecialLinear.rootDatum 1 (GaloisField 2 f)).rootGroup γ,
      RCKRootLineScalars ((SpecialLinear.rootDatum 1 (GaloisField 2 f)).rootGroup γ)
        (GaloisField 2 f) ε := by
  let D : UniversalRootDatum (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :=
    SpecialLinear.rootDatum 1 (GaloisField 2 f)
  have hroot : D.rootGroup γ =
      (Matrix.SpecialLinearGroup.transvectionHom hij :
        Multiplicative (GaloisField 2 f) →*
          Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)).range :=
    SpecialLinear.rootGroup_eq 1 (GaloisField 2 f) hij hγ
  let φ : Multiplicative (GaloisField 2 f) →* D.rootGroup γ :=
    { toFun := fun a => ⟨Matrix.SpecialLinearGroup.transvection hij (Multiplicative.toAdd a), by
        rw [hroot]
        exact ⟨a, by rw [Matrix.SpecialLinearGroup.transvectionHom_apply]⟩⟩
      map_one' := Subtype.ext (by
        show Matrix.SpecialLinearGroup.transvection hij
          (Multiplicative.toAdd (1 : Multiplicative (GaloisField 2 f))) = 1
        rw [show Multiplicative.toAdd (1 : Multiplicative (GaloisField 2 f)) = 0 from rfl]
        exact Matrix.SpecialLinearGroup.transvection_coeff_zero hij)
      map_mul' := fun a b => Subtype.ext (by
        show Matrix.SpecialLinearGroup.transvection hij (Multiplicative.toAdd (a * b)) =
          Matrix.SpecialLinearGroup.transvection hij (Multiplicative.toAdd a) *
            Matrix.SpecialLinearGroup.transvection hij (Multiplicative.toAdd b)
        rw [toAdd_mul, Matrix.SpecialLinearGroup.transvection_add]) }
  have hφbij : Function.Bijective φ := by
    constructor
    · intro a b hab
      have h1 : Multiplicative.toAdd a = Multiplicative.toAdd b :=
        Matrix.SpecialLinearGroup.transvection_injective hij (congrArg Subtype.val hab)
      exact Multiplicative.toAdd.injective h1
    · intro y
      have hy : y.1 ∈ (Matrix.SpecialLinearGroup.transvectionHom hij :
          Multiplicative (GaloisField 2 f) →*
            Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)).range := by
        rw [← hroot]
        exact y.2
      obtain ⟨a, ha⟩ := hy
      exact ⟨a, Subtype.ext (by
        show Matrix.SpecialLinearGroup.transvection hij (Multiplicative.toAdd a) = y.1
        rw [← Matrix.SpecialLinearGroup.transvectionHom_apply]
        exact ha)⟩
  let ε : Multiplicative (GaloisField 2 f) ≃* D.rootGroup γ :=
    MulEquiv.ofBijective φ hφbij
  have hε : ∀ c : GaloisField 2 f,
      (ε (Multiplicative.ofAdd c) : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) =
        Matrix.SpecialLinearGroup.transvection hij c := by
    intro c
    show (φ (Multiplicative.ofAdd c) :
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) =
      Matrix.SpecialLinearGroup.transvection hij c
    change Matrix.SpecialLinearGroup.transvection hij
      (Multiplicative.toAdd (Multiplicative.ofAdd c)) =
      Matrix.SpecialLinearGroup.transvection hij c
    rw [toAdd_ofAdd]
  have hscal : RCKRootLineScalars (D.rootGroup γ) (GaloisField 2 f) ε := by
    intro l hl
    obtain ⟨s, hs⟩ := (Function.Injective.bijective_of_finite
      (CharTwo.sq_injective (R := GaloisField 2 f))).2 l
    have hs0 : s ≠ 0 := by
      rintro rfl
      exact hl (by simpa using hs.symm)
    let u : (GaloisField 2 f)ˣ := Units.mk0 s hs0
    have hu : (u : GaloisField 2 f) * (u : GaloisField 2 f) = l := by
      show s * s = l
      rw [← pow_two]
      simpa using hs
    refine ⟨Matrix.SpecialLinearGroup.diag2nUnit hij u, fun c => ?_⟩
    have hcoe : ((Matrix.SpecialLinearGroup.diag2nUnit hij u :
        Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 f)) =
        Matrix.diagonal (fun r : Fin 2 => if r = i then (u : GaloisField 2 f)
          else if r = j then ((u⁻¹ : (GaloisField 2 f)ˣ) : (GaloisField 2 f))
          else 1) :=
      Matrix.SpecialLinearGroup.diag2nUnit_coe hij u
    rw [hε c, hε (l * c),
      SpecialLinear.conj_transvection_of_coe_eq_diagonal
        (g := Matrix.SpecialLinearGroup.diag2nUnit hij u) hcoe hij c]
    congr 1
    rw [← hu]
    simp [hij, Ne.symm hij]
    ring
  exact ⟨ε, hscal⟩

theorem rckK1I_rootLineAll_PSL2
    {f : ℕ} (hadm : StatedLieAdmissible .PSL 2 2 f) :
    0 < (ggU .PSL 2 f).D.rank ∧ RCKRootLineAll (ggU .PSL 2 f) f := by
  have hf : 1 ≤ f := hadm.2.1
  have hrank : 0 < (ggU .PSL 2 f).D.rank := by
    show 0 < (SpecialLinear.rootDatum 1 (GaloisField 2 f)).rank
    exact Nat.zero_lt_one
  refine ⟨hrank, ?_⟩
  intro δ hδ _
  have hδ' : δ ∈ CFSG.LieType.RootSystem.roots (SpecialLinear.isFiniteType_A 1)
      (∅ : Set (Fin 1)) := hδ
  rw [SpecialLinear.roots_eq] at hδ'
  obtain ⟨i, j, hij, hstd⟩ := hδ'
  obtain ⟨ε, hsc⟩ := rckRLt2a_line_scalars (f := f) hij hstd
  exact ⟨GaloisField 2 f, inferInstance, inferInstance, ε,
    GaloisField.card 2 f (by omega), hsc⟩

end CFSG.StandardType.RCKK1I
