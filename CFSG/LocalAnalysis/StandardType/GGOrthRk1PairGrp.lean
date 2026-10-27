module

public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Anisotropic.Embed
public import CFSG.ClassicalInvolution.Phan.Defs
public import CFSG.LieType.BorelTits.UnitaryForm
public import CFSG.RankThree.PartOne.CTP.PhanBridge
public import CFSG.Assembly.QuasithinDefs
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Anisotropic.Plane
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Pairs
public import CFSG.ClassicalInvolution.WeakCT.StandardPair
public import CFSG.LieType.CurtisTits.SpecialLinear
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Exceptional.E6E7
public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Steinberg.G2
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.S10.Defs
public import CFSG.RankThree.PartOne.S12.Hyp
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

open Module QuadraticMap Matrix

namespace CFSG.StandardType

namespace OrthTorus

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Unitary
  CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg CFSG.LieType.BorelTits

section Comm

variable {K K' V : Type} [Field K] [Field K'] [Algebra K K'] {σ : K' ≃+* K'} [AddCommGroup V]
  [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}

@[expose] def diagMap (a : Fin 3 → K') : (Fin 3 → K') →ₗ[K] (Fin 3 → K') :=
  LinearMap.pi fun l => (LinearMap.mulLeft K (a l)) ∘ₗ (LinearMap.proj l : (Fin 3 → K') →ₗ[K] K')

theorem diagMap_apply (a z : Fin 3 → K') (l : Fin 3) : diagMap (K := K) a z l = a l * z l :=
  rfl

theorem diagMap_smul_embSUid (c : Fin 3) (a : Fin 3 → K') (hac : ∀ l l' : Fin 3, l ≠ c → l' ≠ c →
    a l = a l') (A : SUid σ 2) (z : Fin 3 → K') :
    diagMap (K := K) a (embSUid σ c A • z) = embSUid σ c A • diagMap (K := K) a z := by
  funext l
  fin_cases c <;> fin_cases l <;>
    simp (config := { decide := true }) [smul_def, coe_embSUid, diagMap_apply, embPair,
      Matrix.mulVec_apply_eq_sum, Fin.sum_univ_three, Fin.sum_univ_two, Matrix.vecHead,
      Matrix.vecTail]
  all_goals
    try rw [hac 0 1 (by decide) (by decide)]
    try rw [hac 0 2 (by decide) (by decide)]
    try rw [hac 1 2 (by decide) (by decide)]
    try ring_nf
    try simp

theorem normTriple_theta_mul_comm (hσ : IsUnitaryInvolution σ) (T : NormTriple Q σ)
    (S : V ≃ₗ[K] V) (hS : ∀ x, Q (S x) = Q x) (M M' : (Fin 3 → K') →ₗ[K] (Fin 3 → K'))
    (hM : ∀ z, S (T.incl z) = T.incl (M z)) (hM' : ∀ z, S⁻¹ (T.incl z) = T.incl (M' z))
    (g : SUid σ 3) (hg : ∀ z, M (g • z) = g • M z) :
    S * (T.toEmbedding hσ).theta g = (T.toEmbedding hσ).theta g * S := by
  let D := T.toEmbedding hσ
  change S * D.theta g = D.theta g * S
  have hpolar : ∀ z y, polar Q (T.incl z) y =
      polar Q (T.incl z) (T.incl (D.coords y)) := fun z y => D.polar_coords z y
  have hcoords_incl : ∀ w, D.coords (T.incl w) = w := fun w => D.coords_incl w
  have hS' : ∀ x y, polar Q (S x) (S y) = polar Q x y := by
    intro x y
    rw [QuadraticMap.polar, QuadraticMap.polar, ← map_add, hS (x + y), hS x, hS y]
  have hswap : ∀ z y, polar Q (T.incl z) (S y) =
      polar Q (T.incl (M' z)) (T.incl (D.coords y)) := by
    intro z y
    calc polar Q (T.incl z) (S y)
        = polar Q (S (S.symm (T.incl z))) (S y) := by rw [LinearEquiv.apply_symm_apply]
      _ = polar Q (S.symm (T.incl z)) y := hS' _ _
      _ = polar Q (T.incl (M' z)) y := by
          rw [show S.symm (T.incl z) = T.incl (M' z) from hM' z]
      _ = polar Q (T.incl (M' z)) (T.incl (D.coords y)) := hpolar (M' z) y
  have hcoords : ∀ x, D.coords (S x) = M (D.coords x) := by
    intro x
    have hA : ∀ z, polar Q (T.incl z) (T.incl (D.coords (S x))) =
        polar Q (T.incl (M' z)) (T.incl (D.coords x)) :=
      fun z => (hpolar z (S x)).symm.trans (hswap z x)
    have hB : ∀ z, polar Q (T.incl z) (T.incl (M (D.coords x))) =
        polar Q (T.incl (M' z)) (T.incl (D.coords x)) := by
      intro z
      refine (congrArg (polar Q (T.incl z)) (hM (D.coords x)).symm).trans ?_
      refine (hswap z (T.incl (D.coords x))).trans ?_
      exact congrArg (polar Q (T.incl (M' z)))
        (congrArg T.incl (hcoords_incl (D.coords x)))
    have hkey : ∀ z, polar Q (T.incl z) (T.incl (D.coords (S x) - M (D.coords x))) = 0 := by
      intro z
      rw [map_sub, polar_sub_right, hA z, hB z, sub_self]
    have hu : D.coords (S x) - M (D.coords x) = 0 :=
      T.eq_zero_of_polar hσ (x := D.coords (S x) - M (D.coords x)) fun y => by
        rw [polar_comm]; exact hkey y
    exact sub_eq_zero.mp hu
  refine LinearEquiv.ext fun x => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  calc S (D.theta g x)
      = S (x + D.incl (g • D.coords x - D.coords x)) := by rw [D.theta_apply]
    _ = S x + T.incl (M (g • D.coords x - D.coords x)) := by
        rw [map_add]
        congr 1
        exact hM (g • D.coords x - D.coords x)
    _ = S x + T.incl (g • M (D.coords x) - M (D.coords x)) := by rw [map_sub, hg]
    _ = D.theta g (S x) := by
        rw [D.theta_apply, hcoords x]
        rfl

end Comm

section Blocks

variable {K K' : Type} [Field K] [Finite K] [CharP K 2] [Field K'] [Finite K'] [CharP K' 2] {f : ℕ}

private theorem q2cO4g_sl2_closure_involutions_eq_top {F : Type} [Field F] [CharP F 2] :
    Subgroup.closure {g : Matrix.SpecialLinearGroup (Fin 2) F | g ^ 2 = 1} = ⊤ := by
  rw [eq_top_iff]
  rw [← Matrix.SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field
    (K := F) (ι := Fin 2)]
  refine Subgroup.closure_mono ?_
  rintro g ⟨t, rfl⟩
  obtain ⟨i, j, hij, c⟩ := t
  rw [Matrix.TransvectionStruct.toSpecialLinearGroup_mk]
  change (Matrix.SpecialLinearGroup.transvection hij c) ^ 2 = 1
  have h := Matrix.SpecialLinearGroup.transvection_add (F := F) hij c c
  rw [CharTwo.add_self_eq_zero, Matrix.SpecialLinearGroup.transvection_coeff_zero] at h
  rw [pow_two]
  exact h.symm

theorem embSUid_range_closure (hf : Nat.card K = 2 ^ f) (hK' : Nat.card K' = (2 ^ f) ^ 2)
    (c : Fin 3) :
    Subgroup.closure {g : SUid (unitaryInvolution K' 2 f) 3 |
      g ∈ (embSUid (unitaryInvolution K' 2 f) c).range ∧ g ^ 2 = 1} =
      (embSUid (unitaryInvolution K' 2 f) c).range := by
  obtain ⟨e⟩ := CFSG.RankThree.PartOne.CTP.exists_suid_two_equiv_sl hK' hf (K₀ := K)
  have hS2 : Subgroup.closure {g : SUid (unitaryInvolution K' 2 f) 2 | g ^ 2 = 1} = ⊤ := by
    have hset : {g : SUid (unitaryInvolution K' 2 f) 2 | g ^ 2 = 1} =
        (e.symm : Matrix.SpecialLinearGroup (Fin 2) K →*
          SUid (unitaryInvolution K' 2 f) 2) '' {g : Matrix.SpecialLinearGroup (Fin 2) K |
            g ^ 2 = 1} := by
      ext g
      constructor
      · intro hg
        refine ⟨e g, ?_, ?_⟩
        · change (e g) ^ 2 = 1
          rw [← map_pow, hg, map_one]
        · change e.symm (e g) = g
          exact e.symm_apply_apply g
      · rintro ⟨t, ht, rfl⟩
        change (e.symm t) ^ 2 = 1
        rw [← map_pow, ht, map_one]
    rw [hset, ← MonoidHom.map_closure (e.symm : Matrix.SpecialLinearGroup (Fin 2) K →*
      SUid (unitaryInvolution K' 2 f) 2) {g : Matrix.SpecialLinearGroup (Fin 2) K | g ^ 2 = 1}]
    rw [q2cO4g_sl2_closure_involutions_eq_top]
    exact Subgroup.map_top_of_surjective _ e.symm.surjective
  let ι := embSUid (unitaryInvolution K' 2 f) c
  change Subgroup.closure {g : SUid (unitaryInvolution K' 2 f) 3 |
      g ∈ ι.range ∧ g ^ 2 = 1} = ι.range
  refine le_antisymm ?_ ?_
  · rw [Subgroup.closure_le]
    rintro g ⟨hg, -⟩
    exact hg
  · have hrange : ι.range =
        (Subgroup.closure {g : SUid (unitaryInvolution K' 2 f) 2 | g ^ 2 = 1}).map ι := by
      rw [hS2]
      exact MonoidHom.range_eq_map ι
    conv_lhs => rw [hrange, MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro g ⟨s, hs, rfl⟩
    change ι s ∈ ι.range ∧ (ι s) ^ 2 = 1
    exact ⟨⟨s, rfl⟩, by rw [← map_pow, hs, map_one]⟩

theorem embSUid_range_natCard (hf : Nat.card K = 2 ^ f) (hK' : Nat.card K' = (2 ^ f) ^ 2)
    (c : Fin 3) :
    Nat.card (embSUid (unitaryInvolution K' 2 f) c).range =
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := by
  obtain ⟨e⟩ := CFSG.RankThree.PartOne.CTP.exists_suid_two_equiv_sl hK' hf (K₀ := K)
  have h1 : Nat.card (embSUid (unitaryInvolution K' 2 f) c).range =
      Nat.card (SUid (unitaryInvolution K' 2 f) 2) :=
    Nat.card_range_of_injective (embSUid_injective (unitaryInvolution K' 2 f) c)
  exact h1.trans (Nat.card_congr e.toEquiv)

end Blocks

end OrthTorus

end CFSG.StandardType

end
