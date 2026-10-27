module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJRootCoreOmDiag
public import CFSG.RankThree.PartOne.KC.OrthogonalBlockDet
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
import CFSG.LocalAnalysis.StandardType.GGSecFiveJRootCoreOmEigen
import CFSG.LocalAnalysis.GLTheoremA.CatA.T173SplitVanish
import CFSG.RankThree.PartOne.KC.OrthogonalFactorization
import CFSG.RankThree.PartOne.KC.OrthogonalInnerPlaneDefs
import CFSG.GroupTheory.HallHigmanPiCore
import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
import CFSG.LocalAnalysis.AGLEmbedding.Reduction
import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
import CFSG.RankThree.PartTwo.NotationBlocks
import CFSG.RankThree.PartTwo.Sec14.Std
import CFSG.RankThree.PartTwo.Sec15.F153L3C2Act
import CFSG.RankThree.PartTwo.Sec15.F153L3C2Defs
import CFSG.RankThree.PartTwo.Sec8.Pairs
import CFSG.RankThree.PartTwo.Sec8.Statements

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 Polynomial

private theorem jcoreOm_single_eigen {ι F : Type} [DecidableEq ι] [Field F]
    {x : (ι → F) ≃ₗ[F] (ι → F)} {w : ι → F} (hxa : ∀ v c, x v c = w c * v c) (c : ι) (r : F) :
    x (r • Pi.single c 1) = w c • (r • Pi.single c 1) := by
  refine (jcoreOm_eigen_iff hxa (w c) _).mpr fun b hb => ?_
  have hbc : b ≠ c := by
    rintro rfl
    exact hb rfl
  rw [Pi.smul_apply, Pi.single_eq_of_ne hbc, smul_zero]

private theorem jcoreOm_plusVec_eigen {n : ℕ} {F : Type} [Field F]
    {x : (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F)} {a : Fin n → Fˣ}
    (hxa : ∀ v c, x v c = ((Sum.elim a (fun k => (a k)⁻¹) c : Fˣ) : F) * v c) (k : Fin n)
    (r : F) :
    x (r • plusVec n F k true) = ((a k : Fˣ) : F) • (r • plusVec n F k true) ∧
      x (r • plusVec n F k false) = (((a k)⁻¹ : Fˣ) : F) • (r • plusVec n F k false) :=
  ⟨jcoreOm_single_eigen hxa (.inl k) r, jcoreOm_single_eigen hxa (.inr k) r⟩

private theorem jcoreOm_special_mk {n p : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (hp : p.Prime) (hp2 : p ≠ 2) {x : (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F)}
    (hxΩ : x ∈ orthDerived (quadPlus n F)) (hx : OddOrderIsometry (quadPlus n F) p x)
    {μ : Fˣ} (hμ : μ ≠ 1) {i j : Fin n} (hij : i ≠ j) (s t : Bool)
    (hjt : ∀ r : F, x (r • plusVec n F j t) = (μ : F) • (r • plusVec n F j t))
    (his : ∀ r : F, x (r • plusVec n F i s) = ((μ⁻¹ : Fˣ) : F) • (r • plusVec n F i s))
    (hins : ∀ r : F, x (r • plusVec n F i (!s)) = (μ : F) • (r • plusVec n F i (!s)))
    (hjnt : ∀ r : F, x (r • plusVec n F j (!t)) = ((μ⁻¹ : Fˣ) : F) • (r • plusVec n F j (!t))) :
    JCoreOmRootPair n F (specialBlock (quadPlus n F) x (X - C (μ : F))) := by
  have hQ := nondegenerate_polarBilin_quadPlus n F
  refine ⟨i, j, hij, s, t, fun c => ⟨?_, ?_⟩⟩
  · have ha := hjt 1
    rw [one_smul] at ha
    exact LocalAnalysis.GLTheoremA.T173S.eichler_mem_specialBlock (d := ⟨x, hxΩ⟩) hQ hp hp2
      hx.pow_eq_one hμ ha (his c)
  · have ha := hins 1
    rw [one_smul] at ha
    exact LocalAnalysis.GLTheoremA.T173S.eichler_mem_specialBlock (d := ⟨x, hxΩ⟩) hQ hp hp2
      hx.pow_eq_one hμ ha (hjnt c)

private theorem jcoreOm_ne_inv {F : Type} [Field F] [CharP F 2] {μ ν : Fˣ} (hμ : μ ≠ 1)
    (h₁ : ν = μ) (h₂ : ν⁻¹ = μ) : False := by
  rw [h₁] at h₂
  have h3 : (μ : F) ^ 2 = 1 ^ 2 := by
    rw [sq, sq, ← Units.val_mul, one_mul]
    nth_rewrite 1 [← h₂]
    rw [inv_mul_cancel, Units.val_one]
  exact hμ (Units.ext (CharTwo.sq_injective h3))

theorem jcoreOm_special {n p : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F - 1)
    {x : (Fin n ⊕ Fin n → F) ≃ₗ[F] (Fin n ⊕ Fin n → F)} (hxΩ : x ∈ orthDerived (quadPlus n F))
    (hx : OddOrderIsometry (quadPlus n F) p x) {a : Fin n → Fˣ}
    (hxa : ∀ v c, x v c = ((Sum.elim a (fun k => (a k)⁻¹) c : Fˣ) : F) * v c)
    {h : F[X]} (hh : h ∈ primaryFactors x.toLinearMap) (h1 : h ≠ X - 1)
    (hq : CFSG.IsQuasisimple ↥(specialBlock (quadPlus n F) x h)) :
    JCoreOmRootPair n F (specialBlock (quadPlus n F) x h) := by
  classical
  obtain ⟨μ, -, rfl⟩ := LocalAnalysis.GLTheoremA.T173S.exists_eq_X_sub_C_of_mem_primaryFactors
    hp hpq hx.pow_eq_one hh
  have hμ : μ ≠ 1 := by
    rintro rfl
    exact h1 (by rw [Units.val_one, C_1])
  haveI : Fact (Irreducible (X - C (μ : F))) := ⟨irreducible_X_sub_C _⟩
  have hm : 2 ≤ primaryMultiplicity x.toLinearMap (X - C (μ : F)) := by
    have hpos := hx.primaryMultiplicity_pos hh
    have hne : primaryMultiplicity x.toLinearMap (X - C (μ : F)) ≠ 1 := fun h' =>
      CFSG.RankThree.PartOne.KCOrthogonal.ne_bot_of_isQuasisimple hq
        (hx.specialBlock_eq_bot_of_finrank_eq_one hh h')
    omega
  have hW : ∀ v, v ∈ primaryComponent x.toLinearMap (X - C (μ : F)) ↔ x v = (μ : F) • v := by
    intro v
    rw [mem_primaryComponent, map_sub, aeval_X, aeval_C, LinearMap.sub_apply,
      Module.algebraMap_end_apply, sub_eq_zero, LinearEquiv.coe_coe]
  have hcard := jcoreOm_finrank_eigen hxa (μ : F) hW
  rw [finrank_primaryComponent, natDegree_X_sub_C, one_mul] at hcard
  have h2 : 1 < Nat.card {c // ((Sum.elim a (fun k => (a k)⁻¹) c : Fˣ) : F) = μ} := by
    rw [← hcard]
    exact hm
  obtain ⟨⟨c₁, hc₁⟩, ⟨c₂, hc₂⟩, hne⟩ := (Finite.one_lt_card_iff_nontrivial.mp h2).exists_pair_ne
  have hc : c₁ ≠ c₂ := fun h' => hne (Subtype.ext h')
  have he := jcoreOm_plusVec_eigen hxa
  rcases c₁ with i | i <;> rcases c₂ with j | j
  · have hai : a i = μ := Units.ext hc₁
    have haj : a j = μ := Units.ext hc₂
    refine jcoreOm_special_mk hp hp2 hxΩ hx hμ (fun h' => hc (congrArg Sum.inl h')) false true
      (fun r => ?_) (fun r => ?_) (fun r => ?_) (fun r => ?_)
    · rw [← haj]; exact (he j r).1
    · rw [← hai]; exact (he i r).2
    · rw [← hai]; exact (he i r).1
    · rw [← haj]; exact (he j r).2
  · have hai : a i = μ := Units.ext hc₁
    have haj : (a j)⁻¹ = μ := Units.ext hc₂
    have hij : i ≠ j := by
      rintro rfl
      exact jcoreOm_ne_inv hμ hai haj
    refine jcoreOm_special_mk hp hp2 hxΩ hx hμ hij false false
      (fun r => ?_) (fun r => ?_) (fun r => ?_) (fun r => ?_)
    · rw [← haj]; exact (he j r).2
    · rw [← hai]; exact (he i r).2
    · rw [← hai]; exact (he i r).1
    · rw [← haj, inv_inv]; exact (he j r).1
  · have hai : (a i)⁻¹ = μ := Units.ext hc₁
    have haj : a j = μ := Units.ext hc₂
    have hij : i ≠ j := by
      rintro rfl
      exact jcoreOm_ne_inv hμ haj hai
    refine jcoreOm_special_mk hp hp2 hxΩ hx hμ hij true true
      (fun r => ?_) (fun r => ?_) (fun r => ?_) (fun r => ?_)
    · rw [← haj]; exact (he j r).1
    · rw [← hai, inv_inv]; exact (he i r).1
    · rw [← hai]; exact (he i r).2
    · rw [← haj]; exact (he j r).2
  · have hai : (a i)⁻¹ = μ := Units.ext hc₁
    have haj : (a j)⁻¹ = μ := Units.ext hc₂
    refine jcoreOm_special_mk hp hp2 hxΩ hx hμ (fun h' => hc (congrArg Sum.inr h')) true false
      (fun r => ?_) (fun r => ?_) (fun r => ?_) (fun r => ?_)
    · rw [← haj]; exact (he j r).2
    · rw [← hai, inv_inv]; exact (he i r).1
    · rw [← hai]; exact (he i r).2
    · rw [← haj, inv_inv]; exact (he j r).1

end CFSG.StandardType

end
