module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.GF2n.Stroth80.HeringSec63Setup

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open scoped commutatorElement Matrix

namespace HS6

section Geom

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K] [CharP K 2]

structure OmegaGeom (Q' : QuadraticForm K (ι → K)) (m : ℕ) : Prop where
  nondeg : (polarBilin Q').Nondegenerate
  dim : Module.finrank K (ι → K) = 2 * m
  three_le : 3 ≤ m
  two : ∃ P P' : HypPair Q', P.Orth P'
  three : (∃ P₁ P₂ P₃ : HypPair Q', P₁.Orth P₂ ∧ P₁.Orth P₃ ∧ P₂.Orth P₃) ∨
    (m = 3 ∧ IsMinus Q' 3)

end Geom

theorem omegaGeom_plus {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ} (hm : 3 ≤ m) :
    OmegaGeom (quadPlus m K) m := by
  have hn : 0 < m := by omega
  have h := isPlus_quadPlus (K := K) m
  refine ⟨h.nondeg, h.finrank_eq, hm, ?_, Or.inl ?_⟩
  · exact ⟨plusFamily K hn 0, plusFamily K hn 1, plusFamily_orth hn 0 1 (by omega) (by omega)
      (by omega)⟩
  · exact ⟨plusFamily K hn 0, plusFamily K hn 1, plusFamily K hn 2,
      plusFamily_orth hn 0 1 (by omega) (by omega) (by omega),
      plusFamily_orth hn 0 2 (by omega) (by omega) (by omega),
      plusFamily_orth hn 1 2 (by omega) (by omega) (by omega)⟩

theorem omegaGeom_minus {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ} (hm : 3 ≤ m)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : OmegaGeom (quadMinus m K b c) m := by
  have hn : 0 < m - 1 := by omega
  have h := isMinus_quadMinus (K := K) (m := m) (by omega) hirr
  refine ⟨h.nondeg, h.finrank_eq, hm, ?_, ?_⟩
  · exact ⟨minusFamily K b c hn 0, minusFamily K b c hn 1,
      minusFamily_orth hn 0 1 (by omega) (by omega) (by omega)⟩
  · by_cases h3 : m = 3
    · exact Or.inr ⟨h3, h3 ▸ h⟩
    · exact Or.inl ⟨minusFamily K b c hn 0, minusFamily K b c hn 1, minusFamily K b c hn 2,
        minusFamily_orth hn 0 1 (by omega) (by omega) (by omega),
        minusFamily_orth hn 0 2 (by omega) (by omega) (by omega),
        minusFamily_orth hn 1 2 (by omega) (by omega) (by omega)⟩

section Model

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

structure OmegaModel (hc : Ctx M Q Z B) (t : G) {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] (Q' : QuadraticForm K (ι → K)) {X' : Subgroup (GL ι K)}
    (E : ElemMatrixIso Q' X') (φ : ↥(Rt M (LB M Q B) t) →* GL ι K)
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (ι → K)) (u : ι → K) : Prop where
  range : φ.range = X'
  ker : φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t)
  equi : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
    (w : G) = (s : G) * v * (s : G)⁻¹ →
      Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
        (φ s : Matrix ι ι K) *ᵥ Multiplicative.toAdd (ψ (QuotientGroup.mk v))
  Qu : Q' u = 0
  u0 : u ≠ 0
  hB : ∀ x : ι → K, (∃ b : ↥(Vt M (LB M Q B) B Z t), (b : G) ∈ B ∧ secVec ψ b = x) ↔
    ∃ c : K, x = c • u
  hL : ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ = E.LomGL u
  hLr : ∀ r : ↥(Rt M (LB M Q B) t),
    ((conjSubgroup (r : G) (LB M Q B)).subgroupOf (Rt M (LB M Q B) t)).map φ =
      E.LomGL ((φ r : Matrix ι ι K) *ᵥ u)

variable {hc : Ctx M Q Z B} {n : ℕ} {t : G} {m : ℕ} {X : Subgroup G}

theorem Env.exists_model (I : Inputs) (e : Env hc n t m X) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (K : Type) (_ : Field K) (_ : Finite K)
      (_ : CharP K 2) (Q' : QuadraticForm K (ι → K)) (X' : Subgroup (GL ι K))
      (E : ElemMatrixIso Q' X') (φ : ↥(Rt M (LB M Q B) t) →* GL ι K)
      (_ : (Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal)
      (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
        Multiplicative (ι → K)) (u : ι → K),
      Nat.card K = Nat.card Z ∧ OmegaGeom Q' m ∧ OmegaModel hc t Q' E φ ψ u := by
  have hs := e.hs.toSec5
  have hnatSO := natSO_of_omega e.hm e.hΩ
  obtain ⟨e', -, he, -⟩ := hc.hyp.cp
  rcases e.hΩ with ⟨K, fK, finK, hK, hnat⟩ | ⟨K, fK, finK, hK, b, c, hirr, hnat⟩
  · haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hK.trans he)
    haveI : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by have := e.hm; omega⟩⟩
    obtain ⟨φ, hφ, hker, hact⟩ := hnat
    obtain ⟨hnorm, hn, ψ, hψ⟩ := hact
    haveI := hn
    have hgeom := omegaGeom_plus (K := K) e.hm
    have h3 : 3 ≤ Module.finrank K (Fin m ⊕ Fin m → K) := by
      rw [hgeom.dim]; have := e.hm; omega
    obtain ⟨u, hQu, hu0, hB, -, hL, hr'⟩ := hc.omega_points_core I.h34 I.hRoot hs hnatSO hK
      (ElemMatrixIso.plus e.hm) (nondegenerate_polarBilin_quadPlus m K) h3
      (addCommutantScalar_statedOmegaPlus e.hm) φ hφ hker ψ hψ
      (hc.omega_singular I.h34 I.hRoot hs hnatSO hK (ElemMatrixIso.plus e.hm)
        (nondegenerate_polarBilin_quadPlus m K) h3 (addCommutantScalar_statedOmegaPlus e.hm)
        φ hφ ψ hψ)
    exact ⟨Fin m ⊕ Fin m, inferInstance, inferInstance, K, fK, finK, inferInstance, quadPlus m K,
      _, ElemMatrixIso.plus e.hm, φ, hn, ψ, u, hK, hgeom,
      ⟨hφ, hker, hψ, hQu, hu0, hB, hL, fun r => (hr' r).2⟩⟩
  · haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hK.trans he)
    haveI : Nonempty (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
    obtain ⟨φ, hφ, hker, hact⟩ := hnat
    obtain ⟨hnorm, hn, ψ, hψ⟩ := hact
    haveI := hn
    have hgeom := omegaGeom_minus (K := K) e.hm hirr
    have h3 : 3 ≤ Module.finrank K (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) := by
      rw [hgeom.dim]; have := e.hm; omega
    obtain ⟨u, hQu, hu0, hB, -, hL, hr'⟩ := hc.omega_points_core I.h34 I.hRoot hs hnatSO hK
      (ElemMatrixIso.minus (by have := e.hm; omega) hirr)
      (nondegenerate_polarBilin_quadMinus_of_finite m K hirr) h3
      (addCommutantScalar_statedOmegaMinus (by have := e.hm; omega) hirr) φ hφ hker ψ hψ
      (hc.omega_singular I.h34 I.hRoot hs hnatSO hK
        (ElemMatrixIso.minus (by have := e.hm; omega) hirr)
        (nondegenerate_polarBilin_quadMinus_of_finite m K hirr) h3
        (addCommutantScalar_statedOmegaMinus (by have := e.hm; omega) hirr) φ hφ ψ hψ)
    exact ⟨Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2, inferInstance, inferInstance, K, fK, finK,
      inferInstance, quadMinus m K b c, _, ElemMatrixIso.minus (by have := e.hm; omega) hirr, φ,
      hn, ψ, u, hK, hgeom, ⟨hφ, hker, hψ, hQu, hu0, hB, hL, fun r => (hr' r).2⟩⟩

end Model

end HS6

end CFSG.RankThree.GF2n.Stroth80
