module

public import CFSG.LocalAnalysis.StandardType.GGOuterInvLangDatumThrough
public import CFSG.LocalAnalysis.StandardType.GGOuterInvAtE6
public import CFSG.LocalAnalysis.StandardType.GGFieldOuterInvSolvable
public import CFSG.LocalAnalysis.StandardType.GGOuterInvAtE6OddLemmas
public import CFSG.LocalAnalysis.StandardType.GGOuterInvAtE6OddToral2
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Subnormal
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterFieldCore
public import CFSG.LieType.Chevalley.AlgebraicClosurePrimeField
public import CFSG.LieType.Chevalley.E6SecondGraphFixedSubgroup
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigid
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidCriterion
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm

public section

namespace CFSG.StandardType

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE

theorem baseChange_exactNormalAut_E6 {K L : Type} [Field K] [Field L] [Algebra K L]
    [ExpChar L 2] {a : Fin Tag.E6.rank → Kˣ} {σ : K ≃+* K} {ε e : ℕ}
    (hcomp : (iterateFrobenius L 2 e).comp (algebraMap K L) = (algebraMap K L).comp σ.toRingHom)
    (h : adjointGroup Tag.E6 K) :
    baseChangeGL (algebraMap K L)
        ((exactNormalAut Tag.E6 K a σ ε h : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
      rootDiagUnit Tag.E6 (fun i => Units.map (algebraMap K L).toMonoidHom (a i)) *
        exactQ Tag.E6 L ε *
        Units.map (entrywiseHom (iterateFrobenius L 2 e))
          (baseChangeGL (algebraMap K L) (h : ModGL Tag.E6 K)) *
        (exactQ Tag.E6 L ε)⁻¹ *
        (rootDiagUnit Tag.E6 (fun i => Units.map (algebraMap K L).toMonoidHom (a i)))⁻¹ := by
  have hQ : baseChangeGL (algebraMap K L) (exactQ Tag.E6 K ε) = exactQ Tag.E6 L ε := by
    rw [exactQ_E6, exactQ_E6, map_pow, baseChangeGL_diagramE6]
  have hσ : baseChangeGL (algebraMap K L)
      (Units.map (entrywiseHom σ.toRingHom) (h : ModGL Tag.E6 K)) =
      Units.map (entrywiseHom (iterateFrobenius L 2 e))
        (baseChangeGL (algebraMap K L) (h : ModGL Tag.E6 K)) := by
    rw [units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_baseChangeGL, ← hcomp,
      ← baseChangeGL_baseChangeGL, units_map_entrywiseHom_eq_baseChangeGL]
  rw [coe_exactNormalAut, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv,
    baseChangeGL_rootDiagUnit, hQ, hσ]

theorem mul_conj_mul_cancel {G : Type*} [Group G] (g₀ A D Q F₀ E : G) :
    (g₀⁻¹ * (A * D * Q * F₀)) * (F₀⁻¹ * E * F₀) * (g₀⁻¹ * (A * D * Q * F₀))⁻¹ =
      g₀⁻¹ * (A * D * Q * E * Q⁻¹ * D⁻¹ * A⁻¹) * g₀ := by
  group

theorem e6_baseChangeAction {K : Type} [Field K] [Finite K] [CharP K 2]
    [ExpChar (AlgebraicClosure K) 2] {s : ℕ} {σ : K ≃+* K}
    (hcomp : (iterateFrobenius (AlgebraicClosure K) 2 s).comp
        (algebraMap K (AlgebraicClosure K)) =
        (algebraMap K (AlgebraicClosure K)).comp σ.toRingHom)
    (g : adjointGroup Tag.E6 K) (a : Fin Tag.E6.rank → Kˣ) (ε : ℕ)
    (c : adjointGroup Tag.E6 K) :
    baseChangeGL (algebraMap K (AlgebraicClosure K))
        (((MulAut.conj g * exactNormalAut Tag.E6 K a σ ε) c : adjointGroup Tag.E6 K) :
          ModGL Tag.E6 K) =
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (g : ModGL Tag.E6 K) *
        rootDiagUnit Tag.E6
          (fun i => Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom (a i)) *
        exactQ Tag.E6 (AlgebraicClosure K) ε *
        Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure K) 2 s))
          (baseChangeGL (algebraMap K (AlgebraicClosure K)) (c : ModGL Tag.E6 K)) *
        (exactQ Tag.E6 (AlgebraicClosure K) ε)⁻¹ *
        (rootDiagUnit Tag.E6
          (fun i => Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom (a i)))⁻¹ *
        (baseChangeGL (algebraMap K (AlgebraicClosure K)) (g : ModGL Tag.E6 K))⁻¹ := by
  have hαc : (((MulAut.conj g * exactNormalAut Tag.E6 K a σ ε) c :
      adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
      (g : ModGL Tag.E6 K) *
        ((exactNormalAut Tag.E6 K a σ ε c : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) *
        (g : ModGL Tag.E6 K)⁻¹ := by
    rw [MulAut.mul_apply, MulAut.conj_apply]
    rfl
  rw [hαc, map_mul, map_mul, map_inv,
    baseChange_exactNormalAut_E6 (K := K) (L := AlgebraicClosure K) (a := a) (σ := σ)
      (ε := ε) (e := s) hcomp c]
  simp only [mul_assoc]

theorem e6_conjAction {K : Type} [Field K] [Finite K] [CharP K 2]
    [ExpChar (AlgebraicClosure K) 2] {s p : ℕ} {σ : K ≃+* K}
    (hcomp : (iterateFrobenius (AlgebraicClosure K) 2 s).comp
        (algebraMap K (AlgebraicClosure K)) =
        (algebraMap K (AlgebraicClosure K)).comp σ.toRingHom)
    (g : adjointGroup Tag.E6 K) (a : Fin Tag.E6.rank → Kˣ) (ε : ℕ)
    (S : LangSetup Tag.E6 (AlgebraicClosure K) p)
    (ι : ↥(adjointGroup Tag.E6 K) →* ModGL Tag.E6 (AlgebraicClosure K))
    (hιform : ∀ c, ι c = S.D.g0⁻¹ *
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (c : ModGL Tag.E6 K) * S.D.g0) :
    ∃ z' : ModGL Tag.E6 (AlgebraicClosure K),
      ∀ c, z' * Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure K) 2 s)) (ι c) *
          z'⁻¹ = ι ((MulAut.conj g * exactNormalAut Tag.E6 K a σ ε) c) := by
  classical
  set a' : Fin Tag.E6.rank → (AlgebraicClosure K)ˣ :=
    fun i => Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom (a i) with ha'
  set FrL : ModGL Tag.E6 (AlgebraicClosure K) →* ModGL Tag.E6 (AlgebraicClosure K) :=
    Units.map (entrywiseHom (iterateFrobenius (AlgebraicClosure K) 2 s)) with hFrL
  set QL : ModGL Tag.E6 (AlgebraicClosure K) := exactQ Tag.E6 (AlgebraicClosure K) ε with hQL
  set A : ModGL Tag.E6 (AlgebraicClosure K) :=
    baseChangeGL (algebraMap K (AlgebraicClosure K)) (g : ModGL Tag.E6 K) with hA
  set z' : ModGL Tag.E6 (AlgebraicClosure K) :=
    S.D.g0⁻¹ * (A * rootDiagUnit Tag.E6 a' * QL * FrL S.D.g0) with hz'
  have hBC : ∀ c : adjointGroup Tag.E6 K,
      baseChangeGL (algebraMap K (AlgebraicClosure K))
          (((MulAut.conj g * exactNormalAut Tag.E6 K a σ ε) c : adjointGroup Tag.E6 K) :
            ModGL Tag.E6 K) =
        A * rootDiagUnit Tag.E6 a' * QL *
          FrL (baseChangeGL (algebraMap K (AlgebraicClosure K)) (c : ModGL Tag.E6 K)) *
          QL⁻¹ * (rootDiagUnit Tag.E6 a')⁻¹ * A⁻¹ :=
    e6_baseChangeAction (K := K) (s := s) hcomp g a ε
  refine ⟨z', ?_⟩
  change ∀ c, z' * FrL (ι c) * z'⁻¹ =
    ι ((MulAut.conj g * exactNormalAut Tag.E6 K a σ ε) c)
  intro c
  have hFr : FrL (ι c) =
      (FrL S.D.g0)⁻¹ * FrL (baseChangeGL (algebraMap K (AlgebraicClosure K))
        (c : ModGL Tag.E6 K)) * FrL S.D.g0 := by
    rw [hιform c, map_mul, map_mul, map_inv]
  rw [hFr, hz', mul_conj_mul_cancel]
  rw [← hBC c, hιform]

end CFSG.StandardType
