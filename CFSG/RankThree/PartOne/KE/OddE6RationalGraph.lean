module

public import CFSG.LieType.Chevalley.OddF4CosetDescent
public import CFSG.LieType.Chevalley.OrdinaryEOuterOrder

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit rootDiag)

@[expose] noncomputable def graphAut (K : Type) [Field K] (ε : ℕ) :
    MulAut (adjointGroup Tag.E6 K) :=
  exactNormalAut Tag.E6 K 1 1 ε

@[expose] noncomputable def diagramE6 (K : Type) [Field K] : ModGL Tag.E6 K :=
  diagramMap TwistTag.E6 K

variable {K : Type} [Field K]

theorem exactQ_E6 (ε : ℕ) : exactQ Tag.E6 K ε = diagramE6 K ^ ε := rfl

theorem baseChangeGL_diagramE6 {L : Type} [Field L] (f : K →+* L) :
    baseChangeGL f (diagramE6 K) = diagramE6 L :=
  baseChangeGL_diagramMap f TwistTag.E6

theorem diagramE6_mul_self : diagramE6 K * diagramE6 K = 1 := by
  have h2 : (diagramE6 K) ^ 2 = 1 := diagramMap_pow_order TwistTag.E6 K
  rwa [pow_two] at h2

theorem units_map_entrywiseHom_diagramE6 (σ : K →+* K) :
    Units.map (entrywiseHom σ) (diagramE6 K) = diagramE6 K :=
  units_map_entrywiseHom_diagramMap σ

theorem coe_graphAut (ε : ℕ) (h : adjointGroup Tag.E6 K) :
    (graphAut K ε h : ModGL Tag.E6 K) =
      exactQ Tag.E6 K ε * (h : ModGL Tag.E6 K) * (exactQ Tag.E6 K ε)⁻¹ := by
  rw [graphAut, coe_exactNormalAut, rootDiagUnit_one, inv_one, one_mul, mul_one]
  congr 2
  exact Units.ext (entrywise_id _)

theorem graphAut_zero : graphAut K 0 = 1 :=
  (rootDiagAut_eq_exactNormalAut (τ := Tag.E6) (K := K) 1).symm.trans
    (rootDiagAutHom Tag.E6 K).map_one

theorem graphAut_add (ε ε' : ℕ) : graphAut K (ε + ε') = graphAut K ε * graphAut K ε' := by
  have h := exactNormalAut_mul (τ := Tag.E6) (K := K) 1 1 1 1 ε ε'
  have e : (fun j => (1 : Fin Tag.E6.rank → Kˣ) j * Units.map (1 : K ≃+* K).toRingHom.toMonoidHom
      ((1 : Fin Tag.E6.rank → Kˣ) ((exactPerm Tag.E6 ε).symm j))) = 1 := by
    funext j
    simp
  rw [e, mul_one] at h
  exact h.symm

theorem graphAut_mod (ε : ℕ) : graphAut K (ε % 2) = graphAut K ε :=
  exactNormalAut_mod (τ := Tag.E6) (K := K) 1 1 ε

theorem graphAut_two : graphAut K 2 = 1 := by
  rw [← graphAut_mod, show 2 % 2 = 0 from rfl, graphAut_zero]

theorem entrywiseAdjointAut_eq_exactNormalAut (β : K ≃+* K) :
    entrywiseAdjointAut Tag.E6 β = exactNormalAut Tag.E6 K 1 β 0 := by
  refine MulEquiv.ext fun h => Subtype.ext ?_
  rw [coe_entrywiseAdjointAut, coe_exactNormalAut, rootDiagUnit_one, exactQ_zero]
  simp

theorem graphAut_comm_entrywise (ε : ℕ) (β : K ≃+* K) :
    graphAut K ε * entrywiseAdjointAut Tag.E6 β =
      entrywiseAdjointAut Tag.E6 β * graphAut K ε := by
  rw [entrywiseAdjointAut_eq_exactNormalAut, graphAut, exactNormalAut_mul, exactNormalAut_mul]
  have e1 : (fun j => (1 : Fin Tag.E6.rank → Kˣ) j * Units.map (1 : K ≃+* K).toRingHom.toMonoidHom
      ((1 : Fin Tag.E6.rank → Kˣ) ((exactPerm Tag.E6 ε).symm j))) = 1 := by
    funext j
    simp
  have e2 : (fun j => (1 : Fin Tag.E6.rank → Kˣ) j * Units.map β.toRingHom.toMonoidHom
      ((1 : Fin Tag.E6.rank → Kˣ) ((exactPerm Tag.E6 0).symm j))) = 1 := by
    funext j
    simp
  rw [e1, e2, mul_one, one_mul, add_zero, zero_add]

@[expose] noncomputable def graphFieldHom :
    Multiplicative (ZMod 2) × (K ≃+* K) →* MulAut (adjointGroup Tag.E6 K) where
  toFun x := graphAut K (Multiplicative.toAdd x.1).val * entrywiseAdjointAut Tag.E6 x.2
  map_one' := by
    simp only [Prod.fst_one, toAdd_one, ZMod.val_zero, graphAut_zero, Prod.snd_one,
      entrywiseAdjointAut_one, mul_one]
  map_mul' x y := by
    simp only [Prod.fst_mul, Prod.snd_mul, toAdd_mul, entrywiseAdjointAut_mul]
    have h1 : graphAut K ((Multiplicative.toAdd x.1 + Multiplicative.toAdd y.1).val) =
        graphAut K (Multiplicative.toAdd x.1).val * graphAut K (Multiplicative.toAdd y.1).val := by
      rw [ZMod.val_add, graphAut_mod, graphAut_add]
    rw [h1]
    calc graphAut K (Multiplicative.toAdd x.1).val * graphAut K (Multiplicative.toAdd y.1).val *
          (entrywiseAdjointAut Tag.E6 x.2 * entrywiseAdjointAut Tag.E6 y.2)
        = graphAut K (Multiplicative.toAdd x.1).val *
          (graphAut K (Multiplicative.toAdd y.1).val * entrywiseAdjointAut Tag.E6 x.2) *
            entrywiseAdjointAut Tag.E6 y.2 := by simp only [mul_assoc]
      _ = _ := by rw [graphAut_comm_entrywise, mul_assoc, mul_assoc, mul_assoc]

theorem graphFieldHom_apply (ε : ZMod 2) (β : K ≃+* K) :
    graphFieldHom (Multiplicative.ofAdd ε, β) = graphAut K ε.val * entrywiseAdjointAut Tag.E6 β :=
  rfl

end CFSG.RankThree.PartOne.KE
