module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommPrincipalLayersModels
public import CFSG.LocalAnalysis.SteinbergSFSingleCommTorusLayerAut
public import CFSG.LocalAnalysis.SteinbergSFLinearUnitaryThreeBaseField

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace PrincipalLayers

open Subgroup TorusLayer CFSG.RankThree.PartOne.KCRootAxis
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedProj StatedSL StatedSU StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (conjAut dualAut)
open CFSG.ClassicalGroups.UnitaryFlag (unitaryPSUEquiv)
open CFSG.RankThree.PartTwo.KFacts (unitaryIsom3 psuConj psuField)
open LinearUnitaryThree (barEquiv)
open scoped MatrixGroups

@[expose] def SylowConclusion {F : Type} [Group F] (Y V : Subgroup F) (t : F) : Prop :=
  (∃ R : Sylow 2 ↥Y, (R : Subgroup ↥Y).map Y.subtype = V) ∧ t ∉ Y ∧
    ∃ R : Sylow 2 ↥(Y ⊔ zpowers t),
      (R : Subgroup ↥(Y ⊔ zpowers t)).map (Y ⊔ zpowers t).subtype = V ⊔ zpowers t

@[expose] def NontrivialAxisConclusion (F : Type) [Group F] [Finite F] (K : Type) [Field K]
    (n : ℕ) (S Y V : Subgroup F) (t : F) : Prop :=
  let R := CFSG.Open.standardComponentOddCore F
  let θ : F →* F ⧸ R := QuotientGroup.mk' R
  let Sb := S.map θ
  let D := normalClosure (Sb : Set (F ⧸ R))
  let a := θ t
  (∀ p f : ℕ, p ≠ 2 → ¬ StatedClassicalModel ↥D .PSL 2 p f) ∧
  (∀ m : ℕ, ¬ StatedClassicalModel ↥D .PSL 2 2 m) ∧
  (∀ m : ℕ, StatedClassicalModel ↥D .PSL 3 2 m ∨ StatedClassicalModel ↥D .PSU 3 2 m →
    m = n ∧ SylowConclusion Y V t) ∧
  ((∀ y : Y, θ y = 1 ↔ y ∈ center ↥Y) ∧
    (center ↥Y).map Y.subtype = (CFSG.Open.standardComponentOddCore ↥Y).map Y.subtype ∧
    (CFSG.Open.standardComponentOddCore ↥Y).map Y.subtype = Y ⊓ R) ∧
  (∀ (m : ℕ) (F' : Type) [Field F'] [Finite F'], Nat.card F' = 2 ^ m →
    ∀ η : ↥D ≃* StatedProj (StatedSL 3 F'),
    let Z := (StatedScalars (Fin 3) F').subgroupOf (StatedSL 3 F')
    let π : ↥(StatedSL 3 F') →* StatedProj (StatedSL 3 F') := QuotientGroup.mk' Z
    m = n ∧ Sb = D ⊓ centralizer ({a} : Set (F ⧸ R)) ∧
    (∃ H : GL (Fin 3) F', ∀ d d' : ↥D, (d' : F ⧸ R) = a⁻¹ * d * a →
      conjAut 3 F' H (statedProjEquivProjectiveSL 3 F' (η d')) =
        dualAut 3 F' (conjAut 3 F' H (statedProjEquivProjectiveSL 3 F' (η d)))) ∧
    ∃ γ : ↥(StatedSL 3 F') →* ↥Y, (∀ x, θ (γ x : F) = (η.symm (π x) : F ⧸ R)) ∧
      (∀ γ' : ↥(StatedSL 3 F') →* ↥Y, (∀ x, θ (γ' x : F) = (η.symm (π x) : F ⧸ R)) →
        γ' = γ) ∧
      Function.Surjective γ ∧ γ.ker ≤ Z ∧ Z.map γ = center ↥Y ∧
      (∃ e : ↥(StatedSL 3 F') ⧸ γ.ker ≃* ↥Y, ∀ x, e (QuotientGroup.mk x) = γ x) ∧
      IsCyclic (center ↥Y) ∧ Nat.card (center ↥Y) ∣ Nat.gcd 3 (2 ^ n - 1)) ∧
  (∀ (m : ℕ) (F' : Type) [Field F'] (hF' : UnitaryFieldData 2 m F'),
    ∀ η : ↥D ≃* StatedProj (StatedSU 3 (2 ^ m) F'),
    let Z := (StatedScalars (Fin 3) F').subgroupOf (StatedSU 3 (2 ^ m) F')
    let π : ↥(StatedSU 3 (2 ^ m) F') →* StatedProj (StatedSU 3 (2 ^ m) F') :=
      QuotientGroup.mk' Z
    m = n ∧ Sb = D ⊓ centralizer ({a} : Set (F ⧸ R)) ∧
    (∃ H : unitaryIsom3 hF', ∀ d d' : ↥D, (d' : F ⧸ R) = a⁻¹ * d * a →
      psuConj hF' H ((unitaryPSUEquiv hF' (n := 3) (by norm_num)).symm (η d')) =
        psuField hF' (barEquiv hF')
          (psuConj hF' H ((unitaryPSUEquiv hF' (n := 3) (by norm_num)).symm (η d)))) ∧
    ∃ γ : ↥(StatedSU 3 (2 ^ m) F') →* ↥Y, (∀ x, θ (γ x : F) = (η.symm (π x) : F ⧸ R)) ∧
      (∀ γ' : ↥(StatedSU 3 (2 ^ m) F') →* ↥Y,
        (∀ x, θ (γ' x : F) = (η.symm (π x) : F ⧸ R)) → γ' = γ) ∧
      Function.Surjective γ ∧ γ.ker ≤ Z ∧ Z.map γ = center ↥Y ∧
      (∃ e : ↥(StatedSU 3 (2 ^ m) F') ⧸ γ.ker ≃* ↥Y, ∀ x, e (QuotientGroup.mk x) = γ x) ∧
      IsCyclic (center ↥Y) ∧ Nat.card (center ↥Y) ∣ Nat.gcd 3 (2 ^ n + 1))

structure AxisData (F : Type) [Group F] [Finite F] (K : Type) [Field K] (n : ℕ)
    (S J Y V U : Subgroup F) (t : F) (hk : SL₂ K → F) : Prop where
  layer : TorusLayerConclusion F K n S J Y V t hk
  two_le : 2 ≤ n
  card_K : Nat.card K = 2 ^ n
  equiv : ∃ e : SL₂ K ≃* ↥S, ∀ X, (e X : F) = hk X
  order_t : orderOf t = 2
  perfect : Group.IsPerfect ↥Y
  Y_normal : Y.Normal
  S_le_Y : S ≤ Y
  V_le : V ≤ Y
  V_pgroup : IsPGroup 2 V
  t_mem : t ∈ normalizer (V : Set F)
  U_le_S : U ≤ S
  U_le_V : U ≤ V
  U_comm : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x
  U_sq : ∀ x ∈ U, x * x = 1
  U_card : Nat.card U = 2 ^ n
  U_sylow : ∃ R : Sylow 2 ↥S, (R : Subgroup ↥S).map S.subtype = U
  upper_mem : hk (RootStandard.upperSL 1) ∈ U

end PrincipalLayers

end CFSG.LocalAnalysis.SymplecticFourStandard
