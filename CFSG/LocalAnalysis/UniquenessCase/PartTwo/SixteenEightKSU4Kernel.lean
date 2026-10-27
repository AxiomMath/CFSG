module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8RowBase
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4V1Model
import CFSG.Quasithin.Vol2.GoldschmidtF431UnModel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22 Matrix
open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

private theorem s16k_center_eq_bot_of_mulEquiv {X Y : Type*} [Group X] [Group Y]
    (φ : X ≃* Y) (h : Subgroup.center Y = ⊥) : Subgroup.center X = ⊥ :=
  (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center X) φ.injective).1 <| by
    rw [Subgroup.map_center_eq φ, h]

private theorem s16k_card_psu_four_two_one :
    Nat.card (CFSG.Blueprint.Multiplier.generic .PSU 4 2 1 ×
      CFSG.Blueprint.Multiplier.exceptional .PSU 4 2 1) = 2 := by
  simp only [CFSG.Blueprint.Multiplier.generic, CFSG.Blueprint.Multiplier.exceptional,
    CFSG.Blueprint.Multiplier.genericOrders, CFSG.Blueprint.Multiplier.exceptionalOrders,
    Nat.card_prod]
  norm_num [ZMod.card, Nat.card_eq_fintype_card]

private theorem s16k_su4_center_mult (hGA : CFSG.Open.GriessAllModelsStatement)
    {X : Type} [Group X] (h : IsSUn X 4 1) :
    Subgroup.center X = ⊥ ∧ Nat.card (CFSG.Open.griessHopfMultiplier X) = 2 := by
  obtain ⟨E, hEfield, hEfinite, hE, ⟨e⟩⟩ := h
  letI : Field E := hEfield
  letI : Finite E := hEfinite
  haveI : Fintype E := Fintype.ofFinite E
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP E 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := 1) hE
  have hnq : ((4 : ℕ), 2 ^ 1) ≠ (3, 2) := by decide
  have hSU := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    (p := 2) (f := 1) (n := 4) hE (by norm_num) hnq
  haveI : Group.IsPerfect ↥(StatedSU 4 (2 ^ 1) E) := hSU.1.1
  have hSUbot : (StatedScalars (Fin 4) E).subgroupOf (StatedSU 4 (2 ^ 1) E) = ⊥ :=
    CFSG.Quasithin.H13.F431.Un.statedScalars_inf_eq_bot (f := 1) hE
  have hprojSU : StatedProj (StatedSU 4 (2 ^ 1) E) ≃* ↥(StatedSU 4 (2 ^ 1) E) :=
    (QuotientGroup.quotientMulEquivOfEq hSUbot).trans QuotientGroup.quotientBot
  have hmodeliso : X ≃* StatedProj (StatedSU 4 (2 ^ 1) E) := e.trans hprojSU.symm
  have hZproj : Subgroup.center (StatedProj (StatedSU 4 (2 ^ 1) E)) = ⊥ :=
    s16k_center_eq_bot_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hSU.2.symm)
      (Group.IsPerfect.center_quotient_center_eq_bot (G := ↥(StatedSU 4 (2 ^ 1) E)))
  have hZX : Subgroup.center X = ⊥ := s16k_center_eq_bot_of_mulEquiv hmodeliso hZproj
  have hclass : StatedClassicalModel X .PSU 4 2 1 :=
    ⟨⟨Nat.prime_two, le_refl 1, by norm_num, hnq⟩, E, inferInstance, inferInstance, hE,
      ⟨hmodeliso⟩⟩
  have hmodel : CFSG.Models.LieModel X .PSU 4 2 1 := ⟨hclass.1, Or.inl hclass⟩
  obtain ⟨-, ⟨m⟩⟩ := hGA X .PSU 4 2 1 hmodel
  exact ⟨hZX, by rw [Nat.card_congr m.toEquiv]; exact s16k_card_psu_four_two_one⟩

private theorem s16k_fixOrd_statedSU_four {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ 1) ^ 2) : FixOrd (StatedSU 4 (2 ^ 1) K) 3 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : Fintype K := Fintype.ofFinite K
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  haveI : CharP K 2 := CFSG.ClassicalGroups.Unitary.charP_of_card_sq (p := 2) (f := 1) hK
  let σ : K ≃+* K := unitaryInvolution K 2 1
  have hσ : IsUnitaryInvolution σ :=
    isUnitaryInvolution_unitaryInvolution (p := 2) (f := 1) hK
  have heq : SUid σ 4 = StatedSU 4 (2 ^ 1) K :=
    SUid_eq_statedSU (p := 2) (f := 1) hK 4
  rw [← heq]
  intro a ha
  have hv : Multiplicative.toAdd a ≠ 0 := fun h =>
    ha (by rw [← ofAdd_toAdd a, h, ofAdd_zero])
  obtain ⟨γ, hγ1, hγ3, hγfix⟩ := s16c4v1_stab_ne_zero (σ := σ) hK4 hσ hv
  refine ⟨γ, orderOf_eq_prime hγ3 hγ1, ?_⟩
  change Multiplicative.ofAdd (Matrix.mulVec
    (((γ : GL (Fin 4) K)) : Matrix (Fin 4) (Fin 4) K) (Multiplicative.toAdd a)) = a
  have hvfix : (((γ : GL (Fin 4) K)) : Matrix (Fin 4) (Fin 4) K) *ᵥ
      Multiplicative.toAdd a = Multiplicative.toAdd a := by
    simpa [CFSG.ClassicalGroups.Unitary.smul_def] using hγfix
  rw [hvfix, ofAdd_toAdd]

theorem s16k_false_of_su4_kernel (h : S16gRowCtx D V₀ V L hV)
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSU : IsSUn ↥(lBar V₀ V hV L) 4 1)
    (hN : NatSUn (lBar V₀ V hV L) (commSub ⊤ (lBar V₀ V hV L))
      (commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) 4 1)
    (hσ : 3 ∈ D.sig) (hrk : CFSG.Open.pRank 3 (Mbar D.M V₀ V hV) ≤ 3) : False := by
  obtain ⟨K, hF, hFin, hK, hR⟩ := hN
  letI : Field K := hF
  letI : Finite K := hFin
  obtain ⟨hcenter, hmultcard⟩ := s16k_su4_center_mult hGA hSU
  refine h.false_of_fixOrd hR hσ ?_ ?_ hrk ?_
  · rw [hcenter, Subgroup.card_bot]
    exact odd_one
  · rw [hmultcard]
    norm_num
  · exact s16k_fixOrd_statedSU_four hK

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
