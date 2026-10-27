module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.Open.GriessAllModelsStatement
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOMinusFacts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open

private theorem s16g_charP_two_of_card_eight {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 8) : CharP K 2 := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (f := 3) (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)

private theorem s16g_scalars_subgroupOf_statedSL_eq_bot {K : Type} [Field K] [Finite K]
    {n : ℕ} (hK : Nat.card K = 8) (hgcd : Nat.gcd n 7 = 1) :
    (StatedScalars (Fin n) K).subgroupOf (StatedSL n K) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hg
  have hmem : Matrix.GeneralLinearGroup.scalar (Fin n) c ∈ StatedSL n K := by
    rw [hc]; exact g.2
  have hdet := CFSG.Open.StatedAPI.mem_statedSL_iff.1 hmem
  rw [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
  have hcn : c ^ n = 1 := Units.ext (by simpa using hdet)
  have hc7 : c ^ 7 = 1 := by
    simpa [Nat.card_units, hK] using pow_card_eq_one' (G := Kˣ) (x := c)
  have hord : orderOf c = 1 := by
    apply Nat.dvd_one.1
    rw [← hgcd]
    exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hcn) (orderOf_dvd_of_pow_eq_one hc7)
  have hc1 : c = 1 := orderOf_eq_one_iff.1 hord
  exact Subtype.ext (by rw [← hc, hc1, map_one]; rfl)

private theorem s16g_center_statedSL_eq_bot {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = 8) (hgcd : Nat.gcd n 7 = 1) :
    Subgroup.center (StatedSL n K) = ⊥ := by
  have h : Subgroup.center (StatedSL n K) =
      (StatedScalars (Fin n) K).subgroupOf (StatedSL n K) :=
    (CFSG.LieType.Universal.Unitary.map_center_mulEquiv
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n K)).symm.trans
      (CFSG.Assembly.LowTwoRank.map_center_eq_statedScalars n K)
  rw [h, s16g_scalars_subgroupOf_statedSL_eq_bot hK hgcd]

private theorem s16g_center_statedSp_eq_bot {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 8) (n : ℕ) : Subgroup.center (StatedSp n K) = ⊥ := by
  have : CharP K 2 := s16g_charP_two_of_card_eight hK
  rw [CFSG.LieType.Universal.Symplectic.center_eq,
    CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot]

private theorem s16g_statedClassicalModel_statedSL {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn : 2 ≤ n) (hK : Nat.card K = 8) (hgcd : Nat.gcd n 7 = 1) :
    StatedClassicalModel (StatedSL n K) .PSL n 2 3 := by
  have hbot := s16g_scalars_subgroupOf_statedSL_eq_bot (K := K) (n := n) hK hgcd
  have hproj : StatedProj (StatedSL n K) ≃* StatedSL n K :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  refine ⟨⟨Nat.prime_two, by norm_num, hn, ?_, ?_⟩, K, inferInstance, inferInstance,
    by rw [hK]; norm_num, ⟨hproj.symm⟩⟩
  · rintro h
    exact absurd (congrArg Prod.snd h) (by norm_num)
  · rintro h
    exact absurd (congrArg Prod.snd h) (by norm_num)

private theorem s16g_statedClassicalModel_statedSp {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn : 2 ≤ n) (hK : Nat.card K = 8) :
    StatedClassicalModel (StatedSp n K) .PSp n 2 3 := by
  have : CharP K 2 := s16g_charP_two_of_card_eight hK
  have hbot := CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot (K := K) (n := n)
  have hproj : StatedProj (StatedSp n K) ≃* StatedSp n K :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  refine ⟨⟨Nat.prime_two, by norm_num, hn, ?_⟩, K, inferInstance, inferInstance,
    by rw [hK]; norm_num, ⟨hproj.symm⟩⟩
  rintro h
  exact absurd (congrArg Prod.snd h) (by norm_num)

private theorem s16g_card_generic_exceptional_psl_three :
    Nat.card (CFSG.Blueprint.Multiplier.generic .PSL 3 2 3 ×
      CFSG.Blueprint.Multiplier.exceptional .PSL 3 2 3) = 1 := by
  simp only [CFSG.Blueprint.Multiplier.generic, CFSG.Blueprint.Multiplier.exceptional,
    CFSG.Blueprint.Multiplier.genericOrders, CFSG.Blueprint.Multiplier.exceptionalOrders,
    Nat.card_prod]
  norm_num [ZMod.card, Nat.card_eq_fintype_card]

private theorem s16g_card_generic_exceptional_psl_four :
    Nat.card (CFSG.Blueprint.Multiplier.generic .PSL 4 2 3 ×
      CFSG.Blueprint.Multiplier.exceptional .PSL 4 2 3) = 1 := by
  simp only [CFSG.Blueprint.Multiplier.generic, CFSG.Blueprint.Multiplier.exceptional,
    CFSG.Blueprint.Multiplier.genericOrders, CFSG.Blueprint.Multiplier.exceptionalOrders,
    Nat.card_prod]
  norm_num [ZMod.card, Nat.card_eq_fintype_card]

private theorem s16g_card_generic_exceptional_psp_two :
    Nat.card (CFSG.Blueprint.Multiplier.generic .PSp 2 2 3 ×
      CFSG.Blueprint.Multiplier.exceptional .PSp 2 2 3) = 1 := by
  simp only [CFSG.Blueprint.Multiplier.generic, CFSG.Blueprint.Multiplier.exceptional,
    CFSG.Blueprint.Multiplier.genericOrders, CFSG.Blueprint.Multiplier.exceptionalOrders,
    Nat.card_prod]
  norm_num [ZMod.card, Nat.card_eq_fintype_card]

private theorem s16g_center_eq_bot_of_mulEquiv {X Y : Type*} [Group X] [Group Y]
    (φ : X ≃* Y) (h : Subgroup.center Y = ⊥) : Subgroup.center X = ⊥ :=
  (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center X) φ.injective).1 <| by
    rw [Subgroup.map_center_eq φ, h]

private theorem s16g_card_generic_exceptional_psu_four :
    Nat.card (CFSG.Blueprint.Multiplier.generic .PSU 4 2 3 ×
      CFSG.Blueprint.Multiplier.exceptional .PSU 4 2 3) = 1 := by
  simp only [CFSG.Blueprint.Multiplier.generic, CFSG.Blueprint.Multiplier.exceptional,
    CFSG.Blueprint.Multiplier.genericOrders, CFSG.Blueprint.Multiplier.exceptionalOrders,
    Nat.card_prod]
  norm_num [ZMod.card, Nat.card_eq_fintype_card]

private theorem s16g_center_statedOmega_quadMinus_three_eq_scalars {K : Type} [Field K]
    [Finite K] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hK : 2 < Nat.card K) :
    Subgroup.center (StatedOmega (StatedQuadMinus 3 K b c)) =
      (StatedScalars (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K).subgroupOf
        (StatedOmega (StatedQuadMinus 3 K b c)) := by
  refine le_antisymm ?_ (CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _)
  intro z hz
  rw [Subgroup.mem_subgroupOf]
  obtain ⟨d, hd⟩ := CFSG.ComponentClassification.RankTwoClassical.commutant_statedOmega_quadMinus
    (n := 3) hK (by norm_num) hirr (((z : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) :
        Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
          (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K))
    (fun Z hZ => by
      have h1 := (Subgroup.mem_center_iff.mp hz
        (⟨Z, hZ⟩ : StatedOmega (StatedQuadMinus 3 K b c))).symm
      simpa using congrArg (fun w : StatedOmega (StatedQuadMinus 3 K b c) =>
        ((w : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) :
          Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
            (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K)) h1)
  have hd0 : d ≠ 0 := by
    rintro rfl
    have h1 : ((z : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) :
        Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
          (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) = 0 := by
      rw [hd]; simp
    have hunit : IsUnit ((z : GL (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) :
        Matrix (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2)
          (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) := ⟨z.1, rfl⟩
    rw [h1] at hunit
    exact not_isUnit_zero hunit
  refine ⟨Units.mk0 d hd0, ?_⟩
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_scalar, hd, Matrix.smul_one_eq_diagonal]
  rfl

theorem s16g_trivial_sl3 (hGA : CFSG.Open.GriessAllModelsStatement) {X : Type} [Group X]
    [Finite X] (h : IsSLn X 3 3) :
    Nat.card (Subgroup.center X) = 1 ∧ Nat.card (CFSG.Open.griessHopfMultiplier X) = 1 := by
  obtain ⟨K, hKfield, hKfinite, hcard, ⟨e⟩⟩ := h
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  haveI : Fintype K := Fintype.ofFinite K
  have hK8 : Nat.card K = 8 := by rw [hcard]; norm_num
  have hbot : Subgroup.center (StatedSL 3 K) = ⊥ :=
    s16g_center_statedSL_eq_bot hK8 (by norm_num)
  have hclass : StatedClassicalModel X .PSL 3 2 3 :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm
      (s16g_statedClassicalModel_statedSL (by norm_num) hK8 (by norm_num))
  have hmodel : CFSG.Models.LieModel X .PSL 3 2 3 := ⟨hclass.1, Or.inl hclass⟩
  obtain ⟨-, ⟨m⟩⟩ := hGA X .PSL 3 2 3 hmodel
  refine ⟨?_, ?_⟩
  · rw [s16g_center_eq_bot_of_mulEquiv e hbot, Subgroup.card_bot]
  · rw [Nat.card_congr m.toEquiv]
    exact s16g_card_generic_exceptional_psl_three

theorem s16g_trivial_sl4 (hGA : CFSG.Open.GriessAllModelsStatement) {X : Type} [Group X]
    [Finite X] (h : IsSLn X 4 3) :
    Nat.card (Subgroup.center X) = 1 ∧ Nat.card (CFSG.Open.griessHopfMultiplier X) = 1 := by
  obtain ⟨K, hKfield, hKfinite, hcard, ⟨e⟩⟩ := h
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  haveI : Fintype K := Fintype.ofFinite K
  have hK8 : Nat.card K = 8 := by rw [hcard]; norm_num
  have hbot : Subgroup.center (StatedSL 4 K) = ⊥ :=
    s16g_center_statedSL_eq_bot hK8 (by norm_num)
  have hclass : StatedClassicalModel X .PSL 4 2 3 :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm
      (s16g_statedClassicalModel_statedSL (by norm_num) hK8 (by norm_num))
  have hmodel : CFSG.Models.LieModel X .PSL 4 2 3 := ⟨hclass.1, Or.inl hclass⟩
  obtain ⟨-, ⟨m⟩⟩ := hGA X .PSL 4 2 3 hmodel
  refine ⟨?_, ?_⟩
  · rw [s16g_center_eq_bot_of_mulEquiv e hbot, Subgroup.card_bot]
  · rw [Nat.card_congr m.toEquiv]
    exact s16g_card_generic_exceptional_psl_four

theorem s16g_trivial_sp4 (hGA : CFSG.Open.GriessAllModelsStatement) {X : Type} [Group X]
    [Finite X] (h : IsSpn X 4 3) :
    Nat.card (Subgroup.center X) = 1 ∧ Nat.card (CFSG.Open.griessHopfMultiplier X) = 1 := by
  simp only [IsSpn, Nat.reduceDiv] at h
  obtain ⟨-, K, hKfield, hKfinite, hcard, ⟨e⟩⟩ := h
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  haveI : Fintype K := Fintype.ofFinite K
  have hK8 : Nat.card K = 8 := by rw [hcard]; norm_num
  have hbot : Subgroup.center (StatedSp 2 K) = ⊥ := s16g_center_statedSp_eq_bot hK8 2
  have hclass : StatedClassicalModel X .PSp 2 2 3 :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm
      (s16g_statedClassicalModel_statedSp (n := 2) (by norm_num) hK8)
  have hmodel : CFSG.Models.LieModel X .PSp 2 2 3 := ⟨hclass.1, Or.inl hclass⟩
  obtain ⟨-, ⟨m⟩⟩ := hGA X .PSp 2 2 3 hmodel
  refine ⟨?_, ?_⟩
  · rw [s16g_center_eq_bot_of_mulEquiv e hbot, Subgroup.card_bot]
  · rw [Nat.card_congr m.toEquiv]
    exact s16g_card_generic_exceptional_psp_two

theorem s16g_trivial_omegaMinus6 (hGA : CFSG.Open.GriessAllModelsStatement) {X : Type}
    [Group X] [Finite X] (h : IsOmegaMinus X 6 3) :
    Nat.card (Subgroup.center X) = 1 ∧ Nat.card (CFSG.Open.griessHopfMultiplier X) = 1 := by
  simp only [IsOmegaMinus, Nat.reduceDiv] at h
  obtain ⟨-, K, hKfield, hKfinite, b, c, hcard, hirr, ⟨e⟩⟩ := h
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  haveI : Fintype K := Fintype.ofFinite K
  have hK8 : Nat.card K = 8 := by rw [hcard]; norm_num
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := s16g_charP_two_of_card_eight hK8
  obtain ⟨E, hEfield, hUFD, ⟨eSU⟩⟩ :=
    CFSG.ComponentClassification.RankTwoClassical.nonempty_statedOmega_quadMinus_three_equiv
      (m := 3) hcard hirr
  letI : Field E := hEfield
  haveI : Finite E := hUFD.finite
  have hE : Nat.card E = (2 ^ 3) ^ 2 := hUFD.card_eq_sq
  have hnq : ((4 : ℕ), 2 ^ 3) ≠ (3, 2) := by decide
  have hSU := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    (p := 2) (f := 3) (n := 4) hE (by norm_num) hnq
  have hZΩ := s16g_center_statedOmega_quadMinus_three_eq_scalars (K := K) (b := b) (c := c)
    hirr (by rw [hK8]; norm_num)
  have hmap : ((StatedScalars (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K).subgroupOf
        (StatedOmega (StatedQuadMinus 3 K b c))).map eSU =
      (StatedScalars (Fin 4) E).subgroupOf (StatedSU 4 (2 ^ 3) E) := by
    rw [← hZΩ]
    exact (Subgroup.map_center_eq eSU).trans hSU.2
  have hproj : StatedProj (StatedOmega (StatedQuadMinus 3 K b c)) ≃*
      StatedProj (StatedSU 4 (2 ^ 3) E) :=
    QuotientGroup.congr _ _ eSU hmap
  have hmodeliso : X ≃* StatedProj (StatedSU 4 (2 ^ 3) E) := e.trans hproj
  haveI : Group.IsPerfect (StatedSU 4 (2 ^ 3) E) := hSU.1.1
  have hZproj : Subgroup.center (StatedProj (StatedSU 4 (2 ^ 3) E)) = ⊥ :=
    s16g_center_eq_bot_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hSU.2.symm)
      (Group.IsPerfect.center_quotient_center_eq_bot (G := StatedSU 4 (2 ^ 3) E))
  have hZX : Subgroup.center X = ⊥ := s16g_center_eq_bot_of_mulEquiv hmodeliso hZproj
  have hclass : StatedClassicalModel X .PSU 4 2 3 :=
    ⟨⟨Nat.prime_two, by norm_num, by norm_num, hnq⟩, E, inferInstance, hUFD.finite, hE,
      ⟨hmodeliso⟩⟩
  have hmodel : CFSG.Models.LieModel X .PSU 4 2 3 := ⟨hclass.1, Or.inl hclass⟩
  obtain ⟨-, ⟨m⟩⟩ := hGA X .PSU 4 2 3 hmodel
  refine ⟨?_, ?_⟩
  · rw [hZX, Subgroup.card_bot]
  · rw [Nat.card_congr m.toEquiv]
    exact s16g_card_generic_exceptional_psu_four

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
