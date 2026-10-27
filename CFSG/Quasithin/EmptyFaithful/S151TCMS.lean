module

public import CFSG.Quasithin.EmptyFaithful.S151TCC5A
public import CFSG.Quasithin.EmptyFaithful.S151TCC5B
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftOrigImages
public import CFSG.LocalAnalysis.SectionRank.OddCover.PrimeThree
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin.S151TC

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.S151TB

variable {G : Type} [Group G] [Finite G]

@[expose] def C27CaseG (K R M : Subgroup G) : Prop :=
  (∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F), 1 ≤ n ∧ Fintype.card F = 2 ^ n ∧
      Nonempty (↥(autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))) ≃*
        ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F))) ∧
    IsMaxParabolic2 (autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))))
      (autOn (M ⊓ K) (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)))) ∧
    IsMSPair (K ⊔ R) R

omit [Finite G] in
theorem mem_cComp_sup_of_normalizer {K R H : Subgroup G} (hK : K ∈ cComp H)
    (hRK : R ≤ Subgroup.normalizer (K : Set G)) : K ∈ cComp (K ⊔ R) := by
  obtain ⟨hne, hperf, hsub, hmin⟩ := hK
  refine ⟨hne, hperf, ?_, fun K' hK'K hK'ne hK'perf hK'sub => ?_⟩
  · exact IsSubnormal.step le_sup_left (Subgroup.normal_subgroupOf_of_le_normalizer
      (_root_.sup_le (fun x hx => Subgroup.le_normalizer hx) hRK)) (IsSubnormal.refl _)
  · exact hmin K' hK'K hK'ne hK'perf
      (A3.subnormal_trans (A3.subnormal_of_le_of_le hK'sub hK'K.le le_sup_left) hsub)

theorem commutator_ne_bot_of_caseG {K R M : Subgroup G} (h : C27CaseG K R M) :
    ⁅omegaOneCenterOf (pCoreOf 2 (K ⊔ R)), K⁆ ≠ ⊥ := by
  obtain ⟨⟨n, F, _, _, hn, hF, ⟨e⟩⟩, -, -⟩ := h
  intro hcomm
  have hKc : K ≤ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hcomm
  have hbot : autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ R))) = ⊥ :=
    CFSG.QuasithinUnique.Setup.Lift.autOn_eq_bot_of_le_centralizer hKc
  have hFfin : Finite F := Finite.of_fintype F
  have hcard1 : Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) = 1 := by
    rw [← Nat.card_congr e.toEquiv, hbot, Subgroup.card_bot]
  have hq : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  rw [CFSG.SectionRank.OddCover.card_statedSL_three_eq_mul hq] at hcard1
  have h2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h3 : 8 ≤ (2 ^ n) ^ 3 :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ (2 ^ n) ^ 3 := Nat.pow_le_pow_left h2 3
  have h4 : 1 ≤ (2 ^ n - 1) * (2 ^ n + 1) := Nat.mul_pos (by omega) (by omega)
  have h5 : 1 ≤ (2 ^ n - 1) * ((2 ^ n) ^ 2 + 2 ^ n + 1) := Nat.mul_pos (by omega) (by positivity)
  have : 8 ≤ (2 ^ n) ^ 3 * ((2 ^ n - 1) * (2 ^ n + 1)) *
      ((2 ^ n - 1) * ((2 ^ n) ^ 2 + 2 ^ n + 1)) :=
    le_trans h3 (by
      calc (2 ^ n) ^ 3 = (2 ^ n) ^ 3 * 1 * 1 := by ring
        _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_left _ h4) h5)
  omega

theorem isLnBlock_three_of_case5 {L R : Subgroup G} (hperf : ⁅L, L⁆ = L) (hchar : CharTwo L)
    (hq : CFSG.IsQuasisimple (LStar L)) (hRN : R ≤ Subgroup.normalizer (L : Set G))
    (hVL : ⁅omegaOneCenterOf (pCoreOf 2 (L ⊔ R)), L⁆ ≠ ⊥)
    (h5 : ∃ α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)), IsModO2Surj L α ∧
      Nat.card ↥(c134CQ (L ⊔ R) L) = 2 ∧
      IsSumOfNaturalModulesVia L (c134Q (L ⊔ R) L) (c134CQ (L ⊔ R) L) α false 1) :
    IsLnBlock L 3 := by
  obtain ⟨hlt, hirr⟩ := case5_irreducible hperf hRN h5
  exact ⟨isShort2_of_case5 hperf hchar hq hRN hVL h5 hlt hirr,
    isMatrixBlockType_three_of_case5 hperf hRN h5⟩

end CFSG.Quasithin.S151TC
