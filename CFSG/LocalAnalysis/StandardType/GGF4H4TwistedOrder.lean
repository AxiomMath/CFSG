module

public import CFSG.LocalAnalysis.StandardType.GGF4H4TwistedAux1
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthKSLOrder
import all CFSG.LocalAnalysis.StandardType.GGF4H4TwistedAux1
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLNoJ1Ppd
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatTypeDetOrders

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Orders
  CFSG.SeitzReduction.F4Pilot

private theorem ggF4TWO_one_le_of_card {K : Type} [Field K] [Finite K] {n : ℕ}
    (h : Nat.card K = 2 ^ n) : 1 ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h1 := Finite.one_lt_card (α := K)
    rw [h, pow_zero] at h1
    exact absurd h1 (lt_irrefl 1)
  · exact hn

private theorem ggF4TWO_one_le_C {X : Type} [Group X] {f₁ : ℕ}
    (h : GGHasLabel (⟨.C, 3, f₁⟩ : LargeEvenLabel) X) : 1 ≤ f₁ := by
  obtain ⟨K, _, _, hK, -⟩ := h
  exact ggF4TWO_one_le_of_card hK

private theorem ggF4TWO_one_le_twD4 {X : Type} [Group X] {f₁ : ℕ}
    (h : GGHasLabel (⟨.twD, 4, f₁⟩ : LargeEvenLabel) X) : 1 ≤ f₁ := by
  have h' : LargeEvenRecipeOmegaMinus 3 (2 ^ f₁) fun R' _ _ _ => Nonempty (X ≃* R') := h
  obtain ⟨K, _, _, hK, -⟩ := h'
  exact ggF4TWO_one_le_of_card hK

section Cert


theorem ggF4TW_orderInput_holds : ggF4TW_OrderInput := by
  intro G _ _ J K f f₁ hJK hf hJ
  obtain ⟨r, hr, hrJ⟩ := SCFourCover.exists_ppd_dvd_ordTwistedA_two hf
  have hJl : LargeEvenInLambda2 (⟨.twA, 2, f⟩ : LargeEvenLabel) :=
    ⟨(by omega : 1 ≤ f), le_rfl, fun _ => hf⟩
  have hr6 : 0 < 6 * f := by omega
  have key : ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
      GGHasLabel lab (↥K ⧸ Subgroup.center ↥K) → r ∣ SporadicShape.labOrd lab :=
    fun lab hl hK => hrJ.trans (ggKSL_labOrd_dvd hJK hl hK hJl hJ)
  refine ⟨fun hK => ?_, fun hK => ?_, fun _ hK => ?_⟩
  ·
    have hf₁ := ggF4TWO_one_le_C hK
    have hd : r ∣ ordBC 3 (2 ^ f₁) :=
      key ⟨.C, 3, f₁⟩ ⟨hf₁, (by norm_num : 2 ≤ 3), fun h => by norm_num at h⟩ hK
    obtain ⟨i, hi, hdvd⟩ := ((profile_idxBC (n := 3) hf₁).prim r (6 * f) hr hr6).1 hd
    rw [Finset.mem_Icc] at hi
    have hle := Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) hdvd
    have h6 : f₁ * (2 * i) ≤ f₁ * 6 := Nat.mul_le_mul_left _ (by omega)
    omega
  ·
    have hf₁ := ggF4TWO_one_le_twD4 hK
    have hd : r ∣ ordTwistedD 4 (2 ^ f₁) := key ⟨.twD, 4, f₁⟩ ⟨hf₁, (by norm_num : 2 ≤ 4)⟩ hK
    have h8 : 6 * f ≤ 8 * f₁ := by
      rcases ((profile_idx2D (n := 4) (by norm_num) hf₁).prim r (6 * f) hr hr6).1 hd with
        ⟨hdvd, -⟩ | ⟨i, hi, hdvd⟩
      · have := Nat.le_of_dvd (by omega) hdvd
        omega
      · rw [Finset.mem_Icc] at hi
        have hle := Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) hdvd
        have h6 : f₁ * (2 * i) ≤ f₁ * 6 := Nat.mul_le_mul_left _ (by omega)
        omega
    omega
  ·
    rcases hK with hK | hK
    · have hd : r ∣ ordA 5 (2 ^ 1) :=
        key ⟨.A, 5, 1⟩ ⟨le_rfl, (by norm_num : 1 ≤ 5), fun h => absurd h (by decide)⟩ hK
      obtain ⟨i, hi, hdvd⟩ :=
        ((profile_idxA (n := 5) (by norm_num) le_rfl).prim r (6 * f) hr hr6).1 hd
      rw [Finset.mem_Icc] at hi
      have := Nat.le_of_dvd (by omega) hdvd
      omega
    · have hd : r ∣ ordA 6 (2 ^ 1) :=
        key ⟨.A, 6, 1⟩ ⟨le_rfl, (by norm_num : 1 ≤ 6), fun h => absurd h (by decide)⟩ hK
      obtain ⟨i, hi, hdvd⟩ :=
        ((profile_idxA (n := 6) (by norm_num) le_rfl).prim r (6 * f) hr hr6).1 hd
      rw [Finset.mem_Icc] at hi
      have := Nat.le_of_dvd (by omega) hdvd
      omega

end Cert

end CFSG.StandardType
