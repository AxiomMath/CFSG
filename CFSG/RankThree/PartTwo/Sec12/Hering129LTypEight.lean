module

public import CFSG.RankThree.PartTwo.Sec12.Hering129HEnd
public import CFSG.RankThree.PartTwo.Sec12.Hering129KOrders
public import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Orders
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.RankThree.PartTwo.Sec12

namespace Hering129L

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)

section Orders

theorem card_projSL_two_eight : Nat.card (projSL 2 (GaloisField 2 3)) = 504 := by
  rw [Nat.card_congr (Sec4.projSLEquivPSL (GaloisField 2 3)).toEquiv,
    CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.card_psl2_even (p := 3) (by norm_num)]
  norm_num

theorem false_of_card_projSL_three {K : Type} [Field K] [Finite K]
    (h : Nat.card (projSL 3 K) = 504) : False := by
  have hc := KFacts.KS14.card_projSL_three_mul_gcd K
  rw [h] at hc
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hg : Nat.gcd 3 (Nat.card K - 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
  by_cases hq3 : 3 ≤ Nat.card K
  · have h1 : 27 ≤ Nat.card K ^ 3 := by
      calc 27 = 3 ^ 3 := by norm_num
        _ ≤ Nat.card K ^ 3 := Nat.pow_le_pow_left hq3 3
    have h2 : 9 ≤ Nat.card K ^ 2 := by
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ Nat.card K ^ 2 := Nat.pow_le_pow_left hq3 2
    have h3 : 8 ≤ Nat.card K ^ 2 - 1 := by omega
    have h4 : 26 ≤ Nat.card K ^ 3 - 1 := by omega
    have h5 : 27 * (8 * 26) ≤ Nat.card K ^ 3 * ((Nat.card K ^ 2 - 1) * (Nat.card K ^ 3 - 1)) :=
      Nat.mul_le_mul h1 (Nat.mul_le_mul h3 h4)
    have h6 : 504 * Nat.gcd 3 (Nat.card K - 1) ≤ 504 * 3 := Nat.mul_le_mul_left _ hg
    omega
  · have : Nat.card K = 2 := by omega
    rw [this] at hc
    norm_num at hc

theorem false_of_card_projSU_three {p f : ℕ} [Fact p.Prime] (hf : 1 ≤ f)
    (h : Nat.card (projSU 3 p f) = 504) : False := by
  have hp : p.Prime := Fact.out
  have hc := KFacts.KS14.card_projSU_three_mul_gcd p f hf
  rw [h] at hc
  have hq2 : 2 ≤ p ^ f := by
    calc 2 ≤ p := hp.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
  have hg : Nat.gcd 3 (p ^ f + 1) ≤ 3 := Nat.gcd_le_left _ (by norm_num)
  by_cases hq3 : 3 ≤ p ^ f
  · have h1 : 27 ≤ (p ^ f) ^ 3 := by
      calc 27 = 3 ^ 3 := by norm_num
        _ ≤ (p ^ f) ^ 3 := Nat.pow_le_pow_left hq3 3
    have h2 : 9 ≤ (p ^ f) ^ 2 := by
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ (p ^ f) ^ 2 := Nat.pow_le_pow_left hq3 2
    have h3 : 8 ≤ (p ^ f) ^ 2 - 1 := by omega
    have h4 : 28 ≤ (p ^ f) ^ 3 + 1 := by omega
    have h5 : 27 * (8 * 28) ≤ (p ^ f) ^ 3 * (((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1)) :=
      Nat.mul_le_mul h1 (Nat.mul_le_mul h3 h4)
    have h6 : 504 * Nat.gcd 3 (p ^ f + 1) ≤ 504 * 3 := Nat.mul_le_mul_left _ hg
    omega
  · have : p ^ f = 2 := by omega
    rw [this] at hc
    norm_num at hc

theorem false_of_card_isoLThreePi {Q : Type} [Group Q] {p e : ℕ} [Fact p.Prime]
    (hQ : Nat.card Q = 504) (h : Sec4.IsoLThreePi Q p e) : False := by
  rcases h with ⟨-, ⟨φ⟩⟩ | ⟨hm, ⟨φ⟩⟩
  · exact false_of_card_projSL_three (K := GaloisField p e)
      (by rw [← Nat.card_congr φ.toEquiv]; exact hQ)
  · have he : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with rfl | h
      · simp at hm
      · exact h
    exact false_of_card_projSU_three he (by rw [← Nat.card_congr φ.toEquiv]; exact hQ)

end Orders

section Main

variable {G : Type} [Group G] [Finite G]

theorem notEight_of_type
    {Y : Subgroup G} (hθ : aschbacherSolvableCore 3 Y = CFSG.pCore 2 Y)
    (hty : (∃ (p e : ℕ) (_ : Fact p.Prime), Sec4.IsoLThreePi (Y ⧸ CFSG.pCore 2 Y) p e) ∨
      ∃ (q₀ : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q₀).Valid),
        Nonempty (Y ⧸ CFSG.pCore 2 Y ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q₀, hq⟩).Group))
    (hZ : Subgroup.center (Y ⧸ CFSG.pCore 2 Y) = ⊥) :
    ¬ Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* projSL 2 (GaloisField 2 3)) ∧
      ¬ Sec4.IsSLThreePiAt (Y ⧸ aschbacherSolvableCore 3 Y) 8 := by
  have ePC := QuotientGroup.quotientMulEquivOfEq hθ
  refine ⟨?_, ?_⟩
  · rintro ⟨e⟩
    have hQ : Nat.card (Y ⧸ CFSG.pCore 2 Y) = 504 := by
      rw [Nat.card_congr (ePC.symm.trans e).toEquiv]
      exact card_projSL_two_eight
    rcases hty with ⟨p, e', hp, hiso⟩ | ⟨q₀, hq, ⟨f⟩⟩
    · haveI := hp
      exact false_of_card_isoLThreePi hQ hiso
    · have h1 := Hering129KOrders.card_of_isoD4 (r := q₀) (hr := hq) ⟨f⟩
      have h2 := Hering129KOrders.le_ordTrialityD4 (Hering129KOrders.two_le_card q₀)
      rw [Hering129KOrders.ordTrialityD4_two] at h2
      omega
  · intro hSL
    have h3 := card_center_eq_three_of_isSLThreePi ⟨8, hSL⟩
    have hZ' : Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y) = ⊥ := by
      rw [← Subgroup.map_center_eq ePC.symm, hZ, Subgroup.map_bot]
    rw [hZ'] at h3
    simp at h3

theorem notEight_of_typ129IIIcType
    {L Y : Subgroup G} (hθ : aschbacherSolvableCore 3 Y = CFSG.pCore 2 Y)
    (h3 : Typ129IIIcType L Y) :
    ¬ Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* projSL 2 (GaloisField 2 3)) ∧
      ¬ Sec4.IsSLThreePiAt (Y ⧸ aschbacherSolvableCore 3 Y) 8 :=
  notEight_of_type hθ h3.2.1 h3.2.2

end Main

end Hering129L

end CFSG.RankThree.PartTwo.Sec12
