module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight.Shape

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ABGLocalTools (IsSylowOf)

variable {X : Type} [Group X] [Finite X]

theorem exists_card_eq_five_le {L : Subgroup X} {n : ℕ} (hSz : IsSz (Bar2 L) n) :
    ∃ A : Subgroup X, A ≤ L ∧ Nat.card A = 5 := by
  have h5bar : 5 ∣ Nat.card (Bar2 L) :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.FourteenEight.five_dvd_card_of_isSz hSz
  have h5L : 5 ∣ Nat.card L :=
    h5bar.trans (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥L))
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨A₀, hA₀card⟩ :=
    Sylow.exists_subgroup_card_pow_prime (G := L) (p := 5) (n := 1) (by simpa using h5L)
  exact ⟨A₀.map L.subtype, Subgroup.map_subtype_le A₀,
    by rw [Subgroup.card_map_of_injective L.subtype_injective, hA₀card, pow_one]⟩

theorem centralizer_le_of_normalizer_le {L Y : Subgroup X} {n : ℕ} (hSz : IsSz (Bar2 L) n)
    (hA : ∀ A : Subgroup X, A ≤ L → (Nat.card A).Prime → Nat.card A ≠ 2 →
      normalizer (A : Set X) ≤ Y) :
    centralizer (L : Set X) ≤ Y := by
  obtain ⟨A, hAL, hAcard⟩ := exists_card_eq_five_le hSz
  have hprime : (Nat.card A).Prime := by rw [hAcard]; norm_num
  have hne2 : Nat.card A ≠ 2 := by rw [hAcard]; norm_num
  calc centralizer (L : Set X) ≤ centralizer (A : Set X) :=
        Subgroup.centralizer_le hAL
    _ ≤ normalizer (A : Set X) := Subgroup.centralizer_le_normalizer (A : Set X)
    _ ≤ Y := hA A hAL hprime hne2

omit [Finite X] in
theorem ne_bot_of_normalizer_le {T Y : Subgroup X} (hY : Y ≠ ⊤)
    (hNT : normalizer (T : Set X) ≤ Y) : T ≠ ⊥ := by
  rintro rfl
  have hN : normalizer ((⊥ : Subgroup X) : Set X) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr Subgroup.normal_bot
  rw [hN] at hNT
  exact hY (top_le_iff.mp hNT)

omit [Finite X] in
theorem centOverO2_eq_of_pCoreOf_eq_bot {Y L : Subgroup X} (h : CFSG.Open.pCoreOf 2 L = ⊥) :
    F08.CentOverO2 Y L = Y ⊓ centralizer (L : Set X) := by
  unfold F08.CentOverO2
  rw [h]
  have hset : {x : X | x ∈ Y ∧ ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ (⊥ : Subgroup X)} =
      (Y ⊓ centralizer (L : Set X) : Set X) := by
    ext x
    constructor
    · rintro ⟨hxY, hx⟩
      refine ⟨hxY, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro l hl
      have hx1 : x * l * x⁻¹ * l⁻¹ = 1 := by
        simpa using hx l hl
      have h1 : x * l * x⁻¹ = l := by
        have := congrArg (· * l) hx1
        simpa [mul_assoc] using this
      have h2 : x * l = l * x := by
        have := congrArg (· * x) h1
        simpa [mul_assoc] using this
      exact h2.symm
    · rintro ⟨hxY, hx⟩
      refine ⟨hxY, fun l hl => ?_⟩
      rw [Subgroup.mem_bot]
      have hxl : l * x = x * l := Subgroup.mem_centralizer_iff.mp hx l hl
      have h2 : x * l = l * x := hxl.symm
      rw [h2]
      simp
  conv_lhs => rw [hset]
  exact Subgroup.closure_eq (Y ⊓ centralizer (L : Set X))

omit [Finite X] in
theorem pCore_eq_bot_of_normal {K : Subgroup X} (hO2 : CFSG.pCore 2 X = ⊥)
    (hKn : K.Normal) : CFSG.pCore 2 ↥K = ⊥ := by
  have hchar : (CFSG.pCore 2 ↥K).Characteristic := inferInstance
  have hnorm : ((CFSG.pCore 2 ↥K).map K.subtype).Normal :=
    @ConjAct.normal_of_characteristic_of_normal X _ K hKn (CFSG.pCore 2 ↥K) hchar
  have hp2 : IsPGroup 2 ((CFSG.pCore 2 ↥K).map K.subtype) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥K)).map K.subtype
  have hle : (CFSG.pCore 2 ↥K).map K.subtype ≤ CFSG.pCore 2 X :=
    CFSG.LieType.BorelTits.le_pCore 2 hnorm hp2
  rw [hO2, le_bot_iff] at hle
  exact (Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).mp hle

theorem odd_card_center_of_normal {K : Subgroup X} (hO2 : CFSG.pCore 2 X = ⊥)
    (hKn : K.Normal) : Odd (Nat.card ↥(Subgroup.center ↥K)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKcore : CFSG.pCore 2 ↥K = ⊥ := pCore_eq_bot_of_normal hO2 hKn
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro h2
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 ↥(Subgroup.center ↥K)))
  have hPne : (P : Subgroup ↥(Subgroup.center ↥K)) ≠ ⊥ := P.ne_bot_of_dvd_card h2
  have hPnormal : (P : Subgroup ↥(Subgroup.center ↥K)).Normal :=
    Subgroup.normal_of_isMulCommutative (P : Subgroup ↥(Subgroup.center ↥K))
  have hPchar : (P : Subgroup ↥(Subgroup.center ↥K)).Characteristic :=
    Sylow.characteristic_of_normal P hPnormal
  have hmapNormal :
      ((P : Subgroup ↥(Subgroup.center ↥K)).map (Subgroup.center ↥K).subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal (H := Subgroup.center ↥K)
      (K := (P : Subgroup ↥(Subgroup.center ↥K)))
  have hmap2 : IsPGroup 2
      ((P : Subgroup ↥(Subgroup.center ↥K)).map (Subgroup.center ↥K).subtype) :=
    P.isPGroup'.map _
  have hle : ((P : Subgroup ↥(Subgroup.center ↥K)).map
      (Subgroup.center ↥K).subtype) ≤ CFSG.pCore 2 ↥K :=
    CFSG.LieType.BorelTits.le_pCore 2 hmapNormal hmap2
  rw [hKcore, le_bot_iff] at hle
  exact hPne ((Subgroup.map_eq_bot_iff_of_injective _
    (Subgroup.center ↥K).subtype_injective).mp hle)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410
