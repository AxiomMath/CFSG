module

public import CFSG.RankThree.PartTwo.Sec16.Item165ProofTools
public import CFSG.RankThree.PartTwo.Sec16.Item167Proof
import CFSG.Goldschmidt.Steps.G310Basic
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec17.Item17HeadProof

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec17
  CFSG.RankThree.PartTwo.Late CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise

section Steps

variable {G : Type} [Group G] [Finite G]

@[expose] def E165 (A Y₀ : Subgroup G) : Prop :=
  ∀ S ∈ scriptQPiStar A (lB A) ⊤ (piOf 2), S ≠ ⊥ → ¬ Y₀ ≤ Subgroup.normalizer (S : Set G) →
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ ∃ E : Subgroup G, E ≤ Y₀ ∧ IsPGroup p E ∧ E ≠ ⊥ ∧
      ((E ⊔ S : Subgroup G) : Set G) = (E : Set G) * (S : Set G) ∧
      IsCharacteristicP 2 ↥(E ⊔ S) ∧
      ∀ e ∈ E, e ≠ 1 →
        Y₀ ⊔ S ≤ ((Y₀ ⊔ S) ⊓ Subgroup.normalizer (S : Set G)) ⊔ Subgroup.zpowers e

@[expose] def Three165 (A Y₀ : Subgroup G) : Prop :=
  ∀ X ∈ scriptY3 A (lB A), ¬ X ≤ Subgroup.normalizer (Y₀ : Set G) → 3 ∣ Nat.card X →
    ∀ T ∈ scriptQPiStar A (lB A) X (piOf 2),
      ∃ X' ∈ scriptY3 A (lB A), ¬ X' ≤ Subgroup.normalizer (Y₀ : Set G) ∧
        ¬ 3 ∣ Nat.card X' ∧ T ≤ X'

end Steps

@[expose] def Step165E : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → IsL3TwoPow L → E165 A Y₀

@[expose] def Step165Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → IsL3TwoPow L → Three165 A Y₀

namespace Proof165

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

@[expose] def Good165 (A Y₀ Z T : Subgroup G) : Prop :=
  Z ∈ scriptY A ∧ generalizedFitting ↥Z = CFSG.pCore 2 ↥Z ∧
    ¬ 3 ∣ Nat.card (delta A (lB A) Z) ∧ ¬ delta A (lB A) Z ≤ Subgroup.normalizer (Y₀ : Set G) ∧
    CFSG.Open.fusionIsSylowIn 2 T (delta A (lB A) Z) ∧ A ≤ Subgroup.normalizer (T : Set G)

theorem exists_good_of_three (h : Sec17Std G A c L Y₀) {X : Subgroup G}
    (hX : X ∈ scriptY3 A (lB A)) (hXM : ¬ X ≤ Subgroup.normalizer (Y₀ : Set G))
    (hX3 : ¬ 3 ∣ Nat.card X) : ∃ Z T : Subgroup G, Good165 A Y₀ Z T := by
  have hA : IsE27 A := h.toSec14Std.isE27
  obtain ⟨Z, hXZ, hZ, hFZ, hD1⟩ := exists_overgroup_of_mem_scriptY1 h.isSimpleGroup h.nonabelian
    h.toTheoremFourHyp.charTwoType (mem_scriptY1_of_three hX hX3)
  have hD3 : ¬ 3 ∣ Nat.card (delta A (lB A) Z) := not_three_dvd_of_mem_scriptY1 hD1
  have hXD : X ≤ delta A (lB A) Z := hX.2.le.trans (delta_mono hXZ)
  have hbot2 : IsPGroup 2 (⊥ : Subgroup G) := IsPGroup.of_bot
  obtain ⟨T, hT, -, hAT⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    Nat.prime_three Nat.prime_two hA.isPGroup hD3 (le_normalizer_delta Z) bot_le hbot2
    (by rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]; exact le_top)
  exact ⟨Z, T, hZ, hFZ, hD3, fun hle => hXM (hXD.trans hle), hT, hAT⟩

theorem normalizer_le_M_of_e165 (h : Sec17Std G A c L Y₀) (hE : E165 A Y₀) {T C : Subgroup G}
    (hT : T ∈ scriptQPiStar A (lB A) ⊤ (piOf 2)) (hT1 : T ≠ ⊥) (hCT : C ≤ T) (hC1 : C ≠ ⊥)
    (hNC : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (C : Set G))
    (hhost : ∀ U : Subgroup G, T ≤ U → ¬ 3 ∣ Nat.card U → CFSG.Open.fusionIsSylowIn 2 T U →
      IsCharacteristicP 2 ↥U → U ≤ Subgroup.normalizer (C : Set G)) :
    Subgroup.normalizer (C : Set G) ≤ Subgroup.normalizer (Y₀ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 T := isPGroup_of_mem_scriptQPi Nat.prime_two hT.prop
  have hAT : A ≤ Subgroup.normalizer (T : Set G) := hT.prop.1.1.1.2.2
  have hY₀C : Y₀ ≤ Subgroup.normalizer (C : Set G) := by
    by_cases hYT : Y₀ ≤ Subgroup.normalizer (T : Set G)
    · exact hYT.trans hNC
    obtain ⟨p, hp, hp3, E, -, hEp, hE1, hET, hEc, hgen⟩ := hE T hT hT1 hYT
    have : Fact p.Prime := ⟨hp⟩
    have hidx := card_quotient_dvd_of_coe_sup_eq_mul hET
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hEp
    rw [hk] at hidx
    have hodd : ¬ 2 ∣ (T.subgroupOf (E ⊔ T)).index := by
      intro h2
      rw [Subgroup.index] at h2
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two (h2.trans hidx)
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp this
      omega
    have hsyl : CFSG.Open.fusionIsSylowIn 2 T (E ⊔ T) :=
      Proof165.fusionIsSylowIn_of_not_dvd_index le_sup_right hT2 hodd
    have h3 : ¬ 3 ∣ Nat.card ↥(E ⊔ T) := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (T.subgroupOf (E ⊔ T))]
      intro h3
      rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h | h
      · have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three (h.trans hidx)
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp this
        omega
      · have hT2' : IsPGroup 2 (T.subgroupOf (E ⊔ T)) := hT2.comap_subtype
        obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hT2'
        rw [hm] at h
        have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
        omega
    have hETC : E ⊔ T ≤ Subgroup.normalizer (C : Set G) :=
      hhost (E ⊔ T) le_sup_right h3 hsyl hEc
    obtain ⟨e, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE1
    have he1' : (e : G) ≠ 1 := fun h => he1 (Subtype.ext h)
    calc Y₀ ≤ Y₀ ⊔ T := le_sup_left
      _ ≤ ((Y₀ ⊔ T) ⊓ Subgroup.normalizer (T : Set G)) ⊔ Subgroup.zpowers (e : G) :=
          hgen e e.2 he1'
      _ ≤ Subgroup.normalizer (C : Set G) :=
          sup_le (inf_le_right.trans hNC)
            (Subgroup.zpowers_le.mpr (hETC ((le_sup_left : E ≤ E ⊔ T) e.2)))
  exact Proof165.normalizer_le_M h hC1 (hT2.to_le hCT) (sup_le hY₀C (hAT.trans hNC))

theorem exists_good_lt (h : Sec17Std G A c L Y₀) (hst : StellmacherKP)
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) (h146 : Item146 A (lB A))
    (h149 : Item149 A (lB A)) (hE : E165 A Y₀) (h3 : Three165 A Y₀) {Z T : Subgroup G}
    (hG : Good165 A Y₀ Z T) :
    ∃ Z' T' : Subgroup G, Good165 A Y₀ Z' T' ∧ Nat.card T < Nat.card T' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hZ, hFZ, hD3, hΔM, hTsyl, hAT⟩ := hG
  have hA : IsE27 A := h.toSec14Std.isE27
  have hsimp := h.isSimpleGroup
  have hnab := h.nonabelian
  set Δ := delta A (lB A) Z with hΔ
  set D := deltaZero A (lB A) Z with hD
  have hΔQ : Δ ∈ scriptQ A (lB A) := Proof165.delta_mem_scriptQ_of_three hA h146 Z hD3
  have hTΔ : T ≤ Δ := hTsyl.1
  have hT2 : IsPGroup 2 T := hTsyl.2.1
  have hTQ : T ∈ scriptQ A (lB A) := mem_scriptQ_of_le hΔQ hTΔ hAT
  have hT2Q : T ∈ scriptQPi A (lB A) ⊤ (piOf 2) :=
    ⟨⟨hTQ, le_top⟩, (isPiSubgroup_piOf_iff Nat.prime_two T).mpr hT2⟩
  obtain ⟨hdelta, -, hnorm⟩ := rank3II_14_5_lB hA hbot hZ.2
  have hDM : ¬ D ≤ Subgroup.normalizer (Y₀ : Set G) := by
    intro hDle
    apply hΔM
    rw [hΔ, hdelta]
    exact sup_le hDle (inf_le_left.trans ((pPrimeCoreOf_le 3 _).trans
      (HeadProof.centralizer_le_M h)))
  have hFD : generalizedFitting ↥D = CFSG.pCore 2 ↥D := ((h149 Z hZ).2.2.2 hFZ).2
  have hDc : IsCharacteristicP 2 ↥D :=
    (isCharacteristicP_iff_generalizedFitting_eq_pCore ↥D 2).mpr hFD
  set U := D ⊔ T with hU
  have hTD : T ≤ Subgroup.normalizer (D : Set G) := hTΔ.trans hnorm
  have hUΔ : U ≤ Δ := sup_le (deltaZero_le_delta Z) hTΔ
  have hU3 : ¬ 3 ∣ Nat.card U := fun h3 => hD3 (h3.trans (Subgroup.card_dvd_of_le hUΔ))
  have hUsyl : CFSG.Open.fusionIsSylowIn 2 T U :=
    ⟨le_sup_right, hT2, fun Q hQU hQ hTQ' => hTsyl.2.2 Q (hQU.trans hUΔ) hQ hTQ'⟩
  have hUc : IsCharacteristicP 2 ↥U := Proof165.isCharacteristicP_sup hTD hT2 hDc
  have hD1 : D ≠ ⊥ := fun h0 => hDM (h0 ▸ bot_le)
  have hT1 : T ≠ ⊥ := by
    intro hT0
    have : Nontrivial ↥D := (Subgroup.nontrivial_iff_ne_bot D).mpr hD1
    have hP := pCoreOf_ne_bot_of_pCore_ne_bot (pCore_ne_bot_of_isCharacteristicP hDc)
    apply hP
    have := hUsyl.2.2 (CFSG.Open.pCoreOf 2 D)
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 D).trans le_sup_left)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D) (hT0 ▸ bot_le)
    rw [this, hT0]
  obtain ⟨C, hCT, hC1, hNC, hhost⟩ := Proof165.exists_stellmacher hst h.toTheoremFourHyp hT2 hT1
  have hUC : U ≤ Subgroup.normalizer (C : Set G) := hhost U le_sup_right hU3 hUsyl hUc
  have hC2 : IsPGroup 2 C := hT2.to_le hCT
  have hAC : A ≤ Subgroup.normalizer (C : Set G) := hAT.trans hNC
  by_cases hmax : T ∈ scriptQPiStar A (lB A) ⊤ (piOf 2)
  ·
    exfalso
    have hNM := normalizer_le_M_of_e165 h hE hmax hT1 hCT hC1 hNC hhost
    exact hDM ((le_sup_left.trans hUC).trans hNM)
  ·
    obtain ⟨S, hTS, hS⟩ :=
      Finite.exists_le_maximal (p := (· ∈ scriptQPi A (lB A) ⊤ (piOf 2))) hT2Q
    have hTneS : T ≠ S := fun hTS' => hmax (hTS' ▸ hS)
    have hS2 : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two hS.prop
    have hlt : T < S ⊓ Subgroup.normalizer (T : Set G) :=
      CFSG.Goldschmidt.G310.lt_inf_normalizer hS2 hTS hTneS
    have hSQ : S ∈ scriptQ A (lB A) := hS.prop.1.1
    have hANST : A ≤ Subgroup.normalizer ((S ⊓ Subgroup.normalizer (T : Set G) :
        Subgroup G) : Set G) :=
      le_normalizer_inf hSQ.1.2.2 (hAT.trans Subgroup.le_normalizer)
    have hNSTQ : S ⊓ Subgroup.normalizer (T : Set G) ∈ scriptQ A (lB A) :=
      mem_scriptQ_of_le hSQ inf_le_left hANST
    set K := Subgroup.normalizer (C : Set G) with hK
    have hCQ : C ∈ scriptQ A (lB A) := mem_scriptQ_of_le hTQ hCT hAC
    have hK3 : delta A (lB A) K ∈ scriptY3 A (lB A) :=
      Proof165.delta_normalizer_mem_scriptY3 hsimp hnab hC1 hC2 hCQ
    have hAU : A ≤ Subgroup.normalizer (U : Set G) :=
      Sec14.le_normalizer_sup (le_normalizer_deltaZero Z) hAT
    have hUQ : U ∈ scriptQ A (lB A) := mem_scriptQ_of_le hΔQ hUΔ hAU
    have hUK : U ≤ delta A (lB A) K := le_delta hUQ hUC
    have hKM : ¬ delta A (lB A) K ≤ Subgroup.normalizer (Y₀ : Set G) := fun hle =>
      hDM ((le_sup_left.trans hUK).trans hle)
    have hNSTK : S ⊓ Subgroup.normalizer (T : Set G) ≤ delta A (lB A) K :=
      le_delta hNSTQ (inf_le_right.trans hNC)
    have hNSTmem : S ⊓ Subgroup.normalizer (T : Set G) ∈
        scriptQPi A (lB A) (delta A (lB A) K) (piOf 2) :=
      ⟨⟨hNSTQ, hNSTK⟩, (isPiSubgroup_piOf_iff Nat.prime_two _).mpr (hS2.to_le inf_le_left)⟩
    obtain ⟨T₁, hNT₁, hT₁⟩ := Finite.exists_le_maximal
      (p := (· ∈ scriptQPi A (lB A) (delta A (lB A) K) (piOf 2))) hNSTmem
    obtain ⟨X', hX', hX'M, hX'3, hT₁X'⟩ : ∃ X' ∈ scriptY3 A (lB A),
        ¬ X' ≤ Subgroup.normalizer (Y₀ : Set G) ∧ ¬ 3 ∣ Nat.card X' ∧ T₁ ≤ X' := by
      by_cases h3K : 3 ∣ Nat.card (delta A (lB A) K)
      · exact h3 (delta A (lB A) K) hK3 hKM h3K T₁ hT₁
      · exact ⟨delta A (lB A) K, hK3, hKM, h3K, hT₁.prop.1.2⟩
    obtain ⟨Z', hX'Z', hZ', hFZ', hD'1⟩ := exists_overgroup_of_mem_scriptY1 hsimp hnab
      h.toTheoremFourHyp.charTwoType (Proof165.mem_scriptY1_of_three hX' hX'3)
    have hD'3 : ¬ 3 ∣ Nat.card (delta A (lB A) Z') :=
      Proof165.not_three_dvd_of_mem_scriptY1 hD'1
    have hX'D' : X' ≤ delta A (lB A) Z' := hX'.2.le.trans (delta_mono hX'Z')
    have hT₁D' : T₁ ≤ delta A (lB A) Z' := le_delta hT₁.prop.1.1 (hT₁X'.trans hX'Z')
    have hT₁2 : IsPGroup 2 T₁ := isPGroup_of_mem_scriptQPi Nat.prime_two hT₁.prop
    obtain ⟨T', hT', hT₁T', hAT'⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
      Nat.prime_three Nat.prime_two hA.isPGroup hD'3 (le_normalizer_delta Z') hT₁D' hT₁2
      hT₁.prop.1.1.1.2.2
    refine ⟨Z', T', ⟨hZ', hFZ', hD'3, fun hle => hX'M (hX'D'.trans hle), hT', hAT'⟩, ?_⟩
    calc Nat.card T < Nat.card (S ⊓ Subgroup.normalizer (T : Set G) : Subgroup G) :=
          Subgroup.card_lt_of_lt hlt
      _ ≤ Nat.card T₁ := Subgroup.card_le_of_le hNT₁
      _ ≤ Nat.card T' := Subgroup.card_le_of_le hT₁T'

theorem le_M_of_mem_scriptY3 (h : Sec17Std G A c L Y₀)
    (hst : StellmacherKP) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (h146 : Item146 A (lB A)) (h149 : Item149 A (lB A)) (hE : E165 A Y₀)
    (h3 : Three165 A Y₀) {X : Subgroup G} (hX : X ∈ scriptY3 A (lB A)) :
    X ≤ Subgroup.normalizer (Y₀ : Set G) := by
  by_contra hXM
  obtain ⟨T₀, hT₀⟩ := Sec17.exists_mem_scriptQPiStar (A := A) (LB := lB A) X (piOf 2)
  obtain ⟨X', hX', hX'M, hX'3⟩ : ∃ X' ∈ scriptY3 A (lB A),
      ¬ X' ≤ Subgroup.normalizer (Y₀ : Set G) ∧ ¬ 3 ∣ Nat.card X' := by
    by_cases h3X : 3 ∣ Nat.card X
    · obtain ⟨X', hX', hX'M, hX'3, -⟩ := h3 X hX hXM h3X T₀ hT₀
      exact ⟨X', hX', hX'M, hX'3⟩
    · exact ⟨X, hX, hXM, h3X⟩
  obtain ⟨Z₀, T₁, hgood⟩ := exists_good_of_three h hX' hX'M hX'3
  obtain ⟨T, ⟨Z, hZT⟩, hTmax⟩ := Set.exists_max_image {T : Subgroup G | ∃ Z, Good165 A Y₀ Z T}
    (fun T => Nat.card T) (Set.toFinite _) ⟨T₁, Z₀, hgood⟩
  obtain ⟨Z', T', hZT', hlt⟩ := exists_good_lt h hst hbot h146 h149 hE h3 hZT
  exact absurd (hTmax T' ⟨Z', hZT'⟩) (not_le.mpr hlt)

end Proof165

section Item

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem rank3II_16_5_of (h : Sec17Std G A c L Y₀)
    (hst : StellmacherKP) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (h146 : Item146 A (lB A)) (h149 : Item149 A (lB A)) (hE : IsL3TwoPow L → E165 A Y₀)
    (h3 : IsL3TwoPow L → Three165 A Y₀) : Item165 A (lB A) L := by
  intro hL Y hY Z hZ
  rw [h.eq_of_mem_y0Star hY]
  exact Proof165.le_M_of_mem_scriptY3 h hst hbot h146 h149 (hE hL) (h3 hL) hZ

end Item

theorem item165S17_of (hst : StellmacherKP)
    (hbot : Sec14.Item145BotS17) (h146 : Sec14.Item146S14) (h149 : Item149S14)
    (hE : Step165E) (h3 : Step165Three) : Item165S17 :=
  fun G _ _ A c L Y₀ hs => rank3II_16_5_of hs hst (hbot G A c L Y₀ hs)
    (h146 G A c L hs.toSec14Std) (h149 G A c L hs.toSec14Std) (hE G A c L Y₀ hs)
    (h3 G A c L Y₀ hs)

end CFSG.RankThree.PartTwo.Sec16
