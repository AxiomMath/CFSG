module

public import CFSG.Quasithin.Vol2.Ch11SecCB51Core
public import CFSG.Quasithin.Background.InternalSecB56M
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.InternalSec
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_offender_of {T K Y W : Subgroup G} [IsMulCommutative ↥W]
    (hTsyl : IsSylowTwoOf T Y) (hKY : K ≤ Y) (hYK : Y ≤ normalizer (K : Set G))
    (hred : IsTwoReducedIn Y W) (hq : CFSG.IsQuasisimple ↥(autOn K W))
    (hKW : ¬ K ≤ centralizer (W : Set G)) (hJ : K = ⁅K, thompsonJ T⁆) :
    ∃ A : Subgroup G, IsMaxElemAbelian T A ∧
      IsFFStarOffender (autOn Y W) (autOn A W) ∧ ⁅autOn K W, autOn A W⁆ = autOn K W := by
  have hWe : IsElemAbelian 2 W := hred.2.2.1
  have hTY : T ≤ Y := hTsyl.1
  have hTN : T ≤ normalizer (K : Set G) := hTY.trans hYK
  have hTW : T ≤ normalizer (W : Set G) := hTY.trans hred.2.1
  have hKN : K ≤ normalizer (W : Set G) := hKY.trans hred.2.1
  have hnorm : ∀ A : Subgroup G, A ≤ T →
      autOn A W ≤ normalizer (autOn K W : Set (MulAut ↥W)) := by
    intro A hAT x hx
    have hc := autOn_normal_of (U := W) (hAT.trans hTN)
    rw [mem_normalizer_iff]
    intro k
    refine ⟨fun hk => hc x hx k hk, fun hk => ?_⟩
    have := hc x⁻¹ ((autOn A W).inv_mem hx) _ hk
    simpa [mul_assoc] using this
  by_cases hex : ∃ A : Subgroup G, IsMaxElemAbelian T A ∧ ⁅autOn K W, autOn A W⁆ = autOn K W
  · obtain ⟨A, hA, hKA⟩ := hex
    have hAC : ¬ A ≤ centralizer (W : Set G) := by
      intro hAC
      have h0 : autOn A W = ⊥ := autI_eq_bot_of_le_centralizer hWe hAC
      rw [h0, commutator_bot_right] at hKA
      refine not_commute_of_isQuasisimple hq fun a ha b hb => ?_
      rw [← hKA, mem_bot] at ha hb
      rw [ha, hb]
    have hoff : IsFFOffender Y W A := ⟨isMaxElemAbelian_of_isSylowTwoOf hTsyl hA, hAC⟩
    exact ⟨A, hA, offenderImages_isFFStarOffender hWe hred.1 hred.2.1 ⟨A, hoff, rfl⟩, hKA⟩
  · exfalso
    push Not at hex
    have hbot : ∀ A : Subgroup G, IsMaxElemAbelian T A →
        autOn A W ≤ centralizer (autOn K W : Set (MulAut ↥W)) := by
      intro A hA
      rcases Vol2.Ch11.SecC.B51.commutator_eq_or_eq_bot hq (hnorm A hA.1) with h1 | h1
      · exact absurd h1 (hex A hA)
      · rw [commutator_eq_bot_iff_le_centralizer] at h1
        intro x hx
        rw [mem_centralizer_iff]
        intro k hk
        exact (mem_centralizer_iff.mp (h1 hk) x hx).symm
    set S : Subgroup G :=
      ((centralizer (autOn K W : Set (MulAut ↥W))).comap (conjAct W)).map
        (normalizer (W : Set G)).subtype with hS
    have hJS : thompsonJ T ≤ S := by
      refine iSup₂_le fun A hA => ?_
      intro a ha
      have haN : a ∈ normalizer (W : Set G) := hTW (hA.1 ha)
      exact ⟨⟨a, haN⟩, hbot A hA (Setup.mem_autOn_iff.2 ⟨⟨a, haN⟩, ha, rfl⟩), rfl⟩
    apply hKW
    rw [hJ, commutator_le]
    intro l hl j hj
    obtain ⟨g, hg, rfl⟩ := hJS hj
    set lN : ↥(normalizer (W : Set G)) := ⟨l, hKN hl⟩
    have hlK : conjAct W lN ∈ autOn K W := conjAct_mem_autOn hKN hl
    have hcomm : conjAct W ⁅lN, g⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (mem_centralizer_iff.mp hg _ hlK)
    exact (convI_eq_one_iff hWe ⁅lN, g⁆).1 hcomm

section B56

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem commV_bot : commV (⊥ : Subgroup (MulAut V)) = ⊥ := by
  rw [eq_bot_iff, commV, closure_le]
  rintro _ ⟨g, hg, v, rfl⟩
  rw [mem_bot] at hg
  subst hg
  simp

theorem card_statedSL_three_two : Nat.card ↥(Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) = 168 :=
  CFSG.Open.StatedAPI.card_statedSL_three_zmod_two

theorem false_of_b56Piece_bot {W C : Subgroup V} (h : B56Piece (⊥ : Subgroup (MulAut V)) W C) :
    False := by
  rcases h with ⟨hW, h'⟩ | ⟨hW, h'⟩ | ⟨⟨e⟩, -, -, -, -⟩
  · rw [commV_bot, bot_sup_eq] at hW
    subst hW
    exact not_b56Piece_self (Or.inl ⟨by rw [commV_bot, bot_sup_eq], h'⟩)
  · rw [commV_bot, bot_sup_eq] at hW
    subst hW
    exact not_b56Piece_self (Or.inr (Or.inl ⟨by rw [commV_bot, bot_sup_eq], h'⟩))
  · have h1 := Nat.card_congr e.toEquiv
    rw [card_bot, card_statedSL_three_two] at h1
    exact absurd h1 (by norm_num)

omit [Finite V] in
theorem eq_bot_of_factor {J K A B : Subgroup (MulAut V)} (hKA : K ≤ A) (hAB : A ⊓ B = ⊥)
    (hBJ : B ≤ J) (hJB : J ≤ normalizer (B : Set (MulAut V))) (hO2 : pCoreOf 2 J = ⊥)
    (h2 : ∀ g ∈ J, ∃ m : ℕ, g ^ 2 ^ m ∈ K) : B = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB2 : IsPGroup 2 ↥B := fun b => by
    obtain ⟨m, hm⟩ := h2 b (hBJ b.2)
    refine ⟨m, Subtype.ext ?_⟩
    have h1 : (b : MulAut V) ^ 2 ^ m ∈ A ⊓ B := ⟨hKA hm, pow_mem b.2 _⟩
    rw [hAB, mem_bot] at h1
    simpa using h1
  have hBn : (B.subgroupOf J).Normal := (normal_subgroupOf_iff_le_normalizer hBJ).2 hJB
  have := CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 B J hBJ hBn hB2
  rw [hO2] at this
  exact le_bot_iff.1 this

theorem b56Case1_of_pow_two {J K : Subgroup (MulAut V)} (hKJ : K ≤ J)
    (hn : ∀ x ∈ J, ∀ k ∈ K, x * k * x⁻¹ ∈ K) (hK : CFSG.IsQuasisimple ↥K)
    (hO2 : pCoreOf 2 J = ⊥) (h2 : ∀ g ∈ J, ∃ m : ℕ, g ^ 2 ^ m ∈ K)
    (hcases : B56Case1 J ∨ B56Case2 J ∨ B56Case3 J ∨ B56Case4 J ∨ B56Case5 J) :
    B56Case1 J ∧ quasithinGenFitting J = K := by
  have hnorm : ∀ {A B : Subgroup (MulAut V)}, (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) →
      A ≤ normalizer (B : Set (MulAut V)) := fun hc a ha => by
    rw [mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      rw [hc a ha b hb, mul_inv_cancel_right]
      exact hb
    · intro hb
      have h1 := hc a ha (a * b * a⁻¹) hb
      have : b = a * b * a⁻¹ := by
        calc b = a⁻¹ * ((a * b * a⁻¹) * a) := by group
          _ = a⁻¹ * (a * (a * b * a⁻¹)) := by rw [h1]
          _ = a * b * a⁻¹ := by group
      rw [← this] at hb
      exact hb
  rcases hcases with h1 | ⟨⟨e⟩, -⟩ |
      ⟨G₁, G₂, hsup, hinf, hc, -, -, W₁, W₂, -, -, -, -, -, -, hp₁, hp₂⟩ |
      ⟨G₁, G₂, t, hJt, hinf, hc, -, hc₂, -, -, -, -, -, ht₁, ht₂, -⟩ |
      ⟨G₁, G₂, hsup, hinf, hc, -, ⟨e₁⟩, -, -, h₂⟩
  · exact ⟨h1, eq_of_le_quasisimple hKJ hn hK h1.1⟩
  · exact (not_le_perm_three hK hKJ e).elim
  ·
    exfalso
    have hc' : ∀ a ∈ G₂, ∀ b ∈ G₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
    have hJ₁ : J ≤ normalizer (G₁ : Set (MulAut V)) := by
      rw [← hsup]
      exact sup_le le_normalizer (hnorm hc')
    have hJ₂ : J ≤ normalizer (G₂ : Set (MulAut V)) := by
      rw [← hsup]
      exact sup_le (hnorm hc) le_normalizer
    rcases le_or_le_of_sup_eq hsup hc hKJ hn hK with h | h
    · have hb := eq_bot_of_factor h hinf (hsup ▸ le_sup_right) hJ₂ hO2 h2
      subst hb
      exact false_of_b56Piece_bot hp₂
    · have hb := eq_bot_of_factor h (by rw [inf_comm]; exact hinf) (hsup ▸ le_sup_left) hJ₁ hO2
        h2
      subst hb
      exact false_of_b56Piece_bot hp₁
  ·
    exfalso
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rcases le_or_le_of_sup_zpowers hJt hc ht₁ ht₂ hKJ hn hK with h | h
    · have hJ₂ : J ≤ normalizer (G₂ : Set (MulAut V)) := by
        rw [hJt]
        exact sup_le (sup_le (hnorm hc) le_normalizer) (zpowers_le.2 ht₂)
      have hb := eq_bot_of_factor h hinf (hJt ▸ le_sup_right.trans le_sup_left) hJ₂ hO2 h2
      rw [hb, card_bot] at hc₂
      exact absurd hc₂ (by norm_num)
    · exact not_le_of_card_prime hK h hc₂
  ·
    exfalso
    have hc' : ∀ a ∈ G₂, ∀ b ∈ G₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
    have hJ₁ : J ≤ normalizer (G₁ : Set (MulAut V)) := by
      rw [← hsup]
      exact sup_le le_normalizer (hnorm hc')
    have hJ₂ : J ≤ normalizer (G₂ : Set (MulAut V)) := by
      rw [← hsup]
      exact sup_le (hnorm hc) le_normalizer
    rcases le_or_le_of_sup_eq hsup hc hKJ hn hK with h | h
    · have hb := eq_bot_of_factor h hinf (hsup ▸ le_sup_right) hJ₂ hO2 h2
      subst hb
      rcases h₂ with ⟨⟨e₂⟩, -⟩ | ⟨n, F, _, _, -, π, hR⟩
      · have h3 := Nat.card_congr e₂.toEquiv
        rw [card_bot, card_statedSL_three_two] at h3
        exact absurd h3 (by norm_num)
      · rw [commV_bot] at hR
        exact InternalSec.false_of_realizesVia_nat hR bot_le
    · have hb := eq_bot_of_factor h (by rw [inf_comm]; exact hinf) (hsup ▸ le_sup_left) hJ₁ hO2
        h2
      subst hb
      have h3 := Nat.card_congr e₁.toEquiv
      rw [card_bot, card_statedSL_three_two] at h3
      exact absurd h3 (by norm_num)

end B56

end CFSG.Quasithin.H13.U3
