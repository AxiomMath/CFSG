module

import CFSG.LocalAnalysis.UniquenessCase.UC22K108BigRow
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Chev2StarHolds
import CFSG.Milestones.ASVolI.I2
import CFSG.Blueprint.LieModelAPI
import CFSG.Timmesfeld.Orders.Exceptional
import CFSG.Assembly.OrderReductions.OrderParity
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Open.OrderForm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)


theorem two_dvd_card_of_lieModel_two_classical {S : Type} [Group S] {t : StatedLieTag}
    {m f : ℕ} (h : LieModel S t m 2 f) (ht : t ∈ CFSG.Blueprint.classicalTags) :
    2 ∣ Nat.card S := by
  have hadm := LieModel.admissible h
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    CFSG.Timmesfeld.card_statedClassicalModel_two (LieModel.statedClassicalModel h ht)
  cases t
  case PSL =>
    obtain ⟨-, -, hm, -⟩ := hadm
    rw [h1 rfl]
    exact (CFSG.OrderReductions.OrderParity.orderA_even (m - 1) (2 ^ f) (by omega)).two_dvd
  case PSU =>
    obtain ⟨-, -, hm, -⟩ := hadm
    have hconv : ∀ l Q : ℕ, 1 ≤ Q → CFSG.Open.ordTwistedA l Q = CFSG.Open.orderTwistedA l Q := by
      intro l Q hQ
      unfold CFSG.Open.ordTwistedA CFSG.Open.orderTwistedA
      congr 2
      refine Finset.prod_congr rfl fun i _ => ?_
      have h1 : 1 ≤ Q ^ i := Nat.one_le_pow _ _ hQ
      have hc : ((Q ^ i : ℕ) : ℤ) = (Q : ℤ) ^ i := Nat.cast_pow Q i
      rcases Nat.even_or_odd i with hi | hi
      · rw [if_pos hi, hi.neg_one_pow]
        omega
      · rw [if_neg (Nat.not_even_iff_odd.2 hi), hi.neg_one_pow]
        omega
    rw [h2 rfl, hconv _ _ Nat.one_le_two_pow]
    exact (CFSG.OrderReductions.OrderParity.orderTwistedA_even (m - 1) (2 ^ f)
      (by omega)).two_dvd
  case PSp =>
    obtain ⟨-, -, hm, -⟩ := hadm
    rw [h3 rfl]
    exact (CFSG.OrderReductions.OrderParity.orderBC_even m (2 ^ f) hm).two_dvd
  case POmegaOdd =>
    obtain ⟨-, -, -, h22⟩ := hadm
    exact absurd rfl h22
  case POmegaPlus =>
    obtain ⟨-, -, hm⟩ := hadm
    rw [h4 rfl]
    exact (CFSG.OrderReductions.OrderParity.orderD_even m (2 ^ f) hm).two_dvd
  case POmegaMinus =>
    obtain ⟨-, -, hm⟩ := hadm
    rw [h5 rfl]
    exact (CFSG.OrderReductions.OrderParity.orderTwistedD_even m (2 ^ f) hm).two_dvd
  all_goals exact absurd ht (by decide)

theorem two_dvd_card_of_lieModel_twistedF4 {S : Type} [Group S] [Finite S] [Nontrivial S]
    {m f : ℕ} (h : LieModel S .twistedF4 m 2 f) : 2 ∣ Nat.card S := by
  have hr := (LieModel.reeTitsModel h (by decide)).2
  obtain ⟨-, -, -, -, -, hiso⟩ := CFSG.LieType.Ree.ReeTag.large_Ree_model_Schreier S 2 f hr
  obtain ⟨-, a, rfl, K, _, _, hK, he⟩ := hr
  have : CharP K 2 := CFSG.ASVolI.ChIJK.burnsideI2BN_charP_of_card Nat.prime_two (by omega) hK
  have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := ‹CharP K 2›
  obtain ⟨e⟩ := hiso a K rfl hK he
  by_contra h2
  have hbot := CFSG.LieType.Ree.ReeTag.eq_bot_of_normal_of_odd hK ⊤ inferInstance (by
    rw [Subgroup.card_top, ← Nat.card_congr e.toEquiv, Nat.odd_iff]
    omega)
  have h1 : ∀ z : S, e z = 1 := fun z => Subgroup.mem_bot.1 (hbot ▸ Subgroup.mem_top (e z))
  obtain ⟨x, y, hxy⟩ := exists_pair_ne S
  exact hxy (e.injective ((h1 x).trans (h1 y).symm))

theorem two_dvd_card_of_chevalleyExceptionalModel_two {S : Type} [Group S] {t : StatedLieTag}
    {f : ℕ} (ht : t ∈ CFSG.Blueprint.chevalleyExceptionalTags)
    (h : CFSG.Blueprint.ChevalleyExceptionalModel S t 2 f) : 2 ∣ Nat.card S := by
  cases t
  case G2 =>
    have hc : Nat.card S = CFSG.Open.ordG2 (2 ^ f) :=
      CFSG.Timmesfeld.card_chevalleyExceptionalModel_two h
    rw [hc]
    exact (CFSG.OrderReductions.OrderParity.orderG2_even (2 ^ f)).two_dvd
  case F4 =>
    have hc : Nat.card S = CFSG.Open.ordF4 (2 ^ f) :=
      CFSG.Timmesfeld.card_chevalleyExceptionalModel_two h
    rw [hc]
    exact (CFSG.OrderReductions.OrderParity.orderF4_even (2 ^ f)).two_dvd
  case E6 =>
    have hc : Nat.card S = CFSG.Open.ordE6 (2 ^ f) :=
      CFSG.Timmesfeld.card_chevalleyExceptionalModel_two h
    rw [hc]
    exact (CFSG.OrderReductions.OrderParity.orderE6_even (2 ^ f)).two_dvd
  case E7 =>
    have hc : Nat.card S = CFSG.Open.ordE7 (2 ^ f) :=
      CFSG.Timmesfeld.card_chevalleyExceptionalModel_two h
    rw [hc]
    exact (CFSG.OrderReductions.OrderParity.orderE7_even (2 ^ f)).two_dvd
  case E8 =>
    have hc : Nat.card S = CFSG.Open.ordE8 (2 ^ f) :=
      CFSG.Timmesfeld.card_chevalleyExceptionalModel_two h
    rw [hc]
    exact (CFSG.OrderReductions.OrderParity.orderE8_even (2 ^ f)).two_dvd
  case twistedE6 =>
    have hc : Nat.card S = CFSG.Open.ordTwistedE6 (2 ^ f) :=
      CFSG.Timmesfeld.card_chevalleyExceptionalModel_two h
    rw [hc]
    exact (CFSG.OrderReductions.OrderParity.orderTwistedE6_even (2 ^ f)).two_dvd
  case trialityD4 =>
    have hc : Nat.card S = CFSG.Open.ordTrialityD4 (2 ^ f) :=
      CFSG.Timmesfeld.card_chevalleyExceptionalModel_two h
    rw [hc]
    exact (CFSG.OrderReductions.OrderParity.orderTrialityD4_even (2 ^ f)).two_dvd
  all_goals exact absurd ht (by decide)

theorem two_dvd_card_of_lieModel_two {S : Type} [Group S] [Finite S] [Nontrivial S]
    {t : StatedLieTag} {m f : ℕ} (ht : t ≠ .Tits) (h : LieModel S t m 2 f) : 2 ∣ Nat.card S := by
  by_cases hce : t ∈ CFSG.Blueprint.chevalleyExceptionalTags
  · exact two_dvd_card_of_chevalleyExceptionalModel_two hce
      (LieModel.chevalleyExceptionalModel h hce)
  by_cases hcl : t ∈ CFSG.Blueprint.classicalTags
  · exact two_dvd_card_of_lieModel_two_classical h hcl
  have hadm := LieModel.admissible h
  cases t
  case twistedB2 =>
    obtain ⟨-, a, -, K, _, _, rfl, hK, ⟨e⟩⟩ := (LieModel.suzukiModel h).2
    rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK]
    exact Dvd.dvd.mul_right
      (Dvd.dvd.mul_right (dvd_pow (dvd_pow_self 2 (by omega)) two_ne_zero) _) _
  case twistedG2 =>
    obtain ⟨-, -, -, h23, -⟩ := hadm
    exact absurd h23 (by decide)
  case twistedF4 => exact two_dvd_card_of_lieModel_twistedF4 h
  case Tits => exact absurd rfl ht
  all_goals first | exact (hce (by decide)).elim | exact (hcl (by decide)).elim

theorem le_of_lieModel_two_of_le_normalizer {G : Type} [Group G] [Finite G] {L : Subgroup G}
    [L.Normal] [IsSimpleGroup ↥L] {t : StatedLieTag} {m f : ℕ} (ht : t ≠ .Tits)
    (hL : LieModel ↥L t m 2 f) {T X M : Subgroup G} (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤)
    (hX : (Nat.card X).Prime) (hXodd : Odd (Nat.card X)) (hXT : X ≤ normalizer (T : Set G))
    (hTM : T ≤ M) (hXM : X ≤ M) (hstar : ∀ g : G, (∀ x ∈ X, g⁻¹ * x * g ∈ M) → g ∈ M) :
    L ≤ M := by
  obtain ⟨B, N, hBN⟩ := CFSG.ASVolI.ChIJK.lieModel_has_splitBNPair Nat.prime_two ht hL
  exact k108big_rowX_strong L hBN
    (PartTwo.Inputs1719.chev2star_ne_top_of_dvd_card hBN (two_dvd_card_of_lieModel_two ht hL))
    hT hX hXodd hXT hTM hXM hstar

@[expose] def K108Norm : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), L.Normal → IsSimpleGroup ↥L →
    ((∃ n : ℕ, 2 ≤ n ∧ ∃ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (m : ℕ),
        CFSG.Assembly.LowTwoRank.StatedLieAdmissible t m 2 n ∧ LieModel ↥L t m 2 n) ∨
      Is3D4 ↥L 1) →
    ∀ (T X M : Subgroup G), CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ → (Nat.card X).Prime →
      Odd (Nat.card X) → X ≤ normalizer (T : Set G) → T ≤ M → X ≤ M →
      (∀ g : G, (∀ x ∈ X, g⁻¹ * x * g ∈ M) → g ∈ M) → L ≤ M

theorem k108Norm_holds : K108Norm := by
  intro G _ _ L hLn hLs hshape T X M hT hX hXodd hXT hTM hXM hstar
  have := hLn
  have := hLs
  rcases hshape with ⟨n, hn, t, m, hadm, hmod⟩ | hmod
  · refine le_of_lieModel_two_of_le_normalizer ?_ hmod hT hX hXodd hXT hTM hXM hstar
    rintro rfl
    obtain ⟨-, -, -, -, hn1⟩ := hadm
    omega
  · exact le_of_lieModel_two_of_le_normalizer (by decide) hmod hT hX hXodd hXT hTM hXM hstar

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10
