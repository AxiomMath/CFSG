module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4XG
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21e
import CFSG.LocalAnalysis.UniquenessCase.UC22P22c
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rN
import CFSG.LocalAnalysis.UniquenessCase.UC22BarLemmas
import CFSG.LocalAnalysis.UniquenessCase.UC22BarImagePreimage
import CFSG.LocalAnalysis.UniquenessCase.UC6Syl
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1c
import TauCeti.RepresentationTheory.CharacterTable.Solvable

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem u4x_s21_1Hyp {D : Data G} {X : Subgroup G} {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hXr : Nat.card X = r) {a : ℕ} (hcard : Nat.card ↥(X ⊔ D.T) ∣ 2 ^ a * r ^ 2)
    (hXU : X ∈ uniqueSet D.M) : S21_1Hyp D X := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hcop : ∀ j, Nat.Coprime (r ^ j) (2 ^ a) := fun j =>
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hr Nat.prime_two).2 hr2)
  have hpr : ∀ p ∈ piSet (X ⊔ D.T), p = 2 ∨ p = r := fun p hp => by
    rcases (Nat.Prime.dvd_mul hp.1).1 (hp.2.trans hcard) with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp.1 Nat.prime_two).1 (hp.1.dvd_of_dvd_pow h))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp.1 hr).1 (hp.1.dvd_of_dvd_pow h))
  obtain ⟨P, hP, -⟩ := UC6.exists_isSylowOf_ge (p := r) (bot_le : ⊥ ≤ X ⊔ D.T) IsPGroup.of_bot
  obtain ⟨hPY, hPp, hPi⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hP
  obtain ⟨j, hj⟩ := hPp.exists_card_eq
  have hj2 : j ≤ 2 := by
    have h := (Subgroup.card_dvd_of_le hPY).trans hcard
    rw [hj] at h
    exact (Nat.pow_dvd_pow_iff_le_right hr.one_lt).1 ((hcop j).dvd_of_dvd_mul_left h)
  refine ⟨hXr ▸ hr, hXr ▸ hr2,
    TauCeti.isSolvable_of_card_dvd_prime_pow_mul_prime_pow Nat.prime_two hr hcard,
    ⟨P, ⟨hPY, hj ▸ (hr.odd_of_ne_two hr2).pow, ?_⟩, ?_⟩, fun p hp hp2 => ?_, hXU⟩
  · have hidx : (P.subgroupOf (X ⊔ D.T)).index ∣ 2 ^ a * r ^ 2 :=
      (P.subgroupOf (X ⊔ D.T)).index_dvd_card.trans hcard
    refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Subgroup.index_ne_zero_of_finite
      fun {d} hd hdi => ?_⟩
    rcases hpr d ⟨hd, (hdi.trans (Subgroup.index_dvd_card _))⟩ with h | rfl
    · exact h
    · exact absurd hdi hPi
  · interval_cases j
    · haveI : Subsingleton ↥P := (Nat.card_eq_one_iff_unique.1 (by rw [hj, pow_zero])).1
      exact ⟨⟨fun _ _ => Subsingleton.elim _ _⟩⟩
    · haveI : IsCyclic ↥P := isCyclic_of_prime_card (p := r) (by rw [hj, pow_one])
      exact IsCyclic.isMulCommutative
    · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq hj
  · obtain rfl := (hpr p hp).resolve_left hp2
    refine CFSG.SectionRank.pRank_le (k := 2) hr.one_lt fun E hEY hE => ?_
    obtain ⟨i, hi⟩ := hE.isPGroup.exists_card_eq
    have h := (Subgroup.card_dvd_of_le hEY).trans hcard
    rw [hi] at h ⊢
    exact Nat.le_of_dvd (pow_pos hr.pos 2) ((hcop i).dvd_of_dvd_mul_left h)

namespace U4X

variable {D : Data G} {L K : Subgroup G} {n : ℕ}

theorem false_of_eq_one (u : U4X D L K n) {Ch : Choice2011 G} (h211 : S21_1 D Ch)
    (h1930 : H1930 D) (c : Ctx21 D Ch) {H₁ H₂ : Subgroup G} (hH₁ : H₁ ∈ hSet D.T D.M)
    (hH₂ : H₂ ∈ hSet D.T D.M) (hL0 : c.L0 ≤ H₁ ⊓ H₂)
    (hfX : ∀ X : Subgroup G, X ≤ D.M → D.T ≤ X → F12.InF 1 (⊤ : Subgroup (Bar2 X)) →
      (X : Set G) = ((H₁ ⊓ X : Subgroup G) : Set G) * ((H₂ ⊓ X : Subgroup G) : Set G))
    (hA : ∀ A : Subgroup G, A ≤ L → Nat.card A = 2 ^ n - 1 → A ∈ uniqueSet D.M)
    {b : G} (hb : b ∈ c.B0) (hbN : b ∈ normalizer (D.T : Set G)) (hbo : orderOf b = 2 ^ n - 1)
    {x₀ x₁ : Bar2 D.M} (hx₀ : x₀ ∈ barImage D.M L) (hx₁ : x₁ ∈ barImage D.M K)
    (hx₀q : x₀ ^ (2 ^ n - 1) = 1) (hx₁q : x₁ ^ (2 ^ n - 1) = 1) (hx₀1 : x₀ ≠ 1)
    (hbx : uc22p21cPi D.M ⟨b, c.hBM hb⟩ = x₀ * x₁) : False := by
  haveI : Fact (2 ^ n - 1).Prime := ⟨u.prime_r⟩
  obtain ⟨hcomm, -⟩ := u4x_bar_structure u.hL u.hK u.hne u.hset u.shape
  obtain ⟨X, hXM, hTX, hXH, hXd, hbX, hyX⟩ :=
    u.exists_le_or_le hH₁.1 hH₂.1 hfX hx₀ hx₁ hx₀q hx₁q hx₀1 (b := ⟨b, c.hBM hb⟩) hbN hbx
  replace hbX : b ∈ normalizer (X : Set G) := hbX
  obtain ⟨H, hH, hXH, hbH⟩ : ∃ H ∈ hSet D.T D.M, X ≤ H ∧ b ∈ H := by
    rcases hXH with h | h
    exacts [⟨H₁, hH₁, h, (hL0 (c.hB0.1 hb)).1⟩, ⟨H₂, hH₂, h, (hL0 (c.hB0.1 hb)).2⟩]
  have hYM : zpowers b ⊔ X ≤ D.M := sup_le (zpowers_le.2 (c.hBM hb)) hXM
  have hOY : pCoreOf 2 D.M ≤ zpowers b ⊔ X :=
    (uc22p22c_pCoreOf_le_T D).trans (hTX.trans le_sup_right)
  have hYd : Nat.card ↥(zpowers b ⊔ X) ∣ (2 ^ n - 1) ^ 2 * Nat.card D.T := by
    have h := PartTwo.card_sup_mul_card_inf_of_le_normalizer (zpowers_le.2 hbX)
    rw [Nat.card_zpowers, hbo] at h
    calc Nat.card ↥(zpowers b ⊔ X) ∣ Nat.card X * (2 ^ n - 1) := ⟨_, h.symm⟩
      _ ∣ (2 ^ n - 1) * Nat.card D.T * (2 ^ n - 1) := Nat.mul_dvd_mul_right hXd _
      _ = (2 ^ n - 1) ^ 2 * Nat.card D.T := by ring
  obtain ⟨l, hlL, hl⟩ := uc22p21c_mem_barImage.1 hx₀
  have hll : ((l * l : ↥D.M) : G) ∈ zpowers b ⊔ X := by
    refine (barPreimage_barImage_of_pCoreOf_le hYM hOY).le
      (uc22p21c_mem_barPreimage.2 ⟨(l * l).2, ?_⟩)
    show uc22p21cPi D.M (l * l) ∈ barImage D.M (zpowers b ⊔ X)
    have e : x₀ * x₀ = x₀ * x₁⁻¹ * (x₀ * x₁) := by
      calc x₀ * x₀ = x₀ * (x₀ * x₁⁻¹) * x₁ := by group
        _ = x₀ * (x₁⁻¹ * x₀) * x₁ := by rw [hcomm x₀ hx₀ _ (inv_mem hx₁)]
        _ = x₀ * x₁⁻¹ * (x₀ * x₁) := by group
    rw [map_mul, hl, e, ← hbx]
    exact mul_mem (barImage_mono le_sup_right hyX)
      (uc22p21c_mem_barImage.2 ⟨⟨b, c.hBM hb⟩, mem_sup_left (mem_zpowers b), rfl⟩)
  have hx₀o : orderOf x₀ = 2 ^ n - 1 := orderOf_eq_prime hx₀q hx₀1
  have hw1 : x₀ * x₀ ≠ 1 := fun h => u.r_ne_two <| by
    have h2 : orderOf x₀ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h)
    rw [hx₀o] at h2
    exact (Nat.prime_dvd_prime_iff_eq u.prime_r Nat.prime_two).1 h2
  have hwq : (x₀ * x₀) ^ (2 ^ n - 1) = 1 := by
    rw [← sq, ← pow_mul, mul_comm, pow_mul, hx₀q, one_pow]
  have hdvd : 2 ^ n - 1 ∣ orderOf (l * l) := by
    have h := orderOf_map_dvd (uc22p21cPi D.M) (l * l)
    rwa [map_mul, hl, orderOf_eq_prime hwq hw1] at h
  set w : ↥D.M := (l * l) ^ (orderOf (l * l) / (2 ^ n - 1)) with hw
  have hwo : orderOf (w : G) = 2 ^ n - 1 := by
    rw [Subgroup.orderOf_coe, hw, orderOf_pow_orderOf_div (orderOf_pos _).ne' hdvd]
  have hwL : (w : G) ∈ L := by
    rw [hw, Subgroup.coe_pow, Subgroup.coe_mul]
    exact pow_mem (mul_mem hlL hlL) _
  have hwY : (w : G) ∈ zpowers b ⊔ X := by
    rw [hw, Subgroup.coe_pow]
    exact pow_mem hll _
  have hle : zpowers (w : G) ⊔ D.T ≤ zpowers b ⊔ X :=
    sup_le (zpowers_le.2 hwY) (hTX.trans le_sup_right)
  obtain ⟨a, ha⟩ := D.sylowM.isPGroup.exists_card_eq
  have hcard : Nat.card ↥(zpowers (w : G) ⊔ D.T) ∣ 2 ^ a * (2 ^ n - 1) ^ 2 := by
    rw [mul_comm, ← ha]
    exact (Subgroup.card_dvd_of_le hle).trans hYd
  have hwr : Nat.card (zpowers (w : G)) = 2 ^ n - 1 := by rw [Nat.card_zpowers, hwo]
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := u4x_s21_1Hyp u.prime_r u.r_ne_two hwr hcard
    (hA _ (zpowers_le.2 hwL) hwr)
  exact uc22s21rn_not_le_of_uniqueMax D hH (h211 h1930 c _ h1 h2 h3 h4 h5 h6).1
    (hle.trans (sup_le (zpowers_le.2 hbH) hXH))

end U4X

end CFSG.LocalAnalysis.UniquenessCase.UC22
