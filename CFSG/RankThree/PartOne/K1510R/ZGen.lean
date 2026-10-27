module

public import CFSG.RankThree.PartOne.K159F.ZFive
import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual
import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents

public section

namespace CFSG.RankThree.PartOne.K1510R

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne CFSG.RankThree.PartOne.StrongP
  CFSG.RankThree.PartOne.K159F

@[expose] def KF159ZFiveResGen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152Five p E A (lieGenerated p E) →
    p = 5 → ∀ x ∈ E, x ≠ 1 → ∀ X ∈ thetaComponentsAt p x,
      p ∣ Nat.card ↥(Subgroup.center (↥X ⧸ aschbacherSolvableCore p ↥X)) → E ≤ X → False

theorem kf159ZFiveRes_of_gen (h : KF159ZFiveResGen) : KF159ZFiveRes := by
  intro G _ _ p A c L E h15 hF hout hp5 X hX _ hpZ hEX
  obtain ⟨B, hB, hXB⟩ := hX
  obtain ⟨x, hxB, hx1, hXx⟩ := mem_thetaComponentFamily_iff.1 hXB
  exact h G p A c L E h15 hF hout hp5 x (hB.1 hxB) hx1 X hXx hpZ hEX

@[expose] def KF159ZFiveGen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152Five p E A (lieGenerated p E) →
    ∀ x ∈ E, x ≠ 1 → ∀ X ∈ thetaComponentsAt p x,
      ¬ p ∣ Nat.card ↥(Subgroup.center (↥X ⧸ aschbacherSolvableCore p ↥X))

theorem kf159ZFiveGen_of_inputs (h155 : Node155) (hrank : CenterRankFive)
    (hRes : KF159ZFiveResGen) : KF159ZFiveGen := by
  classical
  intro G _ _ p A c L E h15 hF hout x hxE hx1 X hXx hpZ
  have h := h15.h12
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := by
    have h3 := h.three_lt
    by_contra hlt
    have h4 : p = 4 := by omega
    exact absurd (h4 ▸ hp) (by norm_num)
  have hEcard : Nat.card ↥E = p ^ 4 := by
    obtain ⟨-, -, -, -, -, hc, -⟩ := hout
    exact hc
  have hnonab : ∃ a b : G, a * b ≠ b * a := h.setup.2.1
  have hKP : IsKProper G := h.setup.2.2.1
  have hsimple : IsSimpleGroup G := h.setup.1
  have hrk3 : CFSG.twoLocalOddRank G ≤ 3 := h.setup.2.2.2.2.1.le
  have hEX : E ≤ Subgroup.normalizer (X : Set G) :=
    h.E_normalizes_thetaComponentsAt selected_prime_elements_normalize_theta_components hxE hXx
  have hXC : X ≤ Subgroup.centralizer ({x} : Set G) := (mem_thetaComponentsAt_iff.1 hXx).1
  have hXtop : X ≠ ⊤ := by
    intro htop
    exact EmbeddingFixedResidual.centralizer_ne_top_of_simple hnonab hx1
      (eq_top_iff.2 (htop ▸ hXC))
  have hKX : CFSG.IsKGroup ↥X := hKP X hXtop
  have hQq : CFSG.IsQuasisimple (↥X ⧸ aschbacherSolvableCore p ↥X) :=
    isQuasisimple_thetaQuotient_of_mem_thetaComponentsAt hp hXx
  have hZ2 : ¬ 2 ∣ Nat.card (Subgroup.center (↥X ⧸ aschbacherSolvableCore p ↥X)) :=
    N143.not_dvd_card_center_theta_quotient (L := ↥X) hp Nat.prime_two (by omega)
  have hodd : Odd (Nat.card (Subgroup.center (↥X ⧸ aschbacherSolvableCore p ↥X))) :=
    Nat.odd_iff.2 (by omega)
  have hrkX : CFSG.twoLocalOddRank ↥X ≤ 3 := by
    have h1 := Sec9A.evenRank_subgroup_le X
    rw [CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank,
      CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank] at h1
    exact h1.trans hrk3
  have hθp : ¬ p ∣ Nat.card ↥(aschbacherSolvableCore p ↥X) :=
    (solvable_prime_complement_core_characterization hp).2.2.1
  obtain ⟨P, hPsyl, hEP, hPW⟩ := exists_sylow_normalizer hp h155 X h15 hF hout
  obtain ⟨PW, hPWsyl, hPPW⟩ := Sec12Fus.exists_isSylowOf_ge (p := p) hPW hPsyl.2.1
  have hP' : CFSG.ABGLocalTools.IsSylowOf p P (X ⊔ E) := CFSG.ABGLocalTools.isSylowOf_iff.2 hPsyl
  have hPX : CFSG.ABGLocalTools.IsSylowOf p (P ⊓ X) X :=
    hP'.inf_of_le_normalizer le_sup_left (sup_le Subgroup.le_normalizer hEX)
  have key : ∀ R : Subgroup (↥X ⧸ aschbacherSolvableCore p ↥X), (∀ b ∈ R, b ^ p = 1) →
      (∀ a ∈ R, ∀ b ∈ R, a * b = b * a) → p ^ 4 ≤ Nat.card R →
      ∃ R' : Subgroup G, R' ≤ E ∧ R' ≤ P ⊓ X ∧ Nat.card R' = Nat.card R := by
    intro R hRexp hRab hRcard
    obtain ⟨R', hR'P, hR'exp, hR'ab, hR'card⟩ := exists_lift_elemAbelian hp hPX hθp hRexp hRab
    refine ⟨R', ?_, hR'P, hR'card⟩
    refine le_E_of_elemAb hp h155 h15 hF hout hPWsyl
      (hR'P.trans inf_le_left |>.trans hPPW) hR'exp hR'ab ?_
    rw [hR'card]
    exact hRcard
  rcases hrank ↥X hrkX hKX (aschbacherSolvableCore p ↥X) hQq p hp (by omega) hpZ hodd with
    ⟨R, hRexp, hRab, hRcard⟩ | ⟨hp5eq, R, hRexp, hRab, hRcard⟩
  ·
    obtain ⟨R', hR'E, -, hR'card⟩ := key R hRexp hRab
      (le_trans (Nat.pow_le_pow_right hp.pos (by norm_num)) hRcard)
    have h1 : Nat.card R' ≤ Nat.card E := Subgroup.card_le_of_le hR'E
    rw [hR'card, hEcard] at h1
    have h2 : p ^ 4 < p ^ 5 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  ·
    obtain ⟨R', hR'E, hR'P, hR'card⟩ := key R hRexp hRab hRcard
    have hEeq : R' = E := by
      refine Subgroup.eq_of_le_of_card_ge hR'E ?_
      rw [hR'card, hEcard]
      exact hRcard
    have hEX' : E ≤ X := by
      rw [← hEeq]
      exact hR'P.trans inf_le_right
    exact hRes G p A c L E h15 hF hout hp5eq x hxE hx1 X hXx hpZ hEX'

end CFSG.RankThree.PartOne.K1510R
