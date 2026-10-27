module

public import CFSG.RankThree.PartOne.S9.MinTwoAction.LiftingBase
public import CFSG.RankThree.PartOne.S9.StatementsTwoAction

public section

namespace CFSG.RankThree.PartOne

open CFSG
open scoped commutatorElement

namespace Lifting36

variable {G : Type} [Group G] [Finite G]

theorem alternatives_elementary
    (hEFQKE : ElementaryFaithfulQuotientKernelElimination)
    (hESAWGL : ElementarySmallActionWholeGroupLifting)
    {p q d : ℕ} {A D R X : Subgroup G} (hset : MinTwoActionSetting p q A D R)
    (hrank : ∀ r ∈ R, r ≠ 1 → CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({r} : Set G)) ≤ 3)
    (hpd : (p = 7 ∧ d = 3) ∨ (p = 5 ∧ d = 4))
    (hXD : X ≤ D) (hXirr : IsFrattiniIrreducibleFor (R ⊔ A) X)
    (hKΦ : R ⊓ Subgroup.centralizer (X : Set G) ≤ inSubgroup frattini R)
    (hirrR : ∀ Y : Subgroup G, inSubgroup frattini R ≤ Y → Y ≤ R →
      A ≤ Subgroup.normalizer (Y : Set G) → Y = inSubgroup frattini R ∨ Y = R)
    (hcomm : ⁅R, R⁆ ≤ R ⊓ Subgroup.centralizer (X : Set G))
    (hsq : ∀ r ∈ R, r ^ 2 ∈ R ⊓ Subgroup.centralizer (X : Set G))
    (hidx : (R ⊓ Subgroup.centralizer (X : Set G)).relIndex R = 2 ^ d)
    (hB : Nat.card (A ⊓ Subgroup.centralizer (R : Set G) : Subgroup G) = p) :
    ((p = 5 ∧ IsElementaryAbelian 2 R ∧ Nat.card R = 16) ∨
        (p = 7 ∧ IsElementaryAbelian 2 R ∧ Nat.card R = 8)) ∧
      (∃ r ∈ R, r ≠ 1 ∧ CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({r} : Set G)) = 3) ∧
      ⁅D, R⁆ = D ∧ (inSubgroup frattini D).relIndex D = q ^ p ∧
      (⁅A ⊓ Subgroup.centralizer (R : Set G), D⁆ = ⊥ ∨ q % p = 1) := by
  have hΦK : inSubgroup frattini R ≤ R ⊓ Subgroup.centralizer (X : Set G) :=
    inSubgroup_frattini_le Nat.prime_two hset.R_two hcomm hsq
  have hKeq : R ⊓ Subgroup.centralizer (X : Set G) = inSubgroup frattini R :=
    le_antisymm hKΦ hΦK
  have hAmin : ∀ Y : Subgroup G, R ⊓ Subgroup.centralizer (X : Set G) ≤ Y → Y ≤ R →
      A ≤ Subgroup.normalizer (Y : Set G) →
      Y = R ⊓ Subgroup.centralizer (X : Set G) ∨ Y = R := by
    rw [hKeq]
    exact hirrR
  obtain ⟨hK1, hRel, hRcard, -, -, -, -, -, -⟩ := hEFQKE G p q d A D R X hset.prime_p hset.prime_q
    hset.three_lt_p hset.q_ne_two hset.p_ne_q hpd hset.A_elem hset.A_card hset.R_two hset.R_inv
    hset.D_inv hset.D_pgroup hset.D_exp hset.D_class hrank hXD hXirr hcomm hsq hidx hAmin hB
  have hΦ1 : inSubgroup frattini R = ⊥ := by rw [← hKeq]; exact hK1
  have hirrA : ∀ Y : Subgroup G, Y ≤ R → A ≤ Subgroup.normalizer (Y : Set G) → Y = ⊥ ∨ Y = R := by
    intro Y hYR hAY
    have := hirrR Y (hΦ1 ▸ bot_le) hYR hAY
    rwa [hΦ1] at this
  obtain ⟨-, hDel, hDcard, hDR, -, -, hp7, hp5, hBD⟩ := hESAWGL G p q d A D R hset.prime_p
    hset.prime_q hset.q_ne_two hset.p_ne_q.symm hpd hset.A_elem hset.A_card hset.R_inv hRel hRcard
    hB hirrA hset.D_inv hset.D_pgroup hset.D_exp hset.D_class hset.R_act hrank
  have hΦD : inSubgroup frattini D = ⊥ := inSubgroup_frattini_eq_bot hset.prime_q hDel
  have hidxD : (inSubgroup frattini D).relIndex D = q ^ p := by
    rw [hΦD, Subgroup.relIndex_bot_left, hDcard]
  have hex : ∃ r ∈ R, r ≠ 1 ∧ CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({r} : Set G)) = 3 := by
    have hn : Nat.card R ≠ 1 := by
      rcases hpd with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> rw [hRcard] <;> norm_num
    obtain ⟨r, hrR, hr1⟩ : ∃ r ∈ R, r ≠ 1 := by
      by_contra hcon
      push Not at hcon
      apply hn
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun x y => Subtype.ext ?_⟩, ⟨1⟩⟩
      rw [hcon x x.2, hcon y y.2]
    rcases hpd with ⟨hp7', -⟩ | ⟨hp5', -⟩
    · exact ⟨r, hrR, hr1, hp7 hp7' r hrR hr1⟩
    · have h10 := (hp5 hp5').1
      have hne : {r : G | r ∈ R ∧ r ≠ 1 ∧
          CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({r} : Set G)) = 3}.Nonempty := by
        rw [Set.nonempty_iff_ne_empty]
        intro hemp
        rw [hemp] at h10
        simp at h10
      obtain ⟨r, hrR, hr1, hr3⟩ := hne
      exact ⟨r, hrR, hr1, hr3⟩
  refine ⟨?_, hex, hDR, hidxD, hBD⟩
  rcases hpd with ⟨hp7', hd3⟩ | ⟨hp5', hd4⟩
  · exact Or.inr ⟨hp7', hRel, by rw [hRcard, hd3]; norm_num⟩
  · exact Or.inl ⟨hp5', hRel, by rw [hRcard, hd4]; norm_num⟩

end Lifting36

theorem minimalTwoActionAlternatives_of
    (hMTASFQ : MinimalTwoActionSmallFaithfulQuotient)
    (hEFQKE : ElementaryFaithfulQuotientKernelElimination)
    (hESAWGL : ElementarySmallActionWholeGroupLifting)
    (hMTAWR3 : MinimalTwoActionWithoutRankThreeFixedGroup)
    (hM5 : MinimalFiveActionSmallFieldKernelCentralization) :
    MinimalTwoActionAlternatives := by
  intro G _ _ p q A D R hset hrank
  by_cases h2 : ∀ r ∈ R, r ≠ 1 →
      CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({r} : Set G)) ≤ 2
  · obtain ⟨h5, hR, hDR, hDQ⟩ := hMTAWR3 G p q A D R hset h2
    exact Or.inr (Or.inr ⟨h5, hR, hDR, hDQ⟩)
  · push Not at h2
    obtain ⟨r0, hr0R, hr01, hr0⟩ := h2
    have hr03 : CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({r0} : Set G)) = 3 :=
      le_antisymm (hrank r0 hr0R hr01) hr0
    obtain ⟨X, hXD, -, hXirr, -, hKΦ, -, hirrR, -, hshape, hB, -, -, -⟩ :=
      hMTASFQ G p q A D R hset hrank
    rcases hshape with ⟨hp7, hc, hs, hi⟩ | ⟨hp5, hc, hs, hi⟩ | ⟨hp5, -⟩
    · exact Or.inl (Lifting36.alternatives_elementary hEFQKE hESAWGL hset hrank
        (Or.inl ⟨hp7, rfl⟩) hXD hXirr hKΦ hirrR hc hs hi hB)
    · exact Or.inl (Lifting36.alternatives_elementary hEFQKE hESAWGL hset hrank
        (Or.inr ⟨hp5, rfl⟩) hXD hXirr hKΦ hirrR hc hs hi hB)
    · subst hp5
      refine Or.inr (Or.inl ⟨rfl, ⟨r0, hr0R, hr01, hr03⟩, ?_⟩)
      by_cases hq : 7 < q
      · exact Or.inl hq
      · right
        have hqp := hset.prime_q
        have hq2 := hset.q_ne_two
        have hq5 := hset.p_ne_q
        have hq37 : q = 3 ∨ q = 7 := by
          have : q ≤ 7 := by omega
          interval_cases q <;> first | omega | (exfalso; norm_num at hqp)
        exact hM5 G q A D R hset (by rcases hq37 with rfl | rfl <;> simp) hrank

end CFSG.RankThree.PartOne
