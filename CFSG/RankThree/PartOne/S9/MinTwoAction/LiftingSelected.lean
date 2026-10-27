module

public import CFSG.RankThree.PartOne.S9.MinTwoAction.LiftingSelectedBase
public import CFSG.RankThree.PartOne.S9.StatementsTwoAction
import CFSG.RankThree.GroupTheory.SteinbergBYQD32Extraspecial

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory
open scoped commutatorElement

namespace Lifting36

variable {G : Type} [Group G] [Finite G]

theorem faithful_of_qd32 (hMTASFQ : MinimalTwoActionSmallFaithfulQuotient)
    (hEFQKE : ElementaryFaithfulQuotientKernelElimination) {p q : ℕ} {A D R : Subgroup G}
    (hset : MinTwoActionSetting p q A D R)
    (hrank : ∀ r ∈ R, r ≠ 1 → CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({r} : Set G)) ≤ 3)
    (hp5 : p = 5) (e : ↥R ≃* QD32) : R ⊓ Subgroup.centralizer (D : Set G) = ⊥ := by
  subst hp5
  obtain ⟨X, hXD, -, hXirr, -, hKΦ, -, hirrR, -, hshape, hB, -, -, -⟩ :=
    hMTASFQ G 5 q A D R hset hrank
  have hRcard : Nat.card R = 32 := by
    rw [Nat.card_congr e.toEquiv]
    exact card_QD32
  have hK0 : R ⊓ Subgroup.centralizer (X : Set G) = ⊥ := by
    rcases hshape with ⟨h7, -⟩ | ⟨-, hc, hs, hi⟩ | ⟨-, φ, hφs, hφk⟩
    · omega
    · have hΦK : inSubgroup frattini R ≤ R ⊓ Subgroup.centralizer (X : Set G) :=
        inSubgroup_frattini_le Nat.prime_two hset.R_two hc hs
      have hKeq : R ⊓ Subgroup.centralizer (X : Set G) = inSubgroup frattini R :=
        le_antisymm hKΦ hΦK
      have hAmin : ∀ Y : Subgroup G, R ⊓ Subgroup.centralizer (X : Set G) ≤ Y → Y ≤ R →
          A ≤ Subgroup.normalizer (Y : Set G) →
          Y = R ⊓ Subgroup.centralizer (X : Set G) ∨ Y = R := by
        rw [hKeq]
        exact hirrR
      obtain ⟨-, -, hRc, -, -, -, -, -, -⟩ := hEFQKE G 5 q 4 A D R X hset.prime_p hset.prime_q
        hset.three_lt_p hset.q_ne_two hset.p_ne_q (Or.inr ⟨rfl, rfl⟩) hset.A_elem hset.A_card
        hset.R_two hset.R_inv hset.D_inv hset.D_pgroup hset.D_exp hset.D_class hrank hXD hXirr hc
        hs hi hAmin hB
      rw [hRcard] at hRc
      norm_num at hRc
    · have hker : Nat.card φ.ker * Nat.card φ.range = Nat.card ↥R :=
        Subgroup.card_ker_mul_card_range φ
      have hrange : Nat.card φ.range = 32 := by
        rw [MonoidHom.range_eq_top.mpr hφs, Subgroup.card_top]
        exact card_QD32
      rw [hrange, hRcard] at hker
      have hker1 : Nat.card φ.ker = 1 := by omega
      rw [Subgroup.card_eq_one, hφk] at hker1
      rw [eq_bot_iff]
      intro g hg
      have hmem : (⟨g, hg.1⟩ : ↥R) ∈ (R ⊓ Subgroup.centralizer (X : Set G)).subgroupOf R := hg
      rw [hker1, Subgroup.mem_bot] at hmem
      exact congrArg Subtype.val hmem
  rw [eq_bot_iff]
  intro g hg
  have hg' : g ∈ R ⊓ Subgroup.centralizer (X : Set G) :=
    ⟨hg.1, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hXD) hg.2⟩
  rw [hK0] at hg'
  exact hg'

end Lifting36

theorem selectedPrimeMinimalTwoActionReduction_of (hMTAA : MinimalTwoActionAlternatives)
    (hMTASFQ : MinimalTwoActionSmallFaithfulQuotient)
    (hEFQKE : ElementaryFaithfulQuotientKernelElimination) :
    SelectedPrimeMinimalTwoActionReduction := by
  intro G _ _ hrank p hp hpσ hp3 q hq hq2 hqp A R D hAel hAR hR2 hRA hRne hLD hDq hDexp hDcl hRD
    hidx hBcard hmin hGood
  have hrank3 : ∀ r ∈ R, r ≠ 1 →
      CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({r} : Set G)) ≤ 3 := fun r hr hr1 =>
    Lifting36.pRank_centralizer_le_three hrank hq hq2 D hR2 hr hr1
  obtain ⟨a, b, haA, haB, hbB, hb1, hbD, hset⟩ := Lifting36.exists_A0 hp hp3 hq hq2 hqp hAel hAR
    hR2 hRA hRne hLD hDq hDexp hDcl hRD hidx hBcard hmin
  have hAlt := hMTAA G p q _ D R hset hrank3
  have hp7 : p ≤ 7 := by
    rcases hAlt with ⟨(⟨h5, -⟩ | ⟨h7, -⟩), -⟩ | ⟨h5, -⟩ | ⟨h5, -⟩ <;> omega
  refine ⟨hp7, ?_⟩
  by_cases hBD : ⁅A ⊓ Subgroup.centralizer (R : Set G), D⁆ = ⊥
  · exact Or.inl hBD
  right
  obtain ⟨d₀, hd₀, hbd₀⟩ := hbD hBD
  have hbA₀ : b ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers a :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
  have hB₀ne : ⁅(Subgroup.zpowers b ⊔ Subgroup.zpowers a) ⊓ Subgroup.centralizer (R : Set G),
      D⁆ ≠ ⊥ := by
    intro h
    have := Subgroup.commutator_mem_commutator (show b ∈ (Subgroup.zpowers b ⊔ Subgroup.zpowers a) ⊓
      Subgroup.centralizer (R : Set G) from ⟨hbA₀, hbB.2⟩) hd₀
    rw [h, Subgroup.mem_bot] at this
    exact hbd₀ this
  have hbA : b ∈ A := hbB.1
  have hloc3 : ∀ r ∈ R, r ≠ 1 →
      CFSG.pRank q ↥(D ⊓ Subgroup.centralizer ({r} : Set G)) = 3 → localRank q G = 3 :=
    fun r hr hr1 h3 => le_antisymm (localRank_le_three_of_evenRank_eq_three hrank hq hq2)
      (Lifting36.three_le_localRank_of_pRank_eq_three hq D hR2 hr hr1 h3)
  have hlarge : 5 < q → localRank q G = 3 → sigmaA G = {t | t.Prime ∧ 5 < t ∧ localRank t G = 3} :=
    fun h5q hq3 => rank_three_selector_of_large hrank ⟨q, hq, h5q, hq3⟩
  rcases hAlt with ⟨hshape, ⟨r, hr, hr1, hr3⟩, -, hidxD, hq1⟩ | ⟨hp5, ⟨r, hr, hr1, hr3⟩, hq7⟩ |
      ⟨hp5, ⟨e⟩, hDR, hQD⟩
  ·
    have hqp1 : q % p = 1 := hq1.resolve_left hB₀ne
    have hp57 : p = 5 ∨ p = 7 := by omega
    have hq7 : 7 < q := by
      by_contra hle
      push Not at hle
      have hq1' := hq.two_le
      rcases hp57 with h | h <;> subst h <;> interval_cases q <;>
        first | omega | (exfalso; norm_num at hq)
    have hloc := hloc3 r hr hr1 hr3
    have hσ := hlarge (by omega) hloc
    have hpσ' : p ∈ {t | t.Prime ∧ 5 < t ∧ localRank t G = 3} := hσ ▸ hpσ
    have hp7' : p = 7 := by
      have : 5 < p := hpσ'.2.1
      omega
    subst hp7'
    have hqσ : q ∈ sigmaA G := hσ ▸ ⟨hq, by omega, hloc⟩
    have hqG : CFSG.pRank q G ≤ 3 := hGood rfl q hqσ hq7
    have hDG : CFSG.pRank q ↥D ≤ CFSG.pRank q G :=
      Quotient36.pRank_le_of_injective' hq.one_lt D.subtype D.subtype_injective
    have := Lifting36.three_lt_pRank_of_relIndex hq hDq hDexp hDcl hidxD (by norm_num)
    omega
  ·
    have hq7' : 7 < q := hq7.resolve_right hB₀ne
    have hloc := hloc3 r hr hr1 hr3
    have hσ := hlarge (by omega) hloc
    have hpσ' : p ∈ {t | t.Prime ∧ 5 < t ∧ localRank t G = 3} := hσ ▸ hpσ
    have : 5 < p := hpσ'.2.1
    omega
  ·
    subst hp5
    have hfaith : R ⊓ Subgroup.centralizer (D : Set G) = ⊥ :=
      Lifting36.faithful_of_qd32 hMTASFQ hEFQKE hset hrank3 rfl e
    have hRext : IsExtraspecialPGroup 2 ↥R := Lifting36.isExtraspecialPGroup_of_mulEquiv e.symm
      SteinbergBY.quaternion_dihedral_extraspecial_involution_generation.2.1
    have hRcard : Nat.card R = 2 ^ (1 + 2 * 2) := by
      rw [Nat.card_congr e.toEquiv, card_QD32]
      norm_num
    have hb5 : b ^ 5 = 1 := elemPow_eq_one_of_isElementaryAbelian (A := A) b hbA
    obtain ⟨hq1, hDb⟩ := Lifting36.scalar_conclusions hq hq2 hqp hLD hDq
      le_sup_left hR2 hfaith hRext hRcard (Lifting36.relIndex_frattini_of_isQDShape hq hQD)
      (Subgroup.mem_sup_right hbA) hbB.2 hb5 ⟨d₀, hd₀, hbd₀⟩
    have hDB : ⁅D, A ⊓ Subgroup.centralizer (R : Set G)⁆ = D := by
      refine le_antisymm (Subgroup.le_normalizer_iff_commutator_le_left.mp
        (inf_le_left.trans (le_sup_right.trans hLD))) ?_
      calc D = ⁅D, Subgroup.zpowers b⁆ := hDb.symm
        _ ≤ ⁅D, A ⊓ Subgroup.centralizer (R : Set G)⁆ :=
          Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hbB)
    have hloc2 : localRank q G ≤ 2 := by
      by_contra hcon
      push Not at hcon
      have hloc : localRank q G = 3 :=
        le_antisymm (localRank_le_three_of_evenRank_eq_three hrank hq hq2) hcon
      have hq5 : 5 < q := by
        have hq1' := hq.two_le
        by_contra hle
        push Not at hle
        interval_cases q <;> omega
      have hσ := hlarge hq5 hloc
      have hpσ' : 5 ∈ {t | t.Prime ∧ 5 < t ∧ localRank t G = 3} := hσ ▸ hpσ
      exact absurd hpσ'.2.1 (by norm_num)
    exact ⟨rfl, ⟨e⟩, hfaith, hDR, hDB, hq1, hloc2, hQD⟩

end CFSG.RankThree.PartOne
