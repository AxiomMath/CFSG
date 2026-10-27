module

public import CFSG.RankThree.PartOne.K133.KillL2
public import CFSG.RankThree.PartOne.CTP.SeitzExc
public import CFSG.RankThree.PartOne.K133.TwoLoc

public section

namespace CFSG.RankThree.PartOne.K133

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.GorensteinWalter
open CFSG.RankThree.PartOne.Census3 (IsoLie)

theorem noRankThree_of_rank_le_one {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hZ : Subgroup.center X = ⊥)
    (hX : ∀ A : Subgroup X, IsElementaryAbelian p A → Nat.card A ≤ p)
    (hO : ∀ B : Subgroup (Outer X), IsElementaryAbelian p B → Nat.card B ≤ p) : NoRankThree p X := by
  classical
  rintro ⟨E, hE, hc⟩
  have : Fact p.Prime := ⟨hp⟩
  let φ : ↥E →* Outer X := (QuotientGroup.mk' (inner X)).comp E.subtype
  have hrange : Nat.card φ.range ≤ p := hO _ (isElementaryAbelian_range hE φ)
  have hker : ∀ x : ↥E, x ∈ φ.ker → (x : MulAut X) ∈ inner X := fun x hx =>
    (QuotientGroup.eq_one_iff (x : MulAut X)).1 (MonoidHom.mem_ker.1 hx)
  set E₀ : Subgroup (MulAut X) := φ.ker.map E.subtype with hE₀
  have hE₀le : E₀ ≤ inner X := by
    rintro _ ⟨x, hx, rfl⟩
    exact hker x hx
  have hE₀el : IsElementaryAbelian p E₀ := isElementaryAbelian_of_le hE (Subgroup.map_subtype_le _)
  have hE₀card : Nat.card E₀ = Nat.card φ.ker := by
    rw [hE₀, Subgroup.card_map_of_injective E.subtype_injective]
  have hmul := Subgroup.card_ker_mul_card_range φ
  rw [hc] at hmul
  obtain ⟨A, hA, hAc⟩ := exists_elemAb_card_eq_of_le_inner hZ hE₀el hE₀le
  have hle := hX A hA
  rw [hAc, hE₀card] at hle
  have hp0 : 0 < p := hp.pos
  have h1 : p ^ 3 ≤ p * p := by
    calc p ^ 3 = Nat.card φ.ker * Nat.card φ.range := hmul.symm
      _ ≤ p * p := Nat.mul_le_mul hle hrange
  have h2 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  nlinarith

theorem card_le_of_isCyclic_elemAb {Y : Type*} [Group Y] [Finite Y] [IsCyclic Y] {p : ℕ}
    (hp : p.Prime) (A : Subgroup Y) (hA : IsElementaryAbelian p A) : Nat.card A ≤ p := by
  have : IsCyclic A := Subgroup.isCyclic A
  have hexp : Monoid.exponent ↥A ∣ p := IsElementaryAbelian.exponent_dvd_p p _
  rw [IsCyclic.exponent_eq_card] at hexp
  exact Nat.le_of_dvd hp.pos hexp

theorem kf133ResMaxAt_leaf7_zero : KF133ResMaxAt (leaf7 0) := by
  refine KF133ResMaxAt.of_dead fun X _ _ _ hne hX p hp h5 => ?_
  obtain ⟨q, hq2, hv, ⟨e0⟩⟩ := hX
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have e : X ≃* PSL2 (GaloisField q.p q.exponent) :=
    e0.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv)
  have hne0 : ((p : ℕ) : GaloisField q.p q.exponent) ≠ 0 := by
    intro h0
    rw [CharP.cast_eq_zero_iff (GaloisField q.p q.exponent) q.p p, hq2] at h0
    exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h0) (by omega)
  have : NeZero ((p : ℕ) : GaloisField q.p q.exponent) := ⟨hne0⟩
  exact (NoRankThree.of_mulEquiv hp e (noRankThree_psl2 hp (by omega))).dead

theorem kf133ResMaxAt_leaf7_one :
    KF133ResMaxAt (leaf7 1) := by
  refine KF133ResMaxAt.of_dead fun X _ _ _ hne hX p hp h5 => ?_
  obtain ⟨m, hiso⟩ := hX
  have : Fact p.Prime := ⟨hp⟩
  have hmodel := CTP.suzukiModel_of_isoLie m hiso
  obtain ⟨-, a, ha, F, _, _, hfa, hF, ⟨e⟩⟩ := hmodel
  have hF' : Nat.card F = 2 ^ (2 * a + 1) := by rw [hF, hfa]
  have e' : X ≃* CFSG.Open.GLASzGroup a F :=
    e.trans (MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a F))
  have hsyl := CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.suzuki_model_oddSylow_cyclic
    a ha hF' e'
  have hcyc : IsCyclic (Outer (CFSG.Blueprint.suzukiGroup a F)) :=
    (CFSG.LieType.Suzuki.suzukiGroup_outer_isCyclic_card_dvd ha hF').1
  refine (noRankThree_of_rank_le_one hp (center_eq_bot_of_simple_nonabelian hne) ?_ ?_).dead
  · intro A hA
    have hodd : Odd (Nat.card A) := by
      have : IsPGroup p A := IsElementaryAbelian.isPGroup p A
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 this
      rw [hk]
      exact (hp.eq_two_or_odd'.resolve_left (by omega)).pow
    have hc := CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.odd_commutative_subgroup_cyclic
      A hodd inferInstance hsyl
    have : IsCyclic A := hc
    have hexp : Monoid.exponent ↥A ∣ p := IsElementaryAbelian.exponent_dvd_p p _
    rw [IsCyclic.exponent_eq_card] at hexp
    exact Nat.le_of_dvd hp.pos hexp
  · intro B hB
    have heq : Outer X ≃* Outer (CFSG.Blueprint.suzukiGroup a F) := equivalence e
    have : IsCyclic (Outer X) := isCyclic_of_surjective heq.symm.toMonoidHom heq.symm.surjective
    exact card_le_of_isCyclic_elemAb hp B hB

theorem kf133ResMaxAt_leaf7_ten :
    KF133ResMaxAt (leaf7 10) := by
  refine KF133ResMaxAt.of_dead fun X _ _ _ hne hX p hp h5 => ?_
  have hT : NoRankThree p X := by
    rintro ⟨E, hE, hc⟩
    obtain ⟨hT, -, hO, -⟩ :=
      CFSG.Sporadic.Schreier.Tits.CTI_Tits_model_outer_two_part_bound X 2 1
        (CTP.reeTitsModel_tits hX)
    have hdvd : Nat.card (MulAut X) ∣ 2 * 17971200 := by
      have := CFSG.RankThree.ReeTitsAut.card_mulAut_dvd X
      rwa [hO, hT] at this
    have h3 : p ^ 3 ∣ 2 * 17971200 := by
      rw [← hc]
      exact (Subgroup.card_subgroup_dvd_card E).trans hdvd
    by_cases hp5 : p = 5
    · subst hp5
      norm_num at h3
    · exact CTP.not_sq_dvd_tits_aut hp h5 hp5
        ((pow_dvd_pow p (by norm_num : 2 ≤ 3)).trans h3)
  exact hT.dead

end CFSG.RankThree.PartOne.K133
