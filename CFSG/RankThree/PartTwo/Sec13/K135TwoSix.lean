module

public import CFSG.RankThree.PartTwo.Sec13.F135LastKDefs
public import CFSG.RankThree.PartTwo.Sec13.F135LastLift
public import CFSG.Quasithin.Vol2.KGFactC31HeChains
public import CFSG.Sporadic.GLQ.J4TwoRank
public import CFSG.Sporadic.HeldB.CertPBridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG Subgroup

theorem exists_sub_two_six {G : Type*} [Group G] (E : Subgroup G) {k : ℕ} (hk : 6 ≤ k)
    (hsq : ∀ x ∈ E, x * x = 1) (hcard : Nat.card E = 2 ^ k) :
    ∃ T : Subgroup G, T ≤ E ∧ (∀ t ∈ T, t * t = 1) ∧ Nat.card T = 2 ^ 6 := by
  haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) 2 (n := 6)
    (by rw [hcard]; exact pow_dvd_pow 2 hk)
  refine ⟨K.map E.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · intro t ht
    obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.1 ht
    exact hsq x x.2
  · rw [Subgroup.card_map_of_injective E.subtype_injective, hK]

theorem hasTwoSix_of_sub {G : Type*} [Group G] (H E : Subgroup G) (hEH : E ≤ H) {k : ℕ}
    (hk : 6 ≤ k) (hsq : ∀ x ∈ E, x * x = 1) (hcard : Nat.card E = 2 ^ k) : HasTwoSix H := by
  obtain ⟨T, hTE, hTsq, hTcard⟩ := exists_sub_two_six E hk hsq hcard
  refine ⟨T.subgroupOf H, fun t ht => Subtype.ext (hTsq _ ht), ?_⟩
  rw [← hTcard]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hTE.trans hEH)).toEquiv

theorem sq_eq_one_of_isElementaryAbelian_two {G : Type*} [Group G] (E : Subgroup G)
    (hE : CFSG.IsElementaryAbelian 2 E) : ∀ x ∈ E, x * x = 1 := by
  intro x hx
  have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.1 hE.exponent_dvd_p ⟨x, hx⟩
  have h' := congrArg Subtype.val h
  simpa [sq] using h'

theorem hasTwoSix_He :
    HasTwoSix He := by
  have h : HasTwoSix ↥CFSG.Sporadic.HeldB.heP :=
    hasTwoSix_of_sub CFSG.Sporadic.HeldB.heP _ CFSG.Quasithin.KGC31.He.E_le_heP (k := 6) le_rfl
      (CFSG.Quasithin.KGC31.eSub_sq _) (CFSG.Quasithin.KGC31.card_eSub _)
  exact h.of_mulEquiv CFSG.Sporadic.HeldB.heEquivP.symm

theorem hasTwoSix_J4 :
    HasTwoSix J4 := by
  obtain ⟨E, hE, hcard⟩ := CFSG.Sporadic.GLQ.J4TwoRank.exists_elemAbelian
  have h : HasTwoSix (⊤ : Subgroup J4) :=
    hasTwoSix_of_sub ⊤ E le_top (k := 11) (by norm_num)
      (sq_eq_one_of_isElementaryAbelian_two E hE) hcard
  exact h.of_mulEquiv Subgroup.topEquiv

theorem kFactTwoSix_holds :
    KFactTwoSix :=
  ⟨hasTwoSix_He, hasTwoSix_J4⟩

end CFSG.RankThree.PartTwo.Sec13.F135Last
