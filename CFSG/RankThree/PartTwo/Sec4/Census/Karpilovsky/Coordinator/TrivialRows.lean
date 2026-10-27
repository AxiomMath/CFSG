module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverList
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.PrimaryCells
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.KernelTrivialBridge
public import CFSG.Quasithin.Vol2.Ch11SecJ4MultA2
public import CFSG.GH74.KGroups.CoverM11
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.ThreeCoverSporadic
public import CFSG.Walter.J1Props.Multiplier
public import CFSG.Walter.Models
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ4CoverCert
public import CFSG.Sporadic.Recognition.HNMultiplierCert
public import CFSG.RankThree.PartOne.MultRes.HN
public import CFSG.RankThree.PartOne.MultRes.HNThree

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

open CFSG.Blueprint CFSG.RankThree.PerfectCover CFSG.AGLEmbedding Subgroup
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster
open CFSG.RankThree.PartTwo.Sec4.Census (sporadicMultiplierOrder)
open scoped commutatorElement

section Generic

theorem card_hopfMultiplier_eq_one_of_kernelTrivialAt {X : Type} [Group X] [Finite X]
    [Group.IsPerfect X] (h : ∀ p : ℕ, p.Prime → p ∣ Nat.card X → KernelTrivialAt X p) :
    Nat.card (hopfMultiplier X) = 1 := by
  have := finite_hopfMultiplier (inferInstance : Group.IsPerfect X)
  have h0 : Nat.card (hopfMultiplier X) ≠ 0 := Nat.card_pos.ne'
  by_contra h1
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd h1
  have : Fact p.Prime := ⟨hp⟩
  exact not_dvd_card_hopfMultiplier_of_kernelTrivialAt
    (h p hp (dvd_card_of_dvd_card_hopfMultiplier hp hpd)) hpd

theorem odd_card_of_isPGroup {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) {K : Type*} [Group K]
    [Finite K] (h : IsPGroup p K) : Odd (Nat.card K) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := h.exists_card_eq
  rw [hk]
  exact (hp.odd_of_ne_two h2).pow

theorem isPerfect_of_isSimpleGroup_of_not_prime {G : Type*} [Group G] [Finite G]
    (hs : IsSimpleGroup G) (hc : ¬ (Nat.card G).Prime) : Group.IsPerfect G := by
  refine Group.isPerfect_def.2 ?_
  rcases hs.eq_bot_or_eq_top_of_normal (commutator G) with h | h
  · exfalso
    have hcomm : ∀ a b : G, a * b = b * a := fun a b => by
      have h1 : ⁅a, b⁆ ∈ commutator G :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot] at h1
      exact commutatorElement_eq_one_iff_mul_comm.1 h1
    let _ : CommGroup G := { (inferInstance : Group G) with mul_comm := hcomm }
    exact hc (IsSimpleGroup.prime_card (α := G))
  · exact h

theorem exists_not_commute_of_perfect_simple {G : Type*} [Group G] [Group.IsPerfect G]
    (hs : IsSimpleGroup G) : ∃ a b : G, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have hbot : commutator G = ⊥ := by
    rw [eq_bot_iff]
    refine commutator_le.2 fun a _ b _ => ?_
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hcon a b
  have htop : commutator G = ⊤ := Group.IsPerfect.commutator_eq_top (G := G)
  have hbt : (⊥ : Subgroup G) = ⊤ := hbot.symm.trans htop
  have := hs.toNontrivial
  exact bot_ne_top hbt

theorem center_eq_bot_of_perfect_simple {G : Type*} [Group G] [Group.IsPerfect G]
    (hs : IsSimpleGroup G) : center G = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (center G) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := exists_not_commute_of_perfect_simple hs
    exact hab (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top a) b).symm

theorem kernelTrivialAt_two_of_noTwoCover {X : Type} [Group X] [Finite X] [Group.IsPerfect X]
    (hs : IsSimpleGroup X) (h : CFSG.GH74.Generic.NoTwoCover X) : KernelTrivialAt X 2 := by
  intro E _ _ _ π hπ hC hp
  have hZ : center E = π.ker := by
    refine le_antisymm (fun z hz => ?_) hC
    rw [MonoidHom.mem_ker]
    have : π z ∈ center X := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro g
      obtain ⟨y, rfl⟩ := hπ g
      rw [← map_mul, ← map_mul, hz y]
    rwa [center_eq_bot_of_perfect_simple hs] at this
  let e : E ⧸ center E ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans (QuotientGroup.quotientKerEquivOfSurjective π hπ)
  have := hs
  obtain ⟨a, b, hab⟩ := exists_not_commute_of_perfect_simple hs
  have hq : CFSG.IsQuasisimple E :=
    ⟨inferInstance, e.isSimpleGroup, e.symm a, e.symm b, fun hh => hab (by
      have := congrArg e hh
      simpa using this)⟩
  rw [← hZ] at hp ⊢
  exact h E hq hp ⟨e⟩

theorem kernelTrivialAt_two_of_noPerfectDoubleCover {X : Type} [Group X] [Finite X]
    [Group.IsPerfect X] (h : CFSG.Monster.Schur.NoPerfectDoubleCover X) :
    KernelTrivialAt X 2 :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  kernelTrivialAt_of_not_dvd_card_hopfMultiplier
    (CFSG.Quasithin.Vol2.Ch11.SecS.J4Mult.not_dvd_card_hopfMultiplier
      (fun E _ π hπ hE _ => h E π hπ hE))

theorem sylow_eq_bot_of_ne {r p : ℕ} [Fact r.Prime] (hp : p.Prime) (hrp : r ≠ p) {K : Type*}
    [Group K] [Finite K] (hK : IsPGroup p K) (Cp : Sylow r K) : (Cp : Subgroup K) = ⊥ := by
  have hr : r.Prime := Fact.out
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hm⟩ := hK.exists_card_eq
  obtain ⟨k, hk⟩ := Cp.isPGroup'.exists_card_eq
  refine Subgroup.eq_bot_of_card_eq _ ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [hk, pow_zero]
  · exfalso
    have hd : r ^ k ∣ p ^ m := hk ▸ hm ▸ Subgroup.card_subgroup_dvd_card (Cp : Subgroup K)
    have h1 : r ∣ p := hr.dvd_of_dvd_pow ((dvd_pow_self r hk0.ne').trans hd)
    exact hrp ((Nat.prime_dvd_prime_iff_eq hr hp).1 h1)

end Generic

section Rows

theorem nativeRow_M11 :
    Nat.card (hopfMultiplier (NativeSporadic.Carrier .M11)) = sporadicMultiplierOrder .M11 := by
  have hfs := CFSG.Sporadic.Mathieu.fam_m11_simplicity
  have : Finite (NativeSporadic.Carrier .M11) := hfs.1
  have hs : IsSimpleGroup (NativeSporadic.Carrier .M11) := hfs.2.2
  have : Group.IsPerfect (NativeSporadic.Carrier .M11) :=
    isPerfect_of_isSimpleGroup_of_not_prime hs (by
      rw [show Nat.card (NativeSporadic.Carrier .M11) = 7920 from CFSG.Sporadic.Mathieu.card_M11]
      norm_num)
  refine (card_hopfMultiplier_eq_one_of_kernelTrivialAt fun p hp _ => ?_).trans (by decide)
  by_cases h2 : p = 2
  · subst h2
    exact kernelTrivialAt_two_of_noTwoCover hs
      (CFSG.GH74.KGroups.M11.noTwoCover_M11 _ ⟨MulEquiv.refl _⟩)
  · intro E _ _ _ π hπ hC hpg
    exact CFSG.QuasithinUnique.Ch1.M11_perfect_odd_cover_trivial π hπ hC
      (odd_card_of_isPGroup hp h2 hpg)

theorem nativeRow_M24 :
    Nat.card (hopfMultiplier (NativeSporadic.Carrier .M24)) = sporadicMultiplierOrder .M24 := by
  have hfs := CFSG.Sporadic.Mathieu.fam_m24_simplicity
  have : Finite (NativeSporadic.Carrier .M24) := hfs.1
  have hs : IsSimpleGroup (NativeSporadic.Carrier .M24) := hfs.2.2
  have : Group.IsPerfect (NativeSporadic.Carrier .M24) :=
    isPerfect_of_isSimpleGroup_of_not_prime hs (by
      rw [show Nat.card (NativeSporadic.Carrier .M24) = 244823040 from
        CFSG.Sporadic.Mathieu.card_M24]
      norm_num)
  refine (card_hopfMultiplier_eq_one_of_kernelTrivialAt fun p hp _ => ?_).trans (by decide)
  by_cases h2 : p = 2
  · subst h2
    exact kernelTrivialAt_two_of_noPerfectDoubleCover
      CFSG.Monster.Schur.noPerfectDoubleCover_nativeM24
  · intro E _ _ _ π hπ hC hpg
    exact CFSG.SectionRank.M24_perfect_odd_cover_trivial π hπ hC
      (odd_card_of_isPGroup hp h2 hpg)

theorem nativeRow_J1 :
    Nat.card (hopfMultiplier (NativeSporadic.Carrier .J1)) = sporadicMultiplierOrder .J1 := by
  have hfs := CFSG.Sporadic.J1.fam_j1_simplicity
  have : Finite (NativeSporadic.Carrier .J1) := hfs.1
  have hs : IsSimpleGroup (NativeSporadic.Carrier .J1) := hfs.2.2
  have : Group.IsPerfect (NativeSporadic.Carrier .J1) :=
    isPerfect_of_isSimpleGroup_of_not_prime hs (by
      rw [show Nat.card (NativeSporadic.Carrier .J1) = 175560 from CFSG.Sporadic.J1.card_J1]
      norm_num)
  refine (card_hopfMultiplier_eq_one_of_kernelTrivialAt fun p _ _ => ?_).trans (by decide)
  refine (kernelTrivialAt_iff_of_mulEquiv CFSG.Walter.walterJ1EquivNative p).1 ?_
  intro E _ _ _ π hπ hC _
  exact CFSG.Walter.J1Props.J3_multiplier π hπ hC Group.IsPerfect.commutator_eq_top

theorem nativeRow_J4 :
    Nat.card (hopfMultiplier (NativeSporadic.Carrier .J4)) = sporadicMultiplierOrder .J4 := by
  have hfs := CFSG.Sporadic.J4.fam_j4_simplicity
  have : Finite (NativeSporadic.Carrier .J4) := hfs.1
  have hs : IsSimpleGroup (NativeSporadic.Carrier .J4) := hfs.2.2
  have : Group.IsPerfect (NativeSporadic.Carrier .J4) :=
    isPerfect_of_isSimpleGroup_of_not_prime hs (by
      rw [show Nat.card (NativeSporadic.Carrier .J4) = 86775571046077562880 from
        CFSG.Sporadic.J4.card_J4]
      norm_num)
  refine (card_hopfMultiplier_eq_one_of_kernelTrivialAt fun p hp _ => ?_).trans (by decide)
  by_cases h2 : p = 2
  · subst h2
    exact kernelTrivialAt_two_of_noPerfectDoubleCover
      (CFSG.Sporadic.Recognition.J4Multiplier.noPerfectDoubleCover_J4
        CFSG.ComponentClassification.RankTwoSporadic.J4.j4_foxCert
        CFSG.ComponentClassification.RankTwoSporadic.J4.j4_formCert)
  · intro E _ _ _ π hπ hC hpg
    exact CFSG.SectionRank.J4_perfect_odd_cover_trivial CFSG.SectionRank.j4OrderHyp π hπ hC
      (odd_card_of_isPGroup hp h2 hpg)

theorem prime_dvd_card_HN {p : ℕ} (hp : p.Prime) (h : p ∣ 273030912000000) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 19 := by
  rw [show 273030912000000 = 2 ^ 14 * 3 ^ 6 * 5 ^ 6 * 7 * 11 * 19 by norm_num] at h
  have e : ∀ q : ℕ, q.Prime → p ∣ q → p = q := fun q hq hd =>
    (Nat.prime_dvd_prime_iff_eq hp hq).1 hd
  rcases hp.dvd_mul.1 h with h | h
  · rcases hp.dvd_mul.1 h with h | h
    · rcases hp.dvd_mul.1 h with h | h
      · rcases hp.dvd_mul.1 h with h | h
        · rcases hp.dvd_mul.1 h with h | h
          · exact Or.inl (e 2 Nat.prime_two (hp.dvd_of_dvd_pow h))
          · exact Or.inr (Or.inl (e 3 Nat.prime_three (hp.dvd_of_dvd_pow h)))
        · exact Or.inr (Or.inr (Or.inl (e 5 Nat.prime_five (hp.dvd_of_dvd_pow h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (e 7 (by norm_num) h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (e 11 (by norm_num) h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (e 19 (by norm_num) h)))))

theorem nativeRow_HN :
    Nat.card (hopfMultiplier (NativeSporadic.Carrier .HN)) = sporadicMultiplierOrder .HN := by
  have hfs := CFSG.Sporadic.HN.fam_hn_simplicity
  have : Finite (NativeSporadic.Carrier .HN) := hfs.1
  have hs : IsSimpleGroup (NativeSporadic.Carrier .HN) := hfs.2.2
  have hN : Nat.card (NativeSporadic.Carrier .HN) = 273030912000000 := CFSG.Sporadic.HN.card_HN
  have : Group.IsPerfect (NativeSporadic.Carrier .HN) :=
    isPerfect_of_isSimpleGroup_of_not_prime hs (by rw [hN]; norm_num)
  refine (card_hopfMultiplier_eq_one_of_kernelTrivialAt fun p hp _ => ?_).trans (by decide)
  by_cases h2 : p = 2
  · subst h2
    refine kernelTrivialAt_two_of_noTwoCover hs ?_
    intro K _ _ hK hZ ⟨e⟩
    exact CFSG.Sporadic.Recognition.HNMultiplier.center_eq_bot_of_certificate hK.1 hZ e
  by_cases h3 : p = 3
  · subst h3
    exact kernelTrivialAt_carrier_of_sporadicKernelTrivial
      CFSG.RankThree.PartOne.MultRes.sporadicKernelTrivial_hn_three
  by_cases h5 : p = 5
  · subst h5
    exact kernelTrivialAt_carrier_of_sporadicKernelTrivial
      CFSG.RankThree.PartOne.MultRes.sporadicKernelTrivial_hn_five
  intro E _ _ _ π hπ hC hpg
  refine CFSG.SectionRank.ker_eq_bot_of_sylow_kernel_eq_bot π hπ hC
    (odd_card_of_isPGroup hp h2 hpg) ?_
  intro r hr hr2 hsq _ Cp
  rw [hN] at hsq
  have hrN : r ∣ 273030912000000 := (dvd_pow_self r two_ne_zero).trans hsq
  have hr35 : r = 3 ∨ r = 5 := by
    rcases prime_dvd_card_HN hr hrN with h | h | h | h | h | h
    · exact absurd h hr2
    · exact Or.inl h
    · exact Or.inr h
    all_goals (subst h; norm_num at hsq)
  exact sylow_eq_bot_of_ne hp (by rcases hr35 with h | h <;> omega) hpg Cp

end Rows

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
