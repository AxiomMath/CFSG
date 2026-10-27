module

public import CFSG.Quasithin.Vol2.Ch10SecC9S4a
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.C2Nine

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_oddCoreIn_of_odd' {J K : Subgroup G} (hKJ : K ≤ J)
    (hnorm : J ≤ Subgroup.normalizer (K : Set G)) (hodd : Odd (Nat.card K)) : K ≤ oddCoreIn J := by
  have hnormal : (K.subgroupOf J).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKJ).mpr hnorm
  have hodd' : Odd (Nat.card (K.subgroupOf J)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKJ).toEquiv]
  have hle : K.subgroupOf J ≤ fusionOddCore J := le_sSup ⟨hnormal, hodd'⟩
  intro k hk
  exact ⟨⟨k, hKJ hk⟩, hle hk, rfl⟩

theorem isPGroup_of_isNilpotent {J N : Subgroup G} (hNJ : N ≤ J)
    (hJN : J ≤ Subgroup.normalizer (N : Set G)) (hnil : Group.IsNilpotent N)
    (hO : oddCoreIn J = ⊥) : IsPGroup 2 N := by
  have hON : oddCoreIn N = ⊥ := by
    refine le_bot_iff.mp (hO ▸ le_oddCoreIn_of_odd' ((oddCoreIn_le_self N).trans hNJ)
      (hJN.trans (normalizer_le_normalizer_oddCoreIn' N)) (C2Nine.odd_card_oddCoreIn N))
  have hodd : ∀ p : ℕ, p.Prime → p ∣ Nat.card N → p = 2 := by
    intro p hp hpd
    by_contra hp2
    have : Fact p.Prime := ⟨hp⟩
    obtain P : Sylow p N := Classical.arbitrary _
    have hPn : (P : Subgroup N).Normal := inferInstance
    have hPne : (P : Subgroup N) ≠ ⊥ := P.ne_bot_of_dvd_card hpd
    have hPodd : Odd (Nat.card (P : Subgroup N)) := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp P.isPGroup'
      rw [hk]
      exact (hp.eq_two_or_odd'.resolve_left hp2).pow
    set P' : Subgroup G := (P : Subgroup N).map N.subtype with hP'
    have hP'N : P' ≤ N := Subgroup.map_subtype_le _
    have hNP' : N ≤ Subgroup.normalizer (P' : Set G) := by
      intro n hn
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨⟨n, hn⟩ * y * ⟨n, hn⟩⁻¹, hPn.conj_mem y hy ⟨n, hn⟩, rfl⟩
      · rintro ⟨y, hy, hyx⟩
        refine ⟨⟨n, hn⟩⁻¹ * y * ⟨n, hn⟩, ?_, ?_⟩
        · have := hPn.conj_mem y hy ⟨n, hn⟩⁻¹
          rwa [inv_inv] at this
        · simp only [Subgroup.subtype_apply, Subgroup.coe_mul, Subgroup.coe_inv] at hyx ⊢
          rw [hyx]
          group
    have hP'odd : Odd (Nat.card P') := by
      rwa [hP', Subgroup.card_map_of_injective N.subtype_injective]
    have hle := le_oddCoreIn_of_odd' hP'N hNP' hP'odd
    rw [hON, le_bot_iff, hP', Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective] at hle
    exact hPne hle
  have hcard : Nat.card N = 2 ^ (Nat.card N).primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun hd hdv => hodd _ hd hdv
  exact IsPGroup.of_card hcard

omit [Finite G] in
theorem not_isSolvable_of_isQuasisimple' {K : Subgroup G} (hK : CFSG.Open.IsQuasisimple ↥K) :
    ¬ Group.IsSolvable ↥K := by
  intro hs
  obtain ⟨hperf, hsimp⟩ := hK
  have hder : ∀ n, derivedSeries ↥K n = ⊤ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [derivedSeries_succ, ih]; exact hperf
  obtain ⟨n, hn⟩ := hs.solvable
  have htop : (⊤ : Subgroup ↥K) = ⊥ := (hder n).symm.trans hn
  have : Subsingleton ↥K := by
    refine ⟨fun a b => ?_⟩
    have ha : a ∈ (⊥ : Subgroup ↥K) := htop ▸ Subgroup.mem_top a
    have hb : b ∈ (⊥ : Subgroup ↥K) := htop ▸ Subgroup.mem_top b
    rw [Subgroup.mem_bot] at ha hb
    rw [ha, hb]
  have hnt := hsimp.toNontrivial
  obtain ⟨x, y, hxy⟩ := hnt.exists_pair_ne
  obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
  exact hxy (by rw [Subsingleton.elim x' y'])

theorem charTwo_of_not_isQuasisimple {X J : Subgroup G} (hJ : J ∈ cComp X)
    (hq : ¬ CFSG.Open.IsQuasisimple ↥J) (hO : oddCoreIn J = ⊥) : CharTwo J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  show J ⊓ Subgroup.centralizer (pCoreOf 2 J : Set G) ≤ pCoreOf 2 J
  rw [← quasithinGenFitting_eq_pCoreOf_iff J 2]
  apply le_antisymm
  · refine sup_le (sSup_le fun N hN => ?_) (sSup_le fun K hK => ?_)
    · obtain ⟨hNJ, hNn, hnil⟩ := hN
      have hJN : J ≤ Subgroup.normalizer (N : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hNJ).mp hNn
      exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (r := 2) hNJ hJN
        (isPGroup_of_isNilpotent hNJ hJN hnil hO)
    · exfalso
      obtain ⟨hKJ, hKsub, hKq⟩ := hK
      by_cases hKJe : K = J
      · subst hKJe
        exact hq hKq
      · have hle := le_solvRad_of_subnormal_lt hJ hKsub (lt_of_le_of_ne hKJ hKJe)
        have := solvRad_isSolvable J
        have hsolv : Group.IsSolvable ↥K :=
          Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
        exact not_isSolvable_of_isQuasisimple' hKq hsolv
  · refine le_sup_of_le_left (le_sSup ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 J, ?_, ?_⟩)
    · exact (Subgroup.normal_subgroupOf_iff_le_normalizer
        (CFSG.LieType.BorelTits.pCoreOf_le 2 J)).mpr
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 J)
    · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 J).isNilpotent

omit [Finite G] in
theorem exists_pow_eq_mul {J : Subgroup G} {j r : G} (hj : j ∈ J)
    (hr : r ∈ Subgroup.normalizer (J : Set G)) (n : ℕ) : ∃ j' ∈ J, (j * r) ^ n = j' * r ^ n := by
  induction n with
  | zero => exact ⟨1, J.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨j', hj', he⟩ := ih
    have hrn : r ^ n ∈ Subgroup.normalizer (J : Set G) := Subgroup.pow_mem _ hr n
    have h1 : r ^ n * j * (r ^ n)⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp hrn j).mp hj
    refine ⟨j' * (r ^ n * j * (r ^ n)⁻¹), J.mul_mem hj' h1, ?_⟩
    rw [pow_succ, he, pow_succ]
    group

omit [Finite G] in
theorem mem_normalizer_inf' {A B : Subgroup G} {g : G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro x
  exact ⟨fun hx => ⟨(hA x).mp hx.1, (hB x).mp hx.2⟩, fun hx => ⟨(hA x).mpr hx.1, (hB x).mpr hx.2⟩⟩

omit [Finite G] in
theorem mem_normalizer_centralizer' {Q : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (Q : Set G) : Set G) :=
  SecA.le_normalizer_centralizer (X := Subgroup.zpowers g) (V := Q) (Subgroup.zpowers_le.mpr hg)
    (Subgroup.mem_zpowers g)

theorem charTwo_sup {J R : Subgroup G} (hJ : CharTwo J) (hR : IsPGroup 2 R)
    (hRJ : R ≤ Subgroup.normalizer (J : Set G)) : CharTwo (J ⊔ R) :=
  CFSG.QuasithinUnique.CharTwo.sup_of_le_normalizer hJ hR hRJ

end CFSG.Quasithin.Vol2.Ch10.SecC
