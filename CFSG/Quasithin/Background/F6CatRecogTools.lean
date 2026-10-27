module

public import CFSG.Walter.Cited.PSL2Small
public import CFSG.Quasithin.Background.KnownMultL2
import CFSG.Adapters.StatedPSLTwoNine
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.Quasithin

namespace F6

theorem exists_sylow_quotient_mulEquiv {L : Type*} [Group L] [Finite L] (Z : Subgroup L)
    [Z.Normal] (hZ : Odd (Nat.card Z)) (P : Sylow 2 L) :
    ∃ Q : Sylow 2 (L ⧸ Z), Nonempty (↥(P : Subgroup L) ≃* ↥(Q : Subgroup (L ⧸ Z))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj : Function.Injective ((QuotientGroup.mk' Z).comp (P : Subgroup L).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    rw [Subgroup.mem_bot]
    obtain ⟨k, hk⟩ := P.isPGroup' x
    have h1 : orderOf (x : L) ∣ 2 ^ k :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
    have h2 : orderOf (x : L) ∣ Nat.card Z := Subgroup.orderOf_dvd_natCard Z hx
    have hcop : Nat.Coprime (2 ^ k) (Nat.card Z) :=
      Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hZ)
    exact Subtype.ext (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2))
  refine ⟨P.mapSurjective (QuotientGroup.mk'_surjective Z), ⟨?_⟩⟩
  refine (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr ?_)
  rw [Sylow.coe_mapSurjective, MonoidHom.range_comp, Subgroup.range_subtype]

theorem isPerfect_of_isSimpleGroup {G : Type*} [Group G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) : Group.IsPerfect G := by
  rw [Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer] at h
    exact hab (Subgroup.mem_centralizer_iff.mp (h (Subgroup.mem_top b)) a (Subgroup.mem_top a))
  · exact h

theorem not_isCyclic_sylow_two {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (Q : Sylow 2 G) :
    ¬ IsCyclic (Q : Subgroup G) ∧ 4 ∣ Nat.card (Q : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect G := isPerfect_of_isSimpleGroup hnonab
  have hns : ¬ Group.IsSolvable G := Group.IsPerfect.not_isSolvable G
  have hcyc : ¬ IsCyclic (Q : Subgroup G) := by
    intro hc
    obtain ⟨N, hN, hNQ⟩ :=
      exists_normal_isComplement'_of_isCyclic_sylow (fun q hq _ => hq.two_le) Q hc
    have hcard := hNQ.card_mul_card
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hN' | hN'
    · rw [hN', Subgroup.card_bot, one_mul] at hcard
      have hQ : (Q : Subgroup G) = ⊤ := Subgroup.eq_top_of_card_eq _ hcard
      obtain ⟨a, b, hab⟩ := hnonab
      have : IsCyclic G := isCyclic_of_surjective
        ((Subgroup.topEquiv).toMonoidHom.comp (MulEquiv.subgroupCongr hQ).toMonoidHom)
        (Subgroup.topEquiv.surjective.comp (MulEquiv.subgroupCongr hQ).surjective)
      exact hab (IsCyclic.isMulCommutative.is_comm.comm a b)
    · rw [hN', Subgroup.card_top] at hcard
      have hQ1 : Nat.card (Q : Subgroup G) = 1 := by
        have hpos : 0 < Nat.card G := Nat.card_pos
        nlinarith [Nat.card_pos (α := (Q : Subgroup G))]
      have hodd : Odd (Nat.card G) := by
        rw [Nat.odd_iff]
        by_contra h2
        have h2' : 2 ∣ Nat.card G := Nat.dvd_of_mod_eq_zero (by omega)
        have := Sylow.pow_dvd_card_of_pow_dvd_card (P := Q) (n := 1) (by simpa using h2')
        rw [hQ1] at this
        exact absurd (Nat.le_of_dvd (by norm_num) this) (by norm_num)
      exact hns (CFSG.FeitThompson.isSolvable_of_odd_natCard G hodd)
  refine ⟨hcyc, ?_⟩
  obtain ⟨k, hk⟩ := Q.isPGroup'.exists_card_eq
  rw [hk]
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · exfalso
    apply hcyc
    interval_cases k
    · have : Subsingleton (Q : Subgroup G) := (Nat.card_eq_one_iff_unique.mp (by simpa using hk)).1
      exact isCyclic_of_subsingleton
    · exact isCyclic_of_prime_card (p := 2) (by simpa using hk)
  · exact Dvd.dvd.trans (by norm_num) (pow_dvd_pow 2 hk2)

theorem isKleinFour_of_card_four {G : Type*} [Group G] [Finite G] (h4 : Nat.card G = 4)
    (hc : ¬ IsCyclic G) : IsKleinFour G := by
  have : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp (by rw [h4]; norm_num)
  refine ⟨h4, (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr fun g hg => ?_⟩
  have hdvd : orderOf g ∣ 2 ^ 2 := by
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← h4]
    exact orderOf_dvd_natCard g
  obtain ⟨i, hi, hig⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  interval_cases i
  · exact absurd (orderOf_eq_one_iff.mp (by simpa using hig)) hg
  · simpa using hig
  · exact absurd (isCyclic_of_orderOf_eq_card g (by rw [hig, h4]; norm_num)) hc

theorem sq_sub_one_div_two {m : ℕ} : ((2 * m + 1) ^ 2 - 1) / 2 = 2 * (m * (m + 1)) := by
  have : (2 * m + 1) ^ 2 - 1 = 2 * (2 * (m * (m + 1))) := by
    have h : (2 * m + 1) ^ 2 = 2 * (2 * (m * (m + 1))) + 1 := by ring
    omega
  rw [this, Nat.mul_div_cancel_left _ (by norm_num)]

theorem eight_dvd_card_psl_two {q : ℕ} (hq : q % 8 = 1 ∨ q % 8 = 7) :
    8 ∣ q * ((q ^ 2 - 1) / 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, q = 2 * m + 1 := ⟨q / 2, by omega⟩
  rw [sq_sub_one_div_two]
  have h4 : 4 ∣ m * (m + 1) := by
    rcases hq with h | h
    · exact Dvd.dvd.mul_right (by omega : 4 ∣ m) _
    · exact Dvd.dvd.mul_left (by omega : 4 ∣ m + 1) _
  exact Dvd.dvd.mul_left (by obtain ⟨c, hc⟩ := h4; exact ⟨c, by rw [hc]; ring⟩) _

theorem sixteen_dvd_card_psl_two {q : ℕ} (hq : q % 16 = 1 ∨ q % 16 = 15) :
    16 ∣ q * ((q ^ 2 - 1) / 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, q = 2 * m + 1 := ⟨q / 2, by omega⟩
  rw [sq_sub_one_div_two]
  have h8 : 8 ∣ m * (m + 1) := by
    rcases hq with h | h
    · exact Dvd.dvd.mul_right (by omega : 8 ∣ m) _
    · exact Dvd.dvd.mul_left (by omega : 8 ∣ m + 1) _
  exact Dvd.dvd.mul_left (by obtain ⟨c, hc⟩ := h8; exact ⟨c, by rw [hc]; ring⟩) _

theorem not_eight_dvd_card_psl_two {q : ℕ} (hq : q % 8 = 3 ∨ q % 8 = 5) :
    ¬ 8 ∣ q * ((q ^ 2 - 1) / 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, q = 2 * m + 1 := ⟨q / 2, by omega⟩
  rw [sq_sub_one_div_two]
  obtain ⟨u, hu, hmu⟩ : ∃ u, Odd u ∧ m * (m + 1) = 2 * u := by
    rcases hq with h | h
    · obtain ⟨k, rfl⟩ : ∃ k, m = 4 * k + 1 := ⟨m / 4, by omega⟩
      exact ⟨(4 * k + 1) * (2 * k + 1), Nat.odd_mul.mpr ⟨⟨2 * k, by ring⟩, ⟨k, rfl⟩⟩, by ring⟩
    · obtain ⟨k, rfl⟩ : ∃ k, m = 4 * k + 2 := ⟨m / 4, by omega⟩
      exact ⟨(2 * k + 1) * (4 * k + 3), Nat.odd_mul.mpr ⟨⟨k, rfl⟩, ⟨2 * k + 1, by ring⟩⟩, by ring⟩
  rw [hmu]
  have hw : Odd ((2 * m + 1) * u) := Nat.odd_mul.mpr ⟨⟨m, rfl⟩, hu⟩
  obtain ⟨w, hw'⟩ := hw
  rw [show (2 * m + 1) * (2 * (2 * u)) = 4 * ((2 * m + 1) * u) by ring, hw']
  omega

theorem odd_sq_mod_eight {p : ℕ} (hp : Odd p) : p ^ 2 % 8 = 1 := by
  obtain ⟨m, rfl⟩ := hp
  obtain ⟨t, ht⟩ := Nat.even_mul_succ_self m
  have : (2 * m + 1) ^ 2 = 8 * t + 1 := by
    have h : (2 * m + 1) ^ 2 = 4 * (m * (m + 1)) + 1 := by ring
    rw [h, ht]
    ring
  omega

section PRank

open CFSG.Assembly.LowTwoRank

theorem le_pRank_statedProj_sl_two {K : Type} [Field K] [Finite K] {p f : ℕ} [hp : Fact p.Prime]
    (hK : Nat.card K = p ^ f) :
    f ≤ CFSG.Open.pRank p (⊤ : Subgroup (StatedProj (StatedSL 2 K))) := by
  have : Fintype K := Fintype.ofFinite K
  have : CharP K p := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  let ε := projectiveSpecialLinearGroupEquivStatedProj 2 K
  have : Finite (StatedProj (StatedSL 2 K)) := Finite.of_equiv _ ε.toEquiv
  refine CFSG.SectionRank.le_pRank hp.out.one_lt le_top
    (CFSG.SectionRank.isElemAbelian_map CFSG.SectionRank.OddCover.isElemAbelian_range_pslU
      ε.toMonoidHom) ?_
  rw [← Nat.card_congr ((CFSG.SectionRank.OddCover.pslU (K := K)).range.equivMapOfInjective
    ε.toMonoidHom ε.injective).toEquiv, CFSG.SectionRank.OddCover.card_range_pslU, hK]

theorem le_two_of_isStronglyQuasithin {S : Type} [Group S] [Finite S]
    (hS : CFSG.IsStronglyQuasithin S) {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (e : S ≃* StatedProj (StatedSL 2 K)) : f ≤ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (StatedProj (StatedSL 2 K)) := Finite.of_equiv _ e.toEquiv
  have h1 := le_pRank_statedProj_sl_two hK
  have h2 := (CFSG.SectionRank.isStronglyQuasithin_iff.mp
    (CFSG.SectionRank.isStronglyQuasithin_of_mulEquiv e.symm hS)) p hp hp2
  omega

end PRank

section Center

open CFSG.Assembly.LowTwoRank

theorem center_of_quotient_psl_two {L : Type} [Group L] [Finite L] [Group.IsPerfect L]
    (h3 : IsPGroup 3 (Subgroup.center L)) {K : Type} [Field K] [Finite K] {p f : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f)
    (e : L ⧸ Subgroup.center L ≃* StatedProj (StatedSL 2 K)) :
    (p ^ f ≠ 9 → Subgroup.center L = ⊥) ∧ (p ^ f = 9 → Nat.card (Subgroup.center L) ≤ 3) := by
  obtain ⟨φ, hφ, hker⟩ := exists_surjective_ker_eq_of_mulEquiv_stated_psl (Subgroup.center L) K e
  have hodd : Odd (Nat.card φ.ker) := by
    rw [hker]
    obtain ⟨k, hk⟩ := h3.exists_card_eq
    rw [hk]
    exact Odd.pow (by decide)
  obtain ⟨h1, h2⟩ := CFSG.SectionRank.OddCover.psl_two_perfect_odd_cover_kernel hp2 hK φ hφ
    hker.le hodd
  refine ⟨fun h9 => hker ▸ h1 h9, fun h9 => ?_⟩
  have := (h2 h9).2
  rwa [hker] at this

theorem orderOf_dvd_four_hundred_twenty (σ : Equiv.Perm (Fin 7)) : orderOf σ ∣ 420 := by
  rw [← Equiv.Perm.lcm_cycleType]
  refine Multiset.lcm_dvd.mpr fun n hn => ?_
  have h1 := Equiv.Perm.le_card_support_of_mem_cycleType hn
  have h2 := Equiv.Perm.two_le_of_mem_cycleType hn
  have h3 : σ.support.card ≤ 7 := by
    simpa using Finset.card_le_univ σ.support
  have h7 : n ≤ 7 := h1.trans h3
  interval_cases n <;> norm_num

theorem card_alternating_seven : Nat.card ↥(alternatingGroup (Fin 7)) = 2520 := by
  rw [nat_card_alternatingGroup]
  simp [Nat.card_eq_fintype_card, Nat.factorial]

theorem sylow_three_alternating_seven (Q : Sylow 3 ↥(alternatingGroup (Fin 7))) :
    CFSG.Open.IsElemAbelian 3 (Q : Subgroup ↥(alternatingGroup (Fin 7))) ∧
      Nat.card (Q : Subgroup ↥(alternatingGroup (Fin 7))) = 3 ^ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card ↥(alternatingGroup (Fin 7)) = 3 ^ 2 * 280 := by
    rw [nat_card_alternatingGroup]
    simp [Nat.card_eq_fintype_card, Nat.factorial]
  have hQ : Nat.card (Q : Subgroup ↥(alternatingGroup (Fin 7))) = 3 ^ 2 := by
    rw [Sylow.card_eq_multiplicity, hcard, Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]
  refine ⟨⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq hQ, fun x hx => ?_⟩, hQ⟩
  · have h9 : orderOf x ∣ 9 := by
      have := Subgroup.orderOf_dvd_natCard _ hx
      rwa [hQ] at this
    have h420 : orderOf x ∣ 420 := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_dvd_four_hundred_twenty _
    have h3 : orderOf x ∣ 3 := by
      have := Nat.dvd_gcd h9 h420
      norm_num at this
      exact this
    exact orderOf_dvd_iff_pow_eq_one.mp h3

theorem card_center_le_three_of_alternating_seven {L : Type} [Group L] [Finite L]
    [Group.IsPerfect L] (h3 : IsPGroup 3 (Subgroup.center L))
    (e : L ⧸ Subgroup.center L ≃* ↥(alternatingGroup (Fin 7))) :
    Nat.card (Subgroup.center L) ≤ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let φ : L →* ↥(alternatingGroup (Fin 7)) := e.toMonoidHom.comp (QuotientGroup.mk' _)
  have hφ : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = Subgroup.center L := by
    ext x
    simp [φ]
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow 3 ↥(alternatingGroup (Fin 7))))
  obtain ⟨hQe, hQc⟩ := sylow_three_alternating_seven Q
  obtain ⟨C⟩ := (inferInstance : Nonempty (Sylow 3 φ.ker))
  obtain ⟨-, hC⟩ := CFSG.ShultStronglyClosedTI.central_cover_elementary_rank_two_sylow_kernel_bound
    φ hφ hker.le C Q hQe hQc
  have hpg : IsPGroup 3 φ.ker := by
    rw [hker]
    exact h3
  have htop : (C : Subgroup φ.ker) = ⊤ := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hpg
    rw [← Subgroup.card_eq_iff_eq_top, Sylow.card_eq_multiplicity, hk,
      Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same]
  rw [htop, Subgroup.card_top, hker] at hC
  exact hC

end Center

section Models

open CFSG.GorensteinWalter CFSG.Assembly.LowTwoRank

open CFSG.LocalAnalysis.ComponentInitial in
theorem nonempty_mulEquiv_alternating_six {S : Type} [Group S] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 9) (e : S ≃* StatedProj (StatedSL 2 K)) :
    Nonempty (S ≃* ↥(alternatingGroup (Fin 6))) :=
  CFSG.Open.StatedAPI.nonempty_mulEquiv_alternating_six_of_statedProj hK e

noncomputable def mulAutPSL2EquivPGL2 (K : Type) [Field K] [Finite K] {p : ℕ} [hp : Fact p.Prime]
    (hp5 : 5 ≤ p) (hK : Nat.card K = p) : MulAut (PSL2 K) ≃* PGL2 K :=
  have hodd : IsOddPrimePower (Nat.card K) :=
    ⟨p, 1, hp.out, hp.out.odd_of_ne_two (by omega), le_rfl, by rw [hK, pow_one]⟩
  have h3 : 3 < Nat.card K := by omega
  have : Subsingleton (K ≃+* K) := CFSG.Walter.Suzuki.subsingleton_ringEquiv_of_card_prime K hK
  (MulEquiv.ofBijective (pGammaL2ToMulAutPSL2 K hodd h3)
      ⟨pGammaL2ToMulAutPSL2_injective K hodd h3,
        pGammaL2ToMulAutPSL2_surjective K (p := p) (f := 1) (by rw [hK, pow_one]) hodd
          h3⟩).symm.trans
    (MulEquiv.ofBijective (SemidirectProduct.inl : PGL2 K →* PGammaL2 K)
      ⟨SemidirectProduct.inl_injective, fun x =>
        ⟨x.left, SemidirectProduct.ext rfl (Subsingleton.elim _ _)⟩⟩).symm

end Models

end F6

end CFSG.Quasithin
