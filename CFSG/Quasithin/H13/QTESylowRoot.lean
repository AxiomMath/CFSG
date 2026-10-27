module

public import CFSG.Quasithin.H13.QTESylowStmt
public import CFSG.Quasithin.H13.QTESylowPlane
public import CFSG.Quasithin.H13.QTESylowHS
public import CFSG.Quasithin.H13.QTESylowHeRuStmt
public import CFSG.Quasithin.H13.NQCatUnitary
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Candidates
public import CFSG.RankThree.PartOne.KS.Arith
public import CFSG.RankThree.PartOne.S11c.J4Plane
public import CFSG.Sporadic.Schreier.M11
public import CFSG.Sporadic.Schreier.M12
public import CFSG.Sporadic.Schreier.M22
public import CFSG.Sporadic.Schreier.J1Outer
import CFSG.Adapters.StatedClassicalOrders
import CFSG.Adapters.StatedClassicalUnitaryOrders
public import CFSG.Sporadic.Schreier.M23Base
public import CFSG.Sporadic.Schreier.M24Base

public section

namespace CFSG.Quasithin.H13.QTESylow

open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped Pointwise

theorem sq_dvd_card_of_not_isCyclic {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {P : Subgroup G} (hP : IsPGroup p P) (hnc : ¬ IsCyclic P) : p ^ 2 ∣ Nat.card P := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  rw [hk]
  apply pow_dvd_pow
  by_contra hlt
  have hk1 : k = 0 ∨ k = 1 := by omega
  rcases hk1 with rfl | rfl
  · rw [pow_zero] at hk
    have : Subsingleton P := (Nat.card_eq_one_iff_unique.mp hk).1
    exact hnc isCyclic_of_subsingleton
  · rw [pow_one] at hk
    exact hnc (isCyclic_of_prime_card hk)

theorem ne_bot_of_not_isCyclic {G : Type*} [Group G] {P : Subgroup G} (hnc : ¬ IsCyclic P) :
    P ≠ ⊥ := by
  rintro rfl
  exact hnc Bot.isCyclic

theorem isElemAbelian_of_card_sq {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) {P : Subgroup G}
    (hc : Nat.card P = p ^ 2) (hnc : ¬ IsCyclic P) : CFSG.Open.IsElemAbelian p P := by
  have : Fact p.Prime := ⟨hp⟩
  have hfin : Finite P := Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ hp.ne_zero)
  refine ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq hc, fun x hx => ?_⟩
  have hdvd : orderOf (⟨x, hx⟩ : P) ∣ p ^ 2 := hc ▸ orderOf_dvd_natCard _
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hk1 : k ≤ 1 := by
    by_contra hlt
    have hk2 : k = 2 := by omega
    rw [hk2, ← hc] at hk'
    exact hnc (isCyclic_of_orderOf_eq_card _ hk')
  have h1 : orderOf (⟨x, hx⟩ : P) ∣ p := by
    rw [hk']
    have := pow_dvd_pow p hk1
    rwa [pow_one] at this
  have h2 := orderOf_dvd_iff_pow_eq_one.1 h1
  simpa using congrArg Subtype.val h2

theorem false_of_card_eq {S : Type} [Group S] [Finite S] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {P : Subgroup S} (hP : IsPGroup p P) (hnc : ¬ IsCyclic P) {a b m B : ℕ}
    (hcard : Nat.card S = 2 ^ a * 3 ^ b * m) (hmB : m < (B + 1) ^ 2)
    (hm : ∀ q : ℕ, q ≤ B → 2 ≤ q → ¬ q ^ 2 ∣ m) (hm0 : 0 < m) : False := by
  have h := (sq_dvd_card_of_not_isCyclic hp hP hnc).trans (Subgroup.card_subgroup_dvd_card P)
  rw [hcard] at h
  exact CFSG.RankThree.PartOne.not_sq_dvd_two_pow_three_pow_mul hp (by omega) hmB hm hm0 h

theorem odd_and_not_three_dvd {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) {P : Subgroup G} (hP : IsPGroup p P) :
    Odd (Nat.card P) ∧ ¬ 3 ∣ Nat.card P := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  rw [hk]
  refine ⟨(hp.odd_of_ne_two (by omega)).pow, fun h3 => ?_⟩
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 (Nat.prime_three.dvd_of_dvd_pow h3)
  omega

theorem card_of_statedPSL {X : Type} [Group X] {n p f : ℕ} (hn : 2 ≤ n)
    (h : StatedClassicalModel X .PSL n p f) :
    Nat.card X = ((p ^ f) ^ (n * (n - 1) / 2) * ∏ i ∈ Finset.Icc 2 n, ((p ^ f) ^ i - 1)) /
      Nat.gcd n (p ^ f - 1) :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl (by omega) h

theorem card_of_statedPSU_three_three {X : Type} [Group X]
    (h : StatedClassicalModel X .PSU 3 3 1) : Nat.card X = 6048 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_three h

theorem isCyclic_of_statedPSL_two_even {S : Type} [Group S] {f : ℕ}
    (hS : StatedClassicalModel S .PSL 2 2 f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P : Subgroup S} (hP : IsPGroup p P) : IsCyclic P := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, K, _, _, hKcard, ⟨e⟩⟩ := hS
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 :=
    charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hKcard])
  refine isCyclic_of_mulEquiv_of_pGroups_cyclic
    ((e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm).trans
      (pslEquivSlOfCharTwo K)) hP fun Q hQ => ?_
  exact CFSG.LinearAlgebra.even_SL2_odd_prime_subgroups_cyclic hp2 Q hQ

theorem rank_le_two_of_sqt {S : Type} [Group S] [Finite S] (hSQT : CFSG.IsStronglyQuasithin S) :
    ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q (⊤ : Subgroup S) ≤ 2 := by
  intro q hq hq2
  have := hSQT q hq hq2
  rwa [CFSG.SectionRank.pRank_eq_open_pRank_top] at this

theorem classical_odd_case (S : Type) [Group S] [Finite S] [IsSimpleGroup S]
    (hSQT : CFSG.IsStronglyQuasithin S) {t : StatedLieTag} {n ℓ f : ℕ} (hℓ2 : ℓ ≠ 2)
    (hm : StatedClassicalModel S t n ℓ f) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (T : Sylow 2 S)
    (P : Subgroup S) (hP : IsPGroup p P) (hnc : ¬ IsCyclic P)
    (hPT : (P : Set S) * (T : Set S) = (T : Set S) * (P : Set S)) :
    ∃ ℓ' : ℕ, ℓ'.Prime ∧ 5 ≤ ℓ' ∧
      (StatedClassicalModel S .PSL 3 ℓ' 1 ∨ StatedClassicalModel S .PSU 3 ℓ' 1) := by
  have : Fact p.Prime := ⟨hp⟩
  have hℓ : ℓ.Prime := hm.1.1
  have hℓ5 : ℓ ≠ 3 → 5 ≤ ℓ := fun h3 => by
    have h2 := hℓ.two_le
    by_contra hlt
    have : ℓ = 4 := by omega
    subst this
    norm_num at hℓ
  rcases CFSG.SectionRank.sqt_odd_classical_restriction (rank_le_two_of_sqt hSQT) hℓ2 hm with
    ⟨rfl, rfl, hf12⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  ·
    exfalso
    have : Fact ℓ.Prime := ⟨hℓ⟩
    obtain ⟨-, K, _, _, hKcard, ⟨e⟩⟩ := id hm
    obtain ⟨-, -, hcardS, -, -, -, hcyc⟩ :=
      CFSG.SectionRank.OddCover.odd_psl_two_sylow_data (K := K) hℓ2 hKcard
    have hcardS' : Nat.card S = ℓ ^ f * (((ℓ ^ f) ^ 2 - 1) / 2) := by
      rw [Nat.card_congr e.toEquiv, hcardS]
    by_cases hpℓ : p = ℓ
    · subst hpℓ
      have hsq := (sq_dvd_card_of_not_isCyclic hp hP hnc).trans (Subgroup.card_subgroup_dvd_card P)
      have hodd2 : ∀ k : ℕ, 1 ≤ k → ¬ p ∣ ((p ^ k) ^ 2 - 1) / 2 := by
        intro k hk h
        have h2 : p ∣ (p ^ k) ^ 2 - 1 := h.trans (Nat.div_dvd_of_dvd (by
          have : Odd ((p ^ k) ^ 2) := ((hp.odd_of_ne_two (by omega)).pow).pow
          exact (Nat.Odd.sub_odd this odd_one).two_dvd))
        have h3 : p ∣ (p ^ k) ^ 2 := dvd_pow (dvd_pow_self p (by omega)) (by norm_num)
        have h4 : p ∣ 1 := by
          have := Nat.dvd_sub h3 h2
          rwa [Nat.sub_sub_self (Nat.one_le_pow _ _ (pow_pos hp.pos k))] at this
        exact hp.one_lt.ne' (Nat.dvd_one.1 h4)
      rcases hf12 with rfl | rfl
      ·
        rw [hcardS', pow_one] at hsq
        have h1 : p * p ∣ p * ((p ^ 2 - 1) / 2) := by
          rw [← sq]
          exact hsq
        exact hodd2 1 le_rfl (by rw [pow_one]; exact Nat.dvd_of_mul_dvd_mul_left hp.pos h1)
      ·
        have hPcard : Nat.card P = p ^ 2 := by
          obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
          have hdvd : p ^ k ∣ p ^ 2 * (((p ^ 2) ^ 2 - 1) / 2) := by
            rw [← hk, ← hcardS']
            exact Subgroup.card_subgroup_dvd_card P
          have hcop : Nat.Coprime (p ^ k) (((p ^ 2) ^ 2 - 1) / 2) :=
            Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 (hodd2 2 (by norm_num)))
          have hk2 : k ≤ 2 := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1
            (hcop.dvd_of_dvd_mul_right hdvd)
          have h2k : 2 ≤ k := by
            have := sq_dvd_card_of_not_isCyclic hp hP hnc
            rw [hk] at this
            exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 this
          rw [hk, show k = 2 by omega]
        exact projective_linear_two_odd_plane_sylow_product_exclusion S hSQT hm hp hp5 T P
          (isElemAbelian_of_card_sq hp hPcard hnc) hPcard hPT
    ·
      apply hnc
      have hpcyc : ∀ Q : Subgroup (StatedProj (StatedSL 2 K)), IsPGroup p Q → IsCyclic Q := by
        intro Q hQ
        obtain ⟨R, hR⟩ := hQ.exists_le_sylow
        have := hcyc p hp (by omega) hpℓ R
        exact Subgroup.isCyclic_of_le hR
      exact isCyclic_of_mulEquiv_of_pGroups_cyclic e hP hpcyc
  ·
    by_cases h3 : ℓ = 3
    · subst h3
      exact (false_of_card_eq hp hp5 hP hnc (a := 4) (b := 3) (m := 13) (B := 3)
        (by rw [card_of_statedPSL (by norm_num) hm]; decide) (by norm_num) (by decide)
        (by norm_num)).elim
    · exact ⟨ℓ, hℓ, hℓ5 h3, Or.inl hm⟩
  ·
    by_cases h3 : ℓ = 3
    · subst h3
      exact (false_of_card_eq hp hp5 hP hnc (a := 5) (b := 3) (m := 7) (B := 2)
        (by rw [card_of_statedPSU_three_three hm]; norm_num) (by norm_num) (by decide)
        (by norm_num)).elim
    · exact ⟨ℓ, hℓ, hℓ5 h3, Or.inr hm⟩

theorem classical_even_case (S : Type) [Group S] [Finite S] [IsSimpleGroup S]
    (hnab : ∃ a b : S, a * b ≠ b * a) (hSQT : CFSG.IsStronglyQuasithin S) {t : StatedLieTag}
    {n f : ℕ} (hm : StatedClassicalModel S t n 2 f) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (T : Sylow 2 S) (P : Subgroup S) (hP : IsPGroup p P) (hnc : ¬ IsCyclic P)
    (hPT : (P : Set S) * (T : Set S) = (T : Set S) * (P : Set S)) :
    (∃ f : ℕ, 3 ≤ f ∧ StatedClassicalModel S .PSL 3 2 f) ∨
      (∃ f : ℕ, 2 ≤ f ∧ StatedClassicalModel S .PSp 2 2 f) := by
  rcases CFSG.SectionRank.ClassicalEven.sqt_even_classical_restriction (rank_le_two_of_sqt hSQT)
      hm with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, hf1⟩ | ⟨rfl, hn45, rfl⟩ | ⟨rfl, rfl, hf2⟩ |
      ⟨rfl, rfl, hf2⟩
  ·
    exact (hnc (isCyclic_of_statedPSL_two_even hm hp (by omega) hP)).elim
  ·
    rcases (show f = 1 ∨ f = 2 ∨ 3 ≤ f by omega) with rfl | rfl | hf3
    · exact (false_of_card_eq hp hp5 hP hnc (a := 3) (b := 1) (m := 7) (B := 2)
        (by rw [card_of_statedPSL (by norm_num) hm]; decide) (by norm_num) (by decide)
        (by norm_num)).elim
    · exact (false_of_card_eq hp hp5 hP hnc (a := 6) (b := 2) (m := 35) (B := 5)
        (by rw [card_of_statedPSL (by norm_num) hm]; decide) (by norm_num) (by decide)
        (by norm_num)).elim
    · exact Or.inl ⟨f, hf3, hm⟩
  ·
    rcases hn45 with rfl | rfl
    · exact (false_of_card_eq hp hp5 hP hnc (a := 6) (b := 2) (m := 35) (B := 5)
        (by rw [card_of_statedPSL (by norm_num) hm]; decide) (by norm_num) (by decide)
        (by norm_num)).elim
    · exact (false_of_card_eq hp hp5 hP hnc (a := 10) (b := 2) (m := 1085) (B := 32)
        (by rw [card_of_statedPSL (by norm_num) hm]; decide) (by norm_num) (by decide)
        (by norm_num)).elim
  ·
    have hnab' : ¬ IsMulCommutative S := by
      rintro ⟨hc⟩
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (hc.comm a b)
    obtain ⟨hodd, h3⟩ := odd_and_not_three_dvd hp hp5 hP
    exact (hnc ((CFSG.Quasithin.H13.NQCat.even_unitary_three_three_free_sylow_product_is_cyclic S
      hnab' hf2 hm T).1 P hodd h3 hPT)).elim
  · exact Or.inr ⟨f, hf2, hm⟩

theorem alternating_case (S : Type) [Group S] [Finite S] (hSQT : CFSG.IsStronglyQuasithin S)
    {n : ℕ} (hn : 5 ≤ n) (e : S ≃* alternatingGroup (Fin n)) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (P : Subgroup S) (hP : IsPGroup p P) (hnc : ¬ IsCyclic P) : False := by
  have h8 : n ≤ 8 := by
    by_contra hlt
    have h3 := CFSG.SectionRank.three_le_pRank_alternating (show 9 ≤ n by omega)
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e] at h3
    have h2 := rank_le_two_of_sqt hSQT 3 Nat.prime_three (by norm_num)
    omega
  have hcard : Nat.card S = n.factorial / 2 := by
    have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  interval_cases n
  · exact false_of_card_eq hp hp5 hP hnc (a := 2) (b := 1) (m := 5) (B := 2)
      (by rw [hcard]; decide) (by norm_num) (by decide) (by norm_num)
  · exact false_of_card_eq hp hp5 hP hnc (a := 3) (b := 2) (m := 5) (B := 2)
      (by rw [hcard]; decide) (by norm_num) (by decide) (by norm_num)
  · exact false_of_card_eq hp hp5 hP hnc (a := 3) (b := 2) (m := 35) (B := 5)
      (by rw [hcard]; decide) (by norm_num) (by decide) (by norm_num)
  · exact false_of_card_eq hp hp5 hP hnc (a := 6) (b := 2) (m := 35) (B := 5)
      (by rw [hcard]; decide) (by norm_num) (by decide) (by norm_num)

theorem exceptional_case
    (S : Type) [Group S] [Finite S] (hSQT : CFSG.IsStronglyQuasithin S) (hex : ExceptionalRep S)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (P : Subgroup S) (hP : IsPGroup p P)
    (hnc : ¬ IsCyclic P) :
    ((∃ f : ℕ, 2 ≤ f ∧ ChevalleyExceptionalModel S .G2 2 f) ∨
        ∃ f : ℕ, 1 ≤ f ∧ ChevalleyExceptionalModel S .trialityD4 2 f) ∨
      ((∃ a : ℕ, 1 ≤ a ∧ ReeTitsModel S .twistedF4 2 (2 * a + 1)) ∨
        ReeTitsModel S .Tits 2 1) := by
  rcases CFSG.SectionRank.sqt_exceptional_restriction (rank_le_two_of_sqt hSQT) hex with
    hG2 | hD4 | ⟨f, hodd, hf3, hF4⟩ | hTits | ⟨f, -, -, hSz⟩
  · exact Or.inl (Or.inl hG2)
  · exact Or.inl (Or.inr hD4)
  · obtain ⟨a, rfl⟩ := hodd
    exact Or.inr (Or.inl ⟨a, by omega, hF4⟩)
  · exact Or.inr (Or.inr hTits)
  ·
    exfalso
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨a, ha, ⟨e⟩⟩ :=
      CFSG.LieType.Simplicity.exists_mulEquiv_suzukiMatrixGroup_of_suzukiModel hSz
    apply hnc
    refine isCyclic_of_mulEquiv_of_pGroups_cyclic e hP fun Q hQ => ?_
    obtain ⟨R, hR⟩ := hQ.exists_le_sylow
    have := CFSG.SectionRank.suzuki_sylow_isCyclic a (by omega) (r := p) (by omega) R
    exact Subgroup.isCyclic_of_le hR

theorem sporadic_case
    (hHeRu : StmtHeRuNoncyclicPrimeSylowProduct)
    (S : Type) [Group S] [Finite S] [IsSimpleGroup S] (hSQT : CFSG.IsStronglyQuasithin S)
    (hspor : NativeSporadic.SporadicRep S) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (T : Sylow 2 S)
    (P : Subgroup S) (hP : IsPGroup p P) (hnc : ¬ IsCyclic P)
    (hPT : (P : Set S) * (T : Set S) = (T : Set S) * (P : Set S)) :
    Nonempty (S ≃* NativeSporadic.J4) ∧ p = 11 := by
  have : Nontrivial S := IsSimpleGroup.toNontrivial
  have hP1 := ne_bot_of_not_isCyclic hnc
  obtain ⟨s, hs, ⟨e⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X1.unique_SQT_sporadic_eleven_candidate_restriction hSQT hspor
  have hcard : Nat.card S = Nat.card (NativeSporadic.Carrier s) := Nat.card_congr e.toEquiv
  simp only [CFSG.SectionRank.sqtkSporadicNames, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (false_of_card_eq hp hp5 hP hnc (a := 4) (b := 2) (m := 55) (B := 7)
      (by rw [hcard, show Nat.card (NativeSporadic.Carrier .M11) = 7920 from
        CFSG.Sporadic.Schreier.m11_card]; norm_num) (by norm_num) (by decide) (by norm_num)).elim
  · exact (false_of_card_eq hp hp5 hP hnc (a := 6) (b := 3) (m := 55) (B := 7)
      (by rw [hcard, show Nat.card (NativeSporadic.Carrier .M12) = 95040 from
        CFSG.Sporadic.Schreier.m12_card]; norm_num) (by norm_num) (by decide) (by norm_num)).elim
  · exact (false_of_card_eq hp hp5 hP hnc (a := 7) (b := 2) (m := 385) (B := 19)
      (by rw [hcard, show Nat.card (NativeSporadic.Carrier .M22) = 443520 from
        CFSG.Sporadic.Schreier.m22_card]; norm_num) (by norm_num) (by decide) (by norm_num)).elim
  · exact (false_of_card_eq hp hp5 hP hnc (a := 7) (b := 2) (m := 8855) (B := 94)
      (by rw [hcard, show Nat.card (NativeSporadic.Carrier .M23) = 10200960 from
        CFSG.Sporadic.Schreier.m23_card]; norm_num) (by norm_num) (by decide) (by norm_num)).elim
  · exact (false_of_card_eq hp hp5 hP hnc (a := 10) (b := 3) (m := 8855) (B := 94)
      (by rw [hcard, show Nat.card (NativeSporadic.Carrier .M24) = 244823040 from
        CFSG.Sporadic.Schreier.m24_card]; norm_num) (by norm_num) (by decide) (by norm_num)).elim
  · have hJ1 : Nat.card (NativeSporadic.Carrier .J1) = 175560 :=
      (Nat.card_congr CFSG.Sporadic.Schreier.j1PermEquiv.toEquiv).trans
        CFSG.Sporadic.Schreier.card_j1P
    exact (false_of_card_eq hp hp5 hP hnc (a := 3) (b := 1) (m := 7315) (B := 85)
      (by rw [hcard, hJ1]; norm_num) (by norm_num) (by decide) (by norm_num)).elim
  · exact ((j2_hs_three_free_sylow_product_rigidity (Or.inl ⟨e⟩) T).2 p hp hp5 P hP hP1
      hPT).elim
  · refine ⟨⟨e⟩, ?_⟩
    have hsq := (sq_dvd_card_of_not_isCyclic hp hP hnc).trans (Subgroup.card_subgroup_dvd_card P)
    rw [hcard, show Nat.card (NativeSporadic.Carrier .J4) = 86775571046077562880 from
      CFSG.Sporadic.J4.card_J4] at hsq
    exact CFSG.RankThree.PartOne.eq_eleven_of_sq_dvd_card_J4 hp hp5 hsq
  · exact ((j2_hs_three_free_sylow_product_rigidity (Or.inr ⟨e⟩) T).2 p hp hp5 P hP hP1
      hPT).elim
  · exact (hHeRu S (Or.inl ⟨e⟩) T p hp hp5 P hP hnc hPT).elim
  · exact (hHeRu S (Or.inr ⟨e⟩) T p hp hp5 P hP hnc hPT).elim

theorem catalog_noncyclic_prime_sylow_product_model_restriction
    (hHeRu : StmtHeRuNoncyclicPrimeSylowProduct) :
    StmtCatalogNoncyclicPrimeSylowProduct := by
  intro S _ _ _ hnab hcat hSQT p hp hp5 T P hP hnc hPT
  rcases hcat with ⟨q, -, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨t, n, ℓ, f, hm⟩ | hex | hspor
  ·
    exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (e.injective (by rw [map_mul, map_mul, mul_comm]))
  · exact (alternating_case S hSQT hn e hp hp5 P hP hnc).elim
  · by_cases hℓ2 : ℓ = 2
    · subst hℓ2
      rcases classical_even_case S hnab hSQT hm hp hp5 T P hP hnc hPT with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inl (classical_odd_case S hSQT hℓ2 hm hp hp5 T P hP hnc hPT)
  · rcases exceptional_case S hSQT hex hp hp5 P hP hnc with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (sporadic_case hHeRu S hSQT hspor hp hp5 T P hP hnc hPT)))))

end CFSG.Quasithin.H13.QTESylow
