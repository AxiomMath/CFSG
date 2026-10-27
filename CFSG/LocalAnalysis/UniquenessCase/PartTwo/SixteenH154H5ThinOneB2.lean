module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Cfg
public import CFSG.HardMathSupport.Timmesfeld.FieldBonus.OmegaRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKRank3Omega

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ClassicalGroups.Orthogonal
open CFSG.LieType.Universal.Spin (quadMinus coe_quadMinus)
open scoped commutatorElement

variable {W : Type} [CommGroup W]

private theorem s16h_nontrivial_of_isQuasisimple {X : Type} [Group X]
    (h : CFSG.Open.IsQuasisimple X) : Nontrivial X := by
  haveI : Nontrivial (X ⧸ Subgroup.center X) := h.2.toNontrivial
  exact (QuotientGroup.mk'_surjective (Subgroup.center X)).nontrivial

private theorem s16h_isSolvable_of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H)
    [Group.IsSolvable H] : Group.IsSolvable G :=
  Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective

private theorem s16h_not_isSolvable_of_isQuasisimple {Q : Type} [Group Q]
    (hq : CFSG.Open.IsQuasisimple Q) : ¬ Group.IsSolvable Q := by
  intro hs
  haveI := hs
  haveI : Nontrivial (Q ⧸ Subgroup.center Q) := hq.2.toNontrivial
  haveI : Nontrivial Q := (QuotientGroup.mk'_surjective (Subgroup.center Q)).nontrivial
  have h := Group.IsSolvable.commutator_lt_top_of_nontrivial Q
  rw [hq.1] at h
  exact lt_irrefl _ h

private theorem s16h_charP_two_of_card_eq_two_pow {K : Type} [Field K] [Finite K] {a : ℕ}
    (hK : Nat.card K = 2 ^ a) : CharP K 2 := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (p := 2) (f := a)
    (by rw [← Nat.card_eq_fintype_card]; exact hK)

private theorem s16h_exists_ne_zero_ne_one {K : Type} [Field K] [Finite K] {a : ℕ}
    (ha : 2 ≤ a) (hK : Nat.card K = 2 ^ a) : ∃ c : K, c ≠ 0 ∧ c ≠ 1 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hlt : ({0, 1} : Finset K).card < (Finset.univ : Finset K).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hK]
    have h2 : ({0, 1} : Finset K).card ≤ 2 := Finset.card_le_two
    have h3 : 2 < 2 ^ a := by
      calc 2 = 2 ^ 1 := by norm_num
        _ < 2 ^ a := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := ({0, 1} : Finset K))
    (t := Finset.univ) hlt
  have hc' : c ≠ 0 ∧ c ≠ 1 := by simpa using hc
  exact ⟨c, hc'.1, hc'.2⟩

private theorem s16h_commutator_comm_of_card {L : Type*} [Group L] {O : Subgroup L} {p k : ℕ}
    (hp : p.Prime) (hk : k = 1 ∨ k = 2) (hO : Nat.card O = 2 * p ^ k) :
    ∀ a ∈ ⁅O, O⁆, ∀ b ∈ ⁅O, O⁆, a * b = b * a := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpos : 0 < p ^ k := pow_pos hp.pos k
  haveI : Finite O := Nat.finite_of_card_ne_zero (by rw [hO]; omega)
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime (G := O) p (n := k)
    ⟨2, by rw [hO]; ring⟩
  have hidx : P.index = 2 := by
    have h := Subgroup.card_mul_index P
    rw [hP, hO] at h
    exact Nat.eq_of_mul_eq_mul_left hpos (by linarith)
  haveI : P.Normal := Subgroup.normal_of_index_eq_two hidx
  have hPcomm : ∀ x y : P, x * y = y * x := by
    rcases hk with rfl | rfl
    · haveI := isCyclic_of_prime_card (hP.trans (pow_one p))
      exact fun x y => mul_comm' x y
    · haveI := IsPGroup.isMulCommutative_of_card_eq_prime_sq hP
      exact fun x y => mul_comm' x y
  have hQcard : Nat.card (O ⧸ P) = 2 := by
    rw [← Subgroup.index_eq_card]
    exact hidx
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := isCyclic_of_prime_card hQcard
  have hcomm : ∀ x y : O, ⁅x, y⁆ ∈ P := by
    intro x y
    have h : (QuotientGroup.mk' P) ⁅x, y⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm' _ _)
    exact (QuotientGroup.eq_one_iff _).1 h
  have hle : ⁅O, O⁆ ≤ P.map O.subtype := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    exact ⟨⁅(⟨x, hx⟩ : O), ⟨y, hy⟩⁆, hcomm _ _, by simp [commutatorElement_def]⟩
  intro a ha b hb
  obtain ⟨a', ha', rfl⟩ := hle ha
  obtain ⟨b', hb', rfl⟩ := hle hb
  exact congrArg (fun z : P => O.subtype z.1) (hPcomm ⟨a', ha'⟩ ⟨b', hb'⟩)

private theorem s16h_comm_statedOmega_of_card {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K} (hQ : ⇑Q = Q₀) {p k : ℕ}
    (hp : p.Prime) (hk : k = 1 ∨ k = 2)
    (hO : Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 2 * p ^ k) :
    ∀ x ∈ StatedOmega Q₀, ∀ y ∈ StatedOmega Q₀, x * y = y * x := by
  intro x hx y hy
  rw [statedOmega_eq_comap hQ, Subgroup.mem_comap] at hx hy
  have h := s16h_commutator_comm_of_card hp hk hO _ hx _ hy
  exact (toLinEquiv ι K).injective (by
    rw [map_mul, map_mul]
    exact h)

private theorem s16h_comm_statedOmegaMinus_one {K : Type} [Field K] [Finite K] {a : ℕ}
    (ha : a ≤ 3) (hK : Nat.card K = 2 ^ a) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∀ x ∈ StatedOmega (StatedQuadMinus 1 K b c), ∀ y ∈ StatedOmega (StatedQuadMinus 1 K b c),
      x * y = y * x := by
  have ha1 : 1 ≤ a := by
    by_contra hlt
    have h0 : a = 0 := by omega
    subst h0
    rw [pow_zero] at hK
    have : 1 < Nat.card K := Finite.one_lt_card_iff_nontrivial.2 inferInstance
    omega
  rcases (by omega : a = 1 ∨ a = 2 ∨ a = 3) with rfl | rfl | rfl
  · refine s16h_comm_statedOmega_of_card (coe_quadMinus 1 K b c) Nat.prime_three (Or.inl rfl) ?_
    have h := GroupTheory.WeirSylow.natCard_orthogonalGroup_quadMinus (K := K) hirr 0
    have h2 : (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup (quadMinus 1 K b c)) : ℤ) =
        2 * 3 ^ 1 := by
      rw [h, hK]
      norm_num
    exact_mod_cast h2
  · refine s16h_comm_statedOmega_of_card (coe_quadMinus 1 K b c) (by norm_num : Nat.Prime 5)
      (Or.inl rfl) ?_
    have h := GroupTheory.WeirSylow.natCard_orthogonalGroup_quadMinus (K := K) hirr 0
    have h2 : (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup (quadMinus 1 K b c)) : ℤ) =
        2 * 5 ^ 1 := by
      rw [h, hK]
      norm_num
    exact_mod_cast h2
  · refine s16h_comm_statedOmega_of_card (coe_quadMinus 1 K b c) Nat.prime_three (Or.inr rfl) ?_
    have h := GroupTheory.WeirSylow.natCard_orthogonalGroup_quadMinus (K := K) hirr 0
    have h2 : (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup (quadMinus 1 K b c)) : ℤ) =
        2 * 3 ^ 2 := by
      rw [h, hK]
      norm_num
    exact_mod_cast h2

private theorem s16h_comm_statedOmegaMinus_of_le_one {K : Type} [Field K] [Finite K] {a : ℕ}
    (ha : a ≤ 3) (hK : Nat.card K = 2 ^ a) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {m : ℕ} (hm : m ≤ 1) :
    ∀ x ∈ StatedOmega (StatedQuadMinus m K b c), ∀ y ∈ StatedOmega (StatedQuadMinus m K b c),
      x * y = y * x := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hm with rfl | rfl
  · exact s16h_comm_statedOmegaMinus_one ha hK hirr
  · exact s16h_comm_statedOmegaMinus_one ha hK hirr

private theorem s16h_isSolvable_statedProj_of_comm {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] {Q₀ : (ι → K) → K}
    (hcomm : ∀ x ∈ StatedOmega Q₀, ∀ y ∈ StatedOmega Q₀, x * y = y * x) :
    Group.IsSolvable (StatedProj (StatedOmega Q₀)) := by
  haveI : Group.IsSolvable ↥(StatedOmega Q₀) :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (hcomm a.1 a.2 b.1 b.2)
  exact Group.isSolvable_of_surjective
    (QuotientGroup.mk'_surjective ((StatedScalars ι K).subgroupOf (StatedOmega Q₀)))

theorem s16h_H5_isOmegaMinus_class [Finite W] {A L : Subgroup (MulAut W)} {t : MulAut W}
    (hc : s16h_H5Cfg A L t) {n a : ℕ} (ha : a ≤ 3) (h : IsOmegaMinus ↥L n a) :
    n = 4 ∧ (a = 1 ∨ a = 2 ∨ a = 3) := by
  have hΩ : IsOmegaMinus ↥L n a := h
  obtain ⟨hev, K, hF, hFin, b, c, hKcard, hpoly, ⟨e⟩⟩ := h
  letI := hF
  letI := hFin
  have hq : CFSG.Open.IsQuasisimple ↥L := hc.comp.2.2
  have hnsolv : ¬ Group.IsSolvable ↥L := s16h_not_isSolvable_of_isQuasisimple hq
  have ha1 : 1 ≤ a := by
    by_contra hlt
    have h0 : a = 0 := by omega
    subst h0
    rw [pow_zero] at hKcard
    have : 1 < Nat.card K := Finite.one_lt_card_iff_nontrivial.2 inferInstance
    omega
  have ha' : a = 1 ∨ a = 2 ∨ a = 3 := by omega
  have hchar : CharP K 2 := s16h_charP_two_of_card_eq_two_pow hKcard
  have hm2 : n / 2 = 2 := by
    rcases Nat.lt_or_ge (n / 2) 2 with hm | hm
    ·
      have hm1 : n / 2 ≤ 1 := by omega
      have hcomm := s16h_comm_statedOmegaMinus_of_le_one ha hKcard hpoly hm1
      haveI : Group.IsSolvable (StatedProj (StatedOmega (StatedQuadMinus (n / 2) K b c))) :=
        s16h_isSolvable_statedProj_of_comm hcomm
      exact (hnsolv (s16h_isSolvable_of_mulEquiv e)).elim
    · rcases Nat.lt_or_ge (n / 2) 3 with hm3 | hm3
      · omega
      ·
        have h2 : 2 ≤ CFSG.Open.pRank 3 L := by
          have h2top : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup
              (StatedProj (StatedOmega (StatedQuadMinus (n / 2) K b c)))) := by
            rcases Nat.lt_or_ge (n / 2) 4 with hm4 | hm4
            ·
              have hm3' : n / 2 = 3 := by omega
              by_cases ha1' : a = 1
              ·
                subst ha1'
                have hn6 : n = 6 := by
                  have h2n : n = 2 * (n / 2) := (Nat.two_mul_div_two_of_even hev).symm
                  rw [hm3'] at h2n
                  omega
                have h6 : IsOmegaMinus ↥L 6 1 := by
                  rw [hn6] at hΩ
                  exact hΩ
                obtain ⟨E, hEel, hEcard⟩ := s15k_om6_exists_e27 h6
                have h3top : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) :=
                  CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_top hEel
                    (by rw [hEcard]; norm_num)
                rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e]
                exact (by norm_num : 2 ≤ 3).trans h3top
              ·
                have ha2 : 2 ≤ a := by omega
                obtain ⟨c₀, hc₀0, hc₀1⟩ := s16h_exists_ne_zero_ne_one ha2 hKcard
                have hc₀sq : c₀ ^ 2 ≠ 1 := fun hh =>
                  hc₀1 (CharTwo.sq_injective (hh.trans (one_pow 2).symm))
                exact CFSG.HardMathSupport.Timmesfeld.FieldBonus.Orth.two_le_pRank_minus
                  (K := K) (n := n / 2) hm3 b c hc₀0 hc₀sq
            ·
              haveI : CharP K 2 := hchar
              have h3 := CFSG.SectionRank.ClassicalEven.omegaMinus_three_le_pRank_three
                (K := K) (n := n / 2) hm4 b c
              exact (by norm_num : 2 ≤ 3).trans h3
          rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) L,
            CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e]
          exact h2top
        have h1 := hc.thin 3 Nat.prime_three (by norm_num)
        omega
  have hn : n = 2 * (n / 2) := (Nat.two_mul_div_two_of_even hev).symm
  rw [hm2] at hn
  exact ⟨hn, ha'⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
