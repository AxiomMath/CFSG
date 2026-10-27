module

public import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank
public import CFSG.LocalAnalysis.SectionRank.Ccomm.PowerMap
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.RankThree.GroupTheory

open Subgroup
open scoped commutatorElement

theorem card_le_pow_five_of_exponent_prime_class_two {p : ℕ} [hp : Fact p.Prime] {D : Type*}
    [Group D] [Finite D] (hexp : ∀ x : D, x ^ p = 1) (hclass : commutator D ≤ center D)
    (hrank : pRank p D ≤ 3) : Nat.card D ≤ p ^ 5 := by
  have hp' : p.Prime := hp.out
  have hP : IsPGroup p D := fun x => ⟨1, by rw [pow_one]; exact hexp x⟩
  rcases Nat.lt_or_ge (pRank p D) 2 with h | h
  · have hcard : Nat.card D ≤ p := by
      by_contra hc
      have := CFSG.RankThree.PartTwo.two_le_pRank hP hexp (not_le.mp hc)
      omega
    exact hcard.trans (Nat.le_self_pow (by norm_num) p)
  rcases Nat.eq_or_lt_of_le h with h2 | h3
  · obtain ⟨-, -, hcard, -⟩ :=
      CFSG.RankThree.PartTwo.card_le_pow_three_of_pRank_two hP hexp h2.symm
    exact hcard.trans (Nat.pow_le_pow_right hp'.pos (by norm_num))
  have h3' : pRank p D = 3 := by omega
  obtain ⟨i, hi, -⟩ :=
    (CFSG.RankThree.PartTwo.class_two_small_rank_order_bounds hP hexp hclass).2.1 h3'
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero] at hi
    rw [hi.2.1]
    exact Nat.pow_le_pow_right hp'.pos (by norm_num)
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero] at hi
    exact hi.1.le
  · simp only [Fin.reduceFinMk, Matrix.cons_val] at hi
    rw [hi.1]
    exact Nat.pow_le_pow_right hp'.pos (by norm_num)

theorem central_elementary_odd_quotient_rank_three_bound {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {F : Type*} [Group F] [Finite F] (hrank : pRank p F ≤ 3) (Z : Subgroup F)
    (hZ : Z ≤ center F) :
    haveI : Z.Normal := normal_of_le_center hZ
    ∀ d : ℕ, IsElementaryAbelian p (F ⧸ Z) → Nat.card (F ⧸ Z) = p ^ d → d ≤ 5 := by
  have : Z.Normal := normal_of_le_center hZ
  intro d hel hcard
  have : Fact p.Prime := ⟨hp⟩
  have hpowZ : ∀ x : F, x ^ p ∈ Z := by
    intro x
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p (F ⧸ Z)) _
  have hcommZ : ∀ x y : F, ⁅x, y⁆ ∈ Z := by
    intro x y
    rw [← QuotientGroup.eq_one_iff, commutatorElement_def]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have hxy : (x : F ⧸ Z) * y = y * x := hel.is_comm.comm _ _
    rw [hxy]
    group
  have hcent : ∀ x y : F, ⁅x, y⁆ ∈ center F := fun x y => hZ (hcommZ x y)
  have hcpow : ∀ x y : F, ⁅x, y⁆ ^ p = 1 := by
    intro x y
    rw [← CFSG.SectionRank.Ccomm.commutatorElement_pow_left
      (mem_center_iff.mp (hcent x y) x), commutatorElement_eq_one_iff_mul_comm]
    exact (mem_center_iff.mp (hZ (hpowZ x)) y).symm
  have hmulpow : ∀ x y : F, (x * y) ^ p = x ^ p * y ^ p := fun x y =>
    CFSG.SectionRank.Ccomm.mul_pow_prime_eq_of_commute hp hp2
      (mem_center_iff.mp (hcent y x) x) (mem_center_iff.mp (hcent y x) y) (hcpow y x)
  let θ : F →* F :=
    { toFun := fun x => x ^ p
      map_one' := one_pow p
      map_mul' := hmulpow }
  set D := θ.ker with hD
  have hrangeZ : θ.range ≤ Z := by
    rintro _ ⟨x, rfl⟩
    exact hpowZ x
  have hDcard : Nat.card D ≤ p ^ 5 := by
    refine card_le_pow_five_of_exponent_prime_class_two (fun x => Subtype.ext ?_) ?_ ?_
    · rw [Subgroup.coe_pow]
      exact MonoidHom.mem_ker.mp x.2
    · rw [_root_.commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [mem_center_iff]
      intro g
      exact Subtype.ext (mem_center_iff.mp (hcent a b) g)
    · refine le_trans ?_ hrank
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top p D,
        CFSG.SectionRank.pRank_eq_open_pRank_top p F]
      exact CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt D.subtype D.subtype_injective
  have hF : Nat.card F = Nat.card D * Nat.card θ.range := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have hFZ : Nat.card F = p ^ d * Nat.card Z := by
    rw [← hcard, ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
  have hle : p ^ d * Nat.card Z ≤ Nat.card D * Nat.card Z := by
    rw [← hFZ, hF]
    exact Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hrangeZ)
  have hpd : p ^ d ≤ p ^ 5 := (Nat.le_of_mul_le_mul_right hle Nat.card_pos).trans hDcard
  exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hpd

end CFSG.RankThree.GroupTheory
