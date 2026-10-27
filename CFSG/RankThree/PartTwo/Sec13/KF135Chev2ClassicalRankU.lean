module

public import CFSG.RankThree.PartTwo.Sec13.KF135Chev2ClassicalRank
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutNonsplitSU

public section

namespace CFSG.RankThree.PartTwo.Sec13.KF135Chev2

open Matrix CFSG.LieType.SeitzGeneration
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

theorem suGroup_eq_unitarySU (m n : ℕ) :
    suGroup m n = unitarySU 2 n (GaloisField 2 (2 * n)) m :=
  (CFSG.PGLModel.statedSU_eq_closure_det m (2 ^ n) (GaloisField 2 (2 * n))).symm

theorem exists_maxElemAb_le {f m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hrq : ¬ r ∣ 2 ^ f + 1) {A : Subgroup ↥(unitarySU 2 f K m)}
    (hAp : ∀ a ∈ A, a ^ r = 1) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    ∃ E : Subgroup ↥(unitarySU 2 f K m), CFSG.StandardType.SUTB.MaxElemAb r E ∧ A ≤ E := by
  classical
  have : Finite K := h.finite
  set Q : Subgroup ↥(unitarySU 2 f K m) → Prop := fun E =>
    A ≤ E ∧ (∀ a ∈ E, a ^ r = 1) ∧ ∀ a ∈ E, ∀ b ∈ E, a * b = b * a with hQ
  set P : ℕ → Prop := fun k => ∃ E, Q E ∧ Nat.card E = k with hP
  have hQ0 : Q A := ⟨le_rfl, hAp, hAc⟩
  have hbound : ∀ k, P k → k ≤ Nat.card ↥(unitarySU 2 f K m) := by
    rintro k ⟨E, -, rfl⟩
    exact Subgroup.card_le_card_group E
  have hP0 : P (Nat.card A) := ⟨_, hQ0, rfl⟩
  set N := Nat.findGreatest P (Nat.card ↥(unitarySU 2 f K m)) with hN
  obtain ⟨E, hE, hEN⟩ : P N := Nat.findGreatest_spec (hbound _ hP0) hP0
  refine ⟨E, ⟨hr, hr2, hrq, hE.2.1, hE.2.2, fun g hg hgE => ?_⟩, hE.1⟩
  set E' := Subgroup.closure ((E : Set ↥(unitarySU 2 f K m)) ∪ {g}) with hE'
  have h1 := CFSG.StandardType.OrdPNsU.closure_comm_pow
    (S := (E : Set ↥(unitarySU 2 f K m)) ∪ {g}) (p := r)
    (by
      rintro x (hx | hx) y (hy | hy)
      · exact hE.2.2 x hx y hy
      · rw [Set.mem_singleton_iff.mp hy]; exact (hgE x hx).symm
      · rw [Set.mem_singleton_iff.mp hx]; exact hgE y hy
      · rw [Set.mem_singleton_iff.mp hx, Set.mem_singleton_iff.mp hy])
    (by
      rintro x (hx | hx)
      · exact hE.2.1 x hx
      · rw [Set.mem_singleton_iff.mp hx]; exact hg)
  have hEE' : E ≤ E' := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hQ' : Q E' := ⟨hE.1.trans hEE', h1.2, h1.1⟩
  have hcard : Nat.card E' ≤ Nat.card E := by
    rw [hEN]
    exact Nat.le_findGreatest (hbound _ ⟨E', hQ', rfl⟩) ⟨E', hQ', rfl⟩
  have heq : E = E' := Subgroup.eq_of_le_of_card_ge hEE' hcard
  rw [heq]
  exact Subgroup.subset_closure (Or.inr rfl)

theorem rankLE1_projSU_of_lt_ordNegQ {m n r : ℕ} (hn : 1 ≤ n) (hm : 0 < m) (hr : r.Prime)
    (hrm : m < r) (hr2 : r ≠ 2) (hrq : ¬ r ∣ 2 ^ n + 1)
    (hlt : m < 2 * CFSG.RankThree.PartOne.KCUnitaryPlane.ordNegQ 2 n r) :
    RankLE1 r (projSU m 2 n) := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := GaloisField 2 (2 * n)
  have h : UnitaryFieldData 2 n K := ⟨Nat.prime_two, hn, GaloisField.card 2 (2 * n) (by omega)⟩
  refine RankLE1.of_pRank hr ?_
  rw [projSU_eq_projImage_suGroup,
    CFSG.RankThree.PartOne.LIT.pRank_projImage_eq _ (not_dvd_card_scalars_suGroup hr hrm hm)]
  refine CFSG.RankThree.PartOne.LIT.pRank_le_of_card_gl hr.one_lt _ fun E hEH hc he => ?_
  have hEU : E ≤ unitarySU 2 n K m := hEH.trans (suGroup_eq_unitarySU m n).le
  set U := unitarySU 2 n K m
  let A : Subgroup ↥U := E.comap U.subtype
  have hAE : Nat.card A = Nat.card E := by
    have hmap : A.map U.subtype = E := by
      rw [Subgroup.map_comap_eq, Subgroup.range_subtype]
      exact inf_eq_right.mpr hEU
    rw [← hmap, Subgroup.card_map_of_injective U.subtype_injective]
  obtain ⟨A', hA', hAA'⟩ := exists_maxElemAb_le h hr hr2 hrq (A := A)
    (fun a ha => Subtype.ext (by simpa using he _ ha))
    (fun a ha b hb => Subtype.ext (by simpa using hc _ ha _ hb))
  have hle := CFSG.StandardType.OrdPNsU.card_le_pow_ordNegQ h hA'
  have hdiv : m / CFSG.RankThree.PartOne.KCUnitaryPlane.ordNegQ 2 n r ≤ 1 := by
    have hpos : 0 < CFSG.RankThree.PartOne.KCUnitaryPlane.ordNegQ 2 n r := by
      by_contra h0
      have h0' : CFSG.RankThree.PartOne.KCUnitaryPlane.ordNegQ 2 n r = 0 := by omega
      rw [h0'] at hlt
      omega
    have := (Nat.div_lt_iff_lt_mul hpos).2 (by linarith : m < 2 *
      CFSG.RankThree.PartOne.KCUnitaryPlane.ordNegQ 2 n r)
    omega
  calc Nat.card E = Nat.card A := hAE.symm
    _ ≤ Nat.card A' := Subgroup.card_le_of_le hAA'
    _ ≤ r ^ (m / CFSG.RankThree.PartOne.KCUnitaryPlane.ordNegQ 2 n r) := hle
    _ ≤ r ^ 1 := Nat.pow_le_pow_right hr.pos hdiv

theorem ordNegQ_eq_two_of_eq_one {n r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hx : ((2 ^ n : ℕ) : ZMod r) = 1) :
    CFSG.RankThree.PartOne.KCUnitaryPlane.ordNegQ 2 n r = 2 := by
  haveI : Fact r.Prime := ⟨hr⟩
  rw [CFSG.RankThree.PartOne.KCUnitaryPlane.ordNegQ]
  have hx' : ((2 : ℕ) : ZMod r) ^ n = 1 := by rw [← Nat.cast_pow]; exact hx
  rw [hx', orderOf_neg_one, ZMod.ringChar_zmod_n, if_neg hr2]

theorem ordNegQ_eq_four_of_sq_eq_neg_one {n r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hx : ((2 ^ n : ℕ) : ZMod r) ^ 2 = -1) :
    CFSG.RankThree.PartOne.KCUnitaryPlane.ordNegQ 2 n r = 4 := by
  have hy2 : (-((2 : ℕ) : ZMod r) ^ n) ^ 2 = -1 := by
    rw [neg_sq, ← Nat.cast_pow]
    exact hx
  have hne : (-1 : ZMod r) ≠ 1 := by
    haveI : Fact (1 < r) := ⟨hr.one_lt⟩
    exact Ring.neg_one_ne_one_of_char_ne_two (by rw [ZMod.ringChar_zmod_n]; exact hr2)
  have h4 : orderOf (-((2 : ℕ) : ZMod r) ^ n) = 2 ^ (1 + 1) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime_pow (by rw [pow_one, hy2]; exact hne) ?_
    rw [show 2 ^ (1 + 1) = 2 * 2 by norm_num, pow_mul, hy2]
    exact neg_one_sq
  rw [show (4 : ℕ) = 2 ^ (1 + 1) by norm_num]
  exact h4

end CFSG.RankThree.PartTwo.Sec13.KF135Chev2
