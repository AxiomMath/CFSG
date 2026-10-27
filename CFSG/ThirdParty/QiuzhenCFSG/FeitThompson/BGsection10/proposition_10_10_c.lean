module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.proposition_10_10_b
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection5.theorem_5_3
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection5.theorem_5_5_a
import Mathlib.GroupTheory.Schreier
import Mathlib.LinearAlgebra.Projectivization.Cardinality

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# Statements from BG Section 10

This file records a statement-only scaffold for Section 10 of
`Local Analysis for the Odd Order Theorem`.

The local PDF extraction mangles the Greek letters used in the book. This
module imports the shared Section 10 notation from `FeitThompson.BGsection10.Defs`.
-/

section Section10

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

private theorem CFSG.section10_normalizer_ne_top_of_ne_bot_ne_top_for_10_10
    {Q : Subgroup G} (hQbot : Q ≠ ⊥) (hQtop : Q ≠ ⊤) :
    Subgroup.normalizer (Q : Set G) ≠ ⊤ := by
  intro hnorm_top
  have hQnormal : Q.Normal := Subgroup.normalizer_eq_top_iff.mp hnorm_top
  let : IsSimpleGroup G := IsMinCE.simple
  rcases (haveI := hQnormal; IsSimpleGroup.eq_bot_or_eq_top_of_normal Q) with hbot | htop
  · exact hQbot hbot
  · exact hQtop htop

omit [Group G] [Finite G] [IsMinCE G] in
private theorem CFSG.section10_derivedSubgroup_isPGroup_of_theorem_5_5_a
    {r : ℕ} [Fact r.Prime] (hrodd : r ≠ 2)
    {R : Type*} [Group R] [Finite R] (hnarrow : IsNarrowPGroup r R)
    {A : Subgroup (MulAut R)} [Group.IsSolvable A] (hoddA : Odd (Nat.card A)) :
    IsPGroup r (derivedSubgroup A) := by
  classical
  have hquot_comm : IsMulCommutative (A ⧸ pCore r A) :=
    (theorem_5_5_a (p := r) hrodd (R := R) hnarrow (A := A) hoddA).1
  have hder_le_pcore : derivedSubgroup A ≤ pCore r A := by
    have hcomm_le : _root_.commutator A ≤ pCore r A :=
      (Subgroup.Normal.quotient_commutative_iff_commutator_le
        (N := pCore r A)).1 hquot_comm
    change derivedSeries A 1 ≤ pCore r A
    rw [derivedSeries_one]
    exact hcomm_le
  let Dsub : Subgroup (pCore r A) := (derivedSubgroup A).subgroupOf (pCore r A)
  have hDsubp : IsPGroup r Dsub :=
    (pCore_isPGroup (G := A) (p := r)).to_subgroup Dsub
  simpa [Dsub] using
    hDsubp.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := derivedSubgroup A) (K := pCore r A)
        hder_le_pcore)

omit [Group G] [Finite G] [IsMinCE G] in
private theorem CFSG.section10_card_eq_one_of_isPGroup_isPGroup_ne
    {R : Type*} [Group R] [Finite R] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hpq : p ≠ q) (hRp : IsPGroup p R) (hRq : IsPGroup q R) :
    Nat.card R = 1 := by
  rcases hRp.exists_card_eq with ⟨n, hn⟩
  have hq_not_dvd_p : ¬ q ∣ p := by
    intro hqp
    have hq_eq_p : q = p :=
      (Nat.prime_dvd_prime_iff_eq (Fact.out : Nat.Prime q)
        (Fact.out : Nat.Prime p)).mp hqp
    exact hpq hq_eq_p.symm
  have hq_not_dvd_card : ¬ q ∣ Nat.card R := by
    intro hqcard
    rw [hn] at hqcard
    exact hq_not_dvd_p ((Fact.out : Nat.Prime q).dvd_of_dvd_pow hqcard)
  rcases hRq.card_eq_or_dvd with hcard | hqdiv
  · exact hcard
  · exact False.elim (hq_not_dvd_card hqdiv)

public theorem CFSG.section10_le_centralizer_of_le_derived_normalizer_of_narrow
    {p q : Nat.Primes} (hpq : p ≠ q) {P Q : Subgroup G}
    (hPp : IsPGroup p.val P)
    (hPder : P ≤ ambientDerivedSubgroup (Subgroup.normalizer (Q : Set G)))
    (hQq : IsPGroup q.val Q) (hQnarrow : IsNarrowPGroup q.val Q) :
    P ≤ Subgroup.centralizer (Q : Set G) := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  have : Fact q.val.Prime := ⟨q.property⟩
  by_cases hQbot : Q = ⊥
  · intro x _hxP
    rw [Subgroup.mem_centralizer_iff_commutator_eq_one]
    intro y hyQ
    have hy_one : y = 1 := by simpa [hQbot] using hyQ
    simp [hy_one]
  · let N : Subgroup G := Subgroup.normalizer (Q : Set G)
    have hQ_le_N : Q ≤ N := by
      simpa [N] using (Subgroup.le_normalizer (H := Q))
    have hQtop : Q ≠ ⊤ :=
      section10_global_pSubgroup_proper_of_min_ce (G := G) (p := q.val) hQq
    have hNproper : N ≠ ⊤ :=
      section10_normalizer_ne_top_of_ne_bot_ne_top_for_10_10
        (G := G) hQbot hQtop
    have : Group.IsSolvable N :=
      IsMinCE.proper_subgroups_solvable N (lt_top_iff_ne_top.2 hNproper)
    have hNodd : Odd (Nat.card N) :=
      odd_of_card_dvd IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card N)
    have hq_dvd_Q : q.val ∣ Nat.card Q := by
      rcases hQq.card_eq_or_dvd with hcard | hdiv
      · exact False.elim (hQbot ((Subgroup.card_eq_one (H := Q)).mp hcard))
      · exact hdiv
    have hq_dvd_G : q.val ∣ Nat.card G :=
      dvd_trans hq_dvd_Q (Subgroup.card_subgroup_dvd_card Q)
    have hqodd : q.val ≠ 2 := Odd.ne_two_of_dvd_nat IsMinCE.odd_order hq_dvd_G
    let QN : Subgroup N := Q.subgroupOf N
    have : QN.Normal := by
      exact
        (Subgroup.normal_subgroupOf_iff_le_normalizer
          (H := Q) (K := N) hQ_le_N).mpr (by simp [N])
    have hQNnarrow : IsNarrowPGroup q.val QN :=
      section10_isNarrowPGroup_of_equiv
        (p := q.val) (Subgroup.subgroupOfEquivOfLe (H := Q) (K := N) hQ_le_N)
        hQnarrow
    let φ : N →* MulAut QN := MulAut.conjNormal (H := QN)
    let A : Subgroup (MulAut QN) := φ.range
    have hAodd : Odd (Nat.card A) :=
      odd_of_card_dvd hNodd (Subgroup.card_range_dvd φ)
    have : Group.IsSolvable A :=
      Group.isSolvable_of_surjective (f := φ.rangeRestrict) φ.rangeRestrict_surjective
    have hderAq : IsPGroup q.val (derivedSubgroup A) :=
      section10_derivedSubgroup_isPGroup_of_theorem_5_5_a
        (r := q.val) hqodd (R := QN) hQNnarrow (A := A) hAodd
    let ψ : N →* A := φ.rangeRestrict
    have hψsurj : Function.Surjective ψ := φ.rangeRestrict_surjective
    have hmap_der : (derivedSubgroup N).map ψ = derivedSubgroup A := by
      simpa [derivedSubgroup, derivedSeries_one] using
        map_derivedSeries_eq (f := ψ) hψsurj 1
    have hP_le_N : P ≤ N := by
      intro x hxP
      have hxD : x ∈ ambientDerivedSubgroup N := hPder hxP
      rw [ambientDerivedSubgroup, Subgroup.mem_map] at hxD
      rcases hxD with ⟨d, _hdD, hd_eq⟩
      simp [← hd_eq]
    let ιPN : P →* N := {
      toFun := fun x => ⟨(x : G), hP_le_N x.property⟩
      map_one' := by
        ext
        simp
      map_mul' := by
        intro x y
        ext
        simp
    }
    let χ : P →* A := ψ.comp ιPN
    let R : Subgroup A := (⊤ : Subgroup P).map χ
    have htopPp : IsPGroup p.val (⊤ : Subgroup P) := by
      simpa using hPp.to_subgroup (⊤ : Subgroup P)
    have hRp : IsPGroup p.val R := by
      simpa [R] using
        IsPGroup.map (p := p.val) (H := (⊤ : Subgroup P)) htopPp χ
    have hR_le_der : R ≤ derivedSubgroup A := by
      intro a ha
      change a ∈ (⊤ : Subgroup P).map χ at ha
      rw [Subgroup.mem_map] at ha
      rcases ha with ⟨x, _hx, rfl⟩
      have hxD : ((x : P) : G) ∈ ambientDerivedSubgroup N := hPder x.property
      rw [ambientDerivedSubgroup, Subgroup.mem_map] at hxD
      rcases hxD with ⟨d, hdD, hd_eq⟩
      have hnd : (⟨((x : P) : G), hP_le_N x.property⟩ : N) = d :=
        Subtype.ext hd_eq.symm
      have hχ_eq : χ x = ψ d := by
        simpa [χ, ιPN] using congrArg ψ hnd
      rw [hχ_eq]
      have hψd : ψ d ∈ (derivedSubgroup N).map ψ :=
        Subgroup.mem_map_of_mem ψ hdD
      change ψ d ∈ derivedSubgroup A
      rw [← hmap_der]
      exact hψd
    let Rsub : Subgroup (derivedSubgroup A) := R.subgroupOf (derivedSubgroup A)
    have hRsubq : IsPGroup q.val Rsub := hderAq.to_subgroup Rsub
    have hRq : IsPGroup q.val R :=
      by
        simpa [Rsub] using
          hRsubq.of_equiv
            (Subgroup.subgroupOfEquivOfLe (H := R) (K := derivedSubgroup A) hR_le_der)
    have hpq_val : p.val ≠ q.val := by
      intro hpq_val
      exact hpq (Subtype.ext hpq_val)
    have hRcard_one : Nat.card R = 1 :=
      section10_card_eq_one_of_isPGroup_isPGroup_ne hpq_val hRp hRq
    have hRbot : R = ⊥ := Subgroup.card_eq_one.mp hRcard_one
    intro x hxP
    rw [Subgroup.mem_centralizer_iff]
    intro y hyQ
    let xP : P := ⟨x, hxP⟩
    have hxR : χ xP ∈ R := by
      change χ xP ∈ (⊤ : Subgroup P).map χ
      exact Subgroup.mem_map_of_mem χ (by simp)
    have hxRbot : χ xP ∈ (⊥ : Subgroup A) := by
      simpa [R, hRbot] using hxR
    have hχx_one : χ xP = 1 := Subgroup.mem_bot.mp hxRbot
    let xN : N := ⟨x, hP_le_N hxP⟩
    let yN : N := ⟨y, hQ_le_N hyQ⟩
    let yQN : QN := ⟨yN, by simpa [QN, Subgroup.mem_subgroupOf] using hyQ⟩
    have hfix : φ xN yQN = yQN := by
      have hψ_one : ψ xN = 1 := by
        simpa [χ, ιPN, xP, xN] using hχx_one
      have hval : ((ψ xN : A) : MulAut QN) = 1 :=
        congrArg (fun a : A => (a : MulAut QN)) hψ_one
      change ((ψ xN : A) : MulAut QN) yQN = yQN
      simp [hval]
    have hconj : x * y * x⁻¹ = y := by
      have hval := congrArg (fun z : QN => ((z : N) : G)) hfix
      simpa [φ, xN, yQN, yN, QN, MulAut.conjNormal_apply, MulAut.conj_apply,
        mul_assoc] using hval
    have hxy : x * y = y * x := by
      calc
        x * y = (x * y * x⁻¹) * x := by simp [mul_assoc]
        _ = y * x := by rw [hconj]
    exact hxy.symm

/-- Proposition 10.10(c). -/
public theorem CFSG.proposition_10_10_c
    {p q : Nat.Primes} (hpq : p ≠ q) {A Q : Subgroup G}
    (hA : A ∈ section10RankTwoMaximalElementaryAbelianSubgroups p G)
    (hQ : Q ∈ section7HStarFamily (⊤ : Subgroup G) A {q})
    (hqC : q ∈ subgroupPrimeSet (Subgroup.centralizer (A : Set G)))
    (hQshape :
      IsCyclic Q ∨ ∃ B : Subgroup Q, B ∈ section10RankTwoMaximalElementaryAbelianSubgroups q Q) :
    ∃ P : Sylow p.val G, A ≤ (P : Subgroup G) ∧
      (P : Subgroup G) ≤ Subgroup.centralizer (Q : Set G) := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  have : Fact q.val.Prime := ⟨q.property⟩
  obtain ⟨P, hAP, hPder⟩ := proposition_10_10_b (G := G) hpq hA hQ hqC
  have hQπ : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) Q := hQ.1.2.1
  have hQq : IsPGroup q.val Q :=
    section8_isPGroup_of_isPiSubgroup_singleton (G := G) hQπ
  have hq_dvd_G : q.val ∣ Nat.card G :=
    dvd_trans hqC (Subgroup.card_subgroup_dvd_card (Subgroup.centralizer (A : Set G)))
  have hqodd : q.val ≠ 2 := Odd.ne_two_of_dvd_nat IsMinCE.odd_order hq_dvd_G
  have hQnarrow : IsNarrowPGroup q.val Q := by
    rcases hQshape with hQcyc | hQrank
    · let : IsCyclic Q := hQcyc
      refine ⟨hQq, Or.inl ?_⟩
      exact (groupRank_le_one_of_isCyclic Q).trans (by decide)
    · rcases hQrank with ⟨B, hB⟩
      by_cases hQr : groupRank Q ≤ 2
      · exact ⟨hQq, Or.inl hQr⟩
      · have hQr3 : 3 ≤ groupRank Q := by omega
        exact
          (theorem_5_3 (p := q.val) hqodd (R := Q) hQq hQr3).mpr
            ⟨B, hB.1, hB.2⟩
  exact ⟨P, hAP,
    section10_le_centralizer_of_le_derived_normalizer_of_narrow
      (G := G) hpq P.isPGroup' hPder hQq hQnarrow⟩

end Section10
