module

public import CFSG.RankThree.PartOne.CTP.SeitzField
public import CFSG.RankThree.PartOne.KC.LinearNoninnerPlaneInner
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherLinearAutNormal
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCentralizer
public import CFSG.RankThree.PartOne.CTP.SeitzThree

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCLinPlane CFSG.RankThree.PartOne.KCLinComm
open CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane

section Linear

variable {n : ℕ} {F : Type} [Field F] [Finite F]

theorem mem_semilinearAutGroup_of_pow_eq_one (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {a : MulAut (projectiveSL n F)} (hap : a ^ p = 1) : a ∈ semilinearAutGroup n F :=
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_semilinearAutGroup_of_pow_odd hn (hp.odd_of_ne_two hp2) hap

theorem p_dvd_card_fieldAut_of_outer (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcop : Nat.Coprime p (Nat.gcd n (Nat.card F - 1))) {a : MulAut (projectiveSL n F)}
    (hap : a ^ p = 1) (hout : a ∉ innSL n F) : p ∣ Nat.card (F ≃+* F) := by
  have haE : a ∈ (semilinPsi n F).range := by
    rw [range_semilinPsi]
    exact mem_semilinearAutGroup_of_pow_eq_one hn hp hp2 hap
  set α : ↥(semilinPsi n F).range := ⟨a, haE⟩ with hα
  have hσ1 : sigmaE n F hn α ≠ 1 := fun h =>
    hout (inner_of_mem_linearAut_of_pow_eq_one hn hcop ((sigmaE_eq_one_iff hn α).mp h) hap)
  have hσp : sigmaE n F hn α ^ p = 1 := by
    rw [← map_pow]
    have : α ^ p = 1 := Subtype.ext hap
    rw [this, map_one]
  have : Fact p.Prime := ⟨hp⟩
  rw [← orderOf_eq_prime hσp hσ1]
  exact orderOf_dvd_natCard _

end Linear

theorem extSeitzAtOuter_A_of_exponent_lt_five {m : ℕ} {q : TauCeti.PrimePower} (hm2 : 2 ≤ m)
    (hmq : m ≤ 3 ∨ q.card = 2) (he : q.exponent < 5) : ExtSeitzAtOuter (.A m q) := by
  intro K _ _ _ hnab ⟨hv, ⟨e0⟩⟩ p hp hp5 hpd E hE hc hout
  exfalso
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hn : 3 ≤ m + 1 := by omega
  let e : K ≃* projectiveSL (m + 1) (GaloisField q.p q.exponent) :=
    (e0.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL m q hv)).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (m + 1) _)
  push Not at hout
  obtain ⟨φ, hφE, hφ⟩ := hout
  have hφp : φ ^ p = 1 := elemPow_eq_one_of_isElementaryAbelian φ hφE
  have hφ'p : MulAut.congr e φ ^ p = 1 := by rw [← map_pow, hφp, map_one]
  have hφ'out : MulAut.congr e φ ∉ innSL (m + 1) (GaloisField q.p q.exponent) := by
    rintro ⟨g, hg⟩
    exact hφ (e.symm g) (eq_conj_of_congr_eq_conj e hg.symm)
  have hcop : Nat.Coprime p (Nat.gcd (m + 1) (Nat.card (GaloisField q.p q.exponent) - 1)) := by
    refine (Nat.Prime.coprime_iff_not_dvd hp).2 fun hd => ?_
    rcases hmq with hm | hm
    · have h1 := Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ (by omega)) hd
      have h2 : Nat.gcd (m + 1) (Nat.card (GaloisField q.p q.exponent) - 1) ≤ m + 1 :=
        Nat.gcd_le_left _ (by omega)
      omega
    · have hF : Nat.card (GaloisField q.p q.exponent) = q.card := by
        rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
      rw [hF, hm] at hd
      have : Nat.gcd (m + 1) (2 - 1) = 1 := by simp
      rw [this] at hd
      have := Nat.le_of_dvd (by norm_num) hd
      omega
  have hdvd := p_dvd_card_fieldAut_of_outer hn hp (by omega) hcop hφ'p hφ'out
  have hcardAut : Nat.card (GaloisField q.p q.exponent ≃+* GaloisField q.p q.exponent) =
      q.exponent := by
    obtain ⟨-, -, -, -, hcardAut, -⟩ := finite_field_automorphism_fixed_field_cardinality
      q.prime_p q.exponent_pos (GaloisField.card q.p q.exponent q.exponent_pos.ne')
    exact hcardAut
  rw [hcardAut] at hdvd
  have := Nat.le_of_dvd q.exponent_pos hdvd
  omega

end CFSG.RankThree.PartOne.CTP
