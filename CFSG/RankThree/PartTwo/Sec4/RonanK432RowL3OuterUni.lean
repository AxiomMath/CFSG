module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowL3OuterLin
import CFSG.RankThree.PartTwo.KFacts.AutPSUScalar

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartTwo.KFacts

namespace L3Outer

variable {p f : ℕ} {K : Type} [Field K]

theorem psuConj_eq_one_iff {h : UnitaryFieldData p f K} (A : unitaryIsom3 h) :
    psuConj h A = 1 ↔ Matrix.ProjGenLinGroup.mk (A : GL (Fin 3) K) = 1 := by
  constructor
  · intro hA
    obtain ⟨-, c, -, hc⟩ := eq_one_of_psuConj_mul_psuField_eq_one A 1
      (by rw [map_one, mul_one]; exact hA)
    rw [hc]
    exact Matrix.ProjGenLinGroup.mk_scalar c
  · intro hA
    obtain ⟨c, hc⟩ := mk_eq_one_iff_mem_statedScalars.mp hA
    exact psuConj_eq_one_of_coe_eq_scalar hc.symm

theorem psuConj_mem_range_conj_of_slPi (h : UnitaryFieldData p f K) (g : unitaryIsom3 h)
    (hg : (g : GL (Fin 3) K) ∈ slPi false 3 (p ^ f) K) :
    psuConj h g ∈ (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)).range := by
  have hSU : (g : GL (Fin 3) K) ∈ unitarySU p f K 3 :=
    (mem_unitarySU_iff h).mpr ((mem_slPi_false h).mp hg)
  refine ⟨((⟨g, hSU⟩ : unitarySU p f K 3) : unitaryPSU h 3), ?_⟩
  rw [conj_mk_eq_psuConj]

theorem outerRow_unitaryPSU_three [Finite K] (h : UnitaryFieldData p f K)
    (hK : PiField false p f K) (hq : ModThree false (p ^ f)) (hq2 : 2 < p ^ f)
    (hnf : ∀ σ : K ≃+* K, orderOf σ ≠ 3) : OuterRow (unitaryPSU h 3) := by
  intro _ σ hσ hout
  have hD : σ ∈ (psuConj h).range := by
    by_contra hD
    obtain ⟨τ, hτ, -⟩ := unitary_order_three_field_descent hq2 σ hσ hD
    exact hnf τ hτ
  obtain ⟨A, rfl⟩ := hD
  refine not_autWeaklyClosed_of_diagonal hK hq (psuConj h) (unitaryIsom3 h).subtype
    (fun g => psuConj_eq_one_iff g)
    (fun g => (mem_glPi_false h).mpr (mem_unitaryIsom3.mp g.2))
    (fun g hg => psuConj_mem_range_conj_of_slPi h g hg)
    (fun t ht => ⟨⟨t, mem_unitaryIsom3.mpr ((mem_slPi_false h).mp ht).2⟩, rfl⟩) (y := A) ?_ ?_
  · intro hA
    obtain ⟨c, hc⟩ := hA
    exact hout (by rw [psuConj_eq_one_of_coe_eq_scalar hc.symm]; exact one_mem _)
  · refine mk_eq_one_iff_mem_statedScalars.mp ((psuConj_eq_one_iff (A ^ 3)).mp ?_)
    rw [map_pow]
    exact hσ

end L3Outer

open L3Outer

theorem outerRow_projSU_three_of_mod_two {p f : ℕ} [Fact p.Prime] (hf : f ≠ 0)
    (hq : p ^ f % 3 = 2) (hq2 : p ^ f ≠ 2)
    (hnf : ∀ σ : GaloisField p (2 * f) ≃+* GaloisField p (2 * f), orderOf σ ≠ 3) :
    OuterRow (projSU 3 p f) := by
  have hPi : PiField false p f (GaloisField p (2 * f)) :=
    ⟨Fact.out, Nat.one_le_iff_ne_zero.mpr hf, by
      rw [GaloisField.card p (2 * f) (by omega)]
      change p ^ (2 * f) = (p ^ f) ^ 2
      rw [← pow_mul, mul_comm]⟩
  obtain ⟨e⟩ := nonempty_unitaryPSU_mulEquiv_projSU hPi.unitary
  exact OuterRow.of_mulEquiv e
    (outerRow_unitaryPSU_three hPi.unitary hPi (show ModThree false (p ^ f) from hq)
      (by omega) hnf)

theorem rowOf_two_SU_of_mod_two : ∀ (p e : ℕ) [Fact p.Prime], 3 < p → 1 ≤ e → e ≤ 2 →
    p ^ e % 3 = 2 → RowOf (projSU 3 p e) := by
  intro p e _ hp he he2 hmod S _ _ _ _ ⟨eS⟩
  have hpe : p ≤ p ^ e := Nat.le_self_pow (by omega) p
  exact GoodRow.of_mulEquiv eS.symm
    ⟨listRow_projSU_three_of_mod_two (by omega) hmod,
      outerRow_projSU_three_of_mod_two (by omega) hmod (by omega)
        (no_field_aut_order_three (by omega) (by omega))⟩

theorem rowOf_seven_SU3_of_odd_of_not_three_dvd : ∀ n : ℕ, 1 ≤ n → n % 2 = 1 → n % 3 ≠ 0 →
    RowOf (projSU 3 2 n) := by
  intro n hn hodd h3 S _ _ hs hna ⟨eS⟩
  by_cases hn1 : n = 1
  · subst hn1
    exfalso
    have hsolv : Group.IsSolvable (projSU 3 2 1) := CFSG.RankThree.PartTwo.Sec13.isSolvable_projSU_two
    haveI : Group.IsSolvable S :=
      Group.isSolvable_of_surjective (f := eS.symm.toMonoidHom) eS.symm.surjective
    obtain ⟨a, b, hab⟩ := hna
    exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr ‹_› a b)
  · have hmod : 2 ^ n % 3 = 2 := two_pow_mod_three_of_odd (Nat.odd_iff.mpr hodd)
    have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact GoodRow.of_mulEquiv eS.symm
      ⟨listRow_projSU_three_of_mod_two (by omega) hmod,
        outerRow_projSU_three_of_mod_two (by omega) hmod (by omega)
          (no_field_aut_order_three (by omega) (by omega))⟩

end CFSG.RankThree.PartTwo.Sec4.RonanK432
