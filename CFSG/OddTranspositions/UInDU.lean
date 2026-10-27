module

public import CFSG.OddTranspositions.CommutatorSize
public import CFSG.OddTranspositions.SecondKindCoset
public import CFSG.Timmesfeld.Bridge.OddLocalDefs

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
  CFSG.Timmesfeld.Bridge.OddTransp CFSG.Timmesfeld.Connectivity CFSG.Open
  CFSG.CGT.Timmesfeld75
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem u_mem_closure_commSet (hD : IsOddTransp D) (hN : IsNormalSet D)
    {u w v : G} (htri : IsTriangle D u w v) (h4 : orderOf (u * v * w) = 4)
    (hno : ∀ x ∈ D, x ∈ Subgroup.closure {u, w} → IsTriangle D u x v →
      ¬ IsThirdKind u x v)
    (hm : 3 < orderOf (u * w)) :
    u ∈ Subgroup.closure (CFSG.Timmesfeld.Bridge.commSet D u) := by
  classical
  let Q : Subgroup G := conjClosure (Subgroup.closure {u, w}) (u * v)
  let E : Subgroup G := ⁅Q, Subgroup.zpowers u⁆
  have hS : SecondKindStructure u w v := secondKind_structure hD hN htri h4 hno
  have hu2 : u * u = 1 := hD.mul_self_eq_one htri.1
  have hEQ : E ≤ Q := by
    simpa only [E, Q] using secondKind_commutator_zpowers_u_le hD hN htri h4 hno
  have hEcard : 2 < Nat.card ↥E := by
    simpa only [E, Q] using card_commutator_gt_two hD hN htri h4 hno hm
  have hcen : E ≤ Subgroup.centralizer ({u} : Set G) := by
    simpa only [E, Q] using secondKind_commutator_le_centralizer hD hN htri h4 hno
  have hQsq : ∀ q ∈ Q, q * q = 1 := hS.sq
  have hQ : IsElemAbelian 2 Q := by
    refine ⟨?_, ?_⟩
    · exact IsMulCommutative.of_comm
        (fun x y => Subtype.ext ((hS.comm x.1 x.2 y.1 y.2).eq))
    · intro x hx
      simpa [pow_two] using hQsq x hx
  have hNQ : u ∈ Subgroup.normalizer (Q : Set G) :=
    Subgroup.zpowers_le.mp
      ((Subgroup.le_normalizer_iff_commutator_le_left (H := Subgroup.zpowers u) (K := Q)).mpr
        (by simpa only [E] using hEQ))
  haveI : Fintype ↥E := Fintype.ofFinite ↥E
  have h3E : 3 ≤ Fintype.card ↥E := by
    rw [← Nat.card_eq_fintype_card]
    omega
  obtain ⟨e1, he1ne⟩ : ∃ e : ↥E, e ≠ 1 :=
    Fintype.exists_ne_of_one_lt_card (α := ↥E) (by omega) 1
  have herase : 1 < (Finset.univ.erase (1 : ↥E)).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    omega
  obtain ⟨e2, he2mem, he2ne1⟩ := Finset.exists_mem_ne herase e1
  have he2ne : e2 ≠ 1 := (Finset.mem_erase.mp he2mem).1
  let e3 : ↥E := e1 * e2
  have he3val : (e3 : G) = (e1 : G) * (e2 : G) := by simp [e3]
  have he1sq : (e1 : G) * (e1 : G) = 1 := hQsq _ (hEQ e1.2)
  have he3sq : (e3 : G) * (e3 : G) = 1 := hQsq _ (hEQ e3.2)
  have he3ne : e3 ≠ 1 := by
    intro h
    have h3 : (e1 : G) * (e2 : G) = 1 := by
      have h3' : (e3 : G) = (1 : G) := congrArg (fun x : ↥E => (x : G)) h
      simpa [he3val] using h3'
    apply he2ne1
    apply Subtype.ext
    calc (e2 : G) = 1 * (e2 : G) := (one_mul _).symm
      _ = ((e1 : G) * (e1 : G)) * (e2 : G) := by rw [he1sq]
      _ = (e1 : G) * ((e1 : G) * (e2 : G)) := by rw [mul_assoc]
      _ = (e1 : G) := by rw [h3, mul_one]
  have hcommE : ∀ e : ↥E, Commute u (e : G) := fun e =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hcen e.2)).symm
  have key : ∀ e : ↥E, e ≠ 1 → u * (e : G) ∈ commSet D u := by
    intro e he
    have hsub : (e : G) ∈ commSub u Q := by
      rw [commSub, Subgroup.commutator_comm]
      simpa only [E] using e.2
    obtain ⟨q, hqQ, hq⟩ :=
      (mem_commSub_iff (T := Q) (a := u) hQ (by simpa [pow_two] using hu2) hNQ).1 hsub
    refine ⟨?_, ?_, ?_⟩
    · have h := (mul_commutator_mem_D_inter_S hD hN htri h4 hno (q := q) hqQ).1
      rwa [← hq] at h
    · exact ((Commute.refl u).mul_right (hcommE e)).symm
    · intro h
      apply he
      apply Subtype.ext
      have h' := congrArg (fun x : G => u⁻¹ * x) h
      simpa [mul_assoc] using h'
  have hm1 : u * (e1 : G) ∈ commSet D u := key e1 he1ne
  have hm2 : u * (e2 : G) ∈ commSet D u := key e2 he2ne
  have hm3 : u * (e3 : G) ∈ commSet D u := key e3 he3ne
  have hAu : u * (e1 : G) * u = (e1 : G) := by
    rw [(hcommE e1).eq, mul_assoc, hu2, mul_one]
  have hAB : (u * (e1 : G)) * (u * (e2 : G)) = (e1 : G) * (e2 : G) := by
    rw [← mul_assoc (u * (e1 : G)) u (e2 : G), hAu]
  have hprod : (u * (e1 : G)) * (u * (e2 : G)) * (u * (e3 : G)) = u := by
    rw [hAB]
    have hcu12 : Commute u ((e1 : G) * (e2 : G)) := (hcommE e1).mul_right (hcommE e2)
    rw [← mul_assoc ((e1 : G) * (e2 : G)) u (e3 : G), ← hcu12.eq, mul_assoc,
      ← he3val, he3sq, mul_one]
  have hmem : (u * (e1 : G)) * (u * (e2 : G)) * (u * (e3 : G)) ∈
      Subgroup.closure (commSet D u) :=
    Subgroup.mul_mem _
      (Subgroup.mul_mem _ (Subgroup.subset_closure hm1) (Subgroup.subset_closure hm2))
      (Subgroup.subset_closure hm3)
  rwa [hprod] at hmem

end CFSG.OddTranspositions
