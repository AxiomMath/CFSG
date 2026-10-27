module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenInvariantOddPSubgroupCentralized
import Mathlib.GroupTheory.GroupAction.CardCommute
import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.Tactic
import all Mathlib.GroupTheory.Perm.Cycle.Factors

namespace CFSG
end CFSG
open CFSG

/-!
# The involution count in `A₇`

All involutions of `A₇` form one conjugacy class.  The distinguished double
transposition has centralizer of order `24`, so its conjugacy class, and hence
the full involution set, has cardinality `2520 / 24 = 105`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

private abbrev A7 := alternatingGroup (Fin 7)

private theorem a7_card : Nat.card A7 = 2520 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card]
  decide

private theorem a7t_perm_cycleType :
    (a7t : Equiv.Perm (Fin 7)).cycleType = {2, 2} := by
  decide

private theorem a7t_perm_centralizer_card :
    Nat.card (Subgroup.centralizer
      ({(a7t : Equiv.Perm (Fin 7))} : Set (Equiv.Perm (Fin 7)))) = 48 := by
  rw [Equiv.Perm.nat_card_centralizer, a7t_perm_cycleType]
  norm_num

private theorem a7t_centralizer_card :
    Nat.card (Subgroup.centralizer ({a7t} : Set A7)) = 24 := by
  let C : Subgroup (Equiv.Perm (Fin 7)) :=
    Subgroup.centralizer ({(a7t : Equiv.Perm (Fin 7))} : Set (Equiv.Perm (Fin 7)))
  let A : Subgroup (Equiv.Perm (Fin 7)) := alternatingGroup (Fin 7)
  have hAindex : A.index = 2 := alternatingGroup.index_eq_two
  have hcC : (Equiv.swap (4 : Fin 7) 5) ∈ C := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyP : y = (a7t : Equiv.Perm (Fin 7)) := by simpa using hy
    subst y
    decide
  have hcA : (Equiv.swap (4 : Fin 7) 5) ∉ A := by
    intro h
    change Equiv.Perm.sign (Equiv.swap (4 : Fin 7) 5) = 1 at h
    norm_num [Equiv.Perm.sign_swap] at h
    all_goals exact (by decide : (4 : Fin 7) ≠ 5) h
  let D : Subgroup (Equiv.Perm (Fin 7)) := Lattice.inf C A
  have hrel : D.relIndex C = 2 := by
    rw [Subgroup.relIndex_eq_two_iff]
    refine ⟨Equiv.swap (4 : Fin 7) 5, hcC, ?_⟩
    intro b hbC
    have hbcC : b * Equiv.swap (4 : Fin 7) 5 ∈ C := C.mul_mem hbC hcC
    by_cases hbA : b ∈ A
    · right
      constructor
      · exact Subgroup.mem_inf.mpr ⟨hbC, hbA⟩
      · intro hbc
        have hbcA : b * Equiv.swap (4 : Fin 7) 5 ∈ A :=
          (Subgroup.mem_inf.mp hbc).2
        have hiff : b * Equiv.swap (4 : Fin 7) 5 ∈ A ↔
            (b ∈ A ↔ Equiv.swap (4 : Fin 7) 5 ∈ A) :=
          Subgroup.mul_mem_iff_of_index_two hAindex
        have hbnot : ¬ b ∈ A := by
          intro hbA'
          exact hcA ((hiff.mp hbcA).1 hbA')
        exact hbnot hbA
    · left
      constructor
      · exact Subgroup.mem_inf.mpr ⟨hbcC, by
          exact (Subgroup.mul_mem_iff_of_index_two hAindex).2
            (iff_of_false hbA hcA)⟩
      · intro hbD
        exact hbA ((Subgroup.mem_inf.mp hbD).2)
  have hrel' : (D.subgroupOf C).index = 2 := hrel
  have hperm : Nat.card C = 48 := a7t_perm_centralizer_card
  have hDleC : D ≤ C := inf_le_left
  have hcardSub : Nat.card (D.subgroupOf C) = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDleC).toEquiv
  have hcardC : Nat.card D * 2 = Nat.card C := by
    have h := Subgroup.card_mul_index (D.subgroupOf C)
    rw [hcardSub, hrel'] at h
    exact h
  have hcard24 : Nat.card D = 24 := by omega
  have hmap : (Subgroup.centralizer ({a7t} : Set A7)).map A7.subtype = D := by
    ext p
    constructor
    · rintro ⟨x, hxC, rfl⟩
      constructor
      · change (x : Equiv.Perm (Fin 7)) ∈ C
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hyP : y = (a7t : Equiv.Perm (Fin 7)) := by simpa using hy
        subst y
        have hcomm := (Subgroup.mem_centralizer_iff.mp hxC) a7t (by simp)
        exact congrArg Subtype.val hcomm
      · exact x.2
    · rintro ⟨hpC, hpA⟩
      refine ⟨⟨p, hpA⟩, ?_, rfl⟩
      have hx : (⟨p, hpA⟩ : A7) ∈ Subgroup.centralizer ({a7t} : Set A7) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hyA : y = a7t := by simpa using hy
        subst y
        have hcomm := (Subgroup.mem_centralizer_iff.mp hpC)
          (a7t : Equiv.Perm (Fin 7)) (by simp)
        exact Subtype.ext hcomm
      exact hx
  have hcardMap : Nat.card (Subgroup.centralizer ({a7t} : Set A7)) =
      Nat.card ((Subgroup.centralizer ({a7t} : Set A7)).map A7.subtype) := by
    exact Nat.card_congr (Subgroup.equivMapOfInjective
      (Subgroup.centralizer ({a7t} : Set A7)) A7.subtype
        A7.subtype_injective).toEquiv
  rw [hcardMap, hmap, hcard24]

private theorem card_conjClass_eq_centralizer_index (x : A7) :
    Nat.card (ConjClasses.mk x).carrier =
      (Subgroup.centralizer ({x} : Set A7)).index := by
  classical
  let : Fintype A7 := Fintype.ofFinite A7
  let : Fintype (ConjClasses.mk x).carrier := Fintype.ofFinite _
  let : Fintype (MulAction.stabilizer (ConjAct A7) x) := Fintype.ofFinite _
  have hst := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    (ConjAct A7) x
  have hst' : Fintype.card (ConjClasses.mk x).carrier *
      Fintype.card (MulAction.stabilizer (ConjAct A7) x) = Fintype.card A7 := by
    simpa [ConjAct.orbit_eq_carrier_conjClasses] using hst
  let e : MulAction.stabilizer (ConjAct A7) x ≃
      Subgroup.centralizer ({x} : Set A7) :=
    { toFun := fun y =>
        ⟨ConjAct.ofConjAct y.1, by
          rw [Subgroup.mem_centralizer_iff]
          intro z hz
          simp at hz
          rw [hz]
          have hy : y.1 • x = x := y.2
          rw [ConjAct.smul_def] at hy
          exact (mul_inv_eq_iff_eq_mul.mp (by simpa [mul_assoc] using hy)).symm⟩
      invFun := fun z =>
        ⟨ConjAct.toConjAct (z : A7), by
          change ConjAct.toConjAct (z : A7) • x = x
          rw [ConjAct.toConjAct_smul]
          exact mul_inv_eq_of_eq_mul
            ((Subgroup.mem_centralizer_iff.mp z.2) x (by simp)).symm⟩
      left_inv := by intro y; apply Subtype.ext; rfl
      right_inv := by intro z; apply Subtype.ext; rfl }
  have hC : Fintype.card (MulAction.stabilizer (ConjAct A7) x) =
      Nat.card (Subgroup.centralizer ({x} : Set A7)) := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_congr e
  have hN : (Subgroup.centralizer ({x} : Set A7)).index *
      Fintype.card (MulAction.stabilizer (ConjAct A7) x) = Fintype.card A7 := by
    rw [hC]
    rw [← Nat.card_eq_fintype_card]
    exact Subgroup.index_mul_card (Subgroup.centralizer ({x} : Set A7))
  rw [Nat.card_eq_fintype_card]
  exact Nat.mul_right_cancel
    (by positivity : 0 < Fintype.card (MulAction.stabilizer (ConjAct A7) x)) (by
      rw [← hN] at hst'
      exact hst')

/-- `A₇` has exactly `105` involutions. -/
public theorem aSeven_involutions_card :
    Nat.card {x : alternatingGroup (Fin 7) // IsInvolution x} = 105 := by
  classical
  let I : Type := {x : A7 // IsInvolution x}
  let O : Type := MulAction.orbit (ConjAct A7) a7t
  have ha7t : IsInvolution (a7t : A7) := by
    constructor <;> decide
  let eIO : I ≃ O :=
    { toFun := fun x =>
        ⟨x.1, by
          rcases aSeven_involutions_conjugate x.1 a7t x.2 ha7t with ⟨g, hg⟩
          refine MulAction.mem_orbit_iff.mpr ⟨ConjAct.toConjAct g⁻¹, ?_⟩
          rw [ConjAct.smul_def]
          change g⁻¹ * a7t * g = x.1
          rw [← hg]
          group⟩
      invFun := fun y =>
        ⟨y.1, by
          rcases MulAction.mem_orbit_iff.mp y.2 with ⟨g, hg⟩
          rw [ConjAct.smul_def] at hg
          constructor
          · intro h1
            apply ha7t.1
            have hy1 : (ConjAct.ofConjAct g) * a7t *
                (ConjAct.ofConjAct g)⁻¹ = 1 := by
              simpa [h1] using hg
            calc
              a7t = (ConjAct.ofConjAct g)⁻¹ *
                  ((ConjAct.ofConjAct g) * a7t *
                    (ConjAct.ofConjAct g)⁻¹) * (ConjAct.ofConjAct g) := by group
              _ = 1 := by rw [hy1]; simp
          · rw [← hg]
            calc
              ((ConjAct.ofConjAct g) * a7t *
                  (ConjAct.ofConjAct g)⁻¹) ^ 2 =
                (ConjAct.ofConjAct g) * a7t ^ 2 *
                  (ConjAct.ofConjAct g)⁻¹ := by
                    simp only [pow_two]
                    group
              _ = 1 := by rw [ha7t.2]; simp⟩
      left_inv := by intro x; rfl
      right_inv := by intro y; apply Subtype.ext; rfl }
  have hIO : Nat.card I = Nat.card O := Nat.card_congr eIO
  have hO : Nat.card O = 105 := by
    change Nat.card (MulAction.orbit (ConjAct A7) a7t) = 105
    rw [ConjAct.orbit_eq_carrier_conjClasses]
    rw [card_conjClass_eq_centralizer_index]
    have hidx : (Subgroup.centralizer ({(a7t : A7)} : Set A7)).index = 105 := by
      have hmul := Subgroup.index_mul_card
        (Subgroup.centralizer ({(a7t : A7)} : Set A7))
      rw [a7t_centralizer_card, a7_card] at hmul
      omega
    exact (Subgroup.index_eq_card _).symm.trans hidx
  simpa [I] using hIO.trans hO

end CFSG.GorensteinWalter
