module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import Mathlib.GroupTheory.GroupAction.CardCommute

namespace CFSG
end CFSG
open CFSG

/-!
# Counting a single involution conjugacy class
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

public theorem card_conjClass_eq_centralizer_index_local
    {G : Type u} [Group G] [Finite G] (x : G) :
    Nat.card (ConjClasses.mk x).carrier =
      (Subgroup.centralizer ({x} : Set G)).index := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Fintype (ConjClasses.mk x).carrier := Fintype.ofFinite _
  let : Fintype (MulAction.stabilizer (ConjAct G) x) := Fintype.ofFinite _
  have hst := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    (ConjAct G) x
  have hst' : Fintype.card (ConjClasses.mk x).carrier *
      Fintype.card (MulAction.stabilizer (ConjAct G) x) = Fintype.card G := by
    simpa [ConjAct.orbit_eq_carrier_conjClasses] using hst
  let e : MulAction.stabilizer (ConjAct G) x ≃
      Subgroup.centralizer ({x} : Set G) :=
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
        ⟨ConjAct.toConjAct (z : G), by
          change ConjAct.toConjAct (z : G) • x = x
          rw [ConjAct.toConjAct_smul]
          exact mul_inv_eq_of_eq_mul
            ((Subgroup.mem_centralizer_iff.mp z.2) x (by simp)).symm⟩
      left_inv := by intro y; apply Subtype.ext; rfl
      right_inv := by intro z; apply Subtype.ext; rfl }
  have hC : Fintype.card (MulAction.stabilizer (ConjAct G) x) =
      Nat.card (Subgroup.centralizer ({x} : Set G)) := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_congr e
  have hN : (Subgroup.centralizer ({x} : Set G)).index *
      Fintype.card (MulAction.stabilizer (ConjAct G) x) = Fintype.card G := by
    rw [hC]
    rw [← Nat.card_eq_fintype_card]
    exact Subgroup.index_mul_card (Subgroup.centralizer ({x} : Set G))
  rw [Nat.card_eq_fintype_card]
  exact Nat.mul_right_cancel
    (by positivity : 0 < Fintype.card (MulAction.stabilizer (ConjAct G) x)) (by
      rw [← hN] at hst'
      exact hst')

/-- If every involution of a finite group is conjugate to `t`, then the
involution set has cardinality equal to the index of `C_G(t)`. -/
public theorem involutions_card_eq_centralizer_index_of_fusion
    {G : Type u} [Group G] [Finite G]
    (t : G) (ht : IsInvolution t)
    (hfuse : ∀ x : G, IsInvolution x →
      ∃ g : G, g * x * g⁻¹ = t) :
    Nat.card {x : G // IsInvolution x} =
      (Subgroup.centralizer ({t} : Set G)).index := by
  classical
  let I : Type u := {x : G // IsInvolution x}
  let O : Type u := MulAction.orbit (ConjAct G) t
  let eIO : I ≃ O :=
    { toFun := fun x =>
        ⟨x.1, by
          rcases hfuse x.1 x.2 with ⟨g, hg⟩
          refine MulAction.mem_orbit_iff.mpr ⟨ConjAct.toConjAct g⁻¹, ?_⟩
          rw [ConjAct.smul_def]
          simp only [ConjAct.ofConjAct_toConjAct]
          simp only [inv_inv]
          rw [← hg]
          group⟩
      invFun := fun y =>
        ⟨y.1, by
          rcases MulAction.mem_orbit_iff.mp y.2 with ⟨g, hg⟩
          rw [ConjAct.smul_def] at hg
          constructor
          · intro h1
            apply ht.1
            have hy1 : (ConjAct.ofConjAct g) * t *
                (ConjAct.ofConjAct g)⁻¹ = 1 := by
              simpa [h1] using hg
            calc
              t = (ConjAct.ofConjAct g)⁻¹ *
                  ((ConjAct.ofConjAct g) * t *
                    (ConjAct.ofConjAct g)⁻¹) * (ConjAct.ofConjAct g) := by group
              _ = 1 := by rw [hy1]; simp
          · rw [← hg]
            calc
              ((ConjAct.ofConjAct g) * t *
                  (ConjAct.ofConjAct g)⁻¹) ^ 2 =
                (ConjAct.ofConjAct g) * t ^ 2 *
                  (ConjAct.ofConjAct g)⁻¹ := by
                    simp only [pow_two]
                    group
              _ = 1 := by rw [ht.2]; simp⟩
      left_inv := by intro x; rfl
      right_inv := by intro y; apply Subtype.ext; rfl }
  have hIO : Nat.card I = Nat.card O := Nat.card_congr eIO
  have hO : Nat.card O =
      (Subgroup.centralizer ({t} : Set G)).index := by
    change Nat.card (MulAction.orbit (ConjAct G) t) = _
    rw [ConjAct.orbit_eq_carrier_conjClasses]
    rw [card_conjClass_eq_centralizer_index_local]
  simpa [I] using hIO.trans hO

end CFSG.GorensteinWalter
