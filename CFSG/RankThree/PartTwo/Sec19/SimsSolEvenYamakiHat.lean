module

import CFSG.Mathlib.GroupTheory.PermCommute
public import CFSG.ClassicalInvolution.Sp62Rec.I1.WrModel
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixDefs
public import Certificates.Data.YamakiPres

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven.Yamaki

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Sp62Rec.I1 CFSG.ClassicalInvolution.Solomon73.Yamaki
open CFSG.Quasithin.C116Two CFSG.QuasithinUnique CFSG.Open

@[expose] def hatToWr : YamakiHat →* Wr 6 where
  toFun x := ⟨((Multiplicative.toAdd x.left : evenWeight 6) : Fin 6 → ZMod 2), x.right⟩
  map_one' := rfl
  map_mul' x y := by
    refine Wr.ext (funext fun i => ?_) rfl
    show ((Multiplicative.toAdd (x * y).left : evenWeight 6) : Fin 6 → ZMod 2) i =
      ((Multiplicative.toAdd x.left : evenWeight 6) : Fin 6 → ZMod 2) i +
        ((Multiplicative.toAdd y.left : evenWeight 6) : Fin 6 → ZMod 2) (x.right.symm i)
    rw [SemidirectProduct.mul_left, toAdd_mul, AddSubgroup.coe_add, Pi.add_apply]
    rfl

theorem hatToWr_vec (x : YamakiHat) :
    (hatToWr x).vec = ((Multiplicative.toAdd x.left : evenWeight 6) : Fin 6 → ZMod 2) := rfl

theorem hatToWr_injective : Function.Injective hatToWr := by
  intro x y h
  have hv := congrArg Wr.vec h
  have hp := congrArg Wr.perm h
  rw [hatToWr_vec, hatToWr_vec] at hv
  exact SemidirectProduct.ext (Multiplicative.toAdd.injective (Subtype.ext hv)) hp

theorem hatToWr_mem (x : YamakiHat) : hatToWr x ∈ Wsub :=
  AddMonoidHom.mem_ker.mp (Multiplicative.toAdd x.left).2

theorem exists_hatToWr_eq {a : Wr 6} (ha : a ∈ Wsub) : ∃ x : YamakiHat, hatToWr x = a :=
  ⟨⟨Multiplicative.ofAdd ⟨a.vec, AddMonoidHom.mem_ker.mpr ha⟩, a.perm⟩, rfl⟩

@[expose] noncomputable def hatEquivWsub : YamakiHat ≃* ↥Wsub :=
  MulEquiv.ofBijective (hatToWr.codRestrict Wsub hatToWr_mem)
    ⟨fun x y h => hatToWr_injective (congrArg Subtype.val h), fun a => by
      obtain ⟨x, hx⟩ := exists_hatToWr_eq a.2
      exact ⟨x, Subtype.ext hx⟩⟩

theorem ofPerm_mem_Wsub (τ : Equiv.Perm (Fin 6)) : ofPerm τ ∈ Wsub := by
  show ∑ i, (ofPerm τ).vec i = 0
  simp [ofPerm]

theorem eq_one_or_eq_allOnes_of_central {a : ↥Wsub} (h : ∀ b : ↥Wsub, a * b = b * a) :
    a = 1 ∨ a = ⟨Wr.allOnes 6, allOnes_mem_Wsub⟩ := by
  have hc : ∀ τ : Equiv.Perm (Fin 6), (a : Wr 6) * ofPerm τ = ofPerm τ * (a : Wr 6) := fun τ =>
    congrArg Subtype.val (h ⟨ofPerm τ, ofPerm_mem_Wsub τ⟩)
  have hperm : (a : Wr 6).perm = 1 :=
    CFSG.perm_eq_one_of_forall_commute (by simp) fun τ => congrArg Wr.perm (hc τ)
  have hvec : ∀ τ : Equiv.Perm (Fin 6), ∀ i, (a : Wr 6).vec i = (a : Wr 6).vec (τ.symm i) := by
    intro τ i
    have h1 := congrArg (fun b : Wr 6 => b.vec i) (hc τ)
    simp only [Wr.mul_vec, ofPerm, hperm] at h1
    simpa using h1
  have hconst : ∀ i, (a : Wr 6).vec i = (a : Wr 6).vec 0 := fun i => by
    have := hvec (Equiv.swap 0 i) i
    rwa [Equiv.symm_swap, Equiv.swap_apply_right] at this
  have h01 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases h01 ((a : Wr 6).vec 0) with h0 | h0
  · left
    refine Subtype.ext (Wr.ext (funext fun i => ?_) hperm)
    rw [hconst i, h0]
    rfl
  · right
    refine Subtype.ext (Wr.ext (funext fun i => ?_) hperm)
    rw [hconst i, h0]
    rfl

theorem eq_allOnes_of_central {a : ↥Wsub} (h : ∀ b : ↥Wsub, a * b = b * a) (ha : a ≠ 1) :
    a = ⟨Wr.allOnes 6, allOnes_mem_Wsub⟩ :=
  (eq_one_or_eq_allOnes_of_central h).resolve_left ha

end CFSG.RankThree.PartTwo.Sec19.SolEven.Yamaki
