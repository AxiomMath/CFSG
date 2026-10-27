module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.RankThree.PartOne.N143

open Equiv Equiv.Perm

@[expose] def gens12 : Fin 5 → Perm (Fin 12) :=
  ![swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 4 5 * swap 6 7, swap 4 6 * swap 5 7,
    swap 8 9 * swap 10 11]

@[expose] def vecMap12 (v : Fin 5 → ZMod 2) : Perm (Fin 12) :=
  gens12 0 ^ (v 0).val * gens12 1 ^ (v 1).val * gens12 2 ^ (v 2).val * gens12 3 ^ (v 3).val *
    gens12 4 ^ (v 4).val

theorem vecMap12_zero : vecMap12 0 = 1 := by decide +kernel

theorem vecMap12_add : ∀ v w : Fin 5 → ZMod 2, vecMap12 (v + w) = vecMap12 v * vecMap12 w := by
  decide +kernel

theorem vecMap12_sign : ∀ v : Fin 5 → ZMod 2, sign (vecMap12 v) = 1 := by decide +kernel

theorem vecMap12_injective : Function.Injective vecMap12 := by
  have key : ∀ v w : Fin 5 → ZMod 2,
      (vecMap12 v 0, vecMap12 v 4, vecMap12 v 8) = (vecMap12 w 0, vecMap12 w 4, vecMap12 w 8) →
        v = w := by decide +kernel
  intro v w h
  exact key v w (by rw [h])

@[expose] def vecHom12 : Multiplicative (Fin 5 → ZMod 2) →* Perm (Fin 12) where
  toFun v := vecMap12 v.toAdd
  map_one' := vecMap12_zero
  map_mul' v w := vecMap12_add v.toAdd w.toAdd

@[expose] def castEquiv12 (n : ℕ) (hn : 12 ≤ n) : Fin 12 ≃ {x : Fin n // x.val < 12} where
  toFun a := ⟨Fin.castLE hn a, a.2⟩
  invFun x := ⟨x.1.val, x.2⟩
  left_inv a := by ext; simp
  right_inv x := by ext; simp

@[expose] def vecHomAlt (n : ℕ) (hn : 12 ≤ n) :
    Multiplicative (Fin 5 → ZMod 2) →* alternatingGroup (Fin n) :=
  ((Equiv.Perm.extendDomainHom (castEquiv12 n hn)).comp vecHom12).codRestrict
    (alternatingGroup (Fin n)) fun v => by
      rw [mem_alternatingGroup]
      change sign (Equiv.Perm.extendDomain (vecMap12 v.toAdd) (castEquiv12 n hn)) = 1
      rw [sign_extendDomain]
      exact vecMap12_sign _

theorem vecHomAlt_injective (n : ℕ) (hn : 12 ≤ n) : Function.Injective (vecHomAlt n hn) := by
  intro v w h
  have h1 : (Equiv.Perm.extendDomainHom (castEquiv12 n hn)) (vecHom12 v) =
      (Equiv.Perm.extendDomainHom (castEquiv12 n hn)) (vecHom12 w) :=
    congrArg Subtype.val h
  have h2 := Equiv.Perm.extendDomainHom_injective (castEquiv12 n hn) h1
  exact Multiplicative.toAdd.injective (vecMap12_injective h2)

theorem exists_isElementaryAbelian_two_pow_five {n : ℕ} (hn : 12 ≤ n) :
    ∃ U : Subgroup (alternatingGroup (Fin n)), IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ 5 := by
  have hinj := vecHomAlt_injective n hn
  let e : Multiplicative (Fin 5 → ZMod 2) ≃* (vecHomAlt n hn).range :=
    MonoidHom.ofInjective hinj
  refine ⟨(vecHomAlt n hn).range, ?_, ?_⟩
  · refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }
    · obtain ⟨x, rfl⟩ := e.surjective a
      obtain ⟨y, rfl⟩ := e.surjective b
      rw [← map_mul, ← map_mul, mul_comm]
    · rw [← Monoid.exponent_eq_of_mulEquiv e]
      refine Monoid.exponent_dvd_of_forall_pow_eq_one fun v => ?_
      apply Multiplicative.toAdd.injective
      funext i
      have h2 : (2 : ZMod 2) = 0 := by decide
      simp [h2]
  · rw [← Nat.card_congr e.toEquiv, Nat.card_congr (Multiplicative.toAdd : Multiplicative _ ≃ _),
      Nat.card_fun]
    simp

end CFSG.RankThree.PartOne.N143
