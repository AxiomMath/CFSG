module

public import CFSG.OddTranspositions.O4PairTenInvolutions
public import CFSG.GroupTheory.SymmetricFiveTranspositions
public import Mathlib.Order.Defs.Unbundled

public section

namespace CFSG.OddTranspositions.QZ

open CFSG.PSL2Table

private def f25tDecEq (a b : F25t) : Decidable (a = b) :=
  if h1 : a.a = b.a then
    if h2 : a.b = b.b then
      isTrue (F25t.ext h1 h2)
    else
      isFalse fun h => h2 (by rw [h])
  else
    isFalse fun h => h1 (by rw [h])

private instance (priority := 2000) f25tDecEqInst : DecidableEq F25t := f25tDecEq

theorem commute_x_iff (i j : Fin 10) :
    Commute (x i) (x j) ↔
      X i * X j = X j * X i ∨ X i * X j = -(X j * X i) := by
  have h1 : x i * x j = CFSG.PSL2Table.mk (X i * X j) := by simp [x, map_mul]
  have h2 : x j * x i = CFSG.PSL2Table.mk (X j * X i) := by simp [x, map_mul]
  show x i * x j = x j * x i ↔ _
  rw [h1, h2, CFSG.PSL2Table.mk_eq_mk_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr (by rw [h, neg_neg])
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr (by rw [h, neg_neg])

private def commuteXDecidable (i j : Fin 10) : Decidable (Commute (x i) (x j)) :=
  decidable_of_iff (X i * X j = X j * X i ∨ X i * X j = -(X j * X i))
    (commute_x_iff i j).symm

private instance instDecidableRelCommuteX :
    DecidableRel (fun a b : Fin 10 => Commute (x a) (x b)) :=
  fun a b => commuteXDecidable a b

theorem card_commuting_others (i : Fin 10) :
    Nat.card {j : Fin 10 // j ≠ i ∧ Commute (x i) (x j)} = 3 := by
  rw [Nat.card_eq_fintype_card]
  fin_cases i <;> decide +kernel

def ncTen (a b : Fin 10) : Prop :=
  a ≠ b ∧ ¬ Commute (x a) (x b)

private instance instDecidableRelNcTen : DecidableRel ncTen :=
  fun a b => by
    change Decidable (a ≠ b ∧ ¬ Commute (x a) (x b))
    infer_instance

theorem ncTen_symm : Symmetric ncTen := by
  intro a b h
  change a ≠ b ∧ ¬ Commute (x a) (x b) at h
  change b ≠ a ∧ ¬ Commute (x b) (x a)
  exact ⟨h.1.symm, fun hc => h.2 hc.symm⟩

theorem ncTen_reachable (i : Fin 10) : Relation.ReflTransGen ncTen 0 i := by
  fin_cases i
  · exact Relation.ReflTransGen.refl
  · exact (Relation.ReflTransGen.single (by decide +kernel : ncTen 0 6)).tail
      (by decide +kernel : ncTen 6 1)
  · exact (Relation.ReflTransGen.single (by decide +kernel : ncTen 0 3)).tail
      (by decide +kernel : ncTen 3 2)
  · exact Relation.ReflTransGen.single (by decide +kernel : ncTen 0 3)
  · exact Relation.ReflTransGen.single (by decide +kernel : ncTen 0 4)
  · exact (Relation.ReflTransGen.single (by decide +kernel : ncTen 0 3)).tail
      (by decide +kernel : ncTen 3 5)
  · exact Relation.ReflTransGen.single (by decide +kernel : ncTen 0 6)
  · exact Relation.ReflTransGen.single (by decide +kernel : ncTen 0 7)
  · exact Relation.ReflTransGen.single (by decide +kernel : ncTen 0 8)
  · exact Relation.ReflTransGen.single (by decide +kernel : ncTen 0 9)

theorem ncTen_connected (i j : Fin 10) : Relation.ReflTransGen ncTen i j :=
  (CFSG.GroupTheory.reflTransGen_symm (fun a b h => ncTen_symm h)
    (ncTen_reachable i)).trans (ncTen_reachable j)

end CFSG.OddTranspositions.QZ
