module

import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Open.LocalVocabulary

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.MinimalAction

variable {G : Type*} [Group G]

theorem isElemAbelian_sup {q : ℕ} {A B : Subgroup G} (hA : IsElemAbelian q A)
    (hB : IsElemAbelian q B) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    IsElemAbelian q (A ⊔ B) := CFSG.Open.IsElemAbelian.sup_of_commute hA hB hAB

theorem isElemAbelian_zpowers {q : ℕ} {g : G} (hg : g ^ q = 1) :
    IsElemAbelian q (Subgroup.zpowers g) := CFSG.Open.isElemAbelian_zpowers hg

theorem card_le_four_of_forall_ne_eight [Finite G]
    (hno : ∀ E : Subgroup G, IsElemAbelian 2 E → Nat.card E ≠ 8) :
    ∀ E : Subgroup G, IsElemAbelian 2 E → Nat.card E ≤ 4 := by
  intro E hE
  have hp : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
  by_contra hlt
  have hk3 : 3 ≤ k := by
    by_contra h
    have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card Nat.prime_two hp
    (n := 3) (by rw [hk]; exact Nat.pow_le_pow_right (by norm_num) hk3)
  have hle : K.map E.subtype ≤ E := Subgroup.map_subtype_le K
  have := hE.1
  refine hno (K.map E.subtype) ⟨isMulCommutative_anti hle, fun x hx => hE.2 x (hle hx)⟩ ?_
  rw [Subgroup.card_map_of_injective E.subtype_injective, hK]
  norm_num

end CFSG.SignalizerFunctorTheorem.MinimalAction
