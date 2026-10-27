module

public import CFSG.Permutation.FiveTransitive.TwoGroupQuadCommutatorImage
public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG

namespace FiveTransitive.TwoGroupQuadCommutatorEight

private theorem card_commutator_congr
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    Nat.card (commutator G) = Nat.card (commutator H) := by
  have hm : (commutator G).map e.toMonoidHom = commutator H := by
    rw [map_commutator_eq,MonoidHom.range_eq_top.mpr e.surjective]
    rfl
  rw [← hm,Subgroup.card_map_of_injective e.injective]

private theorem exists_noncommutative_eight :
    ∃ D : Subgroup (Equiv.Perm (Fin 4)), Nat.card D = 8 ∧
      IsPGroup 2 D ∧ ¬ IsMulCommutative D := by
  let d : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3
  let a : Equiv.Perm (Fin 4) := Equiv.swap 0 1
  let b : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3
  let D := Subgroup.centralizer ({d} : Set (Equiv.Perm (Fin 4)))
  have ht : d.cycleType = {2,2} := Equiv.Perm.cycleType_swap_mul_swap_of_nodup (by decide)
  have hD : Nat.card D = 8 := by
    rw [Equiv.Perm.nat_card_centralizer,ht]
    norm_num [Nat.factorial]
  have ha : a ∈ D := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    decide
  have hb : b ∈ D := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    decide
  have hab : a * b ≠ b * a := by decide
  refine ⟨D,hD,IsPGroup.of_card (n := 3) hD,?_⟩
  intro hc
  exact hab (congrArg Subtype.val (isMulCommutative_iff.mp hc (⟨a,ha⟩ : D) ⟨b,hb⟩))

private theorem canonical_commutator_card_eq_two
    (Q : Subgroup (Equiv.Perm (Fin 4))) (hQcard : Nat.card Q = 8) :
    Nat.card (commutator Q) = 2 := by
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hQ : IsPGroup 2 Q := IsPGroup.of_card (n := 3) hQcard
  obtain ⟨D,hDcard,hD,hDnoncomm⟩ := exists_noncommutative_eight
  obtain ⟨S,hQS⟩ := hQ.exists_le_sylow
  obtain ⟨T,hDT⟩ := hD.exists_le_sylow
  have hQS' : Q = (S : Subgroup (Equiv.Perm (Fin 4))) := by
    apply Subgroup.eq_of_le_of_card_ge hQS
    rw [hQcard]
    exact TwoGroupQuadCommutatorImage.card_le_eight _ (by simp) S.isPGroup'
  have hDT' : D = (T : Subgroup (Equiv.Perm (Fin 4))) := by
    apply Subgroup.eq_of_le_of_card_ge hDT
    rw [hDcard]
    exact TwoGroupQuadCommutatorImage.card_le_eight _ (by simp) T.isPGroup'
  let e : Q ≃* D := (MulEquiv.subgroupCongr hQS').trans
    ((Sylow.equiv S T).trans (MulEquiv.subgroupCongr hDT'.symm))
  have hne : commutator D ≠ ⊥ := fun hh => hDnoncomm ((commutator_eq_bot_iff D).mp hh)
  have hlow := (Subgroup.one_lt_card_iff_ne_bot (commutator D)).mpr hne
  have hhigh := TwoGroupQuadCommutatorImage.commutator_card_le_two Q (by simp) hQ
  have he := card_commutator_congr e
  omega

theorem commutator_card_eq_two
    {Y : Type*} [Finite Y] (hY : Nat.card Y = 4)
    (Q : Subgroup (Equiv.Perm Y)) (hQcard : Nat.card Q = 8) :
    Nat.card (commutator Q) = 2 := by
  classical
  let _ : Fintype Y := Fintype.ofFinite _
  let e : Y ≃ Fin 4 := Fintype.equivFinOfCardEq (by rwa [← Nat.card_eq_fintype_card])
  let R := Q.map e.permCongrHom.toMonoidHom
  let f : Q ≃* R := Q.equivMapOfInjective e.permCongrHom.toMonoidHom e.permCongrHom.injective
  have hR : Nat.card R = 8 := (Nat.card_congr f.toEquiv).symm.trans hQcard
  rw [card_commutator_congr f]
  exact canonical_commutator_card_eq_two R hR

end FiveTransitive.TwoGroupQuadCommutatorEight

end CFSG
