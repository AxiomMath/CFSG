module

public import CFSG.Quasithin.Vol2.Ch10SecQ6WrS5b
public import CFSG.Quasithin.Vol2.Ch10SecDWreathD

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

namespace C10P06

open Equiv

@[expose] def wrSub (H : Subgroup (Perm (Fin 5))) : Subgroup SymFiveWrTwo where
  carrier := {g | ∀ q, g.left q ∈ H}
  one_mem' := fun _ => H.one_mem
  mul_mem' {a b} ha hb q := by
    change a.left q * b.left (a.right⁻¹ * q) ∈ H
    exact H.mul_mem (ha q) (hb _)
  inv_mem' {a} ha q := by
    change (a.left (a.right * q))⁻¹ ∈ H
    exact H.inv_mem (ha _)

theorem wrT_mem_wrSub (H : Subgroup (Perm (Fin 5))) : wrT ∈ wrSub H := fun _ => H.one_mem

theorem wrIota_mem_wrSub {H : Subgroup (Perm (Fin 5))} {σ : Perm (Fin 5)} (hσ : σ ∈ H)
    (q : Multiplicative (ZMod 2)) : wrIota q σ ∈ wrSub H := by
  intro x
  change (Pi.mulSingle q σ : Multiplicative (ZMod 2) → Perm (Fin 5)) x ∈ H
  rw [Pi.mulSingle_apply]
  split_ifs
  · exact hσ
  · exact H.one_mem

abbrev S0 : Subgroup SymFiveWrTwo := wrSub D8

abbrev Y0 : Subgroup SymFiveWrTwo := wrSub S4

theorem card_wrSub (H : Subgroup (Perm (Fin 5))) : Nat.card (wrSub H) = Nat.card H ^ 2 * 2 := by
  let e : wrSub H ≃ (Multiplicative (ZMod 2) → H) × Multiplicative (ZMod 2) :=
    { toFun := fun g => (fun q => ⟨g.1.left q, g.2 q⟩, g.1.right)
      invFun := fun p => ⟨⟨fun q => (p.1 q : Perm (Fin 5)), p.2⟩, fun q => (p.1 q).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_fun]
  have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_eq_fintype_card]
    rfl
  rw [h2]

theorem card_S0 : Nat.card S0 = 128 := by
  rw [card_wrSub, card_D8]
  norm_num

theorem card_wreath : Nat.card SymFiveWrTwo = 28800 := by
  rw [RegularWreathProduct.card, card_perm_five]
  have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_eq_fintype_card]
    rfl
  rw [h2]
  norm_num

theorem isPGroup_S0 : IsPGroup 2 S0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsPGroup.of_card (n := 7) (by rw [card_S0]; norm_num)

theorem not_two_dvd_index_S0 : ¬ 2 ∣ S0.index := by
  have h := S0.card_mul_index
  rw [card_S0, card_wreath] at h
  have h225 : S0.index = 225 := by omega
  rw [h225]
  norm_num

theorem eq_or_eq_zs_mul (q q' : Multiplicative (ZMod 2)) : q' = q ∨ q' = zs * q := by
  revert q q'
  decide

theorem zs_mul_zs_mul (q : Multiplicative (ZMod 2)) : zs * (zs * q) = q := by
  revert q
  decide

abbrev coordSub (H : Subgroup SymFiveWrTwo) (q : Multiplicative (ZMod 2)) :
    Subgroup (Perm (Fin 5)) :=
  H.comap (wrIota q)

theorem coordSub_zs_mul {H : Subgroup SymFiveWrTwo} (hT : wrT ∈ H) (q : Multiplicative (ZMod 2)) :
    coordSub H (zs * q) = coordSub H q := by
  ext σ
  simp only [Subgroup.mem_comap]
  constructor
  · intro h
    have h1 := H.mul_mem (H.mul_mem hT h) (H.inv_mem hT)
    rwa [wrT_conj, zs_mul_zs_mul] at h1
  · intro h
    rw [← wrT_conj]
    exact H.mul_mem (H.mul_mem hT h) (H.inv_mem hT)

theorem exists_base {H : Subgroup SymFiveWrTwo} (hT : wrT ∈ H) {h : SymFiveWrTwo} (hh : h ∈ H) :
    ∃ h' ∈ H, h'.right = 1 ∧ h'.left = h.left := by
  rcases zmod2_cases h.right with hr | hr
  · exact ⟨h, hh, hr, rfl⟩
  · refine ⟨h * wrT, H.mul_mem hh hT, ?_, rfl⟩
    rw [RegularWreathProduct.mul_right, hr]
    decide

end C10P06

end CFSG.Quasithin.Vol2.Ch10.SecD
