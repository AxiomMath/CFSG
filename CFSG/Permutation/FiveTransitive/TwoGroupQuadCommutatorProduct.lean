module

public import CFSG.Permutation.FiveTransitive.TwoGroupQuadCommutatorEight
public import Mathlib.GroupTheory.Commutator.Finite

public section

namespace CFSG

namespace FiveTransitive.TwoGroupQuadCommutatorProduct

private theorem card_commutator_pi
    {ι : Type*} [Fintype ι] (G : ι → Type*) [∀ i, Group (G i)] :
    Nat.card (commutator (∀ i, G i)) = ∏ i, Nat.card (commutator (G i)) := by
  classical
  have he : commutator (∀ i, G i) = Subgroup.pi Set.univ (fun i => commutator (G i)) := by
    have h := Subgroup.commutator_pi_pi_of_finite (fun i => (⊤ : Subgroup (G i)))
      (fun i => (⊤ : Subgroup (G i)))
    simpa only [Subgroup.pi_top,commutator_def] using h
  rw [he]
  let e : (Subgroup.pi Set.univ (fun i => commutator (G i))) ≃ (∀ i, commutator (G i)) :=
    { toFun := fun x i => ⟨x.val i,(Subgroup.mem_pi Set.univ).mp x.property i (Set.mem_univ i)⟩
      invFun := fun x => ⟨fun i => (x i).val,(Subgroup.mem_pi Set.univ).mpr (fun i _ => (x i).property)⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun x => rfl }
  rw [Nat.card_congr e,Nat.card_pi]

theorem commutator_card_ge_sixteen
    {A : Type*} {B : Fin 4 → Type*} [Finite A] [∀ i, Finite (B i)]
    (hA : Nat.card A = 2) (hB : ∀ i, Nat.card (B i) = 4)
    (Q : Subgroup (Equiv.Perm A × (∀ i, Equiv.Perm (B i))))
    (hQ : IsPGroup 2 Q) (hQcard : Nat.card Q = 8192) :
    16 ≤ Nat.card (commutator Q) := by
  classical
  let f0 : Q →* Equiv.Perm A :=
    { toFun := fun q => q.val.1
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let fi (i : Fin 4) : Q →* Equiv.Perm (B i) :=
    { toFun := fun q => q.val.2 i
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let R := f0.range × (∀ i, (fi i).range)
  let f : Q →* R :=
    { toFun := fun q => (f0.rangeRestrict q,fun i => (fi i).rangeRestrict q)
      map_one' := by apply Prod.ext; exact map_one _; funext i; exact map_one _
      map_mul' := by intro x y; apply Prod.ext; exact map_mul _ x y; funext i; exact map_mul _ x y }
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun r : R => r.1.val) he
    · funext i
      exact congrArg (fun r : R => (r.2 i).val) he
  have h0 : Nat.card f0.range ≤ 2 := by
    have hh := Nat.card_le_card_of_injective f0.range.subtype f0.range.subtype_injective
    rw [Nat.card_perm,hA] at hh
    simpa [Nat.factorial] using hh
  have hi (i : Fin 4) : Nat.card (fi i).range ≤ 8 :=
    TwoGroupQuadCommutatorImage.card_le_eight _ (hB i).le
      (hQ.of_surjective (fi i).rangeRestrict (fi i).rangeRestrict_surjective)
  have hpi : Nat.card (∀ i, (fi i).range) ≤ 4096 := by
    rw [Nat.card_pi]
    have hh := Finset.prod_le_prod (s := Finset.univ) (f := fun i => Nat.card (fi i).range)
      (g := fun _ : Fin 4 => 8) (fun i _ => hi i)
    simpa using hh
  have hlo := Nat.card_le_card_of_injective f hf
  have hR : Nat.card R = 8192 := by
    have hhi : Nat.card R ≤ 8192 := by
      change Nat.card (f0.range × (∀ i, (fi i).range)) ≤ 8192
      rw [Nat.card_prod]
      exact Nat.mul_le_mul h0 hpi
    rw [hQcard] at hlo
    omega
  have hpiEq : Nat.card (∀ i, (fi i).range) = 4096 := by
    change Nat.card (f0.range × (∀ i, (fi i).range)) = 8192 at hR
    rw [Nat.card_prod] at hR
    nlinarith
  have hiEq (i : Fin 4) : Nat.card (fi i).range = 8 := by
    by_contra hn
    have hh := Finset.prod_lt_prod₀ (s := Finset.univ)
      (f := fun j => Nat.card (fi j).range) (g := fun _ : Fin 4 => 8)
      (fun j _ => Nat.card_pos) (fun j _ => hi j)
      ⟨i,Finset.mem_univ i,by have := hi i; omega⟩
    rw [← Nat.card_pi] at hh
    norm_num at hh
    omega
  have hsurj : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    apply Subgroup.eq_top_of_card_eq
    change Nat.card (Set.range f) = Nat.card R
    rw [Nat.card_range_of_injective hf,hQcard,hR]
  let fp : Q →* (∀ i, (fi i).range) := (MonoidHom.snd _ _).comp f
  have hfp : Function.Surjective fp := by
    intro y
    obtain ⟨x,hx⟩ := hsurj (1,y)
    exact ⟨x,congrArg Prod.snd hx⟩
  have hderived : (commutator Q).map fp = commutator (∀ i, (fi i).range) := by
    rw [map_commutator_eq,MonoidHom.range_eq_top.mpr hfp]
    rfl
  have hc : Nat.card (commutator (∀ i, (fi i).range)) = 16 := by
    rw [card_commutator_pi]
    have he (i : Fin 4) : Nat.card (commutator (fi i).range) = 2 :=
      TwoGroupQuadCommutatorEight.commutator_card_eq_two (hB i) _ (hiEq i)
    simp only [he,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    norm_num
  have hd := (commutator Q).card_map_dvd fp
  rw [hderived,hc] at hd
  exact Nat.le_of_dvd Nat.card_pos hd

end FiveTransitive.TwoGroupQuadCommutatorProduct

end CFSG
