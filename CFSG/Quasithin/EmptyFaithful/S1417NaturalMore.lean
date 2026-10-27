module

public import CFSG.Quasithin.EmptyFaithful.S1417Natural

public section

namespace CFSG.Quasithin

namespace S1417

open Matrix

theorem SL2_center : ∀ s : SL2, (∀ t : SL2, s * t = t * s) → s = 1 := by decide

theorem SL2_cent_three : ∀ l x : SL2, x ^ 3 = 1 → x ≠ 1 → l * x = x * l →
    l = 1 ∨ l = x ∨ l = x⁻¹ := by decide

theorem SL2_normalizes_three : ∀ l x : SL2, x ^ 3 = 1 → x ≠ 1 →
    l * x * l⁻¹ = x ∨ l * x * l⁻¹ = x⁻¹ := by decide

theorem SL2_inv_ne : ∀ x : SL2, x ^ 3 = 1 → x ≠ 1 → x⁻¹ ≠ x := by decide

def vecOf : Fin 3 → (Fin 2 → ZMod 2) := ![![1, 0], ![0, 1], ![1, 1]]

def labelOf (v : Fin 2 → ZMod 2) : Fin 3 :=
  if v = ![1, 0] then 0 else if v = ![0, 1] then 1 else 2

def permOf (M : SL2) (i : Fin 3) : Fin 3 :=
  labelOf ((M : Matrix (Fin 2) (Fin 2) (ZMod 2)) *ᵥ vecOf i)

theorem permOf_bijective : ∀ M : SL2, Function.Bijective (permOf M) := by decide

theorem permOf_mul : ∀ (M N : SL2) (i : Fin 3), permOf (M * N) i = permOf M (permOf N i) := by
  decide

theorem permOf_one : ∀ i : Fin 3, permOf 1 i = i := by decide

theorem permOf_injective : ∀ M N : SL2, (∀ i, permOf M i = permOf N i) → M = N := by decide

noncomputable def slToPerm : SL2 →* Equiv.Perm (Fin 3) where
  toFun M := Equiv.ofBijective (permOf M) (permOf_bijective M)
  map_one' := Equiv.ext fun i => permOf_one i
  map_mul' M N := Equiv.ext fun i => permOf_mul M N i

theorem slToPerm_injective : Function.Injective slToPerm := fun M N h =>
  permOf_injective M N fun i => congrArg (fun f : Equiv.Perm (Fin 3) => f i) h

theorem card_perm_three : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  decide

noncomputable def slEquivPerm : SL2 ≃* Equiv.Perm (Fin 3) :=
  MulEquiv.ofBijective slToPerm
    ⟨slToPerm_injective, (Function.Injective.bijective_of_nat_card_le slToPerm_injective
      (by rw [card_SL2, card_perm_three])).2⟩

section Natural

variable {W : Type*} [CommGroup W] {L : Subgroup (MulAut W)} {U : Subgroup W}

theorem nonempty_equiv_perm (hN : ActsAsNaturalL2 L U) :
    Nonempty (↥L ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨e, -, -⟩ := hN
  exact ⟨e.trans slEquivPerm⟩

theorem eq_one_of_central (hN : ActsAsNaturalL2 L U) {l : MulAut W} (hl : l ∈ L)
    (hc : ∀ l' ∈ L, l * l' = l' * l) : l = 1 := by
  obtain ⟨e, -, -⟩ := hN
  have h1 : e ⟨l, hl⟩ = 1 := by
    refine SL2_center _ fun t => ?_
    obtain ⟨l', hl'⟩ : ∃ l' : ↥L, e l' = t := ⟨e.symm t, by simp⟩
    rw [← hl', ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc l' l'.2)
  have h2 : (⟨l, hl⟩ : L) = 1 := e.injective (by rw [h1, map_one])
  exact congrArg Subtype.val h2

theorem apply_eq_of_commute (hN : ActsAsNaturalL2 L U) (hst : ∀ l ∈ L, ∀ u ∈ U, l u ∈ U)
    {g : MulAut W} (hg : g ∈ stabSub U) (hc : ∀ l ∈ L, g * l = l * g) :
    ∀ u ∈ U, g u = u := by
  obtain ⟨l, hl, hlg⟩ := exists_apply_eq_of_stab hN hst hg
  have hcentral : l = 1 := by
    refine eq_one_of_central hN hl fun l' hl' => ?_
    have h1 : (l * l')⁻¹ * (l' * l) = 1 := by
      refine eq_one_of_forall_apply_eq hN hst (L.mul_mem (L.inv_mem (L.mul_mem hl hl'))
        (L.mul_mem hl' hl)) fun u hu => ?_
      have e1 : (l' * l) u = (l * l') u := by
        have a1 : (l' * l) u = l' (g u) := by
          show l' (l u) = l' (g u)
          rw [hlg u hu]
        have a2 : (l * l') u = l' (g u) := by
          show l (l' u) = l' (g u)
          rw [hlg _ (hst l' hl' u hu)]
          exact congrArg (fun φ : MulAut W => φ u) (hc l' hl')
        rw [a1, a2]
      rw [MulAut.mul_apply, e1]
      simp
    exact inv_mul_eq_one.mp h1
  intro u hu
  rw [← hlg u hu, hcentral, MulAut.one_apply]

end Natural

end S1417

end CFSG.Quasithin
