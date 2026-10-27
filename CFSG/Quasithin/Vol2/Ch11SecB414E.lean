module

public import CFSG.Quasithin.Vol2.Ch11SecB414D
public import CFSG.Quasithin.Vol2.Ch11SecB414C

public section

namespace CFSG.Quasithin.H13.Ch4.B414

open CFSG.QuasithinUnique.Setup.X7a CFSG.Semidihedral.Principal
open CFSG.QuasithinUnique.Setup.X7 (matRep matRep_apply matMap matMap_apply)
open scoped MatrixGroups Matrix

variable {F : Type} [Field F] [CharP F 2] [Fintype F] {U : Type} [AddCommGroup U]
  [Module (ZMod 2) U] (α β : Bool)

@[expose] def swapIdx (x : TIdx 2 (fun _ => α) (fun _ => β)) : TIdx 2 (fun _ => α) (fun _ => β) :=
  ![x 1, x 0]

theorem swapIdx_zero (x : TIdx 2 (fun _ => α) (fun _ => β)) : swapIdx α β x 0 = x 1 := rfl

theorem swapIdx_one (x : TIdx 2 (fun _ => α) (fun _ => β)) : swapIdx α β x 1 = x 0 := rfl

theorem swapIdx_swapIdx (x : TIdx 2 (fun _ => α) (fun _ => β)) :
    swapIdx α β (swapIdx α β x) = x := by
  funext i
  fin_cases i <;> rfl

@[expose] def swapEquiv : TIdx 2 (fun _ => α) (fun _ => β) ≃ TIdx 2 (fun _ => α) (fun _ => β) where
  toFun := swapIdx α β
  invFun := swapIdx α β
  left_inv := swapIdx_swapIdx α β
  right_inv := swapIdx_swapIdx α β

@[expose] def galInv (v : TIdx 2 (fun _ => α) (fun _ => β) → F) :
    TIdx 2 (fun _ => α) (fun _ => β) → F :=
  fun x => v (swapIdx α β x) ^ 2

omit [CharP F 2] in
theorem pow_four_eq (hF : Fintype.card F = 4) (z : F) : z ^ 4 = z := by
  rw [← hF]
  exact FiniteField.pow_card z

omit [Fintype F] in
theorem galInv_add (v w : TIdx 2 (fun _ => α) (fun _ => β) → F) :
    galInv α β (v + w) = galInv α β v + galInv α β w := by
  funext x
  simp only [galInv, Pi.add_apply]
  rw [add_pow_char]

omit [CharP F 2] [Fintype F] in
theorem galInv_smul (c : F) (v : TIdx 2 (fun _ => α) (fun _ => β) → F) :
    galInv α β (c • v) = c ^ 2 • galInv α β v := by
  funext x
  simp only [galInv, Pi.smul_apply, smul_eq_mul]
  exact mul_pow _ _ 2

omit [CharP F 2] in
theorem galInv_galInv (hF : Fintype.card F = 4) (v : TIdx 2 (fun _ => α) (fun _ => β) → F) :
    galInv α β (galInv α β v) = v := by
  funext x
  simp only [galInv, swapIdx_swapIdx, ← pow_mul]
  exact pow_four_eq hF _

theorem tensorRep_swapIdx (hF : Fintype.card F = 4) (g : SL(3, F))
    (x y : TIdx 2 (fun _ => α) (fun _ => β)) :
    tensorRep (F := F) F (fun _ => α) (fun _ => β) g (swapIdx α β x) (swapIdx α β y) ^ 2 =
      tensorRep (F := F) F (fun _ => α) (fun _ => β) g x y := by
  have h1 : ∀ r s, locRep F α β 1 g r s = locRep F α β 0 g r s ^ 2 := fun r s =>
    locRep_succ_sq F α β 0 g r s
  show tensorRepGen F _ _ g _ _ ^ 2 = tensorRepGen F _ _ g _ _
  rw [tensorRepGen_apply, tensorRepGen_apply, Fin.prod_univ_two, Fin.prod_univ_two]
  simp only [swapIdx_zero, swapIdx_one, Fin.val_zero, Fin.val_one]
  rw [h1, h1, mul_pow, ← pow_mul, pow_four_eq hF, mul_comm]

theorem galInv_mulVec (hF : Fintype.card F = 4) (g : SL(3, F))
    (v : TIdx 2 (fun _ => α) (fun _ => β) → F) :
    galInv α β (tensorRep (F := F) F (fun _ => α) (fun _ => β) g *ᵥ v) =
      tensorRep (F := F) F (fun _ => α) (fun _ => β) g *ᵥ galInv α β v := by
  funext x
  simp only [galInv, Matrix.mulVec, dotProduct]
  rw [sum_pow_char (p := 2), ← (swapEquiv α β).sum_comp]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [mul_pow]
  exact congrArg (· * _) (tensorRep_swapIdx α β hF g x y)

@[expose] def galInvHom : (TIdx 2 (fun _ => α) (fun _ => β) → F) →+
    (TIdx 2 (fun _ => α) (fun _ => β) → F) where
  toFun := galInv α β
  map_zero' := by
    funext x
    simp [galInv]
  map_add' := galInv_add α β

@[expose] def galFix : AddSubgroup (TIdx 2 (fun _ => α) (fun _ => β) → F) :=
  AddMonoidHom.ker (galInvHom α β - AddMonoidHom.id _)

omit [Fintype F] in
theorem mem_galFix {v : TIdx 2 (fun _ => α) (fun _ => β) → F} :
    v ∈ galFix α β ↔ galInv α β v = v := by
  rw [galFix, AddMonoidHom.mem_ker, AddMonoidHom.sub_apply, sub_eq_zero]
  rfl

theorem false_of_injective_stable (hF : Fintype.card F = 4)
    {ρ : Representation (ZMod 2) SL(3, F) U} (hirr : ρ.IsIrreducible)
    {H : (TIdx 2 (fun _ => α) (fun _ => β) → F) →+ U}
    (hH : ∀ g v, H (tensorRep (F := F) F (fun _ => α) (fun _ => β) g *ᵥ v) = ρ g (H v))
    (hinj : Function.Injective H) : False := by
  classical
  obtain ⟨ω, hω0, hω1⟩ := exists_ne_zero_ne_one hF
  have hωω := sq_eq_add_one hF hω0 hω1
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  let x₀ : TIdx 2 (fun _ => α) (fun _ => β) := fun _ => ⟨0, B42SL3.locDim_pos α β⟩
  let v₀ : TIdx 2 (fun _ => α) (fun _ => β) → F := Pi.single x₀ 1
  have hv₀ : v₀ ≠ 0 := fun h => by simpa [v₀] using congrFun h x₀
  have htop : ¬ ∀ v : TIdx 2 (fun _ => α) (fun _ => β) → F, galInv α β v = v := by
    intro h
    have h1 := congrFun (h (ω • v₀)) x₀
    rw [galInv_smul, h v₀] at h1
    simp only [v₀, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h1
    exact one_ne_zero (α := F) (by linear_combination h1 - hωω)
  have hbot : ∃ v : TIdx 2 (fun _ => α) (fun _ => β) → F, galInv α β v = v ∧ v ≠ 0 := by
    by_cases h1 : v₀ + galInv α β v₀ = 0
    · refine ⟨ω • v₀ + galInv α β (ω • v₀), ?_, fun h3 => ?_⟩
      · rw [galInv_add, galInv_galInv α β hF, add_comm]
      · have hs : galInv α β v₀ = v₀ := by
          rw [eq_neg_of_add_eq_zero_right h1]
          funext x
          exact CharTwo.neg_eq _
        have h4 := congrFun h3 x₀
        rw [galInv_smul, hs] at h4
        simp only [v₀, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one,
          Pi.zero_apply] at h4
        exact one_ne_zero (α := F) (by linear_combination h4 - hωω - ω * h2)
    · exact ⟨v₀ + galInv α β v₀, by rw [galInv_add, galInv_galInv α β hF, add_comm], h1⟩
  have hB : ∀ g, ∀ u ∈ (galFix α β).map H, ρ g u ∈ (galFix α β).map H := by
    rintro g _ ⟨v, hv, rfl⟩
    refine ⟨_, ?_, hH g v⟩
    rw [SetLike.mem_coe, mem_galFix] at hv ⊢
    rw [galInv_mulVec α β hF, hv]
  rcases addSubgroup_eq_bot_or_top hirr _ hB with h | h
  · obtain ⟨v, hv, hv0⟩ := hbot
    have h3 : H v ∈ (galFix α β).map H := ⟨v, (mem_galFix α β).mpr hv, rfl⟩
    rw [h, AddSubgroup.mem_bot] at h3
    exact hv0 (hinj (h3.trans (map_zero H).symm))
  · apply htop
    intro v
    have h3 : H v ∈ (galFix α β).map H := by
      rw [h]
      exact AddSubgroup.mem_top _
    obtain ⟨w, hw, hwv⟩ := h3
    rw [← hinj hwv]
    exact (mem_galFix α β).mp hw

theorem false_of_stable_label (hF : Fintype.card F = 4) [Finite U]
    {ρ : Representation (ZMod 2) SL(3, F) U} (hirr : ρ.IsIrreducible)
    {H : (TIdx 2 (fun _ => α) (fun _ => β) → F) →+ U}
    (hH : ∀ g v, H (tensorRep (F := F) F (fun _ => α) (fun _ => β) g *ᵥ v) = ρ g (H v))
    (hsurj : Function.Surjective H) {ω : Fˣ} (hω : orderOf ω = 3)
    (hdiv : ∃ m, Nat.card U = Nat.card {u // ρ (dT 1 ω) u = u} * 16 ^ m)
    (hc : ∀ m, Fintype.card (TIdx 2 (fun _ => α) (fun _ => β)) ≠
      Fintype.card {x : TIdx 2 (fun _ => α) (fun _ => β) //
        3 ∣ locE α β (x 0) + 2 * locE α β (x 1)} + 4 * m) : False := by
  by_cases hinj : Function.Injective H
  · exact false_of_injective_stable α β hF hirr hH hinj
  let _ : DecidableEq F := Classical.decEq F
  have : Nontrivial U := ((CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff ρ).mp hirr).1
  have hF' : Fintype.card F = 2 ^ 2 := by
    rw [hF]
    norm_num
  have hR := ((tensorRep_absolutely_irreducible_and_distinct F hF' (by norm_num)).1
    (fun _ => α) (fun _ => β)).1
  obtain ⟨hU, hC⟩ := card_of_not_injective hF hR hH hsurj hinj (dT 1 ω)
  rw [tensorRep_dT, card_fixed_diagonal, card_eig_one α β hω, hF] at hC
  set c := Fintype.card {x : TIdx 2 (fun _ => α) (fun _ => β) //
    3 ∣ locE α β (x 0) + 2 * locE α β (x 1)} with hcdef
  have hCU : Nat.card {u // ρ (dT 1 ω) u = u} = 2 ^ c := by
    apply Nat.pow_left_injective (two_ne_zero)
    simp only
    rw [hC, ← pow_mul, mul_comm, pow_mul]
    norm_num
  obtain ⟨m, hm⟩ := hdiv
  rw [hU, hCU, show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul, ← pow_add] at hm
  exact hc m (Nat.pow_right_injective (le_refl 2) hm)

end CFSG.Quasithin.H13.Ch4.B414
