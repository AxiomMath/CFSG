module

public import CFSG.Quasithin.Vol2.Ch10SecEA5
public import CFSG.Quasithin.Vol2.Ch10SecES5

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv

variable {W : Type*} [CommGroup W]

theorem apply_mem_commV_of_commute {K : Subgroup (MulAut W)} {g : MulAut W}
    (hg : ∀ k ∈ K, g * k = k * g) {w : W} (hw : w ∈ commV K) : g w ∈ commV K := by
  induction hw using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨k, hk, v, rfl⟩ := hy
    rw [map_mul, map_inv]
    have h1 : g (k v) = k (g v) := by
      have := congrArg (fun φ : MulAut W => φ v) (hg k hk)
      simpa only [MulAut.mul_apply] using this
    rw [h1]
    exact Subgroup.subset_closure ⟨k, hk, g v, rfl⟩
  | one => rw [map_one]; exact Subgroup.one_mem _
  | mul a b _ _ ha hb => rw [map_mul]; exact Subgroup.mul_mem _ ha hb
  | inv a _ ha => rw [map_inv]; exact Subgroup.inv_mem _ ha

section Data

variable {K : Subgroup (MulAut W)} (θ : ↥K ≃* Perm (Fin 5))
  (β : ↥(commV K) ≃* Multiplicative (evenWeight 5))

theorem coord_apply
    (hβ : ∀ (h : ↥K) (u : ↥(commV K)) (hu : (h : MulAut W) (u : W) ∈ commV K) (i : Fin 5),
      ((Multiplicative.toAdd (β ⟨(h : MulAut W) u, hu⟩) : evenWeight 5) : Fin 5 → ZMod 2) i =
        ((Multiplicative.toAdd (β u) : evenWeight 5) : Fin 5 → ZMod 2) ((θ h)⁻¹ i))
    (k : ↥K) (u : ↥(commV K)) :
    ((Multiplicative.toAdd (β ⟨(k : MulAut W) u, commV_invariant K _ k.2 _ u.2⟩) :
      evenWeight 5) : Fin 5 → ZMod 2) =
      pact (θ k) ((Multiplicative.toAdd (β u) : evenWeight 5) : Fin 5 → ZMod 2) :=
  funext fun i => hβ k u _ i

variable {θ β} in
theorem fix_commV_of_commute
    (hβ : ∀ (h : ↥K) (u : ↥(commV K)) (hu : (h : MulAut W) (u : W) ∈ commV K) (i : Fin 5),
      ((Multiplicative.toAdd (β ⟨(h : MulAut W) u, hu⟩) : evenWeight 5) : Fin 5 → ZMod 2) i =
        ((Multiplicative.toAdd (β u) : evenWeight 5) : Fin 5 → ZMod 2) ((θ h)⁻¹ i))
    {g : MulAut W} (hg : ∀ k ∈ K, g * k = k * g) {w : W} (hw : w ∈ commV K) : g w = w := by
  let g' : ↥(commV K) →* ↥(commV K) :=
    ((g.toMonoidHom).comp (commV K).subtype).codRestrict (commV K)
      fun u => apply_mem_commV_of_commute hg u.2
  have hg' : ∀ u : ↥(commV K), ((g' u : ↥(commV K)) : W) = g u := fun _ => rfl
  let F : Multiplicative (evenWeight 5) →* Multiplicative (evenWeight 5) :=
    β.toMonoidHom.comp (g'.comp β.symm.toMonoidHom)
  let f : evenWeight 5 → evenWeight 5 := fun e => Multiplicative.toAdd (F (Multiplicative.ofAdd e))
  have hadd : ∀ x y, f (x + y) = f x + f y := fun x y => by
    simp only [f, ofAdd_add, map_mul, toAdd_mul]
  have hinj : Function.Injective f := by
    intro x y h
    have h1 : F (Multiplicative.ofAdd x) = F (Multiplicative.ofAdd y) :=
      Multiplicative.toAdd.injective h
    simp only [F, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h1
    have h2 := β.injective h1
    have h3 : g ((β.symm (Multiplicative.ofAdd x) : ↥(commV K)) : W) =
        g ((β.symm (Multiplicative.ofAdd y) : ↥(commV K)) : W) := by
      rw [← hg', ← hg', h2]
    have h4 := Subtype.ext (g.injective h3)
    exact Multiplicative.ofAdd.injective (β.symm.injective h4)
  have hcomm : ∀ σ : Perm (Fin 5), Perm.sign σ = 1 → ∀ e, f (vact σ e) = vact σ (f e) := by
    intro σ _ e
    set k : ↥K := θ.symm σ
    set u : ↥(commV K) := β.symm (Multiplicative.ofAdd e)
    have hku : β ⟨(k : MulAut W) u, commV_invariant K _ k.2 _ u.2⟩ =
        Multiplicative.ofAdd (vact σ e) := by
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      rw [toAdd_ofAdd, coord_apply θ β hβ k u]
      simp [u, k, vact]
    have hgk : g ((k : MulAut W) u) = (k : MulAut W) (g u) := by
      have := congrArg (fun φ : MulAut W => φ (u : W)) (hg k k.2)
      simpa only [MulAut.mul_apply] using this
    show Multiplicative.toAdd (β (g' (β.symm (Multiplicative.ofAdd (vact σ e))))) =
      vact σ (Multiplicative.toAdd (β (g' u)))
    rw [← hku, MulEquiv.symm_apply_apply]
    have e1 : g' ⟨(k : MulAut W) u, commV_invariant K _ k.2 _ u.2⟩ =
        ⟨(k : MulAut W) (g' u), commV_invariant K _ k.2 _ (g' u).2⟩ := Subtype.ext hgk
    rw [e1]
    apply Subtype.ext
    rw [coord_apply θ β hβ k (g' u)]
    simp [k, vact]
  have hid := rigid f hadd hinj hcomm
  have h1 := hid (Multiplicative.toAdd (β ⟨w, hw⟩))
  simp only [f, F, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ofAdd_toAdd,
    MulEquiv.symm_apply_apply] at h1
  have h2 := β.injective (Multiplicative.toAdd.injective h1)
  exact congrArg Subtype.val h2

variable {θ β} in
theorem exists_mem_commV_oTwoUpper
    (hβ : ∀ (h : ↥K) (u : ↥(commV K)) (hu : (h : MulAut W) (u : W) ∈ commV K) (i : Fin 5),
      ((Multiplicative.toAdd (β ⟨(h : MulAut W) u, hu⟩) : evenWeight 5) : Fin 5 → ZMod 2) i =
        ((Multiplicative.toAdd (β u) : evenWeight 5) : Fin 5 → ZMod 2) ((θ h)⁻¹ i))
    {i j : Fin 5} (hij : i ≠ j) :
    ∃ (w : W) (hw : w ∈ commV K), w ∈ commV (oTwoUpper K) ∧
      ((Multiplicative.toAdd (β ⟨w, hw⟩) : evenWeight 5) : Fin 5 → ZMod 2) =
        Pi.single i 1 + Pi.single j 1 := by
  obtain ⟨σ, hσ3, hσ1, z, hz, he⟩ := exists_comm_pair i j hij
  set k : ↥K := θ.symm σ
  have hk : (k : MulAut W) ∈ oTwoUpper K := by
    refine mem_oTwoUpper_of_odd k.2 ?_
    rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq θ, show θ k = σ from θ.apply_symm_apply σ]
    exact odd_orderOf_of_pow_three hσ3 hσ1
  set u : ↥(commV K) := β.symm (Multiplicative.ofAdd ⟨z, hz⟩)
  have hku := commV_invariant K _ k.2 _ u.2
  refine ⟨(k : MulAut W) u * (u : W)⁻¹, (commV K).mul_mem hku ((commV K).inv_mem u.2),
    Subgroup.subset_closure ⟨k, hk, u, rfl⟩, ?_⟩
  have e1 : (⟨(k : MulAut W) u * (u : W)⁻¹, (commV K).mul_mem hku ((commV K).inv_mem u.2)⟩ :
      ↥(commV K)) = ⟨(k : MulAut W) u, hku⟩ * u⁻¹ := rfl
  rw [e1, map_mul, map_inv, toAdd_mul, toAdd_inv, AddSubgroup.coe_add, AddSubgroup.coe_neg,
    coord_apply θ β hβ k u]
  have hz' : ((Multiplicative.toAdd (β u) : evenWeight 5) : Fin 5 → ZMod 2) = z := by simp [u]
  rw [hz', show θ k = σ from θ.apply_symm_apply σ, ← he]
  congr 1
  funext l
  exact ZMod.neg_eq_self_mod_two _

end Data

end CFSG.Quasithin.Vol2.Ch10.SecE
