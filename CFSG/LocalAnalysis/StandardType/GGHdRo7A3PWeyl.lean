module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7A3Basic
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallModelsAAux

public section

namespace CFSG.StandardType.HdRo7A3

open CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Aux

variable {p m : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
  {θ : (Fin m → ZMod p) →ₗ[ZMod p] V} {z : V}

private noncomputable def hdRo7A3PWeylAux_permFun (hfr : A3Frame p m θ z) (hpm : p ∣ m)
    (σ : Equiv.Perm (Fin m)) : V ≃ₗ[ZMod p] V :=
  Classical.choose (a3_exists_perm hfr hpm σ)

private theorem hdRo7A3PWeylAux_permFun_spec (hfr : A3Frame p m θ z) (hpm : p ∣ m)
    (σ : Equiv.Perm (Fin m)) :
    (∀ u ∈ a3Aug p m, hdRo7A3PWeylAux_permFun hfr hpm σ (θ u) =
      θ (fun i => u (σ.symm i))) ∧ hdRo7A3PWeylAux_permFun hfr hpm σ z = z :=
  Classical.choose_spec (a3_exists_perm hfr hpm σ)

private theorem hdRo7A3PWeylAux_permFun_one (hfr : A3Frame p m θ z) (hpm : p ∣ m) :
    hdRo7A3PWeylAux_permFun hfr hpm 1 = 1 := by
  have h1 := hdRo7A3PWeylAux_permFun_spec hfr hpm (1 : Equiv.Perm (Fin m))
  refine a3P_ext hfr (σ := 1) h1.1 h1.2 ?_ ?_
  · intro u _
    rfl
  · rfl

private theorem hdRo7A3PWeylAux_permFun_mul (hfr : A3Frame p m θ z) (hpm : p ∣ m)
    (σ τ : Equiv.Perm (Fin m)) :
    hdRo7A3PWeylAux_permFun hfr hpm (σ * τ) =
      hdRo7A3PWeylAux_permFun hfr hpm σ * hdRo7A3PWeylAux_permFun hfr hpm τ := by
  have hστ := hdRo7A3PWeylAux_permFun_spec hfr hpm (σ * τ)
  have hσ := hdRo7A3PWeylAux_permFun_spec hfr hpm σ
  have hτ := hdRo7A3PWeylAux_permFun_spec hfr hpm τ
  refine a3P_ext hfr (σ := σ * τ) hστ.1 hστ.2 ?_ ?_
  · intro u hu
    rw [LinearEquiv.mul_apply, hτ.1 u hu, hσ.1 _ (a3Aug_perm hu τ.symm)]
    rfl
  · rw [LinearEquiv.mul_apply, hτ.2, hσ.2]

private noncomputable def hdRo7A3PWeylAux_permHom (hfr : A3Frame p m θ z) (hpm : p ∣ m) :
    Equiv.Perm (Fin m) →* (V ≃ₗ[ZMod p] V) where
  toFun := hdRo7A3PWeylAux_permFun hfr hpm
  map_one' := hdRo7A3PWeylAux_permFun_one hfr hpm
  map_mul' := hdRo7A3PWeylAux_permFun_mul hfr hpm

private noncomputable def hdRo7A3PWeylAux_permHomH (hfr : A3Frame p m θ z) (hpm : p ∣ m)
    (H : Subgroup (V ≃ₗ[ZMod p] V)) (hH : ∀ a, a ∈ H ↔ A3P p m θ z a) :
    Equiv.Perm (Fin m) →* H :=
  (hdRo7A3PWeylAux_permHom hfr hpm).codRestrict H fun σ =>
    (hH _).mpr ⟨σ, (hdRo7A3PWeylAux_permFun_spec hfr hpm σ).1,
      (hdRo7A3PWeylAux_permFun_spec hfr hpm σ).2⟩

private theorem hdRo7A3PWeylAux_permHomH_apply (hfr : A3Frame p m θ z) (hpm : p ∣ m)
    (H : Subgroup (V ≃ₗ[ZMod p] V)) (hH : ∀ a, a ∈ H ↔ A3P p m θ z a)
    (σ : Equiv.Perm (Fin m)) :
    ((hdRo7A3PWeylAux_permHomH hfr hpm H hH σ : H) : V ≃ₗ[ZMod p] V) =
      hdRo7A3PWeylAux_permFun hfr hpm σ :=
  rfl

private theorem hdRo7A3PWeylAux_permHomH_injective (hfr : A3Frame p m θ z) (hpm : p ∣ m)
    (hm : 5 ≤ m) (H : Subgroup (V ≃ₗ[ZMod p] V)) (hH : ∀ a, a ∈ H ↔ A3P p m θ z a) :
    Function.Injective (hdRo7A3PWeylAux_permHomH hfr hpm H hH) := by
  intro σ τ hστ
  apply a3_perm_unique hfr hm
  intro u hu
  have hσ := (hdRo7A3PWeylAux_permFun_spec hfr hpm σ).1 u hu
  have hτ := (hdRo7A3PWeylAux_permFun_spec hfr hpm τ).1 u hu
  have hcongr : hdRo7A3PWeylAux_permFun hfr hpm σ (θ u) =
      hdRo7A3PWeylAux_permFun hfr hpm τ (θ u) := by
    have h := congrArg (fun e : H => (e : V ≃ₗ[ZMod p] V) (θ u)) hστ
    simpa only [hdRo7A3PWeylAux_permHomH_apply] using h
  rw [hσ, hτ] at hcongr
  exact hcongr

private theorem hdRo7A3PWeylAux_permHomH_surjective (hfr : A3Frame p m θ z) (hpm : p ∣ m)
    (H : Subgroup (V ≃ₗ[ZMod p] V)) (hH : ∀ a, a ∈ H ↔ A3P p m θ z a) :
    Function.Surjective (hdRo7A3PWeylAux_permHomH hfr hpm H hH) := by
  rintro ⟨a, ha⟩
  obtain ⟨σ, hσ, haz⟩ := (hH a).mp ha
  refine ⟨σ, ?_⟩
  apply Subtype.ext
  rw [hdRo7A3PWeylAux_permHomH_apply]
  exact a3P_ext hfr (hdRo7A3PWeylAux_permFun_spec hfr hpm σ).1
    (hdRo7A3PWeylAux_permFun_spec hfr hpm σ).2 hσ haz

private theorem hdRo7A3PWeylAux_permHomH_swap (hp : p = 3) (hfr : A3Frame p m θ z)
    (hpm : p ∣ m) (hm : 3 ≤ m) (H : Subgroup (V ≃ₗ[ZMod p] V))
    (hH : ∀ a, a ∈ H ↔ A3P p m θ z a) {i j : Fin m} (hij : i ≠ j) :
    GGLinRefl ((hdRo7A3PWeylAux_permHomH hfr hpm H hH (Equiv.swap i j) : H) :
      V ≃ₗ[ZMod p] V) := by
  obtain ⟨t, _, ht, htz, _, _, _, htref⟩ := a3_transp hp hfr hpm hm hij
  have heq : t = ((hdRo7A3PWeylAux_permHomH hfr hpm H hH (Equiv.swap i j) : H) :
      V ≃ₗ[ZMod p] V) := by
    rw [hdRo7A3PWeylAux_permHomH_apply]
    exact a3P_ext hfr (σ := Equiv.swap i j) ht htz
      (hdRo7A3PWeylAux_permFun_spec hfr hpm (Equiv.swap i j)).1
      (hdRo7A3PWeylAux_permFun_spec hfr hpm (Equiv.swap i j)).2
  rw [← heq]
  exact htref

end Aux

theorem a3_pWeyl_holds : A3PWeylLeaf := by
  intro p _ hp m hm h3 V _ _ θ z hfr H hH
  subst hp
  have hpm : 3 ∣ m := h3
  obtain ⟨n, hm_eq⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  subst hm_eq
  have hn : 1 ≤ n := by omega
  let e : Equiv.Perm (Fin (n + 1)) ≃* H :=
    MulEquiv.ofBijective (hdRo7A3PWeylAux_permHomH hfr hpm H hH)
      ⟨hdRo7A3PWeylAux_permHomH_injective hfr hpm (by omega) H hH,
        hdRo7A3PWeylAux_permHomH_surjective hfr hpm H hH⟩
  have hrefl : ∀ k : Fin n,
      GGLinRefl ((e (Equiv.swap k.castSucc k.succ) : H) : V ≃ₗ[ZMod 3] V) := by
    intro k
    have hne : k.castSucc ≠ k.succ := by
      intro h
      have hv : (k.castSucc : ℕ) = k.succ := congrArg Fin.val h
      simp only [Fin.val_castSucc, Fin.val_succ] at hv
      omega
    exact hdRo7A3PWeylAux_permHomH_swap rfl hfr hpm (by omega) H hH hne
  exact Small.hdRo7SmAAux_linWeyl_of_perm H n hn e hrefl

end CFSG.StandardType.HdRo7A3
