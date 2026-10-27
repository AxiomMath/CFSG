module

public import CFSG.Quasithin.H13.GoldschmidtC137L3Fin
public import CFSG.Quasithin.EmptyFaithful.S153E58C
public import CFSG.Quasithin.Background.Module
public import CFSG.Quasithin.Recognition.HSTypeModels
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyLinearBinary

public section

namespace CFSG.Quasithin.H13.U3.GC137

open CFSG.Quasithin CFSG.Quasithin.L3

variable {M : Type} [CommGroup M] (φ : M ≃* Multiplicative Vec)

include φ

@[expose] def crd (m : M) : Vec := Multiplicative.toAdd (φ m)

theorem crd_one : crd φ 1 = 0 := by simp [crd]

theorem crd_injective : Function.Injective (crd φ) := fun _ _ h =>
  φ.injective (Multiplicative.toAdd.injective h)

theorem crd_surjective : Function.Surjective (crd φ) := fun v =>
  ⟨φ.symm (Multiplicative.ofAdd v), by simp [crd]⟩

theorem crd_eq_zero_iff (m : M) : crd φ m = 0 ↔ m = 1 := by
  rw [← crd_one φ]
  exact (crd_injective φ).eq_iff

theorem crd_ne_zero {u : M} (hu : u ≠ 1) : crd φ u ≠ 0 :=
  fun h => hu ((crd_eq_zero_iff φ u).1 h)

@[expose] noncomputable def crdEquiv : M ≃ Vec :=
  Equiv.ofBijective (crd φ) ⟨crd_injective φ, crd_surjective φ⟩

theorem crdEquiv_apply (m : M) : crdEquiv φ m = crd φ m := rfl

@[expose] noncomputable def psi : MulAut M ≃* Γ :=
  ((MulAut.congr φ).trans (S153E58.mulAutPiEquivGL 3)).trans
    (CFSG.QuasithinUnique.Setup.Family.slEquivGL 3).symm

theorem act_psi (a : MulAut M) (m : M) : act (psi φ a) (crd φ m) = crd φ (a m) := by
  set γ : Γ := psi φ a with hγ
  have h1 : CFSG.QuasithinUnique.Setup.Family.slEquivGL 3 γ =
      S153E58.mulAutPiEquivGL 3 (MulAut.congr φ a) := by
    rw [hγ]
    exact MulEquiv.apply_symm_apply _ _
  have h2 := S153E58.mulAutPiEquivGL_symm_apply 3
    (CFSG.QuasithinUnique.Setup.Family.slEquivGL 3 γ) (φ m)
  have h1' : (S153E58.mulAutPiEquivGL 3).symm
      (CFSG.QuasithinUnique.Setup.Family.slEquivGL 3 γ) = MulAut.congr φ a := by
    rw [h1, MulEquiv.symm_apply_apply]
  rw [h1'] at h2
  have h3 : (MulAut.congr φ a) (φ m) = φ (a m) := by simp
  rw [h3] at h2
  have h4 := congrArg Multiplicative.toAdd h2
  simp only [toAdd_ofAdd] at h4
  exact h4.symm

theorem card_mulAut : Nat.card (MulAut M) = 168 := by
  rw [Nat.card_congr (psi φ).toEquiv]
  exact HSType.card_SL_three_two

theorem isSimpleGroup_mulAut : IsSimpleGroup (MulAut M) :=
  (MulEquiv.isSimpleGroup_congr (psi φ)).mpr HSType.isSimpleGroup_SL_three_two

@[expose] noncomputable def stabM (u : M) : Subgroup (MulAut M) :=
  (stabΓ (crd φ u)).comap (psi φ).toMonoidHom

theorem mem_stabM {u : M} {a : MulAut M} : a ∈ stabM φ u ↔ a u = u := by
  show act (psi φ a) (crd φ u) = crd φ u ↔ a u = u
  rw [act_psi]
  exact (crd_injective φ).eq_iff

@[expose] noncomputable def v4M (u : M) (hu : u ≠ 1) : Subgroup (MulAut M) :=
  (v4Γ (crd φ u) (crd_ne_zero φ hu)).comap (psi φ).toMonoidHom

theorem v4M_le_stabM (u : M) (hu : u ≠ 1) : v4M φ u hu ≤ stabM φ u :=
  Subgroup.comap_mono (v4Γ_le_stabΓ _ _)

theorem normal2_stabM {u : M} (hu : u ≠ 1) (N : Subgroup (MulAut M)) (hN : N ≤ stabM φ u)
    (hnorm : ∀ h ∈ stabM φ u, ∀ n ∈ N, h * n * h⁻¹ ∈ N) (hp : IsPGroup 2 N) (hne : N ≠ ⊥) :
    N = v4M φ u hu := by
  have h := normal2_stab_eq (crd φ u) (crd_ne_zero φ hu) (N.map (psi φ).toMonoidHom)
    (by
      rintro _ ⟨n, hn, rfl⟩
      exact hN hn)
    (by
      intro h hh n' hn'
      obtain ⟨n, hn, rfl⟩ := hn'
      obtain ⟨h₀, rfl⟩ := (psi φ).surjective h
      refine ⟨h₀ * n * h₀⁻¹, hnorm h₀ hh n hn, ?_⟩
      simp)
    (hp.of_equiv (N.equivMapOfInjective _ (psi φ).injective))
    (by rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ (psi φ).injective])
  calc N = (N.map (psi φ).toMonoidHom).comap (psi φ).toMonoidHom :=
        (Subgroup.comap_map_eq_self_of_injective (psi φ).injective N).symm
    _ = v4M φ u hu := by rw [h]; rfl

theorem card_v4M {u : M} (hu : u ≠ 1) : Nat.card (v4M φ u hu) = 4 := by
  rw [← card_v4Γ (crd φ u) (crd_ne_zero φ hu)]
  exact Nat.card_congr (Equiv.subtypeEquiv (psi φ).toEquiv (fun a => Iff.rfl))

theorem v4M_comm {u : M} {hu : u ≠ 1} {a b : MulAut M} (ha : a ∈ v4M φ u hu)
    (hb : b ∈ v4M φ u hu) : a * b = b * a := by
  apply (psi φ).injective
  rw [map_mul, map_mul]
  exact (AS_elem (crd φ u) (crd_ne_zero φ hu) _ ha _ hb).1

theorem v4M_sq {u : M} {hu : u ≠ 1} {a : MulAut M} (ha : a ∈ v4M φ u hu) : a ^ 2 = 1 := by
  apply (psi φ).injective
  rw [map_pow, map_one, pow_two]
  exact (AS_elem (crd φ u) (crd_ne_zero φ hu) _ ha _ ha).2

theorem isElemAbelian2_v4M (u : M) (hu : u ≠ 1) : IsElemAbelian2 (v4M φ u hu) :=
  ⟨fun _ ha _ hb => v4M_comm φ ha hb, fun _ ha => v4M_sq φ ha⟩

theorem v4M_conj_trans {u : M} {hu : u ≠ 1} {a b : MulAut M} (ha : a ∈ v4M φ u hu) (ha1 : a ≠ 1)
    (hb : b ∈ v4M φ u hu) (hb1 : b ≠ 1) : ∃ h ∈ stabM φ u, h * a * h⁻¹ = b := by
  obtain ⟨g, hg, hgab⟩ := v4_conj_trans (crd φ u) (crd_ne_zero φ hu) (psi φ a) ha
    (fun h => ha1 ((psi φ).injective (by rw [h, map_one]))) (psi φ b) hb
    (fun h => hb1 ((psi φ).injective (by rw [h, map_one])))
  refine ⟨(psi φ).symm g, ?_, ?_⟩
  · rw [← mem_stabΓ] at hg
    show psi φ ((psi φ).symm g) ∈ stabΓ (crd φ u)
    rw [MulEquiv.apply_symm_apply]
    exact hg
  · apply (psi φ).injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hgab

end CFSG.Quasithin.H13.U3.GC137
