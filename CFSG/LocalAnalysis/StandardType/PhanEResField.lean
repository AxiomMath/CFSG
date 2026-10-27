module

public import CFSG.LocalAnalysis.StandardType.PhanEResSL

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open Matrix CFSG.LieType.Universal CFSG.LieType.RootSystem
open scoped MatrixGroups

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {Fld : Type} [Field Fld] {Kf : Type} [Field Kf]

@[expose] noncomputable def ChevModel2.mapField (M : ChevModel2 D n H Fld) (κ : Kf ≃+* Fld) :
    ChevModel2 D n H Kf where
  x γ c := M.x γ (κ c)
  x_mem := by
    intro γ hγ g
    exact (M.x_mem γ hγ g).trans
      ⟨fun ⟨c, hc⟩ => ⟨κ.symm c, by simpa using hc⟩, fun ⟨c, hc⟩ => ⟨κ c, hc⟩⟩
  x_add := by
    intro γ hγ c d
    show M.x γ (κ (c + d)) = M.x γ (κ c) * M.x γ (κ d)
    rw [map_add, M.x_add γ hγ (κ c) (κ d)]
  x_inj := fun γ hγ => (M.x_inj γ hγ).comp κ.injective
  nm_conj := fun i γ hγ c => M.nm_conj i γ hγ (κ c)
  nm_sq := M.nm_sq
  hh i := (M.hh i).comp (Units.map κ.toMonoidHom)
  hh_range := by
    intro i
    rw [← M.hh_range i]
    ext g
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨Units.map κ.toMonoidHom t, rfl⟩
    · rintro ⟨u, rfl⟩
      refine ⟨Units.map κ.symm.toMonoidHom u, ?_⟩
      have hcomp : Units.map κ.toMonoidHom (Units.map κ.symm.toMonoidHom u) = u := by
        apply Units.ext
        simp [Units.coe_map]
      rw [MonoidHom.comp_apply, hcomp]
  hh_conj := by
    intro i t γ hγ c
    show M.hh i (Units.map κ.toMonoidHom t) * M.x γ (κ c) *
        (M.hh i (Units.map κ.toMonoidHom t))⁻¹ =
      M.x γ (κ (((t ^ (∑ j, D.cartan i j * γ j) : Kfˣ) : Kf) * c))
    set k : ℤ := ∑ j, D.cartan i j * γ j
    have hpow : κ (((t ^ k : Kfˣ) : Kf)) =
        (((Units.map κ.toMonoidHom t) ^ k : Fldˣ) : Fld) := by
      change κ.toMonoidHom ((t ^ k : Kfˣ) : Kf) =
        (((Units.map κ.toMonoidHom t) ^ k : Fldˣ) : Fld)
      rw [← Units.coe_map κ.toMonoidHom (t ^ k), map_zpow (Units.map κ.toMonoidHom) t k]
    rw [M.hh_conj i (Units.map κ.toMonoidHom t) γ hγ (κ c), map_mul, hpow]
  nm_def := by
    intro i
    show n i = M.x (Pi.single i 1) (κ 1) * M.x (-Pi.single i 1) (κ (-1)) *
      M.x (Pi.single i 1) (κ 1)
    rw [M.nm_def i]
    simp only [map_one, map_neg]
  hh_def := by
    intro i t
    show M.hh i (Units.map κ.toMonoidHom t) =
      (M.x (Pi.single i 1) (κ ↑t) * M.x (-Pi.single i 1) (κ (-↑(t⁻¹))) *
        M.x (Pi.single i 1) (κ ↑t)) * (n i)⁻¹
    rw [M.hh_def i (Units.map κ.toMonoidHom t), Units.val_inv_eq_inv_val,
      Units.val_inv_eq_inv_val, map_neg, map_inv₀, Units.coe_map]
    rfl

@[expose] def ChevModel2.PhiCompat.mapField {M : ChevModel2 D n H Fld}
    {w₀ : (coxeterMatrix D.isFiniteType).Group} {F : FrobData D n H w₀} {θ : Fld →+* Fld}
    (PC : M.PhiCompat F θ) (κ : Kf ≃+* Fld) {θ' : Kf →+* Kf} (hκθ : ∀ c, κ (θ' c) = θ (κ c)) :
    (M.mapField κ).PhiCompat F θ' where
  ρ := PC.ρ
  ρ_single := PC.ρ_single
  ρ_mem := PC.ρ_mem
  phi_x γ hγ c := by
    show F.φ (M.x γ (κ c)) = M.x (PC.ρ γ) (κ (θ' c))
    rw [hκθ]
    exact PC.phi_x γ hγ (κ c)

namespace Res

open CFSG.LieType.Steinberg.CentralExt.SLClosed

private lemma p9uRF_map_tv {R S : Type} [Field R] [Field S] (f : R →+* S)
    {m : ℕ} {p q : Fin (m + 1)} (hpq : p ≠ q) (c : R) :
    SpecialLinearGroup.map f (tv R p q c) = tv S p q (f c) := by
  rw [tv_of_ne hpq, tv_of_ne hpq]
  ext a b
  simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    Matrix.SpecialLinearGroup.transvection_coe, Matrix.one_apply, Matrix.single_apply,
    apply_ite f]

@[expose] noncomputable def SLPath.mapField {M : ChevModel2 D n H Fld} {m : ℕ} (L : SLPath M m)
    (κ : Kf ≃+* Fld) : SLPath (M.mapField κ) m where
  e := L.e
  inj := L.inj
  cartan := L.cartan
  ε := L.ε.comp (SpecialLinearGroup.map (κ : Kf →+* Fld))
  tv_eq := by
    intro p q hpq c
    show L.ε (SpecialLinearGroup.map (κ : Kf →+* Fld) (tv Kf p q c)) =
      M.x (pathRoot L.e p q) (κ c)
    rw [p9uRF_map_tv (κ : Kf →+* Fld) hpq c]
    exact L.tv_eq p q hpq (κ c)

theorem exists_slPath_mapField {M : ChevModel2 D n H Fld} (κ : Kf ≃+* Fld)
    (charts : ∀ (m : ℕ) (e : Fin m → Fin D.rank), 1 ≤ m → m ≤ 3 → Function.Injective e →
      (∀ k l : Fin m, D.cartan (e k) (e l) =
        if k = l then 2 else if k.val + 1 = l.val ∨ l.val + 1 = k.val then -1 else 0) →
      ∃ L : SLPath M m, L.e = e) :
    ∀ (m : ℕ) (e : Fin m → Fin D.rank), 1 ≤ m → m ≤ 3 → Function.Injective e →
      (∀ k l : Fin m, D.cartan (e k) (e l) =
        if k = l then 2 else if k.val + 1 = l.val ∨ l.val + 1 = k.val then -1 else 0) →
      ∃ L : SLPath (M.mapField κ) m, L.e = e := by
  intro m e h1 h3 he hc
  obtain ⟨L, hL⟩ := charts m e h1 h3 he hc
  exact ⟨L.mapField κ, hL⟩

end Res

end CFSG.ClassicalInvolution.Phan.PhanE

end
