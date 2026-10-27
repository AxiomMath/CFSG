module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23PlaneSem
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData

public section

namespace CFSG.Quasithin.H13

open CFSG.ComponentClassification.WittDesign CFSG.Monster.B.Classical.Plane CFSG.Fischer
  CFSG.EvenSmallLie.UnitarySix.MathieuExt CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups Matrix

section Coord

variable {K : Type} [Field K]

@[expose] noncomputable def pslCoordHom {L : Type} [Field L] (κ : K ≃+* L) :
    projectiveSL 3 K →* PSL(3, L) :=
  QuotientGroup.map (scalars 3 K) (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) L))
    (Matrix.SpecialLinearGroup.map κ.toRingHom) (by
      intro x hx
      rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
      rw [scalars_eq_center, Subgroup.mem_center_iff] at hx
      intro y
      obtain ⟨y', rfl⟩ : ∃ y', Matrix.SpecialLinearGroup.map κ.toRingHom y' = y :=
        ⟨Matrix.SpecialLinearGroup.map κ.symm.toRingHom y, by ext i j; simp⟩
      rw [← map_mul, ← map_mul, hx y'])

theorem pslCoordHom_proj {L : Type} [Field L] (κ : K ≃+* L)
    (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    pslCoordHom κ (proj 3 K g) =
      ((Matrix.SpecialLinearGroup.map κ.toRingHom g : Matrix.SpecialLinearGroup (Fin 3) L) :
        PSL(3, L)) :=
  rfl

@[expose] noncomputable def pslCoordInv {L : Type} [Field L] (κ : K ≃+* L) :
    PSL(3, L) →* projectiveSL 3 K :=
  QuotientGroup.map (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) L)) (scalars 3 K)
    (Matrix.SpecialLinearGroup.map κ.symm.toRingHom) (by
      intro x hx
      rw [Subgroup.mem_comap, scalars_eq_center, Subgroup.mem_center_iff]
      rw [Subgroup.mem_center_iff] at hx
      intro y
      obtain ⟨y', rfl⟩ : ∃ y', Matrix.SpecialLinearGroup.map κ.symm.toRingHom y' = y :=
        ⟨Matrix.SpecialLinearGroup.map κ.toRingHom y, by ext i j; simp⟩
      rw [← map_mul, ← map_mul, hx y'])

@[expose] noncomputable def pslCoord (κ : K ≃+* F4) : projectiveSL 3 K ≃* PSL(3, F4) where
  toFun := pslCoordHom κ
  invFun := pslCoordInv κ
  left_inv q := by
    obtain ⟨g, rfl⟩ := proj_surjective 3 K q
    rw [pslCoordHom_proj]
    change proj 3 K (Matrix.SpecialLinearGroup.map κ.symm.toRingHom
      (Matrix.SpecialLinearGroup.map κ.toRingHom g)) = proj 3 K g
    congr 1
    ext i j
    simp
  right_inv q := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    change pslCoordHom κ (proj 3 K (Matrix.SpecialLinearGroup.map κ.symm.toRingHom g)) = _
    rw [pslCoordHom_proj]
    congr 1
    ext i j
    simp
  map_mul' := map_mul (pslCoordHom κ)

theorem pslCoord_proj (κ : K ≃+* F4) (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    pslCoord κ (proj 3 K g) =
      ((Matrix.SpecialLinearGroup.map κ.toRingHom g : Matrix.SpecialLinearGroup (Fin 3) F4) :
        PSL(3, F4)) :=
  rfl

theorem semΓ_conj_slHom (A : GL (Fin 3) F4) (σ : F4 ≃+* F4)
    (M M' : Matrix.SpecialLinearGroup (Fin 3) F4)
    (hM' : (M' : Matrix (Fin 3) (Fin 3) F4) = (A : Matrix (Fin 3) (Fin 3) F4) *
      (M : Matrix (Fin 3) (Fin 3) F4).map σ * ((A⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4)) :
    semΓ A σ * slHom M * (semΓ A σ)⁻¹ = slHom M' := by
  refine Subtype.ext (Equiv.ext fun v => ?_)
  rw [semΓ_inv]
  change slin A σ ((M : Matrix (Fin 3) (Fin 3) F4) *ᵥ slin (slinInvMat A σ) σ.symm v) =
    (M' : Matrix (Fin 3) (Fin 3) F4) *ᵥ v
  have h1 : slin (slinInvMat A σ) σ.symm v =
      σ.symm ∘ (((A⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) *ᵥ v) := by
    rw [comp_mulVec]
    rfl
  have h2 : σ ∘ ((M : Matrix (Fin 3) (Fin 3) F4) *ᵥ
      (σ.symm ∘ (((A⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) *ᵥ v))) =
      (M : Matrix (Fin 3) (Fin 3) F4).map σ *ᵥ
        (((A⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) *ᵥ v) := by
    rw [comp_mulVec]
    congr 1
    funext i
    simp
  rw [h1, slin, h2, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM', Matrix.mul_assoc]

theorem pslPerm_pslCoord_conjAut (κ : K ≃+* F4) (A : GL (Fin 3) K) (σ : K ≃+* K)
    (q : projectiveSL 3 K) :
    pslPerm (pslCoord κ (conjAut 3 K A (fieldAut 3 K σ q))) =
      planePerm (semΓ (Matrix.GeneralLinearGroup.map κ.toRingHom A) (κ.symm.trans (σ.trans κ))) *
        pslPerm (pslCoord κ q) *
        (planePerm (semΓ (Matrix.GeneralLinearGroup.map κ.toRingHom A)
          (κ.symm.trans (σ.trans κ))))⁻¹ := by
  obtain ⟨g, rfl⟩ := proj_surjective 3 K q
  set A' := Matrix.GeneralLinearGroup.map κ.toRingHom A with hA'
  set σ' := κ.symm.trans (σ.trans κ) with hσ'
  set M' := Matrix.SpecialLinearGroup.map κ.toRingHom
    (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K A
      (Matrix.SpecialLinearGroup.map σ.toRingHom g)) with hM'
  have e1 : κ.toRingHom.mapMatrix (A : Matrix (Fin 3) (Fin 3) K) =
      (A' : Matrix (Fin 3) (Fin 3) F4) := rfl
  have e2 : κ.toRingHom.mapMatrix
      ((Matrix.SpecialLinearGroup.map σ.toRingHom g : Matrix.SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) =
      ((Matrix.SpecialLinearGroup.map κ.toRingHom g : Matrix.SpecialLinearGroup (Fin 3) F4) :
        Matrix (Fin 3) (Fin 3) F4).map σ' := by
    ext i j
    simp [hσ']
  have e3 : κ.toRingHom.mapMatrix ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((A'⁻¹ : GL (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) := by
    rw [hA', ← map_inv]
    rfl
  have hconj : semΓ A' σ' * slHom (Matrix.SpecialLinearGroup.map κ.toRingHom g) *
      (semΓ A' σ')⁻¹ = slHom M' := by
    apply semΓ_conj_slHom
    rw [hM', Matrix.SpecialLinearGroup.map_apply_coe, coe_slConjugation, map_mul, map_mul, e1, e2,
      e3]
  rw [fieldAut_proj, conjAut_proj, pslCoord_proj, pslCoord_proj, ← planePerm_slHom,
    ← planePerm_slHom, ← map_inv, ← map_mul, ← map_mul, hconj]

end Coord

section Induce

variable {G : Type} [Group G] {G0 : Subgroup G} (ψ : ↥G0 →* Equiv.Perm (Fin 21))

@[expose] def Induces (g : G) (π : Equiv.Perm (Fin 21)) : Prop :=
  ∀ (x : G) (hx : x ∈ G0) (hgx : g * x * g⁻¹ ∈ G0),
    ψ ⟨g * x * g⁻¹, hgx⟩ = π * ψ ⟨x, hx⟩ * π⁻¹

variable {ψ}

theorem Induces.unique (hψ : ψ.range = P0) {g : G}
    (hg : g ∈ Subgroup.normalizer (G0 : Set G))
    {π π' : Equiv.Perm (Fin 21)} (h : Induces ψ g π) (h' : Induces ψ g π') : π = π' := by
  have hc : ∀ p ∈ P0, (π'⁻¹ * π) * p = p * (π'⁻¹ * π) := by
    intro p hp
    rw [← hψ] at hp
    obtain ⟨⟨x, hx⟩, rfl⟩ := hp
    have hgx : g * x * g⁻¹ ∈ G0 := (Subgroup.mem_normalizer_iff.mp hg x).mp hx
    have e := (h x hx hgx).symm.trans (h' x hx hgx)
    calc π'⁻¹ * π * ψ ⟨x, hx⟩ = π'⁻¹ * (π * ψ ⟨x, hx⟩ * π⁻¹) * π := by group
      _ = π'⁻¹ * (π' * ψ ⟨x, hx⟩ * π'⁻¹) * π := by rw [e]
      _ = ψ ⟨x, hx⟩ * (π'⁻¹ * π) := by group
  have := eq_one_of_commute_P0 hc
  rw [inv_mul_eq_one] at this
  exact this.symm

theorem induces_mul {g h : G} (hh : h ∈ Subgroup.normalizer (G0 : Set G))
    {π ρ : Equiv.Perm (Fin 21)}
    (hgπ : Induces ψ g π) (hhρ : Induces ψ h ρ) : Induces ψ (g * h) (π * ρ) := by
  intro x hx hghx
  have hhx : h * x * h⁻¹ ∈ G0 := (Subgroup.mem_normalizer_iff.mp hh x).mp hx
  have e : g * h * x * (g * h)⁻¹ = g * (h * x * h⁻¹) * g⁻¹ := by group
  have h1 : (⟨g * h * x * (g * h)⁻¹, hghx⟩ : ↥G0) = ⟨g * (h * x * h⁻¹) * g⁻¹, e ▸ hghx⟩ :=
    Subtype.ext e
  rw [h1, hgπ _ hhx, hhρ _ hx]
  group

theorem induces_inv {g : G} {π : Equiv.Perm (Fin 21)} (hgπ : Induces ψ g π) :
    Induces ψ g⁻¹ π⁻¹ := by
  intro x hx hgx
  have e : g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ = x := by group
  have h1 := hgπ (g⁻¹ * x * g⁻¹⁻¹) hgx (e.symm ▸ hx)
  have h2 : (⟨g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹, e.symm ▸ hx⟩ : ↥G0) = ⟨x, hx⟩ := Subtype.ext e
  rw [h2] at h1
  rw [h1]
  group

variable (ψ) in
@[expose] def induceSub : Subgroup G where
  carrier := {g | g ∈ Subgroup.normalizer (G0 : Set G) ∧ ∃ π, Induces ψ g π}
  one_mem' := ⟨Subgroup.one_mem _, 1, fun x hx h1 => by
    have : (⟨1 * x * 1⁻¹, h1⟩ : ↥G0) = ⟨x, hx⟩ := Subtype.ext (by group)
    rw [this]
    group⟩
  mul_mem' := by
    rintro g h ⟨hg, π, hπ⟩ ⟨hh, ρ, hρ⟩
    exact ⟨Subgroup.mul_mem _ hg hh, π * ρ, induces_mul hh hπ hρ⟩
  inv_mem' := by
    rintro g ⟨hg, π, hπ⟩
    exact ⟨Subgroup.inv_mem _ hg, π⁻¹, induces_inv hπ⟩

theorem mem_induceSub_of_mem {x : G} (hx : x ∈ G0) : x ∈ induceSub ψ := by
  refine ⟨Subgroup.le_normalizer hx, ψ ⟨x, hx⟩, fun y hy hxy => ?_⟩
  have : (⟨x * y * x⁻¹, hxy⟩ : ↥G0) = ⟨x, hx⟩ * ⟨y, hy⟩ * ⟨x, hx⟩⁻¹ := rfl
  rw [this, map_mul, map_mul, map_inv]

variable (hψ : ψ.range = P0)
include hψ

@[expose] noncomputable def induceHom : ↥(induceSub ψ) →* Equiv.Perm (Fin 21) where
  toFun g := Classical.choose g.2.2
  map_one' := by
    have h1 : Induces ψ (1 : G) 1 := fun x hx h1 => by
      have : (⟨1 * x * 1⁻¹, h1⟩ : ↥G0) = ⟨x, hx⟩ := Subtype.ext (by group)
      rw [this]
      group
    exact Induces.unique hψ (Subgroup.one_mem _) (Classical.choose_spec (1 : ↥(induceSub ψ)).2.2)
      h1
  map_mul' g h := Induces.unique hψ (Subgroup.mul_mem _ g.2.1 h.2.1)
    (Classical.choose_spec (g * h).2.2)
    (induces_mul h.2.1 (Classical.choose_spec g.2.2) (Classical.choose_spec h.2.2))

theorem induceHom_spec (g : ↥(induceSub ψ)) : Induces ψ (g : G) (induceHom hψ g) :=
  Classical.choose_spec g.2.2

theorem induceHom_eq {g : ↥(induceSub ψ)} {π : Equiv.Perm (Fin 21)} (h : Induces ψ (g : G) π) :
    induceHom hψ g = π :=
  Induces.unique hψ g.2.1 (induceHom_spec hψ g) h

theorem induceHom_of_mem (x : ↥(induceSub ψ)) (hx : (x : G) ∈ G0) :
    induceHom hψ x = ψ ⟨x, hx⟩ :=
  induceHom_eq hψ (fun y hy hxy => by
    have : (⟨(x : G) * y * (x : G)⁻¹, hxy⟩ : ↥G0) = ⟨x, hx⟩ * ⟨y, hy⟩ * ⟨x, hx⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv])

end Induce

end CFSG.Quasithin.H13
