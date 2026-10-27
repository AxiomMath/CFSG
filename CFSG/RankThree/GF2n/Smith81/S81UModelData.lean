module

public import CFSG.RankThree.GF2n.Smith81.S81U6Pure
public import CFSG.RankThree.GF2n.Smith81.S81BGeom
public import CFSG.RankThree.GF2n.Smith81.S81BLane
public import CFSG.ClassicalGroups.Unitary.Finite

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.U6Cube CFSG.RankThree.GF2n.Smith81.A5Cube
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary

section Space

variable {F : Type} [Field F] {K : Type} [Field K]

@[expose] def E3UWspace (σ : F ≃+* F) (_ : K ≃+* Fσ σ) : Type := Wform σ

instance (σ : F ≃+* F) (e : K ≃+* Fσ σ) : AddCommGroup (E3UWspace σ e) :=
  inferInstanceAs (AddCommGroup (Wform σ))

noncomputable instance (σ : F ≃+* F) (e : K ≃+* Fσ σ) : Module K (E3UWspace σ e) :=
  Module.compHom (Wform σ) (e : K →+* Fσ σ)

variable (σ : F ≃+* F) (e : K ≃+* Fσ σ)

theorem e3uWspace_smul_def (c : K) (w : E3UWspace σ e) :
    c • w = (show Wform σ from ((e c : Fσ σ) • (show Wform σ from w))) := rfl

variable [CharP F 2]

@[expose] noncomputable def e3uWactEquiv (g : SUid σ 6) : E3UWspace σ e ≃ₗ[K] E3UWspace σ e where
  toFun w := Wact σ g (show Wform σ from w)
  map_add' x y := map_add (Wact σ g) (show Wform σ from x) (show Wform σ from y)
  map_smul' c x := (Wact σ g).map_smul (e c) (show Wform σ from x)
  invFun w := Wact σ g⁻¹ (show Wform σ from w)
  left_inv w := by
    show (Wact σ g⁻¹) ((Wact σ g) (show Wform σ from w)) = (show Wform σ from w)
    rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  right_inv w := by
    show (Wact σ g) ((Wact σ g⁻¹) (show Wform σ from w)) = (show Wform σ from w)
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl

theorem e3uWactEquiv_apply (g : SUid σ 6) (w : E3UWspace σ e) :
    ((show Wform σ from e3uWactEquiv σ e g w : Wform σ) : Cube F) =
      rho F (g : GL (Fin 6) F) ((show Wform σ from w : Wform σ) : Cube F) := rfl

@[expose] noncomputable def e3uWact : SUid σ 6 →* (E3UWspace σ e ≃ₗ[K] E3UWspace σ e) where
  toFun := e3uWactEquiv σ e
  map_one' := by
    apply LinearEquiv.ext
    intro w
    show (Wact σ 1) (show Wform σ from w) = (show Wform σ from w)
    rw [map_one]
    rfl
  map_mul' g h := by
    apply LinearEquiv.ext
    intro w
    show (Wact σ (g * h)) (show Wform σ from w) =
      (Wact σ g) ((Wact σ h) (show Wform σ from w))
    rw [map_mul]
    rfl

@[expose] noncomputable def e3uGam : Subgroup (E3UWspace σ e ≃ₗ[K] E3UWspace σ e) :=
  (e3uWact σ e).range

@[expose] noncomputable def e3uP0 : E3UWspace σ e :=
  show Wform σ from ⟨pt0 F, mem_Wform_iff.mpr (mem_Wsub_iff.mpr theta_pt0)⟩

@[expose] def e3uT0Vec (i : Fin 3) : Fin 6 → F := fun j => if j.val / 2 = i.val then 1 else 0

@[expose] def e3uU0Sub : Subgroup (SUid σ 6) where
  carrier := {g | ∀ i : Fin 3,
    ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec (e3uT0Vec i) = e3uT0Vec i}
  mul_mem' {a b} ha hb i := by
    rw [Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hb i, ha i]
  one_mem' i := by
    rw [Subgroup.coe_one, Units.val_one, Matrix.one_mulVec]
  inv_mem' {a} ha i := by
    have h1 := ha i
    have h2 : ((a⁻¹ : SUid σ 6) : GL (Fin 6) F).val.mulVec
        (((a : GL (Fin 6) F)).val.mulVec (e3uT0Vec i)) = e3uT0Vec i := by
      rw [Matrix.mulVec_mulVec, Subgroup.coe_inv, ← Units.val_mul,
        inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    rw [h1] at h2
    exact h2

@[expose] noncomputable def e3uU0 : Subgroup (E3UWspace σ e ≃ₗ[K] E3UWspace σ e) :=
  (e3uU0Sub σ).map (e3uWact σ e)

end Space

section ModelData

variable {G : Type} [Group G]

@[expose] def Smith24E3UUniformStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    RemCfg M Q Z B → InCaseE3U M Q Z B →
      ∀ (K : Type) [Field K] [Finite K] (γ : G → K) (M₀ : Tim79.QuadModel Q Z K γ),
        GlobalModelData M Q Z γ M₀ →
          ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (f : ℕ)
            (_ : Nat.card F = (2 ^ f) ^ 2) (e : K ≃+* Fσ (unitaryInvolution F 2 f))
            (ψ : M₀.E ≃ₗ[K] E3UWspace (unitaryInvolution F 2 f) e)
            (φ : Lgen M (LB M Q B) →*
              (E3UWspace (unitaryInvolution F 2 f) e ≃ₗ[K] E3UWspace (unitaryInvolution F 2 f) e)),
              EUniData M Q Z B M₀ ψ φ (e3uGam (unitaryInvolution F 2 f) e)
                (e3uP0 (unitaryInvolution F 2 f) e) (e3uU0 (unitaryInvolution F 2 f) e)

end ModelData

section CubeHom

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
  {K : Type} [Field K] (e : K ≃+* Fσ (unitaryInvolution F 2 f))

@[expose] noncomputable def statedSUToSUid :
    ↥(StatedSU 6 (2 ^ f) F) →* ↥(SUid (unitaryInvolution F 2 f) 6) :=
  Subgroup.inclusion (SUid_eq_statedSU hF 6).ge

theorem cubeHomU_scalar_le :
    (StatedScalars (Fin 6) F).subgroupOf (StatedSU 6 (2 ^ f) F) ≤
      ((e3uWact (unitaryInvolution F 2 f) e).comp (statedSUToSUid hF)).ker := by
  intro x hx
  have hx' : (x : GL (Fin 6) F) ∈ (Matrix.GeneralLinearGroup.scalar (Fin 6)).range :=
    Subgroup.mem_subgroupOf.mp hx
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hx'
  have hdet : ((x : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).det = 1 :=
    det_eq_one_of_mem_statedSU x.2
  have hmat : ((x : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = (c : F) • 1 := by
    rw [← hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]
  have h6 : (c : F) ^ 6 = 1 := by
    rw [hmat, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
    exact hdet
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hsq : ((c : F) ^ 3 - 1) ^ 2 = 0 := by
    linear_combination h6 + (1 - (c : F) ^ 3) * h2
  have hc3 : (c : F) ^ 3 = 1 := sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hsq)
  have hσ : IsUnitaryInvolution (unitaryInvolution F 2 f) :=
    isUnitaryInvolution_unitaryInvolution hF
  have hW : Wact (unitaryInvolution F 2 f) (statedSUToSUid hF x) = 1 :=
    (Wact_eq_one_iff hσ _).mpr ⟨(c : F), hc3, hmat⟩
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
  refine LinearEquiv.ext fun w => ?_
  show (Wact (unitaryInvolution F 2 f) (statedSUToSUid hF x))
      (show Wform (unitaryInvolution F 2 f) from w) =
    (show Wform (unitaryInvolution F 2 f) from w)
  rw [hW]
  rfl

@[expose] noncomputable def cubeHomU :
    StatedProj (StatedSU 6 (2 ^ f) F) →* (E3UWspace (unitaryInvolution F 2 f) e ≃ₗ[K]
      E3UWspace (unitaryInvolution F 2 f) e) :=
  QuotientGroup.lift ((StatedScalars (Fin 6) F).subgroupOf (StatedSU 6 (2 ^ f) F))
    ((e3uWact (unitaryInvolution F 2 f) e).comp (statedSUToSUid hF)) (cubeHomU_scalar_le hF e)

theorem cubeHomU_mk (g : ↥(StatedSU 6 (2 ^ f) F)) :
    cubeHomU hF e (QuotientGroup.mk g) =
      e3uWact (unitaryInvolution F 2 f) e (statedSUToSUid hF g) := rfl

theorem cubeHomU_injective : Function.Injective (cubeHomU hF e) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
  rw [cubeHomU_mk] at ha
  have hσ : IsUnitaryInvolution (unitaryInvolution F 2 f) :=
    isUnitaryInvolution_unitaryInvolution hF
  have hW : Wact (unitaryInvolution F 2 f) (statedSUToSUid hF g) = 1 := by
    refine LinearEquiv.ext fun w => ?_
    have h1 := LinearEquiv.congr_fun ha (show E3UWspace (unitaryInvolution F 2 f) e from w)
    exact h1
  obtain ⟨l, hl3, hl⟩ := (Wact_eq_one_iff hσ _).mp hW
  have hl0 : l ≠ 0 := by
    rintro rfl
    simp at hl3
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]
  refine ⟨Units.mk0 l hl0, ?_⟩
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0, Matrix.scalar_apply,
    ← Matrix.smul_one_eq_diagonal]
  exact hl.symm

theorem cubeHomU_range :
    (cubeHomU hF e).range = e3uGam (unitaryInvolution F 2 f) e := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective a
    exact MonoidHom.mem_range.mpr ⟨statedSUToSUid hF g, rfl⟩
  · intro hx
    obtain ⟨s, rfl⟩ := MonoidHom.mem_range.mp hx
    refine MonoidHom.mem_range.mpr ⟨QuotientGroup.mk ⟨(s : GL (Fin 6) F),
      (SUid_eq_statedSU hF 6).le s.2⟩, rfl⟩

end CubeHom

end CFSG.RankThree.GF2n.Smith81
