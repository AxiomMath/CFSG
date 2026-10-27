module

public import CFSG.Sporadic.J2.Representations.Module12CJ
public import CFSG.Algebra.F4

public section

namespace CFSG.Sporadic.J2.Module12

abbrev V12 : Type := Fin 12 → ZMod 2

local instance instAddCommGroupV12 : AddCommGroup V12 :=
  { Pi.addCommGroup with
    toAddCommMonoid := Pi.addCommMonoid }

@[expose] noncomputable def Jlin : Module.End (ZMod 2) V12 :=
  Matrix.toLinAlgEquiv' Jm

@[simp] theorem Jlin_apply (v : V12) : Jlin v = Matrix.mulVec Jm v :=
  rfl

@[simp] theorem toMatrix'_Jlin : LinearMap.toMatrix' Jlin = Jm := by
  ext i j
  simp [Jlin, LinearMap.toMatrix'_apply, Matrix.mulVec_single_one]

theorem Jlin_sq : Jlin * Jlin = Jlin + 1 := by
  rw [Jlin, ← map_mul, Jm_sq, map_add, map_one]

theorem Jlin_apply_apply (v : V12) : Jlin (Jlin v) = Jlin v + v := by
  have h := congrArg (fun f : Module.End (ZMod 2) V12 => f v) Jlin_sq
  simpa [Jlin_apply] using h

@[expose] noncomputable def phiFun (c : F4) : Module.End (ZMod 2) V12 :=
  c.a • (1 : Module.End (ZMod 2) V12) + c.b • Jlin

theorem phiFun_apply (c : F4) (v : V12) : phiFun c v = c.a • v + c.b • Jlin v := by
  simp [phiFun, LinearMap.add_apply, LinearMap.smul_apply]

theorem phiFun_zero : phiFun 0 = 0 := by
  apply LinearMap.ext
  intro v
  rw [phiFun_apply, F4.zero_def]
  simp

theorem phiFun_one : phiFun 1 = 1 := by
  apply LinearMap.ext
  intro v
  rw [phiFun_apply, F4.one_def]
  simp

theorem phiFun_add (c d : F4) : phiFun (c + d) = phiFun c + phiFun d := by
  apply LinearMap.ext
  intro v
  rw [phiFun_apply, LinearMap.add_apply, phiFun_apply, phiFun_apply, F4.add_def]
  simp only [add_smul]
  abel

theorem phiFun_mul (c d : F4) : phiFun (c * d) = phiFun c * phiFun d := by
  apply LinearMap.ext
  intro v
  rw [phiFun_apply, Module.End.mul_apply, phiFun_apply, phiFun_apply, F4.mul_def]
  simp only [Jlin.map_add, Jlin.map_smul, Jlin_apply_apply, smul_add, smul_smul, add_smul]
  module

@[expose] noncomputable def phi : F4 →+* Module.End (ZMod 2) V12 where
  toFun := phiFun
  map_zero' := phiFun_zero
  map_one' := phiFun_one
  map_add' := phiFun_add
  map_mul' := phiFun_mul

noncomputable instance instModuleF4 : Module F4 V12 :=
  Module.compHom V12 phi

theorem smul_F4_def (c : F4) (v : V12) : c • v = c.a • v + c.b • Jlin v := by
  change phi c v = c.a • v + c.b • Jlin v
  exact phiFun_apply c v

theorem omega_smul (v : V12) : (F4.omega : F4) • v = Jlin v := by
  rw [smul_F4_def]
  simp [F4.omega_def]

theorem zmod_smul_eq_f4 (a : ZMod 2) (v : V12) :
    a • v = (⟨a, 0⟩ : F4) • v := by
  rw [smul_F4_def]
  simp

theorem exists_mem_CJ_of_linearMap (f : V12 →ₗ[F4] V12) :
    ∃ X ∈ CJ, ∀ v : V12, Matrix.mulVec X v = f v := by
  let g : V12 →ₗ[ZMod 2] V12 :=
    { toFun := f
      map_add' := fun x y => f.map_add x y
      map_smul' := fun a v => by
        have h := f.map_smul (⟨a, 0⟩ : F4) v
        rw [← zmod_smul_eq_f4 a v, ← zmod_smul_eq_f4 a (f v)] at h
        exact h }
  have hcomm : g.comp Jlin = Jlin.comp g := by
    apply LinearMap.ext
    intro v
    have h := f.map_smul (F4.omega) v
    rw [omega_smul, omega_smul] at h
    exact h
  let X : Matrix (Fin 12) (Fin 12) (ZMod 2) := LinearMap.toMatrix' g
  have hX : X ∈ CJ := by
    have hmat : LinearMap.toMatrix' (g.comp Jlin) = LinearMap.toMatrix' (Jlin.comp g) := by
      rw [hcomm]
    rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, toMatrix'_Jlin] at hmat
    exact hmat
  refine ⟨X, hX, fun v => ?_⟩
  change Matrix.mulVec (LinearMap.toMatrix' g) v = f v
  rw [LinearMap.toMatrix'_mulVec]
  rfl

theorem Module12_irreducible (U : Submodule (ZMod 2) V12)
    (hU : ∀ X ∈ Aalg, ∀ v ∈ U, Matrix.mulVec X v ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  by_cases hbot : U = ⊥
  · exact Or.inl hbot
  · right
    have hne : ∃ v ∈ U, v ≠ 0 := by
      by_contra h
      apply hbot
      rw [Submodule.eq_bot_iff]
      intro v hv
      by_contra hv0
      exact h ⟨v, hv, hv0⟩
    obtain ⟨v, hvU, hv0⟩ := hne
    ext w
    simp only [Submodule.mem_top, iff_true]
    have hsimple : IsSimpleModule (Module.End F4 V12) V12 := inferInstance
    have hsurj : Function.Surjective
        (LinearMap.toSpanSingleton (Module.End F4 V12) V12 v) :=
      ((isSimpleModule_iff_toSpanSingleton_surjective
        (R := Module.End F4 V12) (M := V12)).mp hsimple).2 v hv0
    obtain ⟨f, hf⟩ := hsurj w
    have hfv : f v = w := by
      simpa using hf
    let f' : V12 →ₗ[F4] V12 := f
    obtain ⟨X, hX, hXf⟩ := exists_mem_CJ_of_linearMap f'
    have hXA : X ∈ Aalg := by
      change X ∈ (Aalg : Set (Matrix (Fin 12) (Fin 12) (ZMod 2)))
      rw [Aalg_eq_CJ]
      exact hX
    have hmem : Matrix.mulVec X v ∈ U := hU X hXA v hvU
    rwa [hXf v, show f' v = w from hfv] at hmem

end CFSG.Sporadic.J2.Module12
