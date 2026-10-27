module

public import CFSG.Quasithin.Background.GoldschmidtD35CoreStab
public import CFSG.Quasithin.Background.GoldschmidtD35CoreSetup

public section

namespace CFSG.Quasithin.D35Core

open CFSG.QuasithinUnique.Setup.X3 CFSG.Quasithin Equiv
open scoped Matrix LinearAlgebra.Projectivization

variable {K : Type} [Field K] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K)}
variable {pt : Fin 6 → ℙ K (Fin 3 → K)}

theorem mem_valL (γ : Γ) : glLin γ.1 ∈ valL Γ := Subgroup.mem_map_of_mem _ γ.2

theorem matrix_eq_smul_one {M : Matrix (Fin 3) (Fin 3) K} {c : K} (h : ∀ v, M *ᵥ v = c • v) :
    M = c • 1 := by
  refine Matrix.ext fun i j => ?_
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply, eq_comm] using this

@[expose] noncomputable def actPerm (hO : IsSixOrbit (valL Γ) pt) (γ : Γ) : Perm (Fin 6) :=
  Classical.choose (hO.exists_perm (g := glLin γ.1) (hO.mem _ (mem_valL γ)))

theorem actPerm_spec (hO : IsSixOrbit (valL Γ) pt) (γ : Γ) (i : Fin 6) :
    lineAction K (Fin 3 → K) (glLin γ.1) (pt i) = pt (actPerm hO γ i) :=
  Classical.choose_spec (hO.exists_perm (g := glLin γ.1) (hO.mem _ (mem_valL γ))) i

theorem actPerm_unique (hO : IsSixOrbit (valL Γ) pt) {γ : Γ} {π : Perm (Fin 6)}
    (h : ∀ i, lineAction K (Fin 3 → K) (glLin γ.1) (pt i) = pt (π i)) : π = actPerm hO γ :=
  Equiv.ext fun i => hO.inj (by rw [← h, actPerm_spec])

theorem actPerm_mul (hO : IsSixOrbit (valL Γ) pt) (γ δ : Γ) :
    actPerm hO (γ * δ) = actPerm hO γ * actPerm hO δ := by
  symm
  apply actPerm_unique
  intro i
  rw [Subgroup.coe_mul, map_mul, map_mul, Perm.mul_apply, actPerm_spec, Perm.mul_apply,
    actPerm_spec]

theorem actPerm_one (hO : IsSixOrbit (valL Γ) pt) : actPerm hO (1 : Γ) = 1 := by
  symm
  apply actPerm_unique
  intro i
  simp

theorem actPerm_even (hO : IsSixOrbit (valL Γ) pt) (γ : Γ) :
    actPerm hO γ ∈ alternatingGroup (Fin 6) :=
  (hO.alt _).2 ⟨glLin γ.1, mem_valL γ, actPerm_spec hO γ⟩

@[expose] noncomputable def actHom (hO : IsSixOrbit (valL Γ) pt) :
    Γ →* alternatingGroup (Fin 6) where
  toFun γ := ⟨actPerm hO γ, actPerm_even hO γ⟩
  map_one' := Subtype.ext (actPerm_one hO)
  map_mul' γ δ := Subtype.ext (actPerm_mul hO γ δ)

theorem coe_actHom (hO : IsSixOrbit (valL Γ) pt) (γ : Γ) :
    ((actHom hO γ : alternatingGroup (Fin 6)) : Perm (Fin 6)) = actPerm hO γ := rfl

theorem actHom_surjective (hO : IsSixOrbit (valL Γ) pt) : Function.Surjective (actHom hO) := by
  intro x
  obtain ⟨g, hg, hgx⟩ := (hO.alt x).1 x.2
  obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hg
  refine ⟨⟨γ, hγ⟩, Subtype.ext ?_⟩
  exact (actPerm_unique hO (γ := ⟨γ, hγ⟩) hgx).symm

theorem actPerm_eq_one_iff [Finite K] (hval : IsValentiner K Γ) (hO : IsSixOrbit (valL Γ) pt)
    (γ : Γ) :
    actPerm hO γ = 1 ↔ γ ∈ Subgroup.center Γ := by
  have hD := threeQuaternaryData_of_valentiner hval
  constructor
  · intro h
    have hfix : ∀ i, lineAction K (Fin 3 → K) (glLin γ.1) (pt i) = pt i := fun i => by
      rw [actPerm_spec hO, h]
      rfl
    obtain ⟨c, hc⟩ := hO.scalar_of_fixes (Module.finrank_fin_fun K) hD.irreducible
      (g := glLin γ.1) (a := 0) (b := 1) (c := 2) (d := 3) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (hfix 0) (hfix 1) (hfix 2) (hfix 3)
    have hM : ((γ : Matrix.GeneralLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = c • 1 :=
      matrix_eq_smul_one fun v => by rw [← glLin_apply, hc]
    rw [Subgroup.mem_center_iff]
    intro δ
    refine Subtype.ext (Units.ext ?_)
    simp [Units.val_mul, hM]
  · intro h
    obtain ⟨c, hc⟩ := hval.2.2.2 γ h
    have hs : ∀ v, glLin γ.1 v = c • v := fun v => by
      rw [glLin_apply, hc]
      simp [Matrix.smul_mulVec]
    symm
    apply actPerm_unique
    intro i
    rw [lineAction_of_smul hs]
    rfl

theorem ker_actHom [Finite K] (hval : IsValentiner K Γ) (hO : IsSixOrbit (valL Γ) pt) :
    (actHom hO).ker = Subgroup.center Γ := by
  ext γ
  rw [MonoidHom.mem_ker, ← actPerm_eq_one_iff hval hO]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

@[expose] noncomputable def actEquiv [Finite K] (hval : IsValentiner K Γ)
    (hO : IsSixOrbit (valL Γ) pt) :
    (Γ ⧸ Subgroup.center Γ) ≃* alternatingGroup (Fin 6) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_actHom hval hO).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (actHom hO) (actHom_surjective hO))

theorem actEquiv_mk [Finite K] (hval : IsValentiner K Γ) (hO : IsSixOrbit (valL Γ) pt) (γ : Γ) :
    actEquiv hval hO (QuotientGroup.mk γ) = actHom hO γ := rfl

end CFSG.Quasithin.D35Core
