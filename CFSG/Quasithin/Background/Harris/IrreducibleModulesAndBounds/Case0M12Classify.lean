module

public import CFSG.Quasithin.Background.SmithB45MatM12
public import CFSG.Quasithin.Background.G11Defs

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Quasithin.B45Mat CFSG.Quasithin.B45Mat.M12
  CFSG.CharacterTheory.SteinbergBY Matrix

namespace Case0M12

theorem rep10_endo_scalar
    (F : Matrix (Fin 10) (Fin 10) (ZMod 2)) (hF : ∀ g : G12, F * rep10 g = rep10 g * F) :
    ∃ c : ZMod 2, F = c • 1 := by
  let k := AlgebraicClosure (ZMod 2)
  let ψ : ZMod 2 →+* k := algebraMap (ZMod 2) k
  have : (matrixBaseChange ψ rep10).IsIrreducible := isIrreducible_rep10 ψ
  let T : (Fin 10 → k) →ₗ[k] (Fin 10 → k) := Matrix.mulVecLin (F.map ψ)
  let f : (matrixBaseChange ψ rep10).IntertwiningMap (matrixBaseChange ψ rep10) :=
    LinearMap.intertwiningMap_of_isIntertwiningMap _ _ T (fun g v => by
      simp only [T, Matrix.mulVecLin_apply, matrixBaseChange_apply]
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.map_mul, ← Matrix.map_mul, hF g])
  obtain ⟨a, ha⟩ := (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
    (ρ := matrixBaseChange ψ rep10)).2 f
  have hT : ∀ v, (F.map ψ) *ᵥ v = a • v := by
    intro v
    have := congrArg (fun φ : (matrixBaseChange ψ rep10).IntertwiningMap
      (matrixBaseChange ψ rep10) => φ.toLinearMap v) ha
    simpa [f, T] using this.symm
  refine ⟨F 0 0, ?_⟩
  have hentry : ∀ i j, ψ (F i j) = if i = j then a else 0 := by
    intro i j
    have := congrFun (hT (Pi.single j 1)) i
    simp [Matrix.mulVec_single_one, Pi.single_apply] at this
    exact this
  have h00 : ψ (F 0 0) = a := by simpa using hentry 0 0
  ext i j
  apply ψ.injective
  rw [hentry]
  by_cases hij : i = j
  · subst hij
    simp [h00, hentry]
  · simp [hij]

theorem m12_classify
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V] {L : Subgroup (GLV V)}
    (hirr : IsIrr L ⊤) (f : ↥L ≃* G12) (hd : Module.finrank (ZMod 2) V ≤ 24) :
    ∃ e : V ≃ₗ[ZMod 2] (Fin 10 → ZMod 2), ∀ (g : G12) (v : V),
      e (((f.symm g : ↥L) : GLV V) v) = rep10 g *ᵥ e v := by
  let τ : Representation (ZMod 2) G12 V :=
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom).comp (L.subtype.comp f.symm.toMonoidHom)
  have hτ : ∀ g v, τ g v = ((f.symm g : ↥L) : GLV V) v := fun _ _ => rfl
  have hτirr : τ.IsIrreducible := by
    obtain ⟨-, hlt, hJ⟩ := hirr
    have hbt : (⊥ : Subrepresentation τ) ≠ ⊤ := by
      intro h
      obtain ⟨b, -, hb⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (bot_lt_iff_ne_bot.1 hlt)
      have hvt : b ∈ (⊤ : Subrepresentation τ).toSubmodule := Submodule.mem_top
      rw [← h] at hvt
      exact hb ((Submodule.mem_bot _).mp hvt)
    have : Nontrivial (Subrepresentation τ) := ⟨⟨⊥, ⊤, hbt⟩⟩
    refine ⟨fun U => ?_⟩
    have hinv : Invariant L U.toSubmodule := by
      intro k hk u hu
      have := U.apply_mem_toSubmodule (f ⟨k, hk⟩) hu
      rwa [hτ, MulEquiv.symm_apply_apply] at this
    rcases hJ _ hinv bot_le le_top with h0 | h0
    · left
      ext v
      constructor
      · intro hv
        have hv' : v ∈ U.toSubmodule := hv
        rw [h0] at hv'
        exact hv'
      · intro hv
        have hv0 : v = 0 := (Submodule.mem_bot _).mp hv
        rw [hv0]
        exact U.toSubmodule.zero_mem
    · right
      ext v
      constructor
      · intro _
        exact Submodule.mem_top
      · intro _
        have hv' : v ∈ U.toSubmodule := by
          rw [h0]
          exact Submodule.mem_top
        exact hv'
  have : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  rcases m12_binary_cases V τ hτirr hd with he | he
  · obtain ⟨e⟩ := he
    exfalso
    have hcard : Nat.card G12 = 95040 := CFSG.Sporadic.Mathieu.card_M12
    have htriv : ∀ g : G12, g = 1 := by
      intro g
      have h1 : ∀ v : V, ((f.symm g : ↥L) : GLV V) v = v := by
        intro v
        have h2 := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g v
        have h3 : rep1 g = 1 := rfl
        rw [matrixBaseChange_apply, h3, RingHom.coe_id, Matrix.map_id, Matrix.one_mulVec,
          Representation.Equiv.coe_toIntertwiningMap] at h2
        exact e.injective h2
      have h5 : f.symm g = 1 := Subtype.ext (LinearEquiv.ext h1)
      exact f.symm.injective (h5.trans (map_one f.symm).symm)
    have : Subsingleton G12 := ⟨fun x y => (htriv x).trans (htriv y).symm⟩
    rw [Nat.card_of_subsingleton (1 : G12)] at hcard
    norm_num at hcard
  · obtain ⟨e⟩ := he
    refine ⟨e.toLinearEquiv, fun g v => ?_⟩
    have h1 := Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g v
    rw [matrixBaseChange_apply, RingHom.coe_id, Matrix.map_id] at h1
    exact h1

end Case0M12

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
