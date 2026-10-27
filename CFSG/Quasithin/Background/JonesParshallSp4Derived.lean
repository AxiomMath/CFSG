module

public import CFSG.Quasithin.Background.JonesParshallSp4Two

public noncomputable section

namespace CFSG.Quasithin.JonesParshall

open Matrix CFSG.Quasithin.Explicit

section RingEquiv

variable {F F' : Type} [Field F] [Field F']

@[expose] def glIxRingEquiv (e : F ≃+* F') : GL Ix F ≃* GL Ix F' where
  toFun := Matrix.GeneralLinearGroup.map e.toRingHom
  invFun := Matrix.GeneralLinearGroup.map e.symm.toRingHom
  left_inv g := by
    ext i j
    change e.symm (e ((g : Matrix Ix Ix F) i j)) = _
    rw [RingEquiv.symm_apply_apply]
  right_inv g := by
    ext i j
    change e (e.symm ((g : Matrix Ix Ix F') i j)) = _
    rw [RingEquiv.apply_symm_apply]
  map_mul' := map_mul _

theorem glIxRingEquiv_coe (e : F ≃+* F') (g : GL Ix F) :
    ((glIxRingEquiv e g : GL Ix F') : Matrix Ix Ix F') = (g : Matrix Ix Ix F).map e := rfl

theorem spJ_map (e : F ≃+* F') : (spJ F).map e = spJ F' := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [spJ, one_apply, apply_ite]

theorem glIxRingEquiv_mem {K K' : Type} [Field K] [Field K'] (e : K ≃+* K') {g : GL Ix K}
    (hg : g ∈ sp4 K) : glIxRingEquiv e g ∈ sp4 K' := by
  change ((glIxRingEquiv e g : GL Ix K') : Matrix Ix Ix K')ᵀ * spJ K' *
    ((glIxRingEquiv e g : GL Ix K') : Matrix Ix Ix K') = spJ K'
  have hg' : (g : Matrix Ix Ix K)ᵀ * spJ K * g = spJ K := hg
  rw [glIxRingEquiv_coe, ← spJ_map e, ← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hg']

theorem map_sp4 (e : F ≃+* F') : (sp4 F).map (glIxRingEquiv e : GL Ix F →* GL Ix F') = sp4 F' := by
  ext h
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact glIxRingEquiv_mem e hg
  · intro hh
    refine ⟨glIxRingEquiv e.symm h, glIxRingEquiv_mem e.symm hh, ?_⟩
    ext i j
    change e (e.symm ((h : Matrix Ix Ix F') i j)) = _
    rw [RingEquiv.apply_symm_apply]

theorem map_sp4_commutator (e : F ≃+* F') :
    (⁅sp4 F, sp4 F⁆).map (glIxRingEquiv e : GL Ix F →* GL Ix F') = ⁅sp4 F', sp4 F'⁆ := by
  rw [Subgroup.map_commutator, map_sp4]

@[expose] def vecIxRingEquiv (e : F ≃+* F') : (Ix → F) ≃+ (Ix → F') where
  toFun v i := e (v i)
  invFun v i := e.symm (v i)
  left_inv v := by
    funext i
    simp
  right_inv v := by
    funext i
    simp
  map_add' v w := by
    funext i
    simp

theorem vecIxRingEquiv_smul (e : F ≃+* F') (g : GL Ix F) (v : Ix → F) :
    vecIxRingEquiv e (g • v) = glIxRingEquiv e g • vecIxRingEquiv e v := by
  funext i
  change e (((g : Matrix Ix Ix F) *ᵥ v) i) = (((g : Matrix Ix Ix F).map e) *ᵥ fun j => e (v j)) i
  exact RingHom.map_mulVec e.toRingHom _ _ i

end RingEquiv

variable {Γ : Type*} [Group Γ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

theorem finrank_H1_sp4Derived_two {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2)
    {ρ : Representation (ZMod 2) Γ W} (h : BinaryNaturalSp4Derived ρ F) :
    Module.finrank (ZMod 2) (H1 ρ) = 1 := by
  obtain ⟨θ, β, hβ⟩ := BinaryNaturalSp4Derived.intertwiner h
  set e : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two hF).symm
  let θ' : Γ ≃* ↥subAB := θ.trans (((glIxRingEquiv e).subgroupMap _).trans
    (MulEquiv.subgroupCongr ((map_sp4_commutator e).trans sp4Two_commutator_eq)))
  let β' : W ≃+ (Ix → ZMod 2) := β.trans (vecIxRingEquiv e)
  have hβ' : ∀ γ w, β' (ρ γ w) = muAB (θ' γ) (β' w) := fun γ w => by
    change vecIxRingEquiv e (β (ρ γ w)) = glIxRingEquiv e (θ γ : GL Ix F) • vecIxRingEquiv e (β w)
    rw [hβ, vecIxRingEquiv_smul]
  have : Finite Γ := Finite.of_equiv _ θ'.toEquiv.symm
  have : Finite W := Finite.of_equiv _ β'.toEquiv.symm
  apply finrank_H1_of_card
  rw [card_H1_eq_of_card ρ hβ' card_Z1A_AB, pow_one]

theorem finrank_H1_sp4Derived {F : Type} [Field F] [Fintype F] {a : ℕ}
    (hF : Fintype.card F = 2 ^ a) (ha : 0 < a) {ρ : Representation (ZMod 2) Γ W}
    (h : BinaryNaturalSp4Derived ρ F) : Module.finrank (ZMod 2) (H1 ρ) = a := by
  have : CharP F 2 := charP_of_card_eq_prime_pow hF
  rcases Nat.lt_or_ge 1 a with h1 | h1
  · exact finrank_H1_sp4Derived_of_one_lt hF h1 h
  · have ha1 : a = 1 := le_antisymm h1 ha
    subst ha1
    exact finrank_H1_sp4Derived_two (by rw [hF, pow_one]) h

end CFSG.Quasithin.JonesParshall
