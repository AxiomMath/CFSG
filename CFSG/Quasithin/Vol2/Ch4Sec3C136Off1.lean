module

public import CFSG.Quasithin.Vol2.Ch4Sec3C136Norm
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.H13.Ch4

open Matrix

variable {F : Type} [Field F]

@[expose] def addPerms (F : Type) [Field F] : Subgroup (Equiv.Perm (Fin 2 → Fin 3 → F)) where
  carrier := {e | ∀ v w, e (v + w) = e v + e w}
  mul_mem' := fun {e f} he hf v w => by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hf, he]
  one_mem' := fun _ _ => rfl
  inv_mem' := fun {e} he v w => by
    apply e.injective
    rw [he]
    simp only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply]

@[expose] def linPerms (F : Type) [Field F] : Subgroup (Equiv.Perm (Fin 2 → Fin 3 → F)) where
  carrier := {e | ∀ (μ : F) v, e (μ • v) = μ • e v}
  mul_mem' := fun {e f} he hf μ v => by
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hf, he]
  one_mem' := fun _ _ => rfl
  inv_mem' := fun {e} he μ v => by
    apply e.injective
    rw [he]
    simp only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply]

theorem dact_dact (X Y : Matrix (Fin 3) (Fin 3) F) (v : Fin 2 → Fin 3 → F) :
    dact X (dact Y v) = dact (X * Y) v := by
  funext i
  simp only [dact, Matrix.mulVec_mulVec]

theorem dact_one (v : Fin 2 → Fin 3 → F) : dact (1 : Matrix (Fin 3) (Fin 3) F) v = v := by
  funext i
  simp only [dact, Matrix.one_mulVec]

@[expose] def diagPerms (F : Type) [Field F] : Subgroup (Equiv.Perm (Fin 2 → Fin 3 → F)) where
  carrier := {e | ∃ X : SpecialLinearGroup (Fin 3) F,
    ∀ v, e v = dact (X : Matrix (Fin 3) (Fin 3) F) v}
  mul_mem' := fun {e f} he hf => by
    obtain ⟨X, hX⟩ := he
    obtain ⟨Y, hY⟩ := hf
    refine ⟨X * Y, fun v => ?_⟩
    rw [Equiv.Perm.mul_apply, hY, hX, dact_dact]
    rfl
  one_mem' := ⟨1, fun v => (dact_one v).symm⟩
  inv_mem' := fun {e} he => by
    obtain ⟨X, hX⟩ := he
    refine ⟨X⁻¹, fun v => ?_⟩
    apply e.injective
    have h1 : (X : Matrix (Fin 3) (Fin 3) F) *
        ((X⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 :=
      congrArg (fun Y : SpecialLinearGroup (Fin 3) F => (Y : Matrix (Fin 3) (Fin 3) F))
        (mul_inv_cancel X)
    rw [Equiv.Perm.coe_inv, Equiv.apply_symm_apply, hX, dact_dact, h1, dact_one]

@[expose] def fixPts (E : Set (Equiv.Perm (Fin 2 → Fin 3 → F))) : Set (Fin 2 → Fin 3 → F) :=
  {v | ∀ e ∈ E, e v = v}

@[expose] def toAddEquivOf (e : Equiv.Perm (Fin 2 → Fin 3 → F)) (he : e ∈ addPerms F) :
    (Fin 2 → Fin 3 → F) ≃+ (Fin 2 → Fin 3 → F) :=
  { e with map_add' := he }

theorem exists_semilinear_perm [Finite F] {e : Equiv.Perm (Fin 2 → Fin 3 → F)}
    (he : e ∈ addPerms F) (hn : NormalizesDact ⇑e) (hn' : NormalizesDact ⇑e⁻¹) :
    ∃ σ : F ≃+* F, ∀ (μ : F) v, e (μ • v) = σ μ • e v :=
  exists_semilinear (T := toAddEquivOf e he) two_ne_zero hn hn'

theorem card_fixPts_sq_le [Finite F] {E E₁ : Subgroup (Equiv.Perm (Fin 2 → Fin 3 → F))}
    (hE₁ : E₁ ≤ E ⊓ linPerms F) (hadd : E ≤ addPerms F) {e : Equiv.Perm (Fin 2 → Fin 3 → F)}
    (he : e ∈ E) {σ : F ≃+* F} (hσ : ∀ (μ : F) v, e (μ • v) = σ μ • e v) {θ : F}
    (hθ : σ θ ≠ θ) :
    Nat.card (fixPts (E : Set (Equiv.Perm (Fin 2 → Fin 3 → F)))) ^ 2 ≤
      Nat.card (fixPts (E₁ : Set (Equiv.Perm (Fin 2 → Fin 3 → F)))) := by
  set C := fixPts (E : Set (Equiv.Perm (Fin 2 → Fin 3 → F))) with hC
  set C₁ := fixPts (E₁ : Set (Equiv.Perm (Fin 2 → Fin 3 → F))) with hC₁
  have hmem : ∀ x ∈ C, ∀ y ∈ C, x + θ • y ∈ C₁ := by
    intro x hx y hy f hf
    have hfE := (hE₁ hf).1
    rw [hadd hfE, (hE₁ hf).2, hx f hfE, hy f hfE]
  let φ : ↥C × ↥C → ↥C₁ := fun p => ⟨p.1 + θ • p.2, hmem _ p.1.2 _ p.2.2⟩
  have hφ : Function.Injective φ := by
    rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ ⟨⟨x', hx'⟩, ⟨y', hy'⟩⟩ h
    have h1 : x + θ • y = x' + θ • y' := congrArg Subtype.val h
    have h2 : x + σ θ • y = x' + σ θ • y' := by
      have h3 := congrArg e h1
      rwa [hadd he, hadd he, hσ, hσ, hx e he, hy e he, hx' e he, hy' e he] at h3
    have h4 : (θ - σ θ) • y = (θ - σ θ) • y' := by
      rw [sub_smul, sub_smul]
      have h5 : θ • y - σ θ • y = θ • y' - σ θ • y' := by
        calc θ • y - σ θ • y = (x + θ • y) - (x + σ θ • y) := by abel
          _ = (x' + θ • y') - (x' + σ θ • y') := by rw [h1, h2]
          _ = θ • y' - σ θ • y' := by abel
      exact h5
    have hyy : y = y' := smul_right_injective _ (sub_ne_zero.mpr (Ne.symm hθ)) h4
    subst hyy
    have hxx : x = x' := add_right_cancel h1
    subst hxx
    rfl
  have h1 := Nat.card_le_card_of_injective φ hφ
  rwa [Nat.card_prod, ← sq] at h1

theorem eq_of_mul_self_eq_one [Finite F] [CharP F 2] {σ τ : F ≃+* F} (hσ : σ * σ = 1)
    (hτ : τ * τ = 1) (hσ1 : σ ≠ 1) (hτ1 : τ ≠ 1) : σ = τ := by
  classical
  let _ : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hfix : ∀ ρ : F ≃+* F, ∀ x : ZMod 2, ρ (algebraMap (ZMod 2) F x) = algebraMap (ZMod 2) F x :=
    fun ρ x => by
      have h : ρ.toRingHom.comp (algebraMap (ZMod 2) F) = algebraMap (ZMod 2) F :=
        Subsingleton.elim _ _
      exact congrArg (fun φ : ZMod 2 →+* F => φ x) h
  let toGal : (F ≃+* F) → (F ≃ₐ[ZMod 2] F) := fun ρ => AlgEquiv.ofRingEquiv (hfix ρ)
  have htoGal : ∀ ρ x, toGal ρ x = ρ x := fun _ _ => rfl
  have hinj : Function.Injective toGal := fun ρ ρ' h => by
    ext x
    rw [← htoGal ρ x, ← htoGal ρ' x, h]
  have hsq : ∀ ρ : F ≃+* F, ρ * ρ = 1 → toGal ρ ^ 2 = 1 := fun ρ h => by
    ext x
    rw [sq, AlgEquiv.mul_apply, htoGal, htoGal, AlgEquiv.one_apply]
    exact congrArg (fun φ : F ≃+* F => φ x) h
  have hne1 : ∀ ρ : F ≃+* F, ρ ≠ 1 → toGal ρ ≠ 1 := fun ρ h h1 => h (by
    ext x
    rw [← htoGal ρ x, h1]
    rfl)
  have : Finite (F ≃ₐ[ZMod 2] F) :=
    Finite.of_injective (fun g : F ≃ₐ[ZMod 2] F => (g : F → F)) DFunLike.coe_injective
  let _ : Fintype (F ≃ₐ[ZMod 2] F) := Fintype.ofFinite _
  by_contra hne
  have hne' : toGal σ ≠ toGal τ := fun h => hne (hinj h)
  have hcard := IsCyclic.card_pow_eq_one_le (α := F ≃ₐ[ZMod 2] F) (n := 2) two_pos
  have hsub : ({1, toGal σ, toGal τ} : Finset (F ≃ₐ[ZMod 2] F)) ⊆
      Finset.univ.filter fun a => a ^ 2 = 1 := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl
    · exact one_pow 2
    · exact hsq σ hσ
    · exact hsq τ hτ
  have h3 : ({1, toGal σ, toGal τ} : Finset (F ≃ₐ[ZMod 2] F)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hne']
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨(hne1 σ hσ1).symm, (hne1 τ hτ1).symm⟩
  have h4 := Finset.card_le_card hsub
  omega

end CFSG.Quasithin.H13.Ch4
