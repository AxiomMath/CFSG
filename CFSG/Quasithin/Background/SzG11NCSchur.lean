module

public import CFSG.Quasithin.Background.G11Defs

public section

namespace CFSG.Quasithin.SzG11NC

open CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def commutantOf (H : Subgroup (GLV V)) :
    Subalgebra (ZMod 2) (Module.End (ZMod 2) V) :=
  Subalgebra.centralizer (ZMod 2) {f | ∃ h ∈ H, f = (h : V →ₗ[ZMod 2] V)}

theorem mem_commutantOf {H : Subgroup (GLV V)} {f : Module.End (ZMod 2) V} :
    f ∈ commutantOf H ↔ ∀ h ∈ H, ∀ v, f (h v) = h (f v) := by
  unfold commutantOf
  rw [Subalgebra.mem_centralizer_iff]
  constructor
  · intro hf h hh v
    have := hf (h : V →ₗ[ZMod 2] V) ⟨h, hh, rfl⟩
    have := congrArg (fun m : Module.End (ZMod 2) V => m v) this
    simpa using this.symm
  · rintro hf g ⟨h, hh, rfl⟩
    apply LinearMap.ext
    intro v
    simpa using (hf h hh v).symm

theorem injective_of_mem_commutantOf {H : Subgroup (GLV V)} (hirr : IsIrr H ⊤)
    {f : Module.End (ZMod 2) V} (hf : f ∈ commutantOf H) (hne : f ≠ 0) :
    Function.Injective f := by
  rw [mem_commutantOf] at hf
  have hinv : Invariant H (LinearMap.ker f) := by
    intro h hh u hu
    rw [LinearMap.mem_ker] at hu ⊢
    rw [hf h hh, hu, map_zero]
  rcases hirr.2.2 (LinearMap.ker f) hinv bot_le le_top with h | h
  · exact LinearMap.ker_eq_bot.1 h
  · exact absurd (LinearMap.ker_eq_top.1 h) hne

theorem nontrivial_of_isIrr_top {H : Subgroup (GLV V)} (hirr : IsIrr H ⊤) : Nontrivial V := by
  have := hirr.2.1
  by_contra hcon
  rw [not_nontrivial_iff_subsingleton] at hcon
  exact absurd (Subsingleton.elim (⊥ : Submodule (ZMod 2) V) ⊤ ▸ this) (lt_irrefl _)

theorem commutantOf_noZeroDivisors {H : Subgroup (GLV V)} (hirr : IsIrr H ⊤) :
    NoZeroDivisors ↥(commutantOf H) := by
  have : Nontrivial V := nontrivial_of_isIrr_top hirr
  constructor
  intro a b hab
  by_contra hcon
  push Not at hcon
  have ha := injective_of_mem_commutantOf hirr a.2 (fun h => hcon.1 (Subtype.ext h))
  have hb := injective_of_mem_commutantOf hirr b.2 (fun h => hcon.2 (Subtype.ext h))
  have hab' : ((a : Module.End (ZMod 2) V) * (b : Module.End (ZMod 2) V)) = 0 := by
    have := congrArg Subtype.val hab
    simpa using this
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have h1 : (a : Module.End (ZMod 2) V) ((b : Module.End (ZMod 2) V) v) = 0 := by
    have := congrArg (fun m : Module.End (ZMod 2) V => m v) hab'
    simpa using this
  have h2 : (b : Module.End (ZMod 2) V) v = 0 := ha (by rw [h1, map_zero])
  exact hv (hb (by rw [h2, map_zero]))

theorem finite_end [Finite V] : Finite (Module.End (ZMod 2) V) :=
  Finite.of_injective (fun f : Module.End (ZMod 2) V => (f : V → V)) DFunLike.coe_injective

@[expose, instance_reducible] noncomputable def commDivRing [Finite V] {H : Subgroup (GLV V)}
    (hirr : IsIrr H ⊤) : DivisionRing ↥(commutantOf H) := by
  classical
  have : NoZeroDivisors ↥(commutantOf H) := commutantOf_noZeroDivisors hirr
  have : Nontrivial V := nontrivial_of_isIrr_top hirr
  have : Nontrivial ↥(commutantOf H) := ⟨⟨0, 1, fun h => by
    have := congrArg (fun f : ↥(commutantOf H) => (f : Module.End (ZMod 2) V)) h
    simp at this⟩⟩
  have : IsDomain ↥(commutantOf H) := NoZeroDivisors.to_isDomain _
  have := finite_end (V := V)
  have : Fintype ↥(commutantOf H) := Fintype.ofFinite _
  exact Fintype.divisionRingOfIsDomain ↥(commutantOf H)

@[expose, instance_reducible] noncomputable def commField [Finite V] {H : Subgroup (GLV V)}
    (hirr : IsIrr H ⊤) : Field ↥(commutantOf H) :=
  have := finite_end (V := V)
  @littleWedderburn _ (commDivRing hirr) inferInstance

@[expose] def CommF (H : Subgroup (GLV V)) (_hirr : IsIrr H ⊤) : Type := ↥(commutantOf H)

variable {H : Subgroup (GLV V)} {hirr : IsIrr H ⊤}

@[expose] def CommF.val (e : CommF H hirr) : Module.End (ZMod 2) V :=
  (e : ↥(commutantOf H)).1

theorem CommF.val_mem (e : CommF H hirr) : e.val ∈ commutantOf H :=
  (e : ↥(commutantOf H)).2

theorem CommF.val_injective :
    Function.Injective (CommF.val : CommF H hirr → Module.End (ZMod 2) V) :=
  fun _ _ h => Subtype.ext h

@[expose] def CommF.mk (f : Module.End (ZMod 2) V) (hf : f ∈ commutantOf H) : CommF H hirr :=
  (⟨f, hf⟩ : ↥(commutantOf H))

@[simp] theorem CommF.val_mk (f : Module.End (ZMod 2) V) (hf : f ∈ commutantOf H) :
    (CommF.mk (hirr := hirr) f hf).val = f := rfl

@[expose] def conjEnd (γ : GLV V) (f : Module.End (ZMod 2) V) : Module.End (ZMod 2) V :=
  (γ : V →ₗ[ZMod 2] V) * f * ((γ⁻¹ : GLV V) : V →ₗ[ZMod 2] V)

theorem conjEnd_apply (γ : GLV V) (f : Module.End (ZMod 2) V) (v : V) :
    conjEnd γ f v = γ (f (γ⁻¹ v)) := rfl

theorem conjEnd_mem {γ : GLV V} (hγ' : ∀ h ∈ H, γ⁻¹ * h * γ ∈ H)
    {f : Module.End (ZMod 2) V} (hf : f ∈ commutantOf H) : conjEnd γ f ∈ commutantOf H := by
  rw [mem_commutantOf] at hf ⊢
  intro h hh v
  have h1 := hγ' h hh
  have e1 : γ⁻¹ (h v) = (γ⁻¹ * h * γ) (γ⁻¹ v) := by simp
  rw [conjEnd_apply, conjEnd_apply, e1, hf _ h1]
  simp

theorem conjEnd_conjEnd (γ : GLV V) (f : Module.End (ZMod 2) V) :
    conjEnd γ⁻¹ (conjEnd γ f) = f := by
  apply LinearMap.ext
  intro v
  simp [conjEnd_apply]

theorem conjEnd_conjEnd' (γ : GLV V) (f : Module.End (ZMod 2) V) :
    conjEnd γ (conjEnd γ⁻¹ f) = f := by
  have := conjEnd_conjEnd γ⁻¹ f
  simpa using this

section Instances

variable [Finite V]

noncomputable instance : Field (CommF H hirr) := commField hirr

instance : Finite (CommF H hirr) :=
  have := finite_end (V := V)
  inferInstanceAs (Finite ↥(commutantOf H))

theorem CommF.val_mul (a b : CommF H hirr) : (a * b).val = a.val * b.val := rfl

theorem CommF.val_add (a b : CommF H hirr) : (a + b).val = a.val + b.val := rfl

theorem CommF.val_one : (1 : CommF H hirr).val = 1 := rfl

theorem CommF.val_zero : (0 : CommF H hirr).val = 0 := rfl

noncomputable instance : Module (CommF H hirr) V :=
  Module.compHom V
    ({ toFun := CommF.val, map_one' := CommF.val_one, map_mul' := CommF.val_mul,
       map_zero' := CommF.val_zero, map_add' := CommF.val_add } :
      CommF H hirr →+* Module.End (ZMod 2) V)

theorem CommF.smul_def (e : CommF H hirr) (v : V) : e • v = e.val v := rfl

@[expose] noncomputable def CommF.conj (γ : GLV V)
    (hγ : ∀ h ∈ H, γ * h * γ⁻¹ ∈ H) (hγ' : ∀ h ∈ H, γ⁻¹ * h * γ ∈ H) :
    CommF H hirr ≃+* CommF H hirr where
  toFun f := CommF.mk (conjEnd γ f.val) (conjEnd_mem hγ' f.val_mem)
  invFun f := CommF.mk (conjEnd γ⁻¹ f.val) (conjEnd_mem (by simpa using hγ) f.val_mem)
  left_inv f := CommF.val_injective (by simp [conjEnd_conjEnd])
  right_inv f := CommF.val_injective (by simp [conjEnd_conjEnd'])
  map_mul' f g := CommF.val_injective (by
    rw [CommF.val_mk, CommF.val_mul, CommF.val_mul, CommF.val_mk, CommF.val_mk]
    apply LinearMap.ext
    intro v
    simp [conjEnd_apply])
  map_add' f g := CommF.val_injective (by
    rw [CommF.val_mk, CommF.val_add, CommF.val_add, CommF.val_mk, CommF.val_mk]
    apply LinearMap.ext
    intro v
    simp [conjEnd_apply])

theorem CommF.conj_smul (γ : GLV V) (hγ : ∀ h ∈ H, γ * h * γ⁻¹ ∈ H)
    (hγ' : ∀ h ∈ H, γ⁻¹ * h * γ ∈ H) (e : CommF H hirr) (v : V) :
    γ (e • v) = (CommF.conj γ hγ hγ' e) • γ v := by
  rw [CommF.smul_def, CommF.smul_def]
  show γ (e.val v) = (conjEnd γ e.val) (γ v)
  simp [conjEnd_apply]

theorem CommF.exists_semilinear (Γ : Subgroup (GLV V))
    (hnorm : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H) {γ : GLV V} (hγ : γ ∈ Γ) :
    ∃ σ : CommF H hirr ≃+* CommF H hirr, ∀ (e : CommF H hirr) (v : V), γ (e • v) = σ e • γ v := by
  have h1 : ∀ h ∈ H, γ * h * γ⁻¹ ∈ H := hnorm γ hγ
  have h2 : ∀ h ∈ H, γ⁻¹ * h * γ ∈ H := fun h hh => by
    simpa using hnorm γ⁻¹ (Γ.inv_mem hγ) h hh
  exact ⟨CommF.conj γ h1 h2, fun e v => CommF.conj_smul γ h1 h2 e v⟩

theorem CommF.card_le (K : Type) [Field K] (sc : K →+* Module.End (ZMod 2) V)
    (hsc : ∀ κ, ∀ h ∈ H, ∀ v, sc κ (h v) = h (sc κ v)) :
    Nat.card K ≤ Nat.card (CommF H hirr) := by
  have : Nontrivial V := nontrivial_of_isIrr_top hirr
  let f : K → CommF H hirr := fun κ => CommF.mk (sc κ) (mem_commutantOf.2 (hsc κ))
  have hf : Function.Injective f := by
    intro κ κ' h
    exact sc.injective (congrArg CommF.val h)
  exact Nat.card_le_card_of_injective f hf

end Instances

end CFSG.Quasithin.SzG11NC
