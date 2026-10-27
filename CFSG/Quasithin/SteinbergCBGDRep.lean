module

public import CFSG.Quasithin.SteinbergCBGDFrob
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Quasithin.SteinbergCB.GDescent

open Matrix

variable {F : Type*} [Field F] {X : Type*} [Group X] {d : ℕ}

@[expose] def IsIrredRep (ρ : X →* GL (Fin d) F) : Prop :=
  ∀ W : Submodule F (Fin d → F), (∀ g, ∀ w ∈ W, (ρ g : Matrix (Fin d) (Fin d) F) *ᵥ w ∈ W) →
    W = ⊥ ∨ W = ⊤

@[expose] def RepIso (ρ ρ' : X →* GL (Fin d) F) : Prop :=
  ∃ P : GL (Fin d) F, ∀ g, ρ' g = P * ρ g * P⁻¹

@[expose] def conjRep (P : GL (Fin d) F) (ρ : X →* GL (Fin d) F) : X →* GL (Fin d) F :=
  (MulAut.conj P).toMonoidHom.comp ρ

@[expose] def twistRep (τ : F ≃+* F) (ρ : X →* GL (Fin d) F) : X →* GL (Fin d) F :=
  (Matrix.GeneralLinearGroup.map (τ : F →+* F)).comp ρ

@[expose] def Realizable (ρ : X →* GL (Fin d) F) (E : Subfield F) : Prop :=
  ∃ P : GL (Fin d) F, ∀ g i j, ((P * ρ g * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) i j ∈ E

@[expose] def traceField (ρ : X →* GL (Fin d) F) : Subfield F :=
  Subfield.closure (Set.range fun g => Matrix.trace (ρ g : Matrix (Fin d) (Fin d) F))

theorem twistRep_val (τ : F ≃+* F) (ρ : X →* GL (Fin d) F) (g : X) :
    ((twistRep τ ρ g : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
      (ρ g : Matrix (Fin d) (Fin d) F).map τ := rfl

theorem RepIso.symm {ρ ρ' : X →* GL (Fin d) F} (h : RepIso ρ ρ') : RepIso ρ' ρ := by
  obtain ⟨P, hP⟩ := h
  exact ⟨P⁻¹, fun g => by rw [hP]; group⟩

theorem RepIso.trans {ρ ρ' ρ'' : X →* GL (Fin d) F} (h : RepIso ρ ρ') (h' : RepIso ρ' ρ'') :
    RepIso ρ ρ'' := by
  obtain ⟨P, hP⟩ := h
  obtain ⟨Q, hQ⟩ := h'
  exact ⟨Q * P, fun g => by rw [hQ, hP]; group⟩

theorem repIso_conjRep (P : GL (Fin d) F) (ρ : X →* GL (Fin d) F) : RepIso ρ (conjRep P ρ) :=
  ⟨P, fun _ => rfl⟩

theorem trace_conj (P A : GL (Fin d) F) :
    Matrix.trace ((P * A * P⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
      Matrix.trace (A : Matrix (Fin d) (Fin d) F) := by
  rw [Units.val_mul, Units.val_mul]
  exact Matrix.trace_units_conj P _

theorem RepIso.trace_eq {ρ ρ' : X →* GL (Fin d) F} (h : RepIso ρ ρ') (g : X) :
    Matrix.trace (ρ' g : Matrix (Fin d) (Fin d) F) =
      Matrix.trace (ρ g : Matrix (Fin d) (Fin d) F) := by
  obtain ⟨P, hP⟩ := h
  rw [hP, trace_conj]

theorem RepIso.twist {ρ ρ' : X →* GL (Fin d) F} (h : RepIso ρ ρ') (τ : F ≃+* F) :
    RepIso (twistRep τ ρ) (twistRep τ ρ') := by
  obtain ⟨P, hP⟩ := h
  refine ⟨Matrix.GeneralLinearGroup.map (τ : F →+* F) P, fun g => ?_⟩
  change Matrix.GeneralLinearGroup.map (τ : F →+* F) (ρ' g) = _
  rw [hP, map_mul, map_mul, map_inv]
  rfl

theorem trace_twistRep (τ : F ≃+* F) (ρ : X →* GL (Fin d) F) (g : X) :
    Matrix.trace ((twistRep τ ρ g : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
      τ (Matrix.trace (ρ g : Matrix (Fin d) (Fin d) F)) := by
  rw [twistRep_val]
  exact (AddMonoidHom.map_trace τ _).symm

theorem twistRep_eq_self {τ : F ≃+* F} {ρ : X →* GL (Fin d) F}
    (h : ∀ g i j, τ ((ρ g : Matrix (Fin d) (Fin d) F) i j) = (ρ g : Matrix (Fin d) (Fin d) F) i j) :
    twistRep τ ρ = ρ := by
  ext g i j
  exact h g i j

theorem IsIrredRep.twist {ρ : X →* GL (Fin d) F} (hρ : IsIrredRep ρ) (τ : F ≃+* F) :
    IsIrredRep (twistRep τ ρ) := by
  intro W hW
  let W' : Submodule F (Fin d → F) :=
    { carrier := {v | (τ ∘ v) ∈ W}
      add_mem' := fun {v w} hv hw => by
        change τ ∘ (v + w) ∈ W
        have : τ ∘ (v + w) = τ ∘ v + τ ∘ w := by
          funext i
          simp
        rw [this]
        exact W.add_mem hv hw
      zero_mem' := by
        change τ ∘ (0 : Fin d → F) ∈ W
        have : τ ∘ (0 : Fin d → F) = 0 := by
          funext i
          simp
        rw [this]
        exact W.zero_mem
      smul_mem' := fun c v hv => by
        change τ ∘ (c • v) ∈ W
        have : τ ∘ (c • v) = τ c • (τ ∘ v) := by
          funext i
          simp
        rw [this]
        exact W.smul_mem _ hv }
  have hmem : ∀ v, v ∈ W' ↔ τ ∘ v ∈ W := fun v => Iff.rfl
  have hW' : ∀ g, ∀ w ∈ W', (ρ g : Matrix (Fin d) (Fin d) F) *ᵥ w ∈ W' := by
    intro g w hw
    rw [hmem] at hw ⊢
    have : τ ∘ ((ρ g : Matrix (Fin d) (Fin d) F) *ᵥ w) =
        ((twistRep τ ρ g : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) *ᵥ (τ ∘ w) := by
      funext i
      rw [twistRep_val]
      exact RingHom.map_mulVec (τ : F →+* F) _ w i
    rw [this]
    exact hW g _ hw
  have hsurj : ∀ w : Fin d → F, τ ∘ (τ.symm ∘ w) = w := fun w => by
    funext i
    simp
  rcases hρ W' hW' with h | h
  · left
    rw [eq_bot_iff]
    intro w hw
    have h1 : τ.symm ∘ w ∈ W' := by
      rw [hmem, hsurj]
      exact hw
    rw [h, Submodule.mem_bot] at h1
    rw [Submodule.mem_bot, ← hsurj w, h1]
    funext i
    simp
  · right
    rw [eq_top_iff]
    intro w _
    have h1 : τ.symm ∘ w ∈ W' := by
      rw [h]
      exact Submodule.mem_top
    rw [hmem, hsurj] at h1
    exact h1

theorem Realizable.mono {ρ : X →* GL (Fin d) F} {E E' : Subfield F} (h : Realizable ρ E)
    (hle : E ≤ E') : Realizable ρ E' := by
  obtain ⟨P, hP⟩ := h
  exact ⟨P, fun g i j => hle (hP g i j)⟩

theorem Realizable.traceField_le {ρ : X →* GL (Fin d) F} {E : Subfield F} (h : Realizable ρ E) :
    traceField ρ ≤ E := by
  obtain ⟨P, hP⟩ := h
  rw [traceField, Subfield.closure_le]
  rintro _ ⟨g, rfl⟩
  change Matrix.trace (ρ g : Matrix (Fin d) (Fin d) F) ∈ E
  rw [← trace_conj P (ρ g), Matrix.trace]
  exact Subfield.sum_mem _ fun i _ => hP g i i

theorem Realizable.repIso_twistRep {ρ : X →* GL (Fin d) F} {E : Subfield F} (h : Realizable ρ E)
    {τ : F ≃+* F} (hτ : ∀ x ∈ E, τ x = x) : RepIso (twistRep τ ρ) ρ := by
  obtain ⟨P, hP⟩ := h
  have h0 : twistRep τ (conjRep P ρ) = conjRep P ρ :=
    twistRep_eq_self fun g i j => hτ _ (hP g i j)
  have h1 : RepIso (twistRep τ ρ) (twistRep τ (conjRep P ρ)) :=
    (repIso_conjRep P ρ).twist τ
  rw [h0] at h1
  exact h1.trans (repIso_conjRep P ρ).symm

end CFSG.Quasithin.SteinbergCB.GDescent
