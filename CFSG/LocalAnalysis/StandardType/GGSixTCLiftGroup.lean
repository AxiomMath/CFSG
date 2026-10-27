module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepACore
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs

public section

namespace CFSG.StandardType.ClassicalPosition

section IsGLLiftLemmas

variable {U X ι F : Type} [Group U] [Group X] [Fintype ι] [DecidableEq ι] [Field F]
  {j : U →* GL ι F} {ψ : U →* X}

theorem IsGLLift.inv_of_injective [Finite U] (hj : Function.Injective j) {s : GL ι F} {b : X}
    (hs : IsGLLift j ψ s b) : IsGLLift j ψ s⁻¹ b⁻¹ := by
  classical
  choose f hfj hfb using hs
  have hfinj : Function.Injective f := by
    intro u v huv
    apply hj
    have h1 : s * j u * s⁻¹ = s * j v * s⁻¹ := by rw [← hfj u, ← hfj v, huv]
    simpa using h1
  have hfsurj : Function.Surjective f := Finite.surjective_of_injective hfinj
  intro u
  obtain ⟨w, rfl⟩ := hfsurj u
  refine ⟨w, ?_, ?_⟩
  · have h := hfj w
    calc j w = s⁻¹ * (s * j w * s⁻¹) * s := by group
      _ = s⁻¹ * j (f w) * s⁻¹⁻¹ := by rw [← h, inv_inv]
  · have h := hfb w
    calc (b⁻¹)⁻¹ * ψ (f w) * b⁻¹ = b * ψ (f w) * b⁻¹ := by rw [inv_inv]
      _ = ψ w := by rw [← h]; group

theorem IsGLLift.central_mul {s z : GL ι F} {b : X} (hs : IsGLLift j ψ s b)
    (hz : z ∈ Subgroup.center (GL ι F)) : IsGLLift j ψ (z * s) b := by
  intro u
  obtain ⟨u', hj', hb'⟩ := hs u
  refine ⟨u', ?_, hb'⟩
  rw [hj']
  have hzc : ∀ g : GL ι F, g * z = z * g := fun g => (Subgroup.mem_center_iff.mp hz g)
  have hzM : ∀ M : GL ι F, z * M * z⁻¹ = M := by
    intro M
    rw [← hzc M]
    group
  calc s * j u * s⁻¹ = z * (s * j u * s⁻¹) * z⁻¹ := (hzM _).symm
    _ = z * s * j u * (z * s)⁻¹ := by group

theorem IsGLLift.unique_of_faithful (hj : Function.Injective j) {B : Subgroup X}
    (hB : B ⊓ Subgroup.centralizer (ψ.range : Set X) = ⊥) {s : GL ι F} {b b' : X}
    (hb : b ∈ B) (hb' : b' ∈ B) (h1 : IsGLLift j ψ s b) (h2 : IsGLLift j ψ s b') : b = b' := by
  have hcent : b' * b⁻¹ ∈ Subgroup.centralizer (ψ.range : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨u, rfl⟩
    obtain ⟨u₁, hj₁, hb₁⟩ := h1 u
    obtain ⟨u₂, hj₂, hb₂⟩ := h2 u
    have hu : u₁ = u₂ := hj (hj₁.trans hj₂.symm)
    subst hu
    have h3 : b⁻¹ * ψ u * b = b'⁻¹ * ψ u * b' := hb₁.trans hb₂.symm
    calc ψ u * (b' * b⁻¹) = b' * (b'⁻¹ * ψ u * b') * b⁻¹ := by group
      _ = b' * (b⁻¹ * ψ u * b) * b⁻¹ := by rw [← h3]
      _ = b' * b⁻¹ * ψ u := by group
  have hmem : b' * b⁻¹ ∈ B ⊓ Subgroup.centralizer (ψ.range : Set X) :=
    ⟨B.mul_mem hb' (B.inv_mem hb), hcent⟩
  rw [hB, Subgroup.mem_bot] at hmem
  exact (mul_inv_eq_one.mp hmem).symm

end IsGLLiftLemmas

end CFSG.StandardType.ClassicalPosition

namespace CFSG.StandardType.TableCRes

open CFSG.StandardType.ClassicalPosition

section LiftGroup

variable {U X ι F : Type} [Group U] [Group X] [Fintype ι] [DecidableEq ι] [Field F]
  {j : U →* GL ι F} {ψ : U →* X}

variable [Finite U]

@[expose] def liftGroup (hj : Function.Injective j) (ψ : U →* X) (Q : Subgroup (GL ι F))
    (B : Subgroup X) : Subgroup (GL ι F) where
  carrier := {t | t ∈ Q ∧ ∃ b ∈ B, IsGLLift j ψ t b}
  mul_mem' := by
    rintro a c ⟨haQ, ba, hba, ha⟩ ⟨hcQ, bc, hbc, hc⟩
    exact ⟨Q.mul_mem haQ hcQ, bc * ba, B.mul_mem hbc hba, hc.mul ha⟩
  one_mem' := ⟨Q.one_mem, 1, B.one_mem, isGLLift_one⟩
  inv_mem' := by
    rintro a ⟨haQ, ba, hba, ha⟩
    exact ⟨Q.inv_mem haQ, ba⁻¹, B.inv_mem hba, IsGLLift.inv_of_injective hj ha⟩

theorem mem_liftGroup {hj : Function.Injective j} {Q : Subgroup (GL ι F)} {B : Subgroup X}
    {t : GL ι F} :
    t ∈ liftGroup hj ψ Q B ↔ t ∈ Q ∧ ∃ b ∈ B, IsGLLift j ψ t b := Iff.rfl

section LiftHom

variable {hj : Function.Injective j} {Q : Subgroup (GL ι F)} {B : Subgroup X}

noncomputable def liftVal (t : liftGroup hj ψ Q B) : X :=
  Classical.choose (mem_liftGroup.mp t.2).2

theorem liftVal_mem (t : liftGroup hj ψ Q B) : liftVal t ∈ B :=
  (Classical.choose_spec (mem_liftGroup.mp t.2).2).1

theorem isGLLift_liftVal (t : liftGroup hj ψ Q B) :
    IsGLLift j ψ (t : GL ι F) (liftVal t) :=
  (Classical.choose_spec (mem_liftGroup.mp t.2).2).2

noncomputable def liftHom (hB : B ⊓ Subgroup.centralizer (ψ.range : Set X) = ⊥)
    (hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) : liftGroup hj ψ Q B →* B where
  toFun t := ⟨liftVal t, liftVal_mem t⟩
  map_one' := by
    refine Subtype.ext ?_
    exact IsGLLift.unique_of_faithful hj hB (liftVal_mem 1) B.one_mem (isGLLift_liftVal 1)
      isGLLift_one
  map_mul' s t := by
    refine Subtype.ext ?_
    have h1 : IsGLLift j ψ ((s * t : liftGroup hj ψ Q B) : GL ι F)
        (liftVal t * liftVal s) :=
      (isGLLift_liftVal t).mul (isGLLift_liftVal s)
    have h2 := IsGLLift.unique_of_faithful hj hB (liftVal_mem (s * t))
      (B.mul_mem (liftVal_mem t) (liftVal_mem s)) (isGLLift_liftVal (s * t)) h1
    change liftVal (s * t) = liftVal s * liftVal t
    rw [h2]
    exact hBc _ (liftVal_mem t) _ (liftVal_mem s)

theorem isGLLift_liftHom (hB : B ⊓ Subgroup.centralizer (ψ.range : Set X) = ⊥)
    (hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) (t : liftGroup hj ψ Q B) :
    IsGLLift j ψ (t : GL ι F) (liftHom (hj := hj) (ψ := ψ) hB hBc t : X) :=
  isGLLift_liftVal t

theorem liftHom_surjective (hB : B ⊓ Subgroup.centralizer (ψ.range : Set X) = ⊥)
    (hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b)
    (hex : ∀ b ∈ B, ∃ s ∈ Q, IsGLLift j ψ s b) :
    Function.Surjective (liftHom (hj := hj) (ψ := ψ) (Q := Q) hB hBc) := by
  intro b
  obtain ⟨s, hsQ, hs⟩ := hex b.1 b.2
  let t : liftGroup hj ψ Q B := ⟨s, hsQ, b.1, b.2, hs⟩
  refine ⟨t, Subtype.ext ?_⟩
  exact IsGLLift.unique_of_faithful hj hB (liftVal_mem t) b.2 (isGLLift_liftVal t) hs

theorem liftHom_eq_one_iff (hB : B ⊓ Subgroup.centralizer (ψ.range : Set X) = ⊥)
    (hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) (t : liftGroup hj ψ Q B) :
    liftHom (hj := hj) (ψ := ψ) hB hBc t = 1 ↔ IsGLLift j ψ (t : GL ι F) 1 := by
  constructor
  · intro h
    have h' : liftVal t = 1 := congrArg Subtype.val h
    have := isGLLift_liftVal t
    rwa [h'] at this
  · intro h
    refine Subtype.ext ?_
    exact IsGLLift.unique_of_faithful hj hB (liftVal_mem t) B.one_mem (isGLLift_liftVal t) h

end LiftHom

end LiftGroup

end CFSG.StandardType.TableCRes
