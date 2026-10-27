module

public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.Quasithin.SteinbergCF

variable {k E V : Type*} [CommRing k] [Group E] [AddCommGroup V] [Module k V]
  {ρ : Representation k E V}

@[expose] def factorSub (U U' : Subrepresentation ρ) : Submodule k U'.toSubmodule :=
  U.toSubmodule.comap U'.toSubmodule.subtype

theorem mem_factorSub {U U' : Subrepresentation ρ} {x : U'.toSubmodule} :
    x ∈ factorSub U U' ↔ (x : V) ∈ U.toSubmodule :=
  Iff.rfl

@[expose] def factorRep (U U' : Subrepresentation ρ) :
    Representation k E (U'.toSubmodule ⧸ factorSub U U') :=
  U'.toRepresentation.quotient (factorSub U U') fun g _ hx => U.apply_mem_toSubmodule g hx

theorem factorRep_mk (U U' : Subrepresentation ρ) (g : E) (x : U'.toSubmodule) :
    factorRep U U' g (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (U'.toRepresentation g x) :=
  rfl

theorem factorRep_eq_self_iff (U U' : Subrepresentation ρ) (g : E) :
    (∀ w, factorRep U U' g w = w) ↔ ∀ x ∈ U'.toSubmodule, ρ g x - x ∈ U.toSubmodule := by
  constructor
  · intro h x hx
    have h1 := h (Submodule.Quotient.mk ⟨x, hx⟩)
    rw [factorRep_mk, Submodule.Quotient.eq, mem_factorSub] at h1
    exact h1
  · intro h w
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    rw [factorRep_mk, Submodule.Quotient.eq, mem_factorSub]
    exact h x x.2

theorem sub_mem_of_isPerfect (ρ : Representation k E V) {L : Subgroup E}
    (hLp : Group.IsPerfect L) {U Z : Submodule k V} (hU : ∀ l ∈ L, ∀ u ∈ U, ρ l u - u ∈ Z)
    {x : V} (hx : ∀ l ∈ L, ρ l x - x ∈ U) : ∀ l ∈ L, ρ l x - x ∈ Z := by
  let δ : L →* Multiplicative (V ⧸ Z) :=
    { toFun := fun l => Multiplicative.ofAdd (Submodule.Quotient.mk (ρ l x - x))
      map_one' := by simp
      map_mul' := fun a b => by
        rw [← ofAdd_add, ← Submodule.Quotient.mk_add]
        congr 1
        rw [Submodule.Quotient.eq]
        have h := hU a a.2 (ρ b x - x) (hx b b.2)
        convert h using 1
        simp only [Subgroup.coe_mul, map_mul, Module.End.mul_apply, map_sub]
        abel }
  intro l hl
  have hker : (⟨l, hl⟩ : L) ∈ δ.ker := by
    have h := Abelianization.commutator_subset_ker δ
    rw [hLp.commutator_eq_top] at h
    exact h (Subgroup.mem_top _)
  have h := MonoidHom.mem_ker.mp hker
  rw [← Submodule.Quotient.mk_eq_zero]
  exact ofAdd_eq_one.mp h

theorem perfect_normal_one_factor_commutator_module_fixed_kernel (ρ : Representation k E V)
    {L : Subgroup E} (hLp : Group.IsPerfect L)
    (hVL : Submodule.span k {w | ∃ l ∈ L, ∃ v : V, w = ρ l v - v} = ⊤)
    {r : ℕ} (Us : Fin (r + 1) → Subrepresentation ρ) (h0 : Us 0 = ⊥)
    (hr : Us (Fin.last r) = ⊤) (j : Fin r)
    (hW : ∀ i : Fin r, (∃ l ∈ L, ∃ w, factorRep (Us i.castSucc) (Us i.succ) l w ≠ w) ↔ i = j)
    (hCW : ∀ w, (∀ l ∈ L, factorRep (Us j.castSucc) (Us j.succ) l w = w) → w = 0) :
    ((Us j.succ).toSubmodule = ⊤ ∧
      (Us j.castSucc).toSubmodule = Representation.invariants (ρ.comp L.subtype)) ∧
    (∀ g : E, ∀ v ∈ Representation.invariants (ρ.comp L.subtype),
      ρ g v ∈ Representation.invariants (ρ.comp L.subtype)) ∧
    (∃ f : V →ₗ[k] (Us j.succ).toSubmodule ⧸ factorSub (Us j.castSucc) (Us j.succ),
      ρ.IsIntertwiningMap (factorRep (Us j.castSucc) (Us j.succ)) f ∧ Function.Surjective f ∧
        LinearMap.ker f = Representation.invariants (ρ.comp L.subtype)) ∧
    ∃ e : (V ⧸ Representation.invariants (ρ.comp L.subtype)) ≃ₗ[k]
        (Us j.succ).toSubmodule ⧸ factorSub (Us j.castSucc) (Us j.succ),
      ∀ (g : E) (v : V), e (Submodule.Quotient.mk (ρ g v)) =
        factorRep (Us j.castSucc) (Us j.succ) g (e (Submodule.Quotient.mk v)) := by
  set C := Representation.invariants (ρ.comp L.subtype) with hC
  have htriv : ∀ i : Fin r, i ≠ j → ∀ l ∈ L, ∀ x ∈ (Us i.succ).toSubmodule,
      ρ l x - x ∈ (Us i.castSucc).toSubmodule := by
    intro i hij l hl
    refine (factorRep_eq_self_iff _ _ l).mp fun w => ?_
    by_contra hw
    exact hij ((hW i).mp ⟨l, hl, w, hw⟩)
  have hlow : ∀ i : Fin (r + 1), i ≤ j.castSucc → ∀ l ∈ L, ∀ x ∈ (Us i).toSubmodule,
      ρ l x - x ∈ (⊥ : Submodule k V) := by
    intro i
    induction i using Fin.induction with
    | zero =>
      intro _ l _ x hx
      rw [h0] at hx
      change x ∈ (⊥ : Submodule k V) at hx
      rw [(Submodule.mem_bot k).mp hx, map_zero, sub_zero]
      exact Submodule.zero_mem _
    | succ i ih =>
      intro hi
      have hij : i < j := by
        rw [Fin.le_def, Fin.val_succ, Fin.val_castSucc] at hi
        exact Fin.lt_def.mpr (by omega)
      intro l hl x hx
      refine sub_mem_of_isPerfect ρ hLp (U := (Us i.castSucc).toSubmodule) ?_
        (fun l hl => htriv i hij.ne l hl x hx) l hl
      exact ih (Fin.le_def.mpr (by rw [Fin.val_castSucc, Fin.val_castSucc]; omega))
  have hhigh : ∀ i : Fin (r + 1), j.succ ≤ i → ∀ l ∈ L, ∀ x ∈ (Us i).toSubmodule,
      ρ l x - x ∈ (Us j.succ).toSubmodule := by
    intro i
    induction i using Fin.induction with
    | zero =>
      intro hi
      exact absurd (Fin.le_def.mp hi) (by rw [Fin.val_succ, Fin.val_zero]; omega)
    | succ i ih =>
      intro hi l hl x hx
      rcases eq_or_ne i j with rfl | hij
      · exact Submodule.sub_mem _ ((Us i.succ).apply_mem_toSubmodule l hx) hx
      · have hji : j.succ ≤ i.castSucc := by
          have h1 := Fin.le_def.mp hi
          have h2 : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
          rw [Fin.val_succ, Fin.val_succ] at h1
          rw [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
          omega
        exact sub_mem_of_isPerfect ρ hLp (U := (Us i.castSucc).toSubmodule) (ih hji)
          (fun l hl => htriv i hij l hl x hx) l hl
  have hsucc : (Us j.succ).toSubmodule = ⊤ := by
    rw [eq_top_iff, ← hVL, Submodule.span_le]
    rintro _ ⟨l, hl, v, rfl⟩
    refine hhigh (Fin.last r) (Fin.le_last _) l hl v ?_
    rw [hr]
    exact Submodule.mem_top
  let f : V →ₗ[k] (Us j.succ).toSubmodule ⧸ factorSub (Us j.castSucc) (Us j.succ) :=
    (factorSub (Us j.castSucc) (Us j.succ)).mkQ ∘ₗ (LinearEquiv.ofTop _ hsucc).symm.toLinearMap
  have hf : ∀ v : V, f v = Submodule.Quotient.mk ⟨v, hsucc.symm ▸ Submodule.mem_top⟩ :=
    fun v => rfl
  have hfint : ∀ (g : E) (v : V), f (ρ g v) = factorRep (Us j.castSucc) (Us j.succ) g (f v) :=
    fun g v => rfl
  have hfsurj : Function.Surjective f :=
    (Submodule.mkQ_surjective _).comp (LinearEquiv.ofTop _ hsucc).symm.surjective
  have hker : LinearMap.ker f = (Us j.castSucc).toSubmodule := by
    ext v
    rw [LinearMap.mem_ker, hf, Submodule.Quotient.mk_eq_zero, mem_factorSub]
  have hjC : (Us j.castSucc).toSubmodule = C := by
    apply le_antisymm
    · intro v hv g
      have h := hlow j.castSucc le_rfl g g.2 v hv
      rw [Submodule.mem_bot, sub_eq_zero] at h
      exact h
    · intro v hv
      rw [← hker, LinearMap.mem_ker]
      refine hCW (f v) fun l hl => ?_
      rw [← hfint, show ρ l v = v from hv ⟨l, hl⟩]
  have hkerC : LinearMap.ker f = C := hker.trans hjC
  refine ⟨⟨hsucc, hjC⟩, fun g v hv => ?_, ⟨f, ⟨hfint⟩, hfsurj, hkerC⟩, ?_⟩
  · rw [← hjC] at hv ⊢
    exact (Us j.castSucc).apply_mem_toSubmodule g hv
  · refine ⟨(Submodule.quotEquivOfEq _ _ hkerC.symm).trans (f.quotKerEquivOfSurjective hfsurj),
      fun g v => ?_⟩
    exact hfint g v

end CFSG.Quasithin.SteinbergCF
