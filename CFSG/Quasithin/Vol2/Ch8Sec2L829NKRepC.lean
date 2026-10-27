module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829NKRepDefs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.L829NK

open CFSG.ProperTwoGeneratedCore.BinaryThreeSpace CFSG.Quasithin.H.SL3Rep

theorem nk_inSubrep_bot_eq {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) GS W} (A : Subrepresentation ρ) :
    (inSubrep (⊥ : Subrepresentation ρ) A).toSubmodule = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  have hx' : (x : W) ∈ (⊥ : Submodule (ZMod 2) W) := hx
  exact Subtype.ext ((Submodule.mem_bot (ZMod 2)).mp hx')

theorem nk_exists_covering_bot {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    [Nontrivial W] (ρ : Representation (ZMod 2) GS W) :
    ∃ A : Subrepresentation ρ, (⊥ : Subrepresentation ρ) < A ∧
      ∀ C : Subrepresentation ρ, (⊥ : Subrepresentation ρ) < C → ¬C < A := by
  have : Module.Finite (ZMod 2) W := Module.finite_iff_finite.mpr inferInstance
  obtain ⟨x, hx⟩ := exists_ne (0 : W)
  obtain ⟨n, c, hc0, hcn, hc⟩ := exists_series (⊤ : Subrepresentation ρ)
  have hn : n ≠ 0 := by
    rintro rfl
    apply bot_ne_top_of_ne_zero ρ hx
    rw [← hc0, ← hcn]
    all_goals rfl
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  obtain ⟨h1, h2⟩ := hc 0
  rw [Fin.castSucc_zero, hc0] at h1 h2
  exact ⟨c (Fin.succ 0), h1, h2⟩

theorem nk_transport {W M : Type} [AddCommGroup W] [Module (ZMod 2) W] [AddCommMonoid M]
    [Module (ZMod 2) M] {ρ : Representation (ZMod 2) GS W} (A : Subrepresentation ρ)
    {σ : Representation (ZMod 2) GS M}
    (φ : (inSubrep (⊥ : Subrepresentation ρ) A).quotient.Equiv σ) :
    ∃ f : A.toSubmodule ≃ₗ[ZMod 2] M, ∀ (g : GS) (u : A.toSubmodule),
      f ⟨ρ g u, A.apply_mem_toSubmodule g u.2⟩ = σ g (f u) := by
  have hI := nk_inSubrep_bot_eq A
  let e : A.toSubmodule ≃ₗ[ZMod 2]
      A.toSubmodule ⧸ (inSubrep (⊥ : Subrepresentation ρ) A).toSubmodule :=
    (Submodule.quotEquivOfEqBot _ hI).symm
  refine ⟨e.trans φ.toLinearEquiv, fun g u => ?_⟩
  have h2 : e ⟨ρ g u, A.apply_mem_toSubmodule g u.2⟩ =
      (inSubrep (⊥ : Subrepresentation ρ) A).quotient g (e u) := rfl
  show φ.toLinearEquiv (e ⟨ρ g u, A.apply_mem_toSubmodule g u.2⟩) =
    σ g (φ.toLinearEquiv (e u))
  rw [h2]
  exact Representation.IntertwiningMap.isIntertwining _ _ φ.toIntertwiningMap g (e u)

theorem nk_exists_model_sub {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    [Nontrivial W] (ρ : Representation (ZMod 2) GS W) :
    ∃ (U : Submodule (ZMod 2) W) (hU : ∀ g, ∀ u ∈ U, ρ g u ∈ U), U ≠ ⊥ ∧
      ((∃ f : U ≃ₗ[ZMod 2] ZMod 2, ∀ g (u : U), f ⟨ρ g u, hU g u u.2⟩ = f u) ∨
       (∃ f : U ≃ₗ[ZMod 2] VS, ∀ g (u : U), f ⟨ρ g u, hU g u u.2⟩ = g (f u)) ∨
       (∃ f : U ≃ₗ[ZMod 2] Module.Dual (ZMod 2) VS, ∀ g (u : U),
          f ⟨ρ g u, hU g u u.2⟩ = (f u).comp (g.symm : VS →ₗ[ZMod 2] VS)) ∨
       (∃ f : U ≃ₗ[ZMod 2] traceZeroEnd VS, ∀ g (u : U),
          ((f ⟨ρ g u, hU g u u.2⟩ : traceZeroEnd VS) : Module.End (ZMod 2) VS) =
            (g : VS →ₗ[ZMod 2] VS) ∘ₗ ((f u : traceZeroEnd VS) : Module.End (ZMod 2) VS) ∘ₗ
              (g.symm : VS →ₗ[ZMod 2] VS))) := by
  classical
  let _ : Fintype (Module.Dual (ZMod 2) VS) := Fintype.ofFinite _
  obtain ⟨A, hAB, hcov⟩ := nk_exists_covering_bot ρ
  have hQ : (inSubrep (⊥ : Subrepresentation ρ) A).quotient.IsIrreducible :=
    quotient_isIrreducible hAB hcov
  have hfinQ : Finite (A.toSubmodule ⧸ (inSubrep (⊥ : Subrepresentation ρ) A).toSubmodule) :=
    Finite.of_surjective (Submodule.Quotient.mk : A.toSubmodule → _)
      (Submodule.Quotient.mk_surjective _)
  refine ⟨A.toSubmodule, fun g u hu => A.apply_mem_toSubmodule g hu, ?_, ?_⟩
  · intro h
    exact hAB.ne' (Subrepresentation.ext h)
  · rcases exists_equiv_model finrank_V3 (inSubrep (⊥ : Subrepresentation ρ) A).quotient hQ
      with h | h | h | h
    · obtain ⟨φ⟩ := h
      obtain ⟨f, hf⟩ := nk_transport A φ
      exact Or.inl ⟨f, fun g u => (hf g u).trans (trivRep_apply g _)⟩
    · obtain ⟨φ⟩ := h
      obtain ⟨f, hf⟩ := nk_transport A φ
      exact Or.inr (Or.inl ⟨f, fun g u => (hf g u).trans (natRep_apply g _)⟩)
    · obtain ⟨φ⟩ := h
      obtain ⟨f, hf⟩ := nk_transport A φ
      exact Or.inr (Or.inr (Or.inl ⟨f, fun g u =>
        (hf g u).trans (LinearMap.ext fun v => dualRep_apply g _ v)⟩))
    · obtain ⟨φ⟩ := h
      obtain ⟨f, hf⟩ := nk_transport A φ
      exact Or.inr (Or.inr (Or.inr ⟨f, fun g u =>
        (congrArg Subtype.val (hf g u)).trans (adjRep_apply g _)⟩))

end CFSG.Quasithin.H13.L829NK
