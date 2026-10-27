module

public import CFSG.Quasithin.Background.G11Defs

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.Quasithin CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

private theorem map_eq_of_invariant {K : Subgroup (GLV V)} {W : Submodule (ZMod 2) V}
    (hW : Invariant K W) (k : K) :
    W.map ((k : GLV V) : V →ₛₗ[RingHom.id (ZMod 2)] V) = W := by
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    exact hW k k.2 w hw
  · intro w hw
    refine ⟨(k : GLV V).symm w, hW (k : GLV V)⁻¹ (inv_mem k.2) w hw, ?_⟩
    simp

noncomputable def restrictHom (K : Subgroup (GLV V)) (W : Submodule (ZMod 2) V)
    (hW : Invariant K W) : ↥K →* GLV ↥W where
  toFun k := (k : GLV V).ofSubmodules W W (map_eq_of_invariant hW k)
  map_one' := by ext x; simp
  map_mul' a b := by ext x; simp

theorem restrictHom_apply (K : Subgroup (GLV V)) (W : Submodule (ZMod 2) V)
    (hW : Invariant K W) (k : K) (w : W) :
    ((restrictHom K W hW k w : W) : V) = (k : GLV V) (w : V) := by
  simp [restrictHom]

noncomputable def quotientHom (K : Subgroup (GLV V)) (W : Submodule (ZMod 2) V)
    (hW : Invariant K W) : ↥K →* GLV (V ⧸ W) where
  toFun k := Submodule.Quotient.equiv W W (k : GLV V) (map_eq_of_invariant hW k)
  map_one' := by
    ext x
    induction x using Submodule.Quotient.induction_on
    simp [Submodule.Quotient.equiv_apply]
  map_mul' a b := by
    ext x
    induction x using Submodule.Quotient.induction_on
    simp [Submodule.Quotient.equiv_apply]

theorem quotientHom_apply (K : Subgroup (GLV V)) (W : Submodule (ZMod 2) V)
    (hW : Invariant K W) (k : K) (v : V) :
    quotientHom K W hW k (Submodule.Quotient.mk v) = Submodule.Quotient.mk ((k : GLV V) v) := by
  simp [quotientHom, Submodule.Quotient.equiv_apply]

theorem restrict_trichotomy [Finite V] {K : Subgroup (GLV V)} {M : ℕ}
    (hM : ∀ (U : Type) [AddCommGroup U] [Module (ZMod 2) U] [Finite U] (ρ : ↥K →* GLV U),
      Module.finrank (ZMod 2) U < M → ∀ k, ρ k = 1)
    (hd : Module.finrank (ZMod 2) V < 2 * M) (hV : Nontrivial V) :
    (∃ v : V, v ≠ 0 ∧ ∀ k ∈ K, k v = v) ∨
    (∃ f : V →ₗ[ZMod 2] ZMod 2, f ≠ 0 ∧ ∀ k ∈ K, ∀ v, f (k v) = f v) ∨
    IsIrr K ⊤ := by
  have hTinv : Invariant K (⊤ : Submodule (ZMod 2) V) := fun _ _ _ _ => Submodule.mem_top
  have hne : (⊤ : Submodule (ZMod 2) V) ≠ ⊥ := top_ne_bot
  obtain ⟨W, ⟨hWne, hWinv⟩, hWmin⟩ := WellFounded.has_min
    (wellFounded_lt (α := Submodule (ZMod 2) V))
    {W : Submodule (ZMod 2) V | W ≠ ⊥ ∧ Invariant K W} ⟨⊤, hne, hTinv⟩
  have hmin : ∀ J : Submodule (ZMod 2) V, Invariant K J → J ≠ ⊥ → ¬ J < W :=
    fun J hJ hJne => hWmin J ⟨hJne, hJ⟩
  by_cases htriv : ∀ k, restrictHom K W hWinv k = 1
  · left
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWne
    refine ⟨w, hw0, fun k hk => ?_⟩
    have := congrArg (fun g : GLV W => ((g ⟨w, hw⟩ : W) : V)) (htriv ⟨k, hk⟩)
    simpa [restrictHom_apply] using this
  · right
    push Not at htriv
    obtain ⟨k0, hk0⟩ := htriv
    have hge : M ≤ Module.finrank (ZMod 2) W := by
      by_contra hlt
      exact hk0 (hM W (restrictHom K W hWinv) (not_le.1 hlt) k0)
    have hsum := Submodule.finrank_quotient_add_finrank W
    have : Finite (V ⧸ W) := Quotient.finite _
    have hq : Module.finrank (ZMod 2) (V ⧸ W) < M := by omega
    have hqtriv := hM (V ⧸ W) (quotientHom K W hWinv) hq
    by_cases hWtop : W = ⊤
    · right
      subst hWtop
      refine ⟨hTinv, bot_lt_iff_ne_bot.2 hne, ?_⟩
      · intro J hJ _ _
        by_cases hJb : J = ⊥
        · exact Or.inl hJb
        · right
          by_contra hJt
          exact hmin J hJ hJb (lt_top_iff_ne_top.2 hJt)
    · left
      have hlt : W < ⊤ := lt_top_iff_ne_top.2 hWtop
      have : Nontrivial (V ⧸ W) := Submodule.Quotient.nontrivial_iff.2 hWtop
      obtain ⟨q, hq0⟩ := exists_ne (0 : V ⧸ W)
      obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Module.Dual (ZMod 2) (V ⧸ W), ℓ q ≠ 0 := by
        by_contra h
        push Not at h
        exact hq0 ((Module.forall_dual_apply_eq_zero_iff (ZMod 2) q).1 h)
      refine ⟨ℓ.comp W.mkQ, ?_, fun k hk v => ?_⟩
      · intro h
        obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective W q
        exact hℓ (by simpa using LinearMap.congr_fun h v)
      · have := hqtriv ⟨k, hk⟩
        have h2 := congrArg (fun g : GLV (V ⧸ W) => ℓ (g (W.mkQ v))) this
        simpa [quotientHom_apply] using h2

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
