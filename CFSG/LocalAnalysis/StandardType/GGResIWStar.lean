module

public import CFSG.LocalAnalysis.StandardType.GGResIIWStar
public import CFSG.LocalAnalysis.StandardType.GGCoxeterForkProofBCDExt

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]

theorem ggResI_linWeyl (hp2 : p ≠ 2) {I : Type} [Fintype I] [DecidableEq I]
    {M : CoxeterMatrix I} {C : Matrix I I ℤ} (hFT : TauCeti.IsFiniteType C) (hC : GGIntCartan M C)
    (hW : GGIsWeylMatrix M) (t : I → (V ≃ₗ[ZMod p] V)) (H : I → V)
    (A : I → Module.Dual (ZMod p) V) (ht : ∀ i w, t i w = w - A i w • H i)
    (hP : ∀ i j, A i (H j) = (C i j : ZMod p)) (hind : LinearIndependent (ZMod p) H) :
    ZS.LinWeyl p (Subgroup.closure (Set.range t)) := by
  classical
  have h2 : ∀ i, A i (H i) = 2 := fun i => by rw [hP, hC.1 i]; norm_num
  have hL := isLiftable_reflection_of_intCartan hC H A h2 hP
  set ρ := M.toCoxeterSystem.lift ⟨fun i => Module.reflection (h2 i), hL⟩ with hρ
  have hρinj : Function.Injective ρ := ggCartanFaithful_of_isFiniteType h2 hP hp2 hFT hC hind
  have hrefl : ∀ i, Module.reflection (h2 i) = t i := by
    intro i
    ext w
    rw [Module.reflection_apply, ht]
  have hrange : ρ.range = Subgroup.closure (Set.range t) := by
    rw [MonoidHom.range_eq_map, ← M.toCoxeterSystem.subgroup_closure_range_simple,
      MonoidHom.map_closure]
    congr 1
    ext e
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, by rw [hρ, CoxeterSystem.lift_apply_simple, hrefl]⟩
    · rintro ⟨i, rfl⟩
      exact ⟨M.toCoxeterSystem.simple i, ⟨i, rfl⟩, by
        rw [hρ, CoxeterSystem.lift_apply_simple, hrefl]⟩
  let e₁ : M.Group ≃* ρ.range := MonoidHom.ofInjective hρinj
  let f : M.Group ≃* ↥(Subgroup.closure (Set.range t)) := e₁.trans (MulEquiv.subgroupCongr hrange)
  refine ⟨I, M, hW, f, fun i => ?_⟩
  have hfi : (f (M.simple i) : V ≃ₗ[ZMod p] V) = t i := by
    change ρ (M.simple i) = t i
    rw [hρ]
    exact (CoxeterSystem.lift_apply_simple _ _ i).trans (hrefl i)
  rw [hfi]
  exact ggResII_isRefl hp2 (ht i) (h2 i)

theorem ggResI_linWeyl_T (hp2 : p ≠ 2) {I : Type} [Fintype I] [DecidableEq I]
    {M : CoxeterMatrix I} {C : Matrix I I ℤ} (hW : GGIsWeylMatrix M) (hC : GGIntCartan M C)
    (t : I → (V ≃ₗ[ZMod p] V)) (H : I → V) (A : I → Module.Dual (ZMod p) V)
    (ht : ∀ i w, t i w = w - A i w • H i) (hP : ∀ i j, A j (H i) = (C i j : ZMod p))
    (hind : LinearIndependent (ZMod p) H) : ZS.LinWeyl p (Subgroup.closure (Set.range t)) := by
  have hFT : TauCeti.IsFiniteType C := isFiniteType_of_ggIsWeylMatrixFixed hW hC
  have hCT : GGIntCartan M C.transpose := by
    refine ⟨fun i => hC.1 i, fun i j hij => ?_⟩
    have hs : M i j = M j i := M.symmetric i j
    rcases hC.2 j i (Ne.symm hij) with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3, h4⟩ |
        ⟨h1, h2, h3, h4⟩
    · exact Or.inl ⟨hs.trans h1, h2, h3⟩
    · exact Or.inr (Or.inl ⟨hs.trans h1, h2, h3⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hs.trans h1, h2, h3, h4⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hs.trans h1, h2, h3, h4⟩))
  exact ggResI_linWeyl hp2 hFT.transpose hCT hW t H A ht (fun i j => hP j i) hind

inductive GGWTypeI where
  | A | B | C | D | E | F
  deriving DecidableEq

@[expose] def ggWCartanI : GGWTypeI → (N : ℕ) → Matrix (Fin N) (Fin N) ℤ
  | .A, N => CartanMatrix.A N
  | .B, N => CartanMatrix.B N
  | .C, N => CartanMatrix.C N
  | .D, N => CartanMatrix.D N
  | .E, N => CartanMatrix.E N
  | .F, N => if h : N = 4 then CartanMatrix.F₄.submatrix (Fin.cast h) (Fin.cast h)
      else CartanMatrix.A N

@[expose] def ggWTypeOk : GGWTypeI → ℕ → Bool
  | .A, N => decide (1 ≤ N)
  | .B, N => decide (2 ≤ N)
  | .C, N => decide (2 ≤ N)
  | .D, N => decide (4 ≤ N)
  | .E, N => decide (N = 6 ∨ N = 7 ∨ N = 8)
  | .F, N => decide (N = 4)

theorem ggWCartanI_spec (typ : GGWTypeI) (N : ℕ) (hok : ggWTypeOk typ N = true) :
    ∃ M : CoxeterMatrix (Fin N), GGIsWeylMatrix M ∧ GGIntCartan M (ggWCartanI typ N) := by
  cases typ <;> simp only [ggWTypeOk, decide_eq_true_eq] at hok
  · exact ⟨CoxeterMatrix.A N, Or.inl ⟨N, Equiv.refl _, hok, Or.inl
      (ggCoxeterMatrix_reindex_refl _).symm⟩, ggIntCartan_A N⟩
  · exact ⟨CoxeterMatrix.B N, Or.inl ⟨N, Equiv.refl _, by omega, Or.inr (Or.inl
      ⟨hok, (ggCoxeterMatrix_reindex_refl _).symm⟩)⟩, ggIntCartan_B N⟩
  · exact ⟨CoxeterMatrix.B N, Or.inl ⟨N, Equiv.refl _, by omega, Or.inr (Or.inl
      ⟨hok, (ggCoxeterMatrix_reindex_refl _).symm⟩)⟩, ggIntCartan_C N⟩
  · exact ⟨ggCoxeterMatrixD N, Or.inl ⟨N, Equiv.refl _, by omega, Or.inr (Or.inr
      ⟨hok, (ggCoxeterMatrix_reindex_refl _).symm⟩)⟩, ggIntCartan_D N⟩
  · rcases hok with rfl | rfl | rfl
    · exact ⟨CoxeterMatrix.E₆, Or.inr (Or.inl ⟨Equiv.refl _,
        (ggCoxeterMatrix_reindex_refl _).symm⟩), ggIntCartan_E₆⟩
    · exact ⟨CoxeterMatrix.E₇, Or.inr (Or.inr (Or.inl ⟨Equiv.refl _,
        (ggCoxeterMatrix_reindex_refl _).symm⟩)), ggIntCartan_E₇⟩
    · exact ⟨CoxeterMatrix.E₈, Or.inr (Or.inr (Or.inr (Or.inl ⟨Equiv.refl _,
        (ggCoxeterMatrix_reindex_refl _).symm⟩))), ggIntCartan_E₈⟩
  · subst hok
    refine ⟨CoxeterMatrix.F₄, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Equiv.refl _,
      (ggCoxeterMatrix_reindex_refl _).symm⟩)))), ?_⟩
    have : ggWCartanI .F 4 = CartanMatrix.F₄ := by
      simp only [ggWCartanI]
      rfl
    rw [this]
    exact ggIntCartan_F₄

end CFSG.StandardType
