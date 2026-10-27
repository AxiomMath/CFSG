module

public import CFSG.RankThree.GF2n.Stroth80.Ext1D4Borel
public import CFSG.LinearAlgebra.IndexAverageProjection
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.RankThree.GF2n.Stroth80.Ext1D4

open Matrix

variable {K : Type*} [Field K] {W : Finset (Fin 4 → ℤ)} {E : Type*} [AddCommGroup E]
  [Module K E]

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

@[expose] noncomputable def graphSub (b : Module.Basis (ι ⊕ κ) K E) (L : Matrix ι κ K) :
    Submodule K E where
  carrier := {v | ∀ i, b.repr v (Sum.inl i) = (L *ᵥ fun j => b.repr v (Sum.inr j)) i}
  add_mem' := by
    intro u v hu hv i
    simp only [Set.mem_setOf_eq, map_add, Finsupp.add_apply] at *
    rw [hu i, hv i, ← Pi.add_apply (L *ᵥ _), ← mulVec_add]
    rfl
  zero_mem' := by
    intro i
    simp only [map_zero, Finsupp.zero_apply]
    show (0 : K) = (L *ᵥ (0 : κ → K)) i
    rw [mulVec_zero]
    rfl
  smul_mem' := by
    intro c v hv i
    simp only [Set.mem_setOf_eq, map_smul, Finsupp.smul_apply, smul_eq_mul] at *
    rw [hv i]
    have : (fun j => c * b.repr v (Sum.inr j)) = c • fun j => b.repr v (Sum.inr j) := rfl
    rw [this, mulVec_smul, Pi.smul_apply, smul_eq_mul]

theorem mem_graphSub (b : Module.Basis (ι ⊕ κ) K E) (L : Matrix ι κ K) (v : E) :
    v ∈ graphSub b L ↔
      ∀ i, b.repr v (Sum.inl i) = (L *ᵥ fun j => b.repr v (Sum.inr j)) i := Iff.rfl

theorem isCompl_graphSub (b : Module.Basis (ι ⊕ κ) K E) (L : Matrix ι κ K) {A : Submodule K E}
    (hA : ∀ v, v ∈ A ↔ ∀ j, b.repr v (Sum.inr j) = 0) : IsCompl A (graphSub b L) := by
  refine ⟨Submodule.disjoint_def.2 fun v hvA hvC => ?_, codisjoint_iff.2 ?_⟩
  · have h2 := (hA v).1 hvA
    have h0 : (fun j => b.repr v (Sum.inr j)) = 0 := funext h2
    refine b.ext_elem fun i => ?_
    rcases i with i | j
    · rw [(mem_graphSub b L v).1 hvC i, h0, mulVec_zero, map_zero, Finsupp.zero_apply]
      rfl
    · rw [h2 j, map_zero, Finsupp.zero_apply]
  · refine Submodule.eq_top_iff'.2 fun v => ?_
    set y : κ → K := fun j => b.repr v (Sum.inr j)
    set c : E := b.equivFun.symm (Sum.elim (L *ᵥ y) y)
    have hc : ∀ i, b.repr c i = Sum.elim (L *ᵥ y) y i := fun i => by
      rw [← b.equivFun_apply, LinearEquiv.apply_symm_apply]
    have hcy : (fun j => b.repr c (Sum.inr j)) = y := funext fun j => by rw [hc]; rfl
    have hcC : c ∈ graphSub b L := fun i => by rw [hcy, hc]; rfl
    have hvA : v - c ∈ A := (hA _).2 fun j => by
      rw [map_sub, Finsupp.sub_apply, hc]
      exact sub_self _
    have : v = (v - c) + c := by abel
    rw [this]
    exact Submodule.add_mem_sup hvA hcC

theorem graphSub_invariant (b : Module.Basis (ι ⊕ κ) K E) (L : Matrix ι κ K) (f : Module.End K E)
    (P : Matrix ι ι K) (P' : Matrix κ κ K)
    (hf : LinearMap.toMatrix b b f = fromBlocks P (L * P' - P * L) 0 P') :
    ∀ v ∈ graphSub b L, f v ∈ graphSub b L := by
  intro v hv
  have hx₁ : ⇑(b.repr v) ∘ Sum.inl = L *ᵥ (⇑(b.repr v) ∘ Sum.inr) := funext hv
  have key : ⇑(b.repr (f v)) =
      Sum.elim (L *ᵥ (P' *ᵥ (⇑(b.repr v) ∘ Sum.inr))) (P' *ᵥ (⇑(b.repr v) ∘ Sum.inr)) := by
    rw [← LinearMap.toMatrix_mulVec_repr b b f v, hf, fromBlocks_mulVec, hx₁, zero_mulVec,
      zero_add, mulVec_mulVec, sub_mulVec, mulVec_mulVec]
    congr 1
    abel
  intro i
  have h1 := congrFun key (Sum.inl i)
  have h2 : (fun j => b.repr (f v) (Sum.inr j)) = P' *ᵥ (⇑(b.repr v) ∘ Sum.inr) :=
    funext fun j => by have := congrFun key (Sum.inr j); simpa using this
  simp only [Sum.elim_inl] at h1
  rw [h1, h2]

theorem fromBlocks_ext_mul (P : Matrix ι ι K) (Q : Matrix ι κ K) (P' : Matrix κ κ K)
    (R : Matrix ι ι K) (S : Matrix ι κ K) (R' : Matrix κ κ K) :
    fromBlocks P Q 0 P' * fromBlocks R S 0 R' =
      fromBlocks (P * R) (P * S + Q * R') 0 (P' * R') := by
  rw [fromBlocks_multiply]
  simp

theorem exists_invariant_compl_of_index {G : Type*} [Group G] (ρ : G →* Module.End K E)
    (A C₁ : Submodule K E) (hAinv : ∀ g, ∀ a ∈ A, ρ g a ∈ A) (hC : IsCompl A C₁)
    (H : Subgroup G) [H.FiniteIndex] (hH : (H.index : K) ≠ 0)
    (hHC : ∀ g ∈ H, ∀ c ∈ C₁, ρ g c ∈ C₁) :
    ∃ C : Submodule K E, IsCompl A C ∧ ∀ g, ∀ c ∈ C, ρ g c ∈ C := by
  set p := Submodule.projection A C₁ hC
  have hpA : ∀ v, p v ∈ A := fun v => Submodule.projection_apply_mem hC v
  have hpid : ∀ a ∈ A, p a = a := fun a ha => Submodule.projection_apply_of_mem_left hC ha
  have hpker : ∀ c ∈ C₁, p c = 0 := fun c hc => Submodule.projection_apply_of_mem_right hC hc
  have hsub : ∀ v, v - p v ∈ C₁ := by
    intro v
    rw [← Submodule.projection_apply_eq_zero_iff hC, map_sub, hpid _ (hpA v), sub_self]
  have hpH : ∀ g ∈ H, ∀ v, p (ρ g v) = ρ g (p v) := by
    intro g hg v
    have hv : v = p v + (v - p v) := by abel
    conv_lhs => rw [hv]
    rw [map_add, map_add, hpid _ (hAinv g _ (hpA v)), hpker _ (hHC g hg _ (hsub v)), add_zero]
  obtain ⟨p', hp'A, hp'id, hp'G⟩ :=
    CFSG.LinearAlgebra.IndexAverage.exists_equivariant_projection_of_index ρ H hH A hAinv p hpA
      hpid hpH
  refine ⟨LinearMap.ker p', ⟨Submodule.disjoint_def.2 fun v hvA hvK => ?_,
    codisjoint_iff.2 (Submodule.eq_top_iff'.2 fun v => ?_)⟩, fun g c hc => ?_⟩
  · rw [← hp'id v hvA]
    exact LinearMap.mem_ker.1 hvK
  · have hv : v = p' v + (v - p' v) := by abel
    rw [hv]
    refine Submodule.add_mem_sup (hp'A v) ?_
    rw [LinearMap.mem_ker, map_sub, hp'id _ (hp'A v), sub_self]
  · rw [LinearMap.mem_ker] at hc ⊢
    rw [hp'G, hc, map_zero]

theorem preserves_of_mem_closure {G : Type*} [Group G] [Finite G] (ρ : G →* Module.End K E)
    (C : Submodule K E) (S : Set G) (hS : ∀ s ∈ S, ∀ c ∈ C, ρ s c ∈ C) :
    ∀ g ∈ Subgroup.closure S, ∀ c ∈ C, ρ g c ∈ C := by
  have hpow : ∀ x : G, (∀ c ∈ C, ρ x c ∈ C) → ∀ n : ℕ, ∀ c ∈ C, ρ (x ^ n) c ∈ C := by
    intro x hx n
    induction n with
    | zero => intro c hc; simpa using hc
    | succ n ih =>
      intro c hc
      rw [pow_succ, map_mul, Module.End.mul_apply]
      exact ih _ (hx c hc)
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem s hs => exact hS s hs
  | one => intro c hc; simpa using hc
  | mul x y _ _ hx hy =>
    intro c hc
    rw [map_mul, Module.End.mul_apply]
    exact hx _ (hy c hc)
  | inv x _ hx =>
    have hn : x⁻¹ = x ^ (orderOf x - 1) := by
      refine (eq_inv_of_mul_eq_one_left ?_).symm
      rw [← pow_succ, Nat.sub_add_cancel (isOfFinOrder_of_finite x).orderOf_pos,
        pow_orderOf_eq_one]
    rw [hn]
    exact hpow x hx _

theorem exists_invariant_compl_of_blocks [Fintype K] [CharP K 2] (hq : 4 ≤ Fintype.card K)
    (hW : W = natWt ∨ W = evenWt ∨ W = oddWt) {G : Type*} [Group G]
    (ρ : G →* Module.End K E) (A : Submodule K E) (hAinv : ∀ g, ∀ a ∈ A, ρ g a ∈ A)
    (b : Module.Basis (W ⊕ W) K E) (hA : ∀ v, v ∈ A ↔ ∀ χ, b.repr v (Sum.inr χ) = 0)
    (x : (Fin 4 → ℤ) → K → G) {Z : Type*} (hz : Z → G) (D : Z → W → Kˣ)
    (bh : (Fin 4 → ℤ) → Z → Kˣ)
    (hD : ∀ β ∈ posRoot, ∀ z, ∀ ψ χ : W, (ψ : Fin 4 → ℤ) = χ + β → D z ψ = bh β z * D z χ)
    (hbh : ∀ β ∈ posRoot, ∀ c : Kˣ, ∃ z, bh β z = c)
    (hsep : ∀ β ∈ posRoot, ∀ ψ χ : W, ψ ≠ χ → (ψ : Fin 4 → ℤ) ≠ χ + β →
      (χ : Fin 4 → ℤ) ≠ ψ + β → ∃ z, bh β z = 1 ∧ D z ψ ≠ D z χ)
    (hR1 : ∀ β ∈ posRoot, ∀ s t, x β (s + t) = x β s * x β t)
    (hR2 : ∀ β ∈ posRoot, ∀ γ ∈ posRoot, β + γ ∉ posRoot → x β 1 * x γ 1 = x γ 1 * x β 1)
    (hR3 : ∀ β ∈ posRoot, ∀ γ ∈ posRoot, β + γ ∈ posRoot →
      x β 1 * x γ 1 = x (β + γ) 1 * x γ 1 * x β 1)
    (hR4 : ∀ β ∈ posRoot, ∀ z t, hz z * x β t = x β ((bh β z : K) * t) * hz z)
    (δ : (Fin 4 → ℤ) → K → Matrix W W K)
    (hx : ∀ β ∈ posRoot, ∀ t, LinearMap.toMatrix b b (ρ (x β t)) =
      fromBlocks (rootElt W β t) (δ β t) 0 (rootElt W β t))
    (hh : ∀ z, LinearMap.toMatrix b b (ρ (hz z)) =
      fromBlocks (diagonal fun χ => (D z χ : K)) 0 0 (diagonal fun χ => (D z χ : K)))
    (H : Subgroup G) [H.FiniteIndex] (hH : (H.index : K) ≠ 0)
    (hHgen : ∀ C : Submodule K E, (∀ β ∈ posRoot, ∀ t, ∀ c ∈ C, ρ (x β t) c ∈ C) →
      (∀ z, ∀ c ∈ C, ρ (hz z) c ∈ C) → ∀ g ∈ H, ∀ c ∈ C, ρ g c ∈ C) :
    ∃ C : Submodule K E, IsCompl A C ∧ ∀ g, ∀ c ∈ C, ρ g c ∈ C := by
  classical
  have hM : ∀ g g' : G, LinearMap.toMatrix b b (ρ (g * g')) =
      LinearMap.toMatrix b b (ρ g) * LinearMap.toMatrix b b (ρ g') := fun g g' => by
    rw [map_mul, LinearMap.toMatrix_mul]
  have hδT : ∀ β ∈ posRoot, ∀ z t, diagonal (fun χ => (D z χ : K)) * δ β t =
      δ β ((bh β z : K) * t) * diagonal (fun χ => (D z χ : K)) := by
    intro β hβ z t
    have h := congrArg (fun g => LinearMap.toMatrix b b (ρ g)) (hR4 β hβ z t)
    simp only [hM, hh, hx β hβ, fromBlocks_ext_mul] at h
    simpa using (fromBlocks_inj.1 h).2.1
  have hδ₁ : ∀ β ∈ posRoot, ∀ s t,
      δ β (s + t) = rootElt W β s * δ β t + δ β s * rootElt W β t := by
    intro β hβ s t
    have h := congrArg (fun g => LinearMap.toMatrix b b (ρ g)) (hR1 β hβ s t)
    simp only [hM, hx β hβ, fromBlocks_ext_mul] at h
    exact (fromBlocks_inj.1 h).2.1
  have hδ₂ : ∀ β ∈ posRoot, ∀ γ ∈ posRoot, β + γ ∉ posRoot →
      rootElt W β 1 * δ γ 1 + δ β 1 * rootElt W γ 1 =
        rootElt W γ 1 * δ β 1 + δ γ 1 * rootElt W β 1 := by
    intro β hβ γ hγ hβγ
    have h := congrArg (fun g => LinearMap.toMatrix b b (ρ g)) (hR2 β hβ γ hγ hβγ)
    simp only [hM, hx β hβ, hx γ hγ, fromBlocks_ext_mul] at h
    exact (fromBlocks_inj.1 h).2.1
  have hδ₃ : ∀ β ∈ posRoot, ∀ γ ∈ posRoot, β + γ ∈ posRoot →
      rootElt W β 1 * δ γ 1 + δ β 1 * rootElt W γ 1 =
        rootElt W (β + γ) 1 * rootElt W γ 1 * δ β 1 +
          rootElt W (β + γ) 1 * δ γ 1 * rootElt W β 1 +
            δ (β + γ) 1 * rootElt W γ 1 * rootElt W β 1 := by
    intro β hβ γ hγ hβγ
    have h := congrArg (fun g => LinearMap.toMatrix b b (ρ g)) (hR3 β hβ γ hγ hβγ)
    simp only [hM, hx β hβ, hx γ hγ, hx _ hβγ, fromBlocks_ext_mul] at h
    rw [(fromBlocks_inj.1 h).2.1]
    noncomm_ring
  obtain ⟨l, hl⟩ := exists_diagonal_of_rootCocycle hq hW D bh hD hbh hsep δ hδT hδ₁ hδ₂ hδ₃
  have hgx : ∀ β ∈ posRoot, ∀ t, ∀ c ∈ graphSub b (diagonal l), ρ (x β t) c ∈
      graphSub b (diagonal l) := fun β hβ t =>
    graphSub_invariant b _ _ (rootElt W β t) (rootElt W β t) (by rw [hx β hβ t, hl β hβ t])
  have hgh : ∀ z, ∀ c ∈ graphSub b (diagonal l), ρ (hz z) c ∈ graphSub b (diagonal l) := by
    intro z
    refine graphSub_invariant b _ _ (diagonal fun χ => (D z χ : K))
      (diagonal fun χ => (D z χ : K)) ?_
    have e : diagonal l * diagonal (fun χ => (D z χ : K)) -
        diagonal (fun χ => (D z χ : K)) * diagonal l = 0 := by
      rw [diagonal_mul_diagonal, diagonal_mul_diagonal, sub_eq_zero]
      congr 1
      funext χ
      exact mul_comm _ _
    rw [hh z, e]
  exact exists_invariant_compl_of_index ρ A _ hAinv (isCompl_graphSub b _ hA) H hH
    (hHgen _ hgx hgh)

theorem exists_invariant_compl_of_sep {W₁ W₂ : Finset (Fin 4 → ℤ)} {G : Type*} [Group G]
    (ρ : G →* Module.End K E) (A : Submodule K E) (hAinv : ∀ g, ∀ a ∈ A, ρ g a ∈ A)
    (b : Module.Basis (W₁ ⊕ W₂) K E) (hA : ∀ v, v ∈ A ↔ ∀ χ, b.repr v (Sum.inr χ) = 0)
    (x : (Fin 4 → ℤ) → K → G) {Z : Type*} (hz : Z → G) (D₁ : Z → W₁ → Kˣ) (D₂ : Z → W₂ → Kˣ)
    (bh : (Fin 4 → ℤ) → Z → Kˣ)
    (hsep : ∀ β ∈ posRoot, ∀ (ψ : W₁) (χ : W₂), ∃ z, bh β z = 1 ∧ D₁ z ψ ≠ D₂ z χ)
    (hR4 : ∀ β ∈ posRoot, ∀ z t, hz z * x β t = x β ((bh β z : K) * t) * hz z)
    (P₁ : (Fin 4 → ℤ) → K → Matrix W₁ W₁ K) (P₂ : (Fin 4 → ℤ) → K → Matrix W₂ W₂ K)
    (δ : (Fin 4 → ℤ) → K → Matrix W₁ W₂ K)
    (hx : ∀ β ∈ posRoot, ∀ t, LinearMap.toMatrix b b (ρ (x β t)) =
      fromBlocks (P₁ β t) (δ β t) 0 (P₂ β t))
    (hh : ∀ z, LinearMap.toMatrix b b (ρ (hz z)) =
      fromBlocks (diagonal fun ψ => (D₁ z ψ : K)) 0 0 (diagonal fun χ => (D₂ z χ : K)))
    (H : Subgroup G) [H.FiniteIndex] (hH : (H.index : K) ≠ 0)
    (hHgen : ∀ C : Submodule K E, (∀ β ∈ posRoot, ∀ t, ∀ c ∈ C, ρ (x β t) c ∈ C) →
      (∀ z, ∀ c ∈ C, ρ (hz z) c ∈ C) → ∀ g ∈ H, ∀ c ∈ C, ρ g c ∈ C) :
    ∃ C : Submodule K E, IsCompl A C ∧ ∀ g, ∀ c ∈ C, ρ g c ∈ C := by
  classical
  have hM : ∀ g g' : G, LinearMap.toMatrix b b (ρ (g * g')) =
      LinearMap.toMatrix b b (ρ g) * LinearMap.toMatrix b b (ρ g') := fun g g' => by
    rw [map_mul, LinearMap.toMatrix_mul]
  have hδT : ∀ β ∈ posRoot, ∀ z t, diagonal (fun ψ => (D₁ z ψ : K)) * δ β t =
      δ β ((bh β z : K) * t) * diagonal (fun χ => (D₂ z χ : K)) := by
    intro β hβ z t
    have h := congrArg (fun g => LinearMap.toMatrix b b (ρ g)) (hR4 β hβ z t)
    simp only [hM, hh, hx β hβ, fromBlocks_ext_mul] at h
    simpa using (fromBlocks_inj.1 h).2.1
  have hδ0 := rootCocycle_eq_zero_of_sep D₁ D₂ bh hsep δ hδT
  have hgx : ∀ β ∈ posRoot, ∀ t, ∀ c ∈ graphSub b (0 : Matrix W₁ W₂ K), ρ (x β t) c ∈
      graphSub b (0 : Matrix W₁ W₂ K) := fun β hβ t =>
    graphSub_invariant b _ _ (P₁ β t) (P₂ β t) (by
      rw [hx β hβ t, hδ0 β hβ t, Matrix.zero_mul, Matrix.mul_zero, sub_zero])
  have hgh : ∀ z, ∀ c ∈ graphSub b (0 : Matrix W₁ W₂ K), ρ (hz z) c ∈
      graphSub b (0 : Matrix W₁ W₂ K) := fun z =>
    graphSub_invariant b _ _ (diagonal fun ψ => (D₁ z ψ : K)) (diagonal fun χ => (D₂ z χ : K))
      (by rw [hh z, Matrix.zero_mul, Matrix.mul_zero, sub_zero])
  exact exists_invariant_compl_of_index ρ A _ hAinv (isCompl_graphSub b _ hA) H hH
    (hHgen _ hgx hgh)

end CFSG.RankThree.GF2n.Stroth80.Ext1D4
