module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLemma112Transport

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGQ2WeylFork (n : ℕ) (C : Matrix (Fin n) (Fin n) ℤ) (σ : Equiv.Perm (Fin n)) :
    Prop :=
  ∀ {U : Type} [AddCommGroup U] [Module (ZMod 3) U] (h : Fin n → U),
    LinearIndependent (ZMod 3) h → Submodule.span (ZMod 3) (Set.range h) = ⊤ →
    ∀ (α : Fin n → Module.Dual (ZMod 3) U), (∀ i j, α i (h j) = ((C i j : ℤ) : ZMod 3)) →
    ∀ T : U ≃ₗ[ZMod 3] U,
      T ∈ Subgroup.normalizer (ggQ2WeylOf h α : Set (U ≃ₗ[ZMod 3] U)) →
      ∃ w ∈ ggQ2WeylOf h α, ∃ ε : ZMod 3, ε ≠ 0 ∧
        ((∀ i, T (h i) = ε • w (h i)) ∨ (∀ i, T (h i) = ε • w (h (σ i))))

theorem GGQ2Lin.fork_of_transport (D : GGQ2Lin 3) {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ)
    (e : Fin n ≃ {k // k ≠ D.a}) (hC : ∀ i j, D.cartan (e i) (e j) = C i j)
    (hind : LinearIndependent (ZMod 3) (fun i : {k // k ≠ D.a} => D.coroot i))
    {σ : Equiv.Perm (Fin n)} (hW : GGQ2WeylFork n C σ) (T : D.V ≃ₗ[ZMod 3] D.V)
    (hT : T ∈ Subgroup.normalizer (D.parab {k | k ≠ D.a} : Set (D.V ≃ₗ[ZMod 3] D.V))) :
    ∃ w ∈ D.parab {k | k ≠ D.a}, ∃ c : ZMod 3, c ≠ 0 ∧
      ((∀ i, T (D.coroot (e i)) = c • w (D.coroot (e i))) ∨
        (∀ i, T (D.coroot (e i)) = c • w (D.coroot (e (σ i))))) := by
  classical
  let h' : Fin n → ggQ2xKDt_U0 D := ggQ2xKDt_h' D e
  let α' : Fin n → Module.Dual (ZMod 3) (ggQ2xKDt_U0 D) := ggQ2xKDt_α' D e
  have hP' : ∀ i j, α' i (h' j) = ((C i j : ℤ) : ZMod 3) := fun i j =>
    ggQ2xKDt_α'_h' D e C hC i j
  have hli' : LinearIndependent (ZMod 3) h' := ggQ2xKDt_h'_li D e hind
  have hsp' : Submodule.span (ZMod 3) (Set.range h') = ⊤ := ggQ2xKDt_h'_span D e hind
  have hrange : (ggQ2xKDt_res D).range = ggQ2WeylOf h' α' :=
    ggQ2xKDt_range_res D e
  let T' : ggQ2xKDt_U0 D ≃ₗ[ZMod 3] ggQ2xKDt_U0 D := ggQ2xKDt_T' D T hT
  have hT'norm : T' ∈ Subgroup.normalizer (ggQ2WeylOf h' α') := by
    rw [← hrange, Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rcases MonoidHom.mem_range.mp hy with ⟨g, hg⟩
      refine MonoidHom.mem_range.mpr ⟨⟨T * g.1 * T⁻¹,
        (Subgroup.mem_normalizer_iff.mp hT g.1).mp g.2⟩, ?_⟩
      rw [← hg]
      exact (ggQ2xKDt_T'_conj D T hT g).symm
    · intro hy
      rcases MonoidHom.mem_range.mp hy with ⟨g, hg⟩
      refine MonoidHom.mem_range.mpr ⟨⟨T⁻¹ * g.1 * T,
        (Subgroup.mem_normalizer_iff''.mp hT g.1).mp g.2⟩, ?_⟩
      have h1 : T'⁻¹ * ggQ2xKDt_res D g * T' = y := by
        rw [hg]; group
      rw [← h1]
      exact (ggQ2xKDt_T'_inv_conj D T hT g).symm
  obtain ⟨w', hw'mem, ε, hε, hcases⟩ := hW h' hli' hsp' α' hP' T' hT'norm
  have hw'range : w' ∈ (ggQ2xKDt_res D).range := by rwa [hrange]
  obtain ⟨w, hw_eq⟩ := MonoidHom.mem_range.mp hw'range
  have hlift : ∀ v : ggQ2xKDt_U0 D, ((w' v : ggQ2xKDt_U0 D) : D.V) = w.1 (v : D.V) := by
    intro v
    rw [← hw_eq]
    exact ggQ2xKDt_res_apply D w (v : D.V) v.2
  have hT'val : ∀ v : ggQ2xKDt_U0 D, ((T' v : ggQ2xKDt_U0 D) : D.V) = T (v : D.V) := fun v =>
    ggQ2xKDt_T'_apply D T hT v
  refine ⟨w.1, w.2, ε, hε, ?_⟩
  rcases hcases with h | h
  · left
    intro i
    simpa [h', ggQ2xKDt_h', hT'val, hlift] using congrArg (fun z : ggQ2xKDt_U0 D => (z : D.V)) (h i)
  · right
    intro i
    simpa [h', ggQ2xKDt_h', hT'val, hlift] using congrArg (fun z : ggQ2xKDt_U0 D => (z : D.V)) (h i)

end CFSG.StandardType

end
