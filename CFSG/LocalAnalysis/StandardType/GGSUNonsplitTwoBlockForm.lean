module

public import CFSG.RankThree.PartOne.S11d.OddHerm
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.StandardType

namespace SUTB

open Module

variable {K : Type} [Field K] {σ : K →+* K} {V : Type} [AddCommGroup V] [Module K V]

@[expose] def NondegOn (B : V →ₛₗ[σ] V →ₗ[K] K) (W : Submodule K V) : Prop :=
  ∀ m ∈ W, (∀ n ∈ W, B n m = 0) → m = 0

variable (B : V →ₛₗ[σ] V →ₗ[K] K)

theorem apply_linearCombination {ι : Type} [Fintype ι] (F : ι → V) (c d : ι → K) :
    B (Fintype.linearCombination K F d) (Fintype.linearCombination K F c) =
      ∑ i, ∑ j, σ (d i) * (c j * B (F i) (F j)) := by
  simp only [Fintype.linearCombination_apply, map_sum, map_smulₛₗ, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

variable {B}

theorem exists_linearMap_of_gram {ι : Type} [Fintype ι] {F F' : ι → V}
    (hG : ∀ i j, B (F i) (F j) = B (F' i) (F' j))
    (hnd : NondegOn B (Submodule.span K (Set.range F'))) :
    ∃ θ : V →ₗ[K] V, ∀ i, θ (F i) = F' i := by
  classical
  set Φ := Fintype.linearCombination K F with hΦ
  set Φ' := Fintype.linearCombination K F' with hΦ'
  have hBB : ∀ c d : ι → K, B (Φ' d) (Φ' c) = B (Φ d) (Φ c) := by
    intro c d
    rw [hΦ, hΦ', apply_linearCombination, apply_linearCombination]
    simp only [hG]
  have hle : LinearMap.ker Φ ≤ LinearMap.ker Φ' := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    refine hnd _ ?_ fun m hm => ?_
    · rw [← Fintype.range_linearCombination]
      exact ⟨c, rfl⟩
    · rw [← Fintype.range_linearCombination] at hm
      obtain ⟨d, rfl⟩ := hm
      rw [hBB, hc, map_zero]
  set θ₀ : LinearMap.range Φ →ₗ[K] V :=
    (LinearMap.ker Φ).liftQ Φ' hle ∘ₗ Φ.quotKerEquivRange.symm.toLinearMap with hθ₀
  have hθ₀c : ∀ (c : ι → K) (h : Φ c ∈ LinearMap.range Φ), θ₀ ⟨Φ c, h⟩ = Φ' c := by
    intro c h
    rw [hθ₀, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]
  obtain ⟨θ, hθ⟩ := LinearMap.exists_extend θ₀
  refine ⟨θ, fun i => ?_⟩
  have h1 : Φ (Pi.single i 1) = F i := by
    rw [hΦ, Fintype.linearCombination_apply_single, one_smul]
  have h1' : Φ' (Pi.single i 1) = F' i := by
    rw [hΦ', Fintype.linearCombination_apply_single, one_smul]
  have hmem : Φ (Pi.single i 1) ∈ LinearMap.range Φ := ⟨_, rfl⟩
  have h2 := LinearMap.congr_fun hθ ⟨Φ (Pi.single i 1), hmem⟩
  rw [LinearMap.comp_apply, Submodule.subtype_apply, hθ₀c] at h2
  rw [← h1, h2, h1']

theorem gram_map_eq {ι : Type} [Fintype ι] {F F' : ι → V}
    (hG : ∀ i j, B (F i) (F j) = B (F' i) (F' j)) {θ : V →ₗ[K] V} (hθ : ∀ i, θ (F i) = F' i)
    {v w : V} (hv : v ∈ Submodule.span K (Set.range F))
    (hw : w ∈ Submodule.span K (Set.range F)) : B (θ v) (θ w) = B v w := by
  obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hv
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hw
  have e1 : θ (∑ i, d i • F i) = Fintype.linearCombination K F' d := by
    rw [Fintype.linearCombination_apply, map_sum]
    simp only [map_smul, hθ]
  have e2 : θ (∑ i, c i • F i) = Fintype.linearCombination K F' c := by
    rw [Fintype.linearCombination_apply, map_sum]
    simp only [map_smul, hθ]
  rw [e1, e2, apply_linearCombination, ← Fintype.linearCombination_apply,
    ← Fintype.linearCombination_apply, apply_linearCombination]
  simp only [hG]

theorem gram_map_mem {ι : Type} [Fintype ι] {F F' : ι → V} {θ : V →ₗ[K] V}
    (hθ : ∀ i, θ (F i) = F' i) {v : V} (hv : v ∈ Submodule.span K (Set.range F)) :
    θ v ∈ Submodule.span K (Set.range F') := by
  obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hv
  rw [map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_smul, hθ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem gram_map_comm {ι : Type} [Fintype ι] {F F' : ι → V} {θ : V →ₗ[K] V}
    (hθ : ∀ i, θ (F i) = F' i) {x : Module.End K V} {τ : ι → ι} (hx : ∀ i, x (F i) = F (τ i))
    (hx' : ∀ i, x (F' i) = F' (τ i)) {v : V} (hv : v ∈ Submodule.span K (Set.range F)) :
    θ (x v) = x (θ v) := by
  obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hv
  simp only [map_sum, map_smul, hx, hθ, hx']

section Restrict

variable [FiniteDimensional K V] {W : Submodule K V}

@[expose] noncomputable def restrictElt (hW : NondegOn B W) (c : Module.End K V)
    (hc : ∀ w ∈ W, c w ∈ W) : Module.End K V :=
  LinearMap.ofIsCompl (CFSG.RankThree.PartOne.OddIso.isCompl_orthogonalBilin_of_sep hW)
    (W.subtype ∘ₗ c.restrict hc) (W.orthogonalBilin B).subtype

variable (hW : NondegOn B W) {c : Module.End K V} (hc : ∀ w ∈ W, c w ∈ W)

theorem restrictElt_apply_of_mem {w : V} (hw : w ∈ W) : restrictElt hW c hc w = c w := by
  have := LinearMap.ofIsCompl_apply_left
    (CFSG.RankThree.PartOne.OddIso.isCompl_orthogonalBilin_of_sep hW)
    (φ := W.subtype ∘ₗ c.restrict hc) (ψ := (W.orthogonalBilin B).subtype) ⟨w, hw⟩
  simpa [restrictElt] using this

theorem restrictElt_apply_of_mem_orth {v : V} (hv : v ∈ W.orthogonalBilin B) :
    restrictElt hW c hc v = v := by
  have := LinearMap.ofIsCompl_apply_right
    (CFSG.RankThree.PartOne.OddIso.isCompl_orthogonalBilin_of_sep hW)
    (φ := W.subtype ∘ₗ c.restrict hc) (ψ := (W.orthogonalBilin B).subtype) ⟨v, hv⟩
  simpa [restrictElt] using this

include hW in
theorem exists_add_orth (v : V) : ∃ m ∈ W, ∃ z ∈ W.orthogonalBilin B, m + z = v := by
  have h1 : v ∈ W ⊔ W.orthogonalBilin B := by
    rw [(CFSG.RankThree.PartOne.OddIso.isCompl_orthogonalBilin_of_sep hW).sup_eq_top]
    trivial
  obtain ⟨m, hm, z, hz, h⟩ := Submodule.mem_sup.mp h1
  exact ⟨m, hm, z, hz, h⟩

theorem restrictElt_pow_apply (k : ℕ) {m z : V} (hm : m ∈ W) (hz : z ∈ W.orthogonalBilin B) :
    (restrictElt hW c hc ^ k) (m + z) = (c ^ k) m + z := by
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, map_add, restrictElt_apply_of_mem hW hc hm,
      restrictElt_apply_of_mem_orth hW hc hz, ih (hc m hm), pow_succ, Module.End.mul_apply]

theorem restrictElt_pow_eq_one {k : ℕ} (hck : c ^ k = 1) : restrictElt hW c hc ^ k = 1 := by
  refine LinearMap.ext fun v => ?_
  obtain ⟨m, hm, z, hz, rfl⟩ := exists_add_orth hW v
  rw [restrictElt_pow_apply hW hc k hm hz, hck]
  rfl

theorem restrictElt_comm {a : Module.End K V} (haW : ∀ w ∈ W, a w ∈ W)
    (haW' : ∀ z ∈ W.orthogonalBilin B, a z ∈ W.orthogonalBilin B)
    (hac : ∀ w ∈ W, a (c w) = c (a w)) : a * restrictElt hW c hc = restrictElt hW c hc * a := by
  refine LinearMap.ext fun v => ?_
  obtain ⟨m, hm, z, hz, rfl⟩ := exists_add_orth hW v
  simp only [Module.End.mul_apply, map_add]
  rw [restrictElt_apply_of_mem hW hc hm, restrictElt_apply_of_mem_orth hW hc hz,
    restrictElt_apply_of_mem hW hc (haW m hm), restrictElt_apply_of_mem_orth hW hc (haW' z hz),
    hac m hm]

theorem restrictElt_isometry (hB : B.IsSymm) (hcB : ∀ v w, B (c v) (c w) = B v w) (v w : V) :
    B (restrictElt hW c hc v) (restrictElt hW c hc w) = B v w := by
  obtain ⟨m, hm, z, hz, rfl⟩ := exists_add_orth hW v
  obtain ⟨n, hn, y, hy, rfl⟩ := exists_add_orth hW w
  have hWo : ∀ a ∈ W, ∀ b ∈ W.orthogonalBilin B, B a b = 0 := fun a ha b hb =>
    (Submodule.mem_orthogonalBilin.mp hb) a ha
  have hoW : ∀ a ∈ W, ∀ b ∈ W.orthogonalBilin B, B b a = 0 := fun a ha b hb => by
    rw [← hB.eq a b, hWo a ha b hb, map_zero]
  simp only [map_add, LinearMap.add_apply, restrictElt_apply_of_mem hW hc hm,
    restrictElt_apply_of_mem hW hc hn, restrictElt_apply_of_mem_orth hW hc hz,
    restrictElt_apply_of_mem_orth hW hc hy]
  rw [hWo _ (hc m hm) y hy, hoW _ (hc n hn) z hz, hWo m hm y hy, hoW n hn z hz, hcB]

end Restrict

end SUTB

end CFSG.StandardType
