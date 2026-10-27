module

public import CFSG.Quasithin.AppendixH.H9.H92.NonQuad.NilpotentAlgebra
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {n : ℕ}

@[expose] def nilOrbitSpace (𝒩 : Submodule (ZMod 2) (Matrix (Fin n) (Fin n) (ZMod 2)))
    (v : Fin n → ZMod 2) : Submodule (ZMod 2) (Fin n → ZMod 2) where
  carrier := {w | ∃ M ∈ 𝒩, M *ᵥ v = w}
  add_mem' := by
    rintro _ _ ⟨M, hM, rfl⟩ ⟨M', hM', rfl⟩
    exact ⟨M + M', 𝒩.add_mem hM hM', Matrix.add_mulVec _ _ _⟩
  zero_mem' := ⟨0, 𝒩.zero_mem, Matrix.zero_mulVec _⟩
  smul_mem' := by
    rintro c _ ⟨M, hM, rfl⟩
    exact ⟨c • M, 𝒩.smul_mem c hM, Matrix.smul_mulVec _ _ _⟩

@[expose] def nilOrbitSpan (𝒩 : Submodule (ZMod 2) (Matrix (Fin n) (Fin n) (ZMod 2)))
    (v : Fin n → ZMod 2) : Submodule (ZMod 2) (Fin n → ZMod 2) :=
  nilOrbitSpace 𝒩 v ⊔ Submodule.span (ZMod 2) {v}

variable {E : Subgroup (GL (Fin n) (ZMod 2))}
  {𝒩 : Submodule (ZMod 2) (Matrix (Fin n) (Fin n) (ZMod 2))} {v : Fin n → ZMod 2}

theorem mulVec_mem_nilOrbitSpace {M : Matrix (Fin n) (Fin n) (ZMod 2)} (hM : M ∈ 𝒩) :
    M *ᵥ v ∈ nilOrbitSpace 𝒩 v := ⟨M, hM, rfl⟩

theorem mem_nilOrbitSpan {w : Fin n → ZMod 2} :
    w ∈ nilOrbitSpan 𝒩 v ↔ ∃ s ∈ nilOrbitSpace 𝒩 v, ∃ c : ZMod 2, s + c • v = w := by
  unfold nilOrbitSpan
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨s, hs, t, ht, rfl⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ht
    exact ⟨s, hs, c, rfl⟩
  · rintro ⟨s, hs, c, rfl⟩
    exact ⟨s, hs, c • v, Submodule.mem_span_singleton.mpr ⟨c, rfl⟩, rfl⟩

theorem nilOrbitSpace_le_nilOrbitSpan : nilOrbitSpace 𝒩 v ≤ nilOrbitSpan 𝒩 v := le_sup_left

theorem self_mem_nilOrbitSpan : v ∈ nilOrbitSpan 𝒩 v :=
  Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)

theorem mulVec_mem_nilOrbitSpace_of_mem (h : SubOneCover E 𝒩) {M : Matrix (Fin n) (Fin n) (ZMod 2)}
    (hM : M ∈ 𝒩) {w : Fin n → ZMod 2} (hw : w ∈ nilOrbitSpace 𝒩 v) :
    M *ᵥ w ∈ nilOrbitSpace 𝒩 v := by
  obtain ⟨M', hM', rfl⟩ := hw
  exact ⟨M * M', h.mul_mem M hM M' hM', (Matrix.mulVec_mulVec _ _ _).symm⟩

theorem self_notMem_nilOrbitSpace (h : SubOneCover E 𝒩) (hv : v ≠ 0) :
    v ∉ nilOrbitSpace 𝒩 v := by
  rintro ⟨M, hM, hMv⟩
  apply hv
  calc v = M *ᵥ v := hMv.symm
    _ = M *ᵥ (M *ᵥ v) := congrArg (M *ᵥ ·) hMv.symm
    _ = (M * M) *ᵥ v := Matrix.mulVec_mulVec _ _ _
    _ = 0 := by rw [h.mul_self M hM, Matrix.zero_mulVec]

theorem sub_one_mulVec_mem_nilOrbitSpace (h : SubOneCover E 𝒩) {k : GL (Fin n) (ZMod 2)}
    (hk : k ∈ E) {w : Fin n → ZMod 2} (hw : w ∈ nilOrbitSpan 𝒩 v) :
    ((k : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) *ᵥ w ∈ nilOrbitSpace 𝒩 v := by
  obtain ⟨s, hs, c, rfl⟩ := mem_nilOrbitSpan.mp hw
  rw [Matrix.mulVec_add, Matrix.mulVec_smul]
  exact Submodule.add_mem _ (mulVec_mem_nilOrbitSpace_of_mem h (h.sub_one_mem k hk) hs)
    (Submodule.smul_mem _ _ (mulVec_mem_nilOrbitSpace (h.sub_one_mem k hk)))

theorem mulVec_mem_nilOrbitSpan (h : SubOneCover E 𝒩) {k : GL (Fin n) (ZMod 2)} (hk : k ∈ E)
    {w : Fin n → ZMod 2} (hw : w ∈ nilOrbitSpan 𝒩 v) :
    (k : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ w ∈ nilOrbitSpan 𝒩 v := by
  have h1 : (k : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ w =
      ((k : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) *ᵥ w + w := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_add_cancel]
  rw [h1]
  exact Submodule.add_mem _ (nilOrbitSpace_le_nilOrbitSpan (sub_one_mulVec_mem_nilOrbitSpace h hk hw))
    hw

theorem sub_one_mulVec_eq_zero_of_fix (h : SubOneCover E 𝒩) {k : GL (Fin n) (ZMod 2)} (hk : k ∈ E)
    (hkv : (k : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v = v) {w : Fin n → ZMod 2}
    (hw : w ∈ nilOrbitSpan 𝒩 v) :
    ((k : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) *ᵥ w = 0 := by
  have hNv : ((k : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) *ᵥ v = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hkv, sub_self]
  obtain ⟨s, ⟨M, hM, rfl⟩, c, rfl⟩ := mem_nilOrbitSpan.mp hw
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, hNv, smul_zero, add_zero, Matrix.mulVec_mulVec,
    h.mul_comm _ (h.sub_one_mem k hk) M hM, ← Matrix.mulVec_mulVec, hNv, Matrix.mulVec_zero]

theorem finrank_nilOrbitSpace_lt (h : SubOneCover E 𝒩) (hv : v ≠ 0) :
    Module.finrank (ZMod 2) (nilOrbitSpace 𝒩 v) + 1 ≤ Module.finrank (ZMod 2) (nilOrbitSpan 𝒩 v) := by
  have hlt : nilOrbitSpace 𝒩 v < nilOrbitSpan 𝒩 v :=
    lt_of_le_of_ne nilOrbitSpace_le_nilOrbitSpan fun heq =>
      self_notMem_nilOrbitSpace h hv (heq ▸ self_mem_nilOrbitSpan)
  exact Submodule.finrank_lt_finrank_of_lt hlt

theorem finrank_nilOrbitSpan_le (hv : v ≠ 0) :
    Module.finrank (ZMod 2) (nilOrbitSpan 𝒩 v) ≤ Module.finrank (ZMod 2) (nilOrbitSpace 𝒩 v) + 1 := by
  have h1 := Submodule.finrank_add_le_finrank_add_finrank (nilOrbitSpace 𝒩 v)
    (Submodule.span (ZMod 2) {v})
  rw [finrank_span_singleton hv] at h1
  exact h1

theorem finrank_nilOrbitSpace_lt_dim (h : SubOneCover E 𝒩) (hv : v ≠ 0) :
    Module.finrank (ZMod 2) (nilOrbitSpace 𝒩 v) < n := by
  have h1 := finrank_nilOrbitSpace_lt h hv
  have h2 := Submodule.finrank_le (nilOrbitSpan 𝒩 v)
  rw [Module.finrank_fin_fun] at h2
  omega

theorem mulVec_sub_self_mem_nilOrbitSpace (h : SubOneCover E 𝒩) {k : GL (Fin n) (ZMod 2)}
    (hk : k ∈ E) (v : Fin n → ZMod 2) :
    (k : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v - v ∈ nilOrbitSpace 𝒩 v := by
  have h1 := mulVec_mem_nilOrbitSpace (v := v) (h.sub_one_mem k hk)
  rwa [Matrix.sub_mulVec, Matrix.one_mulVec] at h1

theorem eq_one_of_sub_one_mulVec_eq_zero {k : GL (Fin n) (ZMod 2)}
    (hk : ∀ w : Fin n → ZMod 2, ((k : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) *ᵥ w = 0) :
    k = 1 := by
  have h0 : ((k : Matrix (Fin n) (Fin n) (ZMod 2)) - 1) = 0 := by
    ext i j
    have := congrFun (hk (Pi.single j 1)) i
    rw [Matrix.mulVec_single_one] at this
    simpa using this
  exact Units.ext (sub_eq_zero.mp h0)

theorem exists_vec_mulVec_ne_zero {M : Matrix (Fin n) (Fin n) (ZMod 2)} (hM : M ≠ 0) :
    ∃ v : Fin n → ZMod 2, M *ᵥ v ≠ 0 := by
  by_contra hcon
  refine hM (Matrix.ext fun i j => ?_)
  have h1 : M *ᵥ Pi.single j 1 = 0 := by
    by_contra h2
    exact hcon ⟨_, h2⟩
  have := congrFun h1 i
  rw [Matrix.mulVec_single_one] at this
  simpa using this

end CFSG.ASVolI.ChH
