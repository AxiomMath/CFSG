module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcRaw

public section

namespace CFSG.StandardType.GGQ2Frame.ExcRaw

@[expose] def NoInternalAt (m : Fin 6) (v : V m) : Prop :=
  ∀ c : Finset (Root m), occurs m (Submodule.span (ZMod 3) {v}) c →
    cent m c = Submodule.span (ZMod 3) {v} → v ∉ inside m c

theorem vanish_span_singleton_iff {m : Fin 6} {v : V m} {i : Root m} :
    Vanish m (Submodule.span (ZMod 3) {v}) i ↔ root m i v = 0 := by
  constructor
  · intro h
    exact h v (Submodule.mem_span_singleton_self v)
  · intro h u hu
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
    rw [map_smul, h, smul_zero]

theorem coroot_mem_cent_of_not_mem {m : Fin 6} {U : Submodule (ZMod 3) (V m)}
    {c : Finset (Root m)} (hc : occurs m U c) {j : Root m} (hj : Vanish m U j)
    (hjc : j ∉ c) : coroot m j ∈ cent m c := by
  rcases hc with ⟨-, -, hcl, -⟩
  simp only [cent, Submodule.mem_iInf, LinearMap.mem_ker]
  intro i hi
  have hnot : ¬ Adj m i j := fun hadj => hjc (hcl i hi j hj hadj)
  have hp : pairing m i j = 0 := by
    by_contra h
    exact hnot (Or.inl h)
  rw [pairing_eq, hp]
  simp

theorem mem_of_occurs_of_cent_eq {m : Fin 6} {U : Submodule (ZMod 3) (V m)}
    {c : Finset (Root m)} (hc : occurs m U c) (hcent : cent m c = U) {j : Root m}
    (hj : Vanish m U j) : j ∈ c := by
  by_contra hjc
  have hmem : coroot m j ∈ U := by
    rw [← hcent]
    exact coroot_mem_cent_of_not_mem hc hj hjc
  have h2 : root m j (coroot m j) = 2 := root_coroot m j
  rw [hj (coroot m j) hmem] at h2
  exact absurd h2 (by decide)

theorem noInternalAt_of_forall_ne_zero {m : Fin 6} {v : V m} (h : ∀ i, root m i v ≠ 0) :
    NoInternalAt m v := by
  intro c hc
  rcases hc with ⟨hcne, hsub, -, -⟩
  obtain ⟨i, hi⟩ := hcne
  intro _ _
  exact absurd (vanish_span_singleton_iff.mp (hsub i hi)) (h i)

theorem noInternalAt_of_dual {m : Fin 6} {v : V m} (φ : Module.Dual (ZMod 3) (V m))
    (hφv : φ v ≠ 0) (hφ : ∀ i, root m i v = 0 → φ (coroot m i) = 0) : NoInternalAt m v := by
  intro c hc _ hv
  rcases hc with ⟨-, hsub, -, -⟩
  have hle : inside m c ≤ LinearMap.ker φ := by
    rw [inside]
    refine Submodule.span_le.mpr ?_
    rintro x ⟨i, hi, rfl⟩
    exact LinearMap.mem_ker.mpr (hφ i (vanish_span_singleton_iff.mp (hsub i hi)))
  exact hφv (LinearMap.mem_ker.mp (hle hv))

theorem noInternalAt_of_closed {m : Fin 6} {v : V m} (T : Finset (Root m)) (hT : T.Nonempty)
    (hTv : ∀ i ∈ T, root m i v = 0) {j₀ : Root m} (hj₀ : root m j₀ v = 0) (hj₀T : j₀ ∉ T)
    (hcl : ∀ i ∈ T, ∀ j, root m j v = 0 → Adj m i j → j ∈ T) : NoInternalAt m v := by
  intro c hc hcent
  have hcomp : IsComp m (Vanish m (Submodule.span (ZMod 3) {v})) c := hc
  rcases hcomp with ⟨-, hsub, -, hmax⟩
  have hmem : ∀ j : Root m, root m j v = 0 → j ∈ c := fun j hj =>
    mem_of_occurs_of_cent_eq hc hcent (vanish_span_singleton_iff.mpr hj)
  have hTc : T ⊆ c := fun i hi => hmem i (hTv i hi)
  have hclosed : ∀ i ∈ T, ∀ j ∈ c, Adj m i j → j ∈ T := by
    intro i hi j hj hadj
    exact hcl i hi j (vanish_span_singleton_iff.mp (hsub j hj)) hadj
  have hTeq : T = c := hmax T hTc hT hclosed
  have hj₀c : j₀ ∈ c := hmem j₀ hj₀
  rw [← hTeq] at hj₀c
  exact absurd hj₀c hj₀T

theorem noInternalAt_smul_iff {m : Fin 6} {v : V m} {a : ZMod 3} (ha : a ≠ 0) :
    NoInternalAt m (a • v) ↔ NoInternalAt m v := by
  have hspan : Submodule.span (ZMod 3) {a • v} = Submodule.span (ZMod 3) {v} :=
    Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr ha) v
  have hsm : ∀ W : Submodule (ZMod 3) (V m), a • v ∈ W ↔ v ∈ W :=
    fun W => Submodule.smul_mem_iff W ha
  constructor
  · intro h c hc hcent
    have hc' : occurs m (Submodule.span (ZMod 3) {a • v}) c := hspan.symm ▸ hc
    have hcent' : cent m c = Submodule.span (ZMod 3) {a • v} := hcent.trans hspan.symm
    exact fun hv => h c hc' hcent' ((hsm (inside m c)).mpr hv)
  · intro h c hc hcent
    have hc' : occurs m (Submodule.span (ZMod 3) {v}) c := hspan ▸ hc
    have hcent' : cent m c = Submodule.span (ZMod 3) {v} := hcent.trans hspan
    exact fun hv => h c hc' hcent' ((hsm (inside m c)).mp hv)

theorem adj_iff_of_natAbs_pairing_le {m : Fin 6}
    (hb : ∀ i j : Root m, (pairing m i j).natAbs ≤ 2) {i j : Root m} :
    Adj m i j ↔ root m i (coroot m j) ≠ 0 ∨ root m j (coroot m i) ≠ 0 := by
  have hiff : ∀ z : ℤ, z.natAbs ≤ 2 → ((z : ZMod 3) = 0 ↔ z = 0) := by
    intro z hz
    constructor
    · intro h
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
      omega
    · rintro rfl
      norm_num
  simp only [Adj, ne_eq, pairing_eq, hiff (pairing m i j) (hb i j),
    hiff (pairing m j i) (hb j i)]

end CFSG.StandardType.GGQ2Frame.ExcRaw
