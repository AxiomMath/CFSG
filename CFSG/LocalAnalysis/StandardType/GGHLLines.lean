module

public import CFSG.LocalAnalysis.StandardType.GGHLDefs
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def ggHLRoots {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V] {Λ : Type}
    (r : Λ → V ≃ₗ[ZMod p] V) (h : Λ → V) : Set V :=
  {v | ∃ w ∈ Submonoid.closure (Set.range r), ∃ i, v = w (h i)}

@[expose] def GGHLLines {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V] (R : Set V)
    (x : V) (g : V ≃ₗ[ZMod p] V) : Prop :=
  ∀ v ∈ R, ∃ w ∈ R, ∃ c d : ZMod p, c ≠ 0 ∧ g v = c • w + d • x

private def l05nHC_P {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V] {Λ : Type}
    (r : Λ → V ≃ₗ[ZMod p] V) (h : Λ → V) (g : V ≃ₗ[ZMod p] V) : Prop :=
  ∀ v ∈ ggHLRoots r h, ∃ w ∈ ggHLRoots r h, ∃ c : ZMod p, c ≠ 0 ∧ g v = c • w

private lemma l05nHC_P_one {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {Λ : Type} {r : Λ → V ≃ₗ[ZMod p] V} {h : Λ → V} :
    l05nHC_P r h 1 := by
  intro v hv
  exact ⟨v, hv, 1, one_ne_zero, by simp⟩

private lemma l05nHC_P_mul {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {Λ : Type} {r : Λ → V ≃ₗ[ZMod p] V} {h : Λ → V}
    {a b : V ≃ₗ[ZMod p] V}
    (ha : l05nHC_P r h a) (hb : l05nHC_P r h b) : l05nHC_P r h (a * b) := by
  intro v hv
  obtain ⟨w, hw, c, hc, hbc⟩ := hb v hv
  obtain ⟨w', hw', c', hc', hac⟩ := ha w hw
  refine ⟨w', hw', c * c', mul_ne_zero hc hc', ?_⟩
  rw [LinearEquiv.mul_apply, hbc, map_smul, hac, smul_smul]

private lemma l05nHC_reflection_perm {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {Λ : Type} {r : Λ → V ≃ₗ[ZMod p] V} {h : Λ → V} (i : Λ) :
    l05nHC_P r h (r i) := by
  intro v hv
  obtain ⟨w, hw, j, rfl⟩ := hv
  refine ⟨r i (w (h j)),
    ⟨r i * w, Submonoid.mul_mem _ (Submonoid.subset_closure ⟨i, rfl⟩) hw, j, ?_⟩,
    1, one_ne_zero, ?_⟩
  · rw [LinearEquiv.mul_apply]
  · rw [one_smul]

private lemma l05nHC_neg_perm {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {Λ : Type} {r : Λ → V ≃ₗ[ZMod p] V} {h : Λ → V} :
    l05nHC_P r h (LinearEquiv.neg (ZMod p)) := by
  intro v hv
  refine ⟨v, hv, -1, neg_ne_zero.mpr (one_ne_zero : (1 : ZMod p) ≠ 0), ?_⟩
  rw [LinearEquiv.neg_apply]
  exact (neg_one_smul (ZMod p) v).symm

private lemma l05nHC_reflection_inv {p : ℕ} [Fact p.Prime] {E : Type} [Group E] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {Λ : Type} (ι : Additive E ≃+ V)
    (φ : Λ → MulAut E) (hsq : ∀ i, φ i ^ 2 = 1) (i : Λ) :
    (ggLin (p := p) ι (φ i))⁻¹ = ggLin (p := p) ι (φ i) := by
  have h : ggLin (p := p) ι (φ i) * ggLin (p := p) ι (φ i) = 1 := by
    rw [← map_mul, ← pow_two, hsq i, map_one]
  exact inv_eq_of_mul_eq_one_right h

private lemma l05nHC_neg_inv {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] :
    (LinearEquiv.neg (ZMod p) : V ≃ₗ[ZMod p] V)⁻¹ = LinearEquiv.neg (ZMod p) := by
  have h : (LinearEquiv.neg (ZMod p) : V ≃ₗ[ZMod p] V) * LinearEquiv.neg (ZMod p) = 1 := by
    ext v
    simp [LinearEquiv.mul_apply]
  exact inv_eq_of_mul_eq_one_right h

private lemma l05nHC_diagram_inv {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {Λ : Type} {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V}
    {g : V ≃ₗ[ZMod p] V} (hg : g ∈ ggDiagramSet h α) :
    g⁻¹ ∈ ggDiagramSet h α := by
  obtain ⟨π, hπ⟩ := hg
  refine ⟨π.symm, ?_⟩
  intro i
  constructor
  · have h1 : g (h (π.symm i)) = h i := by
      simpa using (hπ (π.symm i)).1
    rw [← h1]
    simp
  · intro v
    have h2 := (hπ (π.symm i)).2 (g⁻¹ v)
    simpa using h2.symm

private lemma l05nHC_diagram_conj_gen {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {Λ : Type} {r : Λ → V ≃ₗ[ZMod p] V} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod p) V} {g : V ≃ₗ[ZMod p] V} {π : Λ ≃ Λ}
    (hlin : ∀ i w, r i w = w - α i w • h i)
    (hπ1 : ∀ i, g (h i) = h (π i))
    (hπ2 : ∀ i v, α (π i) (g v) = α i v) (i : Λ) :
    g * r i * g⁻¹ = r (π i) := by
  ext v
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.coe_inv]
  rw [hlin i (g.symm v), map_sub, map_smul, LinearEquiv.apply_symm_apply, hπ1]
  rw [← hπ2 i (g.symm v), LinearEquiv.apply_symm_apply, ← hlin (π i) v]

private lemma l05nHC_diagram_perm {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {Λ : Type} {r : Λ → V ≃ₗ[ZMod p] V} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod p) V} {g : V ≃ₗ[ZMod p] V}
    (hlin : ∀ i w, r i w = w - α i w • h i) (hg : g ∈ ggDiagramSet h α) :
    l05nHC_P r h g := by
  obtain ⟨π, hπ⟩ := hg
  have hπ1 : ∀ i, g (h i) = h (π i) := fun i => (hπ i).1
  have hπ2 : ∀ i v, α (π i) (g v) = α i v := fun i => (hπ i).2
  have hconj : ∀ w ∈ Submonoid.closure (Set.range r),
      g * w * g⁻¹ ∈ Submonoid.closure (Set.range r) := by
    intro w hw
    refine Submonoid.closure_induction
      (motive := fun w _ => g * w * g⁻¹ ∈ Submonoid.closure (Set.range r)) ?_ ?_ ?_ hw
    · intro x hx
      obtain ⟨i, rfl⟩ := hx
      rw [l05nHC_diagram_conj_gen hlin hπ1 hπ2 i]
      exact Submonoid.subset_closure ⟨π i, rfl⟩
    · simpa using Submonoid.one_mem (Submonoid.closure (Set.range r))
    · intro a b ha hb iha ihb
      rw [show g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) by group]
      exact Submonoid.mul_mem _ iha ihb
  intro v hv
  obtain ⟨w, hw, j, rfl⟩ := hv
  refine ⟨(g * w * g⁻¹) (h (π j)),
    ⟨g * w * g⁻¹, hconj w hw, π j, rfl⟩, 1, one_ne_zero, ?_⟩
  rw [one_smul]
  calc g (w (h j)) = (g * w) (h j) := by rw [LinearEquiv.mul_apply]
    _ = ((g * w * g⁻¹) * g) (h j) := by
        rw [show (g * w * g⁻¹) * g = g * w by group]
    _ = (g * w * g⁻¹) (g (h j)) := by rw [LinearEquiv.mul_apply]
    _ = (g * w * g⁻¹) (h (π j)) := by rw [hπ1 j]

theorem ggHL_perm_lines {p : ℕ} [Fact p.Prime] {E : Type} [Group E] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {Λ : Type} (ι : Additive E ≃+ V) (φ : Λ → MulAut E) (h : Λ → V)
    (α : Λ → Module.Dual (ZMod p) V)
    (hlin : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i) (hsq : ∀ i, φ i ^ 2 = 1)
    {g : V ≃ₗ[ZMod p] V} (hg : g ∈ ggHL ι φ h α) :
    ∀ v ∈ ggHLRoots (fun i => ggLin (p := p) ι (φ i)) h,
      ∃ w ∈ ggHLRoots (fun i => ggLin (p := p) ι (φ i)) h, ∃ c : ZMod p, c ≠ 0 ∧ g v = c • w := by
  have key : ∀ g ∈ ggHL ι φ h α,
      l05nHC_P (fun i => ggLin (p := p) ι (φ i)) h g ∧
      l05nHC_P (fun i => ggLin (p := p) ι (φ i)) h g⁻¹ := by
    intro g hg
    refine Subgroup.closure_induction
      (p := fun g _ => l05nHC_P (fun i => ggLin (p := p) ι (φ i)) h g ∧
        l05nHC_P (fun i => ggLin (p := p) ι (φ i)) h g⁻¹) ?_ ?_ ?_ ?_ hg
    · intro x hx
      rcases hx with (hx | hx) | hx
      · obtain ⟨i, rfl⟩ := hx
        exact ⟨l05nHC_reflection_perm i,
          by rw [l05nHC_reflection_inv ι φ hsq i]; exact l05nHC_reflection_perm i⟩
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        exact ⟨l05nHC_neg_perm, by rw [l05nHC_neg_inv]; exact l05nHC_neg_perm⟩
      · exact ⟨l05nHC_diagram_perm (r := fun i => ggLin (p := p) ι (φ i)) hlin hx,
          l05nHC_diagram_perm (r := fun i => ggLin (p := p) ι (φ i)) hlin
            (l05nHC_diagram_inv hx)⟩
    · exact ⟨l05nHC_P_one, by simpa using l05nHC_P_one⟩
    · intro a b ha hb iha ihb
      refine ⟨l05nHC_P_mul iha.1 ihb.1, ?_⟩
      simpa [mul_inv_rev] using l05nHC_P_mul ihb.2 iha.2
    · intro a ha iha
      exact ⟨iha.2, by simpa using iha.1⟩
  exact (key g hg).1

end CFSG.StandardType

