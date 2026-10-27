module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86TArcMain

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

@[expose] def Track.HasReflections (T : Track Γ G) : Prop :=
  ∀ k : ℤ, ∃ f : G, IsReflection T.line k f

@[expose] def TrackPrec (T T' : Track Γ G) : Prop :=
  omega1 T.fixer ≤ omega1 T'.fixer ∧
    ∃ u v : V, Γ.Adj u v ∧ u ∈ Set.range T.line.vert ∧ v ∈ Set.range T.line.vert ∧
      u ∈ Set.range T'.line.vert ∧ v ∈ Set.range T'.line.vert

@[expose] def ReflClosed (T : Track Γ G) : Prop :=
  ∀ T' : Track Γ G, TrackPrec T T' → T'.HasReflections → T.HasReflections

@[expose] def TrackInPi (T : Track Γ G) : Prop := T.fixer ≠ ⊥ ∧ ReflClosed T

variable (T : Track Γ G)

theorem IsTArc.isQuasi {a b : ℤ} (h : IsTArc T a b) : IsQuasiTArc T a b :=
  ⟨h.1, fun hle => h.2.1 ((omega1_le _).trans hle), fun hle => h.2.2.1 ((omega1_le _).trans hle),
    h.2.2.2⟩

theorem IsTArc.translate {a b : ℤ} (h : IsTArc T a b) (k : ℤ) :
    IsTArc T (a + 2 * k) (b + 2 * k) := by
  obtain ⟨hab, hL, hR, hLR⟩ := h
  have hq := (IsTArc.isQuasi T ⟨hab, hL, hR, hLR⟩).translate T k
  refine ⟨hq.1, fun hle => hL fun y hy => ?_, fun hle => hR fun y hy => ?_, hq.2.2.2⟩
  · have := hle (omega1_conj_mem (H := T.subFixer (a + 2 * k) (b + 2 * k)) (H' := T.subFixer a b)
      (g := T.τ ^ k) (fun h hh => (T.conj_mem_subFixer k).2 hh) hy)
    rw [show a + 2 * k - 1 = a - 1 + 2 * k by omega] at this
    exact (T.conj_mem_subFixer k).1 this
  · have := hle (omega1_conj_mem (H := T.subFixer (a + 2 * k) (b + 2 * k)) (H' := T.subFixer a b)
      (g := T.τ ^ k) (fun h hh => (T.conj_mem_subFixer k).2 hh) hy)
    rw [show b + 2 * k + 1 = b + 1 + 2 * k by omega] at this
    exact (T.conj_mem_subFixer k).1 this

theorem Track.conj_mem_subFixer_reflect {f : G} {c : ℤ}
    (hf : ∀ i, f • T.line.vert i = T.line.vert (c - i)) {a b : ℤ} {h : G} :
    f * h * f⁻¹ ∈ T.subFixer (c - b) (c - a) ↔ h ∈ T.subFixer a b := by
  rw [T.mem_subFixer, T.mem_subFixer]
  have hinv : ∀ i, f⁻¹ • T.line.vert i = T.line.vert (c - i) := fun i => by
    rw [inv_smul_eq_iff, hf, sub_sub_cancel]
  constructor
  · intro H i h1 h2
    have := H (c - i) (by omega) (by omega)
    rw [mul_smul, mul_smul, hinv, sub_sub_cancel] at this
    have h3 : f • (h • T.line.vert i) = f • T.line.vert i := by rw [this, hf]
    exact MulAction.injective f h3
  · intro H i h1 h2
    rw [mul_smul, mul_smul, hinv, H (c - i) (by omega) (by omega), hf, sub_sub_cancel]

theorem Track.conj_mem_fixer_reflect {f : G} {c : ℤ}
    (hf : ∀ i, f • T.line.vert i = T.line.vert (c - i)) {h : G} :
    f * h * f⁻¹ ∈ T.fixer ↔ h ∈ T.fixer := by
  rw [T.mem_fixer, T.mem_fixer]
  have hinv : ∀ i, f⁻¹ • T.line.vert i = T.line.vert (c - i) := fun i => by
    rw [inv_smul_eq_iff, hf, sub_sub_cancel]
  constructor
  · intro H i
    have := H (c - i)
    rw [mul_smul, mul_smul, hinv, sub_sub_cancel] at this
    have h3 : f • (h • T.line.vert i) = f • T.line.vert i := by rw [this, hf]
    exact MulAction.injective f h3
  · intro H i
    rw [mul_smul, mul_smul, hinv, H (c - i), hf, sub_sub_cancel]

theorem IsQuasiTArc.reflect {a b : ℤ} (h : IsQuasiTArc T a b) {f : G} {c : ℤ}
    (hf : ∀ i, f • T.line.vert i = T.line.vert (c - i)) : IsQuasiTArc T (c - b) (c - a) := by
  obtain ⟨hab, hL, hR, hLR⟩ := h
  refine ⟨by omega, fun hle => hR fun g hg => ?_, fun hle => hL fun g hg => ?_, ?_⟩
  · have := hle ((T.conj_mem_subFixer_reflect hf).2 hg)
    rw [show c - b - 1 = c - (b + 1) by omega] at this
    exact (T.conj_mem_subFixer_reflect hf).1 this
  · have := hle ((T.conj_mem_subFixer_reflect hf).2 hg)
    rw [show c - a + 1 = c - (a - 1) by omega] at this
    exact (T.conj_mem_subFixer_reflect hf).1 this
  · intro y hy
    have hy' := omega1_conj_mem (H := T.subFixer (a - 1) (b + 1))
      (H' := T.subFixer (c - b - 1) (c - a + 1)) (g := f⁻¹) (fun h hh => by
        have := (T.conj_mem_subFixer_reflect hf (a := a - 1) (b := b + 1)
          (h := f⁻¹ * h * f)).1 (by
            rw [show c - (b + 1) = c - b - 1 by omega, show c - (a - 1) = c - a + 1 by omega]
            simpa [mul_assoc] using hh)
        simpa using this) hy
    have h3 := hLR hy'
    have h4 := (T.conj_mem_fixer_reflect hf).2 (by simpa using h3 : f⁻¹ * y * f ∈ T.fixer)
    simpa [mul_assoc] using h4

theorem Track.isReflection_conj {k : ℤ} {f : G} (h : IsReflection T.line k f) (m : ℤ) :
    IsReflection T.line (k + 2 * m) (T.τ ^ m * f * (T.τ ^ m)⁻¹) := by
  refine ⟨?_, fun i => ?_⟩
  · calc T.τ ^ m * f * (T.τ ^ m)⁻¹ * (T.τ ^ m * f * (T.τ ^ m)⁻¹)
        = T.τ ^ m * (f * f) * (T.τ ^ m)⁻¹ := by group
      _ = 1 := by rw [h.1]; simp
  · have h1 : (T.τ ^ m)⁻¹ • T.line.vert (k + 2 * m + i) = T.line.vert (k + i) := by
      rw [inv_smul_eq_iff, T.zpow_smul_vert]
      congr 1
      omega
    rw [mul_smul, mul_smul, h1, h.2 i, T.zpow_smul_vert]
    congr 1
    omega

theorem Track.hasReflections_of_two (h₁ : ∃ f : G, IsReflection T.line 1 f)
    (h₂ : ∃ f : G, IsReflection T.line 2 f) : T.HasReflections := by
  intro k
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · obtain ⟨f, hf⟩ := h₂
    refine ⟨T.τ ^ ((k - 2) / 2) * f * (T.τ ^ ((k - 2) / 2))⁻¹, ?_⟩
    have := T.isReflection_conj hf ((k - 2) / 2)
    rwa [show 2 + 2 * ((k - 2) / 2) = k by omega] at this
  · obtain ⟨f, hf⟩ := h₁
    refine ⟨T.τ ^ ((k - 1) / 2) * f * (T.τ ^ ((k - 1) / 2))⁻¹, ?_⟩
    have := T.isReflection_conj hf ((k - 1) / 2)
    rwa [show 1 + 2 * ((k - 1) / 2) = k by omega] at this

theorem fan_4_3_2 (F : FanTree Γ G) (hPi : TrackInPi T) {a b : ℤ} (h : IsTArc T a b) :
    (b - a) % 2 = 0 := by
  by_contra hodd
  obtain ⟨hT, hrc⟩ := hPi
  obtain ⟨k, hk⟩ : ∃ k : ℤ, a + 2 * k = b + 1 := ⟨(b + 1 - a) / 2, by omega⟩
  have h' := h.translate T k
  rw [hk] at h'
  have hq := h.isQuasi T
  have hq' := h'.isQuasi T
  have hab : a < b := h.1
  have hab' : b + 1 < b + 2 * k := h'.1
  have inv₁ : ∃ t ∈ T.subFixer a b, t * t = 1 ∧
      t • T.line.vert (b + 1) ≠ T.line.vert (b + 1) := by
    by_contra hcon
    push Not at hcon
    refine h.2.2.1 ?_
    rw [omega1, Subgroup.closure_le]
    rintro t ⟨htθ, ht2⟩
    refine (T.mem_subFixer).2 fun i h1 h2 => ?_
    by_cases hi : i = b + 1
    · subst hi
      exact hcon t htθ ht2
    · exact (T.mem_subFixer).1 htθ i h1 (by omega)
  have inv₂ : ∃ t ∈ T.subFixer (b + 1) (b + 2 * k), t * t = 1 ∧
      t • T.line.vert b ≠ T.line.vert b := by
    by_contra hcon
    push Not at hcon
    refine h'.2.1 ?_
    rw [omega1, Subgroup.closure_le]
    rintro t ⟨htθ, ht2⟩
    refine (T.mem_subFixer).2 fun i h1 h2 => ?_
    by_cases hi : i = b + 1 - 1
    · rw [hi, add_sub_cancel_right]
      exact hcon t htθ ht2
    · exact (T.mem_subFixer).1 htθ i (by omega) h2
  obtain ⟨t₁, ht₁, ht₁2, hm₁⟩ := inv₁
  obtain ⟨t₂, ht₂, ht₂2, hm₂⟩ := inv₂
  have hadj : Γ.Adj (T.line.vert b) (T.line.vert (b + 1)) := T.line.adj b
  have hcross : CrossPair (T.line.vert b) (T.line.vert (b + 1)) t₁ t₂ :=
    ⟨(T.mem_subFixer).1 ht₁ b (by omega) le_rfl, hm₁,
      (T.mem_subFixer).1 ht₂ (b + 1) le_rfl (by omega), hm₂⟩
  have e1 := trackOfPair_vert_one F.adj_smul hadj hcross
  have e2 := trackOfPair_vert_two F.adj_smul hadj hcross
  have eτ := trackOfPair_τ F.adj_smul hadj hcross
  have hrefl : (trackOfPair F.adj_smul hadj hcross).HasReflections :=
    (trackOfPair F.adj_smul hadj hcross).hasReflections_of_two
      ⟨t₁, trackOfPair_reflection_x F.adj_smul hadj hcross ht₁2 ht₂2⟩
      ⟨t₂, trackOfPair_reflection_y F.adj_smul hadj hcross ht₁2 ht₂2⟩
  generalize trackOfPair F.adj_smul hadj hcross = T' at e1 e2 eτ hrefl
  have hN₁ := (IsQuasiTArc.fixer_normal T F hq).2 ht₁
  have hN₂ := (IsQuasiTArc.fixer_normal T F hq').2 ht₂
  have hτ : T'.τ ∈ Subgroup.normalizer (omega1 T.fixer : Set G) := by
    rw [eτ]
    exact Subgroup.mul_mem _ hN₂ hN₁
  have hfix : omega1 T.fixer ≤ T'.fixer := by
    intro y hy
    rw [T'.mem_fixer]
    have hyb : ∀ z ∈ omega1 T.fixer, z • T.line.vert b = T.line.vert b ∧
        z • T.line.vert (b + 1) = T.line.vert (b + 1) := fun z hz =>
      ⟨(T.mem_fixer).1 (omega1_le _ hz) b, (T.mem_fixer).1 (omega1_le _ hz) (b + 1)⟩
    have key : ∀ (m : ℤ) (v : V), (∀ z ∈ omega1 T.fixer, z • v = v) →
        y • (T'.τ ^ m • v) = T'.τ ^ m • v := by
      intro m v hv
      have h1 := (Subgroup.mem_normalizer_iff.1
        (Subgroup.inv_mem _ (Subgroup.zpow_mem _ hτ m)) y).1 hy
      have h2 := hv _ h1
      rw [inv_inv, mul_smul, mul_smul, inv_smul_eq_iff] at h2
      exact h2
    intro j
    rcases Int.emod_two_eq_zero_or_one j with hj | hj
    · obtain ⟨m, rfl⟩ : ∃ m : ℤ, j = 2 + 2 * m := ⟨(j - 2) / 2, by omega⟩
      rw [← T'.zpow_smul_vert m 2, e2]
      exact key m _ (fun z hz => (hyb z hz).2)
    · obtain ⟨m, rfl⟩ : ∃ m : ℤ, j = 1 + 2 * m := ⟨(j - 1) / 2, by omega⟩
      rw [← T'.zpow_smul_vert m 1, e1]
      exact key m _ (fun z hz => (hyb z hz).1)
  have hprec : TrackPrec T T' := by
    refine ⟨?_, T.line.vert b, T.line.vert (b + 1), hadj, ⟨b, rfl⟩, ⟨b + 1, rfl⟩, ⟨1, e1⟩, ⟨2, e2⟩⟩
    rw [omega1, Subgroup.closure_le]
    intro x hx
    exact Subgroup.subset_closure ⟨hfix (Subgroup.subset_closure hx), hx.2⟩
  have hTrefl := hrc T' hprec hrefl
  obtain ⟨f, hf⟩ := hTrefl a
  have hf' : ∀ i, f • T.line.vert i = T.line.vert (2 * a - i) := fun i => by
    have := hf.2 (i - a)
    rwa [show a + (i - a) = i by omega, show a - (i - a) = 2 * a - i by omega] at this
  have hq'' := hq.reflect T hf'
  rcases fan_4_3_1 T F hT hq hq'' with hk | hk
  · rw [T.exists_zpow_smul_iff F.isTree] at hk
    omega
  · rw [T.exists_zpow_smul_iff F.isTree] at hk
    omega

theorem fan_4_3_2_transitive (F : FanTree Γ G) (hPi : TrackInPi T) (u v : V)
    (hu : ∃ a b : ℤ, IsTArc T a b ∧ (u = T.line.vert a ∨ u = T.line.vert b))
    (hv : ∃ a b : ℤ, IsTArc T a b ∧ (v = T.line.vert a ∨ v = T.line.vert b)) :
    ∃ k : ℤ, T.τ ^ k • u = v := by
  obtain ⟨a₁, b₁, h₁, hu⟩ := hu
  obtain ⟨a₂, b₂, h₂, hv⟩ := hv
  have e₁ := fan_4_3_2 T F hPi h₁
  have e₂ := fan_4_3_2 T F hPi h₂
  have hconj := fan_4_3_1 T F hPi.1 (h₁.isQuasi T) (h₂.isQuasi T)
  rw [T.exists_zpow_smul_iff F.isTree, T.exists_zpow_smul_iff F.isTree] at hconj
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;>
    rw [T.exists_zpow_smul_iff F.isTree] <;> omega

end CFSG.Quasithin.Fan86
