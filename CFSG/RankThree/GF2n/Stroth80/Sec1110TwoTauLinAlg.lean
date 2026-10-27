module

public import CFSG.RankThree.GF2n.Stroth80.QuadIso

public section

namespace CFSG.RankThree.GF2n.Tim79.QuadModel

variable {G : Type} [Group G] {QF V : Subgroup G} {K : Type} [Field K] {γ : G → K}

theorem B_sub_self_adjoint (M₀ : QuadModel QF V K γ) {T : M₀.E →ₗ[K] M₀.E}
    (hT : ∀ e, M₀.Qf (T e) = M₀.Qf e) (hT2 : ∀ e, T (T e) = e) (v w : M₀.E) :
    M₀.B (T v - v) w = M₀.B v (T w - w) := by
  have h : M₀.B (T v) w = M₀.B v (T w) := by
    have h' := B_iso hT v (T w)
    rwa [hT2 w] at h'
  simp only [map_sub, LinearMap.sub_apply, h]

theorem Qf_sub_eq_B [CharP K 2] (M₀ : QuadModel QF V K γ) {T : M₀.E →ₗ[K] M₀.E}
    (hT : ∀ e, M₀.Qf (T e) = M₀.Qf e) (v : M₀.E) :
    M₀.Qf (T v - v) = M₀.B v (T v - v) := by
  have h := hT v
  rw [show T v = v + (T v - v) by abel, M₀.Qf_add, add_assoc] at h
  have h' : M₀.Qf v + (M₀.Qf (T v - v) + M₀.B v (T v - v)) = M₀.Qf v + 0 := by
    rw [add_zero]
    exact h
  exact CharTwo.add_eq_zero.mp (add_left_cancel h')

theorem sub_sub_eq_zero_of_invol [CharP K 2] {E : Type*} [AddCommGroup E] [Module K E]
    {T : E →ₗ[K] E} (hT2 : ∀ e, T (T e) = e) (v : E) : T (T v - v) - (T v - v) = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [map_sub, hT2]
  have h : v - T v - (T v - v) = (2 : K) • (v - T v) := by module
  rw [h, h2, zero_smul]

theorem sub_mem_of_perp_of_flag (M₀ : QuadModel QF V K γ) {T : M₀.E →ₗ[K] M₀.E}
    (hT : ∀ e, M₀.Qf (T e) = M₀.Qf e) {W : Submodule K M₀.E}
    (hWo : ∀ v, (∀ w ∈ W, M₀.B v w = 0) → v ∈ W) {b : M₀.E} (hTb : T b = b)
    (hTW : ∀ w ∈ W, ∃ c : K, T w - w = c • b) :
    ∀ v, M₀.B v b = 0 → T v - v ∈ W := by
  intro v hv
  refine hWo _ fun w hw => ?_
  obtain ⟨c, hc⟩ := hTW w hw
  have hTw : T (w - c • b) = w := by
    rw [map_sub, map_smul, hTb, show T w = w + c • b by rw [← hc]; abel]
    abel
  have h1 : M₀.B (T v) (T (w - c • b)) = M₀.B v (w - c • b) := B_iso hT v _
  rw [hTw, map_sub, map_smul, smul_eq_mul, hv, mul_zero, sub_zero] at h1
  rw [map_sub, LinearMap.sub_apply, h1, sub_self]

private theorem exists_B_eq_zero_ne_of_not_mem_span {M₀ : QuadModel QF V K γ} {b c : M₀.E}
    (hb : b ≠ 0) (hcb : ∀ a : K, c ≠ a • b) :
    ∃ v' : M₀.E, M₀.B v' b = 0 ∧ M₀.B c v' ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a, ha⟩ := exists_smul_of_orthogonal hb (v := c) fun x hx => hcon x hx
  exact hcb a ha

private theorem finrank_span_pair_eq_two (M₀ : QuadModel QF V K γ) {b c : M₀.E} (hb : b ≠ 0)
    (hcb : ∀ a : K, c ≠ a • b) :
    Module.finrank K (Submodule.span K ({b, c} : Set M₀.E)) = 2 := by
  classical
  have hb_le : Submodule.span K ({b} : Set M₀.E) ≤
      Submodule.span K ({b, c} : Set M₀.E) := by
    rw [Submodule.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact Submodule.subset_span (by simp)
  have h2 : 1 ≤ Module.finrank K (Submodule.span K ({b, c} : Set M₀.E)) := by
    have h := Submodule.finrank_mono hb_le
    rw [finrank_span_singleton hb] at h
    omega
  have hle2 : Module.finrank K (Submodule.span K ({b, c} : Set M₀.E)) ≤ 2 := by
    have h := finrank_span_finset_le_card (R := K) ({b, c} : Finset M₀.E)
    simp only [Finset.coe_insert, Finset.coe_singleton] at h
    exact h.trans Finset.card_le_two
  by_contra h
  have h1' : Module.finrank K (Submodule.span K ({b, c} : Set M₀.E)) = 1 := by omega
  have heq : Submodule.span K ({b} : Set M₀.E) =
      Submodule.span K ({b, c} : Set M₀.E) :=
    Submodule.eq_of_le_of_finrank_eq hb_le (by
      rw [finrank_span_singleton hb]
      omega)
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (heq ▸ Submodule.subset_span (by simp :
    c ∈ ({b, c} : Set M₀.E)))
  exact hcb a ha.symm

private theorem eq_span_pair_of_finrank_le_two (M₀ : QuadModel QF V K γ) {W' : Submodule K M₀.E}
    {b c : M₀.E} (hbW' : b ∈ W') (hcW' : c ∈ W') (hb : b ≠ 0)
    (hcb : ∀ a : K, c ≠ a • b) (hW' : Module.finrank K W' ≤ 2) :
    W' = Submodule.span K ({b, c} : Set M₀.E) := by
  have hle : Submodule.span K ({b, c} : Set M₀.E) ≤ W' := by
    rw [Submodule.span_le]
    rintro x (rfl | rfl)
    · exact hbW'
    · exact hcW'
  have hdim := finrank_span_pair_eq_two M₀ hb hcb
  have hW2 : Module.finrank K W' = 2 := by
    have hmono := Submodule.finrank_mono hle
    omega
  exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm

private theorem exists_coord_of_finrank_le_two (M₀ : QuadModel QF V K γ)
    {W' : Submodule K M₀.E} {b c : M₀.E} (hbW' : b ∈ W') (hcW' : c ∈ W')
    (hb : b ≠ 0) (hcb : ∀ a : K, c ≠ a • b) (hW' : Module.finrank K W' ≤ 2)
    {x : M₀.E} (hx : x ∈ W') : ∃ a d : K, x = a • b + d • c := by
  rw [eq_span_pair_of_finrank_le_two M₀ hbW' hcW' hb hcb hW'] at hx
  obtain ⟨a, d, h⟩ := Submodule.mem_span_pair.mp hx
  exact ⟨a, d, h.symm⟩

theorem sub_mem_span_of_perp (M₀ : QuadModel QF V K γ) {T : M₀.E →ₗ[K] M₀.E}
    (hsa : ∀ v w, M₀.B (T v - v) w = M₀.B v (T w - w)) {b : M₀.E} (hb : b ≠ 0)
    {W' : Submodule K M₀.E} (hbW' : b ∈ W') (hW' : Module.finrank K W' ≤ 2)
    (hTW' : ∀ v, M₀.B v b = 0 → T v - v ∈ W')
    (halt : ∀ v, M₀.B v b = 0 → M₀.B (T v - v) v = 0) :
    ∀ v, M₀.B v b = 0 → ∃ c : K, T v - v = c • b := by
  intro v hv
  by_cases hle : W' ≤ Submodule.span K ({b} : Set M₀.E)
  · obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hle (hTW' v hv))
    exact ⟨a, ha.symm⟩
  · have hex : ∃ c ∈ W', c ∉ Submodule.span K ({b} : Set M₀.E) := by
      by_contra hcon
      push Not at hcon
      exact hle fun x hx => hcon x hx
    obtain ⟨c, hcW, hcb⟩ := hex
    have hcb' : ∀ a : K, c ≠ a • b := fun a ha =>
      hcb (Submodule.mem_span_singleton.mpr ⟨a, ha.symm⟩)
    obtain ⟨v', hv'b, hcv'⟩ := exists_B_eq_zero_ne_of_not_mem_span hb hcb'
    have hcoord : ∀ x ∈ W', ∃ a d : K, x = a • b + d • c :=
      fun x hx => exists_coord_of_finrank_le_two M₀ hbW' hcW hb hcb' hW' hx
    have hbperp : M₀.B b v' = 0 := by rw [B_comm, hv'b, neg_zero]
    obtain ⟨a', d', hd'⟩ := hcoord (T v' - v') (hTW' v' hv'b)
    have hd'0 : d' = 0 := by
      have h0 := halt v' hv'b
      rw [hd'] at h0
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        hbperp, zero_mul, mul_zero, zero_add] at h0
      exact (mul_eq_zero.mp h0).resolve_right hcv'
    have hTv' : T v' - v' = a' • b := by rw [hd', hd'0, zero_smul, add_zero]
    obtain ⟨a, d, hd⟩ := hcoord (T v - v) (hTW' v hv)
    have hd0 : d = 0 := by
      have h0 := hsa v v'
      rw [hd, hTv'] at h0
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        hbperp, zero_mul, mul_zero, zero_add] at h0
      rw [hv, mul_zero] at h0
      exact (mul_eq_zero.mp h0).resolve_right hcv'
    exact ⟨a, by rw [hd, hd0, zero_smul, add_zero]⟩

private theorem orthogonal_eq_self_of_totally_singular (M₀ : QuadModel QF V K γ)
    {W : Submodule K M₀.E} (hWs : ∀ w ∈ W, M₀.Qf w = 0)
    (hWo : ∀ v, (∀ w ∈ W, M₀.B v w = 0) → v ∈ W) :
    M₀.B.orthogonal W = W := by
  have hBzero : ∀ x ∈ W, ∀ y ∈ W, M₀.B x y = 0 := by
    intro x hx y hy
    have h := M₀.Qf_add x y
    rw [hWs _ (W.add_mem hx hy), hWs x hx, hWs y hy] at h
    simpa using h.symm
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hx
    exact hWo x fun y hy => by rw [B_comm, hx y hy, neg_zero]
  · intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    exact hBzero y hy x hx

private theorem sub_mem_of_fix_of_isometry (M₀ : QuadModel QF V K γ) {T : M₀.E →ₗ[K] M₀.E}
    (hT : ∀ e, M₀.Qf (T e) = M₀.Qf e) {W : Submodule K M₀.E}
    (hWs : ∀ w ∈ W, M₀.Qf w = 0)
    (hWo : ∀ v, (∀ w ∈ W, M₀.B v w = 0) → v ∈ W) (hfix : ∀ w ∈ W, T w = w)
    (f : M₀.E) : T f - f ∈ W := by
  have horth := orthogonal_eq_self_of_totally_singular M₀ hWs hWo
  have hmem : T f - f ∈ M₀.B.orthogonal (M₀.B.orthogonal W) := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro u hu
    have huW : u ∈ W := by rwa [horth] at hu
    have h1 : M₀.B u (T f) = M₀.B u f := by
      have h := B_iso hT u f
      rwa [hfix u huW] at h
    rw [map_sub, h1, sub_self]
  simpa only [horth] using hmem

private theorem range_le_two_of_coord (M₀ : QuadModel QF V K γ) {T : M₀.E →ₗ[K] M₀.E}
    {b : M₀.E} (hb : b ≠ 0)
    (hcoord : ∀ v, M₀.B v b = 0 → ∃ c : K, T v - v = c • b) :
    Module.finrank K (LinearMap.range (T - 1)) ≤ 2 := by
  refine finrank_range_le_two hb ?_
  intro v hv
  obtain ⟨c, hc⟩ := hcoord v hv
  exact ⟨c, by rw [← hc]; abel⟩

private theorem halt_of_totally_singular [CharP K 2] (M₀ : QuadModel QF V K γ)
    {T : M₀.E →ₗ[K] M₀.E} (hT : ∀ e, M₀.Qf (T e) = M₀.Qf e)
    {W : Submodule K M₀.E} (hWs : ∀ w ∈ W, M₀.Qf w = 0) {b : M₀.E}
    (hTH : ∀ v, M₀.B v b = 0 → T v - v ∈ W) :
    ∀ v, M₀.B v b = 0 → M₀.B (T v - v) v = 0 := by
  intro v hv
  have hQ : M₀.Qf (T v - v) = 0 := hWs _ (hTH v hv)
  have hB := Qf_sub_eq_B M₀ hT v
  rw [hQ] at hB
  rw [B_comm, ← hB, neg_zero]

private theorem sub_mem_of_fix (M₀ : QuadModel QF V K γ) {T : M₀.E →ₗ[K] M₀.E}
    (hT : ∀ e, M₀.Qf (T e) = M₀.Qf e) {W : Submodule K M₀.E}
    (hWs : ∀ w ∈ W, M₀.Qf w = 0)
    (hWo : ∀ v, (∀ w ∈ W, M₀.B v w = 0) → v ∈ W) (hfix : ∀ w ∈ W, T w = w)
    {b : M₀.E} (hb : b ≠ 0) (hTH : ∀ v, M₀.B v b = 0 → T v - v ∈ W) :
    ∀ v, T v - v ∈ W := by
  obtain ⟨f₀, hf₀⟩ := exists_B_ne_zero hb
  set f : M₀.E := (M₀.B f₀ b)⁻¹ • f₀ with hfdef
  have hfb : M₀.B f b = 1 := by
    rw [hfdef, map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf₀]
  have hTf : T f - f ∈ W := sub_mem_of_fix_of_isometry M₀ hT hWs hWo hfix f
  intro v
  set c : K := M₀.B v b with hcdef
  have hu : M₀.B (v - c • f) b = 0 := by
    rw [hcdef, map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hfb]
    ring
  have h1 : T (v - c • f) - (v - c • f) ∈ W := hTH _ hu
  have hEq : T v - v = (T (v - c • f) - (v - c • f)) + c • (T f - f) := by
    rw [show v = (v - c • f) + c • f by abel, map_add, map_smul, smul_sub]
    abel_nf
  rw [hEq]
  exact W.add_mem h1 (W.smul_mem c hTf)

private theorem ne_of_ker_flip_of_fix (M₀ : QuadModel QF V K γ) {T : M₀.E →ₗ[K] M₀.E}
    {W : Submodule K M₀.E} (hWs : ∀ w ∈ W, M₀.Qf w = 0)
    (hWo : ∀ v, (∀ w ∈ W, M₀.B v w = 0) → v ∈ W) {b : M₀.E} (hb : b ≠ 0)
    (hfix : ∀ w ∈ W, T w = w) {v₁ : M₀.E} (hv₁ : T v₁ - v₁ = b) :
    W ⊓ LinearMap.ker (M₀.B.flip v₁) ≠ W := by
  intro hEq
  have horth : M₀.B.orthogonal W = W := orthogonal_eq_self_of_totally_singular M₀ hWs hWo
  have hWle : W ≤ LinearMap.ker (M₀.B.flip v₁) := by
    rw [← hEq]
    exact inf_le_right
  have hv₁perp : v₁ ∈ M₀.B.orthogonal W := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro u hu
    have h0 : M₀.B.flip v₁ u = 0 := hWle hu
    rwa [LinearMap.BilinForm.flip_apply] at h0
  have hv₁W : v₁ ∈ W := by rwa [horth] at hv₁perp
  have hzero : T v₁ - v₁ = 0 := by rw [hfix v₁ hv₁W, sub_self]
  rw [hv₁] at hzero
  exact hb hzero

private theorem exists_plane_of_fix [CharP K 2] (M₀ : QuadModel QF V K γ)
    {T : M₀.E →ₗ[K] M₀.E} (hT : ∀ e, M₀.Qf (T e) = M₀.Qf e) (hT2 : ∀ e, T (T e) = e)
    {W : Submodule K M₀.E} (hWs : ∀ w ∈ W, M₀.Qf w = 0)
    (hWo : ∀ v, (∀ w ∈ W, M₀.B v w = 0) → v ∈ W) (hW3 : Module.finrank K W = 3)
    {b : M₀.E} (hb : b ≠ 0) (hbW : b ∈ W) (hfix : ∀ w ∈ W, T w = w)
    (hTH : ∀ v, M₀.B v b = 0 → T v - v ∈ W)
    (hbR : b ∈ LinearMap.range (T - 1)) :
    ∃ W' : Submodule K M₀.E, b ∈ W' ∧ Module.finrank K W' ≤ 2 ∧
      (∀ v, M₀.B v b = 0 → T v - v ∈ W') := by
  obtain ⟨v₁, hv₁⟩ := LinearMap.mem_range.mp hbR
  have hv₁' : T v₁ - v₁ = b := by
    simpa only [LinearMap.sub_apply, Module.End.one_apply] using hv₁
  have hBv₁ : M₀.B v₁ b = 0 := by
    have h := Qf_sub_eq_B M₀ hT v₁
    rw [hv₁', hWs b hbW] at h
    exact h.symm
  have hBbv₁ : M₀.B b v₁ = 0 := by rw [B_comm, hBv₁, neg_zero]
  refine ⟨W ⊓ LinearMap.ker (M₀.B.flip v₁), ?_, ?_, ?_⟩
  · refine ⟨hbW, ?_⟩
    show M₀.B.flip v₁ b = 0
    rw [LinearMap.BilinForm.flip_apply]
    exact hBbv₁
  · have hne : W ⊓ LinearMap.ker (M₀.B.flip v₁) ≠ W :=
      ne_of_ker_flip_of_fix M₀ hWs hWo hb hfix hv₁'
    have hlt : W ⊓ LinearMap.ker (M₀.B.flip v₁) < W := by
      rw [lt_iff_le_and_ne]
      exact ⟨inf_le_left, hne⟩
    have := Submodule.finrank_lt_finrank_of_lt hlt
    omega
  · intro v hv
    refine ⟨hTH v hv, ?_⟩
    show M₀.B.flip v₁ (T v - v) = 0
    rw [LinearMap.BilinForm.flip_apply, B_sub_self_adjoint M₀ hT hT2 v v₁, hv₁', hv]

theorem finrank_range_le_two_of_fix [CharP K 2] (M₀ : QuadModel QF V K γ)
    {T : M₀.E →ₗ[K] M₀.E} (hT : ∀ e, M₀.Qf (T e) = M₀.Qf e) (hT2 : ∀ e, T (T e) = e)
    {W : Submodule K M₀.E} (hWs : ∀ w ∈ W, M₀.Qf w = 0)
    (hWo : ∀ v, (∀ w ∈ W, M₀.B v w = 0) → v ∈ W) (hW3 : Module.finrank K W = 3)
    {b : M₀.E} (hb : b ≠ 0) (hbW : b ∈ W) (hTH : ∀ v, M₀.B v b = 0 → T v - v ∈ W)
    (hfix : ∀ w ∈ W, T w = w) :
    LinearMap.range (T - 1) ≤ W ∧ Module.finrank K (LinearMap.range (T - 1)) ≤ 2 := by
  have hmem := sub_mem_of_fix M₀ hT hWs hWo hfix hb hTH
  have hle : LinearMap.range (T - 1) ≤ W := by
    rintro x ⟨v, rfl⟩
    simpa only [LinearMap.sub_apply, Module.End.one_apply] using hmem v
  refine ⟨hle, ?_⟩
  have h3le : Module.finrank K (LinearMap.range (T - 1)) ≤ 3 := by
    have hmono := Submodule.finrank_mono hle
    omega
  by_cases h3 : Module.finrank K (LinearMap.range (T - 1)) = 3
  · have hrangeW : LinearMap.range (T - 1) = W :=
      Submodule.eq_of_le_of_finrank_eq hle (by omega)
    have hbR : b ∈ LinearMap.range (T - 1) := by rw [hrangeW]; exact hbW
    obtain ⟨W', hbW', hW', hTW'⟩ :=
      exists_plane_of_fix M₀ hT hT2 hWs hWo hW3 hb hbW hfix hTH hbR
    have halt := halt_of_totally_singular M₀ hT hWs hTH
    have hcoord := sub_mem_span_of_perp M₀ (B_sub_self_adjoint M₀ hT hT2) hb hbW' hW'
      hTW' halt
    have h2 := range_le_two_of_coord M₀ hb hcoord
    omega
  · omega

private theorem mem_range_of_move (M₀ : QuadModel QF V K γ) {T : M₀.E →ₗ[K] M₀.E}
    {W : Submodule K M₀.E} {b : M₀.E}
    (hTW : ∀ w ∈ W, ∃ c : K, T w - w = c • b) (hmove : ∃ w ∈ W, T w ≠ w) :
    b ∈ LinearMap.range (T - 1) := by
  obtain ⟨w, hwW, hTw⟩ := hmove
  obtain ⟨c, hc⟩ := hTW w hwW
  have hc0 : c ≠ 0 := fun h0 => hTw (sub_eq_zero.mp (by rw [hc, h0, zero_smul]))
  refine ⟨c⁻¹ • w, ?_⟩
  rw [map_smul, LinearMap.sub_apply, Module.End.one_apply, hc, smul_smul, inv_mul_cancel₀ hc0,
    one_smul]

private theorem le_two_of_move_core [CharP K 2] (M₀ : QuadModel QF V K γ)
    {T : M₀.E →ₗ[K] M₀.E} (hT : ∀ e, M₀.Qf (T e) = M₀.Qf e) (hT2 : ∀ e, T (T e) = e)
    {W : Submodule K M₀.E} (hWs : ∀ w ∈ W, M₀.Qf w = 0) (hW3 : Module.finrank K W = 3)
    {b : M₀.E} (hb : b ≠ 0) (hbW : b ∈ W) (hTb : T b = b)
    (hTH : ∀ v, M₀.B v b = 0 → T v - v ∈ W)
    (hmove : ∃ w ∈ W, T w ≠ w) :
    Module.finrank K (LinearMap.range (T - 1)) ≤ 2 := by
  obtain ⟨w, hwW, hTw⟩ := hmove
  set W' : Submodule K M₀.E := W ⊓ LinearMap.ker (T - 1) with hW'def
  have hbW' : b ∈ W' := by
    rw [hW'def]
    refine ⟨hbW, ?_⟩
    show (T - 1) b = 0
    rw [LinearMap.sub_apply, Module.End.one_apply, hTb, sub_self]
  have hne : W' ≠ W := by
    intro hEq
    have hwU : w ∈ W' := by rw [hEq]; exact hwW
    exact hTw (by
      have hmem : w ∈ W ⊓ LinearMap.ker (T - 1) := by rwa [hW'def] at hwU
      have h0 : (T - 1) w = 0 := hmem.2
      rwa [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h0)
  have hW' : Module.finrank K W' ≤ 2 := by
    have hlt : W' < W := by
      rw [lt_iff_le_and_ne]
      exact ⟨by rw [hW'def]; exact inf_le_left, hne⟩
    have := Submodule.finrank_lt_finrank_of_lt hlt
    omega
  have hTW' : ∀ v, M₀.B v b = 0 → T v - v ∈ W' := by
    intro v hv
    rw [hW'def]
    refine ⟨hTH v hv, ?_⟩
    show (T - 1) (T v - v) = 0
    simpa only [LinearMap.sub_apply, Module.End.one_apply] using
      sub_sub_eq_zero_of_invol hT2 v
  have hcoord := sub_mem_span_of_perp M₀ (B_sub_self_adjoint M₀ hT hT2) hb hbW' hW'
    hTW' (halt_of_totally_singular M₀ hT hWs hTH)
  exact range_le_two_of_coord M₀ hb hcoord

theorem finrank_range_le_two_of_move [CharP K 2] (M₀ : QuadModel QF V K γ)
    {T : M₀.E →ₗ[K] M₀.E} (hT : ∀ e, M₀.Qf (T e) = M₀.Qf e) (hT2 : ∀ e, T (T e) = e)
    {W : Submodule K M₀.E} (hWs : ∀ w ∈ W, M₀.Qf w = 0) (hW3 : Module.finrank K W = 3)
    {b : M₀.E} (hb : b ≠ 0) (hbW : b ∈ W) (hTb : T b = b)
    (hTW : ∀ w ∈ W, ∃ c : K, T w - w = c • b) (hTH : ∀ v, M₀.B v b = 0 → T v - v ∈ W)
    (hmove : ∃ w ∈ W, T w ≠ w) :
    b ∈ LinearMap.range (T - 1) ∧ Module.finrank K (LinearMap.range (T - 1)) ≤ 2 :=
  ⟨mem_range_of_move M₀ hTW hmove,
    le_two_of_move_core M₀ hT hT2 hWs hW3 hb hbW hTb hTH hmove⟩

theorem finrank_range_sub_one_le_two_of_flag [CharP K 2] (M₀ : QuadModel QF V K γ)
    {T : M₀.E →ₗ[K] M₀.E} (hT : ∀ e, M₀.Qf (T e) = M₀.Qf e) (hT2 : ∀ e, T (T e) = e)
    {W : Submodule K M₀.E} (hWs : ∀ w ∈ W, M₀.Qf w = 0)
    (hWo : ∀ v, (∀ w ∈ W, M₀.B v w = 0) → v ∈ W) (hW3 : Module.finrank K W = 3)
    {b : M₀.E} (hb : b ≠ 0) (hbW : b ∈ W) (hTb : T b = b)
    (hTW : ∀ w ∈ W, ∃ c : K, T w - w = c • b) :
    Module.finrank K (LinearMap.range (T - 1)) ≤ 2 ∧
      (LinearMap.range (T - 1) ≤ W ∨ b ∈ LinearMap.range (T - 1)) := by
  have hTH : ∀ v, M₀.B v b = 0 → T v - v ∈ W :=
    sub_mem_of_perp_of_flag M₀ hT hWo hTb hTW
  by_cases hfix : ∀ w ∈ W, T w = w
  · have h := finrank_range_le_two_of_fix M₀ hT hT2 hWs hWo hW3 hb hbW hTH hfix
    exact ⟨h.2, Or.inl h.1⟩
  · push Not at hfix
    obtain ⟨w, hwW, hTw⟩ := hfix
    have h := finrank_range_le_two_of_move M₀ hT hT2 hWs hW3 hb hbW hTb hTW hTH
      ⟨w, hwW, hTw⟩
    exact ⟨h.2, Or.inr h.1⟩

theorem two_le_finrank_range_sub_one [CharP K 2] (M₀ : QuadModel QF V K γ)
    {T : M₀.E →ₗ[K] M₀.E} (hT : ∀ e, M₀.Qf (T e) = M₀.Qf e) (hT1 : ∃ v, T v ≠ v)
    (hs : ∀ v ∈ LinearMap.range (T - 1), M₀.Qf v = 0) :
    2 ≤ Module.finrank K (LinearMap.range (T - 1)) := by
  by_contra hcon
  have hle1 : Module.finrank K (LinearMap.range (T - 1)) ≤ 1 := by omega
  have hne : LinearMap.range (T - 1) ≠ ⊥ := by
    rintro hbot
    obtain ⟨v, hv⟩ := hT1
    have hmem : (T - 1) v ∈ LinearMap.range (T - 1) := LinearMap.mem_range_self _ _
    rw [hbot] at hmem
    have h0 : (T - 1) v = 0 := by simpa using hmem
    rw [LinearMap.sub_apply] at h0
    exact hv (sub_eq_zero.mp h0)
  have h1 : Module.finrank K (LinearMap.range (T - 1)) = 1 :=
    le_antisymm hle1 (Submodule.one_le_finrank_iff.mpr hne)
  obtain ⟨p, hp0, hp⟩ := finrank_eq_one_iff'.mp h1
  have hp1 : p.1 ≠ 0 := fun h => hp0 (Subtype.ext h)
  have hps : M₀.Qf p.1 = 0 := hs p.1 p.2
  have hr : ∀ e, ∃ c : K, T e = e + c • p.1 := by
    intro e
    obtain ⟨c, hc⟩ := hp ⟨(T - 1) e, LinearMap.mem_range_self _ _⟩
    refine ⟨c, ?_⟩
    have h : c • p.1 = T e - e := by
      simpa [LinearMap.sub_apply] using congrArg Subtype.val hc
    rw [show T e = e + (T e - e) by abel, h]
  obtain ⟨v, hv⟩ := hT1
  exact hv (eq_one_of_range_le hT hp1 hps hr v)

theorem finrank_range_eq_two_of_mem (M₀ : QuadModel QF V K γ) {T : M₀.E →ₗ[K] M₀.E}
    (hP : Module.finrank K (LinearMap.range (T - 1)) ≤ 2) {b b' : M₀.E}
    (hbP : b ∈ LinearMap.range (T - 1)) (hb'P : b' ∈ LinearMap.range (T - 1)) (hb : b ≠ 0)
    (hind : ∀ c : K, b' ≠ c • b) (hQb : M₀.Qf b = 0) (hQb' : M₀.Qf b' = 0)
    (hB : M₀.B b b' = 0) :
    Module.finrank K (LinearMap.range (T - 1)) = 2 ∧
      ∀ v ∈ LinearMap.range (T - 1), M₀.Qf v = 0 := by
  have hdim : Module.finrank K (Submodule.span K ({b, b'} : Set M₀.E)) = 2 :=
    finrank_span_pair_eq_two M₀ hb hind
  have hle : Submodule.span K ({b, b'} : Set M₀.E) ≤ LinearMap.range (T - 1) := by
    rw [Submodule.span_le]
    rintro x (rfl | rfl)
    · exact hbP
    · exact hb'P
  have h2 : 2 ≤ Module.finrank K (LinearMap.range (T - 1)) := by
    have hmono := Submodule.finrank_mono hle
    omega
  have hEq : Module.finrank K (LinearMap.range (T - 1)) = 2 := le_antisymm hP h2
  have hrange : LinearMap.range (T - 1) = Submodule.span K ({b, b'} : Set M₀.E) :=
    (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm
  refine ⟨hEq, ?_⟩
  intro v hv
  rw [hrange] at hv
  obtain ⟨a, d, ha⟩ := Submodule.mem_span_pair.mp hv
  rw [← ha, M₀.Qf_add, M₀.Qf_smul, M₀.Qf_smul, hQb, hQb']
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hB, mul_zero, add_zero, zero_add]

theorem finrank_range_eq_two_and_singular_of_flag [CharP K 2] (M₀ : QuadModel QF V K γ)
    {T : M₀.E →ₗ[K] M₀.E} (hT : ∀ e, M₀.Qf (T e) = M₀.Qf e) (hT2 : ∀ e, T (T e) = e)
    {W : Submodule K M₀.E} (hWs : ∀ w ∈ W, M₀.Qf w = 0)
    (hWo : ∀ v, (∀ w ∈ W, M₀.B v w = 0) → v ∈ W) (hW3 : Module.finrank K W = 3)
    {b : M₀.E} (hb : b ≠ 0) (hbW : b ∈ W) (hTb : T b = b)
    (hTW : ∀ w ∈ W, ∃ c : K, T w - w = c • b) (hT1 : ∃ v, T v ≠ v)
    {S : M₀.E →ₗ[K] M₀.E} (hS : ∀ e, M₀.Qf (S e) = M₀.Qf e) (hST : ∀ e, S (T e) = T (S e))
    (hSb : ∀ c : K, S b ≠ c • b) :
    Module.finrank K (LinearMap.range (T - 1)) = 2 ∧
      ∀ v ∈ LinearMap.range (T - 1), M₀.Qf v = 0 := by
  obtain ⟨hP, hdisj⟩ :=
    finrank_range_sub_one_le_two_of_flag M₀ hT hT2 hWs hWo hW3 hb hbW hTb hTW
  have hQb : M₀.Qf b = 0 := hWs b hbW
  rcases hdisj with hleW | hbR
  · have hs : ∀ v ∈ LinearMap.range (T - 1), M₀.Qf v = 0 :=
      fun v hv => hWs v (hleW hv)
    have h2 := two_le_finrank_range_sub_one M₀ hT hT1 hs
    exact ⟨le_antisymm hP h2, hs⟩
  · obtain ⟨v, hv⟩ := LinearMap.mem_range.mp hbR
    have hv' : T v - v = b := by
      simpa only [LinearMap.sub_apply, Module.End.one_apply] using hv
    have hSbP : S b ∈ LinearMap.range (T - 1) := by
      refine ⟨S v, ?_⟩
      show T (S v) - S v = S b
      rw [← hST v, ← map_sub, hv']
    have hQb' : M₀.Qf (S b) = 0 := by rw [hS b, hQb]
    have hB : M₀.B b (S b) = 0 := by
      have h1 : M₀.B b (S b) = M₀.B (T v - v) (S b) := by rw [hv']
      rw [h1, B_sub_self_adjoint M₀ hT hT2 v (S b)]
      have h0 : T (S b) = S b := by rw [← hST b, hTb]
      rw [h0, sub_self, map_zero]
    exact finrank_range_eq_two_of_mem M₀ hP hbR hSbP hb hSb hQb hQb' hB

end CFSG.RankThree.GF2n.Tim79.QuadModel
