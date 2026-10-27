module

public import CFSG.RankThree.GF2n.Stroth80.DictModel

public section

namespace CFSG.RankThree.GF2n.Tim79

open scoped commutatorElement

variable {G : Type} [Group G] {QF V : Subgroup G} {K : Type} [Field K] {γ : G → K}

namespace QuadModel

variable {M₀ : QuadModel QF V K γ}

theorem B_iso {T : M₀.E →ₗ[K] M₀.E} (hT : ∀ e, M₀.Qf (T e) = M₀.Qf e) (e f : M₀.E) :
    M₀.B (T e) (T f) = M₀.B e f := by
  have h1 := M₀.Qf_add (T e) (T f)
  have h2 := M₀.Qf_add e f
  rw [← map_add, hT, hT e, hT f] at h1
  linear_combination h2 - h1

theorem exists_B_ne_zero {e : M₀.E} (he : e ≠ 0) : ∃ f, M₀.B f e ≠ 0 := by
  by_contra hcon
  push Not at hcon
  exact he (M₀.nondeg e fun f => by rw [B_comm, hcon f, neg_zero])

theorem exists_smul_of_orthogonal {e₀ : M₀.E} (he₀ : e₀ ≠ 0) {v : M₀.E}
    (hv : ∀ h, M₀.B h e₀ = 0 → M₀.B v h = 0) : ∃ c : K, v = c • e₀ := by
  obtain ⟨f₀, hf₀⟩ := exists_B_ne_zero he₀
  set f := (M₀.B f₀ e₀)⁻¹ • f₀ with hf
  have hfe : M₀.B f e₀ = 1 := by
    rw [hf, map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf₀]
  refine ⟨- M₀.B v f, ?_⟩
  refine sub_eq_zero.mp (M₀.nondeg _ fun x => ?_)
  have hx : M₀.B (x - M₀.B x e₀ • f) e₀ = 0 := by
    rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hfe, mul_one,
      sub_self]
  have h1 := hv _ hx
  rw [map_sub, map_smul, smul_eq_mul] at h1
  rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, B_comm e₀ x]
  linear_combination h1

theorem coeff_mul_B_eq_zero {T : M₀.E →ₗ[K] M₀.E} (hT : ∀ e, M₀.Qf (T e) = M₀.Qf e)
    {e₀ : M₀.E} (hs : M₀.Qf e₀ = 0) {e : M₀.E} {c : K} (hc : T e = e + c • e₀) :
    c * M₀.B e e₀ = 0 := by
  have h1 := hT e
  rw [hc, M₀.Qf_add, M₀.Qf_smul, hs, map_smul, smul_eq_mul] at h1
  linear_combination h1

theorem eq_one_of_fix_perp {T : M₀.E →ₗ[K] M₀.E} (hT : ∀ e, M₀.Qf (T e) = M₀.Qf e)
    {e₀ : M₀.E} (he₀ : e₀ ≠ 0) (hs : M₀.Qf e₀ = 0)
    (hfix : ∀ h, M₀.B h e₀ = 0 → T h = h) (e : M₀.E) : T e = e := by
  by_cases hB : M₀.B e e₀ = 0
  · exact hfix e hB
  · obtain ⟨c, hc⟩ := exists_smul_of_orthogonal he₀ (v := T e - e) (fun h hh => by
      rw [map_sub, LinearMap.sub_apply, ← B_iso hT e h, hfix h hh, sub_self])
    have hc' : T e = e + c • e₀ := by rw [← hc]; abel
    have h0 := coeff_mul_B_eq_zero hT hs hc'
    have hc0 : c = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact h
      · exact absurd h hB
    rw [hc', hc0, zero_smul, add_zero]

theorem eq_one_of_range_le {T : M₀.E →ₗ[K] M₀.E} (hT : ∀ e, M₀.Qf (T e) = M₀.Qf e)
    {e₀ : M₀.E} (he₀ : e₀ ≠ 0) (hs : M₀.Qf e₀ = 0)
    (hr : ∀ e, ∃ c : K, T e = e + c • e₀) (e : M₀.E) : T e = e := by
  have key : ∀ e : M₀.E, M₀.B e e₀ ≠ 0 → T e = e := by
    intro e hB
    obtain ⟨c, hc⟩ := hr e
    have h0 := coeff_mul_B_eq_zero hT hs hc
    have hc0 : c = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact h
      · exact absurd h hB
    rw [hc, hc0, zero_smul, add_zero]
  by_cases hB : M₀.B e e₀ = 0
  · obtain ⟨f, hf⟩ := exists_B_ne_zero he₀
    have h1 := key f hf
    have h2 : M₀.B (e + f) e₀ ≠ 0 := by
      rw [map_add, LinearMap.add_apply, hB, zero_add]
      exact hf
    have h3 := key _ h2
    rw [map_add, h1] at h3
    exact add_right_cancel h3
  · exact key e hB

theorem finrank_range_le_two {T : M₀.E →ₗ[K] M₀.E} {e₀ : M₀.E} (he₀ : e₀ ≠ 0)
    (hr : ∀ h, M₀.B h e₀ = 0 → ∃ c : K, T h = h + c • e₀) :
    Module.finrank K (LinearMap.range (T - 1)) ≤ 2 := by
  obtain ⟨f₀, hf₀⟩ := exists_B_ne_zero he₀
  set f := (M₀.B f₀ e₀)⁻¹ • f₀ with hf
  have hfe : M₀.B f e₀ = 1 := by
    rw [hf, map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf₀]
  have hle : LinearMap.range (T - 1) ≤ Submodule.span K {e₀, (T - 1) f} := by
    rintro _ ⟨x, rfl⟩
    have hx : M₀.B (x - M₀.B x e₀ • f) e₀ = 0 := by
      rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hfe,
        mul_one, sub_self]
    obtain ⟨c, hc⟩ := hr _ hx
    have : (T - 1) x = c • e₀ + M₀.B x e₀ • (T - 1) f := by
      have h1 : (T - 1) (x - M₀.B x e₀ • f) = c • e₀ := by
        rw [LinearMap.sub_apply, hc]
        simp
      have h2 := congrArg (· + M₀.B x e₀ • (T - 1) f) h1
      simp only [map_sub, map_smul] at h2 ⊢
      rw [← h2]
      abel
    rw [this]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  calc Module.finrank K (LinearMap.range (T - 1))
      ≤ Module.finrank K (Submodule.span K {e₀, (T - 1) f}) := Submodule.finrank_mono hle
    _ ≤ 2 := by
      classical
      have h := finrank_span_finset_le_card (R := K) ({e₀, (T - 1) f} : Finset M₀.E)
      simp only [Finset.coe_insert, Finset.coe_singleton] at h
      exact h.trans Finset.card_le_two


theorem finrank_range_eq_two {T : M₀.E →ₗ[K] M₀.E} (hT : ∀ e, M₀.Qf (T e) = M₀.Qf e)
    {e₀ : M₀.E} (he₀ : e₀ ≠ 0) (hs : M₀.Qf e₀ = 0)
    (hr : ∀ h, M₀.B h e₀ = 0 → ∃ c : K, T h = h + c • e₀) (hne : ∃ e, T e ≠ e) :
    Module.finrank K (LinearMap.range (T - 1)) = 2 := by
  have hle := finrank_range_le_two he₀ hr
  by_contra hcon
  have h1 : Module.finrank K (LinearMap.range (T - 1)) ≤ 1 := by omega
  obtain ⟨e, he⟩ := hne
  by_cases hA : ∀ h, M₀.B h e₀ = 0 → T h = h
  · exact he (eq_one_of_fix_perp hT he₀ hs hA e)
  · push Not at hA
    obtain ⟨h₀, hh₀, hTh₀⟩ := hA
    obtain ⟨c₀, hc₀⟩ := hr h₀ hh₀
    have hc₀0 : c₀ ≠ 0 := by
      rintro rfl
      exact hTh₀ (by rw [hc₀, zero_smul, add_zero])
    have he₀R : e₀ ∈ LinearMap.range (T - 1) :=
      ⟨c₀⁻¹ • h₀, by
        rw [map_smul, LinearMap.sub_apply, Module.End.one_apply, hc₀, add_sub_cancel_left,
          smul_smul, inv_mul_cancel₀ hc₀0, one_smul]⟩
    have hspan : Submodule.span K {e₀} = LinearMap.range (T - 1) := by
      refine Submodule.eq_of_le_of_finrank_le ?_ ?_
      · rw [Submodule.span_le]
        simpa using he₀R
      · rw [finrank_span_singleton he₀]
        exact h1
    refine he (eq_one_of_range_le hT he₀ hs (fun e => ?_) e)
    have : (T - 1) e ∈ Submodule.span K {e₀} := by rw [hspan]; exact ⟨e, rfl⟩
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp this
    exact ⟨c, by
      have h2 : T e - e = c • e₀ := by simpa [LinearMap.sub_apply] using hc.symm
      rw [← h2]; abel⟩

@[expose] def lift (M₀ : QuadModel QF V K γ) (R : AddSubgroup M₀.E) : Subgroup G where
  carrier := {x | x ∈ QF ∧ M₀.π x ∈ R}
  mul_mem' := fun {x y} hx hy =>
    ⟨QF.mul_mem hx.1 hy.1, by rw [M₀.π_mul x hx.1 y hy.1]; exact R.add_mem hx.2 hy.2⟩
  one_mem' := ⟨QF.one_mem, by rw [pi_one M₀]; exact R.zero_mem⟩
  inv_mem' := fun {x} hx =>
    ⟨QF.inv_mem hx.1, by rw [pi_inv M₀ hx.1]; exact R.neg_mem hx.2⟩

theorem mem_lift {R : AddSubgroup M₀.E} {x : G} : x ∈ M₀.lift R ↔ x ∈ QF ∧ M₀.π x ∈ R := Iff.rfl

theorem mem_img_lift {R : AddSubgroup M₀.E} {v : M₀.E} : v ∈ M₀.img (M₀.lift R) ↔ v ∈ R := by
  constructor
  · rintro ⟨x, hx, -, rfl⟩
    exact hx.2
  · intro hv
    obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj v
    exact ⟨x, ⟨hxQ, hv⟩, hxQ, rfl⟩

theorem mem_img_commutator_zpowers {a : G} (T : M₀.E ≃ₗ[K] M₀.E)
    (ha : ∀ x ∈ QF, a * x * a⁻¹ ∈ QF) (ha' : ∀ x ∈ QF, a⁻¹ * x * a ∈ QF)
    (hT : ∀ x ∈ QF, M₀.π (a * x * a⁻¹) = T (M₀.π x)) {e : M₀.E} :
    e ∈ M₀.img ⁅QF, Subgroup.zpowers a⁆ ↔ e ∈ LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1) := by
  set R : AddSubgroup M₀.E := (LinearMap.range ((T : M₀.E →ₗ[K] M₀.E) - 1)).toAddSubgroup with hR
  have hTR : ∀ w, T w - w ∈ R := fun w => ⟨w, by simp [LinearMap.sub_apply]⟩
  have hRT : ∀ w ∈ R, T w ∈ R := by
    intro w hw
    obtain ⟨u, rfl⟩ := hw
    exact ⟨T u, by simp [LinearMap.sub_apply]⟩
  have hRT' : ∀ w ∈ R, T.symm w ∈ R := by
    intro w hw
    obtain ⟨u, rfl⟩ := hw
    refine ⟨T.symm u, ?_⟩
    simp [LinearMap.sub_apply]
  have hTR' : ∀ w, T.symm w - w ∈ R := by
    intro w
    have := R.neg_mem (hTR (T.symm w))
    rwa [LinearEquiv.apply_symm_apply, neg_sub] at this
  have hT' : ∀ x ∈ QF, M₀.π (a⁻¹ * x * a) = T.symm (M₀.π x) := by
    intro x hx
    rw [LinearEquiv.eq_symm_apply, ← hT _ (ha' x hx)]
    congr 1
    group
  have hpow : ∀ k : ℤ, ∀ x ∈ QF, a ^ k * x * (a ^ k)⁻¹ ∈ QF ∧
      M₀.π (a ^ k * x * (a ^ k)⁻¹) - M₀.π x ∈ R := by
    intro k
    induction k using Int.induction_on with
    | zero =>
      intro x hx
      simp only [zpow_zero, one_mul, inv_one, mul_one, sub_self]
      exact ⟨hx, R.zero_mem⟩
    | succ k ih =>
      intro x hx
      obtain ⟨h1, h2⟩ := ih x hx
      have e : a ^ ((k : ℤ) + 1) * x * (a ^ ((k : ℤ) + 1))⁻¹ =
          a * (a ^ (k : ℤ) * x * (a ^ (k : ℤ))⁻¹) * a⁻¹ := by
        rw [zpow_add_one, mul_inv_rev]
        group
      rw [e]
      refine ⟨ha _ h1, ?_⟩
      rw [hT _ h1]
      have e2 : T (M₀.π (a ^ (k : ℤ) * x * (a ^ (k : ℤ))⁻¹)) - M₀.π x =
          T (M₀.π (a ^ (k : ℤ) * x * (a ^ (k : ℤ))⁻¹) - M₀.π x) + (T (M₀.π x) - M₀.π x) := by
        rw [map_sub]; abel
      rw [e2]
      exact R.add_mem (hRT _ h2) (hTR _)
    | pred k ih =>
      intro x hx
      obtain ⟨h1, h2⟩ := ih x hx
      have e : a ^ (-(k : ℤ) - 1) * x * (a ^ (-(k : ℤ) - 1))⁻¹ =
          a⁻¹ * (a ^ (-(k : ℤ)) * x * (a ^ (-(k : ℤ)))⁻¹) * a := by
        rw [zpow_sub_one, mul_inv_rev, inv_inv]
        group
      rw [e]
      refine ⟨ha' _ h1, ?_⟩
      rw [hT' _ h1]
      have e2 : T.symm (M₀.π (a ^ (-(k : ℤ)) * x * (a ^ (-(k : ℤ)))⁻¹)) - M₀.π x =
          T.symm (M₀.π (a ^ (-(k : ℤ)) * x * (a ^ (-(k : ℤ)))⁻¹) - M₀.π x) +
            (T.symm (M₀.π x) - M₀.π x) := by
        rw [map_sub]; abel
      rw [e2]
      exact R.add_mem (hRT' _ h2) (hTR' _)
  constructor
  · rintro ⟨x, hxS, hxQ, rfl⟩
    have hle : ⁅QF, Subgroup.zpowers a⁆ ≤ M₀.lift R := by
      rw [Subgroup.commutator_le]
      intro y hy z hz
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      have hq := hpow k y⁻¹ (QF.inv_mem hy)
      have e : ⁅y, a ^ k⁆ = y * (a ^ k * y⁻¹ * (a ^ k)⁻¹) := by
        rw [commutatorElement_def]; group
      rw [e]
      refine ⟨QF.mul_mem hy hq.1, ?_⟩
      rw [M₀.π_mul _ hy _ hq.1]
      have h3 := hq.2
      rw [pi_inv M₀ hy, sub_neg_eq_add, add_comm] at h3
      exact h3
    exact (hle hxS).2
  · rintro ⟨w, rfl⟩
    obtain ⟨x, hxQ, hx⟩ := M₀.π_surj w
    have hxa : a * x⁻¹ * a⁻¹ ∈ QF := ha _ (QF.inv_mem hxQ)
    have hcomm : ⁅x, a⁆ = x * (a * x⁻¹ * a⁻¹) := by
      rw [commutatorElement_def]; group
    have hmem : -(((T : M₀.E →ₗ[K] M₀.E) - 1) w) ∈ M₀.img ⁅QF, Subgroup.zpowers a⁆ := by
      refine ⟨⁅x, a⁆, Subgroup.commutator_mem_commutator hxQ (Subgroup.mem_zpowers a),
        by rw [hcomm]; exact QF.mul_mem hxQ hxa, ?_⟩
      rw [hcomm, M₀.π_mul _ hxQ _ hxa, hT _ (QF.inv_mem hxQ), pi_inv M₀ hxQ, map_neg, hx]
      simp [LinearMap.sub_apply]
      abel
    simpa using (M₀.img ⁅QF, Subgroup.zpowers a⁆).neg_mem hmem

end QuadModel

end CFSG.RankThree.GF2n.Tim79
