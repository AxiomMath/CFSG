module

public import CFSG.RankThree.SubgroupLists.SymplecticSkewAxes

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank Module

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K]

theorem unipAxis_conj (x h : GL V₄ K) :
    unipAxis (h * x * h⁻¹) = translate h (unipAxis x) := by
  ext u
  rw [mem_translate]
  constructor
  · intro hu
    refine ⟨((h⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) *ᵥ u, ?_, gl_mulVec_inv_mulVec h u⟩
    rw [← mem_unipAxis_conj (h := h), gl_mulVec_inv_mulVec]
    exact hu
  · rintro ⟨v, hv, rfl⟩
    exact mem_unipAxis_conj.mpr hv

theorem finrank_unipAxis_conj (x h : GL V₄ K) :
    finrank K (unipAxis (h * x * h⁻¹)) = finrank K (unipAxis x) := by
  rw [unipAxis_conj, finrank_translate]

theorem sub_one_mulVec_mem_unipAxis {x : GL V₄ K} (hx : IsSqZero x) (v : V₄ → K) :
    ((x : Matrix V₄ V₄ K) - 1) *ᵥ v ∈ unipAxis x := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  exact sub_mem_unipAxis hx v

theorem sub_one_mulVec_eq_zero {x : GL V₄ K} {v : V₄ → K} (hv : v ∈ unipAxis x) :
    ((x : Matrix V₄ V₄ K) - 1) *ᵥ v = 0 := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, mem_unipAxis.mp hv, sub_self]

theorem mulVec_pow_of_isSqZero {x : GL V₄ K} (hx : IsSqZero x) (m : ℕ) (v : V₄ → K) :
    ((x ^ m : GL V₄ K) : Matrix V₄ V₄ K) *ᵥ v =
      v + (m : K) • (((x : Matrix V₄ V₄ K) - 1) *ᵥ v) := by
  induction m generalizing v with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', gl_mulVec_mul, ih]
    have hN : ((x : Matrix V₄ V₄ K) - 1) *ᵥ (((x : Matrix V₄ V₄ K) - 1) *ᵥ v) = 0 := by
      rw [Matrix.mulVec_mulVec, hx, Matrix.zero_mulVec]
    have hxv : (x : Matrix V₄ V₄ K) *ᵥ v = v + ((x : Matrix V₄ V₄ K) - 1) *ᵥ v := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
    have hxNv : (x : Matrix V₄ V₄ K) *ᵥ (((x : Matrix V₄ V₄ K) - 1) *ᵥ v) =
        ((x : Matrix V₄ V₄ K) - 1) *ᵥ v := by
      have := hN
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at this
      exact this
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, hxNv, hxv, Nat.cast_succ, add_smul, one_smul]
    abel

theorem mem_unipAxis_of_sub_one_mulVec_eq_zero {x : GL V₄ K} {v : V₄ → K}
    (hv : ((x : Matrix V₄ V₄ K) - 1) *ᵥ v = 0) : v ∈ unipAxis x := by
  rw [mem_unipAxis]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv
  exact hv

theorem mulVec_conj_triple {x x' : GL V₄ K} (hx : IsSqZero x) (hx' : IsSqZero x') (m : ℕ)
    {v : V₄ → K} (hv : v ∈ unipAxis x) :
    ((x' * x ^ m * x' : GL V₄ K) : Matrix V₄ V₄ K) *ᵥ v =
      (v + (m : K) • (((x : Matrix V₄ V₄ K) - 1) *ᵥ (((x' : Matrix V₄ V₄ K) - 1) *ᵥ v))) +
        ((x' : Matrix V₄ V₄ K) - 1) *ᵥ ((2 : K) • v +
          (m : K) • (((x : Matrix V₄ V₄ K) - 1) *ᵥ (((x' : Matrix V₄ V₄ K) - 1) *ᵥ v))) := by
  have hx'w : ∀ w, (x' : Matrix V₄ V₄ K) *ᵥ w = w + ((x' : Matrix V₄ V₄ K) - 1) *ᵥ w := by
    intro w; rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
  have hNv : ((x : Matrix V₄ V₄ K) - 1) *ᵥ v = 0 := sub_one_mulVec_eq_zero hv
  have hN'N' : ∀ w, ((x' : Matrix V₄ V₄ K) - 1) *ᵥ (((x' : Matrix V₄ V₄ K) - 1) *ᵥ w) = 0 := by
    intro w; rw [Matrix.mulVec_mulVec, hx', Matrix.zero_mulVec]
  set N := (x : Matrix V₄ V₄ K) - 1 with hN
  set N' := (x' : Matrix V₄ V₄ K) - 1 with hN'
  have e2 : ((x ^ m : GL V₄ K) : Matrix V₄ V₄ K) *ᵥ (v + N' *ᵥ v) =
      v + N' *ᵥ v + (m : K) • (N *ᵥ (N' *ᵥ v)) := by
    rw [mulVec_pow_of_isSqZero hx, ← hN, Matrix.mulVec_add, hNv, zero_add]
  rw [gl_mulVec_mul, gl_mulVec_mul, hx'w v, e2, hx'w]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hN'N', add_zero, two_smul]
  abel

theorem unipAxis_inf_conj_triple (h2 : (2 : K) ≠ 0) {x x' : GL V₄ K} (hx : IsSqZero x)
    (hx' : IsSqZero x') (hx2 : finrank K (unipAxis x) = 2)
    (hdisj : unipAxis x ⊓ unipAxis x' = ⊥) {μ : K} {a b : V₄ → K} (ha : a ∈ unipAxis x)
    (ha0 : a ≠ 0)
    (haμ : ((x : Matrix V₄ V₄ K) - 1) *ᵥ (((x' : Matrix V₄ V₄ K) - 1) *ᵥ a) = μ • a)
    (hb : b ∈ unipAxis x)
    (hbμ : ((x : Matrix V₄ V₄ K) - 1) *ᵥ (((x' : Matrix V₄ V₄ K) - 1) *ᵥ b) ≠ μ • b)
    {m : ℕ} (hmc : (m : K) * μ = -2) :
    unipAxis x ⊓ unipAxis ((x' * x ^ m * x') * x * (x' * x ^ m * x')⁻¹) =
      K ∙ (((x' * x ^ m * x' : GL V₄ K) : Matrix V₄ V₄ K) *ᵥ a) := by
  classical
  have hN'L' : ∀ v, ((x' : Matrix V₄ V₄ K) - 1) *ᵥ v ∈ unipAxis x' :=
    sub_one_mulVec_mem_unipAxis hx'
  have hNL : ∀ v, ((x : Matrix V₄ V₄ K) - 1) *ᵥ v ∈ unipAxis x :=
    sub_one_mulVec_mem_unipAxis hx
  have hmemL : ∀ v, v ∈ unipAxis x → v ∈ unipAxis x' → v = 0 := by
    intro v hv hv'
    have : v ∈ unipAxis x ⊓ unipAxis x' := ⟨hv, hv'⟩
    rw [hdisj] at this
    exact (Submodule.mem_bot _).mp this
  have hμ0 : μ ≠ 0 := by
    intro hμ
    rw [hμ, mul_zero] at hmc
    exact h2 (by linear_combination hmc)
  set g : GL V₄ K := x' * x ^ m * x' with hg
  have hkey : ∀ v ∈ unipAxis x, (g : Matrix V₄ V₄ K) *ᵥ v ∈ unipAxis x →
      (2 : K) • v + (m : K) • (((x : Matrix V₄ V₄ K) - 1) *ᵥ
        (((x' : Matrix V₄ V₄ K) - 1) *ᵥ v)) = 0 := by
    intro v hv hgv
    rw [hg, mulVec_conj_triple hx hx' m hv] at hgv
    have hfirst : v + (m : K) • (((x : Matrix V₄ V₄ K) - 1) *ᵥ
        (((x' : Matrix V₄ V₄ K) - 1) *ᵥ v)) ∈ unipAxis x :=
      (unipAxis x).add_mem hv ((unipAxis x).smul_mem _ (hNL _))
    have hsecond := (Submodule.add_mem_iff_right _ hfirst).mp hgv
    have h0 := hmemL _ hsecond (hN'L' _)
    have hw : (2 : K) • v + (m : K) • (((x : Matrix V₄ V₄ K) - 1) *ᵥ
        (((x' : Matrix V₄ V₄ K) - 1) *ᵥ v)) ∈ unipAxis x :=
      (unipAxis x).add_mem ((unipAxis x).smul_mem _ hv) ((unipAxis x).smul_mem _ (hNL _))
    exact hmemL _ hw (mem_unipAxis_of_sub_one_mulVec_eq_zero h0)
  have hga : (g : Matrix V₄ V₄ K) *ᵥ a ∈ unipAxis x := by
    rw [hg, mulVec_conj_triple hx hx' m ha, haμ, smul_smul, hmc]
    have e : (2 : K) • a + (-2 : K) • a = 0 := by
      rw [← add_smul, show (2 : K) + -2 = 0 by ring, zero_smul]
    rw [e, Matrix.mulVec_zero, add_zero]
    exact (unipAxis x).add_mem ha ((unipAxis x).smul_mem _ ha)
  set E : Submodule K (V₄ → K) := unipAxis x ⊓
    LinearMap.ker (Matrix.toLin' (((x : Matrix V₄ V₄ K) - 1) *
      ((x' : Matrix V₄ V₄ K) - 1) - μ • (1 : Matrix V₄ V₄ K))) with hE
  have hmemE : ∀ v, v ∈ E ↔ v ∈ unipAxis x ∧ ((x : Matrix V₄ V₄ K) - 1) *ᵥ
      (((x' : Matrix V₄ V₄ K) - 1) *ᵥ v) = μ • v := by
    intro v
    rw [hE, Submodule.mem_inf, LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.sub_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, sub_eq_zero]
  have hEa : K ∙ a = E := by
    have hle : K ∙ a ≤ E := by
      rw [Submodule.span_singleton_le_iff_mem, hmemE]
      exact ⟨ha, haμ⟩
    have hlt : E < unipAxis x := by
      refine lt_of_le_of_ne inf_le_left fun h => hbμ ?_
      have : b ∈ E := h ▸ hb
      exact ((hmemE b).mp this).2
    have hfin := Submodule.finrank_lt_finrank_of_lt hlt
    rw [hx2] at hfin
    apply Submodule.eq_of_le_of_finrank_le hle
    rw [finrank_span_singleton ha0]
    omega
  apply le_antisymm
  · intro w hw
    obtain ⟨hw, hw'⟩ := Submodule.mem_inf.mp hw
    rw [unipAxis_conj, mem_translate] at hw'
    obtain ⟨v, hv, rfl⟩ := hw'
    have h2v := hkey v hv hw
    have hvE : v ∈ E := by
      rw [hmemE]
      refine ⟨hv, ?_⟩
      have h3 : (m : K) • (((x : Matrix V₄ V₄ K) - 1) *ᵥ
          (((x' : Matrix V₄ V₄ K) - 1) *ᵥ v)) = -((2 : K) • v) :=
        eq_neg_of_add_eq_zero_right h2v
      have h4 := congrArg (fun w => μ • w) h3
      simp only [smul_smul, smul_neg] at h4
      rw [mul_comm μ (m : K), hmc] at h4
      have h5 := congrArg (fun w => (-2 : K)⁻¹ • w) h4
      simp only [smul_smul, smul_neg] at h5
      rw [inv_mul_cancel₀ (neg_ne_zero.mpr h2), one_smul,
        show (-2 : K)⁻¹ * (μ * 2) = -μ by field_simp, neg_smul, neg_neg] at h5
      exact h5
    rw [← hEa] at hvE
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hvE
    rw [Matrix.mulVec_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rw [Submodule.span_singleton_le_iff_mem]
    refine Submodule.mem_inf.mpr ⟨hga, ?_⟩
    rw [unipAxis_conj, mem_translate]
    exact ⟨a, ha, rfl⟩

theorem exists_spTrans_of_disjoint_axes {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {G : Subgroup (GL V₄ (ZMod p))} (hGS : G ≤ StatedSp 2 (ZMod p))
    {x x' : GL V₄ (ZMod p)} (hxG : x ∈ G) (hx'G : x' ∈ G) (hx : IsSqZero x) (hx' : IsSqZero x')
    (hx2 : finrank (ZMod p) (unipAxis x) = 2) (hdisj : unipAxis x ⊓ unipAxis x' = ⊥)
    {μ : ZMod p} {a b : V₄ → ZMod p} (ha : a ∈ unipAxis x) (ha0 : a ≠ 0)
    (haμ : ((x : Matrix V₄ V₄ (ZMod p)) - 1) *ᵥ (((x' : Matrix V₄ V₄ (ZMod p)) - 1) *ᵥ a) =
      μ • a)
    (hb : b ∈ unipAxis x)
    (hbμ : ((x : Matrix V₄ V₄ (ZMod p)) - 1) *ᵥ (((x' : Matrix V₄ V₄ (ZMod p)) - 1) *ᵥ b) ≠
      μ • b) :
    ∃ c : V₄ → ZMod p, ∃ d : ZMod p, c ≠ 0 ∧ d ≠ 0 ∧ spTrans c d ∈ G := by
  classical
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hμ0 : μ ≠ 0 := by
    intro hμ
    rw [hμ, zero_smul] at haμ
    have hmemL : ∀ v, v ∈ unipAxis x → v ∈ unipAxis x' → v = 0 := by
      intro v hv hv'
      have : v ∈ unipAxis x ⊓ unipAxis x' := ⟨hv, hv'⟩
      rw [hdisj] at this
      exact (Submodule.mem_bot _).mp this
    have h1 := hmemL _ (mem_unipAxis_of_sub_one_mulVec_eq_zero haμ)
      (sub_one_mulVec_mem_unipAxis hx' a)
    exact ha0 (hmemL a ha (mem_unipAxis_of_sub_one_mulVec_eq_zero h1))
  set m : ℕ := (-2 / μ).val with hm
  have hmc : (m : ZMod p) * μ = -2 := by
    rw [hm, ZMod.natCast_zmod_val, div_mul_cancel₀ _ hμ0]
  set g : GL V₄ (ZMod p) := x' * x ^ m * x' with hg
  have hgG : g ∈ G := G.mul_mem (G.mul_mem hx'G (G.pow_mem hxG m)) hx'G
  have hint := unipAxis_inf_conj_triple h2 hx hx' hx2 hdisj ha ha0 haμ hb hbμ hmc
  have hga0 : (g : Matrix V₄ V₄ (ZMod p)) *ᵥ a ≠ 0 := by
    intro h
    apply ha0
    rw [← gl_inv_mulVec_mulVec g a, h, Matrix.mulVec_zero]
  exact exists_spTrans_of_axes_meet hp5 hGS hxG (G.mul_mem (G.mul_mem hgG hxG) (G.inv_mem hgG))
    hx (isSqZero_conj hx g) hx2 (by rw [finrank_unipAxis_conj]; exact hx2) hga0 hint

theorem eq_or_inf_eq_bot_or_eq_span {A B : Submodule K (V₄ → K)} (hA : finrank K A = 2)
    (hB : finrank K B = 2) :
    A = B ∨ A ⊓ B = ⊥ ∨ ∃ z : V₄ → K, z ≠ 0 ∧ A ⊓ B = K ∙ z := by
  classical
  by_cases hbot : A ⊓ B = ⊥
  · exact Or.inr (Or.inl hbot)
  by_cases hne : A = B
  · exact Or.inl hne
  right; right
  have hlt : A ⊓ B < A := by
    refine lt_of_le_of_ne inf_le_left fun h => hne ?_
    have hle : A ≤ B := h ▸ inf_le_right
    exact Submodule.eq_of_le_of_finrank_eq hle (by rw [hA, hB])
  have hfin := Submodule.finrank_lt_finrank_of_lt hlt
  rw [hA] at hfin
  have hpos : finrank K ↥(A ⊓ B) ≠ 0 := by
    intro h
    exact hbot (Submodule.finrank_eq_zero.mp h)
  have h1 : finrank K ↥(A ⊓ B) = 1 := by omega
  obtain ⟨z, hz0, hz⟩ := (finrank_eq_one_iff'.mp h1)
  refine ⟨z, fun h => hz0 (Subtype.ext h), ?_⟩
  apply le_antisymm
  · intro w hw
    obtain ⟨c, hc⟩ := hz ⟨w, hw⟩
    rw [Submodule.mem_span_singleton]
    exact ⟨c, by simpa using congrArg Subtype.val hc⟩
  · rw [Submodule.span_singleton_le_iff_mem]
    exact z.2

theorem unipAxis_eq_or_disjoint {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {G : Subgroup (GL V₄ (ZMod p))} (hGS : G ≤ StatedSp 2 (ZMod p))
    (hnotr : ∀ (a : V₄ → ZMod p) (c : ZMod p), a ≠ 0 → c ≠ 0 → spTrans a c ∉ G)
    {x y : GL V₄ (ZMod p)} (hxG : x ∈ G) (hyG : y ∈ G) (hx : IsSqZero x) (hy : IsSqZero y)
    (hx2 : finrank (ZMod p) (unipAxis x) = 2) (hy2 : finrank (ZMod p) (unipAxis y) = 2) :
    unipAxis x = unipAxis y ∨ unipAxis x ⊓ unipAxis y = ⊥ := by
  rcases eq_or_inf_eq_bot_or_eq_span hx2 hy2 with h | h | ⟨z, hz0, hz⟩
  · exact Or.inl h
  · exact Or.inr h
  · obtain ⟨a, c, ha, hc, hT⟩ := exists_spTrans_of_axes_meet hp5 hGS hxG hyG hx hy hx2 hy2 hz0 hz
    exact absurd hT (hnotr a c ha hc)

theorem exists_conj_unipAxis_disjoint {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {G : Subgroup (GL V₄ (ZMod p))} (hGS : G ≤ StatedSp 2 (ZMod p)) (hirr : IsIrreducibleOn G)
    (hnotr : ∀ (a : V₄ → ZMod p) (c : ZMod p), a ≠ 0 → c ≠ 0 → spTrans a c ∉ G)
    {x : GL V₄ (ZMod p)} (hxG : x ∈ G) (hx : IsSqZero x)
    (hx2 : finrank (ZMod p) (unipAxis x) = 2) :
    ∃ g ∈ G, unipAxis x ⊓ unipAxis (g * x * g⁻¹) = ⊥ := by
  classical
  have hnot : ¬ ∀ g ∈ G, ∀ w ∈ unipAxis x, (g : Matrix V₄ V₄ (ZMod p)) *ᵥ w ∈ unipAxis x := by
    intro hinv
    rcases hirr _ hinv with h | h
    · rw [h, finrank_bot] at hx2
      exact absurd hx2 (by norm_num)
    · rw [h, finrank_top, Module.finrank_fintype_fun_eq_card] at hx2
      simp at hx2
  push Not at hnot
  obtain ⟨g, hg, w, hw, hgw⟩ := hnot
  refine ⟨g, hg, ?_⟩
  rcases unipAxis_eq_or_disjoint hp5 hGS hnotr hxG (G.mul_mem (G.mul_mem hg hxG) (G.inv_mem hg))
      hx (isSqZero_conj hx g) hx2 (by rw [finrank_unipAxis_conj]; exact hx2) with h | h
  · exfalso
    apply hgw
    rw [h, unipAxis_conj, mem_translate]
    exact ⟨w, hw, rfl⟩
  · exact h

end CFSG.RankThree.SubgroupLists
