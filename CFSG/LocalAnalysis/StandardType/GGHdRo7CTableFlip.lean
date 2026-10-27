module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CReflSteps

public section

namespace CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private noncomputable def hdRo7CFlipAux_proj {p : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod p) V)
    (F : Finset (Fin (n + 1))) : V →ₗ[ZMod p] V :=
  b.constr (ZMod p) fun i => if i ∈ F then b i else 0

private lemma hdRo7CFlipAux_proj_basis {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (F : Finset (Fin (n + 1)))
    (k : Fin (n + 1)) :
    hdRo7CFlipAux_proj b F (b k) = if k ∈ F then b k else 0 := by
  rw [hdRo7CFlipAux_proj, Module.Basis.constr_basis]

private lemma hdRo7CFlipAux_proj_apply {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (F : Finset (Fin (n + 1))) (u : V) :
    hdRo7CFlipAux_proj b F u = ∑ i ∈ F, b.coord i u • b i := by
  conv_lhs => rw [← Module.Basis.sum_repr b u]
  rw [map_sum]
  rw [← Finset.sum_subset (Finset.subset_univ F)]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [map_smul, hdRo7CFlipAux_proj_basis b F i, if_pos hi, Module.Basis.coord_apply]
  · intro x _ hxF
    rw [map_smul, hdRo7CFlipAux_proj_basis b F x, if_neg hxF, smul_zero]

private def hdRo7CFlipAux_w {p : ℕ} {n : ℕ} (F : Finset (Fin (n + 1))) (i : Fin (n + 1)) :
    ZMod p :=
  if i ∈ F then -1 else 1

private lemma hdRo7CFlipAux_w_mul_self {p : ℕ} {n : ℕ} (F : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) :
    hdRo7CFlipAux_w (p := p) F i * hdRo7CFlipAux_w (p := p) F i = 1 := by
  unfold hdRo7CFlipAux_w
  by_cases h : i ∈ F <;> simp [h]

private noncomputable def hdRo7CFlipAux_T {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (F : Finset (Fin (n + 1))) :
    V →ₗ[ZMod p] V :=
  LinearMap.id - (2 : ZMod p) • hdRo7CFlipAux_proj b F

private lemma hdRo7CFlipAux_T_basis {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (F : Finset (Fin (n + 1)))
    (k : Fin (n + 1)) :
    hdRo7CFlipAux_T b F (b k) = hdRo7CFlipAux_w (p := p) F k • b k := by
  rw [hdRo7CFlipAux_T, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply,
    hdRo7CFlipAux_proj_basis]
  by_cases hk : k ∈ F
  · rw [if_pos hk, two_smul]
    unfold hdRo7CFlipAux_w
    rw [if_pos hk, neg_one_smul]
    abel
  · rw [if_neg hk, smul_zero, sub_zero]
    unfold hdRo7CFlipAux_w
    rw [if_neg hk, one_smul]

private lemma hdRo7CFlipAux_T_comp {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (F : Finset (Fin (n + 1))) :
    (hdRo7CFlipAux_T b F).comp (hdRo7CFlipAux_T b F) = LinearMap.id := by
  apply b.ext
  intro k
  rw [LinearMap.comp_apply, hdRo7CFlipAux_T_basis, map_smul, hdRo7CFlipAux_T_basis, ← smul_assoc,
    smul_eq_mul, hdRo7CFlipAux_w_mul_self, one_smul]
  rfl

private noncomputable def hdRo7CFlipAux_signChange {p : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod p) V)
    (F : Finset (Fin (n + 1))) : V ≃ₗ[ZMod p] V :=
  LinearEquiv.ofInvolutive (hdRo7CFlipAux_T b F) (fun x => by
    have := congrArg (fun L : V →ₗ[ZMod p] V => L x) (hdRo7CFlipAux_T_comp b F)
    simpa [LinearMap.comp_apply] using this)

private lemma hdRo7CFlipAux_signChange_apply_eq {p : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod p) V)
    (F : Finset (Fin (n + 1))) (u : V) :
    hdRo7CFlipAux_signChange b F u = u - (2 : ZMod p) • hdRo7CFlipAux_proj b F u := by
  simp only [hdRo7CFlipAux_signChange, LinearEquiv.coe_ofInvolutive, hdRo7CFlipAux_T,
    LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply]

private lemma hdRo7CFlipAux_signChange_apply_basis {p : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod p) V)
    (F : Finset (Fin (n + 1))) (k : Fin (n + 1)) :
    hdRo7CFlipAux_signChange b F (b k) = hdRo7CFlipAux_w (p := p) F k • b k := by
  simp only [hdRo7CFlipAux_signChange, LinearEquiv.coe_ofInvolutive]
  exact hdRo7CFlipAux_T_basis b F k

private lemma hdRo7CFlipAux_signChange_mul_self {p : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod p) V)
    (F : Finset (Fin (n + 1))) :
    hdRo7CFlipAux_signChange b F * hdRo7CFlipAux_signChange b F = 1 := by
  apply (LinearEquiv.toLinearMap_inj).mp
  apply b.ext
  intro k
  change (hdRo7CFlipAux_signChange b F * hdRo7CFlipAux_signChange b F) (b k) =
    (1 : V ≃ₗ[ZMod p] V) (b k)
  rw [LinearEquiv.mul_apply, hdRo7CFlipAux_signChange_apply_basis, map_smul,
    hdRo7CFlipAux_signChange_apply_basis, ← smul_assoc, smul_eq_mul, hdRo7CFlipAux_w_mul_self,
    one_smul]
  rfl

private lemma hdRo7CFlipAux_signChange_mem {p : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod p) V)
    (F : Finset (Fin (n + 1))) (h0 : (0 : Fin (n + 1)) ∉ F) :
    C2SP p b (hdRo7CFlipAux_signChange b F) := by
  refine ⟨1, fun i => hdRo7CFlipAux_w (p := p) F i, rfl, ?_, ?_, ?_⟩
  · simp [hdRo7CFlipAux_w, h0]
  · intro i; unfold hdRo7CFlipAux_w; by_cases h : i ∈ F <;> simp [h]
  · intro i; rw [hdRo7CFlipAux_signChange_apply_basis, Equiv.Perm.one_apply]

private lemma hdRo7CFlipAux_coord_basis {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (i k : Fin (n + 1)) :
    b.coord k (b i) = if i = k then 1 else 0 := by
  rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]

private lemma hdRo7CFlipAux_coord_proj {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (F : Finset (Fin (n + 1))) (u : V)
    (k : Fin (n + 1)) :
    b.coord k (hdRo7CFlipAux_proj b F u) = if k ∈ F then b.coord k u else 0 := by
  rw [hdRo7CFlipAux_proj_apply, map_sum]
  trans ∑ i ∈ F, b.coord i u * (if i = k then 1 else 0)
  · apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, hdRo7CFlipAux_coord_basis, smul_eq_mul]
  · rw [show (∑ i ∈ F, b.coord i u * (if i = k then 1 else 0))
        = ∑ i ∈ F, (if k = i then b.coord i u else 0) by
          apply Finset.sum_congr rfl
          intro i _
          by_cases h : k = i <;> simp [h, eq_comm]]
    rw [Finset.sum_ite_eq]

private lemma hdRo7CFlipAux_supp_proj {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (F : Finset (Fin (n + 1))) (u : V)
    (hF : ∀ i ∈ F, b.coord i u ≠ 0) :
    Finset.univ.filter (fun i => b.coord i (hdRo7CFlipAux_proj b F u) ≠ 0) = F := by
  apply Finset.ext
  intro k
  rw [Finset.mem_filter]
  constructor
  · intro h
    by_contra hk
    rw [hdRo7CFlipAux_coord_proj, if_neg hk] at h
    exact h.2 rfl
  · intro hk
    exact ⟨Finset.mem_univ _, by rw [hdRo7CFlipAux_coord_proj, if_pos hk]; exact hF k hk⟩

private lemma hdRo7CFlipAux_sq_eq_one {p : ℕ} (hp3 : p = 3) (a : ZMod p) (ha : a ≠ 0) :
    a * a = 1 := by
  revert a
  rw [hp3]
  decide

private lemma hdRo7CFlipAux_phi_proj {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (F : Finset (Fin (n + 1))) (u : V)
    (φ : V →ₗ[ZMod p] ZMod p) (c : ZMod p)
    (hc : ∀ i, i ≠ 0 → φ (b i) = c * b.coord i u)
    (hFmem : ∀ i ∈ F, i ≠ 0 ∧ b.coord i u ≠ 0) (hp3 : p = 3) :
    φ (hdRo7CFlipAux_proj b F u) = c * (F.card : ZMod p) := by
  rw [hdRo7CFlipAux_proj_apply, map_sum]
  calc ∑ i ∈ F, φ (b.coord i u • b i)
      = ∑ i ∈ F, b.coord i u * φ (b i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [map_smul, smul_eq_mul]
    _ = ∑ i ∈ F, b.coord i u * (c * b.coord i u) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hc i (hFmem i hi).1]
    _ = ∑ i ∈ F, c * (b.coord i u * b.coord i u) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
    _ = ∑ i ∈ F, c * 1 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hdRo7CFlipAux_sq_eq_one hp3 (b.coord i u) (hFmem i hi).2]
    _ = c * (F.card : ZMod p) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring

private lemma hdRo7CFlipAux_signChange_sub {p : ℕ} (hp3 : p = 3) {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod p) V)
    (F : Finset (Fin (n + 1))) (u : V) :
    hdRo7CFlipAux_signChange b F u - u = hdRo7CFlipAux_proj b F u := by
  have h1 : u - (2 : ZMod p) • hdRo7CFlipAux_proj b F u - u =
      -((2 : ZMod p) • hdRo7CFlipAux_proj b F u) := by abel
  rw [hdRo7CFlipAux_signChange_apply_eq, h1, ← neg_smul]
  rw [show (-2 : ZMod p) = 1 by rw [hp3]; decide, one_smul]

private lemma hdRo7CFlipAux_num_c1 {p : ℕ} (hp3 : p = 3) :
    (2 : ZMod p) - 2 * ((1 : ZMod p) * 5) = 1 := by
  rw [hp3]; decide

private lemma hdRo7CFlipAux_num_cm1 {p : ℕ} (hp3 : p = 3) :
    (2 : ZMod p) - 2 * ((-1 : ZMod p) * 4) = 1 := by
  rw [hp3]; decide

theorem c2_tableFlip_holds : C2TableFlipLeaf := by
  intro hT hS p hpprime hp3 n hn V iV iM b A hSP hStab r u φ hNF c hc hk hcase
  rcases hcase with ⟨hc1, hk5⟩ | ⟨hcm1, hk4⟩
  · obtain ⟨F, hFsub, hFcard⟩ :=
      Finset.exists_subset_card_eq (s := Finset.univ.filter fun i => i ≠ 0 ∧ b.coord i u ≠ 0)
        (n := 5) hk5
    have hFmem : ∀ i ∈ F, i ≠ 0 ∧ b.coord i u ≠ 0 := by
      intro i hi
      exact (Finset.mem_filter.mp (hFsub hi)).2
    have h0notin : (0 : Fin (n + 1)) ∉ F := fun h => (hFmem 0 h).1 rfl
    have hHmem : C2SP p b (hdRo7CFlipAux_signChange b F) :=
      hdRo7CFlipAux_signChange_mem b F h0notin
    have hsq : hdRo7CFlipAux_signChange b F * hdRo7CFlipAux_signChange b F = 1 :=
      hdRo7CFlipAux_signChange_mul_self b F
    have hinv : (hdRo7CFlipAux_signChange b F)⁻¹ = hdRo7CFlipAux_signChange b F :=
      inv_eq_of_mul_eq_one_right hsq
    have hφ1 : φ (hdRo7CFlipAux_signChange b F u) = 1 := by
      rw [hdRo7CFlipAux_signChange_apply_eq, map_sub, map_smul, hNF.hφu, smul_eq_mul,
        hdRo7CFlipAux_phi_proj b F u φ c hc hFmem hp3, hFcard, hc1]
      exact hdRo7CFlipAux_num_c1 hp3
    have hφ2 : φ ((hdRo7CFlipAux_signChange b F)⁻¹ u) = 1 := by rw [hinv]; exact hφ1
    have htrick := hT hS p hp3 n hn V b A hSP hStab r u φ hNF (hdRo7CFlipAux_signChange b F)
      hHmem hφ1 hφ2
    have hsupp : Finset.univ.filter (fun i => b.coord i (hdRo7CFlipAux_signChange b F u - u) ≠ 0)
        = F := by
      rw [hdRo7CFlipAux_signChange_sub hp3 b F u]
      exact hdRo7CFlipAux_supp_proj b F u fun i hi => (hFmem i hi).2
    rw [hsupp] at htrick
    omega
  · obtain ⟨F, hFsub, hFcard⟩ :=
      Finset.exists_subset_card_eq (s := Finset.univ.filter fun i => i ≠ 0 ∧ b.coord i u ≠ 0)
        (n := 4) hk4
    have hFmem : ∀ i ∈ F, i ≠ 0 ∧ b.coord i u ≠ 0 := by
      intro i hi
      exact (Finset.mem_filter.mp (hFsub hi)).2
    have h0notin : (0 : Fin (n + 1)) ∉ F := fun h => (hFmem 0 h).1 rfl
    have hHmem : C2SP p b (hdRo7CFlipAux_signChange b F) :=
      hdRo7CFlipAux_signChange_mem b F h0notin
    have hsq : hdRo7CFlipAux_signChange b F * hdRo7CFlipAux_signChange b F = 1 :=
      hdRo7CFlipAux_signChange_mul_self b F
    have hinv : (hdRo7CFlipAux_signChange b F)⁻¹ = hdRo7CFlipAux_signChange b F :=
      inv_eq_of_mul_eq_one_right hsq
    have hφ1 : φ (hdRo7CFlipAux_signChange b F u) = 1 := by
      rw [hdRo7CFlipAux_signChange_apply_eq, map_sub, map_smul, hNF.hφu, smul_eq_mul,
        hdRo7CFlipAux_phi_proj b F u φ c hc hFmem hp3, hFcard, hcm1]
      exact hdRo7CFlipAux_num_cm1 hp3
    have hφ2 : φ ((hdRo7CFlipAux_signChange b F)⁻¹ u) = 1 := by rw [hinv]; exact hφ1
    have htrick := hT hS p hp3 n hn V b A hSP hStab r u φ hNF (hdRo7CFlipAux_signChange b F)
      hHmem hφ1 hφ2
    have hsupp : Finset.univ.filter (fun i => b.coord i (hdRo7CFlipAux_signChange b F u - u) ≠ 0)
        = F := by
      rw [hdRo7CFlipAux_signChange_sub hp3 b F u]
      exact hdRo7CFlipAux_supp_proj b F u fun i hi => (hFmem i hi).2
    rw [hsupp] at htrick
    omega

end CFSG.StandardType.HdRo7C
