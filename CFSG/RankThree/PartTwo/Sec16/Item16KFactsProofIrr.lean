module

public import CFSG.RankThree.PartTwo.Sec16.KSL3TwoProofIrr

public section

namespace CFSG.RankThree.PartTwo.Sec16

open Matrix
open scoped Pointwise

@[expose] def KSL3TwoIrrPerfect : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (J : Subgroup (GL (Fin 3) K)),
    (∀ W : Submodule K (Fin 3 → K),
      (∀ g ∈ J, ∀ v ∈ W, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤) →
    Group.IsPerfect J → 3 ∣ Nat.card J

namespace KSL3TwoIrrProof

variable {K : Type} [Field K]

@[expose] def IsInv (N : Subgroup (GL (Fin 3) K)) (W : Submodule K (Fin 3 → K)) : Prop :=
  ∀ n ∈ N, ∀ v ∈ W, (n : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W

@[expose] def IsIrr (N : Subgroup (GL (Fin 3) K)) : Prop :=
  ∀ W : Submodule K (Fin 3 → K), IsInv N W → W = ⊥ ∨ W = ⊤

@[expose] def IsScal (N : Subgroup (GL (Fin 3) K)) : Prop :=
  ∀ n ∈ N, ∃ c : K, (n : Matrix (Fin 3) (Fin 3) K) = c • 1

theorem mem_smul_iff {g : GL (Fin 3) K} {W : Submodule K (Fin 3 → K)} {v : Fin 3 → K} :
    v ∈ g • W ↔ ∃ w ∈ W, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ w = v :=
  Submodule.mem_smul_pointwise_iff_exists v g W

theorem finrank_smul (g : GL (Fin 3) K) (W : Submodule K (Fin 3 → K)) :
    Module.finrank K (g • W : Submodule K (Fin 3 → K)) = Module.finrank K W :=
  LinearEquiv.finrank_map_eq (DistribMulAction.toLinearEquiv K (Fin 3 → K) g) W

theorem isInv_smul {N : Subgroup (GL (Fin 3) K)} {W : Submodule K (Fin 3 → K)} (hW : IsInv N W)
    {g : GL (Fin 3) K} (hg : g ∈ Subgroup.normalizer (N : Set (GL (Fin 3) K))) :
    IsInv N (g • W) := by
  intro n hn v hv
  obtain ⟨w, hw, rfl⟩ := mem_smul_iff.mp hv
  have hn' : g⁻¹ * n * g ∈ N := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) n).mp hn
    simpa [mul_assoc] using this
  refine mem_smul_iff.mpr ⟨_, hW _ hn' w hw, ?_⟩
  rw [Units.val_mul, Units.val_mul, mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul, mulVec_mulVec]

theorem isInv_inf {N : Subgroup (GL (Fin 3) K)} {W W' : Submodule K (Fin 3 → K)}
    (hW : IsInv N W) (hW' : IsInv N W') : IsInv N (W ⊓ W') :=
  fun n hn v hv => ⟨hW n hn v hv.1, hW' n hn v hv.2⟩

theorem isInv_of_smul_le {J : Subgroup (GL (Fin 3) K)} {W : Submodule K (Fin 3 → K)}
    (h : ∀ g ∈ J, g • W ≤ W) : IsInv J W :=
  fun g hg v hv => h g hg (mem_smul_iff.mpr ⟨v, hv, rfl⟩)

theorem not_isScal_of_isIrr {N : Subgroup (GL (Fin 3) K)} (hN : IsIrr N) : ¬ IsScal N := by
  intro hS
  set W := K ∙ (Pi.single 0 1 : Fin 3 → K) with hWdef
  have hinv : IsInv N W := by
    intro n hn v hv
    obtain ⟨c, hc⟩ := hS n hn
    rw [hc, smul_mulVec, one_mulVec]
    exact W.smul_mem c hv
  have hne : (Pi.single 0 1 : Fin 3 → K) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  rcases hN W hinv with h | h
  · have : (Pi.single 0 1 : Fin 3 → K) ∈ W := Submodule.mem_span_singleton_self _
    rw [h, Submodule.mem_bot] at this
    exact hne this
  · have h1 : Module.finrank K W = 1 := finrank_span_singleton hne
    rw [h, finrank_top, Module.finrank_fin_fun] at h1
    norm_num at h1

theorem eq_smul_of_forall {m : Matrix (Fin 3) (Fin 3) K} {c : K}
    (h : ∀ v : Fin 3 → K, m *ᵥ v = c • v) : m = c • 1 := by
  apply (Matrix.toLin' (R := K)).injective
  ext v i
  simp [h]

@[expose] def IsEig (N : Subgroup (GL (Fin 3) K)) (w : Fin 3 → K) : Prop :=
  ∀ n ∈ N, ∃ c : K, (n : Matrix (Fin 3) (Fin 3) K) *ᵥ w = c • w

@[expose] def wt (N : Subgroup (GL (Fin 3) K)) (w : Fin 3 → K) : Submodule K (Fin 3 → K) where
  carrier := {u | ∀ n ∈ N, ∀ c : K, (n : Matrix (Fin 3) (Fin 3) K) *ᵥ w = c • w →
    (n : Matrix (Fin 3) (Fin 3) K) *ᵥ u = c • u}
  add_mem' {u u'} hu hu' n hn c hc := by
    rw [mulVec_add, hu n hn c hc, hu' n hn c hc, smul_add]
  zero_mem' n _ c _ := by rw [mulVec_zero, smul_zero]
  smul_mem' a u hu n hn c hc := by
    rw [mulVec_smul, hu n hn c hc, smul_comm]

variable {N : Subgroup (GL (Fin 3) K)}

theorem mem_wt_self (w : Fin 3 → K) : w ∈ wt N w := fun _ _ _ hc => hc

theorem wt_eq_of_mem {w u : Fin 3 → K} (hw : IsEig N w) (hu : u ∈ wt N w) (hu0 : u ≠ 0) :
    wt N u = wt N w := by
  ext v
  constructor
  · intro hv n hn c hc
    exact hv n hn c (hu n hn c hc)
  · intro hv n hn c hc
    obtain ⟨c', hc'⟩ := hw n hn
    have h1 := hu n hn c' hc'
    rw [hc, ← sub_eq_zero, ← sub_smul, smul_eq_zero] at h1
    rcases h1 with h1 | h1
    · rw [sub_eq_zero] at h1
      rw [h1]
      exact hv n hn c' hc'
    · exact absurd h1 hu0

theorem smul_wt_le {g : GL (Fin 3) K} (hg : g ∈ Subgroup.normalizer (N : Set (GL (Fin 3) K)))
    (w : Fin 3 → K) : g • wt N w ≤ wt N ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ w) := by
  intro v hv
  obtain ⟨u, hu, rfl⟩ := mem_smul_iff.mp hv
  intro n hn c hc
  have hn' : g⁻¹ * n * g ∈ N := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) n).mp hn
    simpa [mul_assoc] using this
  have hgg : ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K) =
      1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hgg' : (g : Matrix (Fin 3) (Fin 3) K) * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h1 : ((g⁻¹ * n * g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w = c • w := by
    rw [Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, hc, mulVec_smul,
      mulVec_mulVec, hgg, one_mulVec]
  have h2 := hu _ hn' c h1
  rw [Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec] at h2
  have h3 := congrArg (fun z => (g : Matrix (Fin 3) (Fin 3) K) *ᵥ z) h2
  simp only [mulVec_mulVec, mulVec_smul] at h3
  rw [← Matrix.mul_assoc, hgg', Matrix.one_mul, ← mulVec_mulVec] at h3
  exact h3

theorem smul_wt {g : GL (Fin 3) K} (hg : g ∈ Subgroup.normalizer (N : Set (GL (Fin 3) K)))
    (w : Fin 3 → K) : g • wt N w = wt N ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ w) := by
  refine le_antisymm (smul_wt_le hg w) ?_
  intro v hv
  have h1 := smul_wt_le (inv_mem hg) ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ w)
  have hgg : ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K) =
      1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [mulVec_mulVec, hgg, one_mulVec] at h1
  have h2 : ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ wt N w :=
    h1 (mem_smul_iff.mpr ⟨v, hv, rfl⟩)
  refine mem_smul_iff.mpr ⟨_, h2, ?_⟩
  rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

theorem isEig_smul {g : GL (Fin 3) K} (hg : g ∈ Subgroup.normalizer (N : Set (GL (Fin 3) K)))
    {w : Fin 3 → K} (hw : IsEig N w) : IsEig N ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ w) := by
  intro n hn
  have hn' : g⁻¹ * n * g ∈ N := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) n).mp hn
    simpa [mul_assoc] using this
  obtain ⟨c, hc⟩ := hw _ hn'
  refine ⟨c, ?_⟩
  have hgg' : (g : Matrix (Fin 3) (Fin 3) K) * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec] at hc
  have h3 := congrArg (fun z => (g : Matrix (Fin 3) (Fin 3) K) *ᵥ z) hc
  simp only [mulVec_mulVec, mulVec_smul] at h3
  rw [← Matrix.mul_assoc, hgg', Matrix.one_mul, ← mulVec_mulVec] at h3
  exact h3

theorem isScal_of_wt_eq_top {w : Fin 3 → K} (hw : IsEig N w) (htop : wt N w = ⊤) : IsScal N := by
  intro n hn
  obtain ⟨c, hc⟩ := hw n hn
  refine ⟨c, eq_smul_of_forall fun v => ?_⟩
  have hv : v ∈ wt N w := htop ▸ Submodule.mem_top
  exact hv n hn c hc

theorem exists_mem_wt {m : ℕ} {x : Fin m → Fin 3 → K} (hli : LinearIndependent K x)
    (hx : ∀ i, IsEig N (x i)) {y : Fin 3 → K} (hy0 : y ≠ 0) {a : Fin m → K}
    (hya : ∑ i, a i • x i = y) : ∃ i, a i ≠ 0 ∧ x i ∈ wt N y := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hy0
    rw [← hya]
    simp [hcon]
  refine ⟨i, hi, fun n hn c hc => ?_⟩
  choose d hd using fun j => hx j n hn
  have hsum : ∑ j, (a j * d j - a j * c) • x j = 0 := by
    have e1 : (n : Matrix (Fin 3) (Fin 3) K) *ᵥ y = ∑ j, (a j * d j) • x j := by
      rw [← hya, mulVec_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mulVec_smul, hd j, smul_smul]
    have e2 : c • y = ∑ j, (a j * c) • x j := by
      rw [← hya, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul, mul_comm]
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [← e1, ← e2, hc, sub_self]
  have h1 := (Fintype.linearIndependent_iff.mp hli) _ hsum i
  have h2 : d i = c := by
    have : a i * (d i - c) = 0 := by rw [mul_sub]; exact h1
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hi
    · exact sub_eq_zero.mp h
  rw [hd i, h2]

theorem false_of_four {x : Fin 4 → Fin 3 → K} (hx : ∀ i, IsEig N (x i)) (h0 : ∀ i, x i ≠ 0)
    (hd : ∀ i j, i ≠ j → x i ∉ wt N (x j)) : False := by
  classical
  have step : ∀ {m : ℕ} (v : Fin m → Fin 3 → K), LinearIndependent K v →
      (∀ i, ∃ j : Fin 4, v i = x j) → ∀ k : Fin 4, (∀ i j, v i = x j → j ≠ k) →
        x k ∉ Submodule.span K (Set.range v) := by
    intro m v hv hvx k hk hmem
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hmem
    have hvE : ∀ i, IsEig N (v i) := fun i => by
      obtain ⟨j, hj⟩ := hvx i
      rw [hj]
      exact hx j
    obtain ⟨i, -, hi⟩ := exists_mem_wt hv hvE (h0 k) ha
    obtain ⟨j, hj⟩ := hvx i
    rw [hj] at hi
    exact hd j k (hk i j hj) hi
  have h2 : LinearIndependent K ![x 2] := by
    rw [linearIndependent_unique_iff]
    exact h0 2
  have h12 : LinearIndependent K ![x 1, x 2] := by
    refine linearIndependent_finCons.mpr ⟨h2, step ![x 2] h2 (fun i => ⟨2, by
      fin_cases i; rfl⟩) 1 (fun i j hij => ?_)⟩
    fin_cases i
    simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_fin_one] at hij
    intro hj
    subst hj
    exact hd 1 2 (by decide) (by rw [hij]; exact mem_wt_self _)
  have h012 : LinearIndependent K ![x 0, x 1, x 2] := by
    refine linearIndependent_finCons.mpr ⟨h12, step ![x 1, x 2] h12 (fun i => by
      fin_cases i
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩) 0 (fun i j hij => ?_)⟩
    intro hj
    subst hj
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero] at hij
      exact hd 0 1 (by decide) (by rw [hij]; exact mem_wt_self _)
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hij
      exact hd 0 2 (by decide) (by rw [hij]; exact mem_wt_self _)
  have htop : Submodule.span K (Set.range ![x 0, x 1, x 2]) = ⊤ :=
    h012.span_eq_top_of_card_eq_finrank (by simp)
  refine step ![x 0, x 1, x 2] h012 (fun i => by
    fin_cases i
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩) 3 (fun i j hij => ?_) (htop ▸ Submodule.mem_top)
  intro hj
  subst hj
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero] at hij
    exact hd 0 3 (by decide) (by rw [hij]; exact mem_wt_self _)
  · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero] at hij
    exact hd 1 3 (by decide) (by rw [hij]; exact mem_wt_self _)
  · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons] at hij
    exact hd 2 3 (by decide) (by rw [hij]; exact mem_wt_self _)

theorem isEig_of_line {L : Submodule K (Fin 3 → K)} (hL : IsInv N L)
    (h1 : Module.finrank K L = 1) {w : Fin 3 → K} (hwL : w ∈ L) (hw0 : w ≠ 0) : IsEig N w := by
  intro n hn
  have hnw : (n : Matrix (Fin 3) (Fin 3) K) *ᵥ w ∈ L := hL n hn w hwL
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨w, hwL⟩ : L)
    (fun h => hw0 (congrArg Subtype.val h))).mp h1 ⟨_, hnw⟩
  exact ⟨c, (congrArg Subtype.val hc).symm⟩

theorem exists_isEig [Finite K] {J : Subgroup (GL (Fin 3) K)} (hJ : IsIrr J)
    (hJN : J ≤ Subgroup.normalizer (N : Set (GL (Fin 3) K))) {W : Submodule K (Fin 3 → K)}
    (hW : IsInv N W) (hW0 : W ≠ ⊥) (hWt : W ≠ ⊤) : ∃ w : Fin 3 → K, w ≠ 0 ∧ IsEig N w := by
  classical
  have hline : ∀ L : Submodule K (Fin 3 → K), IsInv N L → Module.finrank K L = 1 →
      ∃ w : Fin 3 → K, w ≠ 0 ∧ IsEig N w := by
    intro L hL h1
    have hL0 : L ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at h1
      norm_num at h1
    obtain ⟨w, hwL, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hL0
    exact ⟨w, hw0, isEig_of_line hL h1 hwL hw0⟩
  have hd1 : 1 ≤ Module.finrank K W := Submodule.one_le_finrank_iff.mpr hW0
  have hd2 : Module.finrank K W < 3 := by
    have := Submodule.finrank_lt hWt
    rwa [Module.finrank_fin_fun] at this
  by_cases h1 : Module.finrank K W = 1
  · exact hline W hW h1
  have h2 : Module.finrank K W = 2 := by omega
  obtain ⟨g, hg, hgW⟩ : ∃ g ∈ J, ¬ g • W ≤ W := by
    by_contra hcon
    push Not at hcon
    rcases hJ W (isInv_of_smul_le hcon) with h | h
    · exact hW0 h
    · exact hWt h
  have hgWinv : IsInv N (g • W) := isInv_smul hW (hJN hg)
  have hgW2 : Module.finrank K (g • W : Submodule K (Fin 3 → K)) = 2 := by
    rw [finrank_smul, h2]
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq W (g • W)
  have hsup : Module.finrank K (W ⊔ g • W : Submodule K (Fin 3 → K)) ≤ 3 := by
    have := Submodule.finrank_le (W ⊔ g • W)
    rwa [Module.finrank_fin_fun] at this
  have hinf2 : Module.finrank K (W ⊓ g • W : Submodule K (Fin 3 → K)) ≤ 2 := by
    have := Submodule.finrank_mono (inf_le_left : W ⊓ g • W ≤ W)
    omega
  by_cases hi : Module.finrank K (W ⊓ g • W : Submodule K (Fin 3 → K)) = 2
  · exfalso
    have e1 : W ⊓ g • W = W := Submodule.eq_of_le_of_finrank_eq inf_le_left (by rw [hi, h2])
    have e2 : W ⊓ g • W = g • W :=
      Submodule.eq_of_le_of_finrank_eq inf_le_right (by rw [hi, hgW2])
    exact hgW (by rw [← e2, e1])
  · exact hline _ (isInv_inf hW hgWinv) (by omega)

theorem wt_eq_or_disjoint {u u' : Fin 3 → K} (hu : IsEig N u) (hu' : IsEig N u') :
    wt N u = wt N u' ∨ wt N u ⊓ wt N u' = ⊥ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hne, hmeet⟩ := hcon
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hmeet
  exact hne ((wt_eq_of_mem hu hv.1 hv0).symm.trans (wt_eq_of_mem hu' hv.2 hv0))

theorem dichotomy [Finite K] {J : Subgroup (GL (Fin 3) K)} (hJ : IsIrr J)
    (hJ3 : ¬ 3 ∣ Nat.card J) (hJN : J ≤ Subgroup.normalizer (N : Set (GL (Fin 3) K))) :
    IsScal N ∨ IsIrr N := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hNs, hNi⟩ := hcon
  obtain ⟨W, hW, hW0, hWt⟩ : ∃ W, IsInv N W ∧ W ≠ ⊥ ∧ W ≠ ⊤ := by
    by_contra h
    push Not at h
    exact hNi fun W hW => by
      by_cases hW0 : W = ⊥
      · exact Or.inl hW0
      · exact Or.inr (h W hW hW0)
  obtain ⟨w, hw0, hw⟩ := exists_isEig hJ hJN hW hW0 hWt
  set U := wt N w with hU
  have hU0 : U ≠ ⊥ := fun h => hw0 (by
    have := mem_wt_self (N := N) w
    rw [← hU, h, Submodule.mem_bot] at this
    exact this)
  have hUt : U ≠ ⊤ := fun h => hNs (isScal_of_wt_eq_top hw h)
  have hsmulU : ∀ g ∈ J, g • U = wt N ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ w) :=
    fun g hg => smul_wt (hJN hg) w
  have hgw : ∀ g ∈ J, IsEig N ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ w) :=
    fun g hg => isEig_smul (hJN hg) hw
  have hgw0 : ∀ g : GL (Fin 3) K, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ w ≠ 0 := by
    intro g h
    apply hw0
    have := congrArg (fun z => ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ z) h
    simpa [mulVec_mulVec, ← Units.val_mul] using this
  obtain ⟨g, hg, hgU⟩ : ∃ g ∈ J, ¬ g • U ≤ U := by
    by_contra hcon
    push Not at hcon
    rcases hJ U (isInv_of_smul_le hcon) with h | h
    · exact hU0 h
    · exact hUt h
  have hgUne : g • U ≠ U := fun h => hgU h.le
  have hdisj : ∀ a ∈ J, ∀ b ∈ J, a • U ≠ b • U → a • U ⊓ b • U = ⊥ := by
    intro a ha b hb hab
    rw [hsmulU a ha, hsmulU b hb] at hab ⊢
    exact (wt_eq_or_disjoint (hgw a ha) (hgw b hb)).resolve_left hab
  have hUd1 : 1 ≤ Module.finrank K U := Submodule.one_le_finrank_iff.mpr hU0
  have hUd2 : Module.finrank K U < 3 := by
    have := Submodule.finrank_lt hUt
    rwa [Module.finrank_fin_fun] at this
  have hfin3 : ∀ S : Submodule K (Fin 3 → K), Module.finrank K S ≤ 3 := fun S => by
    have := Submodule.finrank_le S
    rwa [Module.finrank_fin_fun] at this
  have h1J : (1 : GL (Fin 3) K) ∈ J := J.one_mem
  have hone : (1 : GL (Fin 3) K) • U = U := one_smul _ U
  by_cases h2 : Module.finrank K U = 2
  ·
    have h0 := hdisj g hg 1 h1J (by rw [hone]; exact hgUne)
    rw [hone] at h0
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq (g • U) U
    rw [h0, finrank_bot, finrank_smul, h2] at hsum
    have := hfin3 (g • U ⊔ U)
    omega
  have h1 : Module.finrank K U = 1 := by omega
  obtain ⟨h, hh, hhU, hhg⟩ : ∃ h ∈ J, h • U ≠ U ∧ h • U ≠ g • U := by
    by_contra hcon
    push Not at hcon
    set S := U ⊔ g • U with hS
    have hSinv : IsInv J S := by
      intro k hk v hv
      obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.mp hv
      rw [mulVec_add]
      have hk1 : (k : Matrix (Fin 3) (Fin 3) K) *ᵥ u₁ ∈ S := by
        have hmem : (k : Matrix (Fin 3) (Fin 3) K) *ᵥ u₁ ∈ k • U :=
          mem_smul_iff.mpr ⟨u₁, hu₁, rfl⟩
        by_cases hkU : k • U = U
        · rw [hkU] at hmem
          exact Submodule.mem_sup_left hmem
        · rw [hcon k hk hkU] at hmem
          exact Submodule.mem_sup_right hmem
      have hk2 : (k : Matrix (Fin 3) (Fin 3) K) *ᵥ u₂ ∈ S := by
        obtain ⟨u, hu, rfl⟩ := mem_smul_iff.mp hu₂
        have hmem : (k : Matrix (Fin 3) (Fin 3) K) *ᵥ ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ u) ∈
            (k * g) • U := by
          refine mem_smul_iff.mpr ⟨u, hu, ?_⟩
          rw [Units.val_mul, mulVec_mulVec]
        have hkg : k * g ∈ J := mul_mem hk hg
        by_cases hkU : (k * g) • U = U
        · rw [hkU] at hmem
          exact Submodule.mem_sup_left hmem
        · rw [hcon (k * g) hkg hkU] at hmem
          exact Submodule.mem_sup_right hmem
      exact S.add_mem hk1 hk2
    rcases hJ S hSinv with hS0 | hSt
    · exact hU0 (le_bot_iff.mp (hS0 ▸ le_sup_left))
    · have := Submodule.finrank_add_le_finrank_add_finrank U (g • U)
      rw [← hS, hSt, finrank_top, Module.finrank_fin_fun, finrank_smul, h1] at this
      omega
  have hall : ∀ k ∈ J, k • U = U ∨ k • U = g • U ∨ k • U = h • U := by
    intro k hk
    by_contra hcon
    push Not at hcon
    obtain ⟨hk1, hk2, hk3⟩ := hcon
    set x : Fin 4 → Fin 3 → K := ![w, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ w,
      (h : Matrix (Fin 3) (Fin 3) K) *ᵥ w, (k : Matrix (Fin 3) (Fin 3) K) *ᵥ w] with hx
    set a : Fin 4 → GL (Fin 3) K := ![1, g, h, k] with ha
    have hxa : ∀ i, x i = (a i : Matrix (Fin 3) (Fin 3) K) *ᵥ w := by
      intro i
      fin_cases i <;> simp [hx, ha]
    have haJ : ∀ i, a i ∈ J := by
      intro i
      fin_cases i
      · exact h1J
      · exact hg
      · exact hh
      · exact hk
    have hval : ∀ i, a i • U = ![U, g • U, h • U, k • U] i := by
      intro i
      fin_cases i
      · exact hone
      · rfl
      · rfl
      · rfl
    have hlines : ∀ i j, i ≠ j → a i • U ≠ a j • U := by
      intro i j hij
      rw [hval i, hval j]
      fin_cases i <;> fin_cases j <;>
        first
        | exact absurd rfl hij
        | exact hgUne.symm | exact hgUne | exact hhU.symm | exact hhU | exact hhg.symm
        | exact hhg | exact hk1.symm | exact hk1 | exact hk2.symm | exact hk2 | exact hk3.symm
        | exact hk3
    refine false_of_four (x := x) (N := N) (fun i => ?_) (fun i => ?_) (fun i j hij hmem => ?_)
    · rw [hxa i]
      exact hgw _ (haJ i)
    · rw [hxa i]
      exact hgw0 _
    · rw [hxa i, hxa j] at hmem
      have e := wt_eq_of_mem (hgw _ (haJ j)) hmem (hgw0 _)
      rw [← hsmulU _ (haJ i), ← hsmulU _ (haJ j)] at e
      exact hlines i j hij e
  have horbit : MulAction.orbit J U = {U, g • U, h • U} := by
    ext W
    constructor
    · rintro ⟨k, rfl⟩
      change (k : GL (Fin 3) K) • U ∈ ({U, g • U, h • U} : Set (Submodule K (Fin 3 → K)))
      rcases hall k k.2 with e | e | e
      · rw [e]; exact Or.inl rfl
      · rw [e]; exact Or.inr (Or.inl rfl)
      · rw [e]; exact Or.inr (Or.inr rfl)
    · rintro (rfl | rfl | rfl)
      · exact ⟨1, one_smul _ U⟩
      · exact ⟨⟨g, hg⟩, rfl⟩
      · exact ⟨⟨h, hh⟩, rfl⟩
  have hcard : (MulAction.orbit J U).ncard = 3 := by
    rw [horbit, Set.ncard_insert_of_notMem, Set.ncard_pair hhg.symm]
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨fun e => hgUne e.symm, fun e => hhU e.symm⟩
  have hidx := MulAction.index_stabilizer J U
  rw [hcard] at hidx
  have hdvd : (MulAction.stabilizer J U).index ∣ Nat.card J := Subgroup.index_dvd_card _
  rw [hidx] at hdvd
  exact hJ3 hdvd

theorem pow_three_of_commutator {x y : GL (Fin 3) K} {ζ : K}
    (h : ((x * y * x⁻¹ * y⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = ζ • 1) :
    ζ ^ 3 = 1 := by
  have h1 : ((x * y * x⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ζ • (y : Matrix (Fin 3) (Fin 3) K) := by
    have e : x * y * x⁻¹ = (x * y * x⁻¹ * y⁻¹) * y := by group
    rw [e, Units.val_mul, h, smul_mul_assoc, Matrix.one_mul]
  have h2 := congrArg Matrix.det h1
  rw [Units.val_mul, Units.val_mul, Matrix.det_units_conj, det_smul, Fintype.card_fin] at h2
  have hy : (y : Matrix (Fin 3) (Fin 3) K).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp y.isUnit).ne_zero
  have : ζ ^ 3 * (y : Matrix (Fin 3) (Fin 3) K).det = 1 * (y : Matrix (Fin 3) (Fin 3) K).det := by
    rw [one_mul, ← h2]
  exact mul_right_cancel₀ hy this

theorem commute_of_scalar_commutator [Finite K] {J : Subgroup (GL (Fin 3) K)}
    (hJ3 : ¬ 3 ∣ Nat.card J) {x y : GL (Fin 3) K} (hx : x ∈ J) (hy : y ∈ J) {ζ : K}
    (h : ((x * y * x⁻¹ * y⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = ζ • 1) :
    x * y = y * x := by
  have hζ := pow_three_of_commutator h
  set c := x * y * x⁻¹ * y⁻¹ with hc
  have hcJ : c ∈ J := mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  have hc3 : c ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, h, smul_pow, one_pow, hζ, one_smul, Units.val_one]
  have h1 : orderOf (⟨c, hcJ⟩ : J) ∣ 3 := by
    apply orderOf_dvd_of_pow_eq_one
    exact Subtype.ext (by simpa using hc3)
  have h2 : orderOf (⟨c, hcJ⟩ : J) ∣ Nat.card J := orderOf_dvd_natCard _
  have hcop : Nat.Coprime 3 (Nat.card J) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hJ3
  have h3 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  rw [orderOf_eq_one_iff] at h3
  have hc1 : c = 1 := congrArg Subtype.val h3
  calc x * y = c * (y * x) := by rw [hc]; group
    _ = y * x := by rw [hc1, one_mul]

@[expose] def conjAlg (g : GL (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K ≃ₐ[K] Matrix (Fin 3) (Fin 3) K where
  toFun x := (g : Matrix (Fin 3) (Fin 3) K) * x * ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  invFun x := ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * x * (g : Matrix (Fin 3) (Fin 3) K)
  left_inv x := by
    simp only [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
  right_inv x := by
    simp only [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
    rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  map_mul' x y := by
    simp only [Matrix.mul_assoc]
    congr 2
    rw [← Matrix.mul_assoc _ (g : Matrix (Fin 3) (Fin 3) K), ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.one_mul]
  map_add' x y := by rw [Matrix.mul_add, Matrix.add_mul]
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      ← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem conjAlg_apply (g : GL (Fin 3) K) (x : Matrix (Fin 3) (Fin 3) K) :
    conjAlg g x = (g : Matrix (Fin 3) (Fin 3) K) * x *
      ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := rfl

open scoped IsMulCommutative in
theorem isMulCommutative_of_abelian [Finite K] {J : Subgroup (GL (Fin 3) K)}
    (hJ3 : ¬ 3 ∣ Nat.card J) (hJN : J ≤ Subgroup.normalizer (N : Set (GL (Fin 3) K)))
    (hNab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) (hNi : IsIrr N) :
    ∀ a ∈ J, ∀ b ∈ J, a * b = b * a := by
  classical
  set S : Set (Matrix (Fin 3) (Fin 3) K) :=
    {m | ∃ n ∈ N, (n : Matrix (Fin 3) (Fin 3) K) = m} with hS
  set L : Subalgebra K (Matrix (Fin 3) (Fin 3) K) := Algebra.adjoin K S with hL
  have hScomm : S.Pairwise Commute := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ -
    exact congrArg Units.val (hNab a ha b hb)
  have : IsMulCommutative L := Algebra.isMulCommutative_adjoin K hScomm
  have hNL : ∀ n ∈ N, (n : Matrix (Fin 3) (Fin 3) K) ∈ L :=
    fun n hn => Algebra.subset_adjoin ⟨n, hn, rfl⟩
  have hLN : ∀ x ∈ L, ∀ n ∈ N,
      (n : Matrix (Fin 3) (Fin 3) K) * x = x * (n : Matrix (Fin 3) (Fin 3) K) := by
    intro x hx n hn
    have := Algebra.commute_of_mem_adjoin_of_forall_mem_commute (a := (n : Matrix _ _ K)) hx
      (fun b hb => by
        obtain ⟨m, hm, rfl⟩ := hb
        exact congrArg Units.val (hNab n hn m hm))
    exact this.eq
  have hinj : ∀ x ∈ L, x ≠ 0 → ∀ v : Fin 3 → K, x *ᵥ v = 0 → v = 0 := by
    intro x hx hx0 v hv
    set W := LinearMap.ker (Matrix.mulVecLin x) with hW
    have hWinv : IsInv N W := by
      intro n hn u hu
      have hu' : x *ᵥ u = 0 := hu
      change x *ᵥ ((n : Matrix (Fin 3) (Fin 3) K) *ᵥ u) = 0
      rw [mulVec_mulVec, ← hLN x hx n hn, ← mulVec_mulVec, hu', mulVec_zero]
    rcases hNi W hWinv with h | h
    · have : v ∈ W := hv
      rw [h, Submodule.mem_bot] at this
      exact this
    · exfalso
      apply hx0
      apply (Matrix.toLin' (R := K)).injective
      refine LinearMap.ext fun u => ?_
      have hu : u ∈ W := h ▸ Submodule.mem_top
      have hu' : x *ᵥ u = 0 := hu
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hu', zero_mulVec]
  have hdom : IsDomain L := by
    have : NoZeroDivisors L := ⟨fun {a b} hab => by
      by_contra hcon
      push Not at hcon
      obtain ⟨ha, hb⟩ := hcon
      have ha' : (a : Matrix (Fin 3) (Fin 3) K) ≠ 0 := fun h => ha (Subtype.ext h)
      have hb' : (b : Matrix (Fin 3) (Fin 3) K) ≠ 0 := fun h => hb (Subtype.ext h)
      apply hb'
      apply (Matrix.toLin' (R := K)).injective
      refine LinearMap.ext fun u => ?_
      have h1 : (a : Matrix (Fin 3) (Fin 3) K) *ᵥ ((b : Matrix (Fin 3) (Fin 3) K) *ᵥ u) = 0 := by
        rw [mulVec_mulVec]
        have := congrArg Subtype.val hab
        simp only [Subalgebra.coe_mul, Subalgebra.coe_zero] at this
        rw [this, zero_mulVec]
      have h2 := hinj _ a.2 ha' _ h1
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h2, zero_mulVec]⟩
    exact NoZeroDivisors.to_isDomain L
  have : Fintype L := Fintype.ofFinite L
  let : Field L := Fintype.fieldOfDomain L
  set v₀ : Fin 3 → K := Pi.single 0 1 with hv₀
  have hv₀0 : v₀ ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [hv₀] at this
  set ev : L →ₗ[K] (Fin 3 → K) :=
    { toFun := fun x => (x : Matrix (Fin 3) (Fin 3) K) *ᵥ v₀
      map_add' := fun x y => by simp [add_mulVec]
      map_smul' := fun c x => by simp [smul_mulVec] } with hev
  have hev_inj : Function.Injective ev := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    rw [Submodule.mem_bot]
    by_contra hx0
    exact hv₀0 (hinj _ x.2 (fun h => hx0 (Subtype.ext h)) _ hx)
  have hev_surj : Function.Surjective ev := by
    rw [← LinearMap.range_eq_top]
    have hinv : IsInv N (LinearMap.range ev) := by
      rintro n hn _ ⟨x, rfl⟩
      refine ⟨⟨(n : Matrix (Fin 3) (Fin 3) K) * (x : Matrix (Fin 3) (Fin 3) K),
        L.mul_mem (hNL n hn) x.2⟩, ?_⟩
      change ((n : Matrix (Fin 3) (Fin 3) K) * (x : Matrix (Fin 3) (Fin 3) K)) *ᵥ v₀ = _
      rw [← mulVec_mulVec]
      rfl
    rcases hNi _ hinv with h | h
    · exfalso
      have : ev 1 ∈ LinearMap.range ev := ⟨1, rfl⟩
      rw [h, Submodule.mem_bot] at this
      apply hv₀0
      simpa [hev] using this
    · exact h
  have hdim : Module.finrank K L = 3 := by
    rw [LinearEquiv.finrank_eq (LinearEquiv.ofBijective ev ⟨hev_inj, hev_surj⟩),
      Module.finrank_fin_fun]
  have hmapS : ∀ g ∈ J, conjAlg g '' S = S := by
    intro g hg
    ext m
    constructor
    · rintro ⟨_, ⟨n, hn, rfl⟩, rfl⟩
      refine ⟨g * n * g⁻¹, (Subgroup.mem_normalizer_iff.mp (hJN hg) n).mp hn, ?_⟩
      rw [conjAlg_apply, Units.val_mul, Units.val_mul]
    · rintro ⟨n, hn, rfl⟩
      have hn' : g⁻¹ * n * g ∈ N := by
        have := (Subgroup.mem_normalizer_iff.mp (inv_mem (hJN hg)) n).mp hn
        simpa [mul_assoc] using this
      refine ⟨_, ⟨_, hn', rfl⟩, ?_⟩
      rw [conjAlg_apply, ← Units.val_mul, ← Units.val_mul]
      congr 1
      group
  have hmapL : ∀ g ∈ J, L.map (conjAlg g : Matrix (Fin 3) (Fin 3) K →ₐ[K] _) = L := by
    intro g hg
    rw [hL, AlgHom.map_adjoin]
    congr 1
    exact hmapS g hg
  have hfix : ∀ g ∈ J, ∀ x ∈ L, conjAlg g x = x := by
    intro g hg
    set σ : L ≃ₐ[K] L := ((conjAlg g).subalgebraMap L).trans
      (Subalgebra.equivOfEq _ _ (hmapL g hg)) with hσ
    have hσx : ∀ x : L, ((σ x : L) : Matrix (Fin 3) (Fin 3) K) = conjAlg g x := fun x => rfl
    have hσk : ∀ k : ℕ, ∀ x : L, (((σ ^ k) x : L) : Matrix (Fin 3) (Fin 3) K) =
        conjAlg (g ^ k) x := by
      intro k
      induction k with
      | zero => intro x; simp [conjAlg_apply]
      | succ k ih =>
        intro x
        rw [pow_succ', AlgEquiv.mul_apply, hσx, ih, conjAlg_apply, conjAlg_apply, conjAlg_apply,
          pow_succ', Units.val_mul, _root_.mul_inv_rev, Units.val_mul]
        simp only [Matrix.mul_assoc]
    have hord : σ ^ orderOf g = 1 := by
      ext x
      rw [hσk, pow_orderOf_eq_one, conjAlg_apply]
      simp
    have h3 : ¬ 3 ∣ orderOf g := by
      intro h
      apply hJ3
      refine h.trans ?_
      rw [show orderOf g = orderOf (⟨g, hg⟩ : J) from (Subgroup.orderOf_mk g hg).symm]
      exact orderOf_dvd_natCard _
    have hcard := IsGalois.card_aut_eq_finrank K L
    have h1 : orderOf σ ∣ 3 := by
      have := orderOf_dvd_natCard σ
      rwa [hcard, hdim] at this
    have h2 : orderOf σ ∣ orderOf g := orderOf_dvd_of_pow_eq_one hord
    have hcop : Nat.Coprime 3 (orderOf g) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
    have hσ1 : σ = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
    intro x hx
    have := hσx ⟨x, hx⟩
    rw [hσ1] at this
    exact this.symm
  have hact : ∀ g ∈ J, ∃ x ∈ L, (g : Matrix (Fin 3) (Fin 3) K) = x := by
    intro g hg
    obtain ⟨x, hx⟩ := hev_surj ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ v₀)
    refine ⟨x, x.2, ?_⟩
    apply (Matrix.toLin' (R := K)).injective
    refine LinearMap.ext fun u => ?_
    obtain ⟨y, rfl⟩ := hev_surj u
    have hgy : (g : Matrix (Fin 3) (Fin 3) K) * (y : Matrix (Fin 3) (Fin 3) K) =
        (y : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K) := by
      have := hfix g hg y y.2
      rw [conjAlg_apply] at this
      calc (g : Matrix (Fin 3) (Fin 3) K) * (y : Matrix (Fin 3) (Fin 3) K) =
          (g : Matrix (Fin 3) (Fin 3) K) * (y : Matrix (Fin 3) (Fin 3) K) *
            ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
            (g : Matrix (Fin 3) (Fin 3) K) := by
            rw [Matrix.mul_assoc _ ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K),
              ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
        _ = (y : Matrix (Fin 3) (Fin 3) K) * (g : Matrix (Fin 3) (Fin 3) K) := by rw [this]
    have hxy : (x : Matrix (Fin 3) (Fin 3) K) * (y : Matrix (Fin 3) (Fin 3) K) =
        (y : Matrix (Fin 3) (Fin 3) K) * (x : Matrix (Fin 3) (Fin 3) K) := by
      have := isMulCommutative_iff.mp (inferInstance : IsMulCommutative L) x y
      exact congrArg Subtype.val this
    have e1 : ev y = (y : Matrix (Fin 3) (Fin 3) K) *ᵥ v₀ := rfl
    have e2 : ev x = (x : Matrix (Fin 3) (Fin 3) K) *ᵥ v₀ := rfl
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, e1]
    calc (g : Matrix (Fin 3) (Fin 3) K) *ᵥ ((y : Matrix (Fin 3) (Fin 3) K) *ᵥ v₀) =
        (y : Matrix (Fin 3) (Fin 3) K) *ᵥ ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ v₀) := by
          rw [mulVec_mulVec, hgy, ← mulVec_mulVec]
      _ = (y : Matrix (Fin 3) (Fin 3) K) *ᵥ ((x : Matrix (Fin 3) (Fin 3) K) *ᵥ v₀) := by
          rw [← e2, hx]
      _ = (x : Matrix (Fin 3) (Fin 3) K) *ᵥ ((y : Matrix (Fin 3) (Fin 3) K) *ᵥ v₀) := by
          rw [mulVec_mulVec, mulVec_mulVec, hxy]
  intro a ha b hb
  obtain ⟨x, hx, hax⟩ := hact a ha
  obtain ⟨y, hy, hby⟩ := hact b hb
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hax, hby]
  have := isMulCommutative_iff.mp (inferInstance : IsMulCommutative L) ⟨x, hx⟩ ⟨y, hy⟩
  exact congrArg Subtype.val this

omit [Field K] in
theorem mem_normalizer_commutator {X : Type*} [Group X] {M : Subgroup X} {g : X}
    (hg : g ∈ Subgroup.normalizer (M : Set X)) :
    g ∈ Subgroup.normalizer ((⁅M, M⁆ : Subgroup X) : Set X) := by
  have hmap : ∀ {h : X}, h ∈ Subgroup.normalizer (M : Set X) →
      M.map (MulAut.conj h).toMonoidHom = M := by
    intro h hh
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hh y).mp hy
    · intro hx
      refine ⟨h⁻¹ * x * h, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hh) x).mp hx
      simpa [mul_assoc] using this
  have hc : ∀ {h : X}, h ∈ Subgroup.normalizer (M : Set X) →
      (⁅M, M⁆ : Subgroup X).map (MulAut.conj h).toMonoidHom = ⁅M, M⁆ := by
    intro h hh
    rw [Subgroup.map_commutator, hmap hh]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← hc hg]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← hc (inv_mem hg)]
    refine ⟨g * x * g⁻¹, hx, ?_⟩
    simp [mul_assoc]

omit [Field K] in
theorem isPerfect_of_commutator_eq {X : Type*} [Group X] {M : Subgroup X}
    (h : ⁅M, M⁆ = M) : Group.IsPerfect M := by
  refine ⟨?_⟩
  apply Subgroup.map_injective M.subtype_injective
  rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, h]

end KSL3TwoIrrProof

open KSL3TwoIrrProof in
theorem ksl3TwoIrrThree_of (hP : KSL3TwoIrrPerfect) : KSL3TwoIrrThree := by
  intro K _ _ _ J hJirr hJnab
  classical
  by_contra hJ3
  have hJi : IsIrr J := hJirr
  obtain ⟨N, -, hNmin⟩ := Finite.exists_le_minimal
    (p := fun N : Subgroup (GL (Fin 3) K) =>
      N ≤ J ∧ J ≤ Subgroup.normalizer (N : Set (GL (Fin 3) K)) ∧ ¬ IsScal N)
    (a := J) ⟨le_rfl, Subgroup.le_normalizer, not_isScal_of_isIrr hJi⟩
  obtain ⟨hNJ, hJN, hNs⟩ := hNmin.prop
  have hNi : IsIrr N := (dichotomy hJi hJ3 hJN).resolve_left hNs
  have hN'N : ⁅N, N⁆ ≤ N := Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hJN' : J ≤ Subgroup.normalizer ((⁅N, N⁆ : Subgroup (GL (Fin 3) K)) : Set (GL (Fin 3) K)) :=
    fun g hg => mem_normalizer_commutator (hJN hg)
  by_cases hN'eq : ⁅N, N⁆ = N
  · have h3 := hP K N hNi (isPerfect_of_commutator_eq hN'eq)
    exact hJ3 (h3.trans (Subgroup.card_dvd_of_le hNJ))
  · have hN's : IsScal ⁅N, N⁆ := by
      by_contra hs
      exact hN'eq (le_antisymm hN'N (hNmin.2 ⟨hN'N.trans hNJ, hJN', hs⟩ hN'N))
    have hNab : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a := by
      intro a ha b hb
      obtain ⟨ζ, hζ⟩ := hN's _ (Subgroup.commutator_mem_commutator ha hb)
      rw [commutatorElement_def] at hζ
      exact commute_of_scalar_commutator hJ3 (hNJ ha) (hNJ hb) hζ
    have hJab := isMulCommutative_of_abelian hJ3 hJN hNab hNi
    obtain ⟨a, ha, b, hb, hab⟩ := hJnab
    exact hab (hJab a ha b hb)

end CFSG.RankThree.PartTwo.Sec16
