module

public import CFSG.Monster.B.E6.StdF4Root
public import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.Monster.B.E6.StdF4RadicalCollect

public noncomputable section

namespace CFSG.Monster.B.E6.StdF4Radical

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Overlap CFSG.Monster.B.E6.StdF4
open scoped commutatorElement

instance instNeZeroRankE6 : NeZero Tag.E6.rank := ⟨by decide⟩

@[expose] def radRootList : List (Fin Tag.E6.rank → ℤ) :=
  [![0, 1, 0, 0, 0, 0], ![0, 1, 0, 1, 0, 0], ![0, 1, 0, 1, 1, 0], ![0, 1, 1, 1, 0, 0],
    ![0, 1, 0, 1, 1, 1], ![1, 1, 1, 1, 0, 0], ![0, 1, 1, 1, 1, 0], ![0, 1, 1, 1, 1, 1],
    ![1, 1, 1, 1, 1, 0], ![0, 1, 1, 2, 1, 0], ![0, 1, 1, 2, 1, 1], ![1, 1, 1, 2, 1, 0],
    ![0, 1, 1, 2, 2, 1], ![1, 1, 2, 2, 1, 0], ![1, 1, 1, 1, 1, 1], ![1, 1, 1, 2, 1, 1],
    ![1, 1, 1, 2, 2, 1], ![1, 1, 2, 2, 1, 1], ![1, 1, 2, 2, 2, 1], ![1, 1, 2, 3, 2, 1],
    ![1, 2, 2, 3, 2, 1]]

@[expose] def rr (k : ℕ) : Fin Tag.E6.rank → ℤ := radRootList.getD k 0

@[expose] def orbIdx (i : ℕ) : List ℕ :=
  [[0], [1], [2, 3], [4, 5], [6], [7, 8], [9], [10, 11], [12, 13], [14], [15], [16, 17], [18],
    [19], [20]].getD i []

theorem radRootList_length : radRootList.length = 21 := rfl

theorem radRootList_eq : radRootList = (List.range 21).map rr := by decide +kernel

theorem radRootList_nodup : radRootList.Nodup := by decide +kernel

theorem range_flatMap_orbIdx : (List.range 15).flatMap orbIdx = List.range 21 := by decide +kernel

theorem rr_twenty : rr 20 = theta := by
  funext i
  fin_cases i <;> rfl

theorem e6Certificate_roots_length : e6Certificate.roots.length = 72 := rfl

theorem rr_injOn {i j : ℕ} (hi : i < 21) (hj : j < 21) (h : rr i = rr j) : i = j := by
  have hnd : ((List.range 21).map rr).Nodup := radRootList_eq ▸ radRootList_nodup
  exact (List.nodup_map_iff_inj_on List.nodup_range).1 hnd i (List.mem_range.2 hi) j
    (List.mem_range.2 hj) h

theorem isRoot_rr {k : ℕ} (hk : k < 21) : IsRoot Tag.E6 (rr k) := by
  have h : (List.range 21).all (fun k => (List.range 72).any fun l =>
      List.ofFn (e6Certificate.root l) == List.ofFn (rr k)) = true := by decide +kernel
  simp only [List.all_eq_true, List.mem_range, List.any_eq_true] at h
  obtain ⟨l, hl, he⟩ := h k hk
  rw [← RootCertificate.eq_of_ofFn_beq he]
  exact RootCertificate.isRoot_root e6Certificate_check l
    (by rw [e6Certificate_roots_length]; exact hl)

theorem rr_one_pos {k : ℕ} (hk : k < 21) : 0 < rr k 1 := by
  have h : (List.range 21).all (fun k => decide (0 < rr k 1)) = true := by decide +kernel
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h k hk

theorem height_rr_pos {k : ℕ} (hk : k < 21) : 0 < height (rr k) := by
  have h : (List.range 21).all (fun k => decide (0 < height (rr k))) = true := by
    decide +kernel
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h k hk

theorem exists_rr_eq
    {a : Fin Tag.E6.rank → ℤ} (ha : IsRoot Tag.E6 a) (h1 : 0 < a 1) :
    ∃ k < 21, rr k = a := by
  obtain ⟨l, hl, rfl⟩ := (RootCertificate.isRoot_iff e6Certificate_check).1 ha
  have h : (List.range 72).all (fun l => !decide (0 < e6Certificate.root l 1) ||
      (List.range 21).any fun k => List.ofFn (rr k) == List.ofFn (e6Certificate.root l)) =
      true := by decide +kernel
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, not_lt, List.any_eq_true] at h
  rcases h l (by rw [← e6Certificate_roots_length]; exact hl) with h' | ⟨k, hk, he⟩
  · exact absurd h1 (not_lt.2 h')
  · exact ⟨k, hk, RootCertificate.eq_of_ofFn_beq he⟩

theorem mem_radRootList_iff {a : Fin Tag.E6.rank → ℤ} :
    a ∈ radRootList ↔ IsRoot Tag.E6 a ∧ 0 < height a ∧ 0 < a 1 := by
  constructor
  · intro ha
    rw [radRootList_eq, List.mem_map] at ha
    obtain ⟨k, hk, rfl⟩ := ha
    rw [List.mem_range] at hk
    exact ⟨isRoot_rr hk, height_rr_pos hk, rr_one_pos hk⟩
  · rintro ⟨ha, -, h1⟩
    obtain ⟨k, hk, rfl⟩ := exists_rr_eq ha h1
    rw [radRootList_eq]
    exact List.mem_map_of_mem (List.mem_range.2 hk)

@[expose] def cRows : List ℕ :=
  [524288, 262144, 131072, 65536, 8192, 4096, 32768, 2048, 1024, 16384, 256, 128, 32, 16, 512, 64,
    8, 4, 2, 1, 0]

@[expose] def cC (i j : ℕ) : Bool := (cRows.getD j 0).testBit i

theorem cC_eq {i j : ℕ} (hi : i < 21) (hj : j < 21) : cC i j = decide (rr i + rr j = theta) := by
  have h : (List.range 21).all (fun i => (List.range 21).all fun j =>
      cC i j == decide (rr i + rr j = theta)) = true := by decide +kernel
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
  exact h i hi j hj

theorem eq_theta_of_isRoot_of_two_le
    {a : Fin Tag.E6.rank → ℤ} (ha : IsRoot Tag.E6 a)
    (h : 2 ≤ a 1) :
    a = theta := by
  obtain ⟨l, hl, rfl⟩ := (RootCertificate.isRoot_iff e6Certificate_check).1 ha
  have h' : (List.range 72).all (fun l => !decide (2 ≤ e6Certificate.root l 1) ||
      List.ofFn (e6Certificate.root l) == List.ofFn theta) = true := by decide +kernel
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, not_le] at h'
  rcases h' l (by rw [← e6Certificate_roots_length]; exact hl) with h'' | h''
  · exact absurd h (not_le.2 h'')
  · exact RootCertificate.eq_of_ofFn_beq h''

theorem eq_theta_of_isRoot_add {i j : ℕ} (hi : i < 21) (hj : j < 21)
    (h : IsRoot Tag.E6 (rr i + rr j)) : rr i + rr j = theta := by
  refine eq_theta_of_isRoot_of_two_le h ?_
  have := rr_one_pos hi
  have := rr_one_pos hj
  simp only [Pi.add_apply]
  omega

theorem rr_ne_neg {i j : ℕ} (hi : i < 21) (hj : j < 21) : rr i ≠ -rr j := by
  intro h
  have h1 := congrFun h 1
  have := rr_one_pos hi
  have := rr_one_pos hj
  simp only [Pi.neg_apply] at h1
  omega

abbrev X1
    (a : Fin Tag.E6.rank → ℤ) : ModGL Tag.E6 K := pinnedX Tag.E6 K a 1

@[expose] def xr
    (k : ℕ) : ModGL Tag.E6 K := X1 (rr k)

theorem X1_mul_self
    (a : Fin Tag.E6.rank → ℤ) : X1 a * X1 a = 1 := by
  rw [X1, ← pinnedX_add, one_add_one_eq_two, StdF4.two_eq_zero_K, pinnedX_zero]

theorem X1_inv
    (a : Fin Tag.E6.rank → ℤ) : (X1 a)⁻¹ = X1 a :=
  inv_eq_of_mul_eq_one_left (X1_mul_self a)

theorem xr_twenty :
    xr 20 = rootInvM := by
  rw [xr, rr_twenty]
  rfl

theorem intCast_eq_one_of_sign {ε : ℤ} (h : ε = 1 ∨ ε = -1) : (ε : K) = 1 := by
  rcases h with rfl | rfl
  · simp
  · simp [CharTwo.neg_eq]

theorem X1_commutator
    {a b : Fin Tag.E6.rank → ℤ} (ha : IsRoot Tag.E6 a) (hb : IsRoot Tag.E6 b)
    (hne : a ≠ b) (hne' : a ≠ -b) (hab : IsRoot Tag.E6 (a + b)) :
    ⁅X1 a, X1 b⁆ = X1 (a + b) := by
  obtain ⟨hε, hc⟩ := (simply_laced_root_commutator_unit Tag.E6 (by decide) ha hb hne hne').1 hab
  rw [X1, X1, hc K 1 1, intCast_eq_one_of_sign hε, mul_one, mul_one]

theorem X1_commute
    {a b : Fin Tag.E6.rank → ℤ} (ha : IsRoot Tag.E6 a) (hb : IsRoot Tag.E6 b)
    (hne : a ≠ b) (hne' : a ≠ -b) (hab : ¬IsRoot Tag.E6 (a + b)) :
    X1 a * X1 b = X1 b * X1 a :=
  ((simply_laced_root_commutator_unit Tag.E6 (by decide) ha hb hne hne').2 hab K _
    (Subgroup.subset_closure ⟨1, rfl⟩) _ (Subgroup.subset_closure ⟨1, rfl⟩)).eq

theorem conj_eq_commutator_mul {M : Type*} [Group M] (u v : M) : u * v * u⁻¹ = ⁅u, v⁆ * v := by
  rw [commutatorElement_def]
  group

theorem theta_add_not_isRoot
    {k : ℕ} (hk : k < 21) : ¬IsRoot Tag.E6 (theta + rr k) := by
  intro h
  have h2 : (theta + rr k) (1 : Fin Tag.E6.rank) ≤ theta (1 : Fin Tag.E6.rank) :=
    le_e6HighestRoot h _
  have := rr_one_pos hk
  have ht : theta (1 : Fin Tag.E6.rank) = 2 := rfl
  rw [Pi.add_apply] at h2
  omega

theorem rootInvM_mul_xr
    {k : ℕ} (hk : k < 21) : rootInvM * xr k = xr k * rootInvM := by
  by_cases h20 : k = 20
  · subst h20
    rw [xr_twenty]
  have hne : theta ≠ rr k := fun h => h20 (rr_injOn (by norm_num) hk (rr_twenty.trans h)).symm
  have hne' : theta ≠ -rr k := by
    rw [← rr_twenty]
    exact rr_ne_neg (by norm_num) hk
  exact X1_commute isRoot_theta (isRoot_rr hk) hne hne' (theta_add_not_isRoot hk)

theorem not_cC_self {i : ℕ} (hi : i < 21) : cC i i = false := by
  have h : (List.range 21).all (fun i => !cC i i) = true := by decide +kernel
  simp only [List.all_eq_true, List.mem_range, Bool.not_eq_true'] at h
  exact h i hi

theorem rels_xr :
    Rels xr rootInvM cC (List.range 21) where
  sq i _ := X1_mul_self _
  zsq := rootInvM_mul_self
  zcomm i hi := rootInvM_mul_xr (List.mem_range.1 hi)
  rel i hi j hj := by
    rw [List.mem_range] at hi hj
    by_cases hij : i = j
    · subst hij
      rw [not_cC_self hi, zb_false, mul_one]
    have hne : rr i ≠ rr j := fun h => hij (rr_injOn hi hj h)
    have hne' := rr_ne_neg hi hj
    by_cases hr : IsRoot Tag.E6 (rr i + rr j)
    · have hθ := eq_theta_of_isRoot_add hi hj hr
      have hc : cC i j = true := by rw [cC_eq hi hj, hθ]; exact decide_eq_true rfl
      rw [hc, zb_true]
      have h1 : ⁅xr i, xr j⁆ = rootInvM := by
        have := X1_commutator (isRoot_rr hi) (isRoot_rr hj) hne hne' hr
        rw [hθ] at this
        exact this
      have h2 : xr i * xr j = rootInvM * (xr j * xr i) := by
        rw [commutatorElement_def] at h1
        calc xr i * xr j = (xr i * xr j * (xr i)⁻¹ * (xr j)⁻¹) * (xr j * xr i) := by group
          _ = rootInvM * (xr j * xr i) := by rw [h1]
      rw [h2, ← mul_assoc, rootInvM_mul_xr hj, mul_assoc, rootInvM_mul_xr hi, ← mul_assoc]
    · have hc : cC i j = false := by
        rw [cC_eq hi hj, decide_eq_false_iff_not]
        intro h
        exact hr (h ▸ isRoot_theta)
      rw [hc, zb_false, mul_one]
      exact X1_commute (isRoot_rr hi) (isRoot_rr hj) hne hne' hr

end CFSG.Monster.B.E6.StdF4Radical
