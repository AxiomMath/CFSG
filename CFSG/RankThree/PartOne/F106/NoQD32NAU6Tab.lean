module

public import CFSG.RankThree.PartOne.F106.NoQD32NAU6Trace
public import CFSG.RankThree.PartOne.F106.NoQD32NAGen
public import CFSG.RankThree.PartOne.F106.NoQD32NAU6Facts
public import CFSG.RankThree.PartOne.F106.U6Three

public section

namespace CFSG.RankThree.PartOne.F106

open Matrix CFSG.Assembly.LowTwoRank Subgroup

section Tab

variable {K : Type} [Field K] [CharP K 2] (ω : Cube K) (hK : Nat.card K = (2 ^ 1) ^ 2)
  (c : U6SylowCert)

structure U6Tab where
  S : Subgroup (StatedProj (StatedSU 6 (2 ^ 1) K))
  card : Nat.card S = 3 ^ 6
  sel_mem : ∀ i < 729, c.sel ω hK i ∈ S
  exists_sel : ∀ y ∈ S, ∃ i < 729, y = c.sel ω hK i
  sel_inj : ∀ i < 729, ∀ j < 729, c.sel ω hK i = c.sel ω hK j → i = j
  sel_zero : c.sel ω hK 0 = 1
  tab_zero : c.tab 0 = U6Mon.one

variable {ω hK c}

theorem sel_mul_eq_iff (i j k : ℕ) :
    c.sel ω hK i * c.sel ω hK j = c.sel ω hK k ↔ (c.tab i).mul (c.tab j) = c.tab k := by
  rw [U6SylowCert.sel, U6SylowCert.sel, U6SylowCert.sel,
    Cube.mu_mul ω hK (U6SylowCert.ok_tab i) (U6SylowCert.ok_tab j)]
  constructor
  · intro h
    exact ω.mu_injective hK (U6Mon.ok_mul (U6SylowCert.ok_tab i) (U6SylowCert.ok_tab j))
      (U6SylowCert.ok_tab k) h
  · intro h
    rw [h]

theorem sel_cube_iff (i : ℕ) : c.sel ω hK i ^ 3 = 1 ↔ (c.tab i).cubeB = true := by
  have h1 : c.sel ω hK i ^ 3 = c.sel ω hK i * c.sel ω hK i * c.sel ω hK i := pow_three' _
  have h2 : c.sel ω hK i * c.sel ω hK i = ω.mu hK ((c.tab i).mul (c.tab i)) := by
    rw [U6SylowCert.sel, Cube.mu_mul ω hK (U6SylowCert.ok_tab i) (U6SylowCert.ok_tab i)]
  have h3 : c.sel ω hK i * c.sel ω hK i * c.sel ω hK i =
      ω.mu hK (((c.tab i).mul (c.tab i)).mul (c.tab i)) := by
    rw [h2, U6SylowCert.sel, Cube.mu_mul ω hK
      (U6Mon.ok_mul (U6SylowCert.ok_tab i) (U6SylowCert.ok_tab i)) (U6SylowCert.ok_tab i)]
  rw [h1, h3, U6Mon.cubeB, decide_eq_true_iff, ← ω.mu_one hK]
  constructor
  · intro h
    exact ω.mu_injective hK (U6Mon.ok_mul (U6Mon.ok_mul (U6SylowCert.ok_tab i)
      (U6SylowCert.ok_tab i)) (U6SylowCert.ok_tab i)) U6Mon.ok_one h
  · intro h
    rw [h]

theorem sel_comm_iff (i j : ℕ) :
    c.sel ω hK i * c.sel ω hK j = c.sel ω hK j * c.sel ω hK i ↔
      U6Mon.commB (c.tab i) (c.tab j) = true := by
  rw [← U6SylowCert.sel_comm ω hK, U6Mon.commB, decide_eq_true_iff]

theorem sel_trZero_iff (i : ℕ) :
    trZeroP (StatedSU 6 (2 ^ 1) K) (c.sel ω hK i) ↔ (c.tab i).trB = true :=
  trZeroP_mu ω hK (U6SylowCert.ok_tab i)

noncomputable def U6Tab.ofFacts [Finite (StatedProj (StatedSU 6 (2 ^ 1) K))] (hf : c.Facts) :
    U6Tab ω hK c := by
  have h := table_subgroup (fun k : Fin 6 => ω.genMu hK (k : ℕ)) (c.sel ω hK)
    (U6SylowCert.sel_zero ω hK hf) (fun i hi j hj h => U6SylowCert.sel_inj ω hK hf hi hj h)
    (fun i hi => U6SylowCert.sel_mem_closure ω hK hf hi)
    (fun i hi k => ⟨c.rtv i k, (hf.rt i hi k k.2).1, U6SylowCert.sel_rt ω hK hf hi k.2⟩)
  exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2.1, h.choose_spec.2.2,
    fun i hi j hj h => U6SylowCert.sel_inj ω hK hf hi hj h, U6SylowCert.sel_zero ω hK hf,
    by show U6Mon.evalWord (c.paths.getD 0 []) = _; rw [hf.zero]; rfl⟩

section Subgroups

variable [Finite (StatedProj (StatedSU 6 (2 ^ 1) K))] (T : U6Tab ω hK c)

include T

variable (ω hK c) in
noncomputable def u6Y0 : Subgroup (StatedProj (StatedSU 6 (2 ^ 1) K)) :=
  Subgroup.closure {g | ∃ i < 729, (c.tab i).blk = 0 ∧ g = c.sel ω hK i}

variable (ω hK c) in
noncomputable def u6E0 : Subgroup (StatedProj (StatedSU 6 (2 ^ 1) K)) :=
  Subgroup.closure {g | ∃ i < 729, ((c.tab i).t0 = 0 ∧ (c.tab i).t1 = 0) ∧ g = c.sel ω hK i}

theorem U6Tab.mem_Y0 {g : StatedProj (StatedSU 6 (2 ^ 1) K)} :
    g ∈ u6Y0 ω hK c ↔ ∃ i < 729, (c.tab i).blk = 0 ∧ g = c.sel ω hK i := by
  have h1 : (1 : StatedProj (StatedSU 6 (2 ^ 1) K)) ∈
      {g | ∃ i < 729, (c.tab i).blk = 0 ∧ g = c.sel ω hK i} :=
    ⟨0, by norm_num, by rw [T.tab_zero]; rfl, T.sel_zero.symm⟩
  have hL : ∀ x ∈ {g | ∃ i < 729, (c.tab i).blk = 0 ∧ g = c.sel ω hK i},
      ∀ y ∈ {g | ∃ i < 729, (c.tab i).blk = 0 ∧ g = c.sel ω hK i},
      x * y ∈ {g | ∃ i < 729, (c.tab i).blk = 0 ∧ g = c.sel ω hK i} := by
    rintro _ ⟨i, hi, hbi, rfl⟩ _ ⟨j, hj, hbj, rfl⟩
    obtain ⟨k, hk, hkeq⟩ := T.exists_sel _ (T.S.mul_mem (T.sel_mem i hi) (T.sel_mem j hj))
    refine ⟨k, hk, ?_, hkeq⟩
    have := (sel_mul_eq_iff (ω := ω) (hK := hK) (c := c) i j k).mp hkeq
    rw [← this, U6Mon.blk_mul, hbi, hbj, add_zero]
  exact mem_closure_iff_of_mul_closed h1 hL g

theorem U6Tab.mem_E0 {g : StatedProj (StatedSU 6 (2 ^ 1) K)} :
    g ∈ u6E0 ω hK c ↔ ∃ i < 729, ((c.tab i).t0 = 0 ∧ (c.tab i).t1 = 0) ∧ g = c.sel ω hK i := by
  have h1 : (1 : StatedProj (StatedSU 6 (2 ^ 1) K)) ∈
      {g | ∃ i < 729, ((c.tab i).t0 = 0 ∧ (c.tab i).t1 = 0) ∧ g = c.sel ω hK i} :=
    ⟨0, by norm_num, by rw [T.tab_zero]; exact ⟨rfl, rfl⟩, T.sel_zero.symm⟩
  have hL : ∀ x ∈ {g | ∃ i < 729, ((c.tab i).t0 = 0 ∧ (c.tab i).t1 = 0) ∧ g = c.sel ω hK i},
      ∀ y ∈ {g | ∃ i < 729, ((c.tab i).t0 = 0 ∧ (c.tab i).t1 = 0) ∧ g = c.sel ω hK i},
      x * y ∈ {g | ∃ i < 729, ((c.tab i).t0 = 0 ∧ (c.tab i).t1 = 0) ∧ g = c.sel ω hK i} := by
    rintro _ ⟨i, hi, hti, rfl⟩ _ ⟨j, hj, htj, rfl⟩
    obtain ⟨k, hk, hkeq⟩ := T.exists_sel _ (T.S.mul_mem (T.sel_mem i hi) (T.sel_mem j hj))
    refine ⟨k, hk, ?_, hkeq⟩
    have := (sel_mul_eq_iff (ω := ω) (hK := hK) (c := c) i j k).mp hkeq
    rw [← this, U6Mon.t0_mul, U6Mon.t1_mul, hti.1, hti.2, htj.1, htj.2]
    exact ⟨add_zero _, add_zero _⟩
  exact mem_closure_iff_of_mul_closed h1 hL g

theorem U6Tab.Y0_le : u6Y0 ω hK c ≤ T.S := fun g hg => by
  obtain ⟨i, hi, -, rfl⟩ := T.mem_Y0.mp hg
  exact T.sel_mem i hi

theorem U6Tab.E0_le : u6E0 ω hK c ≤ T.S := fun g hg => by
  obtain ⟨i, hi, -, rfl⟩ := T.mem_E0.mp hg
  exact T.sel_mem i hi

theorem U6Tab.sel_mem_Y0 {i : ℕ} (hi : i < 729) :
    c.sel ω hK i ∈ u6Y0 ω hK c ↔ (c.tab i).blk = 0 := by
  rw [T.mem_Y0]
  constructor
  · rintro ⟨j, hj, hb, hij⟩
    rwa [T.sel_inj i hi j hj hij]
  · intro h
    exact ⟨i, hi, h, rfl⟩

theorem U6Tab.sel_mem_E0 {i : ℕ} (hi : i < 729) :
    c.sel ω hK i ∈ u6E0 ω hK c ↔ ((c.tab i).t0 = 0 ∧ (c.tab i).t1 = 0) := by
  rw [T.mem_E0]
  constructor
  · rintro ⟨j, hj, hb, hij⟩
    rwa [T.sel_inj i hi j hj hij]
  · intro h
    exact ⟨i, hi, h, rfl⟩

open scoped _root_.Classical in
theorem U6Tab.card_Y0 (hna : c.NAFacts) : Nat.card (u6Y0 ω hK c) = 243 := by
  rw [card_eq_filter T.S (u6Y0 ω hK c) (c.sel ω hK) T.sel_inj T.exists_sel T.Y0_le,
    card_filter_range_eq_length 729 _ (fun i => decide ((c.tab i).blk = 0))
      (fun i hi => by rw [T.sel_mem_Y0 hi]; simp)]
  exact hna.y0

open scoped _root_.Classical in
theorem U6Tab.card_E0 (hna : c.NAFacts) : Nat.card (u6E0 ω hK c) = 81 := by
  rw [card_eq_filter T.S (u6E0 ω hK c) (c.sel ω hK) T.sel_inj T.exists_sel T.E0_le,
    card_filter_range_eq_length 729 _ (fun i => decide ((c.tab i).t0 = 0 ∧ (c.tab i).t1 = 0))
      (fun i hi => by rw [T.sel_mem_E0 hi]; simp)]
  exact hna.e0

open scoped _root_.Classical in
theorem U6Tab.eq_E0_of_elemAbelian (hna : c.NAFacts)
    {E : Subgroup (StatedProj (StatedSU 6 (2 ^ 1) K))} (hES : E ≤ T.S)
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hcube : ∀ a ∈ E, a ^ 3 = 1)
    (h81 : 81 ≤ Nat.card E) : E = u6E0 ω hK c := by
  by_contra hne
  have hE0card := T.card_E0 hna
  have hnle : ¬ E ≤ u6E0 ω hK c := fun hle =>
    hne (Subgroup.eq_of_le_of_card_ge hle (by rw [hE0card]; exact h81))
  obtain ⟨e, heE, heE0⟩ := Set.not_subset.mp hnle
  obtain ⟨i, hi, rfl⟩ := T.exists_sel e (hES heE)
  have hnt : ¬ ((c.tab i).t0 = 0 ∧ (c.tab i).t1 = 0) := fun h =>
    heE0 ((T.sel_mem_E0 hi).mpr h)
  obtain ⟨C, hCmem, hClen, hCcases⟩ := hna.uniq i hi hnt
  set Eidx : Finset ℕ := (Finset.range 729).filter fun j => c.sel ω hK j ∈ E with hEidx
  have hEcard : Eidx.card = Nat.card E :=
    (card_eq_filter T.S E (c.sel ω hK) T.sel_inj T.exists_sel hES).symm
  have hsub : Eidx ⊆ C.toFinset := by
    intro j hj
    rw [hEidx, Finset.mem_filter, Finset.mem_range] at hj
    rw [List.mem_toFinset, hCmem]
    exact ⟨hj.1, (sel_cube_iff (ω := ω) (hK := hK) (c := c) j).mp (hcube _ hj.2),
      (sel_comm_iff (ω := ω) (hK := hK) (c := c) j i).mp (hcomm _ hj.2 _ heE)⟩
  have hCcard : C.toFinset.card ≤ C.length := List.toFinset_card_le C
  have hEC : Eidx = C.toFinset := Finset.eq_of_subset_of_card_le hsub (by omega)
  have hle := Finset.card_le_card hsub
  rcases hCcases with hlt | ⟨x, hx, y, hy, hxy⟩
  · omega
  · have hx' : x ∈ Eidx := by rw [hEC, List.mem_toFinset]; exact hx
    have hy' : y ∈ Eidx := by rw [hEC, List.mem_toFinset]; exact hy
    rw [hEidx, Finset.mem_filter] at hx' hy'
    have h1 := (sel_comm_iff (ω := ω) (hK := hK) (c := c) x y).mp (hcomm _ hx'.2 _ hy'.2)
    rw [h1] at hxy
    exact Bool.noConfusion hxy

open scoped _root_.Classical in
theorem U6Tab.eq_Y0_of_exp_three (hna : c.NAFacts)
    {Y : Subgroup (StatedProj (StatedSU 6 (2 ^ 1) K))} (hYS : Y ≤ T.S)
    (hexp : ∀ y ∈ Y, y ^ 3 = 1) (h243 : 243 ≤ Nat.card Y) : Y = u6Y0 ω hK c := by
  by_contra hne
  have hY0card := T.card_Y0 hna
  set E3idx : Finset ℕ := (Finset.range 729).filter fun j => (c.tab j).cubeB = true with hE3
  have hE3c : E3idx.card = 297 :=
    (card_filter_range_eq_length 729 _ (fun j => (c.tab j).cubeB) (fun j _ => Iff.rfl)).trans hna.e3
  set Yidx : Finset ℕ := (Finset.range 729).filter fun j => c.sel ω hK j ∈ Y with hYidx
  set Y0idx : Finset ℕ := (Finset.range 729).filter fun j => c.sel ω hK j ∈ u6Y0 ω hK c
    with hY0idx
  have hYc : Yidx.card = Nat.card Y :=
    (card_eq_filter T.S Y (c.sel ω hK) T.sel_inj T.exists_sel hYS).symm
  have hY0c : Y0idx.card = 243 :=
    ((card_eq_filter T.S (u6Y0 ω hK c) (c.sel ω hK) T.sel_inj T.exists_sel T.Y0_le).symm.trans
      hY0card)
  have hYsub : Yidx ⊆ E3idx := by
    intro j hj
    rw [hYidx, Finset.mem_filter] at hj
    rw [hE3, Finset.mem_filter]
    exact ⟨hj.1, (sel_cube_iff (ω := ω) (hK := hK) (c := c) j).mp (hexp _ hj.2)⟩
  have hY0sub : Y0idx ⊆ E3idx := by
    intro j hj
    rw [hY0idx, Finset.mem_filter, Finset.mem_range] at hj
    rw [hE3, Finset.mem_filter, Finset.mem_range]
    exact ⟨hj.1, hna.y0cube j hj.1 ((T.sel_mem_Y0 hj.1).mp hj.2)⟩
  have hYle : Nat.card Y ≤ 297 := by
    rw [← hYc, ← hE3c]
    exact Finset.card_le_card hYsub
  have hYdvd : Nat.card Y ∣ 3 ^ 6 := T.card ▸ Subgroup.card_dvd_of_le hYS
  have hY243 : Nat.card Y = 243 := by
    obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hYdvd
    rw [hjeq] at h243 hYle ⊢
    interval_cases j <;> omega
  have hinf : Nat.card (Y ⊓ u6Y0 ω hK c : Subgroup _) ≤ 3 ^ 4 := by
    refine card_le_of_lt (inf_le_right) ?_ (k := 5) (by rw [hY0card]; norm_num)
    intro h
    apply hne
    have hle : u6Y0 ω hK c ≤ Y := h ▸ inf_le_left
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hY243, hY0card])).symm
  set Iidx : Finset ℕ := (Finset.range 729).filter fun j => c.sel ω hK j ∈ Y ⊓ u6Y0 ω hK c
    with hIidx
  have hIc : Iidx.card = Nat.card (Y ⊓ u6Y0 ω hK c : Subgroup _) :=
    (card_eq_filter T.S (Y ⊓ u6Y0 ω hK c) (c.sel ω hK) T.sel_inj T.exists_sel
      (inf_le_left.trans hYS)).symm
  have hinter : Yidx ∩ Y0idx = Iidx := by
    ext j
    simp only [hYidx, hY0idx, hIidx, Finset.mem_inter, Finset.mem_filter, Subgroup.mem_inf]
    constructor
    · rintro ⟨⟨hj, h1⟩, ⟨_, h2⟩⟩
      exact ⟨hj, h1, h2⟩
    · rintro ⟨hj, h1, h2⟩
      exact ⟨⟨hj, h1⟩, ⟨hj, h2⟩⟩
  have hu := Finset.card_union_add_card_inter Yidx Y0idx
  have hunion : (Yidx ∪ Y0idx).card ≤ E3idx.card :=
    Finset.card_le_card (Finset.union_subset hYsub hY0sub)
  rw [hinter, hIc, hYc, hY0c, hY243] at hu
  omega

end Subgroups

end Tab

end CFSG.RankThree.PartOne.F106
