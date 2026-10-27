module

public import Certificates.Data.CFSGNative.MonsterAxis.BabyCover
public import CFSG.Monster.AxisCount.CoverSpec

public section

namespace CFSG.Monster.AxisCount.Native.Baby

open CFSG.Monster.AxisCount.Native.Cover

structure CoverFactsM (m total : ℕ) (T : CoverTables) (rows : Array (Array ℕ))
    (seeds sizes : Array ℕ) : Prop where
  rows_size : rows.size = m
  rows_lt : ∀ g < m, ∀ i < 24, rows[g]![i]! < 2 ^ 24
  sizes_size : seeds.size = sizes.size
  point : ∀ v < 2 ^ 24, cvOKm m T rows seeds v = true
  card_found : (foundSet T).card = total
  card_label : ∀ r < seeds.size, (labelSet T (r + 1)).card = sizes[r]!
  seed : ∀ r < seeds.size, seeds[r]! < 2 ^ 24 ∧ rd8 T.lab seeds[r]! = r + 1

theorem coverFactsM_of_check {m total : ℕ} {T : CoverTables} {rows : Array (Array ℕ)}
    {seeds sizes : Array ℕ} {chunks : ℕ} (hc : 0 < chunks)
    (h : coverCheckM m total T rows seeds sizes chunks = true) :
    CoverFactsM m total T rows seeds sizes := by
  simp only [coverCheckM, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hrows, hall⟩, hsz⟩, -⟩, hpar⟩, hcount⟩, hsizes⟩, hseeds⟩ := h
  have hlt : ∀ g < m, ∀ i < 24, rows[g]![i]! < 2 ^ 24 := by
    intro g hg i hi
    have hg' : g < rows.size := by omega
    have h1 := Array.all_eq_true.1 hall g hg'
    simp only [Bool.and_eq_true, beq_iff_eq] at h1
    obtain ⟨hs, h2⟩ := h1
    have hi' : i < rows[g].size := by omega
    have h3 := Array.all_eq_true.1 h2 i hi'
    simp only [decide_eq_true_eq] at h3
    rw [getElem!_pos rows g hg', getElem!_pos rows[g] i hi']
    exact h3
  refine ⟨hrows, hlt, hsz, parAll_spec hc hpar, ?_, ?_, ?_⟩
  · rw [← hcount, countBelow_eq, foundSet]
    simp
  · intro r hr
    have := parAll_spec hc hsizes r hr
    rw [beq_iff_eq] at this
    rw [← this, countBelow_eq, labelSet]
    simp
  · intro r hr
    have := (allFrom_iff _ 0 seeds.size).1 hseeds r hr
    rw [zero_add] at this
    simpa using this

theorem cvOKm_spec {m : ℕ} {T : CoverTables} {rows : Array (Array ℕ)} {seeds : Array ℕ} {v : ℕ}
    (h : cvOKm m T rows seeds v = true) (hl : rd8 T.lab v ≠ 0) :
    rd8 T.lab v ≤ seeds.size ∧
    (rd8 T.lev v = 1 → v = seeds[rd8 T.lab v - 1]!) ∧
    (rd8 T.lev v ≠ 1 → rd8 T.lev v ≠ 0 ∧ rd32 T.par v < 2 ^ 24 ∧ rd8 T.gen v < m ∧
      rd8 T.lab (rd32 T.par v) = rd8 T.lab v ∧ rd8 T.lev (rd32 T.par v) + 1 = rd8 T.lev v ∧
      cvImg rows (rd8 T.gen v) (rd32 T.par v) = v) ∧
    (∀ j < m, rd8 T.lab (cvImg rows j v) = rd8 T.lab v) := by
  unfold cvOKm at h
  rw [ite_eq_right (by simpa using hl)] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨ho, hd⟩, hcl⟩ := h
  refine ⟨ho, fun h1 => ?_, fun h1 => ?_, fun j hj => ?_⟩
  · rw [ite_eq_left (by simpa using h1)] at hd
    simpa using hd
  · rw [ite_eq_right (by simpa using h1)] at hd
    simpa [Bool.and_eq_true, and_assoc] using hd
  · have := (allFrom_iff _ 0 m).1 hcl j hj
    rw [zero_add] at this
    simpa using this

section Orbits

variable {G X : Type*} [Group G] [MulAction G X] {m total : ℕ} {T : CoverTables}
  {rows : Array (Array ℕ)} {seeds sizes : Array ℕ} {dec : ℕ → X} {gens : ℕ → G}

namespace CoverFactsM

theorem cvImg_lt (hF : CoverFactsM m total T rows seeds sizes) {g : ℕ} (hg : g < m) (v : ℕ) :
    cvImg rows g v < 2 ^ 24 :=
  actGo_lt _ v (hF.rows_lt g hg) 24 0 le_rfl (Nat.two_pow_pos 24)

theorem mem_orbit (hF : CoverFactsM m total T rows seeds sizes)
    (hk : ∀ g < m, ∀ p, dec (cvImg rows g p) = gens g • dec p) :
    ∀ v < 2 ^ 24, rd8 T.lab v ≠ 0 →
      dec v ∈ MulAction.orbit (Subgroup.closure (gens '' Set.Iio m))
        (dec seeds[rd8 T.lab v - 1]!) := by
  intro v hv hl
  induction hlev : rd8 T.lev v using Nat.strong_induction_on generalizing v with
  | _ l ih =>
    obtain ⟨-, h1, hpar, -⟩ := cvOKm_spec (hF.point v hv) hl
    by_cases hl1 : rd8 T.lev v = 1
    · rw [← h1 hl1]
      exact MulAction.mem_orbit_self _
    · obtain ⟨hl0, hp, hg, hlab, hlev', himg⟩ := hpar hl1
      have hpl : rd8 T.lab (rd32 T.par v) ≠ 0 := by rw [hlab]; exact hl
      have ihp := ih _ (by omega) _ hp hpl rfl
      rw [hlab] at ihp
      have e : dec v = gens (rd8 T.gen v) • dec (rd32 T.par v) := by rw [← hk _ hg, himg]
      rw [e]
      exact CFSG.Monster.VisCert.smul_mem_orbit_closure (S := gens '' Set.Iio m)
        (Set.mem_image_of_mem gens (Set.mem_Iio.2 hg)) ihp

theorem lab_le (hF : CoverFactsM m total T rows seeds sizes) {v : ℕ} (hv : v < 2 ^ 24)
    (hl : rd8 T.lab v ≠ 0) : rd8 T.lab v ≤ seeds.size :=
  (cvOKm_spec (hF.point v hv) hl).1

theorem cvImg_mem_labelSet (hF : CoverFactsM m total T rows seeds sizes) {o v : ℕ} (ho : o ≠ 0)
    (hv : v ∈ labelSet T o) {j : ℕ} (hj : j < m) : cvImg rows j v ∈ labelSet T o := by
  simp only [labelSet, Finset.mem_filter, Finset.mem_range] at hv ⊢
  obtain ⟨hv24, hlab⟩ := hv
  have hl : rd8 T.lab v ≠ 0 := by rw [hlab]; exact ho
  obtain ⟨-, -, -, hcl⟩ := cvOKm_spec (hF.point v hv24) hl
  exact ⟨hF.cvImg_lt hj v, (hcl j hj).trans hlab⟩

theorem seed_mem_labelSet (hF : CoverFactsM m total T rows seeds sizes) {r : ℕ}
    (hr : r < seeds.size) : seeds[r]! ∈ labelSet T (r + 1) := by
  obtain ⟨h1, h2⟩ := hF.seed r hr
  simp only [labelSet, Finset.mem_filter, Finset.mem_range]
  exact ⟨h1, h2⟩

theorem labelSet_subset_foundSet (o : ℕ) (ho : o ≠ 0) : labelSet T o ⊆ foundSet T := by
  intro v hv
  simp only [labelSet, foundSet, Finset.mem_filter] at hv ⊢
  exact ⟨hv.1, by rw [hv.2]; exact ho⟩

theorem mem_labelSet_of_mem_foundSet {v : ℕ} (hv : v ∈ foundSet T) :
    v ∈ labelSet T (rd8 T.lab v) := by
  simp only [labelSet, foundSet, Finset.mem_filter, Finset.mem_range] at hv ⊢
  exact ⟨hv.1, trivial⟩

theorem injOn_dec (hdec : ∀ a b, a < 2 ^ 24 → b < 2 ^ 24 → dec a = dec b → a = b)
    (s : Finset ℕ) (hs : s ⊆ Finset.range (2 ^ 24)) : Set.InjOn dec (s : Set ℕ) :=
  fun a ha b hb hab => hdec a b (Finset.mem_range.1 (hs ha)) (Finset.mem_range.1 (hs hb)) hab

theorem orbit_eq (hF : CoverFactsM m total T rows seeds sizes)
    (hk : ∀ g < m, ∀ p, dec (cvImg rows g p) = gens g • dec p) {r : ℕ} (hr : r < seeds.size) :
    MulAction.orbit (Subgroup.closure (gens '' Set.Iio m)) (dec seeds[r]!) =
      dec '' (labelSet T (r + 1) : Set ℕ) := by
  refine Set.Subset.antisymm (CFSG.Monster.VisCert.orbit_closure_subset
    ((labelSet T (r + 1)).finite_toSet.image dec) ?_
    ⟨_, hF.seed_mem_labelSet hr, rfl⟩) ?_
  · rintro _ ⟨j, hj, rfl⟩ _ ⟨v, hv, rfl⟩
    have hj' : j < m := Set.mem_Iio.1 hj
    exact ⟨cvImg rows j v, hF.cvImg_mem_labelSet (Nat.succ_ne_zero r) hv hj', hk j hj' v⟩
  · rintro _ ⟨v, hv, rfl⟩
    have hv' : v ∈ labelSet T (r + 1) := hv
    simp only [labelSet, Finset.mem_filter, Finset.mem_range] at hv'
    obtain ⟨hv24, ho⟩ := hv'
    have := hF.mem_orbit hk v hv24 (by rw [ho]; exact Nat.succ_ne_zero r)
    rwa [ho, Nat.add_sub_cancel] at this

theorem ncard_orbit (hF : CoverFactsM m total T rows seeds sizes)
    (hk : ∀ g < m, ∀ p, dec (cvImg rows g p) = gens g • dec p)
    (hdec : ∀ a b, a < 2 ^ 24 → b < 2 ^ 24 → dec a = dec b → a = b) {r : ℕ}
    (hr : r < seeds.size) :
    (MulAction.orbit (Subgroup.closure (gens '' Set.Iio m)) (dec seeds[r]!)).ncard =
      sizes[r]! := by
  rw [hF.orbit_eq hk hr,
    (injOn_dec hdec (labelSet T (r + 1)) (Finset.filter_subset _ _)).ncard_image,
    Set.ncard_coe_finset, hF.card_label r hr]

theorem image_foundSet_eq_iUnion (hF : CoverFactsM m total T rows seeds sizes)
    (hk : ∀ g < m, ∀ p, dec (cvImg rows g p) = gens g • dec p) :
    dec '' (foundSet T : Set ℕ) = ⋃ r ∈ Set.Iio seeds.size,
      MulAction.orbit (Subgroup.closure (gens '' Set.Iio m)) (dec seeds[r]!) := by
  ext x
  simp only [Set.mem_image, Set.mem_iUnion, Set.mem_Iio, exists_prop]
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hv' : v ∈ foundSet T := hv
    have hm := mem_labelSet_of_mem_foundSet hv'
    simp only [foundSet, Finset.mem_filter, Finset.mem_range] at hv'
    obtain ⟨hv24, hl⟩ := hv'
    have hle := hF.lab_le hv24 hl
    refine ⟨rd8 T.lab v - 1, by omega, ?_⟩
    rw [hF.orbit_eq hk (by omega), Nat.sub_add_cancel (Nat.pos_of_ne_zero hl)]
    exact ⟨v, hm, rfl⟩
  · rintro ⟨r, hr, hx⟩
    rw [hF.orbit_eq hk hr] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    exact ⟨v, labelSet_subset_foundSet _ (Nat.succ_ne_zero r) hv, rfl⟩

theorem disjoint_orbit (hF : CoverFactsM m total T rows seeds sizes)
    (hk : ∀ g < m, ∀ p, dec (cvImg rows g p) = gens g • dec p)
    (hdec : ∀ a b, a < 2 ^ 24 → b < 2 ^ 24 → dec a = dec b → a = b) {r r' : ℕ}
    (hr : r < seeds.size) (hr' : r' < seeds.size) (hne : r ≠ r') :
    Disjoint (MulAction.orbit (Subgroup.closure (gens '' Set.Iio m)) (dec seeds[r]!))
      (MulAction.orbit (Subgroup.closure (gens '' Set.Iio m)) (dec seeds[r']!)) := by
  rw [hF.orbit_eq hk hr, hF.orbit_eq hk hr', Set.disjoint_left]
  rintro _ ⟨v, hv, rfl⟩ ⟨w, hw, hvw⟩
  have hv' : v ∈ labelSet T (r + 1) := hv
  have hw' : w ∈ labelSet T (r' + 1) := hw
  simp only [labelSet, Finset.mem_filter, Finset.mem_range] at hv' hw'
  have := hdec w v hw'.1 hv'.1 hvw
  subst this
  exact hne (by omega)

theorem ncard_image_foundSet (hF : CoverFactsM m total T rows seeds sizes)
    (hdec : ∀ a b, a < 2 ^ 24 → b < 2 ^ 24 → dec a = dec b → a = b) :
    (dec '' (foundSet T : Set ℕ)).ncard = total := by
  rw [(injOn_dec hdec (foundSet T) (Finset.filter_subset _ _)).ncard_image, Set.ncard_coe_finset,
    hF.card_found]

end CoverFactsM

end Orbits

end CFSG.Monster.AxisCount.Native.Baby
