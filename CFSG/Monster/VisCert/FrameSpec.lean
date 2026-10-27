module

public import Certificates.Data.CFSGNative.MonsterVis.Frame
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Monster.VisCert

open Native

theorem allFrom_iff (p : ℕ → Bool) :
    ∀ lo len, allFrom p lo len = true ↔ ∀ k < len, p (lo + k) = true
  | lo, 0 => by simp [allFrom]
  | lo, len + 1 => by
    rw [allFrom]
    by_cases h : p lo = true
    · rw [ite_eq_left h, allFrom_iff p (lo + 1) len]
      constructor
      · intro h' k hk
        rcases k with _ | k
        · simpa using h
        · have := h' k (by omega)
          rwa [show lo + 1 + k = lo + (k + 1) by omega] at this
      · intro h' k hk
        have := h' (k + 1) (by omega)
        rwa [show lo + (k + 1) = lo + 1 + k by omega] at this
    · rw [ite_eq_right h]
      simp only [Bool.false_eq_true, false_iff, not_forall]
      exact ⟨0, by omega, by simpa using h⟩

theorem countGo_eq (p : ℕ → Bool) :
    ∀ n acc, countGo p n acc = acc + ((Finset.range n).filter fun i => p i = true).card
  | 0, acc => by simp [countGo]
  | n + 1, acc => by
    rw [countGo, countGo_eq p n, Finset.range_add_one, Finset.filter_insert]
    by_cases h : p n = true
    · rw [ite_eq_left h, ite_eq_left h, Finset.card_insert_of_notMem (by simp)]
      ring
    · rw [ite_eq_right h, ite_eq_right h]

theorem countBelow_eq (p : ℕ → Bool) (n : ℕ) :
    countBelow p n = ((Finset.range n).filter fun i => p i = true).card := by
  rw [countBelow, countGo_eq, zero_add]

theorem parAll_spec {n chunks : ℕ} {p : ℕ → Bool} (hc : 0 < chunks)
    (h : parAll n chunks p = true) : ∀ i < n, p i = true := by
  intro i hi
  unfold parAll at h
  simp only [List.all_map, List.all_eq_true, List.mem_range, Function.comp_apply] at h
  set sz := n / chunks + 1 with hsz
  have hsz0 : 0 < sz := Nat.succ_pos _
  have hj : i / sz < chunks := by
    rw [Nat.div_lt_iff_lt_mul hsz0]
    have h1 := Nat.div_add_mod n chunks
    have h2 := Nat.mod_lt n hc
    have : chunks * sz = chunks * (n / chunks) + chunks := by rw [hsz]; ring
    rw [this]
    generalize chunks * (n / chunks) = A at h1 ⊢
    omega
  have hstep := h (i / sz) hj
  change allFrom p (i / sz * sz) sz = true at hstep
  have := (allFrom_iff p _ _).1 hstep (i % sz) (Nat.mod_lt _ hsz0)
  have e : i / sz * sz + i % sz = i := by
    rw [mul_comm]
    exact Nat.div_add_mod i sz
  rwa [e] at this

section Invariant

variable {G X : Type*} [Group G] [MulAction G X]

@[expose] def invSubgroup (Y : Set X) (hY : Y.Finite) : Subgroup G where
  carrier := {g | ∀ y ∈ Y, g • y ∈ Y}
  one_mem' := fun y hy => by simpa using hy
  mul_mem' := fun {a b} ha hb y hy => by
    rw [mul_smul]
    exact ha _ (hb y hy)
  inv_mem' := fun {g} hg y hy => by
    have hbij := (hY.injOn_iff_bijOn_of_mapsTo (f := fun x => g • x) hg).1
      (fun a _ b _ hab => smul_left_cancel g hab)
    obtain ⟨y', hy', hyy'⟩ := hbij.surjOn hy
    have : g⁻¹ • y = y' := by
      rw [← hyy']
      simp
    rw [this]
    exact hy'

theorem orbit_closure_subset {S : Set G} {Y : Set X} (hY : Y.Finite)
    (h : ∀ s ∈ S, ∀ y ∈ Y, s • y ∈ Y) {x : X} (hx : x ∈ Y) :
    MulAction.orbit (Subgroup.closure S) x ⊆ Y := by
  have hle : Subgroup.closure S ≤ invSubgroup Y hY :=
    (Subgroup.closure_le _).2 fun s hs => h s hs
  rintro _ ⟨⟨g, hg⟩, rfl⟩
  exact hle hg x hx

theorem smul_mem_orbit_closure {S : Set G} {s : G} (hs : s ∈ S) {x y : X}
    (hy : y ∈ MulAction.orbit (Subgroup.closure S) x) :
    s • y ∈ MulAction.orbit (Subgroup.closure S) x :=
  MulAction.mem_orbit_of_mem_orbit (⟨s, Subgroup.subset_closure hs⟩ : Subgroup.closure S) hy

end Invariant

theorem actGo_lt (rows : Array ℕ) (v : ℕ) (hr : ∀ i < 24, rows[i]! < 2 ^ 24) :
    ∀ n acc, n ≤ 24 → acc < 2 ^ 24 → Native.actGo rows v n acc < 2 ^ 24
  | 0, acc, _, h => h
  | n + 1, acc, hn, h => by
    rw [Native.actGo]
    refine actGo_lt rows v hr n _ (by omega) ?_
    by_cases hb : v.testBit n = true
    · rw [ite_eq_left hb]
      exact Nat.xor_lt_two_pow h (hr n (by omega))
    · rw [ite_eq_right hb]
      exact h

theorem frameRows_lt : ∀ g < 15, ∀ i < 24, (frameRows[g]!)[i]! < 2 ^ 24 := by decide

theorem gimg_lt {g : ℕ} (hg : g < 15) (v : ℕ) : gimg g v < 2 ^ 24 :=
  actGo_lt _ v (frameRows_lt g hg) 24 0 le_rfl (by norm_num)

@[expose] def foundSet (T : FrameTables) : Finset ℕ :=
  (Finset.range (2 ^ 24)).filter fun v => rd8 T.klev v ≠ 0

@[expose] def labelSet (T : FrameTables) (o : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ 24)).filter fun v => rd8 T.klev v ≠ 0 ∧ rd8 T.olab v = o

structure FrameFacts (T : FrameTables) : Prop where
  point : ∀ v < 2 ^ 24, pointOK T v = true
  card_found : (foundSet T).card = deltaCount
  card_label : ∀ o, 1 ≤ o → o ≤ 6 → (labelSet T o).card = frameSizes[o - 1]!
  rep : ∀ o, 1 ≤ o → o ≤ 6 →
    frameReps[o - 1]! < 2 ^ 24 ∧ rd8 T.klev frameReps[o - 1]! ≠ 0 ∧ rd8 T.olab frameReps[o - 1]! = o

theorem frameFacts_of_check {T : FrameTables} {chunks : ℕ} (hc : 0 < chunks)
    (h : frameCheck T chunks = true) : FrameFacts T := by
  simp only [frameCheck, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hpar, hcount⟩, hsizes⟩, hreps⟩ := h
  refine ⟨parAll_spec hc hpar, ?_, ?_, ?_⟩
  · rw [← hcount, countBelow_eq, foundSet]
    simp
  · intro o h1 h6
    have := (allFrom_iff _ 1 6).1 hsizes (o - 1) (by omega)
    rw [show 1 + (o - 1) = o by omega, beq_iff_eq] at this
    rw [← this, countBelow_eq, labelSet]
    simp
  · intro o h1 h6
    have := (allFrom_iff _ 1 6).1 hreps (o - 1) (by omega)
    rw [show 1 + (o - 1) = o by omega] at this
    simpa [and_assoc] using this

theorem pointOK_spec {T : FrameTables} {v : ℕ} (h : pointOK T v = true) (hl : rd8 T.klev v ≠ 0) :
    (rd8 T.klev v = 1 → v = frameSeed) ∧
    (rd8 T.klev v ≠ 1 → rd32 T.kpar v < 2 ^ 24 ∧ rd8 T.klab v < 15 ∧
      rd8 T.klev (rd32 T.kpar v) + 1 = rd8 T.klev v ∧ gimg (rd8 T.klab v) (rd32 T.kpar v) = v) ∧
    1 ≤ rd8 T.olab v ∧ rd8 T.olab v ≤ 6 ∧
    (∀ j, 1 ≤ j → j < 15 → rd8 T.klev (gimg j v) ≠ 0 ∧ rd8 T.olab (gimg j v) = rd8 T.olab v) ∧
    (rd8 T.nlev v = 1 → v = frameReps[rd8 T.olab v - 1]!) ∧
    (rd8 T.nlev v ≠ 1 → rd8 T.nlev v ≠ 0 ∧ rd32 T.npar v < 2 ^ 24 ∧ 1 ≤ rd8 T.nlab v ∧
      rd8 T.nlab v < 15 ∧ rd8 T.klev (rd32 T.npar v) ≠ 0 ∧
      rd8 T.olab (rd32 T.npar v) = rd8 T.olab v ∧
      rd8 T.nlev (rd32 T.npar v) + 1 = rd8 T.nlev v ∧
      gimg (rd8 T.nlab v) (rd32 T.npar v) = v) := by
  unfold pointOK at h
  rw [ite_eq_right (by simpa using hl)] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hk, ho1⟩, ho6⟩, hcl⟩, hn⟩ := h
  refine ⟨fun h1 => ?_, fun h1 => ?_, ho1, ho6, fun j hj1 hj15 => ?_, fun h1 => ?_, fun h1 => ?_⟩
  · unfold kOK at hk
    rw [ite_eq_left (by simpa using h1)] at hk
    simpa using hk
  · unfold kOK at hk
    rw [ite_eq_right (by simpa using h1)] at hk
    simpa [Bool.and_eq_true, and_assoc] using hk
  · unfold closeOK at hcl
    have := (allFrom_iff _ 1 14).1 hcl (j - 1) (by omega)
    rw [show 1 + (j - 1) = j by omega] at this
    simpa [Bool.and_eq_true] using this
  · unfold nOK at hn
    rw [ite_eq_left (by simpa using h1)] at hn
    simpa using hn
  · unfold nOK at hn
    rw [ite_eq_right (by simpa using h1)] at hn
    simpa [Bool.and_eq_true, and_assoc] using hn

section Orbits

variable {G X : Type*} [Group G] [MulAction G X] {T : FrameTables} {dec : ℕ → X} {kGen : ℕ → G}

namespace FrameFacts

theorem mem_orbit_K (hF : FrameFacts T) (hk : ∀ g < 15, ∀ p, dec (gimg g p) = kGen g • dec p) :
    ∀ v < 2 ^ 24, rd8 T.klev v ≠ 0 →
      dec v ∈ MulAction.orbit (Subgroup.closure (kGen '' Set.Iio 15)) (dec frameSeed) := by
  intro v hv hl
  induction hlev : rd8 T.klev v using Nat.strong_induction_on generalizing v with
  | _ l ih =>
    obtain ⟨h1, hpar, -⟩ := pointOK_spec (hF.point v hv) hl
    by_cases hl1 : rd8 T.klev v = 1
    · rw [h1 hl1]
      exact MulAction.mem_orbit_self _
    · obtain ⟨hp, hg, hlp, himg⟩ := hpar hl1
      have hpl : rd8 T.klev (rd32 T.kpar v) ≠ 0 := by omega
      have ihp := ih _ (by omega) _ hp hpl rfl
      rw [← himg, hk _ hg]
      exact smul_mem_orbit_closure (S := kGen '' Set.Iio 15) (Set.mem_image_of_mem kGen hg) ihp

theorem label_mem (hF : FrameFacts T) {v : ℕ} (hv : v < 2 ^ 24) (hl : rd8 T.klev v ≠ 0) :
    1 ≤ rd8 T.olab v ∧ rd8 T.olab v ≤ 6 :=
  ⟨(pointOK_spec (hF.point v hv) hl).2.2.1, (pointOK_spec (hF.point v hv) hl).2.2.2.1⟩

theorem mem_orbit_N (hF : FrameFacts T) (hk : ∀ g < 15, ∀ p, dec (gimg g p) = kGen g • dec p) :
    ∀ v < 2 ^ 24, rd8 T.klev v ≠ 0 →
      dec v ∈ MulAction.orbit (Subgroup.closure (kGen '' Set.Ico 1 15))
        (dec frameReps[rd8 T.olab v - 1]!) := by
  intro v hv hl
  induction hlev : rd8 T.nlev v using Nat.strong_induction_on generalizing v with
  | _ l ih =>
    obtain ⟨-, -, -, -, -, h1, hpar⟩ := pointOK_spec (hF.point v hv) hl
    by_cases hl1 : rd8 T.nlev v = 1
    · rw [← h1 hl1]
      exact MulAction.mem_orbit_self _
    · obtain ⟨hn0, hp, hg1, hg, hpk, hpo, hlp, himg⟩ := hpar hl1
      have ihp := ih _ (by omega) _ hp hpk rfl
      rw [hpo] at ihp
      have e := hk _ hg (rd32 T.npar v)
      rw [himg] at e
      rw [e]
      exact smul_mem_orbit_closure (S := kGen '' Set.Ico 1 15)
        (Set.mem_image_of_mem kGen ⟨hg1, hg⟩) ihp

theorem gimg_mem_labelSet (hF : FrameFacts T) {o : ℕ} {v : ℕ} (hv : v ∈ labelSet T o) {j : ℕ}
    (hj1 : 1 ≤ j) (hj : j < 15) : gimg j v ∈ labelSet T o := by
  simp only [labelSet, Finset.mem_filter, Finset.mem_range] at hv ⊢
  obtain ⟨hv, hl, ho⟩ := hv
  obtain ⟨-, -, -, -, hcl, -⟩ := pointOK_spec (hF.point v hv) hl
  obtain ⟨hwl, hwo⟩ := hcl j hj1 hj
  exact ⟨gimg_lt hj v, hwl, hwo.trans ho⟩

theorem labelSet_subset_foundSet (o : ℕ) : labelSet T o ⊆ foundSet T := by
  intro v hv
  simp only [labelSet, foundSet, Finset.mem_filter] at hv ⊢
  exact ⟨hv.1, hv.2.1⟩

theorem rep_mem_labelSet (hF : FrameFacts T) {o : ℕ} (h1 : 1 ≤ o) (h6 : o ≤ 6) :
    frameReps[o - 1]! ∈ labelSet T o := by
  obtain ⟨hr, hk', ho⟩ := hF.rep o h1 h6
  simp only [labelSet, Finset.mem_filter, Finset.mem_range]
  exact ⟨hr, hk', ho⟩

theorem mem_labelSet_of_mem_foundSet {v : ℕ} (hv : v ∈ foundSet T) :
    v ∈ labelSet T (rd8 T.olab v) := by
  simp only [labelSet, foundSet, Finset.mem_filter, Finset.mem_range] at hv ⊢
  exact ⟨hv.1, hv.2, trivial⟩

theorem injOn_dec (hdec : ∀ a b, a < 2 ^ 24 → b < 2 ^ 24 → dec a = dec b → a = b)
    (s : Finset ℕ) (hs : s ⊆ Finset.range (2 ^ 24)) : Set.InjOn dec (s : Set ℕ) :=
  fun a ha b hb hab => hdec a b (Finset.mem_range.1 (hs ha)) (Finset.mem_range.1 (hs hb)) hab

theorem orbit_N_eq (hF : FrameFacts T) (hk : ∀ g < 15, ∀ p, dec (gimg g p) = kGen g • dec p)
    {o : ℕ} (h1 : 1 ≤ o) (h6 : o ≤ 6) :
    MulAction.orbit (Subgroup.closure (kGen '' Set.Ico 1 15)) (dec frameReps[o - 1]!) =
      dec '' (labelSet T o : Set ℕ) := by
  refine Set.Subset.antisymm (orbit_closure_subset ((labelSet T o).finite_toSet.image dec) ?_
    ⟨_, hF.rep_mem_labelSet h1 h6, rfl⟩) ?_
  · rintro _ ⟨j, ⟨hj1, hj⟩, rfl⟩ _ ⟨v, hv, rfl⟩
    exact ⟨gimg j v, hF.gimg_mem_labelSet hv hj1 hj, hk j hj v⟩
  · rintro _ ⟨v, hv, rfl⟩
    have hv' : v ∈ labelSet T o := hv
    simp only [labelSet, Finset.mem_filter, Finset.mem_range] at hv'
    obtain ⟨hv24, hl, ho⟩ := hv'
    have := hF.mem_orbit_N hk v hv24 hl
    rwa [ho] at this

theorem ncard_orbit_N (hF : FrameFacts T) (hk : ∀ g < 15, ∀ p, dec (gimg g p) = kGen g • dec p)
    (hdec : ∀ a b, a < 2 ^ 24 → b < 2 ^ 24 → dec a = dec b → a = b) {o : ℕ} (h1 : 1 ≤ o)
    (h6 : o ≤ 6) :
    (MulAction.orbit (Subgroup.closure (kGen '' Set.Ico 1 15)) (dec frameReps[o - 1]!)).ncard =
      frameSizes[o - 1]! := by
  rw [hF.orbit_N_eq hk h1 h6,
    (injOn_dec hdec (labelSet T o) (Finset.filter_subset _ _)).ncard_image, Set.ncard_coe_finset,
    hF.card_label o h1 h6]

theorem image_foundSet_subset_orbit_K (hF : FrameFacts T)
    (hk : ∀ g < 15, ∀ p, dec (gimg g p) = kGen g • dec p) :
    dec '' (foundSet T : Set ℕ) ⊆
      MulAction.orbit (Subgroup.closure (kGen '' Set.Iio 15)) (dec frameSeed) := by
  rintro _ ⟨v, hv, rfl⟩
  have hv' : v ∈ foundSet T := hv
  simp only [foundSet, Finset.mem_filter, Finset.mem_range] at hv'
  exact hF.mem_orbit_K hk v hv'.1 hv'.2

theorem ncard_image_foundSet (hF : FrameFacts T)
    (hdec : ∀ a b, a < 2 ^ 24 → b < 2 ^ 24 → dec a = dec b → a = b) :
    (dec '' (foundSet T : Set ℕ)).ncard = deltaCount := by
  rw [(injOn_dec hdec (foundSet T) (Finset.filter_subset _ _)).ncard_image, Set.ncard_coe_finset,
    hF.card_found]

theorem image_foundSet_eq_iUnion (hF : FrameFacts T)
    (hk : ∀ g < 15, ∀ p, dec (gimg g p) = kGen g • dec p) :
    dec '' (foundSet T : Set ℕ) = ⋃ o ∈ Set.Icc 1 6,
      MulAction.orbit (Subgroup.closure (kGen '' Set.Ico 1 15)) (dec frameReps[o - 1]!) := by
  ext x
  simp only [Set.mem_image, Set.mem_iUnion, Set.mem_Icc, exists_prop]
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hv' : v ∈ foundSet T := hv
    have hm := mem_labelSet_of_mem_foundSet hv'
    simp only [foundSet, Finset.mem_filter, Finset.mem_range] at hv'
    obtain ⟨h1, h6⟩ := hF.label_mem hv'.1 hv'.2
    refine ⟨_, ⟨h1, h6⟩, ?_⟩
    rw [hF.orbit_N_eq hk h1 h6]
    exact ⟨v, hm, rfl⟩
  · rintro ⟨o, ⟨h1, h6⟩, hx⟩
    rw [hF.orbit_N_eq hk h1 h6] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    exact ⟨v, labelSet_subset_foundSet o hv, rfl⟩

theorem disjoint_orbit_N (hF : FrameFacts T) (hk : ∀ g < 15, ∀ p, dec (gimg g p) = kGen g • dec p)
    (hdec : ∀ a b, a < 2 ^ 24 → b < 2 ^ 24 → dec a = dec b → a = b) {o o' : ℕ} (h1 : 1 ≤ o)
    (h6 : o ≤ 6) (h1' : 1 ≤ o') (h6' : o' ≤ 6) (hne : o ≠ o') :
    Disjoint (MulAction.orbit (Subgroup.closure (kGen '' Set.Ico 1 15)) (dec frameReps[o - 1]!))
      (MulAction.orbit (Subgroup.closure (kGen '' Set.Ico 1 15)) (dec frameReps[o' - 1]!)) := by
  rw [hF.orbit_N_eq hk h1 h6, hF.orbit_N_eq hk h1' h6', Set.disjoint_left]
  rintro _ ⟨v, hv, rfl⟩ ⟨w, hw, hvw⟩
  have hv' : v ∈ labelSet T o := hv
  have hw' : w ∈ labelSet T o' := hw
  simp only [labelSet, Finset.mem_filter, Finset.mem_range] at hv' hw'
  have := hdec w v hw'.1 hv'.1 hvw
  subst this
  exact hne (hv'.2.2.symm.trans hw'.2.2)

end FrameFacts

end Orbits

end CFSG.Monster.VisCert
