module

public import CFSG.Quasithin.Vol2.GoldschmidtF431F45Abstract
public import CFSG.Quasithin.Recognition.Stroth.RootGroupRegular

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Quasithin CFSG.GH74.BNPair

section Apartment

variable {V : Type} [Fintype V] {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
  {n : ℕ} {D : Type} [Group D] [MulAction D V] [FaithfulSMul D V] [GraphAction D Γ]

@[expose] def apt (t : ZMod (2 * n) → V) (k : ℤ) : V := t k

theorem apt_adj {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (k : ℤ) :
    Γ.Adj (apt t k) (apt t (k + 1)) := by
  have h := ht.2 (k : ZMod (2 * n))
  have e : ((k + 1 : ℤ) : ZMod (2 * n)) = ((k : ℤ) : ZMod (2 * n)) + 1 := by
    push_cast
    ring
  show Γ.Adj (t ((k : ℤ) : ZMod (2 * n))) (t ((k + 1 : ℤ) : ZMod (2 * n)))
  rw [e]
  exact h

theorem apt_injective {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    {a b : ZMod (2 * n)} (h : t a = t b) : a = b :=
  ht.1 h

private theorem two_ne_zero_zmod (hn : 2 ≤ n) : (2 : ZMod (2 * n)) ≠ 0 := by
  intro h
  have hd : 2 * n ∣ 2 := (ZMod.natCast_eq_zero_iff 2 (2 * n)).mp h
  have := Nat.le_of_dvd (by norm_num) hd
  omega

theorem apt_ne_two {t : ZMod (2 * n) → V} (hn : 2 ≤ n) (ht : IsPolygonApartment Γ n t)
    (k : ℤ) : apt t k ≠ apt t (k + 2) := by
  intro h
  have h' : ((k : ℤ) : ZMod (2 * n)) = ((k + 2 : ℤ) : ZMod (2 * n)) := apt_injective ht h
  rw [show ((k + 2 : ℤ) : ZMod (2 * n)) = ((k : ℤ) : ZMod (2 * n)) + 2 by push_cast; ring] at h'
  have h2 : (2 : ZMod (2 * n)) = 0 := by
    have h3 : ((k : ℤ) : ZMod (2 * n)) + 2 = ((k : ℤ) : ZMod (2 * n)) + 0 := by
      rw [add_zero]
      exact h'.symm
    exact add_left_cancel h3
  exact two_ne_zero_zmod hn h2

theorem apt_add_two_mul {t : ZMod (2 * n) → V} (k : ℤ) (c : ℤ) :
    apt t (k + 2 * (n : ℤ) * c) = apt t k := by
  have h : ((2 : ZMod (2 * n)) * ((n : ℤ) : ZMod (2 * n))) = 0 := by
    have h2 := ZMod.natCast_self (2 * n)
    push_cast at h2
    simpa using h2
  show t (((k + 2 * (n : ℤ) * c : ℤ)) : ZMod (2 * n)) = t ((k : ℤ) : ZMod (2 * n))
  have e : ((k + 2 * (n : ℤ) * c : ℤ) : ZMod (2 * n)) =
      ((k : ℤ) : ZMod (2 * n)) +
        ((2 : ZMod (2 * n)) * ((n : ℤ) : ZMod (2 * n))) * ((c : ℤ) : ZMod (2 * n)) := by
    push_cast
    ring
  rw [e, h, zero_mul, add_zero]

end Apartment

section Paths

variable {V : Type} [Fintype V] {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
  {n : ℕ} {t : ZMod (2 * n) → V}

@[expose] def aptPath (hadj : ∀ k : ZMod (2 * n), Γ.Adj (t k) (t (k + 1))) (k : ℤ) : GPath Γ n where
  toFun i := apt t (k + min (i : ℤ) (n : ℤ))
  adj i hi := by
    have h1 : min ((i : ℕ) : ℤ) (n : ℤ) = (i : ℤ) := min_eq_left (by omega)
    have h2 : min (((i + 1 : ℕ)) : ℤ) (n : ℤ) = ((i + 1 : ℕ) : ℤ) := min_eq_left (by omega)
    rw [h1, h2]
    show Γ.Adj (t (((k + (i : ℤ)) : ℤ) : ZMod (2 * n)))
      (t (((k + ((i + 1 : ℕ) : ℤ)) : ℤ) : ZMod (2 * n)))
    rw [show ((i + 1 : ℕ) : ℤ) = (i : ℤ) + 1 by push_cast; ring]
    rw [show ((k + ((i : ℤ) + 1) : ℤ) : ZMod (2 * n)) = ((k + (i : ℤ) : ℤ) : ZMod (2 * n)) + 1 by
      push_cast; ring]
    exact hadj _
  tail i hi := by
    have h1 : min (i : ℤ) (n : ℤ) = n := by
      rw [min_eq_right (show (n : ℤ) ≤ (i : ℤ) by omega)]
    rw [h1, min_self]

@[expose] def aptPathRev (hadj : ∀ k : ZMod (2 * n), Γ.Adj (t k) (t (k + 1))) (k : ℤ) :
    GPath Γ n where
  toFun i := apt t (k + (n : ℤ) - min (i : ℤ) (n : ℤ))
  adj i hi := by
    have h1 : min ((i : ℕ) : ℤ) (n : ℤ) = (i : ℤ) := min_eq_left (by omega)
    have h2 : min (((i + 1 : ℕ)) : ℤ) (n : ℤ) = ((i + 1 : ℕ) : ℤ) := min_eq_left (by omega)
    rw [h1, h2]
    show Γ.Adj (t (((k + (n : ℤ) - (i : ℤ)) : ℤ) : ZMod (2 * n)))
      (t (((k + (n : ℤ) - ((i + 1 : ℕ) : ℤ)) : ℤ) : ZMod (2 * n)))
    rw [show ((i + 1 : ℕ) : ℤ) = (i : ℤ) + 1 by push_cast; ring]
    rw [show (((k + (n : ℤ) - (i : ℤ)) : ℤ) : ZMod (2 * n)) =
      (((k + (n : ℤ) - ((i : ℤ) + 1)) : ℤ) : ZMod (2 * n)) + 1 by push_cast; ring]
    exact (hadj _).symm
  tail i hi := by
    have h1 : min (i : ℤ) (n : ℤ) = n := by
      rw [min_eq_right (show (n : ℤ) ≤ (i : ℤ) by omega)]
    rw [h1, min_self]

@[simp] theorem aptPath_apply (hadj : ∀ k : ZMod (2 * n), Γ.Adj (t k) (t (k + 1))) (k : ℤ)
    {i : ℕ} (hi : i ≤ n) : aptPath hadj k i = apt t (k + (i : ℤ)) := by
  show apt t (k + min (i : ℤ) (n : ℤ)) = apt t (k + (i : ℤ))
  rw [min_eq_left (by omega)]

@[simp] theorem aptPathRev_apply (hadj : ∀ k : ZMod (2 * n), Γ.Adj (t k) (t (k + 1))) (k : ℤ)
    {i : ℕ} (hi : i ≤ n) : aptPathRev hadj k i = apt t (k + (n : ℤ) - (i : ℤ)) := by
  show apt t (k + (n : ℤ) - min (i : ℤ) (n : ℤ)) = apt t (k + (n : ℤ) - (i : ℤ))
  rw [min_eq_left (by omega)]

@[expose] def aptSeg (hadj : ∀ k : ZMod (2 * n), Γ.Adj (t k) (t (k + 1))) (k : ℤ) (m : ℕ)
    (hm : m ≤ n) : GPath Γ m :=
  (aptPath hadj k).take m hm

@[expose] def aptSegRev (hadj : ∀ k : ZMod (2 * n), Γ.Adj (t k) (t (k + 1))) (k : ℤ) (m : ℕ)
    (hm : m ≤ n) : GPath Γ m :=
  (aptPathRev hadj (k - (n : ℤ))).take m hm

@[simp] theorem aptSeg_apply (hadj : ∀ k : ZMod (2 * n), Γ.Adj (t k) (t (k + 1))) (k : ℤ)
    {m : ℕ} (hm : m ≤ n) {i : ℕ} (hi : i ≤ m) : aptSeg hadj k m hm i = apt t (k + (i : ℤ)) := by
  rw [aptSeg, GPath.take_apply_of_le _ _ _ hi, aptPath_apply hadj k (by omega)]

@[simp] theorem aptSegRev_apply (hadj : ∀ k : ZMod (2 * n), Γ.Adj (t k) (t (k + 1))) (k : ℤ)
    {m : ℕ} (hm : m ≤ n) {i : ℕ} (hi : i ≤ m) :
    aptSegRev hadj k m hm i = apt t (k - (i : ℤ)) := by
  rw [aptSegRev, GPath.take_apply_of_le _ _ _ hi]
  rw [aptPathRev_apply hadj (k - (n : ℤ)) (by omega)]
  rw [show k - (n : ℤ) + (n : ℤ) - (i : ℤ) = k - (i : ℤ) by ring]

theorem aptPath_noBack (hn : 2 ≤ n) (ht : IsPolygonApartment Γ n t) (k : ℤ) :
    (aptPath ht.2 k).NoBack := by
  intro i hi heq
  rw [aptPath_apply ht.2 k (by omega), aptPath_apply ht.2 k (by omega)] at heq
  refine apt_ne_two hn ht (k + (i : ℤ)) ?_
  rwa [show k + ((i + 2 : ℕ) : ℤ) = (k + (i : ℤ)) + 2 by push_cast; ring] at heq

theorem aptPathRev_noBack (hn : 2 ≤ n) (ht : IsPolygonApartment Γ n t) (k : ℤ) :
    (aptPathRev ht.2 k).NoBack := by
  intro i hi heq
  rw [aptPathRev_apply ht.2 k (by omega), aptPathRev_apply ht.2 k (by omega)] at heq
  refine apt_ne_two hn ht (k + (n : ℤ) - ((i + 2 : ℕ) : ℤ)) ?_
  have e : (k + (n : ℤ) - ((i + 2 : ℕ) : ℤ)) + 2 = k + (n : ℤ) - (i : ℤ) := by
    push_cast
    ring
  rw [← e] at heq
  exact heq.symm

theorem aptSeg_noBack (hn : 2 ≤ n) (ht : IsPolygonApartment Γ n t) (k : ℤ) {m : ℕ}
    (hm : m ≤ n) : (aptSeg ht.2 k m hm).NoBack :=
  (aptPath_noBack hn ht k).take m hm

theorem aptSegRev_noBack (hn : 2 ≤ n) (ht : IsPolygonApartment Γ n t) (k : ℤ) {m : ℕ}
    (hm : m ≤ n) : (aptSegRev ht.2 k m hm).NoBack :=
  (aptPathRev_noBack hn ht (k - (n : ℤ))).take m hm

end Paths

section RootGroup

variable {V : Type} [Fintype V] {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
  {n : ℕ} {D : Type} [Group D] [MulAction D V] [FaithfulSMul D V] [GraphAction D Γ]

theorem mem_aptRoot {t : ZMod (2 * n) → V} {g : D} {k : ℤ} :
    g ∈ aptRoot D Γ n t k ↔
      ∀ i : ℤ, 1 ≤ i → i ≤ (n : ℤ) - 1 → ∀ w : V, Γ.Adj (apt t (k + i)) w → g • w = w := by
  simp only [aptRoot, apt, Subgroup.mem_iInf, mem_fixingSubgroup_iff, Set.mem_Icc,
    SimpleGraph.mem_neighborSet]
  exact ⟨fun h i h1 h2 => h i ⟨h1, h2⟩, fun h i hi => h i hi.1 hi.2⟩

theorem aptRoot_eq_pathRootGroup {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (k : ℤ) :
    aptRoot D Γ n t k = pathRootGroup D Γ (aptPath ht.2 k) := by
  refine Subgroup.ext fun g => ?_
  rw [mem_aptRoot, mem_pathRootGroup]
  constructor
  · intro h i hi1 hi2 w hw
    refine h (i : ℤ) (by omega) (by omega) w ?_
    rwa [aptPath_apply ht.2 k (by omega)] at hw
  · intro h j hj1 hj2 w hw
    have hj0 : (0 : ℤ) ≤ j := by omega
    have hcast : (((j.toNat : ℕ)) : ℤ) = j := Int.toNat_of_nonneg hj0
    have hi2 : j.toNat ≤ n - 1 := by omega
    have hpath : aptPath ht.2 k j.toNat = apt t (k + j) := by
      rw [aptPath_apply ht.2 k (by omega), hcast]
    refine h j.toNat (by omega) hi2 w ?_
    rw [hpath]
    exact hw

theorem aptRoot_eq_pathRootGroupRev {t : ZMod (2 * n) → V} (hn : 2 ≤ n)
    (ht : IsPolygonApartment Γ n t) (k : ℤ) :
    aptRoot D Γ n t k = pathRootGroup D Γ (aptPathRev ht.2 k) := by
  refine Subgroup.ext fun g => ?_
  rw [mem_aptRoot, mem_pathRootGroup]
  constructor
  · intro h i hi1 hi2 w hw
    rw [aptPathRev_apply ht.2 k (by omega)] at hw
    refine h ((n : ℤ) - (i : ℤ)) (by omega) (by omega) w ?_
    rwa [show k + ((n : ℤ) - (i : ℤ)) = k + (n : ℤ) - (i : ℤ) by ring]
  · intro h j hj1 hj2 w hw
    have h0 : (0 : ℤ) ≤ (n : ℤ) - j := by omega
    have hcast : ((((n : ℤ) - j).toNat : ℕ) : ℤ) = (n : ℤ) - j := Int.toNat_of_nonneg h0
    have hi1 : 1 ≤ ((n : ℤ) - j).toNat := by
      have h3 : (1 : ℤ) ≤ ((((n : ℤ) - j).toNat : ℕ) : ℤ) := by rw [hcast]; omega
      exact_mod_cast h3
    have hi2 : ((n : ℤ) - j).toNat ≤ n - 1 := by
      have h3 : ((((n : ℤ) - j).toNat : ℕ) : ℤ) ≤ ((n - 1 : ℕ) : ℤ) := by
        rw [hcast, show ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 by
          rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num]
        omega
      exact_mod_cast h3
    refine h ((n : ℤ) - j).toNat hi1 hi2 w ?_
    rw [aptPathRev_apply ht.2 k (by omega), hcast]
    rwa [show k + (n : ℤ) - ((n : ℤ) - j) = k + j by ring]

theorem aptRoot_smul_of_adj {t : ZMod (2 * n) → V} {g : D} {k : ℤ}
    (hg : g ∈ aptRoot D Γ n t k) {i : ℤ} (h1 : 1 ≤ i) (h2 : i ≤ (n : ℤ) - 1) {w : V}
    (hw : Γ.Adj (apt t (k + i)) w) : g • w = w :=
  (mem_aptRoot.mp hg) i h1 h2 w hw

theorem aptRoot_fix_of_adj {t : ZMod (2 * n) → V} {g : D} {k : ℤ}
    (hg : g ∈ aptRoot D Γ n t k) {x y : ℤ} (hy1 : k + 1 ≤ y) (hy2 : y ≤ k + (n : ℤ) - 1)
    (hadj : Γ.Adj (apt t y) (apt t x)) : g • apt t x = apt t x := by
  refine aptRoot_smul_of_adj hg (i := y - k) (by omega) (by omega) ?_
  rwa [show k + (y - k) = y by ring]

theorem aptRoot_fix {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) {g : D} {k : ℤ}
    (hg : g ∈ aptRoot D Γ n t k) (hn : 3 ≤ n) {r : ℤ} (h0 : 0 ≤ r) (hr : r ≤ (n : ℤ)) :
    g • apt t (k + r) = apt t (k + r) := by
  rcases eq_or_lt_of_le h0 with h | h
  · have hr0 : r = 0 := h.symm
    subst hr0
    have hadj : Γ.Adj (apt t (k + 1)) (apt t (k + 0)) := by
      simpa using (apt_adj ht (k + 0)).symm
    exact aptRoot_fix_of_adj hg (by omega) (by omega) hadj
  rcases eq_or_lt_of_le hr with h2 | h2
  · have hrn : r = n := h2
    subst hrn
    have hadj : Γ.Adj (apt t (k + (n : ℤ) - 1)) (apt t (k + (n : ℤ))) := by
      simpa using apt_adj ht (k + (n : ℤ) - 1)
    exact aptRoot_fix_of_adj hg (by omega) (by omega) hadj
  · by_cases h3 : r + 1 ≤ (n : ℤ) - 1
    · have hadj : Γ.Adj (apt t (k + (r + 1))) (apt t (k + r)) := by
        have h := (apt_adj ht (k + r)).symm
        rwa [show k + r + 1 = k + (r + 1) by ring] at h
      exact aptRoot_fix_of_adj hg (by omega) (by omega) hadj
    · have hr' : r = (n : ℤ) - 1 := by omega
      subst hr'
      have hadj : Γ.Adj (apt t (k + ((n : ℤ) - 1) - 1)) (apt t (k + ((n : ℤ) - 1))) := by
        simpa using apt_adj ht (k + ((n : ℤ) - 1) - 1)
      exact aptRoot_fix_of_adj hg (by omega) (by omega) hadj

theorem aptRoot_eq_one_of_fix_adj {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    {g : D} {k : ℤ} (hg : g ∈ aptRoot D Γ n t k) (hn : 3 ≤ n)
    (hP : CFSG.Geometry.GeneralizedPolygons.IsGeneralizedPolygon Γ n)
    (hT : CFSG.Geometry.GeneralizedPolygons.IsThick Γ) {w : V}
    (hw : Γ.Adj (apt t (k + (n : ℤ))) w) (hw' : w ≠ apt t (k + (n : ℤ) - 1))
    (hgw : g • w = w) : g = 1 := by
  have hpn : aptPath ht.2 k n = apt t (k + (n : ℤ)) := aptPath_apply ht.2 k le_rfl
  have hpnm : aptPath ht.2 k (n - 1) = apt t (k + (n : ℤ) - 1) := by
    rw [aptPath_apply ht.2 k (by omega)]
    rw [show ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num]
    rw [show k + ((n : ℤ) - 1) = k + (n : ℤ) - 1 by ring]
  refine pathRootGroup_eq_one_of_fix hn hP hT (aptPath_noBack (by omega) ht k) ?_
    (by rwa [hpn]) (by rwa [hpnm]) hgw
  rwa [← aptRoot_eq_pathRootGroup ht k]

theorem aptRoot_exists_smul_of_adj {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hM : MoufangCondition D Γ n) {k : ℤ} {y y' : V}
    (hy : Γ.Adj (apt t (k + (n : ℤ))) y) (hy' : Γ.Adj (apt t (k + (n : ℤ))) y')
    (hne : y ≠ apt t (k + (n : ℤ) - 1)) (hne' : y' ≠ apt t (k + (n : ℤ) - 1)) :
    ∃ g ∈ aptRoot D Γ n t k, g • y = y' := by
  have hp : (aptPath ht.2 k).NoBack := aptPath_noBack (by omega) ht k
  have hpn : aptPath ht.2 k n = apt t (k + (n : ℤ)) := aptPath_apply ht.2 k le_rfl
  have hpnm : aptPath ht.2 k (n - 1) = apt t (k + (n : ℤ) - 1) := by
    rw [aptPath_apply ht.2 k (by omega)]
    rw [show ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num]
    rw [show k + ((n : ℤ) - 1) = k + (n : ℤ) - 1 by ring]
  obtain ⟨g, hfix, hgy⟩ := hM (aptPath ht.2 k) hp y y' (by rwa [hpn]) (by rwa [hpn])
    (by rwa [hpnm]) (by rwa [hpnm])
  refine ⟨g, ?_, hgy⟩
  refine mem_aptRoot.mpr fun i hi1 hi2 w hw => ?_
  have hi0 : (0 : ℤ) ≤ i := by omega
  have hcast : ((i.toNat : ℕ) : ℤ) = i := by rw [Int.toNat_of_nonneg hi0]
  have hI2 : i.toNat ≤ n - 1 := by omega
  have hpath : aptPath ht.2 k i.toNat = apt t (k + i) := by
    rw [aptPath_apply ht.2 k (by omega), hcast]
  refine hfix i.toNat (by omega) hI2 w ?_
  rwa [hpath]

theorem aptRoot_exists_smul_of_adj_start {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hM : MoufangCondition D Γ n) {k : ℤ} {y y' : V}
    (hy : Γ.Adj (apt t k) y) (hy' : Γ.Adj (apt t k) y') (hne : y ≠ apt t (k + 1))
    (hne' : y' ≠ apt t (k + 1)) : ∃ g ∈ aptRoot D Γ n t k, g • y = y' := by
  have hp : (aptPathRev ht.2 k).NoBack := aptPathRev_noBack (by omega) ht k
  have hlast : aptPathRev ht.2 k n = apt t k := by
    rw [aptPathRev_apply ht.2 k le_rfl]
    rw [show k + (n : ℤ) - (n : ℤ) = k by ring]
  have hpen : aptPathRev ht.2 k (n - 1) = apt t (k + 1) := by
    rw [aptPathRev_apply ht.2 k (by omega)]
    rw [show ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num]
    rw [show k + (n : ℤ) - ((n : ℤ) - 1) = k + 1 by ring]
  have hy2 : Γ.Adj (aptPathRev ht.2 k n) y := by rwa [hlast]
  have hy2' : Γ.Adj (aptPathRev ht.2 k n) y' := by rwa [hlast]
  obtain ⟨g, hfix, hgy⟩ := hM (aptPathRev ht.2 k) hp y y' hy2 hy2'
    (by rwa [hpen]) (by rwa [hpen])
  refine ⟨g, ?_, hgy⟩
  refine mem_aptRoot.mpr fun i hi1 hi2 w hw => ?_
  have hi0 : (0 : ℤ) ≤ i := by omega
  have hcast : (((n : ℤ) - i).toNat : ℤ) = (n : ℤ) - i := by
    rw [Int.toNat_of_nonneg]
    omega
  have hI2 : ((n : ℤ) - i).toNat ≤ n - 1 := by omega
  have hpath : aptPathRev ht.2 k ((n : ℤ) - i).toNat = apt t (k + i) := by
    rw [aptPathRev_apply ht.2 k (by omega), hcast]
    rw [show k + (n : ℤ) - ((n : ℤ) - i) = k + i by ring]
  refine hfix ((n : ℤ) - i).toNat (by omega) hI2 w ?_
  rwa [hpath]

theorem conj_mem_aptRoot_iff {t : ZMod (2 * n) → V} (g x : D) (k : ℤ) :
    g⁻¹ * x * g ∈ aptRoot D Γ n t k ↔ x ∈ aptRoot D Γ n (fun j => g • t j) k := by
  have hconv : ∀ w : V, (g⁻¹ * x * g) • w = g⁻¹ • (x • (g • w)) := by
    intro w
    rw [mul_smul, mul_smul]
  rw [mem_aptRoot, mem_aptRoot]
  constructor
  · intro h i hi1 hi2 w hw
    have hAdj : Γ.Adj (apt t (k + i)) (g⁻¹ • w) := by
      have h := (GraphAction.adj_smul (Γ := Γ) g (apt t (k + i)) (g⁻¹ • w)).mp ?_
      · exact h
      · rw [smul_inv_smul]
        exact hw
    have hfix := h i hi1 hi2 (g⁻¹ • w) hAdj
    rw [hconv] at hfix
    have := congrArg (fun v => g • v) hfix
    simpa using this
  · intro h i hi1 hi2 w hw
    have hAdj : Γ.Adj (apt (fun j => g • t j) (k + i)) (g • w) := by
      have h := (GraphAction.adj_smul (Γ := Γ) g (apt t (k + i)) w).mpr hw
      rwa [show g • apt t (k + i) = apt (fun j => g • t j) (k + i) from rfl] at h
    have hfix := h i hi1 hi2 (g • w) hAdj
    rw [hconv, hfix, inv_smul_smul]

theorem aptRoot_map_conj {t : ZMod (2 * n) → V} (g : D) (k : ℤ) :
    (aptRoot D Γ n t k).map (MulAut.conj g).toMonoidHom =
      aptRoot D Γ n (fun j => g • t j) k := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have e : g⁻¹ * (MulAut.conj g y) * g = y := by
      rw [MulAut.conj_apply]
      group
    refine (conj_mem_aptRoot_iff (g := g) (x := MulAut.conj g y) (k := k)).mp ?_
    rwa [e]
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · exact (conj_mem_aptRoot_iff (g := g) (x := x) (k := k)).mpr hx
    · show (MulAut.conj g) (g⁻¹ * x * g) = x
      rw [MulAut.conj_apply]
      group

theorem fix_of_smul_ends {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : CFSG.Geometry.GeneralizedPolygons.IsGeneralizedPolygon Γ n)
    (hT : CFSG.Geometry.GeneralizedPolygons.IsThick Γ) {g : D} {a : ℤ}
    (h0 : g • apt t a = apt t a) (h1 : g • apt t (a + (n : ℤ) - 1) = apt t (a + (n : ℤ) - 1))
    {r : ℕ} (hr : r ≤ n - 1) : g • apt t (a + (r : ℤ)) = apt t (a + (r : ℤ)) := by
  have hm : n - 1 ≤ n := by omega
  have hcast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  let p : GPath Γ (n - 1) := aptSeg ht.2 a (n - 1) hm
  have hp0 : p 0 = apt t a := by
    show (aptSeg ht.2 a (n - 1) hm).toFun 0 = apt t a
    rw [aptSeg_apply ht.2 a hm (i := 0) (by omega)]
    norm_num
  have hpl : p (n - 1) = apt t (a + (n : ℤ) - 1) := by
    show (aptSeg ht.2 a (n - 1) hm).toFun (n - 1) = apt t (a + (n : ℤ) - 1)
    rw [aptSeg_apply ht.2 a hm (i := n - 1) (by omega), hcast]
    rw [show a + ((n : ℤ) - 1) = a + (n : ℤ) - 1 by ring]
  have hgp' : IsGenPolygon Γ n := isGenPolygon_of_isGeneralizedPolygon (by omega) hP hT
  have hp : p.IsGeodesic :=
    CFSG.Quasithin.H13.F431.F45.nb_dist hgp' hm p (aptSeg_noBack (by omega) ht a hm)
  have hgp : (g • p).IsGeodesic := by
    show Γ.dist ((g • p) 0) ((g • p) (n - 1)) = n - 1
    rw [GPath.smul_apply, GPath.smul_apply, GPath.dist_smul hP.connected]
    exact hp
  have hs0 : (g • p) 0 = p 0 := by
    rw [GPath.smul_apply, hp0, h0]
  have hsl : (g • p) (n - 1) = p (n - 1) := by
    rw [GPath.smul_apply, hpl, h1]
  have heq : g • p = p := hgp'.uniqueGeod (n - 1) (g • p) p hgp hp hs0 hsl (by omega)
  have h := congrArg (fun q : GPath Γ (n - 1) => q r) heq
  rw [GPath.smul_apply] at h
  have hpr : p r = apt t (a + (r : ℤ)) := aptSeg_apply ht.2 a hm hr
  rw [hpr] at h
  exact h

theorem commutator_smul_eq {a b : D} {x : V} (ha : ∀ z : V, Γ.Adj x z → a • z = z)
    (hb : b • x = x) {y : V} (hy : Γ.Adj x y) : (a * b * a⁻¹ * b⁻¹) • y = y := by
  have ha' : ∀ z : V, Γ.Adj x z → a⁻¹ • z = z := by
    intro z hz
    calc a⁻¹ • z = a⁻¹ • (a • z) := by rw [ha z hz]
      _ = z := inv_smul_smul a z
  have hb' : b⁻¹ • x = x := by
    have := congrArg (fun v => b⁻¹ • v) hb
    simpa using this.symm
  have hy' : Γ.Adj x (b⁻¹ • y) := by
    have := (GraphAction.adj_smul b⁻¹ x y).mpr hy
    rwa [hb'] at this
  have e : (a * b * a⁻¹ * b⁻¹) • y = a • (b • (a⁻¹ • (b⁻¹ • y))) := by
    simp only [mul_smul]
  rw [e, ha' (b⁻¹ • y) hy', smul_inv_smul]
  exact ha y hy

theorem commutator_smul_eq_right {a b : D} {x : V} (ha : a • x = x)
    (hb : ∀ z : V, Γ.Adj x z → b • z = z) {y : V} (hy : Γ.Adj x y) :
    (a * b * a⁻¹ * b⁻¹) • y = y := by
  have h := commutator_smul_eq (a := b) (b := a) hb ha hy
  have h' : (a * b * a⁻¹ * b⁻¹)⁻¹ • y = y := by
    have e : (a * b * a⁻¹ * b⁻¹)⁻¹ = b * a * b⁻¹ * a⁻¹ := by group
    rw [e]
    exact h
  have e : (a * b * a⁻¹ * b⁻¹) • y =
      (a * b * a⁻¹ * b⁻¹) • ((a * b * a⁻¹ * b⁻¹)⁻¹ • y) := by rw [h']
  rw [e, ← mul_smul, mul_inv_cancel, one_smul]

theorem eq_one_of_fix_apartment_stars {t : ZMod (2 * n) → V}
    (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : CFSG.Geometry.GeneralizedPolygons.IsGeneralizedPolygon Γ n)
    (hT : CFSG.Geometry.GeneralizedPolygons.IsThick Γ) {g : D}
    (hfix : ∀ r : ℤ, g • apt t r = apt t r) {c : ℤ}
    (h0 : ∀ w : V, Γ.Adj (apt t c) w → g • w = w)
    (h1 : ∀ w : V, Γ.Adj (apt t (c + 1)) w → g • w = w) : g = 1 := by
  have hgp : IsGenPolygon Γ n := isGenPolygon_of_isGeneralizedPolygon (by omega) hP hT
  have hT' : ∀ v : V, 3 ≤ (Γ.neighborSet v).encard := three_le_encard_of_isThick hT
  have hzadj : ∀ k : ℕ, Γ.Adj (apt t (c + (k : ℤ))) (apt t (c + ((k + 1 : ℕ) : ℤ))) := by
    intro k
    have := apt_adj ht (c + (k : ℤ))
    rwa [show c + (k : ℤ) + 1 = c + ((k + 1 : ℕ) : ℤ) by push_cast; ring] at this
  have hzb : ∀ k : ℕ, apt t (c + (k : ℤ)) ≠ apt t (c + ((k + 2 : ℕ) : ℤ)) := by
    intro k
    have := apt_ne_two (by omega : 2 ≤ n) ht (c + (k : ℤ))
    rwa [show c + (k : ℤ) + 2 = c + ((k + 2 : ℕ) : ℤ) by push_cast; ring] at this
  have hzp : ∀ k : ℕ, apt t (c + ((k + 2 * n : ℕ) : ℤ)) = apt t (c + (k : ℤ)) := by
    intro k
    have := apt_add_two_mul (n := n) (t := t) (c + (k : ℤ)) 1
    rwa [show c + (k : ℤ) + 2 * (n : ℤ) * 1 = c + ((k + 2 * n : ℕ) : ℤ) by push_cast; ring] at this
  have hfix' : ∀ k : ℕ, g • apt t (c + (k : ℤ)) = apt t (c + (k : ℤ)) := fun k => hfix _
  have h0' : ∀ w : V, Γ.Adj (apt t (c + ((0 : ℕ) : ℤ))) w → g • w = w := by
    simpa using h0
  have h1' : ∀ w : V, Γ.Adj (apt t (c + ((1 : ℕ) : ℤ))) w → g • w = w := by
    simpa using h1
  refine eq_of_smul_eq_smul (m₁ := g) (m₂ := 1) (fun v : V => ?_)
  rw [one_smul]
  exact hgp.smul_eq_of_fix_apartment hn hT'
    (fun k : ℕ => apt t (c + (k : ℤ))) hzadj hzb hzp hfix' h0' h1' v

theorem exists_smul_apt_path {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hM : MoufangCondition D Γ n) {a b : ℤ} (hab : a < b) (hbn : b - a ≤ (n : ℤ))
    (z : ℤ → V) (hzb : z b = apt t b) (hzb1 : z (b + 1) = apt t (b + 1))
    (hadj : ∀ s : ℤ, a ≤ s → s ≤ b → Γ.Adj (z s) (z (s + 1)))
    (hnb : ∀ s : ℤ, a ≤ s → s + 2 ≤ b + 1 → z s ≠ z (s + 2)) :
    ∃ y : D, y ∈ ⨆ s ∈ Set.Ioc a b, aptRoot D Γ n t s ∧ y • apt t b = apt t b ∧
      ∀ s : ℤ, a ≤ s → s ≤ b - 1 → y • apt t s = z s := by
  have hmem : ∀ s : ℤ, a < s → s ≤ b →
      aptRoot D Γ n t s ≤ ⨆ k ∈ Set.Ioc a b, aptRoot D Γ n t k := by
    intro s h1 h2
    exact le_trans (le_iSup (fun _ : s ∈ Set.Ioc a b => aptRoot D Γ n t s) ⟨h1, h2⟩)
      (le_iSup (fun k => ⨆ _ : k ∈ Set.Ioc a b, aptRoot D Γ n t k) s)
  have key : ∀ k : ℕ, ∀ r : ℤ, b - 1 - r = (k : ℤ) → a ≤ r →
      (∀ s : ℤ, r ≤ s → s ≤ b → Γ.Adj (z s) (z (s + 1))) →
      (∀ s : ℤ, r ≤ s → s + 2 ≤ b + 1 → z s ≠ z (s + 2)) →
      ∃ y : D, y ∈ ⨆ s ∈ Set.Ioc a b, aptRoot D Γ n t s ∧ y • apt t b = apt t b ∧
        ∀ s : ℤ, r ≤ s → s ≤ b - 1 → y • apt t s = z s := by
    intro k
    induction k with
    | zero =>
      intro r hr har hadj' hnb'
      have hrb : r = b - 1 := by omega
      subst hrb
      have h1 : Γ.Adj (apt t b) (apt t (b - 1)) := by
        have h := (apt_adj ht (b - 1)).symm
        rwa [show b - 1 + 1 = b by ring] at h
      have h2 : Γ.Adj (apt t b) (z (b - 1)) := by
        have h := hadj' (b - 1) (by omega) (by omega)
        rw [show b - 1 + 1 = b by ring] at h
        rw [hzb] at h
        exact h.symm
      have h3 : apt t (b - 1) ≠ apt t (b + 1) := by
        have h := apt_ne_two (by omega : 2 ≤ n) ht (b - 1)
        rwa [show b - 1 + 2 = b + 1 by ring] at h
      have h4 : z (b - 1) ≠ apt t (b + 1) := by
        have h := hnb' (b - 1) (by omega) (by omega)
        rwa [show b - 1 + 2 = b + 1 by ring, hzb1] at h
      obtain ⟨y, hy, hyz⟩ := aptRoot_exists_smul_of_adj_start ht hn hM (k := b) h1 h2 h3 h4
      refine ⟨y, hmem b hab le_rfl hy, ?_, ?_⟩
      · have h := aptRoot_fix ht hy hn (r := 0) (by omega) (by omega)
        simpa using h
      · intro s hs1 hs2
        have hsb : s = b - 1 := by omega
        subst hsb
        exact hyz
    | succ k ih =>
      intro r hr har hadj' hnb'
      have hr' : b - 1 - (r + 1) = (k : ℤ) := by omega
      obtain ⟨y, hy, hyb, hyz⟩ := ih (r + 1) hr' (by omega)
        (fun s hs1 hs2 => hadj' s (by omega) hs2)
        (fun s hs1 hs2 => hnb' s (by omega) hs2)
      have hzr : Γ.Adj (z r) (z (r + 1)) := hadj' r (by omega) (by omega)
      have hzr1 : z (r + 1) = y • apt t (r + 1) := (hyz (r + 1) (by omega) (by omega)).symm
      have hAdj1 : Γ.Adj (apt t (r + 1)) (y⁻¹ • z r) := by
        have h1 : Γ.Adj (y⁻¹ • z r) (y⁻¹ • z (r + 1)) :=
          (GraphAction.adj_smul (Γ := Γ) y⁻¹ (z r) (z (r + 1))).mpr hzr
        rw [hzr1] at h1
        simpa using h1.symm
      have hne : y⁻¹ • z r ≠ apt t (r + 2) := by
        intro heq
        have h2 : z r = y • apt t (r + 2) := by
          have hh := congrArg (fun v => y • v) heq
          rwa [smul_inv_smul] at hh
        have hzy : y • apt t (r + 2) = z (r + 2) := by
          by_cases hle : r + 2 ≤ b - 1
          · exact hyz (r + 2) (by omega) hle
          · have hb2 : r + 2 = b := by omega
            rw [hb2, hzb]
            exact hyb
        rw [hzy] at h2
        exact hnb' r (by omega) (by omega) h2
      have h1 : Γ.Adj (apt t (r + 1)) (apt t r) := by
        simpa using (apt_adj ht r).symm
      have h3 : apt t r ≠ apt t (r + 1 + 1) := by
        have h := apt_ne_two (by omega : 2 ≤ n) ht r
        rwa [show r + 2 = r + 1 + 1 by ring] at h
      obtain ⟨w, hw, hwy⟩ := aptRoot_exists_smul_of_adj_start ht hn hM (k := r + 1) h1 hAdj1 h3
        (by rwa [show r + 2 = r + 1 + 1 by ring] at hne)
      have hwfix : w • apt t b = apt t b := by
        have h := aptRoot_fix ht hw hn (r := b - (r + 1)) (by omega) (by omega)
        rwa [show r + 1 + (b - (r + 1)) = b by ring] at h
      refine ⟨y * w, ?_, ?_, ?_⟩
      · exact Subgroup.mul_mem _ hy (hmem (r + 1) (by omega) (by omega) hw)
      · calc (y * w) • apt t b = y • (w • apt t b) := by rw [mul_smul]
          _ = y • apt t b := by rw [hwfix]
          _ = apt t b := hyb
      · intro s hs1 hs2
        rcases eq_or_ne s r with hsr | hsr
        · rw [hsr]
          calc (y * w) • apt t r = y • (w • apt t r) := by rw [mul_smul]
            _ = y • (y⁻¹ • z r) := by rw [hwy]
            _ = z r := by rw [smul_inv_smul]
        · have hs1' : r + 1 ≤ s := by omega
          have hws : w • apt t s = apt t s := by
            have h := aptRoot_fix ht hw hn (r := s - (r + 1)) (by omega) (by omega)
            rwa [show r + 1 + (s - (r + 1)) = s by ring] at h
          calc (y * w) • apt t s = y • (w • apt t s) := by rw [mul_smul]
            _ = y • apt t s := by rw [hws]
            _ = z s := hyz s hs1' hs2
  have hb1 : (0 : ℤ) ≤ b - 1 - a := by omega
  obtain ⟨y, hy, hyb, hyz⟩ := key ((b - 1 - a).toNat) a (by rw [Int.toNat_of_nonneg hb1])
    (by omega) hadj hnb
  exact ⟨y, hy, hyb, hyz⟩

end RootGroup

end CFSG.Quasithin.Stroth
