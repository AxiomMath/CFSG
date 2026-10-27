module

public import CFSG.Quasithin.Recognition.Stroth.Weiss80Route
public import CFSG.Quasithin.Recognition.Stroth.MoufangApartment
public import CFSG.Quasithin.Recognition.Stroth.MoufangTitsAxioms
public import CFSG.Quasithin.Recognition.Stroth.MoufangLittleNormal

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Quasithin CFSG.GH74.BNPair CFSG.Geometry.GeneralizedPolygons

open scoped Pointwise

variable {V : Type} [Fintype V] {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
  {n : ℕ} {D : Type} [Group D] [MulAction D V] [FaithfulSMul D V] [GraphAction D Γ]

theorem aptRoot_le_littleGroup {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 2 ≤ n) (k : ℤ) : aptRoot D Γ n t k ≤ littleGroup D Γ n := by
  rw [aptRoot_eq_pathRootGroup ht k]
  exact pathRootGroup_le_littleGroup (aptPath_noBack hn ht k)

@[expose] def aptRootGroup (D : Type) [Group D] [MulAction D V] (Γ : SimpleGraph V) (n : ℕ)
    (t : ZMod (2 * n) → V) : Subgroup D :=
  ⨆ k : ℤ, aptRoot D Γ n t k

theorem aptRoot_le_aptRootGroup {t : ZMod (2 * n) → V} (k : ℤ) :
    aptRoot D Γ n t k ≤ aptRootGroup D Γ n t :=
  le_iSup (fun j : ℤ => aptRoot D Γ n t j) k

theorem aptRootGroup_le_littleGroup {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 2 ≤ n) : aptRootGroup D Γ n t ≤ littleGroup D Γ n := by
  rw [aptRootGroup]
  exact iSup_le fun k => aptRoot_le_littleGroup ht hn k

theorem apt_val_add {t : ZMod (2 * n) → V} (hn : 1 ≤ n) (a : ZMod (2 * n)) (c : ℤ) :
    apt t ((a.val : ℤ) + c) = t (a + (c : ZMod (2 * n))) := by
  haveI : NeZero (2 * n) := ⟨by omega⟩
  show t ((((a.val : ℤ) + c : ℤ) : ZMod (2 * n))) = t (a + (c : ZMod (2 * n)))
  congr 1
  push_cast
  rw [ZMod.natCast_zmod_val]

theorem apt_dist_eq {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) {a : ℤ} {k : ℕ}
    (hk : k ≤ n) : Γ.dist (apt t a) (apt t (a + (k : ℤ))) = k := by
  have hp := aptSeg_isGeodesic (t := t) ht hn hP hT (a := a) (k := k) hk
  rw [GPath.IsGeodesic] at hp
  rw [show (aptSeg ht.2 a k hk) 0 = apt t a from by
        rw [aptSeg_apply ht.2 a hk (i := 0) (by omega)]
        norm_num,
      show (aptSeg ht.2 a k hk) k = apt t (a + (k : ℤ)) from by
        rw [aptSeg_apply ht.2 a hk (i := k) (by omega)]] at hp
  exact hp

theorem apt_adj_iff {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) {a b : ZMod (2 * n)} :
    Γ.Adj (t a) (t b) ↔ b = a + 1 ∨ b = a - 1 := by
  haveI : NeZero (2 * n) := ⟨by omega⟩
  have h1n : 1 ≤ n := by omega
  have hapt : ∀ c : ZMod (2 * n), apt t (c.val : ℤ) = t c := by
    intro c
    have h := apt_val_add (t := t) h1n c 0
    simpa using h
  constructor
  · intro hab
    set j : ℕ := (b - a).val with hj
    have hjz : ((j : ℕ) : ZMod (2 * n)) = b - a := by
      rw [hj]
      exact ZMod.natCast_zmod_val (b - a)
    have hb : b = a + (j : ZMod (2 * n)) := by
      rw [hjz]
      ring
    have hjlt : j < 2 * n := ZMod.val_lt _
    have hdist : Γ.dist (t a) (t b) = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hab
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · rw [hj0, Nat.cast_zero, add_zero] at hb
      rw [hb] at hab
      exact absurd hab (Γ.loopless.irrefl _)
    rcases Nat.lt_or_ge j (n + 1) with hjn | hjn
    · have hle : j ≤ n := by omega
      have h2 : apt t ((a.val : ℤ) + (j : ℤ)) = t b := by
        rw [apt_val_add (t := t) h1n a (j : ℤ)]
        congr 1
        push_cast
        exact hb.symm
      have hd := apt_dist_eq (t := t) ht hn hP hT (a := (a.val : ℤ)) (k := j) hle
      rw [hapt a, h2, hdist] at hd
      have hj1 : j = 1 := by omega
      exact Or.inl (by rw [hb, hj1]; norm_num)
    · have hjle : j ≤ 2 * n - 1 := by omega
      set d : ℕ := 2 * n - j with hddef
      have hdpos : 0 < d := by omega
      have hdle : d ≤ n := by omega
      have hdj : ((j : ℕ) : ZMod (2 * n)) + ((d : ℕ) : ZMod (2 * n)) = 0 := by
        have h2n : ((2 * n : ℕ) : ZMod (2 * n)) = 0 := ZMod.natCast_self (2 * n)
        rw [hddef, Nat.cast_sub (by omega : j ≤ 2 * n), h2n]
        ring
      have hbd : b + (d : ZMod (2 * n)) = a := by
        rw [hb, add_assoc, hdj, add_zero]
      have h2 : apt t ((b.val : ℤ) + (d : ℤ)) = t a := by
        rw [apt_val_add (t := t) h1n b (d : ℤ)]
        congr 1
        push_cast
        exact hbd
      have hd := apt_dist_eq (t := t) ht hn hP hT (a := (b.val : ℤ)) (k := d) hdle
      rw [hapt b, h2, SimpleGraph.dist_comm, hdist] at hd
      have hd1 : d = 1 := by omega
      exact Or.inr (by rw [← hbd, hd1]; norm_num)
  · rintro (hb | hb)
    · rw [hb]
      have h := apt_adj ht (a.val : ℤ)
      have e2 : apt t ((a.val : ℤ) + 1) = t (a + 1) := by
        rw [apt_val_add (t := t) h1n a 1]
        congr 1
        norm_num
      rw [hapt a, e2] at h
      exact h
    · rw [hb]
      have h := (apt_adj ht ((a.val : ℤ) - 1)).symm
      have e1 : apt t ((a.val : ℤ) - 1 + 1) = t a := by
        rw [show ((a.val : ℤ) - 1 + 1) = (a.val : ℤ) + 0 by ring,
          apt_val_add (t := t) h1n a 0]
        norm_num
      have e2 : apt t ((a.val : ℤ) - 1) = t (a - 1) := by
        rw [show ((a.val : ℤ) - 1) = (a.val : ℤ) + (-1) by ring,
          apt_val_add (t := t) h1n a (-1)]
        congr 1
        ring
      rw [e1, e2] at h
      exact h

private theorem apt_eq_of_eq_on_window {t t' : ZMod (2 * n) → V}
    (ht : IsPolygonApartment Γ n t) (ht' : IsPolygonApartment Γ n t')
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) {a : ℤ}
    (hwin : ∀ r : ℤ, a ≤ r → r ≤ a + (n : ℤ) + 1 → apt t' r = apt t r) :
    t' = t := by
  haveI : NeZero (2 * n) := ⟨by omega⟩
  have hgp : IsGenPolygon Γ n := isGenPolygon_of_isGeneralizedPolygon (by omega) hP hT
  have hU : UniqueGeod Γ n := hgp.uniqueGeod
  funext k
  let v : ℕ := (k - (a : ZMod (2 * n))).val
  let r : ℤ := a + (v : ℤ)
  have hr0 : a ≤ r := by
    show a ≤ a + (v : ℤ)
    omega
  have hrlt : r ≤ a + 2 * (n : ℤ) - 1 := by
    have h := ZMod.val_lt (k - (a : ZMod (2 * n)))
    show a + (v : ℤ) ≤ a + 2 * (n : ℤ) - 1
    omega
  have hrk : ((r : ℤ) : ZMod (2 * n)) = k := by
    show ((a + (v : ℤ) : ℤ) : ZMod (2 * n)) = k
    push_cast
    have hv : ((v : ℕ) : ZMod (2 * n)) = k - (a : ZMod (2 * n)) := by
      show ((((k - (a : ZMod (2 * n))).val : ℕ)) : ZMod (2 * n)) = k - (a : ZMod (2 * n))
      exact ZMod.natCast_zmod_val _
    rw [hv]
    ring
  have hcastt' : apt t' r = t' k := by
    show t' ((r : ℤ) : ZMod (2 * n)) = t' k
    rw [hrk]
  have hcastt : apt t r = t k := by
    show t ((r : ℤ) : ZMod (2 * n)) = t k
    rw [hrk]
  rw [← hcastt', ← hcastt]
  by_cases hle : r ≤ a + (n : ℤ) + 1
  · exact hwin r hr0 hle
  · have hge : a + (n : ℤ) + 2 ≤ r := by omega
    have hq0 : 0 ≤ r - (a + (n : ℤ) + 1) := by omega
    have hq : (r - (a + (n : ℤ) + 1)).toNat ≤ n - 1 := by
      have h3 : ((r - (a + (n : ℤ) + 1)).toNat : ℤ) ≤ ((n - 1 : ℕ) : ℤ) := by
        rw [Int.toNat_of_nonneg hq0,
          show ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 by
            rw [Nat.cast_sub (by omega : 1 ≤ n)]
            norm_num]
        omega
      exact_mod_cast h3
    let p' : GPath Γ (n - 1) := aptSeg ht'.2 (a + (n : ℤ) + 1) (n - 1) (by omega)
    let p : GPath Γ (n - 1) := aptSeg ht.2 (a + (n : ℤ) + 1) (n - 1) (by omega)
    have hp' : p'.IsGeodesic :=
      aptSeg_isGeodesic (t := t') ht' hn hP hT (a := a + (n : ℤ) + 1) (k := n - 1) (by omega)
    have hp : p.IsGeodesic :=
      aptSeg_isGeodesic (t := t) ht hn hP hT (a := a + (n : ℤ) + 1) (k := n - 1) (by omega)
    have e0 : p' 0 = p 0 := by
      have h1 : p' 0 = apt t' (a + (n : ℤ) + 1) := by
        show (aptSeg ht'.2 (a + (n : ℤ) + 1) (n - 1) (by omega)) 0 = _
        rw [aptSeg_apply ht'.2 (a + (n : ℤ) + 1) (by omega) (i := 0) (by omega)]
        norm_num
      have h2 : p 0 = apt t (a + (n : ℤ) + 1) := by
        show (aptSeg ht.2 (a + (n : ℤ) + 1) (n - 1) (by omega)) 0 = _
        rw [aptSeg_apply ht.2 (a + (n : ℤ) + 1) (by omega) (i := 0) (by omega)]
        norm_num
      rw [h1, h2]
      exact hwin (a + (n : ℤ) + 1) (by omega) (by omega)
    have eend : p' (n - 1) = p (n - 1) := by
      have h1 : p' (n - 1) = apt t' (a + (n : ℤ) + 1 + ((n - 1 : ℕ) : ℤ)) := by
        show (aptSeg ht'.2 (a + (n : ℤ) + 1) (n - 1) (by omega)) (n - 1) = _
        rw [aptSeg_apply ht'.2 (a + (n : ℤ) + 1) (by omega) (i := n - 1) (by omega)]
      have h2 : p (n - 1) = apt t (a + (n : ℤ) + 1 + ((n - 1 : ℕ) : ℤ)) := by
        show (aptSeg ht.2 (a + (n : ℤ) + 1) (n - 1) (by omega)) (n - 1) = _
        rw [aptSeg_apply ht.2 (a + (n : ℤ) + 1) (by omega) (i := n - 1) (by omega)]
      rw [h1, h2]
      have hcast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ n)]
        norm_num
      rw [hcast]
      have h1 : apt t' (a + (n : ℤ) + 1 + ((n : ℤ) - 1)) = apt t' (a + 2 * (n : ℤ)) := by
        congr 1
        ring
      have h2 : apt t (a + (n : ℤ) + 1 + ((n : ℤ) - 1)) = apt t (a + 2 * (n : ℤ)) := by
        congr 1
        ring
      rw [h1, h2]
      have hper' : apt t' (a + 2 * (n : ℤ)) = apt t' a := by
        have h := apt_add_two_mul (t := t') a 1
        rwa [show a + 2 * (n : ℤ) * 1 = a + 2 * (n : ℤ) by ring] at h
      have hper : apt t (a + 2 * (n : ℤ)) = apt t a := by
        have h := apt_add_two_mul (t := t) a 1
        rwa [show a + 2 * (n : ℤ) * 1 = a + 2 * (n : ℤ) by ring] at h
      rw [hper', hper]
      exact hwin a (by omega) (by omega)
    have hpaths : p' = p := hU (n - 1) p' p hp' hp e0 eend (by omega)
    have hv := congrArg (fun (q : GPath Γ (n - 1)) => q ((r - (a + (n : ℤ) + 1)).toNat)) hpaths
    rw [show p' ((r - (a + (n : ℤ) + 1)).toNat) =
          apt t' (a + (n : ℤ) + 1 + (((r - (a + (n : ℤ) + 1)).toNat : ℕ) : ℤ)) by
        show (aptSeg ht'.2 (a + (n : ℤ) + 1) (n - 1) (by omega)) _ = _
        rw [aptSeg_apply ht'.2 (a + (n : ℤ) + 1) (by omega) hq],
      show p ((r - (a + (n : ℤ) + 1)).toNat) =
          apt t (a + (n : ℤ) + 1 + (((r - (a + (n : ℤ) + 1)).toNat : ℕ) : ℤ)) by
        show (aptSeg ht.2 (a + (n : ℤ) + 1) (n - 1) (by omega)) _ = _
        rw [aptSeg_apply ht.2 (a + (n : ℤ) + 1) (by omega) hq]] at hv
    have hqr : a + (n : ℤ) + 1 + (((r - (a + (n : ℤ) + 1)).toNat : ℕ) : ℤ) = r := by
      rw [Int.toNat_of_nonneg hq0]
      ring
    rwa [hqr] at hv

theorem two_ne_zero_zmod (hn : 2 ≤ n) : (2 : ZMod (2 * n)) ≠ 0 := by
  intro h
  have hd : 2 * n ∣ 2 := (ZMod.natCast_eq_zero_iff 2 (2 * n)).mp h
  have := Nat.le_of_dvd (by norm_num) hd
  omega

theorem apt_fix_of_fix_two {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) {g : D}
    (hstab : g • (Set.range t) = Set.range t) {c : ZMod (2 * n)}
    (hc : g • t c = t c) (hc1 : g • t (c + 1) = t (c + 1)) :
    ∀ k : ZMod (2 * n), g • t k = t k := by
  classical
  haveI : NeZero (2 * n) := ⟨by omega⟩
  have hmem : ∀ k : ZMod (2 * n), g • t k ∈ Set.range t := by
    intro k
    have hx : t k ∈ Set.range t := Set.mem_range_self k
    have h := Set.smul_mem_smul_set (a := g) hx
    rwa [hstab] at h
  set σ : ZMod (2 * n) → ZMod (2 * n) := fun k => Classical.choose (hmem k) with hσ
  have hσspec : ∀ k, t (σ k) = g • t k := by
    intro k
    rw [hσ]
    exact Classical.choose_spec (hmem k)
  have hinj : Function.Injective σ := by
    intro a b hab
    have h : g • t a = g • t b := by rw [← hσspec a, ← hσspec b, hab]
    have h2 : t a = t b := by
      have h3 := congrArg (fun v => g⁻¹ • v) h
      simpa using h3
    exact ht.1 h2
  have hadj : ∀ k : ZMod (2 * n), Γ.Adj (t (σ k)) (t (σ (k + 1))) := by
    intro k
    rw [hσspec, hσspec]
    exact (GraphAction.adj_smul g (t k) (t (k + 1))).mpr (ht.2 k)
  have hstep : ∀ k : ZMod (2 * n), σ (k + 1) = σ k + 1 ∨ σ (k + 1) = σ k - 1 :=
    fun k => (apt_adj_iff ht hn hP hT).mp (hadj k)
  have hbase0 : σ c = c := ht.1 (by rw [hσspec]; exact hc)
  have hbase1 : σ (c + 1) = c + 1 := ht.1 (by rw [hσspec]; exact hc1)
  have hkey : ∀ j : ℕ, σ (c + (j : ZMod (2 * n))) = c + (j : ZMod (2 * n)) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      rcases j with _ | j
      · simpa using hbase0
      rcases j with _ | j
      · simpa using hbase1
      have h1 : σ (c + (j : ZMod (2 * n))) = c + (j : ZMod (2 * n)) := ih j (by omega)
      have h2 : σ (c + ((j + 1 : ℕ) : ZMod (2 * n))) = c + ((j + 1 : ℕ) : ZMod (2 * n)) :=
        ih (j + 1) (by omega)
      have hadj' := hstep (c + ((j + 1 : ℕ) : ZMod (2 * n)))
      have hcast : c + ((j + 1 : ℕ) : ZMod (2 * n)) + 1 =
          c + ((j + 1 + 1 : ℕ) : ZMod (2 * n)) := by
        push_cast
        ring
      rw [h2, hcast] at hadj'
      rcases hadj' with h | h
      · have e : c + ((j + 1 + 1 : ℕ) : ZMod (2 * n)) =
            c + ((j + 2 : ℕ) : ZMod (2 * n)) := by
          push_cast
          ring
        rw [e] at h
        rw [e]
        exact h
      · exfalso
        have hcj : σ (c + (j : ZMod (2 * n))) = c + (j : ZMod (2 * n)) := h1
        have hcast2 : c + ((j + 1 : ℕ) : ZMod (2 * n)) - 1 = c + (j : ZMod (2 * n)) := by
          push_cast
          ring
        rw [hcast2] at h
        have hjj : c + ((j + 1 + 1 : ℕ) : ZMod (2 * n)) = c + (j : ZMod (2 * n)) := by
          apply hinj
          rw [h]
          exact hcj.symm
        have h2ne : (2 : ZMod (2 * n)) = 0 := by
          have e1 : c + ((j + 1 + 1 : ℕ) : ZMod (2 * n)) =
              c + (j : ZMod (2 * n)) + 2 := by
            push_cast
            ring
          rw [e1] at hjj
          have h0 : c + (j : ZMod (2 * n)) + 2 = c + (j : ZMod (2 * n)) + 0 := by
            rw [hjj, add_zero]
          exact add_left_cancel h0
        exact two_ne_zero_zmod (by omega) h2ne
  intro k
  rw [← hσspec k]
  have hk : c + (((k - c).val : ℕ) : ZMod (2 * n)) = k := by
    have h := ZMod.natCast_zmod_val (k - c)
    rw [h]
    ring
  rw [← hk, hkey]

theorem aptRoot_add_two_mul {t : ZMod (2 * n) → V} (k c : ℤ) :
    aptRoot D Γ n t (k + 2 * (n : ℤ) * c) = aptRoot D Γ n t k := by
  ext g
  rw [mem_aptRoot, mem_aptRoot]
  constructor
  · intro h i hi1 hi2 w hw
    refine h i hi1 hi2 w ?_
    simpa [show k + 2 * (n : ℤ) * c + i = (k + i) + 2 * (n : ℤ) * c by ring,
      apt_add_two_mul] using hw
  · intro h i hi1 hi2 w hw
    refine h i hi1 hi2 w ?_
    simpa [show k + 2 * (n : ℤ) * c + i = (k + i) + 2 * (n : ℤ) * c by ring,
      apt_add_two_mul] using hw

theorem apt_ne_succ {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 2 ≤ n)
    (k : ZMod (2 * n)) : t k ≠ t (k + 1) := by
  intro h
  have h4 := ht.1 h
  have h5 := congrArg (fun x : ZMod (2 * n) => x - k) h4
  rw [sub_self, add_sub_cancel_left] at h5
  have h6 : (2 : ZMod (2 * n)) = 0 := by
    rw [show (2 : ZMod (2 * n)) = 1 + 1 by norm_num, h5.symm, zero_add]
  exact two_ne_zero_zmod (by omega) h6

theorem apt_ne_two_zmod {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 2 ≤ n)
    (k : ZMod (2 * n)) : t k ≠ t (k + 2) := by
  intro h
  have h4 := ht.1 h
  have h5 := congrArg (fun x : ZMod (2 * n) => x - k) h4
  rw [sub_self, add_sub_cancel_left] at h5
  exact two_ne_zero_zmod (by omega) h5.symm

@[expose] def baseRootProduct (D : Type) [Group D] [MulAction D V] (Γ : SimpleGraph V) (n : ℕ)
    (t : ZMod (2 * n) → V) : Subgroup D :=
  ⨆ k ∈ Set.Icc (1 : ℤ) (n : ℤ), aptRoot D Γ n t k

theorem exists_smul_apartment_through_chamber {t t' : ZMod (2 * n) → V}
    (ht : IsPolygonApartment Γ n t) (ht' : IsPolygonApartment Γ n t')
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ)
    (hM : MoufangCondition D Γ n) (h0 : t' n = t n) (h1 : t' (n + 1) = t (n + 1)) :
    ∃ u ∈ baseRootProduct D Γ n t, ∀ k : ZMod (2 * n), u • t k = t' k := by
  have hsub : (⨆ s ∈ Set.Ioc (0 : ℤ) (n : ℤ), aptRoot D Γ n t s) ≤
      baseRootProduct D Γ n t := by
    refine iSup_le fun s => iSup_le fun hs => ?_
    exact le_iSup₂_of_le s ⟨by have h := hs.1; omega, hs.2⟩ le_rfl
  obtain ⟨y, hy, hyb, hyz⟩ :=
    exists_smul_apt_path (t := t) ht hn hM (a := (0 : ℤ)) (b := (n : ℤ)) (by omega)
      (by omega) (fun j : ℤ => t' j) (by simpa [apt] using h0) (by simpa [apt] using h1)
      (fun s _ _ => by
        have h := ht'.2 ((s : ℤ) : ZMod (2 * n))
        have e : ((s : ℤ) : ZMod (2 * n)) + 1 = ((s + 1 : ℤ) : ZMod (2 * n)) := by
          push_cast
          ring
        rw [e] at h
        exact h)
      (fun s _ _ => by
        have h := apt_ne_two (n := n) (by omega : 2 ≤ n) ht' s
        intro hc
        exact h (by simpa [apt] using hc))
  have hyfix : y • apt t ((n : ℤ) + 1) = apt t ((n : ℤ) + 1) := by
    have hle := iSup_aptRoot_le_fixing (D := D) (V := V) (Γ := Γ) (n := n) (t := t) ht hn
      (a := (0 : ℤ)) (b := (n : ℤ)) (by omega)
      (r := (n : ℤ) + 1) (fun s _ _ => by omega) (fun s _ _ => by omega)
    have hmem : y ∈ fixingSubgroup D ({apt t ((n : ℤ) + 1)} : Set V) := hle hy
    have h := (mem_fixingSubgroup_iff D).mp hmem (apt t ((n : ℤ) + 1)) (Set.mem_singleton _)
    simpa using h
  have hyt : IsPolygonApartment Γ n (fun k => y • t k) := by
    constructor
    · intro a b hab
      have h : t a = t b := by
        have h := congrArg (fun v => y⁻¹ • v) hab
        simpa using h
      exact ht.1 h
    · intro k
      have h := (GraphAction.adj_smul (Γ := Γ) y (t k) (t (k + 1))).mpr (ht.2 k)
      simpa using h
  have hwin : ∀ r : ℤ, (0 : ℤ) ≤ r → r ≤ (0 : ℤ) + (n : ℤ) + 1 →
      apt t' r = apt (fun k => y • t k) r := by
    intro r hr0 hr1
    change t' ((r : ℤ) : ZMod (2 * n)) = y • t ((r : ℤ) : ZMod (2 * n))
    by_cases hle : r ≤ (n : ℤ) - 1
    · have h := hyz r hr0 hle
      change y • t ((r : ℤ) : ZMod (2 * n)) = t' ((r : ℤ) : ZMod (2 * n)) at h
      exact h.symm
    · have hge : (n : ℤ) ≤ r := by omega
      rcases eq_or_lt_of_le hge with hrn | hrn
      · subst hrn
        have hb' : y • t (((n : ℤ)) : ZMod (2 * n)) =
            t (((n : ℤ)) : ZMod (2 * n)) := by
          simpa [apt] using hyb
        have h0' : t' (((n : ℤ)) : ZMod (2 * n)) = t (((n : ℤ)) : ZMod (2 * n)) := by
          simpa [apt] using h0
        exact h0'.trans hb'.symm
      · have hrn1 : r = (n : ℤ) + 1 := by omega
        subst hrn1
        have hb' : y • t ((((n : ℤ) + 1 : ℤ)) : ZMod (2 * n)) =
            t ((((n : ℤ) + 1 : ℤ)) : ZMod (2 * n)) := by
          simpa [apt] using hyfix
        have h1' : t' ((((n : ℤ) + 1 : ℤ)) : ZMod (2 * n)) =
            t ((((n : ℤ) + 1 : ℤ)) : ZMod (2 * n)) := by
          simpa [apt] using h1
        exact h1'.trans hb'.symm
  have hEq : t' = fun k => y • t k :=
    apt_eq_of_eq_on_window (t := fun k => y • t k) (t' := t') hyt ht' hn hP hT (a := (0 : ℤ))
      (by simpa using hwin)
  exact ⟨y, hsub hy, fun k => (congrFun hEq k).symm⟩

theorem exists_reflectionData {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : CFSG.Geometry.GeneralizedPolygons.IsGeneralizedPolygon Γ n)
    (hT : CFSG.Geometry.GeneralizedPolygons.IsThick Γ) (hM : MoufangCondition D Γ n) (i : ℤ)
    {u : D} (hu : u ∈ aptRoot D Γ n t i) (hu1 : u ≠ 1) :
    ∃ v ∈ aptRoot D Γ n t (i + (n : ℤ)), ∃ w ∈ aptRoot D Γ n t (i + (n : ℤ)),
      (∀ k : ℤ, (v * u * w) • apt t k = apt t (2 * i - k)) ∧
        (∀ j : ℤ, (aptRoot D Γ n t j).map (MulAut.conj (v * u * w)).toMonoidHom =
          aptRoot D Γ n t (2 * i + (n : ℤ) - j)) :=
  exists_reflection_apt (t := t) ht hn hP hT hM hu hu1

@[expose] def moufangN (D : Type) [Group D] [MulAction D V] (Γ : SimpleGraph V)
    (n : ℕ) (t : ZMod (2 * n) → V) : Subgroup ↥(littleGroup D Γ n) :=
  (MulAction.stabilizer D (Set.range t)).subgroupOf (littleGroup D Γ n)

theorem exists_aptReflection {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n) (i : ℤ) :
    ∃ m ∈ littleGroup D Γ n, ∀ k : ℤ, m • apt t k = apt t (2 * i - k) := by
  classical
  obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (aptRoot_ne_bot (t := t) ht hn hP hT hM i)
  have huD : (u : D) ∈ aptRoot D Γ n t i := u.2
  obtain ⟨v, hv, w, hw, hact, -⟩ := exists_reflectionData (t := t) ht hn hP hT hM (i := i)
    (u := (u : D)) huD (by intro h; exact hu1 (Subtype.ext h))
  have h1n : 1 ≤ n := by omega
  refine ⟨v * u * w, ?_, hact⟩
  exact Subgroup.mul_mem _
    (Subgroup.mul_mem _ (aptRoot_le_littleGroup ht (by omega) (i + (n : ℤ)) hv)
      (aptRoot_le_littleGroup ht (by omega) i huD))
    (aptRoot_le_littleGroup ht (by omega) (i + (n : ℤ)) hw)

theorem apt_val {t : ZMod (2 * n) → V} (hn : 1 ≤ n) (k : ZMod (2 * n)) :
    apt t (k.val : ℤ) = t k := by
  haveI : NeZero (2 * n) := ⟨by omega⟩
  show t (((k.val : ℤ) : ZMod (2 * n))) = t k
  congr 1
  push_cast
  exact ZMod.natCast_zmod_val k

theorem reflection_mem_normalizer {t : ZMod (2 * n) → V} {m : D} {i : ℤ} (hn : 3 ≤ n)
    (hmL : m ∈ littleGroup D Γ n)
    (hact : ∀ k : ℤ, m • apt t k = apt t (2 * i - k)) :
    (⟨m, hmL⟩ : ↥(littleGroup D Γ n)) ∈ moufangN D Γ n t := by
  classical
  have h1n : 1 ≤ n := by omega
  refine Subgroup.mem_subgroupOf.mpr ?_
  rw [MulAction.mem_stabilizer_iff]
  ext x
  constructor
  · rw [Set.mem_smul_set]
    rintro ⟨y, ⟨k, rfl⟩, rfl⟩
    refine ⟨(((2 * i - (k.val : ℤ)) : ℤ) : ZMod (2 * n)), ?_⟩
    have hk : apt t (k.val : ℤ) = t k := apt_val h1n k
    have h := hact (k.val : ℤ)
    rw [hk] at h
    change apt t (2 * i - (k.val : ℤ)) = m • t k
    rw [← h]
  · intro hx
    obtain ⟨k, rfl⟩ := hx
    refine ⟨t (((2 * i - (k.val : ℤ)) : ℤ)), ⟨_, rfl⟩, ?_⟩
    have hk : apt t (k.val : ℤ) = t k := apt_val h1n k
    have h := hact (2 * i - (k.val : ℤ))
    rw [show 2 * i - (2 * i - (k.val : ℤ)) = (k.val : ℤ) by ring, hk] at h
    simpa [apt] using h

@[expose] def moufangB (D : Type) [Group D] [MulAction D V] (Γ : SimpleGraph V) (n : ℕ)
    (t : ZMod (2 * n) → V) : Subgroup ↥(littleGroup D Γ n) :=
  (MulAction.stabilizer D (t n) ⊓ MulAction.stabilizer D (t (n + 1))).subgroupOf
    (littleGroup D Γ n)

@[expose] def moufangCartan (D : Type) [Group D] [MulAction D V] (Γ : SimpleGraph V) (n : ℕ)
    (t : ZMod (2 * n) → V) : Subgroup ↥(littleGroup D Γ n) :=
  moufangB D Γ n t ⊓ moufangN D Γ n t

theorem fixingSubgroup_subgroupOf_le_littleCartan {t : ZMod (2 * n) → V} (hn : 1 ≤ n) :
    (fixingSubgroup D (Set.range t)).subgroupOf (littleGroup D Γ n) ≤
      moufangCartan D Γ n t := by
  intro g hg
  have hgD : (g : D) ∈ fixingSubgroup D (Set.range t) := Subgroup.mem_subgroupOf.mp hg
  have hfix : ∀ x : V, x ∈ Set.range t → (g : D) • x = x :=
    fun x hx => (mem_fixingSubgroup_iff D).mp hgD x hx
  constructor
  · refine Subgroup.mem_subgroupOf.mpr ⟨?_, ?_⟩
    · exact MulAction.mem_stabilizer_iff.mpr (hfix _ ⟨(n : ZMod (2 * n)), rfl⟩)
    · exact MulAction.mem_stabilizer_iff.mpr (hfix _ ⟨((n : ZMod (2 * n)) + 1), rfl⟩)
  · change (g : D) ∈ MulAction.stabilizer D (Set.range t)
    rw [MulAction.mem_stabilizer_iff]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [hfix x hx] using hx
    · intro hy
      exact ⟨y, hy, hfix y hy⟩

theorem moufangCartan_le_fixingSubgroup {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) :
    moufangCartan D Γ n t ≤ (fixingSubgroup D (Set.range t)).subgroupOf (littleGroup D Γ n) := by
  intro g hg
  obtain ⟨hgB, hgN⟩ := hg
  have hgB' : (g : D) ∈ MulAction.stabilizer D (t n) ⊓
      MulAction.stabilizer D (t (n + 1)) := Subgroup.mem_subgroupOf.mp hgB
  have hgN' : (g : D) ∈ MulAction.stabilizer D (Set.range t) := Subgroup.mem_subgroupOf.mp hgN
  have h0 : (g : D) • t (n : ZMod (2 * n)) = t (n : ZMod (2 * n)) :=
    MulAction.mem_stabilizer_iff.mp hgB'.1
  have h1 : (g : D) • t ((n : ZMod (2 * n)) + 1) = t ((n : ZMod (2 * n)) + 1) :=
    MulAction.mem_stabilizer_iff.mp hgB'.2
  have hstab : (g : D) • (Set.range t) = Set.range t :=
    MulAction.mem_stabilizer_iff.mp hgN'
  refine Subgroup.mem_subgroupOf.mpr ?_
  refine (mem_fixingSubgroup_iff D).mpr ?_
  intro x hx
  obtain ⟨k, rfl⟩ := hx
  exact apt_fix_of_fix_two ht hn hP hT hstab h0 h1 k

theorem moufangCartan_eq_fixingSubgroup {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) :
    moufangCartan D Γ n t = (fixingSubgroup D (Set.range t)).subgroupOf (littleGroup D Γ n) :=
  le_antisymm (moufangCartan_le_fixingSubgroup ht hn hP hT)
    (fixingSubgroup_subgroupOf_le_littleCartan (by omega))

end CFSG.Quasithin.Stroth
