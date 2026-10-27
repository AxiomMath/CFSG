module

public import CFSG.Quasithin.Recognition.Stroth.MoufangLittleGen

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Quasithin CFSG.GH74.BNPair CFSG.Geometry.GeneralizedPolygons

open scoped Pointwise

variable {V : Type} [Fintype V] {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
  {n : ℕ} {D : Type} [Group D] [MulAction D V] [FaithfulSMul D V] [GraphAction D Γ]

private theorem isPolygonApartment_neg {t : ZMod (2 * n) → V}
    (ht : IsPolygonApartment Γ n t) :
    IsPolygonApartment Γ n (fun j => t (-j)) := by
  refine ⟨fun a b hab => neg_inj.mp (ht.1 hab), fun k => ?_⟩
  have h := (ht.2 (-(k + 1))).symm
  rwa [show -(k + 1) + 1 = -k from by ring] at h

private theorem apt_neg {t : ZMod (2 * n) → V} (k : ℤ) :
    apt (fun j => t (-j)) k = apt t (-k) := by
  show t (-((k : ℤ) : ZMod (2 * n))) = t (((-k : ℤ) : ZMod (2 * n)))
  congr 1
  push_cast
  ring

private theorem aptPath_neg {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (k : ℤ) :
    aptPath (isPolygonApartment_neg ht).2 k = aptPathRev ht.2 (-k - (n : ℤ)) := by
  refine GPath.ext' fun i hi => ?_
  rw [aptPath_apply _ k hi, aptPathRev_apply ht.2 _ hi]
  show t (-((k + (i : ℤ) : ℤ) : ZMod (2 * n))) =
    t ((((-k - (n : ℤ) + (n : ℤ) - (i : ℤ) : ℤ)) : ZMod (2 * n)))
  congr 1
  push_cast
  ring

theorem aptRoot_neg {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (k : ℤ) : aptRoot D Γ n (fun j => t (-j)) k = aptRoot D Γ n t (-k - (n : ℤ)) := by
  rw [aptRoot_eq_pathRootGroup (isPolygonApartment_neg ht) k, aptPath_neg ht k,
    ← aptRoot_eq_pathRootGroupRev (by omega) ht (-k - (n : ℤ))]

theorem aptRootGroup_neg {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n) :
    aptRootGroup D Γ n (fun j => t (-j)) = aptRootGroup D Γ n t := by
  refine le_antisymm ?_ ?_
  · rw [aptRootGroup]
    exact iSup_le fun k => by
      rw [aptRoot_neg ht hn]
      exact aptRoot_le_aptRootGroup (-k - (n : ℤ))
  · rw [aptRootGroup]
    refine iSup_le fun m => ?_
    have h := aptRoot_le_aptRootGroup (D := D) (Γ := Γ) (n := n) (t := fun j => t (-j))
      (-m - (n : ℤ))
    rw [aptRoot_neg ht hn] at h
    rwa [show -(-m - (n : ℤ)) - (n : ℤ) = m from by ring] at h

section Helper

variable {t : ZMod (2 * n) → V}

private theorem exists_smul_of_gpath
    {t' : ZMod (2 * n) → V} (ht' : IsPolygonApartment Γ n t')
    (hn : 3 ≤ n) (hM : MoufangCondition D Γ n)
    {ℓ : ℕ} (pp : GPath Γ ℓ) (hpp : pp.NoBack)
    {a b : ℤ} (hab : a < b) (hba : b - a = (ℓ : ℤ)) (hℓn : ℓ ≤ n)
    (hzb : pp ℓ = apt t' b)
    (hlast : pp (ℓ - 1) ≠ apt t' (b + 1)) :
    ∃ y ∈ ⨆ s ∈ Set.Ioc a b, aptRoot D Γ n t' s,
      y • apt t' b = apt t' b ∧
        ∀ s : ℤ, a ≤ s → s ≤ b - 1 → y • apt t' s = pp (s - a).toNat := by
  have hℓ1 : 1 ≤ ℓ := by
    have h : (0 : ℤ) < (ℓ : ℤ) := by rw [← hba]; omega
    omega
  let z : ℤ → V := fun s => if s ≤ b then pp (s - a).toNat else apt t' (b + 1)
  have hzb' : z b = apt t' b := by
    show (if b ≤ b then pp (b - a).toNat else apt t' (b + 1)) = apt t' b
    rw [if_pos le_rfl, hba]
    rw [Int.toNat_natCast]
    exact hzb
  have hzb1' : z (b + 1) = apt t' (b + 1) := by
    show (if b + 1 ≤ b then pp ((b + 1) - a).toNat else apt t' (b + 1)) = apt t' (b + 1)
    rw [if_neg (by omega)]
  have hzadj : ∀ s : ℤ, a ≤ s → s ≤ b → Γ.Adj (z s) (z (s + 1)) := by
    intro s hs1 hs2
    by_cases hsb : s = b
    · subst hsb
      have e1 : z s = apt t' s := hzb'
      have e2 : z (s + 1) = apt t' (s + 1) := hzb1'
      rw [e1, e2]
      exact apt_adj ht' s
    · have e1 : z s = pp (s - a).toNat := by
        show (if s ≤ b then pp (s - a).toNat else apt t' (b + 1)) = pp (s - a).toNat
        rw [if_pos (by omega)]
      have e2 : z (s + 1) = pp ((s + 1) - a).toNat := by
        show (if s + 1 ≤ b then pp ((s + 1) - a).toNat else apt t' (b + 1)) =
          pp ((s + 1) - a).toNat
        rw [if_pos (by omega)]
      rw [e1, e2]
      have hi : (((s - a).toNat : ℕ) : ℤ) = s - a :=
        Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ s - a)
      have hi' : ((((s + 1) - a).toNat : ℕ) : ℤ) = (s + 1) - a :=
        Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ (s + 1) - a)
      have hcast : (s - a).toNat + 1 = ((s + 1) - a).toNat := by
        have h2 : (((s - a).toNat + 1 : ℕ) : ℤ) = ((((s + 1) - a).toNat : ℕ) : ℤ) := by
          push_cast
          rw [hi, hi']
          ring
        exact_mod_cast h2
      have hlt : (s - a).toNat < ℓ := by
        have h2 : ((s - a).toNat : ℤ) < (ℓ : ℤ) := by
          rw [hi, ← hba]
          omega
        exact_mod_cast h2
      have hadj := pp.adj (s - a).toNat hlt
      rwa [hcast] at hadj
  have hznb : ∀ s : ℤ, a ≤ s → s + 2 ≤ b + 1 → z s ≠ z (s + 2) := by
    intro s hs1 hs2 hEq
    by_cases hcase : s ≤ b - 2
    · have e1 : z s = pp (s - a).toNat := by
        show (if s ≤ b then pp (s - a).toNat else apt t' (b + 1)) = pp (s - a).toNat
        rw [if_pos (by omega)]
      have e2 : z (s + 2) = pp ((s + 2) - a).toNat := by
        show (if s + 2 ≤ b then pp ((s + 2) - a).toNat else apt t' (b + 1)) =
          pp ((s + 2) - a).toNat
        rw [if_pos (by omega)]
      rw [e1, e2] at hEq
      have hi : (((s - a).toNat : ℕ) : ℤ) = s - a :=
        Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ s - a)
      have hi' : ((((s + 2) - a).toNat : ℕ) : ℤ) = (s + 2) - a :=
        Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ (s + 2) - a)
      have hcast : (s - a).toNat + 2 = ((s + 2) - a).toNat := by
        have h2 : (((s - a).toNat + 2 : ℕ) : ℤ) = ((((s + 2) - a).toNat : ℕ) : ℤ) := by
          push_cast
          rw [hi, hi']
          ring
        exact_mod_cast h2
      have hlt : (s - a).toNat + 2 ≤ ℓ := by
        have h2 : ((((s - a).toNat + 2 : ℕ)) : ℤ) ≤ (ℓ : ℤ) := by
          rw [hcast, hi']
          omega
        exact_mod_cast h2
      exact hpp (s - a).toNat hlt (by rwa [← hcast] at hEq)
    · have hsb : s = b - 1 := by omega
      subst hsb
      have e1 : z (b - 1) = pp (ℓ - 1) := by
        show (if b - 1 ≤ b then pp ((b - 1) - a).toNat else apt t' (b + 1)) = pp (ℓ - 1)
        rw [if_pos (by omega)]
        congr 1
        have h1 : (((b - 1) - a).toNat : ℤ) = (b - 1) - a :=
          Int.toNat_of_nonneg (by omega)
        have h2 : ((ℓ - 1 : ℕ) : ℤ) = (ℓ : ℤ) - 1 := by
          rw [Nat.cast_sub hℓ1]
          norm_num
        have h3 : (((b - 1) - a).toNat : ℤ) = (((ℓ - 1 : ℕ)) : ℤ) := by
          rw [h1, h2]
          omega
        exact_mod_cast h3
      have e2 : z (b - 1 + 2) = apt t' (b + 1) := by
        show (if b - 1 + 2 ≤ b then pp ((b - 1 + 2) - a).toNat else apt t' (b + 1)) =
          apt t' (b + 1)
        rw [if_neg (by omega)]
      rw [e1, e2] at hEq
      exact hlast hEq
  obtain ⟨y, hy, hyb, hyz⟩ := exists_smul_apt_path (t := t') ht' hn hM (a := a) (b := b) hab
    (by rw [hba]; exact_mod_cast hℓn) z hzb' hzb1' hzadj hznb
  refine ⟨y, hy, hyb, fun s hs1 hs2 => ?_⟩
  have h := hyz s hs1 hs2
  rwa [show z s = pp (s - a).toNat from by
    show (if s ≤ b then pp (s - a).toNat else apt t' (b + 1)) = pp (s - a).toNat
    rw [if_pos (by omega)]] at h

end Helper

section Edge

variable {t : ZMod (2 * n) → V}

private theorem dist_end_geodesic {d : ℕ} {g : GPath Γ d} (hconn : Γ.Connected)
    (hgeo : g.IsGeodesic) {i : ℕ} (hi : i ≤ d) :
    Γ.dist (g i) (g d) = d - i := by
  have h1 : Γ.dist (g 0) (g d) = d := hgeo
  have h2 : Γ.dist (g 0) (g i) = i := GPath.dist_prefix hconn g hgeo hi
  have h3 := GPath.dist_le_sub hconn g hi le_rfl
  have h4 := hconn.dist_triangle (u := g 0) (v := g i) (w := g d)
  omega

private theorem iSup_aptRoot_le_aptRootGroup {t : ZMod (2 * n) → V} (a b : ℤ) :
    (⨆ s ∈ Set.Ioc a b, aptRoot D Γ n t s) ≤ aptRootGroup D Γ n t := by
  rw [aptRootGroup]
  exact iSup_le fun s => iSup_le fun _ => le_iSup (fun j => aptRoot D Γ n t j) s

private theorem exists_smul_apt_edge_of_far (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n)
    {x y : V} (hxy : Γ.Adj x y) {d : ℕ}
    (hd : Γ.dist (apt t (n : ℤ)) x = d) (hdy : Γ.dist (apt t (n : ℤ)) y = d + 1)
    (hdn : d + 1 ≤ n) :
    ∃ m ∈ aptRootGroup D Γ n t, ∃ k : ℤ,
      (m • apt t k = x ∧ m • apt t (k + 1) = y) ∨
        (m • apt t k = y ∧ m • apt t (k + 1) = x) := by
  have hdx : Γ.dist x (apt t (n : ℤ)) = d := by rw [SimpleGraph.dist_comm]; exact hd
  obtain ⟨g, hg0, hgd, hgnb⟩ := GPath.exists_geodesic' hP.connected x (apt t (n : ℤ)) hdx
  have hyx : Γ.Adj y (g 0) := by rw [hg0]; exact hxy.symm
  have hne : y ≠ g 1 := by
    intro hy
    rcases Nat.eq_zero_or_pos d with hd0 | hdpos
    · obtain rfl : d = 0 := hd0
      have h1 : g 1 = g 0 := g.tail 1 (by omega)
      rw [h1, hg0] at hy
      exact hxy.ne hy.symm
    · have hgeo : g.IsGeodesic := by
        show Γ.dist (g 0) (g d) = d
        rw [hg0, hgd]
        exact hdx
      have hdistg : Γ.dist (apt t (n : ℤ)) (g 1) = d - 1 := by
        have h := dist_end_geodesic hP.connected hgeo (i := 1) (by omega)
        rwa [hgd, SimpleGraph.dist_comm] at h
      rw [← hy] at hdistg
      omega
  let pp : GPath Γ (d + 1) := g.cons y hyx
  have hppnb : pp.NoBack := GPath.noBack_cons y g hyx hgnb hne
  have hpp0 : pp 0 = y := GPath.cons_zero y g hyx
  have hpp1 : pp 1 = x := by
    change (g.cons y hyx) (0 + 1) = x
    rw [GPath.cons_succ, hg0]
  have hppl : pp (d + 1) = apt t (n : ℤ) := by
    rw [GPath.cons_succ, hgd]
  by_cases hcrit : pp ((d + 1) - 1) = apt t ((n : ℤ) + 1)
  ·
    have ht' : IsPolygonApartment Γ n (fun j => t (-j)) := isPolygonApartment_neg ht
    have hlast : pp ((d + 1) - 1) ≠ apt (fun j => t (-j)) ((-(n : ℤ)) + 1) := by
      rw [hcrit, apt_neg]
      rw [show -((-(n : ℤ)) + 1) = (n : ℤ) - 1 from by ring]
      have hne' := apt_ne_two (n := n) (by omega : 2 ≤ n) ht ((n : ℤ) - 1)
      rw [show ((n : ℤ) - 1) + 2 = (n : ℤ) + 1 from by ring] at hne'
      exact fun h => hne' h.symm
    have hzb : pp (d + 1) = apt (fun j => t (-j)) (-(n : ℤ)) := by
      refine hppl.trans ?_
      rw [apt_neg]
      congr 1
      ring
    obtain ⟨m, hm, hfix, hmap⟩ := exists_smul_of_gpath (t' := fun j => t (-j)) ht' hn hM
      pp hppnb (a := -(n : ℤ) - ((d : ℤ) + 1)) (b := -(n : ℤ)) (by omega)
      (by push_cast; ring) (by omega) hzb hlast
    have hmM : m ∈ aptRootGroup D Γ n t := by
      have hle : (⨆ s ∈ Set.Ioc (-(n : ℤ) - ((d : ℤ) + 1)) (-(n : ℤ)),
          aptRoot D Γ n (fun j => t (-j)) s) ≤ aptRootGroup D Γ n (fun j => t (-j)) :=
        iSup_aptRoot_le_aptRootGroup _ _
      rw [aptRootGroup_neg ht hn] at hle
      exact hle hm
    have h1 : m • apt (fun j => t (-j)) (-(n : ℤ) - ((d : ℤ) + 1)) = y := by
      have h := hmap (-(n : ℤ) - ((d : ℤ) + 1)) le_rfl (by omega)
      have hi : ((-(n : ℤ) - ((d : ℤ) + 1)) - (-(n : ℤ) - ((d : ℤ) + 1))).toNat = 0 := by
        rw [sub_self]
        rfl
      rw [hi, hpp0] at h
      exact h
    have h2 : m • apt (fun j => t (-j)) ((-(n : ℤ) - ((d : ℤ) + 1)) + 1) = x := by
      by_cases hle : (-(n : ℤ) - ((d : ℤ) + 1)) + 1 ≤ (-(n : ℤ)) - 1
      · have h := hmap ((-(n : ℤ) - ((d : ℤ) + 1)) + 1) (by omega) hle
        have hi : (((-(n : ℤ) - ((d : ℤ) + 1)) + 1) -
            (-(n : ℤ) - ((d : ℤ) + 1))).toNat = 1 := by
          simp
        rw [hi, hpp1] at h
        exact h
      · have hb' : (-(n : ℤ) - ((d : ℤ) + 1)) + 1 = -(n : ℤ) := by omega
        have hfix' : m • apt (fun j => t (-j)) ((-(n : ℤ) - ((d : ℤ) + 1)) + 1) =
            apt t (n : ℤ) := by
          rw [hb', hfix]
          rw [apt_neg]
          congr 1
          ring
        have hx' : x = apt t (n : ℤ) := by
          have hd0 : d = 0 := by omega
          have hd' : Γ.dist (apt t (n : ℤ)) x = 0 := by rw [hd, hd0]
          exact (hP.connected.dist_eq_zero_iff.mp hd').symm
        rw [hx']
        exact hfix'
    have e1 : apt (fun j => t (-j)) (-(n : ℤ) - ((d : ℤ) + 1)) =
        apt t ((n : ℤ) + (d : ℤ) + 1) := by
      rw [apt_neg]
      congr 1
      ring
    have e2 : apt (fun j => t (-j)) ((-(n : ℤ) - ((d : ℤ) + 1)) + 1) =
        apt t ((n : ℤ) + (d : ℤ)) := by
      rw [apt_neg]
      congr 1
      ring
    refine ⟨m, hmM, (n : ℤ) + (d : ℤ), Or.inl ⟨?_, ?_⟩⟩
    · rw [e2] at h2
      exact h2
    · have h1' : m • apt t ((n : ℤ) + (d : ℤ) + 1) = y := by rwa [e1] at h1
      exact h1'
  ·
    have hlast : pp ((d + 1) - 1) ≠ apt t ((n : ℤ) + 1) := hcrit
    obtain ⟨m, hm, hfix, hmap⟩ := exists_smul_of_gpath (t' := t) ht hn hM
      pp hppnb (a := (n : ℤ) - ((d : ℤ) + 1)) (b := (n : ℤ)) (by omega)
      (by push_cast; ring) (by omega) hppl hlast
    have hmM : m ∈ aptRootGroup D Γ n t :=
      iSup_aptRoot_le_aptRootGroup ((n : ℤ) - ((d : ℤ) + 1)) (n : ℤ) hm
    have h1 : m • apt t ((n : ℤ) - ((d : ℤ) + 1)) = y := by
      have h := hmap ((n : ℤ) - ((d : ℤ) + 1)) le_rfl (by omega)
      have hi : (((n : ℤ) - ((d : ℤ) + 1)) - ((n : ℤ) - ((d : ℤ) + 1))).toNat = 0 := by
        rw [sub_self]
        rfl
      rw [hi, hpp0] at h
      exact h
    have h2 : m • apt t (((n : ℤ) - ((d : ℤ) + 1)) + 1) = x := by
      by_cases hle : ((n : ℤ) - ((d : ℤ) + 1)) + 1 ≤ (n : ℤ) - 1
      · have h := hmap (((n : ℤ) - ((d : ℤ) + 1)) + 1) (by omega) hle
        have hi : ((((n : ℤ) - ((d : ℤ) + 1)) + 1) -
            ((n : ℤ) - ((d : ℤ) + 1))).toNat = 1 := by
          simp
        rw [hi, hpp1] at h
        exact h
      · have hb' : ((n : ℤ) - ((d : ℤ) + 1)) + 1 = (n : ℤ) := by omega
        have hxn : x = apt t (n : ℤ) := by
          have hd0 : d = 0 := by omega
          have hd' : Γ.dist (apt t (n : ℤ)) x = 0 := by rw [hd, hd0]
          exact (hP.connected.dist_eq_zero_iff.mp hd').symm
        rw [hb', hfix, hxn]
    refine ⟨m, hmM, (n : ℤ) - ((d : ℤ) + 1), Or.inr ⟨h1, ?_⟩⟩
    exact h2

theorem aptRootGroup_exists_smul_apt_edge (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n)
    {u v : V} (huv : Γ.Adj u v) :
    ∃ m ∈ aptRootGroup D Γ n t, ∃ k : ℤ,
      (m • apt t k = u ∧ m • apt t (k + 1) = v) ∨
        (m • apt t k = v ∧ m • apt t (k + 1) = u) := by
  have hdv : Γ.dist (apt t (n : ℤ)) v ≤ n := hP.dist_le (by omega) _ _
  have hdu : Γ.dist (apt t (n : ℤ)) u ≤ n := hP.dist_le (by omega) _ _
  rcases hP.dist_adj huv (apt t (n : ℤ)) with hfar | hfar
  · obtain ⟨m, hm, k, hk⟩ := exists_smul_apt_edge_of_far ht hn hP hT hM (x := u) (y := v) huv
      (d := Γ.dist (apt t (n : ℤ)) u) rfl hfar (by omega)
    exact ⟨m, hm, k, hk⟩
  · obtain ⟨m, hm, k, hk⟩ := exists_smul_apt_edge_of_far ht hn hP hT hM (x := v) (y := u)
      huv.symm (d := Γ.dist (apt t (n : ℤ)) v) rfl hfar (by omega)
    rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨m, hm, k, Or.inr ⟨h1, h2⟩⟩
    · exact ⟨m, hm, k, Or.inl ⟨h1, h2⟩⟩

end Edge

section Start

variable {t : ZMod (2 * n) → V}

theorem pathRootGroup_le_aptRootGroup_of_start (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n)
    {q : GPath Γ n} (hq : q.NoBack) {k : ℤ} (hq0 : q 0 = apt t k)
    (hq1 : q 1 = apt t (k + 1)) :
    pathRootGroup D Γ q ≤ aptRootGroup D Γ n t := by
  have ht' : IsPolygonApartment Γ n (fun j => t (-j)) := isPolygonApartment_neg ht
  have hlast : q.rev (n - 1) ≠ apt (fun j => t (-j)) (-k + 1) := by
    rw [GPath.rev_apply _ (by omega), show n - (n - 1) = 1 by omega, hq1]
    rw [apt_neg]
    rw [show -((-k : ℤ) + 1) = k - 1 from by ring]
    have hne := apt_ne_two (n := n) (by omega : 2 ≤ n) ht (k - 1)
    rw [show (k - 1) + 2 = k + 1 from by ring] at hne
    exact fun h => hne h.symm
  have hzb : q.rev n = apt (fun j => t (-j)) (-k) := by
    rw [GPath.rev_apply _ le_rfl, Nat.sub_self, hq0]
    rw [apt_neg]
    congr 1
    ring
  obtain ⟨m, hm, hfix, hmap⟩ := exists_smul_of_gpath (t' := fun j => t (-j)) ht' hn hM
    (ℓ := n) q.rev (GPath.NoBack.rev hq) (a := -k - (n : ℤ)) (b := -k) (by omega)
    (by push_cast; ring) le_rfl hzb hlast
  have hmM : m ∈ aptRootGroup D Γ n t := by
    have hle : (⨆ s ∈ Set.Ioc (-k - (n : ℤ)) (-k),
        aptRoot D Γ n (fun j => t (-j)) s) ≤ aptRootGroup D Γ n (fun j => t (-j)) :=
      iSup_aptRoot_le_aptRootGroup _ _
    rw [aptRootGroup_neg ht hn] at hle
    exact hle hm
  have hpath : m • aptPath ht.2 k = q := by
    refine GPath.ext' fun i hi => ?_
    rw [GPath.smul_apply, aptPath_apply ht.2 k hi]
    rcases Nat.eq_zero_or_pos i with hi0 | hipos
    · subst hi0
      have hfix' : m • apt t k = apt t k := by
        have h := hfix
        rw [show apt (fun j => t (-j)) (-k) = apt t k from by
          rw [apt_neg]
          congr 1
          ring] at h
        exact h
      rw [show k + ((0 : ℕ) : ℤ) = k from by norm_num, hfix', hq0]
    · have hs1 : -k - (n : ℤ) ≤ -k - (i : ℤ) := by push_cast; omega
      have hs2 : -k - (i : ℤ) ≤ -k - 1 := by omega
      have h := hmap (-k - (i : ℤ)) hs1 hs2
      have e : apt (fun j => t (-j)) (-k - (i : ℤ)) = apt t (k + (i : ℤ)) := by
        rw [apt_neg]
        congr 1
        ring
      rw [e] at h
      have hidx : ((-k - (i : ℤ)) - (-k - (n : ℤ))).toNat = n - i := by
        have h1 : (-k - (i : ℤ)) - (-k - (n : ℤ)) = (n : ℤ) - (i : ℤ) := by ring
        rw [h1]
        have h4 : ((n - i : ℕ) : ℤ) = (n : ℤ) - (i : ℤ) := by
          rw [Nat.cast_sub hi]
        have h3 : (((n : ℤ) - (i : ℤ)).toNat : ℤ) = ((n - i : ℕ) : ℤ) := by
          rw [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ (n : ℤ) - (i : ℤ)), h4]
        exact_mod_cast h3
      rw [hidx] at h
      rw [GPath.rev_apply (p := q) (i := n - i) (by omega)] at h
      rwa [show n - (n - i) = i by omega] at h
  have heq : pathRootGroup D Γ q =
      (pathRootGroup D Γ (aptPath ht.2 k)).map (MulAut.conj m).toMonoidHom := by
    rw [pathRootGroup_map_conj, hpath]
  rw [heq]
  intro x hx
  rw [Subgroup.mem_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hyM : y ∈ aptRootGroup D Γ n t := by
    refine aptRoot_le_aptRootGroup k ?_
    rwa [← aptRoot_eq_pathRootGroup ht k] at hy
  show m * y * m⁻¹ ∈ aptRootGroup D Γ n t
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hmM hyM) (Subgroup.inv_mem _ hmM)

theorem pathRootGroup_le_aptRootGroup (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n)
    {p : GPath Γ n} (hp : p.NoBack) :
    pathRootGroup D Γ p ≤ aptRootGroup D Γ n t := by
  have hedge : Γ.Adj (p 0) (p 1) := p.adj 0 (by omega)
  obtain ⟨m, hmM, k, hk | hk⟩ := aptRootGroup_exists_smul_apt_edge ht hn hP hT hM hedge
  · have hq0 : ((m⁻¹ : D) • p) 0 = apt t k := by
      rw [GPath.smul_apply, ← hk.1, inv_smul_smul]
    have hq1 : ((m⁻¹ : D) • p) 1 = apt t (k + 1) := by
      rw [GPath.smul_apply, ← hk.2, inv_smul_smul]
    have hle : pathRootGroup D Γ ((m⁻¹ : D) • p) ≤ aptRootGroup D Γ n t :=
      pathRootGroup_le_aptRootGroup_of_start ht hn hP hT hM (GPath.smul_noBack hp) hq0 hq1
    have heq : pathRootGroup D Γ p =
        (pathRootGroup D Γ ((m⁻¹ : D) • p)).map (MulAut.conj m).toMonoidHom := by
      rw [pathRootGroup_map_conj]
      congr 1
      calc p = (1 : D) • p := (GPath.one_smul' p).symm
        _ = (m * m⁻¹) • p := by rw [mul_inv_cancel]
        _ = m • ((m⁻¹ : D) • p) := GPath.mul_smul' m m⁻¹ p
    rw [heq]
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    show m * y * m⁻¹ ∈ aptRootGroup D Γ n t
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hmM (hle hy)) (Subgroup.inv_mem _ hmM)
  · have ht' : IsPolygonApartment Γ n (fun j => t (-j)) := isPolygonApartment_neg ht
    have hq0 : ((m⁻¹ : D) • p) 0 = apt (fun j => t (-j)) (-k - 1) := by
      rw [GPath.smul_apply, ← hk.2, inv_smul_smul]
      rw [apt_neg]
      congr 1
      ring
    have hq1 : ((m⁻¹ : D) • p) 1 = apt (fun j => t (-j)) ((-k - 1) + 1) := by
      rw [GPath.smul_apply, ← hk.1, inv_smul_smul]
      rw [apt_neg]
      congr 1
      ring
    have hle : pathRootGroup D Γ ((m⁻¹ : D) • p) ≤ aptRootGroup D Γ n (fun j => t (-j)) :=
      pathRootGroup_le_aptRootGroup_of_start ht' hn hP hT hM (GPath.smul_noBack hp) hq0 hq1
    rw [aptRootGroup_neg ht hn] at hle
    have heq : pathRootGroup D Γ p =
        (pathRootGroup D Γ ((m⁻¹ : D) • p)).map (MulAut.conj m).toMonoidHom := by
      rw [pathRootGroup_map_conj]
      congr 1
      calc p = (1 : D) • p := (GPath.one_smul' p).symm
        _ = (m * m⁻¹) • p := by rw [mul_inv_cancel]
        _ = m • ((m⁻¹ : D) • p) := GPath.mul_smul' m m⁻¹ p
    rw [heq]
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    show m * y * m⁻¹ ∈ aptRootGroup D Γ n t
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hmM (hle hy)) (Subgroup.inv_mem _ hmM)

theorem littleGroup_le_aptRootGroup (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n) :
    littleGroup D Γ n ≤ aptRootGroup D Γ n t := by
  rw [littleGroup]
  exact iSup_le fun p => iSup_le fun hp => pathRootGroup_le_aptRootGroup ht hn hP hT hM hp

theorem aptRootGroup_eq_littleGroup (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n) :
    aptRootGroup D Γ n t = littleGroup D Γ n :=
  le_antisymm (aptRootGroup_le_littleGroup ht (by omega))
    (littleGroup_le_aptRootGroup ht hn hP hT hM)

end Start

end CFSG.Quasithin.Stroth
