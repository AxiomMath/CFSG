module

public import CFSG.Quasithin.MS93.S510Chain

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

namespace S510

section General

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] {X : GoldAmalgam A C B}

theorem zm_le_centralizer_zm_of_dist (hyp : Hyp20 X) (hb : 0 < critDist X) {x y : Vtx X}
    (hx : IsMVtx X x) (hy : IsMVtx X y) (hd : X.treeGraph.dist x y < critDist X) :
    ZM X x ≤ Subgroup.centralizer (ZM X y : Set X.Universal) :=
  (zm_le_qv_of_dist_lt X hx hd).trans ((qv_le_centralizer_xm X y).trans
    (Subgroup.centralizer_le (zm_le_xm X hyp hb hy)))

theorem mem_stabCenter_of_reflect {x y z : Vtx X} {c w : X.Universal} (hc : c ∈ stab X x)
    (hcy : c • y = z) (hwx : w ∈ stabCenter X x) (hwy : w ∈ stabCenter X y) :
    w ∈ stabCenter X z := by
  rw [← hcy, stabCenter_smul, mem_map_conj]
  have hcw : c * w = w * c := commute_of_mem_stabCenter hwx hc
  have e : c⁻¹ * w * c = w := by
    calc c⁻¹ * w * c = c⁻¹ * (c * w) := by rw [hcw, mul_assoc]
      _ = w := by group
  rwa [e]

end General

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] {a : ↥M →* ↥(StatedSp 2 F)}

namespace IsChain

variable {h : PUHyp M T L} {q : ℕ} {s t : Vtx (puAmalgam h.le)} {N : ℕ}

theorem mem_stabCenter_of (hch : IsChain h q a s t N)
    (hcase : ∀ j ≤ N, S5.jOff h.le L q (geo _ s t (2 * j + 2)) (geo _ s t (2 * j + 1)) ≠
        S5.jOff h.le L q (geo _ s t (2 * j)) (geo _ s t (2 * j + 1)) ∨ ¬ LineCase h q a)
    {j : ℕ} (hj : j + 2 ≤ N) {w : (puAmalgam h.le).Universal}
    (hwst : w ∈ stab _ (geo _ s t (2 * j)))
    (hwT : w ∈ Subgroup.centralizer (Qv _ (geo _ s t (2 * j + 1)) : Set (puAmalgam h.le).Universal))
    (hw2 : ZM _ (geo _ s t (2 * j + critDist (puAmalgam h.le) + 2)) ≤
      Subgroup.centralizer ({w} : Set (puAmalgam h.le).Universal))
    (hw4 : ZM _ (geo _ s t (2 * j + critDist (puAmalgam h.le) + 4)) ≤
      Subgroup.centralizer ({w} : Set (puAmalgam h.le).Universal)) :
    w ∈ stabCenter _ (geo _ s t (2 * j)) := by
  have hd := hch.dist_eq
  set b := critDist (puAmalgam h.le) with hbdef
  set P := geo _ s t with hP
  have hb2 : 2 ≤ b := two_le_critDist _ h.hyp20 h.critDist_pos
  have hg1 := (hch.facts55 (j := j + 1) (by omega) (by omega) (hcase (j + 1) (by omega))).1
  have hg2 := (hch.facts55 (j := j + 2) (by omega) (by omega) (hcase (j + 2) (by omega))).1
  rw [show 2 * (j + 1) - 1 = 2 * j + 1 by omega, show 2 * (j + 1) = 2 * j + 2 by ring,
    show 2 * j + 2 + b = 2 * j + b + 2 by ring] at hg1
  rw [show 2 * (j + 2) - 1 = 2 * j + 3 by omega, show 2 * (j + 2) = 2 * j + 4 by ring,
    show 2 * j + 4 + b = 2 * j + b + 4 by ring] at hg2
  have hst3 : Qv _ (P (2 * j + 3)) ≤ stab _ (P (2 * j + 2)) :=
    qv_le_stab_of_adj _ (hch.adj_P (i := 2 * j + 2) (by omega)).symm
  have hc2 : stab _ (P (2 * j + 2)) ≤
      Subgroup.centralizer ({w} : Set (puAmalgam h.le).Universal) := by
    rw [← hg1]
    refine sup_le (fun y hy => ?_) hw2
    exact Subgroup.mem_centralizer_singleton_iff.2 ((Subgroup.mem_centralizer_iff.1 hwT) y hy)
  have hc4 : stab _ (P (2 * j + 4)) ≤
      Subgroup.centralizer ({w} : Set (puAmalgam h.le).Universal) := by
    rw [← hg2]
    exact sup_le (hst3.trans hc2) hw4
  obtain ⟨c, hc, hc4j⟩ := hch.straight (j + 1) (by omega) (by omega)
  rw [show 2 * (j + 1) = 2 * j + 2 by ring, show 2 * j + 2 + 2 = 2 * j + 4 by ring,
    show 2 * j + 2 - 2 = 2 * j by omega] at hc4j
  rw [show 2 * (j + 1) = 2 * j + 2 by ring] at hc
  rw [← hP] at hc hc4j
  rw [mem_stabCenter_iff]
  refine ⟨hwst, fun y hy => ?_⟩
  have hy' : c⁻¹ * y * c ∈ stab _ (P (2 * j + 4)) := by
    rw [← hc4j, mem_stab_smul] at hy
    exact hy
  have h1 : c⁻¹ * y * c * w = w * (c⁻¹ * y * c) :=
    (Subgroup.mem_centralizer_singleton_iff.1 (hc4 hy'))
  have h2 : c * w = w * c := Subgroup.mem_centralizer_singleton_iff.1 (hc2 hc)
  calc y * w = c * (c⁻¹ * y * c * w) * c⁻¹ := by
        rw [show c⁻¹ * y * c * w = c⁻¹ * y * (c * w) by group, h2]; group
    _ = c * (w * (c⁻¹ * y * c)) * c⁻¹ := by rw [h1]
    _ = w * y := by
        rw [show c * (w * (c⁻¹ * y * c)) * c⁻¹ = c * w * c⁻¹ * y by group, h2]; group

theorem mem_stabCenter_all (hch : IsChain h q a s t N) {i : ℕ} (hi : i + 1 ≤ N)
    {w : (puAmalgam h.le).Universal} (hw : w ∈ stabCenter _ (geo _ s t (2 * i)))
    (hw' : w ∈ stabCenter _ (geo _ s t (2 * i + 2))) :
    ∀ m ≤ N, w ∈ stabCenter _ (geo _ s t (2 * m)) := by
  have hup : ∀ n, i + n ≤ N → w ∈ stabCenter _ (geo _ s t (2 * (i + n))) ∧
      w ∈ stabCenter _ (geo _ s t (2 * (i + n) + 2)) := by
    intro n
    induction n with
    | zero => intro _; exact ⟨by simpa using hw, by simpa using hw'⟩
    | succ n ih =>
      intro hn
      obtain ⟨h1, h2⟩ := ih (by omega)
      refine ⟨by rw [show 2 * (i + (n + 1)) = 2 * (i + n) + 2 by ring]; exact h2, ?_⟩
      obtain ⟨c, hc, hcs⟩ := hch.straight (i + n + 1) (by omega) hn
      rw [show 2 * (i + n + 1) = 2 * (i + n) + 2 by ring,
        show 2 * (i + n) + 2 + 2 = 2 * (i + (n + 1)) + 2 by ring,
        show 2 * (i + n) + 2 - 2 = 2 * (i + n) by omega] at hcs
      rw [show 2 * (i + n + 1) = 2 * (i + n) + 2 by ring] at hc
      have hcs' : c⁻¹ • geo _ s t (2 * (i + n)) = geo _ s t (2 * (i + (n + 1)) + 2) := by
        rw [← hcs, inv_smul_smul]
      exact mem_stabCenter_of_reflect (inv_mem hc) hcs' h2 h1
  have hdown : ∀ n, n ≤ i → w ∈ stabCenter _ (geo _ s t (2 * (i - n))) ∧
      w ∈ stabCenter _ (geo _ s t (2 * (i - n) + 2)) := by
    intro n
    induction n with
    | zero => intro _; exact ⟨by simpa using hw, by simpa using hw'⟩
    | succ n ih =>
      intro hn
      obtain ⟨h1, h2⟩ := ih (by omega)
      refine ⟨?_, by rw [show 2 * (i - (n + 1)) + 2 = 2 * (i - n) by omega]; exact h1⟩
      obtain ⟨c, hc, hcs⟩ := hch.straight (i - n) (by omega) (by omega)
      rw [show 2 * (i - n) - 2 = 2 * (i - (n + 1)) by omega] at hcs
      exact mem_stabCenter_of_reflect hc hcs h1 h2
  intro m hm
  rcases le_or_gt i m with him | hmi
  · have := (hup (m - i) (by omega)).1
    rwa [show i + (m - i) = m by omega] at this
  · have := (hdown (i - m) (by omega)).1
    rwa [show i - (i - m) = m by omega] at this

end IsChain

end S510

end CFSG.Quasithin.MS93
