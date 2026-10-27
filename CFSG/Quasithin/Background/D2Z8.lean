module

public import CFSG.Quasithin.Background.D2Z7
public import CFSG.Quasithin.Background.D2Y5

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits
open scoped commutatorElement

variable {V : Type*} [CommGroup V] [Finite V]

omit [Finite V] in
structure KTriple (A : Subgroup (MulAut V)) (t u w : MulAut V) : Prop where
  tu : KleinData A t u
  tw : KleinData A t w
  uw : KleinData A u w

omit [Finite V] in
theorem KleinData.toTriple {A : Subgroup (MulAut V)} {t u : MulAut V} (k : KleinData A t u) :
    KTriple A t u (t * u) :=
  ⟨k, k.third, k.third'⟩

namespace KTriple

variable {A : Subgroup (MulAut V)} {t u w : MulAut V}

omit [Finite V] in
theorem swap12 (k : KTriple A t u w) : KTriple A u t w := ⟨k.tu.symm, k.uw, k.tw⟩

omit [Finite V] in
theorem swap23 (k : KTriple A t u w) : KTriple A t w u := ⟨k.tw, k.tu, k.uw.symm⟩

omit [Finite V] in
theorem eq_mul (k : KTriple A t u w) : w = t * u := by
  rcases k.tu.mem w k.tw.hb with h | h | h | h
  · exact absurd h k.tw.hb1
  · exact absurd h.symm k.tw.hab
  · exact absurd h.symm k.uw.hab
  · exact h

end KTriple

omit [Finite V] in
theorem rk_sup_le' [Finite V] (U W : Subgroup V) : rk ↥(U ⊔ W) ≤ rk U + rk W := by
  have := rk_sup_add_rk_inf U W
  omega

section Cases

variable {X A : Subgroup (MulAut V)} {r : ℚ}

theorem pCoreOf_eq_sup_triple (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) {t u w : MulAut V}
    (k : KTriple A t u w) : pCoreOf 3 X = centR X t ⊔ centR X u ⊔ centR X w := by
  rw [k.eq_mul]
  exact pCoreOf_eq_sup_centR hV h k.tu

theorem commV_pCoreOf_triple (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) {t u w : MulAut V}
    (k : KTriple A t u w) :
    commV (pCoreOf 3 X) = commV (centR X t) ⊔ commV (centR X u) ⊔ commV (centR X w) := by
  rw [pCoreOf_eq_sup_triple hV h k, commV_sup, commV_sup]

theorem centR_inf_eq_bot (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) {t u : MulAut V}
    (k : KleinData A t u) : centR X t ⊓ centR X u = ⊥ := by
  rw [eq_bot_iff]
  rintro y ⟨hyt, hyu⟩
  have := centP_trivial hV h k (mem_centR.mp hyt).1 (mem_centR.mp hyt).2.symm
    (mem_centR.mp hyu).2.symm
  rw [this]
  exact Subgroup.one_mem _

theorem Nt_le_fixV_of_disjoint (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) {s w : MulAut V}
    (hd : commV (centR X s) ⊓ commV (centR X w) = ⊥) :
    commV (centR X s) ≤ fixV (centR X w) := by
  have hcomm := pCoreOf_comm hV h
  have hinv : ∀ x ∈ centR X w, ∀ n ∈ commV (centR X s), x n ∈ commV (centR X s) :=
    fun x hx n hn => Nt_inv_P hcomm s (centR_le_pCoreOf X w hx) n hn
  have hle : commSub (commV (centR X s)) (centR X w) ≤
      commV (centR X s) ⊓ commV (centR X w) := by
    refine le_inf (commSub_le_of_invariant hinv) ?_
    rw [commV_eq_commSub (centR X w)]
    exact commSub_mono le_top le_rfl
  rw [hd, le_bot_iff] at hle
  exact commSub_eq_bot_iff.mp hle

theorem sup_inf_eq_bot_of_disjoint (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r)
    {t u w : MulAut V} (hd1 : commV (centR X t) ⊓ commV (centR X w) = ⊥)
    (hd2 : commV (centR X u) ⊓ commV (centR X w) = ⊥) (hcard : Nat.card (centR X w) = 3) :
    (commV (centR X t) ⊔ commV (centR X u)) ⊓ commV (centR X w) = ⊥ := by
  have h1 := Nt_le_fixV_of_disjoint hV h hd1
  have h2 := Nt_le_fixV_of_disjoint hV h hd2
  have hdisj := (commV_card_three hV hcard).2.1
  refine eq_bot_iff.mpr fun x hx => ?_
  have : x ∈ commV (centR X w) ⊓ fixV (centR X w) := ⟨hx.2, sup_le h1 h2 hx.1⟩
  rwa [hdisj, Subgroup.mem_bot] at this

theorem Nt_sup_inv_A (h : D214Hyp X A r) {t u : MulAut V} (ht : t ∈ A) (hu : u ∈ A) :
    ∀ g ∈ A, ∀ w ∈ commV (centR X t) ⊔ commV (centR X u),
      g w ∈ commV (centR X t) ⊔ commV (centR X u) := by
  intro g hg w hw
  obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hw
  rw [map_mul]
  exact Subgroup.mul_mem_sup (Nt_inv_A h ht hg a ha) (Nt_inv_A h hu hg b hb)

theorem rk_commV_zpowers_le (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) {N N' : Subgroup V}
    (hU : commV (pCoreOf 3 X) = N ⊔ N') {x : MulAut V} (hx : x ∈ A) :
    rk (commV (Subgroup.zpowers x)) ≤
      rk (commSub N (Subgroup.zpowers x)) + rk (commSub N' (Subgroup.zpowers x)) := by
  rw [commV_zpowers_eq_commSub hV h hx, hU, commSub_sup_left]
  exact rk_sup_le' _ _

theorem r_of_rkIdx (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) {n : ℕ}
    (hn : rkIdx (fixV A) = n) : (n : ℚ) = 2 * r := by
  have := rkIdx_fixV_eq hV h
  rw [hn] at this
  exact this

theorem caseTwo (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) {t u : MulAut V}
    (k : KleinData A t u) (h1 : centR X t ≠ ⊥) (h2 : centR X u ≠ ⊥)
    (h3 : centR X (t * u) = ⊥) :
    r = 3 / 2 ∧ commV (centR X t) = commV (centR X u) ∧ rk (commV (centR X t)) = 4 := by
  have hU : commV (pCoreOf 3 X) = commV (centR X t) ⊔ commV (centR X u) := by
    rw [commV_pCoreOf_triple hV h k.toTriple, h3, commV_bot, sup_bot_eq]
  have hkapU := kap_commV_pCoreOf hV h
  have hb := rkIdx_fixV_bounds hV h
  have hk1 := kap_Nt hV h k h1
  have hk2 := kap_Nt hV h k.symm h2
  have hr1 := Nt_rank_facts hV h k h1
  have hr2 := Nt_rank_facts hV h k.symm h2
  rcases Nt_disjoint_or_eq hV h (pCoreOf_comm hV h) k h1 h2 with hd | heq
  · exfalso
    have hds : IsDirectSum (commV (pCoreOf 3 X)) (commV (centR X t)) (commV (centR X u)) :=
      ⟨hU.symm, hd⟩
    have hkadd := kap_add hds (Nt_inv_A' h k.ha) (Nt_inv_A' h k.hb)
    rw [hkapU] at hkadd
    obtain ⟨-, -, m1, hm1⟩ := hr1
    obtain ⟨-, -, m2, hm2⟩ := hr2
    have hidx : rkIdx (fixV A) = 4 := by omega
    have hr : r = 2 := by
      have := r_of_rkIdx hV h hidx
      push_cast at this
      linarith
    have e1 := rk_Nt_eq_two_mul hV h k h1
    have e1' := rk_Nt_eq_two_mul hV h k.symm h2
    have s1 := rk_commSub_Nt_self hV h k h1
    have s2 := rk_commSub_Nt_self hV h k.symm h2
    have hcases : (rk (commV (centR X t)) = 4 ∧ rk (commV (centR X u)) = 2) ∨
        (rk (commV (centR X t)) = 2 ∧ rk (commV (centR X u)) = 4) := by omega
    rcases hcases with ⟨ha, hb'⟩ | ⟨ha, hb'⟩
    · have hle := rk_commV_zpowers_le hV h hU k.hb
      have hgt := rk_commV_gt hV h k.hb k.hb1
      have : rk (commV (Subgroup.zpowers u)) ≤ 2 := by omega
      have : (rk (commV (Subgroup.zpowers u)) : ℚ) ≤ 2 := by exact_mod_cast this
      linarith
    · have hle := rk_commV_zpowers_le hV h hU k.ha
      have hgt := rk_commV_gt hV h k.ha k.ha1
      have : rk (commV (Subgroup.zpowers t)) ≤ 2 := by omega
      have : (rk (commV (Subgroup.zpowers t)) : ℚ) ≤ 2 := by exact_mod_cast this
      linarith
  · have h4 := rk_Nt_eq_four_of_eq hV h k h1 h2 heq
    have hU' : commV (pCoreOf 3 X) = commV (centR X t) := by
      rw [hU, ← heq, sup_idem]
    rw [hU'] at hkapU
    have hidx : rkIdx (fixV A) = 3 := by omega
    refine ⟨?_, heq, h4⟩
    have := r_of_rkIdx hV h hidx
    push_cast at this
    linarith


theorem three_two_equal (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) {t u w : MulAut V}
    (kt : KTriple A t u w) (h1 : centR X t ≠ ⊥) (h2 : centR X u ≠ ⊥) (h3 : centR X w ≠ ⊥)
    (heq : commV (centR X t) = commV (centR X u))
    (hd : commV (centR X t) ⊓ commV (centR X w) = ⊥) : False := by
  have h4 := rk_Nt_eq_four_of_eq hV h kt.tu h1 h2 heq
  have hU : commV (pCoreOf 3 X) = commV (centR X t) ⊔ commV (centR X w) := by
    rw [commV_pCoreOf_triple hV h kt, ← heq, sup_idem]
  have hds : IsDirectSum (commV (pCoreOf 3 X)) (commV (centR X t)) (commV (centR X w)) :=
    ⟨hU.symm, hd⟩
  have hkadd := kap_add hds (Nt_inv_A' h kt.tu.ha) (Nt_inv_A' h kt.tw.hb)
  rw [kap_commV_pCoreOf hV h] at hkadd
  have hk1 := kap_Nt hV h kt.tu h1
  have hk3 := kap_Nt hV h kt.tw.symm h3
  have hr3 := Nt_rank_facts hV h kt.tw.symm h3
  have hb := rkIdx_fixV_bounds hV h
  obtain ⟨-, -, m3, hm3⟩ := hr3
  have hidx : rkIdx (fixV A) = 4 := by omega
  have hr : r = 2 := by
    have := r_of_rkIdx hV h hidx
    push_cast at this
    linarith
  have hgt := rk_commV_gt hV h kt.tw.hb kt.tw.hb1
  have hle := rk_commV_zpowers_le hV h hU kt.tw.hb
  have e1 := rk_Nt_eq_two_mul hV h kt.tw h1
  have e2 := rk_commSub_Nt_self hV h kt.tw.symm h3
  have : rk (commV (Subgroup.zpowers w)) ≤ 2 := by omega
  have : (rk (commV (Subgroup.zpowers w)) : ℚ) ≤ 2 := by exact_mod_cast this
  linarith

theorem three_all_equal (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) {t u w : MulAut V}
    (kt : KTriple A t u w) (h1 : centR X t ≠ ⊥) (h2 : centR X u ≠ ⊥) (h3 : centR X w ≠ ⊥)
    (heq : commV (centR X t) = commV (centR X u))
    (heq' : commV (centR X t) = commV (centR X w)) : False := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h4 := rk_Nt_eq_four_of_eq hV h kt.tu h1 h2 heq
  have hU : commV (pCoreOf 3 X) = commV (centR X t) := by
    rw [commV_pCoreOf_triple hV h kt, ← heq, ← heq', sup_idem, sup_idem]
  have hdir := isDirectSum_commV_fixV hV X
  have hfaith : ∀ g ∈ pCoreOf 3 X, (∀ n ∈ commV (centR X t), g n = n) → g = 1 := by
    intro g hg hgN
    ext v
    have hv : v ∈ commV (pCoreOf 3 X) ⊔ fixV (pCoreOf 3 X) := by
      rw [hdir.1]; exact Subgroup.mem_top v
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hv
    rw [map_mul, hgN a (hU ▸ ha), hb g hg]
    rfl
  have hinv : ∀ g ∈ pCoreOf 3 X, ∀ n ∈ commV (centR X t), g n ∈ commV (centR X t) :=
    fun g hg n hn => Nt_inv_P (pCoreOf_comm hV h) t hg n hn
  have hdvd := card_dvd_nine_of_faithful hV (pCoreOf_isPGroup 3 X) h4 hinv hfaith
  have hct : Nat.card (centR X t) = 3 := (centR_data hV h kt.tu h1).1
  have hcu : Nat.card (centR X u) = 3 := (centR_data hV h kt.tu.symm h2).1
  have hne : centR X t ≠ centR X u := by
    intro heq
    apply h1
    have := centR_inf_eq_bot hV h kt.tu
    rwa [← heq, inf_idem] at this
  obtain ⟨h9, -⟩ := sup_structure hct hcu hne (centR_comm hV h t u)
  have hle : centR X t ⊔ centR X u ≤ pCoreOf 3 X :=
    sup_le (centR_le_pCoreOf X t) (centR_le_pCoreOf X u)
  have hdvd' : 9 ∣ Nat.card (pCoreOf 3 X) := by
    rw [← h9]; exact Subgroup.card_dvd_of_le hle
  have hP9 : Nat.card (pCoreOf 3 X) = 9 := Nat.dvd_antisymm hdvd hdvd'
  have hEq : centR X t ⊔ centR X u = pCoreOf 3 X :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hP9, h9])
  have hw : centR X w ≤ centR X t ⊔ centR X u := hEq ▸ centR_le_pCoreOf X w
  have hind := centR_inf_sup_eq_bot hV h kt.tw kt.uw
  apply h3
  rw [eq_bot_iff, ← hind]
  exact le_inf le_rfl hw

theorem three_no_equal (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) {t u w : MulAut V}
    (kt : KTriple A t u w) (h1 : centR X t ≠ ⊥) (h2 : centR X u ≠ ⊥) (h3 : centR X w ≠ ⊥)
    (heq : commV (centR X t) = commV (centR X u)) : False := by
  rcases Nt_disjoint_or_eq hV h (pCoreOf_comm hV h) kt.tw h1 h3 with hd | heq'
  · exact three_two_equal hV h kt h1 h2 h3 heq hd
  · exact three_all_equal hV h kt h1 h2 h3 heq heq'

theorem caseThree (hV : ∀ v : V, v ^ 2 = 1) (h : D214Hyp X A r) {t u w : MulAut V}
    (kt : KTriple A t u w) (h1 : centR X t ≠ ⊥) (h2 : centR X u ≠ ⊥) (h3 : centR X w ≠ ⊥) :
    r = 3 / 2 ∧ rk (commV (centR X t)) = 2 ∧ rk (commV (centR X u)) = 2 ∧
      rk (commV (centR X w)) = 2 ∧ commV (centR X t) ⊓ commV (centR X u) = ⊥ ∧
      commV (centR X t) ⊓ commV (centR X w) = ⊥ ∧ commV (centR X u) ⊓ commV (centR X w) = ⊥ := by
  have hcomm := pCoreOf_comm hV h
  have d_tu : commV (centR X t) ⊓ commV (centR X u) = ⊥ := by
    rcases Nt_disjoint_or_eq hV h hcomm kt.tu h1 h2 with hd | heq
    · exact hd
    · exact (three_no_equal hV h kt h1 h2 h3 heq).elim
  have d_tw : commV (centR X t) ⊓ commV (centR X w) = ⊥ := by
    rcases Nt_disjoint_or_eq hV h hcomm kt.tw h1 h3 with hd | heq
    · exact hd
    · exact (three_no_equal hV h kt.swap23 h1 h3 h2 heq).elim
  have d_uw : commV (centR X u) ⊓ commV (centR X w) = ⊥ := by
    rcases Nt_disjoint_or_eq hV h hcomm kt.uw h2 h3 with hd | heq
    · exact hd
    · exact (three_no_equal hV h kt.swap12.swap23 h2 h3 h1 heq).elim
  have hcw : Nat.card (centR X w) = 3 := (centR_data hV h kt.tw.symm h3).1
  have hsd := sup_inf_eq_bot_of_disjoint hV h d_tw d_uw hcw
  have hU := commV_pCoreOf_triple hV h kt
  have hds1 : IsDirectSum (commV (centR X t) ⊔ commV (centR X u)) (commV (centR X t))
      (commV (centR X u)) := ⟨rfl, d_tu⟩
  have hds2 : IsDirectSum (commV (pCoreOf 3 X)) (commV (centR X t) ⊔ commV (centR X u))
      (commV (centR X w)) := ⟨hU.symm, hsd⟩
  have k1 := kap_add hds1 (Nt_inv_A' h kt.tu.ha) (Nt_inv_A' h kt.tu.hb)
  have k2 := kap_add hds2 (Nt_sup_inv_A h kt.tu.ha kt.tu.hb) (Nt_inv_A' h kt.tw.hb)
  rw [kap_commV_pCoreOf hV h] at k2
  have kt1 := kap_Nt hV h kt.tu h1
  have ku1 := kap_Nt hV h kt.tu.symm h2
  have kw1 := kap_Nt hV h kt.tw.symm h3
  have rt := Nt_rank_facts hV h kt.tu h1
  have ru := Nt_rank_facts hV h kt.tu.symm h2
  have rw' := Nt_rank_facts hV h kt.tw.symm h3
  have hb := rkIdx_fixV_bounds hV h
  obtain ⟨-, -, m1, hm1⟩ := rt
  obtain ⟨-, -, m2, hm2⟩ := ru
  obtain ⟨-, -, m3, hm3⟩ := rw'
  have hidx : rkIdx (fixV A) = 3 := by omega
  have hr : r = 3 / 2 := by
    have := r_of_rkIdx hV h hidx
    push_cast at this
    linarith
  refine ⟨hr, by omega, by omega, by omega, d_tu, d_tw, d_uw⟩

end Cases

end CFSG.Quasithin
