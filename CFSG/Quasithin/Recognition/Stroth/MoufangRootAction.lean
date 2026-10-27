module

public import CFSG.Quasithin.Recognition.Stroth.MoufangTits

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Quasithin CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.Geometry.GeneralizedPolygons

open scoped Pointwise

variable {V : Type} [Fintype V] {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
  {n : ℕ} {D : Type} [Group D] [MulAction D V] [FaithfulSMul D V] [GraphAction D Γ]

theorem conjBy_rootD_pos_of_reflect {t : ZMod (2 * n) → V} {m : ↥(littleGroup D Γ n)} {i : ℤ}
    (hm : ∀ k : ℤ, (m : D) • apt t k = apt t (2 * i - k)) {j : ℤ}
    (hj1 : 1 ≤ j) :
    CFSG.GH74.BNPair.conjBy (m : D) (rootD (D := D) (Γ := Γ) (n := n) t j) =
      aptRoot D Γ n t (2 * i + (n : ℤ) - j) := by
  rw [rootD, if_pos (by omega)]
  exact conjBy_aptRoot_of_map_conj_action
    (aptRoot_map_conj_of_reflect (D := D) (Γ := Γ) (n := n) (t := t) (m := (m : D)) (i := i) hm) j

theorem conjBy_rootD_neg_of_reflect {t : ZMod (2 * n) → V} {m : ↥(littleGroup D Γ n)} {i : ℤ}
    (hm : ∀ k : ℤ, (m : D) • apt t k = apt t (2 * i - k)) {j : ℤ}
    (hj1 : 1 ≤ j) :
    CFSG.GH74.BNPair.conjBy (m : D) (rootD (D := D) (Γ := Γ) (n := n) t (-j)) =
      aptRoot D Γ n t (2 * i - j) := by
  rw [rootD, if_neg (by omega)]
  rw [show (n : ℤ) - -j = (n : ℤ) + j by ring]
  have h := conjBy_aptRoot_of_map_conj_action
    (aptRoot_map_conj_of_reflect (D := D) (Γ := Γ) (n := n) (t := t) (m := (m : D))
      (i := i) hm) ((n : ℤ) + j)
  rwa [show 2 * i + (n : ℤ) - ((n : ℤ) + j) = 2 * i - j by ring] at h

theorem rootL_n_add_one_eq_neg_one {t : ZMod (2 * n) → V} :
    rootL (D := D) (Γ := Γ) (n := n) t ((n : ℤ) + 1) =
      rootL (D := D) (Γ := Γ) (n := n) t (-1) := by
  rw [rootL, rootL]
  congr 1
  rw [rootD, rootD, if_pos (by omega), if_neg (by omega)]
  congr 1

theorem rootL_neg_n_add_one_eq_one {t : ZMod (2 * n) → V} :
    rootL (D := D) (Γ := Γ) (n := n) t (-((n : ℤ) + 1)) =
      rootL (D := D) (Γ := Γ) (n := n) t 1 := by
  rw [rootL, rootL]
  congr 1
  rw [rootD, rootD, if_neg (by omega), if_pos (by omega)]
  rw [show (n : ℤ) - (-((n : ℤ) + 1)) = 1 + 2 * (n : ℤ) * 1 by ring,
    aptRoot_add_two_mul]

theorem rootL_zero_eq_n {t : ZMod (2 * n) → V} (hn : 3 ≤ n) :
    rootL (D := D) (Γ := Γ) (n := n) t 0 =
      rootL (D := D) (Γ := Γ) (n := n) t (n : ℤ) := by
  rw [rootL, rootL]
  congr 1
  rw [rootD, rootD, if_neg (by omega), if_pos (by omega)]
  congr 1

theorem conjBy_rootL_one_of_reflect {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) {m : ↥(littleGroup D Γ n)}
    (hm : ∀ k : ℤ, (m : D) • apt t k = apt t (2 * 1 - k)) {j : ℤ}
    (hj1 : 1 ≤ j) (hjn : j ≤ (n : ℤ)) :
    CFSG.GH74.BNPair.conjBy m (rootL (D := D) (Γ := Γ) (n := n) t j) =
      rootL (D := D) (Γ := Γ) (n := n) t ((n : ℤ) + 2 - j) := by
  have hD : CFSG.GH74.BNPair.conjBy (m : D) (rootD (D := D) (Γ := Γ) (n := n) t j) =
      rootD (D := D) (Γ := Γ) (n := n) t ((n : ℤ) + 2 - j) := by
    rw [conjBy_rootD_pos_of_reflect hm hj1, rootD, if_pos (by omega)]
    congr 1
    ring
  exact conjBy_subgroupOf m (rootD_le_littleGroup ht hn _) (rootD_le_littleGroup ht hn _) hD

theorem conjBy_rootL_one_neg_of_reflect {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) {m : ↥(littleGroup D Γ n)}
    (hm : ∀ k : ℤ, (m : D) • apt t k = apt t (2 * 1 - k)) {j : ℤ}
    (hj1 : 1 ≤ j) (hjn : j ≤ (n : ℤ)) :
    CFSG.GH74.BNPair.conjBy m (rootL (D := D) (Γ := Γ) (n := n) t (-j)) =
      rootL (D := D) (Γ := Γ) (n := n) t (-((n : ℤ) + 2 - j)) := by
  have hD : CFSG.GH74.BNPair.conjBy (m : D) (rootD (D := D) (Γ := Γ) (n := n) t (-j)) =
      rootD (D := D) (Γ := Γ) (n := n) t (-((n : ℤ) + 2 - j)) := by
    rw [conjBy_rootD_neg_of_reflect hm hj1, rootD, if_neg (by omega)]
    have e : (n : ℤ) - (-((n : ℤ) + 2 - j)) = (2 - j) + 2 * (n : ℤ) * 1 := by ring
    rw [e, aptRoot_add_two_mul]
    congr 1
  exact conjBy_subgroupOf m (rootD_le_littleGroup ht hn _) (rootD_le_littleGroup ht hn _) hD

theorem conjBy_rootL_n_of_reflect {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) {m : ↥(littleGroup D Γ n)}
    (hm : ∀ k : ℤ, (m : D) • apt t k = apt t (2 * (n : ℤ) - k)) :
    CFSG.GH74.BNPair.conjBy m (rootL (D := D) (Γ := Γ) (n := n) t (n : ℤ)) =
      rootL (D := D) (Γ := Γ) (n := n) t (-(n : ℤ)) := by
  have hD : CFSG.GH74.BNPair.conjBy (m : D) (rootD (D := D) (Γ := Γ) (n := n) t (n : ℤ)) =
      rootD (D := D) (Γ := Γ) (n := n) t (-(n : ℤ)) := by
    rw [conjBy_rootD_pos_of_reflect hm (by omega), rootD, if_neg (by omega)]
    congr 1
    ring
  exact conjBy_subgroupOf m (rootD_le_littleGroup ht hn _) (rootD_le_littleGroup ht hn _) hD

theorem conjBy_rootL_n_pos_of_reflect {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) {m : ↥(littleGroup D Γ n)}
    (hm : ∀ k : ℤ, (m : D) • apt t k = apt t (2 * (n : ℤ) - k)) {j : ℤ}
    (hj1 : 1 ≤ j) (hjn : j ≤ (n : ℤ) - 1) :
    CFSG.GH74.BNPair.conjBy m (rootL (D := D) (Γ := Γ) (n := n) t j) =
      rootL (D := D) (Γ := Γ) (n := n) t ((n : ℤ) - j) := by
  have hD : CFSG.GH74.BNPair.conjBy (m : D) (rootD (D := D) (Γ := Γ) (n := n) t j) =
      rootD (D := D) (Γ := Γ) (n := n) t ((n : ℤ) - j) := by
    rw [conjBy_rootD_pos_of_reflect hm hj1, rootD, if_pos (by omega)]
    have e : 2 * (n : ℤ) + (n : ℤ) - j = ((n : ℤ) - j) + 2 * (n : ℤ) * 1 := by ring
    rw [e, aptRoot_add_two_mul]
  exact conjBy_subgroupOf m (rootD_le_littleGroup ht hn _) (rootD_le_littleGroup ht hn _) hD

theorem conjBy_rootL_n_neg_of_reflect {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) {m : ↥(littleGroup D Γ n)}
    (hm : ∀ k : ℤ, (m : D) • apt t k = apt t (2 * (n : ℤ) - k)) {j : ℤ}
    (hj1 : 1 ≤ j) (hjn : j ≤ (n : ℤ)) :
    CFSG.GH74.BNPair.conjBy m (rootL (D := D) (Γ := Γ) (n := n) t (-j)) =
      rootL (D := D) (Γ := Γ) (n := n) t (-((n : ℤ) - j)) := by
  have hD : CFSG.GH74.BNPair.conjBy (m : D) (rootD (D := D) (Γ := Γ) (n := n) t (-j)) =
      rootD (D := D) (Γ := Γ) (n := n) t (-((n : ℤ) - j)) := by
    rw [conjBy_rootD_neg_of_reflect hm hj1, rootD, if_neg (by omega)]
    congr 1
    ring
  exact conjBy_subgroupOf m (rootD_le_littleGroup ht hn _) (rootD_le_littleGroup ht hn _) hD


private theorem isRoot_bounds_pos {i : ℤ} (hi : IsRoot n i) (hpos : 0 < i) :
    1 ≤ i ∧ i ≤ (n : ℤ) := by
  have h1 : ((i.natAbs : ℕ) : ℤ) = i := Int.natAbs_of_nonneg (by omega)
  have h2 : ((i.natAbs : ℕ) : ℤ) ≤ (n : ℤ) := by exact_mod_cast hi.2
  omega

private theorem isRoot_bounds_neg {i : ℤ} (hi : IsRoot n i) (hneg : i < 0) :
    1 ≤ -i ∧ -i ≤ (n : ℤ) := by
  have h1 : ((i.natAbs : ℕ) : ℤ) = -i := Int.ofNat_natAbs_of_nonpos (by omega)
  have h2 : ((i.natAbs : ℕ) : ℤ) ≤ (n : ℤ) := by exact_mod_cast hi.2
  omega

theorem action_one_moufang {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n) :
    ∀ m : ↥(moufangN D Γ n t),
      (m : WeylGroup (moufangB D Γ n t) (moufangN D Γ n t)) =
        titsW1 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM →
      CFSG.GH74.BNPair.conjBy (m : ↥(littleGroup D Γ n))
          (rootL (D := D) (Γ := Γ) (n := n) t 1) =
        rootL (D := D) (Γ := Γ) (n := n) t (-1) ∧
      CFSG.GH74.BNPair.conjBy (m : ↥(littleGroup D Γ n))
          (rootL (D := D) (Γ := Γ) (n := n) t (-1)) =
        rootL (D := D) (Γ := Γ) (n := n) t 1 ∧
      ∀ i : ℤ, 2 ≤ i → i ≤ (n : ℤ) →
        CFSG.GH74.BNPair.conjBy (m : ↥(littleGroup D Γ n))
            (rootL (D := D) (Γ := Γ) (n := n) t i) =
          rootL (D := D) (Γ := Γ) (n := n) t ((n : ℤ) + 2 - i) ∧
        CFSG.GH74.BNPair.conjBy (m : ↥(littleGroup D Γ n))
            (rootL (D := D) (Γ := Γ) (n := n) t (-i)) =
          rootL (D := D) (Γ := Γ) (n := n) t (-((n : ℤ) + 2 - i)) := by
  intro m hmW
  let B := moufangB D Γ n t
  let N := moufangN D Γ n t
  letI : (cartan B N).Normal := moufangCartan_normal (t := t) ht hn hP hT
  have hfix : ∀ h ∈ B ⊓ N, ∀ k : ℤ,
      (((h : ↥(littleGroup D Γ n)) : D)) • apt t k = apt t k := by
    intro h hh k
    have hgf := moufangB_inf_moufangN_fix (t := t) ht hn hP hT hh
    exact (mem_fixingSubgroup_iff D).mp hgf (apt t k) ⟨((k : ℤ) : ZMod (2 * n)), rfl⟩
  let m₁ : ↥(littleGroup D Γ n) :=
    ((reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM : ↥(moufangN D Γ n t)) :
      ↥(littleGroup D Γ n))
  have hm₁N : m₁ ∈ N := (reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM).2
  let f : ℤ → ℤ := fun i =>
    if i = 1 then -1 else if i = -1 then 1 else
      if 0 < i then (n : ℤ) + 2 - i else -((n : ℤ) + 2 + i)
  have hconj : ∀ i : ℤ, IsRoot n i →
      CFSG.GH74.BNPair.conjBy m₁ (rootL (D := D) (Γ := Γ) (n := n) t i) =
        rootL (D := D) (Γ := Γ) (n := n) t (f i) := by
    intro i hi
    have hm : ∀ k : ℤ, (m₁ : D) • apt t k = apt t (2 * 1 - k) := by
      intro k
      calc (m₁ : D) • apt t k = apt t (2 * ((n : ℤ) + 1) - k) := by
            simpa [m₁] using reflOneN_smul (t := t) ht hn hP hT hM k
        _ = apt t (2 * 1 - k) := by
            rw [show 2 * ((n : ℤ) + 1) - k = (2 * 1 - k) + 2 * (n : ℤ) * 1 by ring,
              apt_add_two_mul]
    by_cases hi1 : i = 1
    · subst i
      have h := conjBy_rootL_one_of_reflect (t := t) ht hn (m := m₁) hm
        (j := 1) (by norm_num) (by omega)
      rw [h, show (n : ℤ) + 2 - 1 = (n : ℤ) + 1 by ring,
        rootL_n_add_one_eq_neg_one (t := t)]
      simp [f]
    · by_cases him1 : i = -1
      · subst i
        have h := conjBy_rootL_one_neg_of_reflect (t := t) ht hn (m := m₁) hm
          (j := 1) (by norm_num) (by omega)
        rw [h, show (n : ℤ) + 2 - 1 = (n : ℤ) + 1 by ring,
          rootL_neg_n_add_one_eq_one (t := t)]
        simp [f]
      · rcases lt_or_gt_of_ne hi.1 with hneg | hpos
        · have hb := isRoot_bounds_neg hi hneg
          have h := conjBy_rootL_one_neg_of_reflect (t := t) ht hn (m := m₁) hm
            (j := -i) hb.1 hb.2
          rw [show - -i = i by ring] at h
          have hf : f i = -((n : ℤ) + 2 + i) := by
            simp [f, hi1, him1, show ¬ 0 < i by omega]
          rw [h, show (n : ℤ) + 2 - -i = (n : ℤ) + 2 + i by ring, hf]
        · have hb := isRoot_bounds_pos hi hpos
          have h := conjBy_rootL_one_of_reflect (t := t) ht hn (m := m₁) hm
            (j := i) hb.1 hb.2
          have hf : f i = (n : ℤ) + 2 - i := by
            simp [f, hi1, him1, hpos]
          rw [h, hf]
  have hW : (m : WeylGroup B N) = (⟨m₁, hm₁N⟩ : N) := by
    rw [hmW, titsW1_eq_mk]
  have hall := conjBy_eq_of_same_weyl (B := B) (N := N) hfix hm₁N hW (f := f) hconj
  refine ⟨?_, ?_, ?_⟩
  · have h := hall 1 (isRoot_of_pos_le (by norm_num) (by omega))
    simpa [f] using h
  · have h := hall (-1) (by
      constructor
      · norm_num
      · simp only [Int.natAbs_neg, Int.natAbs_one]
        omega)
    simpa [f] using h
  · intro i hi2 hin
    have hiIs : IsRoot n i := isRoot_of_pos_le (by omega) (by omega)
    have hnegIs : IsRoot n (-i) := by
      constructor
      · omega
      · simpa [Int.natAbs_neg] using hiIs.2
    have hpos := hall i hiIs
    have hneg := hall (-i) hnegIs
    have hfpos : f i = (n : ℤ) + 2 - i := by
      simp [f, show i ≠ 1 by omega, show i ≠ -1 by omega, show 0 < i by omega]
    have hfneg : f (-i) = -((n : ℤ) + 2 - i) := by
      simp [f, show -i ≠ 1 by omega, show -i ≠ -1 by omega, show ¬ 0 < -i by omega,
        show ¬ i < 0 by omega]
      ring
    exact ⟨by rw [hpos, hfpos], by rw [hneg, hfneg]⟩

theorem action_two_moufang {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n) :
    ∀ m : ↥(moufangN D Γ n t),
      (m : WeylGroup (moufangB D Γ n t) (moufangN D Γ n t)) =
        titsW2 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM →
      CFSG.GH74.BNPair.conjBy (m : ↥(littleGroup D Γ n))
          (rootL (D := D) (Γ := Γ) (n := n) t (n : ℤ)) =
        rootL (D := D) (Γ := Γ) (n := n) t (-(n : ℤ)) ∧
      CFSG.GH74.BNPair.conjBy (m : ↥(littleGroup D Γ n))
          (rootL (D := D) (Γ := Γ) (n := n) t (-(n : ℤ))) =
        rootL (D := D) (Γ := Γ) (n := n) t (n : ℤ) ∧
      ∀ i : ℤ, 1 ≤ i → i ≤ (n : ℤ) - 1 →
        CFSG.GH74.BNPair.conjBy (m : ↥(littleGroup D Γ n))
            (rootL (D := D) (Γ := Γ) (n := n) t i) =
          rootL (D := D) (Γ := Γ) (n := n) t ((n : ℤ) - i) ∧
        CFSG.GH74.BNPair.conjBy (m : ↥(littleGroup D Γ n))
            (rootL (D := D) (Γ := Γ) (n := n) t (-i)) =
          rootL (D := D) (Γ := Γ) (n := n) t (-((n : ℤ) - i)) := by
  intro m hmW
  let B := moufangB D Γ n t
  let N := moufangN D Γ n t
  letI : (cartan B N).Normal := moufangCartan_normal (t := t) ht hn hP hT
  have hfix : ∀ h ∈ B ⊓ N, ∀ k : ℤ,
      (((h : ↥(littleGroup D Γ n)) : D)) • apt t k = apt t k := by
    intro h hh k
    have hgf := moufangB_inf_moufangN_fix (t := t) ht hn hP hT hh
    exact (mem_fixingSubgroup_iff D).mp hgf (apt t k) ⟨((k : ℤ) : ZMod (2 * n)), rfl⟩
  let m₁ : ↥(littleGroup D Γ n) :=
    ((reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM : ↥(moufangN D Γ n t)) :
      ↥(littleGroup D Γ n))
  have hm₁N : m₁ ∈ N := (reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM).2
  let f : ℤ → ℤ := fun i =>
    if i = (n : ℤ) then -(n : ℤ) else if i = -(n : ℤ) then (n : ℤ) else
      if 0 < i then (n : ℤ) - i else -((n : ℤ) + i)
  have hconj : ∀ i : ℤ, IsRoot n i →
      CFSG.GH74.BNPair.conjBy m₁ (rootL (D := D) (Γ := Γ) (n := n) t i) =
        rootL (D := D) (Γ := Γ) (n := n) t (f i) := by
    intro i hi
    have hm : ∀ k : ℤ, (m₁ : D) • apt t k = apt t (2 * (n : ℤ) - k) := by
      intro k
      simpa [m₁] using reflTwoN_smul (t := t) ht hn hP hT hM k
    by_cases hin : i = (n : ℤ)
    · subst i
      have h := conjBy_rootL_n_of_reflect (t := t) ht hn (m := m₁) hm
      rw [h]
      simp [f]
    · by_cases himn : i = -(n : ℤ)
      · subst i
        have h := conjBy_rootL_n_neg_of_reflect (t := t) ht hn (m := m₁) hm
          (j := (n : ℤ)) (by omega) le_rfl
        rw [h, show (n : ℤ) - (n : ℤ) = 0 by ring, show (-(0 : ℤ)) = 0 by ring,
          rootL_zero_eq_n (t := t) hn]
        simp [f, show n ≠ 0 by omega]
      · rcases lt_or_gt_of_ne hi.1 with hneg | hpos
        · have hb := isRoot_bounds_neg hi hneg
          have hkn : -i ≤ (n : ℤ) - 1 := by
            have hlt : -i < (n : ℤ) := by
              rcases lt_or_eq_of_le hb.2 with h | h
              · exact h
              · exfalso
                exact himn (by omega)
            omega
          have h := conjBy_rootL_n_neg_of_reflect (t := t) ht hn (m := m₁) hm
            (j := -i) hb.1 hb.2
          rw [show - -i = i by ring] at h
          have hf : f i = -((n : ℤ) + i) := by
            simp [f, hin, himn, show ¬ 0 < i by omega]
          rw [h, show (n : ℤ) - -i = (n : ℤ) + i by ring, hf]
        · have hb := isRoot_bounds_pos hi hpos
          have hkn : i ≤ (n : ℤ) - 1 := by
            have hlt : i < (n : ℤ) := by
              rcases lt_or_eq_of_le hb.2 with h | h
              · exact h
              · exact absurd h hin
            omega
          have h := conjBy_rootL_n_pos_of_reflect (t := t) ht hn (m := m₁) hm
            (j := i) hb.1 hkn
          have hf : f i = (n : ℤ) - i := by
            simp [f, hin, himn, hpos]
          rw [h, hf]
  have hW : (m : WeylGroup B N) = (⟨m₁, hm₁N⟩ : N) := by
    rw [hmW, titsW2_eq_mk]
  have hall := conjBy_eq_of_same_weyl (B := B) (N := N) hfix hm₁N hW (f := f) hconj
  refine ⟨?_, ?_, ?_⟩
  · have h := hall (n : ℤ) (isRoot_of_pos_le (by omega) (by omega))
    simpa [f] using h
  · have hnIs : IsRoot n (-(n : ℤ)) := by
      constructor
      · omega
      · have h1 : IsRoot n (n : ℤ) := isRoot_of_pos_le (by omega) (by omega)
        simpa [Int.natAbs_neg] using h1.2
    have h := hall (-(n : ℤ)) hnIs
    simpa [f, show n ≠ 0 by omega] using h
  · intro i hi1 hin
    have hiIs : IsRoot n i := isRoot_of_pos_le hi1 (by omega)
    have hnegIs : IsRoot n (-i) := by
      constructor
      · omega
      · simpa [Int.natAbs_neg] using hiIs.2
    have hpos := hall i hiIs
    have hneg := hall (-i) hnegIs
    have hfpos : f i = (n : ℤ) - i := by
      simp [f, show i ≠ (n : ℤ) by omega, show i ≠ -(n : ℤ) by omega, show 0 < i by omega]
    have hfneg : f (-i) = -((n : ℤ) - i) := by
      simp [f, show -i ≠ (n : ℤ) by omega, show -i ≠ -(n : ℤ) by omega,
        show ¬ 0 < -i by omega, show ¬ i < 0 by omega]
      ring
    exact ⟨by rw [hpos, hfpos], by rw [hneg, hfneg]⟩

theorem isSaturated_moufang {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n) :
    IsSaturated (moufangB D Γ n t) (moufangN D Γ n t) := by
  let B := moufangB D Γ n t
  let N := moufangN D Γ n t
  letI : MulAction ↥N (AptEdge t) := aptEdgeMulAction (t := t) ht hn hP hT
  have hcardOrbit : (MulAction.orbit ↥N (aptEdgeOf t (n : ZMod (2 * n)))).ncard = 2 * n :=
    card_orbit_aptEdge_base (t := t) ht hn hP hT hM
  have horbit : MulAction.orbit ↥N (aptEdgeOf t (n : ZMod (2 * n))) = Set.univ := by
    haveI : Finite (AptEdge t) := Subtype.finite
    rw [Set.eq_univ_iff_ncard]
    rw [hcardOrbit, card_aptEdge (Γ := Γ) (t := t) ht hn]
  unfold IsSaturated
  change B ⊓ N = ⨅ m : ↥N, B.map (MulAut.conj ((m : ↥(littleGroup D Γ n)))⁻¹).toMonoidHom
  refine le_antisymm ?_ ?_
  · intro h hh
    rw [Subgroup.mem_iInf]
    intro m
    rw [Subgroup.mem_map]
    have hhfix := moufangB_inf_moufangN_fix (t := t) ht hn hP hT hh
    have hfix := (mem_fixingSubgroup_iff D).mp hhfix
    have hmN : (m.1 : D) ∈ MulAction.stabilizer D (Set.range t) := mem_moufangN.mp m.2
    let u : ↥(littleGroup D Γ n) := m.1 * h * m.1⁻¹
    have hconj_fix : ∀ y, y ∈ Set.range t → (u : D) • y = y := by
      intro y hy
      have hmy : (m.1 : D)⁻¹ • y ∈ Set.range t := by
        have hset : (m.1 : D) • (Set.range t) = Set.range t :=
          MulAction.mem_stabilizer_iff.mp hmN
        have : y ∈ (m.1 : D) • Set.range t := by rw [hset]; exact hy
        rwa [Set.mem_smul_set_iff_inv_smul_mem] at this
      calc (u : D) • y
          = (m.1 : D) • ((h : D) • ((m.1 : D)⁻¹ • y)) := by simp [u, mul_smul]
        _ = (m.1 : D) • ((m.1 : D)⁻¹ • y) := by
            rw [show (h : D) • ((m.1 : D)⁻¹ • y) = ((m.1 : D)⁻¹ • y) from hfix _ hmy]
        _ = y := by simp
    refine ⟨u, ?_, ?_⟩
    · change u ∈ moufangB D Γ n t
      rw [mem_moufangB]
      exact ⟨hconj_fix (t n) (Set.mem_range_self _),
        hconj_fix (t (n + 1)) (Set.mem_range_self _)⟩
    · simp [u, MulAut.conj_apply, mul_assoc]
  · intro x hx
    have hxprop : ∀ m : ↥N, x ∈
        B.map (MulAut.conj ((m : ↥(littleGroup D Γ n)))⁻¹).toMonoidHom :=
      fun m => Subgroup.mem_iInf.mp hx m
    have hfix_edge : ∀ m : ↥N, ∀ z ∈ aptEdge t (n : ZMod (2 * n)),
        (x : D) • ((m.1 : D)⁻¹ • z) = (m.1 : D)⁻¹ • z := by
      intro m z hz
      obtain ⟨b, hb, hbx⟩ := Subgroup.mem_map.mp (hxprop m)
      have hbconj : m.1 * x * m.1⁻¹ = b := by
        rw [← hbx]
        simp [MulAut.conj_apply, mul_assoc]
      have hbB := mem_moufangB.mp (show b ∈ moufangB D Γ n t from hb)
      have hzpoint : (b : D) • z = z := by
        rw [aptEdge] at hz
        rcases hz with hz | hz
        · rw [hz]
          exact hbB.1
        · rw [hz]
          exact hbB.2
      have h1 : (m.1 : D) • ((x : D) • ((m.1 : D)⁻¹ • z)) =
          (m.1 : D) • ((m.1 : D)⁻¹ • z) := by
        calc (m.1 : D) • ((x : D) • ((m.1 : D)⁻¹ • z))
            = ((m.1 * x * m.1⁻¹ : ↥(littleGroup D Γ n)) : D) • z := by simp [mul_smul]
          _ = (b : D) • z := by rw [hbconj]
          _ = z := hzpoint
          _ = (m.1 : D) • ((m.1 : D)⁻¹ • z) := by simp
      have := congrArg (fun v => (m.1 : D)⁻¹ • v) h1
      simpa using this
    have hfix_edges : ∀ k : ZMod (2 * n), ∀ y ∈ aptEdge t k, (x : D) • y = y := by
      intro k y hy
      have hmem : aptEdgeOf t k ∈
          MulAction.orbit ↥N (aptEdgeOf t (n : ZMod (2 * n))) := by
        rw [horbit]
        exact Set.mem_univ _
      obtain ⟨m, hm⟩ := MulAction.mem_orbit_iff.mp hmem
      have hmval : (m.1 : D) • aptEdge t (n : ZMod (2 * n)) = aptEdge t k :=
        congrArg Subtype.val hm
      rw [← hmval] at hy
      obtain ⟨z, hz, rfl⟩ := Set.mem_smul_set.mp hy
      have h := hfix_edge m⁻¹ z hz
      simpa using h
    have hfix_range : (x : D) ∈ fixingSubgroup D (Set.range t) := by
      rw [mem_fixingSubgroup_iff]
      intro y hy
      obtain ⟨j, rfl⟩ := hy
      have hmem : t j ∈ aptEdge t j := by
        rw [aptEdge]
        exact Or.inl rfl
      exact hfix_edges j (t j) hmem
    have hxH : x ∈ moufangCartan D Γ n t := by
      rw [moufangCartan_eq_fixingSubgroup (t := t) ht hn hP hT]
      exact Subgroup.mem_subgroupOf.mpr hfix_range
    simpa [B, N, moufangCartan] using hxH

theorem meet_one_moufang {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) :
    ∀ x ∈ moufangB D Γ n t,
      x ∈ chainProd (rootL (D := D) (Γ := Γ) (n := n) t) ((intList 1 n).map Neg.neg) → x = 1 := by
  classical
  intro x hxB hx
  let l : List ℤ := (intList 1 (n : ℤ)).map Neg.neg
  have hlnd : l.Nodup := by
    dsimp [l]
    exact (chain_intList_nodup 1 (n : ℤ)).map (fun a b h => neg_inj.mp h)
  obtain ⟨f, hf, hfx⟩ := (chain_mem_chainProd_iff (rootL (D := D) (Γ := Γ) (n := n) t)
    l hlnd x).1 hx
  let g : ℤ → ↥(littleGroup D Γ n) := fun k => f (-k)
  have hxg : x = ((intList 1 n).map g).prod := by
    rw [← hfx]
    dsimp [l, g]
    rw [List.map_map]
    rfl
  have hgmem : ∀ k : ℤ, 1 ≤ k → k ≤ (n : ℤ) →
      g k ∈ rootL (D := D) (Γ := Γ) (n := n) t (-k) := by
    intro k hk1 hkn
    have hk : -k ∈ l := by
      dsimp [l]
      exact List.mem_map.2 ⟨k, mem_intList_iff.2 ⟨hk1, hkn⟩, by simp⟩
    exact hf (-k) hk
  have hgroot : ∀ k : ℤ, 1 ≤ k → k ≤ (n : ℤ) →
      (g k : D) ∈ aptRoot D Γ n t ((n : ℤ) + k) := by
    intro k hk1 hkn
    have h := hgmem k hk1 hkn
    rw [rootL, Subgroup.mem_subgroupOf, rootD, if_neg (by omega)] at h
    rwa [show (n : ℤ) - -k = (n : ℤ) + k by ring] at h
  have keyprod : ∀ (l : List ℤ) (y : V), (∀ j ∈ l, (g j : D) • y = y) →
      (((l.map g).prod : ↥(littleGroup D Γ n)) : D) • y = y := by
    intro l y h
    induction l generalizing y with
    | nil => simp
    | cons a l ih =>
      rw [List.map_cons, List.prod_cons, Subgroup.coe_mul, mul_smul,
        ih y (fun j hj => h j (by simp [hj])), h a (by simp)]
  let P : ℤ → ↥(littleGroup D Γ n) := fun k => ((intList k (n : ℤ)).map g).prod
  have hP1 : P 1 = x := by
    simpa [P] using hxg.symm
  have hPsucc : ∀ k : ℤ, 1 ≤ k → k ≤ (n : ℤ) →
      P k = g k * P (k + 1) := by
    intro k hk1 hkn
    dsimp [P]
    rw [intList_cons hkn, List.map_cons, List.prod_cons]
  have hPtop : P ((n : ℤ) + 1) = 1 := by
    dsimp [P]
    rw [show intList ((n : ℤ) + 1) (n : ℤ) = [] by simp [intList]]
    simp
  have hgk_one : ∀ k : ℤ, 1 ≤ k → k ≤ (n : ℤ) → P (k + 1) = 1 → g k = 1 := by
    intro k hk1 hkn hPk1
    let A : ↥(littleGroup D Γ n) := ((intList 1 (k - 1)).map g).prod
    dsimp [P] at hPk1
    have hsplit : P 1 = A * g k := by
      dsimp [P, A]
      have happ := intList_append (a := (1 : ℤ)) (b := k - 1) (c := (n : ℤ))
        (by omega) (by omega)
      rw [← happ, List.map_append, List.prod_append, show k - 1 + 1 = k by ring,
        intList_cons hkn, List.map_cons, List.prod_cons, hPk1, mul_one]
    have hxsplit : x = A * g k := by
      rw [← hP1, hsplit]
    have hAfix : (A : D) • apt t ((n : ℤ) + k - 1) = apt t ((n : ℤ) + k - 1) := by
      dsimp [A]
      refine keyprod (intList 1 (k - 1)) _ ?_
      intro j hj
      have hjmem := mem_intList_iff.1 hj
      have hmemj := hgroot j hjmem.1 (by omega)
      have h := aptRoot_fix ht hmemj hn (r := (k : ℤ) - 1 - j) (by omega) (by omega)
      rwa [show (n : ℤ) + j + ((k : ℤ) - 1 - j) = (n : ℤ) + (k : ℤ) - 1 by ring] at h
    have hfix0 : (x : D) • apt t 0 = apt t 0 := by
      have hxD : (x : D) = ((((intList 1 n).map g).prod : ↥(littleGroup D Γ n)) : D) := by
        rw [hxg]
      rw [hxD]
      refine keyprod (intList 1 (n : ℤ)) _ ?_
      intro j hj
      have hjmem := mem_intList_iff.1 hj
      have hmemj := hgroot j hjmem.1 hjmem.2
      have h := aptRoot_fix ht hmemj hn (r := (n : ℤ) - j) (by omega) (by omega)
      rwa [show (n : ℤ) + j + ((n : ℤ) - j) = 2 * (n : ℤ) by ring,
        show apt t (2 * (n : ℤ)) = apt t 0 by
          rw [show 2 * (n : ℤ) = 0 + 2 * (n : ℤ) * 1 by ring, apt_add_two_mul]] at h
    have hxw : (x : D) • apt t ((n : ℤ) + k - 1) = apt t ((n : ℤ) + k - 1) := by
      by_cases hk1' : k = 1
      · subst k
        have hw : apt t ((n : ℤ) + 1 - 1) = t (n : ZMod (2 * n)) := by
          rw [show (n : ℤ) + 1 - 1 = (n : ℤ) by ring]
          show t (((n : ℤ) : ZMod (2 * n))) = t (n : ZMod (2 * n))
          congr 1
          push_cast
          rfl
        rw [hw]
        exact mem_moufangB.mp hxB |>.1
      · have hk2 : 2 ≤ k := by omega
        have h0 : (x : D) • apt t ((n : ℤ) + 1) = apt t ((n : ℤ) + 1) := by
          have hcast : apt t ((n : ℤ) + 1) = t ((n : ZMod (2 * n)) + 1) := by
            show t ((((n : ℤ) + 1 : ℤ) : ZMod (2 * n))) = t ((n : ZMod (2 * n)) + 1)
            push_cast
            ring
          rw [hcast]
          exact (mem_moufangB.mp hxB).2
        have h1 : (x : D) • apt t (2 * (n : ℤ)) = apt t (2 * (n : ℤ)) := by
          rw [show 2 * (n : ℤ) = 0 + 2 * (n : ℤ) * 1 by ring, apt_add_two_mul]
          exact hfix0
        have hr : (k - 2).toNat ≤ n - 1 := by omega
        have h1' : (x : D) • apt t ((n : ℤ) + 1 + (n : ℤ) - 1) =
            apt t ((n : ℤ) + 1 + (n : ℤ) - 1) := by
          rw [show (n : ℤ) + 1 + (n : ℤ) - 1 = 2 * (n : ℤ) by ring]
          exact h1
        have h := fix_of_smul_ends (t := t) ht hn hP hT (g := (x : D))
          (a := (n : ℤ) + 1) h0 h1' (r := (k - 2).toNat) hr
        rwa [show (n : ℤ) + 1 + (((k - 2).toNat : ℕ) : ℤ) = (n : ℤ) + (k : ℤ) - 1 by
          rw [Int.toNat_of_nonneg (by omega)]; ring] at h
    have hgfix : (g k : D) • apt t ((n : ℤ) + k - 1) = apt t ((n : ℤ) + k - 1) := by
      have h1 : (((A * g k : ↥(littleGroup D Γ n)) : D)) •
          apt t ((n : ℤ) + k - 1) = apt t ((n : ℤ) + k - 1) := by
        have hxAk : (x : D) = (((A * g k : ↥(littleGroup D Γ n)) : D)) := by
          rw [hxsplit]
        rw [← hxAk]
        exact hxw
      rw [Subgroup.coe_mul, mul_smul] at h1
      have hAinv : ((A : D)⁻¹) • apt t ((n : ℤ) + k - 1) = apt t ((n : ℤ) + k - 1) := by
        have := congrArg (fun v => (A : D)⁻¹ • v) hAfix
        simpa using this.symm
      have := congrArg (fun v => (A : D)⁻¹ • v) h1
      simpa [hAinv] using this
    have hadj : Γ.Adj (apt t ((n : ℤ) + k)) (apt t ((n : ℤ) + k - 1)) := by
      have h := (apt_adj ht ((n : ℤ) + k - 1)).symm
      rwa [show (n : ℤ) + k - 1 + 1 = (n : ℤ) + k by ring] at h
    have hne : apt t ((n : ℤ) + k - 1) ≠ apt t ((n : ℤ) + k + 1) := by
      have h := apt_ne_two (by omega : 2 ≤ n) ht ((n : ℤ) + k - 1)
      rwa [show (n : ℤ) + k - 1 + 2 = (n : ℤ) + k + 1 by ring] at h
    exact Subtype.ext (aptRoot_eq_one_of_fix_adj_start ht (hgroot k hk1 hkn) hn hP hT
      hadj hne hgfix)
  have hpred : ∀ k : ℤ, k ≤ (n : ℤ) + 1 → (k ≤ 0 ∨ P k = 1) →
      ((k - 1) ≤ 0 ∨ P (k - 1) = 1) := by
    intro k hk h
    by_cases hk0 : k - 1 ≤ 0
    · exact Or.inl hk0
    · refine Or.inr ?_
      have hk2 : 1 ≤ k - 1 := by omega
      have hkn : k - 1 ≤ (n : ℤ) := by omega
      have hPk : P k = 1 := by
        rcases h with h0 | h
        · omega
        · exact h
      have hrec : P (k - 1) = g (k - 1) * P k := by
        have := hPsucc (k - 1) hk2 hkn
        rwa [show k - 1 + 1 = k by ring] at this
      have hg1 := hgk_one (k - 1) hk2 hkn (by rwa [show k - 1 + 1 = k by ring])
      rw [hrec, hg1, one_mul, hPk]
  have hall := Int.leInductionDown (m := (n : ℤ) + 1)
    (motive := fun k _ => k ≤ 0 ∨ P k = 1) (Or.inr hPtop) hpred
  have hP1one : P 1 = 1 := by
    rcases hall 1 (by omega) with h | h
    · omega
    · exact h
  rw [← hP1]
  exact hP1one

theorem isRootGroupSystem_moufang {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ)
    (hM : MoufangCondition D Γ n) :
    @IsRootGroupSystem (↥(littleGroup D Γ n)) _
      (moufangB D Γ n t) (moufangN D Γ n t)
      (moufangCartan_normal (t := t) ht hn hP hT)
      (titsW1 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM)
      (titsW2 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM)
      (rootU (D := D) (Γ := Γ) (n := n) t) n (rootL (D := D) (Γ := Γ) (n := n) t) := by
  letI : (cartan (moufangB D Γ n t) (moufangN D Γ n t)).Normal :=
    moufangCartan_normal (t := t) ht hn hP hT
  have hfix : ∀ h ∈ moufangB D Γ n t ⊓ moufangN D Γ n t, ∀ k : ℤ,
      (((h : ↥(littleGroup D Γ n)) : D)) • apt t k = apt t k := by
    intro h hh k
    have hgf := moufangB_inf_moufangN_fix (t := t) ht hn hP hT hh
    exact (mem_fixingSubgroup_iff D).mp hgf (apt t k) ⟨((k : ℤ) : ZMod (2 * n)), rfl⟩
  exact
    { ne_bot := fun i hi => rootL_ne_bot (t := t) ht hn hP hT hM hi
      invariant := fun i hi h hh x hx => rootL_invariant (t := t) _ _ hfix hi hh hx
      carrier_eq := rootU_coe (t := t) ht hn hP hT hM
      unique := fun f g hf hg heq => rootL_prod_unique (t := t) ht hn hP hT hM hf hg heq
      reverse_eq := fun i j hi hij hjn => chainProd_rootL_reverse (t := t) ht hn hP hT hM hi hij hjn
      subgroup := fun i j hi hij hjn => chainProd_rootL_subgroup (t := t) ht hn hP hT hM hi hij hjn
      action₁ := action_one_moufang (t := t) ht hn hP hT hM
      action₂ := action_two_moufang (t := t) ht hn hP hT hM
      meet_one := fun x hxB hx => meet_one_moufang (t := t) ht hn hP hT x hxB hx }

end CFSG.Quasithin.Stroth
