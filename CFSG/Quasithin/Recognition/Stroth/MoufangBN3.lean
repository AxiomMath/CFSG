module

public import CFSG.Quasithin.Recognition.Stroth.MoufangBN2

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Quasithin CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.Geometry.GeneralizedPolygons

open scoped Pointwise

variable {V : Type} [Fintype V] {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
  {n : ℕ} {D : Type} [Group D] [MulAction D V] [FaithfulSMul D V] [GraphAction D Γ]

theorem closure_titsW1_eq {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n)
    [(cartan (moufangB D Γ n t) (moufangN D Γ n t)).Normal] :
    Subgroup.closure ({titsW1 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM} :
      Set (WeylGroup (moufangB D Γ n t) (moufangN D Γ n t))) =
      ({1, titsW1 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM} :
        Set (WeylGroup (moufangB D Γ n t) (moufangN D Γ n t))) := by
  ext x
  refine ⟨fun hx => eq_one_or_eq_of_mem_closure_singleton
    (titsW1_sq (t := t) ht hn hP hT hM) hx, ?_⟩
  rintro (rfl | rfl)
  · exact Subgroup.one_mem _
  · exact Subgroup.subset_closure rfl

theorem closure_titsW2_eq {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n)
    (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ) (hM : MoufangCondition D Γ n)
    [(cartan (moufangB D Γ n t) (moufangN D Γ n t)).Normal] :
    Subgroup.closure ({titsW2 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM} :
      Set (WeylGroup (moufangB D Γ n t) (moufangN D Γ n t))) =
      ({1, titsW2 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM} :
        Set (WeylGroup (moufangB D Γ n t) (moufangN D Γ n t))) := by
  ext x
  refine ⟨fun hx => eq_one_or_eq_of_mem_closure_singleton
    (titsW2_sq (t := t) ht hn hP hT hM) hx, ?_⟩
  rintro (rfl | rfl)
  · exact Subgroup.one_mem _
  · exact Subgroup.subset_closure rfl

theorem stabilizer_vertex1_subset {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ)
    (hM : MoufangCondition D Γ n)
    [(cartan (moufangB D Γ n t) (moufangN D Γ n t)).Normal] :
    ((MulAction.stabilizer D (t (n + 1))).subgroupOf (littleGroup D Γ n) :
      Set ↥(littleGroup D Γ n)) ⊆
      (moufangB D Γ n t : Set ↥(littleGroup D Γ n)) ∪
        dc (moufangB D Γ n t) (moufangN D Γ n t)
          (titsW1 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM) := by
  intro g hg
  have hgv : (((g : ↥(littleGroup D Γ n)) : D)) • t (n + 1) = t (n + 1) :=
    MulAction.mem_stabilizer_iff.mp (Subgroup.mem_subgroupOf.mp hg)
  let nN : ↥(moufangN D Γ n t) := reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM
  have hclass : (nN : WeylGroup (moufangB D Γ n t) (moufangN D Γ n t)) =
      titsW1 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM := rfl
  exact stabilizer_of_moved_edge_subset (t := t) ht hn hP hT hM nN
    (titsW1 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM) hclass
    ((n : ZMod (2 * n)) + 1) (reflOne_moved_chamber (t := t) ht hn hP hT hM)
    (by
      have h := reflOneN_smul_zmod (t := t) ht hn hP hT hM ((n : ZMod (2 * n)) + 1)
      rw [show 2 * ((n : ZMod (2 * n)) + 1) - ((n : ZMod (2 * n)) + 1) =
        (n : ZMod (2 * n)) + 1 by ring] at h
      exact h)
    (by rw [aptEdge]; exact Set.mem_insert _ _)
    (by
      rw [aptEdge]
      intro hmem
      rcases Set.mem_insert_iff.1 hmem with h | h
      · exact apt_ne_succ ht (by omega) (n : ZMod (2 * n)) h
      · exact apt_ne_two_zmod ht (by omega) (n : ZMod (2 * n))
          (by simpa [show ((n : ZMod (2 * n)) + 1) + 1 = (n : ZMod (2 * n)) + 2 by ring]
            using h))
    (rootL (D := D) (Γ := Γ) (n := n) t 1)
    (rootL_le_littleBorel (t := t) ht hn (by norm_num) (by omega))
    (by
      intro yv hyv
      have hyvD : ((yv : ↥(littleGroup D Γ n)) : D) ∈ aptRoot D Γ n t 1 := by
        have hyv' := hyv
        rw [rootL, Subgroup.mem_subgroupOf, rootD, if_pos (by norm_num)] at hyv'
        exact hyv'
      have h := aptRoot_fix (t := t) ht (g := ((yv : ↥(littleGroup D Γ n)) : D)) hyvD hn
        (k := 1) (r := (n : ℤ)) (by omega) (by omega)
      rw [show 1 + (n : ℤ) = ((n + 1 : ℕ) : ℤ) by push_cast; ring] at h
      rw [show ((n : ZMod (2 * n)) + 1) = (((n + 1 : ℕ) : ℤ) : ZMod (2 * n)) by
        push_cast; ring]
      exact h)
    (by
      intro y y' hy hy' hne hne'
      have hcast : apt t (1 + (n : ℤ)) = t (n + 1) := by
        show t (((1 + (n : ℤ) : ℤ) : ZMod (2 * n))) = t (n + 1)
        congr 1
        push_cast
        ring
      have hprev : apt t (1 + (n : ℤ) - 1) = t n := by
        show t (((1 + (n : ℤ) - 1 : ℤ) : ZMod (2 * n))) = t n
        congr 1
        push_cast
        ring
      obtain ⟨yv, hyv, hyvact⟩ := aptRoot_exists_smul_of_adj (t := t) ht hn hM
        (k := 1) (y := y) (y' := y') (by rwa [hcast]) (by rwa [hcast])
        (by rwa [hprev]) (by rwa [hprev])
      refine ⟨⟨yv, aptRoot_le_littleGroup ht (by omega) 1 hyv⟩, ?_, hyvact⟩
      rw [rootL, Subgroup.mem_subgroupOf, rootD, if_pos (by norm_num)]
      exact hyv)
    (g := g) hgv

theorem lift_titsW1_fixes_vertex1 {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ)
    (hM : MoufangCondition D Γ n)
    [(cartan (moufangB D Γ n t) (moufangN D Γ n t)).Normal]
    (nN : ↥(moufangN D Γ n t))
    (hclass : (nN : WeylGroup (moufangB D Γ n t) (moufangN D Γ n t)) =
      titsW1 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM) :
    (((nN : ↥(littleGroup D Γ n)) : D)) • t (n + 1) = t (n + 1) := by
  let a : ↥(moufangN D Γ n t) := reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM
  have ha : (a : WeylGroup (moufangB D Γ n t) (moufangN D Γ n t)) =
      titsW1 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM := rfl
  have hprod : ((a⁻¹ * nN : ↥(moufangN D Γ n t)) :
      WeylGroup (moufangB D Γ n t) (moufangN D Γ n t)) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, ha, hclass, inv_mul_cancel]
  have hcart : a⁻¹ * nN ∈ cartan (moufangB D Γ n t) (moufangN D Γ n t) :=
    (QuotientGroup.eq_one_iff (N := cartan (moufangB D Γ n t) (moufangN D Γ n t)) _).mp hprod
  have hfixall : ((((a⁻¹ * nN : ↥(moufangN D Γ n t)) :
      ↥(littleGroup D Γ n)) : D)) ∈ fixingSubgroup D (Set.range t) :=
    moufangB_inf_moufangN_fix (t := t) ht hn hP hT (Subgroup.mem_subgroupOf.mp hcart)
  have hfixv : ((((a⁻¹ * nN : ↥(moufangN D Γ n t)) :
      ↥(littleGroup D Γ n)) : D)) • t (n + 1) = t (n + 1) :=
    (mem_fixingSubgroup_iff D).mp hfixall (t (n + 1)) (Set.mem_range_self _)
  have hdecomp : (nN : ↥(littleGroup D Γ n)) =
      (a : ↥(littleGroup D Γ n)) * (((a⁻¹ * nN : ↥(moufangN D Γ n t)) :
        ↥(littleGroup D Γ n))) := by
    rw [← Subgroup.coe_mul]
    congr 1
    group
  rw [hdecomp, Subgroup.coe_mul, mul_smul, hfixv]
  have hact := reflOneN_smul_zmod (t := t) ht hn hP hT hM ((n : ZMod (2 * n)) + 1)
  rw [show 2 * ((n : ZMod (2 * n)) + 1) - ((n : ZMod (2 * n)) + 1) =
    (n : ZMod (2 * n)) + 1 by ring] at hact
  exact hact

theorem lift_titsW2_fixes_vertex_n {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ)
    (hM : MoufangCondition D Γ n)
    [(cartan (moufangB D Γ n t) (moufangN D Γ n t)).Normal]
    (nN : ↥(moufangN D Γ n t))
    (hclass : (nN : WeylGroup (moufangB D Γ n t) (moufangN D Γ n t)) =
      titsW2 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM) :
    (((nN : ↥(littleGroup D Γ n)) : D)) • t n = t n := by
  let a : ↥(moufangN D Γ n t) := reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM
  have ha : (a : WeylGroup (moufangB D Γ n t) (moufangN D Γ n t)) =
      titsW2 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM := rfl
  have hprod : ((a⁻¹ * nN : ↥(moufangN D Γ n t)) :
      WeylGroup (moufangB D Γ n t) (moufangN D Γ n t)) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, ha, hclass, inv_mul_cancel]
  have hcart : a⁻¹ * nN ∈ cartan (moufangB D Γ n t) (moufangN D Γ n t) :=
    (QuotientGroup.eq_one_iff (N := cartan (moufangB D Γ n t) (moufangN D Γ n t)) _).mp hprod
  have hfixall : ((((a⁻¹ * nN : ↥(moufangN D Γ n t)) :
      ↥(littleGroup D Γ n)) : D)) ∈ fixingSubgroup D (Set.range t) :=
    moufangB_inf_moufangN_fix (t := t) ht hn hP hT (Subgroup.mem_subgroupOf.mp hcart)
  have hfixv : ((((a⁻¹ * nN : ↥(moufangN D Γ n t)) :
      ↥(littleGroup D Γ n)) : D)) • t n = t n :=
    (mem_fixingSubgroup_iff D).mp hfixall (t n) (Set.mem_range_self _)
  have hdecomp : (nN : ↥(littleGroup D Γ n)) =
      (a : ↥(littleGroup D Γ n)) * (((a⁻¹ * nN : ↥(moufangN D Γ n t)) :
        ↥(littleGroup D Γ n))) := by
    rw [← Subgroup.coe_mul]
    congr 1
    group
  rw [hdecomp, Subgroup.coe_mul, mul_smul, hfixv]
  have hact := reflTwoN_smul_zmod (t := t) ht hn hP hT hM (n : ZMod (2 * n))
  rwa [show 2 * (n : ZMod (2 * n)) - (n : ZMod (2 * n)) =
    (n : ZMod (2 * n)) by ring] at hact

theorem parabolic_titsW1_eq_stabilizer {t : ZMod (2 * n) → V}
    (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n)
    (hT : IsThick Γ) (hM : MoufangCondition D Γ n)
    [(cartan (moufangB D Γ n t) (moufangN D Γ n t)).Normal] :
    parabolic (moufangB D Γ n t) (moufangN D Γ n t)
        ({titsW1 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM} :
          Set (WeylGroup (moufangB D Γ n t) (moufangN D Γ n t))) =
      (MulAction.stabilizer D (t (n + 1))).subgroupOf (littleGroup D Γ n) := by
  let B := moufangB D Γ n t
  let N := moufangN D Γ n t
  let w : WeylGroup B N := titsW1 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM
  let S : Subgroup ↥(littleGroup D Γ n) :=
    (MulAction.stabilizer D (t (n + 1))).subgroupOf (littleGroup D Γ n)
  have hset : parabolicSet B N ({w} : Set (WeylGroup B N)) =
      (B : Set ↥(littleGroup D Γ n)) ∪ dc B N w := by
    rw [parabolicSet, bruhatSet, closure_titsW1_eq (t := t) ht hn hP hT hM]
    ext x
    simp only [Set.mem_iUnion, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_union, dc_one]
    constructor
    · rintro ⟨u, rfl | rfl, hx⟩
      · exact Or.inl (by simpa [dc_one] using hx)
      · exact Or.inr hx
    · intro hx
      rcases hx with hx | hx
      · exact ⟨1, Or.inl rfl, by simpa [dc_one] using hx⟩
      · exact ⟨w, Or.inr rfl, hx⟩
  apply le_antisymm
  · rw [parabolic, hset]
    change Subgroup.closure ((B : Set ↥(littleGroup D Γ n)) ∪ dc B N w) ≤ S
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with hxB | hxdc
    · show x ∈ S
      rw [show S = (MulAction.stabilizer D (t (n + 1))).subgroupOf
        (littleGroup D Γ n) from rfl, Subgroup.mem_subgroupOf,
        MulAction.mem_stabilizer_iff]
      exact (mem_moufangB.mp hxB).2
    · rw [dc] at hxdc
      obtain ⟨nN, hnclass, hx⟩ := hxdc
      obtain ⟨b1, hb1, b2, hb2, rfl⟩ := Set.mem_mul.1 hx
      obtain ⟨a1, ha1, b1', hb1', rfl⟩ := Set.mem_mul.1 hb1
      rw [Set.mem_singleton_iff] at hb1'
      subst hb1'
      have hnfix := lift_titsW1_fixes_vertex1 (t := t) ht hn hP hT hM nN hnclass
      have hb1fix : (((a1 : ↥(littleGroup D Γ n)) : D)) • t (n + 1) = t (n + 1) :=
        (mem_moufangB.mp ha1).2
      have hb2fix : (((b2 : ↥(littleGroup D Γ n)) : D)) • t (n + 1) = t (n + 1) :=
        (mem_moufangB.mp hb2).2
      show (((a1 * (nN : ↥(littleGroup D Γ n)) * b2 : ↥(littleGroup D Γ n)) : D)) •
        t (n + 1) = t (n + 1)
      rw [Subgroup.coe_mul, Subgroup.coe_mul, mul_smul, mul_smul,
        hb2fix, hnfix, hb1fix]
  · intro x hx
    have hxunion := stabilizer_vertex1_subset (t := t) ht hn hP hT hM hx
    rw [parabolic, hset]
    exact Subgroup.subset_closure hxunion

theorem stabilizer_vertex2_subset {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ)
    (hM : MoufangCondition D Γ n)
    [(cartan (moufangB D Γ n t) (moufangN D Γ n t)).Normal] :
    ((MulAction.stabilizer D (t n)).subgroupOf (littleGroup D Γ n) :
      Set ↥(littleGroup D Γ n)) ⊆
      (moufangB D Γ n t : Set ↥(littleGroup D Γ n)) ∪
        dc (moufangB D Γ n t) (moufangN D Γ n t)
          (titsW2 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM) := by
  intro g hg
  have hgv : (((g : ↥(littleGroup D Γ n)) : D)) • t n = t n :=
    MulAction.mem_stabilizer_iff.mp (Subgroup.mem_subgroupOf.mp hg)
  let nN : ↥(moufangN D Γ n t) := reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM
  have hclass : (nN : WeylGroup (moufangB D Γ n t) (moufangN D Γ n t)) =
      titsW2 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM := rfl
  have hnv : ((nN : ↥(littleGroup D Γ n)) : D) • t n = t n := by
    have h := reflTwoN_smul_zmod (t := t) ht hn hP hT hM (n : ZMod (2 * n))
    rw [show 2 * (n : ZMod (2 * n)) - (n : ZMod (2 * n)) =
      (n : ZMod (2 * n)) by ring] at h
    exact h
  exact stabilizer_of_moved_edge_subset_swapped (t := t) ht hn hP hT hM nN
    (titsW2 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM) hclass
    ((n : ZMod (2 * n)) - 1)
    (t (n + 1)) (t n) (by rw [baseChamber, Set.pair_comm])
    (by exact (ht.2 (n : ZMod (2 * n))).symm)
    (by exact (apt_ne_succ ht (by omega) (n : ZMod (2 * n))).symm)
    rfl rfl
    (reflTwo_moved_chamber (t := t) ht hn hP hT hM) hnv
    (by
      rw [aptEdge]
      right
      rw [show (n : ZMod (2 * n)) - 1 + 1 = (n : ZMod (2 * n)) by ring]
      rfl)
    (by
      rw [aptEdge]
      intro hmem
      rcases Set.mem_insert_iff.1 hmem with h | h
      · have h' : t (((n : ZMod (2 * n)) - 1) + 2) = t ((n : ZMod (2 * n)) - 1) := by
          rw [show ((n : ZMod (2 * n)) - 1) + 2 = (n : ZMod (2 * n)) + 1 by ring]
          exact h
        exact (apt_ne_two_zmod ht (by omega) ((n : ZMod (2 * n)) - 1)) h'.symm
      · exact (apt_ne_succ ht (by omega) (n : ZMod (2 * n))).symm (by
          rw [show (n : ZMod (2 * n)) - 1 + 1 = (n : ZMod (2 * n)) by ring] at h
          exact h))
    (rootL (D := D) (Γ := Γ) (n := n) t (n : ℤ))
    (rootL_le_littleBorel (t := t) ht hn (by omega) le_rfl)
    (by
      intro yv hyv
      have hyvD : ((yv : ↥(littleGroup D Γ n)) : D) ∈ aptRoot D Γ n t (n : ℤ) := by
        have hyv' := hyv
        rw [rootL, Subgroup.mem_subgroupOf, rootD, if_pos (by omega)] at hyv'
        exact hyv'
      have h := aptRoot_fix (t := t) ht (g := ((yv : ↥(littleGroup D Γ n)) : D)) hyvD hn
        (k := (n : ℤ)) (r := 0) le_rfl (by omega)
      simpa [apt] using h)
    (by
      intro y y' hy hy' hne hne'
      have hcast : apt t (n : ℤ) = t n := by
        show t ((((n : ℤ) : ℤ) : ZMod (2 * n))) = t n
        congr 1
        push_cast
        rfl
      have hprev : apt t ((n : ℤ) + 1) = t (n + 1) := by
        show t (((((n : ℤ) + 1 : ℤ)) : ZMod (2 * n))) = t (n + 1)
        congr 1
        push_cast
        ring
      obtain ⟨yv, hyv, hyvact⟩ := aptRoot_exists_smul_of_adj_start (t := t) ht hn hM
        (k := (n : ℤ)) (y := y) (y' := y') (by rwa [hcast]) (by rwa [hcast])
        (by rwa [hprev]) (by rwa [hprev])
      refine ⟨⟨yv, aptRoot_le_littleGroup ht (by omega) (n : ℤ) hyv⟩, ?_, hyvact⟩
      rw [rootL, Subgroup.mem_subgroupOf, rootD, if_pos (by omega)]
      exact hyv)
    (g := g) hgv

theorem parabolic_titsW2_eq_stabilizer {t : ZMod (2 * n) → V}
    (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n)
    (hT : IsThick Γ) (hM : MoufangCondition D Γ n)
    [(cartan (moufangB D Γ n t) (moufangN D Γ n t)).Normal] :
    parabolic (moufangB D Γ n t) (moufangN D Γ n t)
        ({titsW2 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM} :
          Set (WeylGroup (moufangB D Γ n t) (moufangN D Γ n t))) =
      (MulAction.stabilizer D (t n)).subgroupOf (littleGroup D Γ n) := by
  let B := moufangB D Γ n t
  let N := moufangN D Γ n t
  let w : WeylGroup B N := titsW2 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM
  let S : Subgroup ↥(littleGroup D Γ n) :=
    (MulAction.stabilizer D (t n)).subgroupOf (littleGroup D Γ n)
  have hset : parabolicSet B N ({w} : Set (WeylGroup B N)) =
      (B : Set ↥(littleGroup D Γ n)) ∪ dc B N w := by
    rw [parabolicSet, bruhatSet, closure_titsW2_eq (t := t) ht hn hP hT hM]
    ext x
    simp only [Set.mem_iUnion, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_union, dc_one]
    constructor
    · rintro ⟨u, rfl | rfl, hx⟩
      · exact Or.inl (by simpa [dc_one] using hx)
      · exact Or.inr hx
    · intro hx
      rcases hx with hx | hx
      · exact ⟨1, Or.inl rfl, by simpa [dc_one] using hx⟩
      · exact ⟨w, Or.inr rfl, hx⟩
  apply le_antisymm
  · rw [parabolic, hset]
    change Subgroup.closure ((B : Set ↥(littleGroup D Γ n)) ∪ dc B N w) ≤ S
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with hxB | hxdc
    · show x ∈ S
      rw [show S = (MulAction.stabilizer D (t n)).subgroupOf
        (littleGroup D Γ n) from rfl, Subgroup.mem_subgroupOf,
        MulAction.mem_stabilizer_iff]
      exact (mem_moufangB.mp hxB).1
    · rw [dc] at hxdc
      obtain ⟨nN, hnclass, hx⟩ := hxdc
      obtain ⟨b1, hb1, b2, hb2, rfl⟩ := Set.mem_mul.1 hx
      obtain ⟨a1, ha1, b1', hb1', rfl⟩ := Set.mem_mul.1 hb1
      rw [Set.mem_singleton_iff] at hb1'
      subst hb1'
      have hnfix := lift_titsW2_fixes_vertex_n (t := t) ht hn hP hT hM nN hnclass
      have hb1fix : (((a1 : ↥(littleGroup D Γ n)) : D)) • t n = t n :=
        (mem_moufangB.mp ha1).1
      have hb2fix : (((b2 : ↥(littleGroup D Γ n)) : D)) • t n = t n :=
        (mem_moufangB.mp hb2).1
      show (((a1 * (nN : ↥(littleGroup D Γ n)) * b2 : ↥(littleGroup D Γ n)) : D)) •
        t n = t n
      rw [Subgroup.coe_mul, Subgroup.coe_mul, mul_smul, mul_smul,
        hb2fix, hnfix, hb1fix]
  · intro x hx
    have hxunion := stabilizer_vertex2_subset (t := t) ht hn hP hT hM hx
    rw [parabolic, hset]
    exact Subgroup.subset_closure hxunion

end CFSG.Quasithin.Stroth
