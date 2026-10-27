module

public import CFSG.Quasithin.Recognition.Stroth.MoufangTits

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Quasithin CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.Geometry.GeneralizedPolygons

open scoped Pointwise

variable {V : Type} [Fintype V] {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
  {n : ℕ} {D : Type} [Group D] [MulAction D V] [FaithfulSMul D V] [GraphAction D Γ]

@[expose] def baseChamber (t : ZMod (2 * n) → V) : Set V :=
  {t n, t (n + 1)}

theorem reflTwoN_smul_zmod {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ)
    (hM : MoufangCondition D Γ n) (k : ZMod (2 * n)) :
    ((reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM : ↥(moufangN D Γ n t)) : D) •
        t k = t (2 * (n : ZMod (2 * n)) - k) := by
  haveI : NeZero (2 * n) := ⟨by omega⟩
  have hcast : ((2 * (n : ℤ) - (k.val : ℤ) : ℤ) : ZMod (2 * n)) =
      2 * (n : ZMod (2 * n)) - k := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  have hk : (((k.val : ℤ) : ZMod (2 * n))) = k := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  calc ((reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM : ↥(moufangN D Γ n t)) : D) • t k
      = (reflTwo ht hn hP hT hM) • apt t (k.val : ℤ) := by
        rw [reflTwoN_coeD]
        congr 1
        simpa [apt] using congrArg t hk.symm
    _ = apt t (2 * (n : ℤ) - (k.val : ℤ)) :=
        reflTwo_smul (t := t) ht hn hP hT hM (k.val : ℤ)
    _ = t (2 * (n : ZMod (2 * n)) - k) := by
        show t ((((2 * (n : ℤ) - (k.val : ℤ) : ℤ)) : ZMod (2 * n))) = _
        rw [hcast]

theorem reflTwoN_smul_aptEdge {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ)
    (hM : MoufangCondition D Γ n) (k : ZMod (2 * n)) :
    ((reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM : ↥(moufangN D Γ n t)) : D) •
        aptEdge t k = aptEdge t (2 * (n : ZMod (2 * n)) - k - 1) := by
  rw [aptEdge, Set.smul_set_insert, Set.smul_set_singleton,
    reflTwoN_smul_zmod (t := t) ht hn hP hT hM k,
    reflTwoN_smul_zmod (t := t) ht hn hP hT hM (k + 1)]
  rw [aptEdge, show 2 * (n : ZMod (2 * n)) - (k + 1) = 2 * (n : ZMod (2 * n)) - k - 1 by ring,
    show 2 * (n : ZMod (2 * n)) - k - 1 + 1 = 2 * (n : ZMod (2 * n)) - k by ring,
    Set.pair_comm]

theorem aptEdge_baseChamber (t : ZMod (2 * n) → V) :
    aptEdge t (n : ZMod (2 * n)) = baseChamber t := by
  rw [aptEdge, baseChamber, show (n : ZMod (2 * n)) + 1 = n + 1 by ring]

theorem aptEdge_adj {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 2 ≤ n) (p : ZMod (2 * n)) : Γ.Adj (t p) (t (p + 1)) := by
  haveI : NeZero (2 * n) := ⟨by omega⟩
  have h := apt_adj ht (p.val : ℤ)
  have h0 : apt t (p.val : ℤ) = t p := by
    show t (((p.val : ℤ) : ZMod (2 * n))) = t p
    congr 1
    push_cast
    rw [ZMod.natCast_zmod_val]
  have h1 : apt t ((p.val : ℤ) + 1) = t (p + 1) := by
    show t ((((p.val : ℤ) + 1 : ℤ) : ZMod (2 * n))) = t (p + 1)
    congr 1
    push_cast
    rw [ZMod.natCast_zmod_val]
  rwa [h0, h1] at h

theorem stabilizer_of_moved_edge_subset {t : ZMod (2 * n) → V}
    (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n)
    (hT : IsThick Γ) (hM : MoufangCondition D Γ n)
    (nN : ↥(moufangN D Γ n t)) (s : WeylGroup (moufangB D Γ n t) (moufangN D Γ n t))
    (hclass : (nN : WeylGroup (moufangB D Γ n t) (moufangN D Γ n t)) = s)
    (p : ZMod (2 * n))
    (hmoved : ((nN : ↥(littleGroup D Γ n)) : D) • baseChamber t = aptEdge t p)
    (hnv : ((nN : ↥(littleGroup D Γ n)) : D) • t (n + 1) = t (n + 1))
    (hv : t (n + 1) ∈ aptEdge t p) (hu : t n ∉ aptEdge t p)
    (Us : Subgroup ↥(littleGroup D Γ n)) (hUsB : Us ≤ moufangB D Γ n t)
    (hUsFixv : ∀ yv ∈ Us, ((yv : ↥(littleGroup D Γ n)) : D) • t (n + 1) = t (n + 1))
    (htrans : ∀ y y' : V, Γ.Adj (t (n + 1)) y → Γ.Adj (t (n + 1)) y' →
      y ≠ t n → y' ≠ t n →
      ∃ yv ∈ Us, ((yv : ↥(littleGroup D Γ n)) : D) • y = y')
    (g : ↥(littleGroup D Γ n))
    (hgv : ((g : ↥(littleGroup D Γ n)) : D) • t (n + 1) = t (n + 1)) :
    letI : (cartan (moufangB D Γ n t) (moufangN D Γ n t)).Normal :=
      moufangCartan_normal (t := t) ht hn hP hT
    g ∈ (moufangB D Γ n t : Set ↥(littleGroup D Γ n)) ∪
      dc (moufangB D Γ n t) (moufangN D Γ n t) s := by
  letI : (cartan (moufangB D Γ n t) (moufangN D Γ n t)).Normal :=
    moufangCartan_normal (t := t) ht hn hP hT
  haveI : NeZero (2 * n) := ⟨by omega⟩
  classical
  by_cases hc : ((g : ↥(littleGroup D Γ n)) : D) • baseChamber t = baseChamber t
  · left
    rw [moufangB]
    change g ∈ moufangB D Γ n t
    rw [mem_moufangB]
    constructor
    · have hmem : ((g : ↥(littleGroup D Γ n)) : D) • t n ∈
          ((g : ↥(littleGroup D Γ n)) : D) • baseChamber t := by
        refine Set.smul_mem_smul_set ?_
        rw [baseChamber]
        exact Set.mem_insert_iff.2 (Or.inl rfl)
      rw [hc, baseChamber] at hmem
      rcases hmem with h | h
      · exact h
      · exfalso
        have h' : ((g : ↥(littleGroup D Γ n)) : D) • t n =
            ((g : ↥(littleGroup D Γ n)) : D) • t (n + 1) := by
          rw [h, hgv]
        have h2 : t n = t (n + 1) := by
          have := congrArg (fun v => ((g : ↥(littleGroup D Γ n)) : D)⁻¹ • v) h'
          simpa using this
        have h3 : (1 : ZMod (2 * n)) = 0 := by
          have h4 := ht.1 h2
          have h5 := congrArg (fun x : ZMod (2 * n) => x - (n : ZMod (2 * n))) h4
          rw [sub_self, add_sub_cancel_left] at h5
          exact h5.symm
        have h4 : (2 : ZMod (2 * n)) = 0 := by
          rw [show (2 : ZMod (2 * n)) = 1 + 1 by norm_num, h3, zero_add]
        exact two_ne_zero_zmod (by omega) h4
    · exact hgv
  · right
    have hgu_ne : ((g : ↥(littleGroup D Γ n)) : D) • t n ≠ t n := by
      intro h
      apply hc
      rw [baseChamber, Set.smul_set_insert, Set.smul_set_singleton, h, hgv]
    have hbase_adj : Γ.Adj (t n) (t (n + 1)) := ht.2 (n : ZMod (2 * n))
    have hgu_adj : Γ.Adj (t (n + 1)) (((g : ↥(littleGroup D Γ n)) : D) • t n) := by
      have h : Γ.Adj (((g : ↥(littleGroup D Γ n)) : D) • t n)
          (((g : ↥(littleGroup D Γ n)) : D) • t (n + 1)) := by
        exact (GraphAction.adj_smul ((g : ↥(littleGroup D Γ n)) : D)
          (t n) (t (n + 1))).mpr hbase_adj
      rw [hgv] at h
      exact h.symm
    have hvw : ∃ w : V, aptEdge t p = {t (n + 1), w} ∧ w ≠ t n ∧
        Γ.Adj (t (n + 1)) w := by
      have hv' : t (n + 1) ∈ aptEdge t p := hv
      rw [aptEdge] at hv'
      rcases Set.mem_insert_iff.1 hv' with h | h
      · refine ⟨t (p + 1), ?_, ?_, ?_⟩
        · rw [aptEdge, h]
        · intro hwu
          apply hu
          rw [← hwu]
          exact Set.mem_insert_of_mem _ rfl
        · rw [h]
          exact aptEdge_adj (t := t) ht (by omega) p
      · refine ⟨t p, ?_, ?_, ?_⟩
        · rw [aptEdge, h]
          exact Set.pair_comm _ _
        · intro hwu
          apply hu
          rw [← hwu]
          exact Set.mem_insert_iff.2 (Or.inl rfl)
        · rw [h]
          exact (aptEdge_adj (t := t) ht (by omega) p).symm
    obtain ⟨w, hw, hwu, hwadj⟩ := hvw
    obtain ⟨yv, hyvU, hyvact⟩ :=
      htrans w (((g : ↥(littleGroup D Γ n)) : D) • t n) hwadj hgu_adj hwu hgu_ne
    let hL : ↥(littleGroup D Γ n) := yv * nN
    have hLcoe : ((hL : ↥(littleGroup D Γ n)) : D) = yv * nN := rfl
    have hh : ((yv * nN : ↥(littleGroup D Γ n)) : D) • baseChamber t =
        ((g : ↥(littleGroup D Γ n)) : D) • baseChamber t := by
      calc ((yv * nN : ↥(littleGroup D Γ n)) : D) • baseChamber t
          = ((yv : ↥(littleGroup D Γ n)) : D) •
              (((nN : ↥(littleGroup D Γ n)) : D) • baseChamber t) := by
            rw [Subgroup.coe_mul, mul_smul]
        _ = ((yv : ↥(littleGroup D Γ n)) : D) • ({t (n + 1), w} : Set V) := by
            rw [hmoved, hw]
        _ = {t (n + 1), ((g : ↥(littleGroup D Γ n)) : D) • t n} := by
            rw [Set.smul_set_insert, Set.smul_set_singleton,
              hUsFixv yv hyvU, hyvact]
        _ = ((g : ↥(littleGroup D Γ n)) : D) • ({t n, t (n + 1)} : Set V) := by
            rw [Set.smul_set_insert, Set.smul_set_singleton, hgv]
            exact (Set.pair_comm _ _).symm
        _ = ((g : ↥(littleGroup D Γ n)) : D) • baseChamber t := by
            rw [baseChamber]
    have hhL : ((hL : ↥(littleGroup D Γ n)) : D) • baseChamber t =
        ((g : ↥(littleGroup D Γ n)) : D) • baseChamber t := by
      rw [hLcoe]
      exact hh
    have hfixvH : ((hL : ↥(littleGroup D Γ n)) : D) • t (n + 1) = t (n + 1) := by
      have h1 : ((yv : ↥(littleGroup D Γ n)) : D) • t (n + 1) = t (n + 1) :=
        hUsFixv yv hyvU
      have h2 : ((nN : ↥(littleGroup D Γ n)) : D) • t (n + 1) = t (n + 1) := hnv
      rw [hLcoe, mul_smul, h2, h1]
    have hco : (((hL⁻¹ * g : ↥(littleGroup D Γ n))) : D) =
        (((hL : ↥(littleGroup D Γ n)) : D)⁻¹) *
          (((g : ↥(littleGroup D Γ n)) : D)) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
    have hkfix : (((hL⁻¹ * g : ↥(littleGroup D Γ n))) : D) •
        baseChamber t = baseChamber t := by
      rw [hco]
      calc ((((hL : ↥(littleGroup D Γ n)) : D)⁻¹) *
            ((g : ↥(littleGroup D Γ n)) : D)) • baseChamber t
          = (((hL : ↥(littleGroup D Γ n)) : D)⁻¹) •
              (((g : ↥(littleGroup D Γ n)) : D) • baseChamber t) := by
            rw [mul_smul]
        _ = (((hL : ↥(littleGroup D Γ n)) : D)⁻¹) •
              (((hL : ↥(littleGroup D Γ n)) : D) • baseChamber t) := by
            rw [← hhL]
        _ = baseChamber t := by
            rw [inv_smul_smul]
    have hfixv : (((hL⁻¹ * g : ↥(littleGroup D Γ n))) : D) • t (n + 1) =
        t (n + 1) := by
      rw [hco]
      calc ((((hL : ↥(littleGroup D Γ n)) : D)⁻¹) *
            ((g : ↥(littleGroup D Γ n)) : D)) • t (n + 1)
          = (((hL : ↥(littleGroup D Γ n)) : D)⁻¹) •
              (((g : ↥(littleGroup D Γ n)) : D) • t (n + 1)) := by
            rw [mul_smul]
        _ = (((hL : ↥(littleGroup D Γ n)) : D)⁻¹) • t (n + 1) := by rw [hgv]
        _ = t (n + 1) := by
            conv_lhs => rw [← hfixvH]
            rw [inv_smul_smul]
    have hker : ((hL⁻¹ * g : ↥(littleGroup D Γ n))) ∈ moufangB D Γ n t := by
      rw [moufangB]
      change ((hL⁻¹ * g : ↥(littleGroup D Γ n))) ∈ moufangB D Γ n t
      rw [mem_moufangB]
      constructor
      · have hmem : (((hL⁻¹ * g : ↥(littleGroup D Γ n))) : D) • t n ∈
            (((hL⁻¹ * g : ↥(littleGroup D Γ n))) : D) • baseChamber t := by
          refine Set.smul_mem_smul_set ?_
          rw [baseChamber]
          exact Set.mem_insert_iff.2 (Or.inl rfl)
        rw [hkfix, baseChamber] at hmem
        rcases hmem with h | h
        · exact h
        · exfalso
          have h' : (((hL⁻¹ * g : ↥(littleGroup D Γ n))) : D) • t n =
              (((hL⁻¹ * g : ↥(littleGroup D Γ n))) : D) • t (n + 1) := by
            rw [h, hfixv]
          have h2 : t n = t (n + 1) := by
            have h6 := congrArg
              (fun v => (((hL⁻¹ * g : ↥(littleGroup D Γ n))) : D)⁻¹ • v) h'
            simpa using h6
          have h3 : (1 : ZMod (2 * n)) = 0 := by
            have h4 := ht.1 h2
            have h5 := congrArg (fun x : ZMod (2 * n) => x - (n : ZMod (2 * n))) h4
            rw [sub_self, add_sub_cancel_left] at h5
            exact h5.symm
          have h4 : (2 : ZMod (2 * n)) = 0 := by
            rw [show (2 : ZMod (2 * n)) = 1 + 1 by norm_num, h3, zero_add]
          exact two_ne_zero_zmod (by omega) h4
      · exact hfixv
    have hrepr : g = hL * ((hL⁻¹ * g : ↥(littleGroup D Γ n))) := by
      rw [← mul_assoc, mul_inv_cancel, one_mul]
    have hmemdc : g ∈ dc (moufangB D Γ n t) (moufangN D Γ n t) s := by
      rw [mem_dc_of_lift (B := moufangB D Γ n t) (N := moufangN D Γ n t) (w := s)
        (n := nN) hclass]
      refine ⟨yv, hUsB hyvU, ((hL⁻¹ * g : ↥(littleGroup D Γ n))), hker, ?_⟩
      conv_lhs => rw [hrepr]
    exact hmemdc

theorem reflOne_moved_chamber {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ)
    (hM : MoufangCondition D Γ n) :
    ((reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM : ↥(moufangN D Γ n t)) : D) •
        baseChamber t = aptEdge t ((n : ZMod (2 * n)) + 1) := by
  rw [← aptEdge_baseChamber (n := n) t, reflOneN_smul_aptEdge (t := t) ht hn hP hT hM]
  congr 2
  ring

theorem reflTwo_moved_chamber {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ)
    (hM : MoufangCondition D Γ n) :
    ((reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM : ↥(moufangN D Γ n t)) : D) •
        baseChamber t = aptEdge t ((n : ZMod (2 * n)) - 1) := by
  rw [← aptEdge_baseChamber (n := n) t, reflTwoN_smul_aptEdge (t := t) ht hn hP hT hM]
  congr 2
  ring

theorem stabilizer_of_moved_edge_subset_swapped {t : ZMod (2 * n) → V}
    (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n)
    (hT : IsThick Γ) (hM : MoufangCondition D Γ n)
    (nN : ↥(moufangN D Γ n t)) (s : WeylGroup (moufangB D Γ n t) (moufangN D Γ n t))
    (hclass : (nN : WeylGroup (moufangB D Γ n t) (moufangN D Γ n t)) = s)
    (p : ZMod (2 * n))
    (u v : V) (hbase : baseChamber t = {u, v}) (huv : Γ.Adj u v) (hne : u ≠ v)
    (hu_eq : u = t (n + 1)) (hv_eq : v = t n)
    (hmoved : ((nN : ↥(littleGroup D Γ n)) : D) • baseChamber t = aptEdge t p)
    (hnv : ((nN : ↥(littleGroup D Γ n)) : D) • v = v)
    (hv : v ∈ aptEdge t p) (hu : u ∉ aptEdge t p)
    (Us : Subgroup ↥(littleGroup D Γ n)) (hUsB : Us ≤ moufangB D Γ n t)
    (hUsFixv : ∀ yv ∈ Us, ((yv : ↥(littleGroup D Γ n)) : D) • v = v)
    (htrans : ∀ y y' : V, Γ.Adj (v) y → Γ.Adj (v) y' →
      y ≠ u → y' ≠ u →
      ∃ yv ∈ Us, ((yv : ↥(littleGroup D Γ n)) : D) • y = y')
    (g : ↥(littleGroup D Γ n))
    (hgv : ((g : ↥(littleGroup D Γ n)) : D) • v = v) :
    letI : (cartan (moufangB D Γ n t) (moufangN D Γ n t)).Normal :=
      moufangCartan_normal (t := t) ht hn hP hT
    g ∈ (moufangB D Γ n t : Set ↥(littleGroup D Γ n)) ∪
      dc (moufangB D Γ n t) (moufangN D Γ n t) s := by
  letI : (cartan (moufangB D Γ n t) (moufangN D Γ n t)).Normal :=
    moufangCartan_normal (t := t) ht hn hP hT
  haveI : NeZero (2 * n) := ⟨by omega⟩
  classical
  by_cases hc : ((g : ↥(littleGroup D Γ n)) : D) • baseChamber t = baseChamber t
  · left
    rw [moufangB]
    change g ∈ moufangB D Γ n t
    rw [mem_moufangB]
    constructor
    · rw [← hv_eq]
      exact hgv
    · have hmem : ((g : ↥(littleGroup D Γ n)) : D) • u ∈
          ((g : ↥(littleGroup D Γ n)) : D) • baseChamber t := by
        refine Set.smul_mem_smul_set ?_
        rw [hbase]
        exact Set.mem_insert_iff.2 (Or.inl rfl)
      rw [hc, hbase] at hmem
      rcases hmem with h | h
      · rw [← hu_eq]
        exact h
      · exfalso
        have h' : ((g : ↥(littleGroup D Γ n)) : D) • u =
            ((g : ↥(littleGroup D Γ n)) : D) • v := by
          rw [h, hgv]
        have h2 : u = v := by
          have := congrArg (fun w => ((g : ↥(littleGroup D Γ n)) : D)⁻¹ • w) h'
          simpa using this
        exact hne h2
  · right
    have hgu_ne : ((g : ↥(littleGroup D Γ n)) : D) • u ≠ u := by
      intro h
      apply hc
      rw [hbase, Set.smul_set_insert, Set.smul_set_singleton, h, hgv]
    have hbase_adj : Γ.Adj u v := huv
    have hgu_adj : Γ.Adj (v) (((g : ↥(littleGroup D Γ n)) : D) • u) := by
      have h : Γ.Adj (((g : ↥(littleGroup D Γ n)) : D) • u)
          (((g : ↥(littleGroup D Γ n)) : D) • v) := by
        exact (GraphAction.adj_smul ((g : ↥(littleGroup D Γ n)) : D)
          (u) (v)).mpr hbase_adj
      rw [hgv] at h
      exact h.symm
    have hvw : ∃ w : V, aptEdge t p = {v, w} ∧ w ≠ u ∧
        Γ.Adj (v) w := by
      have hv' : v ∈ aptEdge t p := hv
      rw [aptEdge] at hv'
      rcases Set.mem_insert_iff.1 hv' with h | h
      · refine ⟨t (p + 1), ?_, ?_, ?_⟩
        · rw [aptEdge, h]
        · intro hwu
          apply hu
          rw [← hwu]
          exact Set.mem_insert_of_mem _ rfl
        · rw [h]
          exact aptEdge_adj (t := t) ht (by omega) p
      · refine ⟨t p, ?_, ?_, ?_⟩
        · rw [aptEdge, h]
          exact Set.pair_comm _ _
        · intro hwu
          apply hu
          rw [← hwu]
          exact Set.mem_insert_iff.2 (Or.inl rfl)
        · rw [h]
          exact (aptEdge_adj (t := t) ht (by omega) p).symm
    obtain ⟨w, hw, hwu, hwadj⟩ := hvw
    obtain ⟨yv, hyvU, hyvact⟩ :=
      htrans w (((g : ↥(littleGroup D Γ n)) : D) • u) hwadj hgu_adj hwu hgu_ne
    let hL : ↥(littleGroup D Γ n) := yv * nN
    have hLcoe : ((hL : ↥(littleGroup D Γ n)) : D) = yv * nN := rfl
    have hh : ((yv * nN : ↥(littleGroup D Γ n)) : D) • baseChamber t =
        ((g : ↥(littleGroup D Γ n)) : D) • baseChamber t := by
      calc ((yv * nN : ↥(littleGroup D Γ n)) : D) • baseChamber t
          = ((yv : ↥(littleGroup D Γ n)) : D) •
              (((nN : ↥(littleGroup D Γ n)) : D) • baseChamber t) := by
            rw [Subgroup.coe_mul, mul_smul]
        _ = ((yv : ↥(littleGroup D Γ n)) : D) • ({v, w} : Set V) := by
            rw [hmoved, hw]
        _ = {v, ((g : ↥(littleGroup D Γ n)) : D) • u} := by
            rw [Set.smul_set_insert, Set.smul_set_singleton,
              hUsFixv yv hyvU, hyvact]
        _ = ((g : ↥(littleGroup D Γ n)) : D) • ({u, v} : Set V) := by
            rw [Set.smul_set_insert, Set.smul_set_singleton, hgv]
            exact (Set.pair_comm _ _).symm
        _ = ((g : ↥(littleGroup D Γ n)) : D) • baseChamber t := by
            rw [hbase]
    have hhL : ((hL : ↥(littleGroup D Γ n)) : D) • baseChamber t =
        ((g : ↥(littleGroup D Γ n)) : D) • baseChamber t := by
      rw [hLcoe]
      exact hh
    have hfixvH : ((hL : ↥(littleGroup D Γ n)) : D) • v = v := by
      have h1 : ((yv : ↥(littleGroup D Γ n)) : D) • v = v :=
        hUsFixv yv hyvU
      have h2 : ((nN : ↥(littleGroup D Γ n)) : D) • v = v := hnv
      rw [hLcoe, mul_smul, h2, h1]
    have hco : (((hL⁻¹ * g : ↥(littleGroup D Γ n))) : D) =
        (((hL : ↥(littleGroup D Γ n)) : D)⁻¹) *
          (((g : ↥(littleGroup D Γ n)) : D)) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
    have hkfix : (((hL⁻¹ * g : ↥(littleGroup D Γ n))) : D) •
        baseChamber t = baseChamber t := by
      rw [hco]
      calc ((((hL : ↥(littleGroup D Γ n)) : D)⁻¹) *
            ((g : ↥(littleGroup D Γ n)) : D)) • baseChamber t
          = (((hL : ↥(littleGroup D Γ n)) : D)⁻¹) •
              (((g : ↥(littleGroup D Γ n)) : D) • baseChamber t) := by
            rw [mul_smul]
        _ = (((hL : ↥(littleGroup D Γ n)) : D)⁻¹) •
              (((hL : ↥(littleGroup D Γ n)) : D) • baseChamber t) := by
            rw [← hhL]
        _ = baseChamber t := by
            rw [inv_smul_smul]
    have hfixv : (((hL⁻¹ * g : ↥(littleGroup D Γ n))) : D) • v =
        v := by
      rw [hco]
      calc ((((hL : ↥(littleGroup D Γ n)) : D)⁻¹) *
            ((g : ↥(littleGroup D Γ n)) : D)) • v
          = (((hL : ↥(littleGroup D Γ n)) : D)⁻¹) •
              (((g : ↥(littleGroup D Γ n)) : D) • v) := by
            rw [mul_smul]
        _ = (((hL : ↥(littleGroup D Γ n)) : D)⁻¹) • v := by rw [hgv]
        _ = v := by
            conv_lhs => rw [← hfixvH]
            rw [inv_smul_smul]
    have hker : ((hL⁻¹ * g : ↥(littleGroup D Γ n))) ∈ moufangB D Γ n t := by
      rw [moufangB]
      change ((hL⁻¹ * g : ↥(littleGroup D Γ n))) ∈ moufangB D Γ n t
      rw [mem_moufangB]
      constructor
      · rw [← hv_eq]
        exact hfixv
      · have hmem : (((hL⁻¹ * g : ↥(littleGroup D Γ n))) : D) • u ∈
            (((hL⁻¹ * g : ↥(littleGroup D Γ n))) : D) • baseChamber t := by
          refine Set.smul_mem_smul_set ?_
          rw [hbase]
          exact Set.mem_insert_iff.2 (Or.inl rfl)
        rw [hkfix, hbase] at hmem
        rcases hmem with h | h
        · rw [← hu_eq]
          exact h
        · exfalso
          have h' : (((hL⁻¹ * g : ↥(littleGroup D Γ n))) : D) • u =
              (((hL⁻¹ * g : ↥(littleGroup D Γ n))) : D) • v := by
            rw [h, hfixv]
          have h2 : u = v := by
            have h6 := congrArg
              (fun w => (((hL⁻¹ * g : ↥(littleGroup D Γ n))) : D)⁻¹ • w) h'
            simpa using h6
          exact hne h2
    have hrepr : g = hL * ((hL⁻¹ * g : ↥(littleGroup D Γ n))) := by
      rw [← mul_assoc, mul_inv_cancel, one_mul]
    have hmemdc : g ∈ dc (moufangB D Γ n t) (moufangN D Γ n t) s := by
      rw [mem_dc_of_lift (B := moufangB D Γ n t) (N := moufangN D Γ n t) (w := s)
        (n := nN) hclass]
      refine ⟨yv, hUsB hyvU, ((hL⁻¹ * g : ↥(littleGroup D Γ n))), hker, ?_⟩
      conv_lhs => rw [hrepr]
    exact hmemdc

end CFSG.Quasithin.Stroth
