module

public import CFSG.Quasithin.Recognition.Stroth.MoufangBN3

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Quasithin CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.Geometry.GeneralizedPolygons

open scoped Pointwise

variable {V : Type} [Fintype V] {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
  {n : ℕ} {D : Type} [Group D] [MulAction D V] [FaithfulSMul D V] [GraphAction D Γ]

theorem exists_moufangN_smul_base_edge {t : ZMod (2 * n) → V}
    (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n)
    (hT : IsThick Γ) (hM : MoufangCondition D Γ n) (k : ZMod (2 * n)) :
    ∃ nN : ↥(moufangN D Γ n t),
      ((nN : ↥(littleGroup D Γ n)) : D) • baseChamber t = aptEdge t k := by
  letI : MulAction ↥(moufangN D Γ n t) (AptEdge t) := aptEdgeMulAction ht hn hP hT
  have hcard : (MulAction.orbit ↥(moufangN D Γ n t) (aptEdgeOf t (n : ZMod (2 * n)))).ncard =
      (Set.univ : Set (AptEdge t)).ncard := by
    rw [Set.ncard_univ, card_orbit_aptEdge_base (t := t) ht hn hP hT hM,
      card_aptEdge (t := t) ht hn]
  have heq : MulAction.orbit ↥(moufangN D Γ n t) (aptEdgeOf t (n : ZMod (2 * n))) =
      (Set.univ : Set (AptEdge t)) :=
    Set.eq_of_subset_of_ncard_le (Set.subset_univ _) (by rw [hcard])
  have hmem : aptEdgeOf t k ∈
      MulAction.orbit ↥(moufangN D Γ n t) (aptEdgeOf t (n : ZMod (2 * n))) := by
    rw [heq]
    exact Set.mem_univ _
  obtain ⟨nN, hnN⟩ := MulAction.mem_orbit_iff.mp hmem
  refine ⟨nN, ?_⟩
  have h := congrArg Subtype.val hnN
  change ((nN : D) • baseChamber t) = aptEdge t k
  exact h

theorem exists_smul_base_vertex {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ)
    (hM : MoufangCondition D Γ n) (u : V) :
    ∃ x : ↥(littleGroup D Γ n),
      (((x : ↥(littleGroup D Γ n)) : D) • t n = u) ∨
        (((x : ↥(littleGroup D Γ n)) : D) • t (n + 1) = u) := by
  have hdeg : 0 < Γ.degree u := by
    have := hT u
    omega
  obtain ⟨v, huv⟩ := (SimpleGraph.degree_pos_iff_exists_adj Γ u).mp hdeg
  obtain ⟨mD, hmM, k, hk | hk⟩ :=
    aptRootGroup_exists_smul_apt_edge (t := t) ht hn hP hT hM huv
  · obtain ⟨nN, hnN⟩ := exists_moufangN_smul_base_edge (t := t) ht hn hP hT hM k
    have hmL : mD ∈ littleGroup D Γ n := by
      rw [← aptRootGroup_eq_littleGroup (t := t) ht hn hP hT hM]
      exact hmM
    let m : ↥(littleGroup D Γ n) := ⟨mD, hmL⟩
    have hnk : t k ∈ ((nN : ↥(littleGroup D Γ n)) : D) • baseChamber t := by
      rw [hnN]
      exact Set.mem_insert _ _
    rw [Set.mem_smul_set] at hnk
    obtain ⟨y, hy, hyk⟩ := hnk
    rcases Set.mem_insert_iff.1 hy with rfl | hy
    · refine ⟨m * nN, Or.inl ?_⟩
      change (mD * (nN : D)) • t n = u
      rw [mul_smul, hyk]
      simpa [apt] using hk.1
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      refine ⟨m * nN, Or.inr ?_⟩
      change (mD * (nN : D)) • t (n + 1) = u
      rw [mul_smul, hyk]
      simpa [apt] using hk.1
  · obtain ⟨nN, hnN⟩ := exists_moufangN_smul_base_edge (t := t) ht hn hP hT hM (k + 1)
    have hmL : mD ∈ littleGroup D Γ n := by
      rw [← aptRootGroup_eq_littleGroup (t := t) ht hn hP hT hM]
      exact hmM
    let m : ↥(littleGroup D Γ n) := ⟨mD, hmL⟩
    have hnk : t (k + 1) ∈ ((nN : ↥(littleGroup D Γ n)) : D) • baseChamber t := by
      rw [hnN]
      exact Set.mem_insert _ _
    rw [Set.mem_smul_set] at hnk
    obtain ⟨y, hy, hyk⟩ := hnk
    rcases Set.mem_insert_iff.1 hy with rfl | hy
    · refine ⟨m * nN, Or.inl ?_⟩
      change (mD * (nN : D)) • t n = u
      rw [mul_smul, hyk]
      simpa [apt] using hk.2
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      refine ⟨m * nN, Or.inr ?_⟩
      change (mD * (nN : D)) • t (n + 1) = u
      rw [mul_smul, hyk]
      simpa [apt] using hk.2

theorem faithfulOnBuilding_moufang {t : ZMod (2 * n) → V} (ht : IsPolygonApartment Γ n t)
    (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n) (hT : IsThick Γ)
    (hM : MoufangCondition D Γ n)
    [(cartan (moufangB D Γ n t) (moufangN D Γ n t)).Normal] :
    FaithfulOnBuilding (moufangB D Γ n t) (moufangN D Γ n t)
      (titsW1 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM)
      (titsW2 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM) := by
  intro g hg
  have hconj1 : ∀ x : ↥(littleGroup D Γ n),
      x * g * x⁻¹ ∈ parabolic (moufangB D Γ n t) (moufangN D Γ n t)
        ({titsW1 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM} : Set _) := by
    intro x
    have hmem := hg (((parabolic (moufangB D Γ n t) (moufangN D Γ n t)
      ({titsW1 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM} : Set _) :
        Subgroup ↥(littleGroup D Γ n)) : Set ↥(littleGroup D Γ n)) * {x})
      (Or.inl ⟨x, rfl⟩)
    have hx0 : x * g ∈ ((parabolic (moufangB D Γ n t) (moufangN D Γ n t)
        ({titsW1 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM} : Set _) :
          Subgroup ↥(littleGroup D Γ n)) : Set ↥(littleGroup D Γ n)) * {x} * {g} := by
      refine Set.mem_mul.2 ⟨x, ?_, g, Set.mem_singleton g, rfl⟩
      exact Set.mem_mul.2 ⟨1, Subgroup.one_mem _, x, Set.mem_singleton x, by simp⟩
    have hx : x * g ∈ ((parabolic (moufangB D Γ n t) (moufangN D Γ n t)
        ({titsW1 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM} : Set _) :
          Subgroup ↥(littleGroup D Γ n)) : Set ↥(littleGroup D Γ n)) * {x} := by
      rwa [hmem] at hx0
    obtain ⟨p, hp, q, hq, hpx⟩ := Set.mem_mul.1 hx
    rw [Set.mem_singleton_iff] at hq
    rw [hq] at hpx
    have hxpc : x * g * x⁻¹ = p := by
      rw [← hpx]
      group
    rwa [hxpc]
  have hconj2 : ∀ x : ↥(littleGroup D Γ n),
      x * g * x⁻¹ ∈ parabolic (moufangB D Γ n t) (moufangN D Γ n t)
        ({titsW2 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM} : Set _) := by
    intro x
    have hmem := hg (((parabolic (moufangB D Γ n t) (moufangN D Γ n t)
      ({titsW2 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM} : Set _) :
        Subgroup ↥(littleGroup D Γ n)) : Set ↥(littleGroup D Γ n)) * {x})
      (Or.inr ⟨x, rfl⟩)
    have hx0 : x * g ∈ ((parabolic (moufangB D Γ n t) (moufangN D Γ n t)
        ({titsW2 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM} : Set _) :
          Subgroup ↥(littleGroup D Γ n)) : Set ↥(littleGroup D Γ n)) * {x} * {g} := by
      refine Set.mem_mul.2 ⟨x, ?_, g, Set.mem_singleton g, rfl⟩
      exact Set.mem_mul.2 ⟨1, Subgroup.one_mem _, x, Set.mem_singleton x, by simp⟩
    have hx : x * g ∈ ((parabolic (moufangB D Γ n t) (moufangN D Γ n t)
        ({titsW2 (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM} : Set _) :
          Subgroup ↥(littleGroup D Γ n)) : Set ↥(littleGroup D Γ n)) * {x} := by
      rwa [hmem] at hx0
    obtain ⟨p, hp, q, hq, hpx⟩ := Set.mem_mul.1 hx
    rw [Set.mem_singleton_iff] at hq
    rw [hq] at hpx
    have hxpc : x * g * x⁻¹ = p := by
      rw [← hpx]
      group
    rwa [hxpc]
  have hfix1 : ∀ x : ↥(littleGroup D Γ n),
      (((g : ↥(littleGroup D Γ n)) : D)) • (x • t (n + 1)) = x • t (n + 1) := by
    intro x
    have hc := hconj1 x⁻¹
    rw [parabolic_titsW1_eq_stabilizer (t := t) ht hn hP hT hM] at hc
    have hv := MulAction.mem_stabilizer_iff.mp (Subgroup.mem_subgroupOf.mp hc)
    have h2 : (((x⁻¹ * g * x : ↥(littleGroup D Γ n)) : D)) • t (n + 1) = t (n + 1) := by
      simpa [inv_inv] using hv
    have := congrArg (fun w => (((x : ↥(littleGroup D Γ n)) : D)) • w) h2
    change (((g : ↥(littleGroup D Γ n)) : D)) •
      (((x : ↥(littleGroup D Γ n)) : D) • t (n + 1)) =
      (((x : ↥(littleGroup D Γ n)) : D) • t (n + 1))
    simpa [mul_smul] using this
  have hfix2 : ∀ x : ↥(littleGroup D Γ n),
      (((g : ↥(littleGroup D Γ n)) : D)) • (x • t n) = x • t n := by
    intro x
    have hc := hconj2 x⁻¹
    rw [parabolic_titsW2_eq_stabilizer (t := t) ht hn hP hT hM] at hc
    have hv := MulAction.mem_stabilizer_iff.mp (Subgroup.mem_subgroupOf.mp hc)
    have h2 : (((x⁻¹ * g * x : ↥(littleGroup D Γ n)) : D)) • t n = t n := by
      simpa [inv_inv] using hv
    have := congrArg (fun w => (((x : ↥(littleGroup D Γ n)) : D)) • w) h2
    change (((g : ↥(littleGroup D Γ n)) : D)) •
      (((x : ↥(littleGroup D Γ n)) : D) • t n) =
      (((x : ↥(littleGroup D Γ n)) : D) • t n)
    simpa [mul_smul] using this
  have hgfix : ∀ u : V, (((g : ↥(littleGroup D Γ n)) : D)) • u = u := by
    intro u
    obtain ⟨x, hx | hx⟩ := exists_smul_base_vertex (t := t) ht hn hP hT hM u
    · rw [← hx]
      exact hfix2 x
    · rw [← hx]
      exact hfix1 x
  apply Subtype.ext
  exact FaithfulSMul.eq_of_smul_eq_smul (m₁ := ((g : ↥(littleGroup D Γ n)) : D))
    (m₂ := 1) (by intro v; rw [one_smul]; exact hgfix v)

end CFSG.Quasithin.Stroth
