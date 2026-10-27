module

public import CFSG.OddTranspositions.OrbitUV
public import CFSG.Timmesfeld.ARS.BasicLines

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
  CFSG.Timmesfeld.Bridge.OddTransp CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.ARS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem card_commutator_gt_two (hD : IsOddTransp D) (hN : IsNormalSet D)
    {u w v : G} (htri : IsTriangle D u w v) (h4 : orderOf (u * v * w) = 4)
    (hno : ∀ x ∈ D, x ∈ Subgroup.closure {u, w} → IsTriangle D u x v →
      ¬ IsThirdKind u x v)
    (hm : 3 < orderOf (u * w)) :
    2 < Nat.card (⁅conjClosure (Subgroup.closure {u, w}) (u * v),
        Subgroup.zpowers u⁆ : Subgroup G) := by
  classical
  let A : Subgroup G := Subgroup.closure ({u, w} : Set G)
  let Q : Subgroup G := conjClosure A (u * v)
  let P : Subgroup G := ⁅Q, Subgroup.zpowers u⁆
  let R : Subgroup G := ⁅Q, Subgroup.zpowers w⁆
  have hS : SecondKindStructure u w v := secondKind_structure hD hN htri h4 hno
  have hc1 : u * v ≠ 1 :=
    fun h => htri.2.2.2.1 (hD.eq_of_mul_eq_one htri.1 h)
  have hcQ : u * v ∈ Q := by
    show u * v ∈ conjClosure A (u * v)
    exact Subgroup.subset_closure ⟨1, A.one_mem, by simp⟩
  have hA_le_K : A ≤ Subgroup.closure ({u, w, v} : Set G) := by
    apply Subgroup.closure_mono
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
    rcases hy with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  let O : Set G := {x : G | ∃ b ∈ A, x = b * (u * v) * b⁻¹}
  have hOcard : O.ncard = orderOf (u * w) := card_orbit_conj_uv hD hN htri h4 hno
  have hOsub : O ⊆ (Q : Set G) := by
    rintro x ⟨b, hbA, rfl⟩
    exact hS.normal b (hA_le_K hbA) (u * v) hcQ
  have hO_one : (1 : G) ∉ O := by
    rintro ⟨b, hbA, hb1⟩
    have hc_eq : u * v = 1 := by
      calc u * v = b⁻¹ * (b * (u * v) * b⁻¹) * b := by group
        _ = 1 := by rw [hb1.symm]; group
    exact hc1 hc_eq
  have hOncard : O.ncard ≤ Nat.card Q - 1 := by
    have h1 : O.ncard ≤ ((Q : Set G) \ {1}).ncard := by
      exact Set.ncard_le_ncard (by
        intro x hx
        exact ⟨hOsub hx, by rintro rfl; exact hO_one hx⟩)
    rwa [Set.ncard_sdiff_singleton_of_mem (Q.one_mem)] at h1
  have hQcard_ge : orderOf (u * w) + 1 ≤ Nat.card Q := by
    have hO_le : orderOf (u * w) ≤ Nat.card Q - 1 := by
      rw [← hOcard]
      exact hOncard
    have hQpos : 0 < Nat.card Q := Nat.card_pos
    omega
  obtain ⟨a, haA, hau⟩ := hD.exists_conj htri.1 htri.2.2.1 htri.2.2.2.2.2.1
  have haK : a ∈ Subgroup.closure ({u, w, v} : Set G) := hA_le_K haA
  let f : G →* G := (MulAut.conj a).toMonoidHom
  have hfQ : Q.map f = Q := by
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap]
      intro q hq
      change f q ∈ Q
      exact hS.normal a haK q hq
    · intro q hq
      rw [Subgroup.mem_map]
      refine ⟨a⁻¹ * q * a, ?_, ?_⟩
      · simpa using hS.normal a⁻¹ (Subgroup.inv_mem _ haK) q hq
      · change a * (a⁻¹ * q * a) * a⁻¹ = q
        group
  have hfu : f u = w := hau
  have hmap : P.map f = R := by
    rw [Subgroup.map_commutator, hfQ, MonoidHom.map_zpowers, hfu]
  have hcard_eq : Nat.card R = Nat.card P := by
    rw [← hmap]
    exact Subgroup.card_map_of_injective (f := f) (by simpa [f] using (MulAut.conj a).injective)
  have hQeq : Q = P ⊔ R := hS.eq_sup
  have hPle : P ≤ Q := by
    rw [hQeq]
    exact le_sup_left
  have hRle : R ≤ Q := by
    rw [hQeq]
    exact le_sup_right
  have hcomm : Commuting P R := fun p hp r hr => hS.comm p (hPle hp) r (hRle hr)
  have hQcard_le : Nat.card Q ≤ Nat.card P * Nat.card R := by
    calc Nat.card Q = Nat.card (P ⊔ R : Subgroup G) := by rw [hQeq]
      _ ≤ Nat.card P * Nat.card R := card_sup_le_of_commuting hcomm
  have hsq : orderOf (u * w) + 1 ≤ Nat.card P * Nat.card P := by
    calc orderOf (u * w) + 1 ≤ Nat.card Q := hQcard_ge
      _ ≤ Nat.card P * Nat.card R := hQcard_le
      _ = Nat.card P * Nat.card P := by rw [hcard_eq]
  have hP3 : 3 ≤ Nat.card P := by
    by_contra h
    have h2 : Nat.card P ≤ 2 := by omega
    have h4 : Nat.card P * Nat.card P ≤ 4 := by
      have h := Nat.mul_le_mul h2 h2
      norm_num at h
      exact h
    omega
  have hP2 : 2 < Nat.card P := by omega
  simpa only [P, Q, A] using hP2

end CFSG.OddTranspositions
