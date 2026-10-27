module

public import CFSG.OddTranspositions.BadCase
public import CFSG.OddTranspositions.OrbitUV
public import CFSG.LieType.SeitzGeneration.HyperIrrGroup

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
  CFSG.Timmesfeld.Bridge.OddTransp CFSG.Timmesfeld.Connectivity
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem three_le_card_inter_D (hD : IsOddTransp D) (hN : IsNormalSet D)
    {u w v : G} (htri : IsTriangle D u w v) (h4 : orderOf (u * v * w) = 4)
    (hno : ∀ x ∈ D, x ∈ Subgroup.closure {u, w} → IsTriangle D u x v →
      ¬ IsThirdKind u x v)
    (hm : 3 < orderOf (u * w)) :
    3 ≤ Nat.card (((Subgroup.zpowers u ⊔
        conjClosure (Subgroup.closure {u, w}) (u * v) : Subgroup G) : Set G) ∩ D : Set G) := by
  classical
  let A : Subgroup G := Subgroup.closure ({u, w} : Set G)
  let Q : Subgroup G := conjClosure A (u * v)
  let S : Subgroup G := Subgroup.zpowers u ⊔ Q
  have hS : SecondKindStructure u w v := secondKind_structure hD hN htri h4 hno
  have hc2 : (u * v) * (u * v) = 1 := htri.uv_mul_self hD
  have hc1 : u * v ≠ 1 :=
    fun h => htri.2.2.2.1 (hD.eq_of_mul_eq_one htri.1 h)
  have hcQ : u * v ∈ Q := by
    show u * v ∈ conjClosure A (u * v)
    exact Subgroup.subset_closure ⟨1, A.one_mem, by simp⟩
  have huS : u ∈ S := Subgroup.mem_sup_left (Subgroup.mem_zpowers u)
  have hvS : v ∈ S := by
    obtain ⟨x, hx, hxu⟩ := hS.conj
    have hxQ : x ∈ Q := secondKind_commutator_zpowers_le hD hN htri h4 hno hx
    rw [← hxu]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right hxQ) huS)
      (Subgroup.inv_mem _ (Subgroup.mem_sup_right hxQ))
  by_contra hcon
  push Not at hcon
  have hcon' : ((S : Set G) ∩ D).ncard < 3 := hcon
  have hbad : ∀ d : G, d ∈ ((S : Set G) ∩ D) → d = u ∨ d = v := by
    intro d hd
    by_contra hne
    push Not at hne
    have hsub : ({u, v, d} : Set G) ⊆ (S : Set G) ∩ D := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨huS, htri.1⟩
      · exact ⟨hvS, htri.2.1⟩
      · exact hd
    have h3 : ({u, v, d} : Set G).ncard = 3 := by
      have hdnot : d ∉ ({u, v} : Set G) := by simp [hne.1, hne.2]
      have heq : ({u, v, d} : Set G) = insert d ({u, v} : Set G) := by
        ext x
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto
      rw [heq, Set.ncard_insert_of_notMem hdnot, Set.ncard_pair htri.2.2.2.1]
    have hle : 3 ≤ ((S : Set G) ∩ D).ncard := by
      have h := Set.ncard_le_ncard hsub
      rwa [h3] at h
    omega
  obtain ⟨hcommu, -⟩ :=
    commutator_zpowers_eq_uv_of_inter_D_pair hD hN htri h4 hno hbad
  have huComm_le : ⁅Q, Subgroup.zpowers u⁆ ≤ Subgroup.zpowers (u * v) := by
    rw [Subgroup.commutator_le]
    intro q hq z hz
    rcases (hcommu ⁅q, z⁆).mp (Subgroup.commutator_mem_commutator hq hz) with h | h
    · rw [h]
      exact Subgroup.one_mem _
    · rw [h]
      exact Subgroup.mem_zpowers (u * v)
  obtain ⟨a, haA, hau⟩ := hD.exists_conj htri.1 htri.2.2.1 htri.2.2.2.2.2.1
  have hA_le_K : A ≤ Subgroup.closure ({u, w, v} : Set G) := by
    apply Subgroup.closure_mono
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
    rcases hy with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
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
  have hcommw_eq : ⁅Q, Subgroup.zpowers w⁆ =
      (⁅Q, Subgroup.zpowers u⁆).map f := by
    rw [Subgroup.map_commutator, hfQ, MonoidHom.map_zpowers]
    have hfu : f u = w := hau
    rw [hfu]
  have hwComm_le : ⁅Q, Subgroup.zpowers w⁆ ≤
      Subgroup.zpowers (a * (u * v) * a⁻¹) := by
    rw [hcommw_eq]
    calc (⁅Q, Subgroup.zpowers u⁆).map f
        ≤ (Subgroup.zpowers (u * v)).map f := Subgroup.map_mono huComm_le
      _ = Subgroup.zpowers (f (u * v)) := MonoidHom.map_zpowers f (u * v)
      _ = Subgroup.zpowers (a * (u * v) * a⁻¹) := by
          rw [show f (u * v) = a * (u * v) * a⁻¹ from rfl]
  have hQle : Q ≤ Subgroup.closure ({u * v, a * (u * v) * a⁻¹} : Set G) := by
    calc Q = ⁅Q, Subgroup.zpowers u⁆ ⊔ ⁅Q, Subgroup.zpowers w⁆ := hS.eq_sup
      _ ≤ Subgroup.closure ({u * v, a * (u * v) * a⁻¹} : Set G) := by
          apply sup_le
          · exact huComm_le.trans
              (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)))
          · exact hwComm_le.trans
              (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp)))
  have hconj_sq : (a * (u * v) * a⁻¹) * (a * (u * v) * a⁻¹) = 1 := by
    calc (a * (u * v) * a⁻¹) * (a * (u * v) * a⁻¹)
        = a * ((u * v) * (u * v)) * a⁻¹ := by group
      _ = 1 := by rw [hc2]; group
  have hQcard_le : Nat.card Q ≤ 4 := by
    have h1 : Nat.card Q ≤
        Nat.card (Subgroup.closure ({u * v, a * (u * v) * a⁻¹} : Set G)) :=
      Subgroup.card_le_of_le hQle
    have h2 : Nat.card (Subgroup.closure ({u * v, a * (u * v) * a⁻¹} : Set G)) ≤ 4 := by
      have hxQ : a * (u * v) * a⁻¹ ∈ Q := hS.normal a haK (u * v) hcQ
      have hcomm : Commute (u * v) (a * (u * v) * a⁻¹) :=
        hS.comm (u * v) hcQ (a * (u * v) * a⁻¹) hxQ
      have hsq1 : (u * v) ^ 2 = 1 := by simpa [pow_two] using hc2
      have hsq2 : (a * (u * v) * a⁻¹) ^ 2 = 1 := by
        simpa [pow_two] using hconj_sq
      have h := CFSG.LieType.SeitzGeneration.card_closure_pair_le (p := 2)
        (by norm_num) hcomm hsq1 hsq2
      simpa using h
    omega
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
  have hO_gt : 3 < O.ncard := by
    rw [hOcard]
    exact hm
  omega

end CFSG.OddTranspositions
