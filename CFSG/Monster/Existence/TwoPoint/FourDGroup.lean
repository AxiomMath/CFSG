module

public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.Monster.Existence

theorem fd_sup_eq_top_of_map {E Q : Type*} [Group E] [Group Q] (φ : E →* Q) {A D : Subgroup E}
    (hker : φ.ker ≤ A)
    (hmax : ∀ B : Subgroup Q, A.map φ < B → B ≤ φ.range → B = φ.range)
    (hnot : ¬ D.map φ ≤ A.map φ) : A ⊔ D = ⊤ := by
  have h1 : A.map φ < (A ⊔ D).map φ := by
    refine lt_of_le_of_ne (Subgroup.map_mono le_sup_left) fun h => hnot ?_
    rw [h, Subgroup.map_sup]
    exact le_sup_right
  have h2 : (A ⊔ D).map φ = φ.range := by
    refine hmax _ h1 ?_
    rw [Subgroup.map_le_iff_le_comap]
    exact fun x _ => ⟨x, rfl⟩
  rw [eq_top_iff]
  intro g _
  have : φ g ∈ (A ⊔ D).map φ := by rw [h2]; exact ⟨g, rfl⟩
  obtain ⟨k, hk, hkg⟩ := this
  have : k⁻¹ * g ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hkg, inv_mul_cancel]
  have h3 : k⁻¹ * g ∈ A ⊔ D := Subgroup.mem_sup_left (hker this)
  have := mul_mem hk h3
  rwa [mul_inv_cancel_left] at this

theorem fd_not_map_le_of_dvd {E Q : Type*} [Group E] [Group Q] (φ : E →* Q) {p : ℕ}
    (hp : p.Prime) (hker : ¬ p ∣ Nat.card φ.ker) {D : Subgroup E} (hD : p ∣ Nat.card D)
    {C : Subgroup Q} (hC : ¬ p ∣ Nat.card C) : ¬ D.map φ ≤ C := by
  intro hle
  have h1 := Subgroup.card_ker_mul_card_range (φ.comp D.subtype)
  have h2 : (φ.comp D.subtype).range = D.map φ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have h3 : Nat.card (φ.comp D.subtype).ker ∣ Nat.card φ.ker := by
    have : (φ.comp D.subtype).ker.map D.subtype ≤ φ.ker := by
      rintro _ ⟨x, hx, rfl⟩
      exact hx
    have h4 := Subgroup.card_dvd_of_le this
    rwa [Subgroup.card_map_of_injective D.subtype_injective] at h4
  have h5 : p ∣ Nat.card (φ.comp D.subtype).ker * Nat.card (φ.comp D.subtype).range := by
    rw [h1]; exact hD
  rcases (Nat.Prime.dvd_mul hp).1 h5 with h | h
  · exact hker (h.trans h3)
  · rw [h2] at h
    exact hC (h.trans (Subgroup.card_dvd_of_le hle))

theorem fd_commutator_le_of_index_two {A : Type*} [Group A] {H : Subgroup A} (h : H.index = 2) :
    commutator A ≤ H := by
  rw [commutator_def, Subgroup.commutator_le]
  intro g₁ _ g₂ _
  rw [commutatorElement_def, Subgroup.mul_mem_iff_of_index_two h,
    Subgroup.mul_mem_iff_of_index_two h, Subgroup.mul_mem_iff_of_index_two h, inv_mem_iff,
    inv_mem_iff]
  tauto

theorem fd_eq_commutator_of_index_two {A : Type*} [Group A] {H : Subgroup A} (h : H.index = 2)
    (hc : (commutator A).index = 2) : H = commutator A := by
  have hle := fd_commutator_le_of_index_two h
  have h1 := Subgroup.relIndex_mul_index hle
  rw [h, hc] at h1
  have h2 : (commutator A).relIndex H = 1 := by omega
  exact le_antisymm (Subgroup.relIndex_eq_one.1 h2) hle

theorem fd_card_isConj_mul_card_centralizer {G : Type*} [Group G] [Finite G] (p : G) :
    Nat.card {x | IsConj p x} * Nat.card (Subgroup.centralizer {p}) = Nat.card G := by
  classical
  have := Fintype.ofFinite G
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct G) p
  have e1 : Nat.card (MulAction.orbit (ConjAct G) p) = Nat.card {x | IsConj p x} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    rw [ConjAct.mem_orbit_conjAct, isConj_comm]
    exact Iff.rfl
  have e2 : Nat.card (MulAction.stabilizer (ConjAct G) p) =
      Nat.card (Subgroup.centralizer {p}) := by
    refine Nat.card_congr (Equiv.subtypeEquiv ConjAct.toConjAct.symm.toEquiv fun a => ?_)
    show a ∈ MulAction.stabilizer (ConjAct G) p ↔ ConjAct.ofConjAct a ∈ Subgroup.centralizer {p}
    rw [MulAction.mem_stabilizer_iff, ConjAct.smul_def, mul_inv_eq_iff_eq_mul,
      Subgroup.mem_centralizer_singleton_iff]
  have e3 : Nat.card (ConjAct G) = Nat.card G := Nat.card_congr ConjAct.toConjAct.toEquiv.symm
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at h
  rw [e1, e2, e3] at h
  exact h

theorem fd_natCard_eq_two_of_mem_iff {X : Type*} [Group X] (K : Subgroup X) (a : X)
    (ha : orderOf a = 2) (h : ∀ y, y ∈ K ↔ y = 1 ∨ y = a) : Nat.card K = 2 := by
  have ha1 : a ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at ha
    omega
  rw [Nat.card_eq_two_iff' (1 : K)]
  refine ⟨⟨a, (h a).2 (Or.inr rfl)⟩, ?_, ?_⟩
  · intro h'
    exact ha1 (congrArg Subtype.val h')
  · intro z hz
    rcases (h z.1).1 z.2 with h1 | h1
    · exact absurd (Subtype.ext h1) hz
    · exact Subtype.ext h1

end CFSG.Monster.Existence
