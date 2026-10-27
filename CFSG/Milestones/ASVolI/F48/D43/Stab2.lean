module

public import CFSG.Milestones.ASVolI.F48.D43.Stab

public section

namespace CFSG.ASVolI

open CFSG.Blueprint.Chevalley CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native

attribute [local irreducible] burnsideF48d_KeysHex burnsideF48d_TabsHex burnsideF48d_GensHex
  burnsideF48d_PhiHex burnsideF48d_limbs burnsideF48d_colTab

section Torus

theorem burnsideF48d_card_T : Nat.card ↥burnsideF48d_T = 52 := burnsideF48d_card_lvT

theorem burnsideF48d_L_mem_T {j : Fin 17} (h1 : 2 ≤ j.val) (h2 : j.val ≤ 4) :
    burnsideF48d_L j ∈ burnsideF48d_T :=
  Subgroup.subset_closure ⟨j, ⟨h1, h2⟩, rfl⟩

theorem burnsideF48d_fixT {p : Fin 26572}
    (h : ∀ t ∈ burnsideF48d_T, ((t : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) p = p) :
    p ∈ burnsideF48d_aptF := by
  have ha := h _ (burnsideF48d_L_mem_T (j := 2) (by norm_num) (by norm_num))
  have hb := h _ (burnsideF48d_L_mem_T (j := 3) (by norm_num) (by norm_num))
  by_contra hp
  rcases burnsideF48d_pt_parts.1 p hp with h1 | h1
  · exact h1 ha
  · exact h1 hb

theorem burnsideF48d_norm_inv {H : Subgroup ↥burnsideF48d_X} {g : ↥burnsideF48d_X}
    (hg : ∀ k ∈ H, g * k * g⁻¹ ∈ H) : ∀ k ∈ H, g⁻¹ * k * g ∈ H := by
  have hinj : Function.Injective (fun k : ↥H => (⟨g * k * g⁻¹, hg k k.2⟩ : ↥H)) := by
    intro a b hab
    apply Subtype.ext
    have := congrArg Subtype.val hab
    simpa using this
  have hsurj := Finite.surjective_of_injective hinj
  intro k hk
  obtain ⟨a, ha⟩ := hsurj ⟨k, hk⟩
  have e : g⁻¹ * k * g = a := by
    have := congrArg Subtype.val ha
    simp only at this
    rw [← this]
    group
  rw [e]
  exact a.2

theorem burnsideF48d_normT_apt {g : ↥burnsideF48d_X}
    (hg : ∀ k ∈ burnsideF48d_T, g * k * g⁻¹ ∈ burnsideF48d_T) {p : Fin 26572}
    (hp : p ∈ burnsideF48d_aptF) : (g : Equiv.Perm (Fin 26572)) p ∈ burnsideF48d_aptF := by
  apply burnsideF48d_fixT
  intro t ht
  have h1 := burnsideF48d_norm_inv hg t ht
  have h2 := (burnsideF48d_mem_T _).1 h1 p hp
  have e : ((t : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) ((g : Equiv.Perm (Fin 26572)) p) =
      (g : Equiv.Perm (Fin 26572)) ((((g⁻¹ * t * g : ↥burnsideF48d_X)) : Equiv.Perm (Fin 26572)) p) := by
    rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply]
    congr 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e, h2]

theorem burnsideF48d_normT_of_apt {g : ↥burnsideF48d_X}
    (hg : ∀ p ∈ burnsideF48d_aptF, (g : Equiv.Perm (Fin 26572)) p ∈ burnsideF48d_aptF) :
    ∀ k ∈ burnsideF48d_T, g * k * g⁻¹ ∈ burnsideF48d_T := by
  have hsurj : ∀ p ∈ burnsideF48d_aptF, ∃ q ∈ burnsideF48d_aptF, (g : Equiv.Perm (Fin 26572)) q = p := by
    have hmaps : Set.MapsTo (g : Equiv.Perm (Fin 26572)) (burnsideF48d_aptF : Set (Fin 26572))
        (burnsideF48d_aptF : Set (Fin 26572)) := fun q hq => hg q hq
    have hbij := (Set.Finite.injOn_iff_bijOn_of_mapsTo (Finset.finite_toSet _) hmaps).1
      (g : Equiv.Perm (Fin 26572)).injective.injOn
    intro p hp
    obtain ⟨q, hq, hqp⟩ := hbij.2.2 (show p ∈ (burnsideF48d_aptF : Set (Fin 26572)) from hp)
    exact ⟨q, hq, hqp⟩
  intro k hk
  rw [burnsideF48d_mem_T]
  intro p hp
  obtain ⟨q, hq, rfl⟩ := hsurj p hp
  have e : (((g * k * g⁻¹ : ↥burnsideF48d_X)) : Equiv.Perm (Fin 26572)) ((g : Equiv.Perm (Fin 26572)) q) =
      (g : Equiv.Perm (Fin 26572)) (((k : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) q) := by
    rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply]
    congr 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e, (burnsideF48d_mem_T k).1 hk q hq]

@[expose] noncomputable def burnsideF48d_oc (p : Fin 26572) : ℕ :=
  Nat.card (MulAction.orbit ↥burnsideF48d_P1 p)

theorem burnsideF48d_oc_smul {y : ↥burnsideF48d_X} (hy : y ∈ burnsideF48d_P1) (p : Fin 26572) :
    burnsideF48d_oc ((y : Equiv.Perm (Fin 26572)) p) = burnsideF48d_oc p := by
  unfold burnsideF48d_oc
  have : ((y : Equiv.Perm (Fin 26572)) p) = (⟨y, hy⟩ : ↥burnsideF48d_P1) • p := rfl
  rw [this, MulAction.orbit_smul]

theorem burnsideF48d_oc_of_mem {p q : Fin 26572}
    (h : ∃ y ∈ burnsideF48d_P1, ((y : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) p = q) :
    burnsideF48d_oc q = burnsideF48d_oc p := by
  obtain ⟨y, hy, rfl⟩ := h
  exact burnsideF48d_oc_smul hy p

theorem burnsideF48d_oc_values : burnsideF48d_oc 0 = 1 ∧ burnsideF48d_oc 6 = 84 ∧
    burnsideF48d_oc 186 = 84 ∧ burnsideF48d_oc 479 = 6804 ∧ burnsideF48d_oc 15916 = 6804 ∧
    burnsideF48d_oc 26571 = 19683 := by
  have h6 : burnsideF48d_oc 6 = 84 := burnsideF48d_card_orbit_P1_6
  have h479 : burnsideF48d_oc 479 = 6804 := burnsideF48d_orb_P1.2.1
  have h26571 : burnsideF48d_oc 26571 = 19683 := burnsideF48d_orb_P1.2.2.1
  refine ⟨?_, h6, ?_, h479, ?_, h26571⟩
  · unfold burnsideF48d_oc
    have : MulAction.orbit ↥burnsideF48d_P1 (0 : Fin 26572) = {0} := by
      ext q
      rw [burnsideF48d_orbit_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (burnsideF48d_mem_P1 y).1 hy
      · rintro rfl
        exact ⟨1, burnsideF48d_P1.one_mem, rfl⟩
    rw [this, Nat.card_unique]
  · rw [← h6]
    exact burnsideF48d_oc_of_mem ((burnsideF48d_orbit_iff _ _).1 burnsideF48d_orb_P1.2.2.2.2.1)
  · rw [← h479]
    exact burnsideF48d_oc_of_mem ((burnsideF48d_orbit_iff _ _).1 burnsideF48d_orb_P1.2.2.2.2.2)

theorem burnsideF48d_xy_apt :
    ((burnsideF48d_L 0 : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) 0 = 0 ∧
    ((burnsideF48d_L 0 : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) 6 = 186 ∧
    ((burnsideF48d_L 0 : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) 479 = 15916 ∧
    ((burnsideF48d_L 0 : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) 26571 = 26571 ∧
    ((burnsideF48d_L 0 : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) 15916 = 479 ∧
    ((burnsideF48d_L 0 : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) 186 = 6 ∧
    ((burnsideF48d_L 1 : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) 0 = 6 ∧
    ((burnsideF48d_L 1 : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) 6 = 0 ∧
    ((burnsideF48d_L 1 : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) 479 = 186 ∧
    ((burnsideF48d_L 1 : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) 26571 = 15916 ∧
    ((burnsideF48d_L 1 : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) 15916 = 26571 ∧
    ((burnsideF48d_L 1 : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) 186 = 479 :=
  burnsideF48d_pt_parts.2.2

theorem burnsideF48d_aptF_cases {p : Fin 26572} (hp : p ∈ burnsideF48d_aptF) :
    p = 0 ∨ p = 6 ∨ p = 479 ∨ p = 26571 ∨ p = 15916 ∨ p = 186 := by
  simpa [burnsideF48d_aptF] using hp

theorem burnsideF48d_apt_line {p : Fin 26572} (hp : p ∈ burnsideF48d_aptF)
    (hl : p ∈ burnsideF48d_line) : p = 0 ∨ p = 6 := by
  rcases burnsideF48d_aptF_cases hp with h | h | h | h | h | h <;> subst h <;>
    first | exact Or.inl rfl | exact Or.inr rfl | exact absurd hl (by decide)

theorem burnsideF48d_apt_oc {p : Fin 26572} (hp : p ∈ burnsideF48d_aptF) :
    (burnsideF48d_oc p = 84 → p = 6 ∨ p = 186) ∧ (burnsideF48d_oc p = 6804 → p = 479 ∨ p = 15916) ∧
      (burnsideF48d_oc p = 19683 → p = 26571) := by
  obtain ⟨h0, h6, h186, h479, h15916, h26571⟩ := burnsideF48d_oc_values
  rcases burnsideF48d_aptF_cases hp with h | h | h | h | h | h <;> subst h <;>
    simp only [h0, h6, h186, h479, h15916, h26571] <;> decide

theorem burnsideF48d_P1_6_le_B :
    burnsideF48d_P1 ⊓ MulAction.stabilizer ↥burnsideF48d_X (6 : Fin 26572) ≤ burnsideF48d_B' := by
  have hU6 : ∀ q : Fin 26572, q = 1 ∨ q = 2 ∨ q = 6 →
      ∃ y ∈ burnsideF48d_U, ((y : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) 6 = q := by
    intro q hq
    refine (burnsideF48d_orbit_iff _ _).1 ?_
    rcases hq with rfl | rfl | rfl
    · exact burnsideF48d_orb_U.2.2.2.2.2.2.1
    · exact burnsideF48d_orb_U.2.2.2.2.2.2.2
    · exact MulAction.mem_orbit_self _
  have hUB : burnsideF48d_U ≤ burnsideF48d_B' := by
    rw [burnsideF48d_U, Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    exact Subgroup.subset_closure ⟨j, by simp only [Set.mem_setOf_eq] at hj ⊢; omega, rfl⟩
  have horb : MulAction.orbit ↥burnsideF48d_B' (6 : Fin 26572) = ({1, 2, 6} : Finset (Fin 26572)) := by
    ext q
    rw [burnsideF48d_orbit_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hyQ : y ∈ burnsideF48d_Q := burnsideF48d_Q_eq ▸ hy
      have h6 : (y : Equiv.Perm (Fin 26572)) 6 ∈ burnsideF48d_line := hyQ.2 6 (by decide)
      have h0 : (y : Equiv.Perm (Fin 26572)) 0 = 0 := (burnsideF48d_mem_P1 y).1 hyQ.1
      have hne : (y : Equiv.Perm (Fin 26572)) 6 ≠ 0 := fun h => by
        rw [← h0] at h
        exact absurd ((y : Equiv.Perm (Fin 26572)).injective h) (by decide)
      simp only [burnsideF48d_line, Finset.mem_insert, Finset.mem_singleton] at h6
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases h6 with h6 | h6 | h6 | h6
      · exact absurd h6 hne
      · exact Or.inl h6
      · exact Or.inr (Or.inl h6)
      · exact Or.inr (Or.inr h6)
    · intro hq
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hq
      obtain ⟨y, hy, hyq⟩ := hU6 q hq
      exact ⟨y, hUB hy, hyq⟩
  have hcard := card_eq_orbit_mul_inf burnsideF48d_B' (6 : Fin 26572)
  rw [horb, Nat.card_coe_set_eq, Set.ncard_coe_finset, show ({1, 2, 6} : Finset (Fin 26572)).card = 3
    by decide, ← burnsideF48d_B_eq_closure, burnsideF48d_card_B] at hcard
  have hle : burnsideF48d_B' ⊓ MulAction.stabilizer ↥burnsideF48d_X (6 : Fin 26572) ≤
      burnsideF48d_P1 ⊓ MulAction.stabilizer ↥burnsideF48d_X (6 : Fin 26572) :=
    inf_le_inf_right _ burnsideF48d_B'_le_P1
  have heq := Subgroup.eq_of_le_of_card_ge hle (by
    rw [burnsideF48d_card_P1_6, ← burnsideF48d_B_eq_closure]
    omega)
  rw [← heq]
  exact inf_le_left

theorem burnsideF48d_fix_mem_stab {z : ↥burnsideF48d_X} {p : Fin 26572}
    (h : (z : Equiv.Perm (Fin 26572)) p = p) : z ∈ MulAction.stabilizer ↥burnsideF48d_X p := h

end Torus

end CFSG.ASVolI
