module

public import Certificates.Certificate7803

public section

namespace CFSG.ASVolI

open CFSG.Blueprint.Chevalley CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native

attribute [local irreducible] burnsideF48d_KeysHex burnsideF48d_TabsHex burnsideF48d_GensHex
  burnsideF48d_PhiHex burnsideF48d_limbs burnsideF48d_colTab

theorem burnsideF48d_orbit_iff {Y : Subgroup ↥burnsideF48d_X} (p q : Fin 26572) :
    q ∈ MulAction.orbit ↥Y p ↔ ∃ y ∈ Y, ((y : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) p = q := by
  constructor
  · rintro ⟨⟨y, hy⟩, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩

section Cert

theorem burnsideF48d_orb_P1 :
    Nat.card (MulAction.orbit ↥burnsideF48d_P1 (6 : Fin 26572)) = 84 ∧
      Nat.card (MulAction.orbit ↥burnsideF48d_P1 (479 : Fin 26572)) = 6804 ∧
      Nat.card (MulAction.orbit ↥burnsideF48d_P1 (26571 : Fin 26572)) = 19683 ∧
      (∀ p : Fin 26572, p ≠ 0 → p ∈ MulAction.orbit ↥burnsideF48d_P1 (6 : Fin 26572) ∨
        p ∈ MulAction.orbit ↥burnsideF48d_P1 (479 : Fin 26572) ∨
        p ∈ MulAction.orbit ↥burnsideF48d_P1 (26571 : Fin 26572)) ∧
      (186 : Fin 26572) ∈ MulAction.orbit ↥burnsideF48d_P1 (6 : Fin 26572) ∧
      (15916 : Fin 26572) ∈ MulAction.orbit ↥burnsideF48d_P1 (479 : Fin 26572) :=
  Certificates.certificate7803.1

theorem burnsideF48d_orb_P2 :
    MulAction.orbit ↥burnsideF48d_P2 (0 : Fin 26572) = (burnsideF48d_line : Set (Fin 26572)) ∧
      Nat.card (MulAction.orbit ↥burnsideF48d_P2 (186 : Fin 26572)) = 324 ∧
      Nat.card (MulAction.orbit ↥burnsideF48d_P2 (26571 : Fin 26572)) = 26244 ∧
      ∀ p : Fin 26572, p ∈ MulAction.orbit ↥burnsideF48d_P2 (0 : Fin 26572) ∨
        p ∈ MulAction.orbit ↥burnsideF48d_P2 (186 : Fin 26572) ∨
        p ∈ MulAction.orbit ↥burnsideF48d_P2 (26571 : Fin 26572) :=
  Certificates.certificate7803.2.1

theorem burnsideF48d_orb_U :
    Nat.card (MulAction.orbit ↥burnsideF48d_U (6 : Fin 26572)) = 3 ∧
      Nat.card (MulAction.orbit ↥burnsideF48d_U (186 : Fin 26572)) = 81 ∧
      Nat.card (MulAction.orbit ↥burnsideF48d_U (479 : Fin 26572)) = 243 ∧
      Nat.card (MulAction.orbit ↥burnsideF48d_U (15916 : Fin 26572)) = 6561 ∧
      Nat.card (MulAction.orbit ↥burnsideF48d_U (26571 : Fin 26572)) = 19683 ∧
      (∀ p : Fin 26572, p ≠ 0 → p ∈ MulAction.orbit ↥burnsideF48d_U (6 : Fin 26572) ∨
        p ∈ MulAction.orbit ↥burnsideF48d_U (186 : Fin 26572) ∨
        p ∈ MulAction.orbit ↥burnsideF48d_U (479 : Fin 26572) ∨
        p ∈ MulAction.orbit ↥burnsideF48d_U (15916 : Fin 26572) ∨
        p ∈ MulAction.orbit ↥burnsideF48d_U (26571 : Fin 26572)) ∧
      (1 : Fin 26572) ∈ MulAction.orbit ↥burnsideF48d_U (6 : Fin 26572) ∧
      (2 : Fin 26572) ∈ MulAction.orbit ↥burnsideF48d_U (6 : Fin 26572) :=
  Certificates.certificate7803.2.2.1

theorem burnsideF48d_pt_parts :
    (∀ p : Fin 26572, p ∉ burnsideF48d_aptF →
        ((burnsideF48d_L 2 : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) p ≠ p ∨
        ((burnsideF48d_L 3 : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) p ≠ p) ∧
      (∀ j : Fin 17, j ≠ 0 → ∀ p ∈ burnsideF48d_line,
        ((burnsideF48d_L j : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) p ∈ burnsideF48d_line) ∧
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
  Certificates.certificate7803.2.2.2.1

end Cert

@[expose] noncomputable def burnsideF48d_SL : Subgroup ↥burnsideF48d_X where
  carrier := {z | ∀ p ∈ burnsideF48d_line, (z : Equiv.Perm (Fin 26572)) p ∈ burnsideF48d_line}
  mul_mem' {a b} ha hb p hp := ha _ (hb p hp)
  one_mem' p hp := hp
  inv_mem' {z} hz p hp := by
    have hmaps : Set.MapsTo (z : Equiv.Perm (Fin 26572)) (burnsideF48d_line : Set (Fin 26572))
        (burnsideF48d_line : Set (Fin 26572)) := fun q hq => hz q hq
    have hinj : Set.InjOn (z : Equiv.Perm (Fin 26572)) (burnsideF48d_line : Set (Fin 26572)) :=
      (z : Equiv.Perm (Fin 26572)).injective.injOn
    have hbij := (Set.Finite.injOn_iff_bijOn_of_mapsTo (Finset.finite_toSet _) hmaps).1 hinj
    obtain ⟨q, hq, hqp⟩ := hbij.2.2 (show p ∈ (burnsideF48d_line : Set (Fin 26572)) from hp)
    show ((z⁻¹ : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) p ∈ burnsideF48d_line
    rw [Subgroup.coe_inv, ← hqp, ← Equiv.Perm.mul_apply, inv_mul_cancel, Equiv.Perm.one_apply]
    exact hq

section Line

theorem burnsideF48d_L_mem_SL {j : Fin 17} (hj : j ≠ 0) : burnsideF48d_L j ∈ burnsideF48d_SL :=
  fun p hp => burnsideF48d_pt_parts.2.1 j hj p hp

theorem burnsideF48d_P2_le_SL : burnsideF48d_P2 ≤ burnsideF48d_SL := by
  rw [burnsideF48d_P2, Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  exact burnsideF48d_L_mem_SL hj

theorem burnsideF48d_top_orbit (p : Fin 26572) :
    MulAction.orbit ↥(⊤ : Subgroup ↥burnsideF48d_X) (0 : Fin 26572) = Set.univ := by
  ext q
  simp only [Set.mem_univ, iff_true]
  obtain ⟨z, hz⟩ := burnsideF48d_trans q
  exact (burnsideF48d_orbit_iff (Y := ⊤) 0 q).2 ⟨z, Subgroup.mem_top _, hz⟩

theorem burnsideF48d_card_P1 : Nat.card ↥burnsideF48d_P1 = 773778096 := by
  have h := card_eq_orbit_mul (⊤ : Subgroup ↥burnsideF48d_X) burnsideF48d_P1 (0 : Fin 26572)
    le_top (fun l hl => Fin.ext (by
      have := (burnsideF48d_mem_P1 l).1 hl
      exact congrArg Fin.val this))
    (fun h _ hh => (burnsideF48d_mem_P1 h).2 hh)
  rw [Subgroup.card_top, burnsideF48d_card_X, burnsideF48d_top_orbit 0, Nat.card_univ,
    Nat.card_eq_fintype_card, Fintype.card_fin] at h
  omega

theorem burnsideF48d_card_orbit_P1_6 :
    Nat.card (MulAction.orbit ↥burnsideF48d_P1 (6 : Fin 26572)) = 84 :=
  burnsideF48d_orb_P1.1

theorem burnsideF48d_card_P1_6 :
    Nat.card ↥(burnsideF48d_P1 ⊓ MulAction.stabilizer ↥burnsideF48d_X (6 : Fin 26572)) = 9211644 := by
  have h := card_eq_orbit_mul_inf burnsideF48d_P1 (6 : Fin 26572)
  rw [burnsideF48d_card_P1, burnsideF48d_card_orbit_P1_6] at h
  omega

noncomputable abbrev burnsideF48d_Q : Subgroup ↥burnsideF48d_X := burnsideF48d_P1 ⊓ burnsideF48d_SL

theorem burnsideF48d_card_Q_le : Nat.card ↥burnsideF48d_Q ≤ 27634932 := by
  have h := card_eq_orbit_mul_inf burnsideF48d_Q (6 : Fin 26572)
  have h1 : Nat.card (MulAction.orbit ↥burnsideF48d_Q (6 : Fin 26572)) ≤ 3 := by
    have hsub : MulAction.orbit ↥burnsideF48d_Q (6 : Fin 26572) ⊆ ({1, 2, 6} : Finset (Fin 26572)) := by
      rintro _ ⟨⟨q, hq1, hq2⟩, rfl⟩
      have h6 : (q : Equiv.Perm (Fin 26572)) 6 ∈ burnsideF48d_line := hq2 6 (by decide)
      have h0 : (q : Equiv.Perm (Fin 26572)) 0 = 0 := (burnsideF48d_mem_P1 q).1 hq1
      have hne : (q : Equiv.Perm (Fin 26572)) 6 ≠ 0 := fun h => by
        rw [← h0] at h
        exact absurd ((q : Equiv.Perm (Fin 26572)).injective h) (by decide)
      show (q : Equiv.Perm (Fin 26572)) 6 ∈ (({1, 2, 6} : Finset (Fin 26572)) : Set (Fin 26572))
      simp only [burnsideF48d_line, Finset.mem_insert, Finset.mem_singleton] at h6
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases h6 with h6 | h6 | h6 | h6
      · exact absurd h6 hne
      · exact Or.inl h6
      · exact Or.inr (Or.inl h6)
      · exact Or.inr (Or.inr h6)
    calc Nat.card (MulAction.orbit ↥burnsideF48d_Q (6 : Fin 26572))
        ≤ Nat.card (({1, 2, 6} : Finset (Fin 26572)) : Set (Fin 26572)) :=
          Nat.card_mono (Finset.finite_toSet _) hsub
      _ = 3 := by rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]; decide
  have h2 : Nat.card ↥(burnsideF48d_Q ⊓ MulAction.stabilizer ↥burnsideF48d_X (6 : Fin 26572)) ≤
      9211644 := by
    rw [← burnsideF48d_card_P1_6]
    exact Subgroup.card_le_of_le (inf_le_inf_right _ inf_le_left)
  rw [h]
  calc _ ≤ 3 * 9211644 := Nat.mul_le_mul h1 h2
    _ = 27634932 := by norm_num

noncomputable abbrev burnsideF48d_B' : Subgroup ↥burnsideF48d_X :=
  Subgroup.closure (burnsideF48d_L '' {j | 2 ≤ j.val})

theorem burnsideF48d_B'_le_P1 : burnsideF48d_B' ≤ burnsideF48d_P1 := by
  rw [Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  exact Subgroup.subset_closure ⟨j, fun h => by
    have : j.val = 1 := congrArg Fin.val h
    simp only [Set.mem_setOf_eq] at hj
    omega, rfl⟩

theorem burnsideF48d_B'_le_P2 : burnsideF48d_B' ≤ burnsideF48d_P2 := by
  rw [Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  exact Subgroup.subset_closure ⟨j, fun h => by
    have : j.val = 0 := congrArg Fin.val h
    simp only [Set.mem_setOf_eq] at hj
    omega, rfl⟩

theorem burnsideF48d_card_B'_ge : 27634932 ≤ Nat.card ↥burnsideF48d_B' := by
  have h := burnsideF48d_lvH_prod_le burnsideF48d_chain_cert.2 burnsideF48d_nestedB 0
    (Nat.zero_le _)
  have e : ∏ l ∈ Finset.Ico 0 burnsideF48d_chainBL.length,
      (burnsideF48d_chainBL.getD l burnsideF48d_lv0).2.2 = 27634932 := by
    decide +kernel
  have hS : ∀ j : Fin 17, j ∈ (burnsideF48d_chainBL.getD 0 burnsideF48d_lv0).2.1 ↔ 2 ≤ j.val := by
    decide +kernel
  have hB : burnsideF48d_lvH burnsideF48d_chainBL 0 = burnsideF48d_B' := by
    unfold burnsideF48d_lvH
    congr 2
    ext j
    exact hS j
  rw [e, hB] at h
  exact h

theorem burnsideF48d_Q_eq : burnsideF48d_B' = burnsideF48d_Q :=
  Subgroup.eq_of_le_of_card_ge (le_inf burnsideF48d_B'_le_P1 (burnsideF48d_B'_le_P2.trans
    burnsideF48d_P2_le_SL)) (burnsideF48d_card_Q_le.trans burnsideF48d_card_B'_ge)

theorem burnsideF48d_mem_P2 (z : ↥burnsideF48d_X) :
    z ∈ burnsideF48d_P2 ↔ ∀ p ∈ burnsideF48d_line, (z : Equiv.Perm (Fin 26572)) p ∈ burnsideF48d_line := by
  constructor
  · exact fun h => burnsideF48d_P2_le_SL h
  · intro hz
    have h0 := hz 0 (by decide)
    have hreach : ∃ y ∈ burnsideF48d_P2, ((y : ↥burnsideF48d_X) : Equiv.Perm (Fin 26572)) 0 =
        (z : Equiv.Perm (Fin 26572)) 0 := by
      refine (burnsideF48d_orbit_iff 0 _).1 ?_
      rw [burnsideF48d_orb_P2.1]
      exact h0
    obtain ⟨y, hy, hyz⟩ := hreach
    have hq : y⁻¹ * z ∈ burnsideF48d_Q := by
      refine ⟨(burnsideF48d_mem_P1 _).2 ?_, burnsideF48d_SL.mul_mem
        (burnsideF48d_SL.inv_mem (burnsideF48d_P2_le_SL hy)) hz⟩
      rw [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply, ← hyz, ← Equiv.Perm.mul_apply,
        inv_mul_cancel, Equiv.Perm.one_apply]
    rw [← burnsideF48d_Q_eq] at hq
    have := burnsideF48d_P2.mul_mem hy (burnsideF48d_B'_le_P2 hq)
    rwa [mul_inv_cancel_left] at this

theorem burnsideF48d_B_eq_closure : burnsideF48d_P1 ⊓ burnsideF48d_P2 = burnsideF48d_B' :=
  le_antisymm (by rw [burnsideF48d_Q_eq]; exact inf_le_inf_left _ burnsideF48d_P2_le_SL)
    (le_inf burnsideF48d_B'_le_P1 burnsideF48d_B'_le_P2)

theorem burnsideF48d_card_B : Nat.card ↥(burnsideF48d_P1 ⊓ burnsideF48d_P2) = 27634932 := by
  rw [burnsideF48d_B_eq_closure]
  exact le_antisymm (burnsideF48d_Q_eq ▸ burnsideF48d_card_Q_le) burnsideF48d_card_B'_ge

theorem burnsideF48d_card_P2 : Nat.card ↥burnsideF48d_P2 = 110539728 := by
  have h := card_eq_orbit_mul burnsideF48d_P2 (burnsideF48d_P1 ⊓ burnsideF48d_P2) (0 : Fin 26572)
    inf_le_right (fun l hl => Fin.ext (by
      have := (burnsideF48d_mem_P1 l).1 hl.1
      exact congrArg Fin.val this))
    (fun h hh h0 => ⟨(burnsideF48d_mem_P1 h).2 h0, hh⟩)
  rw [burnsideF48d_orb_P2.1, Nat.card_coe_set_eq, Set.ncard_coe_finset, burnsideF48d_card_B] at h
  rw [h]
  decide

end Line

end CFSG.ASVolI
