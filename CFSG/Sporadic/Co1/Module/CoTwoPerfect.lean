module

public import CFSG.Sporadic.Co1.Module.CoTwoLit
public import Certificates.Certificate10067

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co1.Module.CoTwo

open scoped commutatorElement

open CFSG.Blueprint CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.OddNative
  CFSG.Sporadic.Co1.CoTwoNative Matrix

@[expose] def y₀ : Vec24 := toVecD 24 y₀code

@[expose] def kp : Subgroup NativeSporadic.Co1 :=
  CFSG.Monster.GMS.co1Stab v₂ ⊓ CFSG.Monster.GMS.co1Stab y₀

@[expose] def kc : Subgroup NativeSporadic.Co1 := CFSG.Monster.GMS.co1Stab v₂

theorem finite_co1_ct : Finite NativeSporadic.Co1 :=
  Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Co1.card_Co1]; norm_num)

theorem mem_kp_iff {g : NativeSporadic.Co1} : g ∈ kp ↔ co1Act g v₂ = v₂ ∧ co1Act g y₀ = y₀ :=
  Iff.rfl

theorem mem_kc_iff {g : NativeSporadic.Co1} : g ∈ kc ↔ co1Act g v₂ = v₂ := Iff.rfl

theorem kp_le_kc : kp ≤ kc := inf_le_left

theorem regA_mem_kp_of {s : ℕ}
    (h : co1Act (regA s) (toVecD 24 2) = toVecD 24 2 ∧
      co1Act (regA s) (toVecD 24 y₀code) = toVecD 24 y₀code) : regA s ∈ kp := by
  have h2 := h.1
  rw [toVecD_v₂] at h2
  exact mem_kp_iff.2 ⟨h2, h.2⟩

theorem regA_mem_kc_of {s : ℕ}
    (h : co1Act (regA s) (toVecD 24 2) = toVecD 24 2) : regA s ∈ kc := by
  rw [toVecD_v₂] at h
  exact mem_kc_iff.2 h

theorem mul_eq_commutator_inv (a b : NativeSporadic.Co1) : a⁻¹ * b⁻¹ * a * b = ⁅a⁻¹, b⁻¹⁆ := by
  rw [commutatorElement_def, inv_inv, inv_inv]

theorem regA13_mem_commutator :
    regA 13 ∈ ⁅kp, kp⁆ := by
  obtain ⟨W, hW⟩ := Certificates.certificate10067
  have ha := regA_mem_kp_of (lit_fixP hW 9 (by simp))
  have hb := regA_mem_kp_of (lit_fixP hW 10 (by simp))
  rw [(lit_comm hW).1, (lit_inv hW).1, (lit_inv hW).2.1, mul_eq_commutator_inv]
  exact Subgroup.commutator_mem_commutator (inv_mem ha) (inv_mem hb)

theorem regA18_mem_commutator :
    regA 18 ∈ ⁅kp, kp⁆ := by
  obtain ⟨W, hW⟩ := Certificates.certificate10067
  have ha := regA_mem_kp_of (lit_fixP hW 14 (by simp))
  have hb := regA_mem_kp_of (lit_fixP hW 15 (by simp))
  rw [(lit_comm hW).2.1, (lit_inv hW).2.2.1, (lit_inv hW).2.2.2.1, mul_eq_commutator_inv]
  exact Subgroup.commutator_mem_commutator (inv_mem ha) (inv_mem hb)

theorem regA23_mem_commutator :
    regA 23 ∈ ⁅kc, kc⁆ := by
  obtain ⟨W, hW⟩ := Certificates.certificate10067
  have ha := regA_mem_kc_of (lit_fixE hW 19 (by simp))
  have hb := regA_mem_kc_of (lit_fixE hW 20 (by simp))
  rw [(lit_comm hW).2.2, (lit_inv hW).2.2.2.2.1, (lit_inv hW).2.2.2.2.2, mul_eq_commutator_inv]
  exact Subgroup.commutator_mem_commutator (inv_mem ha) (inv_mem hb)

theorem regA13_mem_kp :
    regA 13 ∈ kp := Subgroup.commutator_le_self kp regA13_mem_commutator

theorem regA18_mem_kp :
    regA 18 ∈ kp := Subgroup.commutator_le_self kp regA18_mem_commutator

theorem regA23_mem_kc :
    regA 23 ∈ kc := Subgroup.commutator_le_self kc regA23_mem_commutator

theorem card_closure_two_ge :
    898128000 ≤ Nat.card (Subgroup.closure ({regA 13, regA 18} : Set NativeSporadic.Co1)) := by
  obtain ⟨W, hW⟩ := Certificates.certificate10067
  exact lit_two_ge hW

theorem card_closure_three_ge :
    47104 * Nat.card (Subgroup.closure ({regA 13, regA 18} : Set NativeSporadic.Co1)) ≤
      Nat.card (Subgroup.closure ({regA 13, regA 18, regA 23} : Set NativeSporadic.Co1)) := by
  obtain ⟨W, hW⟩ := Certificates.certificate10067
  exact lit_three_ge hW

theorem card_kp
    (hy : y₀ ∈ CFSG.Monster.GMS.co1Orbit 0)
    (hs : v₂ + y₀ ∈ CFSG.Monster.GMS.co1Orbit 1) : Nat.card kp = 898128000 := by
  rw [Pairs.co1Orbit_zero] at hy
  rw [Pairs.co1Orbit_one] at hs
  have h := Pairs.pair_five (MulAction.mem_orbit_self v₂) hy hs
  have e : kp = MulAction.stabilizer NativeSporadic.Co1 v₂ ⊓
      MulAction.stabilizer NativeSporadic.Co1 y₀ := by
    unfold kp
    rw [Pairs.co1Stab_eq, Pairs.co1Stab_eq]
  rw [e, h]
  norm_num

theorem card_kc :
    Nat.card kc = 42305421312000 := by
  unfold kc
  rw [Pairs.co1Stab_eq]
  exact Pairs.card_stabilizer_v₂

theorem kp_eq_closure
    (hy : y₀ ∈ CFSG.Monster.GMS.co1Orbit 0)
    (hs : v₂ + y₀ ∈ CFSG.Monster.GMS.co1Orbit 1) :
    Subgroup.closure ({regA 13, regA 18} : Set NativeSporadic.Co1) = kp := by
  have := finite_co1_ct
  refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [card_kp hy hs]; exact card_closure_two_ge)
  rw [Subgroup.closure_le]
  rintro g (rfl | hg)
  · exact regA13_mem_kp
  · rw [Set.mem_singleton_iff.1 hg]
    exact regA18_mem_kp

theorem kc_eq_closure
    (hy : y₀ ∈ CFSG.Monster.GMS.co1Orbit 0)
    (hs : v₂ + y₀ ∈ CFSG.Monster.GMS.co1Orbit 1) :
    Subgroup.closure ({regA 13, regA 18, regA 23} : Set NativeSporadic.Co1) = kc := by
  have := finite_co1_ct
  refine Subgroup.eq_of_le_of_card_ge ?_ (by
    rw [card_kc]
    have h1 := card_closure_three_ge
    rw [kp_eq_closure hy hs, card_kp hy hs] at h1
    exact h1)
  rw [Subgroup.closure_le]
  rintro g (rfl | rfl | hg)
  · exact kp_le_kc regA13_mem_kp
  · exact kp_le_kc regA18_mem_kp
  · rw [Set.mem_singleton_iff.1 hg]
    exact regA23_mem_kc

theorem kp_perfect
    (hy : y₀ ∈ CFSG.Monster.GMS.co1Orbit 0)
    (hs : v₂ + y₀ ∈ CFSG.Monster.GMS.co1Orbit 1) : ⁅kp, kp⁆ = kp := by
  refine le_antisymm (Subgroup.commutator_le_self kp) ?_
  calc kp = Subgroup.closure ({regA 13, regA 18} : Set NativeSporadic.Co1) :=
        (kp_eq_closure hy hs).symm
    _ ≤ ⁅kp, kp⁆ := by
      rw [Subgroup.closure_le]
      rintro g (rfl | hg)
      · exact regA13_mem_commutator
      · rw [Set.mem_singleton_iff.1 hg]
        exact regA18_mem_commutator

theorem kc_perfect
    (hy : y₀ ∈ CFSG.Monster.GMS.co1Orbit 0)
    (hs : v₂ + y₀ ∈ CFSG.Monster.GMS.co1Orbit 1) : ⁅kc, kc⁆ = kc := by
  refine le_antisymm (Subgroup.commutator_le_self kc) ?_
  calc kc = Subgroup.closure ({regA 13, regA 18, regA 23} : Set NativeSporadic.Co1) :=
        (kc_eq_closure hy hs).symm
    _ ≤ ⁅kc, kc⁆ := by
      rw [Subgroup.closure_le]
      rintro g (rfl | rfl | hg)
      · exact Subgroup.commutator_mono kp_le_kc kp_le_kc regA13_mem_commutator
      · exact Subgroup.commutator_mono kp_le_kc kp_le_kc regA18_mem_commutator
      · rw [Set.mem_singleton_iff.1 hg]
        exact regA23_mem_commutator

end CFSG.Sporadic.Co1.Module.CoTwo

