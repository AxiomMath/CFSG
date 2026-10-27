
module

public import CFSG.Sporadic.Th.KernelSimpleBase

public import CFSG.Sporadic.Th.KernelPlanes
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.Sporadic.Th.Kernel

open CFSG.Sporadic.Bridge CFSG.Sporadic.ThSchreier CFSG.Sporadic.Th.Max3 TauCeti Pointwise
  MulAction

theorem a_mul_a : a * a = 1 :=
  Subtype.ext (Units.ext matA_mul_self)

variable (h : KernelFacts)
include h

theorem a_ne_one : a ≠ 1 := by
  intro ha
  have hJ := card_J_eq h
  have htop : (⊤ : Subgroup J) ≤ Subgroup.zpowers b := by
    rw [← closure_ab, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · rw [ha]
      exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers b
  have h1 : Nat.card J ≤ 3 := by
    rw [← Subgroup.card_top (G := J)]
    refine (Subgroup.card_le_of_le htop).trans ?_
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num)
      (by rw [pow_three, ← mul_assoc]; exact AllConj.b_mul_b_mul_b)
  rw [hJ] at h1
  exact absurd h1 (by norm_num [thOrder])

theorem b_ne_one : b ≠ 1 := by
  intro hb
  have hJ := card_J_eq h
  have htop : (⊤ : Subgroup J) ≤ Subgroup.zpowers a := by
    rw [← closure_ab, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact Subgroup.mem_zpowers a
    · rw [hb]
      exact Subgroup.one_mem _
  have h1 : Nat.card J ≤ 2 := by
    rw [← Subgroup.card_top (G := J)]
    refine (Subgroup.card_le_of_le htop).trans ?_
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num) (by rw [sq]; exact a_mul_a)
  rw [hJ] at h1
  exact absurd h1 (by norm_num [thOrder])

theorem orderOf_a : orderOf a = 2 :=
  orderOf_eq_prime (by rw [sq]; exact a_mul_a) (a_ne_one h)

theorem orderOf_b : orderOf b = 3 :=
  orderOf_eq_prime (by rw [pow_three, ← mul_assoc]; exact AllConj.b_mul_b_mul_b) (b_ne_one h)

theorem orderOf_ab : orderOf (a * b) = 19 := by
  have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  refine orderOf_eq_prime h.ab19 fun hab => ?_
  have hb : b = a⁻¹ := eq_inv_of_mul_eq_one_right hab
  have h3 := orderOf_b h
  rw [hb, orderOf_inv, orderOf_a h] at h3
  exact absurd h3 (by norm_num)

theorem faithful_planeX : FaithfulSMul J planeX := by
  have := h.finite
  have hP := card_P_eq h
  obtain ⟨v, -, -, -, -, -, -, -, hcore⟩ := h.dce hP
  obtain ⟨e, hK, -⟩ := exists_equiv h
  have hSt := (stabilizer_planeWSet_eq h).1
  have hStK : ∀ g : J, g • planeWSet = planeWSet → e.symm g ∈ K := by
    obtain ⟨-, -, hKc⟩ := isPreprimitive_Om h
    have hKS : K.map (e : P →* J) ≤ MulAction.stabilizer J planeWSet := by
      rw [K, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact MulAction.mem_stabilizer_iff.2 (hK i i.2).2
    have hcard : Nat.card (MulAction.stabilizer J planeWSet) ≤ Nat.card (K.map (e : P →* J)) := by
      rw [Subgroup.card_map_of_injective e.injective, hKc, hSt, card_H h]
    have heq := Subgroup.eq_of_le_of_card_ge hKS hcard
    intro g hg
    have hg' : g ∈ K.map (e : P →* J) := heq ▸ MulAction.mem_stabilizer_iff.2 hg
    obtain ⟨k, hk, rfl⟩ := hg'
    simpa using hk
  refine ⟨fun {g₁ g₂} hg => ?_⟩
  obtain ⟨g, hgdef⟩ : ∃ g : J, g = g₂⁻¹ * g₁ := ⟨_, rfl⟩
  have hfix : ∀ x : planeX, g • x = x := by
    intro x
    rw [hgdef, mul_smul, hg x, inv_smul_smul]
  have hconj : ∀ p : P, p⁻¹ * e.symm g * p ∈ K := by
    intro p
    have hrw : p⁻¹ * e.symm g * p = e.symm ((e p)⁻¹ * g * e p) := by
      rw [map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
    rw [hrw]
    apply hStK
    have hx : e p • planeWSet ∈ planeX := ⟨e p, rfl⟩
    have := congrArg Subtype.val (hfix ⟨e p • planeWSet, hx⟩)
    change g • (e p • planeWSet) = e p • planeWSet at this
    rw [mul_smul, mul_smul, this, inv_smul_smul]
  have hmem : ∀ s : P, (∀ p : P, p⁻¹ * s * p ∈ K) → s ∈ stabK (v 3) := by
    intro s hs
    refine ⟨by simpa using hs 1, (v 3)⁻¹ * s * v 3, hs (v 3), ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hs1 := hmem _ hconj
  have hs2 : (gen 1)⁻¹ * e.symm g * gen 1 ∈ stabK (v 3) := by
    refine hmem _ fun p => ?_
    have := hconj (gen 1 * p)
    simpa [mul_assoc] using this
  have hs := hcore _ hs1 hs2
  have hg1 : g = 1 := by
    have := (e.apply_symm_apply g).symm
    rwa [hs, map_one] at this
  rw [hgdef] at hg1
  exact (inv_mul_eq_one.1 hg1).symm

set_option maxRecDepth 8000 in
theorem isSimpleGroup_J : IsSimpleGroup J := by
  have := faithful_planeX h
  have := isPreprimitive_planeX h
  have : Finite J := inferInstance
  have : Finite planeX := planeX_finite.to_subtype
  have hmem : planeWSet ∈ planeX := MulAction.mem_orbit_self _
  refine CFSG.Sporadic.Th.isSimpleGroup_of_primitive_coprime_orders (Ω := planeX) ?_ a b
    closure_ab ⟨planeWSet, hmem⟩ ?_ ?_
  · rw [Nat.card_coe_set_eq, ncard_planeX h]
    norm_num
  · rw [orderOf_a h, orderOf_b h]
    norm_num
  · have e : MulAction.stabilizer J (⟨planeWSet, hmem⟩ : planeX) =
        MulAction.stabilizer J planeWSet := by
      ext g
      rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, Subtype.ext_iff]
      rfl
    rw [orderOf_ab h, e, (stabilizer_planeWSet_eq h).1, card_H h]
    norm_num

theorem isSimpleGroup_Th : IsSimpleGroup Blueprint.NativeSporadic.Th :=
  @MulEquiv.isSimpleGroup _ _ _ _ (isSimpleGroup_J h) thEquivJ

end CFSG.Sporadic.Th.Kernel
