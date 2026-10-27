module

public import Mathlib.GroupTheory.PGroup
import Mathlib.Data.Rat.Floor

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.SL32Fix

variable {X : Type*} [Group X]

def omegaZ (U W : Subgroup X) (hWn : ∀ u ∈ U, ∀ w ∈ W, u * w * u⁻¹ ∈ W) : Subgroup X where
  carrier := {u | u ∈ U ∧ u * u ∈ W ∧ ∀ v ∈ U, u * v * u⁻¹ * v⁻¹ ∈ W}
  mul_mem' := by
    rintro a b ⟨haU, ha2, hac⟩ ⟨hbU, hb2, hbc⟩
    refine ⟨U.mul_mem haU hbU, ?_, ?_⟩
    · have hc : b * a * b⁻¹ * a⁻¹ ∈ W := hbc a haU
      have e : a * b * (a * b) = (a * (b * a * b⁻¹ * a⁻¹) * a⁻¹) * (a * a) * (b * b) := by group
      rw [e]
      exact W.mul_mem (W.mul_mem (hWn a haU _ hc) ha2) hb2
    · intro v hv
      have e : a * b * v * (a * b)⁻¹ * v⁻¹ =
          (a * (b * v * b⁻¹ * v⁻¹) * a⁻¹) * (a * v * a⁻¹ * v⁻¹) := by group
      rw [e]
      exact W.mul_mem (hWn a haU _ (hbc v hv)) (hac v hv)
  one_mem' := ⟨U.one_mem, by simpa using W.one_mem, fun v _ => by simpa using W.one_mem⟩
  inv_mem' := by
    rintro a ⟨haU, ha2, hac⟩
    refine ⟨U.inv_mem haU, ?_, ?_⟩
    · have e : a⁻¹ * a⁻¹ = (a * a)⁻¹ := by group
      rw [e]
      exact W.inv_mem ha2
    · intro v hv
      have h1 : v * a * v⁻¹ * a⁻¹ ∈ W := by
        have h := W.inv_mem (hac v hv)
        have e : (a * v * a⁻¹ * v⁻¹)⁻¹ = v * a * v⁻¹ * a⁻¹ := by group
        rwa [e] at h
      have h2 := hWn a⁻¹ (U.inv_mem haU) _ h1
      have e : a⁻¹ * (v * a * v⁻¹ * a⁻¹) * a⁻¹⁻¹ = a⁻¹ * v * a⁻¹⁻¹ * v⁻¹ := by group
      rwa [e] at h2

variable {U W : Subgroup X} (hWn : ∀ u ∈ U, ∀ w ∈ W, u * w * u⁻¹ ∈ W)

theorem omegaZ_le : omegaZ U W hWn ≤ U := fun _ hu => hu.1

theorem le_omegaZ (hWU : W ≤ U) : W ≤ omegaZ U W hWn := by
  intro w hw
  refine ⟨hWU hw, W.mul_mem hw hw, fun v hv => ?_⟩
  have h : v * w⁻¹ * v⁻¹ ∈ W := hWn v hv _ (W.inv_mem hw)
  have e : w * v * w⁻¹ * v⁻¹ = w * (v * w⁻¹ * v⁻¹) := by group
  rw [e]
  exact W.mul_mem hw h

theorem omegaZ_comm {a b : X} (ha : a ∈ omegaZ U W hWn) (hb : b ∈ U) :
    a * b * a⁻¹ * b⁻¹ ∈ W := ha.2.2 b hb

theorem omegaZ_sq {a : X} (ha : a ∈ omegaZ U W hWn) : a * a ∈ W := ha.2.1

theorem omegaZ_conj_U {u m : X} (hu : u ∈ U) (hm : m ∈ omegaZ U W hWn) :
    u * m * u⁻¹ ∈ omegaZ U W hWn := by
  obtain ⟨hmU, hm2, hmc⟩ := hm
  refine ⟨U.mul_mem (U.mul_mem hu hmU) (U.inv_mem hu), ?_, ?_⟩
  · have e : u * m * u⁻¹ * (u * m * u⁻¹) = u * (m * m) * u⁻¹ := by group
    rw [e]
    exact hWn u hu _ hm2
  · intro v hv
    have hv' : u⁻¹ * v * u ∈ U := U.mul_mem (U.mul_mem (U.inv_mem hu) hv) hu
    have h := hWn u hu _ (hmc _ hv')
    have e : u * (m * (u⁻¹ * v * u) * m⁻¹ * (u⁻¹ * v * u)⁻¹) * u⁻¹ =
        u * m * u⁻¹ * v * (u * m * u⁻¹)⁻¹ * v⁻¹ := by group
    rwa [e] at h

theorem omegaZ_conj_K {x m : X} (hxU : ∀ u ∈ U, x * u * x⁻¹ ∈ U)
    (hxU' : ∀ u ∈ U, x⁻¹ * u * x ∈ U) (hxW : ∀ w ∈ W, x * w * x⁻¹ ∈ W)
    (hm : m ∈ omegaZ U W hWn) : x * m * x⁻¹ ∈ omegaZ U W hWn := by
  obtain ⟨hmU, hm2, hmc⟩ := hm
  refine ⟨hxU m hmU, ?_, ?_⟩
  · have e : x * m * x⁻¹ * (x * m * x⁻¹) = x * (m * m) * x⁻¹ := by group
    rw [e]
    exact hxW _ hm2
  · intro v hv
    have h := hxW _ (hmc _ (hxU' v hv))
    have e : x * (m * (x⁻¹ * v * x) * m⁻¹ * (x⁻¹ * v * x)⁻¹) * x⁻¹ =
        x * m * x⁻¹ * v * (x * m * x⁻¹)⁻¹ * v⁻¹ := by group
    rwa [e] at h

theorem exists_mem_omegaZ_not_mem [Finite X] (hU2 : IsPGroup 2 U) (hWU : W < U) :
    ∃ u ∈ omegaZ U W hWn, u ∉ W := by
  classical
  haveI hN : (W.subgroupOf U).Normal := ⟨fun n hn g => hWn g g.2 n hn⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ2 : IsPGroup 2 (U ⧸ W.subgroupOf U) := hU2.to_quotient _
  obtain ⟨u₀, hu₀U, hu₀W⟩ := SetLike.exists_of_lt hWU
  haveI : Nontrivial (U ⧸ W.subgroupOf U) :=
    ⟨⟨((⟨u₀, hu₀U⟩ : U) : U ⧸ W.subgroupOf U), 1, fun h => hu₀W (by
      have h' := (QuotientGroup.eq_one_iff _).1 h
      rwa [Subgroup.mem_subgroupOf] at h')⟩⟩
  haveI := hQ2.center_nontrivial
  have hZ2 : IsPGroup 2 (Subgroup.center (U ⧸ W.subgroupOf U)) :=
    hQ2.of_injective (Subgroup.center (U ⧸ W.subgroupOf U)).subtype Subtype.val_injective
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 hZ2
  have hn0 : n ≠ 0 := by
    rintro rfl
    have h1 := Finite.one_lt_card_iff_nontrivial.2 (inferInstance :
      Nontrivial (Subgroup.center (U ⧸ W.subgroupOf U)))
    rw [hn] at h1
    simp at h1
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center (U ⧸ W.subgroupOf U)) 2
    (by rw [hn]; exact dvd_pow_self 2 hn0)
  have ht2 : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rwa [ht, pow_two] at h
  have ht1 : (t : U ⧸ W.subgroupOf U) ≠ 1 := by
    intro h
    have : t = 1 := Subtype.ext h
    rw [this, orderOf_one] at ht
    omega
  have hcent : ∀ g : U ⧸ W.subgroupOf U, g * t = t * g := Subgroup.mem_center_iff.1 t.2
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (t : U ⧸ W.subgroupOf U)
  refine ⟨u, ⟨u.2, ?_, ?_⟩, ?_⟩
  · have h : (((u * u : U)) : U ⧸ W.subgroupOf U) = 1 := by
      rw [QuotientGroup.mk_mul, hu]
      exact congrArg Subtype.val ht2
    have h' := (QuotientGroup.eq_one_iff _).1 h
    rwa [Subgroup.mem_subgroupOf] at h'
  · intro v hv
    have hc : ((u : U) : U ⧸ W.subgroupOf U) * ((⟨v, hv⟩ : U) : U ⧸ W.subgroupOf U) =
        ((⟨v, hv⟩ : U) : U ⧸ W.subgroupOf U) * ((u : U) : U ⧸ W.subgroupOf U) := by
      rw [hu]
      exact (hcent _).symm
    have h : (((u * ⟨v, hv⟩ * u⁻¹ * ⟨v, hv⟩⁻¹ : U)) : U ⧸ W.subgroupOf U) = 1 := by
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [hc]
      group
    have h' := (QuotientGroup.eq_one_iff _).1 h
    rwa [Subgroup.mem_subgroupOf] at h'
  · intro huW
    apply ht1
    rw [← hu]
    exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 huW)

end CFSG.RankThree.PartTwo.Sec21.FF81.SL32Fix
