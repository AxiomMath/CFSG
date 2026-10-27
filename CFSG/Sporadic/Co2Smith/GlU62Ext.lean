module

public import CFSG.Sporadic.Co2Smith.GlU62Psi
public import CFSG.Sporadic.Co2Smith.GlU62Gen

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
  CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.CurtisTits

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

variable {G : Type} [Group G] {z : G}
  {φ : centralizer ({z} : Set G) ≃* Cz} {ρ : C0c →* G}

theorem relIndex_G0c_G1c :
    G0c.relIndex G1c = 2 := by
  have h := card_mul_relIndex_of_le G0c_le_G1c
  rw [card_G0c, card_G1c] at h
  omega

theorem u62C1K_six : u62C1K 6 = δ0hK := by
  rw [u62C1K, u62C1_spec.2.2.2.2.1]
  rfl

theorem u62C1K_seven : u62C1K 7 = δ1hK := by
  rw [u62C1K, u62C1_spec.2.2.2.2.2.1]
  rfl

theorem δ1hK_mem_G1c :
    δ1hK ∈ G1c := by
  have := (u62C1K_mem 7).2
  rwa [u62C1K_seven] at this

theorem δ0hK_mem_G1c :
    δ0hK ∈ G1c := by
  have := (u62C1K_mem 6).2
  rwa [u62C1K_six] at this

theorem glD0hWord_mem_glG0Words : Native.glD0hWord ++ [10] ∈ Native.glG0Words := by
  decide +kernel

theorem δ0hK_not_mem_G0c :
    δ0hK ∉ G0c := by
  intro h
  apply γ3K_not_mem_G0c
  have h' : δ0hK * γ3K ∈ G0c := by
    rw [show δ0hK * γ3K = glE (Native.glD0hWord ++ [10]) by rw [glE_append]; rfl]
    exact Subgroup.subset_closure ⟨_, glD0hWord_mem_glG0Words, rfl⟩
  have := G0c.mul_mem (G0c.inv_mem h) h'
  rwa [inv_mul_cancel_left] at this

theorem mul_mem_G0c_iff
    {a b : K} (ha : a ∈ G1c)
    (hb : b ∈ G1c) : a * b ∈ G0c ↔ (a ∈ G0c ↔ b ∈ G0c) := by
  have h2 : (G0c.subgroupOf G1c).index = 2 := relIndex_G0c_G1c
  have := Subgroup.mul_mem_iff_of_index_two h2 (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] at this
  exact this

theorem mem_G0c_or_mul_δ1hK
    {k : K} (hk : k ∈ G1c) : k ∈ G0c ∨ k * δ1hK ∈ G0c := by
  by_cases h : k ∈ G0c
  · exact Or.inl h
  · exact Or.inr ((mul_mem_G0c_iff hk δ1hK_mem_G1c).2 (iff_of_false h δ1hK_not_mem_G0c))

@[expose] noncomputable def psi0Inv
    (hz : z ≠ 1)
    (hm : SmithC0Marking φ α3c ρ) (g : K) :
    G := by
  classical
  exact if h : g ∈ G0c then ((psi0 hz hm).symm ⟨g, h⟩ : G) else 1

theorem psi0Inv_of_mem
    (hz : z ≠ 1)
    (hm : SmithC0Marking φ α3c ρ) {g : K} (h : g ∈ G0c) :
    psi0Inv hz hm g = ((psi0 hz hm).symm ⟨g, h⟩ : G) := by
  classical
  rw [psi0Inv, dite_eq_left h]

theorem psi0Inv_mul
    (hz : z ≠ 1)
    (hm : SmithC0Marking φ α3c ρ) {a b : K} (ha : a ∈ G0c)
    (hb : b ∈ G0c) : psi0Inv hz hm (a * b) = psi0Inv hz hm a * psi0Inv hz hm b := by
  rw [psi0Inv_of_mem hz hm (G0c.mul_mem ha hb), psi0Inv_of_mem hz hm ha, psi0Inv_of_mem hz hm hb,
    psi0_symm_mul]

theorem psi0Inv_one
    (hz : z ≠ 1)
    (hm : SmithC0Marking φ α3c ρ) : psi0Inv hz hm 1 = 1 := by
  rw [psi0Inv_of_mem hz hm G0c.one_mem, show (⟨1, G0c.one_mem⟩ : G0c) = 1 from rfl, map_one]
  rfl

theorem psi0Inv_mem
    (hz : z ≠ 1)
    (hm : SmithC0Marking φ α3c ρ) (g : K) :
    psi0Inv hz hm g ∈ (thetaG hz hm).range := by
  classical
  unfold psi0Inv
  split_ifs
  · exact ((psi0 hz hm).symm _).2
  · exact Subgroup.one_mem _

theorem psi0Inv_injOn
    (hz : z ≠ 1)
    (hm : SmithC0Marking φ α3c ρ) {g : K} (hg : g ∈ G0c)
    (h : psi0Inv hz hm g = 1) : g = 1 := by
  rw [psi0Inv_of_mem hz hm hg] at h
  have : (psi0 hz hm).symm ⟨g, hg⟩ = 1 := Subtype.ext h
  rw [MulEquiv.symm_apply_eq, map_one] at this
  exact congrArg Subtype.val this

theorem psi0Inv_conj
    (hz : z ≠ 1)
    (hm : SmithC0Marking φ α3c ρ) {g : K} (hg : g ∈ G0c) :
    δ1hK * g * δ1hK ∈ G0c ∧
      rhoK ρ δ1hK * psi0Inv hz hm g * rhoK ρ δ1hK = psi0Inv hz hm (δ1hK * g * δ1hK) := by
  rw [← range_thetaK] at hg
  obtain ⟨x, rfl⟩ := hg
  obtain ⟨hmem, e⟩ := psi0_conj hz hm x
  have hδ : δ1hK * thetaK x * δ1hK ∈ G0c := by
    rw [← e]
    exact (psi0 hz hm _).2
  refine ⟨hδ, ?_⟩
  have hx : thetaK x ∈ G0c := by rw [← range_thetaK]; exact ⟨x, rfl⟩
  have e1 : psi0Inv hz hm (thetaK x) = thetaG hz hm x := by
    rw [psi0Inv_of_mem hz hm hx]
    have : (psi0 hz hm).symm ⟨thetaK x, hx⟩ = ⟨thetaG hz hm x, x, rfl⟩ :=
      (MulEquiv.symm_apply_eq _).2 (Subtype.ext (psi0_apply hz hm x).symm)
    rw [this]
  have e2 : psi0Inv hz hm (δ1hK * thetaK x * δ1hK) =
      rhoK ρ δ1hK * thetaG hz hm x * (rhoK ρ δ1hK)⁻¹ := by
    rw [psi0Inv_of_mem hz hm hδ]
    have : (psi0 hz hm).symm ⟨δ1hK * thetaK x * δ1hK, hδ⟩ = ⟨_, hmem⟩ :=
      (MulEquiv.symm_apply_eq _).2 (Subtype.ext e.symm)
    rw [this]
  rw [e1, e2, rhoK_δ1hK_inv]

theorem rhoK_δ1hK_not_mem
    (hz : z ≠ 1)
    (hm : SmithC0Marking φ α3c ρ) :
    rhoK ρ δ1hK ∉ (thetaG hz hm).range := by
  intro hd
  set k0 := (psi0 hz hm ⟨_, hd⟩ : K) with hk0
  have hk0m : k0 ∈ G0c := (psi0 hz hm ⟨_, hd⟩).2
  have hact : ∀ x : SU6, k0 * thetaK x * k0⁻¹ = δ1hK * thetaK x * δ1hK := by
    intro x
    obtain ⟨hmem, e⟩ := psi0_conj hz hm x
    rw [← e]
    have e' : (⟨rhoK ρ δ1hK * thetaG hz hm x * (rhoK ρ δ1hK)⁻¹, hmem⟩ : (thetaG hz hm).range) =
        ⟨_, hd⟩ * ⟨thetaG hz hm x, x, rfl⟩ * (⟨_, hd⟩)⁻¹ := rfl
    rw [e', map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      psi0_apply]
  have h1 : δ1hK⁻¹ * k0 = 1 := eq_one_of_comm_G0c fun g hg => by
    rw [← range_thetaK] at hg
    obtain ⟨x, rfl⟩ := hg
    have := hact x
    rw [δ1hK_inv_eq_self]
    calc δ1hK * k0 * thetaK x = δ1hK * (k0 * thetaK x * k0⁻¹) * k0 := by group
      _ = δ1hK * (δ1hK * thetaK x * δ1hK) * k0 := by rw [this]
      _ = thetaK x * (δ1hK * k0) := by
          rw [show δ1hK * (δ1hK * thetaK x * δ1hK) * k0 = (δ1hK * δ1hK) * thetaK x * (δ1hK * k0)
            by group, δ1hK_mul_self, one_mul]
  apply δ1hK_not_mem_G0c
  rw [inv_mul_eq_one.1 h1]
  exact hk0m

@[expose] noncomputable def extFun
    (hz : z ≠ 1)
    (hm : SmithC0Marking φ α3c ρ) (k : K) :
    G := by
  classical
  exact if k ∈ G0c then psi0Inv hz hm k else psi0Inv hz hm (k * δ1hK) * rhoK ρ δ1hK

theorem extFun_of_mem
    (hz : z ≠ 1)
    (hm : SmithC0Marking φ α3c ρ) {k : K} (h : k ∈ G0c) :
    extFun hz hm k = psi0Inv hz hm k := by
  classical
  rw [extFun, ite_eq_left_iff.2 fun h' => absurd h h']

theorem extFun_of_not_mem
    (hz : z ≠ 1)
    (hm : SmithC0Marking φ α3c ρ) {k : K}
    (h : k ∉ G0c) : extFun hz hm k = psi0Inv hz hm (k * δ1hK) * rhoK ρ δ1hK := by
  classical
  rw [extFun, ite_eq_right_iff.2 fun h' => absurd h' h]

end CFSG.Sporadic.Co2Smith
