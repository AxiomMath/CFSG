module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.StandardType.FrameRoute

theorem tmAsm_exists_sylow_le {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (N : Subgroup G)
    (h : (Nat.card N).factorization p = (Nat.card G).factorization p) :
    ∃ P : Sylow p G, (P : Subgroup G) ≤ N := by
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow p N))
  have hQ : Nat.card Q = p ^ (Nat.card N).factorization p := Sylow.card_eq_multiplicity Q
  refine ⟨Sylow.ofCard (Subgroup.map N.subtype (Q : Subgroup N)) ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective N.subtype_injective, hQ, h]
  · intro x hx
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hx
    exact y.2

theorem tmAsm_card_dvd_of_inf_eq_bot {G : Type*} [Group G] [Finite G] (M H Q : Subgroup G)
    (hMH : M ≤ H) (hQH : Q ≤ H) (hQn : (Q.subgroupOf H).Normal) (hinf : M ⊓ Q = ⊥) :
    Nat.card M ∣ Nat.card (H ⧸ Q.subgroupOf H) := by
  let f : M →* H ⧸ Q.subgroupOf H :=
    (QuotientGroup.mk' (Q.subgroupOf H)).comp (Subgroup.inclusion hMH)
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro m hm
    have h1 : (Subgroup.inclusion hMH m : H) ∈ Q.subgroupOf H := by
      simpa [f, QuotientGroup.eq_one_iff] using hm
    have h2 : (m : G) ∈ Q := by simpa [Subgroup.mem_subgroupOf] using h1
    have h3 : (m : G) ∈ M ⊓ Q := ⟨m.2, h2⟩
    rw [hinf, Subgroup.mem_bot] at h3
    exact Subtype.ext h3
  exact Subgroup.card_dvd_of_injective f hinj

theorem tmAsm_card_dvd_aut {G : Type*} [Group G] [Finite G] (M H J : Subgroup G) (hMH : M ≤ H)
    (hJH : J ≤ H) (hJn : (J.subgroupOf H).Normal)
    (hC : ∀ h ∈ H, (∀ j ∈ J, h * j = j * h) → h = 1) :
    Nat.card M ∣ Nat.card (MulAut J) := by
  let c : H →* MulAut J :=
    { toFun := fun h =>
        { toFun := fun j =>
            ⟨(h : G) * j * (h : G)⁻¹, by
              have := hJn.conj_mem ⟨j, hJH j.2⟩ (by simpa [Subgroup.mem_subgroupOf] using j.2) h
              simpa [Subgroup.mem_subgroupOf] using this⟩
          invFun := fun j =>
            ⟨(h : G)⁻¹ * j * (h : G), by
              have := hJn.conj_mem ⟨j, hJH j.2⟩ (by simpa [Subgroup.mem_subgroupOf] using j.2) h⁻¹
              simpa [Subgroup.mem_subgroupOf] using this⟩
          left_inv := fun j => by ext; simp [mul_assoc]
          right_inv := fun j => by ext; simp [mul_assoc]
          map_mul' := fun a b => by ext; simp [mul_assoc] }
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  have hinj : Function.Injective c := by
    rw [injective_iff_map_eq_one]
    intro h hh
    have h1 : h = 1 := by
      apply Subtype.ext
      apply hC h.1 h.2
      intro j hj
      have := congrArg (fun a : MulAut J => (a ⟨j, hj⟩ : G)) hh
      simp only [c, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.coe_mk, Equiv.coe_fn_mk,
        MulAut.one_apply] at this
      calc (h : G) * j = ((h : G) * j * (h : G)⁻¹) * h := by group
        _ = j * h := by rw [this]
    exact h1
  have hH : Nat.card H ∣ Nat.card (MulAut J) := Subgroup.card_dvd_of_injective c hinj
  exact (Subgroup.card_dvd_of_le hMH).trans hH

end CFSG.StandardType.FrameRoute

end
