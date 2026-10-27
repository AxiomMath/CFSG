module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtNoE9Z4P2Loc
public import CFSG.Quasithin.EmptyFaithful.S152He4Core

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique

section Small

variable {X : Type} [Group X] [Finite X]

theorem E9Local.false_of_smallFacts {L Th Hh Eh R : Subgroup X} (h : E9Local L Th Hh Eh R)
    (hs : He4.SmallFacts ↥L) : False := by
  classical
  have hsylU : IsSylowTwoOf ((Th ⊓ L).subgroupOf L) ⊤ :=
    E9P2.Loc.isSylowTwoOf_inf_subgroupOf h.sylow_T h.normal_L
  obtain ⟨m, hm, hodd⟩ := hs.card
  have hU16 : Nat.card ↥(Th ⊓ L) = 16 := by
    have h1 := He4.card_eq_of_isSylowTwoOf hsylU (c := 4) (m := m)
      (by rwa [Subgroup.card_top]) hodd
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv] at h1
    simpa using h1
  have hRle : R ⊓ L ≤ L := inf_le_right
  have hRL : R ⊓ L ≠ ⊥ := by
    intro hbot
    obtain ⟨φ, -, hφ⟩ := h.quot4
    let ψ : ↥(Th ⊓ L) →* Multiplicative (ZMod 4) := φ.comp (Subgroup.inclusion inf_le_left)
    have hinj : Function.Injective ψ := by
      rw [injective_iff_map_eq_one]
      intro v hv
      have hvR : ((Subgroup.inclusion inf_le_left v : ↥Th) : X) ∈ R := (hφ _).1 hv
      have hvL : (v : X) ∈ L := v.2.2
      have : (v : X) ∈ R ⊓ L := ⟨hvR, hvL⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact Subtype.ext this
    have hle := Nat.card_le_card_of_injective ψ hinj
    rw [hU16, Nat.card_eq_fintype_card] at hle
    simp at hle
  have hP : Nat.card ↥(Eh.subgroupOf L) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E_le_L).toEquiv]
    exact h.card_E
  have hR2 : IsPGroup 2 ↥((R ⊓ L).subgroupOf L) :=
    (h.sylow_T.2.1.to_le (inf_le_left.trans h.R_le_T)).of_equiv
      (Subgroup.subgroupOfEquivOfLe hRle).symm
  have hRne : (R ⊓ L).subgroupOf L ≠ ⊥ := by
    intro hb
    apply hRL
    have h1 : Nat.card ↥((R ⊓ L).subgroupOf L) = Nat.card ↥(R ⊓ L) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRle).toEquiv
    rw [hb, Subgroup.card_bot] at h1
    exact Subgroup.card_eq_one.1 h1.symm
  have hn : ∀ p ∈ Eh.subgroupOf L, ∀ r ∈ (R ⊓ L).subgroupOf L,
      p * r * p⁻¹ ∈ (R ⊓ L).subgroupOf L := by
    intro p hp r hr
    rw [Subgroup.mem_subgroupOf] at hp hr ⊢
    have hpH : (p : X) ∈ Hh := h.E_le_H hp
    refine ⟨?_, (p * r * p⁻¹ : ↥L).2⟩
    have := (Subgroup.mem_normalizer_iff.1 (h.R_norm hpH) (r : X)).1 hr.1
    simpa using this
  exact He4.lam_A hs (Eh.subgroupOf L) ((R ⊓ L).subgroupOf L) hP hR2 hRne hn

end Small

end CFSG.Quasithin
