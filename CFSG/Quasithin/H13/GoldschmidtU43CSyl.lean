module

public import CFSG.Quasithin.H13.GoldschmidtU43CAut

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

theorem factorization_288 : (288 : ℕ).factorization 3 = 2 := by
  have h288 : (288 : ℕ) = 3 ^ 2 * 2 ^ 5 := by norm_num
  rw [h288, Nat.factorization_mul (by positivity) (by positivity),
    Nat.Prime.factorization_pow Nat.prime_three, Nat.Prime.factorization_pow Nat.prime_two]
  simp

variable {G : Type} [Group G]

namespace Hyp

variable {z : G} (h : Hyp z)

noncomputable def Wsub : Subgroup ↥(Hz z) := Rbar.comap h.act

theorem mem_Wsub {x : ↥(Hz z)} : x ∈ h.Wsub ↔ h.act x ∈ Rbar := Iff.rfl

theorem ker_le_Wsub : h.act.ker ≤ h.Wsub := fun x hx => by
  rw [mem_Wsub, MonoidHom.mem_ker.mp hx]
  exact one_mem _

theorem Wsub_normal : (h.Wsub).Normal where
  conj_mem n hn g := by
    rw [mem_Wsub] at hn ⊢
    rw [map_mul, map_mul, map_inv]
    exact conj_mem_Rbar (h.act_mem_Oq g) hn

theorem map_Wsub [Finite G] : h.Wsub.map h.act = Rbar := by
  ext r
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hr
    obtain ⟨x, hx⟩ := h.mem_range_of_pow_three hr.1 hr.2
    exact ⟨x, show h.act x ∈ Rbar by rw [hx]; exact hr, hx⟩

theorem card_Wsub [Finite G] : Nat.card h.Wsub = 288 := by
  set X : Subgroup G := h.Wsub.map (Hz z).subtype with hX
  have hXH : X ≤ Hz z := Subgroup.map_subtype_le _
  have hUX : Uz z ≤ X := by
    intro u hu
    refine ⟨⟨u, Uz_le_Hz z hu⟩, ?_, rfl⟩
    have : (⟨u, Uz_le_Hz z hu⟩ : ↥(Hz z)) ∈ h.act.ker := by
      rw [h.ker_act]
      exact hu
    exact h.ker_le_Wsub this
  have e := h.card_map_act_mul X hUX hXH
  have hsub : X.subgroupOf (Hz z) = h.Wsub :=
    Subgroup.comap_map_eq_self_of_injective (Hz z).subtype_injective _
  have hcard : Nat.card X = Nat.card h.Wsub :=
    Subgroup.card_map_of_injective (Hz z).subtype_injective
  rw [hsub, h.map_Wsub, card_Rbar, hcard] at e
  omega

theorem exists_sylowR [Finite G] : ∃ R : Subgroup ↥(Hz z), R ≤ h.Wsub ∧ Nat.card R = 9 ∧
    Subgroup.normalizer (R : Set ↥(Hz z)) ⊔ h.Wsub = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := h.Wsub_normal
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 3 ↥h.Wsub))
  refine ⟨(P : Subgroup ↥h.Wsub).map h.Wsub.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective h.Wsub.subtype_injective, P.card_eq_multiplicity,
      h.card_Wsub, factorization_288]
    norm_num
  · exact Sylow.normalizer_sup_eq_top P

end Hyp

end CFSG.Quasithin.H13.U43
