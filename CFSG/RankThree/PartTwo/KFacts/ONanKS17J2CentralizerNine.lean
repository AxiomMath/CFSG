module

public import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
public import CFSG.RankThree.PartTwo.KFacts.ONanS3A4

public section

namespace CFSG.RankThree.PartTwo.KFacts

open Subgroup

theorem mem_normalizer_zpowers_of_commute {X : Type*} [Group X] {a g : X} (h : g * a = a * g) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers a : Set X) := by
  have hc : Commute g a := h
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨k, rfl⟩
    rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
    exact ⟨k, rfl⟩
  · rintro ⟨k, hk⟩
    have hcomm : g * a ^ k = a ^ k * g := (hc.zpow_right k).eq
    have hk' : a ^ k = g * x * g⁻¹ := hk
    have hx : x = a ^ k := by
      calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = g⁻¹ * a ^ k * g := by rw [← hk']
        _ = g⁻¹ * (a ^ k * g) := mul_assoc _ _ _
        _ = g⁻¹ * (g * a ^ k) := by rw [hcomm]
        _ = a ^ k := inv_mul_cancel_left g _
    exact ⟨k, hx.symm⟩

theorem ks17J2CentralizerNine :
    ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2) →
      ∀ E : Subgroup X, Nat.card E = 9 → Subgroup.centralizer (E : Set X) ≤ E := by
  intro X _ _ hX E hE9
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEp : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hE9]; norm_num)
  obtain ⟨P, hEP⟩ := hEp.exists_le_sylow
  have h415 := Sec4.Sporadic.rank3II_4_15 X hX P _ rfl _ rfl
  obtain ⟨⟨hHeis, -⟩, -, -, h4, -⟩ := h415
  have hZ3 : Nat.card ((P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X) :
      Subgroup X) = 3 := by
    rw [Sec4.Sporadic.inf_centralizer_eq_map_center,
      Subgroup.card_map_of_injective (P : Subgroup X).subtype_injective]
    exact hHeis.1.2.2.2
  obtain ⟨a, haE, haZ⟩ : ∃ a ∈ E, a ∉ ((P : Subgroup X) ⊓
      Subgroup.centralizer ((P : Subgroup X) : Set X) : Subgroup X) := by
    by_contra hall
    push Not at hall
    have hle : E ≤ ((P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X) :
        Subgroup X) := fun x hx => hall x hx
    have := Subgroup.card_le_of_le hle
    rw [hE9, hZ3] at this
    omega
  obtain ⟨-, ⟨ψ⟩, -⟩ := h4 E ⟨hEP, hE9⟩ a haE haZ
  have hEcomm : IsMulCommutative E := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3)
    (by rw [hE9]; norm_num)
  have hEN : E ≤ Subgroup.normalizer (Subgroup.zpowers a : Set X) := fun e he =>
    mem_normalizer_zpowers_of_commute (congrArg Subtype.val
      (hEcomm.is_comm.comm ⟨e, he⟩ ⟨a, haE⟩))
  intro g hg
  have hga : a * g = g * a := Subgroup.mem_centralizer_iff.mp hg a haE
  have hgN : g ∈ Subgroup.normalizer (Subgroup.zpowers a : Set X) :=
    mem_normalizer_zpowers_of_commute hga.symm
  set EN := E.subgroupOf (Subgroup.normalizer (Subgroup.zpowers a : Set X)) with hEN'
  have hENcard : Nat.card EN = 9 := by
    rw [← hE9]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEN).toEquiv
  set S := EN.map ψ.toMonoidHom with hS
  have hS9 : Nat.card S = 9 := by
    rw [hS, Subgroup.card_map_of_injective ψ.injective, hENcard]
  have hψg : ψ ⟨g, hgN⟩ ∈ Subgroup.centralizer (S : Set S3A4) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨en, hen, rfl⟩
    change ψ en * ψ ⟨g, hgN⟩ = ψ ⟨g, hgN⟩ * ψ en
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hg en.1 (Subgroup.mem_subgroupOf.mp hen)
  obtain ⟨en, hen, hen_eq⟩ := centralizer_le_of_card_nine S hS9 hψg
  have hen' : en = ⟨g, hgN⟩ := ψ.injective hen_eq
  rw [hen'] at hen
  exact Subgroup.mem_subgroupOf.mp hen

end CFSG.RankThree.PartTwo.KFacts
