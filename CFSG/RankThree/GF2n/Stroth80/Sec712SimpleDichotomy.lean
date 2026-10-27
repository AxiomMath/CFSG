module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem simpleDichotomy_holds :
    ∀ (H : Type) [Group H] (R N D : Subgroup H) (S : Type) [Group S] [IsSimpleGroup S]
      (π : ↥R →* S), N ≤ R → Function.Surjective π → (∀ r : ↥R, π r = 1 ↔ (r : H) ∈ N) →
      (∀ r ∈ R, ∀ d ∈ D, r * d * r⁻¹ ∈ D) → D ⊓ R ≤ N ∨ R ≤ (D ⊓ R) ⊔ N := by
  intro H _ R N D S _ _ π _ hsurj hker hD
  have hYRn : ((D ⊓ R).subgroupOf R).Normal := by
    refine ⟨fun v hv g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hv ⊢
    exact Subgroup.mem_inf.2 ⟨hD g.1 g.2 v.1 (Subgroup.mem_inf.1 hv).1, (g * v * g⁻¹).2⟩
  haveI : (((D ⊓ R).subgroupOf R).map π).Normal := hYRn.map π hsurj
  have hdich := IsSimpleGroup.eq_bot_or_eq_top_of_normal (((D ⊓ R).subgroupOf R).map π)
  by_cases hbot : ((D ⊓ R).subgroupOf R).map π = ⊥
  · left
    intro y hy
    have hyR : y ∈ R := (Subgroup.mem_inf.1 hy).2
    have hy' : (⟨y, hyR⟩ : ↥R) ∈ (D ⊓ R).subgroupOf R := Subgroup.mem_subgroupOf.2 hy
    have hmem : π ⟨y, hyR⟩ ∈ ((D ⊓ R).subgroupOf R).map π := Subgroup.mem_map_of_mem π hy'
    rw [hbot, Subgroup.mem_bot] at hmem
    exact (hker ⟨y, hyR⟩).1 hmem
  · right
    have htop : ((D ⊓ R).subgroupOf R).map π = ⊤ := hdich.resolve_left hbot
    intro r hr
    have hmem : π ⟨r, hr⟩ ∈ ((D ⊓ R).subgroupOf R).map π := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨v, hv, hvr⟩ := Subgroup.mem_map.1 hmem
    have h4 : π (v⁻¹ * (⟨r, hr⟩ : ↥R)) = 1 := by
      rw [map_mul, map_inv, hvr, inv_mul_cancel]
    have h5 := (hker _).1 h4
    have hN' : (v : H)⁻¹ * r ∈ N := by
      simpa using h5
    have hv' : (v : H) ∈ D ⊓ R := Subgroup.mem_subgroupOf.1 hv
    have key : (v : H) * ((v : H)⁻¹ * r) ∈ (D ⊓ R) ⊔ N :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_left hv') (Subgroup.mem_sup_right hN')
    have e : (v : H) * ((v : H)⁻¹ * r) = r := by simp
    rw [e] at key
    exact key

end CFSG.RankThree.GF2n.Stroth80
