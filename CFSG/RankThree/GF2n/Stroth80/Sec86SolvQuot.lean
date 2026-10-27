module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

public section

namespace CFSG.RankThree.GF2n.Stroth80

theorem sup_ker_eq_top_of_solvable {R S T : Type} [Group R] [Group S] [Group T]
    [IsSimpleGroup S] (hS : ¬ IsSolvable S) (π : R →* S) (hπ : Function.Surjective π)
    (ψ : R →* T) (hT : IsSolvable T) : ψ.ker ⊔ π.ker = ⊤ := by
  have hT' : Group.IsSolvable T := hT
  have hN : (ψ.ker.map π).Normal := Subgroup.Normal.map (inferInstance : ψ.ker.Normal) π hπ
  rcases Subgroup.Normal.eq_bot_or_eq_top (ψ.ker.map π) with h | h
  · exfalso
    have hle : ψ.ker ≤ π.ker := by
      intro k hk
      have hmem : π k ∈ ψ.ker.map π := Subgroup.mem_map_of_mem π hk
      rw [h, Subgroup.mem_bot] at hmem
      exact MonoidHom.mem_ker.mpr hmem
    have hquot : Group.IsSolvable (R ⧸ ψ.ker) := by
      let e := (QuotientGroup.quotientKerEquivRange ψ).symm
      exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
    have hsurj : Function.Surjective (QuotientGroup.lift ψ.ker π hle) := by
      intro s
      obtain ⟨r, hr⟩ := hπ s
      exact ⟨(r : R ⧸ ψ.ker), hr⟩
    exact hS (Group.isSolvable_of_surjective (f := QuotientGroup.lift ψ.ker π hle) hsurj)
  · refine (Subgroup.eq_top_iff' _).mpr fun r => ?_
    have hmem : π r ∈ ψ.ker.map π := by
      rw [h]
      exact Subgroup.mem_top _
    obtain ⟨k, hk, hkr⟩ := Subgroup.mem_map.mp hmem
    have hker : k⁻¹ * r ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hkr, inv_mul_cancel]
    have hmul : k * (k⁻¹ * r) ∈ ψ.ker ⊔ π.ker :=
      mul_mem (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right hker)
    rwa [mul_inv_cancel_left] at hmul

theorem not_isSolvable_of_simple_of_dvd {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (h : 16 ∣ Nat.card S) : ¬ IsSolvable S := by
  intro hS
  have hcomm : ∀ a b : S, a * b = b * a := IsSimpleGroup.comm_iff_isSolvable.mpr hS
  letI : CommGroup S := { ‹Group S› with mul_comm := hcomm }
  have hp : (Nat.card S).Prime := IsSimpleGroup.prime_card
  have h2 : 2 ∣ Nat.card S := by omega
  rcases hp.eq_one_or_self_of_dvd 2 h2 with h3 | h3
  · omega
  · omega

end CFSG.RankThree.GF2n.Stroth80
