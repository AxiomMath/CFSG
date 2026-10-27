module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG

namespace FiveTransitive.Degree53SevenAutSectionAlgebra

open Subgroup

private theorem ker_le_of_seven_free
    {N A F : Type*} [Group N] [Group A] [Finite N]
    [Fintype F] [DecidableEq F] (hF : Nat.card F = 7)
    (f : N →* A) (rho : N →* Equiv.Perm F) (hrho : Function.Surjective rho)
    (hseven : ¬ 7 ∣ Nat.card f.ker) : f.ker ≤ rho.ker := by
  let _ : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let K := f.ker.map rho
  let _ : K.Normal := (inferInstance : f.ker.Normal).map rho hrho
  have hK : K = ⊥ := by
    by_contra hn
    have hnontriv : Nontrivial K := K.nontrivial_iff_ne_bot.mpr hn
    have hAlt : alternatingGroup F ≤ K :=
      Equiv.Perm.alternatingGroup_le_of_normal (by omega) hnontriv
    have hd : 7 ∣ Nat.card K := by
      apply dvd_trans (b := Nat.card (alternatingGroup F))
      · rw [nat_card_alternatingGroup,hF]
        norm_num [Nat.factorial]
      · exact Subgroup.card_dvd_of_le hAlt
    exact hseven (hd.trans (f.ker.card_map_dvd rho))
  intro n hn
  have hm : rho n ∈ K := ⟨n,hn,rfl⟩
  rw [hK,Subgroup.mem_bot] at hm
  exact hm

theorem exists_surjective_range_hom
    {N A F : Type*} [Group N] [Group A] [Finite N]
    [Fintype F] [DecidableEq F] (hF : Nat.card F = 7)
    (f : N →* A) (rho : N →* Equiv.Perm F) (hrho : Function.Surjective rho)
    (hseven : ¬ 7 ∣ Nat.card f.ker) :
    ∃ tau : f.range →* Equiv.Perm F, Function.Surjective tau := by
  have hk : f.rangeRestrict.ker ≤ rho.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact ker_le_of_seven_free hF f rho hrho hseven
  let tau : f.range →* Equiv.Perm F :=
    f.rangeRestrict.liftOfSurjective f.rangeRestrict_surjective ⟨rho,hk⟩
  have he : tau.comp f.rangeRestrict = rho := by simp [tau]
  refine ⟨tau,?_⟩
  intro z
  obtain ⟨n,hn⟩ := hrho z
  refine ⟨f.rangeRestrict n,?_⟩
  change (tau.comp f.rangeRestrict) n = z
  rw [he,hn]

theorem five_dvd_codomain
    {N A F : Type*} [Group N] [Group A] [Finite N] [Finite A]
    [Fintype F] [DecidableEq F] (hF : Nat.card F = 7)
    (f : N →* A) (rho : N →* Equiv.Perm F) (hrho : Function.Surjective rho)
    (hfive : ¬ 5 ∣ Nat.card f.ker) : 5 ∣ Nat.card A := by
  have hN : 5 ∣ Nat.card N := by
    apply dvd_trans (b := Nat.card (Equiv.Perm F))
    · rw [Nat.card_perm,hF]
      norm_num [Nat.factorial]
    · exact Subgroup.card_dvd_of_surjective hrho
  have hm := f.ker.card_mul_index
  rw [Subgroup.index_ker] at hm
  rw [← hm] at hN
  have hr := ((show Nat.Prime 5 by decide).dvd_mul.mp hN).resolve_left hfive
  exact hr.trans (Subgroup.card_subgroup_dvd_card f.range)

end FiveTransitive.Degree53SevenAutSectionAlgebra

end CFSG
