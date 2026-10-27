module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.Tactic.NormNum.NatFactorial

public section

namespace CFSG

namespace FiveTransitive.A9SmallKernelFactor

theorem ker_le
    {G H F : Type*} [Group G] [Finite G] [Group H]
    [Fintype F] [DecidableEq F] (hF : Nat.card F = 9)
    (rho : G →* alternatingGroup F) (hrho : Function.Surjective rho)
    (sigma : G →* H) (hsmall : Nat.card sigma.ker < 181440) : sigma.ker ≤ rho.ker := by
  classical
  let _ : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let _ : IsSimpleGroup (alternatingGroup F) := alternatingGroup.isSimpleGroup (by omega)
  let K := sigma.ker.map rho
  let _ : K.Normal := (inferInstance : sigma.ker.Normal).map rho hrho
  have hb : K = ⊥ := by
    rcases (inferInstance : K.Normal).eq_bot_or_eq_top with h | h
    · exact h
    · have hh := Nat.le_of_dvd (Nat.card_pos (α := sigma.ker)) (sigma.ker.card_map_dvd rho)
      change Nat.card K ≤ Nat.card sigma.ker at hh
      rw [h,Subgroup.card_top,nat_card_alternatingGroup,hF] at hh
      norm_num only [Nat.factorial] at hh
      omega
  intro g hg
  have hm : rho g ∈ K := ⟨g,hg,rfl⟩
  rw [hb,Subgroup.mem_bot] at hm
  exact hm

theorem exists_factor
    {G H F : Type*} [Group G] [Finite G] [Group H]
    [Fintype F] [DecidableEq F] (hF : Nat.card F = 9)
    (rho : G →* alternatingGroup F) (hrho : Function.Surjective rho)
    (sigma : G →* H) (hsmall : Nat.card sigma.ker < 181440) :
    ∃ t : sigma.range →* alternatingGroup F,
      Function.Surjective t ∧ t.comp sigma.rangeRestrict = rho := by
  have hk : sigma.rangeRestrict.ker ≤ rho.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact ker_le hF rho hrho sigma hsmall
  let t := sigma.rangeRestrict.liftOfSurjective sigma.rangeRestrict_surjective ⟨rho,hk⟩
  have he : t.comp sigma.rangeRestrict = rho := by simp [t]
  refine ⟨t,?_,he⟩
  intro a
  obtain ⟨g,hg⟩ := hrho a
  refine ⟨sigma.rangeRestrict g,?_⟩
  change (t.comp sigma.rangeRestrict) g = a
  rw [he,hg]

end FiveTransitive.A9SmallKernelFactor

end CFSG
