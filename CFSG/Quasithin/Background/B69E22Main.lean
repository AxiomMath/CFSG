module

public import CFSG.Quasithin.Background.B69E22Link

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank

namespace B69

theorem center_eq_bot_of_perfect_simple {Q : Type} [Group Q] [IsSimpleGroup Q] [Group.IsPerfect Q] :
    Subgroup.center Q = ⊥ := by
  rcases CFSG.eq_bot_or_eq_top_of_normal (Subgroup.center Q)
      (inferInstance : (Subgroup.center Q).Normal) with hbot | htop
  · exact hbot
  · exact (Group.IsPerfect.not_isMulCommutative Q (Subgroup.center_eq_top_iff.mp htop)).elim

theorem equiv_of_central_quotients {L Q₁ Q₂ : Type} [Group L] [Group Q₁] [Group Q₂]
    (hL : CFSG.Open.IsQuasisimple L) (f₁ : L →* Q₁) (h₁ : Function.Surjective f₁)
    (f₂ : L →* Q₂) (h₂ : Function.Surjective f₂) [IsSimpleGroup Q₁] [IsSimpleGroup Q₂] :
    Nonempty (Q₁ ≃* Q₂) := by
  have hLperf : Group.IsPerfect L := Group.isPerfect_def.mpr hL.1
  have hker : ∀ {Q : Type} [Group Q] [IsSimpleGroup Q] (f : L →* Q), Function.Surjective f →
      f.ker = Subgroup.center L := by
    intro Q _ _ f hf
    have : Group.IsPerfect Q := Group.IsPerfect.ofSurjective hf
    have hne : f.ker ≠ ⊤ := by
      intro htop
      obtain ⟨a, b, hab⟩ := (inferInstance : Nontrivial Q).exists_pair_ne
      obtain ⟨x, rfl⟩ := hf a
      obtain ⟨y, rfl⟩ := hf b
      apply hab
      have hx : x ∈ f.ker := by rw [htop]; trivial
      have hy : y ∈ f.ker := by rw [htop]; trivial
      rw [MonoidHom.mem_ker.mp hx, MonoidHom.mem_ker.mp hy]
    apply le_antisymm
    · exact CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top hL f.ker hne
    · intro z hz
      rw [MonoidHom.mem_ker]
      have : f z ∈ Subgroup.center Q := by
        rw [Subgroup.mem_center_iff]
        intro q
        obtain ⟨x, rfl⟩ := hf q
        rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz x).symm]
      rw [center_eq_bot_of_perfect_simple] at this
      exact Subgroup.mem_bot.mp this
  have h : f₁.ker = f₂.ker := (hker f₁ h₁).trans (hker f₂ h₂).symm
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective f₁ h₁).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq h).trans (QuotientGroup.quotientKerEquivOfSurjective f₂ h₂))⟩

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem isComponentOf_subgroupOf {X L : Subgroup (MulAut V)}
    (hL : CFSG.Open.IsComponentOf L X) : CFSG.Open.IsComponentOf (L.subgroupOf X) ⊤ :=
  ⟨le_top, (CFSG.Adapters.isSubnormal_top_iff _).2 (isSubnormal_subgroupOf_of_chain hL.2.1),
    CFSG.ComponentClassification.Components.quasisimple_of_equiv
      (Subgroup.subgroupOfEquivOfLe hL.1) hL.2.2⟩

end B69

end CFSG.Quasithin
