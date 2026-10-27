module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF146Case2aE
public import CFSG.LieType.Simplicity.Classical

public section

namespace CFSG.Quasithin.F146Field

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

section Generic

theorem center_eq_bot_of_perfect_simple {Y : Type*} [Group Y] [Group.IsPerfect Y]
    [IsSimpleGroup Y] : Subgroup.center Y = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with h | h
  · exact h
  · refine absurd ⟨⟨fun a b => ?_⟩⟩ (Group.IsPerfect.not_isMulCommutative Y)
    have hb : b ∈ Subgroup.center Y := by
      rw [h]
      exact Subgroup.mem_top b
    exact Subgroup.mem_center_iff.mp hb a

theorem nonempty_mulEquiv_quotient_center_of_cover {X Y : Type*} [Group X] [Group Y] (π : X →* Y)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center X)
    (hY : Subgroup.center Y = ⊥) : Nonempty (Y ≃* X ⧸ Subgroup.center X) := by
  have hcen : Subgroup.center X ≤ π.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    have hzY : π z ∈ Subgroup.center Y := by
      rw [Subgroup.mem_center_iff]
      intro w
      obtain ⟨y, rfl⟩ := hπ w
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz y]
    rw [hY] at hzY
    exact hzY
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective π hπ).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (le_antisymm hker hcen))⟩

end Generic

section Cover

variable {G : Type} [Group G] [Finite G] {T M H K : Subgroup G}

theorem Case2a.Setting.nonempty_mulEquiv_quotient_center (c : Case2a.Setting T M H K)
    (hZ : Subgroup.center ↥(E2.star (H ⊓ M) H K) = ⊥) :
    Nonempty (↥(E2.star (H ⊓ M) H K) ≃* OTwoQuot K ⧸ Subgroup.center (OTwoQuot K)) := by
  obtain ⟨π, hπ, hker, -⟩ := c.exists_cover
  exact nonempty_mulEquiv_quotient_center_of_cover π hπ hker hZ

theorem Case2a.Setting.isPerfect_star (c : Case2a.Setting T M H K) :
    Group.IsPerfect ↥(E2.star (H ⊓ M) H K) := by
  obtain ⟨π, hπ, -, -⟩ := c.exists_cover
  have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp c.comp)
  have : Group.IsPerfect (OTwoQuot K) := inferInstance
  exact Group.IsPerfect.ofSurjective hπ

theorem isCentralL3Sp4_of_star (c : Case2a.Setting T M H K) {m : ℕ} (hm : 2 ≤ m)
    (hty : IsPSL 3 2 m ↥(E2.star (H ⊓ M) H K) ∨ E2.IsSp4Prime m ↥(E2.star (H ⊓ M) H K)) :
    IsCentralL3Sp4 m (OTwoQuot K) := by
  have := c.isPerfect_star
  rcases hty with h | h
  · have : IsSimpleGroup ↥(E2.star (H ⊓ M) H K) :=
      (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 m h).2
    obtain ⟨e⟩ := c.nonempty_mulEquiv_quotient_center center_eq_bot_of_perfect_simple
    exact Or.inl (IsPSL.of_mulEquiv e h)
  · have h' : IsPSp4 2 m ↥(E2.star (H ⊓ M) H K) := by
      have hm1 : m ≠ 1 := by omega
      simpa [E2.IsSp4Prime, hm1] using h
    have : IsSimpleGroup ↥(E2.star (H ⊓ M) H K) :=
      CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp _ 2 2 m h'
    obtain ⟨e⟩ := c.nonempty_mulEquiv_quotient_center center_eq_bot_of_perfect_simple
    exact Or.inr (IsPSp4.of_mulEquiv e h')

end Cover

end CFSG.Quasithin.F146Field
