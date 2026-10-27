module

public import CFSG.Quasithin.Background.RonanE114D4Quot

public section

namespace CFSG.Quasithin.RonanE114

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.E1
open scoped MatrixGroups

section Sup

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_sup_of_isPGroup {N T : Subgroup G} (hT : IsPGroup 2 ↥T)
    (hTN : T ≤ Subgroup.normalizer (N : Set G)) (hN : Group.IsSolvable ↥N) :
    Group.IsSolvable ↥(N ⊔ T) := by
  have hDN : N ⊔ T ≤ Subgroup.normalizer (N : Set G) :=
    sup_le Subgroup.le_normalizer hTN
  have hnorm : (N.subgroupOf (N ⊔ T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hDN
  have hN' : Group.IsSolvable ↥(N.subgroupOf (N ⊔ T)) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe (le_sup_left : N ≤ N ⊔ T)).toMonoidHom)
      (MulEquiv.injective _)
  have hq : IsPGroup 2 (↥(N ⊔ T) ⧸ N.subgroupOf (N ⊔ T)) := by
    intro x
    obtain ⟨d, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨k, hk⟩ := B6.isTwoQuotient_of_sup_eq hT hDN (by rw [sup_comm]) (d : G) d.2
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa using hk
  have hqs : Group.IsSolvable (↥(N ⊔ T) ⧸ N.subgroupOf (N ⊔ T)) := by
    have := hq.isNilpotent
    infer_instance
  haveI := hN'
  haveI := hqs
  exact solvable_of_ker_le_range (N.subgroupOf (N ⊔ T)).subtype
    (QuotientGroup.mk' (N.subgroupOf (N ⊔ T)))
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem nParam_le_of_levi_sup {J T : Subgroup G} (hT : IsPGroup 2 ↥T)
    (hTJ : T ≤ Subgroup.normalizer (J : Set G)) {F : Type} [Field F] [Finite F] {m : ℕ}
    (hF : Nat.card F = 2 ^ m) (hm : 2 ≤ m) (π : ↥J →* SL(2, F)) (hπ : Function.Surjective π)
    (hker : IsPGroup 2 ↥π.ker) : E1.nParam (J ⊔ T) ≤ (m : ℕ∞) := by
  have hDJ : J ⊔ T ≤ Subgroup.normalizer (J : Set G) := sup_le Subgroup.le_normalizer hTJ
  haveI hnorm : (J.subgroupOf (J ⊔ T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hDJ
  let e : ↥(J.subgroupOf (J ⊔ T)) ≃* ↥J := Subgroup.subgroupOfEquivOfLe le_sup_left
  have hQN : ∀ x : ↥(J ⊔ T), ∃ k : ℕ, x ^ 2 ^ k ∈ J.subgroupOf (J ⊔ T) := by
    intro x
    obtain ⟨k, hk⟩ := B6.isTwoQuotient_of_sup_eq hT hDJ (by rw [sup_comm]) (x : G) x.2
    refine ⟨k, ?_⟩
    rw [Subgroup.mem_subgroupOf]
    simpa using hk
  have hπ' : Function.Surjective (π.comp e.toMonoidHom) := hπ.comp e.surjective
  have hker' : IsPGroup 2 ↥(π.comp e.toMonoidHom).ker := by
    have : (π.comp e.toMonoidHom).ker = π.ker.comap e.toMonoidHom := rfl
    rw [this]
    exact IsPGroup.comap_of_injective hker e.toMonoidHom e.injective
  rw [E1.nParam_subgroupOf]
  exact nParam_top_le_of_levi hQN hF hm (π.comp e.toMonoidHom) hπ' hker'

end Sup

section Assembly

variable {G : Type} [Group G] [Finite G]

theorem nParam_top_le_of_parabolics {T B : Subgroup G} (hT : IsSylowIn 2 T ⊤)
    {P J : Fin 2 → Subgroup G} {M : ℕ} (hM : 1 ≤ M) (hgen : P 0 ⊔ P 1 ⊔ T = ⊤)
    (hBs : Group.IsSolvable ↥B) (hTB : T ≤ Subgroup.normalizer (B : Set G))
    (hPJ : ∀ j, P j ≤ B ⊔ J j) (hTJ : ∀ j, T ≤ Subgroup.normalizer (J j : Set G))
    (hJ : ∀ j, Group.IsSolvable ↥(J j) ∨
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (m : ℕ), Nat.card F = 2 ^ m ∧ 2 ≤ m ∧ m ≤ M ∧
        ∃ π : ↥(J j) →* SL(2, F), Function.Surjective π ∧ IsPGroup 2 ↥π.ker) :
    E1.nParam (⊤ : Subgroup G) ≤ (M : ℕ∞) := by
  have hT2 : IsPGroup 2 ↥T := hT.2.1
  set Δ : Set (Subgroup G) := {J 0 ⊔ T, J 1 ⊔ T, B ⊔ T} with hΔdef
  have hΔ : ⨆ D ∈ Δ, D = (⊤ : Subgroup G) := by
    refine le_antisymm le_top ?_
    rw [← hgen]
    have h0 : J 0 ⊔ T ≤ ⨆ D ∈ Δ, D :=
      le_iSup₂_of_le (J 0 ⊔ T) (by simp [hΔdef]) le_rfl
    have h1 : J 1 ⊔ T ≤ ⨆ D ∈ Δ, D :=
      le_iSup₂_of_le (J 1 ⊔ T) (by simp [hΔdef]) le_rfl
    have h2 : B ⊔ T ≤ ⨆ D ∈ Δ, D :=
      le_iSup₂_of_le (B ⊔ T) (by simp [hΔdef]) le_rfl
    refine sup_le (sup_le ?_ ?_) (le_sup_right.trans h2)
    · exact (hPJ 0).trans (sup_le (le_sup_left.trans h2) (le_sup_left.trans h0))
    · exact (hPJ 1).trans (sup_le (le_sup_left.trans h2) (le_sup_left.trans h1))
  have hTΔ : ∀ D ∈ Δ, T ≤ D := by
    intro D hD
    simp only [hΔdef, Set.mem_insert_iff, Set.mem_singleton_iff] at hD
    rcases hD with rfl | rfl | rfl <;> exact le_sup_right
  have hone : ∀ D : Subgroup G, Group.IsSolvable ↥D → E1.nParam D ≤ (M : ℕ∞) := fun D hD =>
    (E1.solvable_nParam_le_one hD).trans (by exact_mod_cast hM)
  have hnJ : ∀ j, E1.nParam (J j ⊔ T) ≤ (M : ℕ∞) := by
    intro j
    rcases hJ j with hs | ⟨F, _, _, m, hF, hm2, hmM, π, hπ, hker⟩
    · exact hone _ (isSolvable_sup_of_isPGroup hT2 (hTJ j) hs)
    · exact (nParam_le_of_levi_sup hT2 (hTJ j) hF hm2 π hπ hker).trans (by exact_mod_cast hmM)
  have hn : ∀ D ∈ Δ, E1.nParam D ≤ (M : ℕ∞) := by
    intro D hD
    simp only [hΔdef, Set.mem_insert_iff, Set.mem_singleton_iff] at hD
    rcases hD with rfl | rfl | rfl
    · exact hnJ 0
    · exact hnJ 1
    · exact hone _ (isSolvable_sup_of_isPGroup hT2 hTB hBs)
  exact E1.nParam_le_of_generated hT hΔ hTΔ hn

end Assembly

end CFSG.Quasithin.RonanE114
