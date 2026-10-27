module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4StdLocAut
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Simple
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModF4Yam
public import CFSG.LocalAnalysis.EvenBN.TwoF4.ModelLevi
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public noncomputable section

namespace CFSG.Quasithin.H13.F431.TwoF4

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.EvenBN.TwoF4
  CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_full_inner_field_automorphism_normal_form)

set_option linter.unusedSectionVars false

section Generic

variable {G : Type} [Group G]

theorem normalizer_eq_of_isCoatom [IsSimpleGroup G] {P : Subgroup G} (hc : IsCoatom P)
    (hne : P ≠ ⊥) : Subgroup.normalizer (P : Set G) = P := by
  rcases hc.le_iff.1 (Subgroup.le_normalizer (H := P)) with h | h
  · exfalso
    have hn : P.Normal := Subgroup.normalizer_eq_top_iff.1 h
    rcases hn.eq_bot_or_eq_top with h0 | h1
    · exact hne h0
    · exact hc.1 h1
  · exact h

theorem mem_normalizer_of_conj_mem_autStab {P : Subgroup G} {x : G}
    (h : MulAut.conj x ∈ autStab P) : x ∈ Subgroup.normalizer (P : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have := h y
  rwa [MulAut.conj_apply] at this

end Generic

section Model


variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem map_exactEntrywiseAut_rootJoin (σ : K ≃+* K) (I : Finset Idx) :
    (rootJoin K a I).map (exactEntrywiseAut F4.tag σ).toMonoidHom = rootJoin K a I := by
  have key : ∀ τ : K ≃+* K,
      (rootJoin K a I).map (exactEntrywiseAut F4.tag τ).toMonoidHom ≤ rootJoin K a I := by
    intro τ
    rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun i hi => ?_
    rw [rootV, Subgroup.closure_le]
    rintro _ ⟨u, rfl⟩
    show exactEntrywiseAut F4.tag τ (rootElt K a i u) ∈ rootJoin K a I
    rw [exactEntrywiseAut_apply, entrywiseHom_rootElt]
    exact rootV_le_rootJoin hi (rootElt_mem_rootV _ _)
  refine le_antisymm (key σ) fun g hg => ?_
  exact ⟨exactEntrywiseAut F4.tag σ.symm g, key σ.symm ⟨g, hg, rfl⟩,
    exactEntrywiseAut_right_inv σ g⟩

theorem exactEntrywiseAut_mem_normalizer_iff (σ : K ≃+* K) {J : Subgroup (ModGL F4.tag K)}
    (hJ : J.map (exactEntrywiseAut F4.tag σ).toMonoidHom = J) (g : ModGL F4.tag K) :
    exactEntrywiseAut F4.tag σ g ∈ Subgroup.normalizer (J : Set (ModGL F4.tag K)) ↔
      g ∈ Subgroup.normalizer (J : Set (ModGL F4.tag K)) := by
  have h := Subgroup.map_equiv_normalizer_eq J (exactEntrywiseAut F4.tag σ)
  rw [hJ] at h
  constructor
  · intro hg
    rw [← h] at hg
    obtain ⟨y, hy, hyg⟩ := hg
    rwa [(exactEntrywiseAut F4.tag σ).injective hyg] at hy
  · intro hg
    rw [← h]
    exact ⟨g, hg, rfl⟩

theorem mem_Pg_one_iff (hK : Nat.card K = 2 ^ (2 * a + 1)) {x : Gm K a} :
    x ∈ Pg K a ⟨1, by decide⟩ ↔
      (x : ModGL F4.tag K) ∈ Subgroup.normalizer (radR K a : Set (ModGL F4.tag K)) := by
  rw [Pg, Subgroup.mem_subgroupOf, ← reeGamma_inf_normalizer_radR hK, Subgroup.mem_inf]
  exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩

theorem mem_Pg_zero_iff (hK : Nat.card K = 2 ^ (2 * a + 1)) {x : Gm K a} :
    x ∈ Pg K a ⟨0, by decide⟩ ↔
      (x : ModGL F4.tag K) ∈ Subgroup.normalizer (radS K a : Set (ModGL F4.tag K)) := by
  rw [Pg, Subgroup.mem_subgroupOf, ← reeGamma_inf_normalizer_radS hK, Subgroup.mem_inf]
  exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩

theorem reeGammaFieldAut_mem_autStab_Pg_one (hK : Nat.card K = 2 ^ (2 * a + 1))
    (σ : K ≃+* K) : F4.reeGammaFieldAut K a σ ∈ autStab (Pg K a ⟨1, by decide⟩) := by
  intro x
  rw [mem_Pg_one_iff hK, mem_Pg_one_iff hK]
  exact (exactEntrywiseAut_mem_normalizer_iff σ (map_exactEntrywiseAut_rootJoin σ _)
    (x : ModGL F4.tag K)).symm

theorem reeGammaFieldAut_mem_autStab_Pg_zero (hK : Nat.card K = 2 ^ (2 * a + 1))
    (σ : K ≃+* K) : F4.reeGammaFieldAut K a σ ∈ autStab (Pg K a ⟨0, by decide⟩) := by
  intro x
  rw [mem_Pg_zero_iff hK, mem_Pg_zero_iff hK]
  exact (exactEntrywiseAut_mem_normalizer_iff σ (map_exactEntrywiseAut_rootJoin σ _)
    (x : ModGL F4.tag K)).symm

theorem normalizer_Pg_one (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Subgroup.normalizer (Pg K a ⟨1, by decide⟩ : Set (Gm K a)) = Pg K a ⟨1, by decide⟩ := by
  have hS := CFSG.Quasithin.H13.Sec53F.ReeF4.f4_yamStd ha hK
  have := isSimpleGroup_gm ha hK
  refine normalizer_eq_of_isCoatom hS.coatom₁ fun h => ?_
  have hz : zg hK ∈ Pg K a ⟨1, by decide⟩ := hS.le₁ (Subgroup.le_normalizer (zg_mem_Ug hK))
  rw [h, Subgroup.mem_bot] at hz
  have := orderOf_zg hK
  rw [hz, orderOf_one] at this
  exact absurd this (by norm_num)

theorem normalizer_Pg_zero (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    Subgroup.normalizer (Pg K a ⟨0, by decide⟩ : Set (Gm K a)) = Pg K a ⟨0, by decide⟩ := by
  have hS := CFSG.Quasithin.H13.Sec53F.ReeF4.f4_yamStd ha hK
  have := isSimpleGroup_gm ha hK
  refine normalizer_eq_of_isCoatom hS.coatom₀ fun h => ?_
  have hz : zg hK ∈ Pg K a ⟨0, by decide⟩ := hS.le₀ (Subgroup.le_normalizer (zg_mem_Ug hK))
  rw [h, Subgroup.mem_bot] at hz
  have := orderOf_zg hK
  rw [hz, orderOf_one] at this
  exact absurd this (by norm_num)

theorem exists_of_autStab_Pg (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {φ : MulAut (Gm K a)} (h1 : φ ∈ autStab (Pg K a ⟨1, by decide⟩))
    (h0 : φ ∈ autStab (Pg K a ⟨0, by decide⟩)) :
    ∃ b ∈ Pg K a ⟨1, by decide⟩ ⊓ Pg K a ⟨0, by decide⟩, ∃ σ : K ≃+* K,
      φ = MulAut.conj b * F4.reeGammaFieldAut K a σ := by
  obtain ⟨x, σ, rfl⟩ := exists_conj_fieldAut ha hK φ
  have hc : ∀ P : Subgroup (Gm K a), F4.reeGammaFieldAut K a σ ∈ autStab P →
      MulAut.conj x * F4.reeGammaFieldAut K a σ ∈ autStab P → MulAut.conj x ∈ autStab P :=
    fun P hσ hφ => by
      have := (autStab P).mul_mem hφ ((autStab P).inv_mem hσ)
      simpa using this
  refine ⟨x, Subgroup.mem_inf.2 ⟨?_, ?_⟩, σ, rfl⟩
  · rw [← normalizer_Pg_one ha hK]
    exact mem_normalizer_of_conj_mem_autStab
      (hc _ (reeGammaFieldAut_mem_autStab_Pg_one hK σ) h1)
  · rw [← normalizer_Pg_zero ha hK]
    exact mem_normalizer_of_conj_mem_autStab
      (hc _ (reeGammaFieldAut_mem_autStab_Pg_zero hK σ) h0)

end Model

end CFSG.Quasithin.H13.F431.TwoF4
