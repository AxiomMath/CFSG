module

public import CFSG.Quasithin.Background.B2Factorization
public import CFSG.Quasithin.Background.InternalSecB51

public section

namespace CFSG.Quasithin.AutOn

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.InternalSec CFSG.QuasithinUnique Subgroup
open scoped IsMulCommutative commutatorElement

theorem commutator_eq_or_eq_bot_of_simple {Ω : Type*} [Group Ω] {K A : Subgroup Ω}
    (hK : IsSimpleGroup ↥K) (hA : A ≤ normalizer (K : Set Ω)) : ⁅K, A⁆ = K ∨ ⁅K, A⁆ = ⊥ := by
  have hle : ⁅K, A⁆ ≤ K := le_normalizer_iff_commutator_le_left.mp hA
  have hN : ((⁅K, A⁆ : Subgroup Ω).subgroupOf K).Normal :=
    (normal_subgroupOf_iff_le_normalizer hle).mpr (normalizer_commutator_ge_left K A)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((⁅K, A⁆ : Subgroup Ω).subgroupOf K) with h | h
  · right
    rw [eq_bot_iff_forall]
    intro x hx
    have h1 : (⟨x, hle hx⟩ : K) ∈ (⁅K, A⁆ : Subgroup Ω).subgroupOf K := hx
    rw [h, mem_bot] at h1
    exact congrArg Subtype.val h1
  · left
    refine le_antisymm hle fun k hk => ?_
    have : (⟨k, hk⟩ : ↥K) ∈ (⁅K, A⁆ : Subgroup Ω).subgroupOf K := by
      rw [h]
      trivial
    exact this

variable {G : Type} [Group G] [Finite G]

theorem exists_isFFStarOffender_moving {T L Y W : Subgroup G} [IsMulCommutative ↥W]
    (hT : IsSylowTwoOf T Y) (hTL : T ≤ normalizer (L : Set G)) (hred : IsTwoReducedIn Y W)
    (hLW : L ≤ normalizer (W : Set G)) (hsimp : IsSimpleGroup ↥(autOn L W))
    (hJ : L = ⁅L, thompsonJ T⁆) :
    ∃ A : Subgroup G, IsMaxElemAbelian T A ∧
      IsFFStarOffender (autOn Y W) (autOn A W) ∧ ⁅autOn L W, autOn A W⁆ = autOn L W := by
  have hWe : IsElemAbelian 2 W := hred.2.2.1
  have hTW : T ≤ normalizer (W : Set G) := hT.1.trans hred.2.1
  have hKne : autOn L W ≠ ⊥ := by
    intro h0
    obtain ⟨x, y, hxy⟩ := hsimp.toNontrivial.exists_pair_ne
    apply hxy
    have hx : (x : MulAut ↥W) = 1 := (eq_bot_iff_forall _).mp h0 (x : MulAut ↥W) x.2
    have hy : (y : MulAut ↥W) = 1 := (eq_bot_iff_forall _).mp h0 (y : MulAut ↥W) y.2
    exact Subtype.ext (hx.trans hy.symm)
  have hnorm : ∀ A : Subgroup G, A ≤ T →
      autOn A W ≤ normalizer (autOn L W : Set (MulAut ↥W)) := by
    intro A hAT x hx
    have hc := autOn_normal_of (U := W) (hAT.trans hTL)
    rw [mem_normalizer_iff]
    intro k
    refine ⟨fun hk => hc x hx k hk, fun hk => ?_⟩
    have := hc x⁻¹ ((autOn A W).inv_mem hx) _ hk
    simpa [mul_assoc] using this
  by_cases hex : ∃ A : Subgroup G, IsMaxElemAbelian T A ∧ ⁅autOn L W, autOn A W⁆ = autOn L W
  · obtain ⟨A, hA, hLA⟩ := hex
    have hAC : ¬ A ≤ centralizer (W : Set G) := by
      intro hAC
      have h0 : autOn A W = ⊥ := autI_eq_bot_of_le_centralizer hWe hAC
      rw [h0, commutator_bot_right] at hLA
      exact hKne hLA.symm
    have hoff : IsFFOffender Y W A := ⟨isMaxElemAbelian_of_isSylowTwoOf hT hA, hAC⟩
    exact ⟨A, hA, offenderImages_isFFStarOffender hWe hred.1 hred.2.1 ⟨A, hoff, rfl⟩, hLA⟩
  · exfalso
    push Not at hex
    have hbot : ∀ A : Subgroup G, IsMaxElemAbelian T A →
        autOn A W ≤ centralizer (autOn L W : Set (MulAut ↥W)) := by
      intro A hA
      rcases commutator_eq_or_eq_bot_of_simple hsimp (hnorm A hA.1) with h1 | h1
      · exact absurd h1 (hex A hA)
      · rw [commutator_eq_bot_iff_le_centralizer] at h1
        intro x hx
        rw [mem_centralizer_iff]
        intro k hk
        exact (mem_centralizer_iff.mp (h1 hk) x hx).symm
    set S : Subgroup G :=
      ((centralizer (autOn L W : Set (MulAut ↥W))).comap (conjAct W)).map
        (normalizer (W : Set G)).subtype with hS
    have hJS : thompsonJ T ≤ S := by
      refine iSup₂_le fun A hA => ?_
      intro a ha
      have haN : a ∈ normalizer (W : Set G) := hTW (hA.1 ha)
      exact ⟨⟨a, haN⟩, hbot A hA (CFSG.Quasithin.AutOn.mem_autOn_iff.2 ⟨⟨a, haN⟩, ha, rfl⟩), rfl⟩
    apply hKne
    rw [eq_bot_iff]
    intro φ hφ
    obtain ⟨⟨l, hlN⟩, hl, rfl⟩ := hφ
    rw [mem_bot]
    have hlC : l ∈ centralizer (W : Set G) := by
      have hLC : L ≤ centralizer (W : Set G) := by
        rw [hJ, commutator_le]
        intro l hl j hj
        obtain ⟨g, hg, rfl⟩ := hJS hj
        set lN : ↥(normalizer (W : Set G)) := ⟨l, hLW hl⟩
        have hlK : conjAct W lN ∈ autOn L W := InternalSec.conjAct_mem_autOn hLW hl
        have hcomm : conjAct W ⁅lN, g⁆ = 1 := by
          rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
          exact (mem_centralizer_iff.mp hg _ hlK)
        exact (convI_eq_one_iff hWe ⁅lN, g⁆).1 hcomm
      exact hLC (mem_subgroupOf.mp hl)
    exact (convI_eq_one_iff hWe ⟨l, hlN⟩).2 hlC

end CFSG.Quasithin.AutOn
