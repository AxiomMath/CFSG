module

public import CFSG.Quasithin.Background.C31Steps
public import CFSG.Quasithin.Background.C48SporSetup
public import CFSG.Quasithin.Background.C41PfKG
public import CFSG.LocalAnalysis.ComponentClassification.AS81QbarAbstract
public import CFSG.GH74.SmallRanks
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47Rank3
import CFSG.RankThree.SubgroupLists.TwoRankPSUThree
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.C31NL

open CFSG.Open hiding StatedSL StatedSp StatedSU StatedProj StatedScalars
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank C48Spor

theorem commutator_eq_bot_of_card_le_four {Γ : Type} [Group Γ] [Finite Γ] {V M₀ : Subgroup Γ}
    (hperf : ⁅M₀, M₀⁆ = M₀) (hMN : M₀ ≤ Subgroup.normalizer (V : Set Γ)) (hV : Nat.card V ≤ 4) :
    ⁅V, M₀⁆ = ⊥ := by
  set ψ : ↥M₀ →* MulAut ↥V := (Subgroup.normalizerMonoidHom V).comp (Subgroup.inclusion hMN)
    with hψ
  have hsol : Group.IsSolvable (MulAut ↥V) :=
    CFSG.ComponentClassification.AS81.Qbar.isSolvable_mulAut_of_card_le_four hV
  have hrange : ψ.range = ⊥ := by
    refine C41Pf.eq_bot_of_perfect_of_isSolvable ?_ ?_
    · rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator]
      congr 1
      apply Subgroup.map_injective M₀.subtype_injective
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hperf]
    · exact Group.isSolvable_of_isSolvable_injective (f := ψ.range.subtype)
        ψ.range.subtype_injective
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro v hv m hm
  have h1 : ψ ⟨m, hm⟩ = 1 := by
    have : ψ ⟨m, hm⟩ ∈ ψ.range := ⟨_, rfl⟩
    rw [hrange] at this
    exact Subgroup.mem_bot.mp this
  have h2 := congrArg (fun f : MulAut ↥V => ((f ⟨v, hv⟩ : ↥V) : Γ)) h1
  simp only [hψ, MonoidHom.comp_apply, MulAut.one_apply] at h2
  change m * v * m⁻¹ = v at h2
  rw [Subgroup.mem_bot, commutatorElement_def]
  calc v * m * v⁻¹ * m⁻¹ = v * (m * v * m⁻¹)⁻¹ := by group
    _ = 1 := by rw [h2, mul_inv_cancel]

theorem twoRank_psu3_le_two {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = (p ^ f) ^ 2) :
    CFSG.Assembly.twoRank (StatedProj (StatedSU 3 (p ^ f) K)) ≤ 2 :=
  CFSG.RankThree.SubgroupLists.twoRank_statedProj_statedSU_three_le_two hp hp2 hK

theorem twoRank_le_two {X : Type} [Group X] [Finite X]
    (hX : IsAlt 7 X ∨ ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
      ((∃ f : ℕ, (f = 1 ∨ f = 2) ∧ IsPSL 2 p f X) ∨ IsPSL 3 p 1 X ∨ IsPSU 3 p 1 X)) :
    CFSG.Open.twoRank X ≤ 2 := by
  rcases hX with h7 | ⟨p, hp, hp2, ⟨f, -, h⟩ | h | h⟩
  · obtain ⟨e⟩ := h7
    exact CFSG.GH74.twoRank_le_two_of_alternating_seven e
  · exact CFSG.GH74.SmallRanks.twoRank_le_two_of_statedClassicalModel_PSL_two_odd hp hp2 h
  · exact CFSG.GH74.GLS.Stage2.Signalizer.Odd87.pRank_two_le_two_of_PSL3 hp hp2
      (Or.inl ⟨by decide, h⟩)
  · obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
    have h2 : CFSG.Open.twoRank (StatedProj (StatedSU 3 (p ^ 1) K)) ≤ 2 :=
      twoRank_psu3_le_two hp hp2 hK
    rw [CFSG.GH74.twoRank_eq_of_mulEquiv e]
    exact h2

variable {G : Type} [Group G] [Finite G]

theorem c31NonLieStep_holds : C31NonLieStep G := by
  intro H R M L V K h hK h31 htype
  have hVne := img_V_ne_bot h h31
  have hcomm := img_V_comm h h31
  have hperf := img_M0_perfect h h31
  have hMN : img (sporN H K) (conjClosure L M) ≤
      Subgroup.normalizer (img (sporN H K) V : Set (↥(sporX H K) ⧸ sporN H K)) :=
    img_le_normalizer (M0_le_normalizer_V h)
  have hE := isElemAbelian_img (N := sporN H K) h.V_elem
  have hE2 : IsPGroup 2 ↥(img (sporN H K) V) := fun x =>
    ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨k, hk⟩ := hE2.exists_card_eq
  have hk3 : 3 ≤ k := by
    by_contra hlt
    have h4 : Nat.card ↥(img (sporN H K) V) ≤ 4 := by
      rw [hk]
      exact (Nat.pow_le_pow_right (by norm_num) (by omega : k ≤ 2)).trans (by norm_num)
    have := commutator_eq_bot_of_card_le_four hperf hMN h4
    rw [hcomm] at this
    exact hVne this
  have hVK : img (sporN H K) V ≤ img (sporN H K) K := img_mono (h.V_le.trans h31.1)
  have hrank : k ≤ CFSG.Open.twoRank ↥(img (sporN H K) K) := by
    have hEsub : IsElemAbelian 2 ((img (sporN H K) V).subgroupOf (img (sporN H K) K)) := by
      refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
      · have := congrArg Subtype.val (hE.1.is_comm.comm (⟨((a : ↥(img (sporN H K) K)) : _), a.2⟩ :
          ↥(img (sporN H K) V)) ⟨((b : ↥(img (sporN H K) K)) : _), b.2⟩)
        simpa using this
      · simpa using hE.2 _ hx
    refine CFSG.SectionRank.le_pRank (by norm_num) le_top hEsub ?_
    rw [← hk]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVK).toEquiv
  have hK2 : CFSG.Open.twoRank ↥(img (sporN H K) K) ≤ 2 := by
    rw [CFSG.GH74.twoRank_eq_of_mulEquiv (kStarEquiv (K_le_sporX hK.1)).symm]
    exact twoRank_le_two htype
  omega

end CFSG.Quasithin.C31NL
