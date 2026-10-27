module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSevenB
import CFSG.LocalAnalysis.WeakClosure81.NineThirteen
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveFourteenB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open CFSG.CGT.Timmesfeld75 (IsTI)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace TwelveSixteen

theorem le_rankThreeGamma {p : ℕ} (hp : p.Prime) {X : Subgroup G} (hXp : IsPGroup p X) :
    X ≤ rankThreeGamma 1 p X := by
  by_cases hX : X = ⊥
  · rw [hX]
    exact bot_le
  haveI : Fact p.Prime := ⟨hp⟩
  have hdvd : p ∣ Nat.card X := by
    rcases hXp.card_eq_or_dvd with h1 | h
    · exact absurd (Subgroup.card_eq_one.1 h1) hX
    · exact h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) p hdvd
  have hx' : orderOf (x : G) = p := by rw [Subgroup.orderOf_coe]; exact hx
  have hxp : (x : G) ^ p = 1 := by rw [← hx']; exact pow_orderOf_eq_one _
  have hE : IsElemAbelian p (zpowers (x : G)) := by
    refine ⟨inferInstance, fun y hy => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]
  have hcard : Nat.card (zpowers (x : G)) = p ^ 1 := by
    rw [Nat.card_zpowers, pow_one, hx']
  have h1 : 1 ≤ CFSG.Open.pRank p X :=
    CFSG.SectionRank.le_pRank hp.one_lt ((Subgroup.zpowers_le).2 x.2) hE hcard
  exact Subgroup.le_normalizer.trans
    (CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore le_rfl h1)

theorem mem_calP (D : Data G) {W : Subgroup G} (hW : InCalV D.M W) (hTI : IsTI W) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {X : Subgroup G} (hXp : IsPGroup p X)
    (hXM : ∀ g : G, g ∉ D.M → W ≤ conjSubgroup D.M g → X ⊓ conjSubgroup D.M g = ⊥)
    (hΓ : rankThreeGamma 1 p X ≤ D.M) : X ∈ calP W := by
  have hN : normalizer (W : Set G) = D.M := normalizer_eq_of_inCalV D hW
  refine ⟨p, hp, hp2, hXp, hN ▸ (le_rankThreeGamma hp hXp).trans hΓ, hN ▸ hΓ,
    fun g hg hWg => ?_⟩
  rw [hN] at hg hWg ⊢
  exact hXM g hg (TwelveSeven.le_conjSubgroup_of_isTI D hW hTI hg hWg)

theorem inf_centralizer_cClos_eq_bot (D : Data G) {W : Subgroup G} (hW : InCalV D.M W)
    (hTI : IsTI W) (h8 : 8 ≤ Nat.card W) {X : Subgroup G}
    (hXM : ∀ g : G, g ∉ D.M → W ≤ conjSubgroup D.M g → X ⊓ conjSubgroup D.M g = ⊥)
    (h1 : ¬ normalizer (E3.wClos W 1 D.T : Set G) ≤ D.M) :
    X ⊓ centralizer (E3.cClos W 1 D.T : Set G) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : normalizer (W : Set G) = D.M := normalizer_eq_of_inCalV D hW
  have hsyl : IsSylowIn 2 D.T (normalizer (W : Set G)) := by
    rw [hN]
    exact TwelveShort.isSylowIn_of_le D D.sylowM.le
  have hWnorm : (W.subgroupOf (normalizer (W : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).2 le_rfl
  have hWp : IsPGroup 2 W := B2F.isPGroup_of_isElemAbelian hW.2.2.2
  have hWT : W ≤ D.T := hsyl.le_of_normal Subgroup.le_normalizer hWnorm hWp
  have hrk := TwelveSeven.two_lt_rk_of_card hW.2.2.2 h8
  have hWW : W ≤ E3.wClos W 1 D.T := E3.le_wClos_of_mQuot_le_self hW.2.2.2 hWT le_rfl
    (k := 1) (by rw [E3.mQuot_self]; norm_num) (by omega)
  obtain ⟨g, hgN, hgM⟩ := SetLike.not_le_iff_exists.1 h1
  have hW1g : conjSubgroup (E3.wClos W 1 D.T) g = E3.wClos W 1 D.T :=
    conjSubgroup_eq_iff_mem_normalizer.2 hgN
  have hW1T : E3.wClos W 1 D.T ≤ D.T := E3.wClos_le 1 D.T
  have hW1two : IsPGroup 2 (E3.wClos W 1 D.T) := hsyl.isPGroup.to_le hW1T
  have hW1N : E3.wClos W 1 D.T ≤ normalizer (W : Set G) := hW1T.trans hsyl.le
  haveI : Group.IsNilpotent (E3.wClos W 1 D.T) := hW1two.isNilpotent
  haveI : (W.subgroupOf (E3.wClos W 1 D.T)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hW1N
  have hne : W.subgroupOf (E3.wClos W 1 D.T) ≠ ⊥ := by
    intro hb
    apply hW.1
    rw [← Subgroup.map_subgroupOf_eq_of_le hWW, hb, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hyW : (y : G) ∈ W := hy.1
  have hyC : (y : G) ∈ centralizer (E3.wClos W 1 D.T : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩)
  have hy1' : (y : G) ≠ 1 := fun h => hy1 (Subtype.ext (Subtype.ext h))
  set b : G := g⁻¹ * (y : G) * g with hbdef
  have hbW : b ∈ conjSubgroup W g := by
    rw [mem_conjSubgroup_iff, hbdef, show g * (g⁻¹ * (y : G) * g) * g⁻¹ = y by group]
    exact hyW
  have hb1 : b ≠ 1 := by
    intro hb
    apply hy1'
    have h1' : (y : G) = g * b * g⁻¹ := by rw [hbdef]; group
    rw [hb] at h1'
    simpa using h1'
  have hbC : b ∈ centralizer (E3.wClos W 1 D.T : Set G) := by
    have h1' : b ∈ conjSubgroup (centralizer (E3.wClos W 1 D.T : Set G)) g := by
      rw [mem_conjSubgroup_iff, hbdef, show g * (g⁻¹ * (y : G) * g) * g⁻¹ = y by group]
      exact hyC
    rwa [E3.conjSubgroup_centralizer, hW1g] at h1'
  have hWgW1 : conjSubgroup W g ≤ E3.wClos W 1 D.T := by
    have h' := E3.conjSubgroup_mono_left g hWW
    rwa [hW1g] at h'
  have hbC1 : b ∈ E3.cClos W 1 D.T := ⟨hW1T (hWgW1 hbW), hbC⟩
  have hCb : centralizer ({b} : Set G) ≤ conjSubgroup D.M g := by
    rw [← hN, E3.conjSubgroup_normalizer]
    exact centralizer_le_normalizer_conj hTI g hbW hb1
  have hWb : W ≤ conjSubgroup D.M g := by
    refine le_trans ?_ hCb
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact ((Subgroup.mem_centralizer_iff.1 hbC) w (hWW hw)).symm
  have hbot := hXM g hgM hWb
  rw [eq_bot_iff]
  intro x hx
  have hxb : x ∈ X ⊓ conjSubgroup D.M g := by
    refine ⟨hx.1, hCb ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact (Subgroup.mem_centralizer_iff.1 hx.2) b hbC1
  rwa [hbot] at hxb

end TwelveSixteen

theorem twelve_sixteen (hTim : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hcat : ¬ CFSG.Blueprint.Catalog G) (D : Data G) (h66 : UC6.R6_6 D) (h88 : W3Thm88 G)
    {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) (h8 : 8 ≤ Nat.card V₀) (h93 : Thm93 V₀ D.T)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Subgroup G} (hXp : IsPGroup p X)
    (hXM : ∀ g : G, g ∉ D.M → V₀ ≤ conjSubgroup D.M g → X ⊓ conjSubgroup D.M g = ⊥)
    (hΓ : rankThreeGamma 1 p X ≤ D.M) (hXT : (X : Set G) * D.T = D.T * X) :
    X ⊓ centralizer (E3.cClos V₀ 1 D.T : Set G) = ⊥ ∧
      X ⊔ D.T ≤ normalizer (E3.wClos V₀ 0 D.T : Set G) := by
  have hV₀ : V₀ ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at h8
    omega
  rcases h.1 with ⟨-, h0⟩ | ⟨h0, hcu, -⟩
  · exact absurd h0 hV₀
  have hW : InCalV D.M V₀ := h0.1
  have hTI : IsTI V₀ := h0.2.2.2.1
  have hz : ∀ z ∈ D.T, (∀ t ∈ D.T, z * t = t * z) → z ≠ 1 →
      centralizer ({z} : Set G) ≤ D.M := fun z hz hzc hz1 => (hcu z hz hzc hz1).1
  have h1 := twelve_seven_three_one hTim hcat D h66 h88 h.2 hW hTI h8 hz
  have hN : normalizer (V₀ : Set G) = D.M := normalizer_eq_of_inCalV D hW
  have h9 : Hyp9 V₀ D.T :=
    { hyp7 := TwelveSeven.hyp7_of_inCalV D hW hTI h8
      sylow := by rw [hN]; exact TwelveShort.isSylowIn_of_le D D.sylowM.le
      ne := (TwelveFourteen.wClos_zero_ne_self hTim hcat D hW hTI (by omega)).symm
      rk_gt := TwelveSeven.two_lt_rk_of_card hW.2.2.2 h8 }
  refine ⟨TwelveSixteen.inf_centralizer_cClos_eq_bot D hW hTI h8 hXM h1, ?_⟩
  rcases nine_thirteen h9 h93 (TwelveSixteen.mem_calP D hW hTI hp hp2 hXp hXM hΓ) hXT with
    h2 | h2
  · exact absurd (h2.trans hN.le) h1
  · exact h2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
