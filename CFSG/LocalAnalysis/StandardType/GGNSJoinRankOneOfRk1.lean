module

public import CFSG.LocalAnalysis.StandardType.GGNSJoinRealized
public import CFSG.LocalAnalysis.StandardType.GGMemberRowsDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanPrimDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQSplit
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneCard
import CFSG.LocalAnalysis.StandardType.GGSecFiveNbrGenKNOfInputs
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.Adapters.SpecialLinearPerfect
import CFSG.Quasithin.Vol2.Ch10SecHeLMain
import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
import CFSG.Quasithin.Background.A3Structure312Facts
import CFSG.Quasithin.Background.A3Structure36A
import CFSG.Quasithin.Background.A3Structure36BBase
import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
import CFSG.Quasithin.Background.B1More13A
import CFSG.Quasithin.Background.B1More13Defs
import CFSG.Quasithin.Background.B1MoreEleven
import CFSG.Quasithin.Background.B5CompA
import CFSG.Quasithin.Background.B5CompB
import CFSG.Quasithin.Background.B5FinOut
import CFSG.Quasithin.Background.B6
import CFSG.Quasithin.Background.B6Example
import CFSG.Quasithin.Background.E2Hyp
import CFSG.Quasithin.Background.E2SolvTwo
import CFSG.Quasithin.Background.F9FiveStruct
import CFSG.Quasithin.Background.F9G2
import CFSG.Quasithin.Background.F9Geometry
import CFSG.Quasithin.Background.InternalSecAutOn
import CFSG.Quasithin.Background.InternalSecB4
import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
import CFSG.Quasithin.EmptyFaithful.S142Statements
import CFSG.Quasithin.H13.A5S1326
import CFSG.Quasithin.H13.A5Top
import CFSG.Quasithin.Vol2.Ch11StatementsB
import CFSG.Quasithin.Vol2.Ch11StatementsC
import CFSG.Quasithin.Vol2.Ch12Sec2Statements
import CFSG.Quasithin.Vol2.Ch1Faithful
import CFSG.Quasithin.Vol2.Ch3Sec3StatementsB
import Certificates.Certificate8026Base

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal

open scoped MatrixGroups

private theorem rk1_card_eq {G : Type} [Group G] {F : Type} [Field F] [Finite F]
    {θ : SL(2, F) →* G} (hθinj : Function.Injective θ) {S : Subgroup G} (hθrange : θ.range = S) :
    Nat.card ↥S = Nat.card F * (Nat.card F ^ 2 - 1) := by
  rw [← hθrange, ← ggSL2_card F]
  exact Nat.card_congr (MonoidHom.ofInjective hθinj).toEquiv.symm

private theorem rk1_four_le_card {F : Type} [Field F] [Finite F] [CharP F 2]
    (h6 : Nat.card F * (Nat.card F ^ 2 - 1) ≠ 6) : 4 ≤ Nat.card F := by
  haveI := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  rw [Nat.card_eq_fintype_card, hn] at h6 ⊢
  rcases Nat.lt_or_ge (n : ℕ) 2 with h | h
  · have hn1 : (n : ℕ) = 1 := by have := n.pos; omega
    rw [hn1] at h6
    norm_num at h6
  · calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n : ℕ) := Nat.pow_le_pow_right (by norm_num) h

theorem ggRankOneIn_sl2_of_concl {G : Type} [Group G] [Finite G] {p : ℕ} {Bs X : Subgroup G}
    {r : MulAut ↥Bs} (hRkX : GGRk1Concl p Bs X r) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (θ : SL(2, F) →* G), CharP F 2 ∧
      Function.Injective θ ∧ θ.range = ggRankOneIn X Bs r ∧
      (GGSplitLie p X → p ∣ Nat.card F - 1) ∧ (¬ GGSplitLie p X → p ∣ Nat.card F + 1) ∧
      ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
        GGHasLabel lab (↥X ⧸ Subgroup.center ↥X) → 2 ^ lab.n ≤ Nat.card F := by
  obtain ⟨F, hF, hFfin, θ, hchar, hθinj, hθrange, -, hsplit, hnsplit, hlab⟩ := hRkX
  exact ⟨F, hF, hFfin, θ, hchar, hθinj, hθrange, hsplit, hnsplit, hlab⟩

theorem ggRankOneIn_sl2_of_rk1 (hRk1 : GGSecFiveRk1PhanInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hns : ¬ GGSplitLie p L) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    {X : Subgroup G} (hX : X = L ∨ X ∈ 𝒦) {r : MulAut ↥Bs} (hrA : r ∈ ggAutomizer X Bs)
    (hr : GGIsReflection p r) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (θ : SL(2, F) →* G), CharP F 2 ∧
      Function.Injective θ ∧ θ.range = ggRankOneIn X Bs r ∧
      (GGSplitLie p X → p ∣ Nat.card F - 1) ∧ (¬ GGSplitLie p X → p ∣ Nat.card F + 1) ∧
      ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
        GGHasLabel lab (↥X ⧸ Subgroup.center ↥X) → 2 ^ lab.n ≤ Nat.card F := by
  have hrC : r ∈ ggCoxRefl M e :=
    ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres h3
      (ggAutomizer_le_ggAutomizerJoin hX hrA) hr
  exact ggRankOneIn_sl2_of_concl (hRk1 G p B Bs x L D J 𝒦 hcfg hns ι M e hpres h3 X hX r hrA hrC)

theorem ggRankOneIn_isQuasisimple_of_concl {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs X : Subgroup G} {r : MulAut ↥Bs} (hRkX : GGRk1Concl p Bs X r)
    (h6 : Nat.card ↥(ggRankOneIn X Bs r) ≠ 6) :
    CFSG.Assembly.IsQuasisimple ↥(ggRankOneIn X Bs r) ∧ p ∣ Nat.card ↥(ggRankOneIn X Bs r) := by
  obtain ⟨F, _, _, θ, hchar, hθinj, hθrange, hsplit, hnsplit, -⟩ := ggRankOneIn_sl2_of_concl hRkX
  haveI := hchar
  have hcard := rk1_card_eq hθinj hθrange
  have h4 : 4 ≤ Nat.card F := rk1_four_le_card (hcard ▸ h6)
  have hSL : CFSG.Assembly.IsQuasisimple SL(2, F) :=
    ⟨(CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card _ h4).commutator_eq_top,
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4⟩
  refine ⟨?_, ?_⟩
  · rw [← hθrange]
    exact CFSG.Assembly.IsQuasisimple.of_mulEquiv (MonoidHom.ofInjective hθinj).symm hSL
  · rw [hcard]
    have h1 : Nat.card F ^ 2 - 1 = (Nat.card F + 1) * (Nat.card F - 1) := by
      rw [sq]
      exact mul_self_tsub_one _
    refine dvd_mul_of_dvd_right ?_ _
    rw [h1]
    by_cases hsp : GGSplitLie p X
    · exact dvd_mul_of_dvd_right (hsplit hsp) _
    · exact dvd_mul_of_dvd_left (hnsplit hsp) _

theorem ggRankOneIn_isQuasisimple_of_rk1 (hRk1 : GGSecFiveRk1PhanInput) {G : Type} [Group G]
    [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hns : ¬ GGSplitLie p L) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {X : Subgroup G} (hX : X = L ∨ X ∈ 𝒦)
    {r : MulAut ↥Bs} (hrA : r ∈ ggAutomizer X Bs) (hr : GGIsReflection p r)
    (h6 : Nat.card ↥(ggRankOneIn X Bs r) ≠ 6) :
    CFSG.Assembly.IsQuasisimple ↥(ggRankOneIn X Bs r) ∧ p ∣ Nat.card ↥(ggRankOneIn X Bs r) := by
  have hrC : r ∈ ggCoxRefl M e :=
    ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres h3
      (ggAutomizer_le_ggAutomizerJoin hX hrA) hr
  exact ggRankOneIn_isQuasisimple_of_concl
    (hRk1 G p B Bs x L D J 𝒦 hcfg hns ι M e hpres h3 X hX r hrA hrC) h6

theorem ggRankOneIn_minimal_of_concl {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs X : Subgroup G} {r : MulAut ↥Bs} (hRkX : GGRk1Concl p Bs X r)
    (h6 : Nat.card ↥(ggRankOneIn X Bs r) ≠ 6) :
    ∀ N : Subgroup G, N ≤ ggRankOneIn X Bs r → N ≠ ⊥ →
      (∀ a ∈ ggRankOneIn X Bs r, ∀ b ∈ N, a * b * a⁻¹ ∈ N) → ggRankOneIn X Bs r ≤ N := by
  obtain ⟨F, _, _, θ, hchar, hθinj, hθrange, -, -, -⟩ := ggRankOneIn_sl2_of_concl hRkX
  haveI := hchar
  have h4 : 4 ≤ Nat.card F := rk1_four_le_card (rk1_card_eq hθinj hθrange ▸ h6)
  haveI : IsSimpleGroup SL(2, F) := CFSG.Quasithin.Vol2.Ch10.HeL.sl2_isSimpleGroup h4
  intro N hN hN1 hnorm
  rw [← hθrange] at hN hnorm ⊢
  exact s2jn_range_simple θ hθinj N hN hN1 hnorm

theorem ggRankOneIn_minimal_of_rk1 (hRk1 : GGSecFiveRk1PhanInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hns : ¬ GGSplitLie p L) {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    {X : Subgroup G} (hX : X = L ∨ X ∈ 𝒦) {r : MulAut ↥Bs} (hrA : r ∈ ggAutomizer X Bs)
    (hr : GGIsReflection p r) (h6 : Nat.card ↥(ggRankOneIn X Bs r) ≠ 6) :
    ∀ N : Subgroup G, N ≤ ggRankOneIn X Bs r → N ≠ ⊥ →
      (∀ a ∈ ggRankOneIn X Bs r, ∀ b ∈ N, a * b * a⁻¹ ∈ N) → ggRankOneIn X Bs r ≤ N := by
  have hrC : r ∈ ggCoxRefl M e :=
    ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres h3
      (ggAutomizer_le_ggAutomizerJoin hX hrA) hr
  exact ggRankOneIn_minimal_of_concl
    (hRk1 G p B Bs x L D J 𝒦 hcfg hns ι M e hpres h3 X hX r hrA hrC) h6

namespace NSJoin

theorem nsRankOneL_of_rk1 {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (hT3 : ∀ {ι : Type} {M : CoxeterMatrix ι}, T M → ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hRk1 : GGSecFiveRk1PhanInput) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hns : ¬ GGSplitLie p L)
    (hguard : NSJoinGuardOf T p L Bs 𝒦) {r : MulAut ↥Bs} (hrA : r ∈ ggAutomizer L Bs)
    (hr : GGIsReflection p r) :
    CFSG.Assembly.IsQuasisimple ↥(ggRankOneIn L Bs r) ∧ p ∣ Nat.card ↥(ggRankOneIn L Bs r) := by
  obtain ⟨ι, M, e, hpres, hT, hbig⟩ := hguard
  have hrC : r ∈ ggCoxRefl M e :=
    ggCoxRefl_of_cfg hcfg (ggAutomizerJoin_le_top L Bs 𝒦) hpres (hT3 hT)
      (ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) hrA) hr
  exact ggRankOneIn_isQuasisimple_of_rk1 hRk1 hcfg hns hpres (hT3 hT) (Or.inl rfl) hrA hr
    (hbig r hrA hrC)

theorem nsRankOneLInputOf_of_rk1 {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (hT3 : ∀ {ι : Type} {M : CoxeterMatrix ι}, T M → ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    (hRk1 : GGSecFiveRk1PhanInput) : NSRankOneLInputOf T := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg r hrA hr
  obtain ⟨hcfg, hns, hguard⟩ := hcfg
  exact nsRankOneL_of_rk1 hT3 hRk1 hcfg hns hguard hrA hr

theorem nsRankOneLInput_of_rk1 (hRk1 : GGSecFiveRk1PhanInput) : NSRankOneLInput :=
  nsRankOneLInputOf_of_rk1 NSTypeAD.le_three hRk1

end NSJoin

end CFSG.StandardType

end
