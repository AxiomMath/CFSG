module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Nine24XDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs2
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Nine24XNormal
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC6CommAux1
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ShapeDisjoint
import CFSG.Adapters.LieModelSimple
import CFSG.GroupTheory.PCoreSurjective
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R912A5
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R98W
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank
public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem normal_opp_eq_of_mem_calY2 (hB0 : KFactL2EvenThreeElts) (D : Data G)
    {L P X Y : Subgroup G} {n : ℕ} (hL : L ∈ calC D.M) (hLN : D.M ≤ normalizer (L : Set G))
    (hn : 1 < n) (hU : IsU4 (Bar2 L) n) (hP : ParabolicOf L P) (hX : X = F07.DerInf P)
    (hL2 : IsL2 (Bar2 X) (2 * n)) (hXp : pCoreOf 2 X ≠ ⊥)
    (hY : Y ∈ F09.calY2_9 D) (hXY : X ≤ Y) :
    (X.subgroupOf Y).Normal ∧ Opp 3 Y = X ∧ pCoreOf 2 Y ≠ ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨N, hNmem, hNM⟩ : ∃ N ∈ calMOf Y, N ≠ D.M := by
    by_contra h
    apply hY.2.1
    ext N
    simp only [Set.mem_singleton_iff]
    constructor
    · intro hN
      by_contra hNne
      exact h ⟨N, hN, hNne⟩
    · intro hND
      rw [hND]
      exact ⟨D.maxLocal, hY.1.1⟩
  have hNH9 : N ∈ F09.calH9 D Y := by
    rcases hY.2.2.1 hNmem with h | h
    · exact h
    · exact absurd (Set.mem_singleton_iff.mp h) hNM
  have hYN : Y ≤ N := hNH9.1
  have hprankL9 : CFSG.Open.pRank 3 (F09.L9 Y N) ≤ 1 := hNH9.2.2.le
  have hperfx : ⁅X, X⁆ = X := by
    rw [hX]
    change ⁅(CFSG.perfectResidual ↥P).map P.subtype,
        (CFSG.perfectResidual ↥P).map P.subtype⁆ = (CFSG.perfectResidual ↥P).map P.subtype
    exact Subgroup.isPerfect_iff.mp
      (CFSG.SignalizerFunctorTheorem.Nonsolvable.isPerfect_perfectResidual_map P)
  have hsimpleX : IsSimpleGroup (Bar2 X) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL2
  have h3X : 3 ∣ Nat.card (Bar2 X) := three_dvd_card_of_isL2 hL2
  have hXopp : Opp 3 X = X := s16c6_opp3_eq_self hperfx hsimpleX h3X
  have hOppXle : Opp 3 X ≤ Opp 3 Y :=
    Subgroup.closure_mono fun x hx => ⟨hXY hx.1, hx.2⟩
  have hL9le : F09.L9 X (N ⊓ D.M) ≤ F09.L9 Y N := by
    change (⨆ w : ↥(N ⊓ D.M), (Opp 3 X).map (MulAut.conj (w : G)).toMonoidHom) ≤ F09.L9 Y N
    refine iSup_le fun w => ?_
    have hwN : (w : G) ∈ N := (Subgroup.mem_inf.mp w.2).1
    exact (Subgroup.map_mono (f := (MulAut.conj (w : G)).toMonoidHom) hOppXle).trans
      (le_iSup (fun n : ↥N => (Opp 3 Y).map (MulAut.conj (n : G)).toMonoidHom)
        ⟨(w : G), hwN⟩)
  have hprankL9X : CFSG.Open.pRank 3 (F09.L9 X (N ⊓ D.M)) ≤ 1 :=
    (CFSG.SectionRank.pRank_mono (by norm_num) hL9le).trans hprankL9
  have hXN : X ≤ N := hXY.trans hYN
  have hXH : X ≤ N ⊓ D.M := le_inf hXN (hXY.trans hY.1.1)
  have hnormal :=
    normal_subgroupOf_inf_of_pRank_le_one (H := N) D hL hLN hn hU hP hX hL2 hXN hprankL9X
  have hNnorm : N ⊓ D.M ≤ Subgroup.normalizer (X : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXH).mp hnormal
  have hYnorm : Y ≤ Subgroup.normalizer (X : Set G) :=
    (le_inf hYN hY.1.1).trans hNnorm
  have hXnormY : (X.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXY).mpr hYnorm
  let X₁ : Subgroup G := Opp 3 Y
  have hX₁Y : X₁ ≤ Y := F09.opp_le_self 3 Y
  have hXX₁ : X ≤ X₁ := hXopp.symm.le.trans hOppXle
  have hprankX₁ : CFSG.Open.pRank 3 X₁ ≤ 1 :=
    (CFSG.SectionRank.pRank_mono (by norm_num) (F09.opp_le_L9 Y N)).trans hprankL9
  let X' : Subgroup ↥X₁ := X.subgroupOf X₁
  have hX'norm : X'.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXX₁).mpr (hX₁Y.trans hYnorm)
  have hperf' : ⁅X', X'⁆ = X' := by
    refine (Subgroup.map_subtype_inj (H := X₁)).mp ?_
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hXX₁, hperfx]
  have hL2' : IsL2 (Bar2 X') (2 * n) := by
    have hker : IsPGroup 2 (Subgroup.subgroupOfEquivOfLe hXX₁).symm.toMonoidHom.ker := by
      have hb : (Subgroup.subgroupOfEquivOfLe hXX₁).symm.toMonoidHom.ker = ⊥ :=
        MonoidHom.ker_eq_bot _ (Subgroup.subgroupOfEquivOfLe hXX₁).symm.injective
      rw [hb]
      exact IsPGroup.of_bot
    obtain ⟨eBar⟩ := CFSG.nonempty_quotient_pCore_equiv_of_surjective_of_isPGroup_ker
      (p := 2) (Subgroup.subgroupOfEquivOfLe hXX₁).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hXX₁).symm.surjective hker
    exact CFSG.Blueprint.LieModel.of_mulEquiv eBar hL2
  have hprankTop : CFSG.Open.pRank 3 (⊤ : Subgroup ↥X₁) ≤ 1 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup X₁]
    exact hprankX₁
  have hthree : ∀ z : ↥X₁, IsPGroup 3 (Subgroup.zpowers z) → z ∈ X' :=
    hB0 ↥X₁ X' n hX'norm hperf' hL2' hprankTop
  have hX₁X : X₁ ≤ X := by
    intro y hy
    change y ∈ Subgroup.closure {x : G | x ∈ Y ∧ ∃ k : ℕ, orderOf x = 3 ^ k} at hy
    have hsub : {x : G | x ∈ Y ∧ ∃ k : ℕ, orderOf x = 3 ^ k} ⊆ X := by
      rintro x ⟨hxY, k, hk⟩
      have hxX₁ : x ∈ X₁ := Subgroup.subset_closure ⟨hxY, k, hk⟩
      have hz3 : IsPGroup 3 (Subgroup.zpowers (⟨x, hxX₁⟩ : ↥X₁)) :=
        IsPGroup.of_card (n := k)
          (by rw [Nat.card_zpowers, ← Subgroup.orderOf_coe, hk])
      exact Subgroup.mem_subgroupOf.mp (hthree ⟨x, hxX₁⟩ hz3)
    exact (Subgroup.closure_le X).mpr hsub hy
  have hOppEq : Opp 3 Y = X := le_antisymm hX₁X hXX₁
  have hXYp : pCoreOf 2 X ≤ pCoreOf 2 Y :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 X).trans hXY)
      (hYnorm.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)
  have hYp : pCoreOf 2 Y ≠ ⊥ := by
    intro hbot
    exact hXp (bot_unique (hbot ▸ hXYp))
  exact ⟨hXnormY, hOppEq, hYp⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
