module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Nine24XDefs
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09R98W
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09R912A5
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214Rk
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214c
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Nine24XBasic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtySixAlt3
public import CFSG.GroupTheory.PCoreSurjective

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem opp_eq_of_le_normalizer (hB0 : KFactL2EvenThreeElts) {X Y : Subgroup G} {n : ℕ}
    (hperf : ⁅X, X⁆ = X) (hL2 : IsL2 (Bar2 X) (2 * n)) (hXY : X ≤ Y)
    (hYnorm : Y ≤ normalizer (X : Set G)) (h3 : CFSG.Open.pRank 3 (Opp 3 Y) ≤ 1) :
    Opp 3 Y = X ∧ pCoreOf 2 X ≤ pCoreOf 2 Y := by
  let X₁ : Subgroup G := Opp 3 Y
  have hX₁Y : X₁ ≤ Y := F09.opp_le_self 3 Y
  have hXopp : Opp 3 X = X := opp3_eq_self_of_isL2 hperf hL2
  have hOppXle : Opp 3 X ≤ Opp 3 Y :=
    Subgroup.closure_mono fun x hx => ⟨hXY hx.1, hx.2⟩
  have hXX₁ : X ≤ X₁ := hXopp.symm.le.trans hOppXle
  have hprankX₁ : CFSG.Open.pRank 3 X₁ ≤ 1 := h3
  let X' : Subgroup ↥X₁ := X.subgroupOf X₁
  have hX'norm : X'.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXX₁).mpr (hX₁Y.trans hYnorm)
  have hperf' : ⁅X', X'⁆ = X' := by
    refine (Subgroup.map_subtype_inj (H := X₁)).mp ?_
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hXX₁, hperf]
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
  exact ⟨hOppEq, hXYp⟩

theorem le_normalizer_of_pRank_L9_le_one {M L K : Subgroup G} {n : ℕ} (hL : L ∈ calC M)
    (hL2 : IsL2 (Bar2 L) n) (hKM : K ≤ M) (h3 : CFSG.Open.pRank 3 (F09.L9 L K) ≤ 1) :
    K ≤ normalizer (L : Set G) := by
  have hLM : L ≤ M := CFSG.Open.IsSubnormal.le hL.1
  have hopp : Opp 3 L = L := opp3_eq_self_of_isL2 hL.2.1 hL2
  haveI : IsSimpleGroup (Bar2 L) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL2
  have hcenter : Subgroup.center (Bar2 L) = ⊥ :=
    UC22.uc22p21k_center_eq_bot hL.2.2
  have h3index : 3 ∣ (Subgroup.center (Bar2 L)).index := by
    rw [hcenter, Subgroup.index_bot]
    exact three_dvd_card_of_isL2 hL2
  intro k hk
  by_contra hkN
  let K' : Subgroup G := L.map (MulAut.conj k).toMonoidHom
  have hK'calC : K' ∈ calC M :=
    uc22p2214_calC_of_mem_conjSetOf hL ⟨k, hKM hk, rfl⟩
  have hne : K' ≠ L := fun hEq =>
    hkN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hEq)
  have hconj : ∃ g : G, K' = uniqueFourConj g L := by
    refine ⟨k⁻¹, ?_⟩
    simp [K', uniqueFourConj]
  have hKL9 : L ≤ F09.L9 L K := hopp.symm.le.trans (F09.opp_le_L9 L K)
  have hK'L9 : K' ≤ F09.L9 L K := by
    have hEq : K' = (Opp 3 L).map (MulAut.conj (k : G)).toMonoidHom := by rw [hopp]
    rw [hEq]
    exact le_iSup (fun h : ↥K => (Opp 3 L).map (MulAut.conj (h : G)).toMonoidHom) ⟨k, hk⟩
  have hL9M : F09.L9 L K ≤ M := by
    change (⨆ h : ↥K, (Opp 3 L).map (MulAut.conj (h : G)).toMonoidHom) ≤ M
    refine iSup_le fun h => ?_
    rw [hopp]
    rintro x ⟨y, hy, rfl⟩
    exact M.mul_mem (M.mul_mem (hKM h.2) (hLM hy)) (M.inv_mem (hKM h.2))
  have h2 := P2214R.two_le_pRank_of_conj hL hK'calC hne hconj hKL9 hK'L9 hL9M
    Nat.prime_three (by norm_num) h3index
  omega

theorem normal_opp_eq_of_mem_calY2_of_calC (hB0 : KFactL2EvenThreeElts) (D : Data G)
    {L Y : Subgroup G} {n : ℕ} (hL : L ∈ calC D.M) (hL2 : IsL2 (Bar2 L) (2 * n))
    (hY : Y ∈ F09.calY2_9 D) (hLY : L ≤ Y) :
    (L.subgroupOf Y).Normal ∧ Opp 3 Y = L ∧ pCoreOf 2 Y ≠ ⊥ := by
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
  have hOppLle : Opp 3 L ≤ Opp 3 Y :=
    Subgroup.closure_mono fun x hx => ⟨hLY hx.1, hx.2⟩
  have hL9le : F09.L9 L (N ⊓ D.M) ≤ F09.L9 Y N := by
    change (⨆ w : ↥(N ⊓ D.M), (Opp 3 L).map (MulAut.conj (w : G)).toMonoidHom) ≤ F09.L9 Y N
    refine iSup_le fun w => ?_
    have hwN : (w : G) ∈ N := (Subgroup.mem_inf.mp w.2).1
    exact (Subgroup.map_mono (f := (MulAut.conj (w : G)).toMonoidHom) hOppLle).trans
      (le_iSup (fun n : ↥N => (Opp 3 Y).map (MulAut.conj (n : G)).toMonoidHom)
        ⟨(w : G), hwN⟩)
  have hprankL9L : CFSG.Open.pRank 3 (F09.L9 L (N ⊓ D.M)) ≤ 1 :=
    (CFSG.SectionRank.pRank_mono (by norm_num) hL9le).trans hprankL9
  have hNMnorm : N ⊓ D.M ≤ normalizer (L : Set G) :=
    le_normalizer_of_pRank_L9_le_one hL hL2 inf_le_right hprankL9L
  have hYnorm : Y ≤ normalizer (L : Set G) :=
    (le_inf hYN hY.1.1).trans hNMnorm
  have hLnormY : (L.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).mpr hYnorm
  have h3Y : CFSG.Open.pRank 3 (Opp 3 Y) ≤ 1 :=
    (CFSG.SectionRank.pRank_mono (by norm_num) (F09.opp_le_L9 Y N)).trans hprankL9
  obtain ⟨hOppEq, hpc⟩ := opp_eq_of_le_normalizer hB0 hL.2.1 hL2 hLY hYnorm h3Y
  have hLbot : pCoreOf 2 L ≠ ⊥ :=
    pCoreOf_ne_bot_of_mem_calC D.standing.charTwo D.maxLocal.1 hL
  exact ⟨hLnormY, hOppEq, fun hbot => hLbot (bot_unique (hbot ▸ hpc))⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
