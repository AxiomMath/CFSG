module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyThreeOne
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22tc
public import CFSG.LocalAnalysis.WeakClosure81.InFASMulEquiv

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace TwelveEighteen

variable {M V₀ V : Subgroup G}

theorem twelve_eighteen_three_of_no_calO1_AS (hH : Hyp6H M V₀ V) (hV₀ : V₀ ≠ ⊥) {i n k : ℕ}
    (hink : i + n ≤ k) (hkr : (k : ℕ∞) < rMV M V) (hkm : k < mBar M V₀ V hH.elemAbelian)
    (hno : ∀ g : G, ¬ InCalO1 k M V₀ V g) {H S : Subgroup G} (hS : IsSylowIn 2 S H)
    (hF : InFSqAS n H) :
    H ≤ normalizer (E3.wClos V i S : Set G) ∨ ⁅E3.cClos V k S, twoResidual H⁆ = ⊥ := by
  by_cases hHN : H ≤ normalizer (E3.wClos V i S : Set G)
  · exact Or.inl hHN
  right
  set J := H ⊓ centralizer (E3.cClos V k S : Set G) with hJ
  have hSJ : S ≤ normalizer (J : Set G) :=
    A1a.le_normalizer_inf (hS.le.trans Subgroup.le_normalizer)
      (A1a.le_normalizer_centralizer
        (Subgroup.le_normalizer.trans (E3.normalizer_le_normalizer_cClos (V := V) (i := k) S)))
  suffices hres : twoResidual H ≤ J by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hres.trans inf_le_right)
  by_cases hHM : H ≤ J ⊔ S
  · exact CFSG.Quasithin.RonanE111.twoResidual_le_of_le_sup_two hSJ hS.isPGroup hHM
  · exfalso
    obtain ⟨A, hA, K, hK, hKM⟩ := UC22.uc22p22tc_exists_isE_not_le hH.elemAbelian hS hF
      le_sup_right hHM (exists_gammaSet_not_le_pCoreOf hS hHN)
    have hcomm := commutator_twoResidual_cClos_eq_bot_of_no_calO1_gen hH hV₀ hink hkr hkm
      hno hS hA hK
    apply hKM
    have hSK : IsSylowIn 2 (S ⊓ K) K := hK.2.2.1
    rw [← sup_twoResidual_eq hSK]
    refine sup_le (inf_le_left.trans le_sup_right) (le_sup_of_le_left (le_inf ?_ ?_))
    · exact (twoResidual_le K).trans hK.1
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm

end TwelveEighteen

section Certified


theorem TwelveTwentyTwo.twelve_eighteen_three_AS (D : Data G) (hx : DataExt D)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h1114 : R1114 D) (h162 : W3Thm162Ext G)
    (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    (hV₀ : V₀ ≠ ⊥) {i n : ℕ} {X : Subgroup G} (hXM : X ≤ D.M)
    (hXn : D.M ≤ normalizer (X : Set G)) (hX1 : barSub V₀ V h.isElemAbelian X ≠ ⊥)
    (hb : bBar X D.M V₀ V h.isElemAbelian < mBar D.M V₀ V h.isElemAbelian - (i + n))
    (hab : XCond1218 D.M V₀ V h.isElemAbelian (i + n) X) {H S : Subgroup G}
    (hS : IsSylowIn 2 S H) (hF : InFSqAS n H) :
    H ≤ normalizer (E3.wClos V i S : Set G) ∨
      ⁅E3.cClos V (i + n) S, twoResidual H⁆ = ⊥ := by
  have hemp := twelve_eighteen_empty D hx h61 h127 h1114 h162 hTor h1482 h hV₀ hXM hXn hX1 hb
    hab
  have hW := weakClosureSetting_of_hyp125 D hx h61 h127 h1114 h hV₀
  have hH := hW.hyp6H
  have hV := h.isElemAbelian
  have hjm : i + n < mBar D.M V₀ V hH.elemAbelian := by
    have : 0 < mBar D.M V₀ V hV - (i + n) := lt_of_le_of_lt (Nat.zero_le _) hb
    omega
  have hkr : ((i + n : ℕ) : ℕ∞) < rMV D.M V := by
    by_cases hm1 : 1 < mBar D.M V₀ V hV
    · have h1 := h162 D V₀ V hW hx h61 hV₀ hm1
      refine lt_of_lt_of_le ?_ h1
      exact_mod_cast (by omega : i + n < mBar D.M V₀ V hV + mSub V₀)
    · have h0 : i + n = 0 := by omega
      rw [h0]
      exact lt_of_lt_of_le (by norm_num)
        (TwelveEighteen.one_le_rMV (B2F.isPGroup_of_isElemAbelian hV) hH.normalizer_eq)
  have hno : ∀ g : G, ¬ InCalO1 (i + n) D.M V₀ V g := fun g hg => hemp g hg.1
  exact TwelveEighteen.twelve_eighteen_three_of_no_calO1_AS hH hV₀ le_rfl hkr hjm hno hS hF

theorem twelve_twentyTwo_three_AS (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1114 : R1114 D) (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G)
    (h1482 : W3Lem148_2 G) (h126 : R126 D) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V)
    (hV₀ : V₀ ≠ ⊥) {X : Subgroup G} (hXM : X ≤ D.M) (hXn : D.M ≤ normalizer (X : Set G))
    (hX1 : barSub V₀ V h.isElemAbelian X ≠ ⊥) {Δ : Finset (Subgroup G)}
    (hΔ : ∀ H ∈ Δ, D.T ≤ H ∧ H ≤ D.M) (hΔU : UniqueMax D.M (⨆ H ∈ Δ, H))
    (ι : Subgroup G → ℕ) (hι : ∀ H ∈ Δ, InFSqAS (ι H) H)
    (hO2 : ∀ H ∈ Δ, ∀ g : G, g ∉ D.M → ¬ twoResidual H ≤ conjSubgroup D.M g)
    (hab : XCond1218 D.M V₀ V h.isElemAbelian (D.k + Δ.sup ι) X) :
    mBar D.M V₀ V h.isElemAbelian ≤ bBar X D.M V₀ V h.isElemAbelian + (D.k + Δ.sup ι) := by
  by_contra hlt
  have hlt' : bBar X D.M V₀ V h.isElemAbelian + (D.k + Δ.sup ι) <
      mBar D.M V₀ V h.isElemAbelian := not_le.1 hlt
  have hV := h.isElemAbelian
  have hk := TwelveShort.one_le_k D
  have hrk : mBar D.M V₀ V hV ≤ rk ↥V := mBar_le_rk hV h.pairFacts.le
  have hN0 : ¬ normalizer (E3.wClos V 0 D.T : Set G) ≤ D.M :=
    twelve_twentyTwo_two D hx h61 h127 h1114 h162 hTor h1482 h126 h hV₀ hXM hXn hX1 (by omega)
      (TwelveTwentyTwo.xCond1218_anti (by omega) hab)
  have hNi : ¬ normalizer (E3.wClos V (Δ.sup ι) D.T : Set G) ≤ D.M :=
    twelve_twentyTwo_two D hx h61 h127 h1114 h162 hTor h1482 h126 h hV₀ hXM hXn hX1 (by omega)
      (TwelveTwentyTwo.xCond1218_anti (by omega) hab)
  have hVT := TwelveTwentyTwo.le_T_of_hyp125 h
  have hW0 : E3.wClos V 0 D.T ≠ ⊥ := E3.wClos_ne_bot hV hVT (by omega)
  have hW02 : IsPGroup 2 (E3.wClos V 0 D.T) :=
    (TwelveTwentyTwo.isPGroup_T D).to_le (E3.wClos_le 0 D.T)
  obtain ⟨H, hH, hHN⟩ :=
    TwelveTwentyTwo.exists_not_le_normalizer_of_uniqueMax hΔU hW0 hW02 hN0
  have hTH : IsSylowIn 2 D.T H := TwelveShort.isSylowIn_of_le D (hΔ H hH).1
  have hF : InFSqAS (Δ.sup ι) H := inFSqAS_mono (Finset.le_sup hH) (hι H hH)
  have h3 := TwelveTwentyTwo.twelve_eighteen_three_AS D hx h61 h127 h1114 h162 hTor h1482 h
    hV₀ hXM hXn hX1 (i := 0) (n := Δ.sup ι) (by omega)
    (TwelveTwentyTwo.xCond1218_anti (by omega) hab) hTH hF
  rw [zero_add] at h3
  have hC := h3.resolve_left hHN
  rw [Subgroup.commutator_comm] at hC
  have hR : twoResidual H ≤ centralizer (E3.cClos V (Δ.sup ι) D.T : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hC
  obtain ⟨g, hgN, hgM⟩ := SetLike.not_le_iff_exists.1 hNi
  exact hO2 H hH g hgM
    (TwelveTwentyTwo.le_conjSubgroup_of_le_centralizer_cClos h hV₀ (by omega) hR hgN)

theorem twelve_twentyThree_three_AS (D : Data G) (hx : DataExt D)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h1114 : R1114 D) (h162 : W3Thm162Ext G)
    (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G) (h126 : R126 D) {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) (hV₀ : V₀ ≠ ⊥) {L : Subgroup G} (hLM : CFSG.Open.IsSubnormal L D.M)
    (hLq : CFSG.Open.IsQuasisimple (UC22.Bar2 L)) (hL1 : barSub V₀ V h.isElemAbelian L ≠ ⊥)
    {Δ : Finset (Subgroup G)} (hΔ : ∀ H ∈ Δ, D.T ≤ H ∧ H ≤ D.M)
    (hΔU : UniqueMax D.M (⨆ H ∈ Δ, H)) (ι : Subgroup G → ℕ) (hι : ∀ H ∈ Δ, InFSqAS (ι H) H)
    (hO2 : ∀ H ∈ Δ, ∀ g : G, g ∉ D.M → ¬ twoResidual H ≤ conjSubgroup D.M g) :
    mBar D.M V₀ V h.isElemAbelian ≤
      bBar (UC22.conjClosure D.M L) D.M V₀ V h.isElemAbelian + D.k + Δ.sup ι := by
  have h3 := twelve_twentyTwo_three_AS D hx h61 h127 h1114 h162 hTor h1482 h126 h hV₀
    (TwelveTwentyThree.conjClosure_le hLM.le)
    (TwelveTwentyThree.le_normalizer_conjClosure D.M L)
    (TwelveTwentyThree.barSub_conjClosure_ne_bot h.isElemAbelian hL1) hΔ hΔU ι hι hO2
    (TwelveTwentyThree.xCond1218_conjClosure h hV₀ hLM hLq _)
  omega

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

section Certified


theorem mBar_le_bBar_add_of_deltaAS (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1114 : R1114 D) (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G)
    (h1482 : W3Lem148_2 G) (h126 : R126 D) (h111 : W3Thm111 G)
    {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V) {L : Subgroup G} (k₀ : ℕ)
    (hLM : CFSG.Open.IsSubnormal L D.M) (hLq : CFSG.Open.IsQuasisimple (UC22.Bar2 L))
    (hL1 : barSub V₀ V hV.isElemAbelian L ≠ ⊥)
    (hU : UniqueMax D.M (UC22.conjClosure D.M L))
    (hconf : V₀ ≠ ⊥ → ∃ Δ : Finset (Subgroup G),
      (∀ H ∈ Δ, D.T ≤ H ∧ H ≤ D.M) ∧ UniqueMax D.M (⨆ H ∈ Δ, H) ∧
      (∀ H ∈ Δ, InFSqAS 2 H) ∧
      (∀ H ∈ Δ, ∀ g : G, g ∉ D.M → ¬ twoResidual H ≤ conjSubgroup D.M g))
    (hk : D.k ≤ k₀) :
    mBar D.M V₀ V hV.isElemAbelian ≤
      bBar (UC22.conjClosure D.M L) D.M V₀ V hV.isElemAbelian + k₀ + 2 := by
  by_cases hV0 : V₀ = ⊥
  · have h1 := twelve_twentyThree_one D hx h61 h126 h111 hV hV0 hLM hLq hL1 hU
    omega
  · obtain ⟨Δ, hTM, hUΔ, hι, hO2⟩ := hconf hV0
    have hsup : Δ.sup (fun _ => 2) ≤ 2 := Finset.sup_le fun _ _ => le_rfl
    have h3 := twelve_twentyThree_three_AS D hx h61 h127 h1114 h162 hTor h1482 h126 hV hV0
      hLM hLq hL1 hTM hUΔ (fun _ => 2) (fun H hH => hι H hH) hO2
    omega

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
