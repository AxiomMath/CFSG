module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenT7Proof
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenSmallDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def RT7OneSmall (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (h : Hyp154 D V₀ V L), mSub V₀ ≤ 2 →
    barSub V₀ V h.hyp151.isElemAbelian L ≠ ⊥ →
      ∀ F C K : Subgroup G,
        s15T7Config D.M
          (wSub V₀ V h.hyp151.isElemAbelian L ⊔ v1Sub D.M V₀ V h.hyp151.isElemAbelian L)
          (v1Sub D.M V₀ V h.hyp151.isElemAbelian L) F C K →
          gamma15 D.M V₀ V h.hyp151.isElemAbelian L = 3 ∧
            s15 D.M V₀ V h.hyp151.isElemAbelian L = 2

theorem s15Small_T7_rt7_of_one (D : Data G) (h1 : RT7OneSmall D) : RT7Small D := by
  intro V₀ V L h hsmall hL g X hX F C K hFab hFM hCF hFN hC hUK hKE hmK hFK hmFC
  obtain ⟨m, hm, rfl⟩ := hX
  have hv1 : conjSubgroup (v1Sub D.M V₀ V h.hyp151.isElemAbelian L) m =
      v1Sub D.M V₀ V h.hyp151.isElemAbelian L :=
    s15_Infra_conjSubgroup_v1Sub h.hyp151.hyp125 h.hyp151.isElemAbelian hm
  have hM : conjSubgroup D.M m = D.M :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hm)
  have hE : conjSubgroup (conjSubgroup (wSub V₀ V h.hyp151.isElemAbelian L) m ⊔
      v1Sub D.M V₀ V h.hyp151.isElemAbelian L) g =
      conjSubgroup (wSub V₀ V h.hyp151.isElemAbelian L ⊔
        v1Sub D.M V₀ V h.hyp151.isElemAbelian L) (m * g) := by
    rw [← conjSubgroup_conjSubgroup, s15_T7_conjSubgroup_sup (wSub V₀ V _ L) _ m, hv1]
  have hU : conjSubgroup (v1Sub D.M V₀ V h.hyp151.isElemAbelian L) g =
      conjSubgroup (v1Sub D.M V₀ V h.hyp151.isElemAbelian L) (m * g) := by
    rw [← conjSubgroup_conjSubgroup, hv1]
  have hM' : conjSubgroup D.M g = conjSubgroup D.M (m * g) := by
    rw [← conjSubgroup_conjSubgroup, hM]
  have hcfg : s15T7Config (conjSubgroup D.M (m * g))
      (conjSubgroup (wSub V₀ V h.hyp151.isElemAbelian L ⊔
        v1Sub D.M V₀ V h.hyp151.isElemAbelian L) (m * g))
      (conjSubgroup (v1Sub D.M V₀ V h.hyp151.isElemAbelian L) (m * g)) F C K := by
    rw [← hE, ← hU, ← hM']
    exact ⟨hFab, hFM, hCF, hFN, hC, hUK, hKE, hmK, hFK, hmFC⟩
  exact h1 V₀ V L h hsmall hL _ _ _ (s15_T7_config_conj _ _ _ F C K (m * g) hcfg)

theorem s15Small_T7_rt7One_of_fifteen_three (D : Data G) (h153 : R15_3Small D)
    (h129 : R129_1 D) (h1217 : R1217 D) : RT7OneSmall D := by
  intro V₀ V L h hsmall hL F C K hcfg
  have hQ := s15_T7_exists_group D h.hyp151 hcfg
  have hdesc := h153 V₀ V L h.hyp151 hsmall (s15_T7_exists_transvection D h.hyp151 hQ)
  have hs := fifteen_five D h129 h1217 h h.hyp151.isElemAbelian hL
  rcases hdesc with h1 | h2 | h3
  · have h1s := h1.2.2.2.2.1
    omega
  · exact s15_T7_case2 D h.hyp151 hs hQ h2
  · exact (s15_T7_case3 D h.hyp151 hQ h3).elim

theorem rt7_of_fifteen_three_small (D : Data G) (h153 : R15_3Small D) (h129 : R129_1 D)
    (h1217 : R1217 D) : RT7Small D :=
  s15Small_T7_rt7_of_one D (s15Small_T7_rt7One_of_fifteen_three D h153 h129 h1217)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
