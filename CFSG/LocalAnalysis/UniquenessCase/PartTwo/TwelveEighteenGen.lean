module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveEighteenNine
public import CFSG.LocalAnalysis.WeakClosure81.EightTwelveBridge
public import CFSG.LocalAnalysis.WeakClosure81.SixThirteenGen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace TwelveEighteen

variable {M V₀ V : Subgroup G}

theorem commutator_twoResidual_cClos_eq_bot_of_no_calO1_gen (hH : Hyp6H M V₀ V)
    (hV₀ : V₀ ≠ ⊥) {i n k : ℕ} (hink : i + n ≤ k) (hkr : (k : ℕ∞) < rMV M V)
    (hkm : k < mBar M V₀ V hH.elemAbelian) (hno : ∀ g : G, ¬ InCalO1 k M V₀ V g)
    {H S A K : Subgroup G} (hS : IsSylowIn 2 S H) (hA : A ∈ E3.gammaSet V i S)
    (hK : E1.IsE n H S A K) :
    ⁅twoResidual K, E3.cClos V k S⁆ = ⊥ := by
  by_contra hne
  obtain ⟨-, g, hg⟩ := exists_inCalO1_of_commutator_ne_bot_gen hH.elemAbelian hH.le
    hH.normalizer_eq.symm.le hH.le_normalizer₀ hH.normalizer_eq (hH.normalizer₀ hV₀)
    (forall_conjSubgroup_eq_of_isTI (hH.isTI hV₀)) hS hink hA hK
    (hkm.trans_le (mBar_le_rk hH.elemAbelian hH.le))
    (by rwa [← rMV_eq_rParam hH.normalizer_eq]) hkm hne
  exact hno g hg

theorem eGen_le_sup_of_no_calO1_gen (hH : Hyp6H M V₀ V) (hV₀ : V₀ ≠ ⊥) {i n k : ℕ}
    (hink : i + n ≤ k) (hkr : (k : ℕ∞) < rMV M V) (hkm : k < mBar M V₀ V hH.elemAbelian)
    (hno : ∀ g : G, ¬ InCalO1 k M V₀ V g) {H S : Subgroup G} (hS : IsSylowIn 2 S H) :
    E1.eGen n H S (E3.gammaSet V i H) ≤ (H ⊓ centralizer (E3.cClos V k S : Set G)) ⊔ S := by
  refine iSup₂_le fun A hA => iSup_le fun hAS => iSup₂_le fun K hK => ?_
  have hAΓ : A ∈ E3.gammaSet V i S := ⟨hAS, hA.2⟩
  have hSK : IsSylowIn 2 (S ⊓ K) K := hK.2.2.1
  have hKeq : K = (S ⊓ K) ⊔ twoResidual K := (sup_twoResidual_eq hSK).symm
  have hcomm := commutator_twoResidual_cClos_eq_bot_of_no_calO1_gen hH hV₀ hink hkr hkm
    hno hS hAΓ hK
  have h1 : S ⊓ K ≤ S := inf_le_left
  have h2 : twoResidual K ≤ H ⊓ centralizer (E3.cClos V k S : Set G) :=
    le_inf ((twoResidual_le K).trans hK.1)
      (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm)
  rw [hKeq]
  exact sup_le (h1.trans le_sup_right) (h2.trans le_sup_left)

theorem six_thirteen_two_of_no_calO1_gen (hH : Hyp6H M V₀ V) (hV₀ : V₀ ≠ ⊥) {i n k : ℕ}
    (hink : i + n ≤ k) (hkr : (k : ℕ∞) < rMV M V) (hkm : k < mBar M V₀ V hH.elemAbelian)
    (hno : ∀ g : G, ¬ InCalO1 k M V₀ V g) {H S : Subgroup G} (hS : IsSylowIn 2 S H)
    (hE : E1.InE n H) :
    (H ⊓ normalizer (E3.wClos V i S : Set G)) ⊔ (H ⊓ centralizer (E3.cClos V k S : Set G)) =
      H := by
  refine le_antisymm (sup_le inf_le_left inf_le_left) ?_
  have hV := hH.elemAbelian
  have hEF := (E1.inE_iff_inEFor hS).1 hE (E3.gammaSet V i H) (E3.isInvColl_gammaSet hV i H)
  rw [E3.weakClosure_gammaSet hS.le] at hEF
  have hSN : S ≤ H ⊓ normalizer (E3.wClos V i S : Set G) :=
    le_inf hS.le (Subgroup.le_normalizer.trans (E3.normalizer_le_normalizer_wClos S))
  calc H = E1.eGen n H S (E3.gammaSet V i H) ⊔
        (H ⊓ normalizer (E3.wClos V i S : Set G)) := hEF.symm
    _ ≤ ((H ⊓ centralizer (E3.cClos V k S : Set G)) ⊔ S) ⊔
        (H ⊓ normalizer (E3.wClos V i S : Set G)) :=
      sup_le_sup_right (eGen_le_sup_of_no_calO1_gen hH hV₀ hink hkr hkm hno hS) _
    _ ≤ _ := sup_le (sup_le le_sup_right (hSN.trans le_sup_left)) le_sup_left

theorem exists_gammaSet_not_le_pCoreOf {V H S : Subgroup G} {i : ℕ} (hS : IsSylowIn 2 S H)
    (hHN : ¬ H ≤ normalizer (E3.wClos V i S : Set G)) :
    ∃ A ∈ E3.gammaSet V i S, ¬ A ≤ pCoreOf 2 H := by
  by_contra hc
  apply hHN
  have hle : ∀ A ∈ E3.gammaSet V i S, A ≤ pCoreOf 2 H := by
    intro A hA
    by_contra hA'
    exact hc ⟨A, hA, hA'⟩
  have hW : E3.wClos V i S = E3.wClos V i (pCoreOf 2 H) := by
    refine le_antisymm ?_ (E3.wClos_mono (E1.pCoreOf_two_le_of_isSylowIn hS))
    exact E3.wClos_le_of_forall fun A hA => E3.le_wClos ⟨hle A hA, hA.2⟩
  rw [hW]
  exact (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H).trans
    (E3.normalizer_le_normalizer_wClos (V := V) (i := i) (pCoreOf 2 H))

private theorem twoResidual_le_of_le_sup_two {J S P : Subgroup G}
    (hSJ : S ≤ normalizer (J : Set G)) (hS2 : IsPGroup 2 S) (hP : P ≤ J ⊔ S) :
    twoResidual P ≤ J := by
  have hpow : ∀ c ∈ J ⊔ S, ∃ n : ℕ, c ^ 2 ^ n ∈ J := by
    intro c hc
    have h : c ∈ (↑(J ⊔ S) : Set G) := hc
    rw [Subgroup.coe_mul_of_right_le_normalizer_left J S hSJ] at h
    obtain ⟨k, hk, s, hs, rfl⟩ := h
    obtain ⟨n, hn⟩ := hS2 ⟨s, hs⟩
    have hsn : s ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have key : ∀ m : ℕ, ∃ k' ∈ J, (k * s) ^ m = k' * s ^ m := by
      intro m
      induction m with
      | zero => exact ⟨1, J.one_mem, by simp⟩
      | succ m ih =>
        obtain ⟨k', hk', h'⟩ := ih
        refine ⟨k' * (s ^ m * k * (s ^ m)⁻¹), ?_, ?_⟩
        · refine J.mul_mem hk' ?_
          have : s ^ m ∈ normalizer (J : Set G) := Subgroup.pow_mem _ (hSJ hs) m
          exact (mem_normalizer_iff.mp this k).mp hk
        · rw [pow_succ, h', pow_succ]
          group
    obtain ⟨k', hk', h'⟩ := key (2 ^ n)
    exact ⟨n, by rw [h', hsn, mul_one]; exact hk'⟩
  have hJS : J ⊔ S ≤ normalizer (J : Set G) := sup_le Subgroup.le_normalizer hSJ
  have h1 : twoResidual P ≤ P ⊓ J := by
    refine twoResidual_le_of_isTwoQuotient inf_le_left ?_ ?_
    · exact fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hx, hJS (hP hx)⟩
    · intro y hy
      obtain ⟨k, hk⟩ := hpow y (hP hy)
      exact ⟨k, P.pow_mem hy _, hk⟩
  exact h1.trans inf_le_right

theorem twelve_eighteen_three_of_no_calO1 (hH : Hyp6H M V₀ V) (hV₀ : V₀ ≠ ⊥) {i n k : ℕ}
    (hink : i + n ≤ k) (hkr : (k : ℕ∞) < rMV M V) (hkm : k < mBar M V₀ V hH.elemAbelian)
    (hno : ∀ g : G, ¬ InCalO1 k M V₀ V g) {H S : Subgroup G} (hS : IsSylowIn 2 S H)
    (hF : InFSq n H) :
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
  · exact twoResidual_le_of_le_sup_two hSJ hS.isPGroup hHM
  · exfalso
    obtain ⟨A, hA, -, K, hK, hKM⟩ := exists_isE_not_le_of_inF2 hH.elemAbelian hS hF
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

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
