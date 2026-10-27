module

public import CFSG.LocalAnalysis.UniquenessCase.UC9R96Core
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddComm
public import CFSG.LocalAnalysis.UniquenessCase.UC9R96Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC9R96

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem uc9r96_comm_mem_pCoreOf_of_not_normalizes {K L A : Subgroup G} (hL : L ∈ calC K)
    (hAK : A ≤ K) (hA3 : ¬ 3 ∣ Nat.card A) {a d : G} (ha : a ∈ A)
    (hdA : d ∈ normalizer (A : Set G)) (hdL : d ∈ L) (haL : a ∉ normalizer (L : Set G))
    {k : ℕ} (hdk : orderOf d = 3 ^ k) : ⁅a, d⁆ ∈ pCoreOf 2 K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLK : L ≤ K := hL.1.le
  have hL' : uniqueFourConj a⁻¹ L ∈ calC K :=
    uc22p22u_calC_conj (Subgroup.le_normalizer) hL (K.inv_mem (hAK ha))
  have hne : uniqueFourConj a⁻¹ L ≠ L := by
    intro h
    apply haL
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    simpa [uniqueFourConj] using h
  have hu : a * d * a⁻¹ ∈ uniqueFourConj a⁻¹ L :=
    Subgroup.mem_map.2 ⟨d, hdL, by simp [MulAut.conj_apply]⟩
  have hcomm := PartTwo.commutator_mem_pCoreOf_of_ne hL' hL hne hu (L.inv_mem hdL)
  set π : ↥K →* Bar2 K := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  set a' : ↥K := ⟨a, hAK ha⟩ with ha'
  set d' : ↥K := ⟨d, hLK hdL⟩ with hd'
  have hd3 : d' ^ 3 ^ k = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one, hd', ← hdk]
    exact pow_orderOf_eq_one d
  have hc : Commute (π (a' * d' * a'⁻¹)) (π d'⁻¹) := by
    rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement, hπ,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      CFSG.RankThree.PartTwo.Sec16.Step163Alt.mem_pCore_two_iff]
    simpa [ha', hd', commutatorElement_def] using hcomm
  have hwA : ⁅a, d⁆ ∈ A := by
    have h1 : ⁅a, d⁆ = a * (d * a⁻¹ * d⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [h1]
    exact A.mul_mem ha ((Subgroup.mem_normalizer_iff.1 hdA a⁻¹).1 (A.inv_mem ha))
  set w' : ↥K := ⟨⁅a, d⁆, hAK hwA⟩ with hw'
  have hw : w' = a' * d' * a'⁻¹ * d'⁻¹ := by
    apply Subtype.ext
    simp [hw', ha', hd', commutatorElement_def]
  have hord : ¬ 3 ∣ orderOf (π (a' * d' * a'⁻¹) * π d'⁻¹) := by
    intro h3
    rw [← map_mul, ← hw] at h3
    have h4 : orderOf w' = orderOf (⟨⁅a, d⁆, hwA⟩ : ↥A) := by
      rw [← Subgroup.orderOf_coe w', ← Subgroup.orderOf_coe (⟨⁅a, d⁆, hwA⟩ : ↥A)]
    exact hA3 ((h3.trans ((orderOf_map_dvd π w').trans (dvd_of_eq h4))).trans
      (orderOf_dvd_natCard _))
  have h1 := eq_one_of_commute_threePow hc (k := k) (by
    rw [← map_pow, conj_pow, hd3]; simp) (by
    rw [← map_pow, inv_pow, hd3]; simp) hord
  rw [← map_mul, ← hw, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    CFSG.RankThree.PartTwo.Sec16.Step163Alt.mem_pCore_two_iff] at h1
  exact h1

private theorem uc9r96_comm_le_inf_pCoreOf {K X A : Subgroup G} (hX : X ∈ calC K)
    (hX3 : Opp 3 X = X) (hs : IsSimpleGroup (Bar2 X)) (h3 : 3 ∣ Nat.card (Bar2 X))
    (hAK : A ≤ K) (hA3 : ¬ 3 ∣ Nat.card A) (hXA : X ≤ normalizer (A : Set G)) :
    ⁅A, X⁆ ≤ A ⊓ pCoreOf 2 K := by
  have hXK : X ≤ K := hX.1.le
  have hXB : X ≤ normalizer ((A ⊓ pCoreOf 2 K : Subgroup G) : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hXA hx,
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K (hXK hx)⟩
  have hXN : X ≤ normalizer ((A ⊓ normalizer (X : Set G) : Subgroup G) : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hXA hx,
      Subgroup.le_normalizer (Subgroup.le_normalizer hx)⟩
  have hO : pCoreOf 2 X ≤ pCoreOf 2 K :=
    CFSG.Quasithin.pCoreOf_le_pCoreOf_of_isSubnormal hX.1
  have hsup : X = X ⊔ pCoreOf 2 X := (sup_eq_left.2 (map_subtype_le (pCore 2 ↥X))).symm
  have key : ∀ d ∈ X, (∃ k : ℕ, orderOf d = 3 ^ k) → ∀ a ∈ A, ⁅a, d⁆ ∈ A ⊓ pCoreOf 2 K := by
    intro d hd ⟨k, hk⟩ a ha
    have hdA : ⁅a, d⁆ ∈ A := by
      have h1 : ⁅a, d⁆ = a * (d * a⁻¹ * d⁻¹) := by simp [commutatorElement_def, mul_assoc]
      rw [h1]
      exact A.mul_mem ha ((Subgroup.mem_normalizer_iff.1 (hXA hd) a⁻¹).1 (A.inv_mem ha))
    refine ⟨hdA, ?_⟩
    by_cases haX : a ∈ normalizer (X : Set G)
    · have hmem : ⁅a, d⁆ ∈ ⁅A ⊓ normalizer (X : Set G), X⁆ :=
        Subgroup.commutator_mem_commutator ⟨ha, haX⟩ hd
      exact hO (comm_le_pCoreOf_of_normalizes le_rfl hsup hs h3 inf_le_right hXN
        (fun h => hA3 (h.trans (Subgroup.card_dvd_of_le inf_le_left))) hmem)
    · exact uc9r96_comm_mem_pCoreOf_of_not_normalizes hX hAK hA3 ha (hXA hd) hd haX hk
  rw [Subgroup.commutator_le]
  intro a ha x hx
  exact commutator_mem_of_three_elements hXB key x (by rw [hX3]; exact hx) a ha

theorem comm_le_pCoreOf_of_mem_calC {K X A : Subgroup G} (hX : X ∈ calC K) (hX3 : Opp 3 X = X)
    (hs : IsSimpleGroup (Bar2 X)) (h3 : 3 ∣ Nat.card (Bar2 X)) (hAK : A ≤ K)
    (hA3 : ¬ 3 ∣ Nat.card A) (hXA : X ≤ normalizer (A : Set G)) : ⁅A, X⁆ ≤ pCoreOf 2 A :=
  (uc9r96_comm_le_inf_pCoreOf hX hX3 hs h3 hAK hA3 hXA).trans
    (CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 hAK)

namespace Std96

variable {D : Data G} {Y H D₃ : Subgroup G}

theorem toCore (S : Std96 D Y H D₃) : Core D Y H 7 :=
  ⟨S.Y_le_H, S.Y_le_M, S.not_H_le_M, S.ne_top, by norm_num, by norm_num, S.seven,
    S.isSimpleGroup_bar2_opp, S.three_dvd_card_bar2_opp,
    fun h => uc22p22a_qs_not_solvable S.calC.2.2 h,
    fun _ hAH hAM hA3 hXA => comm_le_pCoreOf_of_mem_calC S.calC
      (PartOne.Section9.opp_opp 3 Y) S.isSimpleGroup_bar2_opp S.three_dvd_card_bar2_opp
      (le_inf hAH hAM) hA3 hXA⟩

end Std96

end CFSG.LocalAnalysis.UniquenessCase.UC9R96
