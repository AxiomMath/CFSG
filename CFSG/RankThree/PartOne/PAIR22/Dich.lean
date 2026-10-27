module

public import CFSG.RankThree.PartOne.PAIR22.Lift
public import CFSG.RankThree.PartOne.S13K.Pair134
import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents

public section

namespace CFSG.RankThree.PartOne.PAIR22

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.K1320X
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem kf133Two_conj (h133 : KF133Two) {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G}
    {c : G} {L E : Subgroup G} (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hF13 : Sec13Facts G p A c L E) (hT : ¬ Outcome152Five p E A (lieGenerated p E))
    {s : MulAut E} (hs : s ∈ reflectionSet p E) {w : G} (hw : w ∈ Subgroup.normalizer (E : Set G))
    (hsL : conjAut E w hw * s * (conjAut E w hw)⁻¹ ∈ torusImage E L) {K : Subgroup G}
    (hK : IsKt p E s K) {e : G} (he : e ∈ autFixedInG E s) (he1 : e ≠ 1) {I : Subgroup G}
    (hI : I ∈ thetaComponentsAt p e) (hKI : K ≤ I) :
    (E = A ∧ ∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f + 1 ∧
        StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 2 f) ∨
      ∃ J ∈ thetaCompZeroStarE p E, sectionTenRel p I J := by
  have hp := h.prime
  have hmem : w * e * w⁻¹ ∈ autFixedInG E (conjAut E w hw * s * (conjAut E w hw)⁻¹) := by
    rw [Equivariance.autFixedInG_conj s hw]
    exact Subgroup.mem_map_of_mem (MulAut.conj w).toMonoidHom he
  have hne : w * e * w⁻¹ ≠ 1 := fun h1 => he1 (conj_eq_one_iff.mp h1)
  rcases h133 G p A c L E h hF hF13 hT _ (conj_mem_reflectionSet hp hs hw) hsL (conjBy w K)
      (isKt_conj hK hw) (w * e * w⁻¹) hmem hne (conjBy w I)
      (conjBy_mem_thetaComponentsAt hp w e hI) (Subgroup.map_mono hKI) with
    hex | ⟨J, hJ, hIJ⟩
  · exact Or.inl hex
  · refine Or.inr ⟨conjBy w⁻¹ J, conjBy_mem_thetaCompZeroStarE hp
      ((Subgroup.normalizer (E : Set G)).inv_mem hw) hJ, ?_⟩
    have h2 := (sectionTenRel_conjBy hp w⁻¹).2 hIJ
    rwa [Equivariance.conjBy_inv_conjBy] at h2

theorem pair_dich (hS : SchreierFor InCatalog) (h133 : KF133Two) {G : Type} [Group G] [Finite G]
    {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G} (h : Sec12Hyp G p A c L E)
    (hF : Sec12Facts G p A c L E) (hF13 : Sec13Facts G p A c L E)
    (hT : ¬ Outcome152Five p E A (lieGenerated p E)) {s t : MulAut E}
    (hs : s ∈ reflectionSet p E) (ht : t ∈ reflectionSet p E) {w : G}
    (hw : w ∈ Subgroup.normalizer (E : Set G))
    (hsL : conjAut E w hw * s * (conjAut E w hw)⁻¹ ∈ torusImage E L) {Ks Kt : Subgroup G}
    (hKs : KtLift p E s Ks) (hqs : CFSG.IsQuasisimple ↥(kZero p E s)) (hKt : KtLift p E t Kt)
    (hqt : CFSG.IsQuasisimple ↥(kZero p E t)) :
    (∃ (e : G) (I₁ I₂ : Subgroup G), e ∈ E ∧ e ≠ 1 ∧ e ∈ autFixedInG E s ∧ e ∈ autFixedInG E t ∧
        I₁ ∈ thetaComponentsAt p e ∧ I₂ ∈ thetaComponentsAt p e ∧ I₁ ≠ I₂ ∧ Ks ≤ I₁ ∧ Kt ≤ I₂) ∨
      ∃ (e : G) (I : Subgroup G), e ∈ E ∧ e ≠ 1 ∧ e ∈ autFixedInG E s ∧ e ∈ autFixedInG E t ∧
        I ∈ thetaComponentsAt p e ∧ Ks ≤ I ∧ Kt ≤ I ∧
        ((E = A ∧ ∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f + 1 ∧
            StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 2 f) ∨
          ∃ J ∈ thetaCompZeroStarE p E, Ks ≤ J ∧ Kt ≤ J) := by
  have hp := h.prime
  have hE : IsElementaryAbelian p ↥E := h.E_elem
  obtain ⟨⟨e, hee⟩, hne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (hF13.axes s hs t ht)
  have he1 : e ≠ 1 := fun h1 => hne (Subtype.ext h1)
  have hesE : e ∈ autFixedInG E s := (Subgroup.mem_inf.mp hee).1
  have hetE : e ∈ autFixedInG E t := (Subgroup.mem_inf.mp hee).2
  have heE : e ∈ E := Subgroup.map_subtype_le _ hesE
  obtain ⟨I₁, hI₁, hK₀I₁⟩ := exists_thetaComponentsAt_ge_of_hyp h hS he1
    (isElementaryAbelian_of_le' hE (Subgroup.map_subtype_le _)) hesE
    (kZero_le_centralizer_fixed p E s) (kZero_mem_thetaComponents hp hqs)
  obtain ⟨I₂, hI₂, hK₀I₂⟩ := exists_thetaComponentsAt_ge_of_hyp h hS he1
    (isElementaryAbelian_of_le' hE (Subgroup.map_subtype_le _)) hetE
    (kZero_le_centralizer_fixed p E t) (kZero_mem_thetaComponents hp hqt)
  have hKsI₁ : Ks ≤ I₁ := (IsKt.le_kZero hKs.1).trans hK₀I₁
  have hKtI₂ : Kt ≤ I₂ := (IsKt.le_kZero hKt.1).trans hK₀I₂
  by_cases hI : I₁ = I₂
  · subst hI
    refine Or.inr ⟨e, I₁, heE, he1, hesE, hetE, hI₁, hKsI₁, hKtI₂, ?_⟩
    rcases kf133Two_conj h133 h hF hF13 hT hs hw hsL hKs.1 hesE he1 hI₁ hKsI₁ with hex | ⟨J, hJ, hIJ⟩
    · exact Or.inl hex
    · have hEI : E ≤ Subgroup.normalizer (I₁ : Set G) :=
        h.E_normalizes_thetaComponentsAt selected_prime_elements_normalize_theta_components heE hI₁
      have hEJ : E ≤ Subgroup.normalizer (J : Set G) := normalizes_of_mem_thetaCompE h hJ.2.1
      exact Or.inr ⟨J, hJ, isKt_le_of_sectionTenRel hp hE hKs.1 hKs.2.1.1 hesE hI₁ hKsI₁ hIJ hEI hEJ,
        isKt_le_of_sectionTenRel hp hE hKt.1 hKt.2.1.1 hetE hI₁ hKtI₂ hIJ hEI hEJ⟩
  · exact Or.inl ⟨e, I₁, I₂, heE, he1, hesE, hetE, hI₁, hI₂, hI, hKsI₁, hKtI₂⟩

theorem pair_member (hS : SchreierFor InCatalog) (h133 : KF133Two) {G : Type} [Group G] [Finite G]
    {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G} (h : Sec12Hyp G p A c L E)
    (hF : Sec12Facts G p A c L E) (hF13 : Sec13Facts G p A c L E)
    (hT : ¬ Outcome152Five p E A (lieGenerated p E))
    (hn8 : ¬ ∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f + 1 ∧
      StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 2 f)
    {s t : MulAut E} (hs : s ∈ reflectionSet p E) (ht : t ∈ reflectionSet p E)
    (hst : s * t ≠ t * s) {w : G} (hw : w ∈ Subgroup.normalizer (E : Set G))
    (hsL : conjAut E w hw * s * (conjAut E w hw)⁻¹ ∈ torusImage E L) (hLs : PairLift p E s)
    (hLt : PairLift p E t) :
    ∃ J ∈ thetaCompZeroStarE p E, s ∈ torusImage E J ∧ t ∈ torusImage E J := by
  obtain ⟨Ks, hKs, hqs⟩ := hLs
  obtain ⟨Kt, hKt, hqt⟩ := hLt
  rcases pair_dich hS h133 h hF hF13 hT hs ht hw hsL hKs hqs hKt hqt with
    ⟨e, I₁, I₂, heE, -, -, -, hI₁, hI₂, hne, hK₁, hK₂⟩ | ⟨e, I, -, -, -, -, -, -, -, hcase⟩
  · exfalso
    apply hst
    obtain ⟨-, -, -, -, ks, hks, hksK, hks_eq⟩ := hKs
    obtain ⟨-, -, -, -, kt, hkt, hktK, hkt_eq⟩ := hKt
    have := commute_of_distinct_components h.prime h.E_elem heE hI₁ hI₂ hne (hK₁ hksK) (hK₂ hktK)
      hks hkt
    rw [hks_eq, hkt_eq] at this
    exact this
  · rcases hcase with ⟨-, hex⟩ | ⟨J, hJ, hKsJ, hKtJ⟩
    · exact absurd hex hn8
    · obtain ⟨-, -, -, -, ks, hks, hksK, hks_eq⟩ := hKs
      obtain ⟨-, -, -, -, kt, hkt, hktK, hkt_eq⟩ := hKt
      exact ⟨J, hJ, Sec12Three.mem_torusImage_iff.mpr ⟨ks, hKsJ hksK, hks, hks_eq⟩,
        Sec12Three.mem_torusImage_iff.mpr ⟨kt, hKtJ hktK, hkt, hkt_eq⟩⟩

end CFSG.RankThree.PartOne.PAIR22
