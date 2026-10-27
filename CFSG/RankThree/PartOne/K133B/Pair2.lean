module

public import CFSG.RankThree.PartOne.K133B.Glue

public section

namespace CFSG.RankThree.PartOne.K133B

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.K1320X
  CFSG.RankThree.PartOne.Q1327T
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

theorem not_dvd_card_center_thetaQuot (hSLB : N143.SectionListBound) {G : Type} [Group G]
    [Finite G] (hKP : CFSG.IsKProper G) (he : CFSG.twoLocalOddRank G ≤ 3) {p : ℕ}
    (hp : p.Prime) {a : G} {I : Subgroup G} (hI : I ∈ thetaComponentsAt p a) (hItop : I ≠ ⊤)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (h7 : 7 ≤ ℓ) :
    ¬ ℓ ∣ Nat.card (Subgroup.center (↥I ⧸ aschbacherSolvableCore p ↥I)) := by
  have hKI : CFSG.IsKGroup ↥I := hKP I hItop
  have heI : CFSG.Assembly.evenRank ↥I ≤ 3 :=
    (CFSG.RankThree.PartTwo.evenRank_subgroup_le I).trans
      ((CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank G).le.trans he)
  have hq : CFSG.IsQuasisimple (↥I ⧸ aschbacherSolvableCore p ↥I) :=
    isQuasisimple_thetaQuotient_of_mem_thetaComponentsAt hp hI
  exact (hSLB ↥I hKI heI ⊤ _ hq
    ((QuotientGroup.mk' (aschbacherSolvableCore p ↥I)).comp
      (Subgroup.topEquiv : (⊤ : Subgroup ↥I) ≃* ↥I).toMonoidHom)
    ((QuotientGroup.mk'_surjective _).comp
      (Subgroup.topEquiv : (⊤ : Subgroup ↥I) ≃* ↥I).surjective)).2 ℓ hℓ h7

@[expose] def Row8NotCentral5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G 5 A c L E → Sec13Facts G 5 A c L E → E = A →
    ∀ t ∈ reflectionSet 5 E, ∀ K : Subgroup G, KtLift 5 E t K →
      (∃ g : ℕ, StatedClassicalModel ↥K .PSL 2 2 g ∧ 5 ∣ 2 ^ g + 1) →
      ∀ e ∈ autFixedInG E t, e ≠ 1 → ∀ I ∈ thetaComponentsAt 5 e, K ≤ I → e ∉ I

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

theorem oddDatum_of_pair (hSLB : N143.SectionListBound) (hInsp : Row8U3Inspection)
    (hOdd : Row8OddInspection) (hNC : Row8NotCentral5) (h : Sec12Hyp G p A c L E)
    (hF13 : Sec13Facts G p A c L E) (hEA : E = A) {t s : MulAut E} (ht : t ∈ reflectionSet p E)
    (hs : s ∈ reflectionSet p E) (hts : t * s ≠ s * t) {K Ks : Subgroup G}
    (hK : KtLift p E t K) (hKs : KtLift p E s Ks) {g : ℕ}
    (hmod : StatedClassicalModel ↥K .PSL 2 2 g) (hpg : p ∣ 2 ^ g + 1) {e : G} (he1 : e ≠ 1)
    (hetE : e ∈ autFixedInG E t) {I : Subgroup G} (hI : I ∈ thetaComponentsAt p e)
    (hKI : K ≤ I) (hKsI : Ks ≤ I) : OddOrderOneOrThree ↥(torusImage E I) := by
  have hp := h.prime
  have hp5 := Sec12Three.five_le h
  have hcard : Nat.card E = p ^ 3 := by rw [hEA]; exact h.A_card
  have htw : t ∈ torusWeyl E := by
    obtain ⟨X, -, hX⟩ := ht.2
    exact Sec127.torusImage_le_torusWeyl E X hX
  have hsw : s ∈ torusWeyl E := by
    obtain ⟨X, -, hX⟩ := hs.2
    exact Sec127.torusImage_le_torusWeyl E X hX
  by_cases heP : e ∈ autMovedInG E t ⊔ autMovedInG E s
  · exfalso
    have hPI : autMovedInG E t ⊔ autMovedInG E s ≤ I :=
      sup_le (hK.2.2.2.1.trans hKI) (hKs.2.2.2.1.trans hKsI)
    have heI : e ∈ I := hPI heP
    obtain ⟨hIC, -⟩ := mem_thetaComponentsAt_iff.1 hI
    have heIcent : ∀ n ∈ I, e * n = n * e := fun n hn =>
      Subgroup.mem_centralizer_iff.1 (hIC hn) e rfl
    have hep : e ^ p = 1 := Sec12Three.pow_eq_one_of_mem_E h (Subgroup.map_subtype_le _ hetE)
    have hdvd := dvd_card_center_of_mem hp he1 hep heIcent heI
    by_cases h5 : p = 5
    · subst h5
      exact hNC G A c L E h hF13 hEA t ht K hK ⟨g, hmod, hpg⟩ e hetE he1 I hI hKI heI
    · have h7 : 7 ≤ p := by
        by_contra hlt
        push Not at hlt
        interval_cases p
        · exact h5 rfl
        · exact absurd hp (by decide)
      obtain ⟨hsimp, hnonab, hKP, -, he3, -⟩ := h.setup
      have := hsimp
      have hItop : I ≠ ⊤ := by
        intro htop
        exact EmbeddingFixedResidual.centralizer_ne_top_of_simple hnonab he1
          (eq_top_iff.2 (htop ▸ hIC))
      exact not_dvd_card_center_thetaQuot hSLB hKP he3.le hp hI hItop hp h7 hdvd
  · obtain ⟨P, PD⟩ := exists_planeData hSLB h hEA hF13.noTransvection ht.1 hs.1 htw hsw hts hK
      hKs hmod hpg he1 hetE hI hKI hKsI heP
    exact oddDatum_of_planeData hInsp hOdd hp h.E_elem hcard hF13.noTransvection PD

end CFSG.RankThree.PartOne.K133B
