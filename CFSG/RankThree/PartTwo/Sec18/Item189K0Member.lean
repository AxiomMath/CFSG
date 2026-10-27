module

public import CFSG.RankThree.PartTwo.Sec18.Item189K0Centralizes
public import CFSG.GroupTheory.ABGLocalTools.Constraint
public import CFSG.RankThree.PartTwo.KFacts.KS44OutSz
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.LayerOfNotConstrained
import CFSG.RankThree.PartTwo.Sec4.T444.Step450
import CFSG.RankThree.PartTwo.Sec6.Item65Tools
import CFSG.RankThree.PartTwo.Sec10.Item1012Res2ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G] {A B X M : Subgroup G} {c : G}

section Exists


theorem exists_mem_thetaComponentsIn_three_dvd (hSz : KFacts.KPSz) (hM : SectionFourHyp ↥M)
    (hnc : ¬ CFSG.ABGLocalTools.IsPConstrained 3 ↥M) :
    ∃ K ∈ thetaComponentsIn M, 3 ∣ Nat.card K := by
  have hlay : CFSG.layer (↥M ⧸ CFSG.pPrimeCore 3 ↥M) ≠ ⊥ :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.layer_ne_bot_of_not_isPConstrained hnc
  obtain ⟨J, hJ⟩ : ∃ J : Subgroup (↥M ⧸ CFSG.pPrimeCore 3 ↥M), CFSG.IsComponent J := by
    by_contra hcon
    apply hlay
    have he : {K : Subgroup (↥M ⧸ CFSG.pPrimeCore 3 ↥M) | CFSG.IsComponent K} = ∅ := by
      ext K
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hK => hcon ⟨K, hK⟩
    rw [CFSG.layer.eq_sSup, he, sSup_empty]
  obtain ⟨L, hL, hLJ⟩ := Sec4.exists_mem_thetaComponents_map_eq hSz hM.kGroup
    (Sec4.localRank_theta_quotient_le hM) hJ
  have hX : CFSG.pPrimeCore 3 (↥M ⧸ CFSG.pPrimeCore 3 ↥M) = ⊥ :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.pPrimeCore_three_quotient_eq_bot ↥M
  have h3J : 3 ∣ Nat.card J := Sec4.three_dvd_card_of_isComponent hX hJ
  have hJL : Nat.card J ∣ Nat.card L := by
    rw [← hLJ]
    exact Subgroup.card_map_dvd _ _
  have hmem : L.map M.subtype ∈ thetaComponentsIn M := Set.mem_image_of_mem _ hL
  refine ⟨L.map M.subtype, hmem, ?_⟩
  rw [Subgroup.card_map_of_injective M.subtype_injective]
  exact h3J.trans hJL

end Exists

private theorem exists_three_noncentral {K : Subgroup G} (hK : K ∈ thetaComponentsIn M)
    (h3 : 3 ∣ Nat.card K) :
    ∃ e ∈ imM M K, e ^ 3 = 1 ∧ ∃ g ∈ imM M K, g * e ≠ e * g := by
  obtain ⟨e, he3, hec⟩ :=
    Sec6.exists_pow_three_eq_one_not_mem_center (imM_isPerfect hK) (three_dvd_card_imM hK h3)
  refine ⟨(e : ↥M ⧸ aschbacherSolvableCore 3 ↥M), e.2, ?_, ?_⟩
  · rw [← Subgroup.coe_pow, he3, Subgroup.coe_one]
  · by_contra hcon
    push Not at hcon
    apply hec
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcon g.1 g.2)

theorem K0Setting.eq_of_three_dvd (h45 : Sec4.Item4_5) (h : K0Setting G A B X M c)
    {K₁ K₂ : Subgroup G} (hK₁ : K₁ ∈ thetaComponentsIn M) (hK₂ : K₂ ∈ thetaComponentsIn M)
    (h₁ : 3 ∣ Nat.card K₁) (h₂ : 3 ∣ Nat.card K₂) : K₁ = K₂ := by
  by_contra hne
  have hBM : B ≤ M := h.le_A.trans h.hAM
  have hBe : CFSG.Open.IsElemAbelian 3 (imM M B) := imM_isElemAbelian hBM h.isElemAbelian_B
  have hB9 : Nat.card (imM M B) = 9 := by
    rw [imM_card_eq_of_isPGroup hBM h.isElemAbelian_B.isPGroup, h.plane.card_plane]
  have hB₁ : B ≤ Sec4.thetaQuotCentralizer K₁ := h.le_thetaQuotCentralizer h45 hK₁
  have hB₂ : B ≤ Sec4.thetaQuotCentralizer K₂ := h.le_thetaQuotCentralizer h45 hK₂
  have hc12 : ∀ x ∈ imM M K₁, ∀ y ∈ imM M K₂, x * y = y * x := imM_commute_of_ne hK₁ hK₂ hne
  have hcB₁ : ∀ x ∈ imM M B, ∀ y ∈ imM M K₁, x * y = y * x :=
    imM_commute_of_le_thetaQuotCentralizer hK₁ hBM hB₁
  have hcB₂ : ∀ x ∈ imM M B, ∀ y ∈ imM M K₂, x * y = y * x :=
    imM_commute_of_le_thetaQuotCentralizer hK₂ hBM hB₂
  obtain ⟨e₁, he₁, he₁3, g₁, hg₁, hg₁e⟩ := exists_three_noncentral hK₁ h₁
  obtain ⟨e₂, he₂, he₂3, g₂, hg₂, hg₂e⟩ := exists_three_noncentral hK₂ h₂
  have he₁B : e₁ ∉ imM M B := fun hmem => hg₁e (hcB₁ e₁ hmem g₁ hg₁).symm
  have hce₁ : ∀ x ∈ imM M B, x * e₁ = e₁ * x := fun x hx => hcB₁ x hx e₁ he₁
  obtain ⟨hP₁, hP₁card⟩ := isElemAbelian_zpowers_sup hBe he₁3 hce₁ he₁B
  rw [hB9] at hP₁card
  have h3z : e₁ ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, he₁3]
  have he₂P : e₂ ∉ Subgroup.zpowers e₁ ⊔ imM M B := by
    intro hmem
    have hcenB : e₁ ∈ Subgroup.centralizer (imM M B : Set (↥M ⧸ aschbacherSolvableCore 3 ↥M)) :=
      Subgroup.mem_centralizer_iff.mpr fun x hx => hce₁ x hx
    have hle : Subgroup.zpowers e₁ ≤
        Subgroup.normalizer (imM M B : Set (↥M ⧸ aschbacherSolvableCore 3 ↥M)) :=
      Subgroup.zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ hcenB)
    have hmem' : e₂ ∈ (↑(Subgroup.zpowers e₁ ⊔ imM M B) :
        Set (↥M ⧸ aschbacherSolvableCore 3 ↥M)) := hmem
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle, Set.mem_mul] at hmem'
    obtain ⟨y, hy, b, hb, hyb⟩ := hmem'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hcomm2 : Commute g₁ e₂ := hc12 g₁ hg₁ e₂ he₂
    have hbg : Commute b g₁ := hcB₁ b hb g₁ hg₁
    have hyg : Commute g₁ (e₁ ^ k) := by
      have h1 : Commute g₁ (e₁ ^ k * b) := by
        rw [hyb]
        exact hcomm2
      have h2 := h1.mul_right hbg.symm.inv_right
      rwa [mul_inv_cancel_right] at h2
    by_cases hk3 : (3 : ℤ) ∣ k
    ·
      obtain ⟨m, rfl⟩ := hk3
      have h1 : e₁ ^ (3 * m) = 1 := by
        rw [zpow_mul, h3z, one_zpow]
      rw [h1, one_mul] at hyb
      have he₂B : e₂ ∈ imM M B := by
        rw [← hyb]
        exact hb
      exact hg₂e (hcB₂ e₂ he₂B g₂ hg₂).symm
    ·
      exfalso
      obtain ⟨u, v, huv⟩ := (Int.prime_three.irreducible.coprime_iff_not_dvd.mpr hk3).symm
      have hexp : k * u + 3 * v = 1 := by linear_combination huv
      have he : e₁ = (e₁ ^ k) ^ u := by
        calc e₁ = e₁ ^ (k * u + 3 * v) := by rw [hexp, zpow_one]
          _ = (e₁ ^ k) ^ u * (e₁ ^ (3 : ℤ)) ^ v := by rw [zpow_add, zpow_mul, zpow_mul]
          _ = (e₁ ^ k) ^ u := by rw [h3z, one_zpow, mul_one]
      have hcomm : Commute e₁ g₁ := by
        rw [he]
        exact (hyg.zpow_right u).symm
      exact hg₁e hcomm.eq.symm
  have hce₂ : ∀ x ∈ Subgroup.zpowers e₁ ⊔ imM M B, x * e₂ = e₂ * x := by
    have hT : Subgroup.zpowers e₁ ⊔ imM M B ≤
        Subgroup.centralizer ({e₂} : Set (↥M ⧸ aschbacherSolvableCore 3 ↥M)) := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) ?_
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hc12 e₁ he₁ e₂ he₂)
      · intro b hb
        exact Subgroup.mem_centralizer_singleton_iff.mpr (hcB₂ b hb e₂ he₂)
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp (hT hx)
  obtain ⟨hE, hEcard⟩ := isElemAbelian_zpowers_sup hP₁ he₂3 hce₂ he₂P
  have hle27 := h.card_le_of_isElemAbelian_quot hE
  rw [hP₁card] at hEcard
  omega

theorem le_normalizer_of_unique {K₀ : Subgroup G} (hK₀ : K₀ ∈ thetaComponentsIn M)
    (huniq : ∀ K ∈ thetaComponentsIn M, 3 ∣ Nat.card K → K = K₀) (h3 : 3 ∣ Nat.card K₀) :
    M ≤ Subgroup.normalizer (K₀ : Set G) := by
  intro m hm
  have hmem := Sec10.Item1012Res2Proof.conj_mem_thetaComponentsIn hK₀ hm
  have hcard : Nat.card (K₀.map (MulAut.conj m).toMonoidHom) = Nat.card K₀ :=
    Subgroup.card_map_of_injective (MulAut.conj m).injective
  have heq : K₀.map (MulAut.conj m).toMonoidHom = K₀ :=
    huniq _ hmem (by rw [hcard]; exact h3)
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq

end CFSG.RankThree.PartTwo.Sec18
