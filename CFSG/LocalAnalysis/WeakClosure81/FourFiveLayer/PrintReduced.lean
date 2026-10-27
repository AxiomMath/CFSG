module

import CFSG.LocalAnalysis.WeakClosure81.FourFiveLayer.PrintLift
import CFSG.LocalAnalysis.WeakClosure81.FourFiveLayer.PrintCover
public import CFSG.LocalAnalysis.WeakClosure81.FourFiveHyp
public import CFSG.LocalAnalysis.WeakClosure81.FourFiveIsComp
public import CFSG.LocalAnalysis.WeakClosure81.FourFiveLiftFas
public import CFSG.LocalAnalysis.WeakClosure81.FourFiveSyl
public import CFSG.Quasithin.Background.RonanE111Cov
public import CFSG.Quasithin.Background.RonanE111Gamma
public import CFSG.Quasithin.Background.RonanE111Gen

public section

namespace CFSG.LocalAnalysis.WeakClosure81.FourFiveLayer

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.E2.E22N CFSG.Quasithin.Vol2.Ch11.SecB
open CFSG.Quasithin.RonanE111 CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup

variable {G : Type} [Group G]

theorem le_eGenP {i : ℕ} {H T A K : Subgroup G} {Ω : Set (Subgroup G)} (hA : A ∈ Ω) (hAT : A ≤ T)
    (hK : F12.IsEP i H T A K) : K ≤ F12.eGenP i H T Ω :=
  le_iSup₂_of_le A hA (le_iSup_of_le hAT (le_iSup₂_of_le K hK le_rfl))

theorem P_le_covP [Finite G] {X T J : Subgroup G} (hR : E111Reduced G X T) (hJ : E111R.IsComp X J)
    {n : ℕ} (hn : 1 ≤ n) {G₁ : Subgroup G} (hTG : T ≤ G₁) {A : Subgroup G} (hAT : A ≤ T)
    (hAab : IsElemAbelian 2 A) (hmem : ∀ K : Subgroup G, F12.IsEP n ⊤ T A K → K ≤ G₁)
    {P : Subgroup G}
    (hP : E1.IsE n (J ⊔ (T ⊓ Subgroup.normalizer (J : Set G)))
      (T ⊓ Subgroup.normalizer (J : Set G)) (A ⊓ Subgroup.normalizer (J : Set G)) P) :
    P ≤ Cov G₁ J := by
  refine P_le_cov_of_diagCoverIn hR hJ hn hTG hAT hAab hmem ?_ hP
  intro Z Zfin h D Y 𝒟 hJD hSylD hmove hrank
  exact (cover_diagP hn h hJD hSylD hmove hrank).trans
    (sup_le hTG (iSup₂_le fun K hK => hmem K hK))

private theorem isInvColl_gamma_redP {T J : Subgroup G} {Ω : Set (Subgroup G)}
    (hΩ : E1.IsInvColl ⊤ Ω)
    (hSle : T ⊓ Subgroup.normalizer (J : Set G) ≤ F12.autNL T J) :
    E1.IsInvColl (F12.autNL T J)
      {B | ∃ A ∈ Ω, A ≤ T ∧ ∃ g ∈ F12.autNL T J,
        B = CFSG.Quasithin.A1b.conjSub g (A ⊓ Subgroup.normalizer (J : Set G))} := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨A, hAΩ, hAT, g, hg, rfl⟩
    intro y hy
    rw [CFSG.Quasithin.A1b.mem_conjSub_iff] at hy
    have hyS : g⁻¹ * y * g ∈ T ⊓ Subgroup.normalizer (J : Set G) := ⟨hAT hy.1, hy.2⟩
    have := (F12.autNL T J).mul_mem
      ((F12.autNL T J).mul_mem hg (hSle hyS)) ((F12.autNL T J).inv_mem hg)
    simpa [mul_assoc] using this
  · rintro _ ⟨A, hAΩ, hAT, g, hg, rfl⟩
    exact CFSG.Quasithin.E2.E22N.E111R.isElemAbelian_of_le
      (CFSG.Open.IsElemAbelian.map (hΩ.isElemAbelian A hAΩ) (MulAut.conj g).toMonoidHom)
      (Subgroup.map_mono inf_le_left)
  · rintro _ ⟨A, hAΩ, hAT, g, hg, rfl⟩ h hh
    exact ⟨A, hAΩ, hAT, h * g, (F12.autNL T J).mul_mem hh hg,
      by rw [CFSG.Quasithin.A1b.conjSub_mul]⟩

private theorem exists_not_le_autC_gamma_redP {T J : Subgroup G} {Ω : Set (Subgroup G)}
    (hA : ∃ A ∈ Ω, A ≤ T ∧
      ¬ A ⊓ Subgroup.normalizer (J : Set G) ≤ Subgroup.centralizer (J : Set G)) :
    ∃ B ∈ {B | ∃ A ∈ Ω, A ≤ T ∧ ∃ g ∈ F12.autNL T J,
        B = CFSG.Quasithin.A1b.conjSub g (A ⊓ Subgroup.normalizer (J : Set G))},
      ¬ B ≤ F12.autC T J := by
  obtain ⟨A, hAΩ, hAT, hA⟩ := hA
  refine ⟨A ⊓ Subgroup.normalizer (J : Set G), ?_, ?_⟩
  · exact ⟨A, hAΩ, hAT, 1, (F12.autNL T J).one_mem,
      by rw [CFSG.Quasithin.A1b.conjSub_one]⟩
  · intro hle
    exact hA (hle.trans (by rw [F12.autC]; exact inf_le_right))

private theorem twoResidual_le_cov_gamma_redP [Finite G] {X T J : Subgroup G} {n : ℕ}
    (hn : 1 ≤ n) (hR : E111Reduced G X T) (hJ : E111R.IsComp X J)
    {Ω : Set (Subgroup G)} (hΩ : E1.IsInvColl ⊤ Ω)
    (hHeq : F12.autNL T J = J ⊔ (T ⊓ Subgroup.normalizer (J : Set G))) :
    ∀ B ∈ {B | ∃ A ∈ Ω, A ≤ T ∧ ∃ g ∈ F12.autNL T J,
        B = CFSG.Quasithin.A1b.conjSub g (A ⊓ Subgroup.normalizer (J : Set G))},
      B ≤ T ⊓ Subgroup.normalizer (J : Set G) → ¬ B ≤ F12.autC T J →
      ∀ P : Subgroup G,
        E1.IsE n (F12.autNL T J) (T ⊓ Subgroup.normalizer (J : Set G)) B P →
        twoResidual P ≤ Cov (F12.eGenP n ⊤ T Ω ⊔ T) J := by
  intro B hB hBS hBC P hPE
  obtain ⟨A, hAΩ, hAT, g, hg, rfl⟩ := hB
  have hg' : g ∈ J ⊔ (T ⊓ Subgroup.normalizer (J : Set G)) := hHeq ▸ hg
  have hPE' : E1.IsE n (J ⊔ (T ⊓ Subgroup.normalizer (J : Set G)))
      (T ⊓ Subgroup.normalizer (J : Set G))
      (CFSG.Quasithin.A1b.conjSub g (A ⊓ Subgroup.normalizer (J : Set G))) P :=
    hHeq ▸ hPE
  obtain ⟨A'', hA''Ω, hA''T, hP''⟩ := gamma_member hR hJ hΩ hg' hAΩ hAT hBS hPE'
  exact (twoResidual_le P).trans
    (P_le_covP hR hJ hn le_sup_right hA''T (hΩ.isElemAbelian A'' hA''Ω)
      (fun K hK => (le_eGenP hA''Ω hA''T hK).trans le_sup_left) hP'')

theorem fourFive_caseIP [Finite G] {X T J : Subgroup G} {n : ℕ} (hn : 1 ≤ n)
    (hR : E111Reduced G X T) (hJ : E111R.IsComp X J)
    (hF : fourFiveFAS n (↥(F12.autNL T J) ⧸ (F12.autC T J).subgroupOf (F12.autNL T J)))
    {Ω : Set (Subgroup G)} (hΩ : E1.IsInvColl ⊤ Ω)
    (hA : ∃ A ∈ Ω, A ≤ T ∧
      ¬ A ⊓ Subgroup.normalizer (J : Set G) ≤ Subgroup.centralizer (J : Set G)) :
    J ≤ F12.eGenP n ⊤ T Ω ⊔ T := by
  classical
  have hT : IsSylowIn 2 T ⊤ := hR.2.2.2.2.2.1
  have hN : FourFiveNMN X := fourFive_nmn_of_reduced hR
  have hJc : IsComponentOf J X := fourFive_isComponentOf_of_isComp hJ
  have hHeq : F12.autNL T J = J ⊔ (T ⊓ Subgroup.normalizer (J : Set G)) := by
    rw [F12.autNL, sup_comm]
  have hSH : IsSylowIn 2 (T ⊓ Subgroup.normalizer (J : Set G)) (F12.autNL T J) :=
    fourFive_sylow_autNL hT hN hJc
  have hCS : F12.autC T J ≤ T ⊓ Subgroup.normalizer (J : Set G) :=
    fourFive_autC_le hT hN hJc
  have hSle : T ⊓ Subgroup.normalizer (J : Set G) ≤ F12.autNL T J := by
    rw [hHeq]
    exact le_sup_right
  set Γ : Set (Subgroup G) := {B | ∃ A ∈ Ω, A ≤ T ∧ ∃ g ∈ F12.autNL T J,
    B = CFSG.Quasithin.A1b.conjSub g (A ⊓ Subgroup.normalizer (J : Set G))} with hΓ
  have hΓinv : E1.IsInvColl (F12.autNL T J) Γ := isInvColl_gamma_redP hΩ hSle
  have hne : ∃ B ∈ Γ, ¬ B ≤ F12.autC T J := exists_not_le_autC_gamma_redP hA
  set G₁ : Subgroup G := F12.eGenP n ⊤ T Ω ⊔ T with hG₁
  set G₂ : Subgroup G := Cov G₁ J with hG₂
  have hP : ∀ B ∈ Γ, B ≤ T ⊓ Subgroup.normalizer (J : Set G) →
      ¬ B ≤ F12.autC T J → ∀ P : Subgroup G,
      E1.IsE n (F12.autNL T J) (T ⊓ Subgroup.normalizer (J : Set G)) B P →
      twoResidual P ≤ G₂ :=
    twoResidual_le_cov_gamma_redP hn hR hJ hΩ hHeq
  have hSG : T ⊓ Subgroup.normalizer (J : Set G) ≤ G₂ :=
    (inf_le_inf_right _ le_sup_right).trans (inf_normalizer_le_Cov G₁ J)
  have hHCov : F12.autNL T J ≤ G₂ :=
    fourFive_le_of_fas hSH hCS hF hΓinv hne hP hSG
  have hJH : J ≤ F12.autNL T J := by
    rw [hHeq]
    exact le_sup_left
  exact le_of_le_Cov hR hJ (exists_involution_of_isComp hJ) le_sup_right (hJH.trans hHCov)

private theorem le_eGenP_sup_of_le_centralizer_redP [Finite G] {X T J : Subgroup G} {n : ℕ}
    (hn : 1 ≤ n) (hR : E111Reduced G X T) (hJ : E111R.IsComp X J)
    {Ω : Set (Subgroup G)} {A : Subgroup G} (hAΩ : A ∈ Ω) (hAT : A ≤ T)
    (hAab : IsElemAbelian 2 A) (hAS : ¬ A ≤ Subgroup.centralizer (J : Set G))
    (h1' : A ⊓ Subgroup.normalizer (J : Set G) ≤ Subgroup.centralizer (J : Set G)) :
    J ≤ F12.eGenP n ⊤ T Ω ⊔ T := by
  classical
  set G₁ : Subgroup G := F12.eGenP n ⊤ T Ω ⊔ T with hG₁
  obtain ⟨K, hK, hcov⟩ := exists_memberP_comp hR hn hAT hAab hJ hAS
    (fun h => absurd h1' h)
  have hKle : K ≤ G₁ := (le_eGenP hAΩ hAT hK).trans le_sup_left
  have hcov' : J ≤ Cov G₁ J := by
    intro x hx
    rw [mem_Cov_iff]
    refine ⟨Subgroup.le_normalizer hx, ?_⟩
    obtain ⟨y, hyK, hyc⟩ := hcov x hx
    exact ⟨y, hKle hyK, hyc⟩
  exact le_of_le_Cov hR hJ (exists_involution_of_isComp hJ) le_sup_right hcov'

theorem fourFive_le_of_not_centralizerP [Finite G] {X T J : Subgroup G} {n : ℕ} (hn : 1 ≤ n)
    (hR : E111Reduced G X T) (hJ : E111R.IsComp X J)
    (hF : fourFiveFAS n (↥(F12.autNL T J) ⧸ (F12.autC T J).subgroupOf (F12.autNL T J)))
    {Ω : Set (Subgroup G)} (hΩ : E1.IsInvColl ⊤ Ω)
    (hA : ∃ A ∈ Ω, A ≤ T ∧ ¬ A ≤ Subgroup.centralizer (J : Set G)) :
    J ≤ F12.eGenP n ⊤ T Ω ⊔ T := by
  classical
  by_cases h1 : ∃ A ∈ Ω, A ≤ T ∧
      ¬ A ⊓ Subgroup.normalizer (J : Set G) ≤ Subgroup.centralizer (J : Set G)
  · exact fourFive_caseIP hn hR hJ hF hΩ h1
  · have h1' : ∀ A ∈ Ω, A ≤ T →
        A ⊓ Subgroup.normalizer (J : Set G) ≤ Subgroup.centralizer (J : Set G) := by
      intro A hAΩ hAT
      by_contra h
      exact h1 ⟨A, hAΩ, hAT, h⟩
    obtain ⟨A, hAΩ, hAT, hAS⟩ := hA
    exact le_eGenP_sup_of_le_centralizer_redP hn hR hJ hAΩ hAT
      (hΩ.isElemAbelian A hAΩ) hAS (h1' A hAΩ hAT)

end CFSG.LocalAnalysis.WeakClosure81.FourFiveLayer
