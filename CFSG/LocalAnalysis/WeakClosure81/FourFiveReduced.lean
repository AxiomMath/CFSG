module

public import CFSG.LocalAnalysis.WeakClosure81.FourFiveLiftFas
public import CFSG.LocalAnalysis.WeakClosure81.FourFiveIsComp
public import CFSG.LocalAnalysis.WeakClosure81.FourFiveHyp
public import CFSG.LocalAnalysis.WeakClosure81.FourFiveSyl
public import CFSG.Quasithin.Background.RonanE111Mem
public import CFSG.Quasithin.Background.RonanE111Gamma

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.E2.E22N CFSG.Quasithin.Vol2.Ch11.SecB
open CFSG.Quasithin.RonanE111 CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup

theorem fourFive_caseI {G : Type} [Group G] [Finite G] {X T J : Subgroup G} {n : ℕ}
    (hn : 1 ≤ n) (hR : E111Reduced G X T) (hJ : E111R.IsComp X J)
    (hF : fourFiveFAS n (↥(F12.autNL T J) ⧸ (F12.autC T J).subgroupOf (F12.autNL T J)))
    {Ω : Set (Subgroup G)} (hΩ : E1.IsInvColl ⊤ Ω)
    (hA : ∃ A ∈ Ω, A ≤ T ∧
      ¬ A ⊓ Subgroup.normalizer (J : Set G) ≤ Subgroup.centralizer (J : Set G)) :
    J ≤ E1.eGen n ⊤ T Ω ⊔ T := by
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
  have hΓinv : E1.IsInvColl (F12.autNL T J) Γ := by
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
  have hne : ∃ B ∈ Γ, ¬ B ≤ F12.autC T J := by
    obtain ⟨A, hAΩ, hAT, hA⟩ := hA
    refine ⟨A ⊓ Subgroup.normalizer (J : Set G), ?_, ?_⟩
    · exact ⟨A, hAΩ, hAT, 1, (F12.autNL T J).one_mem,
        by rw [CFSG.Quasithin.A1b.conjSub_one]⟩
    · intro hle
      exact hA (hle.trans (by rw [F12.autC]; exact inf_le_right))
  set G₁ : Subgroup G := E1.eGen n ⊤ T Ω ⊔ T with hG₁
  set G₂ : Subgroup G := Cov G₁ J with hG₂
  have hP : ∀ B ∈ Γ, B ≤ T ⊓ Subgroup.normalizer (J : Set G) →
      ¬ B ≤ F12.autC T J → ∀ P : Subgroup G,
      E1.IsE n (F12.autNL T J) (T ⊓ Subgroup.normalizer (J : Set G)) B P →
      twoResidual P ≤ G₂ := by
    intro B hB hBS hBC P hPE
    obtain ⟨A, hAΩ, hAT, g, hg, rfl⟩ := hB
    have hg' : g ∈ J ⊔ (T ⊓ Subgroup.normalizer (J : Set G)) := hHeq ▸ hg
    have hPE' : E1.IsE n (J ⊔ (T ⊓ Subgroup.normalizer (J : Set G)))
        (T ⊓ Subgroup.normalizer (J : Set G))
        (CFSG.Quasithin.A1b.conjSub g (A ⊓ Subgroup.normalizer (J : Set G))) P :=
      hHeq ▸ hPE
    obtain ⟨A'', hA''Ω, hA''T, hP''⟩ := gamma_member hR hJ hΩ hg' hAΩ hAT hBS hPE'
    exact (twoResidual_le P).trans
      (P_le_cov hR hJ hn le_sup_right hA''T (hΩ.isElemAbelian A'' hA''Ω)
        (fun K hK => (E1.le_eGen hA''Ω hA''T hK).trans le_sup_left) hP'')
  have hSG : T ⊓ Subgroup.normalizer (J : Set G) ≤ G₂ :=
    (inf_le_inf_right _ le_sup_right).trans (inf_normalizer_le_Cov G₁ J)
  have hHCov : F12.autNL T J ≤ G₂ :=
    fourFive_le_of_fas hSH hCS hF hΓinv hne hP hSG
  have hJH : J ≤ F12.autNL T J := by
    rw [hHeq]
    exact le_sup_left
  exact le_of_le_Cov hR hJ (exists_involution_of_isComp hJ) le_sup_right (hJH.trans hHCov)

theorem fourFive_reduced_dichotomy {G : Type} [Group G] [Finite G] {X T J : Subgroup G}
    {n : ℕ} (hn : 1 ≤ n) (hR : E111Reduced G X T) (hJ : E111R.IsComp X J)
    (hF : fourFiveFAS n (↥(F12.autNL T J) ⧸ (F12.autC T J).subgroupOf (F12.autNL T J)))
    {Ω : Set (Subgroup G)} (hΩ : E1.IsInvColl ⊤ Ω) :
    J ≤ E1.eGen n ⊤ T Ω ⊔ T ∨ J ≤ Subgroup.normalizer (E1.weakClosure T Ω : Set G) := by
  classical
  by_cases h1 : ∃ A ∈ Ω, A ≤ T ∧
      ¬ A ⊓ Subgroup.normalizer (J : Set G) ≤ Subgroup.centralizer (J : Set G)
  · exact Or.inl (fourFive_caseI hn hR hJ hF hΩ h1)
  · have h1' : ∀ A ∈ Ω, A ≤ T →
        A ⊓ Subgroup.normalizer (J : Set G) ≤ Subgroup.centralizer (J : Set G) := by
      intro A hAΩ hAT
      by_contra h
      exact h1 ⟨A, hAΩ, hAT, h⟩
    by_cases h2 : ∃ A ∈ Ω, A ≤ T ∧ ¬ A ≤ Subgroup.centralizer (J : Set G)
    · obtain ⟨A, hAΩ, hAT, hAS⟩ := h2
      set G₁ : Subgroup G := E1.eGen n ⊤ T Ω ⊔ T with hG₁
      obtain ⟨K, hK, hcov⟩ := exists_member_comp hR hn hAT (hΩ.isElemAbelian A hAΩ) hJ hAS
        (fun h => absurd (h1' A hAΩ hAT) h)
      have hKle : K ≤ G₁ := (E1.le_eGen hAΩ hAT hK).trans le_sup_left
      have hcov' : J ≤ Cov G₁ J := by
        intro x hx
        rw [mem_Cov_iff]
        refine ⟨Subgroup.le_normalizer hx, ?_⟩
        obtain ⟨y, hyK, hyc⟩ := hcov x hx
        exact ⟨y, hKle hyK, hyc⟩
      exact Or.inl (le_of_le_Cov hR hJ (exists_involution_of_isComp hJ) le_sup_right hcov')
    · right
      have h2' : ∀ A ∈ Ω, A ≤ T → A ≤ Subgroup.centralizer (J : Set G) := by
        intro A hAΩ hAT
        by_contra h
        exact h2 ⟨A, hAΩ, hAT, h⟩
      have hWle : E1.weakClosure T Ω ≤ Subgroup.centralizer (J : Set G) := by
        rw [E1.weakClosure]
        refine iSup₂_le fun A hA => iSup_le fun hAT => ?_
        exact h2' A hA hAT
      have hJcent : J ≤ Subgroup.centralizer (E1.weakClosure T Ω : Set G) :=
        Subgroup.le_centralizer_iff.mpr hWle
      exact hJcent.trans (Subgroup.centralizer_le_normalizer (E1.weakClosure T Ω : Set G))

end CFSG.LocalAnalysis.WeakClosure81
