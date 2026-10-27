module

public import CFSG.LocalAnalysis.StandardType.GGFamOuterDFour
public import CFSG.LocalAnalysis.StandardType.GGFamLabelD4TwE6
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoRatLabelDStrict
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabelOuterD

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp CFSG.RankThree.Lattice
  CFSG.RankThree.PartOne.KE

theorem fam_label_d4_selected
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (i : KernelComponent χ)
    (b : Fin τ.rank → Lˣ) (j : KernelComponent (rootCharHom b))
    (hsel : componentRoots (rootCharHom b) j = componentRoots χ i)
    (v : WeylGroup τ)
    (hpin : componentRoots χ i =
      (fun α => v • α) '' parabolicRoots τ (d4Nodes τ))
    (hρΨ : ∀ γ ∈ componentRoots χ i, S.ρ γ ∈ componentRoots χ i)
    (hout : ¬ twistInner (componentRoots χ i) (S.ρ : (Fin τ.rank → ℤ) → _)) :
    ∃ f : ℕ, ringChar L ^ f = S.D.q ∧
      ((twistInner (componentRoots χ i)
          ((S.ρ : (Fin τ.rank → ℤ) → _)^[2]) ∧
        LieModel (↥(rationalComponentM S.ρ S.Γ χ i) ⧸
          Subgroup.center ↥(rationalComponentM S.ρ S.Γ χ i)) .POmegaMinus 4 (ringChar L) f) ∨
       (¬ twistInner (componentRoots χ i)
          ((S.ρ : (Fin τ.rank → ℤ) → _)^[2]) ∧
        LieModel (↥(rationalComponentM S.ρ S.Γ χ i) ⧸
          Subgroup.center ↥(rationalComponentM S.ρ S.Γ χ i)) .trialityD4 0 (ringChar L) f)) := by
  classical
  have hpinb : componentRoots (rootCharHom b) j =
      (fun α => v • α) '' parabolicRoots τ (d4Nodes τ) := by
    rw [hsel]; exact hpin
  have hρb : ∀ γ ∈ componentRoots (rootCharHom b) j,
      S.ρ γ ∈ componentRoots (rootCharHom b) j := by
    intro γ hγ
    rw [hsel] at hγ ⊢
    exact hρΨ γ hγ
  have houtb : ¬ twistInner (componentRoots (rootCharHom b) j)
      (S.ρ : (Fin τ.rank → ℤ) → _) := by
    rw [← hsel] at hout
    exact hout
  have hcomp : rationalComponent S.ρ S.Γ (rootCharHom b) j =
      rationalComponentM S.ρ S.Γ χ i :=
    (rationalComponentM_eq S.ρ S.Γ (rootCharHom b) j).symm.trans
      (rationalComponentM_eq_of_componentRoots_eq (ρ := S.ρ) (Γ := S.Γ)
        (χ := rootCharHom b) (χ' := χ) (i := j) (j := i) hsel)
  have hs_b : componentOrbitLength S.ρ (componentRoots (rootCharHom b) j) = 1 :=
    componentOrbitLength_eq_one
      ((finite_setOf_isRoot τ).subset fun γ hγ => hγ.1.1) hρb
  have h1b : ¬ twistInner (componentRoots (rootCharHom b) j)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom b) j)]) := by
    rw [hs_b, Function.iterate_one]
    exact houtb
  by_cases hsq : twistInner (componentRoots (rootCharHom b) j)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[2])
  ·
    rcases hτ with rfl | rfl | rfl
    ·
      obtain ⟨w, hn⟩ := S.D.n_weyl
      obtain ⟨Fr, hFr, P, hP, hΦ⟩ := S.D.steinberg
      rcases hP with rfl | ⟨t, ht, rfl⟩
      · have hΦ' : S.D.Φ = Units.map (entrywiseHom Fr) := by
          ext1 g
          rw [hΦ, one_mul, inv_one, mul_one]
        obtain ⟨f, hf, hM⟩ :=
          CFSG.StandardType.TablePThreeKG.e6TwoRatLabelD_strict_rationalComponent_of_d4_outer
            d4Base_E6 (d4SwapLayer_E6 e6FixDNAll_proved)
            CFSG.StandardType.TablePThreeKG.e6TwoRatLabelD_strict_swapLayer_E6 S hFr hΦ' hn
            (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ' hn hγ) j v hpinb hρb h1b hsq
        exact ⟨f, hf, Or.inl ⟨by simpa only [hsel] using hsq,
          by rw [hcomp] at hM
             simpa only [CFSG.StandardType.TablePThreeKG.e6TwoRatLabelD_StrictModel] using hM⟩⟩
      · obtain ⟨f, hf, hM⟩ :=
          CFSG.StandardType.TablePThreeKG.e6TwoRatLabelD_strict_rationalComponent_of_d4_twE6 S
            ⟨t, ht, Fr, hFr, hΦ⟩ j v hpinb hρb houtb hsq
        exact ⟨f, hf, Or.inl ⟨by simpa only [hsel] using hsq,
          by rw [hcomp] at hM
             simpa only [CFSG.StandardType.TablePThreeKG.e6TwoRatLabelD_StrictModel] using hM⟩⟩
    ·
      obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted twistTag_tag_ne_E7
      obtain ⟨w, hn⟩ := S.D.n_weyl
      obtain ⟨f, hf, hM⟩ :=
        CFSG.StandardType.TablePThreeKG.e6TwoRatLabelD_strict_rationalComponent_of_d4_outer
          d4Base_E7 (d4SwapLayer_E7 e6FixDNAll_proved)
          CFSG.StandardType.TablePThreeKG.e6TwoRatLabelD_strict_swapLayer_E7 S hFr hΦ hn
          (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ hn hγ) j v hpinb hρb h1b hsq
      exact ⟨f, hf, Or.inl ⟨by simpa only [hsel] using hsq,
        by rw [hcomp] at hM
           simpa only [CFSG.StandardType.TablePThreeKG.e6TwoRatLabelD_StrictModel] using hM⟩⟩
    ·
      obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted twistTag_tag_ne_E8
      obtain ⟨w, hn⟩ := S.D.n_weyl
      obtain ⟨f, hf, hM⟩ :=
        CFSG.StandardType.TablePThreeKG.e6TwoRatLabelD_strict_rationalComponent_of_d4_outer
          d4Base_E8 (d4SwapLayer_E8 e6FixDNAll_proved)
          CFSG.StandardType.TablePThreeKG.e6TwoRatLabelD_strict_swapLayer_E8 S hFr hΦ hn
          (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ hn hγ) j v hpinb hρb h1b hsq
      exact ⟨f, hf, Or.inl ⟨by simpa only [hsel] using hsq,
        by rw [hcomp] at hM
           simpa only [CFSG.StandardType.TablePThreeKG.e6TwoRatLabelD_StrictModel] using hM⟩⟩
  ·
    have h2b : ¬ twistInner (componentRoots (rootCharHom b) j)
        ((S.ρ : (Fin τ.rank → ℤ) → _)^[2 * componentOrbitLength S.ρ
          (componentRoots (rootCharHom b) j)]) := by
      simpa only [hs_b, mul_one] using hsq
    rcases hτ with rfl | rfl | rfl
    ·
      obtain ⟨w, hn⟩ := S.D.n_weyl
      obtain ⟨Fr, hFr, P, hP, hΦ⟩ := S.D.steinberg
      rcases hP with rfl | ⟨t, ht, rfl⟩
      · have hΦ' : S.D.Φ = Units.map (entrywiseHom Fr) := by
          ext1 g
          rw [hΦ, one_mul, inv_one, mul_one]
        obtain ⟨f, hf, hM⟩ :=
          CFSG.StandardType.TablePThreeKG.lieModel_rationalComponent_of_d4_triality d4Base_E6
            d4TrialityLayer_E6 S hFr hΦ' hn
            (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ' hn hγ) j v hpinb hρb h1b h2b
        exact ⟨f, hf, Or.inr ⟨by simpa only [hsel] using hsq,
          by rw [hcomp] at hM; exact hM⟩⟩
      · obtain ⟨f, hf, hM⟩ :=
          lieModel_rationalComponent_of_d4_twE6_triality S ⟨t, ht, Fr, hFr, hΦ⟩ j v hpinb hρb
            houtb hsq
        exact ⟨f, hf, Or.inr ⟨by simpa only [hsel] using hsq,
          by rw [hcomp] at hM; exact hM⟩⟩
    ·
      obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted twistTag_tag_ne_E7
      obtain ⟨w, hn⟩ := S.D.n_weyl
      obtain ⟨f, hf, hM⟩ :=
        CFSG.StandardType.TablePThreeKG.lieModel_rationalComponent_of_d4_triality d4Base_E7
          CFSG.RankThree.PartOne.KD4L.d4TrialityLayer_E7 S hFr hΦ hn
          (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ hn hγ) j v hpinb hρb h1b h2b
      exact ⟨f, hf, Or.inr ⟨by simpa only [hsel] using hsq,
        by rw [hcomp] at hM; exact hM⟩⟩
    ·
      obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted twistTag_tag_ne_E8
      obtain ⟨w, hn⟩ := S.D.n_weyl
      obtain ⟨f, hf, hM⟩ :=
        CFSG.StandardType.TablePThreeKG.lieModel_rationalComponent_of_d4_triality d4Base_E8
          CFSG.RankThree.PartOne.KD4L.d4TrialityLayer_E8 S hFr hΦ hn
          (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ hn hγ) j v hpinb hρb h1b h2b
      exact ⟨f, hf, Or.inr ⟨by simpa only [hsel] using hsq,
        by rw [hcomp] at hM; exact hM⟩⟩


end CFSG.StandardType.TableCRes

end
