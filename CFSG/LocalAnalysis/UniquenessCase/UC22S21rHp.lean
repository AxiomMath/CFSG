module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU3Sig1
import CFSG.GroupTheory.PRankLeOfSylowLe
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.SylowProduct
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KHupGeFive
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rN

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22s21rhp_not_isSolvable (D : Data G) (hSg : UC6S846.SigmaStd D) (h61 : UC6.R6_1 D)
    {H₁ H₂ : Subgroup G} (hH₁ : H₁ ∈ hSet D.T D.M) (hH₂ : H₂ ∈ hSet D.T D.M)
    (hfM : Group.IsSolvable ↥D.M →
      (D.M : Set G) = ((H₁ ⊓ D.M : Subgroup G) : Set G) * ((H₂ ⊓ D.M : Subgroup G) : Set G)) :
    ¬ Group.IsSolvable ↥D.M := by
  intro hs
  obtain ⟨p, hp⟩ := hSg.nonempty
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have : Fact p.Prime := ⟨hpp⟩
  have hfac : ∀ m ∈ D.M, ∃ a ∈ H₁ ⊓ D.M, ∃ b ∈ H₂ ⊓ D.M, m = a * b := by
    intro m hm
    have hm' : m ∈ ((H₁ ⊓ D.M : Subgroup G) : Set G) * ((H₂ ⊓ D.M : Subgroup G) : Set G) := by
      rw [← hfM hs]
      exact hm
    obtain ⟨a, ha, b, hb, hab⟩ := hm'
    exact ⟨a, ha, b, hb, hab.symm⟩
  obtain ⟨W, hWM, hWp, hWidx, hWfac⟩ :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.exists_sylow_eq_mul_of_mul (p := p)
      (inf_le_right : H₁ ⊓ D.M ≤ D.M) (inf_le_right : H₂ ⊓ D.M ≤ D.M) hfac
  have hcyc : ∀ {H : Subgroup G}, H ∈ hSet D.T D.M → IsCyclic ↥(W ⊓ (H ⊓ D.M)) := by
    intro H hH
    by_contra hnc
    have hle : W ⊓ (H ⊓ D.M) ≤ D.M := inf_le_left.trans hWM
    exact uc22s21rn_not_le_of_uniqueMax D hH (h61 p hp _ hle (hWp.to_inf_left) hnc)
      (inf_le_right.trans inf_le_left)
  have hrank : CFSG.Open.pRank p W ≤ 2 :=
    CFSG.LocalAnalysis.RankThreeUC.S15.kHupAt_odd hpp hp2 G W (W ⊓ (H₁ ⊓ D.M))
      (W ⊓ (H₂ ⊓ D.M)) hWp inf_le_left inf_le_left (hcyc hH₁) (hcyc hH₂) hWfac
  have hWp' : IsPGroup p ↥(W.subgroupOf D.M) := hWp.comap_subtype
  have hsyl : CFSG.ABGLocalTools.IsSylowOf p W D.M := by
    refine ⟨hWp'.toSylow hWidx, ?_⟩
    rw [IsPGroup.toSylow_coe, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hWM]
  have hle := CFSG.pRank_le_of_isSylowOf_le hpp hWM hsyl le_rfl
  have h3 := hSg.three_le p hp
  omega

theorem uc22s21rhp_sig_eq_sig1 (D : Data G) (hSg : UC6S846.SigmaStd D) (h61 : UC6.R6_1 D)
    {H₁ H₂ : Subgroup G} (hH₁ : H₁ ∈ hSet D.T D.M) (hH₂ : H₂ ∈ hSet D.T D.M)
    (hfX : ∀ X : Subgroup G, X ≤ D.M → D.T ≤ X →
      (F12.InF 1 (⊤ : Subgroup (Bar2 X)) ∨ Group.IsSolvable ↥X) →
      (X : Set G) = ((H₁ ⊓ X : Subgroup G) : Set G) * ((H₂ ⊓ X : Subgroup G) : Set G)) :
    D.sig = D.sig1 := by
  have hns := uc22s21rhp_not_isSolvable D hSg h61 hH₁ hH₂
    (fun hs => hfX D.M le_rfl D.sylowM.le (Or.inr hs))
  refine Set.Subset.antisymm (UC6S846.sig_subset_sig1 hSg hns) fun p hp => ?_
  rw [D.sig_sub]
  exact Or.inl (Or.inl hp)

theorem s21_22Sig1_holds (D : Data G) (Ch : Choice2011 G) (hSg : UC6S846.SigmaStd D)
    (h61 : UC6.R6_1 D) : S21_22Sig1 D Ch :=
  fun _ _ _ hH₁ _ hH₂ _ hfX _ => uc22s21rhp_sig_eq_sig1 D hSg h61 hH₁ hH₂ hfX

theorem s21_22U3_holds (D : Data G) (Ch : Choice2011 G) (st : Standing22 D)
    (h2118 : S21_18 D Ch) (h211 : S21_1 D Ch) : S21_22U3 D Ch :=
  s21_22U3_of_s21_22Sig1 D Ch st h2118 h211 (s21_22Sig1_holds D Ch st.sigmaStd st.r6_1)

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
