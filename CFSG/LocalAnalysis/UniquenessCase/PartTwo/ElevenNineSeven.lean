module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenNineBasic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenNineEngine

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.CGT.Timmesfeld75 CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

namespace ElevenNine

theorem c117_of_hyp11 (D : Data G) (h869 : F08.R869 D) {V₀ V : Subgroup G}
    (hV : F11.Hyp11 D V₀ V) : C117 D V₀ V := by
  unfold C117
  obtain ⟨hn, hO, hXM⟩ := hyp11_ctilde D hV
  obtain ⟨hVin, hV₀V, hV₀n, -⟩ := uc22p22q_hyp11_unpack D hV
  have hMV : D.M ≤ normalizer (V : Set G) := hVin.2.2.1
  have hVel : IsElemAbelian 2 V := hVin.2.2.2
  have hV₀comm : ∀ a ∈ V₀, ∀ b ∈ V₀, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hVel.1.is_comm.comm ⟨a, hV₀V ha⟩ ⟨b, hV₀V hb⟩)
  have hcard := card_le_four_or_eight_le D hV
  have h8 := not_uniqueMax_of_eight_le D hV
  have hsub : IsSubnormal (F11.CTilde D.M V₀ V) D.M :=
    IsSubnormal.step hXM ((Subgroup.normal_subgroupOf_iff_le_normalizer hXM).2 hn)
      (IsSubnormal.refl D.M)
  have A1 : ∀ K ∈ calC D.M, K ≤ F11.CTilde D.M V₀ V → F08.Thin8 (conjClosure D.M K) := by
    intro K hK hKX
    by_contra hnt
    obtain ⟨hYM, hMY, hprod⟩ :=
      uc22p22u_conjClosure_isProd (M := D.M) (X := D.M) (K := K) le_rfl Subgroup.le_normalizer hK
    have hYV₀ : conjClosure D.M K ≤ centralizer (V₀ : Set G) :=
      le_centralizer_of_not_thin D h869 hV₀n hcard h8 hK rfl hnt
    have hYX : conjClosure D.M K ≤ F11.CTilde D.M V₀ V := conjClosure_le_of_le hn hKX
    have hYV : conjClosure D.M K ≤ centralizer (V : Set G) :=
      le_centralizer_of_perfect_of_sub (conjClosure_isPerfect hK) hV₀comm hYV₀
        (fun l hl v hv => (uc22p22q_mem_ctilde.1 (hYX hl)).2.2 v hv)
    have hN := h869 _ (Or.inr ⟨hYM, hMY, hprod⟩) _ le_rfl
      (sup_eq_left.2 (uc22p21c_pCoreOf_le _)) hnt
    have hU := uc22p22u_uniqueMax_of_calN D hYM hN
    exact hV.2.1 (uc22p22u_isTI_of_uniqueMax D hVel hMV hYV hU)
  intro K hK
  have hKX : K ≤ F11.CTilde D.M V₀ V := CFSG.Quasithin.A3.subnormal_le hK.1
  have hKM : K ∈ calC D.M := uc22p22u_calC_mono hsub hK
  have hKL : K ≤ conjClosure D.M K := TwelveTwentyThree.le_conjClosure D.M K
  have hthin : F08.Thin8 (conjClosure D.M K) := A1 K hKM hKX
  refine ⟨?_, fun p hp hp2 =>
    (CFSG.SectionRank.pRank_mono hp.one_lt hKL).trans (hthin p hp hp2)⟩
  by_contra hnot
  obtain ⟨m, hm, hne⟩ : ∃ m ∈ D.M, uniqueFourConj m K ≠ K := by
    by_contra h
    exact hnot fun m hm => UC6.uniqueFourConj_eq_self_iff.1 (by
      by_contra hne
      exact h ⟨m, hm, hne⟩)
  have hK' := uc22p22u_calC_conj hn hK hm
  have hK'L : uniqueFourConj m K ≤ conjClosure D.M K :=
    le_iSup₂_of_le (f := fun A (_ : A ∈ conjSetOf D.M K) => A) (uniqueFourConj m K)
      ⟨m⁻¹, D.M.inv_mem hm, rfl⟩ le_rfl
  have hLX : conjClosure D.M K ≤ F11.CTilde D.M V₀ V := conjClosure_le_of_le hn hKX
  exact (uc22p22u_not_thin_of_conj hK hK' hne ⟨m, rfl⟩ hKL hK'L hLX) hthin

end ElevenNine

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
