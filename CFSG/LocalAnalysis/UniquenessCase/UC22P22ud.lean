module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22uc
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22u
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ua

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] [Finite G]

@[expose] def C117 (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ K ∈ calC (F11.CTilde D.M V₀ V), D.M ≤ normalizer (K : Set G) ∧ F08.Thin8 K

@[expose] def R117W (D : Data G) : Prop := ∀ V : Subgroup G, F11.Hyp11 D ⊥ V → C117 D ⊥ V

theorem uc22p22u_c117W (D : Data G) (h869 : F08.R869 D) : R117W D := by
  intro V hV
  unfold C117
  obtain ⟨hW, hTI⟩ := uc22p22u_hyp11_W D hV
  have hVc := uc22p22u_cTilde_bot D.M V
  have hMV : D.M ≤ normalizer (V : Set G) := hW.1.1.2.2.1
  have hVel : IsElemAbelian 2 V := hW.1.1.2.2.2
  generalize hX : F11.CTilde D.M ⊥ V = X at hVc ⊢
  have hXM : X ≤ D.M := by rw [hVc]; exact inf_le_left
  have hXC : X ≤ centralizer (V : Set G) := by rw [hVc]; exact inf_le_right
  have hn : D.M ≤ normalizer (X : Set G) := by rw [hVc]; exact uc22p22u_normalizes_cent hMV
  have hsub : IsSubnormal X D.M :=
    IsSubnormal.step hXM ((Subgroup.normal_subgroupOf_iff_le_normalizer hXM).2 hn) (IsSubnormal.refl D.M)
  have A1 : ∀ L : Subgroup G, L ≤ X →
      (L ∈ calC D.M ∨ (L ≤ D.M ∧ D.M ≤ normalizer (L : Set G) ∧ F08.IsProdOfCalC D.M L)) →
      F08.Thin8 L := by
    intro L hLX hL
    by_contra hnt
    have hLM : L ≤ D.M := hLX.trans hXM
    have hN := h869 L hL L le_rfl (sup_eq_left.2 (uc22p21c_pCoreOf_le L)) hnt
    have hU := uc22p22u_uniqueMax_of_calN D hLM hN
    exact hTI (uc22p22u_isTI_of_uniqueMax D hVel hMV (hLX.trans hXC) hU)
  intro K hK
  have hKX : K ≤ X := CFSG.Quasithin.A3.subnormal_le hK.1
  refine ⟨?_, A1 K hKX (Or.inl (uc22p22u_calC_mono hsub hK))⟩
  by_contra hnot
  obtain ⟨m, hm, hne⟩ : ∃ m ∈ D.M, uniqueFourConj m K ≠ K := by
    by_contra h
    exact hnot fun m hm => UC6.uniqueFourConj_eq_self_iff.1 (by
      by_contra hne
      exact h ⟨m, hm, hne⟩)
  have hK' := uc22p22u_calC_conj hn hK hm
  obtain ⟨L, hLX, hLn, hLprod, hconj⟩ := uc22p22u_exists_prod_conj hXM hn hK
  have hKL : K ≤ L := by
    have h1 : uniqueFourConj 1 K = K := UC6.uniqueFourConj_eq_self_iff.2 (Subgroup.one_mem _)
    have := hconj 1 D.M.one_mem
    rwa [h1] at this
  have hnt := uc22p22u_not_thin_of_conj hK hK' hne ⟨m, rfl⟩ hKL (hconj m hm) hLX
  exact hnt (A1 L hLX (Or.inr ⟨hLX.trans hXM, hLn, hLprod⟩))

end CFSG.LocalAnalysis.UniquenessCase.UC22
