module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ud

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace F08

@[expose] def R869MCons (D : Data G) : Prop :=
  ∀ L : Subgroup G,
    ((L ∈ calC D.M ∧ D.M ≤ normalizer (L : Set G)) ∨
      ∃ K ∈ calC D.M, ¬ D.M ≤ normalizer (K : Set G) ∧ L = conjClosure D.M K) →
    ¬ Thin8 L → UniqueMax D.M L

end F08

theorem uc22p22u_c117W_of_R869MCons (D : Data G) (h869 : F08.R869MCons D) : R117W D := by
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
    IsSubnormal.step hXM ((Subgroup.normal_subgroupOf_iff_le_normalizer hXM).2 hn)
      (IsSubnormal.refl D.M)
  have A1 : ∀ L : Subgroup G, L ≤ X →
      ((L ∈ calC D.M ∧ D.M ≤ normalizer (L : Set G)) ∨
        ∃ K ∈ calC D.M, ¬ D.M ≤ normalizer (K : Set G) ∧ L = conjClosure D.M K) →
      F08.Thin8 L := by
    intro L hLX hL
    by_contra hnt
    exact hTI (uc22p22u_isTI_of_uniqueMax D hVel hMV (hLX.trans hXC) (h869 L hL hnt))
  intro K hK
  have hKX : K ≤ X := CFSG.Quasithin.A3.subnormal_le hK.1
  have hKM : K ∈ calC D.M := uc22p22u_calC_mono hsub hK
  have hN : D.M ≤ normalizer (K : Set G) := by
    by_contra hnot
    obtain ⟨m, hm, hne⟩ : ∃ m ∈ D.M, uniqueFourConj m K ≠ K := by
      by_contra h
      exact hnot fun m hm => UC6.uniqueFourConj_eq_self_iff.1 (by
        by_contra hne
        exact h ⟨m, hm, hne⟩)
    have hK' := uc22p22u_calC_conj hn hK hm
    have hLX : conjClosure D.M K ≤ X := (uc22p22u_conjClosure_isProd hXM hn hK).1
    have hconj : ∀ m ∈ D.M, uniqueFourConj m K ≤ conjClosure D.M K := fun m hm =>
      le_iSup₂_of_le (f := fun A (_ : A ∈ conjSetOf D.M K) => A) (uniqueFourConj m K)
        ⟨m⁻¹, D.M.inv_mem hm, rfl⟩ le_rfl
    have hKL : K ≤ conjClosure D.M K := by
      have h1 : uniqueFourConj 1 K = K := UC6.uniqueFourConj_eq_self_iff.2 (Subgroup.one_mem _)
      have := hconj 1 D.M.one_mem
      rwa [h1] at this
    exact uc22p22u_not_thin_of_conj hK hK' hne ⟨m, rfl⟩ hKL (hconj m hm) hLX
      (A1 _ hLX (Or.inr ⟨K, hKM, hnot, rfl⟩))
  exact ⟨hN, A1 K hKX (Or.inl ⟨hKM, hN⟩)⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
