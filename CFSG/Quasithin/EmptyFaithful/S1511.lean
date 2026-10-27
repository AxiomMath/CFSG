module

public import CFSG.Quasithin.EmptyFaithful.S151Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem lemma_15_1_1_one {T Mc M : Subgroup G} (h : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M)
    {H : Subgroup G} (hH : IsHStar T M H) :
    Hyp315Base T M (M ⊓ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (VZ T M : Set G) : Subgroup G) : Set G)) H (VZ T M) ∧
      Hyp315.CaseII M H (VZ T M) := by
  obtain ⟨S, rfl⟩ := h.exists_sylow
  have hmax : IsOrdMaximalIn (S : Subgroup G) (InM (S : Subgroup G)) M := hM.1
  obtain ⟨⟨hpc, -⟩, hred, -, -⟩ := A57.main h.qtke.2.1 S hmax (Or.inl rfl)
  have hSM : (S : Subgroup G) ≤ M := hM.1.1.2
  have hVn := le_normalizer_VZ (S : Subgroup G) M
  exact ⟨⟨le_inf hSM (le_normalizer_inf_centralizer' Subgroup.le_normalizer (hSM.trans hVn)),
    inf_le_left, hH, hred, hpc⟩, inf_le_right.trans hVn⟩

theorem lemma_15_1_1_two (h316 : Theorem316Statement) {T Mc M : Subgroup G}
    (h : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M) :
    qhatOn M (VZ T M) ≤ 2 ∧ (2 < qOn M (VZ T M) → qhatOn M (VZ T M) < 2) := by
  obtain ⟨S, rfl⟩ := h.exists_sylow
  have hMT : InM (S : Subgroup G) M := hM.1.1
  have hW := isElemAbelian_VZ h hMT
  obtain ⟨H, hH⟩ := exists_isHStar h.inM_mc hMT (Ne.symm hM.2.1)
  obtain ⟨hbase, hII⟩ := lemma_15_1_1_one h hM hH
  have hmax : IsOrdMaximalIn (S : Subgroup G) (InM (S : Subgroup G)) M := hM.1
  obtain ⟨-, -, hauto, huniq⟩ := A57.main h.qtke.2.1 S hmax (Or.inl rfl)
  set M₀ : Subgroup G := M ⊓ Subgroup.normalizer
    (((S : Subgroup G) ⊓ Subgroup.centralizer (VZ (S : Subgroup G) M : Set G) : Subgroup G) :
      Set G) with hM₀
  have hyp : Hyp315 (S : Subgroup G) M M₀ H (VZ (S : Subgroup G) M) :=
    { toHyp315Base := hbase, «case» := Or.inr hII }
  have hq := h316 G S h.simple h.nonabelian h.qtke h.sylow M M₀ H _ hMT hyp
  have hVn := le_normalizer_VZ (S : Subgroup G) M
  have e1 : qhatOn M (VZ (S : Subgroup G) M) =
      qhatInt M₀ (VZ (S : Subgroup G) M) hyp.reduced.2.2.1 := by
    rw [qhatOn_eq hW]
    exact qhatInt_congr hW hauto
  have e2 : qOn M (VZ (S : Subgroup G) M) = qInt M₀ (VZ (S : Subgroup G) M) hyp.reduced.2.2.1 := by
    rw [qOn_eq hW]
    exact qInt_congr hW hauto
  rcases hq with ⟨R₀, hR₀, hR₀le, hR₀N⟩ | ⟨-, hq2, hTI⟩ | hq3
  · exfalso
    have hR₀p : IsPGroup 2 R₀ := (pCoreOf_isPGroup 2 M₀).to_le hR₀le
    obtain ⟨K, hK, hNK⟩ :=
      exists_maxTwoLocal_ge (L := Subgroup.normalizer (R₀ : Set G)) ⟨R₀, hR₀, hR₀p, rfl⟩
    have hKM : K = M := huniq.2 K ⟨hK, (le_sup_left.trans hR₀N).trans hNK⟩
    exact hH.2.1 ((le_sup_right.trans hR₀N).trans (hNK.trans hKM.le))
  · have hTI' : IsTISetIn (VZ (S : Subgroup G) M) M :=
      ⟨VZ_le_self hMT.2, fun g hg hgn => absurd (hVn hg) hgn⟩
    refine ⟨e1 ▸ hq2, fun _ => e1 ▸ hTI hTI'⟩
  · refine ⟨(qhatOn_le_qOn hW).trans (e2 ▸ hq3), fun hlt => ?_⟩
    exact absurd (e2 ▸ hq3) (not_le_of_gt hlt)

theorem stageLemma1511_of_theorem316 (h316 : Theorem316Statement) : StageLemma1511 := by
  intro G _ _ T Mc M h hM
  exact ⟨fun H hH => lemma_15_1_1_one h hM hH, lemma_15_1_1_two h316 h hM⟩

end CFSG.Quasithin
