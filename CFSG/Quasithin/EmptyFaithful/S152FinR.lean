module

public import CFSG.Quasithin.EmptyFaithful.S152FinN
public import CFSG.Quasithin.EmptyFaithful.S152L27
public import CFSG.Quasithin.EmptyFaithful.S152FinCore
public import CFSG.Quasithin.EmptyFaithful.S152FinTop

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

@[expose] def StageFinal152R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Setting152 T Mc M →
    ∀ H : Subgroup G, IsHStar T M H → ∀ H₁ H₂ : Subgroup G, IsHPair H (V154 T Mc M) H₁ H₂ →
      ∀ B₀ : Subgroup (MulAut (V154 T Mc M)), IsB0 T Mc M B₀ →
        AmalgamHypV (nOfR152 T Mc M ⊔ H) (nOfR152 T Mc M) H T (V154 T Mc M) →
        autOn (nOfR152 T Mc M) (V154 T Mc M) = autOn M (V154 T Mc M) →
        Lemma1518Concl T Mc M →
        (V154 T Mc M ≤ pCoreOf 2 H ∧ IsElemAbelian 2 (conjClosure (V154 T Mc M) H)) →
        Concl319 T M (V154 T Mc M) H True →
        Nonempty (OTwoQuot H ≃* Equiv.Perm (Fin 3) ≀ᵣ Multiplicative (ZMod 2)) →
        Lemma15225Concl T Mc M → Lemma15226Concl T Mc M →
        (E3.wClos (V154 T Mc M) 0 (pCoreOf 2 H) ≤
          H ⊓ Subgroup.centralizer (conjClosure (V154 T Mc M) H : Set G)) →
        Lemma15227Three T Mc M B₀ →
        ⁅conjClosure (V154 T Mc M) H, lambdaOf (pCoreOf 2 H)⁆ ≤ zSOf T Mc M B₀ → False

open S152Fin in
theorem stageFinal152R : StageFinal152R := by
  intro G _ _ T Mc M hs H hH H₁ H₂ hP B₀ hB₀ hAm hFr h1518 h1511 hC hq h25 h26 h26₃ h27 h28
  have hV₂ : IsElemAbelian 2 (V154 T Mc M) := hAm.elemAbelian
  obtain ⟨hVQ, hUab⟩ := h1511
  have hMV : M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := le_normalizer_V154 T Mc M
  have hZV : zSOf T Mc M B₀ ≤ V154 T Mc M := zSOf_le_V154 T Mc M B₀
  have hsV : 1 < E3.sParam hV₂ := by
    obtain ⟨hV, -, hs'⟩ := h26.r_gt
    exact hs'
  have hFF : ¬ @IsFFModule (V154 T Mc M) (commGroupOfElemAbelian hV₂)
      (autOn (nOfR152 T Mc M) (V154 T Mc M)) := by
    rw [hFr]
    exact not_isFFModule_of_lemma1518 hV₂ h1518
  refine final_core (Z := zSOf T Mc M B₀) hAm hFF hVQ hUab hsV hZV
    h26₃ h27 h28 (input152Kernel G T Mc M hs H hH hAm.sylow₂ hC hq)
    (fun E hEH hE => relIndex_pCoreOf_le_four hq hEH hE)
    (fun D hD hDab => relIndex_centralizer_le_two hMV hV₂ h25.cases.2
      (hD.trans (inf_le_left : nOfR152 T Mc M ≤ M)) hDab)
    (fun X hXH hXab hXidx => input152Transvection G T Mc M hs H hH hAm.sylow₂ hC hq X hXH hXab hXidx)

theorem stageRankNotTwo_of_finalR (h1518 : StageLemma1518) (h1519 : StageLemma1519)
    (h15111 : StageLemma15111) (h15112 : StageLemma15112) (h15208 : StageLemma15208)
    (h15209 : StageNotation15209) (h15213 : StageLemma15213) (h15215 : StageTheorem15215)
    (h25 : StageLemma15225) (h26 : StageLemma15226) (h27 : StageLemma15227Two)
    (h28 : StageLemma15228) (hfin : StageFinal152R) : StageRankNotTwo := by
  intro G _ _ T Mc M h hM hne4
  by_contra hOF
  have hCE : IsCE1513 T M := ⟨hne4, hOF⟩
  have hs : Setting152 T Mc M := ⟨h, hM, hCE⟩
  obtain ⟨H, hH⟩ := exists_isHStar h.inM_mc hM.1.1 hM.2.1.symm
  obtain ⟨H₁, H₂, hP⟩ := (h15209 G T Mc M hs H hH).pair
  obtain ⟨B₀, hB₀, -, -⟩ := (h15213 G T Mc M hs H hH).exists_B0
  have c1519 := h1519 G T Mc M h hM hCE
  have hAm := stageObserveF7N_of h1519 G T Mc M hs H hH
  exact hfin G T Mc M hs H hH H₁ H₂ hP B₀ hB₀ hAm
    c1519.six_autOn (h1518 G T Mc M h hM hCE) (h15111 G T Mc M h hM hCE H hH)
    (h15112 G T Mc M h hM hCE H hH).1 (h15208 G T Mc M hs H hH) (h25 G T Mc M hs)
    (h26 G T Mc M hs).1 ((h26 G T Mc M hs).2 H hH)
    (lemma15227_three_of hs c1519 (h15215 G T Mc M hs B₀ hB₀) (h26 G T Mc M hs).1.w0_le
      hAm.elemAbelian (h27 G T Mc M hs))
    (h28 G T Mc M hs H hH B₀ hB₀)

end CFSG.Quasithin
