module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitTvSixQ2Descent
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitTvSixQ2Odd
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitTvSix
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUCoverOdd
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63Q2ProofFinal
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLTv

public section

namespace CFSG.StandardType.UnitTvQ2

open CFSG CFSG.Assembly TableB CFSG.ClassicalGroups.UnitaryFlag

theorem noTransvectionSCr_unitary_two {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ 1) ^ 2) (hcov : Line63.UnitaryCoverOddAt 1 6 K) :
    GGNoTransvectionSCr 3 4 (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
        (LargeEvenGUSet (Fin 6) K (2 ^ 1))) := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr _h3 hsc α hα
  exact tv_descent hψ hker hperf hA hAI hsc
    (fun L₁ _ _ ψ₁ hs hk hp hodd A₁ hA₁ hAI₁ hc hsc₁ α₁ _ =>
      noTransvection_odd hK hcov hs hk hp hodd hA₁ hAI₁ (by rw [hc]; exact hr) hsc₁ α₁)
    α hα

section Labels


theorem largeEvenLabelAll_unitDvd63_two_tv {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (h : GGUnitDvd63Label p lab) (hn1 : lab.n = 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusLift p 3 R ∧ GGNoTransvectionSCr p 4 R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨⟨ht, -, hpn, -⟩, hl5, hp3⟩ := h
  dsimp only at ht hpn hl5 hp3 hn1
  subst ht hl5 hp3 hn1
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
  have hdq : (5 + 1, 2 ^ 1) ≠ (3, 2) := by
    intro heq
    have := congrArg Prod.fst heq
    simp only at this
    omega
  have hlift := ggTorusLift_unitary hK (le_refl 1) (by norm_num : 3 ≤ 5 + 1) hdq hp hpn
  have hrk : ggUnitaryTorusRank 3 (5 + 1) = 3 := by simp [ggUnitaryTorusRank]
  rw [hrk] at hlift
  exact ⟨K, i1, i2, hK, ⟨hQ', hlift, noTransvectionSCr_unitary_two hK
    (LineU.unitaryCoverOddAt_six_two K (by norm_num [hK]))⟩⟩

end Labels

end CFSG.StandardType.UnitTvQ2

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

section Labels


theorem ggLTransvectionCenterInputOn_unitDvd63_two :
    GGLTransvectionCenterInputOn fun p lab => GGUnitDvd63Label p lab ∧ lab.n = 1 := by
  intro G _ _ p B Bs x L D J hC hM φ hφ htv b
  have hp : p.Prime := hC.1.2.2.2.2.2.1.1
  have hcard := Line63.H5.ggUnitDvd63BstarRankInput_holds G p B Bs x L D J hC
    (hM.mono fun _ _ h => h.1)
  obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => GGUnitDvd63Label p lab ∧ lab.n = 1)
    (fun lab _ hs => UnitTvQ2.largeEvenLabelAll_unitDvd63_two_tv hp hs.1 hs.2)
    (fun _ _ _ _ _ _ hP => hP.1) hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, -, hBsN, h3⟩, hlift, htvt⟩ :=
    largeEvenRawDatum_exists hraw
  have hnc := UnitTv.exists_noncyclic_of_torusLift hp (by norm_num : 2 ≤ 3) hL θ hlift
  obtain ⟨-, hBs, hxBs, hLx, -⟩ := hC.tableB_facts
  have hS : LargeEvenSStar p B x L := hC.1.2.2.2.2.2.2.1
  have hmul := card_range_ggGamma_mul_of hp hBs hxBs hS.2.2.1 hLx hS.2.2.2.2 hBsN
  have h4' : p ^ 4 ≤ Nat.card (ggGamma L hBsN).range := by
    rw [← hmul, pow_succ] at hcard
    exact Nat.le_of_mul_le_mul_right hcard hp.pos
  exact UnitTv.mem_zpowers_of_noTransvectionSCr_card hC hnc hL θ hBsN
    (fun b hb => ggLAut_mem_of_induces L θ hBsN h3 hb) h4'
    ((Nat.pow_le_pow_right hp.pos (by norm_num)).trans h4') htvt hφ htv b

theorem ggLTransvectionCenterInputOn_of_not_unitDvd63Two {S : ℕ → LargeEvenLabel → Prop}
    (h : GGLTransvectionCenterInputOn fun p lab =>
      S p lab ∧ ¬ (GGUnitDvd63Label p lab ∧ lab.n = 1)) :
    GGLTransvectionCenterInputOn S := by
  have h' := ggLTransvectionCenterInputOn_unitDvd63_two.or h
  intro G _ _ p B Bs x L D J hC hL
  refine h' G p B Bs x L D J hC (hL.mono fun p lab hlab => ?_)
  by_cases h1 : GGUnitDvd63Label p lab ∧ lab.n = 1
  · exact Or.inl h1
  · exact Or.inr ⟨hlab, h1⟩

end Labels

end CFSG.StandardType

end
