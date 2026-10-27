module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnit63ActCfg
public import CFSG.LocalAnalysis.StandardType.GGTableBUnit63Main
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitActMain

public section

namespace CFSG.StandardType.U63TB

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.StandardType CFSG.StandardType.LineU CFSG.StandardType.UnitTB CFSG.Assembly TableB

section Certificates

theorem ggTableBActionSCr_unitary63_big {n : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 2 ≤ n) (hpq : 3 ∣ 2 ^ n + 1) :
    GGTableBActionSCr 3 4 (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ n)))
        (LargeEvenGUSet (Fin 6) K (2 ^ n))) := by
  refine ⟨by norm_num, fun L' _ _ ψ hψ hker hperf A hA hAI hr _ hsc => ?_⟩
  have hcov := unitaryUniversalCover_holds n 6 K hK (by norm_num)
    (fun h => absurd (congrArg Prod.snd h) (by omega))
  exact act63_of_cover hK (by omega) hpq hcov.1
    (fun ψ'' hs hk => hcov.2 L' ψ'' hs (hk ▸ hker) hperf) hψ hker hperf hA hAI hr hsc

theorem ggTableBActionSCrW_unitary63_two {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ 1) ^ 2) :
    GGTableBActionSCrW 3 4 (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
        (LargeEvenGUSet (Fin 6) K (2 ^ 1))) := by
  refine ⟨by norm_num, fun L' _ _ ψ hψ hker hperf A hA hAI hr _ hsc => ?_⟩
  have hcov := unitaryCoverOddAt_six_two K (by norm_num [hK])
  exact actConclW_descent hker hψ hperf hA hAI hsc
    (fun L₁ _ _ ψ₁ hs hk hp hodd A₁ hA₁ hAI₁ hc hsc₁ =>
      act63_of_cover hK le_rfl (by norm_num) hcov.1
        (fun ψ'' hs'' hk'' => hcov.2 L₁ ψ'' hs'' (hk'' ▸ hk) hp (hk'' ▸ hodd)) hs hk hp hA₁ hAI₁
        (by rw [hc]; exact hr) hsc₁)

theorem ggTableBActionSCrW_unitary63 {n : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hpq : 3 ∣ 2 ^ n + 1) :
    GGTableBActionSCrW 3 4 (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ n)))
        (LargeEvenGUSet (Fin 6) K (2 ^ n))) := by
  rcases Nat.lt_or_ge n 2 with h | h
  · obtain rfl : n = 1 := by omega
    exact ggTableBActionSCrW_unitary63_two hK
  · exact ggTableBActionSCrW_of (ggTableBActionSCr_unitary63_big hK h hpq)

end Certificates

end CFSG.StandardType.U63TB

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB LineU

section Results

theorem largeEvenLabelAll_unitDvd63_action {p : ℕ} {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGUnitDvd63Label p lab) :
    LargeEvenLabelAll lab fun R _ I _ => U63TB.GGTableBActionSCrW p 4 R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨⟨ht, -, hpn, -⟩, hl5, hp3⟩ := h
  dsimp only at ht hpn hl5 hp3
  subst ht hl5 hp3
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQ'⟩ := hQ
  exact ⟨K, i1, i2, hK, ⟨hQ', U63TB.ggTableBActionSCrW_unitary63 hK hn hpn⟩⟩

theorem ggTableBActionInputOn_unitDvd63_of_lid {S : ℕ → LargeEvenLabel → Prop}
    (hS : ∀ p lab, S p lab → GGUnitDvd63Label p lab) (hD : GGBstarInnerDiagLInputOn S) :
    GGTableBActionInputOn S := by
  intro G _ _ p B Bs x L D J B₂ hcfg hM hMod
  have hMs := hD G p B Bs x L D J hcfg hM
  obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll (S := fun lab => S p lab)
    (P' := fun R _ I _ => U63TB.GGTableBActionSCrW p 4 R I)
    (fun lab hlab hs => largeEvenLabelAll_unitDvd63_action hlab (hS p lab hs))
    (fun _ _ _ _ _ _ hP => hP.1) hMs
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, -, hBsN, h3⟩, hT⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨h4', h3'⟩ := card_range_ggGamma_unitDvd63 hcfg (hMs.mono hS) hBsN
  exact U63TB.ggTableBAction_of_cardW hcfg hL θ hBsN
    (fun b hb => ggLAut_mem_of_induces L θ hBsN h3 hb) h4' h3' hT hMod

theorem ggTableBActionInputOn_unitDvd63 (hD : GGBstarInnerDiagLInputOn GGUnitDvd63Label) :
    GGTableBActionInputOn GGUnitDvd63Label :=
  ggTableBActionInputOn_unitDvd63_of_lid (fun _ _ h => h) hD

theorem ggTableBActionInputOn_unitDvd63CoprimeN_holds :
    GGTableBActionInputOn GGUnitDvd63CoprimeNLabel :=
  ggTableBActionInputOn_unitDvd63_of_lid (fun _ _ h => h.1)
    ggBstarInnerDiagLInputOn_unitDvd63_coprimeN

theorem ggTableBActionInputOn_of_not_unitDvd63CoprimeN {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBActionInputOn fun p lab => S p lab ∧ ¬ GGUnitDvd63CoprimeNLabel p lab) :
    GGTableBActionInputOn S :=
  (ggTableBActionInputOn_unitDvd63CoprimeN_holds.or h).mono fun p lab hlab => by
    by_cases hl : GGUnitDvd63CoprimeNLabel p lab
    · exact Or.inl hl
    · exact Or.inr ⟨hlab, hl⟩

theorem ggTableBActionInputOn_of_not_unitDvd63
    (hF : GGBstarInnerDiagLInputOn GGUnitDvd63FieldLabel) {S : ℕ → LargeEvenLabel → Prop}
    (h : GGTableBActionInputOn fun p lab => S p lab ∧ ¬ GGUnitDvd63Label p lab) :
    GGTableBActionInputOn S :=
  ((ggTableBActionInputOn_unitDvd63 (ggBstarInnerDiagLInputOn_unitDvd63 hF)).or h).mono
    fun p lab hlab => by
      by_cases hl : GGUnitDvd63Label p lab
      · exact Or.inl hl
      · exact Or.inr ⟨hlab, hl⟩

end Results

end CFSG.StandardType

end
