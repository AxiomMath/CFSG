module

public import CFSG.LocalAnalysis.StandardType.GGFrameEndGuard
public import CFSG.LocalAnalysis.StandardType.GGFrameEndAutomizer
public import CFSG.LocalAnalysis.StandardType.GGFrameEndModel
public import CFSG.LocalAnalysis.StandardType.GGFrameEndNum
public import CFSG.LocalAnalysis.StandardType.GGFrameEndTX
public import CFSG.LocalAnalysis.StandardType.GGFrameEndTXClosure
public import CFSG.LocalAnalysis.StandardType.GGFrameModelStep
public import CFSG.LocalAnalysis.StandardType.GGFrameE78TX
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteJoin
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteJoinDefs
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteJoinTBDefs
public import CFSG.LocalAnalysis.StandardType.GGFrameTBVacuous
public import CFSG.LocalAnalysis.StandardType.GGFrameFSxEndsCardJoin
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteLower
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBFixLine
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyDichotomy
public import CFSG.LocalAnalysis.StandardType.GGSpNbrKGMark
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1WeylE
public import CFSG.LocalAnalysis.StandardType.GGStdSubExist
public import CFSG.LocalAnalysis.StandardType.GGCoxReflConv
public import CFSG.LocalAnalysis.StandardType.GGFrameE78Facts
public import Certificates.Certificate1952
public import Certificates.Certificate709590
public import CFSG.LocalAnalysis.StandardType.GGTorusMaxThreaded
import CFSG.LocalAnalysis.StandardType.GGFrameTBHolds
import CFSG.LocalAnalysis.StandardType.GGTorusMaxOverProof

public section

namespace CFSG.StandardType.FrameRoute

open CFSG CFSG.Assembly TableB CFSG.Open

theorem largeEvenLabelAll_const {lab : LargeEvenLabel} {C : Prop} (h : C) :
    LargeEvenLabelAll lab fun _ _ _ _ => C := fun _ hQ =>
  largeEvenRawDatum_mono (fun _ _ _ _ hq => ⟨hq, h⟩) hQ

theorem largeEvenLabelAll_imp {lab : LargeEvenLabel} {C : Prop} {P : LargeEvenRawCont}
    (h : C → LargeEvenLabelAll lab P) : LargeEvenLabelAll lab fun R _ I F => C → P R I F := by
  by_cases hC : C
  · exact fun Q hQ =>
      largeEvenRawDatum_mono (fun _ _ _ _ hq => ⟨hq.1, fun _ => hq.2⟩) (h hC Q hQ)
  · exact fun _ hQ =>
      largeEvenRawDatum_mono (fun _ _ _ _ hq => ⟨hq, fun hc => absurd hc hC⟩) hQ

private def frameEndLabP (lab : LargeEvenLabel) : LargeEvenRawCont := fun R _ I _ =>
  LargeEvenInLambda2 lab ∧
    (lab.n = 1 → frameTagTabled lab.tag →
      ∀ r : ℕ, 6 ≤ r → frameTBRange lab r → GGTorusReflGenW 3 r R I ∧
        ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
          GGTorusTBGroup 3 r R I L' ψ A →
            (FrameNumIs (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) (frameLabNum lab).1
                (frameLabNum lab).2 ∧
              FrameConn (ggAutomizer (MulAut.conj : L' →* MulAut L').range A)) ∧
            ∃ S : Subgroup L', IsPGroup 3 S ∧ ¬ IsCyclic S) ∧
    (lab.n = 1 → ¬ frameTagTabled lab.tag →
      ∀ r : ℕ, 6 ≤ r → ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R)
        (A : Subgroup (MulAut L')), ¬ GGTorusTBGroup 3 r R I L' ψ A) ∧
    (lab.n = 1 → lab.tag = .twA → GGTorusLift 3 (ggUnitaryTorusRank 3 (lab.rank + 1)) R) ∧
    (lab.n = 1 → lab.tag = .E8 → GGTorusLift 3 7 R)

private theorem frameEndLabP_all
    (hb1 : GGFrameTBNumerologyInput)
    (hb1' : GGFrameTBVacuousInput) {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab) :
    LargeEvenLabelAll lab (frameEndLabP lab) :=
  largeEvenLabelAll_and (largeEvenLabelAll_const hΛ)
    (largeEvenLabelAll_and
      (largeEvenLabelAll_imp fun hn1 => largeEvenLabelAll_imp fun htab => hb1.1 lab hΛ hn1 htab)
      (largeEvenLabelAll_and
        (largeEvenLabelAll_imp fun hn1 => largeEvenLabelAll_imp fun htab => hb1' lab hΛ hn1 htab)
        (largeEvenLabelAll_and
          (largeEvenLabelAll_imp fun hn1 => largeEvenLabelAll_imp fun htag =>
            largeEvenLabelAll_torusLift_twA hΛ htag Nat.prime_three (by rw [hn1]; norm_num))
          (largeEvenLabelAll_imp fun hn1 => largeEvenLabelAll_imp fun htag =>
            hb1.2 lab hΛ hn1 htag))))

theorem frameEnd_marking_of_weylAtJoin
    {n : ℕ} (hn : n = 7 ∨ n = 8) {M : CoxeterMatrix (Fin n)}
    (h2 : ∃ S : Subgroup M.Group, IsElemAbelian 2 S ∧
      ∃ f : Finset (Fin n) → S, Function.Injective f)
    (hMW : GGIsWeylMatrix M) (h3 : ∀ i j : Fin n, i ≠ j → M.M i j ≤ 3)
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    (hb1 : GGFrameTBNumerologyInput) (hb1' : GGFrameTBVacuousInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hR : GGSecFiveRestHyp 3 B Bs x L D J) (hW : GGSecFiveWeylCase 3 B Bs x D J)
    (hq : GGInnerDiagOnLabel GGLabQTwo 3 Bs L)
    (hmodel : ∀ {𝒜 : Subgroup (MulAut ↥Bs)} (e : M.Group ≃* ↥𝒜),
      (∀ φ ∈ 𝒜, φ ∈ ggInduced ⊤ Bs) →
      (∀ i, GGIsReflection 3 ((e (M.simple i) : ↥𝒜) : MulAut ↥Bs)) →
      (∀ b : ↥Bs, (∀ φ ∈ 𝒜, φ b = b) → b = 1) → Nat.card ↥Bs = 3 ^ n →
      ∃ (ψ : Additive ↥Bs ≃+ FEVec n) (ρ : ↥𝒜 →* FEMat n), Function.Injective ρ ∧
        (∀ (φ : ↥𝒜) (b : ↥Bs), (ρ φ).mulVec (ψ (Additive.ofMul b)) =
          ψ (Additive.ofMul ((φ : MulAut ↥Bs) b))) ∧
        ∀ i, ρ (e (M.simple i)) = feS n i)
    (hJ : GGSecFiveWeylAtJoin 3 B Bs x L D J M) :
    LargeEvenMarking L (fun lab _ _ _ _ _ => LargeEvenInLambda2 lab ∧ lab.n = 1 ∧
      frameEndPair n (frameLabNum lab).1 (frameLabNum lab).2) := by
  classical
  obtain ⟨𝒦, h𝒦, hne, e, he⟩ := hJ
  have hcfg := hR.1
  obtain ⟨hp, hBsE, hxBs, hLx, -⟩ := hcfg.tableB_facts
  have hS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hN : Bs ≤ Subgroup.normalizer (L : Set G) :=
    GGDichotomy.le_normalizer_of_innerDiagOn hR.2.2.1.1
  have hBs : Nat.card Bs = 3 ^ n :=
    card_bstar_of_weylAtJoin (Fintype.card_fin n) h2 hTBF hWI hR hW h𝒦 hne ⟨e, he⟩
  have hA : Nat.card (ggGamma L hN).range * 3 = Nat.card Bs :=
    card_range_ggGamma_mul_of hp hBsE hxBs hx1 hLx hS.2.2.2.2 hN
  have hA' : Nat.card (ggGamma L hN).range = 3 ^ (n - 1) := by
    rw [hBs] at hA
    rcases hn with rfl | rfl <;> norm_num at hA ⊢ <;> omega
  have h6 : 6 ≤ n - 1 := by rcases hn with rfl | rfl <;> norm_num
  have hE1 := largeEvenMarking_torusTBGroup_of_qTwo hR hq hN (n - 1) hA'.ge
    (by rw [hA']; exact Nat.pow_le_pow_right (by norm_num) (by omega))
  have hL𝒜 : ggAutomizer L Bs ≤ ggAutomizerJoin L Bs 𝒦 := le_sup_left
  have h𝒜H : ggAutomizerJoin L Bs 𝒦 ≤ ggAutomizer (ggG0 3 B x L D J) Bs :=
    ggAutomizerJoin_le_ggG0 h𝒦
  have hnt : ∀ φ ∈ ggAutomizerJoin L Bs 𝒦, ¬ GGIsTransvection 3 φ :=
    ggNoTransvection_of_le_automizer hR.2.2.2.1 (h𝒜H.trans (ggAutomizer_mono Bs le_top))
  have hfpf : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizerJoin L Bs 𝒦, φ b = b) → b = 1 :=
    eq_one_of_fix_ggAutomizerJoin hTBF hWI hR hW h𝒦 hne
  have hA : ∀ φ ∈ ggAutomizerJoin L Bs 𝒦, φ ∈ ggInduced ⊤ Bs := fun φ hφ =>
    mem_ggAutomizer_iff.mp ((h𝒜H.trans (ggAutomizer_mono Bs le_top)) hφ)
  obtain ⟨ψ, ρ, -, hact, hρ⟩ := hmodel e hA he hfpf hBs
  have hrefl : ∀ φ ∈ ggAutomizerJoin L Bs 𝒦, GGIsReflection 3 φ → frameRho ψ φ ∈ feT n :=
    fun φ hφ hr => frameRho_mem_feT_of_isReflection hBsE ⟨hMW, he⟩ h3 hnt hact hρ hφ hr
  have hfeT : ∀ t ∈ feT n, ∃ φ ∈ ggAutomizerJoin L Bs 𝒦, GGIsReflection 3 φ ∧ frameRho ψ φ = t :=
    fun t ht => exists_isReflection_frameRho_eq he hact hρ ht
  have hfix : ∀ b : ↥Bs, (∀ φ ∈ ggAutomizer L Bs, φ b = b) → (b : G) ∈ Subgroup.zpowers x :=
    fun b => ((hR.fixLineComp_L hTBF hW.2).fix_iff b).1
  refine largeEvenMarking_mono_labelAll (P' := frameEndLabP)
    (fun lab hΛ => frameEndLabP_all hb1 hb1' hΛ) ?_ hE1
  intro lab R _ I F θ _ hP hP'
  obtain ⟨hq2, hTB⟩ := hP
  obtain ⟨hΛ, hb1c, hb1'c, htw, htw8⟩ := hP'
  have hn1 : lab.n = 1 := by
    have h1 := hΛ.1
    have h2 : lab.n < 2 := hq2
    omega
  by_cases htab : frameTagTabled lab.tag
  swap
  · exact absurd hTB (hb1'c hn1 htab (n - 1) h6 L (ggQuotHom θ) (ggGamma L hN).range)
  have hrange : frameTBRange lab (n - 1) :=
    frameTBRange_of_torusLift hR hn hBs hq.1 θ (htw hn1) (htw8 hn1)
  obtain ⟨hT, hNum⟩ := hb1c hn1 htab (n - 1) h6 hrange
  obtain ⟨⟨hNumA, hConnA⟩, S, hS3, hSnc⟩ := hNum L (ggQuotHom θ) (ggGamma L hN).range hTB
  obtain ⟨hbij, hRG⟩ := bijective_ggAutomizerGammaHom_and_reflGenerated hR hN θ hTB hT
  obtain ⟨hNumL, hConnL⟩ :=
    frameNumIs_frameConn_of_ggAutomizerGammaHom hR hN hbij _ _ ⟨hNumA, hConnA⟩
  have hLn : (L.subgroupOf (Subgroup.centralizer ({x} : Set G))).Normal := by
    refine subgroupOf_centralizer_normal_of_noncyclic hR
      ⟨S.map L.subtype, ?_, hS3.map L.subtype, ?_⟩
    · rintro _ ⟨s, -, rfl⟩
      exact s.2
    · intro hcyc
      exact hSnc (isCyclic_of_injective
        (Subgroup.equivMapOfInjective S L.subtype L.subtype_injective).toMonoidHom
        (Subgroup.equivMapOfInjective S L.subtype L.subtype_injective).injective)
  obtain ⟨-, d, hd, hpair⟩ := feTx_eq_and_endPair hn (frameCoord_ne_zero ψ hxBs hx1)
    (image_frameReflSet_subset_feTx ψ hxBs hLx hL𝒜 hrefl)
    (exists_eq_smul_of_forall_mulVec_eq ψ hxBs hfix hRG)
    (conj_mem_submonoidClosure_image_frameReflSet ψ hxBs hLx hLn hRG h𝒜H hfeT)
    (mem_image_frameReflSet_of_mem_closure ψ hRG fun t ht => (hfeT t ht).imp fun _ h => h.2)
    (frameConn_image (frameRho ψ) (frameRho_injective ψ) hConnL)
  have hne' : (frameReflSet (ggAutomizer L Bs)).Nonempty := by
    have h0 : (frameRho ψ '' frameReflSet (ggAutomizer L Bs)).ncard ≠ 0 := by
      rcases hpair with ⟨-, ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩⟩ | ⟨-, ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩⟩ <;> omega
    exact (Set.nonempty_of_ncard_ne_zero h0).of_image
  obtain ⟨hNeq, hdeq⟩ := frameNumIs_image (frameRho ψ) (frameRho_injective ψ) hNumL hd hne'
  rw [hNeq, ← hdeq] at hpair
  exact ⟨hΛ, hn1, hpair⟩

theorem ggFrameEndLabelJoinInput_of_tableB
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) (hb1 : GGFrameTBNumerologyInput)
    (hb1' : GGFrameTBVacuousInput) : GGFrameEndLabelJoinInput := by
  have hr7 : CoxeterMatrix.E₇ = CoxeterMatrix.E₇.reindex (Equiv.refl (Fin 7)) := by
    apply CoxeterMatrix.ext
    funext i j
    rw [CoxeterMatrix.reindex_apply]
    simp
  have hr8 : CoxeterMatrix.E₈ = CoxeterMatrix.E₈.reindex (Equiv.refl (Fin 8)) := by
    apply CoxeterMatrix.ext
    funext i j
    rw [CoxeterMatrix.reindex_apply]
    simp
  intro G _ _ B Bs x L D J hR hW hq
  have hBsE : IsElemAbelian 3 Bs := hR.1.tableB_facts.2.1
  refine ⟨fun hJ => ?_, fun hJ => ?_⟩
  · refine largeEvenMarking_mono (fun lab _ _ _ _ _ h => ?_)
      (frameEnd_marking_of_weylAtJoin (Or.inl rfl) exists_elemAbelian_two_coxeterE7
        (Or.inr (Or.inr (Or.inl ⟨_, hr7⟩))) (GGIsWeylMatrixE.le_three (Or.inr (Or.inl ⟨_, hr7⟩)))
        hTBF hWI hb1 hb1' hR hW hq
        (fun e hA he hfix hcard => exists_frameModel_E7 hBsE hR.2.2.2.1 hA e he hfix hcard) hJ)
    obtain ⟨hΛ, hn1, hpair⟩ := h
    rcases frameLab_mem_of_num hΛ hn1 hpair with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h (by norm_num)
  · refine largeEvenMarking_mono (fun lab _ _ _ _ _ h => ?_)
      (frameEnd_marking_of_weylAtJoin (Or.inr rfl) exists_elemAbelian_two_coxeterE8
        (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hr8⟩))))
        (GGIsWeylMatrixE.le_three (Or.inr (Or.inr ⟨_, hr8⟩))) hTBF hWI hb1 hb1' hR hW hq
        (fun e hA he hfix hcard => exists_frameModel_E8 hBsE hR.2.2.2.1 hA e he hfix hcard) hJ)
    obtain ⟨hΛ, hn1, hpair⟩ := h
    rcases frameLab_mem_of_num hΛ hn1 hpair with ⟨h, -⟩ | ⟨-, h⟩
    · exact absurd h (by norm_num)
    · exact h

theorem ggFrameRouteJoinInputs_of_tableB
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) (h : GGFrameRouteJoinTBInputs)
    (h5 : GGFSyNonFSPointJoinInput) : GGFrameRouteJoinInputs :=
  ⟨h, tmThreaded_lss92TorusMaxInput lss92MaxOvergroupInput_holds,
    ggFrameEndLabelJoinInput_of_tableB hTBF hWI ggFrameTBNumerologyInput_holds
      ggFrameTBVacuousInput_holds,
    ggFSxEndsCardJoinInput_holds, h5⟩

end CFSG.StandardType.FrameRoute

end
