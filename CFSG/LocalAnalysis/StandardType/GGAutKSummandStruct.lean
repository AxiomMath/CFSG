module

public import CFSG.LocalAnalysis.StandardType.GGAutKLemmaXi
public import CFSG.LocalAnalysis.StandardType.GGStructSOneCompHolds
public import CFSG.LocalAnalysis.StandardType.GGSummandStructAbstract
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatIVInputs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

open scoped commutatorElement

section Item1

theorem ggSummandStruct_of_O2 (hE : GGE0InnerDiagInput) (h1c : GGStructSOneComp)
    (h1d : GGStructSOnePerf) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ} {ψ : (ggU t n f).K →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ) (s1 : GGSixStepOne p B Bs x L D J)
    {b : G} {L₁ K : Subgroup G} {m : G} (hcfg : GGAutKConjConfig p B Bs x L D J b L₁ K m)
    (hOT : pCoreOf 2 (ggM p B x L D J ⊓ Subgroup.centralizer {b}) = ⊥ ∨
      GGOTwoXi (ggM p B x L D J) (D.map (MulAut.conj m⁻¹).toMonoidHom) b) :
    GGSummandStruct (D.map (MulAut.conj m⁻¹).toMonoidHom) K (ggM p B x L D J) ⊥
      {S | IsComponentOf S (ggG0 p B x L D J ⊓ Subgroup.centralizer {b}) ∧
        S ≤ K ⊓ ggM p B x L D J} := by
  obtain ⟨hb, hb1, hL₁, hK, hLK, hKM, hm, hEC⟩ := hcfg
  have : IsSimpleGroup G := hctx.1.1
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hctx.1.2.2.2.2.2.1.2.1
  have hchar : IsCharTwoType G := hctx.1.2.2.2.1
  obtain ⟨⟨hBBs, hBsEl, -, -⟩, ⟨⟨hDB, hDel, hDcard, -⟩, -⟩, -, -, -, ⟨hBsN, -⟩, -, -⟩ := hctx.2
  obtain ⟨hsimple, hperf, hmk⟩ := ggIVFlatData_of_ctx hctx s1
  have hfusE : GGControlsStrongFusion (ggM p B x L D J) (D.map (MulAut.conj m⁻¹).toMonoidHom) := by
    refine s1.2.1.of_map_conj_le ((ggM p B x L D J).inv_mem hm) ?_
    rintro _ ⟨_, ⟨d, hd, rfl⟩, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hd
  have hE0el : IsElemAbelian p (D.map (MulAut.conj m⁻¹).toMonoidHom) :=
    isElemAbelian_map_hom hDel _
  have hE0card : Nat.card (D.map (MulAut.conj m⁻¹).toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj m⁻¹).injective, hDcard]
  have hH₀Y : IsSubnormal (ggG0 p B x L D J ⊓ Subgroup.centralizer {b})
      (ggM p B x L D J ⊓ Subgroup.centralizer {b}) :=
    ggIsSubnormal_of_normal (inf_le_inf_right _ Subgroup.le_normalizer) (ggStepTwo_inf_normal _ b)
  have hKN : IsSubnormal (K ⊓ ggM p B x L D J) (ggM p B x L D J ⊓ Subgroup.centralizer {b}) := by
    have := ggIsSubnormal_inf hK.2.1 (ggM p B x L D J)
    rwa [inf_comm (Subgroup.centralizer {b}) (ggM p B x L D J)] at this
  have hKNY : K ⊓ ggM p B x L D J ≤ ggM p B x L D J ⊓ Subgroup.centralizer {b} :=
    le_inf inf_le_right (inf_le_left.trans hK.1)
  have hO2 : pCoreOf 2 (K ⊓ ggM p B x L D J) = ⊥ := by
    have hY : pCoreOf 2 (ggM p B x L D J ⊓ Subgroup.centralizer {b}) = ⊥ := by
      rcases hOT with h | hXi
      · exact h
      · exact (ggFalse_of_Xi hchar hp hp2 hfusE hE0el (le_of_eq hE0card.symm) hXi).elim
    exact le_bot_iff.mp ((pCoreOf_le_of_isSubnormal 2 hKN).trans hY.le)
  have hbBs : Subgroup.zpowers b ≤ Bs := (Subgroup.zpowers_le).mpr hb
  have hAel : IsElemAbelian p (Subgroup.zpowers b) := isElemAbelian_zpowers_of_mem hBsEl hb
  have hAN : Subgroup.zpowers b ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G) :=
    hbBs.trans hBsN
  have hmkA : LargeEvenMarking ↥(ggG0 p B x L D J) (fun _ _ _ I _ θ => ∀ a ∈ Subgroup.zpowers b,
      ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = a⁻¹ * l * a) φ) :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h a ha => h a (hbBs ha)) hmk
  have hcent : Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G) ⊓
      ggG0 p B x L D J = ggG0 p B x L D J ⊓ Subgroup.centralizer {b} := by
    rw [centralizer_zpowers_eq, inf_comm]
  refine ⟨hO2, ?_, ?_⟩
  ·
    intro P hPKM hPP
    have hPG₀ : P ≤ ggG0 p B x L D J := hperf P (hPKM.trans inf_le_right) hPP
    have hPC : P ≤ Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G) ⊓
        ggG0 p B x L D J := by
      rw [hcent]
      exact le_inf hPG₀ (hPKM.trans (inf_le_left.trans hK.1))
    have hlayer := h1d G p (ggG0 p B x L D J) (Subgroup.zpowers b) hp hp2 hsimple hAel hAN hmkA P
      hPC hPP
    rw [hcent] at hlayer
    exact ggPerfect_le_sSup_components hH₀Y hKN hPKM hPP hlayer
  ·
    rintro S ⟨hSc, hSN⟩
    have hE0S := hE G p B Bs x L D J t n f ψ hctx s1 b hb hb1 m hm hEC S hSc
    refine ⟨hSN, bot_le, ggIsSubnormal_of_le_of_le (ggIsSubnormal_trans hSc.2.1 hH₀Y) hSN hKNY,
      commutator_self_eq_of_isQuasisimple hSc.2.2, hE0S.1, ?_⟩
    intro _
    refine ⟨ggQuasisimple_quot_bot hSc.2.2, ?_⟩
    have hSc' : IsComponentOf S (Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G) ⊓
        ggG0 p B x L D J) := by
      rw [hcent]; exact hSc
    exact ggMarking_quot_bot
      (hE0S.2 (h1c G p (ggG0 p B x L D J) (Subgroup.zpowers b) hp hp2 hsimple hAel hAN hmkA S hSc'))

theorem ggHypRestIIIFlat_of_summandStruct {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* G} (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ)
    (s1 : GGSixStepOne p B Bs x L D J) {b : G} {L₁ K : Subgroup G} {m : G}
    (hcfg : GGAutKConjConfig p B Bs x L D J b L₁ K m)
    (hS : GGSummandStruct (D.map (MulAut.conj m⁻¹).toMonoidHom) K (ggM p B x L D J) ⊥
      {S | IsComponentOf S (ggG0 p B x L D J ⊓ Subgroup.centralizer {b}) ∧
        S ≤ K ⊓ ggM p B x L D J})
    [hN : ((ggAutKV D K (ggM p B x L D J) m).subgroupOf (ggAutKW D K m)).Normal] :
    GGHypRestIIIFlat p
      (((ggAutKH D K (ggM p B x L D J) m).subgroupOf (ggAutKW D K m)).map
        (ggAutKPi D K (ggM p B x L D J) m))
      (((D.map (MulAut.conj m⁻¹).toMonoidHom).subgroupOf (ggAutKW D K m)).map
        (ggAutKPi D K (ggM p B x L D J) m)) := by
  obtain ⟨hb, hb1, hL₁, hK, hLK, hKM, hm, hEC⟩ := hcfg
  have : IsSimpleGroup G := hctx.1.1
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hctx.1.2.2.2.2.2.1.2.1
  obtain ⟨-, ⟨⟨-, hDel, hDcard, -⟩, -⟩, -⟩ := hctx.2
  have hfusE : GGControlsStrongFusion (ggM p B x L D J) (D.map (MulAut.conj m⁻¹).toMonoidHom) := by
    refine s1.2.1.of_map_conj_le ((ggM p B x L D J).inv_mem hm) ?_
    rintro _ ⟨_, ⟨d, hd, rfl⟩, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hd
  have hE0el : IsElemAbelian p (D.map (MulAut.conj m⁻¹).toMonoidHom) :=
    isElemAbelian_map_hom hDel _
  have hE0card : Nat.card (D.map (MulAut.conj m⁻¹).toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj m⁻¹).injective, hDcard]
  have hnorm : D.map (MulAut.conj m⁻¹).toMonoidHom ≤ Subgroup.normalizer (K : Set G) :=
    ggLemmaThreeThirteenInput_holds G p hp hp2 (Subgroup.centralizer {b})
      (ggM p B x L D J ⊓ Subgroup.centralizer {b}) _
      (ggStepTwo_kGroup_of_ne_top hctx.1.2.2.1 (ggStepTwo_centralizer_ne_top hctx.1.2.1 hb1))
      hE0el hE0card (hfusE.inf_in hEC) K hK (fun h => hKM (h.trans inf_le_left))
  have hEM : D.map (MulAut.conj m⁻¹).toMonoidHom ≤ ggM p B x L D J := hfusE.1
  have hH₀C : D.map (MulAut.conj m⁻¹).toMonoidHom ⊔ (K ⊓ ggM p B x L D J) ≤
      ggM p B x L D J ⊓ Subgroup.centralizer {b} :=
    sup_le (le_inf hEM hEC) (le_inf inf_le_right (inf_le_left.trans hK.1))
  have h3 : GGRCSAutKIIIFlat (ggM p B x L D J) (D.map (MulAut.conj m⁻¹).toMonoidHom) K :=
    ggRCSAutKIIIFlat_of_summandStruct hp hp2 hE0el hEM hnorm hS
  have hker : (ggAutKPi D K (ggM p B x L D J) m).ker ≤
      (ggAutKH D K (ggM p B x L D J) m ⊓ Subgroup.centralizer (K : Set G)).subgroupOf
        (ggAutKW D K m) := by
    intro w hw
    rw [ggAutKPi, QuotientGroup.ker_mk'] at hw
    exact hw
  have hL₁M : IsComponentOf L₁ (ggM p B x L D J ⊓ Subgroup.centralizer {b}) := by
    have hle' : ggG0 p B x L D J ⊓ Subgroup.centralizer {b} ≤
        ggM p B x L D J ⊓ Subgroup.centralizer {b} :=
      inf_le_inf_right _ Subgroup.le_normalizer
    exact ⟨hL₁.1.trans hle', ggIsSubnormal_trans hL₁.2.1
      (ggIsSubnormal_of_normal hle' (ggStepTwo_inf_normal _ b)), hL₁.2.2⟩
  exact ggHypRestIIIFlat_of_ad (@h3 hN)
    (ggAutK_layer_ne_bot hL₁M hLK (hL₁M.1.trans inf_le_left) hH₀C
      (ggAutKPi D K (ggM p B x L D J) m) hker)

end Item1

end CFSG.StandardType
