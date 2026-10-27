module

public import CFSG.Quasithin.Background.C1GNC128
public import CFSG.Quasithin.Vol2.Ch11SecSSym

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA

@[expose] def Obl11_1_2StarZL2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I V₁ V₂ X K : Subgroup G),
    StarHyp G T L I V₁ V₂ X K → ⁅quasithinOmegaOneCenter T, LOf L V₂⁆ ≠ ⊥

variable {G : Type} [Group G] [Finite G]

namespace StarHyp

variable {T L I V₁ V₂ X K : Subgroup G}

theorem isFaithfulLocal_J (hZ : Obl11_1_2StarZL2) (h : StarHyp G T L I V₁ V₂ X K)
    {Y J : Subgroup G} (hTY : T ≤ Y) (hY : pCoreOf 2 Y ≠ ⊥) (hJ : J ∈ cComp Y)
    (hL₂J : LOf L V₂ ≤ J) : quasithinIsFaithfulLocal T J := by
  have hloc := h.isLocal_of_mem_cComp_Y hTY hY hJ
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo h.sylow
  have hchar : QuasithinUnique.CharTwo (J ⊔ T) := by
    have hH : InH (S : Subgroup G) (J ⊔ T) := ⟨hS ▸ le_sup_right, hloc.2.2.2⟩
    exact charTwo_of_inH h.hyp.fsu.qtke.2.1 S hH
  have hV := C1GN.isTwoReducedIn_VZ hchar (isSylowTwoOf_of_quasithinIsSylowTwo h.sylow le_sup_right)
  refine Ch10.SecD.quasithinIsFaithfulLocal_of_isTwoReducedIn hloc hloc.2.1 hchar hV ?_
  intro hb
  apply hZ G T L I V₁ V₂ X K h
  refine eq_bot_iff.mpr ?_
  rw [← hb]
  exact Subgroup.commutator_mono (le_conjClosure _ _) hL₂J

theorem exists_hyp11_J (hfsu : Ch10.StmtFSUChoice) (hRQ : RankTwoQuasisimple)
    (h : StarHyp G T L I V₁ V₂ X K) {J : Subgroup G} (hmax : quasithinIsMaximalLocal T J)
    (hf : quasithinIsFaithfulLocal T J) (hTJ : T ≤ Subgroup.normalizer (J : Set G))
    (hs : Shape11 J 2) : ∃ I' : Subgroup G, Hyp11 G T J I' 2 := by
  obtain ⟨I', hI'⟩ := hfsu G T J h.hyp.fsu.simple h.hyp.fsu.nonabelian h.hyp.fsu.qtke h.sylow
    hmax hf (hRQ _ 2 (by norm_num) hs)
  exact ⟨I', hI', hTJ, by norm_num, hs⟩

end StarHyp

end CFSG.Quasithin.Vol2.Ch11.SecS
