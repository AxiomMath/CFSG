module

public import CFSG.Quasithin.EmptyFaithful.S1413
public import CFSG.Quasithin.Vol2.Ch1Unique

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

theorem stageLemma1416_of_a3 (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    StageLemma1416 := by
  intro G _ _ T Mc h
  have h1413 := stageLemma1413_of_a39 h39 G T h.simple h.qtke h.sylow h.faithful_empty
  obtain ⟨S, hST⟩ := h.exists_sylow
  have hMcH : pCoreOf 2 Mc ≠ ⊥ := pCoreOf_ne_bot_of_isTwoLocal h.mc_max.1
  have p3 : ∀ H : Subgroup G, InH T H →
      perfectCore H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
    intro H hH
    have hH' : InH (S : Subgroup G) H := hST ▸ hH
    have hF : H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ≤ pCoreOf 2 H :=
      charTwo_of_inH h.qtke.2.1 S hH'
    have hZ : quasithinOmegaOneCenter T ≤ quasithinOmegaOneCenter (S : Subgroup G) := by
      rw [hST]
    have hV := isTwoReducedIn_conjClosure H S hH'.1 hF hZ
    exact (h1413 H hH _ hV).trans
      (Subgroup.centralizer_le (le_conjClosure (quasithinOmegaOneCenter T) H))
  have hLMc : ∀ L : Subgroup G, quasithinIsLocal T L → L ≤ Mc := by
    intro L hL
    have hH : InH T (L ⊔ T) := ⟨le_sup_right, hL.2.2.2⟩
    exact (le_perfectCore_of_perfect le_sup_left (perfect_of_mem_cComp hL.2.1)).trans
      ((p3 _ hH).trans h.centralizer_le_mc)
  have hmax_to : ∀ L : Subgroup G, quasithinIsMaximalLocal T L → L ∈ cComp Mc := by
    intro L hL
    exact lemma_1_2_7_one h.qtke h.simple h.nonabelian h37 h39 h.sylow hL
      ⟨sup_le (hLMc L hL.1) h.t_le_mc, hMcH⟩
  have hiff : ∀ L : Subgroup G, quasithinIsMaximalLocal T L ↔ L ∈ cComp Mc := by
    intro L
    refine ⟨hmax_to L, fun hL => ?_⟩
    have hLloc : quasithinIsLocal T L := isLocal_of_mem_cComp_of_sylow
      (isSylowTwoOf_of_quasithinIsSylowTwo h.sylow h.t_le_mc) hMcH hL
    obtain ⟨K, hKmax⟩ := (Set.toFinite {K : Subgroup G | quasithinIsLocal T K ∧ L ≤ K}).exists_maximal
      ⟨L, hLloc, le_rfl⟩
    obtain ⟨⟨hKloc, hLK⟩, hKm⟩ := hKmax
    have hKmax' : quasithinIsMaximalLocal T K := ⟨hKloc, fun K' hK' hKK' =>
      le_antisymm (hKm ⟨hK', hLK.trans hKK'⟩ hKK') hKK'⟩
    have hKc : K ∈ cComp Mc := hmax_to K hKmax'
    have hLK' : L = K := by
      by_contra hne
      exact not_subnormal_of_mem_cComp hKc (lt_of_le_of_ne hLK hne) (ne_bot_of_mem_cComp hL)
        (perfect_of_mem_cComp hL) (subnormal_of_mem_cComp hL)
    rw [hLK']
    exact hKmax'
  refine ⟨fun M V hM hV => h1413 M (inH_of_inM hM) V hV, hiff, fun K hK => ?_,
    fun H hH => ⟨p3 H hH, h.centralizer_le_mc⟩⟩
  have hKmax := (hiff K).mpr hK
  have hU := lemma_1_2_7_three h.qtke h.simple h.nonabelian h37 h38 h39 h.sylow hKmax
  have hMcK : InM (K ⊔ T) Mc := ⟨h.mc_max, sup_le (le_of_mem_cComp hK) h.t_le_mc⟩
  rw [hU.2 Mc hMcK]
  exact hU

end CFSG.Quasithin
