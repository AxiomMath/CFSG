module

public import CFSG.Quasithin.Background.ONanE68Dich
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239ListedInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeEmbedding
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdNative
public import CFSG.Quasithin.Background.ONanE68Setting

public section

namespace CFSG.Quasithin

namespace E6

namespace E68Proof

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native.L239

section Elim

variable {G : Type} [Group G] [Finite G] {T M V U L : Subgroup G}

theorem pCoreOf_centralizer_ne_bot (h : HypE61 T M V) (hU : U ∈ gammaE64 V M) :
    pCoreOf 2 (Subgroup.centralizer (U : Set G)) ≠ ⊥ := fun h0 => hU.2.1 (le_bot_iff.1 (h0 ▸
  C1.le_pCoreOf_of_normalized
    (fun _ hu => Subgroup.mem_centralizer_iff.2 fun _ hu' =>
      B2F.isElemAbelian_comm h.isElemAbelian (hU.1 hu') (hU.1 hu))
    (Subgroup.centralizer_le_normalizer _) (h.isPGroup_V.to_le hU.1)))

theorem le_normalizer_of_not_is121List (h121 : Id2519.Prop121Three) (h : HypE61 T M V)
    (hU : U ∈ gammaE64 V M) (hL : IsComponentIn L (Subgroup.centralizer (U : Set G)))
    (hn : ¬ Id2519.Is121List (↥L ⧸ CFSG.pCore 2 ↥L)) :
    Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have := h.simple
  rcases h121 G h.simple h.nonabelian (qtkeCore_of_cat h.nonabelian h.qtke) _
      (pCoreOf_centralizer_ne_bot h hU) L (Vol2Native.mem_cComp_of_isComponentIn hL) with
    hN | ⟨-, hlist⟩
  · exact hN
  · exact absurd hlist hn

omit [Finite G] in
theorem isNormalListedType_of_pair {R : Subgroup G} (h : IsParabolicPairType L R) :
    IsNormalListedType L := by
  rcases h with h | h | h | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem false_of_pairs (hC129 : ∀ (G : Type) [Group G] [Finite G], ASC129Statement G)
    (hpairs : L239ParabolicPairs) (hnot : L239NotRankOne) (h121 : Id2519.Prop121Three)
    (h : HypE61 T M V) (hU : U ∈ gammaE64 V M)
    (hL : IsComponentIn L (Subgroup.centralizer (U : Set G)))
    (htype : IsParabolicPairType L (T ⊓ Subgroup.centralizer (V : Set G))) : False := by
  have hq : CFSG.IsQuasisimple ↥L := BenderBranch.isQuasisimple_of_isComponentIn hL
  have hnorm := le_normalizer_of_not_is121List h121 h hU hL fun hl =>
    hnot G L hq (isNormalListedType_of_pair htype) (Id2519.a38Types_of_is121List hl)
  have hQH := e6_5_one h hU
  have hQN : T ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    hQH.1.trans hnorm
  have hSyl : IsSylowTwoOf ((T ⊓ Subgroup.centralizer (V : Set G)) ⊓ L) L :=
    RankOneRecog.isSylowTwoOf_inf_of_subnormal hQH hL.1 hL.2.2
  obtain ⟨K₁, K₂, hK₁, hK₂, -, -, hjoin, hN₁, hN₂, hc₁, hc₂, hb₁, hb₂⟩ :=
    hpairs G L _ hq htype h.isPGroup_Q hQN hSyl
  have h1 : K₁ ≤ M :=
    (dich hC129 h hU (hK₁.trans hL.1) hN₁ hc₁).resolve_right hb₁
  have h2 : K₂ ≤ M :=
    (dich hC129 h hU (hK₂.trans hL.1) hN₂ hc₂).resolve_right hb₂
  exact not_le_of_component h hU.1 hL (by rw [← hjoin]; exact sup_le h1 h2)

end Elim

end E68Proof

end E6

end CFSG.Quasithin
