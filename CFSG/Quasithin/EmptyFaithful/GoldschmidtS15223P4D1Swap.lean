module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4Ctx
public import CFSG.Quasithin.EmptyFaithful.SBc2G27
public import CFSG.Quasithin.EmptyFaithful.S152U21
public import CFSG.Quasithin.Background.F9Comp

public section

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open

namespace CFSG.Quasithin.S15223P4.D1

variable {G : Type} [Group G] [Finite G]
  {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I X : Subgroup G}

theorem normal_or_swap (c : P4Ctx T Mc M H B₀ I X) (h37 : A37ForSQTK) (h38 : A38ForSQTK) :
    I ≤ Subgroup.normalizer (X : Set G) ∨
      ∃ s ∈ sOf152 T Mc M B₀, conjSub s X ∈ cComp I ∧ conjSub s X ≠ X ∧
        ⁅X, conjSub s X⁆ ≤ pCoreOf 2 I := by
  have hs := c.setting
  have hQ := sqtkHyp_quotient_of_pCoreOf_ne_bot hs.qtfe.qtke hs.qtfe.simple
    hs.qtfe.nonabelian c.min.1.inH.2
  have h1 := lemma_1_2_1_three hs.qtfe.qtke hs.qtfe.simple hs.qtfe.nonabelian h37 h38
    c.min.1.inH.2 c.comp
  rcases h1 with hn | ⟨hcard, -⟩
  · exact Or.inl ((Subgroup.normal_subgroupOf_iff_le_normalizer c.X_le_I).mp hn)
  right
  obtain ⟨s, hsS, hsn⟩ := SBc2.exists_not_mem_normalizer_of_ncard_two c.sylow hcard
  have hsI : s ∈ I := S_le_I152 c.inputs hsS
  have hne : conjSub s X ≠ X := fun h => hsn (mem_normalizer_of_conjSub_eq152 h)
  have hX' : conjSub s X ∈ cComp I := conjSub_mem_cComp_of_mem c.comp hsI
  have hcomm : ⁅X, conjSub s X⁆ ≤ pCoreOf 2 I :=
    commutator_le_pCoreOf_of_ne (h37 _ hQ) c.comp hX' (Ne.symm hne)
  exact ⟨s, hsS, hX', hne, hcomm⟩

end CFSG.Quasithin.S15223P4.D1
