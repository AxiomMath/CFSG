module

public import CFSG.Quasithin.Vol2.Ch11SecSRole5
public import CFSG.Quasithin.Vol2.Ch11SecQ9aM23
public import CFSG.Quasithin.Vol2.Ch11SecSZK
public import CFSG.Quasithin.Vol2.Ch11SecSZK3
public import CFSG.Quasithin.Vol2.Ch11SecSZK4

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin SecA

theorem obl11_1_2StarSymRole'_of (hNot : FactL34NotL42) (hL3 : FactList3Table) (hF : Facts12)
    (hC : CartanFacts) (hF11 : Facts11) (hN : NatFacts) (h1102 : Stmt11_0_2)
    (h318 : A318Facts) (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (h312 : A312ForSQTK) : Obl11_1_2StarSymRole' := by
  intro G _ _ T L I V₁ V₂ X K K₀ I' U₁ U₂ h hK0 _ _ _ _ _ _ _ hJ hU₁ hU₂ _ _ hR1 _ hcart hKU
  have hS := isSylowTwoOf_of_quasithinIsSylowTwo h.sylow hU₁.2
  have hH := pCoreOf_normalizer_ne_bot hJ hU₁ le_rfl
  have hKH : K ≤ Subgroup.normalizer (U₁ : Set G) :=
    hKU.trans (Subgroup.centralizer_le_normalizer _)
  have hB : K ∈ lFamily T := mem_lFamily_of_isLocal h.isLocal_K
  obtain ⟨K', ⟨hK', hKK'⟩, -⟩ := CFSG.Quasithin.lemma_1_2_4_existsUnique h.hyp.fsu.qtke
    h.hyp.fsu.simple h.hyp.fsu.nonabelian h37 h39 hH hS hKH hB
  obtain ⟨e₁⟩ := modO2Image_quotEquiv hKH
  have hD := l34Data_of (isPSL_of_mulEquiv e₁.symm h.psl)
  rcases CFSG.Quasithin.lemma_1_2_4_list h.hyp.fsu.qtke h.hyp.fsu.simple h.hyp.fsu.nonabelian
      h312 hH hS hKH hB hK' hKK' with heq | hc | hnq
  · obtain rfl : K = K' := eq_of_modO2Image_eq hS (le_of_mem_cComp hK') hKK'
      (perfect_of_mem_cComp hK') h.T_le_normalizer_K heq
    exact hK'
  · exfalso
    have hn := CFSG.Quasithin.lemma_1_2_4_normal h.hyp.fsu.qtke h.hyp.fsu.simple
      h.hyp.fsu.nonabelian h37 h38 hH hS hB hKK' hK' h.T_le_normalizer_K
    have hNK' : Subgroup.normalizer (U₁ : Set G) ≤ Subgroup.normalizer (K' : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (le_of_mem_cComp hK')).mp hn
    obtain ⟨e₂⟩ := modO2_mulEquiv hK'
    obtain ⟨f⟩ := hD.of_a312Case hNot hc
    have hLK' : LOf (K₀ ⊔ LOf L V₂) U₁ ≤ K' := by
      rw [hR1]
      exact hK0.2.1.trans hKK'
    exact C11P9A.false_of_M23 hL3 hF hC hF11 hN h318 h36 h38 h1102 hJ hU₁ hU₂ hcart hK' hNK'
      hLK' ⟨e₂.trans f⟩
  · exact (hD.false_of_nonquasi (Subgroup.map_mono fun x hx => hKK' hx) hnq).elim

end CFSG.Quasithin.Vol2.Ch11.SecS
