module

public import CFSG.Quasithin.Vol2.Ch11SecS12ZA
public import CFSG.Quasithin.Vol2.Ch11SecBFacts22
public import CFSG.Quasithin.Vol2.Ch11StatementsInputs

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G] {T L I V₁ V₂ X K : Subgroup G}

theorem isUniqueM_lXOne (h4213 : TmpL6_4_2_13) (hNot4213 : SecB.FactNot4213) (h331 : Stmt3_3_1)
    (hC : SecS.CartanFacts) (hN : SecA.NatFacts) (hG2 : SecA.FactG2DerivedOrder)
    (hFb : SecA.Facts12b) (h1102 : Stmt11_0_2) (h : SecS.StarHyp G T L I V₁ V₂ X K)
    (hSL3 : KindSL3 L (fsuV T I) 2)
    (hO2 : pCoreOf 2 (lXOne L (SecA.xOne X (LOf L V₁))) ≠ ⊥) :
    IsUniqueM (lXOne L (SecA.xOne X (LOf L V₁))) (Subgroup.normalizer (L : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc := (SecS.cartan_of hC hN hG2 h1102 h.hyp h.v₁ h.v₂ h.cartan).1
  have hLperf : ⁅L, L⁆ = L := SecD.perfect_of_hyp11 h.hyp
  have hSL := isSL3_four_of h1102 h.hyp hSL3
  have hX₁p : IsPGroup 3 ↥(SecA.xOne X (LOf L V₁)) := IsPGroup.of_card (n := 1) (by
    rw [hc.cardX₁, pow_one])
  have hcov : ∀ l ∈ L, ∃ b ∈ pCoreOf 2 L,
      l * b ∈ Subgroup.normalizer (SecA.xOne X (LOf L V₁) : Set G) := by
    intro l hl
    obtain ⟨b, hb, hlb⟩ := exists_mul_mem_centralizer hX₁p
      (fun x hx => Subgroup.le_normalizer ((h.cartan.1 hx.1).1)) (fun x hx l hl =>
        SecA.C11P9B.commutator_mem_of_isSL3 hFb hN h1102 h.hyp h.v₁ h.v₂ h.cartan hSL hx hl) hl
    exact ⟨b, hb, Subgroup.centralizer_le_normalizer _ hlb⟩
  have hXL : lXOne L (SecA.xOne X (LOf L V₁)) ≤ L := (perfectCore_le _).trans inf_le_left
  have hXM : lXOne L (SecA.xOne X (LOf L V₁)) ≤ Subgroup.normalizer (L : Set G) :=
    hXL.trans Subgroup.le_normalizer
  have hH421 : Ch10.TmpL6_Hyp4_2_1 G T (Subgroup.normalizer (L : Set G)) L :=
    ⟨h.hyp.fsu.simple, h.hyp.fsu.nonabelian, h.hyp.fsu.qtke, h.hyp.fsu.sylow,
      SecA.isMaxTwoLocal_M h331 h.hyp, h.hyp.normal, h.hyp.fsu.maximal, h.hyp.fsu.faithful,
      Subgroup.le_normalizer, h.hyp.fsu.quasisimple⟩
  have hconj : ∀ Y : Subgroup G, Y ≤ Subgroup.normalizer (L : Set G) →
      conjSubgroupsBy Y L = {L} := by
    intro Y hY
    ext J
    simp only [conjSubgroupsBy, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      ext y
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp (hY hx) z).mp hz
      · intro hy
        refine ⟨x⁻¹ * y * x, ?_, by simp [mul_assoc]⟩
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hY hx)) y).mp hy
        simpa [mul_assoc] using this
    · rintro rfl
      refine ⟨1, Y.one_mem, ?_⟩
      ext y
      simp
  have hNot : IsNotation4211 T (Subgroup.normalizer (L : Set G)) L
      (lXOne L (SecA.xOne X (LOf L V₁))) := by
    refine ⟨hXM, fun l hl => ?_, ?_, hO2⟩
    · obtain ⟨l', hl', hll⟩ := exists_lXOne_mul hLperf hcov hl
      exact Set.mem_mul.mpr ⟨l', hl', l'⁻¹ * l, pCoreOf_le_pCoreOf_LT h.hyp hll,
        mul_inv_cancel_left l' l⟩
    · rw [hconj T h.hyp.normal, hconj _ hXM]
  rcases h4213 G T _ L _ hH421 hNot with hU | ⟨hC4, -⟩ | hO
  · exact hU
  · exact (hNot4213 G T _ L _ 2 le_rfl h.hyp.shape (Or.inl hC4)).elim
  · exact (hNot4213 G T _ L _ 2 le_rfl h.hyp.shape (Or.inr hO)).elim

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12
