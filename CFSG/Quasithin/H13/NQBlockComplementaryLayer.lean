module

public import CFSG.Quasithin.H13.NQBlockSQTKCcomponents
public import CFSG.Quasithin.H13.NQBlockSourceY
public import CFSG.Quasithin.Vol2.Ch10SecABasic

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

section Layer

variable {G : Type} [Group G] [Finite G]

theorem existsUnique_cComp_of_lFamily (h39 : SQTKCLayerPerfectResidual)
    (hloc : LocalSQTK G) {H S B : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥) (hS : IsSylowTwoOf S H)
    (hBH : B ≤ H) (hB : B ∈ lFamily S) : ∃! L, L ∈ cComp H ∧ B ≤ L := by
  have hQ := Vol2Native.sqtkHypCat_quotient_of_pCoreOf_ne_bot hloc hH
  have := hQ.finite
  have h37 : A37Statement (↥H ⧸ CFSG.pCore 2 ↥H) := Vol2Native.a37ForSQTKCat_proved _ hQ
  have hEC := h39 _ ⟨hQ.sqt, hQ.kgroup⟩ hQ.o2
  obtain ⟨L, hL, hBL⟩ := exists_cComp_ge_of_subgroup_of_cCompSpan_eq hS hBH hB h37 hEC
  exact ⟨L, ⟨hL, hBL⟩, fun L' hL' =>
    Vol2Native.lemma_1_2_4_unique hloc Vol2Native.a37ForSQTKCat_proved hH hB hL'.1 hL hL'.2 hBL⟩

omit [Finite G] in
theorem le_normalizer_nqComplementaryLayer {H A : Subgroup G} (hA : (A.subgroupOf H).Normal)
    (hAH : A ≤ H) : H ≤ normalizer (nqComplementaryLayer H A : Set G) := by
  have key : ∀ g ∈ H, (nqComplementaryLayer H A).map (MulAut.conj g).toMonoidHom ≤
      nqComplementaryLayer H A := by
    intro g hg
    rw [nqComplementaryLayer, Subgroup.map_le_iff_le_comap]
    refine sSup_le fun C hC => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    refine le_sSup ⟨map_conj_mem_cComp hC.1 hg, fun he => hC.2 ?_⟩
    have hAg : A.map (MulAut.conj g).toMonoidHom = A :=
      A38.map_conj_eq_iff.mpr ((Subgroup.normal_subgroupOf_iff_le_normalizer hAH).mp hA hg)
    exact Subgroup.map_injective (MulAut.conj g).injective (he.trans hAg.symm)
  intro h hh
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine le_antisymm (key h hh) ?_
  have h1 := Subgroup.map_mono (f := (MulAut.conj h).toMonoidHom) (key h⁻¹ (H.inv_mem hh))
  rwa [Subgroup.map_map, show (MulAut.conj h).toMonoidHom.comp
      (MulAut.conj h⁻¹).toMonoidHom = MonoidHom.id G by ext; simp; group, Subgroup.map_id] at h1

theorem originalKComplementaryLayerControl_of (h39 : SQTKCLayerPerfectResidual)
    : OriginalKComplementaryLayerControl := by
  intro G _ _ T L M h H hH hKTH hHM
  classical
  have := h.simple
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hloc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  obtain ⟨P, hP1, hP2, hHP⟩ := hH.1
  have hPH : P ≤ H := hHP ▸ Subgroup.le_normalizer
  have hO2 : pCoreOf 2 H ≠ ⊥ := by
    intro hb
    apply hP1
    rw [eq_bot_iff, ← hb]
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hPH (hHP ▸ le_rfl) hP2
  have hTH : T ≤ H := le_sup_right.trans hKTH
  have hTs : IsSylowTwoOf T H :=
    ⟨hTH, h.sylow.1, fun h2 => h.sylow.2 (h2.trans (Subgroup.relIndex_dvd_index_of_le hTH))⟩
  obtain ⟨R, hR⟩ := exists_originalCentralizer (h.t_le.trans h.eq_normalizer.le)
  obtain ⟨-, -, -, -, -, -, -, -, -, hTK, hKc, -, -⟩ := original_radical_supplement h.sylow.1
    h.maximal_local.1.2.2.1 (h.eq_normalizer ▸ h.t_le) h.maximal_local.1.2.1 hR
  have hKH : nqOriginalK T L ≤ H := le_sup_left.trans hKTH
  obtain ⟨A, ⟨hA, hKA⟩, huniq⟩ := existsUnique_cComp_of_lFamily h39 hloc hO2 hTs hKH hKc
  have hAn : (A.subgroupOf H).Normal := Vol2Native.lemma_1_2_4_normal hloc
    Vol2Native.a37ForSQTKCat_proved Vol2.Ch10.SecA.a38ForSQTKCat_proved hO2 hTs hKc hKA hA hTK
  refine ⟨A, hA, hKA, fun A' hA' hKA' => huniq A' ⟨hA', hKA'⟩, ?_⟩
  set Y := nqComplementaryLayer H A with hYdef
  have hAH : A ≤ H := le_of_mem_cComp hA
  have hYH : Y ≤ H := sSup_le fun C hC => le_of_mem_cComp hC.1
  have hHY := le_normalizer_nqComplementaryLayer hAn hAH
  have hHQ : H ≤ normalizer (pCoreOf 2 Y : Set G) := by
    have h1 := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (CFSG.pCore 2 ↥Y)
    have e : (CFSG.pCore 2 ↥Y).map Y.subtype = pCoreOf 2 Y := by
      unfold pCoreOf
      try with_reducible rfl
    rw [e] at h1
    exact hHY.trans h1
  have hAC : ∀ C ∈ cComp H, C ≠ A → ⁅A, C⁆ ≤ pCoreOf 2 Y := by
    intro C hC hCA
    have h1 := (Vol2Native.lemma_1_2_1_two hloc Vol2Native.a37ForSQTKCat_proved hO2 hA hC
      (Ne.symm hCA)).1
    have hCY : C ≤ Y := le_sSup ⟨hC, hCA⟩
    have hsub : IsSubnormal C Y := A4.subnormal_of_le_of_le (subnormal_of_mem_cComp hC) hCY hYH
    exact h1.trans (inf_le_right.trans (A4.pCoreOf_le_of_subnormal 2 hsub))
  have hAY : ⁅A, Y⁆ ≤ pCoreOf 2 Y := by
    rw [Subgroup.commutator_le]
    intro a ha y hy
    let S : Subgroup G :=
      { carrier := {y | y ∈ Y ∧ ⁅a, y⁆ ∈ pCoreOf 2 Y}
        one_mem' := ⟨Y.one_mem, by rw [commutatorElement_one_right]; exact (pCoreOf 2 Y).one_mem⟩
        mul_mem' := by
          rintro y₁ y₂ ⟨hy₁, hc₁⟩ ⟨hy₂, hc₂⟩
          refine ⟨Y.mul_mem hy₁ hy₂, ?_⟩
          have h2 : y₁ * ⁅a, y₂⁆ * y₁⁻¹ ∈ pCoreOf 2 Y :=
            (Subgroup.mem_normalizer_iff.mp (hHQ (hYH hy₁)) _).mp hc₂
          have e : ⁅a, y₁ * y₂⁆ = ⁅a, y₁⁆ * (y₁ * ⁅a, y₂⁆ * y₁⁻¹) := by
            simp only [commutatorElement_def]
            group
          rw [e]
          exact (pCoreOf 2 Y).mul_mem hc₁ h2
        inv_mem' := by
          rintro y ⟨hy, hc⟩
          refine ⟨Y.inv_mem hy, ?_⟩
          have h2 : y⁻¹ * ⁅a, y⁆⁻¹ * y⁻¹⁻¹ ∈ pCoreOf 2 Y :=
            (Subgroup.mem_normalizer_iff.mp (hHQ (hYH (Y.inv_mem hy))) _).mp
              ((pCoreOf 2 Y).inv_mem hc)
          have e : ⁅a, y⁻¹⁆ = y⁻¹ * ⁅a, y⁆⁻¹ * y⁻¹⁻¹ := by
            simp only [commutatorElement_def]
            group
          rw [e]
          exact h2 }
    have hSY : Y ≤ S := sSup_le fun C hC c hc =>
      ⟨le_sSup hC hc, hAC C hC.1 hC.2 (Subgroup.commutator_mem_commutator ha hc)⟩
    exact (hSY hy).2
  exact (Subgroup.commutator_mono hKA le_rfl).trans hAY

theorem originalKEscapingSourceY_of_cLayer (h39 : SQTKCLayerPerfectResidual)
    (hF : OriginalKContainingConfinement) (hA : AllComponentsContainedSourceY)
    (hB : ComplementaryEscapeSimpleSourceY) : OriginalKEscapingSourceY :=
  originalKEscapingSourceY_of (originalKComplementaryLayerControl_of h39) hF hA hB

@[expose] def SylowNormalizedLocalNormalComponent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    quasithinIsQTKECat G → ∀ H S B : Subgroup G, pCoreOf 2 H ≠ ⊥ → IsSylowTwoOf S H → B ≤ H →
      quasithinIsLocal S B → S ≤ normalizer (B : Set G) →
      ∃ L : Subgroup G, (L ∈ cComp H ∧ B ≤ L) ∧
        (∀ L' : Subgroup G, L' ∈ cComp H ∧ B ≤ L' → L' = L) ∧ (L.subgroupOf H).Normal ∧
        (quasithinIsMaximalLocal S B → L = B ∧ (B.subgroupOf H).Normal)

end Layer

end CFSG.Quasithin.H13.NQBlock
