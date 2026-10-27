module

public import CFSG.Adapters.StatedClassicalUnitaryOrders
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Cover

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c1_card_isU4 {X : Type} [Group X] (h : IsU4 X 1) : Nat.card X = 25920 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_four_two
    (CFSG.Blueprint.LieModel.statedClassicalModel h (by decide))

theorem s16c1_card_isOmegaMinus_six {X : Type} [Group X] (h : IsOmegaMinus X 6 1) :
    Nat.card X = 25920 :=
  s16c1_card_isU4 (isU4_of_isOmegaMinus_six h)

theorem s16c1_isSimpleGroup_of_isOmegaMinus_six {X : Type} [Group X] (h : IsOmegaMinus X 6 1) :
    IsSimpleGroup X := by
  have hdiv : (6 : ℕ) / 2 = 3 := by norm_num
  simp only [IsOmegaMinus, hdiv] at h
  obtain ⟨-, K, hKfield, hKfinite, b, c, hcard, hirr, ⟨e⟩⟩ := h
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  haveI : Fintype K := Fintype.ofFinite K
  have hcard2 : Nat.card K = 2 := by rw [hcard]; norm_num
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 :=
    charP_of_card_eq_prime (p := 2) (by rw [Fintype.card_eq_nat_card, hcard2])
  have hfacts :=
    CFSG.ComponentClassification.RankTwoClassical.isSimpleGroup_statedOmega_quadMinus_small
      (n := 3) (b := b) (c := c) (Or.inr rfl) hirr
  haveI : IsSimpleGroup (StatedOmega (StatedQuadMinus 3 K b c)) := hfacts.1
  have hSbot : (StatedScalars (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K).subgroupOf
      (StatedOmega (StatedQuadMinus 3 K b c)) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((StatedScalars (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K).subgroupOf
        (StatedOmega (StatedQuadMinus 3 K b c))) with hS | hS
    · exact hS
    · exfalso
      have hle : StatedOmega (StatedQuadMinus 3 K b c) ≤
          StatedScalars (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K :=
        Subgroup.subgroupOf_eq_top.1 hS
      exact hfacts.2.2 fun x y => Subtype.ext <| by
        have hx : (x : Matrix.GeneralLinearGroup (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) ∈
            Subgroup.center _ := by
          rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
          exact hle x.2
        exact (Subgroup.mem_center_iff.mp hx (y : _)).symm
  have eN : StatedProj (StatedOmega (StatedQuadMinus 3 K b c)) ≃*
      StatedOmega (StatedQuadMinus 3 K b c) :=
    (QuotientGroup.quotientMulEquivOfEq hSbot).trans QuotientGroup.quotientBot
  have eX : X ≃* StatedOmega (StatedQuadMinus 3 K b c) := e.trans eN
  exact eX.isSimpleGroup

theorem s16c1_card_of_isE16A5 {X : Type} [Group X] (h : IsE16A5 X) : Nat.card X = 960 := by
  obtain ⟨N, hN, hNe, hAlt⟩ := h
  haveI := hN
  have hNcard : Nat.card ↥N = 16 := by
    obtain ⟨e⟩ := hNe
    rw [Nat.card_congr e.toEquiv,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 4 → ZMod 2) ≃ (Fin 4 → ZMod 2)),
      Nat.card_fun, Nat.card_fin, Nat.card_zmod]
    norm_num
  have hQcard : Nat.card (X ⧸ N) = 60 := by
    obtain ⟨e⟩ := hAlt
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  calc Nat.card X = Nat.card (X ⧸ N) * Nat.card ↥N :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup N
    _ = 60 * 16 := by rw [hQcard, hNcard]
    _ = 960 := by norm_num

theorem s16c1_le_stabTil (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) : L ≤ stabTil V₀ V :=
  hS.setting.hyp151.le.trans
    (le_stabTil hS.setting.hyp151.hyp125.pairFacts.le_normalizer
      hS.setting.hyp151.hyp125.pairFacts.le_normalizer₀)

private theorem s16c1_ker_actTil (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (hc : Case167_1 D V₀ V hV L) (hU4 : IsU4 (Bar2 L) 1) :
    ((actTil V₀ V hV).comp (Subgroup.inclusion (s16c1_le_stabTil D hS))).ker =
      CFSG.pCore 2 ↥L := by
  let φ : ↥L →* MulAut (Vtil V₀ V hV) :=
    (actTil V₀ V hV).comp (Subgroup.inclusion (s16c1_le_stabTil D hS))
  let O : Subgroup ↥L := CFSG.pCore 2 ↥L
  have hφrange : φ.range = lBar V₀ V hV L := by
    show ((actTil V₀ V hV).comp (Subgroup.inclusion (s16c1_le_stabTil D hS))).range =
      lBar V₀ V hV L
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  have hcard_range : Nat.card ↥φ.range = 25920 := by
    rw [hφrange]
    exact s16c1_card_isOmegaMinus_six hc.1
  have hcard_bar2 : Nat.card (Bar2 L) = 25920 := s16c1_card_isU4 hU4
  haveI : IsSimpleGroup ↥(lBar V₀ V hV L) :=
    s16c1_isSimpleGroup_of_isOmegaMinus_six hc.1
  have hsimple : IsSimpleGroup ↥φ.range := by
    rw [hφrange]
    infer_instance
  have hOmap_normal : (O.map φ.rangeRestrict).Normal :=
    Subgroup.Normal.map (CFSG.pCore_normal (p := 2) (G := ↥L)) φ.rangeRestrict
      φ.rangeRestrict_surjective
  have hOmap_pg : IsPGroup 2 (O.map φ.rangeRestrict) :=
    IsPGroup.map (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) φ.rangeRestrict
  have hOker : O ≤ φ.ker := by
    haveI := hOmap_normal
    rcases hsimple.eq_bot_or_eq_top_of_normal (O.map φ.rangeRestrict) with hbot | htop
    · rw [← MonoidHom.ker_rangeRestrict φ]
      exact (Subgroup.map_eq_bot_iff (H := O) (f := φ.rangeRestrict)).mp hbot
    · exfalso
      have hsurj : Function.Surjective (O.map φ.rangeRestrict).subtype := by
        intro x
        exact ⟨⟨x, by rw [htop]; trivial⟩, rfl⟩
      have hpg_range : IsPGroup 2 ↥φ.range := hOmap_pg.of_surjective _ hsurj
      obtain ⟨k, hk⟩ := hpg_range.exists_card_eq
      rw [hcard_range] at hk
      have h3 : 3 ∣ 2 ^ k := by rw [← hk]; norm_num
      exact (by norm_num : ¬ (3 : ℕ) ∣ 2) (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
  have hker : φ.ker = O := by
    refine le_antisymm ?_ hOker
    have hrel := Subgroup.relIndex_mul_index (H := O) (K := φ.ker) hOker
    have hker_index : φ.ker.index = 25920 := by
      rw [Subgroup.index]
      exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv).trans hcard_range
    have hO_index : O.index = 25920 := by
      rw [Subgroup.index]
      change Nat.card (Bar2 L) = 25920
      exact hcard_bar2
    rw [hker_index, hO_index] at hrel
    exact Subgroup.relIndex_eq_one.mp (by omega)
  exact hker

theorem s16c1_actTil_eq_one_iff (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (hc : Case167_1 D V₀ V hV L) (hU4 : IsU4 (Bar2 L) 1)
    (g : ↥(stabTil V₀ V)) (hg : (g : G) ∈ L) :
    actTil V₀ V hV g = 1 ↔ (g : G) ∈ pCoreOf 2 L := by
  let φ : ↥L →* MulAut (Vtil V₀ V hV) :=
    (actTil V₀ V hV).comp (Subgroup.inclusion (s16c1_le_stabTil D hS))
  have hker : φ.ker = CFSG.pCore 2 ↥L := by
    show ((actTil V₀ V hV).comp (Subgroup.inclusion (s16c1_le_stabTil D hS))).ker =
      CFSG.pCore 2 ↥L
    exact s16c1_ker_actTil D hS hc hU4
  have hmem : φ ⟨(g : G), hg⟩ = 1 ↔ (g : G) ∈ pCoreOf 2 L := by
    rw [← MonoidHom.mem_ker, hker]
    constructor
    · intro hx
      exact Subgroup.mem_map.mpr ⟨⟨(g : G), hg⟩, hx, rfl⟩
    · rintro ⟨o, ho, hoo⟩
      have ho' : o = ⟨(g : G), hg⟩ := Subtype.ext hoo
      simpa [ho'] using ho
  have hφg : φ ⟨(g : G), hg⟩ = actTil V₀ V hV g :=
    congrArg (actTil V₀ V hV) (Subtype.ext rfl)
  rw [← hφg]
  exact hmem

theorem s16c1_card_barSub_eq_card_starImg (D : Data G) {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hS : Sect16 D V₀ V L hV) (hc : Case167_1 D V₀ V hV L)
    (hU4 : IsU4 (Bar2 L) 1) {Y : Subgroup G} (hYL : Y ≤ L) :
    Nat.card ↥(barSub V₀ V hV Y) = Nat.card ↥(starImg L Y) := by
  let φ : ↥L →* MulAut (Vtil V₀ V hV) :=
    (actTil V₀ V hV).comp (Subgroup.inclusion (s16c1_le_stabTil D hS))
  let π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  let Y' : Subgroup ↥L := Y.subgroupOf L
  let ψ : ↥Y' →* MulAut (Vtil V₀ V hV) := φ.comp Y'.subtype
  let ρ : ↥Y' →* Bar2 L := π.comp Y'.subtype
  have hkerφ : φ.ker = CFSG.pCore 2 ↥L := by
    show ((actTil V₀ V hV).comp (Subgroup.inclusion (s16c1_le_stabTil D hS))).ker =
      CFSG.pCore 2 ↥L
    exact s16c1_ker_actTil D hS hc hU4
  have hkerπ : π.ker = CFSG.pCore 2 ↥L := by
    show (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).ker = CFSG.pCore 2 ↥L
    rw [QuotientGroup.ker_mk']
  have hkerψρ : ψ.ker = ρ.ker := by
    show (φ.comp Y'.subtype).ker = (π.comp Y'.subtype).ker
    rw [← MonoidHom.comap_ker φ Y'.subtype, ← MonoidHom.comap_ker π Y'.subtype,
      hkerφ, hkerπ]
  have hYbar : barSub V₀ V hV Y = Y'.map φ := by
    ext φ'
    rw [mem_barSub V₀ V hV Y φ', Subgroup.mem_map]
    constructor
    · rintro ⟨g, hgY, rfl⟩
      refine ⟨⟨(g : G), hYL hgY⟩, hgY, ?_⟩
      show φ ⟨(g : G), hYL hgY⟩ = actTil V₀ V hV g
      exact congrArg (actTil V₀ V hV)
        (Subtype.ext (rfl : ((Subgroup.inclusion (s16c1_le_stabTil D hS))
          ⟨(g : G), hYL hgY⟩ : G) = (g : G)))
    · rintro ⟨y, hy, rfl⟩
      exact actTil_mem_barSub V₀ V hV hy (s16c1_le_stabTil D hS y.2)
  have hYstar : starImg L Y = Y'.map π := rfl
  have hrangeψ : ψ.range = Y'.map φ := by
    show (φ.comp Y'.subtype).range = Y'.map φ
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hrangeρ : ρ.range = Y'.map π := by
    show (π.comp Y'.subtype).range = Y'.map π
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hcardψ : Nat.card ↥(Y'.map φ) = Nat.card (↥Y' ⧸ ψ.ker) := by
    rw [← hrangeψ]
    exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv).symm
  have hcardρ : Nat.card ↥(Y'.map π) = Nat.card (↥Y' ⧸ ρ.ker) := by
    rw [← hrangeρ]
    exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv).symm
  calc Nat.card ↥(barSub V₀ V hV Y)
      = Nat.card ↥(Y'.map φ) := by rw [hYbar]
    _ = Nat.card (↥Y' ⧸ ψ.ker) := hcardψ
    _ = Nat.card (↥Y' ⧸ ρ.ker) := by rw [hkerψρ]
    _ = Nat.card ↥(Y'.map π) := hcardρ.symm
    _ = Nat.card ↥(starImg L Y) := by rw [hYstar]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
