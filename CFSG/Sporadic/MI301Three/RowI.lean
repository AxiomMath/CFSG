module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeAMain
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017MRankThreeCover
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Defs
public import CFSG.Sporadic.MI301.LayerQuot

public section

namespace CFSG.Sporadic.MI301Three

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S8 CFSG.HardMathSupport.Dickson.I271.TabMThreeA
  CFSG.Monster.Existence
open scoped commutatorElement

private theorem layer_eq_and_isTypeWithCenter {G : Type} [Group G] [Finite G] {C : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple ↥C) (hp : 3 ∣ Nat.card ↥C)
    (hZ : Nat.card ↥(Subgroup.center ↥C) = 3)
    (e : ↥C ⧸ Subgroup.center ↥C ≃* CFSG.Blueprint.NativeSporadic.Fi24prime)
    (b : CFSG.Blueprint.NativeSporadic.Fi24prime ≃* TauCeti.SporadicName.Fi24Prime.Group) :
    GLAPLayer 3 C = C ∧ IsTypeWithCenter 3 C (sporIs .Fi24Prime) 3 := by
  have hZp : IsPGroup 3 ↥(Subgroup.center ↥C) := IsPGroup.of_card (n := 1) (by rw [hZ, pow_one])
  have hn : (C.subgroupOf C).Normal := by
    rw [Subgroup.subgroupOf_self]
    infer_instance
  have hc : ⁅C, C⁆ ≤ C := Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact C.mul_mem (C.mul_mem (C.mul_mem ha hb) (C.inv_mem ha)) (C.inv_mem hb)
  refine ⟨CFSG.Sporadic.MI301.glaPLayer_eq_of_isQuasisimple_normal Nat.prime_three le_rfl hn hq hp
    hZp hc, ?_⟩
  obtain ⟨f⟩ := CFSG.Sporadic.MI301.nonempty_pQuot_equiv_self_of_isQuasisimple Nat.prime_three hq
    hp hZp
  exact ⟨⟨TauCeti.CFSGIndex.sporadic .Fi24Prime, rfl,
    ⟨((QuotientGroup.congr _ _ f (Subgroup.map_center_eq f)).trans e).trans b⟩⟩,
    (Nat.card_congr (Subgroup.centerCongr f).toEquiv).trans hZ⟩

section Zeta


theorem rowI_zetaM (hB3 : CFSG.HardMathSupport.Dickson.I271.TabBThreeACard)
    (hG : CFSG.Monster.Generated.Gmat = CFSG.Monster.Griess.AutO) :
    CFSG.LocalAnalysis.GLTheoremA.H301.rowIOf 3
        (CFSG.HardMathSupport.Dickson.I271.TabMThreeA.zetaM hG) =
      Subgroup.centralizer ({CFSG.HardMathSupport.Dickson.I271.TabMThreeA.zetaM hG} :
        Set CFSG.Monster.Existence.MGriess) ∧
    CFSG.LocalAnalysis.GLTheoremA.S8.RowI .m3 3 (CFSG.LocalAnalysis.GLTheoremA.H301.rowIOf 3
      (CFSG.HardMathSupport.Dickson.I271.TabMThreeA.zetaM hG)) := by
  obtain ⟨hζ3, -, -, hq, ⟨f⟩⟩ := zetaM_spec hB3 hG
  have h := ker_yMc_le hG
  obtain ⟨-, -, -, hker⟩ := ker_coverHom_yMc hG h
  have hZ := CFSG.LocalAnalysis.GLTheoremA.H1017.card_center_centralizer_of_cover
    (centralizer_zetaM_eq_range hB3 hG) (coverHom_surjective h yJ_surjective)
    CFSG.Sporadic.Fi24.center_J hker
  rw [hζ3] at hZ
  have hζC : zetaM hG ∈ Subgroup.centralizer ({zetaM hG} : Set MGriess) :=
    Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hp : 3 ∣ Nat.card ↥(Subgroup.centralizer ({zetaM hG} : Set MGriess)) := by
    have := orderOf_dvd_natCard
      (⟨zetaM hG, hζC⟩ : ↥(Subgroup.centralizer ({zetaM hG} : Set MGriess)))
    rwa [Subgroup.orderOf_mk, hζ3] at this
  obtain ⟨hL, hI⟩ := layer_eq_and_isTypeWithCenter hq hp hZ f
    CFSG.Sporadic.Bridge.Fi24.nonempty_mulEquiv.some
  refine ⟨hL, ?_⟩
  show IsTypeWithCenter 3 (H301.rowIOf 3 (zetaM hG)) (sporIs .Fi24Prime) 3
  have hr : H301.rowIOf 3 (zetaM hG) = Subgroup.centralizer ({zetaM hG} : Set MGriess) := hL
  rw [hr]
  exact hI

end Zeta

end CFSG.Sporadic.MI301Three
