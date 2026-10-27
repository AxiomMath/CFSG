module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420SuzCo1Centre
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeALeech
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301LayerQuot
public import CFSG.Sporadic.MI301.LayerQuot

public section

namespace CFSG.Sporadic.MI301Three

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block
  CFSG.HardMathSupport.Dickson.I271 CFSG.HardMathSupport.Dickson.I271.TabCo1
  CFSG.LieType.Multipliers.U43
open scoped commutatorElement

private theorem commutator_le_of_card_le_two_mul {G : Type} [Group G] [Finite G]
    {H J : Subgroup G} (hJH : J ≤ H) (hcard : Nat.card ↥H ≤ 2 * Nat.card ↥J) : ⁅H, H⁆ ≤ J := by
  set J' : Subgroup ↥H := J.subgroupOf H
  have hJ' : Nat.card ↥J' = Nat.card ↥J :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJH).toEquiv
  have hidx := J'.card_mul_index
  rw [hJ'] at hidx
  have hle : J'.index ≤ 2 := by
    refine Nat.le_of_mul_le_mul_left ?_ (Nat.card_pos (α := ↥J))
    rw [hidx]
    linarith
  have hne : J'.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rw [Subgroup.commutator_le]
  intro g₁ h₁ g₂ h₂
  set a : ↥H := ⟨g₁, h₁⟩
  set b : ↥H := ⟨g₂, h₂⟩
  have key : ⁅a, b⁆ ∈ J' := by
    obtain hI | hI : J'.index = 1 ∨ J'.index = 2 := by omega
    · rw [Subgroup.index_eq_one.1 hI]
      exact Subgroup.mem_top _
    · have h2 : ∀ c d : ↥H, c * d ∈ J' ↔ (c ∈ J' ↔ d ∈ J') := fun c d =>
        Subgroup.mul_mem_iff_of_index_two hI
      have hab : ⁅a, b⁆ = a * b * (a⁻¹ * b⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [hab, h2, h2, h2, inv_mem_iff, inv_mem_iff]
  exact (Subgroup.mem_subgroupOf).1 key

section Model


private theorem nonempty_centralizer_co1MatEquiv (x : CFSG.Blueprint.NativeSporadic.Co1) :
    Nonempty (↥(Subgroup.centralizer ({x} : Set CFSG.Blueprint.NativeSporadic.Co1)) ≃*
      ↥(Subgroup.centralizer ({co1MatEquiv x} : Set ↥GA))) :=
  ⟨{ toFun := fun c => ⟨co1MatEquiv c, by
        have h := Subgroup.mem_centralizer_singleton_iff.1 c.2
        rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, h]⟩
     invFun := fun c => ⟨co1MatEquiv.symm c, by
        have h := Subgroup.mem_centralizer_singleton_iff.1 c.2
        rw [Subgroup.mem_centralizer_singleton_iff]
        apply co1MatEquiv.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply, h]⟩
     left_inv := fun c => Subtype.ext (co1MatEquiv.symm_apply_apply _)
     right_inv := fun c => Subtype.ext (co1MatEquiv.apply_symm_apply _)
     map_mul' := fun a b => Subtype.ext (map_mul co1MatEquiv a.1 b.1) }⟩

end Model

section Root


private theorem exists_centralizer_equiv {y : CFSG.Blueprint.NativeSporadic.Co1}
    (hy : IsConj TabMThreeALeech.c0 y) :
    ∃ g : ↥GA, MRep (TabCo1ThreeB.rootRows3B ()) (g : GL24) ∧
      Nonempty (↥(Subgroup.centralizer ({y} : Set CFSG.Blueprint.NativeSporadic.Co1)) ≃*
        ↥(Subgroup.centralizer ({(g : GL24)} : Set GL24) ⊓ GA)) := by
  obtain ⟨v, hv⟩ := isConj_iff.1 hy
  obtain ⟨u, x, hu, hx⟩ := TabMThreeALeech.exists_conj_root
  have hwx : MulAut.conj (v * u) x = y := by
    rw [MulAut.conj_apply, ← hv, hu]
    group
  have h1 := CFSG.HardMathSupport.Dickson.I271.map_centralizer_singleton (MulAut.conj (v * u)) x
  rw [hwx] at h1
  have h3 := CFSG.HardMathSupport.Dickson.I271.map_centralizer_subtype' GA (co1MatEquiv x)
  obtain ⟨e₂⟩ := nonempty_centralizer_co1MatEquiv x
  exact ⟨co1MatEquiv x, hx, ⟨(((MulAut.conj (v * u)).subgroupMap _).trans
    (MulEquiv.subgroupCongr h1)).symm.trans (e₂.trans
      (((Subgroup.centralizer _).equivMapOfInjective GA.subtype GA.subtype_injective).trans
        (MulEquiv.subgroupCongr h3)))⟩⟩

end Root

section Layer


theorem exists_layer_centralizer_of_isConj_c0 {y : CFSG.Blueprint.NativeSporadic.Co1}
    (hy : IsConj TabMThreeALeech.c0 y) :
    ∃ J : Subgroup GL24, CFSG.Open.IsQuasisimple ↥J ∧ Nat.card ↥(Subgroup.center ↥J) = 9 ∧
      Nonempty ((↥J ⧸ Subgroup.center ↥J) ≃* X₀) ∧
      Nonempty (PQuot 3 (GLAPLayer 3 (⊤ : Subgroup
        ↥(Subgroup.centralizer ({y} : Set CFSG.Blueprint.NativeSporadic.Co1)))) ≃* ↥J) := by
  haveI : Finite GL24 := inferInstance
  haveI : Finite CFSG.Blueprint.NativeSporadic.Co1 := CFSG.Sporadic.Co1.Module.finite_co1
  obtain ⟨g, hx, ⟨eW⟩⟩ := exists_centralizer_equiv hy
  obtain ⟨J, hJH, hJn, hq, hp3, hZ3, -, ⟨eJ⟩, hZ9⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.H1420.suzCo1_threeB_data hx
  set H : Subgroup GL24 := Subgroup.centralizer ({(g : GL24)} : Set GL24) ⊓ GA with hH
  have hJcard : Nat.card ↥J = 29393280 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥J),
      Nat.card_congr eJ.toEquiv, card_X₀, hZ9]
  have hHcard : Nat.card ↥H ≤ 58786560 := by
    rw [hH, ← card_centralizer_GA_eq_inf GA g]
    exact card_cent_threeB_le g hx
  have hc : ⁅H, H⁆ ≤ J := commutator_le_of_card_le_two_mul hJH (by rw [hJcard]; omega)
  have hSn : (J.subgroupOf H).Normal :=
    ⟨fun l hl c => (Subgroup.mem_subgroupOf).2 (hJn c c.2 l ((Subgroup.mem_subgroupOf).1 hl))⟩
  have hL : GLAPLayer 3 H = J :=
    CFSG.Sporadic.MI301.glaPLayer_eq_of_isQuasisimple_normal Nat.prime_three hJH hSn hq hp3 hZ3
      hc
  obtain ⟨e₁⟩ := CFSG.Sporadic.MI301.nonempty_pQuot_glaPLayer_top_of_surjective Nat.prime_three
    (eW : ↥(Subgroup.centralizer ({y} : Set CFSG.Blueprint.NativeSporadic.Co1)) →* ↥H)
    eW.surjective (by
      rw [(MonoidHom.ker_eq_bot_iff _).2 eW.injective, Subgroup.card_bot]
      norm_num)
  obtain ⟨e₂⟩ := CFSG.LocalAnalysis.GLTheoremA.H301.nonempty_pQuot_glaPLayer_subtype
    Nat.prime_three H
  have e₃ : Nonempty (PQuot 3 (GLAPLayer 3 H) ≃* ↥J) := by
    rw [hL]
    exact CFSG.Sporadic.MI301.nonempty_pQuot_equiv_self_of_isQuasisimple Nat.prime_three hq hp3
      hZ3
  obtain ⟨e₃⟩ := e₃
  exact ⟨J, hq, hZ9, ⟨eJ⟩, ⟨e₁.trans (e₂.symm.trans e₃)⟩⟩

end Layer

end CFSG.Sporadic.MI301Three
