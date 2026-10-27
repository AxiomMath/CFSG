module

public import CFSG.LocalAnalysis.StandardType.GGE6DepKDefs

public section

namespace CFSG.StandardType

namespace E6Dep

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

private theorem phi_range_iff {Bs X : Subgroup G} (hBsN : Bs ≤ Subgroup.normalizer (X : Set G))
    {Z : Subgroup ↥X} {Φ : ↥(ggGamma X hBsN).range →* Multiplicative (Fin 6 → ZMod 3)}
    {T : Subgroup ↥X} {w : Fin 6 → ↥X}
    (hmodel : GGE6ThreeWeylModelWith Z (ggGamma X hBsN).range Φ T w)
    (hcard : Nat.card (ggGamma X hBsN).range = 3 ^ 5) :
    ∀ y : Vec6, Multiplicative.ofAdd y ∈ Φ.range ↔ y ∈ NoOffRest.hypE6 := by
  have hΦinj : Function.Injective Φ := hmodel.1
  have hcardVec : Nat.card Vec6 = 3 ^ 6 := by
    rw [Vec6, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  have hΦrange_ne_top : Φ.range ≠ ⊤ := by
    intro htop
    have hsurj : Function.Surjective Φ := fun y => by
      have hy : y ∈ Φ.range := by rw [htop]; trivial
      exact hy
    have hle1 : Nat.card (ggGamma X hBsN).range ≤ Nat.card (Multiplicative Vec6) :=
      Nat.card_le_card_of_injective Φ hΦinj
    have hle2 : Nat.card (Multiplicative Vec6) ≤ Nat.card (ggGamma X hBsN).range :=
      Nat.card_le_card_of_surjective Φ hsurj
    have hcardVecM : Nat.card (Multiplicative Vec6) = 3 ^ 6 := by
      rw [Nat.card_congr Multiplicative.toAdd, hcardVec]
    have hle2' : 3 ^ 6 ≤ Nat.card (ggGamma X hBsN).range := hcardVecM ▸ hle2
    rw [hcard] at hle2'
    norm_num at hle2'
  exact hmodel.2.1.resolve_left hΦrange_ne_top

private theorem kdot_of_phi {Bs X : Subgroup G} (hBsN : Bs ≤ Subgroup.normalizer (X : Set G))
    {Z : Subgroup ↥X} {Φ : ↥(ggGamma X hBsN).range →* Multiplicative (Fin 6 → ZMod 3)}
    {T : Subgroup ↥X} {w : Fin 6 → ↥X}
    (hmodel : GGE6ThreeWeylModelWith Z (ggGamma X hBsN).range Φ T w)
    (hcard : Nat.card (ggGamma X hBsN).range = 3 ^ 5)
    (a : ↥(ggGamma X hBsN).range) :
    NoOffRest.kDotP 3 (Multiplicative.toAdd (Φ a)) = 0 := by
  have hmem : Multiplicative.toAdd (Φ a) ∈ NoOffRest.hypE6 :=
    (phi_range_iff hBsN hmodel hcard (Multiplicative.toAdd (Φ a))).mp ⟨a, rfl⟩
  exact NoOffRest.mem_hypE6.mp hmem

theorem kappaOf_coordE {Bs X : Subgroup G} (hBsN : Bs ≤ Subgroup.normalizer (X : Set G))
    {Z : Subgroup ↥X} {Φ : ↥(ggGamma X hBsN).range →* Multiplicative (Fin 6 → ZMod 3)}
    {T : Subgroup ↥X} {w : Fin 6 → ↥X}
    (hmodel : GGE6ThreeWeylModelWith Z (ggGamma X hBsN).range Φ T w)
    (hcard : Nat.card (ggGamma X hBsN).range = 3 ^ 5) (b : ↥Bs) :
    coordE.mulVec (kappaOf hBsN Φ (Additive.ofMul b)) =
      Multiplicative.toAdd (Φ ((ggGamma X hBsN).rangeRestrict b)) := by
  have hk := kdot_of_phi hBsN hmodel hcard ((ggGamma X hBsN).rangeRestrict b)
  change coordE.mulVec (coordF.mulVec
    (Multiplicative.toAdd (Φ ((ggGamma X hBsN).rangeRestrict b)))) =
    Multiplicative.toAdd (Φ ((ggGamma X hBsN).rangeRestrict b))
  exact coordE_coordF _ hk

theorem kappaOf_five {Bs X : Subgroup G} (hBsN : Bs ≤ Subgroup.normalizer (X : Set G))
    {Z : Subgroup ↥X} {Φ : ↥(ggGamma X hBsN).range →* Multiplicative (Fin 6 → ZMod 3)}
    {T : Subgroup ↥X} {w : Fin 6 → ↥X}
    (hmodel : GGE6ThreeWeylModelWith Z (ggGamma X hBsN).range Φ T w)
    (hcard : Nat.card (ggGamma X hBsN).range = 3 ^ 5) (b : ↥Bs) :
    kappaOf hBsN Φ (Additive.ofMul b) 5 = 0 := by
  have hk := kdot_of_phi hBsN hmodel hcard ((ggGamma X hBsN).rangeRestrict b)
  change (coordF.mulVec
    (Multiplicative.toAdd (Φ ((ggGamma X hBsN).rangeRestrict b)))) 5 = 0
  exact coordF_five _ hk

theorem kappaOf_frame_base {Bs X : Subgroup G} {y : G}
    (hBsN : Bs ≤ Subgroup.normalizer (X : Set G)) {Z : Subgroup ↥X}
    {Φ : ↥(ggGamma X hBsN).range →* Multiplicative (Fin 6 → ZMod 3)} {T : Subgroup ↥X}
    {w : Fin 6 → ↥X} (hmodel : GGE6ThreeWeylModelWith Z (ggGamma X hBsN).range Φ T w)
    (hcard : Nat.card (ggGamma X hBsN).range = 3 ^ 5)
    (hker : Bs ⊓ Subgroup.centralizer (X : Set G) = Subgroup.zpowers y) :
    (∀ b : ↥Bs, kappaOf hBsN Φ (Additive.ofMul b) = 0 ↔ (b : G) ∈ Subgroup.zpowers y) ∧
      (∀ b : ↥Bs, kappaOf hBsN Φ (Additive.ofMul b) 5 = 0) ∧
      (∀ v : Vec6, v 5 = 0 → ∃ b : ↥Bs, kappaOf hBsN Φ (Additive.ofMul b) = v) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro b
    constructor
    · intro h
      have hcoord := kappaOf_coordE hBsN hmodel hcard b
      have h3 : Multiplicative.toAdd (Φ ((ggGamma X hBsN).rangeRestrict b)) = 0 := by
        rw [← hcoord, h]
        exact Matrix.mulVec_zero _
      have hPhi : Φ ((ggGamma X hBsN).rangeRestrict b) = 1 := by
        have hh := congrArg Multiplicative.ofAdd h3
        simpa using hh
      have hres : (ggGamma X hBsN).rangeRestrict b = 1 :=
        hmodel.1 (hPhi.trans (map_one Φ).symm)
      have hgamma : ggGamma X hBsN b = 1 := by
        have h1 := congrArg Subtype.val hres
        simpa using h1
      have hcent : (b : G) ∈ Subgroup.centralizer (X : Set G) :=
        (ggGamma_eq_one_iff X hBsN b).mp hgamma
      rw [← hker]
      exact Subgroup.mem_inf.mpr ⟨b.2, hcent⟩
    · intro hb
      have hcent : (b : G) ∈ Subgroup.centralizer (X : Set G) := by
        have hb' : (b : G) ∈ Bs ⊓ Subgroup.centralizer (X : Set G) := by
          rw [hker]; exact hb
        exact (Subgroup.mem_inf.mp hb').2
      have hgamma : ggGamma X hBsN b = 1 := (ggGamma_eq_one_iff X hBsN b).mpr hcent
      have hres : (ggGamma X hBsN).rangeRestrict b = 1 :=
        Subtype.ext (by simpa using hgamma)
      change coordF.mulVec
        (Multiplicative.toAdd (Φ ((ggGamma X hBsN).rangeRestrict b))) = 0
      rw [hres, map_one]
      exact Matrix.mulVec_zero _
  · intro b
    exact kappaOf_five hBsN hmodel hcard b
  · intro v hv
    have hmem : coordE.mulVec v ∈ NoOffRest.hypE6 := coordE_mem v hv
    have hof : Multiplicative.ofAdd (coordE.mulVec v) ∈ Φ.range :=
      (phi_range_iff hBsN hmodel hcard (coordE.mulVec v)).mpr hmem
    obtain ⟨a, ha⟩ := hof
    obtain ⟨b, hb⟩ := MonoidHom.rangeRestrict_surjective (ggGamma X hBsN) a
    refine ⟨b, ?_⟩
    change coordF.mulVec
      (Multiplicative.toAdd (Φ ((ggGamma X hBsN).rangeRestrict b))) = v
    rw [hb, ha]
    simpa using coordF_coordE v hv

end E6Dep

end CFSG.StandardType

end
