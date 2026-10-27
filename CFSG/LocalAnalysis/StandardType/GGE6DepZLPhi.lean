module

public import CFSG.LocalAnalysis.StandardType.GGE6DepZLDefs
public import CFSG.LocalAnalysis.StandardType.GGE6DepZLFinite
public import CFSG.LocalAnalysis.StandardType.GGE6DepZLWeyl
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestDefs
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase

public section

namespace CFSG.StandardType

namespace E6Dep

namespace ZL

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G]

@[expose] noncomputable def phiB {L Bs : Subgroup G}
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (Φ : ↥(ggGamma L hBsN).range →* Multiplicative (Fin 6 → ZMod 3)) : Additive ↥Bs →+ Vec6 where
  toFun v := Multiplicative.toAdd (Φ ((ggGamma L hBsN).rangeRestrict (Additive.toMul v)))
  map_zero' := by simp
  map_add' u v := by simp

private theorem zlp_range_iff {L Bs : Subgroup G}
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    {Φ : ↥(ggGamma L hBsN).range →* Multiplicative (Fin 6 → ZMod 3)}
    (hcard : Nat.card (ggGamma L hBsN).range = 3 ^ 5)
    (hΦrange : Φ.range = ⊤ ∨ ∀ y, Multiplicative.ofAdd y ∈ Φ.range ↔ y ∈ NoOffRest.hypE6)
    (hΦinj : Function.Injective Φ) :
    ∀ y, Multiplicative.ofAdd y ∈ Φ.range ↔ y ∈ NoOffRest.hypE6 := by
  have hΦne : Φ.range ≠ ⊤ := by
    intro htop
    let A : Subgroup (MulAut ↥L) := (ggGamma L hBsN).range
    have hcardA : Nat.card A = 3 ^ 5 := hcard
    have h1 : Nat.card A = Nat.card Φ.range :=
      Nat.card_congr (MonoidHom.ofInjective hΦinj).toEquiv
    have h2 : Nat.card Φ.range = Nat.card (Multiplicative (Fin 6 → ZMod 3)) := by
      rw [htop, Subgroup.card_top]
    have h3 : Nat.card (Multiplicative (Fin 6 → ZMod 3)) = 3 ^ 6 := by
      rw [Nat.card_congr (Multiplicative.toAdd (α := Fin 6 → ZMod 3)), Nat.card_fun,
        Nat.card_zmod, Nat.card_fin]
    have : (3 : ℕ) ^ 5 = 3 ^ 6 := by rw [← hcardA, h1, h2, h3]
    norm_num at this
  exact hΦrange.resolve_left hΦne

private lemma zlp_rangeRestrict_eq_one {L Bs : Subgroup G}
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (b : ↥Bs) :
    (ggGamma L hBsN).rangeRestrict b = 1 ↔ ggGamma L hBsN b = 1 := by
  constructor
  · intro h
    have h1 := congrArg (fun w : ↥(ggGamma L hBsN).range => (w : MulAut ↥L)) h
    simpa using h1
  · intro h
    apply Subtype.ext
    rw [MonoidHom.coe_rangeRestrict]
    simpa using h

private lemma zlp_mem_zmultiples_iff {Bs : Subgroup G} {x : G} (hxBs : x ∈ Bs) (c : ↥Bs) :
    Additive.ofMul c ∈ AddSubgroup.zmultiples (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs)) ↔
      (c : G) ∈ Subgroup.zpowers x := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp h
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have h1 : (⟨x, hxBs⟩ : ↥Bs) ^ k = c := by
      apply Additive.ofMul.injective
      rw [ofMul_zpow]
      exact hk
    rw [← h1]
    rfl
  · intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    refine AddSubgroup.mem_zmultiples_iff.mpr ⟨k, ?_⟩
    have h1 : (⟨x, hxBs⟩ : ↥Bs) ^ k = c := Subtype.ext (by simpa using hk)
    rw [← h1]
    exact (ofMul_zpow k (⟨x, hxBs⟩ : ↥Bs)).symm

theorem phiB_kappa {L Bs : Subgroup G} (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    {Φ : ↥(ggGamma L hBsN).range →* Multiplicative (Fin 6 → ZMod 3)}
    (hcard : Nat.card (ggGamma L hBsN).range = 3 ^ 5)
    (hΦrange : Φ.range = ⊤ ∨ ∀ y, Multiplicative.ofAdd y ∈ Φ.range ↔ y ∈ NoOffRest.hypE6)
    (hΦinj : Function.Injective Φ) (v : Additive ↥Bs) : kappa ⬝ᵥ phiB hBsN Φ v = 0 := by
  have hrange := zlp_range_iff hBsN hcard hΦrange hΦinj
  have hmem : phiB hBsN Φ v ∈ NoOffRest.hypE6 :=
    (hrange (phiB hBsN Φ v)).mp (by
      change Multiplicative.ofAdd (Multiplicative.toAdd
        (Φ ((ggGamma L hBsN).rangeRestrict (Additive.toMul v)))) ∈ Φ.range
      rw [ofAdd_toAdd]
      exact MonoidHom.mem_range.mpr
        ⟨(ggGamma L hBsN).rangeRestrict (Additive.toMul v), rfl⟩)
  have hk := NoOffRest.mem_hypE6.mp hmem
  rwa [kDotP_eq_kappa_dotProduct] at hk

theorem phiB_surj {L Bs : Subgroup G} (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    {Φ : ↥(ggGamma L hBsN).range →* Multiplicative (Fin 6 → ZMod 3)}
    (hcard : Nat.card (ggGamma L hBsN).range = 3 ^ 5)
    (hΦrange : Φ.range = ⊤ ∨ ∀ y, Multiplicative.ofAdd y ∈ Φ.range ↔ y ∈ NoOffRest.hypE6)
    (hΦinj : Function.Injective Φ) (u : Vec6) (hu : kappa ⬝ᵥ u = 0) : ∃ v, phiB hBsN Φ v = u := by
  have hrange := zlp_range_iff hBsN hcard hΦrange hΦinj
  have hmem : u ∈ NoOffRest.hypE6 := by
    show NoOffRest.kDotP 3 u = 0
    rw [kDotP_eq_kappa_dotProduct]
    exact hu
  obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp ((hrange u).mpr hmem)
  obtain ⟨b, hb⟩ := MonoidHom.rangeRestrict_surjective (ggGamma L hBsN) a
  refine ⟨Additive.ofMul b, ?_⟩
  change Multiplicative.toAdd (Φ ((ggGamma L hBsN).rangeRestrict
    (Additive.toMul (Additive.ofMul b)))) = u
  rw [toMul_ofMul, hb, ha, toAdd_ofAdd]

theorem phiB_ker {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} [Finite G]
    (hcfg : GGConfig 3 B Bs x L D J) (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    {Φ : ↥(ggGamma L hBsN).range →* Multiplicative (Fin 6 → ZMod 3)}
    (hΦinj : Function.Injective Φ) (hxBs : x ∈ Bs) (v : Additive ↥Bs) :
    phiB hBsN Φ v = 0 ↔ v ∈ AddSubgroup.zmultiples (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs)) := by
  set b : ↥Bs := Additive.toMul v with hb
  have hv : v = Additive.ofMul b := by
    rw [hb]
    rfl
  rw [hv]
  change Multiplicative.toAdd (Φ ((ggGamma L hBsN).rangeRestrict b)) = 0 ↔
    Additive.ofMul b ∈ AddSubgroup.zmultiples (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs))
  calc
    Multiplicative.toAdd (Φ ((ggGamma L hBsN).rangeRestrict b)) = 0 ↔
        Φ ((ggGamma L hBsN).rangeRestrict b) = 1 := toAdd_eq_zero
    _ ↔ (ggGamma L hBsN).rangeRestrict b = 1 := by
          constructor
          · intro h
            exact hΦinj (h.trans (map_one Φ).symm)
          · intro h
            rw [h, map_one Φ]
    _ ↔ ggGamma L hBsN b = 1 := zlp_rangeRestrict_eq_one hBsN b
    _ ↔ (b : G) ∈ Subgroup.centralizer (L : Set G) := ggGamma_eq_one_iff L hBsN b
    _ ↔ (b : G) ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := by
          rw [Subgroup.mem_inf]
          exact ⟨fun h => ⟨b.2, h⟩, fun h => h.2⟩
    _ ↔ (b : G) ∈ Subgroup.zpowers x := by rw [hcfg.bstar_inf_centralizer_L]
    _ ↔ Additive.ofMul b ∈ AddSubgroup.zmultiples (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs)) :=
          (zlp_mem_zmultiples_iff hxBs b).symm

end ZL

end E6Dep

end CFSG.StandardType

end
