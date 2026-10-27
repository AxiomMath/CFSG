module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowDefs
public import CFSG.Open.LocalVocabulary

import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LieType.Chevalley.GraphFixedParameterFields
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCTGraphTwisted
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotOrth
import CFSG.LocalAnalysis.StandardType.ExcPay.CoverTwE6
import CFSG.LocalAnalysis.StandardType.GGTBE6IndTwistAlign
import CFSG.LocalAnalysis.StandardType.GGTBE6IndTwistTorus
import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Delta
import CFSG.LocalAnalysis.StandardType.Marking
import CFSG.LocalAnalysis.StandardType.MarkingDict
import CFSG.RankThree.CentralCover.SteinbergBNLinearTorus

public section

namespace CFSG.StandardType.ExcPay

open CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.StandardType CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg.TwistedE6

private theorem excPayK6_eq_one_of_mem_subgroupOf {G : Type} [Group G] [Finite G]
    {p f : ℕ} {K : Type} [Field K] [Finite K] {Bs X : Subgroup G}
    (hBs : IsElemAbelian p Bs)
    (hZ : Nat.Coprime (Nat.card ↥(Subgroup.center ↥X)) p)
    (θ : ↥X ⧸ Subgroup.center ↥X ≃* TwE6Delta.RecipeR K f)
    {z : ↥X} (hz : z ∈ (X ⊓ Bs).subgroupOf X)
    (hz1 : (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥X))) z = 1) :
    z = 1 := by
  let A0 : Subgroup ↥X := (X ⊓ Bs).subgroupOf X
  have hA0el : IsElemAbelian p A0 := (hBs.mono inf_le_right).comap X.subtype_injective
  have hψz : z ∈ Subgroup.center ↥X := by
    have hmk : (QuotientGroup.mk' (Subgroup.center ↥X)) z = 1 := by
      apply θ.injective
      simpa using hz1
    exact (QuotientGroup.eq_one_iff z).1 hmk
  have hzp : z ^ p = 1 := hA0el.2 z hz
  have hord : orderOf z ∣ Nat.gcd p (Nat.card ↥(Subgroup.center ↥X)) :=
    Nat.dvd_gcd (orderOf_dvd_iff_pow_eq_one.2 hzp)
      (Subgroup.orderOf_dvd_natCard (Subgroup.center ↥X) hψz)
  have hgcd : Nat.gcd p (Nat.card ↥(Subgroup.center ↥X)) = 1 := by
    rw [Nat.gcd_comm]
    exact hZ.gcd_eq_one
  rw [hgcd, Nat.dvd_one] at hord
  exact orderOf_eq_one_iff.1 hord

private theorem excPayK6_card_image {G : Type} [Group G] [Finite G] {p f : ℕ}
    {K : Type} [Field K] [Finite K] {Bs X : Subgroup G}
    (hBs : IsElemAbelian p Bs)
    (hZ : Nat.Coprime (Nat.card ↥(Subgroup.center ↥X)) p)
    (θ : ↥X ⧸ Subgroup.center ↥X ≃* TwE6Delta.RecipeR K f) :
    Nat.card (((X ⊓ Bs).subgroupOf X).map
        (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥X)))) =
      Nat.card ↥(X ⊓ Bs : Subgroup G) := by
  let ψ := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥X))
  let A0 : Subgroup ↥X := (X ⊓ Bs).subgroupOf X
  have hψ0inj : Function.Injective (ψ.comp A0.subtype) := by
    intro a b hab
    have hmem : (a : ↥X) * (b : ↥X)⁻¹ ∈ A0 :=
      A0.mul_mem a.2 (A0.inv_mem b.2)
    have hz1 : (a : ↥X) * (b : ↥X)⁻¹ = 1 := by
      apply excPayK6_eq_one_of_mem_subgroupOf hBs hZ θ hmem
      rw [map_mul, map_inv]
      change ψ (a : ↥X) * (ψ (b : ↥X))⁻¹ = 1
      change ψ (a : ↥X) = ψ (b : ↥X) at hab
      rw [hab, mul_inv_cancel]
    exact Subtype.ext (mul_inv_eq_one.mp hz1)
  have hrange : (ψ.comp A0.subtype).range = A0.map ψ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hcard : Nat.card (A0.map ψ) = Nat.card A0 := by
    rw [← hrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hψ0inj).toEquiv).symm
  have hA0card : Nat.card A0 = Nat.card ↥(X ⊓ Bs : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : (X ⊓ Bs : Subgroup G) ≤ X)).toEquiv
  change Nat.card (A0.map ψ) = Nat.card ↥(X ⊓ Bs : Subgroup G)
  rw [hcard, hA0card]

private theorem excPayK6_ker_comp {G : Type} [Group G] {f : ℕ} {K : Type} [Field K]
    {X : Subgroup G} (θ : ↥X ⧸ Subgroup.center ↥X ≃* TwE6Delta.RecipeR K f) :
    ∀ z : ↥X,
      (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥X))) z = 1 ↔
        z ∈ Subgroup.center ↥X := by
  intro z
  have hψ : (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥X))) z =
      θ ((QuotientGroup.mk' (Subgroup.center ↥X)) z) := rfl
  rw [hψ]
  constructor
  · intro hz
    have hmk : (QuotientGroup.mk' (Subgroup.center ↥X)) z = 1 :=
      θ.injective (by rw [hz, map_one])
    exact (QuotientGroup.eq_one_iff z).1 (by
      simpa [QuotientGroup.mk'_apply] using hmk)
  · intro hz
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff z).2 hz, map_one]

private theorem excPayK6_surjective_comp {G : Type} [Group G] {f : ℕ} {K : Type} [Field K]
    {X : Subgroup G} (θ : ↥X ⧸ Subgroup.center ↥X ≃* TwE6Delta.RecipeR K f) :
    Function.Surjective (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥X))) := by
  intro y
  obtain ⟨q, hq⟩ := θ.surjective y
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (N := Subgroup.center ↥X) q
  refine ⟨x, ?_⟩
  show θ ((QuotientGroup.mk' (Subgroup.center ↥X)) x) = y
  rw [hx, hq]

private theorem excPayK6_exists_mul_modEq_one {n p : ℕ} (h : Nat.Coprime n p) :
    ∃ k : ℕ, n * k ≡ 1 [MOD p] := by
  refine ⟨((n : ZMod p)⁻¹).val, ?_⟩
  refine (ZMod.natCast_eq_natCast_iff (n * ((n : ZMod p)⁻¹).val) 1 p).1 ?_
  simpa only [Nat.cast_mul, Nat.cast_one] using
    ZMod.mul_val_inv (m := n) (n := p) h

private theorem excPayK6_modEq_one_mod {n k p : ℕ} (hp : p.Prime)
    (h : n * k ≡ 1 [MOD p]) : (n * k) % p = 1 := by
  simpa [Nat.ModEq, Nat.mod_eq_of_lt hp.one_lt] using h

private theorem excPayK6_pow_mod {R : Type} [Group R] {g : R} {p m : ℕ}
    (hgp : g ^ p = 1) (hm1 : m % p = 1) : g ^ m = g := by
  have h1 : m = p * (m / p) + 1 := by
    conv_lhs => rw [← Nat.div_add_mod m p, hm1]
  rw [h1, pow_add, pow_mul, hgp, one_pow, one_mul, pow_one]

private theorem excPayK6_lift_pow {G : Type} [Group G] {f p : ℕ} {K : Type} [Field K]
    {X : Subgroup G} (ψ : ↥X →* TwE6Delta.RecipeR K f)
    (hker : ∀ z : ↥X, ψ z = 1 ↔ z ∈ Subgroup.center ↥X)
    (hp : p.Prime) {g : TwE6Delta.RecipeR K f} (hgp : g ^ p = 1)
    {y₀ : ↥X} (hy₀ : ψ y₀ = g) {n k : ℕ}
    (hdvd : Nat.card ↥(Subgroup.center ↥X) ∣ n) (hk : n * k ≡ 1 [MOD p]) :
    ∃ y : ↥X, ψ y = g ∧ y ^ p = 1 := by
  have hzn : (y₀ ^ p) ^ n = 1 := by
    have hzp : y₀ ^ p ∈ Subgroup.center ↥X :=
      (hker _).1 (by simpa [map_pow, hy₀, hgp])
    exact orderOf_dvd_iff_pow_eq_one.mp
      ((Subgroup.orderOf_dvd_natCard (Subgroup.center ↥X) hzp).trans hdvd)
  have hm1 : (n * k) % p = 1 := excPayK6_modEq_one_mod hp hk
  let y : ↥X := y₀ ^ (n * k)
  refine ⟨y, ?_, ?_⟩
  · dsimp only [y]
    rw [map_pow, hy₀]
    exact excPayK6_pow_mod hgp hm1
  · dsimp only [y]
    calc (y₀ ^ (n * k)) ^ p = y₀ ^ ((n * k) * p) := (pow_mul y₀ (n * k) p).symm
      _ = y₀ ^ (p * (n * k)) := by rw [Nat.mul_comm]
      _ = (y₀ ^ p) ^ (n * k) := pow_mul y₀ p (n * k)
      _ = ((y₀ ^ p) ^ n) ^ k := by rw [pow_mul]
      _ = 1 := by rw [hzn, one_pow]

private theorem excPayK6_commutator_eq_one {G : Type} [Group G] {f p : ℕ}
    {K : Type} [Field K] {X : Subgroup G} (ψ : ↥X →* TwE6Delta.RecipeR K f)
    (hker : ∀ z : ↥X, ψ z = 1 ↔ z ∈ Subgroup.center ↥X)
    (A0 : Subgroup ↥X) (hA0el : IsElemAbelian p A0)
    (hZ : Nat.Coprime (Nat.card ↥(Subgroup.center ↥X)) p)
    {y : ↥X} (hyp : y ^ p = 1)
    (hg : ∀ x ∈ A0.map ψ, ψ y * x = x * ψ y) :
    ∀ x' ∈ A0, y * x' * y⁻¹ * x'⁻¹ = 1 := by
  intro x' hx'
  have hxE : ψ x' ∈ A0.map ψ := Subgroup.mem_map_of_mem ψ hx'
  have hx'p : x' ^ p = 1 := hA0el.2 x' hx'
  let f : ↥X := y * x' * y⁻¹ * x'⁻¹
  have hmem : f ∈ Subgroup.center ↥X := by
    apply (hker _).1
    dsimp only [f]
    simp only [map_mul, map_inv]
    rw [hg (ψ x') hxE]
    group
  have hconj : (y * x' * y⁻¹) ^ p = 1 := by
    rw [conj_pow, hx'p]
    group
  have hcomm : Commute f x' := (Subgroup.mem_center_iff.1 hmem x').symm
  have hfa : y * x' * y⁻¹ = f * x' := by dsimp only [f]; group
  have h2 : (f * x') ^ p = f ^ p * x' ^ p := hcomm.mul_pow p
  rw [← hfa, hconj, hx'p, mul_one] at h2
  have hfp : f ^ p = 1 := h2.symm
  have hordp : orderOf f ∣ p := orderOf_dvd_iff_pow_eq_one.2 hfp
  have hordn : orderOf f ∣ Nat.card ↥(Subgroup.center ↥X) :=
    Subgroup.orderOf_dvd_natCard (Subgroup.center ↥X) hmem
  have hgcd : Nat.gcd p (Nat.card ↥(Subgroup.center ↥X)) = 1 := by
    rw [Nat.gcd_comm]
    exact hZ.gcd_eq_one
  have hord : orderOf f ∣ Nat.gcd p (Nat.card ↥(Subgroup.center ↥X)) :=
    Nat.dvd_gcd hordp hordn
  rw [hgcd, Nat.dvd_one] at hord
  exact orderOf_eq_one_iff.1 hord

private theorem excPayK6_mem_image_of_commutes {G : Type} [Group G] {p f : ℕ}
    {K : Type} [Field K] {Bs X : Subgroup G}
    (hsplit2 : ∀ y ∈ X, (∀ x ∈ X ⊓ Bs, y * x = x * y) → y ^ p = 1 → y ∈ Bs)
    (ψ : ↥X →* TwE6Delta.RecipeR K f) {g : TwE6Delta.RecipeR K f}
    {y : ↥X} (hy : ψ y = g) (hyp : y ^ p = 1)
    (hcommA0 : ∀ x' ∈ (X ⊓ Bs).subgroupOf X, y * x' * y⁻¹ * x'⁻¹ = 1) :
    g ∈ ((X ⊓ Bs).subgroupOf X).map ψ := by
  let A0 : Subgroup ↥X := (X ⊓ Bs).subgroupOf X
  have hcommG : ∀ x ∈ X ⊓ Bs, (y : G) * x = x * (y : G) := by
    intro x hx
    have hx' : (⟨x, hx.1⟩ : ↥X) ∈ A0 := Subgroup.mem_subgroupOf.mpr hx
    have h := hcommA0 ⟨x, hx.1⟩ hx'
    have h' : (y : G) * x * (y : G)⁻¹ = x := by
      have h2 := congrArg Subtype.val h
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] at h2
      exact mul_inv_eq_one.mp h2
    calc (y : G) * x = ((y : G) * x * (y : G)⁻¹) * (y : G) := by group
      _ = x * (y : G) := by rw [h']
  have hyX : (y : G) ∈ X := y.2
  have hypG : (y : G) ^ p = 1 := by simpa using congrArg Subtype.val hyp
  have hyBs : (y : G) ∈ Bs := hsplit2 (y : G) hyX hcommG hypG
  rw [← hy]
  exact ⟨y, Subgroup.mem_subgroupOf.mpr ⟨hyX, hyBs⟩, rfl⟩

private theorem excPayK6_sc_image {G : Type} [Group G] [Finite G] {p f : ℕ}
    {K : Type} [Field K] [Finite K] {Bs X : Subgroup G}
    (hp : p.Prime) (hBs : IsElemAbelian p Bs)
    (hZ : Nat.Coprime (Nat.card ↥(Subgroup.center ↥X)) p)
    (hsplit2 : ∀ y ∈ X, (∀ x ∈ X ⊓ Bs, y * x = x * y) → y ^ p = 1 → y ∈ Bs)
    (θ : ↥X ⧸ Subgroup.center ↥X ≃* TwE6Delta.RecipeR K f) :
    ∀ g : TwE6Delta.RecipeR K f,
      (∀ x ∈ ((X ⊓ Bs).subgroupOf X).map
        (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥X))), g * x = x * g) →
      g ^ p = 1 →
      g ∈ ((X ⊓ Bs).subgroupOf X).map
        (θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥X))) := by
  let ψ := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥X))
  let A0 : Subgroup ↥X := (X ⊓ Bs).subgroupOf X
  have hA0el : IsElemAbelian p A0 := (hBs.mono inf_le_right).comap X.subtype_injective
  have hker : ∀ z : ↥X, ψ z = 1 ↔ z ∈ Subgroup.center ↥X := excPayK6_ker_comp θ
  intro g hg hgp
  obtain ⟨y₀, hy₀⟩ := excPayK6_surjective_comp θ g
  obtain ⟨k, hk⟩ := excPayK6_exists_mul_modEq_one hZ
  obtain ⟨y, hy, hyp⟩ :=
    excPayK6_lift_pow ψ hker hp hgp hy₀ (dvd_rfl) hk
  have hcommA0 : ∀ x' ∈ A0, y * x' * y⁻¹ * x'⁻¹ = 1 := by
    apply excPayK6_commutator_eq_one ψ hker A0 hA0el hZ hyp
    intro x hx
    rw [hy]
    exact hg x hx
  exact excPayK6_mem_image_of_commutes hsplit2 ψ hy hyp hcommA0


private theorem excPayK6_graph_card {K : Type} [Field K] [Finite K] [CharP K 2]
    {f p : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (θ : K ≃+* K) (hθ : ∀ c, θ.toRingHom (θ.toRingHom c) = c)
    (l : K) (hl : θ.toRingHom l = l + 1)
    (hθq : ∀ c, θ.toRingHom c = c ^ (2 ^ f)) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ 2 ^ f + 1) [NeZero p]
    (ζ : CFSG.LieType.Steinberg.normOne θ) (hζ : ζ ^ p = 1)
    (hζo : orderOf (ζ : Kˣ) = p)
    (E : Subgroup (graphFixedRootGroup TwistTag.E6 K θ.toRingHom))
    (hE : IsElemAbelian p E)
    (hSC : ∀ g, (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E) :
    Nat.card E = p ^ 6 := by
  have hp3 : p ≠ 3 := by omega
  have hζo' : orderOf ζ = p := by
    rw [← Subgroup.orderOf_coe ζ]
    exact hζo
  let q := CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK θ.toRingHom hθq
  have hqc : q.ker ≤ Subgroup.center (fixedGroup K θ.toRingHom) :=
    (CFSG.SeitzReduction.F4Pilot.ker_twistedIsogenyC hf hK θ.toRingHom hθq).le
  let ι := q.comp (TBE6IndTwist.langPFrame K θ hθ l hl ζ hζ)
  have hι : Function.Injective ι :=
    TBE6IndTwist.cover_langPFrame_injective K θ hθ l hl hK hθq hp hp3 q hqc ζ hζ hζo'
  have hframe : Nat.card ι.range = p ^ 6 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hι).toEquiv,
      CFSG.RankThree.CentralCover.card_multiplicative_fin_zmod]
    rfl
  obtain ⟨c, hc⟩ :=
    TBE6IndTwist.exists_graph_frame_conj_of_selfCent K θ hθ l hl hf hK hθq hp hp5 hpq
      ζ hζ hζo E hE hSC
  have hconj : Nat.card (E.map (MulAut.conj c).toMonoidHom) = Nat.card E :=
    Subgroup.card_map_of_injective (K := E) (f := (MulAut.conj c).toMonoidHom)
      (MulAut.conj c).injective
  rw [← hconj, hc]
  exact hframe


private theorem excPayK6_card_of_recipe {K : Type} [Field K] [Finite K] [CharP K 2]
    {f p : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (θ : K ≃+* K) (hθ : ∀ c, θ.toRingHom (θ.toRingHom c) = c)
    (l : K) (hl : θ.toRingHom l = l + 1) (hθq : ∀ c, θ.toRingHom c = c ^ (2 ^ f))
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ f + 1) [NeZero p]
    (ζ : CFSG.LieType.Steinberg.normOne θ) (hζ : ζ ^ p = 1)
    (hζo : orderOf (ζ : Kˣ) = p)
    (E : Subgroup (TwE6Delta.RecipeR K f)) (hE : IsElemAbelian p E)
    (hSC : ∀ g, (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E) :
    Nat.card E = p ^ 6 := by
  obtain ⟨ε⟩ := TwE6Rank.exists_mulEquiv_graphFixedRootGroup hf hK θ.toRingHom hθq
  let E' : Subgroup (graphFixedRootGroup TwistTag.E6 K θ.toRingHom) :=
    E.map ε.toMonoidHom
  have hE' : IsElemAbelian p E' := hE.map ε.toMonoidHom
  have hSC' : ∀ g : graphFixedRootGroup TwistTag.E6 K θ.toRingHom,
      (∀ x ∈ E', g * x = x * g) → g ^ p = 1 → g ∈ E' := by
    intro g hg hgp
    have hg' : ε.symm g ∈ E := by
      apply hSC (ε.symm g)
      · intro e he
        apply ε.injective
        rw [map_mul, map_mul, ε.apply_symm_apply]
        exact hg (ε e) (Subgroup.mem_map_of_mem ε.toMonoidHom he)
      · rw [← map_pow, hgp, map_one]
    exact ⟨ε.symm g, hg', ε.apply_symm_apply g⟩
  have hcard' : Nat.card E' = p ^ 6 :=
    excPayK6_graph_card hf hK θ hθ l hl hθq hp hp5 hpq ζ hζ hζo E' hE' hSC'
  have hcard : Nat.card E = Nat.card E' :=
    (Subgroup.card_map_of_injective (K := E) (f := ε.toMonoidHom) ε.injective).symm
  rw [hcard]
  exact hcard'

theorem card_eq_pow_six_of_sc_twE6 {K : Type} [Field K] [Finite K] {f p : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ 2 ^ f + 1)
    (E : Subgroup (TwE6Delta.RecipeR K f)) (hE : IsElemAbelian p E)
    (hSC : ∀ g, (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E) :
    Nat.card E = p ^ 6 := by
  classical
  haveI : CharP K 2 := charP_two_of_card (m := f * 2) (by rw [hK, ← pow_mul])
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨θ, hθq, hθo, -⟩ :=
    finite_graph_field_parameter_fields TwistTag.E6 Nat.prime_two hf K hK
  have hθ : ∀ c, θ.toRingHom (θ.toRingHom c) = c :=
    CFSG.SeitzReduction.F4Pilot.involutive_of_natCard_eq hK (fun c => hθq c)
  have hθ1 : θ ≠ 1 := by
    change orderOf θ = 2 at hθo
    intro h
    rw [h, orderOf_one] at hθo
    omega
  have hθ2 : θ * θ = 1 := by
    change orderOf θ = 2 at hθo
    simpa only [hθo, pow_two] using pow_orderOf_eq_one θ
  obtain ⟨l, hl⟩ :=
    CFSG.SeitzReduction.LinearPilot.exists_trace_one_of_involution hθ1 hθ2
  obtain ⟨ζ, hζo⟩ :=
    TBE6IndTwist.exists_normOne_prime K θ hf hK (fun c => hθq c) hp hpq
  have hζ : ζ ^ p = 1 := by
    apply Subtype.ext
    change (ζ : Kˣ) ^ p = 1
    rw [← hζo, pow_orderOf_eq_one]
  exact excPayK6_card_of_recipe hf hK θ hθ l hl hθq hp hp5 hpq ζ hζ hζo
    E hE hSC

theorem card_inf_eq_pow_six_of_marking_twE6 {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs X : Subgroup G} (hp : p.Prime) (hp5 : 5 ≤ p) (hBs : IsElemAbelian p Bs)
    (hmark : GGInnerDiagOnLabel (fun p lab => ggRowP_ETwE6 p lab ∧ 2 ≤ lab.n) p Bs X)
    (hZ : Nat.Coprime (Nat.card ↥(Subgroup.center ↥X)) p)
    (hsplit2 : ∀ y ∈ X, (∀ x ∈ X ⊓ Bs, y * x = x * y) → y ^ p = 1 → y ∈ Bs) :
    Nat.card ↥(X ⊓ Bs : Subgroup G) = p ^ 6 := by
  classical
  obtain ⟨f, K, hfld, hfin, θ, hf2, hpq, hK, -, -, -⟩ :=
    exists_recipe_of_marking_twE6 hmark
  letI : Field K := hfld
  letI : Finite K := hfin
  let ψ := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥X))
  let A0 : Subgroup ↥X := (X ⊓ Bs).subgroupOf X
  let E : Subgroup (TwE6Delta.RecipeR K f) := A0.map ψ
  have hEel : IsElemAbelian p E :=
    ((hBs.mono inf_le_right).comap X.subtype_injective).map ψ
  have hSCE : ∀ g : TwE6Delta.RecipeR K f,
      (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E :=
    excPayK6_sc_image hp hBs hZ hsplit2 θ
  have hEcard : Nat.card E = p ^ 6 :=
    card_eq_pow_six_of_sc_twE6 (K := K) (f := f) (p := p) (by omega) hK hp hp5 hpq
      E hEel hSCE
  have hcard : Nat.card E = Nat.card ↥(X ⊓ Bs : Subgroup G) :=
    excPayK6_card_image hBs hZ θ
  rw [← hcard]
  exact hEcard

end CFSG.StandardType.ExcPay
