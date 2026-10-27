module

public import CFSG.LocalAnalysis.StandardType.GGRCLinRefl
public import CFSG.LocalAnalysis.StandardType.GGWitSlpm
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.LocalAnalysis.StandardType.GGKGReflection
public import CFSG.RankThree.CentralCover.ReflectionRadical
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.GroupTheory.ElementaryAbelianTransport

public noncomputable section

namespace CFSG.StandardType

open CFSG CFSG.Open CFSG.Assembly CFSG.RankThree.Classical2 CFSG.RankThree.CentralCover
open scoped IsMulCommutative

section Negative

attribute [local instance] CFSG.RankThree.GroupTheory.kernelOmega_isElementaryAbelian

theorem GGIsReflection.commute_lifts_of_equivariant_negative
    {Y H A : Type} [Group Y] [Group H] [Group A] (π : Y →* H) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center Y) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {E : Subgroup A} [Finite E] (hE : IsElemAbelian p E)
    (ι : E →* H) (φ : MulAut E) (hr : GGIsReflection p φ)
    (g : H) (hactφ : ∀ w, g * ι w * g⁻¹ = ι (φ w))
    {x : E} (hx : φ x = x⁻¹)
    {u v : Y} (hu : π u = ι x) (hv : ∃ y : E, π v = ι y) : u * v = v * u := by
  classical
  let := hE.isElementaryAbelian
  let V := Additive E
  let r : V ≃ₗ[ZMod p] V := ggLin (p := p) (AddEquiv.refl V) φ
  have hr' : ZS.IsRefl p r := (ggRC_isReflection_iff_linRefl (AddEquiv.refl V) _).mp hr
  obtain ⟨a, α, hα, hform⟩ := ZS.slpm_refl_form hp2 hr'
  let e : Multiplicative V →* H :=
    ι.comp
      { toFun := fun v => Additive.toMul (Multiplicative.toAdd v)
        map_one' := rfl
        map_mul' _ _ := rfl }
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : Nat.Prime p) Nat.prime_two).mp hd)
  have hact : ∀ w : V, g * e (.ofAdd w) * g⁻¹ = e (.ofAdd (w - α w • a)) := by
    intro w
    calc g * e (.ofAdd w) * g⁻¹ = e (.ofAdd (r w)) := hactφ _
      _ = e (.ofAdd (w - α w • a)) := by rw [hform]; rfl
  let xv : V := Additive.ofMul x
  have hneg : r xv = -xv := congrArg Additive.ofMul hx
  have hscalar : (2 : ZMod p) • xv = α xv • a := by
    have hformx : r xv = xv - α xv • a := by rw [hform]; rfl
    have hh : xv - α xv • a = -xv := hformx.symm.trans hneg
    rw [sub_eq_iff_eq_add] at hh
    calc (2 : ZMod p) • xv = xv + xv := two_smul (ZMod p) xv
      _ = α xv • a := by
        have hh' := congrArg (fun w : V => xv + w) hh
        simpa only [add_assoc, add_neg_cancel_left] using hh'
  obtain ⟨y, hy⟩ := hv
  have ha := liftComm_eq_one_of_preReflection hπ hker e h2 a α hα g hact
    (Additive.ofMul y)
  let B := liftCommBilinear (p := p) hπ hker e
  have haB : B a (Additive.ofMul y) = 0 := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact ha
  have hzero : B xv (Additive.ofMul y) = 0 := by
    have hh := congrArg (fun w : V => B w (Additive.ofMul y)) hscalar
    simp only [map_smul, LinearMap.smul_apply, haB, smul_zero] at hh
    exact (smul_eq_zero.mp hh).resolve_left h2
  have hcomm : liftComm π hπ (ι x) (ι y) = 1 :=
    congrArg (fun b : Additive (CFSG.RankThree.GroupTheory.kernelOmega hker p) =>
      ((Additive.toMul b : CFSG.RankThree.GroupTheory.kernelOmega hker p) : Y)) hzero
  rw [liftComm_eq hπ hker hu hy] at hcomm
  exact commutatorElement_eq_one_iff_mul_comm.mp hcomm

end Negative

theorem ggIsReflection_comap_commute_of_central_fixed
    {Y H : Type} [Group Y] [Group H] (π : Y →* H) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center Y) (hY : Group.IsPerfect Y)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {E : Subgroup H} [Finite E]
    (hE : IsElemAbelian p E) (hcard : Nat.card E ≤ p ^ 3)
    {g : H} (hg : g ∈ Subgroup.normalizer (E : Set H))
    (hr : GGIsReflection p (ggConjAut E hg))
    {x : H} (hxE : x ∈ E) (hx : x ≠ 1) (hxc : x ∈ Subgroup.center H) :
    ∀ u ∈ E.comap π, ∀ v ∈ E.comap π, u * v = v * u := by
  classical
  have hp : p.Prime := Fact.out
  let := hE.isElementaryAbelian
  let V := Additive E
  let r : V ≃ₗ[ZMod p] V := ggLin (p := p) (AddEquiv.refl V) (ggConjAut E hg)
  have hr' : ZS.IsRefl p r := (ggRC_isReflection_iff_linRefl (AddEquiv.refl V) _).mp hr
  obtain ⟨a, α, hα, hform⟩ := ZS.slpm_refl_form hp2 hr'
  let e : Multiplicative V →* H :=
    { toFun := fun v => (Additive.toMul (Multiplicative.toAdd v) : E)
      map_one' := rfl
      map_mul' _ _ := rfl }
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd)
  have hdim : Module.finrank (ZMod p) V ≤ 3 := by
    have hpow : p ^ Module.finrank (ZMod p) V ≤ p ^ 3 := by
      rw [FiniteField.pow_finrank_eq_natCard p V]
      exact hcard
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hpow
  let xv : V := Additive.ofMul (⟨x, hxE⟩ : E)
  have hxv : xv ≠ 0 := by
    intro hz
    exact hx (congrArg (fun v : V => ((Additive.toMul v : E) : H)) hz)
  have hact : ∀ v : V, g * e (.ofAdd v) * g⁻¹ = e (.ofAdd (v - α v • a)) := by
    intro v
    calc g * e (.ofAdd v) * g⁻¹ = e (.ofAdd (r v)) := rfl
      _ = e (.ofAdd (v - α v • a)) := by rw [hform]; rfl
  have hxfix : r xv = xv := by
    apply Additive.toMul.injective
    apply Subtype.ext
    change g * x * g⁻¹ = x
    rw [(Subgroup.mem_center_iff.mp hxc g), mul_inv_cancel_right]
  have hfix : α xv = 0 := by
    have ha : a ≠ 0 := by
      intro hz
      rw [hz, map_zero] at hα
      exact h2 hα.symm
    have hsmul : α xv • a = 0 := by
      have h := hxfix
      rw [hform] at h
      change xv - α xv • a = xv at h
      exact sub_eq_self.mp h
    exact (smul_eq_zero.mp hsmul).resolve_right ha
  obtain ⟨z, hz⟩ := hπ x
  have hzc : z ∈ Subgroup.center Y := by
    rw [← CFSG.LocalCores.comap_center_eq_of_perfect hY π hπ hker]
    change π z ∈ Subgroup.center H
    rwa [hz]
  have hpair := liftComm_eq_one_of_preReflection_of_central_lift
    hπ hker e h2 hdim a α hα g hact xv hxv hfix z hzc hz
  intro u hu v hv
  refine mul_comm_of_liftComm_eq_one hπ hker (U := E) ?_ hu hv
  intro s hs t ht
  exact hpair (Additive.ofMul (⟨s, hs⟩ : E)) (Additive.ofMul (⟨t, ht⟩ : E))

theorem ggKGIsReflAt_comap_commute_of_central_fixed
    {Y H : Type} [Group Y] [Group H] (π : Y →* H)
    (hker : π.ker ≤ Subgroup.center Y) (hY : Group.IsPerfect Y)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {E : Subgroup H} [Finite E]
    (hE : IsElemAbelian p E) (hcard : Nat.card E ≤ p ^ 3) (hEπ : E ≤ π.range)
    {g : H} (hgπ : g ∈ π.range) (hr : GGKGIsReflAt p E g)
    {x : H} (hxE : x ∈ E) (hx : x ≠ 1) (hxc : x ∈ Subgroup.centralizer (π.range : Set H)) :
    ∀ u ∈ E.comap π, ∀ v ∈ E.comap π, u * v = v * u := by
  let E' : Subgroup π.range := E.subgroupOf π.range
  let : Finite E' := Finite.of_equiv E (Subgroup.subgroupOfEquivOfLe hEπ).symm.toEquiv
  let g' : π.range := ⟨g, hgπ⟩
  let x' : π.range := ⟨x, hEπ hxE⟩
  have hmap : E'.map π.range.subtype = E := Subgroup.map_subgroupOf_eq_of_le hEπ
  have hr' : GGKGIsReflAt p E' g' := GGKGIsReflAt.of_map π.range.subtype
    Subtype.val_injective (by simpa only [hmap, g', Subgroup.subtype_apply] using hr)
  have hcard' : Nat.card E' ≤ p ^ 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEπ).toEquiv]
    exact hcard
  have hxc' : x' ∈ Subgroup.center π.range := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxc y y.2)
  have hcomm := ggIsReflection_comap_commute_of_central_fixed π.rangeRestrict
    π.rangeRestrict_surjective (by simpa only [MonoidHom.ker_rangeRestrict] using hker)
    hY hp2 (hE.subgroupOf π.range) hcard' hr'.1 hr'.isReflection
    (show x' ∈ E' from hxE) (fun h => hx (congrArg Subtype.val h)) hxc'
  exact hcomm

end CFSG.StandardType

end
