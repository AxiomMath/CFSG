module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Extraspecial
public import Mathlib.GroupTheory.Frattini
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core
import CFSG.LinearAlgebra.OddSolvableUnitary.CommutatorForm
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public noncomputable section

open Subgroup
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec11.SimsR1.Blackburn

private theorem exists_ofMul_of {D : Type*} [Group D] (v : Additive (Abelianization D)) :
    ∃ q : D, Additive.ofMul (Abelianization.of q) = v := by
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
  exact ⟨x, congrArg Additive.ofMul hx⟩

section Extraspecial

variable {p : ℕ} {P : Type} [Group P] [Finite P]
  (E : Subgroup P) [E.Normal] [hE : IsExtraspecial p E]

include hE

private theorem commutator_le_center_of_isExtraspecial :
    _root_.commutator ↥E ≤ center ↥E := by
  haveI : IsElementaryAbelian p (↥E ⧸ center ↥E) :=
    IsExtraspecial.quotient_elementary_abelian p ↥E
  exact Subgroup.Normal.quotient_commutative_iff_commutator_le.1 inferInstance

private theorem center_eq_commutator_of_isExtraspecial (hp : p.Prime) :
    center ↥E = _root_.commutator ↥E := by
  have hle := commutator_le_center_of_isExtraspecial (p := p) E
  have hcZ : Nat.card (center ↥E) = p := IsExtraspecial.center_order_p p ↥E
  have hne : _root_.commutator ↥E ≠ ⊥ := by
    intro h
    rw [commutator_eq_bot_iff_center_eq_top] at h
    haveI := IsExtraspecial.quotient_nontrivial p ↥E
    rw [h] at this
    exact (not_nontrivial_iff_subsingleton.2 QuotientGroup.subsingleton_quotient_top) this
  have hdvd : Nat.card (_root_.commutator ↥E) ∣ p := hcZ ▸ card_dvd_of_le hle
  have hcard : Nat.card (_root_.commutator ↥E) = p := by
    rcases (Nat.dvd_prime hp).1 hdvd with h | h
    · exact absurd (Subgroup.card_eq_one.1 h) hne
    · exact h
  exact (eq_of_le_of_card_ge hle (by rw [hcZ, hcard])).symm

private theorem exists_inner_of_triv_quotient (hp : p.Prime) (hexp : ∀ x : ↥E, x ^ p = 1) {g : P}
    (hg : ∀ x : ↥E, x⁻¹ * MulAut.conjNormal g x ∈ center ↥E) :
    ∃ u : ↥E, (u : P)⁻¹ * g ∈ centralizer (E : Set P) := by
  have hZ := center_eq_commutator_of_isExtraspecial (p := p) E hp
  have hcZ : Nat.card (center ↥E) = p := IsExtraspecial.center_order_p p ↥E
  obtain ⟨ε⟩ : Nonempty (center ↥E ≃* Multiplicative (ZMod p)) := by
    haveI : Fact p.Prime := ⟨hp⟩
    exact CFSG.OddSolvableUnitary.nonempty_center_mulEquiv hcZ
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI _hmod : Module (ZMod p) (Additive (Abelianization ↥E)) :=
    AddCommGroup.zmodModule (CFSG.OddSolvableUnitary.nsmul_abelianization_eq_zero hexp)
  obtain ⟨B, -, hBn, hB⟩ := CFSG.OddSolvableUnitary.exists_commForm hZ ε
  let α : MulAut ↥E := MulAut.conjNormal g
  let f : ↥E →* center ↥E :=
    { toFun := fun x => ⟨x⁻¹ * α x, hg x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        show (x * y)⁻¹ * α (x * y) = x⁻¹ * α x * (y⁻¹ * α y)
        rw [map_mul, mul_inv_rev]
        have hc := mem_center_iff.1 (hg x) y⁻¹
        calc y⁻¹ * x⁻¹ * (α x * α y) = y⁻¹ * (x⁻¹ * α x) * α y := by group
          _ = (x⁻¹ * α x) * y⁻¹ * α y := by rw [hc]
          _ = x⁻¹ * α x * (y⁻¹ * α y) := by group) }
  let ℓ : Additive (Abelianization ↥E) →ₗ[ZMod p] ZMod p :=
    (MonoidHom.toAdditiveLeft (ε.toMonoidHom.comp (Abelianization.lift f))).toZModLinearMap p
  have hℓ : ∀ x : ↥E, ℓ (Additive.ofMul (Abelianization.of x)) =
      Multiplicative.toAdd (ε (f x)) := fun x => rfl
  have hex : ∃ w : Additive (Abelianization ↥E), ∀ v, B w v = ℓ v := by
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : Finite (Additive (Abelianization ↥E)) :=
      Finite.of_surjective (fun x : ↥E => Additive.ofMul (Abelianization.of x))
        fun v => QuotientGroup.mk_surjective (Additive.toMul v)
    haveI : FiniteDimensional (ZMod p) (Additive (Abelianization ↥E)) := Module.Finite.of_finite
    exact ⟨(B.toDual hBn).symm ℓ, fun v => by
      rw [← LinearMap.BilinForm.toDual_def hBn, LinearEquiv.apply_symm_apply]⟩
  obtain ⟨w, hw⟩ := hex
  obtain ⟨u, hu⟩ := exists_ofMul_of w
  have hcomm : ∀ x : ↥E, ⁅u, x⁆ = x⁻¹ * α x := by
    intro x
    have h1 := hw (Additive.ofMul (Abelianization.of x))
    rw [← hu, hB u x, hℓ] at h1
    have h3 := ε.injective (Multiplicative.toAdd.injective h1)
    exact congrArg (fun t : center ↥E => (t : ↥E)) h3
  have hconj : ∀ x : ↥E, α x = u * x * u⁻¹ := by
    intro x
    have hc : ⁅u, x⁆ ∈ center ↥E := by
      rw [hZ]
      exact commutator_mem_commutator (mem_top u) (mem_top x)
    have hxc := mem_center_iff.1 hc x
    calc α x = x * (x⁻¹ * α x) := by group
      _ = x * ⁅u, x⁆ := by rw [hcomm]
      _ = ⁅u, x⁆ * x := hxc
      _ = u * x * u⁻¹ := by rw [commutatorElement_def]; group
  refine ⟨u, mem_centralizer_iff.2 fun h hh => ?_⟩
  have hx := congrArg (fun t : ↥E => (t : P)) (hconj ⟨h, hh⟩)
  simp only [α, MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_inv] at hx
  calc h * ((u : P)⁻¹ * g) = (u : P)⁻¹ * ((u : P) * h * (u : P)⁻¹) * g := by group
    _ = (u : P)⁻¹ * (g * h * g⁻¹) * g := by rw [hx]
    _ = ((u : P)⁻¹ * g) * h := by group

end Extraspecial

section Action

variable {p : ℕ}

private def autEnd {D : Type*} [Group D] [Module (ZMod p) (Additive (Abelianization D))] :
    MulAut D →* Module.End (ZMod p) (Additive (Abelianization D)) where
  toFun ψ := (MonoidHom.toAdditive (Abelianization.map (ψ : D →* D))).toZModLinearMap p
  map_one' := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨q, rfl⟩ := exists_ofMul_of v
    rfl
  map_mul' ψ ψ' := by
    refine LinearMap.ext fun v => ?_
    obtain ⟨q, rfl⟩ := exists_ofMul_of v
    rfl

variable {P : Type} [Group P]

private def actGL (E : Subgroup P) [E.Normal] [Module (ZMod p) (Additive (Abelianization ↥E))] :
    P →* LinearMap.GeneralLinearGroup (ZMod p) (Additive (Abelianization ↥E)) :=
  ((autEnd (p := p)).comp (MulAut.conjNormal : P →* MulAut ↥E)).toHomUnits

private theorem mem_commutator_of_mem_ker_actGL (E : Subgroup P) [E.Normal]
    [Module (ZMod p) (Additive (Abelianization ↥E))] {g : P} (hg : g ∈ (actGL (p := p) E).ker)
    (x : ↥E) : x⁻¹ * MulAut.conjNormal g x ∈ _root_.commutator ↥E := by
  have h1 : actGL (p := p) E g = 1 := hg
  have h2 := congrArg (fun T : LinearMap.GeneralLinearGroup (ZMod p)
    (Additive (Abelianization ↥E)) => (T : Additive (Abelianization ↥E) →ₗ[ZMod p]
      Additive (Abelianization ↥E)) (Additive.ofMul (Abelianization.of x))) h1
  exact QuotientGroup.eq.1 (Additive.ofMul.injective h2).symm

end Action

section GLTwo

variable {p : ℕ}

private theorem card_gl_two (hp : p.Prime) {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    [Finite V] (hV : Module.finrank (ZMod p) V = 2) :
    Nat.card (LinearMap.GeneralLinearGroup (ZMod p) V) = (p ^ 2 - 1) * (p ^ 2 - p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : FiniteDimensional (ZMod p) V := Module.Finite.of_finite
  rw [← Nat.card_congr (Matrix.GeneralLinearGroup.toLin'
    (Module.finBasisOfFinrankEq (ZMod p) V hV)).toEquiv, Matrix.card_GL_field,
    Fin.prod_univ_two, ZMod.card]
  simp

private theorem coprime_gl_two (hp : p.Prime) : Nat.Coprime p ((p ^ 2 - 1) * (p - 1)) := by
  have hp2 := hp.two_le
  refine Nat.Coprime.mul_right ?_ ?_
  · rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro h
    have h3 : p ∣ p ^ 2 := dvd_pow_self p (by norm_num)
    have h4 : p ∣ p ^ 2 - (p ^ 2 - 1) := Nat.dvd_sub h3 h
    have h5 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.pos
    have h6 : p ^ 2 - (p ^ 2 - 1) = 1 := by omega
    rw [h6] at h4
    exact hp.one_lt.ne' (Nat.dvd_one.1 h4)
  · rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro h
    have := Nat.le_of_dvd (by omega) h
    omega

private theorem card_le_of_isPGroup_gl_two (hp : p.Prime) {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] [Finite V] (hV : Module.finrank (ZMod p) V = 2)
    (T : Subgroup (LinearMap.GeneralLinearGroup (ZMod p) V)) (hT : IsPGroup p T) :
    Nat.card T ≤ p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 := hp.two_le
  have hGL := card_gl_two hp hV
  haveI : Finite (LinearMap.GeneralLinearGroup (ZMod p) V) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [hGL]
    have h1 : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
    have h2 : p < p ^ 2 := by nlinarith
    exact Nat.mul_ne_zero (by omega) (by omega)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hT
  have hdvd : p ^ k ∣ p * ((p ^ 2 - 1) * (p - 1)) := by
    rw [← hk]
    have h1 : p ^ 2 - p = p * (p - 1) := by rw [Nat.mul_sub_one, sq]
    have : (p ^ 2 - 1) * (p ^ 2 - p) = p * ((p ^ 2 - 1) * (p - 1)) := by
      rw [h1, mul_left_comm]
    exact this ▸ hGL ▸ Subgroup.card_subgroup_dvd_card T
  have hp' : p ^ k ∣ p := (Nat.Coprime.pow_left k (coprime_gl_two hp)).dvd_of_dvd_mul_right hdvd
  rw [hk]
  exact Nat.le_of_dvd hp.pos hp'

end GLTwo

section Index

variable {p : ℕ} {P : Type} [Group P] [Finite P]

private theorem exists_subgroup_index_le (hp : p.Prime) (hP : IsPGroup p P) (E : Subgroup P)
    [E.Normal] [IsExtraspecial p E] (hEcard : Nat.card ↥E = p ^ 3)
    (hexp : ∀ x : ↥E, x ^ p = 1) :
    ∃ K : Subgroup P, K.index ≤ p ∧
      ∀ g ∈ K, ∀ x : ↥E, x⁻¹ * MulAut.conjNormal g x ∈ center ↥E := by
  have hZ := center_eq_commutator_of_isExtraspecial (p := p) E hp
  have hcZ : Nat.card (center ↥E) = p := IsExtraspecial.center_order_p p ↥E
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI _hmod : Module (ZMod p) (Additive (Abelianization ↥E)) :=
    AddCommGroup.zmodModule (CFSG.OddSolvableUnitary.nsmul_abelianization_eq_zero hexp)
  haveI hfin : Finite (Additive (Abelianization ↥E)) :=
    Finite.of_surjective (fun x : ↥E => Additive.ofMul (Abelianization.of x))
      fun v => QuotientGroup.mk_surjective (Additive.toMul v)
  have hV : Module.finrank (ZMod p) (Additive (Abelianization ↥E)) = 2 := by
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : FiniteDimensional (ZMod p) (Additive (Abelianization ↥E)) := Module.Finite.of_finite
    have h1 : Nat.card (Abelianization ↥E) * p = p ^ 3 :=
      (CFSG.OddSolvableUnitary.card_eq_card_abelianization_mul hZ hcZ).symm.trans hEcard
    have h2 : Nat.card (Abelianization ↥E) = p ^ 2 :=
      Nat.eq_of_mul_eq_mul_right hp.pos (by rw [h1]; ring)
    have h3 := Module.natCard_eq_pow_finrank (K := ZMod p)
      (V := Additive (Abelianization ↥E))
    rw [Nat.card_zmod, Nat.card_congr (Additive.toMul : Additive (Abelianization ↥E) ≃ _), h2]
      at h3
    exact (Nat.pow_right_injective hp.two_le h3).symm
  refine ⟨(actGL (p := p) E).ker, ?_, fun g hg x => by
    rw [hZ]; exact mem_commutator_of_mem_ker_actGL E hg x⟩
  rw [Subgroup.index_ker]
  exact card_le_of_isPGroup_gl_two hp hV _
    (hP.of_surjective (actGL (p := p) E).rangeRestrict (MonoidHom.rangeRestrict_surjective _))

end Index

section Order

private theorem card_zpowers_sup_center {p : ℕ} (hp : p.Prime) {D : Type*} [Group D] [Finite D]
    (hexp : ∀ x : D, x ^ p = 1) (hcZ : Nat.card (center D) = p) {w : D} (hw : w ∉ center D) :
    Nat.card ↥(zpowers w ⊔ center D) = p ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hw1 : w ≠ 1 := fun h => hw (h ▸ one_mem _)
  have hord : orderOf w = p := orderOf_eq_prime (hexp w) hw1
  have hzp : Nat.card (zpowers w) = p := by rw [Nat.card_zpowers, hord]
  have hrel : (center D).relIndex (zpowers w) = p := by
    have hdvd : (center D).relIndex (zpowers w) ∣ p := by
      rw [← hzp]
      exact Subgroup.index_dvd_card _
    rcases (Nat.dvd_prime hp).1 hdvd with h | h
    · exact absurd ((Subgroup.relIndex_eq_one.1 h) (mem_zpowers w)) hw
    · exact h
  have h2 : (center D).relIndex (zpowers w ⊔ center D) = p := by
    rw [Subgroup.relIndex_sup_right, hrel]
  have h3 : ((center D).subgroupOf (zpowers w ⊔ center D)).index *
      Nat.card ((center D).subgroupOf (zpowers w ⊔ center D)) =
        Nat.card ↥(zpowers w ⊔ center D) := Subgroup.index_mul_card _
  have h4 : Nat.card ((center D).subgroupOf (zpowers w ⊔ center D)) = Nat.card (center D) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [← h3, h4, hcZ]
  change (center D).relIndex (zpowers w ⊔ center D) * p = p ^ 2
  rw [h2]
  ring

end Order

section Main

theorem index_sup_centralizer_le_of_extraspecial {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {P : Type} [Group P] [Finite P] (hP : IsPGroup p P) (E : Subgroup P) [E.Normal]
    [IsExtraspecial p E] (hEcard : Nat.card E = p ^ 3) (hEexp : Monoid.exponent E = p) :
    (E ⊔ Subgroup.centralizer (E : Set P)).index ≤ p := by
  have hpp : p.Prime := Fact.out
  have hexp : ∀ x : ↥E, x ^ p = 1 := fun x => by
    rw [← hEexp]
    exact Monoid.pow_exponent_eq_one x
  obtain ⟨K, hKidx, hK⟩ := exists_subgroup_index_le hpp hP E hEcard hexp
  have hKle : K ≤ E ⊔ Subgroup.centralizer (E : Set P) := by
    intro g hg
    obtain ⟨u, hu⟩ := exists_inner_of_triv_quotient E hpp hexp (hK g hg)
    have hg' : g = (u : P) * ((u : P)⁻¹ * g) := by group
    rw [hg']
    exact mul_mem_sup u.2 hu
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    (Subgroup.index_dvd_of_le hKle)).trans hKidx

theorem exists_le_frattini_of_not_mem_sup_centralizer {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {P : Type} [Group P] [Finite P] (hP : IsPGroup p P) (E : Subgroup P) [E.Normal]
    [IsExtraspecial p E] (hEcard : Nat.card E = p ^ 3) (hEexp : Monoid.exponent E = p)
    {x : P} (hx : x ∉ E ⊔ Subgroup.centralizer (E : Set P)) :
    ∃ A₁ : Subgroup P, A₁ ≤ E ∧ Nat.card A₁ = p ^ 2 ∧ A₁ ≤ frattini P := by
  have hpp : p.Prime := Fact.out
  have hexp : ∀ y : ↥E, y ^ p = 1 := fun y => by
    rw [← hEexp]
    exact Monoid.pow_exponent_eq_one y
  have hZ := center_eq_commutator_of_isExtraspecial (p := p) E hpp
  have hcZ : Nat.card (center ↥E) = p := IsExtraspecial.center_order_p p ↥E
  obtain ⟨e, he⟩ : ∃ e : ↥E, e⁻¹ * MulAut.conjNormal x e ∉ center ↥E := by
    by_contra hcon
    push Not at hcon
    obtain ⟨u, hu⟩ := exists_inner_of_triv_quotient E hpp hexp hcon
    apply hx
    have hx' : x = (u : P) * ((u : P)⁻¹ * x) := by group
    rw [hx']
    exact mul_mem_sup u.2 hu
  set w : ↥E := e⁻¹ * MulAut.conjNormal x e with hw
  refine ⟨(zpowers w ⊔ center ↥E).map E.subtype, map_subtype_le _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective E.subtype_injective]
    exact card_zpowers_sup_center hpp hexp hcZ he
  · haveI : Fact (IsPGroup p P) := ⟨hP⟩
    refine le_trans ?_ (CFSG.commutator_le_frattini_of_isPGroup (p := p) (R := P))
    rw [Subgroup.map_sup, MonoidHom.map_zpowers]
    refine sup_le ?_ ?_
    · rw [zpowers_le]
      have hwP : E.subtype w = ⁅(e : P)⁻¹, x⁆ := by
        simp only [hw, MonoidHom.coe_mk, Subgroup.coe_subtype, Subgroup.coe_mul,
          Subgroup.coe_inv, MulAut.conjNormal_apply, commutatorElement_def, inv_inv]
        group
      rw [hwP]
      exact commutator_mem_commutator (mem_top _) (mem_top _)
    · rw [hZ, _root_.commutator_def, Subgroup.map_commutator, _root_.commutator_def]
      exact commutator_mono le_top le_top

end Main

end CFSG.RankThree.PartTwo.Sec11.SimsR1.Blackburn
