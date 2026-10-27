module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelBasic
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Card
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module

public section

namespace CFSG.StandardType

open Module CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Linear

variable {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Finite V]

omit [Finite V] in
theorem card_ker_mul_eq_of_ne_zero {φ : Module.Dual (ZMod p) V} (hφ : φ ≠ 0) :
    Nat.card (LinearMap.ker φ) * p = Nat.card V := by
  have hsurj : Function.Surjective φ := by
    obtain ⟨v, hv⟩ : ∃ v, φ v ≠ 0 := by
      by_contra h
      push Not at h
      exact hφ (LinearMap.ext h)
    intro c
    refine ⟨(c * (φ v)⁻¹) • v, ?_⟩
    rw [map_smul, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hv, mul_one]
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker φ),
    Nat.card_congr (φ.quotKerEquivOfSurjective hsurj).toEquiv, Nat.card_zmod]

omit [Finite V] in
theorem card_fixed_eq_card_ker (T : V →ₗ[ZMod p] V) :
    Nat.card {v : V // T v = v} = Nat.card (LinearMap.ker (LinearMap.id - T)) :=
  Nat.card_congr (Equiv.subtypeEquivRight fun v => by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero, eq_comm])

theorem exists_eq_reflection_of_card (T : V →ₗ[ZMod p] V) (hT : ∀ v, T (T v) = v)
    (hcard : Nat.card {v : V // T v = v} * p = Nat.card V) :
    ∃ (x : V) (f : Module.Dual (ZMod p) V), f x = 2 ∧ ∀ v, T v = v - f v • x := by
  set π : V →ₗ[ZMod p] V := LinearMap.id - T with hπ
  have hπv : ∀ v, π v = v - T v := fun v => rfl
  have hV := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker π)
  rw [card_fixed_eq_card_ker] at hcard
  have hR : Nat.card (LinearMap.range π) = p := by
    rw [← Nat.card_congr (π.quotKerEquivRange).toEquiv]
    have hpos : 0 < Nat.card (LinearMap.ker π) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (by rw [← hV, ← hcard])
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hnt : Nontrivial (LinearMap.range π) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hR]; exact hp1)
  obtain ⟨r, hr⟩ := exists_ne (0 : LinearMap.range π)
  have hrank : Module.finrank (ZMod p) (LinearMap.range π) = 1 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := LinearMap.range π)
    rw [hR, Nat.card_zmod] at h
    exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le (by simpa using h.symm))
  have hmult : ∀ w ∈ LinearMap.range π, ∃ c : ZMod p, c • (r : V) = w := by
    intro w hw
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' r hr).mp hrank ⟨w, hw⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  have hr0 : (r : V) ≠ 0 := fun h => hr (Subtype.ext h)
  obtain ⟨φ, hφ⟩ := Projective.exists_dual_ne_zero (ZMod p) hr0
  have hTr : T r = -(r : V) := by
    obtain ⟨v, hv⟩ := r.2
    rw [← hv, hπv, map_sub, hT]
    abel
  refine ⟨r, (φ r)⁻¹ • φ.comp π, ?_, fun v => ?_⟩
  · simp only [LinearMap.smul_apply, LinearMap.comp_apply, hπv, hTr, sub_neg_eq_add, map_add,
      smul_eq_mul]
    field_simp
    ring
  · obtain ⟨c, hc⟩ := hmult (π v) (LinearMap.mem_range_self π v)
    have hf : ((φ r)⁻¹ • φ.comp π) v = c := by
      simp only [LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul, ← hc, map_smul]
      field_simp
    rw [hf, hc, hπv]
    abel

end Linear

theorem zmod_two_ne_zero {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff (ZMod p) p] at h'
  exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp h')

section Bridge

variable {p : ℕ} [Fact p.Prime] {E : Type*} [Group E] {V : Type*} [AddCommGroup V]
  [Module (ZMod p) V]

@[expose] noncomputable def ggLin (ι : Additive E ≃+ V) : MulAut E →* (V ≃ₗ[ZMod p] V) where
  toFun φ := LinearEquiv.ofBijective
      ((ι.symm.trans ((MulEquiv.toAdditive φ).trans ι)).toAddMonoidHom.toZModLinearMap p)
      (ι.symm.trans ((MulEquiv.toAdditive φ).trans ι)).bijective
  map_one' := by
    refine LinearEquiv.ext fun v => ?_
    simp [LinearEquiv.ofBijective_apply]
  map_mul' φ ψ := by
    refine LinearEquiv.ext fun v => ?_
    simp [LinearEquiv.ofBijective_apply]

theorem ggLin_apply (ι : Additive E ≃+ V) (φ : MulAut E) (v : V) :
    ggLin (p := p) ι φ v = ι (Additive.ofMul (φ (Additive.toMul (ι.symm v)))) := rfl

theorem ggLin_apply_ofMul (ι : Additive E ≃+ V) (φ : MulAut E) (b : E) :
    ggLin (p := p) ι φ (ι (Additive.ofMul b)) = ι (Additive.ofMul (φ b)) := by
  rw [ggLin_apply, AddEquiv.symm_apply_apply, toMul_ofMul]

theorem ggLin_injective (ι : Additive E ≃+ V) : Function.Injective (ggLin (p := p) ι) := by
  intro φ ψ h
  refine MulEquiv.ext fun b => ?_
  have hb := congrArg (fun T : V ≃ₗ[ZMod p] V => T (ι (Additive.ofMul b))) h
  simp only [ggLin_apply_ofMul] at hb
  exact Additive.ofMul.injective (ι.injective hb)

theorem ggLin_fix_iff (ι : Additive E ≃+ V) (φ : MulAut E) (b : E) :
    φ b = b ↔ ggLin (p := p) ι φ (ι (Additive.ofMul b)) = ι (Additive.ofMul b) := by
  rw [ggLin_apply_ofMul]
  exact ⟨fun h => by rw [h], fun h => Additive.ofMul.injective (ι.injective h)⟩

theorem ggLin_inv_iff (ι : Additive E ≃+ V) (φ : MulAut E) (b : E) :
    φ b = b⁻¹ ↔ ggLin (p := p) ι φ (ι (Additive.ofMul b)) = -ι (Additive.ofMul b) := by
  rw [ggLin_apply_ofMul, ← map_neg, ← ofMul_inv]
  exact ⟨fun h => by rw [h], fun h => Additive.ofMul.injective (ι.injective h)⟩

theorem card_fixed_ggLin (ι : Additive E ≃+ V) (φ : MulAut E) :
    Nat.card {b : E // φ b = b} = Nat.card {v : V // ggLin (p := p) ι φ v = v} := by
  refine Nat.card_congr (Equiv.subtypeEquiv (Additive.ofMul.trans ι.toEquiv) fun b => ?_)
  exact ggLin_fix_iff ι φ b

omit [Fact p.Prime] [Module (ZMod p) V] in
theorem card_eq_of_ggLin (ι : Additive E ≃+ V) : Nat.card E = Nat.card V :=
  Nat.card_congr (Additive.ofMul.trans ι.toEquiv)

theorem exists_ggLinData {G : Type} [Group G] {Bs : Subgroup G} (hBs : IsElemAbelian p Bs) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod p) V),
      Nonempty (Additive ↥Bs ≃+ V) := by
  let iA : AddCommGroup (Additive ↥Bs) :=
    { (inferInstance : AddGroup (Additive ↥Bs)) with
      add_comm := fun a b => by
        have h := hBs.1.is_comm.comm (Additive.toMul a) (Additive.toMul b)
        exact congrArg Additive.ofMul h }
  let iM : Module (ZMod p) (Additive ↥Bs) := AddCommGroup.zmodModule (n := p) fun a => by
    have h : (Additive.toMul a) ^ p = 1 := Subtype.ext (hBs.2 _ (Additive.toMul a).2)
    rw [← ofMul_toMul a, ← ofMul_pow, h, ofMul_one]
  exact ⟨Additive ↥Bs, iA, iM, ⟨AddEquiv.refl _⟩⟩

end Bridge

section MulEquivTransport

variable {p : ℕ} [Fact p.Prime] {E E' : Type} [Group E] [Group E']
  {V : Type} [AddCommGroup V] [Module (ZMod p) V]

theorem ggLin_mulEquiv_congr (e : E ≃* E') (ι : Additive E ≃+ V) (φ : MulAut E) :
    ggLin (p := p) ((MulEquiv.toAdditive e.symm).trans ι) (MulAut.congr e φ)
      = ggLin (p := p) ι φ := by
  refine LinearEquiv.ext fun v => ?_
  set x : E := Additive.toMul (ι.symm v) with hx
  have hv : v = ι (Additive.ofMul x) := by
    rw [hx, ofMul_toMul, AddEquiv.apply_symm_apply]
  let ι' : Additive E' ≃+ V := (MulEquiv.toAdditive e.symm).trans ι
  have hι' : ∀ y : E, ι' (Additive.ofMul (e y)) = ι (Additive.ofMul y) := by
    intro y
    rw [AddEquiv.trans_apply]
    simp [MulEquiv.toAdditive]
  have hsymm : ι'.symm v = Additive.ofMul (e x) := by
    apply ι'.injective
    rw [AddEquiv.apply_symm_apply, hι' x]
    exact hv
  have htoMul : Additive.toMul (ι'.symm v) = e x := by rw [hsymm, toMul_ofMul]
  rw [ggLin_apply, ggLin_apply]
  change ι' (Additive.ofMul ((MulAut.congr e) φ (Additive.toMul (ι'.symm v)))) =
    ι (Additive.ofMul (φ (Additive.toMul (ι.symm v))))
  rw [htoMul, ← hx]
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  exact hι' (φ x)

end MulEquivTransport

section ReflectionTransport

theorem ggIsReflection_iff_of_card {M M' : Type} [Group M] [Group M'] {p : ℕ}
    {Bs : Subgroup M} {Bs' : Subgroup M'} {φ : MulAut ↥Bs} {φ' : MulAut ↥Bs'}
    (hsq : φ' ^ 2 = 1 ↔ φ ^ 2 = 1) {c : ℕ} (hc : 0 < c)
    (hfix : Nat.card {b : ↥Bs' // φ' b = b} = Nat.card {b : ↥Bs // φ b = b} * c)
    (hcard : Nat.card ↥Bs' = Nat.card ↥Bs * c) :
    GGIsReflection p φ' ↔ GGIsReflection p φ := by
  unfold GGIsReflection
  rw [hsq, hfix, hcard]
  refine and_congr_right fun _ => ⟨fun h => Nat.eq_of_mul_eq_mul_right hc ?_, fun h => ?_⟩
  · rw [← h]
    ring
  · rw [← h]
    ring

namespace F4AutRefl

theorem ggIsReflection_congr_iff {M M' : Type} [Group M] [Group M'] {p : ℕ}
    {Bs : Subgroup M} {Bs' : Subgroup M'} (e : ↥Bs ≃* ↥Bs') (φ : MulAut ↥Bs) :
    GGIsReflection p (MulAut.congr e φ) ↔ GGIsReflection p φ := by
  refine ggIsReflection_iff_of_card ?_ one_pos ?_ ?_
  · rw [← map_pow, MulEquiv.map_eq_one_iff]
  · rw [mul_one]
    refine Nat.card_congr (Equiv.subtypeEquiv e.symm.toEquiv fun b => ?_)
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.toEquiv_eq_coe,
      MulEquiv.coe_toEquiv]
    constructor
    · intro h
      have h' := congrArg e.symm h
      rwa [MulEquiv.symm_apply_apply] at h'
    · intro h
      rw [h, MulEquiv.apply_symm_apply]
  · rw [mul_one]
    exact Nat.card_congr e.toEquiv.symm

end F4AutRefl

end ReflectionTransport

section Induced

variable {G : Type} [Group G]

theorem mul_mem_ggInduced {H Bs : Subgroup G} {φ ψ : MulAut ↥Bs} (hφ : φ ∈ ggInduced H Bs)
    (hψ : ψ ∈ ggInduced H Bs) : φ * ψ ∈ ggInduced H Bs := by
  obtain ⟨g, hgH, hgN, hg⟩ := hφ
  obtain ⟨h, hhH, hhN, hh⟩ := hψ
  refine ⟨g * h, H.mul_mem hgH hhH, Subgroup.mul_mem _ hgN hhN, fun b => ?_⟩
  rw [MulAut.mul_apply, hg, hh]
  group

theorem one_mem_ggInduced (H Bs : Subgroup G) : (1 : MulAut ↥Bs) ∈ ggInduced H Bs :=
  ⟨1, H.one_mem, Subgroup.one_mem _, fun b => by simp⟩

theorem pow_mem_ggInduced {H Bs : Subgroup G} {φ : MulAut ↥Bs} (hφ : φ ∈ ggInduced H Bs)
    (n : ℕ) : φ ^ n ∈ ggInduced H Bs := by
  induction n with
  | zero => exact one_mem_ggInduced H Bs
  | succ n ih => rw [pow_succ]; exact mul_mem_ggInduced ih hφ

end Induced

section GG

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
  {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

theorem ggIsReflection_iff (ι : Additive ↥Bs ≃+ V) (φ : MulAut ↥Bs) :
    GGIsReflection p φ ↔ (ggLin (p := p) ι φ) ^ 2 = 1 ∧
      Nat.card {v : V // ggLin (p := p) ι φ v = v} * p = Nat.card V := by
  have h1 : (ggLin (p := p) ι φ) ^ 2 = 1 ↔ φ ^ 2 = 1 := by
    rw [← map_pow, ← map_one (ggLin (p := p) ι), (ggLin_injective ι).eq_iff]
  rw [GGIsReflection, h1, card_fixed_ggLin (p := p) ι φ, card_eq_of_ggLin ι]

theorem exists_of_ggIsReflection [Finite V] (ι : Additive ↥Bs ≃+ V) {φ : MulAut ↥Bs}
    (h : GGIsReflection p φ) :
    ∃ (x : V) (f : Module.Dual (ZMod p) V), f x = 2 ∧ ∀ v, ggLin (p := p) ι φ v = v - f v • x := by
  rw [ggIsReflection_iff ι] at h
  refine exists_eq_reflection_of_card (ggLin (p := p) ι φ).toLinearMap (fun v => ?_) h.2
  have hv := congrArg (fun T : V ≃ₗ[ZMod p] V => T v) h.1
  simpa [pow_two] using hv

theorem ggIsTransvection_of_apply (ι : Additive ↥Bs ≃+ V) {φ : MulAut ↥Bs} {w : V}
    {f : Module.Dual (ZMod p) V} (hw : w ≠ 0) (hf : f ≠ 0) (hfw : f w = 0)
    (h : ∀ v, ggLin (p := p) ι φ v = v + f v • w) : GGIsTransvection p φ := by
  refine ⟨?_, fun b => ?_⟩
  · rw [card_fixed_ggLin (p := p) ι φ, card_eq_of_ggLin ι, ← card_ker_mul_eq_of_ne_zero hf]
    congr 1
    refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
    rw [h, add_eq_left, LinearMap.mem_ker, smul_eq_zero, or_iff_left hw]
  · rw [ggLin_fix_iff (p := p) ι]
    have hc : ι (Additive.ofMul (b⁻¹ * φ b)) = f (ι (Additive.ofMul b)) • w := by
      rw [ofMul_mul, map_add, ofMul_inv, map_neg, ← ggLin_apply_ofMul (p := p) ι φ b, h]
      abel
    rw [hc, h, map_smul, hfw, smul_eq_mul, mul_zero, zero_smul, add_zero]

theorem ne_zero_of_apply_eq_two (hp2 : p ≠ 2) {x : V} {f : Module.Dual (ZMod p) V}
    (hfx : f x = 2) : x ≠ 0 ∧ f ≠ 0 := by
  have h2 := zmod_two_ne_zero hp2
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h, map_zero] at hfx
    exact h2 hfx.symm
  · rw [h, LinearMap.zero_apply] at hfx
    exact h2 hfx.symm

theorem ggLin_eq_reflection (ι : Additive ↥Bs ≃+ V) {φ : MulAut ↥Bs} {x : V}
    {f : Module.Dual (ZMod p) V} (hfx : f x = 2) (h : ∀ v, ggLin (p := p) ι φ v = v - f v • x) :
    ggLin (p := p) ι φ = reflection hfx :=
  LinearEquiv.ext fun v => by rw [h, reflection_apply]

theorem ggIsReflection_of_eq_reflection (hp2 : p ≠ 2) (ι : Additive ↥Bs ≃+ V) {φ : MulAut ↥Bs}
    {x : V} {f : Module.Dual (ZMod p) V} (hfx : f x = 2)
    (h : ggLin (p := p) ι φ = reflection hfx) : GGIsReflection p φ := by
  obtain ⟨hx0, hf0⟩ := ne_zero_of_apply_eq_two hp2 hfx
  rw [ggIsReflection_iff ι, h]
  refine ⟨LinearEquiv.ext fun v => ?_, ?_⟩
  · rw [pow_two, LinearEquiv.mul_apply, involutive_reflection hfx v]
    rfl
  · rw [← card_ker_mul_eq_of_ne_zero hf0]
    congr 1
    refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
    rw [reflection_apply, sub_eq_self, smul_eq_zero, or_iff_left hx0, LinearMap.mem_ker]

theorem ggCross_eq_zero_of_noTransvection (hp2 : p ≠ 2) (hNT : GGNoTransvection p Bs)
    (ι : Additive ↥Bs ≃+ V) {φ ψ : MulAut ↥Bs} (hφ : φ ∈ ggInduced ⊤ Bs)
    (hψ : ψ ∈ ggInduced ⊤ Bs) {x y : V} {f g : Module.Dual (ZMod p) V} (hfx : f x = 2)
    (hgy : g y = 2) (hLφ : ggLin (p := p) ι φ = reflection hfx)
    (hLψ : ggLin (p := p) ι ψ = reflection hgy) (hfy : f y = 0) : g x = 0 := by
  have h2 := zmod_two_ne_zero hp2
  obtain ⟨hy0, -⟩ := ne_zero_of_apply_eq_two hp2 hgy
  by_contra hgx
  refine hNT ((φ * ψ) ^ 2) (pow_mem_ggInduced (mul_mem_ggInduced hφ hψ) 2) ?_
  refine ggIsTransvection_of_apply ι (w := y) (f := g x • f) hy0 ?_ ?_ ?_
  · intro h0
    have hx := congrArg (fun F : Module.Dual (ZMod p) V => F x) h0
    simp only [LinearMap.smul_apply, smul_eq_mul, hfx, LinearMap.zero_apply] at hx
    exact h2 ((mul_eq_zero.mp hx).resolve_left hgx)
  · rw [LinearMap.smul_apply, hfy, smul_zero]
  · intro v
    rw [map_pow, map_mul, hLφ, hLψ, reflection_mul_reflection_sq_apply_of_eq_zero hfx hgy hfy,
      LinearMap.smul_apply, smul_eq_mul]

theorem ggReflection_fixes_imp_of_noTransvection [Finite G] (hp2 : p ≠ 2)
    (hBs : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs) {φ ψ : MulAut ↥Bs}
    (hφ : φ ∈ ggInduced ⊤ Bs) (hψ : ψ ∈ ggInduced ⊤ Bs) (hφr : GGIsReflection p φ)
    (hψr : GGIsReflection p ψ) (h : ∀ b : ↥Bs, ψ b = b⁻¹ → φ b = b) :
    ∀ b : ↥Bs, φ b = b⁻¹ → ψ b = b := by
  obtain ⟨W, _, _, ⟨ι⟩⟩ := exists_ggLinData (p := p) hBs
  have : Finite W := Finite.of_equiv _ (Additive.ofMul.trans ι.toEquiv)
  have h2 := zmod_two_ne_zero hp2
  obtain ⟨x, f, hfx, hφx⟩ := exists_of_ggIsReflection ι hφr
  obtain ⟨y, g, hgy, hψy⟩ := exists_of_ggIsReflection ι hψr
  obtain ⟨hx0, hf0⟩ := ne_zero_of_apply_eq_two hp2 hfx
  obtain ⟨hy0, -⟩ := ne_zero_of_apply_eq_two hp2 hgy
  have hfy : f y = 0 := by
    set b : ↥Bs := Additive.toMul (ι.symm y) with hbdef
    have hb : ι (Additive.ofMul b) = y := by rw [hbdef, ofMul_toMul, AddEquiv.apply_symm_apply]
    have hψb : ψ b = b⁻¹ := by
      rw [ggLin_inv_iff (p := p) ι, hb, hψy, hgy, two_smul]
      abel
    have hφb := (ggLin_fix_iff (p := p) ι φ b).mp (h b hψb)
    rw [hb, hφx, sub_eq_self, smul_eq_zero] at hφb
    exact hφb.resolve_right hx0
  have hgx : g x = 0 := ggCross_eq_zero_of_noTransvection hp2 hNT ι hφ hψ hfx hgy
    (ggLin_eq_reflection ι hfx hφx) (ggLin_eq_reflection ι hgy hψy) hfy
  intro b hb
  rw [ggLin_inv_iff (p := p) ι, hφx] at hb
  rw [ggLin_fix_iff (p := p) ι, hψy]
  set v := ι (Additive.ofMul b)
  have h2v : (2 : ZMod p) • v - f v • x = 0 := by
    rw [two_smul, ← sub_eq_zero.mpr hb]
    abel
  have hgv := congrArg g h2v
  rw [map_sub, map_smul, map_smul, hgx, smul_zero, sub_zero, map_zero, smul_eq_mul] at hgv
  rw [(mul_eq_zero.mp hgv).resolve_left h2, zero_smul, sub_zero]

theorem ggReflection_fixes_iff_of_noTransvection [Finite G] (hp2 : p ≠ 2)
    (hBs : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs) {φ ψ : MulAut ↥Bs}
    (hφ : φ ∈ ggInduced ⊤ Bs) (hψ : ψ ∈ ggInduced ⊤ Bs) (hφr : GGIsReflection p φ)
    (hψr : GGIsReflection p ψ) :
    (∀ b : ↥Bs, ψ b = b⁻¹ → φ b = b) ↔ (∀ b : ↥Bs, φ b = b⁻¹ → ψ b = b) :=
  ⟨ggReflection_fixes_imp_of_noTransvection hp2 hBs hNT hφ hψ hφr hψr,
    ggReflection_fixes_imp_of_noTransvection hp2 hBs hNT hψ hφ hψr hφr⟩

end GG

end CFSG.StandardType
