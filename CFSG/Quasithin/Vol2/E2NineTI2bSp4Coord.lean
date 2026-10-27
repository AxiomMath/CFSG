module

public import CFSG.Quasithin.Vol2.E2SevenKG7Member

public section

namespace CFSG.Quasithin.E2.TI2b.Sp4

open CFSG.Open CFSG.QuasithinUnique B6
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiSp antiUnipotent minorAut)
open CFSG.Quasithin.Ch3E213M

variable {G : Type} [Group G] [Finite G] {X T M V K : Subgroup G} {k : Type} [Field k] [Finite k]
  [CharP k 2]

theorem exists_coordEmb_conj (D : Sp4Data X T M V K k) (hker : kerIn M X = ⊥) (hMX : M ≤ X)
    (hKX : K ≤ X) :
    ∃ φ : antiSp k →* G, Function.Injective φ ∧ φ.range = K ∧
      (∀ A : Subgroup G, A ≤ X → A.comap φ = coordIn D.θ A) ∧
      ∀ s ∈ barIn M X T, ∀ σ : MulAut (antiSp k), (∀ x, D.θ (D.ι s x) = σ (D.θ x)) →
        ∃ t ∈ T, ∀ a : antiSp k, t * φ a * t⁻¹ = φ (σ a) := by
  set q := QuotientGroup.mk' (kerIn (M.subgroupOf X) ⊤) with hq
  have hqi : Function.Injective q := mk'_kerIn_injective hker hMX
  let e₁ : ↥(K.subgroupOf X) ≃* ↥(barIn M X K) :=
    (K.subgroupOf X).equivMapOfInjective q hqi
  let e₂ : ↥(kZero X M) ≃* ↥(barIn M X K) := MulEquiv.subgroupCongr D.kZero_eq
  let φ : antiSp k →* G := X.subtype.comp ((K.subgroupOf X).subtype.comp
    (e₁.symm.toMonoidHom.comp (e₂.toMonoidHom.comp D.θ.symm.toMonoidHom)))
  have hφq : ∀ y : antiSp k, ∃ hx : φ y ∈ X,
      q ⟨φ y, hx⟩ = ((D.θ.symm y : ↥(kZero X M)) : ↥X ⧸ kerIn (M.subgroupOf X) ⊤) := by
    intro y
    refine ⟨(e₁.symm (e₂ (D.θ.symm y)) : ↥X).2, ?_⟩
    have h1 := congrArg Subtype.val (e₁.apply_symm_apply (e₂ (D.θ.symm y)))
    exact h1
  refine ⟨φ, ?_, ?_, fun A hAX => ?_, fun s hs σ hσ => ?_⟩
  · intro y z hyz
    apply D.θ.symm.injective
    apply e₂.injective
    apply e₁.symm.injective
    apply Subtype.ext
    exact X.subtype_injective hyz
  · ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact Subgroup.mem_subgroupOf.mp (e₁.symm (e₂ (D.θ.symm y))).2
    · intro hx
      obtain ⟨y, hy⟩ := D.θ.symm.surjective (e₂.symm (e₁ ⟨⟨x, hKX hx⟩,
        Subgroup.mem_subgroupOf.mpr hx⟩))
      refine ⟨y, ?_⟩
      change ((e₁.symm (e₂ (D.θ.symm y)) : ↥X) : G) = x
      rw [hy]
      simp only [MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply]
  · ext y
    rw [Subgroup.mem_comap, coordIn, Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf]
    obtain ⟨hx, hqx⟩ := hφq y
    change φ y ∈ A ↔ ((D.θ.symm y : ↥(kZero X M)) : ↥X ⧸ kerIn (M.subgroupOf X) ⊤) ∈
      (A.subgroupOf X).map q
    rw [← hqx]
    constructor
    · intro h
      exact ⟨⟨φ y, hx⟩, Subgroup.mem_subgroupOf.mpr h, rfl⟩
    · rintro ⟨x', hx', hxe⟩
      have := hqi hxe
      rw [this] at hx'
      exact Subgroup.mem_subgroupOf.mp hx'
  ·
    have hs' : s ∈ (T.subgroupOf X).map q := hs
    obtain ⟨x, hxT, hxs⟩ := Subgroup.mem_map.mp hs'
    refine ⟨(x : G), Subgroup.mem_subgroupOf.mp hxT, fun a => ?_⟩
    obtain ⟨ha, hqa⟩ := hφq a
    obtain ⟨hσa, hqσa⟩ := hφq (σ a)
    have hι : D.ι s (D.θ.symm a) = D.θ.symm (σ a) := by
      rw [MulEquiv.eq_symm_apply, hσ (D.θ.symm a), MulEquiv.apply_symm_apply]
    have key : q (x * (⟨φ a, ha⟩ : ↥X) * x⁻¹) = q ⟨φ (σ a), hσa⟩ := by
      rw [map_mul, map_mul, map_inv, hxs, hqa, hqσa, ← hι, D.ι_apply]
    have h2 := congrArg Subtype.val (hqi key)
    simpa using h2

end CFSG.Quasithin.E2.TI2b.Sp4
