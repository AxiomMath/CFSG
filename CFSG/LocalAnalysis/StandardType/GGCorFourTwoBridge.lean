module

public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoKantor
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.StandardType

open CFSG.RankThree.PartOne.LIT
open CFSG.RankThree.Classical (IsTransvectionWith)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Linear

variable {p : ℕ} [Fact p.Prime] {H : Type} [CommGroup H] [Module (ZMod p) (Additive H)]

@[expose] noncomputable def ggLinAut : MulAut H →* (Additive H ≃ₗ[ZMod p] Additive H) where
  toFun φ := (MulEquiv.toAdditive φ).toLinearEquiv fun c v =>
    ZMod.map_smul (MulEquiv.toAdditive φ) c v
  map_one' := by
    ext v
    rfl
  map_mul' φ ψ := by
    ext v
    rfl

theorem ggLinAut_apply (φ : MulAut H) (h : H) :
    ggLinAut (p := p) φ (Additive.ofMul h) = Additive.ofMul (φ h) :=
  rfl

theorem ggLinAut_injective : Function.Injective (ggLinAut (p := p) (H := H)) := by
  intro φ ψ hφψ
  ext h
  have := congrArg (fun e : Additive H ≃ₗ[ZMod p] Additive H => e (Additive.ofMul h)) hφψ
  exact Additive.ofMul.injective this

theorem ggLinAut_sub (φ : MulAut H) (h : H) :
    ggLinAut (p := p) φ (Additive.ofMul h) - Additive.ofMul h = Additive.ofMul (h⁻¹ * φ h) := by
  rw [ggLinAut_apply, ← ofMul_div, div_eq_inv_mul]

@[expose] noncomputable def ggFixEquivKer (φ : MulAut H) :
    {h : H // φ h = h} ≃
      LinearMap.ker ((ggLinAut (p := p) φ : Additive H →ₗ[ZMod p] Additive H) - LinearMap.id) where
  toFun h := ⟨Additive.ofMul h.1, by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe,
      ggLinAut_apply, h.2, sub_self]⟩
  invFun v := ⟨Additive.toMul v.1, by
    have h := v.2
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe,
      sub_eq_zero] at h
    have h' : ggLinAut (p := p) φ (Additive.ofMul (Additive.toMul v.1)) =
        Additive.ofMul (Additive.toMul v.1) := h
    rw [ggLinAut_apply] at h'
    exact Additive.ofMul.injective h'⟩
  left_inv h := rfl
  right_inv v := rfl

variable [Finite H]

instance : Module.Finite (ZMod p) (Additive H) := Module.Finite.of_finite

theorem card_eq_pow_finrank_additive : Nat.card H = p ^ Module.finrank (ZMod p) (Additive H) := by
  have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive H)
  rw [Nat.card_zmod] at h
  exact h

theorem exists_isTransvectionWith_of_fix (φ : MulAut H)
    (h1 : Nat.card {h : H // φ h = h} * p = Nat.card H)
    (h2 : ∀ h : H, φ (h⁻¹ * φ h) = h⁻¹ * φ h) :
    ∃ (c : Additive H) (f : Module.Dual (ZMod p) (Additive H)),
      IsTransvectionWith (ggLinAut (p := p) φ) c f := by
  set N : Additive H →ₗ[ZMod p] Additive H :=
    (ggLinAut (p := p) φ : Additive H →ₗ[ZMod p] Additive H) - LinearMap.id with hN
  have hk : Nat.card {h : H // φ h = h} = p ^ Module.finrank (ZMod p) (LinearMap.ker N) := by
    rw [Nat.card_congr (ggFixEquivKer (p := p) φ), Module.natCard_eq_pow_finrank (K := ZMod p),
      Nat.card_zmod]
  have hn := card_eq_pow_finrank_additive (p := p) (H := H)
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hkn : Module.finrank (ZMod p) (LinearMap.ker N) + 1 =
      Module.finrank (ZMod p) (Additive H) := by
    rw [hk, hn, ← pow_succ] at h1
    exact Nat.pow_right_injective (Fact.out : p.Prime).two_le h1
  have hrk := LinearMap.finrank_range_add_finrank_ker (K := ZMod p) N
  have hr : Module.finrank (ZMod p) (LinearMap.range N) = 1 := by omega
  refine exists_isTransvectionWith_of_lin (ggLinAut (p := p) φ) hr ?_
  ext v
  obtain ⟨h, rfl⟩ := Additive.ofMul.surjective v
  have hNh : N (Additive.ofMul h) = Additive.ofMul (h⁻¹ * φ h) := by
    rw [hN, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe, ggLinAut_sub]
  show N (N (Additive.ofMul h)) = 0
  rw [hNh, hN, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe, ggLinAut_apply,
    h2 h, sub_self]

theorem fix_of_isTransvectionWith {φ : MulAut H} {c : Additive H}
    {f : Module.Dual (ZMod p) (Additive H)} (ht : IsTransvectionWith (ggLinAut (p := p) φ) c f) :
    Nat.card {h : H // φ h = h} * p = Nat.card H ∧ ∀ h : H, φ (h⁻¹ * φ h) = h⁻¹ * φ h := by
  obtain ⟨hc, hf, hfc, htx⟩ := ht
  set N : Additive H →ₗ[ZMod p] Additive H :=
    (ggLinAut (p := p) φ : Additive H →ₗ[ZMod p] Additive H) - LinearMap.id with hN
  have hNv : ∀ v, N v = f v • c := by
    intro v
    rw [hN, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe, htx v,
      add_sub_cancel_left]
  have hker : LinearMap.ker N = LinearMap.ker f := by
    ext v
    rw [LinearMap.mem_ker, LinearMap.mem_ker, hNv, smul_eq_zero, or_iff_left hc]
  have hrange : Module.finrank (ZMod p) (LinearMap.range f) = 1 := by
    have hle := Submodule.finrank_le (LinearMap.range f)
    rw [Module.finrank_self] at hle
    have hpos : 0 < Module.finrank (ZMod p) (LinearMap.range f) := by
      rw [Module.finrank_pos_iff_exists_ne_zero]
      obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hf (LinearMap.ext hcon)
      exact ⟨⟨f v, LinearMap.mem_range_self f v⟩, fun h0 => hv (congrArg Subtype.val h0)⟩
    omega
  have hrk := LinearMap.finrank_range_add_finrank_ker (K := ZMod p) f
  have hk : Nat.card {h : H // φ h = h} = p ^ Module.finrank (ZMod p) (LinearMap.ker f) := by
    rw [Nat.card_congr (ggFixEquivKer (p := p) φ), ← hN, hker,
      Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  refine ⟨?_, fun h => ?_⟩
  · rw [hk, card_eq_pow_finrank_additive (p := p), ← pow_succ]
    congr 1
    omega
  · apply Additive.ofMul.injective
    have hNh : N (Additive.ofMul h) = Additive.ofMul (h⁻¹ * φ h) := by
      rw [hN, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe, ggLinAut_sub]
    have h1 : N (Additive.ofMul (h⁻¹ * φ h)) = 0 := by
      rw [← hNh, hNv (Additive.ofMul h), map_smul, hNv c, hfc, zero_smul, smul_zero]
    rw [hN, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe, sub_eq_zero,
      ggLinAut_apply] at h1
    exact h1

omit [Finite H] in
theorem apply_eq_of_isTransvectionWith {φ : MulAut H} {c : Additive H}
    {f : Module.Dual (ZMod p) (Additive H)} (ht : IsTransvectionWith (ggLinAut (p := p) φ) c f)
    {x : H} (hx : f (Additive.ofMul x) = 0) : φ x = x := by
  apply Additive.ofMul.injective
  rw [← ggLinAut_apply (p := p), ht.2.2.2, hx, zero_smul, add_zero]

omit [Finite H] in
theorem exists_notMem_zpowers_of_isTransvectionWith {φ : MulAut H} {c : Additive H}
    {f : Module.Dual (ZMod p) (Additive H)} (ht : IsTransvectionWith (ggLinAut (p := p) φ) c f)
    {x : H} (hcx : c ∉ Submodule.span (ZMod p) {Additive.ofMul x}) :
    ∃ h : H, h⁻¹ * φ h ∉ Subgroup.zpowers x := by
  obtain ⟨hc, hf, hfc, htx⟩ := ht
  obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hf (LinearMap.ext hcon)
  refine ⟨Additive.toMul v, fun hmem => hcx ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have h1 : Additive.ofMul ((Additive.toMul v)⁻¹ * φ (Additive.toMul v)) = f v • c := by
    rw [← ggLinAut_sub (p := p), ofMul_toMul, htx v, add_sub_cancel_left]
  have h2 : f v • c ∈ Submodule.span (ZMod p) {Additive.ofMul x} := by
    rw [← h1, ← hk, ofMul_zpow, ← Int.cast_smul_eq_zsmul (ZMod p)]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have h3 := Submodule.smul_mem _ (f v)⁻¹ h2
  rwa [smul_smul, inv_mul_cancel₀ hv, one_smul] at h3

omit [Finite H] in
theorem map_ggLinAut_noNormalP {A : Subgroup (MulAut H)}
    (hA : ∀ N : Subgroup (MulAut H), N ≤ A → (∀ a ∈ A, ∀ n ∈ N, a * n * a⁻¹ ∈ N) →
      IsPGroup p N → N = ⊥) :
    ∀ N : Subgroup (Additive H ≃ₗ[ZMod p] Additive H), N ≤ A.map (ggLinAut (p := p)) →
      (∀ a ∈ A.map (ggLinAut (p := p)), ∀ n ∈ N, a * n * a⁻¹ ∈ N) → IsPGroup p N → N = ⊥ := by
  intro N hNA hNn hNp
  have hN'A : N.comap (ggLinAut (p := p) (H := H)) ≤ A := by
    intro n hn
    obtain ⟨a, haA, ha⟩ := hNA hn
    rwa [ggLinAut_injective ha] at haA
  have hN'n : ∀ a ∈ A, ∀ n ∈ N.comap (ggLinAut (p := p) (H := H)),
      a * n * a⁻¹ ∈ N.comap (ggLinAut (p := p) (H := H)) := by
    intro a ha n hn
    show ggLinAut (p := p) (a * n * a⁻¹) ∈ N
    rw [map_mul, map_mul, map_inv]
    exact hNn _ ⟨a, ha, rfl⟩ _ hn
  have hbot := hA _ hN'A hN'n (hNp.comap_of_injective _ ggLinAut_injective)
  rw [eq_bot_iff]
  intro n hn
  obtain ⟨a, -, rfl⟩ := hNA hn
  have ha : a ∈ N.comap (ggLinAut (p := p) (H := H)) := hn
  rw [hbot, Subgroup.mem_bot] at ha
  rw [ha, map_one]
  exact Subgroup.one_mem _

theorem exists_subgroup_of_plane {A : Subgroup (MulAut H)} {W : Submodule (ZMod p) (Additive H)}
    (hW : Module.finrank (ZMod p) W = 2) {x : H} (hxW : Additive.ofMul x ∈ W)
    (hinv : ∀ a ∈ A.map (ggLinAut (p := p)), ∀ w ∈ W, a w ∈ W) :
    ∃ E : Subgroup H, Nat.card E = p ^ 2 ∧ x ∈ E ∧ ∀ φ ∈ A, ∀ e ∈ E, φ e ∈ E := by
  refine ⟨AddSubgroup.toSubgroup' W.toAddSubgroup, ?_, hxW, fun φ hφ e he => ?_⟩
  · have hc : Nat.card (AddSubgroup.toSubgroup' W.toAddSubgroup) = Nat.card W :=
      Nat.card_congr
        { toFun := fun e => ⟨Additive.ofMul e.1, e.2⟩
          invFun := fun w => ⟨Additive.toMul w.1, w.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    rw [hc, Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod, hW]
  · exact hinv _ ⟨φ, hφ, rfl⟩ _ he

end Linear

theorem exists_transvection_fix_or_plane_comm (hK : GGKantorReductionInput) {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {H : Type} [CommGroup H] [Module (ZMod p) (Additive H)]
    [Finite H] (A : Subgroup (MulAut H))
    (hA : ∀ N : Subgroup (MulAut H), N ≤ A → (∀ a ∈ A, ∀ n ∈ N, a * n * a⁻¹ ∈ N) →
      IsPGroup p N → N = ⊥)
    (htr : ∃ φ ∈ A, Nat.card {h : H // φ h = h} * p = Nat.card H ∧
      ∀ h : H, φ (h⁻¹ * φ h) = h⁻¹ * φ h) (x : H) :
    (∃ φ ∈ A, (Nat.card {h : H // φ h = h} * p = Nat.card H ∧
        ∀ h : H, φ (h⁻¹ * φ h) = h⁻¹ * φ h) ∧ φ x = x ∧ ∃ h : H, h⁻¹ * φ h ∉ Subgroup.zpowers x) ∨
      ∃ E : Subgroup H, Nat.card E = p ^ 2 ∧ x ∈ E ∧ ∀ φ ∈ A, ∀ e ∈ E, φ e ∈ E := by
  obtain ⟨φ₀, hφ₀A, h1, h2⟩ := htr
  obtain ⟨c₀, f₀, ht₀⟩ := exists_isTransvectionWith_of_fix (p := p) φ₀ h1 h2
  have hA' := map_ggLinAut_noNormalP (p := p) hA
  have htr' : ∃ t ∈ A.map (ggLinAut (p := p)), ∃ (c : Additive H)
      (f : Module.Dual (ZMod p) (Additive H)), IsTransvectionWith t c f :=
    ⟨_, ⟨φ₀, hφ₀A, rfl⟩, c₀, f₀, ht₀⟩
  rcases exists_transvection_fix_or_plane hK hp2 (A.map (ggLinAut (p := p))) hA' htr'
      (Additive.ofMul x) with ⟨t, ⟨φ, hφA, rfl⟩, c, f, ht, hfx, hcx⟩ | ⟨W, hW2, hxW, hWinv⟩
  · exact Or.inl ⟨φ, hφA, fix_of_isTransvectionWith ht, apply_eq_of_isTransvectionWith ht hfx,
      exists_notMem_zpowers_of_isTransvectionWith ht hcx⟩
  · exact Or.inr (exists_subgroup_of_plane hW2 hxW hWinv)

set_option linter.style.haveILetI false in
theorem exists_transvection_fix_or_plane_mul (hK : GGKantorReductionInput) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {H : Type} [Group H] [Finite H]
    (hcomm : ∀ a b : H, a * b = b * a) (hexp : ∀ a : H, a ^ p = 1) (A : Subgroup (MulAut H))
    (hA : ∀ N : Subgroup (MulAut H), N ≤ A → (∀ a ∈ A, ∀ n ∈ N, a * n * a⁻¹ ∈ N) →
      IsPGroup p N → N = ⊥)
    (htr : ∃ φ ∈ A, Nat.card {h : H // φ h = h} * p = Nat.card H ∧
      ∀ h : H, φ (h⁻¹ * φ h) = h⁻¹ * φ h) (x : H) :
    (∃ φ ∈ A, (Nat.card {h : H // φ h = h} * p = Nat.card H ∧
        ∀ h : H, φ (h⁻¹ * φ h) = h⁻¹ * φ h) ∧ φ x = x ∧ ∃ h : H, h⁻¹ * φ h ∉ Subgroup.zpowers x) ∨
      ∃ E : Subgroup H, Nat.card E = p ^ 2 ∧ x ∈ E ∧ ∀ φ ∈ A, ∀ e ∈ E, φ e ∈ E := by
  haveI : Fact p.Prime := ⟨hp⟩
  letI : CommGroup H := { (inferInstance : Group H) with mul_comm := hcomm }
  letI : Module (ZMod p) (Additive H) := AddCommGroup.zmodModule (n := p) fun v => by
    rw [← ofMul_toMul v, ← ofMul_pow, hexp, ofMul_one]
  exact exists_transvection_fix_or_plane_comm hK hp2 A hA htr x

end CFSG.StandardType
