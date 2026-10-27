module

public import CFSG.ClassicalGroups.Orthogonal.CharTwoTransvection
public import CFSG.RankThree.OrthogonalInvolutions.Dickson

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.RankThree.Literature.FSmith

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.OrthogonalInvolutions
open scoped commutatorElement

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {Q : QuadraticForm (ZMod 2) V}

theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  revert a
  decide

theorem zmod2_eq_one_of_ne_zero {a : ZMod 2} (h : a ≠ 0) : a = 1 := by
  revert a
  decide

theorem zmod2_eq_zero_or_eq_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a
  decide

theorem zmod2_eq_of_add_eq_zero {a b : ZMod 2} (h : a + b = 0) : a = b := by
  revert h
  revert a b
  decide

theorem polar_self_zmod2 (x : V) : polar Q x x = 0 := by
  rw [polar_self, two_nsmul, zmod2_add_self]

theorem reflect_mul_reflect_pow_three {u u' : V} (hu : Q u = 1) (hu' : Q u' = 1)
    (huu' : polar Q u u' = 1) : (reflect Q u * reflect Q u') ^ 3 = 1 := by
  have huu : polar Q u u = 0 := polar_self_zmod2 u
  have hu'u' : polar Q u' u' = 0 := polar_self_zmod2 u'
  have hu'u : polar Q u' u = 1 := by rw [polar_comm]; exact huu'
  set g := reflect Q u * reflect Q u' with hgdef
  have hg : ∀ x, g x = x + polar Q x u' • u' + (polar Q x u + polar Q x u') • u := by
    intro x
    rw [hgdef, LinearEquiv.mul_apply, reflect_apply_of_map_eq_one hu',
      reflect_apply_of_map_eq_one hu, polar_add_left, polar_smul_left, hu'u, smul_eq_mul,
      mul_one]
  have hs : ∀ x, polar Q (g x) u = polar Q x u + polar Q x u' := by
    intro x
    rw [hg, polar_add_left, polar_add_left, polar_smul_left, polar_smul_left, hu'u, huu,
      smul_eq_mul, smul_eq_mul, mul_one, mul_zero, add_zero]
  have ht : ∀ x, polar Q (g x) u' = polar Q x u := by
    intro x
    rw [hg, polar_add_left, polar_add_left, polar_smul_left, polar_smul_left, hu'u', huu',
      smul_eq_mul, smul_eq_mul, mul_zero, mul_one, add_zero]
    generalize polar Q x u = a
    generalize polar Q x u' = b
    revert a b
    decide
  ext x
  rw [pow_succ, pow_two, LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.coe_one, id,
    hg (g (g x)), hs, ht, hs, ht, hg (g x), hs, ht, hg x]
  generalize polar Q x u = a
  generalize polar Q x u' = b
  have key : ∀ a b : ZMod 2, b + a + (a + b) = 0 ∧
      (a + b) + (a + b + a) + (a + b + a + (a + b)) = 0 := by decide
  obtain ⟨k1, k2⟩ := key a b
  calc x + b • u' + (a + b) • u + a • u' + (a + b + a) • u + (a + b) • u' +
        (a + b + a + (a + b)) • u
      = x + (b + a + (a + b)) • u' + ((a + b) + (a + b + a) + (a + b + a + (a + b))) • u := by
        module
    _ = x := by rw [k1, k2, zero_smul, zero_smul, add_zero, add_zero]

theorem reflect_mul_reflect_eq_commutator_sq {u u' : V} (hu : Q u = 1) (hu' : Q u' = 1)
    (huu' : polar Q u u' = 1) :
    reflect Q u * reflect Q u' = ⁅reflect Q u, reflect Q u'⁆ ^ 2 := by
  have h3 := reflect_mul_reflect_pow_three hu hu' huu'
  rw [commutatorElement_def, reflect_inv, reflect_inv]
  calc reflect Q u * reflect Q u' = (reflect Q u * reflect Q u') ^ 3 *
        (reflect Q u * reflect Q u') := by rw [h3, one_mul]
    _ = (reflect Q u * reflect Q u' * reflect Q u * reflect Q u') ^ 2 := by
        rw [pow_succ, pow_two, pow_two]; group

theorem conj_mem_commutator_orthogonalGroup {c n : V ≃ₗ[ZMod 2] V}
    (hc : c ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hn : n ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆) :
    c * n * c⁻¹ ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  set O := TauCeti.QuadraticMap.orthogonalGroup Q
  rw [← Subgroup.map_subtype_commutator] at hn ⊢
  obtain ⟨n', hn', rfl⟩ := hn
  refine ⟨⟨c, hc⟩ * n' * ⟨c, hc⟩⁻¹, ?_, rfl⟩
  exact (inferInstance : (_root_.commutator O).Normal).conj_mem n' hn' ⟨c, hc⟩

theorem eq_one_or_eq_reflect_of_fix (hQ : (polarBilin Q).Nondegenerate) {v : V} (hv : Q v = 1)
    {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hfix : ∀ y, polar Q y v = 0 → g y = y) : g = 1 ∨ g = reflect Q v := by
  have hv0 : v ≠ 0 := fun h0 => by rw [h0, map_zero] at hv; exact zero_ne_one hv
  obtain ⟨x₁, hx₁⟩ := exists_polar_ne_zero hQ hv0
  have hx₁' : polar Q v x₁ = 1 := zmod2_eq_one_of_ne_zero hx₁
  set w := g x₁ - x₁ with hw
  have hwperp : ∀ y, polar Q y v = 0 → polar Q w y = 0 := by
    intro y hy
    rw [hw, polar_sub_left, ← hfix y hy, TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg,
      hfix y hy, sub_self]
  have hwv : w = polar Q w x₁ • v := by
    rw [← sub_eq_zero]
    refine eq_zero_of_polar_eq_zero hQ fun y => ?_
    have hy : polar Q (y - polar Q v y • x₁) v = 0 := by
      rw [polar_sub_left, polar_smul_left, polar_comm _ x₁ v, hx₁', smul_eq_mul, mul_one,
        polar_comm, sub_self]
    have h1 := hwperp _ hy
    rw [polar_sub_right, polar_smul_right, smul_eq_mul, sub_eq_zero] at h1
    rw [polar_sub_left, polar_smul_left, smul_eq_mul, h1, polar_comm _ v y]
    ring
  have hgx : ∀ x, g x = x + polar Q v x • w := by
    intro x
    have hx : polar Q (x - polar Q v x • x₁) v = 0 := by
      rw [polar_sub_left, polar_smul_left, polar_comm _ x₁ v, hx₁', smul_eq_mul, mul_one,
        polar_comm, sub_self]
    have h1 := hfix _ hx
    rw [map_sub, map_smul, sub_eq_iff_eq_add] at h1
    rw [h1, hw]
    module
  rcases zmod2_eq_zero_or_eq_one (polar Q w x₁) with h | h
  · left
    ext x
    rw [hgx, hwv, h, zero_smul, smul_zero, add_zero, LinearEquiv.coe_one, id]
  · right
    ext x
    rw [hgx, reflect_apply_of_map_eq_one hv, hwv, h, one_smul, polar_comm]

theorem eq_reflect_of_apply {v : V} (hv : Q v = 1) {r : V ≃ₗ[ZMod 2] V}
    (hr : ∀ u, r u = u + polar Q u v • v) : r = reflect Q v := by
  ext u
  rw [hr, reflect_apply_of_map_eq_one hv]

theorem exists_polar_eq_one_polar_eq_one (hQ : (polarBilin Q).Nondegenerate) {u u' : V}
    (hu : u ≠ 0) (hu' : u' ≠ 0) : ∃ x, polar Q x u = 1 ∧ polar Q x u' = 1 := by
  obtain ⟨x₁, hx₁⟩ := exists_polar_ne_zero hQ hu
  obtain ⟨x₂, hx₂⟩ := exists_polar_ne_zero hQ hu'
  rw [polar_comm] at hx₁ hx₂
  have h1 := zmod2_eq_one_of_ne_zero hx₁
  have h2 := zmod2_eq_one_of_ne_zero hx₂
  by_cases h12 : polar Q x₁ u' = 1
  · exact ⟨x₁, h1, h12⟩
  by_cases h21 : polar Q x₂ u = 1
  · exact ⟨x₂, h21, h2⟩
  have h12' : polar Q x₁ u' = 0 := by
    rcases zmod2_eq_zero_or_eq_one (polar Q x₁ u') with h | h
    · exact h
    · exact absurd h h12
  have h21' : polar Q x₂ u = 0 := by
    rcases zmod2_eq_zero_or_eq_one (polar Q x₂ u) with h | h
    · exact h
    · exact absurd h h21
  refine ⟨x₁ + x₂, ?_, ?_⟩
  · rw [polar_add_left, h1, h21', add_zero]
  · rw [polar_add_left, h12', h2, zero_add]

theorem exists_polar_eq_one_polar_eq_zero (hQ : (polarBilin Q).Nondegenerate) {u u' : V}
    (hu : u ≠ 0) (huu' : u ≠ u') : ∃ x, polar Q x u = 1 ∧ polar Q x u' = 0 := by
  have hsub : u - u' ≠ 0 := sub_ne_zero.mpr huu'
  obtain ⟨x, hx, hx'⟩ := exists_polar_eq_one_polar_eq_one hQ hu hsub
  refine ⟨x, hx, ?_⟩
  rw [polar_sub_right, hx] at hx'
  have h := congrArg (· + polar Q x u') hx'
  simp only [sub_add_cancel] at h
  rw [eq_comm, ← sub_eq_zero] at h
  rw [← h]
  ring

section FiniteDimensional

variable [FiniteDimensional (ZMod 2) V]

theorem exists_map_eq_one_polar_eq_one (hQ : (polarBilin Q).Nondegenerate)
    (h5 : 5 ≤ finrank (ZMod 2) V) {u u' : V} (hu : u ≠ 0) (hu' : u' ≠ 0) :
    ∃ x, Q x = 1 ∧ polar Q x u = 1 ∧ polar Q x u' = 1 := by
  obtain ⟨x₀, h0u, h0u'⟩ := exists_polar_eq_one_polar_eq_one hQ hu hu'
  set f := (polarBilin Q u).prod (polarBilin Q u') with hfdef
  have hmem : ∀ y, y ∈ LinearMap.ker f ↔ polar Q u y = 0 ∧ polar Q u' y = 0 := fun y => by
    simp [hfdef]
  by_contra! hno
  have hzero : ∀ y ∈ LinearMap.ker f, Q (x₀ + y) = 0 := by
    intro y hy
    obtain ⟨hyu, hyu'⟩ := (hmem y).mp hy
    rcases zmod2_eq_zero_or_eq_one (Q (x₀ + y)) with h | h
    · exact h
    · exfalso
      refine hno (x₀ + y) h ?_ ?_
      · rw [polar_add_left, h0u, polar_comm, hyu, add_zero]
      · rw [polar_add_left, h0u', polar_comm, hyu', add_zero]
  have hQx₀ : Q x₀ = 0 := by simpa using hzero 0 (Submodule.zero_mem _)
  have hQK : ∀ y ∈ LinearMap.ker f, Q y = polar Q x₀ y := by
    intro y hy
    have h := hzero y hy
    rw [QuadraticMap.map_add Q, hQx₀, zero_add] at h
    exact zmod2_eq_of_add_eq_zero h
  have hle : LinearMap.ker f ≤
      LinearMap.BilinForm.orthogonal (polarBilin Q) (LinearMap.ker f) := by
    intro a ha
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro b hb
    rw [polarBilin_apply_apply, polar,
      hQK _ (Submodule.add_mem _ hb ha), hQK b hb, hQK a ha, polar_add_right]
    ring
  have h1 := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal hQ] at h1
  have h2 := LinearMap.finrank_range_add_finrank_ker f
  have h3 : finrank (ZMod 2) (LinearMap.range f) ≤ 2 :=
    (Submodule.finrank_le _).trans (by simp)
  omega

theorem exists_ne_zero_polar_eq_zero (h3 : 3 ≤ finrank (ZMod 2) V) (u u' : V) :
    ∃ x, x ≠ 0 ∧ polar Q x u = 0 ∧ polar Q x u' = 0 := by
  set f := (polarBilin Q u).prod (polarBilin Q u') with hfdef
  have h2 := LinearMap.finrank_range_add_finrank_ker f
  have h3' : finrank (ZMod 2) (LinearMap.range f) ≤ 2 :=
    (Submodule.finrank_le _).trans (by simp)
  have hpos : 0 < finrank (ZMod 2) (LinearMap.ker f) := by omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Submodule.one_le_finrank_iff.mp hpos)
  have hfx : polar Q u x = 0 ∧ polar Q u' x = 0 := by
    have h := LinearMap.mem_ker.mp hx
    simpa [hfdef] using h
  exact ⟨x, hx0, by rw [polar_comm]; exact hfx.1, by rw [polar_comm]; exact hfx.2⟩

theorem reflect_mul_reflect_mem_commutator (hQ : (polarBilin Q).Nondegenerate)
    (h5 : 5 ≤ finrank (ZMod 2) V) {u u' : V} (hu : Q u = 1) (hu' : Q u' = 1) :
    reflect Q u * reflect Q u' ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  have hpair : ∀ {a b : V}, Q a = 1 → Q b = 1 → polar Q a b = 1 →
      reflect Q a * reflect Q b ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
    intro a b ha hb hab
    rw [reflect_mul_reflect_eq_commutator_sq ha hb hab]
    exact Subgroup.pow_mem _ (Subgroup.commutator_mem_commutator
      (reflect_mem_orthogonalGroup Q a) (reflect_mem_orthogonalGroup Q b)) 2
  rcases zmod2_eq_zero_or_eq_one (polar Q u u') with h | h
  · have hu0 : u ≠ 0 := fun h0 => by rw [h0, map_zero] at hu; exact zero_ne_one hu
    have hu'0 : u' ≠ 0 := fun h0 => by rw [h0, map_zero] at hu'; exact zero_ne_one hu'
    obtain ⟨x, hx, hxu, hxu'⟩ := exists_map_eq_one_polar_eq_one hQ h5 hu0 hu'0
    have e : reflect Q u * reflect Q u' =
        (reflect Q u * reflect Q x) * (reflect Q x * reflect Q u') := by
      rw [mul_assoc, ← mul_assoc (reflect Q x), reflect_mul_self, one_mul]
    rw [e]
    exact Subgroup.mul_mem _ (hpair hu hx (by rw [polar_comm]; exact hxu)) (hpair hx hu' hxu')
  · exact hpair hu hu' h

theorem commutator_orthogonalGroup_eq_omegaGroup (hQ : (polarBilin Q).Nondegenerate)
    (h6 : 6 ≤ finrank (ZMod 2) V) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      omegaGroup Q hQ := by
  set O := TauCeti.QuadraticMap.orthogonalGroup Q with hOdef
  set N := ⁅O, O⁆ with hNdef
  have hNΩ : N ≤ omegaGroup Q hQ := by
    rw [hNdef, Subgroup.commutator_le]
    intro g hg h hh
    have hk : (⟨⁅g, h⁆, Subgroup.commutator_le_self O
        (Subgroup.commutator_mem_commutator hg hh)⟩ : O) ∈ (dicksonHom Q hQ).ker := by
      rw [MonoidHom.mem_ker]
      have : (⟨⁅g, h⁆, Subgroup.commutator_le_self O
          (Subgroup.commutator_mem_commutator hg hh)⟩ : O) = ⁅(⟨g, hg⟩ : O), ⟨h, hh⟩⁆ := rfl
      rw [this, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, mul_comm]
    rw [dicksonHom_ker, Subgroup.mem_subgroupOf] at hk
    exact hk
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  obtain ⟨v₀, hv₀⟩ := exists_map_ne_zero hQ
  have hv₀1 : Q v₀ = 1 := zmod2_eq_one_of_ne_zero hv₀
  set r₀ := reflect Q v₀ with hr₀
  have hr₀O : r₀ ∈ O := reflect_mem_orthogonalGroup Q v₀
  have hr₀2 : r₀ * r₀ = 1 := reflect_mul_self Q v₀
  have hr₀inv : r₀⁻¹ = r₀ := reflect_inv Q v₀
  have hr₀Ω : r₀ ∉ omegaGroup Q hQ := by
    intro h
    let _ : Invertible (Q v₀) := invertibleOfNonzero hv₀
    have h1 := finrank_commSpace_reflection hQ v₀
    rw [← reflect_eq_reflection] at h1
    have h2 := (mem_omegaGroup.mp h).2
    rw [h1] at h2
    exact Nat.not_even_one h2
  have hgen := orthogonalGroup_eq_closure_reflect hQ (by omega) (Or.inl (by omega))
  have hdich : ∀ g ∈ O, g ∈ N ∨ g * r₀ ∈ N := by
    intro g hg
    rw [hOdef, hgen] at hg
    refine Subgroup.closure_induction (p := fun g _ => g ∈ O ∧ (g ∈ N ∨ g * r₀ ∈ N))
      (fun x hx => ?_) ⟨one_mem _, Or.inl (one_mem _)⟩ (fun x y _ _ hx hy => ?_)
      (fun x _ hx => ?_) hg |>.2
    · obtain ⟨v, rfl⟩ := hx
      refine ⟨reflect_mem_orthogonalGroup Q v, ?_⟩
      rcases zmod2_eq_zero_or_eq_one (Q v) with h | h
      · left
        rw [reflect_of_map_eq_zero h]
        exact one_mem _
      · right
        exact reflect_mul_reflect_mem_commutator hQ (by omega) h hv₀1
    · obtain ⟨hxO, hx⟩ := hx
      obtain ⟨hyO, hy⟩ := hy
      refine ⟨mul_mem hxO hyO, ?_⟩
      have hc : ∀ n ∈ N, r₀⁻¹ * n * r₀ ∈ N := fun n hn => by
        have := conj_mem_commutator_orthogonalGroup (inv_mem hr₀O) hn
        rwa [inv_inv] at this
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact Or.inl (mul_mem hx hy)
      · right
        rw [mul_assoc]
        exact mul_mem hx hy
      · right
        have : x * y * r₀ = x * r₀ * (r₀⁻¹ * y * r₀) := by group
        rw [this]
        exact mul_mem hx (hc y hy)
      · left
        have h11 : r₀⁻¹ * r₀⁻¹ = 1 := by rw [← mul_inv_rev, hr₀2, inv_one]
        have : x * y = x * r₀ * (r₀⁻¹ * (y * r₀) * r₀) * (r₀⁻¹ * r₀⁻¹) := by group
        rw [this, h11, mul_one]
        exact mul_mem hx (hc _ hy)
    · obtain ⟨hxO, hx⟩ := hx
      refine ⟨inv_mem hxO, ?_⟩
      rcases hx with hx | hx
      · exact Or.inl (inv_mem hx)
      · right
        have hc := conj_mem_commutator_orthogonalGroup (inv_mem hr₀O) hx
        rw [inv_inv] at hc
        have : x⁻¹ * r₀ = (r₀⁻¹ * (x * r₀) * r₀⁻¹)⁻¹ := by group
        rw [this, hr₀inv]
        exact inv_mem (by simpa [hr₀inv] using hc)
  refine le_antisymm hNΩ fun g hg => ?_
  rcases hdich g (omegaGroup_le Q hQ hg) with h | h
  · exact h
  · exfalso
    apply hr₀Ω
    have : r₀ = g⁻¹ * (g * r₀) := by group
    rw [this]
    exact mul_mem (inv_mem hg) (hNΩ h)

theorem finrank_commSpace_reflect (hQ : (polarBilin Q).Nondegenerate) {v : V} (hv : Q v = 1) :
    finrank (ZMod 2) (commSpace (reflect Q v)) = 1 := by
  have hv0 : Q v ≠ 0 := by rw [hv]; exact one_ne_zero
  let _ : Invertible (Q v) := invertibleOfNonzero hv0
  rw [reflect_eq_reflection]
  exact finrank_commSpace_reflection hQ v

theorem commutator_orthogonalGroup_eq_subgroupOf (hQ : (polarBilin Q).Nondegenerate)
    (h6 : 6 ≤ finrank (ZMod 2) V) :
    _root_.commutator (TauCeti.QuadraticMap.orthogonalGroup Q) =
      (omegaGroup Q hQ).subgroupOf (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  rw [← commutator_orthogonalGroup_eq_omegaGroup hQ h6, ← Subgroup.map_subtype_commutator,
    Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
      (TauCeti.QuadraticMap.orthogonalGroup Q).subtype_injective]

end FiniteDimensional

end CFSG.RankThree.Literature.FSmith
