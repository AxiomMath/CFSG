module

public import CFSG.Timmesfeld.Bridge.RootStructR2HigmanIrr
public import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

universe u

namespace CFSG.Timmesfeld.Bridge

open CFSG.QuasithinUnique.Setup.SL2Modules
open scoped MatrixGroups

namespace RootMany

theorem two_mul_le_two_pow {k : ℕ} (hk : 1 ≤ k) : 2 * k ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have h2 : 2 ≤ 2 ^ k := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    rw [pow_succ]
    omega

theorem sq_le_card_of_irreducible {m : ℕ} (hm : 1 ≤ m) {F : Type*} [Field F] [Fintype F]
    [CharP F 2] (hF : Fintype.card F = 2 ^ m) {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] (ρ : Representation (ZMod 2) SL(2, F) W) [Fact ρ.IsIrreducible]
    (hnt : ∃ g, ρ g ≠ 1) : (2 ^ m) ^ 2 ≤ Nat.card W := by
  classical
  obtain ⟨d, hd1, hDcard, hb⟩ := binary_SL2_irreducible_Frobenius_descent hm hF ρ hnt
  have hfin : Finite (EndRing ρ) := finite_endRing ρ
  have : Module.Finite (EndRing ρ) W := Module.Finite.of_finite
  obtain ⟨E, _, _, _, ιF, ιD, J, hJne, hJn, -, hshift, hdim⟩ :=
    hb (Module.finBasis (EndRing ρ) W)
  have hWcard : Nat.card W = 2 ^ (d * 2 ^ J.card) := by
    rw [Module.natCard_eq_pow_finrank (K := EndRing ρ) (V := W), hDcard, hdim, ← pow_mul]
  have hkg := Higman.le_card_mul_gcd_of_shift (by omega) hJne hJn hshift
  have hk : 1 ≤ J.card := Finset.card_pos.mpr hJne
  rw [hWcard, ← pow_mul]
  apply Nat.pow_le_pow_right (by norm_num)
  have hg : Nat.gcd m d ≤ d := Nat.gcd_le_right _ (by omega)
  have h2k := two_mul_le_two_pow hk
  calc m * 2 ≤ J.card * Nat.gcd m d * 2 := Nat.mul_le_mul_right 2 hkg
    _ = (2 * J.card) * Nat.gcd m d := by ring
    _ ≤ 2 ^ J.card * d := Nat.mul_le_mul h2k hg
    _ = d * 2 ^ J.card := by ring

theorem eq_one_of_trivial_of_perfect {K : Type*} [Group K] (hK : commutator K = ⊤)
    {U : Type*} [AddCommGroup U] [Module (ZMod 2) U] (ρ : Representation (ZMod 2) K U)
    (X : Submodule (ZMod 2) U) (h1 : ∀ g, ∀ x ∈ X, ρ g x = x) (h2 : ∀ g u, ρ g u - u ∈ X)
    (g : K) : ρ g = 1 := by
  let ψ : K →* Multiplicative (U →ₗ[ZMod 2] U) :=
    { toFun := fun g => Multiplicative.ofAdd (ρ g - 1)
      map_one' := by simp
      map_mul' := fun g g' => by
        rw [← ofAdd_add]
        congr 1
        refine LinearMap.ext fun u => ?_
        simp only [LinearMap.sub_apply, LinearMap.add_apply, Module.End.one_apply, map_mul,
          Module.End.mul_apply]
        have hw := h2 g' u
        have hfix := h1 g _ hw
        rw [map_sub] at hfix
        have : ρ g (ρ g' u) = ρ g u + (ρ g' u - u) := by
          rw [← hfix]
          abel
        rw [this]
        abel }
  have hker := Abelianization.commutator_subset_ker ψ
  rw [hK] at hker
  have hg := hker (Subgroup.mem_top g)
  rw [MonoidHom.mem_ker] at hg
  have : ρ g - 1 = 0 := by
    have := congrArg Multiplicative.toAdd hg
    simpa [ψ] using this
  exact sub_eq_zero.mp this

theorem exists_irreducible_subquotient_of_perfect {K : Type*} [Group K] (hK : commutator K = ⊤)
    (n : ℕ) :
    ∀ {U : Type u} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
      (ρ : Representation (ZMod 2) K U), Module.finrank (ZMod 2) U = n → (∃ g, ρ g ≠ 1) →
      ∃ (Y : Type u) (_ : AddCommGroup Y) (_ : Module (ZMod 2) Y) (_ : Finite Y)
        (σ : Representation (ZMod 2) K Y), σ.IsIrreducible ∧ (∃ g, σ g ≠ 1) ∧
          Nat.card Y ≤ Nat.card U := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro U _ _ _ ρ hn hρ
    obtain ⟨k, hk⟩ := hρ
    have hU : Nontrivial U := by
      by_contra h
      rw [not_nontrivial_iff_subsingleton] at h
      exact hk (LinearMap.ext fun u => Subsingleton.elim _ _)
    by_cases hirr : ρ.IsIrreducible
    · exact ⟨U, inferInstance, inferInstance, inferInstance, ρ, hirr, ⟨k, hk⟩, le_rfl⟩
    have hXex : ∃ Xs : Subrepresentation ρ, Xs ≠ ⊥ ∧ Xs ≠ ⊤ := by
      by_contra h
      push Not at h
      apply hirr
      have : Nontrivial (Subrepresentation ρ) := by
        refine ⟨⊥, ⊤, fun h' => ?_⟩
        obtain ⟨x, y, hxy⟩ := hU
        have h2 : (⊥ : Submodule (ZMod 2) U) = ⊤ := congrArg Subrepresentation.toSubmodule h'
        have h3 : x - y ∈ (⊥ : Submodule (ZMod 2) U) := h2 ▸ Submodule.mem_top
        exact hxy (sub_eq_zero.mp ((Submodule.mem_bot _).mp h3))
      exact { eq_bot_or_eq_top := fun X => (em (X = ⊥)).imp_right (h X) }
    obtain ⟨Xs, hXbot, hXtop⟩ := hXex
    set X := Xs.toSubmodule with hX
    have hXbot' : X ≠ ⊥ := fun h => hXbot (Subrepresentation.toSubmodule_injective h)
    have hXtop' : X ≠ ⊤ := fun h => hXtop (Subrepresentation.toSubmodule_injective h)
    have hfin : Module.Finite (ZMod 2) U := Module.Finite.of_finite
    by_cases hX1 : ∃ g, ∃ x ∈ X, ρ g x ≠ x
    · have hlt : Module.finrank (ZMod 2) X < n := by
        rw [← hn]
        exact Submodule.finrank_lt hXtop'
      obtain ⟨g, x, hx, hne⟩ := hX1
      obtain ⟨Y, i1, i2, i3, σ, h1, h2, h3⟩ := ih _ hlt (U := ↥X) Xs.toRepresentation rfl
        ⟨g, by
          intro h
          apply hne
          have := LinearMap.congr_fun h ⟨x, hx⟩
          exact congrArg Subtype.val this⟩
      refine ⟨Y, i1, i2, i3, σ, h1, h2, h3.trans ?_⟩
      exact Nat.card_le_card_of_injective _ Subtype.val_injective
    · push Not at hX1
      have hlt : Module.finrank (ZMod 2) (U ⧸ X) < n := by
        have h1 := Submodule.finrank_quotient_add_finrank X
        have h2 : 1 ≤ Module.finrank (ZMod 2) X := Submodule.one_le_finrank_iff.mpr hXbot'
        omega
      have hQfin : Finite (U ⧸ X) :=
        Finite.of_surjective Submodule.Quotient.mk (Submodule.Quotient.mk_surjective X)
      have hQnt : ∃ g, Xs.quotient g ≠ 1 := by
        by_contra h
        push Not at h
        apply hk
        refine eq_one_of_trivial_of_perfect hK ρ X hX1 (fun g u => ?_) k
        have h3 : (Submodule.Quotient.mk (ρ g u) : U ⧸ X) = Submodule.Quotient.mk u :=
          LinearMap.congr_fun (h g) (Submodule.Quotient.mk u)
        exact (Submodule.Quotient.eq X).mp h3
      obtain ⟨Y, i1, i2, i3, σ, h1, h2, h3⟩ := ih _ hlt (U := U ⧸ X) Xs.quotient rfl hQnt
      refine ⟨Y, i1, i2, i3, σ, h1, h2, h3.trans ?_⟩
      exact Nat.card_le_card_of_surjective _ (Submodule.Quotient.mk_surjective X)

theorem sq_le_card_of_nontrivial {m : ℕ} (hm : 2 ≤ m) {F : Type*} [Field F] [Fintype F]
    [CharP F 2] (hF : Fintype.card F = 2 ^ m) {U : Type u} [AddCommGroup U] [Module (ZMod 2) U]
    [Finite U] (ρ : Representation (ZMod 2) SL(2, F) U) (hnt : ∃ g, ρ g ≠ 1) :
    (2 ^ m) ^ 2 ≤ Nat.card U := by
  have hperf : commutator SL(2, F) = ⊤ := by
    have h4 : ∃ s : Finset F, s.card = 4 := by
      classical
      have h : 4 ≤ Fintype.card F := by
        rw [hF]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
        (show 4 ≤ (Finset.univ : Finset F).card by rw [Finset.card_univ]; exact h)
      exact ⟨s, hs⟩
    exact (CFSG.LinearGroups.special_linear_dimension_two_perfect h4).commutator_eq_top
  obtain ⟨Y, _, _, _, σ, hσ, hσnt, hcard⟩ :=
    exists_irreducible_subquotient_of_perfect hperf _ ρ rfl hnt
  have : Fact σ.IsIrreducible := ⟨hσ⟩
  exact (sq_le_card_of_irreducible (by omega) hF σ hσnt).trans hcard

section GroupForm

variable {R : Type*} [Group R] (M A : Subgroup R) [M.Normal] [A.Normal]

abbrev quotCommGroup (hcomm : ∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ A) :
    CommGroup (M ⧸ A.subgroupOf M) :=
  { (inferInstance : Group (M ⧸ A.subgroupOf M)) with
    mul_comm := fun u v => by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective u
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective v
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      have h := hcomm _ (inv_mem y.2) _ (inv_mem x.2)
      simp only [inv_inv] at h
      simpa [mul_assoc] using h }

@[expose] def conjQuot (r : R) : M ⧸ A.subgroupOf M →* M ⧸ A.subgroupOf M :=
  QuotientGroup.map _ _ (MulAut.conjNormal r).toMonoidHom fun x hx => by
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom,
      MulAut.conjNormal_apply]
    exact ‹A.Normal›.conj_mem _ (Subgroup.mem_subgroupOf.mp hx) r

theorem conjQuot_mk (r : R) (x : M) :
    conjQuot M A r (x : M ⧸ A.subgroupOf M) =
      ((⟨r * x * r⁻¹, ‹M.Normal›.conj_mem _ x.2 r⟩ : M) : M ⧸ A.subgroupOf M) := by
  rw [conjQuot, QuotientGroup.map_mk]
  exact congrArg _ (Subtype.ext (MulAut.conjNormal_apply r x))

end GroupForm

theorem sq_mul_card_le_card {m : ℕ} (hm : 2 ≤ m) {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 2 ^ m) {R : Type u} [Group R] [Finite R] (f : R →* SL(2, F))
    (hf : Function.Surjective f) {M A : Subgroup R} (hAM : A ≤ M) [A.Normal]
    (hker : f.ker = M) (hcomm : ∀ x ∈ M, ∀ y ∈ M, x * y * x⁻¹ * y⁻¹ ∈ A)
    (hsq : ∀ x ∈ M, x * x ∈ A) (hnt : ∃ r : R, ∃ x ∈ M, r * x * r⁻¹ * x⁻¹ ∉ A) :
    (2 ^ m) ^ 2 * Nat.card A ≤ Nat.card M := by
  classical
  subst hker
  have : Fintype F := Fintype.ofFinite F
  have hF' : Fintype.card F = 2 ^ m := by rw [← Nat.card_eq_fintype_card, hF]
  let _ := quotCommGroup f.ker A hcomm
  have h2 : ∀ v : Additive (f.ker ⧸ A.subgroupOf f.ker), 2 • v = 0 := by
    intro v
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    have hv : v = Additive.ofMul (x : f.ker ⧸ A.subgroupOf f.ker) := by rw [hx]; rfl
    rw [hv, ← ofMul_pow, ← ofMul_one, ← QuotientGroup.mk_pow]
    congr 1
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, pow_two]
    exact hsq _ x.2
  let _ : Module (ZMod 2) (Additive (f.ker ⧸ A.subgroupOf f.ker)) := AddCommGroup.zmodModule h2
  have : Finite (Additive (f.ker ⧸ A.subgroupOf f.ker)) :=
    Finite.of_surjective (fun x : f.ker => Additive.ofMul (x : f.ker ⧸ A.subgroupOf f.ker))
      fun v => by
        obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
        refine ⟨x, ?_⟩
        show Additive.ofMul (x : f.ker ⧸ A.subgroupOf f.ker) = v
        rw [hx]
        rfl
  let ρR : R →* (Additive (f.ker ⧸ A.subgroupOf f.ker) →ₗ[ZMod 2]
      Additive (f.ker ⧸ A.subgroupOf f.ker)) :=
    { toFun := fun r => (MonoidHom.toAdditive (conjQuot f.ker A r)).toZModLinearMap 2
      map_one' := by
        refine LinearMap.ext fun v => ?_
        obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
        have hv : v = Additive.ofMul (x : f.ker ⧸ A.subgroupOf f.ker) := by rw [hx]; rfl
        subst hv
        show Additive.ofMul (conjQuot f.ker A 1 (x : f.ker ⧸ A.subgroupOf f.ker)) =
          Additive.ofMul (x : f.ker ⧸ A.subgroupOf f.ker)
        rw [conjQuot_mk]
        congr 2
        exact Subtype.ext (by simp)
      map_mul' := fun r s => by
        refine LinearMap.ext fun v => ?_
        obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
        have hv : v = Additive.ofMul (x : f.ker ⧸ A.subgroupOf f.ker) := by rw [hx]; rfl
        subst hv
        show Additive.ofMul (conjQuot f.ker A (r * s) (x : f.ker ⧸ A.subgroupOf f.ker)) =
          Additive.ofMul (conjQuot f.ker A r (conjQuot f.ker A s
            (x : f.ker ⧸ A.subgroupOf f.ker)))
        rw [conjQuot_mk, conjQuot_mk, conjQuot_mk]
        congr 2
        exact Subtype.ext (by simp [mul_assoc]) }
  have hρR : ∀ (r : R) (x : f.ker), ρR r (Additive.ofMul (x : f.ker ⧸ A.subgroupOf f.ker)) =
      Additive.ofMul ((⟨r * x * r⁻¹, (MonoidHom.normal_ker f).conj_mem _ x.2 r⟩ : f.ker) :
        f.ker ⧸ A.subgroupOf f.ker) := fun r x => congrArg Additive.ofMul (conjQuot_mk _ _ r x)
  have hρker : f.ker ≤ ρR.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    refine LinearMap.ext fun v => ?_
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    have hv : v = Additive.ofMul (y : f.ker ⧸ A.subgroupOf f.ker) := by rw [hy]; rfl
    subst hv
    rw [hρR, Module.End.one_apply]
    congr 1
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h := hcomm x hx _ (inv_mem y.2)
    simp only [inv_inv] at h
    simpa [mul_assoc] using h
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  let ρ : Representation (ZMod 2) SL(2, F) (Additive (f.ker ⧸ A.subgroupOf f.ker)) :=
    (QuotientGroup.lift f.ker ρR hρker).comp e.symm.toMonoidHom
  have hρ : ∀ r, ρ (f r) = ρR r := by
    intro r
    have he : e.symm (f r) = (r : R ⧸ f.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show QuotientGroup.lift f.ker ρR hρker (e.symm (f r)) = ρR r
    rw [he, QuotientGroup.lift_mk]
  have hnt' : ∃ g, ρ g ≠ 1 := by
    obtain ⟨r, x, hx, hrx⟩ := hnt
    refine ⟨f r, fun h => hrx ?_⟩
    rw [hρ] at h
    have h' := LinearMap.congr_fun h
      (Additive.ofMul ((⟨x, hx⟩ : f.ker) : f.ker ⧸ A.subgroupOf f.ker))
    rw [hρR, Module.End.one_apply] at h'
    have h'' := Additive.ofMul.injective h'
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h''
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h''
    have h3 := ‹A.Normal›.conj_mem _ (inv_mem h'') x
    have e3 : x * ((r * x * r⁻¹)⁻¹ * x)⁻¹ * x⁻¹ = r * x * r⁻¹ * x⁻¹ := by group
    rwa [e3] at h3
  have hcard := sq_le_card_of_nontrivial hm hF' ρ hnt'
  have hL := Subgroup.card_eq_card_quotient_mul_card_subgroup (A.subgroupOf f.ker)
  have hA : Nat.card ↥(A.subgroupOf f.ker) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv
  calc (2 ^ m) ^ 2 * Nat.card A ≤ Nat.card (f.ker ⧸ A.subgroupOf f.ker) * Nat.card A :=
        Nat.mul_le_mul_right _ hcard
    _ = Nat.card f.ker := by rw [hL, hA]

end RootMany

end CFSG.Timmesfeld.Bridge
