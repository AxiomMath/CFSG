module

public import CFSG.RankThree.CentralExtension.InvariantComplement
public import CFSG.LinearAlgebra.OddSolvableUnitary.CommutatorForm


public section

namespace CFSG.RankThree.CentralExtension

open Subgroup
open scoped commutatorElement IsMulCommutative

variable {U Q : Type*} [Group U] [Group Q] {A : Type*} [Group A]

@[expose] def invariantAltForms (p : ℕ) [Module (ZMod p) (Additive (Abelianization Q))]
    (π : U →* Q) (φ : A →* MulAut U) :
    Submodule (ZMod p) (LinearMap.BilinForm (ZMod p) (Additive (Abelianization Q))) where
  carrier := {β | (∀ v, β v v = 0) ∧ ∀ (a : A) (u u' : U),
    β (Additive.ofMul (Abelianization.of (π (φ a u))))
        (Additive.ofMul (Abelianization.of (π (φ a u')))) =
      β (Additive.ofMul (Abelianization.of (π u))) (Additive.ofMul (Abelianization.of (π u')))}
  add_mem' := by
    rintro β β' ⟨hβ, hβi⟩ ⟨hβ', hβ'i⟩
    refine ⟨fun v => ?_, fun a u u' => ?_⟩
    · rw [LinearMap.add_apply, LinearMap.add_apply, hβ v, hβ' v, add_zero]
    · rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.add_apply, LinearMap.add_apply,
        hβi, hβ'i]
  zero_mem' := ⟨fun _ => rfl, fun _ _ _ => rfl⟩
  smul_mem' := by
    rintro c β ⟨hβ, hβi⟩
    refine ⟨fun v => ?_, fun a u u' => ?_⟩
    · rw [LinearMap.smul_apply, LinearMap.smul_apply, hβ v, smul_zero]
    · rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply,
        LinearMap.smul_apply, hβi]

theorem mem_invariantAltForms {p : ℕ} [Module (ZMod p) (Additive (Abelianization Q))]
    {π : U →* Q} {φ : A →* MulAut U}
    {β : LinearMap.BilinForm (ZMod p) (Additive (Abelianization Q))} :
    β ∈ invariantAltForms p π φ ↔ (∀ v, β v v = 0) ∧ ∀ (a : A) (u u' : U),
      β (Additive.ofMul (Abelianization.of (π (φ a u))))
          (Additive.ofMul (Abelianization.of (π (φ a u')))) =
        β (Additive.ofMul (Abelianization.of (π u))) (Additive.ofMul (Abelianization.of (π u'))) :=
  Iff.rfl

theorem exists_smul_eq_of_finrank_eq_one {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] {S : Submodule (ZMod p) (LinearMap.BilinForm (ZMod p) V)}
    (hS : Module.finrank (ZMod p) S = 1) {β₀ β₁ : LinearMap.BilinForm (ZMod p) V} (h₀ : β₀ ∈ S)
    (h₁ : β₁ ∈ S) (hne : β₀ ≠ 0) : ∃ k : ZMod p, k • β₀ = β₁ := by
  let _ : AddCommGroup S :=
    Submodule.addCommGroup (R := ZMod p) (M := LinearMap.BilinForm (ZMod p) V) S
  have hne' : (⟨β₀, h₀⟩ : S) ≠ 0 := fun h => hne (congrArg Subtype.val h)
  obtain ⟨k, hk⟩ := (finrank_eq_one_iff_of_nonzero' (K := ZMod p) _ hne').1 hS ⟨β₁, h₁⟩
  exact ⟨k, congrArg Subtype.val hk⟩

theorem apply_eq_of_trivial_on_center {p : ℕ} [Finite A] (π : U →* Q) (hCp : IsPGroup p π.ker)
    (hA : (Nat.card A).Coprime p) (φ : A →* MulAut U) (hφC : ∀ a, ∀ c ∈ π.ker, φ a c = c)
    (hφZ : ∀ a u, π u ∈ center Q → π (φ a u) = π u) (a : A) {w : U} (hw : π w ∈ center Q) :
    φ a w = w := by
  set c := w⁻¹ * φ a w with hcdef
  have hc : c ∈ π.ker := by
    rw [MonoidHom.mem_ker, hcdef, map_mul, map_inv, hφZ a w hw, inv_mul_cancel]
  have haw : φ a w = w * c := by rw [hcdef, mul_inv_cancel_left]
  have hpow : ∀ k : ℕ, (φ a ^ k) w = w * c ^ k := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_zero, mul_one]; rfl
    | succ k ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hφC a c hc, haw, pow_succ',
        mul_assoc]
  have hcA : c ^ Nat.card A = 1 := by
    have h := hpow (Nat.card A)
    rw [← map_pow, pow_card_eq_one', map_one, MulAut.one_apply] at h
    exact (mul_eq_left.1 h.symm)
  obtain ⟨k, hk⟩ := hCp ⟨c, hc⟩
  have hk' : c ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hcA) (orderOf_dvd_of_pow_eq_one hk')
  rw [Nat.Coprime.gcd_eq_one (hA.pow_right k), Nat.dvd_one, orderOf_eq_one_iff] at hd
  rw [haw, hd, mul_one]

theorem commutatorElement_mul_left_of_central {G : Type*} [Group G]
    (h : ∀ x y : G, ⁅x, y⁆ ∈ center G) (x x' y : G) : ⁅x * x', y⁆ = ⁅x, y⁆ * ⁅x', y⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul, mem_center_iff.1 (h x' y) x,
    mul_inv_cancel_right]
  exact (mem_center_iff.1 (h x' y) ⁅x, y⁆).symm

theorem commutatorElement_mul_right_of_central {G : Type*} [Group G]
    (h : ∀ x y : G, ⁅x, y⁆ ∈ center G) (x y y' : G) : ⁅x, y * y'⁆ = ⁅x, y⁆ * ⁅x, y'⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj, mul_assoc ⁅x, y⁆ y,
    mem_center_iff.1 (h x y') y, ← mul_assoc, mul_inv_cancel_right]

theorem exists_commutator_form {p : ℕ} [Module (ZMod p) (Additive (Abelianization Q))]
    (π : U →* Q) (hπ : Function.Surjective π) (hW : (commutator Q).comap π ≤ center U)
    (f : Additive (commutator U) →+ ZMod p) :
    ∃ β : LinearMap.BilinForm (ZMod p) (Additive (Abelianization Q)), (∀ v, β v v = 0) ∧
      ∀ x y : U, β (Additive.ofMul (Abelianization.of (π x)))
          (Additive.ofMul (Abelianization.of (π y))) =
        f (Additive.ofMul ⟨⁅x, y⁆, commutator_mem_commutator (mem_top x) (mem_top y)⟩) := by
  set vU : U →* Abelianization Q := Abelianization.of.comp π with hvU
  have hvUsurj : Function.Surjective vU := (QuotientGroup.mk_surjective).comp hπ
  have hker : ∀ w, vU w = 1 → w ∈ center U := fun w hw => hW (by
    rw [mem_comap, ← Abelianization.ker_of]
    exact hw)
  have hcent : ∀ x y : U, ⁅x, y⁆ ∈ center U := fun x y => hW (by
    rw [mem_comap, map_commutatorElement]
    exact commutator_mem_commutator (mem_top _) (mem_top _))
  set s := Function.surjInv hvUsurj with hs
  have hvs : ∀ v, vU (s v) = v := Function.surjInv_eq hvUsurj
  let F : U → U → ZMod p := fun x y =>
    f (Additive.ofMul ⟨⁅x, y⁆, commutator_mem_commutator (mem_top x) (mem_top y)⟩)
  have hFw : ∀ x y w w' : U, vU w = 1 → vU w' = 1 → F (x * w) (y * w') = F x y := by
    intro x y w w' hw hw'
    change f _ = f _
    congr 2
    exact Subtype.ext (show ⁅x * w, y * w'⁆ = ⁅x, y⁆ by
      rw [commutatorElement_mul_center_left (hker w hw),
        commutatorElement_mul_center_right (hker w' hw')])
  have hFs : ∀ x y : U, F (s (vU x)) (s (vU y)) = F x y := by
    intro x y
    have h1 : vU (x⁻¹ * s (vU x)) = 1 := by rw [map_mul, map_inv, hvs, inv_mul_cancel]
    have h2 : vU (y⁻¹ * s (vU y)) = 1 := by rw [map_mul, map_inv, hvs, inv_mul_cancel]
    rw [← hFw x y _ _ h1 h2, mul_inv_cancel_left, mul_inv_cancel_left]
  have hFl : ∀ x x' y : U, F (x * x') y = F x y + F x' y := by
    intro x x' y
    change f _ = f _ + f _
    rw [← map_add, ← ofMul_mul]
    congr 2
    exact Subtype.ext (commutatorElement_mul_left_of_central hcent x x' y)
  have hFr : ∀ x y y' : U, F x (y * y') = F x y + F x y' := by
    intro x y y'
    change f _ = f _ + f _
    rw [← map_add, ← ofMul_mul]
    congr 2
    exact Subtype.ext (commutatorElement_mul_right_of_central hcent x y y')
  let G : Additive (Abelianization Q) → Additive (Abelianization Q) → ZMod p := fun v w =>
    F (s (Additive.toMul v)) (s (Additive.toMul w))
  have hG : ∀ x y : U, G (Additive.ofMul (vU x)) (Additive.ofMul (vU y)) = F x y := hFs
  have hsurjV : ∀ v : Additive (Abelianization Q), ∃ x : U, Additive.ofMul (vU x) = v :=
    fun v => ⟨s (Additive.toMul v), by rw [hvs]; rfl⟩
  have hGl : ∀ v v' w, G (v + v') w = G v w + G v' w := by
    intro v v' w
    obtain ⟨x, rfl⟩ := hsurjV v
    obtain ⟨x', rfl⟩ := hsurjV v'
    obtain ⟨y, rfl⟩ := hsurjV w
    rw [← ofMul_mul, ← map_mul, hG, hG, hG, hFl]
  have hGr : ∀ v w w', G v (w + w') = G v w + G v w' := by
    intro v w w'
    obtain ⟨x, rfl⟩ := hsurjV v
    obtain ⟨y, rfl⟩ := hsurjV w
    obtain ⟨y', rfl⟩ := hsurjV w'
    rw [← ofMul_mul, ← map_mul, hG, hG, hG, hFr]
  let β₀ : Additive (Abelianization Q) →+ Additive (Abelianization Q) →+ ZMod p :=
    AddMonoidHom.mk' (fun v => AddMonoidHom.mk' (G v) (hGr v)) fun v v' =>
      AddMonoidHom.ext fun w => hGl v v' w
  let β : LinearMap.BilinForm (ZMod p) (Additive (Abelianization Q)) :=
    AddMonoidHom.toZModLinearMap p
      { toFun := fun v => AddMonoidHom.toZModLinearMap p (β₀ v)
        map_zero' := by ext w; simp
        map_add' := fun v v' => by ext w; simp }
  have hβ : ∀ v w, β v w = G v w := fun v w => rfl
  refine ⟨β, fun v => ?_, fun x y => ?_⟩
  · obtain ⟨x, rfl⟩ := hsurjV v
    rw [hβ, hG]
    change f _ = 0
    rw [← map_zero f]
    congr 2
    exact Subtype.ext (commutatorElement_self x)
  · exact (hβ _ _).trans (hG x y)

theorem extraspecial_coprime_invariant_form_central_extension_unique_complement {p : ℕ}
    [hp : Fact p.Prime] (hp2 : p ≠ 2) [Finite U] (π : U →* Q) (hπ : Function.Surjective π)
    (hC : π.ker ≤ center U) (hCp : IsPGroup p π.ker) (hQexp : ∀ q : Q, q ^ p = 1)
    (hZQ : center Q = commutator Q) (hZcard : Nat.card (center Q) = p)
    [Module (ZMod p) (Additive (Abelianization Q))] [Finite A] (hA : (Nat.card A).Coprime p)
    (φ : A →* MulAut U) (hφC : ∀ a, ∀ c ∈ π.ker, φ a c = c)
    (hφZ : ∀ a u, π u ∈ center Q → π (φ a u) = π u) (b : A)
    (hb : ∀ u : U, Abelianization.of (π (φ b u)) = (Abelianization.of (π u))⁻¹)
    (hdim : Module.finrank (ZMod p) (invariantAltForms p π φ) = 1) :
    π.ker ⊓ commutator U = ⊥ ∧
      ∃ D : Subgroup U, ((∀ a, ∀ d ∈ D, φ a d ∈ D) ∧ π.ker ⊔ D = ⊤ ∧ π.ker ⊓ D = ⊥) ∧
        (∀ D' : Subgroup U, (∀ a, ∀ d ∈ D', φ a d ∈ D') → π.ker ⊔ D' = ⊤ →
          π.ker ⊓ D' = ⊥ → D' = D) ∧
        commutator U ≤ D ∧ D.Normal ∧ Function.Bijective (π.domRestrict D) ∧
        ∃ e : π.ker × D ≃* U, ∀ c d, e (c, d) = (c : U) * d := by
  classical
  have hr : ∀ u : U, (π u ^ (p - 1))⁻¹ * π (φ b u) ∈ center Q := by
    intro u
    have hp1 : Abelianization.of (π u) ^ p = 1 := by rw [← map_pow, hQexp, map_one]
    rw [hZQ, ← Abelianization.ker_of, MonoidHom.mem_ker, map_mul, map_inv, map_pow, hb u,
      pow_pred_eq_inv hp1, inv_inv, mul_inv_cancel]
  have hW := comap_center_le_center_of_scalar π hπ hC hQexp hZQ hZcard (φ b) (hφC b) (p - 1)
    hr (natCast_pred_pow_three_ne_one hp2)
  have hπc : ∀ x y : U, π ⁅x, y⁆ ∈ center Q := fun x y => by
    rw [map_commutatorElement]; exact commutatorElement_mem_center_of_eq hZQ _ _
  have hcent : ∀ x y : U, ⁅x, y⁆ ∈ center U := fun x y => hW (hπc x y)
  have hUc : commutator U ≤ center U := by
    rw [_root_.commutator_def, commutator_le]
    exact fun x _ y _ => hcent x y
  have hπU' : ∀ w ∈ commutator U, π w ∈ center Q := by
    intro w hw
    have h : commutator U ≤ (center Q).comap π := by
      rw [_root_.commutator_def, commutator_le]
      exact fun x _ y _ => hπc x y
    exact h hw
  have hU'p : ∀ w ∈ commutator U, w ^ p = 1 := by
    intro w hw
    simp only [_root_.commutator_def, commutator_def] at hw
    induction hw using closure_induction with
    | mem g hg =>
      obtain ⟨x, -, y, -, rfl⟩ := hg
      have hxp : x ^ p ∈ π.ker := by rw [MonoidHom.mem_ker, map_pow, hQexp]
      rw [Commute.commutatorElement_pow_left
          (show Commute x ⁅x, y⁆ from mem_center_iff.1 (hcent x y) x) p,
        commutatorElement_eq_one_iff_mul_comm]
      exact (mem_center_iff.1 (hC hxp) y).symm
    | one => exact one_pow p
    | mul g h hg _ ihg ihh =>
      have hgc : g ∈ center U := hUc (by
        simp only [_root_.commutator_def, commutator_def]; exact hg)
      rw [Commute.mul_pow (show Commute g h from (mem_center_iff.1 hgc h).symm), ihg, ihh,
        one_mul]
    | inv g _ ih => rw [inv_pow, ih, inv_one]
  have hφU' : ∀ a, ∀ x y : U, φ a ⁅x, y⁆ = ⁅x, y⁆ := fun a x y =>
    apply_eq_of_trivial_on_center π hCp hA φ hφC hφZ a (hπc x y)
  have hCU : π.ker ⊓ commutator U = ⊥ := by
    refine eq_bot_iff.2 fun c hc => ?_
    obtain ⟨hcC, hcU⟩ := mem_inf.1 hc
    rw [mem_bot]
    by_contra hne
    have : IsMulCommutative (commutator U) :=
      ⟨⟨fun a b => Subtype.ext (mem_center_iff.1 (hUc b.2) a)⟩⟩
    have hpsmul : ∀ w : Additive (commutator U), p • w = 0 := by
      intro w
      rw [← toMul_eq_one, toMul_nsmul]
      exact Subtype.ext (by
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
        exact hU'p _ (Additive.toMul w).2)
    have _ : Module (ZMod p) (Additive (commutator U)) := AddCommGroup.zmodModule hpsmul
    obtain ⟨f₁, hf₁⟩ : ∃ f : Additive (commutator U) →ₗ[ZMod p] ZMod p,
        f (Additive.ofMul (⟨c, hcU⟩ : commutator U)) ≠ 0 := by
      by_contra hcon
      simp only [not_exists, ne_eq, not_not] at hcon
      have h0 := (Module.forall_dual_apply_eq_zero_iff (ZMod p)
        (Additive.ofMul (⟨c, hcU⟩ : commutator U))).1 hcon
      exact hne (congrArg Subtype.val (ofMul_eq_zero.1 h0))
    obtain ⟨ε⟩ := CFSG.OddSolvableUnitary.nonempty_center_mulEquiv hZcard
    let g : commutator U →* center Q :=
      (π.domRestrict (commutator U)).codRestrict (center Q) fun w => hπU' w w.2
    let f₀ : Additive (commutator U) →+ ZMod p := MonoidHom.toAdditiveLeft (ε.toMonoidHom.comp g)
    have hf₀ : ∀ w : commutator U, f₀ (Additive.ofMul w) = Multiplicative.toAdd (ε (g w)) :=
      fun w => rfl
    have hWQ : (commutator Q).comap π ≤ center U := hZQ ▸ hW
    obtain ⟨β₀, hβ₀a, hβ₀⟩ := exists_commutator_form π hπ hWQ f₀
    obtain ⟨β₁, hβ₁a, hβ₁⟩ := exists_commutator_form π hπ hWQ f₁.toAddMonoidHom
    have hinvar : ∀ (f : Additive (commutator U) →+ ZMod p)
        (β : LinearMap.BilinForm (ZMod p) (Additive (Abelianization Q))), (∀ v, β v v = 0) →
        (∀ x y : U, β (Additive.ofMul (Abelianization.of (π x)))
          (Additive.ofMul (Abelianization.of (π y))) =
          f (Additive.ofMul ⟨⁅x, y⁆, commutator_mem_commutator (mem_top x) (mem_top y)⟩)) →
        β ∈ invariantAltForms p π φ := by
      intro f β hβa hβ
      refine ⟨hβa, fun a u u' => ?_⟩
      rw [hβ, hβ]
      congr 2
      exact Subtype.ext (show ⁅φ a u, φ a u'⁆ = ⁅u, u'⁆ by
        rw [← map_commutatorElement, hφU'])
    have hβ₀mem := hinvar f₀ β₀ hβ₀a hβ₀
    have hβ₁mem := hinvar f₁.toAddMonoidHom β₁ hβ₁a hβ₁
    have hβ₀ne : β₀ ≠ 0 := by
      intro h0'
      obtain ⟨q₁, q₂, hq⟩ : ∃ q₁ q₂ : Q, ⁅q₁, q₂⁆ ≠ 1 := by
        by_contra hcon
        simp only [not_exists, ne_eq, not_not] at hcon
        have hbot : commutator Q = ⊥ := by
          rw [eq_bot_iff, _root_.commutator_def, commutator_le]
          exact fun x _ y _ => (mem_bot).2 (hcon x y)
        rw [← hZQ] at hbot
        rw [hbot, card_bot] at hZcard
        exact hp.out.one_lt.ne hZcard
      obtain ⟨x, rfl⟩ := hπ q₁
      obtain ⟨y, rfl⟩ := hπ q₂
      have h := hβ₀ x y
      rw [h0', LinearMap.zero_apply, LinearMap.zero_apply, hf₀] at h
      apply hq
      rw [← map_commutatorElement]
      have h1 := h.symm
      rw [← toAdd_one, Multiplicative.toAdd.injective.eq_iff, ← map_one ε,
        ε.injective.eq_iff] at h1
      exact congrArg Subtype.val h1
    obtain ⟨k, hk'⟩ := exists_smul_eq_of_finrank_eq_one hdim hβ₀mem hβ₁mem hβ₀ne
    have hcomm : ∀ x y : U,
        f₁ (Additive.ofMul ⟨⁅x, y⁆, commutator_mem_commutator (mem_top x) (mem_top y)⟩) =
          k * f₀ (Additive.ofMul ⟨⁅x, y⁆, commutator_mem_commutator (mem_top x) (mem_top y)⟩) := by
      intro x y
      have h := hβ₁ x y
      rw [← hk', LinearMap.smul_apply, LinearMap.smul_apply, hβ₀ x y, smul_eq_mul] at h
      exact h.symm
    have hall : ∀ w ∈ commutator U, ∀ hw : w ∈ commutator U,
        f₁ (Additive.ofMul ⟨w, hw⟩) = k * f₀ (Additive.ofMul ⟨w, hw⟩) := by
      intro w hw
      simp only [_root_.commutator_def, commutator_def] at hw
      induction hw using closure_induction with
      | mem g hg =>
        obtain ⟨x, -, y, -, rfl⟩ := hg
        intro _
        exact hcomm x y
      | one =>
        intro _
        rw [show (⟨1, _⟩ : commutator U) = 1 from rfl, ofMul_one, map_zero, map_zero,
          mul_zero]
      | mul g h hg hh ihg ihh =>
        intro _
        have hg' : g ∈ commutator U := by
          simp only [_root_.commutator_def, commutator_def]; exact hg
        have hh' : h ∈ commutator U := by
          simp only [_root_.commutator_def, commutator_def]; exact hh
        rw [show (⟨g * h, _⟩ : commutator U) = ⟨g, hg'⟩ * ⟨h, hh'⟩ from rfl, ofMul_mul, map_add,
          map_add, ihg hg', ihh hh', mul_add]
      | inv g hg ihg =>
        intro _
        have hg' : g ∈ commutator U := by
          simp only [_root_.commutator_def, commutator_def]; exact hg
        rw [show (⟨g⁻¹, _⟩ : commutator U) = (⟨g, hg'⟩)⁻¹ from rfl, ofMul_inv, map_neg,
          map_neg, ihg hg', mul_neg]
    apply hf₁
    have h1 : g ⟨c, hcU⟩ = 1 := Subtype.ext hcC
    change f₁ (Additive.ofMul (⟨c, hcU⟩ : commutator U)) = 0
    rw [hall c hcU hcU, hf₀, h1, map_one, toAdd_one, mul_zero]
  have hAcard : (Nat.card φ.range).Coprime p :=
    Nat.Coprime.coprime_dvd_left (card_range_dvd φ) hA
  have hAfix : ∀ a ∈ φ.range, ∀ c ∈ π.ker, a c = c := by
    rintro _ ⟨a, rfl⟩ c hc
    exact hφC a c hc
  have hDmap : (autCommutator φ.range).map π = ⊤ :=
    map_eq_top_of_scalar π hπ hQexp hZQ (φ b)
      (fun u => inv_mul_apply_mem_autCommutator u ⟨b, rfl⟩) (p - 1) hr
      (natCast_pred_ne_one hp2)
  obtain ⟨hinv, hsup, hinf, hcommD, hnormal, hbij, huniq⟩ :=
    invariant_complement_of_map_eq_top π hC hCp φ.range hAcard hAfix hCU hDmap
  refine ⟨hCU, autCommutator φ.range,
    ⟨fun a d hd => hinv (φ a) ⟨a, rfl⟩ d hd, hsup, hinf⟩, ?_, hcommD,
    hnormal, hbij, exists_mulEquiv_prod_of_central hC hsup hinf⟩
  intro D' hD' hsup' hinf'
  refine huniq D' ?_ hsup' hinf'
  rintro _ ⟨a, rfl⟩ d hd
  exact hD' a d hd

end CFSG.RankThree.CentralExtension
