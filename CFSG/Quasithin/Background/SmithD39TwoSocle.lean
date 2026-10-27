module

public import CFSG.Quasithin.EmptyFaithful.SmithD391Decomp
public import CFSG.Quasithin.EmptyFaithful.SmithD391Hom
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.SmithD39Two

open CFSG.Quasithin.Z391 CFSG.Quasithin.SmithD391
open scoped Pointwise

section Modules

variable {R : Type*} [Ring R]

theorem card_linearMap_eq {I X S : Type*} [AddCommGroup I] [Module R I] [AddCommGroup X]
    [Module R X] [AddCommGroup S] [Module R S] [Finite I] [Finite X] [Finite S]
    [IsSimpleModule R I] [IsSemisimpleModule R X] [IsSemisimpleModule R S]
    (hX : IsIsotypicOfType R X I) (hS : IsIsotypicOfType R S I) {d c : ℕ}
    (hd : Nat.card X = Nat.card I ^ d) (hc : Nat.card S = Nat.card I ^ c) :
    Nat.card (X →ₗ[R] S) = Nat.card (Module.End R I) ^ (d * c) := by
  classical
  obtain ⟨d', ⟨eX⟩⟩ := hX.linearEquiv_fun
  obtain ⟨c', ⟨eS⟩⟩ := hS.linearEquiv_fun
  have : Nontrivial I := IsSimpleModule.nontrivial R I
  have hI1 : 1 < Nat.card I := Finite.one_lt_card
  have hd' : d' = d := by
    have h1 : Nat.card X = Nat.card I ^ d' := by
      rw [Nat.card_congr eX.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin d'),
        Fintype.card_fin]
    exact Nat.pow_right_injective hI1 (h1.symm.trans hd)
  have hc' : c' = c := by
    have h1 : Nat.card S = Nat.card I ^ c' := by
      rw [Nat.card_congr eS.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin c'),
        Fintype.card_fin]
    exact Nat.pow_right_injective hI1 (h1.symm.trans hc)
  subst hd' hc'
  let e₁ : (X →ₗ[R] S) ≃ ((Fin d' → I) →ₗ[R] (Fin c' → I)) :=
    { toFun := fun f => eS.toLinearMap ∘ₗ f ∘ₗ eX.symm.toLinearMap
      invFun := fun g => eS.symm.toLinearMap ∘ₗ g ∘ₗ eX.toLinearMap
      left_inv := fun f => by ext x; simp
      right_inv := fun g => by ext x; simp }
  let e₂ : ((Fin d' → I) →ₗ[R] (Fin c' → I)) ≃ (Fin c' → ((Fin d' → I) →ₗ[R] I)) :=
    { toFun := fun f i => (LinearMap.proj i) ∘ₗ f
      invFun := fun g => LinearMap.pi g
      left_inv := fun f => by ext x i; simp
      right_inv := fun g => by funext i; ext x; simp }
  let e₃ : ((Fin d' → I) →ₗ[R] I) ≃ (Fin d' → (I →ₗ[R] I)) :=
    (LinearMap.lsum R (fun _ : Fin d' => I) ℕ).symm.toEquiv
  rw [Nat.card_congr (e₁.trans e₂), Nat.card_fun, Nat.card_congr e₃, Nat.card_fun,
    Nat.card_eq_fintype_card (α := Fin d'), Nat.card_eq_fintype_card (α := Fin c'),
    Fintype.card_fin, Fintype.card_fin, ← pow_mul]

theorem isIsotypicOfType_quotient {M S : Type*} [AddCommGroup M] [Module R M] [AddCommGroup S]
    [Module R S] [IsSemisimpleModule R M] (h : IsIsotypicOfType R M S) (N : Submodule R M) :
    IsIsotypicOfType R (M ⧸ N) S := by
  obtain ⟨P, ⟨eP⟩⟩ := IsSemisimpleModule.exists_submodule_linearEquiv_quotient N
  have h2 : IsIsotypicOfType R P S := h.of_injective P.subtype P.subtype_injective
  exact (LinearEquiv.isIsotypicOfType_iff eP).1 h2

end Modules

section Isotypic

variable {A : Type*} [Group A] {Q : Type*} [CommGroup Q] [MulDistribMulAction A Q]

variable (A) in
@[expose] def isoComp (I : Subgroup Q) : Subgroup Q :=
  ⨆ J : {J : Subgroup Q // XMod.IsIrr A J ∧ XMod.Iso A J I}, (J : Subgroup Q)

theorem le_isoComp {I J : Subgroup Q} (hJ : XMod.IsIrr A J) (hJI : XMod.Iso A J I) :
    J ≤ isoComp A I :=
  le_iSup (fun J : {J : Subgroup Q // XMod.IsIrr A J ∧ XMod.Iso A J I} => (J : Subgroup Q))
    ⟨J, hJ, hJI⟩

theorem isInv_isoComp (I : Subgroup Q) : XMod.IsInv A (isoComp A I) :=
  XMod.isInv_iSup fun J => J.2.1.1

theorem card_toSubmod {S : Subgroup Q} (hS : XMod.IsInv A S) :
    Nat.card ↥(XMod.toSubmod hS) = Nat.card ↥S :=
  Nat.card_congr
    { toFun := fun p => ⟨Additive.toMul p.1, p.2⟩
      invFun := fun s => ⟨Additive.ofMul s.1, s.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem toSubmod_le_isotypicComponent {I S : Subgroup Q} (hI : XMod.IsIrr A I)
    (hS : XMod.IsInv A S) (hSI : S ≤ isoComp A I) :
    XMod.toSubmod hS ≤
      isotypicComponent ↥(XMod.opRing A Q) (Additive Q) ↥(XMod.toSubmod hI.1) := by
  have h1 : XMod.toSubmod hS ≤ XMod.toSubmod (isInv_isoComp (A := A) I) :=
    XMod.toSubmod_le_iff.2 hSI
  refine h1.trans ?_
  rw [show XMod.toSubmod (isInv_isoComp (A := A) I) = XMod.toSubmod (XMod.isInv_iSup
      (fun J : {J : Subgroup Q // XMod.IsIrr A J ∧ XMod.Iso A J I} => J.2.1.1)) from rfl,
    XMod.toSubmod_iSup (fun J : {J : Subgroup Q // XMod.IsIrr A J ∧ XMod.Iso A J I} => J.2.1.1)]
  exact iSup_le fun J => le_sSup (XMod.nonempty_linearEquiv_of_iso J.2.1.1 hI.1 J.2.2)

theorem isSemisimpleModule_toSubmod {I S : Subgroup Q} (hI : XMod.IsIrr A I)
    (hS : XMod.IsInv A S) (hSI : S ≤ isoComp A I) :
    IsSemisimpleModule ↥(XMod.opRing A Q) ↥(XMod.toSubmod hS) := by
  have := (XMod.isIrr_iff hI.1).1 hI
  have h := toSubmod_le_isotypicComponent hI hS hSI
  exact IsSemisimpleModule.of_injective (Submodule.inclusion h) (Submodule.inclusion_injective h)

theorem isIsotypicOfType_toSubmod {I S : Subgroup Q} (hI : XMod.IsIrr A I)
    (hS : XMod.IsInv A S) (hSI : S ≤ isoComp A I) :
    IsIsotypicOfType ↥(XMod.opRing A Q) ↥(XMod.toSubmod hS) ↥(XMod.toSubmod hI.1) := by
  have := (XMod.isIrr_iff hI.1).1 hI
  have h := toSubmod_le_isotypicComponent hI hS hSI
  exact (IsIsotypicOfType.isotypicComponent _ _ _).of_injective (Submodule.inclusion h)
    (Submodule.inclusion_injective h)

theorem exists_rk_eq_mul [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) {I S : Subgroup Q}
    (hI : XMod.IsIrr A I) (hS : XMod.IsInv A S) (hSI : S ≤ isoComp A I) :
    ∃ c : ℕ, rk ↥S = c * rk ↥I := by
  have := isSemisimpleModule_toSubmod hI hS hSI
  obtain ⟨c, ⟨e⟩⟩ := (isIsotypicOfType_toSubmod hI hS hSI).linearEquiv_fun
  refine ⟨c, ?_⟩
  have h1 : Nat.card ↥S = Nat.card ↥I ^ c := by
    rw [← card_toSubmod hS, ← card_toSubmod hI.1, Nat.card_congr e.toEquiv, Nat.card_fun,
      Nat.card_eq_fintype_card (α := Fin c), Fintype.card_fin]
  rw [card_eq_two_pow hQ S, card_eq_two_pow hQ I, ← pow_mul] at h1
  have := Nat.pow_right_injective le_rfl h1
  rw [this, mul_comm]

@[expose] def IsotypicOfLength (A : Type*) [Group A] [MulDistribMulAction A Q]
    (S I : Subgroup Q) (k : ℕ) : Prop :=
  XMod.IsInv A S ∧ S ≤ isoComp A I ∧ rk ↥S = k * rk ↥I

theorem IsotypicOfLength.exists_of_le [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) {I S T : Subgroup Q}
    {k : ℕ} (hI : XMod.IsIrr A I) (hS : IsotypicOfLength A S I k) (hT : XMod.IsInv A T)
    (hTS : T ≤ S) : ∃ c : ℕ, IsotypicOfLength A T I c := by
  obtain ⟨c, hc⟩ := exists_rk_eq_mul hQ hI hT (hTS.trans hS.2.1)
  exact ⟨c, hT, hTS.trans hS.2.1, hc⟩

end Isotypic

section Layer

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

theorem opRing_apply_ofMul_smul {Λ : Subgroup Γ} {x : Γ} (hx : ∀ l ∈ Λ, l * x = x * l)
    {r : AddMonoid.End (Additive Q)} (hr : r ∈ XMod.opRing ↥Λ Q) (q : Q) :
    r (Additive.ofMul (x • q)) = Additive.ofMul (x • Additive.toMul (r (Additive.ofMul q))) := by
  induction hr using Subring.closure_induction generalizing q with
  | mem f hf =>
    obtain ⟨l, rfl⟩ := hf
    show Additive.ofMul ((l : Γ) • x • q) = Additive.ofMul (x • (l : Γ) • q)
    rw [smul_smul, smul_smul, hx l l.2]
  | zero =>
    show (0 : Additive Q) = Additive.ofMul (x • Additive.toMul (0 : Additive Q))
    rw [toMul_zero, smul_one, ofMul_one]
  | one => rfl
  | add f g _ _ hf hg =>
    show f (Additive.ofMul (x • q)) + g (Additive.ofMul (x • q)) =
      Additive.ofMul (x • Additive.toMul (f (Additive.ofMul q) + g (Additive.ofMul q)))
    rw [hf, hg, toMul_add, smul_mul', ofMul_mul]
  | neg f _ hf =>
    show -(f (Additive.ofMul (x • q))) =
      Additive.ofMul (x • Additive.toMul (-(f (Additive.ofMul q))))
    rw [hf, toMul_neg, smul_inv', ofMul_inv]
  | mul f g _ _ hf hg =>
    show f (g (Additive.ofMul (x • q))) =
      Additive.ofMul (x • Additive.toMul (f (g (Additive.ofMul q))))
    rw [hg, hf, ofMul_toMul]

@[expose] def commMap {Λ : Subgroup Γ} {x : Γ} (hx : ∀ l ∈ Λ, l * x = x * l)
    {U S : Subgroup Q} (hU : XMod.IsInv ↥Λ U) (hS : XMod.IsInv ↥Λ S)
    (hxU : ∀ u ∈ U, x • u * u⁻¹ ∈ S) :
    ↥(XMod.toSubmod hU) →ₗ[↥(XMod.opRing ↥Λ Q)] ↥(XMod.toSubmod hS) where
  toFun p := ⟨Additive.ofMul (x • Additive.toMul p.1 * (Additive.toMul p.1)⁻¹), hxU _ p.2⟩
  map_add' p p' := by
    apply Subtype.ext
    show Additive.ofMul (x • Additive.toMul (p.1 + p'.1) * (Additive.toMul (p.1 + p'.1))⁻¹) =
      Additive.ofMul (x • Additive.toMul p.1 * (Additive.toMul p.1)⁻¹) +
        Additive.ofMul (x • Additive.toMul p'.1 * (Additive.toMul p'.1)⁻¹)
    rw [← ofMul_mul, toMul_add, smul_mul']
    congr 1
    rw [mul_inv]
    ac_rfl
  map_smul' r p := by
    apply Subtype.ext
    show Additive.ofMul (x • Additive.toMul (r.1 p.1) * (Additive.toMul (r.1 p.1))⁻¹) =
      r.1 (Additive.ofMul (x • Additive.toMul p.1 * (Additive.toMul p.1)⁻¹))
    have h1 : Additive.ofMul (x • Additive.toMul p.1 * (Additive.toMul p.1)⁻¹) =
        Additive.ofMul (x • Additive.toMul p.1) + -p.1 := by
      rw [ofMul_mul, ofMul_inv, ofMul_toMul]
    rw [h1, map_add, map_neg, opRing_apply_ofMul_smul hx r.2 (Additive.toMul p.1), ofMul_toMul,
      ofMul_mul, ofMul_inv, ofMul_toMul]

theorem card_end_le [Finite Q] {Λ : Subgroup Γ} {I : Subgroup Q} (hI : XMod.IsInv ↥Λ I) :
    Nat.card (Module.End ↥(XMod.opRing ↥Λ Q) ↥(XMod.toSubmod hI)) ≤
      Nat.card {θ : ↥I →* ↥I // IsEqv Λ (I.subtype.comp θ)} := by
  classical
  have : Finite (↥I →* ↥I) := Finite.of_injective (fun θ : ↥I →* ↥I => (θ : ↥I → ↥I))
    DFunLike.coe_injective
  let θ : Module.End ↥(XMod.opRing ↥Λ Q) ↥(XMod.toSubmod hI) → (↥I →* ↥I) := fun g =>
    { toFun := fun v => ⟨Additive.toMul (g ⟨Additive.ofMul v.1, v.2⟩).1, (g _).2⟩
      map_one' := by
        apply Subtype.ext
        show Additive.toMul (g 0).1 = 1
        rw [map_zero]
        rfl
      map_mul' := fun v w => by
        apply Subtype.ext
        show Additive.toMul (g (⟨Additive.ofMul v.1, v.2⟩ + ⟨Additive.ofMul w.1, w.2⟩)).1 =
          Additive.toMul (g ⟨Additive.ofMul v.1, v.2⟩).1 *
            Additive.toMul (g ⟨Additive.ofMul w.1, w.2⟩).1
        rw [map_add]
        rfl }
  have hθ : ∀ g, IsEqv Λ (I.subtype.comp (θ g)) := by
    intro g l v w hvw
    have h1 : (⟨Additive.ofMul w.1, w.2⟩ : ↥(XMod.toSubmod hI)) =
        (⟨XMod.actEnd ↥Λ Q l, XMod.actEnd_mem_opRing l⟩ : ↥(XMod.opRing ↥Λ Q)) •
          ⟨Additive.ofMul v.1, v.2⟩ := by
      apply Subtype.ext
      show Additive.ofMul w.1 = XMod.actEnd ↥Λ Q l (Additive.ofMul v.1)
      rw [← hvw]
      rfl
    show Additive.toMul (g ⟨Additive.ofMul w.1, w.2⟩).1 =
      (l : Γ) • Additive.toMul (g ⟨Additive.ofMul v.1, v.2⟩).1
    rw [h1, map_smul]
    rfl
  let f : Module.End ↥(XMod.opRing ↥Λ Q) ↥(XMod.toSubmod hI) →
      {θ : ↥I →* ↥I // IsEqv Λ (I.subtype.comp θ)} := fun g => ⟨θ g, hθ g⟩
  have hf : Function.Injective f := by
    intro g g' h
    refine LinearMap.ext fun p => Subtype.ext ?_
    have h1 := congrArg (fun t : {θ : ↥I →* ↥I // IsEqv Λ (I.subtype.comp θ)} =>
      ((t.1 ⟨Additive.toMul p.1, p.2⟩ : ↥I) : Q)) h
    exact congrArg Additive.ofMul h1
  exact Nat.card_le_card_of_injective f hf

theorem rk_le_add_of_layer [Finite Γ] [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) {Λ X : Subgroup Γ}
    (hΛX : ∀ l ∈ Λ, ∀ x ∈ X, l * x = x * l) {I T U S : Subgroup Q} (hI : XMod.IsIrr ↥Λ I)
    (hT : XMod.IsInv ↥Λ T) (hU : XMod.IsInv ↥Λ U) (hS : XMod.IsInv ↥Λ S) (hTU : T ≤ U)
    (hUI : U ≤ isoComp ↥Λ I) (hSI : S ≤ isoComp ↥Λ I)
    (hXU : ∀ x ∈ X, ∀ u ∈ U, x • u * u⁻¹ ∈ S) (hXT : ∀ x ∈ X, ∀ t ∈ T, x • t = t)
    (hXS : ∀ x ∈ X, ∀ s ∈ S, x • s = s) {d c e : ℕ} (hd : rk ↥U = rk ↥T + d * rk ↥I)
    (hc : rk ↥S = c * rk ↥I)
    (he : Nat.card {θ : ↥I →* ↥I // IsEqv Λ (I.subtype.comp θ)} ≤ 2 ^ e) :
    rk ↥X ≤ e * d * c + rk ↥(X ⊓ fixingSubgroup Γ (U : Set Q)) := by
  classical
  have : IsSimpleModule ↥(XMod.opRing ↥Λ Q) ↥(XMod.toSubmod hI.1) := (XMod.isIrr_iff hI.1).1 hI
  have := isSemisimpleModule_toSubmod hI hU hUI
  have := isSemisimpleModule_toSubmod hI hS hSI
  have hUiso := isIsotypicOfType_toSubmod hI hU hUI
  have hSiso := isIsotypicOfType_toSubmod hI hS hSI
  set U' := XMod.toSubmod hU with hU'
  set T' := XMod.toSubmod hT with hT'
  set S' := XMod.toSubmod hS with hS'
  set I' := XMod.toSubmod hI.1 with hI'
  set N : Submodule ↥(XMod.opRing ↥Λ Q) ↥U' := T'.comap U'.subtype with hN
  have : Finite (↥U' ⧸ N) := Finite.of_surjective N.mkQ N.mkQ_surjective
  have hXiso : IsIsotypicOfType ↥(XMod.opRing ↥Λ Q) (↥U' ⧸ N) ↥I' :=
    isIsotypicOfType_quotient hUiso N
  have hcardI : Nat.card ↥I' = 2 ^ rk ↥I := by rw [card_toSubmod, card_eq_two_pow hQ]
  have hcardS : Nat.card ↥S' = Nat.card ↥I' ^ c := by
    rw [card_toSubmod, card_eq_two_pow hQ, hc, hcardI, ← pow_mul, mul_comm]
  have hcardN : Nat.card ↥N = Nat.card ↥T := by
    rw [← card_toSubmod hT]
    exact Nat.card_congr
      { toFun := fun p => ⟨p.1.1, p.2⟩
        invFun := fun t => ⟨⟨t.1, hTU t.2⟩, t.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hcardX : Nat.card (↥U' ⧸ N) = Nat.card ↥I' ^ d := by
    have h1 := Submodule.card_eq_card_quotient_mul_card N
    rw [card_toSubmod, hcardN, card_eq_two_pow hQ U, card_eq_two_pow hQ T, hd, pow_add] at h1
    rw [hcardI, ← pow_mul, mul_comm]
    exact (Nat.eq_of_mul_eq_mul_left (by positivity) h1).symm
  have hHom := card_linearMap_eq hXiso hSiso hcardX hcardS
  have hEnd : Nat.card (Module.End ↥(XMod.opRing ↥Λ Q) ↥I') ≤ 2 ^ e :=
    (card_end_le hI.1).trans he
  have hcomm : ∀ x : ↥X, ∀ l ∈ Λ, l * (x : Γ) = (x : Γ) * l := fun x l hl => hΛX l hl x x.2
  let D : ↥X → (↥U' →ₗ[↥(XMod.opRing ↥Λ Q)] ↥S') := fun x => commMap (hcomm x) hU hS (hXU x x.2)
  have hDN : ∀ x : ↥X, N ≤ LinearMap.ker (D x) := by
    intro x p hp
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    show Additive.ofMul ((x : Γ) • Additive.toMul p.1 * (Additive.toMul p.1)⁻¹) = 0
    have h := hXT x x.2 (Additive.toMul p.1) hp
    rw [h, mul_inv_cancel]
    rfl
  let φ : ↥X → (↥U' ⧸ N →ₗ[↥(XMod.opRing ↥Λ Q)] ↥S') := fun x => N.liftQ (D x) (hDN x)
  have hφ : ∀ (x : ↥X) (p : ↥U'), φ x (N.mkQ p) = D x p := fun x p => N.liftQ_apply _ p
  have hDmul : ∀ x y : ↥X, D (x * y) = D y + D x := by
    intro x y
    refine LinearMap.ext fun p => Subtype.ext ?_
    show Additive.ofMul (((x : Γ) * (y : Γ)) • Additive.toMul p.1 * (Additive.toMul p.1)⁻¹) =
      Additive.ofMul ((y : Γ) • Additive.toMul p.1 * (Additive.toMul p.1)⁻¹) +
        Additive.ofMul ((x : Γ) • Additive.toMul p.1 * (Additive.toMul p.1)⁻¹)
    set u := Additive.toMul p.1 with hu
    have hyu : (y : Γ) • u * u⁻¹ ∈ S := hXU y y.2 u p.2
    have hfix : (x : Γ) • ((y : Γ) • u * u⁻¹) = (y : Γ) • u * u⁻¹ := hXS x x.2 _ hyu
    rw [← ofMul_mul]
    congr 1
    rw [mul_smul]
    have h2 : (y : Γ) • u = ((y : Γ) • u * u⁻¹) * u := by group
    rw [h2, smul_mul', hfix]
    group
  have hφmul : ∀ x y : ↥X, φ (x * y) = φ y + φ x := by
    intro x y
    refine Submodule.linearMap_qext N (LinearMap.ext fun p => ?_)
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.add_apply, hφ, hDmul]
  have hφzero : ∀ x : ↥X, φ x = 0 ↔ (x : Γ) ∈ fixingSubgroup Γ (U : Set Q) := by
    intro x
    rw [mem_fixingSubgroup_iff]
    constructor
    · intro h u hu
      have h2 := congrArg (fun f => ((f (N.mkQ ⟨Additive.ofMul u, hu⟩) : ↥S') : Additive Q)) h
      simp only [hφ, LinearMap.zero_apply, ZeroMemClass.coe_zero] at h2
      have h3 : (x : Γ) • u * u⁻¹ = 1 := h2
      exact mul_inv_eq_one.1 h3
    · intro h
      refine Submodule.linearMap_qext N (LinearMap.ext fun p => Subtype.ext ?_)
      show Additive.ofMul ((x : Γ) • Additive.toMul p.1 * (Additive.toMul p.1)⁻¹) = 0
      rw [h (Additive.toMul p.1) p.2, mul_inv_cancel]
      rfl
  set K : Subgroup ↥X := (X ⊓ fixingSubgroup Γ (U : Set Q)).subgroupOf X with hK
  have hfib : ∀ x y : ↥X, φ x = φ y ↔ x⁻¹ * y ∈ K := by
    intro x y
    have h1 : φ y = φ (x⁻¹ * y) + φ x := by rw [← hφmul, mul_inv_cancel_left]
    rw [h1, hK, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h2 : φ (x⁻¹ * y) = 0 := by
        refine Submodule.linearMap_qext N (LinearMap.ext fun p => ?_)
        have h3 := congrArg (fun g => g (N.mkQ p)) h
        simp only [LinearMap.add_apply] at h3
        have h4 : (φ (x⁻¹ * y)) (N.mkQ p) + (φ x) (N.mkQ p) = 0 + (φ x) (N.mkQ p) := by
          rw [zero_add]; exact h3.symm
        simpa using add_right_cancel h4
      exact ⟨(x⁻¹ * y).2, (hφzero _).1 h2⟩
    · intro h
      rw [(hφzero _).2 h.2, zero_add]
  have hcardK : Nat.card ↥K = Nat.card ↥(X ⊓ fixingSubgroup Γ (U : Set Q)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  let f : ↥X ⧸ K → (↥U' ⧸ N →ₗ[↥(XMod.opRing ↥Λ Q)] ↥S') :=
    Quotient.lift φ (fun a b hab => (hfib a b).2 (QuotientGroup.leftRel_apply.1 hab))
  have hf : Function.Injective f := by
    intro a b hab
    induction a using QuotientGroup.induction_on with
    | H a =>
      induction b using QuotientGroup.induction_on with
      | H b => exact QuotientGroup.eq.2 ((hfib a b).1 hab)
  have : Finite (↥U' ⧸ N →ₗ[↥(XMod.opRing ↥Λ Q)] ↥S') :=
    Finite.of_injective (fun g : ↥U' ⧸ N →ₗ[↥(XMod.opRing ↥Λ Q)] ↥S' => (g : ↥U' ⧸ N → ↥S'))
      DFunLike.coe_injective
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup K
  have hquot : Nat.card (↥X ⧸ K) ≤ 2 ^ (e * d * c) := by
    calc Nat.card (↥X ⧸ K) ≤ Nat.card (↥U' ⧸ N →ₗ[↥(XMod.opRing ↥Λ Q)] ↥S') :=
          Nat.card_le_card_of_injective f hf
      _ = Nat.card (Module.End ↥(XMod.opRing ↥Λ Q) ↥I') ^ (d * c) := hHom
      _ ≤ (2 ^ e) ^ (d * c) := Nat.pow_le_pow_left hEnd _
      _ = 2 ^ (e * d * c) := by rw [← pow_mul, mul_assoc]
  have h2 : padicValNat 2 (Nat.card (↥X ⧸ K)) ≤ e * d * c := by
    have h3 : 2 ^ padicValNat 2 (Nat.card (↥X ⧸ K)) ≤ Nat.card (↥X ⧸ K) :=
      Nat.le_of_dvd Nat.card_pos pow_padicValNat_dvd
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 (h3.trans hquot)
  unfold rk
  rw [h1, padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', hcardK]
  omega

@[instance_reducible] private noncomputable def cosetAct {B : Subgroup Γ} {T Y : Subgroup Q}
    (hTB : ∀ b ∈ B, ∀ t ∈ T, b • t ∈ T) (hYB : ∀ b ∈ B, ∀ y ∈ Y, b • y ∈ Y) :
    MulAction ↥B (↥Y ⧸ T.subgroupOf Y) where
  smul b := QuotientGroup.map (T.subgroupOf Y) (T.subgroupOf Y)
    (MonoidHom.mk' (fun y : ↥Y => (⟨(b : Γ) • (y : Q), hYB b b.2 y y.2⟩ : ↥Y))
      (fun y y' => Subtype.ext (smul_mul' (b : Γ) (y : Q) y')))
    (fun y hy => hTB b b.2 _ hy)
  one_smul q := by
    induction q using QuotientGroup.induction_on with
    | H y =>
      show (QuotientGroup.mk (⟨((1 : ↥B) : Γ) • (y : Q), _⟩ : ↥Y) : ↥Y ⧸ T.subgroupOf Y) =
        QuotientGroup.mk y
      congr 1
      exact Subtype.ext (one_smul Γ (y : Q))
  mul_smul b b' q := by
    induction q using QuotientGroup.induction_on with
    | H y =>
      show (QuotientGroup.mk (⟨((b * b' : ↥B) : Γ) • (y : Q), _⟩ : ↥Y) :
        ↥Y ⧸ T.subgroupOf Y) = QuotientGroup.mk ⟨(b : Γ) • (b' : Γ) • (y : Q), _⟩
      congr 1
      exact Subtype.ext (mul_smul (b : Γ) (b' : Γ) (y : Q))

theorem exists_mem_not_mem_of_lt [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) {B : Subgroup Γ}
    (hB : IsPGroup 2 ↥B) {T Y : Subgroup Q} (hTY : T < Y) (hTB : ∀ b ∈ B, ∀ t ∈ T, b • t ∈ T)
    (hYB : ∀ b ∈ B, ∀ y ∈ Y, b • y ∈ Y) :
    ∃ y ∈ Y, y ∉ T ∧ ∀ b ∈ B, b • y * y⁻¹ ∈ T := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _i := cosetAct hTB hYB
  have hsmul : ∀ (b : ↥B) (y : ↥Y), b • (QuotientGroup.mk y : ↥Y ⧸ T.subgroupOf Y) =
      QuotientGroup.mk ⟨(b : Γ) • (y : Q), hYB b b.2 y y.2⟩ := fun _ _ => rfl
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (T.subgroupOf Y)
  have hTcard : Nat.card ↥(T.subgroupOf Y) = Nat.card ↥T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTY.le).toEquiv
  rw [hTcard, Subgroup.card_top.symm.trans (Subgroup.card_top (G := ↥Y)), card_eq_two_pow hQ Y,
    card_eq_two_pow hQ T] at hcard
  have hlt : rk ↥T < rk ↥Y := by
    by_contra hle
    exact hTY.ne (eq_of_le_of_rk_le hQ hTY.le (by omega))
  have h2 : 2 ∣ Nat.card (↥Y ⧸ T.subgroupOf Y) := by
    have h3 : Nat.card (↥Y ⧸ T.subgroupOf Y) = 2 ^ (rk ↥Y - rk ↥T) := by
      have h4 : 2 ^ rk ↥Y = 2 ^ (rk ↥Y - rk ↥T) * 2 ^ rk ↥T := by
        rw [← pow_add, Nat.sub_add_cancel hlt.le]
      rw [h4] at hcard
      exact (Nat.eq_of_mul_eq_mul_right (by positivity) hcard).symm
    rw [h3]
    exact dvd_pow_self 2 (by omega)
  have h1 : (1 : ↥Y ⧸ T.subgroupOf Y) ∈ MulAction.fixedPoints ↥B (↥Y ⧸ T.subgroupOf Y) := by
    intro b
    show b • (QuotientGroup.mk (1 : ↥Y) : ↥Y ⧸ T.subgroupOf Y) = QuotientGroup.mk 1
    rw [hsmul]
    congr 1
    exact Subtype.ext (smul_one (b : Γ))
  obtain ⟨q, hq, hne⟩ := hB.exists_fixed_point_of_prime_dvd_card_of_fixed_point _ h2 h1
  induction q using QuotientGroup.induction_on with
  | H y =>
    refine ⟨y, y.2, fun hyT => hne ?_, fun b hb => ?_⟩
    · exact (QuotientGroup.eq_one_iff y).2 hyT |>.symm
    · have h3 := hq ⟨b, hb⟩
      rw [hsmul, QuotientGroup.eq] at h3
      have h4 : ((⟨b • (y : Q), hYB b hb y y.2⟩ : ↥Y)⁻¹ * y : Q) ∈ T := h3
      have h5 := T.inv_mem h4
      simp only [Subgroup.coe_inv, mul_inv_rev, inv_inv] at h5
      rwa [mul_comm] at h5

end Layer

section Socle

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

private def nextLayer (B : Subgroup Γ) (T Y : Subgroup Q) : Subgroup Q where
  carrier := {y | y ∈ Y ∧ ∀ b ∈ B, b • y * y⁻¹ ∈ T}
  mul_mem' := by
    rintro y y' ⟨hy, hyB⟩ ⟨hy', hy'B⟩
    refine ⟨Y.mul_mem hy hy', fun b hb => ?_⟩
    have h1 : b • (y * y') * (y * y')⁻¹ = (b • y * y⁻¹) * (b • y' * y'⁻¹) := by
      rw [smul_mul', mul_inv]
      ac_rfl
    rw [h1]
    exact T.mul_mem (hyB b hb) (hy'B b hb)
  one_mem' := ⟨Y.one_mem, fun b _ => by rw [smul_one, inv_one, mul_one]; exact T.one_mem⟩
  inv_mem' := by
    rintro y ⟨hy, hyB⟩
    refine ⟨Y.inv_mem hy, fun b hb => ?_⟩
    have h1 : b • y⁻¹ * y⁻¹⁻¹ = (b • y * y⁻¹)⁻¹ := by
      rw [smul_inv', mul_inv, inv_inv]
    rw [h1]
    exact T.inv_mem (hyB b hb)

theorem rk_le_of_socle [Finite Γ] [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) {Λ B : Subgroup Γ}
    (hΛB : ∀ l ∈ Λ, ∀ b ∈ B, l * b = b * l) (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hB2 : ∀ b ∈ B, b ^ 2 = 1) {I Y : Subgroup Q} (hI : XMod.IsIrr ↥Λ I) {k c e : ℕ}
    (hY : IsotypicOfLength ↥Λ Y I k) (hYB : ∀ b ∈ B, ∀ y ∈ Y, b • y ∈ Y)
    (hc : rk ↥(Y ⊓ XMod.fixed ↥B ⊤) = c * rk ↥I)
    (he : Nat.card {θ : ↥I →* ↥I // IsEqv Λ (I.subtype.comp θ)} ≤ 2 ^ e) :
    rk ↥B ≤ e * c * (k - c) + rk ↥(B ⊓ fixingSubgroup Γ (Y : Set Q)) := by
  obtain ⟨hYΛ, hYI, hYk⟩ := hY
  have hBp : IsPGroup 2 ↥B := fun b => ⟨1, Subtype.ext (by simpa using hB2 b b.2)⟩
  have hrkI : 0 < rk ↥I := by
    rcases Nat.eq_zero_or_pos (rk ↥I) with h | h
    · exact absurd ((rk_eq_zero_iff hQ).1 h) hI.2.1.ne'
    · exact h
  set S₁ := Y ⊓ XMod.fixed ↥B (⊤ : Subgroup Q) with hS₁
  have hS₁B : ∀ b ∈ B, ∀ s ∈ S₁, b • s = s := fun b hb s hs => hs.2.2 ⟨b, hb⟩
  have hS₁Λ : XMod.IsInv ↥Λ S₁ := by
    intro l s hs
    refine ⟨hYΛ l s hs.1, trivial, fun b => ?_⟩
    change (b : Γ) • (l : Γ) • s = (l : Γ) • s
    rw [smul_smul, ← hΛB l l.2 b b.2, mul_smul, hS₁B b b.2 s hs]
  have key : ∀ n : ℕ, ∀ T : Subgroup Q, ∀ t : ℕ, XMod.IsInv ↥Λ T →
      (∀ b ∈ B, ∀ x ∈ T, b • x ∈ T) → S₁ ≤ T → T ≤ Y → rk ↥T = t * rk ↥I → k - t = n →
      rk ↥(B ⊓ fixingSubgroup Γ (T : Set Q)) ≤
        e * c * (k - t) + rk ↥(B ⊓ fixingSubgroup Γ (Y : Set Q)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro T t hTΛ hTB hS₁T hTY hTt hn
    rcases hTY.lt_or_eq with hlt | heq
    swap
    · rw [heq]
      exact Nat.le_add_left _ _
    set Tp := nextLayer B T Y with hTp
    have hTpY : Tp ≤ Y := fun y hy => hy.1
    have hTTp : T ≤ Tp := fun x hx => ⟨hTY hx, fun b hb => T.mul_mem (hTB b hb x hx)
      (T.inv_mem hx)⟩
    have hTpΛ : XMod.IsInv ↥Λ Tp := by
      intro l y hy
      refine ⟨hYΛ l y hy.1, fun b hb => ?_⟩
      have h1 : b • ((l : Γ) • y) * ((l : Γ) • y)⁻¹ = (l : Γ) • (b • y * y⁻¹) := by
        rw [smul_mul', smul_inv', smul_smul, smul_smul, hΛB l l.2 b hb]
      change b • ((l : Γ) • y) * ((l : Γ) • y)⁻¹ ∈ T
      rw [h1]
      exact hTΛ l _ (hy.2 b hb)
    have hTpB : ∀ b ∈ B, ∀ y ∈ Tp, b • y ∈ Tp := by
      intro b' hb' y hy
      refine ⟨hYB b' hb' y hy.1, fun b hb => ?_⟩
      have h1 : b • (b' • y) * (b' • y)⁻¹ = b' • (b • y * y⁻¹) := by
        rw [smul_mul', smul_inv', smul_smul, smul_smul, hBc b hb b' hb']
      rw [h1]
      exact hTB b' hb' _ (hy.2 b hb)
    have hTlt : T < Tp := by
      obtain ⟨y, hyY, hyT, hyB⟩ := exists_mem_not_mem_of_lt hQ hBp hlt hTB hYB
      exact lt_of_le_of_ne hTTp fun h => hyT (h ▸ (⟨hyY, hyB⟩ : y ∈ Tp))
    obtain ⟨tp, htp⟩ := exists_rk_eq_mul hQ hI hTpΛ (hTpY.trans hYI)
    have htlt : t < tp := by
      have h1 : rk ↥T < rk ↥Tp := by
        by_contra hle
        exact hTlt.ne (eq_of_le_of_rk_le hQ hTTp (by omega))
      rw [hTt, htp] at h1
      exact lt_of_mul_lt_mul_right h1 (Nat.zero_le _)
    have htpk : tp ≤ k := by
      have h1 : rk ↥Tp ≤ rk ↥Y := rk_mono hTpY
      rw [htp, hYk] at h1
      exact le_of_mul_le_mul_right h1 hrkI
    have hIH := ih (k - tp) (by omega) Tp tp hTpΛ hTpB (hS₁T.trans hTTp) hTpY htp rfl
    have hXU : ∀ x ∈ B ⊓ fixingSubgroup Γ (T : Set Q), ∀ u ∈ Tp, x • u * u⁻¹ ∈ S₁ := by
      intro x hx u hu
      refine ⟨Y.mul_mem (hYB x hx.1 u (hTpY hu)) (Y.inv_mem (hTpY hu)), trivial, fun b => ?_⟩
      have hw : (b : Γ) • u * u⁻¹ ∈ T := hu.2 b b.2
      have hxw : x • ((b : Γ) • u * u⁻¹) = (b : Γ) • u * u⁻¹ :=
        (mem_fixingSubgroup_iff Γ).1 hx.2 _ hw
      have hbu : (b : Γ) • u = ((b : Γ) • u * u⁻¹) * u := by group
      change (b : Γ) • (x • u * u⁻¹) = x • u * u⁻¹
      rw [smul_mul', smul_inv', smul_smul, ← hBc x hx.1 b b.2, mul_smul, hbu, smul_mul', hxw]
      generalize (b : Γ) • u * u⁻¹ = w
      generalize x • u = z
      rw [mul_inv, mul_comm w z, mul_assoc, ← mul_assoc w, mul_inv_cancel, one_mul]
    have hd : rk ↥Tp = rk ↥T + (tp - t) * rk ↥I := by
      rw [htp, hTt, Nat.sub_mul]
      have := Nat.mul_le_mul_right (rk ↥I) htlt.le
      omega
    have hlayer := rk_le_add_of_layer hQ (X := B ⊓ fixingSubgroup Γ (T : Set Q))
      (fun l hl x hx => hΛB l hl x hx.1) hI hTΛ hTpΛ hS₁Λ hTTp (hTpY.trans hYI)
      ((inf_le_left : S₁ ≤ Y).trans hYI) hXU
      (fun x hx t ht => (mem_fixingSubgroup_iff Γ).1 hx.2 t ht)
      (fun x hx s hs => hS₁B x hx.1 s hs) hd hc he
    have hinf : B ⊓ fixingSubgroup Γ (T : Set Q) ⊓ fixingSubgroup Γ (Tp : Set Q) =
        B ⊓ fixingSubgroup Γ (Tp : Set Q) := by
      rw [inf_assoc]
      congr 1
      refine inf_eq_right.2 fun g hg => (mem_fixingSubgroup_iff Γ).2 fun x hx =>
        (mem_fixingSubgroup_iff Γ).1 hg x (hTTp hx)
    rw [hinf] at hlayer
    have hsplit : k - t = (tp - t) + (k - tp) := by omega
    rw [hsplit, mul_add]
    have h1 : e * (tp - t) * c = e * c * (tp - t) := by ring
    rw [h1] at hlayer
    omega
  have hS₁T : B ⊓ fixingSubgroup Γ (S₁ : Set Q) = B :=
    inf_eq_left.2 fun b hb => (mem_fixingSubgroup_iff Γ).2 fun s hs => hS₁B b hb s hs
  have h := key (k - c) S₁ c hS₁Λ (fun b hb s hs => by rw [hS₁B b hb s hs]; exact hs) le_rfl
    inf_le_left hc rfl
  rwa [hS₁T] at h

theorem isInv_inf_fixed {Λ B : Subgroup Γ} (hΛB : ∀ l ∈ Λ, ∀ b ∈ B, l * b = b * l)
    {Y : Subgroup Q} (hY : XMod.IsInv ↥Λ Y) : XMod.IsInv ↥Λ (Y ⊓ XMod.fixed ↥B ⊤) := by
  intro l s hs
  refine ⟨hY l s hs.1, trivial, fun b => ?_⟩
  change (b : Γ) • (l : Γ) • s = (l : Γ) • s
  have h1 : (b : Γ) • s = s := hs.2.2 b
  rw [smul_smul, ← hΛB l l.2 b b.2, mul_smul, h1]

theorem exists_rk_inf_fixed_eq_mul [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) {Λ B : Subgroup Γ}
    (hΛB : ∀ l ∈ Λ, ∀ b ∈ B, l * b = b * l) {I Y : Subgroup Q} (hI : XMod.IsIrr ↥Λ I) {k : ℕ}
    (hY : IsotypicOfLength ↥Λ Y I k) :
    ∃ c : ℕ, c ≤ k ∧ rk ↥(Y ⊓ XMod.fixed ↥B ⊤) = c * rk ↥I := by
  obtain ⟨c, hc⟩ := exists_rk_eq_mul hQ hI (isInv_inf_fixed hΛB hY.1)
    (inf_le_left.trans hY.2.1)
  refine ⟨c, ?_, hc⟩
  have hrkI : 0 < rk ↥I := by
    rcases Nat.eq_zero_or_pos (rk ↥I) with h | h
    · exact absurd ((rk_eq_zero_iff hQ).1 h) hI.2.1.ne'
    · exact h
  have h1 : rk ↥(Y ⊓ XMod.fixed ↥B ⊤) ≤ rk ↥Y := rk_mono inf_le_left
  rw [hc, hY.2.2] at h1
  exact le_of_mul_le_mul_right h1 hrkI

theorem rk_le_of_socle_two [Finite Γ] [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1) {Λ B : Subgroup Γ}
    (hΛB : ∀ l ∈ Λ, ∀ b ∈ B, l * b = b * l) (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hB2 : ∀ b ∈ B, b ^ 2 = 1) {I₁ I₂ Y₁ Y₂ : Subgroup Q} (hI₁ : XMod.IsIrr ↥Λ I₁)
    (hI₂ : XMod.IsIrr ↥Λ I₂) {k₁ k₂ c₁ c₂ e₁ e₂ : ℕ} (hY₁ : IsotypicOfLength ↥Λ Y₁ I₁ k₁)
    (hY₂ : IsotypicOfLength ↥Λ Y₂ I₂ k₂) (hY₁B : ∀ b ∈ B, ∀ y ∈ Y₁, b • y ∈ Y₁)
    (hY₂B : ∀ b ∈ B, ∀ y ∈ Y₂, b • y ∈ Y₂) (hc₁ : rk ↥(Y₁ ⊓ XMod.fixed ↥B ⊤) = c₁ * rk ↥I₁)
    (hc₂ : rk ↥(Y₂ ⊓ XMod.fixed ↥B ⊤) = c₂ * rk ↥I₂)
    (he₁ : Nat.card {θ : ↥I₁ →* ↥I₁ // IsEqv Λ (I₁.subtype.comp θ)} ≤ 2 ^ e₁)
    (he₂ : Nat.card {θ : ↥I₂ →* ↥I₂ // IsEqv Λ (I₂.subtype.comp θ)} ≤ 2 ^ e₂) :
    rk ↥B ≤ e₁ * c₁ * (k₁ - c₁) + e₂ * c₂ * (k₂ - c₂) +
      rk ↥(B ⊓ fixingSubgroup Γ (Y₁ : Set Q) ⊓ fixingSubgroup Γ (Y₂ : Set Q)) := by
  have h1 := rk_le_of_socle hQ hΛB hBc hB2 hI₁ hY₁ hY₁B hc₁ he₁
  have h2 := rk_le_of_socle hQ hΛB hBc hB2 hI₂ hY₂ hY₂B hc₂ he₂
  set X₁ := B ⊓ fixingSubgroup Γ (Y₁ : Set Q) with hX₁
  set X₂ := B ⊓ fixingSubgroup Γ (Y₂ : Set Q) with hX₂
  have hX : X₁ ⊓ X₂ = B ⊓ fixingSubgroup Γ (Y₁ : Set Q) ⊓ fixingSubgroup Γ (Y₂ : Set Q) := by
    rw [hX₁, hX₂, inf_assoc, inf_assoc, inf_left_comm (fixingSubgroup Γ (Y₁ : Set Q)) B,
      ← inf_assoc B B, inf_idem]
  have hidx := Subgroup.relIndex_inf_le (H := X₁) (K := X₂) (L := B)
  have hc1 := Subgroup.relIndex_mul_card X₁ B
  have hc2 := Subgroup.relIndex_mul_card X₂ B
  have hc3 := Subgroup.relIndex_mul_card (X₁ ⊓ X₂) B
  rw [inf_eq_left.2 (inf_le_left : X₁ ≤ B)] at hc1
  rw [inf_eq_left.2 (inf_le_left : X₂ ≤ B)] at hc2
  rw [inf_eq_left.2 (inf_le_left.trans inf_le_left : X₁ ⊓ X₂ ≤ B)] at hc3
  have hBpos : 0 < Nat.card ↥B := Nat.card_pos
  have hi1 : 0 < X₁.relIndex B := Nat.pos_of_ne_zero fun h => by
    rw [h, zero_mul] at hc1; omega
  have hi2 : 0 < X₂.relIndex B := Nat.pos_of_ne_zero fun h => by
    rw [h, zero_mul] at hc2; omega
  have hkey : Nat.card ↥X₁ * Nat.card ↥X₂ ≤ Nat.card ↥B * Nat.card ↥(X₁ ⊓ X₂) := by
    have h3 : X₁.relIndex B * X₂.relIndex B * (Nat.card ↥X₁ * Nat.card ↥X₂) ≤
        X₁.relIndex B * X₂.relIndex B * (Nat.card ↥B * Nat.card ↥(X₁ ⊓ X₂)) := by
      calc X₁.relIndex B * X₂.relIndex B * (Nat.card ↥X₁ * Nat.card ↥X₂)
          = (X₁.relIndex B * Nat.card ↥X₁) * (X₂.relIndex B * Nat.card ↥X₂) := by ring
        _ = Nat.card ↥B * ((X₁ ⊓ X₂).relIndex B * Nat.card ↥(X₁ ⊓ X₂)) := by
          rw [hc1, hc2, hc3]
        _ ≤ Nat.card ↥B * (X₁.relIndex B * X₂.relIndex B * Nat.card ↥(X₁ ⊓ X₂)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hidx)
        _ = X₁.relIndex B * X₂.relIndex B * (Nat.card ↥B * Nat.card ↥(X₁ ⊓ X₂)) := by ring
    exact Nat.le_of_mul_le_mul_left h3 (Nat.mul_pos hi1 hi2)
  have hrk : rk ↥X₁ + rk ↥X₂ ≤ rk ↥B + rk ↥(X₁ ⊓ X₂) := by
    have hBp : IsPGroup 2 ↥B := fun b => ⟨1, Subtype.ext (by simpa using hB2 b b.2)⟩
    have hX₁p : IsPGroup 2 ↥X₁ := hBp.to_le inf_le_left
    have hX₂p : IsPGroup 2 ↥X₂ := hBp.to_le inf_le_left
    have hX₃p : IsPGroup 2 ↥(X₁ ⊓ X₂) := hBp.to_le (inf_le_left.trans inf_le_left)
    rw [card_eq_two_pow_of_isPGroup hX₁p, card_eq_two_pow_of_isPGroup hX₂p,
      card_eq_two_pow_of_isPGroup hBp, card_eq_two_pow_of_isPGroup hX₃p, ← pow_add,
      ← pow_add] at hkey
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hkey
  rw [← hX]
  omega

end Socle

theorem isoSum_le_isoComp {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q]
    [MulDistribMulAction Γ Q] {Λ : Subgroup Γ} (hΛ : ∀ g : Γ, ∀ l ∈ Λ, g * l * g⁻¹ ∈ Λ)
    {V : Subgroup Q} (hV : XMod.IsIrr ↥Λ V) : isoSum Λ V ≤ isoComp ↥Λ V :=
  iSup₂_le fun g hg => le_isoComp (isIrr_smul (normalizes_whole Λ hΛ) g hV) hg

end CFSG.Quasithin.SmithD39Two
