module

public import CFSG.RankThree.GroupTheory.SteinbergBMRelativeMinimalFrattini
public import CFSG.RankThree.GroupTheory.SteinbergCDBinaryPrimeActionDegree
public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartOne.Extract

open Subgroup CFSG CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement IsMulCommutative

section Bridge

variable {H : Type*} [Group H]

theorem map_actionCommutator_normalizes {K X : Subgroup H} (hXK : X ≤ normalizer (K : Set H))
    (K' : Subgroup K) :
    letI : MulDistribMulAction X K := conjMulDistribMulActionOfLeNormalizer X K hXK
    (actionCommutator X K').map K.subtype = ⁅K'.map K.subtype, X⁆ := by
  let : MulDistribMulAction X K := conjMulDistribMulActionOfLeNormalizer X K hXK
  have hsmul : ∀ (x : X) (k : K), ((x • k : K) : H) = x * k * (x : H)⁻¹ := fun _ _ => rfl
  unfold actionCommutator
  rw [MonoidHom.map_closure, Subgroup.commutator_def]
  refine le_antisymm ((closure_le _).2 ?_) ((closure_le _).2 ?_)
  · rintro _ ⟨_, ⟨k, hk, x, rfl⟩, rfl⟩
    have e : K.subtype (k⁻¹ * (x • k)) = ⁅(k : H)⁻¹, (x : H)⁆ := by
      rw [map_mul, map_inv, coe_subtype, hsmul, commutatorElement_def, inv_inv]
      group
    rw [e]
    exact subset_closure ⟨_, (K'.map K.subtype).inv_mem (mem_map_of_mem K.subtype hk), x, x.2,
      rfl⟩
  · rintro _ ⟨_, ⟨k, hk, rfl⟩, x, hx, rfl⟩
    have hmem : k⁻¹⁻¹ * ((⟨x, hx⟩ : X) • k⁻¹) ∈
        {y : K | ∃ h ∈ K', ∃ a : X, y = h⁻¹ * (a • h)} := ⟨k⁻¹, K'.inv_mem hk, ⟨x, hx⟩, rfl⟩
    refine subset_closure ⟨_, hmem, ?_⟩
    rw [map_mul, map_inv, coe_subtype, hsmul, commutatorElement_def]
    simp only [inv_inv, coe_inv]
    group

end Bridge

section Representation

@[expose] noncomputable def actionGL (n : ℕ) [Fact n.Prime] (A : Type*) [Group A] (G : Type*)
    [Group G] [IsElementaryAbelian n G] [MulDistribMulAction A G] :
    A →* LinearMap.GeneralLinearGroup (ZMod n) (Additive G) where
  toFun a := LinearMap.GeneralLinearGroup.ofLinearEquiv
    ((MulEquiv.toAdditive (MulDistribMulAction.toMulAut A G a)).toLinearEquiv
      (fun c x => ZMod.map_smul
        (MulEquiv.toAdditive (MulDistribMulAction.toMulAut A G a)).toAddMonoidHom c x))
  map_one' := by
    apply Units.ext
    ext x
    apply Additive.toMul.injective
    simp
  map_mul' a b := by
    apply Units.ext
    ext x
    apply Additive.toMul.injective
    simp [mul_smul]

theorem actionGL_apply (n : ℕ) [Fact n.Prime] (A : Type*) [Group A] (G : Type*)
    [Group G] [IsElementaryAbelian n G] [MulDistribMulAction A G] (a : A) (x : Additive G) :
    ((actionGL n A G a : LinearMap.GeneralLinearGroup (ZMod n) (Additive G)) :
      Additive G →ₗ[ZMod n] Additive G) x = Additive.ofMul (a • Additive.toMul x) := rfl

end Representation

section Main

variable {H : Type} [Group H] [Finite H]

theorem card_inf_centralizer_eq {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {A R J : Subgroup H}
    [J.Normal] [IsElementaryAbelian p A] (hA : Nat.card A = p ^ 3)
    (hAR : A ≤ normalizer (R : Set H)) (hR2 : IsPGroup 2 R) (hRc : ⁅R, A⁆ = R) (hRJ : ¬ R ≤ J)
    (hmin : ∀ U : Subgroup H, U < R → A ≤ normalizer (U : Set H) → ⁅U, A⁆ = U → U ≤ J) :
    Nat.card (A ⊓ centralizer (R : Set H) : Subgroup H) = p ^ 2 := by
  have hp : p.Prime := Fact.out
  let : MulDistribMulAction A R := conjMulDistribMulActionOfLeNormalizer A R hAR
  have hsmul : ∀ (a : A) (x : R), ((a • x : R) : H) = a * x * (a : H)⁻¹ := fun _ _ => rfl
  have hRnt : Nontrivial R := (nontrivial_iff_ne_bot R).mpr fun h => hRJ (h ▸ bot_le)
  have hAodd : ¬ 2 ∣ Nat.card A := by
    rw [hA]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
      (Nat.prime_two.dvd_of_dvd_pow h)).symm
  set K : Subgroup R := J.subgroupOf R with hK
  have hKP : K < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => hRJ fun r hr => ?_
    have : (⟨r, hr⟩ : R) ∈ K := h ▸ mem_top _
    exact this
  have hKinv : ∀ a : A, ∀ x ∈ K, a • x ∈ K := by
    intro a x hx
    show ((a • x : R) : H) ∈ J
    rw [hsmul]
    have hxJ : (x : H) ∈ J := hx
    exact Normal.conj_mem (inferInstance : J.Normal) _ hxJ (a : H)
  have hmapTop : (⊤ : Subgroup R).map R.subtype = R := by
    rw [← MonoidHom.range_eq_map, range_subtype]
  have hPA : actionCommutator A (⊤ : Subgroup R) = ⊤ := by
    apply map_injective R.subtype_injective
    have := map_actionCommutator_normalizes hAR (⊤ : Subgroup R)
    rw [this, hmapTop, hRc]
  have hU : ∀ U : Subgroup R, U < ⊤ → (∀ a : A, ∀ x ∈ U, a • x ∈ U) →
      actionCommutator A U = U → U ≤ K := by
    intro U hUt hUinv hUc
    set U₁ := U.map R.subtype with hU₁
    have hU₁R : U₁ < R := by
      refine lt_of_le_of_ne (map_subtype_le U) fun h => hUt.ne ?_
      apply map_injective R.subtype_injective
      rw [hmapTop]
      exact h
    have hAU₁ : A ≤ normalizer (U₁ : Set H) := by
      rw [le_normalizer_iff]
      rintro a ha _ ⟨x, hx, rfl⟩
      exact ⟨(⟨a, ha⟩ : A) • x, hUinv ⟨a, ha⟩ x hx, hsmul ⟨a, ha⟩ x⟩
    have hU₁c : ⁅U₁, A⁆ = U₁ := by
      have := map_actionCommutator_normalizes hAR U
      rw [← this, hUc]
    have hU₁J := hmin U₁ hU₁R hAU₁ hU₁c
    intro x hx
    exact hU₁J (mem_map_of_mem R.subtype hx)
  obtain ⟨hnt', hirr', -, -⟩ :=
    CFSG.RankThree.GroupTheory.SteinbergBM.relative_minimal_action_frattini_irreducibility
      (A := A) (l := 2) Nat.prime_two hR2 hAodd K hKP hKinv hPA hU
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 R) := ⟨hR2⟩
  have hEl : IsElementaryAbelian 2 (R ⧸ frattini R) :=
    isElementaryAbelian_quotient_frattini (p := 2) (R := R)
  let actB : MulDistribMulAction A (R ⧸ frattini R) :=
    quotientMulDistribMulAction (A := A) (G := R) (frattini R)
      (isInvariant_of_characteristic (A := A) (G := R) (frattini R))
  have hnt : ∃ a : A, ∃ v : R ⧸ frattini R, a • v ≠ v := hnt'
  have hirr : ∀ W : Subgroup (R ⧸ frattini R), (∀ a : A, ∀ v ∈ W, a • v ∈ W) →
      W = ⊥ ∨ W = ⊤ := hirr'
  let ρ := actionGL 2 A (R ⧸ frattini R)
  have hirrV : ∀ W : Submodule (ZMod 2) (Additive (R ⧸ frattini R)),
      (∀ a : A, ∀ v ∈ W, (ρ a : Additive (R ⧸ frattini R) →ₗ[ZMod 2]
        Additive (R ⧸ frattini R)) v ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    let W₀ : Subgroup (R ⧸ frattini R) :=
      { carrier := {x | Additive.ofMul x ∈ W}
        mul_mem' := fun {x y} hx hy => W.add_mem hx hy
        one_mem' := W.zero_mem
        inv_mem' := fun {x} hx => W.neg_mem hx }
    have hW₀ : ∀ a : A, ∀ v ∈ W₀, a • v ∈ W₀ := fun a v hv => hW a (Additive.ofMul v) hv
    rcases hirr W₀ hW₀ with h | h
    · left
      rw [Submodule.eq_bot_iff]
      intro v hv
      have hv' : Additive.toMul v ∈ W₀ := hv
      rw [h, mem_bot] at hv'
      exact Additive.toMul.injective hv'
    · right
      rw [Submodule.eq_top_iff']
      intro v
      have hv' : Additive.toMul v ∈ W₀ := by
        rw [h]
        exact mem_top _
      exact hv'
  obtain ⟨a₀, v₀, hav⟩ := hnt
  have : Nontrivial (Additive (R ⧸ frattini R)) :=
    ⟨⟨Additive.ofMul (a₀ • v₀), Additive.ofMul v₀, fun h => hav (Additive.ofMul.injective h)⟩⟩
  have : Finite (Additive (R ⧸ frattini R)) := inferInstanceAs (Finite (R ⧸ frattini R))
  have : FiniteDimensional (ZMod 2) (Additive (R ⧸ frattini R)) := Module.Finite.of_finite
  have hρnt : ρ.range ≠ ⊥ := by
    intro h
    have h0 : ρ a₀ ∈ ρ.range := ⟨a₀, rfl⟩
    rw [h, mem_bot] at h0
    apply hav
    have h1 := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2)
      (Additive (R ⧸ frattini R)) => (g : Additive (R ⧸ frattini R) →ₗ[ZMod 2]
        Additive (R ⧸ frattini R)) (Additive.ofMul v₀)) h0
    exact Additive.ofMul.injective h1
  have hbin := CFSG.RankThree.GroupTheory.binary_irreducible_prime_action_degree hp (A := A)
    ρ hirrV hρnt
  have hcardρ : Nat.card ρ.range = p := hbin.2.1
  have hforward : ∀ a : A, ρ a = 1 → ∀ x : R, a • x = x := by
    intro a ha x
    set σ := MulDistribMulAction.toMulAut A R a with hσ
    have hkerK := CFSG.GroupTheory.frattini_automorphism_kernel (p := 2) hR2
    have hσker : σ ∈ (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism
        (frattini R)).ker := by
      rw [MonoidHom.mem_ker]
      ext y
      induction y using QuotientGroup.induction_on with
      | H x =>
        rw [hkerK.1 σ x, MulAut.one_apply]
        have h1 := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2)
          (Additive (R ⧸ frattini R)) => (g : Additive (R ⧸ frattini R) →ₗ[ZMod 2]
            Additive (R ⧸ frattini R)) (Additive.ofMul (x : R ⧸ frattini R))) ha
        exact Additive.ofMul.injective h1
    obtain ⟨k, hk⟩ := hkerK.2 ⟨σ, hσker⟩
    have hσk : σ ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hσo : σ ^ orderOf a = 1 := by
      rw [hσ, ← map_pow, pow_orderOf_eq_one, map_one]
    have hcopk : Nat.Coprime (2 ^ k) (orderOf a) :=
      Nat.Coprime.pow_left k (Nat.Coprime.coprime_dvd_right (orderOf_dvd_natCard a)
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hAodd))
    have hσ1 : σ = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcopk
      (orderOf_dvd_of_pow_eq_one hσk) (orderOf_dvd_of_pow_eq_one hσo))
    exact congrArg (fun τ : MulAut R => τ x) hσ1
  have hker : ρ.ker = (A ⊓ centralizer (R : Set H)).subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, mem_subgroupOf, mem_inf]
    constructor
    · intro h1
      refine ⟨a.2, mem_centralizer_iff.mpr fun r hr => ?_⟩
      have h := congrArg Subtype.val (hforward a h1 ⟨r, hr⟩)
      rw [hsmul] at h
      have h' : (a : H) * r * (a : H)⁻¹ = r := h
      calc r * (a : H) = ((a : H) * r * (a : H)⁻¹) * a := by rw [h']
        _ = a * r := by group
    · rintro ⟨-, hc⟩
      apply Units.ext
      refine LinearMap.ext fun v => ?_
      obtain ⟨y, rfl⟩ := Additive.ofMul.surjective v
      induction y using QuotientGroup.induction_on with
      | H x =>
        have hx : (a • x : R) = x := by
          apply Subtype.ext
          rw [hsmul]
          have := mem_centralizer_iff.mp hc (x : H) x.2
          calc (a : H) * x * (a : H)⁻¹ = (x * a) * (a : H)⁻¹ := by rw [← this]
            _ = x := by group
        exact congrArg Additive.ofMul (congrArg (QuotientGroup.mk (s := frattini R)) hx)
  have hcard := card_ker_mul_card_range ρ
  rw [hker, hcardρ, hA, Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : A ⊓ _ ≤ A)).toEquiv]
    at hcard
  have h3 : p ^ 3 = p ^ 2 * p := by ring
  rw [h3] at hcard
  exact Nat.eq_of_mul_eq_mul_right hp.pos hcard

end Main

end CFSG.RankThree.PartOne.Extract
