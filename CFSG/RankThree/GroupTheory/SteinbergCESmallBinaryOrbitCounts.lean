module

public import CFSG.RankThree.GroupTheory.SteinbergCEPrimeDimScalarCentralizer
public import Mathlib.Algebra.Group.Equiv.Finite
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Mathlib.Topology.Sheaves.Presheaf
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.RankThree.GroupTheory

open CFSG.RankThree.LocalRank

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section FixedSpace

variable {A : Type*} [CommGroup A] [Module (ZMod 2) (Additive A)]
  {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem eigenspace_one_eq_iSup_signWeightSpace [Fintype A]
    [Fintype (Module.Dual (ZMod 2) (Additive A))] (hK : (2 : K) ≠ 0) (ρ : Representation K A V)
    (a : A) :
    Module.End.eigenspace (ρ a) 1 =
      ⨆ χ : Module.Dual (ZMod 2) (Additive A),
        if χ (Additive.ofMul a) = 0 then signWeightSpace ρ χ else ⊥ := by
  set P := ⨆ χ : Module.Dual (ZMod 2) (Additive A),
    if χ (Additive.ofMul a) = 0 then signWeightSpace ρ χ else ⊥
  set M := ⨆ χ : Module.Dual (ZMod 2) (Additive A),
    if χ (Additive.ofMul a) = 0 then ⊥ else signWeightSpace ρ χ
  have hP : P ≤ Module.End.eigenspace (ρ a) 1 := by
    refine iSup_le fun χ => ?_
    split_ifs with h
    · intro v hv
      rw [Module.End.mem_eigenspace_iff, (mem_signWeightSpace ρ χ v).mp hv a, h, ZMod.val_zero,
        pow_zero]
    · exact bot_le
  have hM : M ≤ Module.End.eigenspace (ρ a) (-1) := by
    refine iSup_le fun χ => ?_
    split_ifs with h
    · exact bot_le
    · intro v hv
      have h1 : ZMod.val (1 : ZMod 2) = 1 := rfl
      rw [Module.End.mem_eigenspace_iff, (mem_signWeightSpace ρ χ v).mp hv a,
        dual_apply_eq_one h, h1, pow_one]
  have htop : P ⊔ M = ⊤ := by
    rw [eq_top_iff, ← iSup_signWeightSpace_eq_top ρ hK]
    refine iSup_le fun χ => ?_
    by_cases h : χ (Additive.ofMul a) = 0
    · refine le_sup_of_le_left (le_iSup_of_le χ ?_)
      simp only [h, ↓reduceIte, le_refl]
    · refine le_sup_of_le_right (le_iSup_of_le χ ?_)
      simp only [h, ↓reduceIte, le_refl]
  refine le_antisymm (fun v hv => ?_) hP
  have hv' : v ∈ P ⊔ M := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hv'
  have h1 : z ∈ Module.End.eigenspace (ρ a) 1 := by
    have h := Submodule.sub_mem _ hv (hP hy)
    rwa [add_sub_cancel_left] at h
  have h2 := hM hz
  rw [Module.End.mem_eigenspace_iff] at h1 h2
  have hz0 : z = 0 := by
    rw [h1, one_smul, neg_one_smul] at h2
    have h3 : (2 : K) • z = 0 := by
      rw [two_smul]
      nth_rewrite 1 [h2]
      exact neg_add_cancel z
    exact (smul_eq_zero.mp h3).resolve_left hK
  rw [hz0, add_zero]
  exact hy

theorem finrank_eigenspace_one_eq_sum [Fintype A] [Fintype (Module.Dual (ZMod 2) (Additive A))]
    [FiniteDimensional K V] (hK : (2 : K) ≠ 0) (ρ : Representation K A V) (a : A) :
    Module.finrank K (Module.End.eigenspace (ρ a) 1) =
      ∑ χ : Module.Dual (ZMod 2) (Additive A),
        if χ (Additive.ofMul a) = 0 then Module.finrank K (signWeightSpace ρ χ) else 0 := by
  have hind : iSupIndep fun χ : Module.Dual (ZMod 2) (Additive A) =>
      if χ (Additive.ofMul a) = 0 then signWeightSpace ρ χ else ⊥ :=
    (iSupIndep_signWeightSpace ρ hK).mono fun χ => by
      split_ifs
      · exact le_rfl
      · exact bot_le
  rw [eigenspace_one_eq_iSup_signWeightSpace hK ρ a, finrank_iSup_eq_sum_of_iSupIndep hind]
  refine Finset.sum_congr rfl fun χ _ => ?_
  by_cases h : χ (Additive.ofMul a) = 0
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h, finrank_bot]

theorem two_mul_card_filter_dual_eq_zero [Fintype (Module.Dual (ZMod 2) (Additive A))]
    {x : Additive A} (hx : x ≠ 0) :
    2 * (Finset.univ.filter fun χ : Module.Dual (ZMod 2) (Additive A) => χ x = 0).card =
      Fintype.card (Module.Dual (ZMod 2) (Additive A)) := by
  obtain ⟨χ₁, hχ₁⟩ := exists_dual_apply_eq_one hx
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (fun χ : Module.Dual (ZMod 2) (Additive A) => χ x = 0)
  have hbij : (Finset.univ.filter fun χ : Module.Dual (ZMod 2) (Additive A) => χ x = 0).card =
      (Finset.univ.filter fun χ : Module.Dual (ZMod 2) (Additive A) => ¬ χ x = 0).card := by
    refine Finset.card_equiv (dualTranslate χ₁) fun χ => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change χ x = 0 ↔ ¬ (χ₁ + χ) x = 0
    rw [LinearMap.add_apply, hχ₁]
    generalize χ x = y
    revert y
    decide
  rw [Finset.card_univ] at h
  omega

omit [Module (ZMod 2) (Additive A)] in
theorem natCard_dual_eq [Finite A] [Module (ZMod 2) (Additive A)] :
    Nat.card (Module.Dual (ZMod 2) (Additive A)) = Nat.card A := by
  have : Module.Finite (ZMod 2) (Additive A) := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Subspace.dual_finrank_eq,
    ← Module.natCard_eq_pow_finrank, Nat.card_congr Additive.toMul]

end FixedSpace


section Irreducible

variable {S : Type*} [CommGroup S] [Finite S] [Module (ZMod 2) (Additive S)] {A : Type*}
  [Group A] {φ : A →* MulAut S}

theorem eq_zero_of_dualAct_eq_self
    (hirr : ∀ U : Subgroup S, (∀ a : A, ∀ x ∈ U, φ a x ∈ U) → U = ⊥ ∨ U = ⊤)
    (hcomm : ∀ a b : A, φ a * φ b = φ b * φ a) {b : A} (hb : φ b ≠ 1)
    {χ : Module.Dual (ZMod 2) (Additive S)} (hχ : dualAct (φ b) χ = χ) : χ = 0 := by
  have : Finite (Module.Dual (ZMod 2) (Additive S)) :=
    Finite.of_injective (fun f : Module.Dual (ZMod 2) (Additive S) => (f : Additive S → ZMod 2))
      DFunLike.coe_injective
  have : FiniteDimensional (ZMod 2) (Module.Dual (ZMod 2) (Additive S)) := Module.Finite.of_finite
  set D : Submodule (ZMod 2) (Module.Dual (ZMod 2) (Additive S)) :=
    LinearMap.ker (dualAct (φ b) - LinearMap.id)
  have hmemD : ∀ ψ, ψ ∈ D ↔ dualAct (φ b) ψ = ψ := fun ψ => by
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  have hDinv : ∀ a : A, ∀ ψ ∈ D, dualAct (φ a) ψ ∈ D := by
    intro a ψ hψ
    rw [hmemD] at hψ ⊢
    rw [← dualAct_mul, hcomm b a, dualAct_mul, hψ]
  let U : Subgroup S :=
    { carrier := {s | ∀ ψ ∈ D, ψ (Additive.ofMul s) = 0}
      mul_mem' := fun {s t} hs ht ψ hψ => by
        rw [ofMul_mul, map_add, hs ψ hψ, ht ψ hψ, add_zero]
      one_mem' := fun ψ _ => by rw [ofMul_one, map_zero]
      inv_mem' := fun {s} hs ψ hψ => by rw [ofMul_inv, map_neg, hs ψ hψ, neg_zero] }
  have hU : ∀ a : A, ∀ s ∈ U, φ a s ∈ U := by
    intro a s hs ψ hψ
    have h := hs _ (hDinv a⁻¹ ψ hψ)
    rwa [dualAct_ofMul, map_inv, inv_inv] at h
  rcases hirr U hU with h | h
  ·
    exfalso
    apply hb
    have hco : D.dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Submodule.mem_dualCoannihilator] at hx
      have hxU : Additive.toMul x ∈ U := fun ψ hψ => by
        rw [ofMul_toMul]
        exact hx ψ hψ
      rw [h, Subgroup.mem_bot] at hxU
      rw [Submodule.mem_bot, ← ofMul_toMul x, hxU, ofMul_one]
    have hD : D = ⊤ := by
      have h1 := Subspace.dualCoannihilator_dualAnnihilator_eq (W := D)
      rw [hco, Submodule.dualAnnihilator_bot] at h1
      exact h1.symm
    ext s
    have h2 : ∀ ψ : Module.Dual (ZMod 2) (Additive S),
        ψ (Additive.ofMul ((φ b)⁻¹ s) - Additive.ofMul s) = 0 := fun ψ => by
      have h3 : ψ ∈ D := by
        rw [hD]
        exact Submodule.mem_top
      rw [hmemD] at h3
      rw [map_sub, ← dualAct_ofMul, h3, sub_self]
    have h4 := (Module.forall_dual_apply_eq_zero_iff (ZMod 2) _).mp h2
    rw [sub_eq_zero] at h4
    have h5 : (φ b)⁻¹ s = s := Additive.ofMul.injective h4
    calc (φ b) s = (φ b) ((φ b)⁻¹ s) := by rw [h5]
      _ = s := MulAut.apply_inv_self S _ s
      _ = (1 : MulAut S) s := rfl
  ·
    apply LinearMap.ext
    intro x
    have hxU : Additive.toMul x ∈ U := by
      rw [h]
      exact Subgroup.mem_top _
    have h1 := hxU χ ((hmemD χ).mpr hχ)
    rwa [ofMul_toMul] at h1

end Irreducible

section Orbit

variable {S : Type*} [CommGroup S] [Module (ZMod 2) (Additive S)] {A : Type*} [Group A]
  {φ : A →* MulAut S} {k : Type*} [Field k] {W : Type*} [AddCommGroup W] [Module k W]

theorem signWeightSpace_eq_bot_of_forall_dualAct_ne [Fintype S]
    [Fintype (Module.Dual (ZMod 2) (Additive S))] (hk : (2 : k) ≠ 0)
    (ρ : Representation k (S ⋊[φ] A) W) (hρ : ρ.IsIrreducible)
    {χ₀ : Module.Dual (ZMod 2) (Additive S)}
    (hχ₀ : signWeightSpace (ρ.comp SemidirectProduct.inl) χ₀ ≠ ⊥)
    {ψ : Module.Dual (ZMod 2) (Additive S)} (hψ : ∀ a, dualAct (φ a) χ₀ ≠ ψ) :
    signWeightSpace (ρ.comp SemidirectProduct.inl) ψ = ⊥ := by
  set ρS := ρ.comp SemidirectProduct.inl
  set M := ⨆ a : A, signWeightSpace ρS (dualAct (φ a) χ₀)
  have hmemM : ∀ f : Module.End k W,
      (∀ a, ∀ v ∈ signWeightSpace ρS (dualAct (φ a) χ₀), f v ∈ M) → ∀ v ∈ M, f v ∈ M := by
    intro f hf v hv
    refine Submodule.iSup_induction _ (motive := fun w => f w ∈ M) hv (fun a w hw => hf a w hw)
      (by rw [map_zero]; exact M.zero_mem) fun x y hx hy => by
        rw [map_add]
        exact M.add_mem hx hy
  have hinv : ∀ x, ∀ v ∈ M, ρ x v ∈ M := by
    refine semidirect_rep_mem (fun s => hmemM _ fun a v hv => ?_)
      fun b => hmemM _ fun a v hv => ?_
    · exact Submodule.mem_iSup_of_mem a (rep_inl_mem_signWeightSpace ρ s hv)
    · have h := rep_inr_mem_signWeightSpace ρ b hv
      rw [← dualAct_mul, ← map_mul] at h
      exact Submodule.mem_iSup_of_mem (b * a) h
  have hM : M = ⊤ := by
    rcases eq_bot_or_eq_top_of_isIrreducible hρ M hinv with h | h
    · exfalso
      apply hχ₀
      rw [eq_bot_iff, ← h]
      have h1 : signWeightSpace ρS (dualAct (φ 1) χ₀) ≤ M :=
        le_iSup (fun a => signWeightSpace ρS (dualAct (φ a) χ₀)) 1
      rwa [map_one, dualAct_one] at h1
    · exact h
  have hle : signWeightSpace ρS ψ ≤ ⨆ (j) (_ : j ≠ ψ), signWeightSpace ρS j := by
    calc signWeightSpace ρS ψ ≤ M := by
          rw [hM]
          exact le_top
      _ ≤ _ := iSup_le fun a => le_iSup₂_of_le (dualAct (φ a) χ₀) (hψ a) le_rfl
  exact ((iSupIndep_signWeightSpace ρS hk) ψ).eq_bot_of_le hle

end Orbit

@[expose] def zeroCountFive (w : Fin 5 → ZMod 2) : ℕ := (Finset.univ.filter fun i => w i = 0).card

theorem card_filter_sum_eq_zero_fin_five :
    (Finset.univ.filter fun w : Fin 5 → ZMod 2 => ∑ i, w i = 0).card = 16 := by
  decide

theorem zeroCountFive_eq_three_or_one :
    ∀ w : Fin 5 → ZMod 2, ∑ i, w i = 0 → w ≠ 0 → zeroCountFive w = 3 ∨ zeroCountFive w = 1 := by
  unfold zeroCountFive
  decide

theorem sum_eq_zero_of_zeroCountFive_eq_three :
    ∀ w : Fin 5 → ZMod 2, zeroCountFive w = 3 → ∑ i, w i = 0 := by
  unfold zeroCountFive
  decide

theorem sum_eq_zero_of_zeroCountFive_eq_one :
    ∀ w : Fin 5 → ZMod 2, zeroCountFive w = 1 → ∑ i, w i = 0 := by
  unfold zeroCountFive
  decide

theorem ncard_zeroCountFive_eq_three : {w : Fin 5 → ZMod 2 | zeroCountFive w = 3}.ncard = 10 := by
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
  unfold zeroCountFive
  decide

theorem ncard_zeroCountFive_eq_one : {w : Fin 5 → ZMod 2 | zeroCountFive w = 1}.ncard = 5 := by
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
  unfold zeroCountFive
  decide

theorem zeroCountFive_zero : zeroCountFive 0 = 5 := by
  unfold zeroCountFive
  decide

theorem small_binary_prime_orbit_fixed_space_counts {p d : ℕ}
    (hpd : (p = 7 ∧ d = 3) ∨ (p = 5 ∧ d = 4)) {S : Type*} [CommGroup S] [Finite S]
    [Module (ZMod 2) (Additive S)] (hS : Nat.card S = 2 ^ d) {A : Type*} [Group A]
    {φ : A →* MulAut S} (hφ : Nat.card φ.range = p)
    (hirr : ∀ U : Subgroup S, (∀ a : A, ∀ x ∈ U, φ a x ∈ U) → U = ⊥ ∨ U = ⊤)
    {k : Type*} [Field k] (hk : (2 : k) ≠ 0) {W : Type*} [AddCommGroup W] [Module k W]
    [FiniteDimensional k W] (ρ : Representation k (S ⋊[φ] A) W) (hρ : ρ.IsIrreducible)
    (hinj : Function.Injective (ρ.comp SemidirectProduct.inl)) :
    (∃ χ₀ : Module.Dual (ZMod 2) (Additive S), χ₀ ≠ 0 ∧
      {χ | signWeightSpace (ρ.comp SemidirectProduct.inl) χ ≠ ⊥} =
        Set.range fun a : A => dualAct (φ a) χ₀) ∧
    Set.ncard {χ | signWeightSpace (ρ.comp SemidirectProduct.inl) χ ≠ ⊥} = p ∧
    ∃ e : ℕ, 1 ≤ e ∧
      (∀ χ, signWeightSpace (ρ.comp SemidirectProduct.inl) χ ≠ ⊥ →
        Module.finrank k (signWeightSpace (ρ.comp SemidirectProduct.inl) χ) = e) ∧
      Module.finrank k W = p * e ∧
      (p = 7 → ∀ s : S, s ≠ 1 →
        Module.finrank k (Module.End.eigenspace (ρ (SemidirectProduct.inl s)) 1) = 3 * e) ∧
      (p = 5 →
        Set.ncard {s : S | s ≠ 1 ∧
          Module.finrank k (Module.End.eigenspace (ρ (SemidirectProduct.inl s)) 1) = 3 * e} =
          10 ∧
        Set.ncard {s : S | s ≠ 1 ∧
          Module.finrank k (Module.End.eigenspace (ρ (SemidirectProduct.inl s)) 1) = e} = 5 ∧
        ∀ s : S, s ≠ 1 →
          Module.finrank k (Module.End.eigenspace (ρ (SemidirectProduct.inl s)) 1) = 3 * e ∨
          Module.finrank k (Module.End.eigenspace (ρ (SemidirectProduct.inl s)) 1) = e) ∧
      ((∀ s : S, s ≠ 1 →
          Module.finrank k (Module.End.eigenspace (ρ (SemidirectProduct.inl s)) 1) ≤ 4) →
        e = 1 ∧ Module.finrank k W = p) := by
  classical
  have hp : p.Prime := by
    rcases hpd with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num
  have : Fact p.Prime := ⟨hp⟩
  let := Fintype.ofFinite S
  have : Finite (Module.Dual (ZMod 2) (Additive S)) :=
    Finite.of_injective (fun f : Module.Dual (ZMod 2) (Additive S) => (f : Additive S → ZMod 2))
      DFunLike.coe_injective
  let := Fintype.ofFinite (Module.Dual (ZMod 2) (Additive S))
  set ρS := ρ.comp SemidirectProduct.inl with hρS
  set Γ := φ.range
  let := Fintype.ofFinite Γ
  have hcardΓ : Fintype.card Γ = p := by rw [← Nat.card_eq_fintype_card]; exact hφ
  have hS8 : 8 ≤ Nat.card S := by
    rcases hpd with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> rw [hS] <;> norm_num
  have : Nontrivial W := nontrivial_of_isIrreducible hρ
  have hcomm : ∀ a b : A, φ a * φ b = φ b * φ a := by
    have := isCyclic_of_prime_card hφ
    intro a b
    have h := (IsCyclic.isMulCommutative (α := Γ)).is_comm.comm ⟨φ a, a, rfl⟩ ⟨φ b, b, rfl⟩
    exact congrArg Subtype.val h
  have hzero : signWeightSpace ρS 0 = ⊥ := by
    rcases eq_bot_or_eq_top_of_isIrreducible hρ _
        (signWeightSpace_rep_mem_of_forall_dualAct ρ fun a => map_zero (dualAct (φ a))) with
      h | h
    · exact h
    · have := card_le_two_of_signWeightSpace_eq_top ρS hinj h
      omega
  obtain ⟨χ₀, hχ₀⟩ : ∃ χ, signWeightSpace ρS χ ≠ ⊥ := by
    by_contra h
    push Not at h
    have htop := iSup_signWeightSpace_eq_top ρS hk
    simp only [h, iSup_bot] at htop
    exact bot_ne_top htop
  have hχ₀0 : χ₀ ≠ 0 := fun h => hχ₀ (h ▸ hzero)
  set g : Γ → Module.Dual (ZMod 2) (Additive S) := fun σ => dualAct (σ : MulAut S) χ₀ with hg
  have horbinj : Function.Injective g := by
    intro σ τ hστ
    change dualAct (σ : MulAut S) χ₀ = dualAct (τ : MulAut S) χ₀ at hστ
    by_contra hne
    obtain ⟨b, hb⟩ := (τ⁻¹ * σ).2
    have hb1 : φ b ≠ 1 := by
      rw [hb]
      intro h1
      exact hne (inv_mul_eq_one.mp (Subtype.ext h1)).symm
    apply hχ₀0
    refine eq_zero_of_dualAct_eq_self hirr hcomm hb1 ?_
    rw [hb]
    change dualAct ((τ : MulAut S)⁻¹ * (σ : MulAut S)) χ₀ = χ₀
    rw [dualAct_mul, hστ, dualAct_inv_dualAct]
  have hsupp : {χ | signWeightSpace ρS χ ≠ ⊥} = Set.range fun a : A => dualAct (φ a) χ₀ := by
    ext ψ
    constructor
    · intro hψ
      by_contra h
      exact hψ (signWeightSpace_eq_bot_of_forall_dualAct_ne hk ρ hρ hχ₀ fun a ha => h ⟨a, ha⟩)
    · rintro ⟨a, rfl⟩
      exact signWeightSpace_dualAct_ne_bot ρ a hχ₀
  have hrange : (Set.range fun a : A => dualAct (φ a) χ₀) = Set.range g := by
    ext ψ
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨⟨φ a, a, rfl⟩, rfl⟩
    · rintro ⟨⟨_, a, rfl⟩, rfl⟩
      exact ⟨a, rfl⟩
  have hsuppF : ∀ ψ, signWeightSpace ρS ψ ≠ ⊥ ↔ ∃ σ : Γ, g σ = ψ := fun ψ =>
    Set.ext_iff.mp (hsupp.trans hrange) ψ
  have hncard : Set.ncard {χ | signWeightSpace ρS χ ≠ ⊥} = p := by
    rw [hsupp, hrange, Set.ncard_range_of_injective horbinj, hφ]
  have hfilt : (Finset.univ.filter fun χ => signWeightSpace ρS χ ≠ ⊥) = Finset.univ.image g := by
    ext ψ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    exact hsuppF ψ
  have hsumΓ : ∀ f : Module.Dual (ZMod 2) (Additive S) → ℕ,
      ∑ χ, (if signWeightSpace ρS χ ≠ ⊥ then f χ else 0) = ∑ σ : Γ, f (g σ) := by
    intro f
    rw [← Finset.sum_filter, hfilt, Finset.sum_image fun σ _ τ _ h => horbinj h]
  set e := Module.finrank k (signWeightSpace ρS χ₀) with he_def
  have he1 : 1 ≤ e := Nat.pos_of_ne_zero fun h => hχ₀ (Submodule.finrank_eq_zero.mp h)
  have he : ∀ χ, signWeightSpace ρS χ ≠ ⊥ → Module.finrank k (signWeightSpace ρS χ) = e := by
    intro χ hχ
    obtain ⟨σ, rfl⟩ := (hsuppF χ).mp hχ
    obtain ⟨a, ha⟩ := σ.2
    change Module.finrank k (signWeightSpace ρS (dualAct (σ : MulAut S) χ₀)) = e
    rw [← ha]
    exact finrank_signWeightSpace_dualAct ρ a χ₀
  have hdimW : Module.finrank k W = p * e := by
    have h := finrank_iSup_eq_sum_of_iSupIndep (iSupIndep_signWeightSpace ρS hk)
    rw [iSup_signWeightSpace_eq_top ρS hk, finrank_top] at h
    have h1 : ∀ χ, Module.finrank k (signWeightSpace ρS χ) =
        if signWeightSpace ρS χ ≠ ⊥ then e else 0 := by
      intro χ
      by_cases h2 : signWeightSpace ρS χ = ⊥
      · rw [h2, finrank_bot]
        simp
      · rw [he χ h2]
        simp [h2]
    rw [h, Finset.sum_congr rfl fun χ _ => h1 χ, hsumΓ (fun _ => e), Finset.sum_const,
      Finset.card_univ, hcardΓ, smul_eq_mul]
  have hfix : ∀ s : S,
      Module.finrank k (Module.End.eigenspace (ρ (SemidirectProduct.inl s)) 1) =
        e * (Finset.univ.filter fun σ : Γ => g σ (Additive.ofMul s) = 0).card := by
    intro s
    have h := finrank_eigenspace_one_eq_sum hk ρS s
    have h1 : ∀ χ, (if χ (Additive.ofMul s) = 0 then
          Module.finrank k (signWeightSpace ρS χ) else 0) =
        if signWeightSpace ρS χ ≠ ⊥ then (if χ (Additive.ofMul s) = 0 then e else 0) else 0 := by
      intro χ
      by_cases h2 : signWeightSpace ρS χ = ⊥
      · simp [h2]
      · rw [he χ h2]
        simp [h2]
    change Module.finrank k (Module.End.eigenspace (ρS s) 1) = _
    rw [h, Finset.sum_congr rfl fun χ _ => h1 χ,
      hsumΓ (fun χ => if χ (Additive.ofMul s) = 0 then e else 0), ← Finset.sum_filter,
      Finset.sum_const, smul_eq_mul, mul_comm]
  have h7 : p = 7 → ∀ s : S, s ≠ 1 →
      Module.finrank k (Module.End.eigenspace (ρ (SemidirectProduct.inl s)) 1) = 3 * e := by
    intro hp7 s hs
    have hd : d = 3 := by
      rcases hpd with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · omega
    have hcardD : Fintype.card (Module.Dual (ZMod 2) (Additive S)) = 8 := by
      rw [← Nat.card_eq_fintype_card, natCard_dual_eq, hS, hd]
      norm_num
    have himg : Finset.univ.image g = Finset.univ.erase 0 := by
      apply Finset.eq_of_subset_of_card_le
      · intro χ hχ
        rw [Finset.mem_erase]
        refine ⟨fun h0 => ?_, Finset.mem_univ _⟩
        rw [← hfilt, Finset.mem_filter] at hχ
        exact hχ.2 (by rw [h0]; exact hzero)
      · rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcardD,
          Finset.card_image_of_injective _ horbinj, Finset.card_univ, hcardΓ, hp7]
    have hcount : (Finset.univ.filter fun σ : Γ => g σ (Additive.ofMul s) = 0).card = 3 := by
      have h1 : (Finset.univ.filter fun σ : Γ => g σ (Additive.ofMul s) = 0).card =
          ((Finset.univ.image g).filter fun χ => χ (Additive.ofMul s) = 0).card := by
        rw [Finset.filter_image, Finset.card_image_of_injective _ horbinj]
      rw [h1, himg, Finset.filter_erase, Finset.card_erase_of_mem]
      · have h2 := two_mul_card_filter_dual_eq_zero (A := S) (x := Additive.ofMul s)
          (by rwa [ne_eq, ofMul_eq_zero])
        rw [hcardD] at h2
        omega
      · simp
    rw [hfix s, hcount, mul_comm]
  have h5 : p = 5 →
      (Set.ncard {s : S | s ≠ 1 ∧
          Module.finrank k (Module.End.eigenspace (ρ (SemidirectProduct.inl s)) 1) = 3 * e} =
          10 ∧
        Set.ncard {s : S | s ≠ 1 ∧
          Module.finrank k (Module.End.eigenspace (ρ (SemidirectProduct.inl s)) 1) = e} = 5 ∧
        ∀ s : S, s ≠ 1 →
          Module.finrank k (Module.End.eigenspace (ρ (SemidirectProduct.inl s)) 1) = 3 * e ∨
          Module.finrank k (Module.End.eigenspace (ρ (SemidirectProduct.inl s)) 1) = e) := by
    intro hp5
    have hd : d = 4 := by
      rcases hpd with ⟨h, -⟩ | ⟨-, h⟩
      · omega
      · exact h
    let eΓ : Γ ≃ Fin 5 := Fintype.equivFinOfCardEq (hcardΓ.trans hp5)
    set ev : S → Fin 5 → ZMod 2 := fun s i => g (eΓ.symm i) (Additive.ofMul s) with hev
    have hzc : ∀ s, (Finset.univ.filter fun σ : Γ => g σ (Additive.ofMul s) = 0).card =
        zeroCountFive (ev s) := by
      intro s
      refine Finset.card_equiv eΓ fun σ => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, ev, Equiv.symm_apply_apply]
    have hsum0 : ∑ σ : Γ, g σ = 0 := by
      have : Nontrivial Γ := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
      obtain ⟨τ, hτ⟩ := exists_ne (1 : Γ)
      obtain ⟨b, hb⟩ := τ.2
      refine eq_zero_of_dualAct_eq_self hirr hcomm (b := b)
        (fun h1 => hτ (Subtype.ext (hb.symm.trans h1))) ?_
      rw [map_sum, hb]
      exact Fintype.sum_equiv (Equiv.mulLeft τ) _ _ fun σ => (dualAct_mul _ _ _).symm
    have hev_sum : ∀ s, ∑ i, ev s i = 0 := by
      intro s
      have h := congrArg (fun ψ : Module.Dual (ZMod 2) (Additive S) => ψ (Additive.ofMul s)) hsum0
      simp only [LinearMap.zero_apply] at h
      rw [LinearMap.sum_apply] at h
      rw [← h]
      exact Fintype.sum_equiv eΓ.symm _ _ fun i => rfl
    have hev_inj : Function.Injective ev := by
      intro s t hst
      have h1 : ∀ σ : Γ, g σ (Additive.ofMul (s * t⁻¹)) = 0 := by
        intro σ
        have h2 := congrFun hst (eΓ σ)
        simp only [ev, Equiv.symm_apply_apply] at h2
        rw [ofMul_mul, ofMul_inv, map_add, map_neg, h2, add_neg_cancel]
      have h3 : ρS (s * t⁻¹) = 1 := (rep_eq_one_iff_signWeightSpace ρS hk _).mpr fun χ hχ => by
        obtain ⟨σ, rfl⟩ := (hsuppF χ).mp hχ
        exact h1 σ
      exact mul_inv_eq_one.mp (hinj (h3.trans (map_one ρS).symm))
    have hcardS : Fintype.card S = 16 := by
      rw [← Nat.card_eq_fintype_card, hS, hd]
      norm_num
    have hsurj : ∀ w : Fin 5 → ZMod 2, ∑ i, w i = 0 → w ∈ Set.range ev := by
      have himg : Finset.univ.image ev =
          Finset.univ.filter fun w : Fin 5 → ZMod 2 => ∑ i, w i = 0 := by
        apply Finset.eq_of_subset_of_card_le
        · intro w hw
          obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hw
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hev_sum s⟩
        · rw [Finset.card_image_of_injective _ hev_inj, Finset.card_univ, hcardS,
            card_filter_sum_eq_zero_fin_five]
      intro w hw
      have h : w ∈ Finset.univ.image ev := by
        rw [himg]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩
      obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp h
      exact ⟨s, rfl⟩
    have hev1 : ev 1 = 0 := by
      funext i
      simp only [ev, ofMul_one, map_zero, Pi.zero_apply]
    have hfix' : ∀ s, Module.finrank k (Module.End.eigenspace (ρ (SemidirectProduct.inl s)) 1) =
        e * zeroCountFive (ev s) := fun s => by rw [hfix s, hzc s]
    have hset3 : {s : S | s ≠ 1 ∧
        Module.finrank k (Module.End.eigenspace (ρ (SemidirectProduct.inl s)) 1) = 3 * e} =
        ev ⁻¹' {w | zeroCountFive w = 3} := by
      ext s
      change (s ≠ 1 ∧ _ = 3 * e) ↔ zeroCountFive (ev s) = 3
      rw [hfix' s]
      constructor
      · rintro ⟨-, h⟩
        exact Nat.eq_of_mul_eq_mul_left he1 (h.trans (mul_comm 3 e))
      · intro h
        refine ⟨fun hs1 => ?_, by rw [h, mul_comm]⟩
        rw [hs1, hev1, zeroCountFive_zero] at h
        omega
    have hset1 : {s : S | s ≠ 1 ∧
        Module.finrank k (Module.End.eigenspace (ρ (SemidirectProduct.inl s)) 1) = e} =
        ev ⁻¹' {w | zeroCountFive w = 1} := by
      ext s
      change (s ≠ 1 ∧ _ = e) ↔ zeroCountFive (ev s) = 1
      rw [hfix' s]
      constructor
      · rintro ⟨-, h⟩
        exact Nat.eq_of_mul_eq_mul_left he1 (h.trans (mul_one e).symm)
      · intro h
        refine ⟨fun hs1 => ?_, by rw [h, mul_one]⟩
        rw [hs1, hev1, zeroCountFive_zero] at h
        omega
    refine ⟨?_, ?_, fun s hs => ?_⟩
    · rw [hset3, Set.ncard_preimage_of_injective_subset_range (s := {w | zeroCountFive w = 3})
        hev_inj (fun w hw => hsurj w (sum_eq_zero_of_zeroCountFive_eq_three w hw)),
        ncard_zeroCountFive_eq_three]
    · rw [hset1, Set.ncard_preimage_of_injective_subset_range (s := {w | zeroCountFive w = 1})
        hev_inj (fun w hw => hsurj w (sum_eq_zero_of_zeroCountFive_eq_one w hw)),
        ncard_zeroCountFive_eq_one]
    · have hne : ev s ≠ 0 := fun h => hs (hev_inj (h.trans hev1.symm))
      rw [hfix' s]
      rcases zeroCountFive_eq_three_or_one (ev s) (hev_sum s) hne with h | h
      · left
        rw [h, mul_comm]
      · right
        rw [h, mul_one]
  have hwit : ∃ s : S, s ≠ 1 ∧
      Module.finrank k (Module.End.eigenspace (ρ (SemidirectProduct.inl s)) 1) = 3 * e := by
    rcases hpd with ⟨hp7, -⟩ | ⟨hp5, -⟩
    · have : Nontrivial S := Finite.one_lt_card_iff_nontrivial.mp (by omega)
      obtain ⟨s, hs⟩ := exists_ne (1 : S)
      exact ⟨s, hs, h7 hp7 s hs⟩
    · obtain ⟨s, hs⟩ := Set.nonempty_of_ncard_ne_zero (by rw [(h5 hp5).1]; norm_num)
      exact ⟨s, hs⟩
  refine ⟨⟨χ₀, hχ₀0, hsupp⟩, hncard, e, he1, he, hdimW, h7, h5, fun hle => ?_⟩
  obtain ⟨s, hs, h3⟩ := hwit
  have h4 := hle s hs
  have he' : e = 1 := by omega
  exact ⟨he', by rw [hdimW, he', mul_one]⟩

end CFSG.RankThree.GroupTheory
