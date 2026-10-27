module

public import Mathlib.Algebra.CharP.LinearMaps
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.LinearAlgebra.Semisimple
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RepresentationTheory.Character
public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RepresentationTheory.Semisimple
public import Mathlib.RepresentationTheory.Submodule
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.RingTheory.SimpleModule.Isotypic
public import Mathlib.RingTheory.ZMod.Torsion
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CriticalSubgroupLemmas
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Burnside.NormalComplement
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Extraspecial
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.LinearAlgebra.BlockElementaryMap
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ConjugateRep
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection2.EndFieldRep

namespace CFSG
end CFSG
open CFSG

open _root_.Representation
open Theory.Representation
open MonoidAlgebra
open Module
open Module.End
open Polynomial
open scoped DirectSum
open scoped BigOperators
open scoped TensorProduct
open scoped MonoidAlgebra
open scoped Function
open scoped commutatorElement
/-
**Kind**: Theorem
**Note**: Theorem 2.6
**Stmt**:
Let $G$ be a finite group of odd order.
Let $F$ be a field.
Let $V$ be an $FG$-module of dimension two over $F$ on which $G$ acts faithfully.
Then
(a) If $\char F$ does not divide $|G|$, then $G$ is abelian.
(b) If $\char F = p < \infty$ is divisor of $|G|$, then $G$ has an
abelian Sylow $p$-subgroup that contains $[G, G]$.
-/

lemma CFSG.top_eq_sylow_zero
    {G : Type*} [Group G]
    {p : ℕ} (hp : p = 0) (C : Sylow p G) :
    ⊤ = C.toSubgroup :=
  C.is_maximal' (fun g ↦ ⟨1, by rw [pow_one, hp, pow_zero]⟩) fun _ _ ↦ trivial

lemma CFSG.card_not_dvd_sylow_eq_bot
    {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hp : ¬ p ∣ Nat.card G) (C : Sylow p G) :
    C.toSubgroup = ⊥ := by
  contrapose hp
  have h : p ∣ Nat.card C := by
    rcases IsPGroup.iff_card.mp C.isPGroup' with ⟨n, hn⟩
    rw [hn]
    refine dvd_pow_self p ?_
    contrapose hp
    rw [hp, pow_zero] at hn
    exact (Subgroup.eq_bot_iff_card C.toSubgroup).mpr hn
  exact Nat.dvd_trans h (Subgroup.card_subgroup_dvd_card _)

lemma CFSG.ringChar_prime
    {F : Type*} [Field F]
    (hc : ¬ ringChar F = 0) :
  Fact (ringChar F).Prime := {
    out := by
      have := CharP.char_is_prime_or_zero F (ringChar F)
      rcases CharP.char_is_prime_or_zero F (ringChar F) with h | h
      · exact h
      · exfalso
        exact hc h
  }

private lemma CFSG.card_odd_finite
    {G : Type*} (ho : Odd (Nat.card G)) :
    Finite G :=
  Nat.finite_of_card_ne_zero (Nat.ne_of_odd_add ho)

lemma CFSG.covby_top_of_index_eq_prime {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G] (h : IsPGroup p G)
    {H : Subgroup G} (h_idx : H.index = p) : CovBy H ⊤ ∧ H.Normal := by
  have hp : p.Prime := Fact.out
  have (a b : Prop) : a ∧ b ↔ a ∧ (a → b) := by tauto
  rw [this]
  constructor
  · refine ⟨Ne.lt_top (fun h ↦ ?_), fun K h₁ h₂ ↦ ?_⟩
    · simp [h] at h_idx
      simp [← h_idx, Nat.not_prime_one] at hp
    · have h₃ := Subgroup.relIndex_mul_index h₁.le
      have h₄ : (H.relIndex K * K.index).Prime := by rwa [h₃, h_idx]
      rcases Nat.prime_mul_iff.mp h₄ with (⟨-, h₅⟩ | ⟨-, h₅⟩)
      · rw [Subgroup.index_eq_one] at h₅
        simp [h₅] at h₂
      · rw [Subgroup.relIndex_eq_one] at h₅
        exact h₁.not_ge h₅
  · intro h_max
    simp only [covBy_top_iff] at h_max
    have G_nilpotent : Group.IsNilpotent G := IsPGroup.isNilpotent (p := p) h
    exact Subgroup.NormalizerCondition.normal_of_coatom H Group.normalizerCondition_of_isNilpotent h_max

/-
**Kind**: Theorem
**Note**: G, Theorem 3.2.2
**Stmt**:
Let $G$ be a finite group.
Let $F$ be a field.
Let $V$ be a finite dimensional vector space over $F$.
Let $ρ$ be a faithful and irreducible representation of $G$ over $V$.
Then $Z(G)$ is cyclic.
-/

open scoped IsMulCommutative in
set_option backward.isDefEq.respectTransparency false in
public theorem CFSG.center_cyclic_of_representation_faithful_irreducible
    {F : Type*} [Field F]
    {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F G V) [inst : IsIrreducible ρ]
    (hi : Function.Injective ρ) :
    IsCyclic (Subgroup.center G) := by
  let _ := (inferInstance : FiniteDimensional F V)
  let f : (Subgroup.center G) →* End F[G] ρ.asModule := {
    toFun := fun c' ↦ {
      toFun := fun v' ↦ (single c'.val (1 : F)) • v'
      map_add' := by simp only [smul_add, single_smul, one_smul, implies_true]
      map_smul' := fun x v' ↦ by
        have : (single c'.val (1 : F)) * x = x * (single c'.val (1 : F)) := by
          refine induction_linear x ?_ (fun x y h1 h2 ↦ ?_) (fun g f ↦ ?_)
          · simp only [mul_zero, zero_mul]
          · rw [mul_add, h1, h2, add_mul]
          · simp only [single_mul_single, one_mul, mul_one]
            rw [Subgroup.mem_center_iff.mp c'.prop]
        rw [smul_smul, this, RingHom.id_apply, smul_smul]
    }
    map_one' := by
      ext v'
      have : (single (1 : G) (1 : F)) • v' = (1 : End F[G] ρ.asModule) v' := by
        simp only [single_smul, map_one, Module.End.one_apply, one_smul]
        rfl
      exact this
    map_mul' := fun c₁ c₂ ↦ by
      ext v'
      change single (c₁ * c₂).val (1 : F) • v' =
        single c₁.val (1 : F) • (single c₂.val (1 : F) • v')
      calc
        single (c₁ * c₂).val (1 : F) • v' =
            (single c₁.val (1 : F) * single c₂.val (1 : F)) • v' := by
              rw [single_mul_single, Subgroup.coe_mul, one_mul]
        _ = single c₁.val (1 : F) • (single c₂.val (1 : F) • v') :=
          mul_smul _ _ _
  }
  let k := Subring.closure (Set.range f)
  let : IsMulCommutative k := by
    apply Subring.isMulCommutative_closure
    intro x hx y hy _
    rcases hx with ⟨cx, hcx⟩
    rcases hy with ⟨cy, hcy⟩
    change x * y = y * x
    rw [← hcx, ← hcy, ← map_mul, ← map_mul]
    apply DFunLike.congr_arg
    suffices h :  cx.val * cy.val = cy.val * cx.val by
      exact SetLike.coe_eq_coe.mp (hi (congrArg (⇑ρ) (hi (congrArg (⇑ρ) h))))
    rw [Subgroup.mem_center_iff.mp cx.prop]
  let f' : (Subgroup.center G) →* k := {
    toFun := fun c' ↦ ⟨f c', Subring.mem_closure_of_mem (Set.mem_range_self c')⟩
    map_one' := by simp only [map_one]; rfl
    map_mul' := by simp only [map_mul, MulMemClass.mk_mul_mk, implies_true]
  }
  have hf : Function.Injective f := fun c₁ c₂ he ↦ by
    have (v' : ρ.asModule) : (single c₁.val (1 : F)) • v' = (single c₂.val (1 : F)) • v' := by calc
      _ = f c₁ v' := rfl
      _ = f c₂ v' := by rw [he]
      _ = _ := rfl
    simp only [single_smul, one_smul] at this
    have : ∀ (v : V), (ρ c₁.val) v = (ρ c₂.val) v := fun v ↦ this (ρ.asModuleEquiv.symm v)
    rw [← DFunLike.ext_iff] at this
    exact SetLike.coe_eq_coe.mp (hi this)
  have := Subrepresentation.irreducible_module_nontrivial ρ
  have : Nontrivial ρ.asModule := Function.Injective.nontrivial (f := ρ.asModuleEquiv.symm) (LinearEquiv.injective ρ.asModuleEquiv.symm)
  have : IsDomain k := {
    toIsCancelMulZero := by
      refine isCancelMulZero_iff_noZeroDivisors.mpr ?_
      rw [_root_.noZeroDivisors_iff]
      intro a b hab
      have : DecidableEq (End F[G] ρ.asModule) := by exact Classical.typeDecidableEq (End F[G] ρ.asModule)
      have : IsSimpleModule F[G] ρ.asModule := (irreducible_iff_isSimpleModule_asModule ρ).mp inst
      exact zero_eq_mul.mp hab.symm
    toNontrivial := Subring.instNontrivialSubtypeMem k
  }
  have : Function.Injective f' := fun c₁ c₂ he ↦ by
    have : (f' c₁).val = (f' c₂).val := by rw [he]
    exact (Subgroup.inclusion_inj fun ⦃x⦄ a ↦ a).mp (hf this)
  exact isCyclic_of_injective_ringHom f' this

lemma CFSG.pGroup_fix_nonzero_vector
    {F : Type*} [Field F] (hc : ¬ ringChar F = 0)
    {G : Type*} [Group G] [Finite G] (hp : IsPGroup (ringChar F) G)
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [Nontrivial V]
    (ρ : Representation F G V) :
    ∃ v : V, v ≠ 0 ∧ ∀ g : G, ρ g • v = v := by
  let p := ringChar F
  let hc := ringChar_prime hc
  let pr : ℕ → Prop := fun n ↦ (H : Subgroup G) → (hcard : Nat.card H = p ^ n) → ∃ v : V, v ≠ 0 ∧ ∀ g ∈ H, ρ g • v = v
  have (n : ℕ) : pr n := by
    induction n with
    | zero =>
      intro H hH
      obtain ⟨v, hv⟩ := (exists_ne 0 : ∃ v : V, v ≠ 0)
      use v
      refine ⟨hv, fun g hg ↦ ?_⟩
      rw [pow_zero, Subgroup.card_eq_one] at hH
      rw [hH] at hg
      have : g = 1 := ofMul_eq_zero.mp hg
      rw [this, map_one, one_smul]
    | succ n ih =>
      intro H hH
      have hdvd : p ^ n ∣ Nat.card H := hH ▸ dvd_of_mul_right_eq p rfl
      obtain ⟨M, hM⟩ := Sylow.exists_subgroup_card_pow_prime p (G := H) hdvd
      have h_idx : M.index = ringChar F := by
        rw [Subgroup.index_eq_card, ← mul_left_inj' (c := Nat.card M) (ne_zero_of_lt Nat.card_pos), ← Subgroup.card_eq_card_quotient_mul_card_subgroup M, hH, hM, pow_succ']
      have hp : IsPGroup (ringChar F) ↥H := IsPGroup.to_subgroup hp H
      obtain ⟨hM1, hM2⟩ := covby_top_of_index_eq_prime hp h_idx (H := M) (G := H)
      obtain ⟨w, hw1, hw2⟩ := ih (M.map H.subtype) (by rw [Subgroup.card_subtype, hM])
      let φ : Subrepresentation (ρ.comp H.subtype) := {
        toSubmodule := {
          carrier := {w | ∀ g ∈ Subgroup.map H.subtype M, ρ g • w = w}
          add_mem' := by
            simp_all only [Subgroup.mem_map, Subgroup.subtype_apply, Subtype.exists, exists_and_right, exists_eq_right, Module.End.smul_def, forall_exists_index, Set.mem_ofPred_eq, map_add, implies_true]
          zero_mem' := by
            simp_all only [Subgroup.mem_map, Subgroup.subtype_apply, Subtype.exists, exists_and_right, exists_eq_right, Module.End.smul_def, forall_exists_index, Set.mem_ofPred_eq, map_zero, implies_true]
          smul_mem' := by
            simp_all only [Subgroup.mem_map, Subgroup.subtype_apply, Subtype.exists, exists_and_right, exists_eq_right, Module.End.smul_def, forall_exists_index, Set.mem_ofPred_eq, map_smul, implies_true]
        }
        apply_mem_toSubmodule := by
          intro g v hv g' hg'
          suffices h : (ρ g⁻¹) • ρ g' • (ρ g) • v =  v by
            nth_rw 2 [← h]
            simp only [MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply, Module.End.smul_def, self_inv_apply]
          rw [← mul_smul, ← mul_smul, ← map_mul, ← map_mul]
          exact hv (g⁻¹ * g' * g) (by
            let g'' : H := ⟨g', by
              simp_all only [ne_eq, Module.End.smul_def, covBy_top_iff, Subgroup.mem_map, Subgroup.subtype_apply,
                Subtype.exists, exists_and_right, exists_eq_right, forall_exists_index, Submodule.mem_mk,
                AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq, pr, p]
              obtain ⟨val, property⟩ := g
              obtain ⟨w_1, h⟩ := hg'
              simp_all only⟩
            suffices g⁻¹ * g'' * g ∈ M by
              simp_all only [ne_eq, Module.End.smul_def, covBy_top_iff, Subgroup.mem_map, Subgroup.subtype_apply,
                Subtype.exists, exists_and_right, exists_eq_right, forall_exists_index, Submodule.mem_mk,
                AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq, InvMemClass.coe_inv, pr, p, g'']
              obtain ⟨val, property⟩ := g
              obtain ⟨val_1, property_1⟩ := g''
              obtain ⟨w_1, h⟩ := hg'
              simp_all only
              apply Exists.intro
              · exact this
              · apply MulMemClass.mul_mem
                · apply MulMemClass.mul_mem
                  · simp_all only [inv_mem_iff]
                  · obtain ⟨val_2, property_2⟩ := w_1
                    obtain ⟨left, right⟩ := h
                    subst right
                    simp_all only [Subgroup.subtype_apply]
                · simp_all only
            exact Subgroup.Normal.conj_mem' hM2 g'' (by
              simp_all only [ne_eq, Module.End.smul_def, covBy_top_iff, Subgroup.mem_map, Subgroup.subtype_apply, Subtype.exists, exists_and_right, exists_eq_right, forall_exists_index, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq, pr, p, g'']
              obtain ⟨val, property⟩ := g
              obtain ⟨val_1, property_1⟩ := g''
              obtain ⟨w_1, h⟩ := hg'
              obtain ⟨val_2, property_2⟩ := w_1
              obtain ⟨left, right⟩ := h
              subst right
              simp_all only [Subgroup.subtype_apply]
              exact left) g)
        }
      obtain ⟨y, hy1⟩ : ∃ y : H, y ∉ M := SetLike.exists_not_mem_of_ne_top M (CovBy.ne' hM1).symm rfl
      have hy2 : y ^ (ringChar F) ∈ M := h_idx.symm ▸ Subgroup.pow_index_mem M y
      let : Nontrivial ↥φ.toSubmodule := by
        obtain ⟨v, hv1, hv2⟩ := ih (M.map H.subtype) (by rw [Subgroup.card_subtype, hM])
        rw [nontrivial_iff_exists_ne 0]
        use ⟨v, hv2⟩
        suffices v ≠ 0 by
          contrapose! this
          have : (⟨v, hv2⟩ : φ.toSubmodule).val = 0 := by rw [this]; rfl
          exact this
        exact hv1
      have : (φ.toRepresentation y) ^ p = 1 := by
        ext w
        rw [Module.End.one_apply, ← map_pow]
        have := w.prop (y ^ p) (by
          simp only [Subgroup.mem_map, Subgroup.subtype_apply, Subtype.exists, exists_and_right, exists_eq_right]
          exact ⟨Subgroup.pow_mem H (SetLike.coe_mem y) p, hy2⟩)
        exact this
      have : (φ.toRepresentation y - 1) ^ p = 0 := by
        let ip : CharP (End F φ.toSubmodule) p := by
          rw [CharP.charP_iff_prime_eq_zero hc.out]
          ext w
          simp only [Module.End.natCast_apply, SetLike.val_smul_of_tower, LinearMap.zero_apply, ZeroMemClass.coe_zero]
          have : (ringChar F : F) • w.val = 0 := by
            rw [ringChar.Nat.cast_ringChar, zero_smul]
          rw [← this, Nat.cast_smul_eq_nsmul]
        simp only [Commute.one_right, sub_pow_expChar_of_commute, one_pow]
        rw [this, sub_self]
      have := IsNilpotent.mk (φ.toRepresentation y - 1) p this
      have : End.HasEigenvalue (φ.toRepresentation y - 1) 0 := by
        rw [LinearMap.isNilpotent_iff_charpoly] at this
        have : Polynomial.constantCoeff (φ.toRepresentation y - 1).charpoly = 0 := by
          rw [this]
          have : 0 < Module.finrank F φ.toSubmodule := by
            rw [Module.finrank_pos_iff_of_free F ↥φ.toSubmodule]
            infer_instance
          have : Module.finrank F φ.toSubmodule ≠ 0 := Nat.ne_zero_iff_zero_lt.mpr this
          show Polynomial.coeff (Polynomial.X ^ Module.finrank F ↥φ.toSubmodule) 0 = 0
          rw [Polynomial.coeff_X_pow, ite_eq_right_iff]
          tauto
        have h := (LinearMap.hasEigenvalue_zero_tfae (φ.toRepresentation y - 1)).out 1 3
        rw [h, this]
      obtain ⟨w, hw⟩ := End.HasEigenvalue.exists_hasEigenvector this
      rw [End.hasEigenvector_iff] at hw
      use w, (by simp only [ne_eq,
        ZeroMemClass.coe_eq_zero, hw.2, not_false_eq_true])
      have hw := hw.1
      simp only [End.eigenspace_zero, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply] at hw
      intro g hg
      have : ∃ n : ℕ, ∃ m ∈ (M.map H.subtype), g = m * y ^ n := by
        let y' : H ⧸ M := y⁻¹
        let h : H := ⟨g, hg⟩
        let h' : H ⧸ M := h⁻¹
        have : Nat.card (H ⧸ M) = p := Nat.succ_inj.mp (congrArg Nat.succ h_idx)
        have : Submonoid.powers y' = ⊤ := powers_eq_top_of_prime_card this (by
          contrapose hy1
          exact (QuotientGroup.eq_one_iff y).mp (one_eq_inv.mp hy1.symm))
        have hh' : h' ∈ (⊤ : Submonoid (H ⧸ M)) := Submonoid.mem_top h'
        rw [← this, Submonoid.mem_powers_iff] at hh'
        obtain ⟨n, hn⟩ := hh'
        have hn : ((y⁻¹ ^ n : H) : H ⧸ M) = (h⁻¹ : H ⧸ M) := by
          subst h'
          rw [← hn]
          rfl
        have : (h⁻¹ : H ⧸ M) = ((h⁻¹ : H) : H ⧸ M) := rfl
        rw [this, QuotientGroup.eq, ← Subgroup.inv_mem_iff, inv_pow, inv_inv, mul_inv_rev, inv_inv, ← inv_pow] at hn
        use n, (h * (y⁻¹ ^ n)).val, (by
          simp only [Subgroup.mem_map, Subgroup.subtype_apply, Subtype.exists, exists_and_right, exists_eq_right]
          exact ⟨SetLike.coe_mem (h * y⁻¹ ^ n), hn⟩)
        simp only [inv_pow, Subgroup.coe_mul, InvMemClass.coe_inv, SubmonoidClass.coe_pow, inv_mul_cancel_right]
        rfl
      obtain ⟨n, m, hm, h⟩ := this
      rw [← add_left_inj (a := w), zero_add, sub_add, sub_self, sub_zero] at hw
      have hw : ρ y w = w := by nth_rw 2 [← hw]; rfl
      have : ρ (y ^ n) w = w := by
        clear h
        induction n with
        | zero =>
          simp only [pow_zero, map_one, Module.End.one_apply]
        | succ n ih =>
          rw [pow_succ', map_mul, Module.End.mul_apply, ih, hw]
      show ρ g w = w
      rw [h, map_mul, Module.End.mul_apply, this]
      exact w.prop m hm
  obtain ⟨n, hn⟩ := IsPGroup.exists_card_eq hp
  exact Exists.casesOn (this n ⊤ (hn.symm ▸ Subgroup.card_top)) fun w h ↦
      And.casesOn h fun l r ↦ Exists.intro w ⟨l, fun g ↦ r g trivial⟩

lemma CFSG.nontrivial_of_finrank_eq_two
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (hdim : Module.finrank F V = 2) : Nontrivial V := by
  have hpos : 0 < Module.finrank F V := by omega
  exact (Module.finrank_pos_iff (R := F) (M := V)).mp hpos

lemma CFSG.subrepresentation_isCompl_toSubmodule
    {F G V : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V]
    {ρ : Representation F G V}
    {φ ψ : Subrepresentation ρ}
    (hcompl : IsCompl φ ψ) :
    IsCompl φ.toSubmodule ψ.toSubmodule := by
  refine ⟨?_, ?_⟩
  · rw [disjoint_iff]
    have h := congrArg Subrepresentation.toSubmodule hcompl.inf_eq_bot
    change φ.toSubmodule ⊓ ψ.toSubmodule = (⊥ : Submodule F V) at h
    exact h
  · rw [codisjoint_iff]
    have h := congrArg Subrepresentation.toSubmodule hcompl.sup_eq_top
    change φ.toSubmodule ⊔ ψ.toSubmodule = (⊤ : Submodule F V) at h
    exact h

lemma CFSG.det_eq_det_mul_det_of_isCompl_subrepresentation
    {F G V : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F G V) (φ ψ : Subrepresentation ρ)
    (hcompl : IsCompl φ.toSubmodule ψ.toSubmodule) (x : G) :
    LinearMap.det (ρ x) =
      LinearMap.det (φ.toRepresentation x) * LinearMap.det (ψ.toRepresentation x) := by
  let eQ : (V ⧸ φ.toSubmodule) ≃ₗ[F] ψ.toSubmodule :=
    Submodule.quotientEquivOfIsCompl φ.toSubmodule ψ.toSubmodule hcompl
  have hconj :
      ((eQ : (V ⧸ φ.toSubmodule) →ₗ[F] ψ.toSubmodule) ∘ₗ
        Submodule.mapQ φ.toSubmodule φ.toSubmodule (ρ x) (φ.apply_mem_toSubmodule x) ∘ₗ
        ((eQ.symm : ψ.toSubmodule ≃ₗ[F] (V ⧸ φ.toSubmodule)) : ψ.toSubmodule →ₗ[F] (V ⧸ φ.toSubmodule))) =
      ψ.toRepresentation x := by
    apply LinearMap.ext
    intro w
    calc
      _ = (⟨(ρ x) w, ψ.apply_mem_toSubmodule x w.2⟩ : ψ.toSubmodule) := by
        simpa [eQ] using
          (Submodule.quotientEquivOfIsCompl_apply_mk_right
            (p := φ.toSubmodule) (q := ψ.toSubmodule) hcompl
            ⟨(ρ x) w, ψ.apply_mem_toSubmodule x w.2⟩)
      _ = ψ.toRepresentation x w := rfl
  have hdetq :
      LinearMap.det (Submodule.mapQ φ.toSubmodule φ.toSubmodule (ρ x) (φ.apply_mem_toSubmodule x)) =
        LinearMap.det (ψ.toRepresentation x) := by
    have htmp := LinearMap.det_conj
      (f := Submodule.mapQ φ.toSubmodule φ.toSubmodule (ρ x) (φ.apply_mem_toSubmodule x))
      (e := eQ)
    rw [hconj] at htmp
    simpa using htmp.symm
  calc
    LinearMap.det (ρ x) =
      LinearMap.det ((ρ x).restrict (φ.apply_mem_toSubmodule x)) *
        LinearMap.det (Submodule.mapQ φ.toSubmodule φ.toSubmodule (ρ x) (φ.apply_mem_toSubmodule x)) := by
          simpa using LinearMap.det_eq_det_mul_det
            (e := ρ x) (W := φ.toSubmodule) (he := φ.apply_mem_toSubmodule x)
    _ = LinearMap.det (φ.toRepresentation x) *
          LinearMap.det (Submodule.mapQ φ.toSubmodule φ.toSubmodule (ρ x) (φ.apply_mem_toSubmodule x)) := by
          rfl
    _ = LinearMap.det (φ.toRepresentation x) * LinearMap.det (ψ.toRepresentation x) := by
          rw [hdetq]

lemma CFSG.finrank_eq_one_of_isCompl_left_of_finrank_eq_two
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (φ ψ : Submodule F V) (hcompl : IsCompl φ ψ)
    (hφ : Module.finrank F φ = 1) (hdim : Module.finrank F V = 2) :
    Module.finrank F ψ = 1 := by
  have hadd := Submodule.finrank_add_eq_of_isCompl hcompl
  rw [hdim, hφ] at hadd
  omega

lemma CFSG.linearMap_eq_id_of_isCompl_of_eq_id_on_each
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (e : Module.End F V) (φ ψ : Submodule F V) (hcompl : IsCompl φ ψ)
    (hφ : ∀ u : φ, e u = u) (hψ : ∀ w : ψ, e w = w) :
    e = LinearMap.id := by
  ext v
  rcases Submodule.existsUnique_add_of_isCompl hcompl v with ⟨u, w, huw, _⟩
  calc
    e v = e (u + w) := by rw [huw]
    _ = e u + e w := by rw [map_add]
    _ = u + w := by rw [hφ u, hψ w]
    _ = v := huw

lemma CFSG.linearMap_eq_of_isCompl_of_eq_on_each
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (e f : Module.End F V) (φ ψ : Submodule F V) (hcompl : IsCompl φ ψ)
    (hφ : ∀ u : φ, e u = f u) (hψ : ∀ w : ψ, e w = f w) :
    e = f := by
  ext v
  rcases Submodule.existsUnique_add_of_isCompl hcompl v with ⟨u, w, huw, _⟩
  calc
    e v = e (u + w) := by rw [huw]
    _ = e u + e w := by rw [map_add]
    _ = f u + f w := by rw [hφ u, hψ w]
    _ = f (u + w) := by rw [map_add]
    _ = f v := by rw [huw]

lemma CFSG.subrepresentation_eq_smul_id_apply
    {F G V : Type*} [Field F] [Group G] [AddCommGroup V] [Module F V]
    {ρ : Representation F G V} (φ : Subrepresentation ρ) {g : G} {c : F}
    (hc : φ.toRepresentation g = c • LinearMap.id) :
    ∀ u : φ.toSubmodule, ρ g u = c • u := by
  intro u
  have hu : φ.toRepresentation g u = c • u := by
    simpa using congrArg (fun f : Module.End F φ.toSubmodule => f u) hc
  exact congrArg Subtype.val hu

lemma CFSG.eigenspace_le_of_isCompl_of_eq_left
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (e : Module.End F V) (φ ψ : Submodule F V) (hcompl : IsCompl φ ψ)
    {a b : F}
    (hφ : ∀ u : φ, e u = a • u) (hψ : ∀ w : ψ, e w = b • w)
    (hab : a ≠ b) :
    Module.End.eigenspace e a ≤ φ := by
  intro z hz
  rw [Module.End.mem_eigenspace_iff] at hz
  rcases Submodule.existsUnique_add_of_isCompl hcompl z with ⟨u, w, huw, huniqz⟩
  have hu : e (u : V) = a • (u : V) := hφ u
  have hw : e (w : V) = b • (w : V) := hψ w
  have hz1 : ((a • u : φ) : V) + (b • w : ψ) = e z := by
    calc
      ((a • u : φ) : V) + (b • w : ψ) = e (u : V) + e (w : V) := by
        simp [hu, hw]
      _ = e (u + w) := by rw [map_add]
      _ = e z := by rw [huw]
  have hz2 : ((a • u : φ) : V) + (a • w : ψ) = e z := by
    rw [hz]
    simpa [smul_add] using congrArg (fun t : V => a • t) huw
  obtain ⟨u1, w1, hu1w1, huniq⟩ := Submodule.existsUnique_add_of_isCompl hcompl (e z)
  have hu1 := huniq (a • u) (b • w) hz1
  have hu2 := huniq (a • u) (a • w) hz2
  have hw_eq : (b • w : ψ) = a • w := by
    rw [hu1.2, hu2.2]
  have hw_zero : (w : V) = 0 := by
    have hw_eq' : (b : F) • (w : V) = a • (w : V) := congrArg Subtype.val hw_eq
    have : (b - a) • (w : V) = 0 := by
      rw [sub_smul, hw_eq', sub_self]
    rw [smul_eq_zero] at this
    rcases this with hba | hw0
    · exact False.elim (hab (sub_eq_zero.mp hba).symm)
    · exact hw0
  exact huw.symm ▸ by
    simp [hw_zero]

lemma CFSG.eigenspace_eq_bot_of_isCompl_of_ne_left_right
    {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (e : Module.End F V) (φ ψ : Submodule F V) (hcompl : IsCompl φ ψ)
    {a b c : F}
    (hφ : ∀ u : φ, e u = a • u) (hψ : ∀ w : ψ, e w = b • w)
    (hca : c ≠ a) (hcb : c ≠ b) :
    Module.End.eigenspace e c = ⊥ := by
  apply le_antisymm
  · intro z hz
    rw [Module.End.mem_eigenspace_iff] at hz
    rcases Submodule.existsUnique_add_of_isCompl hcompl z with ⟨u, w, huw, huniqz⟩
    have hu : e (u : V) = a • (u : V) := hφ u
    have hw : e (w : V) = b • (w : V) := hψ w
    have hz1 : ((a • u : φ) : V) + (b • w : ψ) = e z := by
      calc
        ((a • u : φ) : V) + (b • w : ψ) = e (u : V) + e (w : V) := by
          simp [hu, hw]
        _ = e (u + w) := by rw [map_add]
        _ = e z := by rw [huw]
    have hz2 : ((c • u : φ) : V) + (c • w : ψ) = e z := by
      rw [hz]
      simpa [smul_add] using congrArg (fun t : V => c • t) huw
    obtain ⟨u1, w1, hu1w1, huniq⟩ := Submodule.existsUnique_add_of_isCompl hcompl (e z)
    have hu1 := huniq (a • u) (b • w) hz1
    have hu2 := huniq (c • u) (c • w) hz2
    have hu_eq : (a • u : φ) = c • u := by
      rw [hu1.1, hu2.1]
    have hw_eq : (b • w : ψ) = c • w := by
      rw [hu1.2, hu2.2]
    have hu_zero : (u : V) = 0 := by
      have hu_eq' : (a : F) • (u : V) = c • (u : V) := congrArg Subtype.val hu_eq
      have : (a - c) • (u : V) = 0 := by
        rw [sub_smul, hu_eq', sub_self]
      rw [smul_eq_zero] at this
      rcases this with hac | hu0
      · exact False.elim (hca (sub_eq_zero.mp hac).symm)
      · exact hu0
    have hw_zero : (w : V) = 0 := by
      have hw_eq' : (b : F) • (w : V) = c • (w : V) := congrArg Subtype.val hw_eq
      have : (b - c) • (w : V) = 0 := by
        rw [sub_smul, hw_eq', sub_self]
      rw [smul_eq_zero] at this
      rcases this with hbc | hw0
      · exact False.elim (hcb (sub_eq_zero.mp hbc).symm)
      · exact hw0
    rw [Submodule.mem_bot, ← huw, hu_zero, hw_zero, zero_add]
  · exact bot_le

lemma CFSG.representation_map_injective
    {F G V : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) (g : G) :
    Function.Injective (ρ g) := by
  intro u v huv
  have h' := congrArg (fun z => (ρ g⁻¹) z) huv
  simpa [map_mul] using h'

lemma CFSG.representation_pow_mem_submodule_of_map_mem
    {F G V : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) (U : Submodule F V) {g : G}
    (hU : ∀ u, u ∈ U → ρ g u ∈ U) :
    ∀ n : ℕ, ∀ u, u ∈ U → ρ (g ^ n) u ∈ U := by
  intro n
  induction n with
  | zero =>
      intro u hu
      simpa using hu
  | succ n ih =>
      intro u hu
      have hu' : ρ g u ∈ U := hU _ hu
      have hpow : ρ (g ^ n) (ρ g u) ∈ U := ih (ρ g u) hu'
      simpa [pow_succ, map_mul, Module.End.mul_eq_comp] using hpow

lemma CFSG.exists_central_element_orderOf_eq_prime_of_nontrivial_pgroup_subgroup
    {G : Type*} [Group G] [Finite G] {q : ℕ} [Fact q.Prime]
    (Q : Subgroup G) (hQp : IsPGroup q Q) (hQne : Q ≠ ⊥) :
    ∃ x : G, x ∈ Q ∧ orderOf x = q ∧ (∀ h ∈ Q, x * h = h * x) ∧ x ^ q = 1 ∧ x ≠ 1 := by
  have : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).2 hQne
  have : Nontrivial (Subgroup.center Q) := IsPGroup.center_nontrivial hQp
  have hcenter_p : IsPGroup q (Subgroup.center Q) := hQp.to_subgroup _
  have hcenter_ne_bot : (Subgroup.center Q : Subgroup Q) ≠ ⊥ := by
    exact (Subgroup.nontrivial_iff_ne_bot (Subgroup.center Q)).1 inferInstance
  have hqdvd : q ∣ Nat.card (Subgroup.center Q) := by
    rcases hcenter_p.card_eq_or_dvd with h1 | hdvd
    · have hone : Nat.card (Subgroup.center Q) > 1 :=
        (Subgroup.one_lt_card_iff_ne_bot (Subgroup.center Q)).2 hcenter_ne_bot
      omega
    · exact hdvd
  obtain ⟨z, hzq⟩ := exists_prime_orderOf_dvd_card' q hqdvd
  refine ⟨z.1.1, z.1.2, ?_, ?_, ?_, ?_⟩
  · calc
      orderOf z.1.1 = orderOf z.1 := Subgroup.orderOf_coe z.1
      _ = orderOf z := Subgroup.orderOf_coe z
      _ = q := hzq
  · intro h hh
    have hzcomm : ∀ y : Q, z.1 * y = y * z.1 := by
      have hzmem : z.1 ∈ Subgroup.center Q := z.2
      rw [Subgroup.mem_center_iff] at hzmem
      intro y
      exact (hzmem y).symm
    exact congrArg Subtype.val (hzcomm ⟨h, hh⟩)
  · have hzpow : z ^ q = 1 := by
      simpa [hzq] using pow_orderOf_eq_one z
    exact congrArg Subtype.val <| congrArg Subtype.val hzpow
  · intro hx1
    have horder : orderOf z = 1 := by
      have hz1 : z = 1 := by
        ext
        exact hx1
      simp [hz1]
    have : q = 1 := hzq.symm.trans horder
    exact (Fact.out : Nat.Prime q).ne_one this

lemma CFSG.exists_prime_dvd_ne_of_not_prime_power_bg {m p : ℕ} (hm0 : m ≠ 0)
    (hm_not : ∀ n, m ≠ p ^ n) : ∃ q, Nat.Prime q ∧ q ∣ m ∧ q ≠ p := by
  by_contra! h
  have h' : ∀ {d}, Nat.Prime d → d ∣ m → d = p := by
    intro d hprime hdvd
    exact h d hprime hdvd
  apply hm_not (Nat.primeFactorsList m).length
  exact Nat.eq_prime_pow_of_unique_prime_dvd hm0 h'

set_option maxHeartbeats 1000000 in
public theorem CFSG.theorem_2_6_b
    {F : Type*} [Field F]
    {G : Type*} [Group G] (ho : Odd (Nat.card G))
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (hdim : Module.finrank F V = 2)
    {ρ : Representation F G V} (hi : Function.Injective ρ) :
    ∃ C : Sylow (ringChar F) G, IsMulCommutative C ∧ commutator G ≤ C := by
  let := card_odd_finite ho

  -- Induction on Nat.card G
  suffices ∀ n, Nat.card G = n → ∃ C : Sylow (ringChar F) G, IsMulCommutative C ∧ commutator G ≤ C by exact this _ rfl
  intro n hc
  induction n using Nat.strong_induction_on generalizing G V with | h n ih =>

  -- Nat.card G = 0
  rcases n with _ | n
  · contrapose! hc; exact ne_zero_of_lt Nat.card_pos

  rcases n with _ | n
  -- Nat.card G = 1
  · rw [zero_add] at hc
    have (H : Subgroup G) : H = ⊥ := by
        rw [← Subgroup.card_le_one_iff_eq_bot, ← hc]
        exact Subgroup.card_le_card_group _
    use ⟨⊥, IsPGroup.of_bot, fun a b ↦ this _⟩
    constructor
    · rw [← Subgroup.le_centralizer_iff_isMulCommutative]
      exact Subgroup.le_centralizer ⊥
    · rw [this (commutator G)]
  -- Genuine induction
  · rw [add_assoc, one_add_one_eq_two] at hc ih

    -- Working on algebraic closed fields
    have hdim0 := hdim
    have hi0 := hi
    let F' := AlgebraicClosure F
    let V' := F' ⊗[F] V
    let ρ' := extendScalars F' ρ
    have hdim : Module.finrank F' V' = 2 := hdim.symm ▸ finrank_baseChange
    have hi : Function.Injective ρ' := (extendScalars_faithful_iff F' ρ).mp hi
    let Gs : Subgroup G := {
      carrier := { g | LinearMap.det (ρ' g) = 1}
      mul_mem' := by
        intro g h hg hh
        simp only [Set.mem_ofPred_eq] at hg hh ⊢
        rw [map_mul, Module.End.mul_eq_comp, LinearMap.det_comp, hg, hh, one_mul]
      one_mem' := by simp only [Set.mem_ofPred_eq, map_one]
      inv_mem' := by
        intro g hg
        simp only [Set.mem_ofPred_eq] at hg ⊢
        have : LinearMap.det (ρ' g) * LinearMap.det (ρ' g⁻¹) = 1 := by
          rw [← LinearMap.det_comp, ← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one, Module.End.one_eq_id, LinearMap.det_id]
        rw [← this, hg, one_mul]
    } -- The subgroup G* := G ⋂ SL(V, F)
    have hGs : Gs.Normal := {
      conj_mem := by
        intro s hs g
        simp only [Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_ofPred_eq, Gs] at hs
        simp only [Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_ofPred_eq, map_mul, hs, mul_one, Gs]
        rw [← LinearMap.det_comp, ← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one, map_one]
    }
    by_cases! hGs : Gs = ⊥
    -- G* = ⊥
    · have h : Subgroup.center G = ⊤ := by
        apply le_antisymm; exact Subgroup.toSubmonoid_le.mp fun _ _ ↦ trivial
        intro h _
        rw [Subgroup.mem_center_iff]
        intro g
        suffices g * h * g⁻¹ * h⁻¹ = 1 by
          have : g * h * g⁻¹ * h⁻¹ * h * g = h * g := by
            rw [this, one_mul]
          rw [← this]
          group
        have : LinearMap.det (ρ' (g * h * g⁻¹ * h⁻¹)) = 1 := by calc
          LinearMap.det (ρ' (g * h * g⁻¹ * h⁻¹)) = LinearMap.det (ρ' g) * LinearMap.det (ρ' h) * LinearMap.det (ρ' g⁻¹) * LinearMap.det (ρ' h⁻¹) := by simp only [map_mul, Module.End.mul_eq_comp, LinearMap.det_comp]
          _ = LinearMap.det (ρ' g) * LinearMap.det (ρ' g⁻¹) * LinearMap.det (ρ' h) * LinearMap.det (ρ' h⁻¹) := by field
          _ = 1 := by simp only [← map_mul, mul_inv_cancel, map_one, one_mul]
        exact Subgroup.mem_bot.mp <| hGs ▸ this
      let c : CommGroup G := {
        mul_comm a b := by
          have : b ∈ (⊤ : Subgroup G) := Subgroup.mem_top b
          rw [← h, Subgroup.mem_center_iff] at this
          exact this a
      }
      let C : Sylow (ringChar F) G := Classical.choice inferInstance
      use C
      constructor
      · infer_instance
      · rw [(commutator_eq_bot_iff_center_eq_top G).mpr h]
        exact bot_le

    -- G* ≠ ⊥
    have hq : ∃ q : ℕ , q.Prime ∧ pCore q Gs ≠ ⊥ := by
      have hap (N : Subgroup Gs) (hne : N ≠ ⊥) : ∃ q : ℕ, q.Prime ∧ pCore q N ≠ ⊥ := by
        have hoGs : Odd (Nat.card Gs) := Odd.of_dvd_nat ho Gs.card_subgroup_dvd_card
        have hoN : Odd (Nat.card N) := Odd.of_dvd_nat hoGs N.card_subgroup_dvd_card
        suffices ∀ m, Nat.card N = m → ∃ q, Nat.Prime q ∧ pCore q N ≠ ⊥ by
          exact this _ rfl
        intro m hcardN
        induction m using Nat.strong_induction_on generalizing N with | h m ihN =>
        by_cases! hpow : ∃ n : ℕ, Nat.card N = (ringChar F) ^ n
        · obtain ⟨n, hn⟩ := hpow
          have hN1 : Nat.card N > 1 := (Subgroup.one_lt_card_iff_ne_bot N).mpr hne
          use ringChar F, (ringChar_prime (by by_contra; rw [this] at hn; rw [hn] at hN1; contrapose! hN1; exact zero_pow_le_one n)).out
          unfold pCore
          rw [ne_eq, sSup_eq_bot.not]
          simp only [Set.mem_ofPred_eq, and_imp, not_forall]
          have : Nat.card (⊤ : Subgroup N) = Nat.card N := Subgroup.card_top
          use ⊤, { conj_mem := fun n a g ↦ a }, IsPGroup.of_card (this ▸ hn)
          have := (Subgroup.nontrivial_iff_ne_bot N).mpr hne
          exact top_ne_bot
        · have hNcard_ne_zero : Nat.card N ≠ 0 := Nat.card_pos.ne'
          have hnotpow : ∀ n : ℕ, Nat.card N ≠ (ringChar F) ^ n := by
            intro n hn
            exact hpow n hn
          obtain ⟨q, hq_prime, hq_dvd, hq_ne_char⟩ :=
            exists_prime_dvd_ne_of_not_prime_power_bg hNcard_ne_zero hnotpow
          have : Fact q.Prime := ⟨hq_prime⟩
          let Q : Sylow q N := Classical.choice Sylow.nonempty
          by_cases hnormQ : Subgroup.normalizer (Q : Set N) = ⊤
          · have hQ_normal : (Q : Subgroup N).Normal := Subgroup.normalizer_eq_top_iff.mp hnormQ
            have hQ_le_pCore : (Q : Subgroup N) ≤ pCore q N := le_sSup ⟨hQ_normal, Q.isPGroup'⟩
            have hQ_ne_bot : (Q : Subgroup N) ≠ ⊥ := Sylow.ne_bot_of_dvd_card Q hq_dvd
            refine ⟨q, hq_prime, ?_⟩
            intro hbot
            apply hQ_ne_bot
            exact le_bot_iff.mp (by simpa [hbot] using hQ_le_pCore)
          · let H : Subgroup N := Subgroup.normalizer (Q : Set N)
            have hQ_le_H : (Q : Subgroup N) ≤ H := by
              simpa [H] using (Subgroup.le_normalizer (H := (Q : Subgroup N)))
            have hH_ne_top : H ≠ ⊤ := by
              simpa [H] using hnormQ
            have hcardH_lt : Nat.card H < Nat.card N := by
              have hx : ∃ x : N, x ∉ H := by
                by_contra hno
                have hall : ∀ x : N, x ∈ H := by
                  intro x
                  by_contra hx
                  exact hno ⟨x, hx⟩
                have hH_top : H = ⊤ := by
                  ext x
                  constructor
                  · intro _; simp
                  · intro _; exact hall x
                exact hH_ne_top hH_top
              rcases hx with ⟨x, hx⟩
              simpa [H] using (Finite.card_subtype_lt (p := fun h : N => h ∈ H) hx)
            have hoH : Odd (Nat.card H) := Odd.of_dvd_nat hoN H.card_subgroup_dvd_card
            let ρH : Representation F H V := ρ.comp (Gs.subtype.comp (N.subtype.comp H.subtype))
            have hiH : Function.Injective ρH := by
              intro x y hxy
              repeat' apply Subtype.ext
              exact hi0 (by simpa [ρH] using hxy)
            have hcardH_lt_G : Nat.card H < Nat.card G := by
              exact lt_of_lt_of_le hcardH_lt
                (le_trans (Subgroup.card_le_card_group N) (Subgroup.card_le_card_group Gs))
            obtain ⟨C, hCcomm, hcomm_le_C⟩ :=
              ih (Nat.card H) (by simpa [hc] using hcardH_lt_G)
                (G := H) hoH (V := V) hdim0 (ρ := ρH) hiH rfl
            let QH : Subgroup H := (Q : Subgroup N).subgroupOf H
            have hQH_normal : QH.Normal := by
              rw [Subgroup.normal_subgroupOf_iff_le_normalizer hQ_le_H]
              change Subgroup.normalizer ((Q : Subgroup N) : Set N) ≤
                Subgroup.normalizer (((Q : Subgroup N) : Set N))
              exact le_rfl
            have hQH_p : IsPGroup q QH := by
              simpa [QH] using
                Q.isPGroup'.of_equiv
                  (Subgroup.subgroupOfEquivOfLe (H := (Q : Subgroup N)) (K := H) hQ_le_H).symm
            have hQH_center : QH ≤ Subgroup.center H := by
              by_cases hchar0 : ringChar F = 0
              · intro x hx
                rw [Subgroup.mem_center_iff]
                intro y
                have htop : (C : Subgroup H) = ⊤ := by
                  simpa using (top_eq_sylow_zero hchar0 C).symm
                rw [htop] at hCcomm
                exact setLike_mul_comm (s := (⊤ : Subgroup H)) trivial trivial
              · have : Fact (Nat.Prime (ringChar F)) := ringChar_prime hchar0
                have hQH_disj_C : Disjoint QH (C : Subgroup H) :=
                  IsPGroup.disjoint_of_ne q (ringChar F) hq_ne_char QH (C : Subgroup H) hQH_p C.isPGroup'
                intro x hx
                rw [Subgroup.mem_center_iff]
                intro y
                have hxy_left : ⁅x, y⁆ ∈ QH := by
                  exact
                    (Subgroup.commutator_le_left (H₁ := QH) (H₂ := (⊤ : Subgroup H)))
                      (Subgroup.commutator_mem_commutator hx (by simp))
                have hxy_comm : ⁅x, y⁆ ∈ commutator H := by
                  have hle : ⁅QH, (⊤ : Subgroup H)⁆ ≤ commutator H := by
                    rw [commutator_def]
                    exact Subgroup.commutator_mono (show QH ≤ (⊤ : Subgroup H) by simp) le_rfl
                  exact hle (Subgroup.commutator_mem_commutator hx (by simp))
                have hxy_right : ⁅x, y⁆ ∈ (C : Subgroup H) := hcomm_le_C hxy_comm
                have hxy_bot : ⁅x, y⁆ ∈ (⊥ : Subgroup H) := by
                  simpa [hQH_disj_C.eq_bot] using
                    show ⁅x, y⁆ ∈ QH ⊓ (C : Subgroup H) from ⟨hxy_left, hxy_right⟩
                have hxy_one : ⁅x, y⁆ = (1 : H) := by simpa using hxy_bot
                have hxy_mul : x * y = y * x := by
                  rwa [commutatorElement_eq_one_iff_mul_comm] at hxy_one
                exact hxy_mul.symm
            have hQ_center : (Q : Subgroup N) ≤ centerIn (G := N) H := by
              intro x hx
              constructor
              · exact hQ_le_H hx
              · change x ∈ Subgroup.centralizer (H : Set N)
                rw [Subgroup.mem_centralizer_iff]
                intro y hy
                let xH : H := ⟨x, hQ_le_H hx⟩
                let yH : H := ⟨y, hy⟩
                have hxH : xH ∈ QH := hx
                exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp (hQH_center hxH)) yH)
            obtain ⟨M, hM_normal, hM_cop, hNmodM_q⟩ :=
              exists_normal_coprime_subgroup_and_pgroup_quotient_of_sylow_le_center_normalizer q Q hQ_center
            have hM_ne_top : M ≠ ⊤ := by
              intro hM_top
              have hcop : Nat.Coprime q (Nat.card N) := by
                simpa [hM_top] using hM_cop
              exact (Nat.Prime.coprime_iff_not_dvd hq_prime).mp hcop hq_dvd
            have hM_ne_bot : M ≠ ⊥ := by
              intro hM_bot
              let e : N ⧸ M ≃* N := (QuotientGroup.quotientMulEquivOfEq hM_bot).trans QuotientGroup.quotientBot
              have hN_q : IsPGroup q N := hNmodM_q.of_equiv e
              have hQ_normal : (Q : Subgroup N).Normal :=
                Group.IsNilpotent.sylow_normal hN_q.isNilpotent q Q
              have hnormQ_top : Subgroup.normalizer (Q : Set N) = ⊤ :=
                Subgroup.normalizer_eq_top_iff.mpr hQ_normal
              exact hnormQ hnormQ_top
            have hcardM_lt : Nat.card M < Nat.card N := by
              have hx : ∃ x : N, x ∉ M := by
                by_contra hno
                have hall : ∀ x : N, x ∈ M := by
                  intro x
                  by_contra hx
                  exact hno ⟨x, hx⟩
                have hM_top : M = ⊤ := by
                  ext x
                  constructor
                  · intro _; simp
                  · intro _; exact hall x
                exact hM_ne_top hM_top
              rcases hx with ⟨x, hx⟩
              simpa using (Finite.card_subtype_lt (p := fun h : N => h ∈ M) hx)
            let M' : Subgroup Gs := M.map N.subtype
            have hM'_ne_bot : M' ≠ ⊥ := by
              intro hM'_bot
              apply hM_ne_bot
              exact
                (Subgroup.map_eq_bot_iff_of_injective (H := M) (f := N.subtype)
                  N.subtype_injective).mp hM'_bot
            have hcardM'_eq : Nat.card M' = Nat.card M := by
              simpa [M'] using
                (Subgroup.card_map_of_injective (K := M) (f := N.subtype) N.subtype_injective)
            have hcardM'_lt : Nat.card M' < Nat.card N := by
              rw [hcardM'_eq]
              exact hcardM_lt
            have hoM' : Odd (Nat.card M') := by
              rw [hcardM'_eq]
              exact Odd.of_dvd_nat hoN M.card_subgroup_dvd_card
            obtain ⟨r, hr_prime, hr_core⟩ :=
              ihN (Nat.card M') (by simpa [hcardN] using hcardM'_lt) M' hM'_ne_bot hoM' rfl
            have : Fact r.Prime := ⟨hr_prime⟩
            let e : M ≃* M' := M.equivMapOfInjective N.subtype N.subtype_injective
            have hpCore_map : (pCore r M).map e.toMonoidHom = pCore r M' := by
              simpa using (pCore_map_iso (G := M) (G' := M') (p := r) (f := e))
            have hr_core_M : pCore r M ≠ ⊥ := by
              intro hbot
              have hmap_bot : (pCore r M).map e.toMonoidHom = ⊥ := by
                simp [hbot]
              rw [hpCore_map] at hmap_bot
              exact hr_core hmap_bot
            have hcoreM_normal : ((pCore r M).map M.subtype).Normal := by
              let : M.Normal := hM_normal
              let : (pCore r M).Characteristic := pCore_characteristic (G := M) (p := r)
              exact ConjAct.normal_of_characteristic_of_normal
            have hcoreM_p : IsPGroup r ((pCore r M).map M.subtype) := by
              exact IsPGroup.map (p := r) (H := pCore r M) (pCore_isPGroup (p := r) (G := M))
                M.subtype
            have hcoreM_le : ((pCore r M).map M.subtype) ≤ pCore r N := le_sSup ⟨hcoreM_normal, hcoreM_p⟩
            have hcoreM_ne_bot : ((pCore r M).map M.subtype) ≠ ⊥ := by
              intro hbot
              exact hr_core_M <|
                (Subgroup.map_eq_bot_iff_of_injective (H := pCore r M) (f := M.subtype)
                  M.subtype_injective).mp hbot
            refine ⟨r, hr_prime, ?_⟩
            intro hbot
            apply hcoreM_ne_bot
            exact le_bot_iff.mp (by simpa [hbot] using hcoreM_le)
      have := (Subgroup.nontrivial_iff_ne_bot Gs).mpr hGs
      obtain ⟨q, hq1, hq2⟩ := hap ⊤ top_ne_bot
      use q, hq1
      unfold pCore at hq2 ⊢
      contrapose hq2
      rw [sSup_eq_bot] at hq2 ⊢
      intro K hK
      have := hq2 (K.map (⊤ : Subgroup Gs).subtype) (by
        constructor
        · apply Subgroup.Normal.map
          · exact hK.1
          · exact fun x ↦ ⟨⟨x, Subgroup.mem_top x⟩, (Subgroup.inclusion_inj fun ⦃x⦄ a ↦ a).mp rfl⟩
        · exact IsPGroup.map hK.2 _)
      rw [Subgroup.map_eq_bot_iff_of_injective] at this
      · exact this
      · exact Subgroup.subtype_injective ⊤
    obtain ⟨q, hq1, hq2⟩ := hq
    let qC := (pCore q Gs).map Gs.subtype
    let K : Subgroup G := {
      carrier := {g : G | g ∈ qC ∧ (∀ h ∈ qC, g * h = h * g) ∧ g ^ q = 1}
      mul_mem' := by
        intro g₁ g₂ hg₁ hg₂
        refine ⟨(Subgroup.mul_mem_cancel_left qC hg₁.1).mpr hg₂.1, ?_ , ?_⟩
        · intro h hh
          rw [mul_assoc, hg₂.2.1 h hh, ← mul_assoc, hg₁.2.1 h hh, mul_assoc]
        · have : Commute g₁ g₂ := by rw [commute_iff_eq, hg₁.2.1 g₂ hg₂.1]
          rw [Commute.mul_pow this, hg₁.2.2, hg₂.2.2, one_mul]
      one_mem' := by simp only [Set.mem_ofPred_eq, one_mem, one_mul, mul_one, one_pow, and_self, implies_true]
      inv_mem' := by
        intro g hg
        refine ⟨Subgroup.inv_mem qC hg.1, ?_, ?_⟩
        · intro h hh
          rw [← commute_iff_eq, Commute.inv_left_iff, commute_iff_eq, hg.2.1 h hh]
        · rw [inv_pow, hg.2.2, inv_one]
    }
    have hK1 : IsElementaryAbelian q K := {
      toIsMulCommutative := {
        is_comm := {
          comm k₁ k₂ := SetLike.coe_eq_coe.mp (k₁.2.2.1 k₂ k₂.2.1)
        }
      }
      exponent_dvd_p := by
        rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
        intro k
        exact SetLike.coe_eq_coe.mp k.2.2.2
    }
    have hqC : qC.Normal := by
      have : (pCore q Gs).Characteristic := pCore_characteristic (G := Gs) (p := q)
      exact ConjAct.normal_of_characteristic_of_normal
    have hK2 : K.Normal := {
      conj_mem := by
        intro k hk g
        refine ⟨Subgroup.Normal.conj_mem hqC k hk.1 g, ?_, ?_⟩
        · intro h hh
          rw [← mul_left_inj (a := g)]
          calc
          g * k * g⁻¹ * h * g = g * (k * (g⁻¹ * h * g)) := by group
          _ = g * ((g⁻¹ * h * g) * k) := by rw [hk.2.1 _ (Subgroup.Normal.conj_mem' hqC h hh g)]
          _ = _ := by group
        · rw [conj_pow, hk.2.2, mul_one, mul_inv_cancel]
    }
    by_cases! h : q = ringChar F
    · have : Fact q.Prime := ⟨hq1⟩
      have hqC_p : IsPGroup q qC := by
        dsimp [qC]
        exact IsPGroup.map (p := q) (H := pCore q Gs) (pCore_isPGroup (p := q) (G := Gs))
          Gs.subtype
      have hqC_ne : qC ≠ ⊥ := by
        intro hbot
        exact hq2 <|
          (Subgroup.map_eq_bot_iff_of_injective (H := pCore q Gs) (f := Gs.subtype)
            Gs.subtype_injective).mp (by simpa [qC] using hbot)
      have hqC_le_Gs : qC ≤ Gs := by
        intro y hy
        rcases Subgroup.mem_map.mp hy with ⟨z, hz, rfl⟩
        simp
      obtain ⟨x, hxqC, hxord, hxcent, hxpow, hxne1⟩ :=
        exists_central_element_orderOf_eq_prime_of_nontrivial_pgroup_subgroup qC hqC_p hqC_ne
      have hxK : x ∈ K := ⟨hxqC, hxcent, hxpow⟩
      have hchar0 : ringChar F ≠ 0 := by
        intro h0
        have : q = 0 := by simpa [h] using h0
        exact hq1.ne_zero this
      have hchar0' : ringChar F' ≠ 0 := by
        simpa [Algebra.ringChar_eq F F'] using hchar0
      have : CharP F q := by
        rw [CharP.charP_iff_prime_eq_zero hq1, h, ringChar.Nat.cast_ringChar]
      have : CharP F' q :=
        CharP.of_ringHom_of_ne_zero (algebraMap F F') q hq1.ne_zero
      have : ExpChar F' q := ExpChar.prime hq1
      let : Fact (Module.finrank F' V' = 2) := ⟨hdim⟩
      let : FiniteDimensional F' V' := FiniteDimensional.of_fact_finrank_eq_two
      let : Nontrivial V' := nontrivial_of_finrank_eq_two hdim
      let sigma : Representation F' K V' := ρ'.comp K.subtype
      have hKp : IsPGroup (ringChar F') K := by
        simpa [h, Algebra.ringChar_eq F F'] using (IsElementaryAbelian.isPGroup q K)
      obtain ⟨v, hv0, hvfix⟩ := pGroup_fix_nonzero_vector (F := F') (G := K) hchar0' hKp sigma
      let U : Submodule F' V' := Representation.invariants sigma
      have hvU : v ∈ U := by
        exact (Representation.mem_invariants (ρ := sigma) v).2 hvfix
      have hU_ne_bot : U ≠ ⊥ := by
        intro hUbot
        have : v = 0 := by simpa [U, hUbot] using hvU
        exact hv0 this
      let xK : K := ⟨x, hxK⟩
      have hU_ne_top : U ≠ ⊤ := by
        intro hUtop
        have hxid : ρ' x = LinearMap.id := by
          refine LinearMap.ext fun w : V' => ?_
          have hwU : w ∈ U := by
            simp [U, hUtop]
          have hwfix : sigma xK w = w :=
            (Representation.mem_invariants (ρ := sigma) w).1 hwU xK
          simpa [sigma] using hwfix
        have hxeq : ρ' x = ρ' 1 := by
          calc
            ρ' x = LinearMap.id := hxid
            _ = ρ' 1 := by
              change (1 : Module.End F' V') = ρ' 1
              simp
        exact hxne1 (hi hxeq)
      have hU_pos : 0 < Module.finrank F' U := by
        let : Nontrivial U := (Submodule.nontrivial_iff_ne_bot).2 hU_ne_bot
        exact Module.finrank_pos (R := F') (M := U)
      have hU_lt : Module.finrank F' U < 2 := by
        simpa [hdim] using (Submodule.finrank_lt (K := F') (V := V') hU_ne_top)
      have hU1 : Module.finrank F' U = 1 := by
        omega
      have hU_stable (g : G) : U ≤ U.comap (ρ' g) := by
        intro u hu
        have hu_inv : ∀ k : K, sigma k u = u := by
          exact (Representation.mem_invariants (ρ := sigma) u).1 (by simpa [U] using hu)
        change ρ' g u ∈ U
        rw [show U = Representation.invariants sigma by rfl, Representation.mem_invariants]
        intro k
        let kg : K := ⟨g⁻¹ * (k : G) * g, Subgroup.Normal.conj_mem' hK2 k k.2 g⟩
        have hku : sigma kg u = u := hu_inv kg
        have hmul : (k : G) * g = g * (kg : K) := by
          change k.1 * g = g * (g⁻¹ * k.1 * g)
          group
        calc
          ρ' k (ρ' g u) = ρ' (k * g) u := by simp [map_mul, Module.End.mul_eq_comp]
          _ = ρ' (g * kg) u := by rw [hmul]
          _ = ρ' g (ρ' kg u) := by simp [map_mul, Module.End.mul_eq_comp]
          _ = ρ' g u := by simpa [sigma] using congrArg (fun z : V' => ρ' g z) hku
      let rhoU : Representation F' G U := Representation.subrepresentation ρ' U hU_stable
      let rhoQ : Representation F' G (V' ⧸ U) := Representation.quotient ρ' U hU_stable
      let : Module.Free F' U := Module.Free.of_divisionRing F' U
      let : Module.Free F' (V' ⧸ U) := Module.Free.of_divisionRing F' (V' ⧸ U)
      have hQ1 : Module.finrank F' (V' ⧸ U) = 1 := by
        have hsum := Submodule.finrank_quotient_add_finrank (R := F') (M := V') U
        omega
      have hU_data (g : G) :
          ∃ a : F', (∀ u : U, rhoU g u = a • u) ∧ LinearMap.det (rhoU g) = a := by
        obtain ⟨a, ha, _⟩ :=
          LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hU1 (rhoU g)
        refine ⟨a, ?_, ?_⟩
        · intro u
          simpa using congrArg (fun f : Module.End F' U => f u) ha
        · rw [ha, LinearMap.det_smul, LinearMap.det_id, hU1, pow_one, mul_one]
      have hQ_data (g : G) :
          ∃ a : F', (∀ z : V' ⧸ U, rhoQ g z = a • z) ∧ LinearMap.det (rhoQ g) = a := by
        obtain ⟨a, ha, _⟩ :=
          LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hQ1 (rhoQ g)
        refine ⟨a, ?_, ?_⟩
        · intro z
          simpa using congrArg (fun f : Module.End F' (V' ⧸ U) => f z) ha
        · rw [ha, LinearMap.det_smul, LinearMap.det_id, hQ1, pow_one, mul_one]
      have hmulU_comm (g1 g2 : G) : rhoU g1 * rhoU g2 = rhoU g2 * rhoU g1 := by
        refine LinearMap.ext fun u : U => ?_
        obtain ⟨a1, ha1, -⟩ := hU_data g1
        obtain ⟨a2, ha2, -⟩ := hU_data g2
        calc
          (rhoU g1 * rhoU g2) u = rhoU g1 (rhoU g2 u) := rfl
          _ = rhoU g1 (a2 • u) := by rw [ha2 u]
          _ = a2 • rhoU g1 u := by rw [map_smul]
          _ = a2 • (a1 • u) := by rw [ha1 u]
          _ = (a2 * a1) • u := by rw [smul_smul]
          _ = (a1 * a2) • u := by rw [mul_comm]
          _ = a1 • (a2 • u) := by rw [smul_smul]
          _ = a1 • rhoU g2 u := by rw [ha2 u]
          _ = rhoU g2 (a1 • u) := by rw [map_smul]
          _ = rhoU g2 (rhoU g1 u) := by rw [ha1 u]
          _ = (rhoU g2 * rhoU g1) u := rfl
      have hmulQ_comm (g1 g2 : G) : rhoQ g1 * rhoQ g2 = rhoQ g2 * rhoQ g1 := by
        refine LinearMap.ext fun z : V' ⧸ U => ?_
        obtain ⟨a1, ha1, -⟩ := hQ_data g1
        obtain ⟨a2, ha2, -⟩ := hQ_data g2
        calc
          (rhoQ g1 * rhoQ g2) z = rhoQ g1 (rhoQ g2 z) := rfl
          _ = rhoQ g1 (a2 • z) := by rw [ha2 z]
          _ = a2 • rhoQ g1 z := by rw [map_smul]
          _ = a2 • (a1 • z) := by rw [ha1 z]
          _ = (a2 * a1) • z := by rw [smul_smul]
          _ = (a1 * a2) • z := by rw [mul_comm]
          _ = a1 • (a2 • z) := by rw [smul_smul]
          _ = a1 • rhoQ g2 z := by rw [ha2 z]
          _ = rhoQ g2 (a1 • z) := by rw [map_smul]
          _ = rhoQ g2 (rhoQ g1 z) := by rw [ha1 z]
          _ = (rhoQ g2 * rhoQ g1) z := rfl
      have hcomm_le_ker_U : commutator G ≤ rhoU.ker := by
        rw [commutator_eq_closure, Subgroup.closure_le]
        rintro c ⟨g1, g2, rfl⟩
        change rhoU (g1 * g2 * g1⁻¹ * g2⁻¹) = 1
        have hcomm' : rhoU g2 * rhoU g1⁻¹ = rhoU g1⁻¹ * rhoU g2 := by
          calc
            rhoU g2 * rhoU g1⁻¹ = rhoU (g2 * g1⁻¹) := (map_mul rhoU g2 g1⁻¹).symm
            _ = rhoU (g1⁻¹ * g2) := by
              have := hmulU_comm g2 g1⁻¹
              simpa [map_mul] using this
            _ = rhoU g1⁻¹ * rhoU g2 := map_mul rhoU g1⁻¹ g2
        have hg1 : rhoU g1 * rhoU g1⁻¹ = 1 := by
          calc
            rhoU g1 * rhoU g1⁻¹ = rhoU (g1 * g1⁻¹) := (map_mul rhoU g1 g1⁻¹).symm
            _ = 1 := by simp
        have hg2 : rhoU g2 * rhoU g2⁻¹ = 1 := by
          calc
            rhoU g2 * rhoU g2⁻¹ = rhoU (g2 * g2⁻¹) := (map_mul rhoU g2 g2⁻¹).symm
            _ = 1 := by simp
        calc
          rhoU (g1 * g2 * g1⁻¹ * g2⁻¹) = rhoU g1 * (rhoU g2 * rhoU g1⁻¹) * rhoU g2⁻¹ := by
            simp [map_mul, mul_assoc]
          _ = rhoU g1 * (rhoU g1⁻¹ * rhoU g2) * rhoU g2⁻¹ := by rw [hcomm']
          _ = (rhoU g1 * rhoU g1⁻¹) * (rhoU g2 * rhoU g2⁻¹) := by
            simp [mul_assoc]
          _ = 1 := by simp [hg1, hg2]
      have hcomm_le_ker_Q : commutator G ≤ rhoQ.ker := by
        rw [commutator_eq_closure, Subgroup.closure_le]
        rintro c ⟨g1, g2, rfl⟩
        change rhoQ (g1 * g2 * g1⁻¹ * g2⁻¹) = 1
        have hcomm' : rhoQ g2 * rhoQ g1⁻¹ = rhoQ g1⁻¹ * rhoQ g2 := by
          calc
            rhoQ g2 * rhoQ g1⁻¹ = rhoQ (g2 * g1⁻¹) := (map_mul rhoQ g2 g1⁻¹).symm
            _ = rhoQ (g1⁻¹ * g2) := by
              have := hmulQ_comm g2 g1⁻¹
              simpa [map_mul] using this
            _ = rhoQ g1⁻¹ * rhoQ g2 := map_mul rhoQ g1⁻¹ g2
        have hg1 : rhoQ g1 * rhoQ g1⁻¹ = 1 := by
          calc
            rhoQ g1 * rhoQ g1⁻¹ = rhoQ (g1 * g1⁻¹) := (map_mul rhoQ g1 g1⁻¹).symm
            _ = 1 := by simp
        have hg2 : rhoQ g2 * rhoQ g2⁻¹ = 1 := by
          calc
            rhoQ g2 * rhoQ g2⁻¹ = rhoQ (g2 * g2⁻¹) := (map_mul rhoQ g2 g2⁻¹).symm
            _ = 1 := by simp
        calc
          rhoQ (g1 * g2 * g1⁻¹ * g2⁻¹) = rhoQ g1 * (rhoQ g2 * rhoQ g1⁻¹) * rhoQ g2⁻¹ := by
            simp [map_mul, mul_assoc]
          _ = rhoQ g1 * (rhoQ g1⁻¹ * rhoQ g2) * rhoQ g2⁻¹ := by rw [hcomm']
          _ = (rhoQ g1 * rhoQ g1⁻¹) * (rhoQ g2 * rhoQ g2⁻¹) := by
            simp [mul_assoc]
          _ = 1 := by simp [hg1, hg2]
      have hcomm_fix_U (c : G) (hc : c ∈ commutator G) : ∀ u : U, ρ' c u = u := by
        have hcU : rhoU c = 1 := MonoidHom.mem_ker.mp (hcomm_le_ker_U hc)
        intro u
        exact congrArg Subtype.val (congrArg (fun f : Module.End F' U => f u) hcU)
      have hcomm_fix_Q (c : G) (hc : c ∈ commutator G) : ∀ z : V' ⧸ U, rhoQ c z = z := by
        have hcQ : rhoQ c = 1 := MonoidHom.mem_ker.mp (hcomm_le_ker_Q hc)
        intro z
        simpa using congrArg (fun f : Module.End F' (V' ⧸ U) => f z) hcQ
      let : CharP (Module.End F' V') q := by
        refine Module.charP_end (R := F') (M := V') (p := q) ?_
        obtain ⟨w, hw⟩ := exists_ne (0 : V')
        refine ⟨w, ?_⟩
        rw [Ideal.torsionOf_eq_bot_iff_of_noZeroSMulDivisors]
        exact hw
      have : ExpChar (Module.End F' V') q := ExpChar.prime hq1
      have hcomm_qpow : ∀ c ∈ commutator G, c ^ q = 1 := by
        intro c hc
        obtain ⟨W, hcomplUW⟩ := exists_isCompl U
        let e : Module.End F' V' := ρ' c - 1
        have heU : ∀ u : U, e u = 0 := by
          intro u
          dsimp [e]
          rw [hcomm_fix_U c hc u, sub_self]
        have heW : ∀ w : W, e w ∈ U := by
          intro w
          have hq : rhoQ c (Submodule.Quotient.mk (w : V')) = Submodule.Quotient.mk (w : V') :=
            hcomm_fix_Q c hc (Submodule.Quotient.mk (w : V'))
          change Submodule.Quotient.mk ((ρ' c) w) = Submodule.Quotient.mk (w : V') at hq
          simpa [e] using (Submodule.Quotient.eq U).mp hq
        have he2 : e ^ 2 = 0 := by
          apply linearMap_eq_of_isCompl_of_eq_on_each (e := e ^ 2) (f := 0) (φ := U) (ψ := W) hcomplUW
          · intro u
            change e (e u) = 0
            rw [heU u, map_zero]
          · intro w
            change e (e w) = 0
            exact heU ⟨e w, heW w⟩
        have heq : e ^ q = 0 := pow_eq_zero_of_le hq1.two_le he2
        have hsub : (ρ' c) ^ q - 1 = 0 := by
          calc
            (ρ' c) ^ q - 1 = e ^ q := by
              symm
              simpa [e] using
                (sub_pow_expChar_of_commute (R := Module.End F' V') (p := q)
                  (x := ρ' c) (y := 1) (Commute.one_right _))
            _ = 0 := heq
        have hpow : (ρ' c) ^ q = 1 := sub_eq_zero.mp hsub
        apply hi
        calc
          ρ' (c ^ q) = (ρ' c) ^ q := map_pow ρ' c q
          _ = 1 := hpow
          _ = ρ' 1 := (map_one ρ').symm
      have hcomm_p : IsPGroup q (commutator G) := by
        apply isPGroup_of_prime_order_eq_p q (H := commutator G)
        intro x hxprime
        have hxpow : (x : G) ^ q = 1 := hcomm_qpow x x.2
        have hxdvdG : orderOf (x : G) ∣ q := orderOf_dvd_of_pow_eq_one hxpow
        have hxdvd : orderOf x ∣ q := by
          simpa using hxdvdG
        exact (Nat.prime_dvd_prime_iff_eq hxprime hq1).mp hxdvd
      obtain ⟨C, hcomm_le_C⟩ := IsPGroup.exists_le_sylow (p := q) hcomm_p
      have hscalar_eq_one {a : F'} {m : ℕ} (ha : a ^ q ^ m = 1) : a = 1 := by
        have hpow0 : (a - 1) ^ q ^ m = 0 := by
          calc
            (a - 1) ^ q ^ m = a ^ q ^ m - 1 ^ q ^ m := by
              simpa using
                (sub_pow_expChar_pow_of_commute (p := q) (x := a) (y := (1 : F')) (n := m)
                  (Commute.one_right _))
            _ = 0 := by rw [ha, one_pow, sub_self]
        have : a - 1 = 0 := eq_zero_of_pow_eq_zero hpow0
        exact sub_eq_zero.mp this
      obtain ⟨W, hcomplUW⟩ := exists_isCompl U
      have hU_fix_C (y : C) : ∀ u : U, ρ' y u = u := by
        obtain ⟨a, ha, hdet⟩ := hU_data y
        obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp C.isPGroup') y
        have hy_pow : (y : G) ^ orderOf y = 1 := by
          exact congrArg Subtype.val (pow_orderOf_eq_one y)
        have hpow : (rhoU y) ^ orderOf y = 1 := by
          calc
            (rhoU y) ^ orderOf y = rhoU ((y : G) ^ orderOf y) := by rw [← map_pow]
            _ = 1 := by rw [hy_pow, map_one]
        rw [hm] at hpow
        have hdetpow := congrArg (fun f : Module.End F' U => LinearMap.det f) hpow
        rw [map_pow, hdet] at hdetpow
        have ha1 : a = 1 := hscalar_eq_one (by simpa using hdetpow)
        intro u
        have hu : rhoU y u = u := by
          calc
            rhoU y u = a • u := ha u
            _ = u := by simp [ha1]
        change ((rhoU y u : U) : V') = (u : V')
        exact congrArg Subtype.val hu
      have hQ_fix_C (y : C) : ∀ z : V' ⧸ U, rhoQ y z = z := by
        obtain ⟨a, ha, hdet⟩ := hQ_data y
        obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp C.isPGroup') y
        have hy_pow : (y : G) ^ orderOf y = 1 := by
          exact congrArg Subtype.val (pow_orderOf_eq_one y)
        have hpow : (rhoQ y) ^ orderOf y = 1 := by
          calc
            (rhoQ y) ^ orderOf y = rhoQ ((y : G) ^ orderOf y) := by rw [← map_pow]
            _ = 1 := by rw [hy_pow, map_one]
        rw [hm] at hpow
        have hdetpow :=
          congrArg (fun f : Module.End F' (V' ⧸ U) => LinearMap.det f) hpow
        rw [map_pow, hdet] at hdetpow
        have ha1 : a = 1 := hscalar_eq_one (by simpa using hdetpow)
        intro z
        calc
          rhoQ y z = a • z := ha z
          _ = z := by simp [ha1]
      have hW_mem_C (y : C) : ∀ w : W, (ρ' y - 1) w ∈ U := by
        intro w
        have hq : rhoQ y (Submodule.Quotient.mk (w : V')) = Submodule.Quotient.mk (w : V') :=
          hQ_fix_C y (Submodule.Quotient.mk (w : V'))
        change Submodule.Quotient.mk ((ρ' y) w) = Submodule.Quotient.mk (w : V') at hq
        simpa using (Submodule.Quotient.eq U).mp hq
      have hcomm_rho_C : ∀ y z : C, ρ' (y * z) = ρ' (z * y) := by
        intro y z
        apply linearMap_eq_of_isCompl_of_eq_on_each (e := ρ' (y * z)) (f := ρ' (z * y))
          (φ := U) (ψ := W) hcomplUW
        · intro u
          calc
            ρ' (y * z) u = ρ' y (ρ' z u) := by simp [map_mul, Module.End.mul_eq_comp]
            _ = ρ' y u := by rw [hU_fix_C z u]
            _ = u := hU_fix_C y u
            _ = ρ' z u := (hU_fix_C z u).symm
            _ = ρ' z (ρ' y u) := by rw [hU_fix_C y u]
            _ = ρ' (z * y) u := by simp [map_mul, Module.End.mul_eq_comp]
        · intro w
          have hyw : (ρ' y - 1) w ∈ U := hW_mem_C y w
          have hzw : (ρ' z - 1) w ∈ U := hW_mem_C z w
          have hyU : ρ' y ((ρ' z - 1) w) = (ρ' z - 1) w := by
            exact hU_fix_C y ⟨(ρ' z - 1) w, hzw⟩
          have hzU : ρ' z ((ρ' y - 1) w) = (ρ' y - 1) w := by
            exact hU_fix_C z ⟨(ρ' y - 1) w, hyw⟩
          have hydecomp : ρ' y w = w + (ρ' y - 1) w := by
            change ρ' y w = w + (ρ' y w - w)
            exact (sub_eq_iff_eq_add').mp rfl
          have hzdecomp : ρ' z w = w + (ρ' z - 1) w := by
            change ρ' z w = w + (ρ' z w - w)
            exact (sub_eq_iff_eq_add').mp rfl
          calc
            ρ' (y * z) w = ρ' y (ρ' z w) := by simp [map_mul, Module.End.mul_eq_comp]
            _ = ρ' y (w + (ρ' z - 1) w) := by rw [hzdecomp]
            _ = ρ' y w + ρ' y ((ρ' z - 1) w) := by rw [map_add]
            _ = ρ' y w + (ρ' z - 1) w := by rw [hyU]
            _ = (w + (ρ' y - 1) w) + (ρ' z - 1) w := by rw [hydecomp]
            _ = w + (ρ' y - 1) w + (ρ' z - 1) w := by rw [add_assoc]
            _ = w + (ρ' z - 1) w + (ρ' y - 1) w := by abel
            _ = (w + (ρ' z - 1) w) + (ρ' y - 1) w := by rw [add_assoc]
            _ = ρ' z w + (ρ' y - 1) w := by rw [hzdecomp]
            _ = ρ' z w + ρ' z ((ρ' y - 1) w) := by rw [hzU]
            _ = ρ' z (w + (ρ' y - 1) w) := by rw [← map_add]
            _ = ρ' z (ρ' y w) := by rw [hydecomp]
            _ = ρ' (z * y) w := by simp [map_mul, Module.End.mul_eq_comp]
      have hCcomm : ∀ y z : C, y * z = z * y := by
        intro y z
        apply Subtype.ext
        exact hi (hcomm_rho_C y z)
      rw [← h]
      use C
      constructor
      · exact IsMulCommutative.mk <| Std.Commutative.mk hCcomm
      · exact hcomm_le_C
    · have : Fact q.Prime := ⟨hq1⟩
      have hqC_p : IsPGroup q qC := by
        dsimp [qC]
        exact IsPGroup.map (p := q) (H := pCore q Gs) (pCore_isPGroup (p := q) (G := Gs))
          Gs.subtype
      have hqC_ne : qC ≠ ⊥ := by
        intro hbot
        exact hq2 <|
          (Subgroup.map_eq_bot_iff_of_injective (H := pCore q Gs) (f := Gs.subtype)
            Gs.subtype_injective).mp (by simpa [qC] using hbot)
      have hqC_le_Gs : qC ≤ Gs := by
        intro y hy
        rcases Subgroup.mem_map.mp hy with ⟨z, hz, rfl⟩
        simp
      obtain ⟨x, hxqC, hxord, hxcent, hxpow, hxne1⟩ :=
        exists_central_element_orderOf_eq_prime_of_nontrivial_pgroup_subgroup qC hqC_p hqC_ne
      have hxK : x ∈ K := ⟨hxqC, hxcent, hxpow⟩
      let σ : Representation F' K V' := ρ'.comp K.subtype
      have hσcr : σ.IsCompletelyReducible := by
        apply Representation.isCompletelyReducible_of_ringChar_eq_zero_or_prime_coprime (ρ := σ)
        by_cases hchar0 : ringChar F = 0
        · left
          rw [← Algebra.ringChar_eq F F']
          exact hchar0
        · right
          have hprime : Nat.Prime (ringChar F) := (ringChar_prime hchar0).out
          have hprime' : Nat.Prime (ringChar F') := by
            simpa [Algebra.ringChar_eq F F'] using hprime
          refine ⟨hprime', ?_⟩
          rcases (IsElementaryAbelian.isPGroup q K).exists_card_eq with ⟨m, hm⟩
          have hnotdvd : ¬ q ∣ ringChar F' := by
            intro hdvd
            have hdvd' : q ∣ ringChar F := by
              simpa [Algebra.ringChar_eq F F'] using hdvd
            have hEq : q = ringChar F := (Nat.prime_dvd_prime_iff_eq hq1 hprime).mp hdvd'
            exact h hEq
          have hcop : Nat.Coprime (ringChar F') (q ^ m) :=
            hq1.coprime_pow_of_not_dvd (m := m) hnotdvd
          simpa [hm] using hcop
      let : ComplementedLattice (Subrepresentation σ) := by
        exact
          (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule
            (ρ := σ)).2 hσcr
      let : Fact (Module.finrank F' V' = 2) := ⟨hdim⟩
      let : FiniteDimensional F' V' := FiniteDimensional.of_fact_finrank_eq_two
      let : Nontrivial V' := nontrivial_of_finrank_eq_two hdim
      obtain ⟨φ, hφirr⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional σ
      obtain ⟨ψ, hcompl⟩ := exists_isCompl φ
      have hcompl_sub : IsCompl φ.toSubmodule ψ.toSubmodule :=
        subrepresentation_isCompl_toSubmodule hcompl
      let : IsMulCommutative K := hK1.toIsMulCommutative
      let := hφirr
      have hφ1 : Module.finrank F' φ.toSubmodule = 1 := by
        simpa using
          Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative
            (G := K) (k := F') (V := φ.toSubmodule) (ρ := φ.toRepresentation)
      have hψ1 : Module.finrank F' ψ.toSubmodule = 1 :=
        finrank_eq_one_of_isCompl_left_of_finrank_eq_two φ.toSubmodule ψ.toSubmodule hcompl_sub
          hφ1 hdim
      let xK : K := ⟨x, hxK⟩
      let : Module.Free F' φ.toSubmodule :=
        Module.Free.of_divisionRing F' φ.toSubmodule
      let : Module.Free F' ψ.toSubmodule :=
        Module.Free.of_divisionRing F' ψ.toSubmodule
      obtain ⟨a, ha, _⟩ :=
        LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hφ1 (φ.toRepresentation xK)
      obtain ⟨b, hb, _⟩ :=
        LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hψ1 (ψ.toRepresentation xK)
      have hφx : ∀ u : φ.toSubmodule, ρ' x u = a • u := by
        simpa [σ, xK] using subrepresentation_eq_smul_id_apply φ ha
      have hψx : ∀ w : ψ.toSubmodule, ρ' x w = b • w := by
        simpa [σ, xK] using subrepresentation_eq_smul_id_apply ψ hb
      have hdetφ :
          (@LinearMap.det φ.toSubmodule φ.toSubmodule.addCommGroup F'
            Field.toCommRing φ.toSubmodule.module) (φ.toRepresentation xK) = a := by
        rw [ha, LinearMap.det_smul, LinearMap.det_id, hφ1, pow_one, mul_one]
      have hdetψ :
          (@LinearMap.det ψ.toSubmodule ψ.toSubmodule.addCommGroup F'
            Field.toCommRing ψ.toSubmodule.module) (ψ.toRepresentation xK) = b := by
        rw [hb, LinearMap.det_smul, LinearMap.det_id, hψ1, pow_one, mul_one]
      have hab1 : a * b = 1 := by
        have hxGs : x ∈ Gs := hqC_le_Gs hxqC
        have hdet := det_eq_det_mul_det_of_isCompl_subrepresentation σ φ ψ hcompl_sub xK
        rw [show σ xK = ρ' x by rfl, hdetφ, hdetψ, hxGs] at hdet
        exact hdet.symm
      have hxKpow : xK ^ q = 1 := by
        ext
        exact hxpow
      have haq : a ^ q = 1 := by
        have hpow : (φ.toRepresentation xK) ^ q = 1 := by
          rw [← map_pow, hxKpow, map_one]
        have hdet :=
          congrArg (fun f : Module.End F' φ.toSubmodule => LinearMap.det f) hpow
        rw [map_pow, hdetφ] at hdet
        simpa using hdet
      have hbq : b ^ q = 1 := by
        have hpow : (ψ.toRepresentation xK) ^ q = 1 := by
          rw [← map_pow, hxKpow, map_one]
        have hdet :=
          congrArg (fun f : Module.End F' ψ.toSubmodule => LinearMap.det f) hpow
        rw [map_pow, hdetψ] at hdet
        simpa using hdet
      have hqodd : Odd q := by
        rw [← hxord]
        exact Odd.of_dvd_nat ho (orderOf_dvd_natCard x)
      have hab : a ≠ b := by
        intro habEq
        have hsq' : b ^ 2 = 1 := by
          rw [habEq] at hab1
          simpa [pow_two] using hab1
        have hsq : a ^ 2 = 1 := by
          simpa [habEq] using hsq'
        have horder2 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
        have horderq : orderOf a ∣ q := orderOf_dvd_of_pow_eq_one haq
        have hq_ne_two : q ≠ 2 := by
          intro hq2
          have : ¬ Odd 2 := by decide
          exact this (hq2 ▸ hqodd)
        have htwo_ne_q : 2 ≠ q := by
          intro h2q
          exact hq_ne_two h2q.symm
        have hcop2q : Nat.Coprime 2 q :=
          (Nat.coprime_primes Nat.prime_two hq1).2 htwo_ne_q
        have horder1 : orderOf a = 1 := Nat.eq_one_of_dvd_coprimes hcop2q horder2 horderq
        have ha1 : a = 1 := (orderOf_eq_one_iff.mp horder1)
        have hb1 : b = 1 := by rw [← habEq, ha1]
        have hxid : ρ' x = LinearMap.id := by
          apply linearMap_eq_id_of_isCompl_of_eq_id_on_each (e := ρ' x)
            (φ := φ.toSubmodule) (ψ := ψ.toSubmodule) hcompl_sub
          · intro u
            calc
              ρ' x u = a • u := hφx u
              _ = u := by simp [ha1]
          · intro w
            calc
              ρ' x w = b • w := hψx w
              _ = w := by simp [hb1]
        have hρone : ρ' 1 = LinearMap.id := by
          change ρ' 1 = (1 : Module.End F' V')
          exact map_one ρ'
        have hxeq : ρ' x = ρ' 1 := by
          calc
            ρ' x = LinearMap.id := hxid
            _ = ρ' 1 := hρone.symm
        exact hxne1 (hi hxeq)
      let U : Submodule F' V' := φ.toSubmodule
      let W : Submodule F' V' := ψ.toSubmodule
      have hU1 : Module.finrank F' U = 1 := by
        simpa [U] using hφ1
      have hW1 : Module.finrank F' W = 1 := by
        simpa [W] using hψ1
      have hcomplUW : IsCompl U W := by
        simpa [U, W] using hcompl_sub
      have hUx : ∀ u : U, ρ' x u = a • u := by
        simpa [U] using hφx
      have hWx : ∀ w : W, ρ' x w = b • w := by
        simpa [W] using hψx
      have hU_ne_bot : U ≠ ⊥ := by
        intro hUbot
        have : Module.finrank F' U = 0 := by simp [hUbot]
        omega
      have hU_ne_W : U ≠ W := by
        intro hUW
        have hdisj : Disjoint U W := hcomplUW.disjoint
        have : Disjoint U U := by simpa [hUW] using hdisj
        exact hU_ne_bot (disjoint_self.mp this)
      have hU_map_or (g : G) : U.map (ρ' g) = U ∨ U.map (ρ' g) = W := by
        let Ug : Submodule F' V' := U.map (ρ' g)
        have hUg1 : Module.finrank F' Ug = 1 := by
          let e : U ≃ₗ[F'] Ug :=
            Submodule.equivMapOfInjective (ρ' g) (representation_map_injective ρ' g) U
          exact e.finrank_eq.symm.trans hU1
        let yg : K := ⟨g⁻¹ * x * g, Subgroup.Normal.conj_mem' hK2 x hxK g⟩
        obtain ⟨c, hc, _⟩ :=
          LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hU1 (φ.toRepresentation yg)
        have hUyg : ∀ u : U, ρ' (g⁻¹ * x * g) u = c • u := by
          intro u
          exact subrepresentation_eq_smul_id_apply φ hc u
        have hUg_le_eig : Ug ≤ Module.End.eigenspace (ρ' x) c := by
          intro z hz
          rw [Module.End.mem_eigenspace_iff]
          rcases Submodule.mem_map.mp hz with ⟨u, hu, rfl⟩
          have hmul : x * g = g * (g⁻¹ * x * g) := by group
          calc
            ρ' x (ρ' g u) = ρ' (x * g) u := by simp [map_mul, Module.End.mul_eq_comp]
            _ = ρ' (g * (g⁻¹ * x * g)) u := by rw [hmul]
            _ = ρ' g (ρ' (g⁻¹ * x * g) u) := by simp [map_mul, Module.End.mul_eq_comp]
            _ = ρ' g (c • u) := by rw [hUyg ⟨u, hu⟩]
            _ = c • ρ' g u := by rw [map_smul]
        by_cases hca : c = a
        · left
          apply Submodule.eq_of_le_of_finrank_eq
          · rw [hca] at hUg_le_eig
            exact le_trans hUg_le_eig <|
              eigenspace_le_of_isCompl_of_eq_left (e := ρ' x) (φ := U) (ψ := W)
                hcomplUW hUx hWx hab
          · exact hUg1.trans hU1.symm
        · by_cases hcb : c = b
          · right
            apply Submodule.eq_of_le_of_finrank_eq
            · rw [hcb] at hUg_le_eig
              exact le_trans hUg_le_eig <|
                eigenspace_le_of_isCompl_of_eq_left (e := ρ' x) (φ := W) (ψ := U)
                  hcomplUW.symm hWx hUx hab.symm
            · exact hUg1.trans hW1.symm
          · have heig_bot : Module.End.eigenspace (ρ' x) c = ⊥ :=
              eigenspace_eq_bot_of_isCompl_of_ne_left_right (e := ρ' x) (φ := U) (ψ := W)
                hcomplUW hUx hWx hca hcb
            rw [heig_bot] at hUg_le_eig
            have hUg_bot : Ug = ⊥ := le_antisymm hUg_le_eig bot_le
            have : Module.finrank F' Ug = 0 := by simp [hUg_bot]
            omega
      have hW_map_or (g : G) : W.map (ρ' g) = U ∨ W.map (ρ' g) = W := by
        let Wg : Submodule F' V' := W.map (ρ' g)
        have hWg1 : Module.finrank F' Wg = 1 := by
          let e : W ≃ₗ[F'] Wg :=
            Submodule.equivMapOfInjective (ρ' g) (representation_map_injective ρ' g) W
          exact e.finrank_eq.symm.trans hW1
        let yg : K := ⟨g⁻¹ * x * g, Subgroup.Normal.conj_mem' hK2 x hxK g⟩
        obtain ⟨c, hc, _⟩ :=
          LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hψ1 (ψ.toRepresentation yg)
        have hWyg : ∀ w : W, ρ' (g⁻¹ * x * g) w = c • w := by
          intro w
          exact subrepresentation_eq_smul_id_apply ψ hc w
        have hWg_le_eig : Wg ≤ Module.End.eigenspace (ρ' x) c := by
          intro z hz
          rw [Module.End.mem_eigenspace_iff]
          rcases Submodule.mem_map.mp hz with ⟨w, hw, rfl⟩
          have hmul : x * g = g * (g⁻¹ * x * g) := by group
          have hconj :
              ρ' x * ρ' g = ρ' g * ρ' (g⁻¹ * x * g) := by
            calc
              ρ' x * ρ' g = ρ' (x * g) := (map_mul ρ' x g).symm
              _ = ρ' (g * (g⁻¹ * x * g)) := congrArg ρ' hmul
              _ = ρ' g * ρ' (g⁻¹ * x * g) := map_mul ρ' g (g⁻¹ * x * g)
          have hconj_apply :
              ρ' x (ρ' g w) = ρ' g (ρ' (g⁻¹ * x * g) w) := by
            change ((ρ' x) * (ρ' g)) w = ((ρ' g) * (ρ' (g⁻¹ * x * g))) w
            exact congrArg (fun f : Module.End F' V' => f w) hconj
          calc
            ρ' x (ρ' g w) = ρ' g (ρ' (g⁻¹ * x * g) w) := hconj_apply
            _ = ρ' g (c • w) := by rw [hWyg ⟨w, hw⟩]
            _ = c • ρ' g w := by rw [map_smul]
        by_cases hca : c = a
        · left
          apply Submodule.eq_of_le_of_finrank_eq
          · rw [hca] at hWg_le_eig
            exact le_trans hWg_le_eig <|
              eigenspace_le_of_isCompl_of_eq_left (e := ρ' x) (φ := U) (ψ := W)
                hcomplUW hUx hWx hab
          · exact hWg1.trans hU1.symm
        · by_cases hcb : c = b
          · right
            apply Submodule.eq_of_le_of_finrank_eq
            · rw [hcb] at hWg_le_eig
              exact le_trans hWg_le_eig <|
                eigenspace_le_of_isCompl_of_eq_left (e := ρ' x) (φ := W) (ψ := U)
                  hcomplUW.symm hWx hUx hab.symm
            · exact hWg1.trans hW1.symm
          · have heig_bot : Module.End.eigenspace (ρ' x) c = ⊥ :=
              eigenspace_eq_bot_of_isCompl_of_ne_left_right (e := ρ' x) (φ := U) (ψ := W)
                hcomplUW hUx hWx hca hcb
            rw [heig_bot] at hWg_le_eig
            have hWg_bot : Wg = ⊥ := le_antisymm hWg_le_eig bot_le
            have : Module.finrank F' Wg = 0 := by simp [hWg_bot]
            omega
      have hmap_top (g : G) : (⊤ : Submodule F' V').map (ρ' g) = ⊤ := by
        rw [Submodule.map_top, LinearMap.range_eq_top]
        exact LinearMap.surjective_of_injective (f := ρ' g) (representation_map_injective ρ' g)
      have hU_map_eq (g : G) : U.map (ρ' g) = U := by
        rcases hU_map_or g with hUU | hUW
        · exact hUU
        · have hWgU : W.map (ρ' g) = U := by
            rcases hW_map_or g with hWU | hWW
            · exact hWU
            · exfalso
              have htopW : (⊤ : Submodule F' V') = W := by
                calc
                  ⊤ = (⊤ : Submodule F' V').map (ρ' g) := by simpa using (hmap_top g).symm
                  _ = (U ⊔ W).map (ρ' g) := by rw [hcomplUW.sup_eq_top]
                  _ = U.map (ρ' g) ⊔ W.map (ρ' g) := by rw [Submodule.map_sup]
                  _ = W := by rw [hUW, hWW, sup_idem]
              have : Module.finrank F' (⊤ : Submodule F' V') = 1 := by
                rw [htopW]
                exact hW1
              rw [finrank_top] at this
              omega
          have hU_g2 : ∀ u, u ∈ U → ρ' (g ^ 2) u ∈ U := by
            intro u hu
            have hgU_W : ρ' g u ∈ W := by
              rw [← hUW]
              exact Submodule.mem_map.mpr ⟨u, hu, rfl⟩
            have hg2U : ρ' g (ρ' g u) ∈ U := by
              rw [← hWgU]
              exact Submodule.mem_map.mpr ⟨ρ' g u, hgU_W, rfl⟩
            simpa [pow_two, map_mul, Module.End.mul_eq_comp] using hg2U
          have hcop2 : Nat.Coprime 2 (orderOf g) := by
            have hgodd : Odd (orderOf g) := Odd.of_dvd_nat ho (orderOf_dvd_natCard g)
            exact Nat.prime_two.coprime_iff_not_dvd.mpr hgodd.not_two_dvd_nat
          obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (x := g) hcop2
          have hU_pres : ∀ u, u ∈ U → ρ' g u ∈ U := by
            intro u hu
            have hpowmem :=
              representation_pow_mem_submodule_of_map_mem (ρ := ρ') (U := U) (g := g ^ 2) hU_g2
                m u hu
            simpa [hm] using hpowmem
          have hUg_le_U : U.map (ρ' g) ≤ U := by
            intro z hz
            rcases Submodule.mem_map.mp hz with ⟨u, hu, rfl⟩
            exact hU_pres u hu
          have hW_le_U : W ≤ U := by
            rw [← hUW]
            exact hUg_le_U
          have hWUeq : W = U := Submodule.eq_of_le_of_finrank_eq hW_le_U (hW1.trans hU1.symm)
          exact False.elim (hU_ne_W hWUeq.symm)
      have hW_map_eq (g : G) : W.map (ρ' g) = W := by
        rcases hW_map_or g with hWU | hWW
        · exfalso
          have htopU : (⊤ : Submodule F' V') = U := by
            calc
              ⊤ = (⊤ : Submodule F' V').map (ρ' g) := by simpa using (hmap_top g).symm
              _ = (U ⊔ W).map (ρ' g) := by rw [hcomplUW.sup_eq_top]
              _ = U.map (ρ' g) ⊔ W.map (ρ' g) := by rw [Submodule.map_sup]
              _ = U := by rw [hU_map_eq g, hWU, sup_idem]
          have : Module.finrank F' (⊤ : Submodule F' V') = 1 := by
            rw [htopU]
            exact hU1
          rw [finrank_top] at this
          omega
        · exact hWW
      have hU_stable (g : G) : ∀ u, u ∈ U → ρ' g u ∈ U := by
        intro u hu
        rw [← hU_map_eq g]
        exact Submodule.mem_map.mpr ⟨u, hu, rfl⟩
      have hW_stable (g : G) : ∀ w, w ∈ W → ρ' g w ∈ W := by
        intro w hw
        rw [← hW_map_eq g]
        exact Submodule.mem_map.mpr ⟨w, hw, rfl⟩
      have hU_scalar (g : G) : ∃ c : F', ∀ u : U, ρ' g u = c • u := by
        let gU : Module.End F' U := (ρ' g).restrict (hU_stable g)
        obtain ⟨c, hc, _⟩ :=
          LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hU1 gU
        refine ⟨c, ?_⟩
        intro u
        have hu : gU u = c • u := by
          simpa using congrArg (fun f : Module.End F' U => f u) hc
        exact congrArg Subtype.val hu
      have hW_scalar (g : G) : ∃ c : F', ∀ w : W, ρ' g w = c • w := by
        let gW : Module.End F' W := (ρ' g).restrict (hW_stable g)
        obtain ⟨c, hc, _⟩ :=
          LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hW1 gW
        refine ⟨c, ?_⟩
        intro w
        have hw : gW w = c • w := by
          simpa using congrArg (fun f : Module.End F' W => f w) hc
        exact congrArg Subtype.val hw
      have hcommρ : ∀ g h : G, ρ' (g * h) = ρ' (h * g) := by
        intro g h
        obtain ⟨ag, hag⟩ := hU_scalar g
        obtain ⟨ah, hah⟩ := hU_scalar h
        obtain ⟨bg, hbg⟩ := hW_scalar g
        obtain ⟨bh, hbh⟩ := hW_scalar h
        apply linearMap_eq_of_isCompl_of_eq_on_each (e := ρ' (g * h)) (f := ρ' (h * g))
          (φ := U) (ψ := W) hcomplUW
        · intro u
          have hg_u : ρ' g u ∈ U := hU_stable g _ u.2
          calc
            ρ' (g * h) u = ρ' g (ρ' h u) := by simp [map_mul, Module.End.mul_eq_comp]
            _ = ρ' g (ah • u) := by rw [hah u]
            _ = ah • ρ' g u := by rw [map_smul]
            _ = ah • (ag • u) := by rw [hag u]
            _ = (ah * ag) • u := by rw [smul_smul]
            _ = (ag * ah) • u := by rw [mul_comm]
            _ = ag • (ah • u) := by rw [smul_smul]
            _ = ag • ρ' h u := by rw [hah u]
            _ = ρ' h (ag • u) := by rw [map_smul]
            _ = ρ' h (ρ' g u) := by rw [hag u]
            _ = ρ' (h * g) u := by simp [map_mul, Module.End.mul_eq_comp]
        · intro w
          have hg_w : ρ' g w ∈ W := hW_stable g _ w.2
          calc
            ρ' (g * h) w = ρ' g (ρ' h w) := by simp [map_mul, Module.End.mul_eq_comp]
            _ = ρ' g (bh • w) := by rw [hbh w]
            _ = bh • ρ' g w := by rw [map_smul]
            _ = bh • (bg • w) := by rw [hbg w]
            _ = (bh * bg) • w := by rw [smul_smul]
            _ = (bg * bh) • w := by rw [mul_comm]
            _ = bg • (bh • w) := by rw [smul_smul]
            _ = bg • ρ' h w := by rw [hbh w]
            _ = ρ' h (bg • w) := by rw [map_smul]
            _ = ρ' h (ρ' g w) := by rw [hbg w]
            _ = ρ' (h * g) w := by simp [map_mul, Module.End.mul_eq_comp]
      let : CommGroup G := {
        mul_comm := fun g h ↦ hi (hcommρ g h)
      }
      let C : Sylow (ringChar F) G := Classical.choice inferInstance
      use C
      constructor
      · infer_instance
      · rw [(commutator_eq_bot_iff_center_eq_top G).mpr CommGroup.center_eq_top]
        exact bot_le



public theorem CFSG.theorem_2_6_a
    {F : Type*} [Field F]
    {G : Type*} [Group G] (ho : Odd (Nat.card G))
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (hdim : Module.finrank F V = 2)
    {ρ : Representation F G V} (hi : Function.Injective ρ)
    (hc : ¬ ringChar F ∣ Nat.card G) :
    IsMulCommutative G := by
  let := card_odd_finite ho
  rcases (theorem_2_6_b ho hdim hi) with ⟨C, hC, hC'⟩
  refine IsMulCommutative.mk <| Std.Commutative.mk <| fun a b ↦ ?_
  by_cases h : ringChar F = 0
  · rw [← top_eq_sylow_zero h] at hC
    exact setLike_mul_comm (s := (⊤ : Subgroup G)) trivial trivial
  · have : Fact (ringChar F).Prime := ringChar_prime h
    rw [card_not_dvd_sylow_eq_bot hc, commutator_def, Subgroup.commutator_le] at hC'
    exact commutatorElement_eq_one_iff_mul_comm.mp (hi (congrArg ρ (hC' a trivial b trivial)))
