module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RepresentationTheory.Irreducible

import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesInternal
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellSL2
import CFSG.LocalAnalysis.EvenBN.Common.FongSeitzFourB
import CFSG.GroupTheory.HyperplaneDecomposition
import CFSG.GroupTheory.OddOrderClosurePerfect
import CFSG.LinearAlgebra.LinearGroups.QuadraticActions

public section

namespace CFSG.Quasithin.St84

open scoped MatrixGroups LinearAlgebra.Projectivization
open CFSG.QuasithinUnique.Setup.SL2Modules
open CFSG.SolvableHall
open CFSG.QuasithinUnique.Setup.Campbell

private def fixedSubtypeEquivInvariants {G W : Type*} [Group G] [Finite G] [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) G W) (A : Subgroup G) :
    {w : W // ∀ a ∈ A, ρ a w = w} ≃
      ↥(Representation.invariants (ρ.comp A.subtype)) where
  toFun w := ⟨w.1, mem_invariants_comp_subtype.mpr w.2⟩
  invFun w := ⟨w.1, fun a ha => mem_invariants_comp_subtype.mp w.2 a ha⟩
  left_inv _ := rfl
  right_inv _ := rfl

private lemma natCard_fixed_eq_invariants {G W : Type*} [Group G] [Finite G] [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) G W) (A : Subgroup G) :
    Nat.card {w : W // ∀ a ∈ A, ρ a w = w} =
      Nat.card (Representation.invariants (ρ.comp A.subtype)) :=
  Nat.card_congr (fixedSubtypeEquivInvariants ρ A)

private def fixedSubtypeEquivInf {G W : Type*} [Group G] [Finite G] [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) G W) (U : Subrepresentation ρ)
    (A : Subgroup G) :
    {u : U // ∀ a ∈ A, U.toRepresentation a u = u} ≃
      ↥(Representation.invariants (ρ.comp A.subtype) ⊓ U.toSubmodule) where
  toFun u :=
    ⟨u.1.1, mem_invariants_comp_subtype.mpr fun a ha =>
      (Subrepresentation.toRepresentation_apply_coe).mp (u.2 a ha), u.1.2⟩
  invFun w :=
    ⟨⟨w.1, w.2.2⟩, fun a ha =>
      (Subrepresentation.toRepresentation_apply_coe).mpr
        (mem_invariants_comp_subtype.mp w.2.1 a ha)⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem card_le_mul_card_fixed_of_subrepresentation {G W : Type*} [Group G] [Finite G]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W] (ρ : Representation (ZMod 2) G W)
    (U : Subrepresentation ρ) (A : Subgroup G)
    (hoff : Nat.card W ≤ Nat.card A * Nat.card {w : W // ∀ a ∈ A, ρ a w = w}) :
    Nat.card U ≤ Nat.card A * Nat.card {u : U // ∀ a ∈ A, U.toRepresentation a u = u} := by
  classical
  let C : Submodule (ZMod 2) W := Representation.invariants (ρ.comp A.subtype)
  let Cadd : AddSubgroup W := C.toAddSubgroup
  let Uadd : AddSubgroup W := U.toSubmodule.toAddSubgroup
  have hWfix : Nat.card {w : W // ∀ a ∈ A, ρ a w = w} = Nat.card Cadd := by
    rw [natCard_fixed_eq_invariants ρ A]
    rfl
  have hUfix : Nat.card {u : U // ∀ a ∈ A, U.toRepresentation a u = u} =
      Nat.card ↥(Cadd ⊓ Uadd) := by
    rw [Nat.card_congr (fixedSubtypeEquivInf ρ U A)]
    rfl
  have hCindex : Cadd.relIndex ⊤ * Nat.card Cadd = Nat.card W := by
    simpa using (AddSubgroup.relIndex_mul_card (H := Cadd) (K := (⊤ : AddSubgroup W)))
  have hCindexpos : Cadd.relIndex ⊤ ≠ 0 := by
    intro h
    rw [h, zero_mul] at hCindex
    exact (Nat.card_pos (α := W)).ne' hCindex.symm
  have hCindex_le : Cadd.relIndex ⊤ ≤ Nat.card A := by
    have h1 : Cadd.relIndex ⊤ * Nat.card Cadd ≤ Nat.card A * Nat.card Cadd := by
      calc Cadd.relIndex ⊤ * Nat.card Cadd = Nat.card W := hCindex
        _ ≤ Nat.card A * Nat.card {w : W // ∀ a ∈ A, ρ a w = w} := hoff
        _ = Nat.card A * Nat.card Cadd := by rw [hWfix]
    exact Nat.le_of_mul_le_mul_right h1 (Nat.card_pos (α := Cadd))
  have hstep : (Cadd ⊓ Uadd).relIndex Uadd ≤ Cadd.relIndex ⊤ := by
    rw [AddSubgroup.inf_relIndex_right]
    exact AddSubgroup.relIndex_le_of_le_right le_top hCindexpos
  have hUcard : (Cadd ⊓ Uadd).relIndex Uadd * Nat.card ↥(Cadd ⊓ Uadd) =
      Nat.card Uadd := by
    simpa [inf_assoc] using
      (AddSubgroup.relIndex_mul_card (H := Cadd ⊓ Uadd) (K := Uadd))
  calc Nat.card U = Nat.card Uadd := rfl
    _ = (Cadd ⊓ Uadd).relIndex Uadd * Nat.card ↥(Cadd ⊓ Uadd) := hUcard.symm
    _ ≤ Cadd.relIndex ⊤ * Nat.card ↥(Cadd ⊓ Uadd) := Nat.mul_le_mul_right _ hstep
    _ ≤ Nat.card A * Nat.card ↥(Cadd ⊓ Uadd) := Nat.mul_le_mul_right _ hCindex_le
    _ = Nat.card A * Nat.card {u : U // ∀ a ∈ A, U.toRepresentation a u = u} := by
      rw [hUfix]

private noncomputable def representationMulAut {G V : Type*} [Group G] [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V) :
    G →* MulAut (Multiplicative V) where
  toFun g :=
    AddEquiv.toMultiplicative
      (LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom g)).toAddEquiv
  map_one' := by
    ext x
    simp [LinearMap.GeneralLinearGroup.toLinearEquiv]
  map_mul' g h := by
    ext x
    simp [LinearMap.GeneralLinearGroup.toLinearEquiv_mul]

private lemma representationMulAut_apply {G V : Type*} [Group G] [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V) (g : G) (v : V) :
    Multiplicative.toAdd (representationMulAut ρ g (Multiplicative.ofAdd v)) = ρ g v := by
  simp [representationMulAut, LinearMap.GeneralLinearGroup.toLinearEquiv,
    Representation.asGroupHom_apply]

private theorem card_sq_le_of_nontrivial_rep {n : ℕ} (hn : 2 ≤ n) {F : Type*} [Field F]
    [Fintype F] (hF : Fintype.card F = 2 ^ n) {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] (ρ : Representation (ZMod 2) SL(2, F) V)
    (hnt : ∃ g, ρ g ≠ 1) : Nat.card F ^ 2 ≤ Nat.card V := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := charP_two_of_card_eq hF
  let ρ' := representationMulAut ρ
  have hρ' : ρ' ≠ 1 := by
    intro h
    obtain ⟨g, hg⟩ := hnt
    apply hg
    ext v
    have h1 : ρ' g = 1 := by rw [h, MonoidHom.one_apply]
    have h2 := congrArg (fun e : MulAut (Multiplicative V) =>
      Multiplicative.toAdd (e (Multiplicative.ofAdd v))) h1
    simpa [ρ', representationMulAut_apply] using h2
  have hV : IsPGroup 2 (Multiplicative V) := by
    refine IsPGroup.of_card (n := Module.finrank (ZMod 2) V) ?_
    have hcard : Nat.card (Multiplicative V) = Nat.card V :=
      Nat.card_congr Multiplicative.toAdd
    rw [hcard]
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
    rwa [Nat.card_zmod] at h
  have hk : Nat.card F = 2 ^ n := by
    rw [Nat.card_eq_fintype_card, hF]
  have h := CFSG.LocalAnalysis.EvenBN.Common.sl2_card_sq_le_of_ne_one
    (MulEquiv.refl SL(2, F)) hk hn ρ' hV hρ'
  have hcard : Nat.card (Multiplicative V) = Nat.card V :=
    Nat.card_congr Multiplicative.toAdd
  rwa [hcard] at h

private theorem sq_sub_one_eq_zero_of_trivial_sub_quotient {G W : Type*} [Group G]
    [AddCommGroup W] [Module (ZMod 2) W] (ρ : Representation (ZMod 2) G W)
    (U : Subrepresentation ρ) [Representation.IsTrivial U.toRepresentation]
    [Representation.IsTrivial U.quotient] (g : G) : (ρ g - 1) ^ 2 = 0 := by
  ext w
  have hU : ∀ u : U.toSubmodule, ρ g (u : W) = (u : W) := by
    intro u
    have h := Representation.isTrivial_apply (ρ := U.toRepresentation) g u
    exact (Subrepresentation.toRepresentation_apply_coe).mp h
  have hQ : ∀ w : W, ρ g w - w ∈ U.toSubmodule := by
    intro w
    have h := Representation.isTrivial_apply (ρ := U.quotient) g
      (Submodule.mkQ U.toSubmodule w)
    have h1 : U.quotient g (Submodule.mkQ U.toSubmodule w) =
        Submodule.mkQ U.toSubmodule (ρ g w) := rfl
    rw [h1] at h
    have hzero : Submodule.mkQ U.toSubmodule (ρ g w - w) = 0 := by
      rw [map_sub, h, sub_self]
    exact (Submodule.Quotient.mk_eq_zero U.toSubmodule).mp hzero
  have hfix : ρ g (ρ g w - w) = ρ g w - w := hU ⟨ρ g w - w, hQ w⟩
  change ρ g (ρ g w - w) - (ρ g w - w) = 0
  rw [hfix, sub_self]

theorem eq_one_of_sq_sub_one_eq_zero_of_odd_order {G V : Type*} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) G V) {g : G} (hodd : Odd (orderOf g))
    (hsq : (ρ g - 1) ^ 2 = 0) : ρ g = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let a : LinearMap.GeneralLinearGroup (ZMod 2) V := ρ.asGroupHom g
  have ha : ((a : V →ₗ[ZMod 2] V) - 1) ^ 2 = 0 := by
    simpa [a, Representation.asGroupHom_apply] using hsq
  have ha2 : a ^ 2 = 1 := (CFSG.LinearGroups.quadratic_linear_p_elements 2 a ha).1
  have ham : a ^ orderOf g = 1 := by
    rw [show a = ρ.asGroupHom g from rfl, ← map_pow, pow_orderOf_eq_one, map_one]
  have ha1 : a = 1 := by
    rcases hodd with ⟨k, hk⟩
    calc a = (a ^ 2) ^ k * a := by rw [ha2, one_pow, one_mul]
      _ = a ^ (2 * k) * a := by rw [pow_mul]
      _ = a ^ (2 * k + 1) := by rw [pow_succ]
      _ = 1 := by rw [← hk]; exact ham
  ext v
  have h := congrArg (fun e : LinearMap.GeneralLinearGroup (ZMod 2) V =>
    (e : V →ₗ[ZMod 2] V) v) ha1
  simpa [a, Representation.asGroupHom_apply] using h

private theorem card_le_sq_of_offender {n : ℕ} {F : Type*} [Field F]
    [Fintype F] (hF : Fintype.card F = 2 ^ n) {W : Type*} [AddCommGroup W]
    [Module (ZMod 2) W] [Finite W] [Nontrivial W] (ρ : Representation (ZMod 2) SL(2, F) W)
    (hfix : ∀ w : W, (∀ g, ρ g w = w) → w = 0) (A : Subgroup SL(2, F))
    [CFSG.IsElementaryAbelian 2 A] (hAq : Nat.card A = 2 ^ n)
    (hoff : Nat.card W ≤ Nat.card A * Nat.card {w : W // ∀ a ∈ A, ρ a w = w}) :
    Nat.card W ≤ (2 ^ n) ^ 2 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := charP_two_of_card_eq hF
  have hAcard : Nat.card A = Nat.card F := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hF]
    simpa using hAq
  obtain ⟨x, hAx⟩ : ∃ x : ℙ F (Fin 2 → F), A = rootGrp x :=
    exists_point_eq_rootGrp (k := F) (p := 2) (f := n)
      Nat.prime_two (by rw [Nat.card_eq_fintype_card, hF]) hAcard
  obtain ⟨y, hxy⟩ : ∃ y : ℙ F (Fin 2 → F), y ≠ x := exists_ne_point x
  let S' : Subgroup SL(2, F) := rootGrp y
  have hsup : A ⊔ S' = ⊤ := by
    rw [hAx]
    exact rootGrp_sup_rootGrp (Ne.symm hxy)
  obtain ⟨g, hg⟩ : ∃ g : SL(2, F), g • y = x :=
    MulAction.exists_smul_eq (M := SL(2, F)) (α := ℙ F (Fin 2 → F)) y x
  have hroot : rootGrp x = S'.map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    exact rootGrp_smul_eq_map g y
  have hconj : ∀ z, z ∈ A ↔ g⁻¹ * z * g ∈ S' := by
    intro z
    rw [hAx, hroot]
    constructor
    · rintro ⟨s, hs, rfl⟩
      simpa [mul_assoc] using hs
    · intro hz
      exact ⟨g⁻¹ * z * g, hz, by simp [MulAut.conj_apply, mul_assoc]⟩
  let C : Submodule (ZMod 2) W := Representation.invariants (ρ.comp A.subtype)
  let CS : Submodule (ZMod 2) W := Representation.invariants (ρ.comp S'.subtype)
  have htop : Representation.invariants
      (ρ.comp (⊤ : Subgroup SL(2, F)).subtype) = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Submodule.mem_bot]
    exact hfix w fun g => mem_invariants_comp_subtype.mp hw g (Subgroup.mem_top g)
  have hCinf : C ⊓ CS = ⊥ := by
    rw [← invariants_comp_subtype_sup ρ A S', hsup, htop]
  have hCAfix : Nat.card {w : W // ∀ a ∈ A, ρ a w = w} = Nat.card C := by
    rw [natCard_fixed_eq_invariants ρ A]
  have hCSfix : Nat.card {w : W // ∀ a ∈ S', ρ a w = w} = Nat.card CS := by
    rw [natCard_fixed_eq_invariants ρ S']
  have hCSeq : Nat.card CS = Nat.card C := by
    rw [← hCSfix, ← hCAfix]
    exact (natCard_fixed_conj ρ A S' g hconj).symm
  have hprod_le : Nat.card ↥C * Nat.card ↥CS ≤ Nat.card W := by
    have hinj : Function.Injective
        (fun p : ↥C × ↥CS => (p.1 : W) + (p.2 : W)) := by
      rintro ⟨c₁, s₁⟩ ⟨c₂, s₂⟩ h
      have h1 : (c₁ : W) - c₂ = s₂ - s₁ := by
        rw [sub_eq_iff_eq_add]
        calc (c₁ : W) = (c₂ + s₂) - s₁ := (eq_sub_iff_add_eq).mpr h
          _ = (s₂ - s₁) + c₂ := by abel
      have hmemC : (c₁ : W) - c₂ ∈ C := C.sub_mem c₁.2 c₂.2
      have hmemS : (c₁ : W) - c₂ ∈ CS := by
        rw [h1]
        exact CS.sub_mem s₂.2 s₁.2
      have hzero : (c₁ : W) - c₂ ∈ (⊥ : Submodule (ZMod 2) W) := by
        rw [← hCinf]
        exact Submodule.mem_inf.mpr ⟨hmemC, hmemS⟩
      have hc : (c₁ : W) = c₂ := sub_eq_zero.mp (by simpa using hzero)
      have hs : (s₁ : W) = s₂ := by
        change (c₁ : W) + (s₁ : W) = (c₂ : W) + (s₂ : W) at h
        rw [hc] at h
        exact add_left_cancel h
      exact Prod.ext (Subtype.ext hc) (Subtype.ext hs)
    have hle := Nat.card_le_card_of_injective
      (fun p : ↥C × ↥CS => (p.1 : W) + (p.2 : W)) hinj
    simpa using hle
  have hoffC : Nat.card W ≤ Nat.card A * Nat.card C := by
    calc Nat.card W ≤ Nat.card A * Nat.card {w : W // ∀ a ∈ A, ρ a w = w} := hoff
      _ = Nat.card A * Nat.card C := by rw [hCAfix]
  have hCSle : Nat.card CS ≤ Nat.card A := by
    have h1 : Nat.card CS * Nat.card C ≤ Nat.card A * Nat.card C := by
      calc Nat.card CS * Nat.card C = Nat.card C * Nat.card CS := Nat.mul_comm _ _
        _ ≤ Nat.card W := hprod_le
        _ ≤ Nat.card A * Nat.card C := hoffC
    exact Nat.le_of_mul_le_mul_right h1 (Nat.card_pos (α := C))
  have hCle : Nat.card C ≤ Nat.card A := by
    rw [← hCSeq]
    exact hCSle
  calc Nat.card W ≤ Nat.card A * Nat.card C := hoffC
    _ ≤ Nat.card A * Nat.card A := Nat.mul_le_mul_left _ hCle
    _ = (2 ^ n) ^ 2 := by rw [hAq, pow_two]

private theorem card_eq_pow_of_offender_aux {n : ℕ} (hn : 2 ≤ n) {F : Type*} [Field F]
    [Fintype F] (hF : Fintype.card F = 2 ^ n) (N : ℕ) :
    ∀ {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W] [Nontrivial W]
      (ρ : Representation (ZMod 2) SL(2, F) W), Nat.card W = N →
      (∀ w : W, (∀ g, ρ g w = w) → w = 0) →
      ∀ (A : Subgroup SL(2, F)) [CFSG.IsElementaryAbelian 2 A], A ≠ ⊥ →
      Nat.card W ≤ Nat.card A * Nat.card {w : W // ∀ a ∈ A, ρ a w = w} →
      Nat.card A = 2 ^ n := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro W _ _ _ _ ρ hWN hfix A _ hA1 hoff
    classical
    by_cases hirr : ρ.IsIrreducible
    · have hnt : ∃ g, ρ g ≠ 1 := by
        by_contra h
        push Not at h
        obtain ⟨w, hw⟩ := exists_ne (0 : W)
        exact hw (hfix w fun g => by rw [h g]; rfl)
      obtain ⟨φ, hφ, hB, hC, hD, hE⟩ :=
        binary_SL2_internal_offender_natural_module (by omega : 1 ≤ n) hF ρ hirr hnt A hA1 hoff
      obtain ⟨ℓ, hℓ, hgen, hfixA, hAeq, hP, hprod⟩ := hE
      exact hAeq
    · have hproper : ∃ U : Subrepresentation ρ, U ≠ ⊥ ∧ U ≠ ⊤ := by
        by_contra h
        push Not at h
        apply hirr
        refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
        · intro hbot
          exact bot_ne_top (congrArg Subrepresentation.toSubmodule hbot)
        · intro U
          by_cases hU : U = ⊥
          · exact Or.inl hU
          · exact Or.inr (h U hU)
      obtain ⟨U, hUbot, hUtop⟩ := hproper
      have hUbot' : U.toSubmodule ≠ ⊥ := by
        intro h
        exact hUbot (Subrepresentation.toSubmodule_injective (by rw [h]; rfl))
      have hUtop' : U.toSubmodule ≠ ⊤ := by
        intro h
        exact hUtop (Subrepresentation.toSubmodule_injective (by rw [h]; rfl))
      haveI : Nontrivial ↥U.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hUbot'
      have hfixU : ∀ u : U, (∀ g, U.toRepresentation g u = u) → u = (0 : U.toSubmodule) := by
        intro u hu
        have hzero : (u : W) = 0 :=
          hfix u.1 fun g => (Subrepresentation.toRepresentation_apply_coe).mp (hu g)
        exact Subtype.ext (by simpa using hzero)
      have hoffU : Nat.card U ≤ Nat.card A *
          Nat.card {u : U // ∀ a ∈ A, U.toRepresentation a u = u} :=
        card_le_mul_card_fixed_of_subrepresentation ρ U A hoff
      have hUN : Nat.card U < N := by
        rw [← hWN]
        haveI : Finite (W ⧸ U.toSubmodule) :=
          Finite.of_surjective (Submodule.mkQ U.toSubmodule) (Submodule.mkQ_surjective _)
        haveI : Nontrivial (W ⧸ U.toSubmodule) :=
          (Submodule.Quotient.nontrivial_iff).mpr hUtop'
        have hq2 : 2 ≤ Nat.card (W ⧸ U.toSubmodule) := by
          have := Finite.one_lt_card (α := W ⧸ U.toSubmodule)
          omega
        have hpos : 0 < Nat.card U := Nat.card_pos
        have hlt : Nat.card U < Nat.card U * Nat.card (W ⧸ U.toSubmodule) := by
          nlinarith
        exact (Submodule.card_eq_card_quotient_mul_card U.toSubmodule).symm ▸ hlt
      exact ih (Nat.card U) hUN U.toRepresentation rfl hfixU A hA1 hoffU

theorem exists_natural_of_offender {n : ℕ} (hn : 2 ≤ n) {F : Type*} [Field F] [Fintype F]
    (hF : Fintype.card F = 2 ^ n) {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    [Nontrivial W] (ρ : Representation (ZMod 2) SL(2, F) W)
    (hfix : ∀ w : W, (∀ g, ρ g w = w) → w = 0) (A : Subgroup SL(2, F))
    [CFSG.IsElementaryAbelian 2 A] (hA1 : A ≠ ⊥)
    (hoff : Nat.card W ≤ Nat.card A * Nat.card {w : W // ∀ a ∈ A, ρ a w = w}) :
    ρ.IsIrreducible ∧ Nat.card A = 2 ^ n ∧
      ∃ φ : W ≃+ (Fin 2 → F), ∀ g w,
        φ (ρ g w) = (g : Matrix (Fin 2) (Fin 2) F).mulVec (φ w) := by
  classical
  have hAq : Nat.card A = 2 ^ n :=
    card_eq_pow_of_offender_aux hn hF (Nat.card W) ρ rfl hfix A hA1 hoff
  have hWle : Nat.card W ≤ (2 ^ n) ^ 2 :=
    card_le_sq_of_offender hF ρ hfix A hAq hoff
  have hnt : ∃ g, ρ g ≠ 1 := by
    by_contra h
    push Not at h
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    exact hw (hfix w fun g => by rw [h g]; rfl)
  have hirr : ρ.IsIrreducible := by
    by_contra hnotirr
    have hproper : ∃ U : Subrepresentation ρ, U ≠ ⊥ ∧ U ≠ ⊤ := by
      by_contra h
      push Not at h
      apply hnotirr
      refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
      · intro hbot
        exact bot_ne_top (congrArg Subrepresentation.toSubmodule hbot)
      · intro U
        by_cases hU : U = ⊥
        · exact Or.inl hU
        · exact Or.inr (h U hU)
    obtain ⟨U, hUbot, hUtop⟩ := hproper
    have hUbot' : U.toSubmodule ≠ ⊥ := by
      intro h
      exact hUbot (Subrepresentation.toSubmodule_injective (by rw [h]; rfl))
    have hUtop' : U.toSubmodule ≠ ⊤ := by
      intro h
      exact hUtop (Subrepresentation.toSubmodule_injective (by rw [h]; rfl))
    haveI : Nontrivial ↥U.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hUbot'
    haveI : Finite (W ⧸ U.toSubmodule) :=
      Finite.of_surjective (Submodule.mkQ U.toSubmodule) (Submodule.mkQ_surjective _)
    have hFcard : Nat.card F = 2 ^ n := by
      rw [Nat.card_eq_fintype_card, hF]
    have hWleF : Nat.card W ≤ Nat.card F ^ 2 := by
      rw [hFcard]
      exact hWle
    by_cases hUtriv : Representation.IsTrivial U.toRepresentation
    · haveI : Representation.IsTrivial U.toRepresentation := hUtriv
      by_cases hQtriv : Representation.IsTrivial U.quotient
      ·
        haveI : Representation.IsTrivial U.quotient := hQtriv
        exfalso
        have h4 : 4 ≤ Nat.card F := by
          rw [Nat.card_eq_fintype_card, hF]
          have hpow : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num : (0 : ℕ) < 2) hn
          norm_num at hpow ⊢
          exact hpow
        have hperfect : Group.IsPerfect SL(2, F) :=
          CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F h4
        have hodd : ∀ g : SL(2, F), Odd (orderOf g) → ρ g = 1 := fun g hg =>
          eq_one_of_sq_sub_one_eq_zero_of_odd_order ρ hg
            (sq_sub_one_eq_zero_of_trivial_sub_quotient ρ U g)
        obtain ⟨w, hw⟩ := exists_ne (0 : W)
        have hwfix : ∀ g : SL(2, F), ρ g w = w := by
          intro g
          have hmem : ρ.asGroupHom g ∈ (⊥ : Subgroup ((W →ₗ[ZMod 2] W)ˣ)) :=
            CFSG.GroupTheory.map_le_of_isPerfect_of_forall_odd_order
              (f := ρ.asGroupHom) (K := ⊥) (fun x hx => by
                rw [Subgroup.mem_bot]
                exact Units.ext (by
                  rw [Representation.asGroupHom_apply, hodd x hx, Units.val_one])) g
          have h1 : ρ.asGroupHom g = 1 := by simpa using hmem
          have h2 : ρ g = 1 := by
            have := congrArg Units.val h1
            simpa [Representation.asGroupHom_apply] using this
          rw [h2]
          rfl
        exact hw (hfix w hwfix)
      ·
        have hntQ : ∃ g, U.quotient g ≠ 1 := by
          by_contra h
          push Not at h
          exact hQtriv ⟨h⟩
        have hqbound : Nat.card F ^ 2 ≤ Nat.card (W ⧸ U.toSubmodule) :=
          card_sq_le_of_nontrivial_rep (V := W ⧸ U.toSubmodule) hn hF U.quotient hntQ
        have hU2 : 2 ≤ Nat.card ↥U.toSubmodule := by
          have := Finite.one_lt_card (α := ↥U.toSubmodule)
          omega
        haveI : Nontrivial (W ⧸ U.toSubmodule) :=
          (Submodule.Quotient.nontrivial_iff).mpr hUtop'
        have hq2 : 2 ≤ Nat.card (W ⧸ U.toSubmodule) := by
          have := Finite.one_lt_card (α := W ⧸ U.toSubmodule)
          omega
        have hWbig : 2 * Nat.card F ^ 2 ≤ Nat.card W := by
          rw [Submodule.card_eq_card_quotient_mul_card U.toSubmodule]
          nlinarith
        have hqpos : 0 < Nat.card F ^ 2 := pow_pos (Nat.card_pos (α := F)) 2
        nlinarith [hWleF, hWbig, hqpos]
    ·
      have hntU : ∃ g, U.toRepresentation g ≠ 1 := by
        by_contra h
        push Not at h
        exact hUtriv ⟨h⟩
      have hubound : Nat.card F ^ 2 ≤ Nat.card U :=
        card_sq_le_of_nontrivial_rep (V := ↥U.toSubmodule) hn hF U.toRepresentation hntU
      have hUle : Nat.card U ≤ Nat.card W :=
        Nat.card_le_card_of_injective (fun u : U => (u : W)) (fun _ _ h => Subtype.ext h)
      have hUeq : Nat.card U = Nat.card W :=
        le_antisymm hUle (by nlinarith [hWleF, hubound])
      have hUtopeq : U.toSubmodule = ⊤ := by
        by_contra hne
        haveI : Nontrivial (W ⧸ U.toSubmodule) :=
          (Submodule.Quotient.nontrivial_iff).mpr hne
        have hq2 : 1 < Nat.card (W ⧸ U.toSubmodule) := Finite.one_lt_card
        have hUpos : 0 < Nat.card ↥U.toSubmodule := Nat.card_pos
        have hW_eq : Nat.card W = Nat.card ↥U.toSubmodule * Nat.card (W ⧸ U.toSubmodule) :=
          Submodule.card_eq_card_quotient_mul_card U.toSubmodule
        have h1 : Nat.card ↥U.toSubmodule * 1 =
            Nat.card ↥U.toSubmodule * Nat.card (W ⧸ U.toSubmodule) := by
          rw [Nat.mul_one, ← hW_eq]
          exact hUeq
        have h2 : Nat.card (W ⧸ U.toSubmodule) = 1 := by
          exact (Nat.mul_left_cancel hUpos h1).symm
        omega
      exact hUtop (Subrepresentation.toSubmodule_injective hUtopeq)
  obtain ⟨φ, hφ, -⟩ :=
    binary_SL2_internal_offender_natural_module (by omega : 1 ≤ n) hF ρ hirr hnt A hA1 hoff
  exact ⟨hirr, hAq, φ, hφ⟩

end CFSG.Quasithin.St84
