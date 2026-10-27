module

import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.PFsection9_3
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_5_b
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.PFsection9_6
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ElementaryAbelianAction
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.RingTheory.ZMod.UnitsCyclic

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped IsMulCommutative MonoidAlgebra commutatorElement

namespace CFSG.Section9

universe u v w

private theorem theorem_9_7_quotientCentralizedBy_C_sec9
    {G : Type u} [Group G]
    {MF H0 U C : Subgroup G} :
    quotientCentralizerIn MF H0 U C →
      quotientCentralizedBy MF H0 C := by
  intro hC x hxC h hhMF
  exact (hC.2 x (hC.1 hxC)).mp hxC h hhMF

public theorem theorem_9_7_barU_isMulCommutative_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 H0 C : Subgroup G} {q : ℕ}
    (h92 : hypothesis_9_2_statement M MF U W1 W2 q)
    (hC : quotientCentralizerIn MF H0 U C)
    (hnormalC : (C.subgroupOf U).Normal) :
    letI : (C.subgroupOf U).Normal := hnormalC
    IsMulCommutative (U ⧸ C.subgroupOf U) := by
  classical
  letI : (C.subgroupOf U).Normal := hnormalC
  apply Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
  intro x hx
  have hPsource : Section8.typePDefinitionData M MF U W1 W2 := by
    exact h92.typePDefinitionData
  have hcomm_image :
      (_root_.commutator U).map U.subtype ≤ Subgroup.centralizer (MF : Set G) :=
    (Section8.theorem_8_5_b M MF U W1 W2 hPsource).1
  have hxmap : (x : G) ∈ (_root_.commutator U).map U.subtype := by
    exact ⟨x, hx, rfl⟩
  have hxcent : (x : G) ∈ Subgroup.centralizer (MF : Set G) := hcomm_image hxmap
  have hxC : (x : G) ∈ C := by
    rw [(hC.2 (x : G) x.property)]
    intro h hhMF
    have hxcomm := (Subgroup.mem_centralizer_iff.mp hxcent) h hhMF
    have hcomm_eq : ⁅(x : G), h⁆ = 1 := by
      rw [commutatorElement_def]
      calc
        (x : G) * h * (x : G)⁻¹ * h⁻¹ =
            (h * (x : G)) * (x : G)⁻¹ * h⁻¹ := by
          rw [hxcomm]
        _ = 1 := by group
    rw [hcomm_eq]
    exact H0.one_mem
  simpa [Subgroup.mem_subgroupOf] using hxC

private theorem theorem_9_7_commuting_image_of_quotient_kernel_commutative_sec9
    {F G V : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V]
    (ρ : Representation F G V)
    (hquotComm :
      letI : ρ.ker.Normal := MonoidHom.normal_ker ρ
      IsMulCommutative (G ⧸ ρ.ker)) :
    ∀ g h : G, (ρ g).comp (ρ h) = (ρ h).comp (ρ g) := by
  classical
  letI : ρ.ker.Normal := MonoidHom.normal_ker ρ
  intro g h
  have hq :
      QuotientGroup.mk' ρ.ker (g * h) =
        QuotientGroup.mk' ρ.ker (h * g) := by
    calc
      QuotientGroup.mk' ρ.ker (g * h) =
          QuotientGroup.mk' ρ.ker g * QuotientGroup.mk' ρ.ker h := by
            simp
      _ = QuotientGroup.mk' ρ.ker h * QuotientGroup.mk' ρ.ker g := by
            exact mul_comm _ _
      _ = QuotientGroup.mk' ρ.ker (h * g) := by
            simp
  have hker : (g * h)⁻¹ * (h * g) ∈ ρ.ker := QuotientGroup.eq.mp hq
  have hρ_eq : ρ (g * h) = ρ (h * g) := by
    have hmul : (g * h) * ((g * h)⁻¹ * (h * g)) = h * g := by
      group
    have htmp := congrArg ρ hmul
    rw [map_mul, MonoidHom.mem_ker.mp hker, mul_one] at htmp
    exact htmp
  ext x
  calc
    (ρ g).comp (ρ h) x = ρ (g * h) x := by
      simp [← Module.End.mul_apply, ← map_mul]
    _ = ρ (h * g) x := by
      rw [hρ_eq]
    _ = (ρ h).comp (ρ g) x := by
      simp [← Module.End.mul_apply, ← map_mul]

private theorem theorem_9_7_finrank_eq_one_of_abs_irred_commuting_image_sec9
    {F G V : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F G V)
    [Representation.IsIrreducible ρ]
    [Theory.Representation.IsAbsolutelyIrreducible ρ]
    (hcomm : ∀ g h : G, (ρ g).comp (ρ h) = (ρ h).comp (ρ g)) :
    Module.finrank F V = 1 := by
  classical
  have hsurj : Function.Surjective (algebraMap F (Theory.Representation.End ρ)) :=
    (Theory.Representation.isAbsolutelyIrreducible_iff_surjective ρ).1 inferInstance
  haveI : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hscalar (g : G) : ∃ c : F, ρ g v = c • v := by
    let f : Theory.Representation.End ρ :=
      (ρ g).intertwiningMap_of_isIntertwiningMap ρ ρ (by
        intro h x
        exact LinearMap.congr_fun (hcomm g h) x)
    rcases hsurj f with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have happ := congrArg (fun T : Theory.Representation.End ρ => T v) hc
    calc
      ρ g v = f v := rfl
      _ = (algebraMap F (Theory.Representation.End ρ) c) v := happ.symm
      _ = c • v := by
        simp [Theory.Representation.End.algebraMap_apply]
  let S : Subrepresentation ρ :=
    { toSubmodule := Submodule.span F ({v} : Set V)
      apply_mem_toSubmodule := by
        intro g x hx
        rcases Submodule.mem_span_singleton.mp hx with ⟨a, ha⟩
        rcases hscalar g with ⟨c, hc⟩
        refine Submodule.mem_span_singleton.mpr ⟨a * c, ?_⟩
        calc
          (a * c) • v = a • (c • v) := by
            rw [smul_smul]
          _ = a • (ρ g v) := by
            rw [hc]
          _ = ρ g (a • v) := by
            rw [map_smul]
          _ = ρ g x := by
            rw [ha] }
  have hS_ne_bot : S ≠ ⊥ := by
    intro hbot
    have hvS : v ∈ S := Submodule.mem_span_singleton_self v
    have hz : v = 0 := (Representation.eq_bot_iff.mp hbot) v hvS
    exact hv hz
  have hS_top : S = ⊤ := by
    rcases (inferInstance : Representation.IsIrreducible ρ).eq_bot_or_eq_top S with
      hbot | htop
    · exact False.elim (hS_ne_bot hbot)
    · exact htop
  have hspan_top :
      (Submodule.span F ({v} : Set V) : Submodule F V) = ⊤ := by
    have hsub := congrArg Subrepresentation.toSubmodule hS_top
    change
      (Submodule.span F ({v} : Set V) : Submodule F V) =
        (⊤ : Submodule F V) at hsub
    exact hsub
  rw [finrank_eq_one_iff_of_nonzero' v hv]
  intro x
  have hxmem : x ∈ (Submodule.span F ({v} : Set V) : Submodule F V) := by
    rw [hspan_top]
    exact trivial
  exact Submodule.mem_span_singleton.mp hxmem

private theorem theorem_9_7_finrank_eq_one_of_abs_irred_quotient_kernel_commutative_sec9
    {F G V : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F G V)
    [Representation.IsIrreducible ρ]
    [Theory.Representation.IsAbsolutelyIrreducible ρ]
    (hquotComm :
      letI : ρ.ker.Normal := MonoidHom.normal_ker ρ
      IsMulCommutative (G ⧸ ρ.ker)) :
    Module.finrank F V = 1 :=
  theorem_9_7_finrank_eq_one_of_abs_irred_commuting_image_sec9 ρ
    (theorem_9_7_commuting_image_of_quotient_kernel_commutative_sec9 ρ
      hquotComm)

private theorem theorem_9_7_quotient_commutative_of_eq_kernel_sec9
    {G : Type*} [Group G] {C K : Subgroup G}
    [C.Normal] [K.Normal]
    (hCcomm : IsMulCommutative (G ⧸ C))
    (hCK : C = K) :
    IsMulCommutative (G ⧸ K) := by
  classical
  refine ⟨?_⟩
  refine Std.Commutative.mk ?_
  intro x y
  refine QuotientGroup.induction_on x ?_
  intro a
  refine QuotientGroup.induction_on y ?_
  intro b
  apply QuotientGroup.eq.mpr
  have hqC : QuotientGroup.mk' C (a * b) = QuotientGroup.mk' C (b * a) := by
    calc
      QuotientGroup.mk' C (a * b) =
          QuotientGroup.mk' C a * QuotientGroup.mk' C b := by
            simp
      _ = QuotientGroup.mk' C b * QuotientGroup.mk' C a := by
            exact mul_comm _ _
      _ = QuotientGroup.mk' C (b * a) := by
            simp
  have hmemC : (a * b)⁻¹ * (b * a) ∈ C := QuotientGroup.eq.mp hqC
  simpa [hCK] using hmemC

set_option backward.isDefEq.respectTransparency false in
private theorem
    theorem_9_7_endFieldRep_finrank_eq_one_of_quotient_kernel_commutative_sec9
    {F : Type*} [Field F] [Finite F]
    {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F G V) [Representation.IsIrreducible ρ]
    (hquotComm :
      letI : (endFieldRep ρ).ker.Normal := MonoidHom.normal_ker (endFieldRep ρ)
      IsMulCommutative (G ⧸ (endFieldRep ρ).ker)) :
    let E := Module.End (MonoidAlgebra F G) ρ.asModule
    letI : Field E := endField_field ρ
    letI : Module E ρ.asModule := endFieldModule ρ
    Module.finrank E ρ.asModule = 1 := by
  classical
  dsimp
  let E := Module.End (MonoidAlgebra F G) ρ.asModule
  letI : Field E := endField_field ρ
  letI : Module E ρ.asModule := endFieldModule ρ
  have hρasFinite : Finite ρ.asModule :=
    Module.finite_iff_finite.mp (inferInstance : FiniteDimensional F V)
  letI : Module.Finite E ρ.asModule := Module.Finite.of_finite
  have hEndIrred := endFieldRep_isIrreducible ρ
  letI := hEndIrred
  have hEndAbs := endFieldRep_isAbsolutelyIrreducible ρ
  letI := hEndAbs
  exact
    theorem_9_7_finrank_eq_one_of_abs_irred_quotient_kernel_commutative_sec9
      (endFieldRep ρ) hquotComm

private noncomputable def theorem_9_7_ringAutEquivAlgEquivZMod_sec9
    (F : Type u) [Field F] (p : ℕ) [Fact p.Prime] [CharP F p] :
    letI : Algebra (ZMod p) F := ZMod.algebra F p
    RingAut F ≃ (F ≃ₐ[ZMod p] F) := by
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  refine
    { toFun := fun σ => AlgEquiv.ofRingEquiv (f := σ) ?_
      invFun := fun σ => σ.toRingEquiv
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    change σ (ZMod.cast x : F) = ZMod.cast x
    obtain ⟨k, rfl⟩ := ZMod.intCast_surjective x
    rw [ZMod.cast_intCast']
    exact map_intCast σ k
  · intro σ
    ext x
    rfl
  · intro σ
    ext x
    rfl

private theorem theorem_9_7_ringAut_card_eq_finrank_zmod_sec9
    (F : Type u) [Field F] [Fintype F]
    (p : ℕ) [Fact p.Prime] [CharP F p] :
    letI : Algebra (ZMod p) F := ZMod.algebra F p
    Nat.card (RingAut F) = Module.finrank (ZMod p) F := by
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  rw [Nat.card_congr (theorem_9_7_ringAutEquivAlgEquivZMod_sec9 F p)]
  exact IsGalois.card_aut_eq_finrank (ZMod p) F

private theorem theorem_9_7_ringAut_card_eq_q_of_finite_field_card_sec9
    (F : Type u) [Field F] [Fintype F] {p q : ℕ}
    (hpprime : Nat.Prime p)
    (hcard : Nat.card F = p ^ q) :
    Nat.card (RingAut F) = q := by
  classical
  haveI : Fact p.Prime := ⟨hpprime⟩
  have hcardFintype : Fintype.card F = p ^ q := by
    simpa [Nat.card_eq_fintype_card] using hcard
  haveI : CharP F p := charP_of_card_eq_prime_pow hcardFintype
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  have hfinrank : Module.finrank (ZMod p) F = q := by
    apply Nat.pow_right_injective hpprime.two_le
    calc
      p ^ Module.finrank (ZMod p) F = Fintype.card F :=
        FiniteField.pow_finrank_eq_card p F
      _ = p ^ q := hcardFintype
  calc
    Nat.card (RingAut F) = Module.finrank (ZMod p) F :=
      theorem_9_7_ringAut_card_eq_finrank_zmod_sec9 F p
    _ = q := hfinrank

private noncomputable def theorem_9_7_mulEquivOfInjectiveHomCardEq_sec9
    {A B : Type u} [Group A] [Group B] [Finite A] [Finite B]
    (φ : A →* B)
    (hinj : Function.Injective φ)
    (hcard : Nat.card A = Nat.card B) :
    A ≃* B := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype B := Fintype.ofFinite B
  refine MulEquiv.ofBijective φ ?_
  apply (Fintype.bijective_iff_injective_and_card φ).2
  refine ⟨hinj, ?_⟩
  simpa [Nat.card_eq_fintype_card] using hcard

private theorem theorem_9_7_quotient_hom_injective_of_kernel_eq_sec9
    {U : Type u} {A : Type v} [Group U] [Group A]
    (C : Subgroup U) [C.Normal]
    (ψ : U →* A)
    (hCker : C ≤ ψ.ker)
    (hkerC : ψ.ker ≤ C) :
    ∃ φ : U ⧸ C →* A, Function.Injective φ := by
  classical
  haveI : ψ.ker.Normal := MonoidHom.normal_ker ψ
  have hC_eq_ker : C = ψ.ker := le_antisymm hCker hkerC
  let ψ' : U ⧸ ψ.ker →* A := QuotientGroup.kerLift ψ
  have hψ'inj : Function.Injective ψ' := QuotientGroup.kerLift_injective ψ
  let e : U ⧸ C ≃* U ⧸ ψ.ker := QuotientGroup.quotientMulEquivOfEq hC_eq_ker
  refine ⟨ψ'.comp e.toMonoidHom, ?_⟩
  exact hψ'inj.comp e.injective

private theorem theorem_9_7_quotient_equiv_range_of_eq_ker_sec9
    {U : Type u} {A : Type v} [Group U] [Group A]
    (C : Subgroup U) [C.Normal]
    (ψ : U →* A)
    (hCker : C = ψ.ker) :
    ∃ Ustar : Subgroup A,
      ∃ φU : U ⧸ C ≃* Ustar,
        ∀ u : U, ((φU (QuotientGroup.mk' C u) : Ustar) : A) = ψ u := by
  classical
  haveI : ψ.ker.Normal := MonoidHom.normal_ker ψ
  let e : U ⧸ C ≃* U ⧸ ψ.ker := QuotientGroup.quotientMulEquivOfEq hCker
  let ψker : U ⧸ ψ.ker →* A := QuotientGroup.kerLift ψ
  let ψC : U ⧸ C →* A := ψker.comp e.toMonoidHom
  have hψCinj : Function.Injective ψC :=
    (QuotientGroup.kerLift_injective ψ).comp e.injective
  refine ⟨ψC.range, MonoidHom.ofInjective hψCinj, ?_⟩
  intro u
  change ψC (QuotientGroup.mk' C u) = ψ u
  simp [ψC, ψker, e]

public def theorem_9_7_fin_succ_of_sub_one_sec9
    {q : ℕ} (hqpos : 0 < q) (j : Fin (q - 1)) : Fin q :=
  ⟨j.1 + 1, by omega⟩

@[expose] public def theorem_9_7_fin_cyclic_succ_sec9
    {q : ℕ} (hqpos : 0 < q) (i : Fin q) : Fin q :=
  if h : i.1 + 1 < q then ⟨i.1 + 1, h⟩ else ⟨0, hqpos⟩

private theorem theorem_9_7_fin_eq_zero_or_succ_of_sub_one_sec9
    {q : ℕ} (hqpos : 0 < q) (i : Fin q) :
    i = ⟨0, hqpos⟩ ∨
      ∃ j : Fin (q - 1),
        theorem_9_7_fin_succ_of_sub_one_sec9 hqpos j = i := by
  by_cases hi0 : i.1 = 0
  · left
    exact Fin.ext hi0
  · right
    have hipos : 0 < i.1 := Nat.pos_of_ne_zero hi0
    refine ⟨⟨i.1 - 1, by omega⟩, ?_⟩
    apply Fin.ext
    simp [theorem_9_7_fin_succ_of_sub_one_sec9]
    omega

private theorem theorem_9_7_component_value_eq_zero_of_relative_equalizer_sec9
    {q : ℕ} (hqpos : 0 < q) {A : Type v} (χ : Fin q → A)
    (hrel :
      ∀ j : Fin (q - 1),
        χ (theorem_9_7_fin_succ_of_sub_one_sec9 hqpos j) =
          χ ⟨0, hqpos⟩) :
    ∀ i, χ i = χ ⟨0, hqpos⟩ := by
  intro i
  rcases theorem_9_7_fin_eq_zero_or_succ_of_sub_one_sec9 hqpos i with hi | ⟨j, hj⟩
  · rw [hi]
  · rw [← hj]
    exact hrel j

public theorem theorem_9_7_component_character_generator_agreement_of_transition_sec9
    {q : ℕ} (hqpos : 0 < q) {X : Type u} {A : Type v}
    (χbar : Fin q → X → A) (x y : X)
    (htransition :
      ∀ i, χbar i y = χbar (theorem_9_7_fin_cyclic_succ_sec9 hqpos i) x)
    (hrel :
      ∀ j : Fin (q - 1),
        χbar (theorem_9_7_fin_succ_of_sub_one_sec9 hqpos j) x =
          χbar ⟨0, hqpos⟩ x) :
    ∀ i, χbar i y = χbar i x := by
  intro i
  have hall :=
    theorem_9_7_component_value_eq_zero_of_relative_equalizer_sec9
      hqpos (fun k => χbar k x) hrel
  calc
    χbar i y = χbar (theorem_9_7_fin_cyclic_succ_sec9 hqpos i) x :=
      htransition i
    _ = χbar ⟨0, hqpos⟩ x := hall _
    _ = χbar i x := (hall i).symm

private noncomputable def theorem_9_7_relative_product_hom_sec9
    {U : Type u} {A : Type v} [Group U] [CommGroup A]
    {q : ℕ} (hqpos : 0 < q)
    (χ : Fin q → U →* A) :
    U →* (Fin (q - 1) → A) where
  toFun x j :=
    χ (theorem_9_7_fin_succ_of_sub_one_sec9 hqpos j) x *
      (χ ⟨0, hqpos⟩ x)⁻¹
  map_one' := by
    ext j
    simp
  map_mul' x y := by
    ext j
    simp [mul_inv_rev, mul_assoc, mul_left_comm, mul_comm]

private theorem theorem_9_7_relative_product_hom_C_le_ker_sec9
    {U : Type u} {A : Type v} [Group U] [CommGroup A]
    {q : ℕ} (hqpos : 0 < q)
    (C : Subgroup U) (χ : Fin q → U →* A)
    (hχC : ∀ i, C ≤ (χ i).ker) :
    C ≤ (theorem_9_7_relative_product_hom_sec9 hqpos χ).ker := by
  intro x hx
  rw [MonoidHom.mem_ker]
  ext j
  have hs : χ (theorem_9_7_fin_succ_of_sub_one_sec9 hqpos j) x = 1 :=
    hχC _ hx
  have h0 : χ ⟨0, hqpos⟩ x = 1 := hχC _ hx
  simp [theorem_9_7_relative_product_hom_sec9, hs, h0]

private theorem theorem_9_7_relative_product_hom_ker_le_of_equalizer_sec9
    {U : Type u} {A : Type v} [Group U] [CommGroup A]
    {q : ℕ} (hqpos : 0 < q)
    (C : Subgroup U) (χ : Fin q → U →* A)
    (hequalizer :
      ∀ x : U,
        (∀ j : Fin (q - 1),
          χ (theorem_9_7_fin_succ_of_sub_one_sec9 hqpos j) x =
            χ ⟨0, hqpos⟩ x) →
        x ∈ C) :
    (theorem_9_7_relative_product_hom_sec9 hqpos χ).ker ≤ C := by
  intro x hx
  apply hequalizer x
  intro j
  have hcoord :
      χ (theorem_9_7_fin_succ_of_sub_one_sec9 hqpos j) x *
          (χ ⟨0, hqpos⟩ x)⁻¹ = 1 := by
    have hrel := MonoidHom.mem_ker.mp hx
    exact congrFun (by
      simpa [theorem_9_7_relative_product_hom_sec9] using hrel) j
  calc
    χ (theorem_9_7_fin_succ_of_sub_one_sec9 hqpos j) x =
        (χ (theorem_9_7_fin_succ_of_sub_one_sec9 hqpos j) x *
          (χ ⟨0, hqpos⟩ x)⁻¹) * χ ⟨0, hqpos⟩ x := by
          group
    _ = 1 * χ ⟨0, hqpos⟩ x := by rw [hcoord]
    _ = χ ⟨0, hqpos⟩ x := by simp

public theorem theorem_9_7_quotient_component_pullback_C_le_ker_sec9
    {U : Type u} {A : Type v} [Group U] [Group A]
    (C : Subgroup U) [C.Normal]
    (χbar : U ⧸ C →* A) :
    C ≤ (χbar.comp (QuotientGroup.mk' C)).ker := by
  intro x hx
  rw [MonoidHom.mem_ker]
  change χbar ((QuotientGroup.mk' C) x) = 1
  have hxq : (QuotientGroup.mk' C) x = 1 := by
    exact (QuotientGroup.eq_one_iff x).2 hx
  rw [hxq]
  simp


private theorem theorem_9_7_factorAction_unique_of_action_field_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 U C : Subgroup G}
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hnormalC : (C.subgroupOf U).Normal]
    {Q : Subgroup (MF ⧸ H0.subgroupOf MF)}
    {ρ σ : (U ⧸ C.subgroupOf U) →* MulAut Q}
    (hactionρ :
      ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ Q,
              (ρ x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (hactionσ :
      ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ Q,
              (σ x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩) :
    ρ = σ := by
  classical
  apply MonoidHom.ext
  intro x
  ext y
  rcases y with ⟨y, hyQ⟩
  refine QuotientGroup.induction_on x ?_
  intro u
  revert hyQ
  refine QuotientGroup.induction_on y ?_
  intro h hyQ
  rcases hactionρ (QuotientGroup.mk' (C.subgroupOf U) u) u rfl with
    ⟨hconjρ, hρ⟩
  rcases hactionσ (QuotientGroup.mk' (C.subgroupOf U) u) u rfl with
    ⟨hconjσ, hσ⟩
  calc
    ((ρ (QuotientGroup.mk' (C.subgroupOf U) u))
        ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hyQ⟩ :
        MF ⧸ H0.subgroupOf MF) =
        QuotientGroup.mk' (H0.subgroupOf MF)
          ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjρ h⟩ :=
          hρ h hyQ
    _ = QuotientGroup.mk' (H0.subgroupOf MF)
          ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjσ h⟩ := by
          apply congrArg (QuotientGroup.mk' (H0.subgroupOf MF))
          apply Subtype.ext
          rfl
    _ = ((σ (QuotientGroup.mk' (C.subgroupOf U) u))
        ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hyQ⟩ :
        MF ⧸ H0.subgroupOf MF) :=
          (hσ h hyQ).symm

private noncomputable def theorem_9_7_mulAutConjEquiv_sec9
    {Q : Type u} {R : Type v} [Group Q] [Group R]
    (e : Q ≃* R) : MulAut Q ≃* MulAut R where
  toFun α := e.symm.trans (α.trans e)
  invFun β := e.trans (β.trans e.symm)
  left_inv α := by
    ext x
    simp
  right_inv β := by
    ext x
    simp
  map_mul' α β := by
    ext x
    simp

private noncomputable def theorem_9_7_transportFactorAction_sec9
    {X : Type u} [Group X]
    {Q : Type v} {R : Type*} [Group Q] [Group R]
    (e : Q ≃* R) (ρ : X →* MulAut Q) : X →* MulAut R :=
  (theorem_9_7_mulAutConjEquiv_sec9 e).toMonoidHom.comp ρ

private theorem theorem_9_7_transportFactorAction_apply_sec9
    {X : Type u} [Group X]
    {Q : Type v} {R : Type*} [Group Q] [Group R]
    (e : Q ≃* R) (ρ : X →* MulAut Q) (x : X) (y : R) :
    theorem_9_7_transportFactorAction_sec9 e ρ x y = e (ρ x (e.symm y)) :=
  rfl

private theorem theorem_9_7_transportFactorAction_range_eq_map_sec9
    {X : Type u} [Group X]
    {Q : Type v} {R : Type*} [Group Q] [Group R]
    (e : Q ≃* R) (ρ : X →* MulAut Q) :
    MonoidHom.range (theorem_9_7_transportFactorAction_sec9 e ρ) =
      (MonoidHom.range ρ).map
        (theorem_9_7_mulAutConjEquiv_sec9 e).toMonoidHom := by
  ext β
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨ρ x, ⟨x, rfl⟩, rfl⟩
  · rintro ⟨α, ⟨x, hx⟩, hα⟩
    refine ⟨x, ?_⟩
    rw [← hα, ← hx]
    rfl


private theorem theorem_9_7_monoidHom_range_comp_mulEquiv_sec9
    {X A : Type u} [Group X] [Group A]
    (τ : X ≃* X) (ρ : X →* A) :
    MonoidHom.range (ρ.comp τ.toMonoidHom) = MonoidHom.range ρ := by
  ext a
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨τ x, rfl⟩
  · rintro ⟨x, rfl⟩
    refine ⟨τ.symm x, ?_⟩
    simp


public noncomputable def theorem_9_7_successorTransportFactorAction_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 U W1 C : Subgroup G}
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hW1normU : Subgroup.Normalizes W1 U]
    (hnormalC : (C.subgroupOf U).Normal)
    (hCinv : IsInvariant W1 U (C.subgroupOf U))
    (w0 : W1)
    {Q R : Subgroup (MF ⧸ H0.subgroupOf MF)}
    (e : Q ≃* R)
    (ρ : (U ⧸ C.subgroupOf U) →* MulAut Q) :
    (U ⧸ C.subgroupOf U) →* MulAut R := by
  letI : (C.subgroupOf U).Normal := hnormalC
  letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
    quotientMulDistribMulAction (A := W1) (G := U) (C.subgroupOf U) hCinv
  exact theorem_9_7_transportFactorAction_sec9 e
    (ρ.comp (((MulDistribMulAction.toMulAut W1 (U ⧸ C.subgroupOf U)) w0).toMonoidHom))

public theorem theorem_9_7_successorTransportFactorAction_apply_mk_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 U W1 C : Subgroup G}
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hW1normU : Subgroup.Normalizes W1 U]
    (hnormalC : (C.subgroupOf U).Normal)
    (hCinv : IsInvariant W1 U (C.subgroupOf U))
    (w0 : W1)
    {Q R : Subgroup (MF ⧸ H0.subgroupOf MF)}
    (e : Q ≃* R)
    (ρ : (U ⧸ C.subgroupOf U) →* MulAut Q)
    (x : U) (y : R) :
    theorem_9_7_successorTransportFactorAction_sec9
        hnormalC hCinv w0 e ρ (QuotientGroup.mk' (C.subgroupOf U) x) y =
      e (ρ (QuotientGroup.mk' (C.subgroupOf U) (w0 • x)) (e.symm y)) := by
  classical
  letI : (C.subgroupOf U).Normal := hnormalC
  letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
    quotientMulDistribMulAction (A := W1) (G := U) (C.subgroupOf U) hCinv
  rw [theorem_9_7_successorTransportFactorAction_sec9]
  rw [theorem_9_7_transportFactorAction_apply_sec9]
  rfl


private noncomputable def theorem_9_7_successorTransportFactorAction_rangeEquiv_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 U W1 C : Subgroup G}
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hW1normU : Subgroup.Normalizes W1 U]
    (hnormalC : (C.subgroupOf U).Normal)
    (hCinv : IsInvariant W1 U (C.subgroupOf U))
    (w0 : W1)
    {Q R : Subgroup (MF ⧸ H0.subgroupOf MF)}
    (e : Q ≃* R)
    (ρ : (U ⧸ C.subgroupOf U) →* MulAut Q) :
    MonoidHom.range ρ ≃*
      MonoidHom.range
        (theorem_9_7_successorTransportFactorAction_sec9
          hnormalC hCinv w0 e ρ) := by
  classical
  letI : (C.subgroupOf U).Normal := hnormalC
  letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
    quotientMulDistribMulAction (A := W1) (G := U) (C.subgroupOf U) hCinv
  let τ : (U ⧸ C.subgroupOf U) ≃* (U ⧸ C.subgroupOf U) :=
    (MulDistribMulAction.toMulAut W1 (U ⧸ C.subgroupOf U)) w0
  change MonoidHom.range ρ ≃*
    MonoidHom.range
      (theorem_9_7_transportFactorAction_sec9 e (ρ.comp τ.toMonoidHom))
  exact
    (MulEquiv.subgroupCongr
      (theorem_9_7_monoidHom_range_comp_mulEquiv_sec9 τ ρ).symm).trans
      (((theorem_9_7_mulAutConjEquiv_sec9 e).subgroupMap
        (MonoidHom.range (ρ.comp τ.toMonoidHom))).trans
        (MulEquiv.subgroupCongr
          (theorem_9_7_transportFactorAction_range_eq_map_sec9 e
            (ρ.comp τ.toMonoidHom)).symm))

private theorem theorem_9_7_successorTransportFactorAction_rangeEquiv_apply_mk_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 U W1 C : Subgroup G}
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hW1normU : Subgroup.Normalizes W1 U]
    (hnormalC : (C.subgroupOf U).Normal)
    (hCinv : IsInvariant W1 U (C.subgroupOf U))
    (w0 : W1)
    {Q R : Subgroup (MF ⧸ H0.subgroupOf MF)}
    (e : Q ≃* R)
    (ρ : (U ⧸ C.subgroupOf U) →* MulAut Q)
    (x : U) :
    theorem_9_7_successorTransportFactorAction_rangeEquiv_sec9
        hnormalC hCinv w0 e ρ
        ⟨ρ (QuotientGroup.mk' (C.subgroupOf U) (w0 • x)),
          ⟨QuotientGroup.mk' (C.subgroupOf U) (w0 • x), rfl⟩⟩ =
      ⟨theorem_9_7_successorTransportFactorAction_sec9 hnormalC hCinv w0 e ρ
          (QuotientGroup.mk' (C.subgroupOf U) x),
        ⟨QuotientGroup.mk' (C.subgroupOf U) x, rfl⟩⟩ := by
  rfl

private theorem theorem_9_7_successorTransportFactorAction_rangeEdge_apply_mk_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 U W1 C : Subgroup G}
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hW1normU : Subgroup.Normalizes W1 U]
    (hnormalC : (C.subgroupOf U).Normal)
    (hCinv : IsInvariant W1 U (C.subgroupOf U))
    (w0 : W1)
    {Q R : Subgroup (MF ⧸ H0.subgroupOf MF)}
    (e : Q ≃* R)
    (ρ : (U ⧸ C.subgroupOf U) →* MulAut Q)
    (σ : (U ⧸ C.subgroupOf U) →* MulAut R)
    (hσ :
      theorem_9_7_successorTransportFactorAction_sec9
        hnormalC hCinv w0 e ρ = σ)
    (x : U) :
    ((theorem_9_7_successorTransportFactorAction_rangeEquiv_sec9
        hnormalC hCinv w0 e ρ).trans
      (MulEquiv.subgroupCongr (congrArg MonoidHom.range hσ)))
        ⟨ρ (QuotientGroup.mk' (C.subgroupOf U) (w0 • x)),
          ⟨QuotientGroup.mk' (C.subgroupOf U) (w0 • x), rfl⟩⟩ =
      ⟨σ (QuotientGroup.mk' (C.subgroupOf U) x),
        ⟨QuotientGroup.mk' (C.subgroupOf U) x, rfl⟩⟩ := by
  rw [MulEquiv.trans_apply]
  rw [theorem_9_7_successorTransportFactorAction_rangeEquiv_apply_mk_sec9]
  apply Subtype.ext
  calc
    (((MulEquiv.subgroupCongr (congrArg MonoidHom.range hσ))
        ⟨theorem_9_7_successorTransportFactorAction_sec9 hnormalC hCinv w0 e ρ
            (QuotientGroup.mk' (C.subgroupOf U) x),
          ⟨QuotientGroup.mk' (C.subgroupOf U) x, rfl⟩⟩) :
        MulAut R) =
        theorem_9_7_successorTransportFactorAction_sec9 hnormalC hCinv w0 e ρ
          (QuotientGroup.mk' (C.subgroupOf U) x) :=
      MulEquiv.subgroupCongr_apply (congrArg MonoidHom.range hσ) _
    _ = σ (QuotientGroup.mk' (C.subgroupOf U) x) :=
      congrArg (fun f => f (QuotientGroup.mk' (C.subgroupOf U) x)) hσ

private theorem theorem_9_7_generator_pow_card_eq_one_sec9
    {G : Type u} [Group G] [Finite G]
    {W1 : Subgroup G} (w0 : W1)
    (hw0gen : Subgroup.zpowers w0 = ⊤) :
    w0 ^ Nat.card W1 = 1 := by
  rw [← orderOf_eq_card_of_zpowers_eq_top hw0gen]
  exact pow_orderOf_eq_one w0

private theorem theorem_9_7_generator_pow_eq_one_of_card_sec9
    {G : Type u} [Group G] [Finite G]
    {W1 : Subgroup G} {q : ℕ} (w0 : W1)
    (hW1card : Nat.card W1 = q)
    (hw0gen : Subgroup.zpowers w0 = ⊤) :
    w0 ^ q = 1 := by
  rw [← hW1card]
  exact theorem_9_7_generator_pow_card_eq_one_sec9 w0 hw0gen


private theorem theorem_9_7_generator_quotient_action_pow_eq_one_sec9
    {G : Type u} [Group G] [Finite G]
    {U W1 C : Subgroup G}
    [hW1normU : Subgroup.Normalizes W1 U]
    (hnormalC : (C.subgroupOf U).Normal)
    (hCinv : IsInvariant W1 U (C.subgroupOf U))
    {q : ℕ} (w0 : W1)
    (hW1card : Nat.card W1 = q)
    (hw0gen : Subgroup.zpowers w0 = ⊤) :
    ((MulDistribMulAction.toMulAut W1 (U ⧸ C.subgroupOf U)) w0) ^ q = 1 := by
  classical
  letI : (C.subgroupOf U).Normal := hnormalC
  letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
    quotientMulDistribMulAction (A := W1) (G := U) (C.subgroupOf U) hCinv
  rw [← map_pow]
  rw [theorem_9_7_generator_pow_eq_one_of_card_sec9 w0 hW1card hw0gen]
  exact map_one (MulDistribMulAction.toMulAut W1 (U ⧸ C.subgroupOf U))

private theorem theorem_9_7_generator_MF_quotient_action_inv_pow_eq_one_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 W1 : Subgroup G}
    [hW1normMF : Subgroup.Normalizes W1 MF]
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    (hH0invW1 : IsInvariant W1 MF (H0.subgroupOf MF))
    {q : ℕ} (w0 : W1)
    (hW1card : Nat.card W1 = q)
    (hw0gen : Subgroup.zpowers w0 = ⊤) :
    (letI : MulAction.QuotientAction W1 (H0.subgroupOf MF) :=
      quotientAction_of_isInvariant (A := W1) (G := MF)
        (H0.subgroupOf MF) hH0invW1
    letI : MulDistribMulAction W1 (MF ⧸ H0.subgroupOf MF) :=
      quotientMulDistribMulAction (A := W1) (G := MF)
        (H0.subgroupOf MF) hH0invW1
    ((MulDistribMulAction.toMulAut W1
      (MF ⧸ H0.subgroupOf MF)) (w0⁻¹ : W1)) ^ q = 1) := by
  classical
  let H0MF : Subgroup MF := H0.subgroupOf MF
  haveI : H0MF.Normal := hnormalH0
  letI : MulAction.QuotientAction W1 H0MF :=
    quotientAction_of_isInvariant (A := W1) (G := MF) H0MF hH0invW1
  letI : MulDistribMulAction W1 (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := W1) (G := MF) H0MF hH0invW1
  rw [← map_pow]
  have hpow : (w0⁻¹ : W1) ^ q = 1 := by
    rw [inv_pow, theorem_9_7_generator_pow_eq_one_of_card_sec9 w0 hW1card hw0gen,
      inv_one]
  rw [hpow]
  exact map_one (MulDistribMulAction.toMulAut W1 (MF ⧸ H0MF))

private theorem theorem_9_7_mulEquiv_cast_apply_family_sec9
    {ι : Type*} {A : ι → Type*} [∀ i, Mul (A i)]
    {i j : ι} (h : i = j) (x : ∀ i, A i) :
    MulEquiv.cast (M := A) h (x i) = x j := by
  cases h
  rfl

private noncomputable def theorem_9_7_successor_range_chain_lt_sec9
    {q : ℕ} (hqpos : 0 < q)
    {X : Type u} [Group X]
    {B : Fin q → Type v} [∀ i, Group (B i)]
    (ρ : ∀ i, X →* B i)
    (edge : ∀ i, (ρ i).range ≃*
      (ρ (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)).range) :
    (n : ℕ) → (hn : n < q) →
      (ρ ⟨0, hqpos⟩).range ≃* (ρ ⟨n, hn⟩).range
  | 0, _ => MulEquiv.refl _
  | n + 1, hn =>
      have hnq : n < q := by omega
      let hidx :
          theorem_9_7_fin_cyclic_succ_sec9 hqpos ⟨n, hnq⟩ =
            ⟨n + 1, hn⟩ :=
        Fin.ext (by simp [theorem_9_7_fin_cyclic_succ_sec9, hn])
      (theorem_9_7_successor_range_chain_lt_sec9 hqpos ρ edge n hnq).trans
        ((edge ⟨n, hnq⟩).trans
          (MulEquiv.cast (M := fun i => (ρ i).range) hidx))

private theorem theorem_9_7_successor_range_chain_lt_apply_sec9
    {q : ℕ} (hqpos : 0 < q)
    {X : Type u} [Group X]
    (τ : MulAut X)
    {B : Fin q → Type v} [∀ i, Group (B i)]
    (ρ : ∀ i, X →* B i)
    (edge : ∀ i, (ρ i).range ≃*
      (ρ (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)).range)
    (hedge :
      ∀ i x,
        edge i ⟨ρ i (τ x), ⟨τ x, rfl⟩⟩ =
          ⟨ρ (theorem_9_7_fin_cyclic_succ_sec9 hqpos i) x, ⟨x, rfl⟩⟩) :
    ∀ n (hn : n < q) x,
      theorem_9_7_successor_range_chain_lt_sec9 hqpos ρ edge n hn
          ⟨ρ ⟨0, hqpos⟩ ((τ ^ n) x), ⟨(τ ^ n) x, rfl⟩⟩ =
        ⟨ρ ⟨n, hn⟩ x, ⟨x, rfl⟩⟩ := by
  intro n
  induction n with
  | zero =>
      intro hn x
      rfl
  | succ n ih =>
      intro hn x
      have hnq : n < q := by omega
      let hidx :
          theorem_9_7_fin_cyclic_succ_sec9 hqpos ⟨n, hnq⟩ =
            ⟨n + 1, hn⟩ :=
        Fin.ext (by simp [theorem_9_7_fin_cyclic_succ_sec9, hn])
      rw [← show (τ ^ n) (τ x) = (τ ^ (n + 1)) x by
        rw [pow_succ]
        rfl]
      change
        (MulEquiv.cast (M := fun i => (ρ i).range) hidx
          ((edge ⟨n, hnq⟩)
            ((theorem_9_7_successor_range_chain_lt_sec9 hqpos ρ edge n hnq)
              ⟨ρ ⟨0, hqpos⟩ ((τ ^ n) (τ x)),
                ⟨(τ ^ n) (τ x), rfl⟩⟩))) = _
      rw [ih hnq (τ x)]
      rw [hedge ⟨n, hnq⟩ x]
      exact theorem_9_7_mulEquiv_cast_apply_family_sec9
        (A := fun i => (ρ i).range) hidx
        (fun i => ⟨ρ i x, ⟨x, rfl⟩⟩)

private theorem theorem_9_7_successor_range_zmod_equivs_sec9
    {q a : ℕ} (hqpos : 0 < q)
    {X : Type u} [Group X]
    (τ : MulAut X)
    (hτ : τ ^ q = 1)
    {B : Fin q → Type v} [∀ i, Group (B i)]
    (ρ : ∀ i, X →* B i)
    (hcyc : ∀ i, IsCyclic (ρ i).range)
    (hcard : ∀ i, Nat.card (ρ i).range = a)
    (edge : ∀ i, (ρ i).range ≃*
      (ρ (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)).range)
    (hedge :
      ∀ i x,
        edge i ⟨ρ i (τ x), ⟨τ x, rfl⟩⟩ =
          ⟨ρ (theorem_9_7_fin_cyclic_succ_sec9 hqpos i) x, ⟨x, rfl⟩⟩) :
    ∃ ψ : ∀ i, (ρ i).range ≃* Multiplicative (ZMod a),
      ∀ x i,
        ψ i ⟨ρ i (τ x), ⟨τ x, rfl⟩⟩ =
          ψ (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)
            ⟨ρ (theorem_9_7_fin_cyclic_succ_sec9 hqpos i) x,
              ⟨x, rfl⟩⟩ := by
  classical
  let i0 : Fin q := ⟨0, hqpos⟩
  haveI : IsCyclic (ρ i0).range := hcyc i0
  have htarget : Nat.card (Multiplicative (ZMod a)) = a := by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod a) ≃ ZMod a),
      Nat.card_zmod]
  let base : (ρ i0).range ≃* Multiplicative (ZMod a) :=
    mulEquivOfCyclicCardEq (G := (ρ i0).range)
      (G' := Multiplicative (ZMod a)) ((hcard i0).trans htarget.symm)
  let chainTo : ∀ i, (ρ i0).range ≃* (ρ i).range :=
    fun i => theorem_9_7_successor_range_chain_lt_sec9 hqpos ρ edge i.1 i.2
  let ψ : ∀ i, (ρ i).range ≃* Multiplicative (ZMod a) :=
    fun i => (chainTo i).symm.trans base
  refine ⟨ψ, ?_⟩
  intro x i
  dsimp [ψ]
  let n := i.1
  by_cases hi : i.1 + 1 < q
  · have hsucc_eq :
        theorem_9_7_fin_cyclic_succ_sec9 hqpos i = ⟨n + 1, hi⟩ := by
      apply Fin.ext
      simp [theorem_9_7_fin_cyclic_succ_sec9, hi, n]
    have hleft_map :=
      theorem_9_7_successor_range_chain_lt_apply_sec9 hqpos τ ρ edge hedge
        n i.2 (τ x)
    have hpow : (τ ^ n) (τ x) = (τ ^ (n + 1)) x := by
      rw [pow_succ]
      rfl
    have hleft_symm :
        (chainTo i).symm ⟨ρ i (τ x), ⟨τ x, rfl⟩⟩ =
          ⟨ρ i0 ((τ ^ (n + 1)) x), ⟨(τ ^ (n + 1)) x, rfl⟩⟩ := by
      calc
        (chainTo i).symm ⟨ρ i (τ x), ⟨τ x, rfl⟩⟩ =
            (chainTo i).symm (chainTo i
              ⟨ρ i0 ((τ ^ n) (τ x)), ⟨(τ ^ n) (τ x), rfl⟩⟩) := by
              rw [hleft_map]
        _ = ⟨ρ i0 ((τ ^ n) (τ x)), ⟨(τ ^ n) (τ x), rfl⟩⟩ := by
              simp
        _ = ⟨ρ i0 ((τ ^ (n + 1)) x), ⟨(τ ^ (n + 1)) x, rfl⟩⟩ := by
              rw [hpow]
    have hright_map :=
      theorem_9_7_successor_range_chain_lt_apply_sec9 hqpos τ ρ edge hedge
        (n + 1) hi x
    have hright_symm :
        (chainTo (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)).symm
            ⟨ρ (theorem_9_7_fin_cyclic_succ_sec9 hqpos i) x, ⟨x, rfl⟩⟩ =
          ⟨ρ i0 ((τ ^ (n + 1)) x), ⟨(τ ^ (n + 1)) x, rfl⟩⟩ := by
      rw [hsucc_eq]
      calc
        (chainTo ⟨n + 1, hi⟩).symm
            ⟨ρ ⟨n + 1, hi⟩ x, ⟨x, rfl⟩⟩ =
          (chainTo ⟨n + 1, hi⟩).symm
            (chainTo ⟨n + 1, hi⟩
              ⟨ρ i0 ((τ ^ (n + 1)) x), ⟨(τ ^ (n + 1)) x, rfl⟩⟩) := by
              rw [hright_map]
        _ = ⟨ρ i0 ((τ ^ (n + 1)) x), ⟨(τ ^ (n + 1)) x, rfl⟩⟩ := by
              simp
    rw [hleft_symm, hright_symm]
  · have hnq : n + 1 = q := by omega
    have hsucc_eq :
        theorem_9_7_fin_cyclic_succ_sec9 hqpos i = i0 := by
      apply Fin.ext
      simp [theorem_9_7_fin_cyclic_succ_sec9, hi, i0]
    have hleft_map :=
      theorem_9_7_successor_range_chain_lt_apply_sec9 hqpos τ ρ edge hedge
        n i.2 (τ x)
    have hpowq : (τ ^ n) (τ x) = x := by
      have hpow : (τ ^ n) (τ x) = (τ ^ q) x := by
        rw [← hnq, pow_succ]
        rfl
      rw [hpow, hτ]
      rfl
    have hleft_symm :
        (chainTo i).symm ⟨ρ i (τ x), ⟨τ x, rfl⟩⟩ =
          ⟨ρ i0 x, ⟨x, rfl⟩⟩ := by
      calc
        (chainTo i).symm ⟨ρ i (τ x), ⟨τ x, rfl⟩⟩ =
            (chainTo i).symm (chainTo i
              ⟨ρ i0 ((τ ^ n) (τ x)), ⟨(τ ^ n) (τ x), rfl⟩⟩) := by
              rw [hleft_map]
        _ = ⟨ρ i0 ((τ ^ n) (τ x)), ⟨(τ ^ n) (τ x), rfl⟩⟩ := by
              simp
        _ = ⟨ρ i0 x, ⟨x, rfl⟩⟩ := by
              rw [hpowq]
    have hright_symm :
        (chainTo (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)).symm
            ⟨ρ (theorem_9_7_fin_cyclic_succ_sec9 hqpos i) x,
              ⟨x, rfl⟩⟩ =
          ⟨ρ i0 x, ⟨x, rfl⟩⟩ := by
      rw [hsucc_eq]
      rfl
    rw [hleft_symm, hright_symm]


private theorem theorem_9_7_quotient_cardinality_from_chief_data_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 H0 : Subgroup G}
    {p q : ℕ} {hp : Nat.Primes} :
    hypothesis_9_2_statement M MF U W1 W2 q →
      hp.val = p →
        quotientChiefFactorData_9_6 M MF H0 W1 hp →
          Nat.card (MF ⧸ H0.subgroupOf MF) = p ^ q := by
  intro h92 hp_eq h96
  rcases h96 with ⟨_hH0MF, _hMFM, _hnorm, _hchief, _hWbar, hcard⟩
  calc
    Nat.card (MF ⧸ H0.subgroupOf MF) = hp.val ^ Nat.card W1 := hcard
    _ = p ^ q := by rw [hp_eq, h92.q_eq]

private theorem theorem_9_7_W1_fixedPointSubgroup_card_eq_source_subtype_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (MF W1 H0 : Subgroup G) [Subgroup.Normalizes W1 MF]
    (hH0_inv : IsInvariant W1 MF (H0.subgroupOf MF))
    (hnormal : (H0.subgroupOf MF).Normal) :
    (letI : (H0.subgroupOf MF).Normal := hnormal;
      letI : MulDistribMulAction W1 (MF ⧸ H0.subgroupOf MF) :=
        quotientMulDistribMulAction (A := W1) (G := MF)
          (H0.subgroupOf MF) hH0_inv;
      Nat.card {x : MF ⧸ H0.subgroupOf MF //
        ∀ h : MF, QuotientGroup.mk' (H0.subgroupOf MF) h = x →
          ∀ w : G, w ∈ W1 → ⁅w, (h : G)⁆ ∈ H0} =
        Nat.card (fixedPointSubgroup W1 (MF ⧸ H0.subgroupOf MF))) := by
  classical
  let H0MF : Subgroup MF := H0.subgroupOf MF
  haveI : H0MF.Normal := hnormal
  letI : MulDistribMulAction W1 (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := W1) (G := MF) H0MF hH0_inv
  have hiff : ∀ x : MF ⧸ H0MF,
      (∀ h : MF, QuotientGroup.mk' H0MF h = x →
        ∀ w : G, w ∈ W1 → ⁅w, (h : G)⁆ ∈ H0) ↔
        x ∈ fixedPointSubgroup W1 (MF ⧸ H0MF) := by
    intro x
    constructor
    · intro hx
      change ∀ w : W1, w • x = x
      intro w
      revert hx
      refine QuotientGroup.induction_on x ?_
      intro h hx
      have hcommH0 : ⁅(w : G), (h : G)⁆ ∈ H0 :=
        hx h rfl (w : G) w.property
      apply QuotientGroup.eq_iff_div_mem.mpr
      have hcommH0MF : ((w • h : MF) / h) ∈ H0MF := by
        have hval : ((((w • h : MF) / h : MF) : G) = ⁅(w : G), (h : G)⁆) := by
          simp [div_eq_mul_inv, commutatorElement_def,
            Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, mul_assoc]
        simpa [H0MF, Subgroup.mem_subgroupOf, hval] using hcommH0
      simpa [div_eq_mul_inv] using hcommH0MF
    · intro hx h hh w hw
      let wW1 : W1 := ⟨w, hw⟩
      have hfixed : wW1 • x = x := by
        change ∀ w : W1, w • x = x at hx
        exact hx wW1
      have hfixed_mk :
          wW1 • QuotientGroup.mk' H0MF h = QuotientGroup.mk' H0MF h := by
        simpa [hh] using hfixed
      have hq : QuotientGroup.mk' H0MF (wW1 • h) = QuotientGroup.mk' H0MF h := by
        simpa using hfixed_mk
      have hcommH0MF : ((wW1 • h : MF) / h) ∈ H0MF :=
        QuotientGroup.eq_iff_div_mem.mp hq
      have hval : ((((wW1 • h : MF) / h : MF) : G) = ⁅w, (h : G)⁆) := by
        simp [wW1, div_eq_mul_inv, commutatorElement_def,
          Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, mul_assoc]
      simpa [H0MF, Subgroup.mem_subgroupOf, hval] using hcommH0MF
  simpa [H0MF] using (Nat.card_congr (Equiv.subtypeEquivRight hiff))

private theorem theorem_9_7_W1_fixedPointSubgroup_ne_top_of_chief_data_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {M MF U W1 W2 H0 : Subgroup G} {p q : ℕ} :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
          quotientChiefFactorData_9_6 M MF H0 W1 hp) →
      Nat.Prime p →
        Nat.Prime q →
          (hnormalH0 : (H0.subgroupOf MF).Normal) →
            (hW1normMF : W1 ≤ Subgroup.normalizer (MF : Set G)) →
              (hH0invW1 :
                letI : Subgroup.Normalizes W1 MF := ⟨hW1normMF⟩
                IsInvariant W1 MF (H0.subgroupOf MF)) →
              (hbarCard :
                letI : (H0.subgroupOf MF).Normal := hnormalH0
                Nat.card (MF ⧸ H0.subgroupOf MF) = p ^ q) →
              letI : Subgroup.Normalizes W1 MF := ⟨hW1normMF⟩
              letI : (H0.subgroupOf MF).Normal := hnormalH0
              letI : MulDistribMulAction W1 (MF ⧸ H0.subgroupOf MF) :=
                quotientMulDistribMulAction (A := W1) (G := MF)
                  (H0.subgroupOf MF) hH0invW1
              fixedPointSubgroup W1 (MF ⧸ H0.subgroupOf MF) ≠ ⊤ := by
  classical
  intro _h92 hp96 hpprime hqprime hnormalH0 hW1normMF hH0invW1 hbarCard
  letI : Subgroup.Normalizes W1 MF := ⟨hW1normMF⟩
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  letI : MulDistribMulAction W1 (MF ⧸ H0.subgroupOf MF) :=
    quotientMulDistribMulAction (A := W1) (G := MF) (H0.subgroupOf MF) hH0invW1
  rcases hp96 with ⟨hp, hp_eq, _hpData, h96⟩
  rcases h96 with ⟨_hH0MF, _hMFM, _hnormal96, _hchief, hsourceFixed, _hcard⟩
  rcases hsourceFixed with ⟨_hnormalSrc, hsourceCard⟩
  have hsourceCard' :
      Nat.card {x : MF ⧸ H0.subgroupOf MF //
        ∀ h : MF, QuotientGroup.mk' (H0.subgroupOf MF) h = x →
          ∀ w : G, w ∈ W1 → ⁅w, (h : G)⁆ ∈ H0} = p := by
    simpa [hp_eq] using hsourceCard
  have hsource_eq_fixed :
      Nat.card {x : MF ⧸ H0.subgroupOf MF //
        ∀ h : MF, QuotientGroup.mk' (H0.subgroupOf MF) h = x →
          ∀ w : G, w ∈ W1 → ⁅w, (h : G)⁆ ∈ H0} =
        Nat.card (fixedPointSubgroup W1 (MF ⧸ H0.subgroupOf MF)) := by
    simpa using
      theorem_9_7_W1_fixedPointSubgroup_card_eq_source_subtype_sec9
        MF W1 H0 hH0invW1 hnormalH0
  have hfixedCard :
      Nat.card (fixedPointSubgroup W1 (MF ⧸ H0.subgroupOf MF)) = p :=
    hsource_eq_fixed.symm.trans hsourceCard'
  intro htop
  have hquotCard_eq_p :
      Nat.card (MF ⧸ H0.subgroupOf MF) = p := by
    calc
      Nat.card (MF ⧸ H0.subgroupOf MF) =
          Nat.card (⊤ : Subgroup (MF ⧸ H0.subgroupOf MF)) := by
            rw [Subgroup.card_top]
      _ = Nat.card (fixedPointSubgroup W1 (MF ⧸ H0.subgroupOf MF)) := by
            rw [htop]
      _ = p := hfixedCard
  have hpow_ne_p : p ^ q ≠ p := by
    have hlt : p ^ 1 < p ^ q := Nat.pow_lt_pow_right hpprime.one_lt hqprime.one_lt
    exact (by simpa using hlt.ne.symm)
  have hbarCard' : Nat.card (MF ⧸ H0.subgroupOf MF) = p ^ q := by
    simpa using hbarCard
  exact hpow_ne_p (hbarCard'.symm.trans hquotCard_eq_p)

public theorem theorem_9_7_quotient_finrank_eq_q_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 : Subgroup G} {p q : ℕ}
    (hpprime : Nat.Prime p)
    (hnormalH0 : (H0.subgroupOf MF).Normal)
    (hbarElem :
      letI : (H0.subgroupOf MF).Normal := hnormalH0
      IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF))
    (hbarCard :
      letI : (H0.subgroupOf MF).Normal := hnormalH0
      Nat.card (MF ⧸ H0.subgroupOf MF) = p ^ q) :
    letI : Fact p.Prime := ⟨hpprime⟩
    letI : (H0.subgroupOf MF).Normal := hnormalH0
    letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
    Module.finrank (ZMod p) (Additive (MF ⧸ H0.subgroupOf MF)) = q := by
  classical
  letI : Fact p.Prime := ⟨hpprime⟩
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
  have h_add_card :
      Nat.card (Additive (MF ⧸ H0.subgroupOf MF)) =
        Nat.card (MF ⧸ H0.subgroupOf MF) :=
    Nat.card_congr
      { toFun := Additive.toMul
        invFun := Additive.ofMul
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl }
  have hcard_add : Nat.card (Additive (MF ⧸ H0.subgroupOf MF)) = p ^ q := by
    rw [h_add_card, hbarCard]
  have hnat := Module.natCard_eq_pow_finrank (K := ZMod p)
    (V := Additive (MF ⧸ H0.subgroupOf MF))
  have hnat' :
      Nat.card (Additive (MF ⧸ H0.subgroupOf MF)) =
        p ^ Module.finrank (ZMod p)
          (Additive (MF ⧸ H0.subgroupOf MF)) := by
    simpa [Nat.card_eq_fintype_card, ZMod.card] using hnat
  have hpow :
      p ^ Module.finrank (ZMod p) (Additive (MF ⧸ H0.subgroupOf MF)) =
        p ^ q :=
    hnat'.symm.trans hcard_add
  exact Nat.pow_right_injective hpprime.two_le hpow


private theorem theorem_9_7_quotientBarUCyclicData_of_field_model_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 U C W1 : Subgroup G} {p q u : ℕ} :
    C ≤ U →
      quotientFieldSemidirectModelData MF H0 U C W1 p q u →
        quotientBarUCyclicData U C u := by
  intro hCU hfield
  rcases hfield with
    ⟨_hnH0, hnC, _hW1normU, _hCinv, F, fieldInst, fintypeInst, Ustar,
      _hFcard, hUstarcard, _hcyc, _hspan, _phiH, phiU, _phiW, _hactU,
      _hactW⟩
  letI : Field F := fieldInst
  letI : Fintype F := fintypeInst
  refine ⟨hCU, hnC, ?_, ?_⟩
  · exact isCyclic_of_surjective phiU.symm.toMonoidHom phiU.symm.surjective
  · calc
      Nat.card (U ⧸ C.subgroupOf U) = Nat.card Ustar := Nat.card_congr phiU.toEquiv
      _ = u := hUstarcard

private theorem theorem_9_7_case_b_divides_field_units_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 U C W1 : Subgroup G} {p q u : ℕ} :
    quotientFieldSemidirectModelData MF H0 U C W1 p q u →
      u ∣ p ^ q - 1 := by
  intro hfield
  rcases hfield with
    ⟨_hnH0, _hnC, _hW1normU, _hCinv, F, fieldInst, fintypeInst, Ustar,
      hFcard, hUstarcard, _hcyc, _hspan, _phiH, _phiU, _phiW, _hactU,
      _hactW⟩
  letI : Field F := fieldInst
  letI : Fintype F := fintypeInst
  have hsub : Nat.card Ustar ∣ Nat.card Fˣ :=
    Subgroup.card_subgroup_dvd_card Ustar
  rw [Nat.card_units, hFcard] at hsub
  simpa [hUstarcard] using hsub

private theorem theorem_9_7_field_unit_fixed_of_order_dvd_prime_pred_sec9
    {F : Type u} [Field F] {p : ℕ} [Fact (Nat.Prime p)] [CharP F p]
    (a : Fˣ) :
    orderOf a ∣ p - 1 →
      ∀ σ : RingAut F, Units.map σ.toMonoidHom a = a := by
  intro horder σ
  apply Units.ext
  have hp : Nat.Prime p := Fact.out
  have hpow_units : a ^ (p - 1) = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp horder
  have hpow_field : (a : F) ^ (p - 1) = 1 := by
    simpa using congrArg (fun z : Fˣ => (z : F)) hpow_units
  have hpowp : (a : F) ^ p = (a : F) := by
    calc
      (a : F) ^ p = (a : F) ^ ((p - 1) + 1) := by
        rw [Nat.sub_one_add_one_eq_of_pos hp.pos]
      _ = (a : F) := by simp [pow_succ, hpow_field]
  have hbot : (a : F) ∈ (⊥ : Subfield F) := by
    exact (Subfield.mem_bot_iff_pow_eq_self F p).2 hpowp
  rcases (mem_bot_iff_intCast p F).1 hbot with ⟨n, hn⟩
  calc
    (Units.map σ.toMonoidHom a : F) = σ (a : F) := rfl
    _ = σ (n : F) := by rw [← hn]
    _ = (n : F) := by simp
    _ = (a : F) := hn

private theorem theorem_9_7_finite_field_unit_fixed_of_order_dvd_prime_pred_sec9
    {F : Type u} [Field F] [Fintype F] {p q : ℕ}
    (hp : Nat.Prime p) (hcard : Nat.card F = p ^ q) (a : Fˣ) :
    orderOf a ∣ p - 1 →
      ∀ σ : RingAut F, Units.map σ.toMonoidHom a = a := by
  intro horder
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hcard' : Fintype.card F = p ^ q := by
    simpa [Nat.card_eq_fintype_card] using hcard
  haveI : CharP F p :=
    charP_of_card_eq_prime_pow (R := F) (p := p) (f := q) hcard'
  exact theorem_9_7_field_unit_fixed_of_order_dvd_prime_pred_sec9 a horder

private theorem theorem_9_7_mem_prime_field_zpowers_of_frobenius_fixed_sec9
    {F : Type u} [Field F] [Fintype F] {p : ℕ}
    [Fact (Nat.Prime p)] [CharP F p] {z : F} :
    z ^ p = z →
      Multiplicative.ofAdd z ∈
        Subgroup.zpowers (Multiplicative.ofAdd (1 : F)) := by
  intro hz
  have hzbot : z ∈ (⊥ : Subfield F) := by
    exact (Subfield.mem_bot_iff_pow_eq_self F p).2 hz
  rcases (mem_bot_iff_intCast p F).1 hzbot with ⟨n, hn⟩
  rw [← hn]
  rcases n with n | n
  · refine Subgroup.mem_zpowers_iff.mpr ⟨(n : ℤ), ?_⟩
    rw [← ofAdd_zsmul]
    simp
  · refine Subgroup.mem_zpowers_iff.mpr ⟨-((n.succ : ℕ) : ℤ), ?_⟩
    rw [← ofAdd_zsmul]
    simp

private theorem theorem_9_7_prime_field_zpowers_card_sec9
    {F : Type u} [Field F] {p : ℕ}
    [Fact (Nat.Prime p)] [CharP F p] :
    Nat.card (Subgroup.zpowers (Multiplicative.ofAdd (1 : F))) = p := by
  have horder : orderOf (Multiplicative.ofAdd (1 : F)) = p := by
    rw [orderOf_ofAdd_eq_addOrderOf]
    exact CharP.eq F (CharP.addOrderOf_one F) (inferInstance : CharP F p)
  rw [← horder]
  exact Nat.card_zpowers _

private theorem theorem_9_7_case_b_quotient_divisibility_sec9
    {p q u : ℕ} :
    Nat.Prime p →
      Nat.Coprime u (p - 1) →
        u ∣ p ^ q - 1 →
          u ∣ (p ^ q - 1) / (p - 1) := by
  intro _hp hcop hdiv
  have hpminus_dvd : p - 1 ∣ p ^ q - 1 :=
    Nat.sub_one_dvd_pow_sub_one p q
  have hmul :
      (p ^ q - 1) / (p - 1) * (p - 1) = p ^ q - 1 :=
    Nat.div_mul_cancel hpminus_dvd
  have hdiv_mul : u ∣ (p ^ q - 1) / (p - 1) * (p - 1) := by
    simpa [hmul] using hdiv
  exact hcop.dvd_of_dvd_mul_right hdiv_mul

private theorem theorem_9_7_coprime_of_common_divisors_eq_one_sec9
    {p u : ℕ} :
    (∀ d : ℕ, d ∣ u → d ∣ p - 1 → d = 1) →
      Nat.Coprime u (p - 1) := by
  intro hcommon
  rw [Nat.coprime_iff_gcd_eq_one]
  exact hcommon (Nat.gcd u (p - 1))
    (Nat.gcd_dvd_left u (p - 1)) (Nat.gcd_dvd_right u (p - 1))

private theorem theorem_9_7_common_divisors_eq_one_of_no_common_prime_sec9
    {u n : ℕ} :
    (∀ r : ℕ, Nat.Prime r → r ∣ u → r ∣ n → False) →
      ∀ d : ℕ, d ∣ u → d ∣ n → d = 1 := by
  intro hno d hdu hdn
  apply (Nat.eq_one_iff_not_exists_prime_dvd).2
  intro r hr hrd
  exact hno r hr (dvd_trans hrd hdu) (dvd_trans hrd hdn)

private theorem theorem_9_7_prime_order_action_image_card_dvd_pred_sec9
    {Q A : Type u} [Group Q] [Finite Q] [Group A]
    {p a : ℕ} :
    Nat.Prime p →
      Nat.card Q = p →
        (ρ : A →* MulAut Q) →
          Nat.card ρ.range = a →
            a ∣ p - 1 := by
  intro hp hQcard ρ hρcard
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : IsCyclic Q := isCyclic_of_prime_card (α := Q) (p := p) hQcard
  have hdiv : Nat.card ρ.range ∣ Nat.card (MulAut Q) :=
    Subgroup.card_subgroup_dvd_card ρ.range
  have hAut : Nat.card (MulAut Q) = p - 1 := by
    rw [IsCyclic.card_mulAut, hQcard, Nat.totient_prime hp]
  rw [← hρcard]
  simpa [hAut] using hdiv

private theorem theorem_9_7_case_a_divides_p_minus_one_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 U C W1 : Subgroup G} {p q a : ℕ} :
    Nat.Prime p →
      Nat.Prime q →
        (∃ hnormal : (H0.subgroupOf MF).Normal,
          letI : (H0.subgroupOf MF).Normal := hnormal
          ∃ H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF),
            (∀ i, Nat.card (H i) = p) ∧
              (∀ i, quotientSubgroupNormalizedBy MF H0 U (H i)) ∧
              iSupIndep H ∧
              iSup H = ⊤ ∧
              (∀ i, quotientFactorActionCentralizerData MF H0 U C (H i) a) ∧
              ∃ hqpos : 0 < q,
                ∀ i : Fin q,
                  ∃ w : W1,
                    quotientSubgroupConjugateByElement MF H0
                      (H ⟨0, hqpos⟩) (H i) (w : G)) →
          a ∣ p - 1 := by
  intro hp hq hdecomp
  rcases hdecomp with
    ⟨hnormalH0, H, hHcard, _hHnorm, _hInd, _hSup, hfactor, _hconj⟩
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  have hqpos : 0 < q := hq.pos
  rcases hfactor ⟨0, hqpos⟩ with
    ⟨_hnormalC, ρ, _hcyc, hρcard, _haction, _hker⟩
  exact theorem_9_7_prime_order_action_image_card_dvd_pred_sec9
    hp (hHcard ⟨0, hqpos⟩) ρ hρcard

private theorem theorem_9_7_W1_le_normalizer_U_of_hypothesis_9_2_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G} {q : ℕ} :
  hypothesis_9_2_statement M MF U W1 W2 q →
      W1 ≤ Subgroup.normalizer (U : Set G) := by
  intro h92
  rcases h92.typePDefinitionData with
    ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD,
      _hUnil, hW1normU, _hcompDU, _hMFnotcyc, _hsecond, _hfitEq,
      _hfitLeD, _hW2le, _hW2cyc, _hW2ne, _hcentW1, _hnormX⟩
  intro w hw
  exact (mem_subgroupNormalizerIn.mp (hW1normU hw)).1

private theorem theorem_9_7_W1_card_coprime_U_card_of_hypothesis_9_2_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G} {q : ℕ} :
    hypothesis_9_2_statement M MF U W1 W2 q →
      Nat.Coprime (Nat.card W1) (Nat.card U) := by
  intro h92
  let D : Subgroup G := ambientDerivedSubgroup M
  rcases h92.typePDefinitionData with
    ⟨_hMFsource, _hW1cyc, _hW1ne, hW1hall, hcompMW1, hUleD,
      _hUnil, _hW1normU, _hcompDU, _hMFnotcyc, _hsecond, _hfitEq,
      _hfitLeD, _hW2le, _hW2cyc, _hW2ne, _hcentW1, _hnormX⟩
  rcases hW1hall with ⟨hW1leM, hHallW1M⟩
  have hDleM : D ≤ M := by
    dsimp [D]
    exact section12_ambientDerivedSubgroup_le
  have hDnormalM : (D.subgroupOf M).Normal := by
    dsimp [D]
    exact (section12_normalIn_ambientDerivedSubgroup (E := M)).2
  have hDdisjW1 : Disjoint (D.subgroupOf M) (W1.subgroupOf M) := by
    have hDdisj : Disjoint D W1 := by
      simpa [D] using hcompMW1.2.2.2
    rw [disjoint_iff] at hDdisj ⊢
    apply le_antisymm
    · intro x hx
      have hxAmb : (x : G) ∈ D ⊓ W1 := by
        exact ⟨by simpa [Subgroup.mem_subgroupOf, D] using hx.1,
          by simpa [Subgroup.mem_subgroupOf] using hx.2⟩
      have hxBot : (x : G) ∈ (⊥ : Subgroup G) := by
        simpa [hDdisj] using hxAmb
      ext
      simpa using hxBot
    · exact bot_le
  have hDsupW1 : D.subgroupOf M ⊔ W1.subgroupOf M = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (A := D) (A' := W1) (B := M) hDleM hW1leM]
    exact Subgroup.subgroupOf_eq_top.2 (by
      intro x hxM
      have hxSup : x ∈ ambientDerivedSubgroup M ⊔ W1 := by
        rw [← hcompMW1.2.2.1]
        exact hxM
      simpa [D] using hxSup)
  have hDcompW1 : (D.subgroupOf M).IsComplement' (W1.subgroupOf M) := by
    letI : (D.subgroupOf M).Normal := hDnormalM
    exact isComplement'_of_disjoint_sup_eq_top_of_normal
      (D.subgroupOf M) (W1.subgroupOf M) hDdisjW1 hDsupW1
  have hW1index : (W1.subgroupOf M).index = Nat.card D := by
    have hidx := hDcompW1.index_eq_card
    rw [natCard_subgroupOf_eq D M hDleM] at hidx
    exact hidx
  have hW1cardSub : Nat.card (W1.subgroupOf M) = Nat.card W1 :=
    natCard_subgroupOf_eq W1 M hW1leM
  have hcopD : Nat.Coprime (Nat.card W1) (Nat.card D) := by
    have hcopSub : Nat.Coprime (Nat.card (W1.subgroupOf M)) (Nat.card D) := by
      simpa [Nat.card_eq_fintype_card, hW1index] using hHallW1M.card_coprime_index
    rw [hW1cardSub] at hcopSub
    exact hcopSub
  have hUcardDvdD : Nat.card U ∣ Nat.card D :=
    Subgroup.card_dvd_of_le (by simpa [D] using hUleD)
  exact Nat.Coprime.of_dvd_right hUcardDvdD hcopD

private theorem theorem_9_7_fixedPointSubgroup_W1_U_eq_bot_of_hypothesis_9_2_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G} {q : ℕ}
    (h92 : hypothesis_9_2_statement M MF U W1 W2 q)
    (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G)) :
    letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
    fixedPointSubgroup W1 U = ⊥ := by
  classical
  letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
  rw [Subgroup.eq_bot_iff_forall]
  intro x hxfix
  rcases h92.typePDefinitionData with
    ⟨_hMFsource, _hW1cyc, hW1ne, _hW1hall, _hcompMW1, hUleD,
      _hUnil, _hW1normU, hcompDU, _hMFnotcyc, _hsecond, _hfitEq,
      _hfitLeD, hW2le, _hW2cyc, _hW2ne, hcentW1, _hnormX⟩
  rcases Subgroup.ne_bot_iff_exists_ne_one.mp hW1ne with ⟨w, hw_ne⟩
  let wG : G := (w : G)
  have hwW1 : wG ∈ W1 := w.property
  have hwG_ne : wG ≠ 1 := by
    intro hw
    exact hw_ne (Subtype.ext hw)
  have hxD : (x : G) ∈ ambientDerivedSubgroup M := hUleD x.property
  have hxfix_w : w • x = x := by
    simpa using hxfix w
  have hxconj : wG * (x : G) * wG⁻¹ = (x : G) := by
    simpa [wG, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
      congrArg Subtype.val hxfix_w
  have hxcomm : (x : G) * wG = wG * (x : G) := by
    have hmul := congrArg (fun t : G => t * wG) hxconj
    simpa [wG, mul_assoc] using hmul.symm
  have hxcent : (x : G) ∈ elementCentralizerIn (ambientDerivedSubgroup M) wG := by
    refine ⟨hxD, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr hxcomm
  have hxW2 : (x : G) ∈ W2 := by
    simpa [hcentW1 wG hwW1 hwG_ne] using hxcent
  have hxMF : (x : G) ∈ MF := (le_inf_iff.mp hW2le).1 hxW2
  have hxBot : (x : G) ∈ (⊥ : Subgroup G) := by
    have hdisj : Disjoint MF U := hcompDU.2.2.2
    exact (Subgroup.disjoint_def.mp hdisj) hxMF x.property
  exact Subtype.ext (by simpa using hxBot)

public theorem theorem_9_7_quotientCentralizerIn_isInvariant_W1_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 H0 C : Subgroup G} {q : ℕ} {p : Nat.Primes}
    (h92 : hypothesis_9_2_statement M MF U W1 W2 q)
    (hpData : hoReductionData M MF U W2 H0 p)
    (hC : quotientCentralizerIn MF H0 U C)
    (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G))
    (hW1normMF : W1 ≤ Subgroup.normalizer (MF : Set G)) :
    letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
    IsInvariant W1 U (C.subgroupOf U) := by
  classical
  letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
  rcases hpData with
    ⟨hH0MF, hMF_M, hH0_normal_M, _hH0_normal_MF, _hH0lt, _helem,
      _htypeIIIIV⟩
  have hW1leM : W1 ≤ M := by
    rcases h92.typePDefinitionData with
      ⟨_hMFsource, _hW1cyc, _hW1ne, hW1hall, _hcompMW1, _hUleD,
        _hUnil, _hW1normU, _hcompDU, _hMFnotcyc, _hsecond, _hfitEq,
        _hfitLeD, _hW2le, _hW2cyc, _hW2ne, _hcentW1, _hnormX⟩
    exact hW1hall.1
  have hH0M : H0 ≤ M := hH0MF.trans hMF_M
  have hforward :
      ∀ (w : W1) (x : U), x ∈ C.subgroupOf U → w • x ∈ C.subgroupOf U := by
    intro w x hxCsub
    have hxC : (x : G) ∈ C := by
      simpa [Subgroup.mem_subgroupOf] using hxCsub
    have hxCent : ∀ h : G, h ∈ MF → ⁅(x : G), h⁆ ∈ H0 :=
      (hC.2 (x : G) x.property).mp hxC
    have hsmulU : (w • x : U).1 ∈ U := (w • x).property
    have hsmulC : (w • x : U).1 ∈ C := by
      rw [(hC.2 ((w • x : U).1) hsmulU)]
      intro h hhMF
      have hwinv_norm : (w : G)⁻¹ ∈ Subgroup.normalizer (MF : Set G) :=
        (Subgroup.normalizer (MF : Set G)).inv_mem (hW1normMF w.property)
      have hh' : (w : G)⁻¹ * h * (w : G) ∈ MF := by
        simpa [mul_assoc] using
          (Subgroup.mem_normalizer_iff.mp hwinv_norm h).1 hhMF
      have hcomm : ⁅(x : G), (w : G)⁻¹ * h * (w : G)⁆ ∈ H0 :=
        hxCent ((w : G)⁻¹ * h * (w : G)) hh'
      let wM : M := ⟨(w : G), hW1leM w.property⟩
      let cM : M := ⟨⁅(x : G), (w : G)⁻¹ * h * (w : G)⁆, hH0M hcomm⟩
      have hcM : cM ∈ H0.subgroupOf M := by
        simpa [cM, Subgroup.mem_subgroupOf] using hcomm
      have hconjM : wM * cM * wM⁻¹ ∈ H0.subgroupOf M :=
        hH0_normal_M.conj_mem cM hcM wM
      have hconjH0 :
          (w : G) * ⁅(x : G), (w : G)⁻¹ * h * (w : G)⁆ * (w : G)⁻¹ ∈ H0 := by
        simpa [wM, cM, Subgroup.mem_subgroupOf] using hconjM
      have hcomm_eq :
          ⁅((w • x : U) : G), h⁆ =
            (w : G) * ⁅(x : G), (w : G)⁻¹ * h * (w : G)⁆ * (w : G)⁻¹ := by
        simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
          commutatorElement_def]
        group
      rw [hcomm_eq]
      exact hconjH0
    simpa [Subgroup.mem_subgroupOf] using hsmulC
  refine ⟨?_⟩
  intro w x
  constructor
  · exact hforward w x
  · intro hxCsub
    have hx' : (w⁻¹ : W1) • (w • x) ∈ C.subgroupOf U :=
      hforward w⁻¹ (w • x) hxCsub
    simpa using hx'

public theorem theorem_9_7_fixedPointSubgroup_W1_barU_eq_bot_of_isInvariant_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 C : Subgroup G} {q : ℕ}
    (h92 : hypothesis_9_2_statement M MF U W1 W2 q)
    (hnormalC : (C.subgroupOf U).Normal)
    (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G))
    (hCinv :
      letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
      IsInvariant W1 U (C.subgroupOf U)) :
    letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
    letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
      quotientMulDistribMulAction (A := W1) (G := U) (C.subgroupOf U) hCinv
    fixedPointSubgroup W1 (U ⧸ C.subgroupOf U) = ⊥ := by
  classical
  letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
  letI : (C.subgroupOf U).Normal := hnormalC
  letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
    quotientMulDistribMulAction (A := W1) (G := U) (C.subgroupOf U) hCinv
  letI : MulAction.QuotientAction W1 (C.subgroupOf U) :=
    quotientAction_of_isInvariant (A := W1) (C.subgroupOf U) hCinv
  have hUsolv : Group.IsSolvable U := by
    rcases h92.typePDefinitionData with
      ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD,
        hUnil, _hW1normU, _hcompDU, _hMFnotcyc, _hsecond, _hfitEq,
        _hfitLeD, _hW2le, _hW2cyc, _hW2ne, _hcentW1, _hnormX⟩
    letI : Group.IsNilpotent U := hUnil
    exact IsNilpotent.to_isSolvable
  have hcop : Nat.Coprime (Nat.card W1) (Nat.card U) :=
    theorem_9_7_W1_card_coprime_U_card_of_hypothesis_9_2_sec9 h92
  have hfixU_bot : fixedPointSubgroup W1 U = ⊥ :=
    theorem_9_7_fixedPointSubgroup_W1_U_eq_bot_of_hypothesis_9_2_sec9
      h92 hW1normU
  have hfix_map_bot :
      (fixedPointSubgroup W1 U).map (QuotientGroup.mk' (C.subgroupOf U)) = ⊥ := by
    rw [hfixU_bot]
    simp
  have hfix_quot_eq :
      fixedPointSubgroup W1 (U ⧸ C.subgroupOf U) =
        (fixedPointSubgroup W1 U).map (QuotientGroup.mk' (C.subgroupOf U)) :=
    fixedPointSubgroup_quotient_eq_map_of_solvable_coprime_action
      (G := U) (A := W1) hUsolv hcop (π := (∅ : Set Nat.Primes))
      (C.subgroupOf U) hCinv
  rw [hfix_quot_eq, hfix_map_bot]


private theorem theorem_9_7_W1_le_normalizer_MF_of_hypothesis_9_2_sec9
    {G : Type u} [Group G] [Finite G]
    {M MF U W1 W2 : Subgroup G} {q : ℕ} :
    hypothesis_9_2_statement M MF U W1 W2 q →
      W1 ≤ Subgroup.normalizer (MF : Set G) := by
  intro h92
  exact le_sup_right.trans
    (theorem_9_3_action_normalizes_and_solvable_sec9 M MF U W1 W2 q h92).1

public theorem theorem_9_7_mem_C_of_barU_fixed_sec9
    {G : Type u} [Group G] [Finite G]
    {U W1 C : Subgroup G}
    (hnormalC : (C.subgroupOf U).Normal)
    (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G))
    (hCinv :
      letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
      IsInvariant W1 U (C.subgroupOf U))
    (hfixedBot :
      letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
      letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
        quotientMulDistribMulAction (A := W1) (G := U)
          (C.subgroupOf U) hCinv
      fixedPointSubgroup W1 (U ⧸ C.subgroupOf U) = ⊥)
    (x : U)
    (hxfix :
      letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
      letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
        quotientMulDistribMulAction (A := W1) (G := U)
          (C.subgroupOf U) hCinv
      QuotientGroup.mk' (C.subgroupOf U) x ∈
        fixedPointSubgroup W1 (U ⧸ C.subgroupOf U)) :
    x ∈ C.subgroupOf U := by
  classical
  letI : (C.subgroupOf U).Normal := hnormalC
  letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
  letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
    quotientMulDistribMulAction (A := W1) (G := U) (C.subgroupOf U) hCinv
  have hxbot :
      QuotientGroup.mk' (C.subgroupOf U) x ∈
        (⊥ : Subgroup (U ⧸ C.subgroupOf U)) := by
    simpa [hfixedBot] using hxfix
  have hxone : QuotientGroup.mk' (C.subgroupOf U) x = 1 := by
    simpa using hxbot
  exact (QuotientGroup.eq_one_iff (N := C.subgroupOf U) (x := x)).1 hxone

private theorem theorem_9_7_irreducible_representation_of_quotientIrreducible_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 U : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hnormalH0 : (H0.subgroupOf MF).Normal)
    (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G))
    (hH0invU :
      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
      IsInvariant U MF (H0.subgroupOf MF))
    (hbarElem :
      letI : (H0.subgroupOf MF).Normal := hnormalH0
      IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF))
    [Nontrivial (MF ⧸ H0.subgroupOf MF)] :
    quotientIrreducibleActionData MF H0 U →
      letI : (H0.subgroupOf MF).Normal := hnormalH0
      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
      letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
        quotientMulDistribMulAction (A := U) (G := MF)
          (H0.subgroupOf MF) hH0invU
      Representation.IsIrreducible
        (Theory.Representation.ofElementaryAbelianAction (A := U)
          (G := MF ⧸ H0.subgroupOf MF) (p := p)) := by
  classical
  intro hirred
  let H0MF : Subgroup MF := H0.subgroupOf MF
  haveI : H0MF.Normal := hnormalH0
  letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
  have hH0invU' : IsInvariant U MF H0MF := by
    simpa [H0MF] using hH0invU
  letI : MulDistribMulAction U (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := U) (G := MF) H0MF hH0invU'
  haveI : IsElementaryAbelian p (MF ⧸ H0MF) := by
    simpa [H0MF] using hbarElem
  rcases hirred with ⟨_hnormalIrred, hminv⟩
  let ρ :=
    Theory.Representation.ofElementaryAbelianAction (A := U)
      (G := MF ⧸ H0MF) (p := p)
  refine
    { toNontrivial := inferInstance
      eq_bot_or_eq_top := ?_ }
  intro S
  let N : Subgroup (MF ⧸ H0MF) := S.toSubmodule.toAddSubgroup.toSubgroup'
  have hN_inv : IsInvariant U (MF ⧸ H0MF) N := by
    have hmap_mem (a : U) {x : MF ⧸ H0MF} (hx : x ∈ N) : a • x ∈ N := by
      change Additive.ofMul (a • x) ∈ S.toSubmodule
      have hx' : Additive.ofMul x ∈ S.toSubmodule := by
        change Additive.ofMul x ∈ S.toSubmodule at hx
        exact hx
      have hx'' := S.apply_mem_toSubmodule a hx'
      simpa [ρ, Theory.Representation.ofElementaryAbelianAction_apply_ofMul] using hx''
    refine { invariant := ?_ }
    intro a x
    constructor
    · intro hx
      exact hmap_mem a hx
    · intro hx
      have hx' : (a : U)⁻¹ • ((a : U) • x) ∈ N := hmap_mem (a : U)⁻¹ hx
      simpa [smul_smul] using hx'
  have hN_norm : quotientSubgroupNormalizedBy MF H0 U N := by
    simpa [H0MF, N] using
      quotientSubgroupNormalizedBy_of_isInvariant_sec9 MF H0 U hH0invU' N hN_inv
  rcases hminv N hN_norm with hN_bot | hN_top
  · left
    apply Subrepresentation.toSubmodule_injective
    ext x
    have hxN : Additive.toMul x ∈ N ↔ x ∈ S.toSubmodule := by
      simp [N]
    rw [← hxN, hN_bot]
    constructor
    · intro hx
      simpa [hx]
    · intro hx
      change x = 0 at hx
      subst x
      exact Subgroup.one_mem _
  · right
    apply Subrepresentation.toSubmodule_injective
    ext x
    have hxN : Additive.toMul x ∈ N ↔ x ∈ S.toSubmodule := by
      simp [N]
    rw [← hxN, hN_top]
    constructor
    · intro _hx
      exact trivial
    · intro _hx
      exact trivial

private theorem theorem_9_7_exists_proper_U_normalized_quotient_subgroup_of_not_irreducible_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 U : Subgroup G}
    (hnormal : (H0.subgroupOf MF).Normal) :
    ¬ quotientIrreducibleActionData MF H0 U →
      letI : (H0.subgroupOf MF).Normal := hnormal
      ∃ Q : Subgroup (MF ⧸ H0.subgroupOf MF),
        quotientSubgroupNormalizedBy MF H0 U Q ∧ Q ≠ ⊥ ∧ Q ≠ ⊤ := by
  classical
  intro hnon
  letI : (H0.subgroupOf MF).Normal := hnormal
  by_contra hnone
  apply hnon
  refine ⟨hnormal, ?_⟩
  intro Q hQnorm
  by_cases hbot : Q = ⊥
  · exact Or.inl hbot
  · by_cases htop : Q = ⊤
    · exact Or.inr htop
    · exfalso
      exact hnone ⟨Q, hQnorm, hbot, htop⟩

private theorem theorem_9_7_fixedPointSubgroup_mem_of_generator_fixed_sec9
    {A : Type u} {X : Type v} [Group A] [Group X] [MulDistribMulAction A X]
    {g : A} {x : X}
    (hg : Subgroup.zpowers g = ⊤)
    (hx : g • x = x) :
    x ∈ fixedPointSubgroup A X := by
  intro a
  have ha : a ∈ Subgroup.zpowers g := by
    rw [hg]
    exact Subgroup.mem_top a
  exact smul_eq_self_of_mem_zpowers ha hx

private theorem theorem_9_7_generator_fixed_coset_of_smul_div_mem_C_sec9
    {G : Type u} [Group G]
    {U W1 C : Subgroup G}
    (hnormalC : (C.subgroupOf U).Normal)
    (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G))
    (hCinv :
      letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
      IsInvariant W1 U (C.subgroupOf U))
    (w0 : W1) (x : U)
    (hxdiv :
      letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
      (w0 • x) / x ∈ C.subgroupOf U) :
    letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
    letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
      quotientMulDistribMulAction (A := W1) (G := U) (C.subgroupOf U) hCinv
    letI : (C.subgroupOf U).Normal := hnormalC
    w0 • (QuotientGroup.mk' (C.subgroupOf U) x) =
      QuotientGroup.mk' (C.subgroupOf U) x := by
  letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
  letI : (C.subgroupOf U).Normal := hnormalC
  letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
    quotientMulDistribMulAction (A := W1) (G := U) (C.subgroupOf U) hCinv
  change QuotientGroup.mk' (C.subgroupOf U) (w0 • x) =
    QuotientGroup.mk' (C.subgroupOf U) x
  exact
    (QuotientGroup.eq_iff_div_mem (N := C.subgroupOf U) (x := w0 • x)
      (y := x)).2 hxdiv

private theorem theorem_9_7_smul_div_mem_C_of_quotient_centralizes_sec9
    {G : Type u} [Group G]
    {MF H0 U W1 C : Subgroup G}
    (hC : quotientCentralizerIn MF H0 U C)
    (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G))
    (w0 : W1) (x : U)
    (hcent :
      letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
      ∀ h : G, h ∈ MF → ⁅(((w0 • x) / x : U) : G), h⁆ ∈ H0) :
    letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
    (w0 • x) / x ∈ C.subgroupOf U := by
  letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
  have hiff :
      ((((w0 • x) / x : U) : G) ∈ C ↔
        ∀ h : G, h ∈ MF → ⁅(((w0 • x) / x : U) : G), h⁆ ∈ H0) :=
    hC.2 ((((w0 • x) / x : U) : G)) (((w0 • x) / x : U).property)
  have hdivC : ((((w0 • x) / x : U) : G) ∈ C) := hiff.mpr hcent
  change ((((w0 • x) / x : U) : G) ∈ C)
  exact hdivC

public theorem theorem_9_7_quotient_action_fixed_to_commutator_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 U : Subgroup G}
    (hnormalH0 : (H0.subgroupOf MF).Normal)
    (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G))
    (hH0invU :
      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
      IsInvariant U MF (H0.subgroupOf MF))
    (x : U)
    (hfix :
      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
      letI : (H0.subgroupOf MF).Normal := hnormalH0
      letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
        quotientMulDistribMulAction (A := U) (G := MF)
          (H0.subgroupOf MF) hH0invU
      ∀ h : MF, x • QuotientGroup.mk' (H0.subgroupOf MF) h =
        QuotientGroup.mk' (H0.subgroupOf MF) h) :
    ∀ h : G, h ∈ MF → ⁅(x : G), h⁆ ∈ H0 := by
  classical
  let H0MF : Subgroup MF := H0.subgroupOf MF
  haveI : H0MF.Normal := hnormalH0
  letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
  have hH0invU' : IsInvariant U MF H0MF := by
    simpa [H0MF] using hH0invU
  letI : MulDistribMulAction U (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := U) (G := MF) H0MF hH0invU'
  intro h hhMF
  let hMF : MF := ⟨h, hhMF⟩
  have hfixed :
      x • QuotientGroup.mk' H0MF hMF = QuotientGroup.mk' H0MF hMF := by
    simpa [H0MF] using hfix hMF
  have hq : QuotientGroup.mk' H0MF (x • hMF) = QuotientGroup.mk' H0MF hMF := by
    simpa using hfixed
  have hcommH0MF : ((x • hMF : MF) / hMF) ∈ H0MF :=
    QuotientGroup.eq_iff_div_mem.mp hq
  have hval : ((((x • hMF : MF) / hMF : MF) : G) = ⁅(x : G), h⁆) := by
    simp [hMF, div_eq_mul_inv, commutatorElement_def,
      Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, mul_assoc]
  simpa [H0MF, Subgroup.mem_subgroupOf, hval] using hcommH0MF

private theorem theorem_9_7_quotient_action_fixed_of_commutator_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 U : Subgroup G}
    (hnormalH0 : (H0.subgroupOf MF).Normal)
    (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G))
    (hH0invU :
      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
      IsInvariant U MF (H0.subgroupOf MF))
    (x : U)
    (hcomm : ∀ h : G, h ∈ MF → ⁅(x : G), h⁆ ∈ H0) :
    letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
    letI : (H0.subgroupOf MF).Normal := hnormalH0
    letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
      quotientMulDistribMulAction (A := U) (G := MF)
        (H0.subgroupOf MF) hH0invU
    ∀ y : MF ⧸ H0.subgroupOf MF, x • y = y := by
  classical
  let H0MF : Subgroup MF := H0.subgroupOf MF
  haveI : H0MF.Normal := hnormalH0
  letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
  have hH0invU' : IsInvariant U MF H0MF := by
    simpa [H0MF] using hH0invU
  letI : MulDistribMulAction U (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := U) (G := MF) H0MF hH0invU'
  intro y
  refine QuotientGroup.induction_on y ?_
  intro h
  have hq : QuotientGroup.mk' H0MF (x • h) = QuotientGroup.mk' H0MF h := by
    apply QuotientGroup.eq_iff_div_mem.mpr
    have hcommH0 : ⁅(x : G), (h : G)⁆ ∈ H0 := hcomm (h : G) h.property
    have hval : ((((x • h : MF) / h : MF) : G) = ⁅(x : G), (h : G)⁆) := by
      simp [div_eq_mul_inv, commutatorElement_def,
        Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, mul_assoc]
    simpa [H0MF, Subgroup.mem_subgroupOf, hval] using hcommH0
  simpa using hq

private theorem
    theorem_9_7_quotient_action_fixed_of_inv_quotientSubgroupCentralizedByElement_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 U : Subgroup G}
    (hnormalH0 : (H0.subgroupOf MF).Normal)
    (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G))
    (hH0invU :
      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
      IsInvariant U MF (H0.subgroupOf MF))
    {Q : Subgroup (MF ⧸ H0.subgroupOf MF)}
    (x : U)
    (hcent :
      quotientSubgroupCentralizedByElement MF H0 Q (((x : U) : G)⁻¹)) :
    letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
    letI : (H0.subgroupOf MF).Normal := hnormalH0
    letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
      quotientMulDistribMulAction (A := U) (G := MF)
        (H0.subgroupOf MF) hH0invU
    ∀ y : MF ⧸ H0.subgroupOf MF, y ∈ Q → x • y = y := by
  classical
  let H0MF : Subgroup MF := H0.subgroupOf MF
  haveI : H0MF.Normal := hnormalH0
  letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
  have hH0invU' : IsInvariant U MF H0MF := by
    simpa [H0MF] using hH0invU
  letI : MulDistribMulAction U (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := U) (G := MF) H0MF hH0invU'
  rcases hcent with ⟨hconjMF, action, haction, hfix⟩
  intro y
  refine QuotientGroup.induction_on y ?_
  intro h hy
  have hleft :
      action (QuotientGroup.mk' H0MF h) =
        x • QuotientGroup.mk' H0MF h := by
    rw [haction h]
    change
      QuotientGroup.mk' H0MF
          ⟨((((x : U) : G)⁻¹)⁻¹ * (h : G) * (((x : U) : G)⁻¹)),
            hconjMF h⟩ =
        QuotientGroup.mk' H0MF (x • h)
    apply congrArg (QuotientGroup.mk' H0MF)
    apply Subtype.ext
    simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
      mul_assoc]
  change x • QuotientGroup.mk' H0MF h = QuotientGroup.mk' H0MF h
  rw [← hleft]
  exact hfix (QuotientGroup.mk' H0MF h) hy

private theorem
    theorem_9_7_quotientSubgroupCentralizedByElement_of_factorActionKernel_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 U C : Subgroup G}
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hnormalC : (C.subgroupOf U).Normal]
    {Q : Subgroup (MF ⧸ H0.subgroupOf MF)}
    {ρ : (U ⧸ C.subgroupOf U) →* MulAut Q}
    (hker :
      ∀ x : U ⧸ C.subgroupOf U,
        ρ x = 1 ↔
          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
            quotientSubgroupCentralizedByElement MF H0 Q (u : G))
    (x : U)
    (hxker : ρ (QuotientGroup.mk' (C.subgroupOf U) x) = 1) :
    quotientSubgroupCentralizedByElement MF H0 Q (x : G) := by
  exact (hker (QuotientGroup.mk' (C.subgroupOf U) x)).mp hxker x rfl

private theorem theorem_9_7_factorActionKernel_of_generator_action_eq_sec9
    {G : Type u} [Group G]
    {U W1 C : Subgroup G}
    [hnormalC : (C.subgroupOf U).Normal]
    (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G))
    {A : Type v} [Group A]
    (ρ : (U ⧸ C.subgroupOf U) →* A)
    (w0 : W1) (x : U)
    (hρeq :
      letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
      ρ (QuotientGroup.mk' (C.subgroupOf U) (w0 • x)) =
        ρ (QuotientGroup.mk' (C.subgroupOf U) x)) :
    letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
    ρ (QuotientGroup.mk' (C.subgroupOf U)
      (((w0 • x) / x : U)⁻¹)) = 1 := by
  classical
  letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
  have hdiv :
      ρ (QuotientGroup.mk' (C.subgroupOf U) ((w0 • x) / x : U)) = 1 := by
    calc
      ρ (QuotientGroup.mk' (C.subgroupOf U) ((w0 • x) / x : U)) =
          ρ (QuotientGroup.mk' (C.subgroupOf U) (w0 • x)) *
            (ρ (QuotientGroup.mk' (C.subgroupOf U) x))⁻¹ := by
            simp [div_eq_mul_inv]
      _ = 1 := by
        rw [hρeq]
        simp
  calc
    ρ (QuotientGroup.mk' (C.subgroupOf U) (((w0 • x) / x : U)⁻¹)) =
        (ρ (QuotientGroup.mk' (C.subgroupOf U) ((w0 • x) / x : U)))⁻¹ := by
        simp
    _ = 1 := by
      rw [hdiv]
      simp

private theorem theorem_9_7_quotient_action_fixed_of_iSup_factors_fixed_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 U : Subgroup G}
    (hnormalH0 : (H0.subgroupOf MF).Normal)
    (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G))
    (hH0invU :
      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
      IsInvariant U MF (H0.subgroupOf MF))
    {q : ℕ}
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hSup : iSup H = ⊤)
    (x : U)
    (hfactor :
      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
      letI : (H0.subgroupOf MF).Normal := hnormalH0
      letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
        quotientMulDistribMulAction (A := U) (G := MF)
          (H0.subgroupOf MF) hH0invU
      ∀ i, ∀ y : MF ⧸ H0.subgroupOf MF, y ∈ H i → x • y = y) :
    letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
    letI : (H0.subgroupOf MF).Normal := hnormalH0
    letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
      quotientMulDistribMulAction (A := U) (G := MF)
        (H0.subgroupOf MF) hH0invU
    ∀ h : MF, x • QuotientGroup.mk' (H0.subgroupOf MF) h =
      QuotientGroup.mk' (H0.subgroupOf MF) h := by
  classical
  letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
    quotientMulDistribMulAction (A := U) (G := MF)
      (H0.subgroupOf MF) hH0invU
  let Fix : Subgroup (MF ⧸ H0.subgroupOf MF) :=
    { carrier := {y | x • y = y}
      one_mem' := by simp
      mul_mem' := by
        intro y z hy hz
        calc
          x • (y * z) = (x • y) * (x • z) := by simp
          _ = y * z := by rw [hy, hz]
      inv_mem' := by
        intro y hy
        calc
          x • y⁻¹ = (x • y)⁻¹ := by simp
          _ = y⁻¹ := by rw [hy] }
  have hHle : ∀ i, H i ≤ Fix := by
    intro i y hy
    change x • y = y
    exact hfactor i y hy
  have htop_le : (⊤ : Subgroup (MF ⧸ H0.subgroupOf MF)) ≤ Fix := by
    rw [← hSup]
    exact iSup_le hHle
  intro h
  exact htop_le (Subgroup.mem_top _)

private theorem theorem_9_7_conj_inv_mem_of_conj_mem_finite_sec9
    {G : Type u} [Group G] [Finite G]
    {MF : Subgroup G} {g : G}
    (hconjMF : ∀ h : MF, g⁻¹ * (h : G) * g ∈ MF) :
    ∀ h : MF, g * (h : G) * g⁻¹ ∈ MF := by
  classical
  letI : Fintype MF := Fintype.ofFinite MF
  let f : MF → MF := fun h => ⟨g⁻¹ * (h : G) * g, hconjMF h⟩
  have hf_inj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hval := congrArg Subtype.val hxy
    dsimp [f] at hval
    calc
      (x : G) = g * (g⁻¹ * (x : G) * g) * g⁻¹ := by group
      _ = g * (g⁻¹ * (y : G) * g) * g⁻¹ := by rw [hval]
      _ = (y : G) := by group
  have hf_surj : Function.Surjective f := by
    exact (Fintype.bijective_iff_injective_and_card f).2 ⟨hf_inj, rfl⟩ |>.2
  intro h
  rcases hf_surj h with ⟨k, hk⟩
  have hkval := congrArg Subtype.val hk
  dsimp [f] at hkval
  have hk_eq : (k : G) = g * (h : G) * g⁻¹ := by
    calc
      (k : G) = g * (g⁻¹ * (k : G) * g) * g⁻¹ := by group
      _ = g * (h : G) * g⁻¹ := by rw [hkval]
  simp [← hk_eq, k.property]


private theorem theorem_9_7_quotientSubgroupConjugateByElement_equiv_bi_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 : Subgroup G}
    [hnormal : (H0.subgroupOf MF).Normal]
    {Q R : Subgroup (MF ⧸ H0.subgroupOf MF)} {g : G}
    (hQR : quotientSubgroupConjugateByElement MF H0 Q R g) :
    ∃ e : Q ≃* R,
      ∃ hconjMF : ∀ h : MF, g⁻¹ * (h : G) * g ∈ MF,
        ∃ hconjInvMF : ∀ h : MF, g * (h : G) * g⁻¹ ∈ MF,
          (∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ Q,
            (e ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                MF ⧸ H0.subgroupOf MF) =
              QuotientGroup.mk' (H0.subgroupOf MF)
                ⟨g⁻¹ * (h : G) * g, hconjMF h⟩) ∧
          ∀ h : MF, ∀ hhR : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ R,
            (e.symm ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhR⟩ :
                MF ⧸ H0.subgroupOf MF) =
              QuotientGroup.mk' (H0.subgroupOf MF)
                ⟨g * (h : G) * g⁻¹, hconjInvMF h⟩ := by
  classical
  rcases hQR with ⟨hconjMF, action, haction, hR⟩
  let e0 : Q ≃* Q.map action.toMonoidHom := action.subgroupMap Q
  let e : Q ≃* R := e0.trans (MulEquiv.subgroupCongr hR.symm)
  have hconjInvMF : ∀ h : MF, g * (h : G) * g⁻¹ ∈ MF :=
    theorem_9_7_conj_inv_mem_of_conj_mem_finite_sec9 hconjMF
  refine ⟨e, hconjMF, hconjInvMF, ?_, ?_⟩
  · intro h hhQ
    change action (QuotientGroup.mk' (H0.subgroupOf MF) h) = _
    exact haction h
  · intro h hhR
    change action.symm (QuotientGroup.mk' (H0.subgroupOf MF) h) = _
    apply action.injective
    simp only [MulEquiv.apply_symm_apply]
    symm
    calc
      action (QuotientGroup.mk' (H0.subgroupOf MF)
          ⟨g * (h : G) * g⁻¹, hconjInvMF h⟩) =
          QuotientGroup.mk' (H0.subgroupOf MF)
            ⟨g⁻¹ * (g * (h : G) * g⁻¹) * g,
              hconjMF ⟨g * (h : G) * g⁻¹, hconjInvMF h⟩⟩ :=
        haction _
      _ = QuotientGroup.mk' (H0.subgroupOf MF) h := by
        apply congrArg (QuotientGroup.mk' (H0.subgroupOf MF))
        apply Subtype.ext
        group

private theorem theorem_9_7_successorTransportFactorAction_action_field_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 U W1 C : Subgroup G}
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hW1normU : Subgroup.Normalizes W1 U]
    (hnormalC : (C.subgroupOf U).Normal)
    (hCinv : IsInvariant W1 U (C.subgroupOf U))
    (w0 : W1)
    {Q R : Subgroup (MF ⧸ H0.subgroupOf MF)}
    (hQR : quotientSubgroupConjugateByElement MF H0 Q R (w0 : G))
    (ρ : (U ⧸ C.subgroupOf U) →* MulAut Q)
    (hactionρ :
      ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ Q,
              (ρ x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩) :
    ∃ e : Q ≃* R,
      (∃ hconjW : ∀ h : MF, (w0 : G)⁻¹ * (h : G) * (w0 : G) ∈ MF,
        (∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ Q,
          (e ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
              MF ⧸ H0.subgroupOf MF) =
            QuotientGroup.mk' (H0.subgroupOf MF)
              ⟨(w0 : G)⁻¹ * (h : G) * (w0 : G), hconjW h⟩) ∧
        ∃ hconjWinv : ∀ h : MF, (w0 : G) * (h : G) * (w0 : G)⁻¹ ∈ MF,
          ∀ h : MF, ∀ hhR : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ R,
            (e.symm ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhR⟩ :
                MF ⧸ H0.subgroupOf MF) =
              QuotientGroup.mk' (H0.subgroupOf MF)
                ⟨(w0 : G) * (h : G) * (w0 : G)⁻¹, hconjWinv h⟩) ∧
      ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF, ∀ hhR : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ R,
              (theorem_9_7_successorTransportFactorAction_sec9
                  hnormalC hCinv w0 e ρ x
                  ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhR⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩ := by
  classical
  letI : (C.subgroupOf U).Normal := hnormalC
  letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
    quotientMulDistribMulAction (A := W1) (G := U) (C.subgroupOf U) hCinv
  rcases theorem_9_7_quotientSubgroupConjugateByElement_equiv_bi_sec9 hQR with
    ⟨e, hconjW, hconjWinv, he, hesymm⟩
  refine ⟨e, ?_, ?_⟩
  · exact ⟨hconjW, he, hconjWinv, hesymm⟩
  intro x u hux
  rcases hactionρ (QuotientGroup.mk' (C.subgroupOf U) (w0 • u)) (w0 • u) rfl with
    ⟨hconjρ, hρ⟩
  let wConj (h : MF) : MF :=
    ⟨(w0 : G) * (h : G) * (w0 : G)⁻¹, hconjWinv h⟩
  have hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF := by
    intro h
    have hmem :=
      hconjW
        ⟨((w0 • u : U) : G)⁻¹ * (wConj h : G) * ((w0 • u : U) : G),
          hconjρ (wConj h)⟩
    convert hmem using 1
    dsimp [wConj]
    rw [show ((w0 • u : U) : G) = (w0 : G) * (u : G) * (w0 : G)⁻¹ by rfl]
    group
  refine ⟨hconjMF, ?_⟩
  intro h hhR
  let hW : MF := wConj h
  have hhWQ : QuotientGroup.mk' (H0.subgroupOf MF) hW ∈ Q := by
    have hmem :
        ((e.symm ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhR⟩ : Q) :
            MF ⧸ H0.subgroupOf MF) ∈ Q :=
      (e.symm ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhR⟩).property
    rwa [hesymm h hhR] at hmem
  let k : MF :=
    ⟨((w0 • u : U) : G)⁻¹ * (hW : G) * ((w0 • u : U) : G), hconjρ hW⟩
  have hkQ : QuotientGroup.mk' (H0.subgroupOf MF) k ∈ Q := by
    have hmem :
        ((ρ (QuotientGroup.mk' (C.subgroupOf U) (w0 • u))
            ⟨QuotientGroup.mk' (H0.subgroupOf MF) hW, hhWQ⟩ : Q) :
            MF ⧸ H0.subgroupOf MF) ∈ Q :=
      (ρ (QuotientGroup.mk' (C.subgroupOf U) (w0 • u))
        ⟨QuotientGroup.mk' (H0.subgroupOf MF) hW, hhWQ⟩).property
    rwa [hρ hW hhWQ] at hmem
  have hsymQ :
      e.symm ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhR⟩ =
        ⟨QuotientGroup.mk' (H0.subgroupOf MF) hW, hhWQ⟩ := by
    apply Subtype.ext
    exact hesymm h hhR
  have hρQ :
      ρ (QuotientGroup.mk' (C.subgroupOf U) (w0 • u))
          ⟨QuotientGroup.mk' (H0.subgroupOf MF) hW, hhWQ⟩ =
        ⟨QuotientGroup.mk' (H0.subgroupOf MF) k, hkQ⟩ := by
    apply Subtype.ext
    exact hρ hW hhWQ
  calc
    (theorem_9_7_successorTransportFactorAction_sec9
        hnormalC hCinv w0 e ρ x
        ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhR⟩ :
        MF ⧸ H0.subgroupOf MF) =
        (theorem_9_7_successorTransportFactorAction_sec9
          hnormalC hCinv w0 e ρ (QuotientGroup.mk' (C.subgroupOf U) u)
          ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhR⟩ :
          MF ⧸ H0.subgroupOf MF) := by
          rw [hux]
    _ = (e
          (ρ (QuotientGroup.mk' (C.subgroupOf U) (w0 • u))
            (e.symm ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhR⟩)) :
          MF ⧸ H0.subgroupOf MF) := by
          rw [theorem_9_7_successorTransportFactorAction_apply_mk_sec9]
    _ = (e
          (ρ (QuotientGroup.mk' (C.subgroupOf U) (w0 • u))
            ⟨QuotientGroup.mk' (H0.subgroupOf MF) hW, hhWQ⟩) :
          MF ⧸ H0.subgroupOf MF) := by
          rw [hsymQ]
    _ = (e ⟨QuotientGroup.mk' (H0.subgroupOf MF) k, hkQ⟩ :
          MF ⧸ H0.subgroupOf MF) := by
          rw [hρQ]
    _ = QuotientGroup.mk' (H0.subgroupOf MF)
          ⟨(w0 : G)⁻¹ * (k : G) * (w0 : G), hconjW k⟩ :=
          he k hkQ
    _ = QuotientGroup.mk' (H0.subgroupOf MF)
          ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩ := by
          apply congrArg (QuotientGroup.mk' (H0.subgroupOf MF))
          apply Subtype.ext
          dsimp [k, hW, wConj]
          rw [show ((w0 • u : U) : G) =
            (w0 : G) * (u : G) * (w0 : G)⁻¹ by rfl]
          group

public theorem theorem_9_7_successorTransportFactorAction_eq_of_action_field_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 U W1 C : Subgroup G}
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hW1normU : Subgroup.Normalizes W1 U]
    (hnormalC : (C.subgroupOf U).Normal)
    (hCinv : IsInvariant W1 U (C.subgroupOf U))
    (w0 : W1)
    {Q R : Subgroup (MF ⧸ H0.subgroupOf MF)}
    (hQR : quotientSubgroupConjugateByElement MF H0 Q R (w0 : G))
    {ρ : (U ⧸ C.subgroupOf U) →* MulAut Q}
    {σ : (U ⧸ C.subgroupOf U) →* MulAut R}
    (hactionρ :
      ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ Q,
              (ρ x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (hactionσ :
      ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF, ∀ hhR : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ R,
              (σ x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhR⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩) :
    ∃ e : Q ≃* R,
      (∃ hconjW : ∀ h : MF, (w0 : G)⁻¹ * (h : G) * (w0 : G) ∈ MF,
        (∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ Q,
          (e ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
              MF ⧸ H0.subgroupOf MF) =
            QuotientGroup.mk' (H0.subgroupOf MF)
              ⟨(w0 : G)⁻¹ * (h : G) * (w0 : G), hconjW h⟩) ∧
        ∃ hconjWinv : ∀ h : MF, (w0 : G) * (h : G) * (w0 : G)⁻¹ ∈ MF,
          ∀ h : MF, ∀ hhR : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ R,
            (e.symm ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhR⟩ :
                MF ⧸ H0.subgroupOf MF) =
              QuotientGroup.mk' (H0.subgroupOf MF)
                ⟨(w0 : G) * (h : G) * (w0 : G)⁻¹, hconjWinv h⟩) ∧
      theorem_9_7_successorTransportFactorAction_sec9 hnormalC hCinv w0 e ρ =
        σ := by
  classical
  rcases theorem_9_7_successorTransportFactorAction_action_field_sec9
      hnormalC hCinv w0 hQR ρ hactionρ with
    ⟨e, heData, hactionTransport⟩
  exact ⟨e, heData,
    theorem_9_7_factorAction_unique_of_action_field_sec9
      hactionTransport hactionσ⟩


private theorem theorem_9_7_quotientSubgroupConjugateByElement_symm_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 : Subgroup G}
    [hnormal : (H0.subgroupOf MF).Normal]
    {Q R : Subgroup (MF ⧸ H0.subgroupOf MF)} {g : G}
    (hQR : quotientSubgroupConjugateByElement MF H0 Q R g) :
    quotientSubgroupConjugateByElement MF H0 R Q g⁻¹ := by
  classical
  rcases hQR with ⟨hconjMF, action, haction, hR⟩
  have hconjInvMF : ∀ h : MF, g * (h : G) * g⁻¹ ∈ MF :=
    theorem_9_7_conj_inv_mem_of_conj_mem_finite_sec9 hconjMF
  refine ⟨?_, action.symm, ?_, ?_⟩
  · intro h
    simpa only [inv_inv] using hconjInvMF h
  · intro h
    apply action.injective
    simp only [MulEquiv.apply_symm_apply]
    symm
    calc
      action (QuotientGroup.mk' (H0.subgroupOf MF)
          ⟨(g⁻¹)⁻¹ * (h : G) * g⁻¹, by
            simpa only [inv_inv] using hconjInvMF h⟩) =
          QuotientGroup.mk' (H0.subgroupOf MF)
            ⟨g⁻¹ * ((g⁻¹)⁻¹ * (h : G) * g⁻¹) * g,
              hconjMF ⟨(g⁻¹)⁻¹ * (h : G) * g⁻¹, by
                simpa only [inv_inv] using hconjInvMF h⟩⟩ :=
        haction _
      _ = QuotientGroup.mk' (H0.subgroupOf MF) h := by
        apply congrArg (QuotientGroup.mk' (H0.subgroupOf MF))
        apply Subtype.ext
        group
  · ext x
    constructor
    · intro hxQ
      refine ⟨action x, ?_, by simp⟩
      rw [hR]
      exact ⟨x, hxQ, rfl⟩
    · rintro ⟨y, hyR, hyx⟩
      rw [hR] at hyR
      rcases hyR with ⟨z, hzQ, rfl⟩
      have hzx : z = x := by
        simpa using congrArg action hyx
      simpa [← hzx] using hzQ

private theorem theorem_9_7_quotientSubgroupConjugateByElement_one_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 : Subgroup G}
    [hnormal : (H0.subgroupOf MF).Normal]
    (Q : Subgroup (MF ⧸ H0.subgroupOf MF)) :
    quotientSubgroupConjugateByElement MF H0 Q Q (1 : G) := by
  refine ⟨?_, 1, ?_, ?_⟩
  · intro h
    simp
  · intro h
    simp
  · ext x
    simp [Subgroup.mem_map]

private theorem theorem_9_7_quotientSubgroupConjugateByElement_trans_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 : Subgroup G}
    [hnormal : (H0.subgroupOf MF).Normal]
    {Q R S : Subgroup (MF ⧸ H0.subgroupOf MF)} {g h : G}
    (hQR : quotientSubgroupConjugateByElement MF H0 Q R g)
    (hRS : quotientSubgroupConjugateByElement MF H0 R S h) :
    quotientSubgroupConjugateByElement MF H0 Q S (g * h) := by
  rcases hQR with ⟨hconjG, actionG, hactionG, hR⟩
  rcases hRS with ⟨hconjH, actionH, hactionH, hS⟩
  let hconjGH : ∀ k : MF, (g * h)⁻¹ * (k : G) * (g * h) ∈ MF := by
    intro k
    have hmem := hconjH ⟨g⁻¹ * (k : G) * g, hconjG k⟩
    simpa [mul_assoc] using hmem
  refine ⟨hconjGH, actionG.trans actionH, ?_, ?_⟩
  · intro k
    calc
      (actionG.trans actionH) (QuotientGroup.mk' (H0.subgroupOf MF) k) =
          actionH (actionG (QuotientGroup.mk' (H0.subgroupOf MF) k)) := rfl
      _ = actionH (QuotientGroup.mk' (H0.subgroupOf MF)
            ⟨g⁻¹ * (k : G) * g, hconjG k⟩) := by
          rw [hactionG k]
      _ = QuotientGroup.mk' (H0.subgroupOf MF)
            ⟨h⁻¹ * (g⁻¹ * (k : G) * g) * h,
              hconjH ⟨g⁻¹ * (k : G) * g, hconjG k⟩⟩ := by
          exact hactionH ⟨g⁻¹ * (k : G) * g, hconjG k⟩
      _ = QuotientGroup.mk' (H0.subgroupOf MF)
            ⟨(g * h)⁻¹ * (k : G) * (g * h), hconjGH k⟩ := by
          congr 1
          apply Subtype.ext
          group
  · calc
      S = R.map actionH.toMonoidHom := hS
      _ = (Q.map actionG.toMonoidHom).map actionH.toMonoidHom := by rw [hR]
      _ = Q.map (actionG.trans actionH).toMonoidHom := by
          rw [Subgroup.map_map]
          rfl

private theorem
    theorem_9_7_quotientSubgroupConjugateByElement_action_map_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 A : Subgroup G}
    [Subgroup.Normalizes A MF]
    [hnormal : (H0.subgroupOf MF).Normal]
    (hH0inv : IsInvariant A MF (H0.subgroupOf MF))
    (Q : Subgroup (MF ⧸ H0.subgroupOf MF))
    (a : A) :
    (letI : MulAction.QuotientAction A (H0.subgroupOf MF) :=
      quotientAction_of_isInvariant (A := A) (G := MF) (H0.subgroupOf MF) hH0inv
    letI : MulDistribMulAction A (MF ⧸ H0.subgroupOf MF) :=
      quotientMulDistribMulAction (A := A) (G := MF) (H0.subgroupOf MF) hH0inv
    quotientSubgroupConjugateByElement MF H0 Q
      (Q.map (MulDistribMulAction.toMulAut A
        (MF ⧸ H0.subgroupOf MF) (a⁻¹ : A)).toMonoidHom) (a : G)) := by
  classical
  let H0MF : Subgroup MF := H0.subgroupOf MF
  haveI : H0MF.Normal := hnormal
  letI : MulAction.QuotientAction A H0MF :=
    quotientAction_of_isInvariant (A := A) (G := MF) H0MF hH0inv
  letI : MulDistribMulAction A (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := A) (G := MF) H0MF hH0inv
  let hconjMF : ∀ h : MF, (a : G)⁻¹ * (h : G) * (a : G) ∈ MF := by
    intro h
    have hsmulG :
        (((a⁻¹ : A) • h : MF) : G) = (a : G)⁻¹ * (h : G) * (a : G) := by
      simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
    exact hsmulG ▸ (((a⁻¹ : A) • h : MF).property)
  refine ⟨hconjMF, ?_⟩
  let action : MulAut (MF ⧸ H0MF) :=
    MulDistribMulAction.toMulAut A (MF ⧸ H0MF) (a⁻¹ : A)
  refine ⟨action, ?_, rfl⟩
  intro h
  have hsmul_eq :
      ((a⁻¹ : A) • h : MF) =
        ⟨(a : G)⁻¹ * (h : G) * (a : G), hconjMF h⟩ := by
    apply Subtype.ext
    simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
  change action (QuotientGroup.mk' H0MF h) =
    QuotientGroup.mk' H0MF
      ⟨(a : G)⁻¹ * (h : G) * (a : G), hconjMF h⟩
  change (a⁻¹ : A) • QuotientGroup.mk' H0MF h =
    QuotientGroup.mk' H0MF
      ⟨(a : G)⁻¹ * (h : G) * (a : G), hconjMF h⟩
  have hsmul_mk :
      (a⁻¹ : A) • QuotientGroup.mk' H0MF h =
        QuotientGroup.mk' H0MF ((a⁻¹ : A) • h) := by
    simpa only [QuotientGroup.mk'_apply] using
      (MulAction.Quotient.smul_mk (H := H0MF) (a⁻¹ : A) h)
  rw [hsmul_mk, hsmul_eq]

public theorem theorem_9_7_weak_orbit_of_successor_conjugates_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 W1 : Subgroup G}
    [hnormal : (H0.subgroupOf MF).Normal]
    {q : ℕ} (hqpos : 0 < q)
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (w0 : W1)
    (hsucc :
      ∀ i : Fin q,
        quotientSubgroupConjugateByElement MF H0 (H i)
          (H (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)) (w0 : G)) :
    ∀ i : Fin q,
      ∃ w : W1,
        quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i) (w : G) := by
  have hstep : ∀ n : ℕ, ∀ hn : n < q,
      ∃ w : W1,
        quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H ⟨n, hn⟩)
          (w : G) := by
    intro n
    induction n with
    | zero =>
        intro hn
        exact ⟨1, by
          simpa using
            (theorem_9_7_quotientSubgroupConjugateByElement_one_sec9
              (MF := MF) (H0 := H0) (Q := H ⟨0, hqpos⟩))⟩
    | succ n ih =>
        intro hn
        have hnq : n < q := Nat.lt_trans (Nat.lt_succ_self n) hn
        rcases ih hnq with ⟨w, hw⟩
        have hidx :
            theorem_9_7_fin_cyclic_succ_sec9 hqpos ⟨n, hnq⟩ = ⟨n + 1, hn⟩ := by
          apply Fin.ext
          simp [theorem_9_7_fin_cyclic_succ_sec9, hn]
        have hsucc_target :
            quotientSubgroupConjugateByElement MF H0 (H ⟨n, hnq⟩) (H ⟨n + 1, hn⟩)
              (w0 : G) := by
          simpa [hidx] using hsucc ⟨n, hnq⟩
        exact ⟨w * w0, by
          simpa using
            (theorem_9_7_quotientSubgroupConjugateByElement_trans_sec9
              hw hsucc_target)⟩
  intro i
  exact hstep i.1 i.2

public theorem theorem_9_7_successor_conjugates_pow_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 W1 : Subgroup G}
    [hnormal : (H0.subgroupOf MF).Normal]
    {q : ℕ} (hqpos : 0 < q)
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (w0 : W1)
    (hsucc :
      ∀ i : Fin q,
        quotientSubgroupConjugateByElement MF H0 (H i)
          (H (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)) (w0 : G)) :
    ∀ n : ℕ, ∀ hn : n < q,
      quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H ⟨n, hn⟩)
        ((w0 ^ n : W1) : G) := by
  intro n
  induction n with
  | zero =>
      intro _hn
      simpa using
        (theorem_9_7_quotientSubgroupConjugateByElement_one_sec9
          (MF := MF) (H0 := H0) (Q := H ⟨0, hqpos⟩))
  | succ n ih =>
      intro hn
      have hnq : n < q := Nat.lt_trans (Nat.lt_succ_self n) hn
      have hprev := ih hnq
      have hidx :
          theorem_9_7_fin_cyclic_succ_sec9 hqpos ⟨n, hnq⟩ = ⟨n + 1, hn⟩ := by
        apply Fin.ext
        simp [theorem_9_7_fin_cyclic_succ_sec9, hn]
      have hsucc_target :
          quotientSubgroupConjugateByElement MF H0 (H ⟨n, hnq⟩) (H ⟨n + 1, hn⟩)
            (w0 : G) := by
        simpa [hidx] using hsucc ⟨n, hnq⟩
      have htrans :=
        theorem_9_7_quotientSubgroupConjugateByElement_trans_sec9
          hprev hsucc_target
      simpa [pow_succ] using htrans

private theorem
    theorem_9_7_quotientSubgroupNormalizedBy_of_generator_conjugates_self_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 W1 : Subgroup G}
    [hnormal : (H0.subgroupOf MF).Normal]
    {Q : Subgroup (MF ⧸ H0.subgroupOf MF)}
    (w0 : W1)
    (hw0gen : Subgroup.zpowers w0 = ⊤)
    (hw0Q : quotientSubgroupConjugateByElement MF H0 Q Q (w0 : G)) :
    quotientSubgroupNormalizedBy MF H0 W1 Q := by
  let N : Subgroup W1 :=
    { carrier := {w | quotientSubgroupConjugateByElement MF H0 Q Q (w : G)}
      one_mem' := by
        simpa using
          theorem_9_7_quotientSubgroupConjugateByElement_one_sec9
            (MF := MF) (H0 := H0) (Q := Q)
      mul_mem' := by
        intro a b ha hb
        simpa using
          theorem_9_7_quotientSubgroupConjugateByElement_trans_sec9
            ha hb
      inv_mem' := by
        intro a ha
        simpa using
          theorem_9_7_quotientSubgroupConjugateByElement_symm_sec9
            ha }
  intro w
  have hw0N : w0 ∈ N := by
    simpa [N] using hw0Q
  have hwmem : w ∈ Subgroup.zpowers w0 := by
    rw [hw0gen]
    exact Subgroup.mem_top w
  have hwN : w ∈ N :=
    (Subgroup.zpowers_le_of_mem hw0N) hwmem
  simpa [N] using hwN

private theorem
    theorem_9_7_generator_not_conjugates_quotientSubgroup_self_of_not_normalized_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 W1 : Subgroup G}
    [hnormal : (H0.subgroupOf MF).Normal]
    {Q : Subgroup (MF ⧸ H0.subgroupOf MF)}
    (w0 : W1)
    (hw0gen : Subgroup.zpowers w0 = ⊤)
    (hQnotW1 : ¬ quotientSubgroupNormalizedBy MF H0 W1 Q) :
    ¬ quotientSubgroupConjugateByElement MF H0 Q Q (w0 : G) := by
  intro hw0Q
  exact hQnotW1
    (theorem_9_7_quotientSubgroupNormalizedBy_of_generator_conjugates_self_sec9
      w0 hw0gen hw0Q)


private theorem theorem_9_7_base_normalizedBy_of_equal_conjugates_distinct_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 W1 : Subgroup G}
    [hnormal : (H0.subgroupOf MF).Normal]
    {Q R S : Subgroup (MF ⧸ H0.subgroupOf MF)}
    (hW1prime : Nat.Prime (Nat.card W1))
    (wi wj : W1)
    (hi : quotientSubgroupConjugateByElement MF H0 Q R (wi : G))
    (hj : quotientSubgroupConjugateByElement MF H0 Q S (wj : G))
    (hRS : R = S)
    (hij : wi ≠ wj) :
    quotientSubgroupNormalizedBy MF H0 W1 Q := by
  let g : W1 := wi * wj⁻¹
  have hg_ne_one : g ≠ 1 := by
    intro hg
    have hgval : (wi : G) * (wj : G)⁻¹ = 1 := by
      simpa [g] using congrArg Subtype.val hg
    exact hij (Subtype.ext (by
      calc
        (wi : G) = (wi : G) * (wj : G)⁻¹ * (wj : G) := by group
        _ = (1 : G) * (wj : G) := by rw [hgval]
        _ = (wj : G) := by group))
  have hggen : Subgroup.zpowers g = ⊤ :=
    zpowers_eq_top_of_prime_card_of_ne_one hW1prime hg_ne_one
  have hself : quotientSubgroupConjugateByElement MF H0 Q Q (g : G) := by
    have hiS : quotientSubgroupConjugateByElement MF H0 Q S (wi : G) := by
      simpa [hRS] using hi
    have hS0 : quotientSubgroupConjugateByElement MF H0 S Q ((wj : G)⁻¹) :=
      theorem_9_7_quotientSubgroupConjugateByElement_symm_sec9 hj
    have htrans :=
      theorem_9_7_quotientSubgroupConjugateByElement_trans_sec9 hiS hS0
    simpa [g] using htrans
  exact
    theorem_9_7_quotientSubgroupNormalizedBy_of_generator_conjugates_self_sec9
      g hggen hself

private theorem theorem_9_7_generator_powers_ne_of_lt_card_sec9
    {G : Type u} [Group G] [Finite G]
    {W1 : Subgroup G} {q i j : ℕ}
    (hW1card : Nat.card W1 = q)
    (w0 : W1)
    (hw0gen : Subgroup.zpowers w0 = ⊤)
    (hi : i < q) (hj : j < q)
    (hij : i ≠ j) :
    (w0 ^ i : W1) ≠ w0 ^ j := by
  intro hpow
  have horder : orderOf w0 = q := by
    rw [orderOf_eq_card_of_zpowers_eq_top hw0gen, hW1card]
  have hmodeq : i ≡ j [MOD orderOf w0] :=
    pow_eq_pow_iff_modEq.mp hpow
  have hi' : i < orderOf w0 := by
    simpa [horder] using hi
  have hj' : j < orderOf w0 := by
    simpa [horder] using hj
  exact hij (hmodeq.eq_of_lt_of_lt hi' hj')

private theorem
    theorem_9_7_base_normalizedBy_of_equal_generator_orbit_indices_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 W1 : Subgroup G}
    [hnormal : (H0.subgroupOf MF).Normal]
    {q : ℕ}
    (hqprime : Nat.Prime q)
    (hW1card : Nat.card W1 = q)
    (w0 : W1)
    (hw0gen : Subgroup.zpowers w0 = ⊤)
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hsucc :
      ∀ i : Fin q,
        quotientSubgroupConjugateByElement MF H0 (H i)
          (H (theorem_9_7_fin_cyclic_succ_sec9 hqprime.pos i)) (w0 : G))
    {i j : Fin q}
    (hij : i ≠ j)
    (hHij : H i = H j) :
    quotientSubgroupNormalizedBy MF H0 W1 (H ⟨0, hqprime.pos⟩) := by
  have hW1prime : Nat.Prime (Nat.card W1) := by
    simpa [hW1card] using hqprime
  have hi_conj :
      quotientSubgroupConjugateByElement MF H0
        (H ⟨0, hqprime.pos⟩) (H i) ((w0 ^ i.1 : W1) : G) :=
    theorem_9_7_successor_conjugates_pow_sec9 hqprime.pos H w0 hsucc i.1 i.2
  have hj_conj :
      quotientSubgroupConjugateByElement MF H0
        (H ⟨0, hqprime.pos⟩) (H j) ((w0 ^ j.1 : W1) : G) :=
    theorem_9_7_successor_conjugates_pow_sec9 hqprime.pos H w0 hsucc j.1 j.2
  have hpows_ne : (w0 ^ i.1 : W1) ≠ w0 ^ j.1 :=
    theorem_9_7_generator_powers_ne_of_lt_card_sec9 hW1card w0 hw0gen
      i.2 j.2 (by
        intro hval
        exact hij (Fin.ext hval))
  exact
    theorem_9_7_base_normalizedBy_of_equal_conjugates_distinct_sec9
      hW1prime (w0 ^ i.1 : W1) (w0 ^ j.1 : W1) hi_conj hj_conj hHij hpows_ne

private theorem theorem_9_7_generator_orbit_injective_of_base_not_normalized_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 W1 : Subgroup G}
    [hnormal : (H0.subgroupOf MF).Normal]
    {q : ℕ}
    (hqprime : Nat.Prime q)
    (hW1card : Nat.card W1 = q)
    (w0 : W1)
    (hw0gen : Subgroup.zpowers w0 = ⊤)
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hsucc :
      ∀ i : Fin q,
        quotientSubgroupConjugateByElement MF H0 (H i)
          (H (theorem_9_7_fin_cyclic_succ_sec9 hqprime.pos i)) (w0 : G))
    (hH0notW1 :
      ¬ quotientSubgroupNormalizedBy MF H0 W1 (H ⟨0, hqprime.pos⟩)) :
    Function.Injective H := by
  intro i j hHij
  by_cases hidx : i = j
  · exact hidx
  · exact False.elim
      (hH0notW1
        (theorem_9_7_base_normalizedBy_of_equal_generator_orbit_indices_sec9
          hqprime hW1card w0 hw0gen H hsucc hidx hHij))

private theorem theorem_9_7_not_W1_normalized_of_UW1_minimal_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 U W1 : Subgroup G}
    [hnormal : (H0.subgroupOf MF).Normal]
    {Q : Subgroup (MF ⧸ H0.subgroupOf MF)}
    (hUW1minimal :
      ∀ R : Subgroup (MF ⧸ H0.subgroupOf MF),
        quotientSubgroupNormalizedBy MF H0 U R →
          quotientSubgroupNormalizedBy MF H0 W1 R →
            R = ⊥ ∨ R = ⊤)
    (hQnorm : quotientSubgroupNormalizedBy MF H0 U Q)
    (hQneBot : Q ≠ ⊥)
    (hQneTop : Q ≠ ⊤) :
    ¬ quotientSubgroupNormalizedBy MF H0 W1 Q := by
  intro hQnormW1
  rcases hUW1minimal Q hQnorm hQnormW1 with hQbot | hQtop
  · exact hQneBot hQbot
  · exact hQneTop hQtop


private theorem
    theorem_9_7_exists_minimal_U_normalized_not_W1_of_reducible_minimal_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 U W1 : Subgroup G}
    (hnormal : (H0.subgroupOf MF).Normal)
    (hUW1minimal :
      letI : (H0.subgroupOf MF).Normal := hnormal
      ∀ R : Subgroup (MF ⧸ H0.subgroupOf MF),
        quotientSubgroupNormalizedBy MF H0 U R →
          quotientSubgroupNormalizedBy MF H0 W1 R →
            R = ⊥ ∨ R = ⊤)
    (hnonUirred : ¬ quotientIrreducibleActionData MF H0 U) :
    letI : (H0.subgroupOf MF).Normal := hnormal
    ∃ Q : Subgroup (MF ⧸ H0.subgroupOf MF),
      quotientSubgroupNormalizedBy MF H0 U Q ∧
        Q ≠ ⊥ ∧
        Q ≠ ⊤ ∧
        (∀ R : Subgroup (MF ⧸ H0.subgroupOf MF),
          quotientSubgroupNormalizedBy MF H0 U R →
            R ≠ ⊥ → R ≤ Q → Q ≤ R) ∧
        ¬ quotientSubgroupNormalizedBy MF H0 W1 Q := by
  classical
  letI : (H0.subgroupOf MF).Normal := hnormal
  let K := MF ⧸ H0.subgroupOf MF
  have hproper :
      ∃ Q : Subgroup K,
        quotientSubgroupNormalizedBy MF H0 U Q ∧ Q ≠ ⊥ ∧ Q ≠ ⊤ := by
    simpa [K] using
      theorem_9_7_exists_proper_U_normalized_quotient_subgroup_of_not_irreducible_sec9
        (MF := MF) (H0 := H0) (U := U) hnormal hnonUirred
  have hnonzero :
      ∃ Q : Subgroup K, quotientSubgroupNormalizedBy MF H0 U Q ∧ Q ≠ ⊥ := by
    rcases hproper with ⟨Q, hQnorm, hQneBot, _hQneTop⟩
    exact ⟨Q, hQnorm, hQneBot⟩
  rcases exists_minimal_of_wellFoundedLT
      (P := fun Q : Subgroup K => quotientSubgroupNormalizedBy MF H0 U Q ∧ Q ≠ ⊥)
      hnonzero with
    ⟨Q, hQmin⟩
  have hQnorm : quotientSubgroupNormalizedBy MF H0 U Q := hQmin.1.1
  have hQneBot : Q ≠ ⊥ := hQmin.1.2
  have hQminimal :
      ∀ R : Subgroup K,
        quotientSubgroupNormalizedBy MF H0 U R →
          R ≠ ⊥ → R ≤ Q → Q ≤ R := by
    intro R hRnorm hRneBot hRQ
    exact (Minimal.eq_of_le hQmin ⟨hRnorm, hRneBot⟩ hRQ).symm.le
  have hQneTop : Q ≠ ⊤ := by
    intro hQtop
    rcases hproper with ⟨R, hRnorm, hRneBot, hRneTop⟩
    have hQR : Q ≤ R := hQminimal R hRnorm hRneBot (hQtop ▸ le_top)
    rw [hQtop] at hQR
    exact hRneTop (top_le_iff.mp hQR)
  exact
    ⟨Q, hQnorm, hQneBot, hQneTop, hQminimal,
      theorem_9_7_not_W1_normalized_of_UW1_minimal_sec9
        (MF := MF) (H0 := H0) (U := U) (W1 := W1)
        hUW1minimal hQnorm hQneBot hQneTop⟩

private theorem theorem_9_7_subgroup_map_mulAut_ne_bot_sec9
    {K : Type u} [Group K] (φ : MulAut K) (Q : Subgroup K) :
    Q ≠ ⊥ → Q.map φ.toMonoidHom ≠ ⊥ := by
  intro hQ hmap
  exact hQ
    ((Subgroup.map_eq_bot_iff_of_injective
      (H := Q) (f := φ.toMonoidHom) φ.injective).mp hmap)

private theorem theorem_9_7_subgroup_map_mulAut_ne_top_sec9
    {K : Type u} [Group K] (φ : MulAut K) (Q : Subgroup K) :
    Q ≠ ⊤ → Q.map φ.toMonoidHom ≠ ⊤ := by
  intro hQ hmap
  have hmapTop : (⊤ : Subgroup K).map φ.toMonoidHom = ⊤ :=
    Subgroup.map_top_of_surjective φ.toMonoidHom φ.surjective
  have hmap_eq_top_map :
      Q.map φ.toMonoidHom = (⊤ : Subgroup K).map φ.toMonoidHom := by
    rw [hmap, hmapTop]
  exact hQ
    ((Subgroup.map_injective (f := φ.toMonoidHom) φ.injective)
      hmap_eq_top_map)

private theorem theorem_9_7_subgroup_map_mulAut_card_sec9
    {K : Type u} [Group K] (φ : MulAut K) (Q : Subgroup K) :
    Nat.card (Q.map φ.toMonoidHom) = Nat.card Q := by
  exact Subgroup.card_map_of_injective (K := Q) (f := φ.toMonoidHom) φ.injective

private theorem theorem_9_7_subgroup_map_mulAut_le_iff_sec9
    {K : Type u} [Group K] (φ : MulAut K) (Q R : Subgroup K) :
    Q.map φ.toMonoidHom ≤ R ↔ Q ≤ R.map φ.symm.toMonoidHom := by
  constructor
  · intro h x hx
    refine ⟨φ x, h ?_, ?_⟩
    · exact Subgroup.mem_map_of_mem φ.toMonoidHom hx
    · simp
  · intro h x hx
    rcases hx with ⟨y, hy, rfl⟩
    have hy' : y ∈ R.map φ.symm.toMonoidHom := h hy
    rcases hy' with ⟨z, hz, hzy⟩
    have hz_eq : z = φ y := by
      simpa using congrArg φ hzy
    simpa [hz_eq] using hz

private theorem theorem_9_7_subgroup_le_map_mulAut_iff_sec9
    {K : Type u} [Group K] (φ : MulAut K) (R Q : Subgroup K) :
    R ≤ Q.map φ.toMonoidHom ↔ R.map φ.symm.toMonoidHom ≤ Q := by
  constructor
  · intro h x hx
    rcases hx with ⟨y, hy, rfl⟩
    have hy' : y ∈ Q.map φ.toMonoidHom := h hy
    rcases hy' with ⟨z, hz, hzy⟩
    have hz_eq : z = φ.symm y := by
      simpa using congrArg φ.symm hzy
    simpa [hz_eq] using hz
  · intro h x hx
    have hx' : φ.symm x ∈ Q :=
      h (Subgroup.mem_map_of_mem φ.symm.toMonoidHom hx)
    refine ⟨φ.symm x, hx', ?_⟩
    simp

private theorem theorem_9_7_subgroup_map_mulAut_pow_succ_sec9
    {K : Type u} [Group K] (φ : MulAut K) (Q : Subgroup K) (n : ℕ) :
    (Q.map ((φ ^ n).toMonoidHom)).map φ.toMonoidHom =
      Q.map ((φ ^ (n + 1)).toMonoidHom) := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  rw [pow_succ]
  change (φ * φ ^ n) x = (φ ^ n * φ) x
  rw [← pow_succ', ← pow_succ]

private theorem theorem_9_7_subgroup_map_mulAut_pow_eq_self_sec9
    {K : Type u} [Group K] (φ : MulAut K) (Q : Subgroup K) {q : ℕ}
    (hφpow : φ ^ q = 1) :
    Q.map ((φ ^ q).toMonoidHom) = Q := by
  rw [hφpow]
  ext x
  simp

private theorem
    theorem_9_7_quotientSubgroupNormalizedBy_w1_conjugate_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 U W1 : Subgroup G}
    [Subgroup.Normalizes U MF] [Subgroup.Normalizes W1 MF]
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [Subgroup.Normalizes W1 U]
    (hH0invU : IsInvariant U MF (H0.subgroupOf MF))
    (hH0invW1 : IsInvariant W1 MF (H0.subgroupOf MF))
    (Q : Subgroup (MF ⧸ H0.subgroupOf MF))
    (hQnorm : quotientSubgroupNormalizedBy MF H0 U Q)
    (w : W1) :
    (letI : MulAction.QuotientAction W1 (H0.subgroupOf MF) :=
      quotientAction_of_isInvariant (A := W1) (G := MF)
        (H0.subgroupOf MF) hH0invW1
    letI : MulDistribMulAction W1 (MF ⧸ H0.subgroupOf MF) :=
      quotientMulDistribMulAction (A := W1) (G := MF)
        (H0.subgroupOf MF) hH0invW1
    quotientSubgroupNormalizedBy MF H0 U
      (Q.map (MulDistribMulAction.toMulAut W1
        (MF ⧸ H0.subgroupOf MF) (w⁻¹ : W1)).toMonoidHom)) := by
  classical
  let H0MF : Subgroup MF := H0.subgroupOf MF
  haveI : H0MF.Normal := hnormalH0
  letI : MulAction.QuotientAction U H0MF :=
    quotientAction_of_isInvariant (A := U) (G := MF) H0MF hH0invU
  letI : MulDistribMulAction U (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := U) (G := MF) H0MF hH0invU
  letI : MulAction.QuotientAction W1 H0MF :=
    quotientAction_of_isInvariant (A := W1) (G := MF) H0MF hH0invW1
  letI : MulDistribMulAction W1 (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := W1) (G := MF) H0MF hH0invW1
  let φ : MulAut (MF ⧸ H0MF) :=
    MulDistribMulAction.toMulAut W1 (MF ⧸ H0MF) (w⁻¹ : W1)
  let Qw : Subgroup (MF ⧸ H0MF) := Q.map φ.toMonoidHom
  have hQ_forward :
      ∀ u : U, ∀ {x : MF ⧸ H0MF}, x ∈ Q → u • x ∈ Q := by
    intro u x hx
    rcases QuotientGroup.mk'_surjective H0MF x with ⟨h, rfl⟩
    rcases hQnorm (u⁻¹) with ⟨hconjMF, action, haction, hmap⟩
    have hx_action :
        action (QuotientGroup.mk' H0MF h) ∈ Q := by
      have hx_map :
          action.toMonoidHom (QuotientGroup.mk' H0MF h) ∈
            Q.map action.toMonoidHom :=
        Subgroup.mem_map_of_mem action.toMonoidHom hx
      rw [hmap]
      exact hx_map
    have haction_eq :
        action (QuotientGroup.mk' H0MF h) =
          u • QuotientGroup.mk' H0MF h := by
      rw [haction h]
      have hsmul_mk :
          u • QuotientGroup.mk' H0MF h =
            QuotientGroup.mk' H0MF (u • h) := by
        simpa only [QuotientGroup.mk'_apply] using
          (MulAction.Quotient.smul_mk (H := H0MF) u h)
      rw [hsmul_mk]
      apply congrArg (QuotientGroup.mk' H0MF)
      apply Subtype.ext
      simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
    exact haction_eq ▸ hx_action
  have hQw_forward :
      ∀ u : U, ∀ {x : MF ⧸ H0MF}, x ∈ Qw → u • x ∈ Qw := by
    intro u x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hyQ, rfl⟩
    let u' : U := w • u
    refine Subgroup.mem_map.mpr ⟨u' • y, hQ_forward u' hyQ, ?_⟩
    rcases QuotientGroup.mk'_surjective H0MF y with ⟨h, rfl⟩
    change φ (u' • QuotientGroup.mk' H0MF h) =
      u • φ (QuotientGroup.mk' H0MF h)
    change (w⁻¹ : W1) • (u' • QuotientGroup.mk' H0MF h) =
      u • ((w⁻¹ : W1) • QuotientGroup.mk' H0MF h)
    have hu'_mk :
        u' • QuotientGroup.mk' H0MF h =
          QuotientGroup.mk' H0MF (u' • h) := by
      simpa only [QuotientGroup.mk'_apply] using
        (MulAction.Quotient.smul_mk (H := H0MF) u' h)
    have hw_mk :
        (w⁻¹ : W1) • QuotientGroup.mk' H0MF (u' • h) =
          QuotientGroup.mk' H0MF ((w⁻¹ : W1) • (u' • h)) := by
      simpa only [QuotientGroup.mk'_apply] using
        (MulAction.Quotient.smul_mk (H := H0MF) (w⁻¹ : W1) (u' • h))
    have hw_h_mk :
        (w⁻¹ : W1) • QuotientGroup.mk' H0MF h =
          QuotientGroup.mk' H0MF ((w⁻¹ : W1) • h) := by
      simpa only [QuotientGroup.mk'_apply] using
        (MulAction.Quotient.smul_mk (H := H0MF) (w⁻¹ : W1) h)
    have hu_w_mk :
        u • QuotientGroup.mk' H0MF ((w⁻¹ : W1) • h) =
          QuotientGroup.mk' H0MF (u • ((w⁻¹ : W1) • h)) := by
      simpa only [QuotientGroup.mk'_apply] using
        (MulAction.Quotient.smul_mk (H := H0MF) u ((w⁻¹ : W1) • h))
    rw [hu'_mk, hw_mk, hw_h_mk, hu_w_mk]
    apply congrArg (QuotientGroup.mk' H0MF)
    apply Subtype.ext
    simp [u', Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
    group
  have hQw_inv : IsInvariant U (MF ⧸ H0MF) Qw := by
    constructor
    intro u x
    constructor
    · exact hQw_forward u
    · intro hx
      have hx' : (u⁻¹ : U) • (u • x) ∈ Qw := hQw_forward u⁻¹ hx
      simpa using hx'
  simpa [Qw, φ, H0MF] using
    (quotientSubgroupNormalizedBy_of_isInvariant_sec9
      (MF := MF) (H0 := H0) (A := U) hH0invU Qw hQw_inv)

private theorem
    theorem_9_7_quotientSubgroupNormalizedBy_w1_conjugate_symm_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 U W1 : Subgroup G}
    [Subgroup.Normalizes U MF] [Subgroup.Normalizes W1 MF]
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [Subgroup.Normalizes W1 U]
    (hH0invU : IsInvariant U MF (H0.subgroupOf MF))
    (hH0invW1 : IsInvariant W1 MF (H0.subgroupOf MF))
    (Q : Subgroup (MF ⧸ H0.subgroupOf MF))
    (hQnorm : quotientSubgroupNormalizedBy MF H0 U Q)
    (w : W1) :
    (letI : MulAction.QuotientAction W1 (H0.subgroupOf MF) :=
      quotientAction_of_isInvariant (A := W1) (G := MF)
        (H0.subgroupOf MF) hH0invW1
    letI : MulDistribMulAction W1 (MF ⧸ H0.subgroupOf MF) :=
      quotientMulDistribMulAction (A := W1) (G := MF)
        (H0.subgroupOf MF) hH0invW1
    quotientSubgroupNormalizedBy MF H0 U
      (Q.map (MulDistribMulAction.toMulAut W1
        (MF ⧸ H0.subgroupOf MF) w).toMonoidHom)) := by
  simpa using
    theorem_9_7_quotientSubgroupNormalizedBy_w1_conjugate_sec9
      (MF := MF) (H0 := H0) (U := U) (W1 := W1)
      hH0invU hH0invW1 Q hQnorm (w⁻¹)

private theorem theorem_9_7_minimal_of_W1_conjugate_minimal_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 U W1 : Subgroup G}
    [Subgroup.Normalizes U MF] [Subgroup.Normalizes W1 MF]
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [Subgroup.Normalizes W1 U]
    (hH0invU : IsInvariant U MF (H0.subgroupOf MF))
    (hH0invW1 : IsInvariant W1 MF (H0.subgroupOf MF))
    {Q R : Subgroup (MF ⧸ H0.subgroupOf MF)}
    (hQminimal :
      ∀ T : Subgroup (MF ⧸ H0.subgroupOf MF),
        quotientSubgroupNormalizedBy MF H0 U T →
          T ≠ ⊥ → T ≤ Q → Q ≤ T)
    (w : W1)
    (hQR : quotientSubgroupConjugateByElement MF H0 Q R (w : G)) :
    ∀ T : Subgroup (MF ⧸ H0.subgroupOf MF),
      quotientSubgroupNormalizedBy MF H0 U T →
        T ≠ ⊥ → T ≤ R → R ≤ T := by
  classical
  let K : Type u := MF ⧸ H0.subgroupOf MF
  let ψ : MulAut K :=
    MulDistribMulAction.toMulAut W1 K (w⁻¹ : W1)
  have hQR_step :
      quotientSubgroupConjugateByElement MF H0 Q
        (Q.map ψ.toMonoidHom) (w : G) := by
    simpa [K, ψ] using
      theorem_9_7_quotientSubgroupConjugateByElement_action_map_sec9
        (MF := MF) (H0 := H0) (A := W1) hH0invW1 Q w
  have hR_eq : R = Q.map ψ.toMonoidHom := by
    rcases hQR with ⟨hconjMF, action, haction, hR⟩
    rcases hQR_step with ⟨hconjMF', action', haction', hR'⟩
    have haction_eq : action = action' := by
      ext x
      rcases QuotientGroup.mk'_surjective (H0.subgroupOf MF) x with ⟨h, rfl⟩
      calc
        action (QuotientGroup.mk' (H0.subgroupOf MF) h) =
            QuotientGroup.mk' (H0.subgroupOf MF)
              ⟨(w : G)⁻¹ * (h : G) * (w : G), hconjMF h⟩ := haction h
        _ = QuotientGroup.mk' (H0.subgroupOf MF)
              ⟨(w : G)⁻¹ * (h : G) * (w : G), hconjMF' h⟩ := by
              congr 1
        _ = action' (QuotientGroup.mk' (H0.subgroupOf MF) h) := (haction' h).symm
    rw [hR, haction_eq, ← hR']
  intro T hTnorm hTneBot hTleR
  have hTpre_norm :
      quotientSubgroupNormalizedBy MF H0 U
        (T.map ψ.symm.toMonoidHom) := by
    have hnorm :=
      theorem_9_7_quotientSubgroupNormalizedBy_w1_conjugate_symm_sec9
        (MF := MF) (H0 := H0) (U := U) (W1 := W1)
        hH0invU hH0invW1 T hTnorm w
    change
      quotientSubgroupNormalizedBy MF H0 U
        (T.map (MulDistribMulAction.toMulAut W1 K w).toMonoidHom) at hnorm
    have hψ_symm :
        (MulDistribMulAction.toMulAut W1 K w) = ψ.symm := by
      ext x
      dsimp [ψ]
      simp
    simpa [hψ_symm]
      using hnorm
  have hTpre_neBot : T.map ψ.symm.toMonoidHom ≠ ⊥ := by
    intro hmap
    exact hTneBot
      ((Subgroup.map_eq_bot_iff_of_injective
        (H := T) (f := ψ.symm.toMonoidHom) ψ.symm.injective).mp hmap)
  have hTpre_le_Q : T.map ψ.symm.toMonoidHom ≤ Q := by
    rw [hR_eq] at hTleR
    exact (theorem_9_7_subgroup_le_map_mulAut_iff_sec9 ψ T Q).1 hTleR
  have hQ_le_Tpre : Q ≤ T.map ψ.symm.toMonoidHom :=
    hQminimal (T.map ψ.symm.toMonoidHom)
      hTpre_norm hTpre_neBot hTpre_le_Q
  rw [hR_eq]
  exact (theorem_9_7_subgroup_map_mulAut_le_iff_sec9 ψ Q T).2 hQ_le_Tpre

private theorem theorem_9_7_fin_cyclic_succ_surjective_sec9
    {q : ℕ} (hqpos : 0 < q) :
    Function.Surjective (theorem_9_7_fin_cyclic_succ_sec9 hqpos) := by
  intro j
  by_cases hj0 : j.1 = 0
  · refine ⟨⟨q - 1, by omega⟩, ?_⟩
    apply Fin.ext
    have hwrap : ¬ q - 1 + 1 < q := by omega
    simp [theorem_9_7_fin_cyclic_succ_sec9, hwrap, hj0]
  · refine ⟨⟨j.1 - 1, by omega⟩, ?_⟩
    apply Fin.ext
    have hnext : j.1 - 1 + 1 < q := by omega
    simp [theorem_9_7_fin_cyclic_succ_sec9, hnext]
    omega

private theorem theorem_9_7_iSup_fin_cyclic_succ_eq_sec9
    {α : Type v} [CompleteLattice α]
    {q : ℕ} (hqpos : 0 < q) (H : Fin q → α) :
    (⨆ i, H (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)) = ⨆ i, H i := by
  apply le_antisymm
  · refine iSup_le ?_
    intro i
    exact le_iSup H (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)
  · refine iSup_le ?_
    intro j
    rcases theorem_9_7_fin_cyclic_succ_surjective_sec9 hqpos j with ⟨i, rfl⟩
    exact le_iSup (fun i => H (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)) i

private theorem theorem_9_7_quotientSubgroupNormalizedBy_iSup_fin_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 A : Subgroup G}
    [hnormal : (H0.subgroupOf MF).Normal]
    {q : ℕ} (hqpos : 0 < q)
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHnorm : ∀ i : Fin q, quotientSubgroupNormalizedBy MF H0 A (H i)) :
    quotientSubgroupNormalizedBy MF H0 A (iSup H) := by
  classical
  intro a
  rcases hHnorm ⟨0, hqpos⟩ a with ⟨hconjMF, action, haction, _hmapZero⟩
  refine ⟨hconjMF, action, haction, ?_⟩
  have hmap_each :
      ∀ i : Fin q, (H i).map action.toMonoidHom = H i := by
    intro i
    rcases hHnorm i a with ⟨hconjMF_i, action_i, haction_i, hmap_i⟩
    have haction_eq : action_i = action := by
      ext x
      rcases QuotientGroup.mk'_surjective (H0.subgroupOf MF) x with ⟨h, rfl⟩
      calc
        action_i (QuotientGroup.mk' (H0.subgroupOf MF) h) =
            QuotientGroup.mk' (H0.subgroupOf MF)
              ⟨(a : G)⁻¹ * (h : G) * (a : G), hconjMF_i h⟩ := haction_i h
        _ = QuotientGroup.mk' (H0.subgroupOf MF)
              ⟨(a : G)⁻¹ * (h : G) * (a : G), hconjMF h⟩ := by
              congr 1
        _ = action (QuotientGroup.mk' (H0.subgroupOf MF) h) := (haction h).symm
    simpa [haction_eq] using hmap_i.symm
  have hmap_sup : (iSup H).map action.toMonoidHom = iSup H := by
    rw [Subgroup.map_iSup]
    apply le_antisymm
    · refine iSup_le ?_
      intro i
      rw [hmap_each i]
      exact le_iSup H i
    · refine iSup_le ?_
      intro i
      rw [← hmap_each i]
      exact le_iSup (fun i => (H i).map action.toMonoidHom) i
  exact hmap_sup.symm

private theorem
    theorem_9_7_quotientSubgroupConjugateByElement_iSup_of_fin_cyclic_successor_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 W1 : Subgroup G}
    [hnormal : (H0.subgroupOf MF).Normal]
    {q : ℕ} (hqpos : 0 < q)
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (w0 : W1)
    (hsucc :
      ∀ i : Fin q,
        quotientSubgroupConjugateByElement MF H0 (H i)
          (H (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)) (w0 : G)) :
    quotientSubgroupConjugateByElement MF H0 (iSup H) (iSup H) (w0 : G) := by
  classical
  rcases hsucc ⟨0, hqpos⟩ with ⟨hconjMF, action, haction, _hmapZero⟩
  refine ⟨hconjMF, action, haction, ?_⟩
  have hmap_each :
      ∀ i : Fin q,
        (H i).map action.toMonoidHom =
          H (theorem_9_7_fin_cyclic_succ_sec9 hqpos i) := by
    intro i
    rcases hsucc i with ⟨hconjMF_i, action_i, haction_i, hmap_i⟩
    have haction_eq : action_i = action := by
      ext x
      rcases QuotientGroup.mk'_surjective (H0.subgroupOf MF) x with ⟨h, rfl⟩
      calc
        action_i (QuotientGroup.mk' (H0.subgroupOf MF) h) =
            QuotientGroup.mk' (H0.subgroupOf MF)
              ⟨((w0 : W1) : G)⁻¹ * (h : G) * ((w0 : W1) : G),
                hconjMF_i h⟩ := haction_i h
        _ = QuotientGroup.mk' (H0.subgroupOf MF)
              ⟨((w0 : W1) : G)⁻¹ * (h : G) * ((w0 : W1) : G),
                hconjMF h⟩ := by
              congr 1
        _ = action (QuotientGroup.mk' (H0.subgroupOf MF) h) := (haction h).symm
    simpa [haction_eq] using hmap_i.symm
  have hmap_sup : (iSup H).map action.toMonoidHom = iSup H := by
    rw [Subgroup.map_iSup]
    calc
      (⨆ i, (H i).map action.toMonoidHom) =
          ⨆ i, H (theorem_9_7_fin_cyclic_succ_sec9 hqpos i) := by
            apply le_antisymm
            · refine iSup_le ?_
              intro i
              rw [hmap_each i]
              exact le_iSup
                (fun i => H (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)) i
            · refine iSup_le ?_
              intro i
              rw [← hmap_each i]
              exact le_iSup (fun i => (H i).map action.toMonoidHom) i
      _ = iSup H := theorem_9_7_iSup_fin_cyclic_succ_eq_sec9 hqpos H
  exact hmap_sup.symm

private def theorem_9_7_orderedCliffordComponentData_sec9
    {G : Type u} [Group G] [Finite G]
    (MF H0 U W1 C : Subgroup G)
    (p q a : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    (w0 : W1) (hqpos : 0 < q) : Prop :=
  ∃ H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF),
    (∀ i, Nat.card (H i) = p) ∧
      (∀ i, quotientSubgroupNormalizedBy MF H0 U (H i)) ∧
      iSupIndep H ∧
      iSup H = ⊤ ∧
      (∀ i, quotientFactorActionCentralizerData MF H0 U C (H i) a) ∧
      ∀ i : Fin q,
        quotientSubgroupConjugateByElement MF H0
          (H i) (H (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)) (w0 : G)


private def theorem_9_7_orderedCliffordOrbitFactorData_sec9
    {G : Type u} [Group G] [Finite G]
    (MF H0 U C : Subgroup G)
    (p a : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    {q : ℕ}
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF)) : Prop :=
  (∀ i, Nat.card (H i) = p) ∧
    iSupIndep H ∧
    ∀ i, quotientFactorActionCentralizerData MF H0 U C (H i) a

private def theorem_9_7_orderedCliffordCharacterTransitionData_sec9
    {G : Type u} [Group G] [Finite G]
    (MF H0 U W1 C : Subgroup G)
    (q a : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hW1normU : Subgroup.Normalizes W1 U]
    (hnormalC : (C.subgroupOf U).Normal)
    (w0 : W1)
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q) : Prop :=
  letI : (C.subgroupOf U).Normal := hnormalC
  ∃ χbar : Fin q → (U ⧸ C.subgroupOf U) →* Multiplicative (ZMod a),
    (∀ i,
      ∃ ρ : (U ⧸ C.subgroupOf U) →* MulAut (H i),
        IsCyclic ρ.range ∧
          Nat.card ρ.range = a ∧
          (∀ x : U ⧸ C.subgroupOf U,
            ∀ u : U,
              QuotientGroup.mk' (C.subgroupOf U) u = x →
              ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
                ∀ h : MF,
                ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H i,
                  (ρ x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                      MF ⧸ H0.subgroupOf MF) =
                    QuotientGroup.mk' (H0.subgroupOf MF)
                      ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩) ∧
          (∀ x : U ⧸ C.subgroupOf U,
            ρ x = 1 ↔
              ∀ u : U,
                QuotientGroup.mk' (C.subgroupOf U) u = x →
                quotientSubgroupCentralizedByElement MF H0 (H i) (u : G)) ∧
          ∀ x y : U ⧸ C.subgroupOf U,
            χbar i x = χbar i y → ρ x = ρ y) ∧
      ∀ x : U,
        ∀ i,
          χbar i (QuotientGroup.mk' (C.subgroupOf U) (w0 • x)) =
            χbar (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)
              (QuotientGroup.mk' (C.subgroupOf U) x)

private theorem
    theorem_9_7_orderedCliffordCharacterRangeEquivs_of_successor_factor_actions_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {MF H0 U W1 C : Subgroup G}
    {q a : ℕ}
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hW1normU : Subgroup.Normalizes W1 U]
    (hnormalC : (C.subgroupOf U).Normal)
    (hCinv : IsInvariant W1 U (C.subgroupOf U))
    (w0 : W1)
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (hW1card : Nat.card W1 = q)
    (hw0gen : Subgroup.zpowers w0 = ⊤)
    (ρ : ∀ i, (U ⧸ C.subgroupOf U) →* MulAut (H i))
    (hcyc : ∀ i, IsCyclic (ρ i).range)
    (hcard : ∀ i, Nat.card (ρ i).range = a)
    (htransport :
      ∀ i : Fin q,
        ∃ e : H i ≃* H (theorem_9_7_fin_cyclic_succ_sec9 hqpos i),
          theorem_9_7_successorTransportFactorAction_sec9 hnormalC hCinv w0 e
            (ρ i) =
            ρ (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)) :
    letI : (C.subgroupOf U).Normal := hnormalC
    ∃ ψ : ∀ i, (ρ i).range ≃* Multiplicative (ZMod a),
      ∀ x : U,
        ∀ i,
          ψ i
              ⟨ρ i (QuotientGroup.mk' (C.subgroupOf U) (w0 • x)),
                ⟨QuotientGroup.mk' (C.subgroupOf U) (w0 • x), rfl⟩⟩ =
            ψ (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)
              ⟨ρ (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)
                  (QuotientGroup.mk' (C.subgroupOf U) x),
                ⟨QuotientGroup.mk' (C.subgroupOf U) x, rfl⟩⟩ := by
  classical
  letI : (C.subgroupOf U).Normal := hnormalC
  letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
    quotientMulDistribMulAction (A := W1) (G := U) (C.subgroupOf U) hCinv
  let τ : MulAut (U ⧸ C.subgroupOf U) :=
    (MulDistribMulAction.toMulAut W1 (U ⧸ C.subgroupOf U)) w0
  have hτ : τ ^ q = 1 :=
    theorem_9_7_generator_quotient_action_pow_eq_one_sec9
      hnormalC hCinv w0 hW1card hw0gen
  choose e he using htransport
  let edge : ∀ i, (ρ i).range ≃*
      (ρ (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)).range :=
    fun i =>
      (theorem_9_7_successorTransportFactorAction_rangeEquiv_sec9
        hnormalC hCinv w0 (e i) (ρ i)).trans
        (MulEquiv.subgroupCongr (congrArg MonoidHom.range (he i)))
  have hedge :
      ∀ i y,
        edge i ⟨ρ i (τ y), ⟨τ y, rfl⟩⟩ =
          ⟨ρ (theorem_9_7_fin_cyclic_succ_sec9 hqpos i) y, ⟨y, rfl⟩⟩ := by
    intro i y
    refine QuotientGroup.induction_on y ?_
    intro x
    simpa [edge, τ] using
      theorem_9_7_successorTransportFactorAction_rangeEdge_apply_mk_sec9
        hnormalC hCinv w0 (e i) (ρ i)
        (ρ (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)) (he i) x
  rcases
      theorem_9_7_successor_range_zmod_equivs_sec9
        hqpos τ hτ ρ hcyc hcard edge hedge with
    ⟨ψ, hψ⟩
  refine ⟨ψ, ?_⟩
  intro x i
  simpa [τ] using hψ (QuotientGroup.mk' (C.subgroupOf U) x) i

private theorem
    theorem_9_7_orderedCliffordCharacterIdentifications_of_successor_factor_actions_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {MF H0 U W1 C : Subgroup G}
    {q a : ℕ}
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hW1normU : Subgroup.Normalizes W1 U]
    (hnormalC : (C.subgroupOf U).Normal)
    (hCinv : IsInvariant W1 U (C.subgroupOf U))
    (w0 : W1)
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (hW1card : Nat.card W1 = q)
    (hw0gen : Subgroup.zpowers w0 = ⊤)
    (ρ : ∀ i, (U ⧸ C.subgroupOf U) →* MulAut (H i))
    (hcyc : ∀ i, IsCyclic (ρ i).range)
    (hcard : ∀ i, Nat.card (ρ i).range = a)
    (htransport :
      ∀ i : Fin q,
        ∃ e : H i ≃* H (theorem_9_7_fin_cyclic_succ_sec9 hqpos i),
          theorem_9_7_successorTransportFactorAction_sec9 hnormalC hCinv w0 e
            (ρ i) =
            ρ (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)) :
    letI : (C.subgroupOf U).Normal := hnormalC
    ∃ χbar : Fin q → (U ⧸ C.subgroupOf U) →* Multiplicative (ZMod a),
      (∀ i, ∀ x y : U ⧸ C.subgroupOf U,
        χbar i x = χbar i y → ρ i x = ρ i y) ∧
      ∀ x : U,
        ∀ i,
          χbar i (QuotientGroup.mk' (C.subgroupOf U) (w0 • x)) =
            χbar (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)
              (QuotientGroup.mk' (C.subgroupOf U) x) := by
  classical
  letI : (C.subgroupOf U).Normal := hnormalC
  rcases
      theorem_9_7_orderedCliffordCharacterRangeEquivs_of_successor_factor_actions_source_bridge_sec9
        hnormalC hCinv w0 H hqpos hW1card hw0gen ρ hcyc hcard htransport with
    ⟨ψ, hψ⟩
  let χbar : Fin q → (U ⧸ C.subgroupOf U) →* Multiplicative (ZMod a) :=
    fun i => (ψ i).toMonoidHom.comp (ρ i).rangeRestrict
  refine ⟨χbar, ?_, ?_⟩
  · intro i x y hxy
    dsimp [χbar] at hxy
    have hsub :
        (⟨ρ i x, ⟨x, rfl⟩⟩ : (ρ i).range) =
          ⟨ρ i y, ⟨y, rfl⟩⟩ :=
      (ψ i).injective hxy
    exact congrArg Subtype.val hsub
  · intro x i
    dsimp [χbar]
    exact hψ x i

private theorem
    theorem_9_7_orderedCliffordCharacterTransitionData_of_ordered_components_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {MF H0 U W1 C : Subgroup G}
    {q a : ℕ}
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hW1normU : Subgroup.Normalizes W1 U]
    (hnormalC : (C.subgroupOf U).Normal)
    (hCinv : IsInvariant W1 U (C.subgroupOf U))
    (w0 : W1)
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (hW1card : Nat.card W1 = q)
    (hw0gen : Subgroup.zpowers w0 = ⊤)
    (hfac : ∀ i, quotientFactorActionCentralizerData MF H0 U C (H i) a)
    (hsucc :
      ∀ i : Fin q,
        quotientSubgroupConjugateByElement MF H0
          (H i) (H (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)) (w0 : G)) :
    theorem_9_7_orderedCliffordCharacterTransitionData_sec9
      MF H0 U W1 C q a hnormalC w0 H hqpos := by
  classical
  letI : (C.subgroupOf U).Normal := hnormalC
  have hfacActions :
      ∀ i,
        ∃ ρ : (U ⧸ C.subgroupOf U) →* MulAut (H i),
          IsCyclic ρ.range ∧
            Nat.card ρ.range = a ∧
            (∀ x : U ⧸ C.subgroupOf U,
              ∀ u : U,
                QuotientGroup.mk' (C.subgroupOf U) u = x →
                ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
                  ∀ h : MF,
                  ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H i,
                    (ρ x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                        MF ⧸ H0.subgroupOf MF) =
                      QuotientGroup.mk' (H0.subgroupOf MF)
                        ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩) ∧
            ∀ x : U ⧸ C.subgroupOf U,
              ρ x = 1 ↔
                ∀ u : U,
                  QuotientGroup.mk' (C.subgroupOf U) u = x →
                  quotientSubgroupCentralizedByElement MF H0 (H i) (u : G) := by
    intro i
    rcases hfac i with ⟨_hnormal, ρ, hcyc, hcard, haction, hker⟩
    exact ⟨ρ, hcyc, hcard, haction, hker⟩
  choose ρ hρ using hfacActions
  have hcyc : ∀ i, IsCyclic (ρ i).range := fun i => (hρ i).1
  have hcard : ∀ i, Nat.card (ρ i).range = a := fun i => (hρ i).2.1
  have haction :
      ∀ i,
        ∀ x : U ⧸ C.subgroupOf U,
          ∀ u : U,
            QuotientGroup.mk' (C.subgroupOf U) u = x →
            ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
              ∀ h : MF,
              ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H i,
                (ρ i x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                    MF ⧸ H0.subgroupOf MF) =
                  QuotientGroup.mk' (H0.subgroupOf MF)
                    ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩ :=
    fun i => (hρ i).2.2.1
  have hker :
      ∀ i,
        ∀ x : U ⧸ C.subgroupOf U,
          ρ i x = 1 ↔
            ∀ u : U,
              QuotientGroup.mk' (C.subgroupOf U) u = x →
              quotientSubgroupCentralizedByElement MF H0 (H i) (u : G) :=
    fun i => (hρ i).2.2.2
  have htransport :
      ∀ i : Fin q,
        ∃ e : H i ≃* H (theorem_9_7_fin_cyclic_succ_sec9 hqpos i),
          theorem_9_7_successorTransportFactorAction_sec9 hnormalC hCinv w0 e
            (ρ i) =
            ρ (theorem_9_7_fin_cyclic_succ_sec9 hqpos i) := by
    intro i
    rcases theorem_9_7_successorTransportFactorAction_eq_of_action_field_sec9
        hnormalC hCinv w0 (hsucc i) (ρ := ρ i)
        (σ := ρ (theorem_9_7_fin_cyclic_succ_sec9 hqpos i))
        (haction i)
        (haction (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)) with
      ⟨e, _heData, he⟩
    exact ⟨e, he⟩
  rcases
      theorem_9_7_orderedCliffordCharacterIdentifications_of_successor_factor_actions_source_bridge_sec9
        hnormalC hCinv w0 H hqpos hW1card hw0gen ρ hcyc hcard htransport with
    ⟨χbar, hχsep, hχtrans⟩
  exact ⟨χbar, fun i => ⟨ρ i, hcyc i, hcard i, haction i, hker i, hχsep i⟩,
    hχtrans⟩

private theorem theorem_9_7_base_card_eq_prime_of_iSupIndep_equal_card_span_sec9
    {V : Type u} [Group V] [Finite V]
    {p q : ℕ}
    (hpprime : Nat.Prime p)
    (hqprime : Nat.Prime q)
    (hVelem : IsElementaryAbelian p V)
    (hfinrank :
      letI : Fact p.Prime := ⟨hpprime⟩
      letI : IsElementaryAbelian p V := hVelem
      Module.finrank (ZMod p) (Additive V) = q)
    (Q : Subgroup V)
    (H : Fin q → Subgroup V)
    (hHcardEqQ : ∀ i, Nat.card (H i) = Nat.card Q)
    (hHsup : iSup H = ⊤)
    (hHindep : iSupIndep H) :
    Nat.card Q = p := by
  classical
  letI : Fact p.Prime := ⟨hpprime⟩
  letI : IsElementaryAbelian p V := hVelem
  have hVcard : Nat.card V = p ^ q := by
    have hnat := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive V)
    have hcardAdd : Nat.card (Additive V) = Nat.card V :=
      Nat.card_congr
        { toFun := Additive.toMul
          invFun := Additive.ofMul
          left_inv := by intro x; rfl
          right_inv := by intro x; rfl }
    calc
      Nat.card V = Nat.card (Additive V) := hcardAdd.symm
      _ = p ^ Module.finrank (ZMod p) (Additive V) := by
        simpa [Nat.card_eq_fintype_card, ZMod.card] using hnat
      _ = p ^ q := by rw [hfinrank]
  have hcomm :
      Pairwise fun i j : Fin q =>
        ∀ x y : V, x ∈ H i → y ∈ H j → Commute x y := by
    intro _i _j _hij x y _hx _hy
    exact mul_comm x y
  let φ : ((i : Fin q) → H i) →* V :=
    Subgroup.noncommPiCoprod (H := H) hcomm
  have hφinj : Function.Injective φ :=
    Subgroup.injective_noncommPiCoprod_of_iSupIndep
      (H := H) (hcomm := hcomm) hHindep
  have hφrange : φ.range = ⊤ := by
    calc
      φ.range = iSup H := by
        simpa [φ] using
          (Subgroup.noncommPiCoprod_range (H := H) (hcomm := hcomm))
      _ = ⊤ := hHsup
  have hprodCard : Nat.card ((i : Fin q) → H i) = Nat.card V := by
    calc
      Nat.card ((i : Fin q) → H i) = Nat.card φ.range :=
        Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv
      _ = Nat.card (⊤ : Subgroup V) := by rw [hφrange]
      _ = Nat.card V := Subgroup.card_top
  have hQpow : Nat.card Q ^ q = p ^ q := by
    calc
      Nat.card Q ^ q = ∏ _i : Fin q, Nat.card Q := by simp
      _ = ∏ i : Fin q, Nat.card (H i) := by
        exact Finset.prod_congr rfl (fun i _hi => (hHcardEqQ i).symm)
      _ = Nat.card ((i : Fin q) → H i) := by rw [Nat.card_pi]
      _ = Nat.card V := hprodCard
      _ = p ^ q := hVcard
  exact Nat.pow_left_injective hqprime.ne_zero hQpow

private theorem theorem_9_7_iSupIndep_of_noncommPiCoprod_injective_sec9
    {G : Type u} [CommGroup G]
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    {H : ι → Subgroup G}
    (hcomm :
      Pairwise fun i j : ι =>
        ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y)
    (hinj :
      Function.Injective (Subgroup.noncommPiCoprod (H := H) hcomm)) :
    iSupIndep H := by
  classical
  rw [iSupIndep_def]
  intro i
  rw [disjoint_iff]
  apply le_bot_iff.mp
  intro x hx
  rcases hx with ⟨hxi, hxrest⟩
  let K : {j // j ≠ i} → Subgroup G := fun j => H j.1
  have hcommK :
      Pairwise fun a b : {j // j ≠ i} =>
        ∀ x y : G, x ∈ K a → y ∈ K b → Commute x y := by
    intro a b hab x y hx hy
    exact hcomm (fun h => hab (Subtype.ext h)) x y hx hy
  have hxrange :
      x ∈ (Subgroup.noncommPiCoprod (H := K) hcommK).range := by
    rw [Subgroup.noncommPiCoprod_range (H := K) (hcomm := hcommK)]
    simpa [K, iSup_subtype'] using hxrest
  rcases hxrange with ⟨frest, hfrest⟩
  let fone : (j : ι) → H j := fun j =>
    if hji : j = i then
      1
    else
      ⟨(frest ⟨j, hji⟩ : G), by
        change (frest ⟨j, hji⟩ : G) ∈ K ⟨j, hji⟩
        exact (frest ⟨j, hji⟩).property⟩
  have hfone : Subgroup.noncommPiCoprod (H := H) hcomm fone = x := by
    rw [← hfrest]
    simp only [Subgroup.noncommPiCoprod_apply, Finset.noncommProd_eq_prod]
    rw [Fintype.prod_eq_mul_prod_subtype_ne (fun j => (fone j : G)) i]
    simp only [fone]
    simp
    apply Finset.prod_congr rfl
    intro j _hj
    simp [K, j.property]
  let fxi : (j : ι) → H j := Pi.mulSingle i ⟨x, hxi⟩
  have hfxi : Subgroup.noncommPiCoprod (H := H) hcomm fxi = x := by
    simp [fxi]
  have hfg : fxi = fone := hinj (by rw [hfxi, hfone])
  have hi := congrFun hfg i
  have hx1 : x = 1 := by
    have := congrArg Subtype.val hi
    simpa [fxi, fone] using this
  exact Subgroup.mem_bot.mpr hx1

private theorem theorem_9_7_iSupIndep_of_zmod_submodule_iSupIndep_sec9
    {V : Type u} [Group V] {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {ι : Sort v} (H : ι → Subgroup V)
    (hHindep :
      iSupIndep
        ((Subgroup.toAddSubgroup.trans
          (AddSubgroup.toZModSubmodule (M := Additive V) (n := p))) ∘ H)) :
    iSupIndep H := by
  exact
    (iSupIndep_map_orderIso_iff
      (Subgroup.toAddSubgroup.trans
        (AddSubgroup.toZModSubmodule (M := Additive V) (n := p)))
      (a := H)).mp hHindep

private theorem theorem_9_7_zmod_submodule_iSupIndep_of_iSupIndep_sec9
    {V : Type u} [Group V] {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {ι : Sort v} (H : ι → Subgroup V)
    (hHindep : iSupIndep H) :
    iSupIndep
      ((Subgroup.toAddSubgroup.trans
        (AddSubgroup.toZModSubmodule (M := Additive V) (n := p))) ∘ H) := by
  exact
    (iSupIndep_map_orderIso_iff
      (Subgroup.toAddSubgroup.trans
        (AddSubgroup.toZModSubmodule (M := Additive V) (n := p)))
      (a := H)).mpr hHindep

private theorem theorem_9_7_zmod_submodule_internal_direct_sum_of_iSupIndep_span_sec9
    {V : Type u} [Group V] {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {ι : Type v} [DecidableEq ι] (H : ι → Subgroup V)
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤) :
    let η : Subgroup V ≃o Submodule (ZMod p) (Additive V) :=
      Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule (n := p))
    DirectSum.IsInternal fun i => η (H i) := by
  classical
  let η : Subgroup V ≃o Submodule (ZMod p) (Additive V) :=
    Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule (n := p))
  have hHindepZ : iSupIndep fun i => η (H i) := by
    change iSupIndep
      ((Subgroup.toAddSubgroup.trans
        (AddSubgroup.toZModSubmodule (M := Additive V) (n := p))) ∘ H)
    exact theorem_9_7_zmod_submodule_iSupIndep_of_iSupIndep_sec9
      (V := V) (p := p) H hHindep
  have hHsupZ : iSup (fun i => η (H i)) = ⊤ := by
    calc
      iSup (fun i => η (H i)) = η (iSup H) := (η.map_iSup H).symm
      _ = η ⊤ := by rw [hHsup]
      _ = ⊤ := by simp [η]
  exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hHindepZ hHsupZ

private theorem theorem_9_7_ofSubmodule_mapSubmodule_toSubmodule_sec9
    {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (S : ρ.invtSubmodule) :
    (Subrepresentation.ofSubmodule' (ρ.mapSubmodule S)).toSubmodule =
      (S : Submodule k V) := by
  ext v
  constructor
  · intro hv
    change v ∈ AddSubmonoid.map ρ.asModuleEquiv.symm
      (S : Submodule k V).toAddSubmonoid at hv
    rcases hv with ⟨x, hx, hxv⟩
    have hxv' : x = v := by
      calc
        x = ρ.asModuleEquiv (ρ.asModuleEquiv.symm x) :=
          (ρ.asModuleEquiv.apply_symm_apply x).symm
        _ = ρ.asModuleEquiv v := congrArg ρ.asModuleEquiv hxv
        _ = v := rfl
    simpa [hxv'] using hx
  · intro hv
    change v ∈ AddSubmonoid.map ρ.asModuleEquiv.symm
      (S : Submodule k V).toAddSubmonoid
    refine ⟨v, hv, ?_⟩
    rfl

private theorem theorem_9_7_iSupIndep_of_subrepresentation_carriers_sec9
    {A V : Type*} [Group A] [Group V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (ρ : Representation (ZMod p) A (Additive V))
    {ι : Sort v} (H : ι → Subgroup V) (S : ι → Subrepresentation ρ)
    (hS :
      ∀ i,
        (S i).toSubmodule =
          (Subgroup.toAddSubgroup.trans
            (AddSubgroup.toZModSubmodule (M := Additive V) (n := p))) (H i))
    (hSindep : iSupIndep fun i => (S i).toSubmodule) :
    iSupIndep H := by
  refine theorem_9_7_iSupIndep_of_zmod_submodule_iSupIndep_sec9 (V := V) (p := p) H ?_
  convert hSindep using 1
  ext i x
  simp [Function.comp, hS i]

private theorem theorem_9_7_subrepresentation_le_of_nonzero_mem_sec9
    {F A V : Type*} [Field F] [Group A] [AddCommGroup V] [Module F V]
    {ρ : Representation F A V}
    (S T : Subrepresentation ρ) [Representation.IsIrreducible S.toRepresentation]
    {v : V} (hvS : v ∈ S.toSubmodule) (hvT : v ∈ T.toSubmodule)
    (hv : v ≠ 0) :
    S ≤ T := by
  let U : Subrepresentation S.toRepresentation := {
    toSubmodule := T.toSubmodule.comap S.toSubmodule.subtype
    apply_mem_toSubmodule := by
      intro a w hw
      exact T.apply_mem_toSubmodule a hw }
  have hU_ne : U ≠ ⊥ := by
    intro hU
    have hvU : (⟨v, hvS⟩ : S.toSubmodule) ∈ U.toSubmodule := hvT
    have hv0 : v = 0 := by
      have hv0sub : (⟨v, hvS⟩ : S.toSubmodule) = 0 := by
        rw [hU] at hvU
        change (⟨v, hvS⟩ : S.toSubmodule) = 0 at hvU
        exact hvU
      exact Subtype.ext_iff.mp hv0sub
    exact hv hv0
  have hU_top : U = ⊤ := by
    rcases (inferInstance : Representation.IsIrreducible S.toRepresentation).eq_bot_or_eq_top U with
    hbot | htop
    · exact False.elim (hU_ne hbot)
    · exact htop
  intro w hw
  have hwU : (⟨w, hw⟩ : S.toSubmodule) ∈ U.toSubmodule := by
    rw [hU_top]
    trivial
  exact hwU


private theorem
    theorem_9_7_zmod_submodule_mem_invtSubmodule_of_quotientSubgroupNormalizedBy_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 U : Subgroup G} {p : ℕ}
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [Fact p.Prime]
    (hbarElem : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF))
    (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G))
    (hH0invU :
      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
      IsInvariant U MF (H0.subgroupOf MF))
    (Q : Subgroup (MF ⧸ H0.subgroupOf MF))
    (hQnorm : quotientSubgroupNormalizedBy MF H0 U Q) :
    letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
    letI : MulAction.QuotientAction U (H0.subgroupOf MF) :=
      quotientAction_of_isInvariant (A := U) (G := MF)
        (H0.subgroupOf MF) hH0invU
    letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
      quotientMulDistribMulAction (A := U) (G := MF)
        (H0.subgroupOf MF) hH0invU
    letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
    let ρ : Representation (ZMod p) U (Additive (MF ⧸ H0.subgroupOf MF)) :=
      Theory.Representation.ofElementaryAbelianAction
        (A := U) (G := MF ⧸ H0.subgroupOf MF) (p := p)
    let η : Subgroup (MF ⧸ H0.subgroupOf MF) ≃o
        Submodule (ZMod p) (Additive (MF ⧸ H0.subgroupOf MF)) :=
      Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule (n := p))
    η Q ∈ ρ.invtSubmodule := by
  classical
  letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
  letI : MulAction.QuotientAction U (H0.subgroupOf MF) :=
    quotientAction_of_isInvariant (A := U) (G := MF)
      (H0.subgroupOf MF) hH0invU
  letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
    quotientMulDistribMulAction (A := U) (G := MF)
      (H0.subgroupOf MF) hH0invU
  letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
  let ρ : Representation (ZMod p) U (Additive (MF ⧸ H0.subgroupOf MF)) :=
    Theory.Representation.ofElementaryAbelianAction
      (A := U) (G := MF ⧸ H0.subgroupOf MF) (p := p)
  let η : Subgroup (MF ⧸ H0.subgroupOf MF) ≃o
      Submodule (ZMod p) (Additive (MF ⧸ H0.subgroupOf MF)) :=
    Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule (n := p))
  have hQinv : IsInvariant U (MF ⧸ H0.subgroupOf MF) Q :=
    isInvariant_of_quotientSubgroupNormalizedBy_sec9
      (MF := MF) (H0 := H0) (A := U) hH0invU Q hQnorm
  rw [Representation.mem_invtSubmodule]
  intro u
  rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
  intro x hx
  have hxQ : Additive.toMul x ∈ Q := by
    simpa [η] using hx
  simpa [ρ, η] using
    (IsInvariant.invariant (A := U) (G := MF ⧸ H0.subgroupOf MF)
      (H := Q) u (Additive.toMul x)).1 hxQ

private theorem
    theorem_9_7_subrepresentation_of_quotientSubgroupNormalizedBy_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 U : Subgroup G} {p : ℕ}
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [Fact p.Prime]
    (hbarElem : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF))
    (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G))
    (hH0invU :
      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
      IsInvariant U MF (H0.subgroupOf MF))
    (Q : Subgroup (MF ⧸ H0.subgroupOf MF))
    (hQnorm : quotientSubgroupNormalizedBy MF H0 U Q) :
    letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
    letI : MulAction.QuotientAction U (H0.subgroupOf MF) :=
      quotientAction_of_isInvariant (A := U) (G := MF)
        (H0.subgroupOf MF) hH0invU
    letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
      quotientMulDistribMulAction (A := U) (G := MF)
        (H0.subgroupOf MF) hH0invU
    letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
    let ρ : Representation (ZMod p) U (Additive (MF ⧸ H0.subgroupOf MF)) :=
      Theory.Representation.ofElementaryAbelianAction
        (A := U) (G := MF ⧸ H0.subgroupOf MF) (p := p)
    let η : Subgroup (MF ⧸ H0.subgroupOf MF) ≃o
        Submodule (ZMod p) (Additive (MF ⧸ H0.subgroupOf MF)) :=
      Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule (n := p))
    ∃ S : Subrepresentation ρ, S.toSubmodule = η Q := by
  classical
  letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
  letI : MulAction.QuotientAction U (H0.subgroupOf MF) :=
    quotientAction_of_isInvariant (A := U) (G := MF)
      (H0.subgroupOf MF) hH0invU
  letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
    quotientMulDistribMulAction (A := U) (G := MF)
      (H0.subgroupOf MF) hH0invU
  letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
  let ρ : Representation (ZMod p) U (Additive (MF ⧸ H0.subgroupOf MF)) :=
    Theory.Representation.ofElementaryAbelianAction
      (A := U) (G := MF ⧸ H0.subgroupOf MF) (p := p)
  let η : Subgroup (MF ⧸ H0.subgroupOf MF) ≃o
      Submodule (ZMod p) (Additive (MF ⧸ H0.subgroupOf MF)) :=
    Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule (n := p))
  have hQinvt : η Q ∈ ρ.invtSubmodule :=
    theorem_9_7_zmod_submodule_mem_invtSubmodule_of_quotientSubgroupNormalizedBy_sec9
      (MF := MF) (H0 := H0) (U := U) hbarElem hUnormMF hH0invU Q hQnorm
  let Qpack : ρ.invtSubmodule := ⟨η Q, hQinvt⟩
  refine ⟨Subrepresentation.ofSubmodule' (ρ.mapSubmodule Qpack), ?_⟩
  calc
    (Subrepresentation.ofSubmodule' (ρ.mapSubmodule Qpack)).toSubmodule =
        (Qpack : Submodule (ZMod p) (Additive (MF ⧸ H0.subgroupOf MF))) :=
      theorem_9_7_ofSubmodule_mapSubmodule_toSubmodule_sec9 ρ Qpack
    _ = η Q := rfl

private theorem
    theorem_9_7_irreducible_subrepresentation_of_minimal_invariant_subgroup_sec9
    {A V : Type*} [Group A] [Group V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    [MulDistribMulAction A V]
    (Q : Subgroup V)
    (hQneBot : Q ≠ ⊥)
    (hQminimal :
      ∀ R : Subgroup V, IsInvariant A V R → R ≠ ⊥ → R ≤ Q → Q ≤ R)
    (S : Subrepresentation
      (Theory.Representation.ofElementaryAbelianAction (A := A) (G := V) (p := p)))
    (hS :
      let η : Subgroup V ≃o Submodule (ZMod p) (Additive V) :=
        Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule (n := p))
      S.toSubmodule = η Q) :
    Representation.IsIrreducible S.toRepresentation := by
  classical
  let ρ : Representation (ZMod p) A (Additive V) :=
    Theory.Representation.ofElementaryAbelianAction (A := A) (G := V) (p := p)
  let η : Subgroup V ≃o Submodule (ZMod p) (Additive V) :=
    Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule (n := p))
  have hS' : S.toSubmodule = η Q := by
    simpa [η] using hS
  rw [Subrepresentation.irreducible_iff_isAtom]
  constructor
  · intro hSbot
    apply hQneBot
    ext x
    constructor
    · intro hxQ
      have hxS : Additive.ofMul x ∈ S.toSubmodule := by
        simpa [hS', η] using hxQ
      rw [hSbot] at hxS
      change x = 1 at hxS
      exact Subgroup.mem_bot.mpr hxS
    · intro hxBot
      have hxone := Subgroup.mem_bot.mp hxBot
      rw [hxone]
      exact Q.one_mem
  · intro T hTS
    by_cases hTbot : T = ⊥
    · exact hTbot
    · exfalso
      let R : Subgroup V := T.toSubmodule.toAddSubgroup.toSubgroup'
      have hRinv : IsInvariant A V R := by
        have hmap_mem (a : A) {x : V} (hx : x ∈ R) : a • x ∈ R := by
          change Additive.ofMul (a • x) ∈ T.toSubmodule
          have hx' : Additive.ofMul x ∈ T.toSubmodule := by
            simpa [R, Submodule.mem_toAddSubgroup] using hx
          have hx'' := T.apply_mem_toSubmodule a hx'
          simpa [ρ, Theory.Representation.ofElementaryAbelianAction_apply_ofMul] using hx''
        refine { invariant := ?_ }
        intro a x
        constructor
        · intro hx
          exact hmap_mem a hx
        · intro hx
          have hx' : (a : A)⁻¹ • ((a : A) • x) ∈ R := hmap_mem (a : A)⁻¹ hx
          simpa [smul_smul] using hx'
      have hRneBot : R ≠ ⊥ := by
        intro hRbot
        apply hTbot
        apply Subrepresentation.toSubmodule_injective
        ext x
        constructor
        · intro hxT
          have hxR : Additive.toMul x ∈ R := by
            simpa [R, Submodule.mem_toAddSubgroup] using hxT
          have hxBot : Additive.toMul x ∈ (⊥ : Subgroup V) := by
            simpa [hRbot] using hxR
          change Additive.toMul x = 1
          exact Subgroup.mem_bot.mp hxBot
        · intro hxBot
          change x = 0 at hxBot
          subst x
          exact T.toSubmodule.zero_mem
      have hRleQ : R ≤ Q := by
        intro x hxR
        have hxT : Additive.ofMul x ∈ T.toSubmodule := by
          simpa [R, Submodule.mem_toAddSubgroup] using hxR
        have hxS : Additive.ofMul x ∈ S.toSubmodule := hTS.le hxT
        have hxQ : x ∈ Q := by
          simpa [hS', η] using hxS
        exact hxQ
      have hQleR : Q ≤ R := hQminimal R hRinv hRneBot hRleQ
      have hSleT : S ≤ T := by
        intro x hxS
        change x ∈ S.toSubmodule at hxS
        have hxQ : Additive.toMul x ∈ Q := by
          simpa [hS', η] using hxS
        have hxR : Additive.toMul x ∈ R := hQleR hxQ
        change Additive.toMul x ∈ R
        exact hxR
      have hEq : T = S := le_antisymm hTS.le hSleT
      exact (ne_of_lt hTS) hEq

private theorem theorem_9_7_iSupIndep_of_equal_prime_card_span_sec9
    {V : Type u} [Group V] [Finite V]
    {p q : ℕ}
    (hpprime : Nat.Prime p)
    (hVelem : IsElementaryAbelian p V)
    (hfinrank :
      letI : Fact p.Prime := ⟨hpprime⟩
      letI : IsElementaryAbelian p V := hVelem
      Module.finrank (ZMod p) (Additive V) = q)
    (Q : Subgroup V)
    (H : Fin q → Subgroup V)
    (hQcard : Nat.card Q = p)
    (hHcardEqQ : ∀ i, Nat.card (H i) = Nat.card Q)
    (hHsup : iSup H = ⊤) :
    iSupIndep H := by
  classical
  letI : Fact p.Prime := ⟨hpprime⟩
  letI : IsElementaryAbelian p V := hVelem
  letI : CommGroup V := { (inferInstance : Group V) with mul_comm := mul_comm }
  have hVcard : Nat.card V = p ^ q := by
    have hnat := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive V)
    have hcardAdd : Nat.card (Additive V) = Nat.card V :=
      Nat.card_congr
        { toFun := Additive.toMul
          invFun := Additive.ofMul
          left_inv := by intro x; rfl
          right_inv := by intro x; rfl }
    calc
      Nat.card V = Nat.card (Additive V) := hcardAdd.symm
      _ = p ^ Module.finrank (ZMod p) (Additive V) := by
        simpa [Nat.card_eq_fintype_card, ZMod.card] using hnat
      _ = p ^ q := by rw [hfinrank]
  have hdomainCard : Nat.card ((i : Fin q) → H i) = p ^ q := by
    calc
      Nat.card ((i : Fin q) → H i) =
          ∏ i : Fin q, Nat.card (H i) := Nat.card_pi
      _ = ∏ _i : Fin q, p := by
        apply Finset.prod_congr rfl
        intro i _hi
        rw [hHcardEqQ i, hQcard]
      _ = p ^ q := by simp
  have hcomm :
      Pairwise fun i j : Fin q =>
        ∀ x y : V, x ∈ H i → y ∈ H j → Commute x y := by
    intro _i _j _hij x y _hx _hy
    exact mul_comm x y
  let φ : ((i : Fin q) → H i) →* V :=
    Subgroup.noncommPiCoprod (H := H) hcomm
  have hφrange : φ.range = ⊤ := by
    calc
      φ.range = iSup H := by
        simpa [φ] using
          (Subgroup.noncommPiCoprod_range (H := H) (hcomm := hcomm))
      _ = ⊤ := hHsup
  have hsurj : Function.Surjective φ := by
    intro x
    have hx : x ∈ φ.range := by
      rw [hφrange]
      exact Subgroup.mem_top x
    exact hx
  have hφinj : Function.Injective φ :=
    (hsurj.bijective_of_nat_card_le (by rw [hdomainCard, hVcard])).1
  exact theorem_9_7_iSupIndep_of_noncommPiCoprod_injective_sec9 hcomm hφinj

private theorem
    theorem_9_7_quotientFactorActionCentralizerData_of_prime_card_normalized_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 U C : Subgroup G} {p : ℕ}
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    (hpprime : Nat.Prime p)
    (hnormalC : (C.subgroupOf U).Normal)
    (hC : quotientCentralizerIn MF H0 U C)
    (hbarComm :
      letI : (C.subgroupOf U).Normal := hnormalC
      IsMulCommutative (U ⧸ C.subgroupOf U))
    (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G))
    (hH0invU :
      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
      IsInvariant U MF (H0.subgroupOf MF))
    (Q : Subgroup (MF ⧸ H0.subgroupOf MF))
    (hQnorm : quotientSubgroupNormalizedBy MF H0 U Q)
    (hQcard : Nat.card Q = p) :
    ∃ a : ℕ, quotientFactorActionCentralizerData MF H0 U C Q a := by
  classical
  let H0MF : Subgroup MF := H0.subgroupOf MF
  haveI : H0MF.Normal := hnormalH0
  letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
  have hH0invU' : IsInvariant U MF H0MF := by
    simpa [H0MF] using hH0invU
  letI : MulAction.QuotientAction U H0MF :=
    quotientAction_of_isInvariant (A := U) (G := MF) H0MF hH0invU'
  letI : MulDistribMulAction U (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := U) (G := MF) H0MF hH0invU'
  have hQinv : IsInvariant U (MF ⧸ H0MF) Q := by
    simpa [H0MF] using
      (isInvariant_of_quotientSubgroupNormalizedBy_sec9
        (MF := MF) (H0 := H0) (A := U) hH0invU' Q hQnorm)
  letI : IsInvariant U (MF ⧸ H0MF) Q := hQinv
  let φU : U →* MulAut Q := MulDistribMulAction.toMulAut U Q
  have hCker : C.subgroupOf U ≤ φU.ker := by
    intro c _hc
    rw [MonoidHom.mem_ker]
    ext y
    have hcC : (c : G) ∈ C := by
      simpa [Subgroup.mem_subgroupOf] using _hc
    have hcommc :
        ∀ h : G, h ∈ MF →
          ⁅(c : G), h⁆ ∈ H0 := by
      intro h hhMF
      exact (hC.2 (c : G) c.property).mp hcC h hhMF
    have hfix :=
      theorem_9_7_quotient_action_fixed_of_commutator_sec9
        (MF := MF) (H0 := H0) (U := U) hnormalH0 hUnormMF hH0invU'
        (x := c) hcommc
    change c • (y : MF ⧸ H0MF) = (y : MF ⧸ H0MF)
    exact hfix (y : MF ⧸ H0MF)
  let φbar : (U ⧸ C.subgroupOf U) →* MulAut Q :=
    QuotientGroup.lift (C.subgroupOf U) φU hCker
  letI : (C.subgroupOf U).Normal := hnormalC
  haveI : IsMulCommutative (U ⧸ C.subgroupOf U) := hbarComm
  letI : CommGroup (U ⧸ C.subgroupOf U) := IsMulCommutative.instCommGroup
  let ρ : (U ⧸ C.subgroupOf U) →* MulAut Q :=
    φbar.comp (invMonoidHom : (U ⧸ C.subgroupOf U) →* (U ⧸ C.subgroupOf U))
  refine ⟨Nat.card ρ.range, hnormalC, ρ, ?_, rfl, ?_, ?_⟩
  · haveI : Fact p.Prime := ⟨hpprime⟩
    haveI : IsCyclic Q := isCyclic_of_prime_card (p := p) hQcard
    have hAutCyclic : IsCyclic (MulAut Q) := by
      let e : MulAut Q ≃* (ZMod (Nat.card Q))ˣ :=
        IsCyclic.mulAutMulEquiv (G := Q)
      have hUnits : IsCyclic (ZMod (Nat.card Q))ˣ := by
        rw [hQcard]
        exact ZMod.isCyclic_units_prime hpprime
      exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
    letI : IsCyclic (MulAut Q) := hAutCyclic
    infer_instance
  · intro x u hux
    have hxinv : x⁻¹ = QuotientGroup.mk' (C.subgroupOf U) (u⁻¹) := by
      rw [← hux]
      simp
    have hρu : ρ x = φU (u⁻¹) := by
      change φbar (x⁻¹) = φU (u⁻¹)
      rw [hxinv]
      exact QuotientGroup.lift_mk' (C.subgroupOf U) hCker (u⁻¹)
    let hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF := by
      intro h
      have hsmulG :
          (((u⁻¹ : U) • h : MF) : G) =
            (u : G)⁻¹ * (h : G) * (u : G) := by
        simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
      exact hsmulG ▸ (((u⁻¹ : U) • h : MF).property)
    refine ⟨hconjMF, ?_⟩
    intro h hhQ
    have hsmul_mk :
        (u⁻¹ : U) • QuotientGroup.mk' H0MF h =
          QuotientGroup.mk' H0MF ((u⁻¹ : U) • h) := by
      simpa only [QuotientGroup.mk'_apply] using
        (MulAction.Quotient.smul_mk (H := H0MF) (u⁻¹ : U) h)
    have hsmul_eq :
        ((u⁻¹ : U) • h : MF) =
          ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩ := by
      apply Subtype.ext
      simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
    calc
      (ρ x ⟨QuotientGroup.mk' H0MF h, hhQ⟩ : MF ⧸ H0MF) =
          (φU (u⁻¹) ⟨QuotientGroup.mk' H0MF h, hhQ⟩ : MF ⧸ H0MF) := by
            rw [hρu]
      _ = (u⁻¹ : U) • QuotientGroup.mk' H0MF h := rfl
      _ = QuotientGroup.mk' H0MF ((u⁻¹ : U) • h) := hsmul_mk
      _ = QuotientGroup.mk' H0MF
            ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩ := by
          rw [hsmul_eq]
  · intro x
    constructor
    · intro hx u hux
      have hxinv : x⁻¹ = QuotientGroup.mk' (C.subgroupOf U) (u⁻¹) := by
        rw [← hux]
        simp
      have hρu : ρ x = φU (u⁻¹) := by
        change φbar (x⁻¹) = φU (u⁻¹)
        rw [hxinv]
        exact QuotientGroup.lift_mk' (C.subgroupOf U) hCker (u⁻¹)
      have hφu : φU (u⁻¹) = 1 := by
        rw [← hρu]
        exact hx
      let hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF := by
        intro h
        have hsmulG :
            (((u⁻¹ : U) • h : MF) : G) =
              (u : G)⁻¹ * (h : G) * (u : G) := by
          simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
        exact hsmulG ▸ (((u⁻¹ : U) • h : MF).property)
      let action : MulAut (MF ⧸ H0MF) :=
        MulDistribMulAction.toMulAut U (MF ⧸ H0MF) (u⁻¹ : U)
      refine ⟨hconjMF, action, ?_, ?_⟩
      · intro h
        have hsmul_mk :
            (u⁻¹ : U) • QuotientGroup.mk' H0MF h =
              QuotientGroup.mk' H0MF ((u⁻¹ : U) • h) := by
          simpa only [QuotientGroup.mk'_apply] using
            (MulAction.Quotient.smul_mk (H := H0MF) (u⁻¹ : U) h)
        have hsmul_eq :
            ((u⁻¹ : U) • h : MF) =
              ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩ := by
          apply Subtype.ext
          simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
        change (u⁻¹ : U) • QuotientGroup.mk' H0MF h =
          QuotientGroup.mk' H0MF
            ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩
        rw [hsmul_mk, hsmul_eq]
      · intro y hyQ
        have hyfix : φU (u⁻¹) ⟨y, hyQ⟩ = ⟨y, hyQ⟩ := by
          rw [hφu]
          rfl
        exact congrArg Subtype.val hyfix
    · intro hcent
      revert hcent
      refine QuotientGroup.induction_on x ?_
      intro u hcent
      have hρu : ρ (QuotientGroup.mk' (C.subgroupOf U) u) = φU (u⁻¹) := by
        change φbar ((QuotientGroup.mk' (C.subgroupOf U) u)⁻¹) = φU (u⁻¹)
        rw [show (QuotientGroup.mk' (C.subgroupOf U) u)⁻¹ =
            QuotientGroup.mk' (C.subgroupOf U) (u⁻¹) by simp]
        exact QuotientGroup.lift_mk' (C.subgroupOf U) hCker (u⁻¹)
      rcases hcent u rfl with ⟨hconjMF, action, haction, hfix⟩
      change ρ (QuotientGroup.mk' (C.subgroupOf U) u) = 1
      rw [hρu]
      ext y
      rcases y with ⟨y, hyQ⟩
      revert hyQ
      refine QuotientGroup.induction_on y ?_
      intro h hyQ
      have hsmul_mk :
          (u⁻¹ : U) • QuotientGroup.mk' H0MF h =
            QuotientGroup.mk' H0MF ((u⁻¹ : U) • h) := by
        simpa only [QuotientGroup.mk'_apply] using
          (MulAction.Quotient.smul_mk (H := H0MF) (u⁻¹ : U) h)
      let hconjMFU : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF := by
        intro h
        have hsmulG :
            (((u⁻¹ : U) • h : MF) : G) =
              (u : G)⁻¹ * (h : G) * (u : G) := by
          simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
        exact hsmulG ▸ (((u⁻¹ : U) • h : MF).property)
      have hsmul_eq :
          ((u⁻¹ : U) • h : MF) =
            ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMFU h⟩ := by
        apply Subtype.ext
        simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
      calc
        (φU (u⁻¹) ⟨QuotientGroup.mk' H0MF h, hyQ⟩ : MF ⧸ H0MF) =
            (u⁻¹ : U) • QuotientGroup.mk' H0MF h := rfl
        _ = QuotientGroup.mk' H0MF ((u⁻¹ : U) • h) := hsmul_mk
        _ = QuotientGroup.mk' H0MF
              ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMFU h⟩ := by
            rw [hsmul_eq]
        _ = QuotientGroup.mk' H0MF
              ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩ := by
            apply congrArg (QuotientGroup.mk' H0MF)
            apply Subtype.ext
            rfl
        _ = action (QuotientGroup.mk' H0MF h) := (haction h).symm
        _ = QuotientGroup.mk' H0MF h := hfix (QuotientGroup.mk' H0MF h) hyQ

private theorem
    theorem_9_7_quotientFactorActions_of_prime_card_ordered_components_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 U W1 C : Subgroup G}
    {p q : ℕ}
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hW1normU : Subgroup.Normalizes W1 U]
    (hpprime : Nat.Prime p)
    (hqpos : 0 < q)
    (hnormalC : (C.subgroupOf U).Normal)
    (hC : quotientCentralizerIn MF H0 U C)
    (hbarComm :
      letI : (C.subgroupOf U).Normal := hnormalC
      IsMulCommutative (U ⧸ C.subgroupOf U))
    (hCinv : IsInvariant W1 U (C.subgroupOf U))
    (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G))
    (hH0invU :
      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
      IsInvariant U MF (H0.subgroupOf MF))
    (w0 : W1)
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hsucc :
      ∀ i : Fin q,
        quotientSubgroupConjugateByElement MF H0
          (H i) (H (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)) (w0 : G)) :
    ∃ a : ℕ, ∀ i, quotientFactorActionCentralizerData MF H0 U C (H i) a := by
  classical
  have hfacActions :
      ∀ i,
        ∃ ρ : (U ⧸ C.subgroupOf U) →* MulAut (H i),
          IsCyclic ρ.range ∧
            (∀ x : U ⧸ C.subgroupOf U,
              ∀ u : U,
                QuotientGroup.mk' (C.subgroupOf U) u = x →
                ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
                  ∀ h : MF,
                  ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H i,
                    (ρ x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                        MF ⧸ H0.subgroupOf MF) =
                      QuotientGroup.mk' (H0.subgroupOf MF)
                        ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩) ∧
            ∀ x : U ⧸ C.subgroupOf U,
              ρ x = 1 ↔
                ∀ u : U,
                  QuotientGroup.mk' (C.subgroupOf U) u = x →
                  quotientSubgroupCentralizedByElement MF H0 (H i) (u : G) := by
    intro i
    rcases
        theorem_9_7_quotientFactorActionCentralizerData_of_prime_card_normalized_sec9
          (MF := MF) (H0 := H0) (U := U) (C := C)
          hpprime hnormalC hC hbarComm hUnormMF hH0invU
          (H i) (hHnorm i) (hHcard i) with
      ⟨_a, _hnormal, ρ, hcyc, _hcard, haction, hker⟩
    exact ⟨ρ, hcyc, haction, hker⟩
  choose ρ hρ using hfacActions
  have hcyc : ∀ i, IsCyclic (ρ i).range := fun i => (hρ i).1
  have haction :
      ∀ i,
        ∀ x : U ⧸ C.subgroupOf U,
          ∀ u : U,
            QuotientGroup.mk' (C.subgroupOf U) u = x →
            ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
              ∀ h : MF,
              ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H i,
                (ρ i x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                    MF ⧸ H0.subgroupOf MF) =
                  QuotientGroup.mk' (H0.subgroupOf MF)
                    ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩ :=
    fun i => (hρ i).2.1
  have hker :
      ∀ i,
        ∀ x : U ⧸ C.subgroupOf U,
          ρ i x = 1 ↔
            ∀ u : U,
              QuotientGroup.mk' (C.subgroupOf U) u = x →
              quotientSubgroupCentralizedByElement MF H0 (H i) (u : G) :=
    fun i => (hρ i).2.2
  have htransport :
      ∀ i : Fin q,
        ∃ e : H i ≃* H (theorem_9_7_fin_cyclic_succ_sec9 hqpos i),
          theorem_9_7_successorTransportFactorAction_sec9 hnormalC hCinv w0 e
            (ρ i) =
            ρ (theorem_9_7_fin_cyclic_succ_sec9 hqpos i) := by
    intro i
    rcases theorem_9_7_successorTransportFactorAction_eq_of_action_field_sec9
        hnormalC hCinv w0 (hsucc i) (ρ := ρ i)
        (σ := ρ (theorem_9_7_fin_cyclic_succ_sec9 hqpos i))
        (haction i)
        (haction (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)) with
      ⟨e, _heData, he⟩
    exact ⟨e, he⟩
  choose e he using htransport
  let edge : ∀ i, (ρ i).range ≃*
      (ρ (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)).range :=
    fun i =>
      (theorem_9_7_successorTransportFactorAction_rangeEquiv_sec9
        hnormalC hCinv w0 (e i) (ρ i)).trans
        (MulEquiv.subgroupCongr (congrArg MonoidHom.range (he i)))
  let i0 : Fin q := ⟨0, hqpos⟩
  let a : ℕ := Nat.card (ρ i0).range
  have hcard : ∀ i, Nat.card (ρ i).range = a := by
    intro i
    exact
      Nat.card_congr
        ((theorem_9_7_successor_range_chain_lt_sec9 hqpos ρ edge i.1 i.2).symm.toEquiv)
  exact ⟨a, fun i => ⟨hnormalC, ρ i, hcyc i, hcard i, haction i, hker i⟩⟩

private theorem theorem_9_7_prime_card_of_zmod_submodule_finrank_one_sec9
    {V : Type u} [Group V] [Finite V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (Q : Subgroup V)
    (hQrank :
      let η : Subgroup V ≃o Submodule (ZMod p) (Additive V) :=
        Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule (n := p))
      Module.finrank (ZMod p) (η Q) = 1) :
    Nat.card Q = p := by
  classical
  let η : Subgroup V ≃o Submodule (ZMod p) (Additive V) :=
    Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule (n := p))
  have hcard_submodule (H : Subgroup V) : Nat.card (η H) = Nat.card H := by
    let eη : (η H) ≃ Subgroup.toAddSubgroup H := {
      toFun x := ⟨x.1, by
        have hx :
            x.1 ∈ AddSubgroup.toZModSubmodule (n := p) (Subgroup.toAddSubgroup H) :=
          x.property
        exact hx⟩
      invFun x := ⟨x.1, by
        have hx : x.1 ∈ Subgroup.toAddSubgroup H := x.property
        exact hx⟩
      left_inv x := by
        apply Subtype.ext
        rfl
      right_inv x := by
        apply Subtype.ext
        rfl }
    let eH : Subgroup.toAddSubgroup H ≃ H := {
      toFun x := ⟨Additive.toMul x.1, (Additive.mem_toAddSubgroup H x.1).1 x.property⟩
      invFun x := ⟨Additive.ofMul (x : V), (Additive.mem_toAddSubgroup H _).2 x.property⟩
      left_inv x := by
        apply Subtype.ext
        rfl
      right_inv x := by
        apply Subtype.ext
        rfl }
    exact (Nat.card_congr eη).trans (Nat.card_congr eH)
  have hnat : Nat.card (η Q) = p ^ Module.finrank (ZMod p) (η Q) := by
    simpa [ZMod.card] using Module.natCard_eq_pow_finrank (K := ZMod p) (V := η Q)
  rw [← hcard_submodule Q, hnat, hQrank, pow_one]

private theorem theorem_9_7_zmod_submodule_finrank_one_of_prime_card_sec9
    {V : Type u} [Group V] [Finite V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (Q : Subgroup V) (hQcard : Nat.card Q = p) :
    let η : Subgroup V ≃o Submodule (ZMod p) (Additive V) :=
      Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule (n := p))
    Module.finrank (ZMod p) (η Q) = 1 := by
  classical
  let η : Subgroup V ≃o Submodule (ZMod p) (Additive V) :=
    Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule (n := p))
  have hcard_submodule (H : Subgroup V) : Nat.card (η H) = Nat.card H := by
    let eη : (η H) ≃ Subgroup.toAddSubgroup H := {
      toFun x := ⟨x.1, by
        have hx :
            x.1 ∈ AddSubgroup.toZModSubmodule (n := p) (Subgroup.toAddSubgroup H) :=
          x.property
        exact hx⟩
      invFun x := ⟨x.1, by
        have hx : x.1 ∈ Subgroup.toAddSubgroup H := x.property
        exact hx⟩
      left_inv x := by
        apply Subtype.ext
        rfl
      right_inv x := by
        apply Subtype.ext
        rfl }
    let eH : Subgroup.toAddSubgroup H ≃ H := {
      toFun x := ⟨Additive.toMul x.1, (Additive.mem_toAddSubgroup H x.1).1 x.property⟩
      invFun x := ⟨Additive.ofMul (x : V), (Additive.mem_toAddSubgroup H _).2 x.property⟩
      left_inv x := by
        apply Subtype.ext
        rfl
      right_inv x := by
        apply Subtype.ext
        rfl }
    exact (Nat.card_congr eη).trans (Nat.card_congr eH)
  have hpow : p ^ Module.finrank (ZMod p) (η Q) = p := by
    calc
      p ^ Module.finrank (ZMod p) (η Q) = Nat.card (η Q) := by
        simpa [ZMod.card] using
          (Module.natCard_eq_pow_finrank (K := ZMod p) (V := η Q)).symm
      _ = Nat.card Q := hcard_submodule Q
      _ = p := hQcard
  exact ((Nat.Prime.pow_eq_iff (p := p) (a := p)
    (k := Module.finrank (ZMod p) (η Q)) Fact.out).mp hpow).2

private theorem theorem_9_7_base_finrank_one_of_iSupIndep_equal_card_span_sec9
    {V : Type u} [Group V] [Finite V]
    {p q : ℕ}
    (hpprime : Nat.Prime p)
    (hqprime : Nat.Prime q)
    (hVelem : IsElementaryAbelian p V)
    (hfinrank :
      letI : Fact p.Prime := ⟨hpprime⟩
      letI : IsElementaryAbelian p V := hVelem
      Module.finrank (ZMod p) (Additive V) = q)
    (Q : Subgroup V)
    (H : Fin q → Subgroup V)
    (hHcardEqQ : ∀ i, Nat.card (H i) = Nat.card Q)
    (hHsup : iSup H = ⊤)
    (hHindep : iSupIndep H) :
    letI : Fact p.Prime := ⟨hpprime⟩
    letI : IsElementaryAbelian p V := hVelem
    let η : Subgroup V ≃o Submodule (ZMod p) (Additive V) :=
      Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule (n := p))
    Module.finrank (ZMod p) (η Q) = 1 := by
  classical
  letI : Fact p.Prime := ⟨hpprime⟩
  letI : IsElementaryAbelian p V := hVelem
  have hQcard : Nat.card Q = p :=
    theorem_9_7_base_card_eq_prime_of_iSupIndep_equal_card_span_sec9
      hpprime hqprime hVelem hfinrank Q H hHcardEqQ hHsup hHindep
  exact theorem_9_7_zmod_submodule_finrank_one_of_prime_card_sec9
    (V := V) (p := p) Q hQcard

private theorem theorem_9_7_base_finrank_one_of_zmod_submodule_iSupIndep_equal_card_span_sec9
    {V : Type u} [Group V] [Finite V]
    {p q : ℕ}
    (hpprime : Nat.Prime p)
    (hqprime : Nat.Prime q)
    (hVelem : IsElementaryAbelian p V)
    (hfinrank :
      letI : Fact p.Prime := ⟨hpprime⟩
      letI : IsElementaryAbelian p V := hVelem
      Module.finrank (ZMod p) (Additive V) = q)
    (Q : Subgroup V)
    (H : Fin q → Subgroup V)
    (hHcardEqQ : ∀ i, Nat.card (H i) = Nat.card Q)
    (hHsup : iSup H = ⊤)
    (hHindepZ :
      letI : Fact p.Prime := ⟨hpprime⟩
      letI : IsElementaryAbelian p V := hVelem
      let η : Subgroup V ≃o Submodule (ZMod p) (Additive V) :=
        Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule (n := p))
      iSupIndep fun i => η (H i)) :
    letI : Fact p.Prime := ⟨hpprime⟩
    letI : IsElementaryAbelian p V := hVelem
    let η : Subgroup V ≃o Submodule (ZMod p) (Additive V) :=
      Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule (n := p))
    Module.finrank (ZMod p) (η Q) = 1 := by
  classical
  letI : Fact p.Prime := ⟨hpprime⟩
  letI : IsElementaryAbelian p V := hVelem
  let η : Subgroup V ≃o Submodule (ZMod p) (Additive V) :=
    Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule (n := p))
  have hHindep : iSupIndep H :=
    theorem_9_7_iSupIndep_of_zmod_submodule_iSupIndep_sec9
      (V := V) (p := p) H (by
        change iSupIndep fun i => η (H i)
        exact hHindepZ)
  exact theorem_9_7_base_finrank_one_of_iSupIndep_equal_card_span_sec9
    hpprime hqprime hVelem hfinrank Q H hHcardEqQ hHsup hHindep

private theorem theorem_9_7_finrank_one_of_prime_dimension_eq_sec9
    {q r : ℕ} (hqpos : 0 < q) (h : q = q * r) :
    r = 1 := by
  exact Nat.eq_of_mul_eq_mul_left hqpos (by simpa using h.symm)

private theorem theorem_9_7_base_card_eq_prime_of_clifford_dimension_sec9
    {V : Type u} [Group V] [Finite V]
    {p q : ℕ}
    (hpprime : Nat.Prime p)
    (hqprime : Nat.Prime q)
    (hVelem : IsElementaryAbelian p V)
    (Q : Subgroup V)
    (hdim :
      letI : Fact p.Prime := ⟨hpprime⟩
      letI : IsElementaryAbelian p V := hVelem
      let η : Subgroup V ≃o Submodule (ZMod p) (Additive V) :=
        Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule (n := p))
      q = q * Module.finrank (ZMod p) (η Q)) :
    Nat.card Q = p := by
  classical
  letI : Fact p.Prime := ⟨hpprime⟩
  letI : IsElementaryAbelian p V := hVelem
  let η : Subgroup V ≃o Submodule (ZMod p) (Additive V) :=
    Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule (n := p))
  have hQrank : Module.finrank (ZMod p) (η Q) = 1 :=
    theorem_9_7_finrank_one_of_prime_dimension_eq_sec9 hqprime.pos
      (by simpa [η] using hdim)
  exact
    theorem_9_7_prime_card_of_zmod_submodule_finrank_one_sec9
      (V := V) (p := p) Q hQrank

private theorem theorem_9_7_quotientSubgroupNormalizedBy_inf_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 A : Subgroup G}
    [hnormal : (H0.subgroupOf MF).Normal]
    {Q R : Subgroup (MF ⧸ H0.subgroupOf MF)}
    (hQnorm : quotientSubgroupNormalizedBy MF H0 A Q)
    (hRnorm : quotientSubgroupNormalizedBy MF H0 A R) :
    quotientSubgroupNormalizedBy MF H0 A (Q ⊓ R) := by
  classical
  intro a
  rcases hQnorm a with ⟨hconjMF, action, haction, hmapQ⟩
  rcases hRnorm a with ⟨hconjMF_R, action_R, haction_R, hmapR⟩
  refine ⟨hconjMF, action, haction, ?_⟩
  have haction_eq : action_R = action := by
    ext x
    rcases QuotientGroup.mk'_surjective (H0.subgroupOf MF) x with ⟨h, rfl⟩
    calc
      action_R (QuotientGroup.mk' (H0.subgroupOf MF) h) =
          QuotientGroup.mk' (H0.subgroupOf MF)
            ⟨(a : G)⁻¹ * (h : G) * (a : G), hconjMF_R h⟩ := haction_R h
      _ = QuotientGroup.mk' (H0.subgroupOf MF)
            ⟨(a : G)⁻¹ * (h : G) * (a : G), hconjMF h⟩ := by
            congr 1
      _ = action (QuotientGroup.mk' (H0.subgroupOf MF) h) := (haction h).symm
  have hmapQ' : Q.map action.toMonoidHom = Q := hmapQ.symm
  have hmapR' : R.map action.toMonoidHom = R := by
    simpa [haction_eq] using hmapR.symm
  have hmapInf :
      (Q ⊓ R).map action.toMonoidHom = Q ⊓ R := by
    rw [Subgroup.map_inf, hmapQ', hmapR']
    exact action.injective
  exact hmapInf.symm

private theorem theorem_9_7_minimal_of_ordered_generator_orbit_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 U W1 : Subgroup G}
    [Subgroup.Normalizes U MF] [Subgroup.Normalizes W1 MF]
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [Subgroup.Normalizes W1 U]
    (hH0invU : IsInvariant U MF (H0.subgroupOf MF))
    (hH0invW1 : IsInvariant W1 MF (H0.subgroupOf MF))
    {q : ℕ} (hqpos : 0 < q)
    (w0 : W1)
    {Q : Subgroup (MF ⧸ H0.subgroupOf MF)}
    (hQminimal :
      ∀ R : Subgroup (MF ⧸ H0.subgroupOf MF),
        quotientSubgroupNormalizedBy MF H0 U R →
          R ≠ ⊥ → R ≤ Q → Q ≤ R)
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHzero_eq_Q : H ⟨0, hqpos⟩ = Q)
    (hsucc :
      ∀ i : Fin q,
        quotientSubgroupConjugateByElement MF H0
          (H i) (H (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)) (w0 : G)) :
    ∀ i : Fin q, ∀ R : Subgroup (MF ⧸ H0.subgroupOf MF),
      quotientSubgroupNormalizedBy MF H0 U R →
        R ≠ ⊥ → R ≤ H i → H i ≤ R := by
  classical
  have horbit :=
    theorem_9_7_weak_orbit_of_successor_conjugates_sec9
      (MF := MF) (H0 := H0) (W1 := W1) hqpos H w0 hsucc
  intro i
  rcases horbit i with ⟨w, hconj⟩
  exact
    theorem_9_7_minimal_of_W1_conjugate_minimal_sec9
      (MF := MF) (H0 := H0) (U := U) (W1 := W1)
      hH0invU hH0invW1 hQminimal w
      (by simpa [hHzero_eq_Q] using hconj)

private theorem theorem_9_7_disjoint_of_ne_of_minimal_normalized_equal_card_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 U : Subgroup G}
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    {Q R : Subgroup (MF ⧸ H0.subgroupOf MF)}
    (hQminimal :
      ∀ T : Subgroup (MF ⧸ H0.subgroupOf MF),
        quotientSubgroupNormalizedBy MF H0 U T →
          T ≠ ⊥ → T ≤ Q → Q ≤ T)
    (hQnorm : quotientSubgroupNormalizedBy MF H0 U Q)
    (hRnorm : quotientSubgroupNormalizedBy MF H0 U R)
    (hcard : Nat.card Q = Nat.card R)
    (hne : Q ≠ R) :
    Disjoint Q R := by
  classical
  rw [disjoint_iff]
  apply le_bot_iff.mp
  intro x hx
  by_cases hInfBot : Q ⊓ R = ⊥
  · simpa [hInfBot] using hx
  · have hInfNorm :
        quotientSubgroupNormalizedBy MF H0 U (Q ⊓ R) :=
      theorem_9_7_quotientSubgroupNormalizedBy_inf_sec9 hQnorm hRnorm
    have hQleInf : Q ≤ Q ⊓ R :=
      hQminimal (Q ⊓ R) hInfNorm hInfBot inf_le_left
    have hQleR : Q ≤ R := le_trans hQleInf inf_le_right
    have hEq : Q = R :=
      Subgroup.eq_of_le_of_card_ge hQleR (by rw [← hcard])
    exact False.elim (hne hEq)

private theorem theorem_9_7_pairwise_disjoint_of_minimal_generator_orbit_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 U W1 : Subgroup G}
    [Subgroup.Normalizes U MF] [Subgroup.Normalizes W1 MF]
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [Subgroup.Normalizes W1 U]
    (hH0invU : IsInvariant U MF (H0.subgroupOf MF))
    (hH0invW1 : IsInvariant W1 MF (H0.subgroupOf MF))
    {q : ℕ}
    (hqprime : Nat.Prime q)
    (hW1card : Nat.card W1 = q)
    (w0 : W1)
    (hw0gen : Subgroup.zpowers w0 = ⊤)
    {Q : Subgroup (MF ⧸ H0.subgroupOf MF)}
    (hQminimal :
      ∀ R : Subgroup (MF ⧸ H0.subgroupOf MF),
        quotientSubgroupNormalizedBy MF H0 U R →
          R ≠ ⊥ → R ≤ Q → Q ≤ R)
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHzero_eq_Q : H ⟨0, hqprime.pos⟩ = Q)
    (hH0notW1 :
      ¬ quotientSubgroupNormalizedBy MF H0 W1 (H ⟨0, hqprime.pos⟩))
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHcardEqQ : ∀ i, Nat.card (H i) = Nat.card Q)
    (hsucc :
      ∀ i : Fin q,
        quotientSubgroupConjugateByElement MF H0
          (H i) (H (theorem_9_7_fin_cyclic_succ_sec9 hqprime.pos i)) (w0 : G)) :
    ∀ ⦃i j : Fin q⦄, i ≠ j → Disjoint (H i) (H j) := by
  have hinj :=
    theorem_9_7_generator_orbit_injective_of_base_not_normalized_sec9
      hqprime hW1card w0 hw0gen H hsucc hH0notW1
  have hminimal :=
    theorem_9_7_minimal_of_ordered_generator_orbit_sec9
      hH0invU hH0invW1 hqprime.pos w0 hQminimal H hHzero_eq_Q hsucc
  intro i j hij
  have hne : H i ≠ H j := by
    intro hHij
    exact hij (hinj hHij)
  have hcard : Nat.card (H i) = Nat.card (H j) := by
    rw [hHcardEqQ i, hHcardEqQ j]
  exact
    theorem_9_7_disjoint_of_ne_of_minimal_normalized_equal_card_sec9
      (hminimal i) (hHnorm i) (hHnorm j) hcard hne

private theorem theorem_9_7_iSupIndep_fin_two_of_pairwise_disjoint_sec9
    {α : Type u} [CompleteLattice α] {f : Fin 2 → α}
    (hpair : ∀ ⦃i j : Fin 2⦄, i ≠ j → Disjoint (f i) (f j)) :
    iSupIndep f := by
  rw [iSupIndep_def]
  intro i
  fin_cases i
  · change Disjoint (f (0 : Fin 2)) (⨆ j, ⨆ (_ : j ≠ (0 : Fin 2)), f j)
    have hsup : (⨆ j, ⨆ (_ : j ≠ (0 : Fin 2)), f j) = f 1 := by
      apply le_antisymm
      · refine iSup_le ?_
        intro j
        refine iSup_le ?_
        intro hj
        fin_cases j
        · exact False.elim (hj rfl)
        · exact le_rfl
      · exact le_iSup_of_le (1 : Fin 2)
          (le_iSup_of_le (by decide : (1 : Fin 2) ≠ 0) le_rfl)
    rw [hsup]
    exact hpair (i := 0) (j := 1) (by decide)
  · change Disjoint (f (1 : Fin 2)) (⨆ j, ⨆ (_ : j ≠ (1 : Fin 2)), f j)
    have hsup : (⨆ j, ⨆ (_ : j ≠ (1 : Fin 2)), f j) = f 0 := by
      apply le_antisymm
      · refine iSup_le ?_
        intro j
        refine iSup_le ?_
        intro hj
        fin_cases j
        · exact le_rfl
        · exact False.elim (hj rfl)
      · exact le_iSup_of_le (0 : Fin 2)
          (le_iSup_of_le (by decide : (0 : Fin 2) ≠ 1) le_rfl)
    rw [hsup]
    exact disjoint_comm.mp (hpair (i := 0) (j := 1) (by decide))

private theorem theorem_9_7_iSupIndep_of_pairwise_disjoint_card_two_sec9
    {α : Type u} [CompleteLattice α] {q : ℕ}
    (H : Fin q → α)
    (hq2 : q = 2)
    (hpair : ∀ ⦃i j : Fin q⦄, i ≠ j → Disjoint (H i) (H j)) :
    iSupIndep H := by
  subst q
  exact theorem_9_7_iSupIndep_fin_two_of_pairwise_disjoint_sec9 hpair

private theorem
    theorem_9_7_base_card_eq_prime_of_pairwise_disjoint_card_two_span_sec9
    {V : Type u} [Group V] [Finite V]
    {p q : ℕ}
    (hpprime : Nat.Prime p)
    (hqprime : Nat.Prime q)
    (hVelem : IsElementaryAbelian p V)
    (hfinrank :
      letI : Fact p.Prime := ⟨hpprime⟩
      letI : IsElementaryAbelian p V := hVelem
      Module.finrank (ZMod p) (Additive V) = q)
    (Q : Subgroup V)
    (H : Fin q → Subgroup V)
    (hHcardEqQ : ∀ i, Nat.card (H i) = Nat.card Q)
    (hHsup : iSup H = ⊤)
    (hq2 : q = 2)
    (hpair : ∀ ⦃i j : Fin q⦄, i ≠ j → Disjoint (H i) (H j)) :
    Nat.card Q = p := by
  have hHindep :
      iSupIndep H :=
    theorem_9_7_iSupIndep_of_pairwise_disjoint_card_two_sec9 H hq2 hpair
  exact
    theorem_9_7_base_card_eq_prime_of_iSupIndep_equal_card_span_sec9
      hpprime hqprime hVelem hfinrank Q H hHcardEqQ hHsup hHindep

private theorem theorem_9_7_toSubmodule_finset_sup_sec9
    {F A V : Type*} [Field F] [Group A] [AddCommGroup V] [Module F V]
    (ρ : Representation F A V)
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (S : ι → Subrepresentation ρ) :
    ∀ s : Finset ι, (s.sup S : Subrepresentation ρ).toSubmodule =
      (s.sup (fun i => (S i).toSubmodule) : Submodule F V) := by
  classical
  intro s
  refine Finset.induction_on s ?_ ?_
  · rfl
  · intro i s his ih
    simp [Finset.sup_insert, ih]

private theorem theorem_9_7_finrank_dvd_finrank_finsetSup_irreducible_equal_dim_sec9
    {F A V : Type*} [Field F] [Group A] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V]
    (ρ : Representation F A V)
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (S : ι → Subrepresentation ρ) (i0 : ι)
    (hSirr : ∀ i, Representation.IsIrreducible (S i).toRepresentation)
    (hSdim : ∀ i, Module.finrank F (S i).toSubmodule =
      Module.finrank F (S i0).toSubmodule) :
    ∀ s : Finset ι,
      Module.finrank F (S i0).toSubmodule ∣
        Module.finrank F
          (s.sup (fun i => (S i).toSubmodule) : Submodule F V) := by
  classical
  let d : ℕ := Module.finrank F (S i0).toSubmodule
  intro s
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sup_empty, finrank_bot]
    exact dvd_zero (Module.finrank F (S i0).toSubmodule)
  · intro i s his ih
    let T : Subrepresentation ρ := s.sup S
    have hTsub :
        T.toSubmodule =
          (s.sup (fun j => (S j).toSubmodule) : Submodule F V) :=
      theorem_9_7_toSubmodule_finset_sup_sec9 ρ S s
    have hInf :
        Module.finrank F
            ((S i).toSubmodule ⊓ T.toSubmodule : Submodule F V) = 0 ∨
          Module.finrank F
            ((S i).toSubmodule ⊓ T.toSubmodule : Submodule F V) = d := by
      by_cases hbot :
          ((S i).toSubmodule ⊓ T.toSubmodule : Submodule F V) = ⊥
      · left
        simp [hbot]
      · right
        rcases
          ((S i).toSubmodule ⊓ T.toSubmodule : Submodule F V).ne_bot_iff.mp hbot with
          ⟨v, hv, hv0⟩
        rcases Submodule.mem_inf.mp hv with ⟨hvS, hvT⟩
        haveI : Representation.IsIrreducible (S i).toRepresentation := hSirr i
        have hleT : S i ≤ T :=
          theorem_9_7_subrepresentation_le_of_nonzero_mem_sec9
            (S := S i) (T := T) hvS hvT hv0
        have hsub :
            ((S i).toSubmodule ⊓ T.toSubmodule : Submodule F V) =
              (S i).toSubmodule := by
          apply le_antisymm
          · exact inf_le_left
          · intro x hx
            exact Submodule.mem_inf.mpr ⟨hx, hleT hx⟩
        change
          Module.finrank F
              ((S i).toSubmodule ⊓ T.toSubmodule : Submodule F V) =
            Module.finrank F (S i0).toSubmodule
        rw [hsub, hSdim i]
    have hsup :
        ((insert i s).sup (fun j => (S j).toSubmodule) : Submodule F V) =
          (S i).toSubmodule ⊔
            (s.sup (fun j => (S j).toSubmodule) : Submodule F V) := by
      simp [Finset.sup_insert]
    have hdim_sup :
        Module.finrank F
            ((insert i s).sup (fun j => (S j).toSubmodule) : Submodule F V) +
            Module.finrank F
              ((S i).toSubmodule ⊓ T.toSubmodule : Submodule F V) =
      d + Module.finrank F
            (s.sup (fun j => (S j).toSubmodule) : Submodule F V) := by
      rw [hsup, ← hTsub, Submodule.finrank_sup_add_finrank_inf_eq]
      dsimp [d]
      rw [hSdim i]
    rcases ih with ⟨m, hm⟩
    rcases hInf with hInf0 | hInfd
    · refine ⟨m + 1, ?_⟩
      calc
        Module.finrank F
              ((insert i s).sup (fun j => (S j).toSubmodule) : Submodule F V)
            = d + Module.finrank F
              (s.sup (fun j => (S j).toSubmodule) : Submodule F V) := by
              simpa [hInf0] using hdim_sup
        _ = d + d * m := by rw [hm]
        _ = d * (m + 1) := by ring
    · refine ⟨m, ?_⟩
      have hcancel :
          Module.finrank F
              ((insert i s).sup (fun j => (S j).toSubmodule) : Submodule F V) + d =
            d * m + d := by
        calc
        Module.finrank F
              ((insert i s).sup (fun j => (S j).toSubmodule) : Submodule F V) + d
            = d + Module.finrank F
              (s.sup (fun j => (S j).toSubmodule) : Submodule F V) := by
              simpa [hInfd, add_comm, add_left_comm, add_assoc] using hdim_sup
        _ = d + d * m := by
              dsimp [d]
              rw [hm]
        _ = d * m + d := by ac_rfl
      exact Nat.add_right_cancel hcancel

private theorem theorem_9_7_finrank_dvd_finrank_iSup_irreducible_equal_dim_sec9
    {F A V : Type*} [Field F] [Group A] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V]
    (ρ : Representation F A V)
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (S : ι → Subrepresentation ρ) (i0 : ι)
    (hSirr : ∀ i, Representation.IsIrreducible (S i).toRepresentation)
    (hSdim : ∀ i, Module.finrank F (S i).toSubmodule =
      Module.finrank F (S i0).toSubmodule) :
    Module.finrank F (S i0).toSubmodule ∣
      Module.finrank F (⨆ i, (S i).toSubmodule : Submodule F V) := by
  classical
  have hfin :=
    theorem_9_7_finrank_dvd_finrank_finsetSup_irreducible_equal_dim_sec9
      ρ S i0 hSirr hSdim Finset.univ
  have hsup :
      (Finset.univ.sup (fun i => (S i).toSubmodule) :
          Submodule F V) =
        (⨆ i, (S i).toSubmodule : Submodule F V) :=
    Finset.sup_univ_eq_iSup fun i => (S i).toSubmodule
  rw [← hsup]
  exact hfin

private theorem
    theorem_9_7_clifford_zmod_submodule_iSupIndep_of_minimal_generator_orbit_ne_two_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {MF H0 U W1 : Subgroup G}
    (p q : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hW1normU : Subgroup.Normalizes W1 U]
    (hpprime : Nat.Prime p)
    (hqprime : Nat.Prime q)
    (hbarElem : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF))
    (hbarFinrank :
      letI : Fact p.Prime := ⟨hpprime⟩
      letI : (H0.subgroupOf MF).Normal := hnormalH0
      letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
      Module.finrank (ZMod p) (Additive (MF ⧸ H0.subgroupOf MF)) = q)
    (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G))
    (hH0invU :
      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
      IsInvariant U MF (H0.subgroupOf MF))
    (hW1normMF : W1 ≤ Subgroup.normalizer (MF : Set G))
    (hH0invW1 :
      letI : Subgroup.Normalizes W1 MF := ⟨hW1normMF⟩
      IsInvariant W1 MF (H0.subgroupOf MF))
    (w0 : W1)
    (_hW1card : Nat.card W1 = q)
    (_hw0gen : Subgroup.zpowers w0 = ⊤)
    (_hUW1minimal :
      ∀ R : Subgroup (MF ⧸ H0.subgroupOf MF),
        quotientSubgroupNormalizedBy MF H0 U R →
          quotientSubgroupNormalizedBy MF H0 W1 R →
            R = ⊥ ∨ R = ⊤)
    (Q : Subgroup (MF ⧸ H0.subgroupOf MF))
    (_hQnorm : quotientSubgroupNormalizedBy MF H0 U Q)
    (_hQneBot : Q ≠ ⊥)
    (_hQneTop : Q ≠ ⊤)
    (hQminimal :
      ∀ R : Subgroup (MF ⧸ H0.subgroupOf MF),
        quotientSubgroupNormalizedBy MF H0 U R →
          R ≠ ⊥ → R ≤ Q → Q ≤ R)
    (_hQnotW1 : ¬ quotientSubgroupNormalizedBy MF H0 W1 Q)
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHzero_eq_Q : H ⟨0, hqprime.pos⟩ = Q)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHneBot : ∀ i, H i ≠ ⊥)
    (hHneTop : ∀ i, H i ≠ ⊤)
    (_hHnotW1 : ∀ i, ¬ quotientSubgroupNormalizedBy MF H0 W1 (H i))
    (hHcardEqQ : ∀ i, Nat.card (H i) = Nat.card Q)
    (hHsup : iSup H = ⊤)
    (hsucc :
      ∀ i : Fin q,
        quotientSubgroupConjugateByElement MF H0
          (H i) (H (theorem_9_7_fin_cyclic_succ_sec9 hqprime.pos i)) (w0 : G))
    (_hHsucc_ne :
      ∀ i : Fin q, H (theorem_9_7_fin_cyclic_succ_sec9 hqprime.pos i) ≠ H i)
    (_hqne_two : q ≠ 2) :
    letI : Fact p.Prime := ⟨hpprime⟩
    letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
    let η : Subgroup (MF ⧸ H0.subgroupOf MF) ≃o
        Submodule (ZMod p) (Additive (MF ⧸ H0.subgroupOf MF)) :=
      Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule (n := p))
    iSupIndep fun i => η (H i) := by
  classical
  letI : Fact p.Prime := ⟨hpprime⟩
  letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
  letI : Subgroup.Normalizes W1 MF := ⟨hW1normMF⟩
  letI : MulAction.QuotientAction U (H0.subgroupOf MF) :=
    quotientAction_of_isInvariant (A := U) (G := MF)
      (H0.subgroupOf MF) hH0invU
  letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
    quotientMulDistribMulAction (A := U) (G := MF)
      (H0.subgroupOf MF) hH0invU
  letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
  let ρ : Representation (ZMod p) U (Additive (MF ⧸ H0.subgroupOf MF)) :=
    Theory.Representation.ofElementaryAbelianAction
      (A := U) (G := MF ⧸ H0.subgroupOf MF) (p := p)
  let η : Subgroup (MF ⧸ H0.subgroupOf MF) ≃o
      Submodule (ZMod p) (Additive (MF ⧸ H0.subgroupOf MF)) :=
    Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule (n := p))
  let i0 : Fin q := ⟨0, hqprime.pos⟩
  have hSexists : ∀ i, ∃ S : Subrepresentation ρ, S.toSubmodule = η (H i) := by
    intro i
    simpa [ρ, η] using
      theorem_9_7_subrepresentation_of_quotientSubgroupNormalizedBy_sec9
        (MF := MF) (H0 := H0) (U := U) (p := p)
        hbarElem hUnormMF hH0invU (H i) (hHnorm i)
  choose S hS using hSexists
  have hminimal :
      ∀ i : Fin q, ∀ R : Subgroup (MF ⧸ H0.subgroupOf MF),
        quotientSubgroupNormalizedBy MF H0 U R →
          R ≠ ⊥ → R ≤ H i → H i ≤ R :=
    theorem_9_7_minimal_of_ordered_generator_orbit_sec9
      hH0invU hH0invW1 hqprime.pos w0 hQminimal H hHzero_eq_Q hsucc
  have hminimalInv :
      ∀ i : Fin q, ∀ R : Subgroup (MF ⧸ H0.subgroupOf MF),
        IsInvariant U (MF ⧸ H0.subgroupOf MF) R →
          R ≠ ⊥ → R ≤ H i → H i ≤ R := by
    intro i R hRinv hRne hRle
    have hRnorm : quotientSubgroupNormalizedBy MF H0 U R := by
      simpa using
        quotientSubgroupNormalizedBy_of_isInvariant_sec9
          MF H0 U hH0invU R hRinv
    exact hminimal i R hRnorm hRne hRle
  have hSirr : ∀ i, Representation.IsIrreducible (S i).toRepresentation := by
    intro i
    exact
      theorem_9_7_irreducible_subrepresentation_of_minimal_invariant_subgroup_sec9
        (A := U) (V := MF ⧸ H0.subgroupOf MF) (p := p)
        (H i) (hHneBot i) (hminimalInv i) (S i)
        (by simpa [ρ, η] using hS i)
  have hcard_submodule :
      ∀ K : Subgroup (MF ⧸ H0.subgroupOf MF), Nat.card (η K) = Nat.card K := by
    intro K
    let eη : (η K) ≃ Subgroup.toAddSubgroup K := {
      toFun x := ⟨x.1, by
        have hx :
            x.1 ∈ AddSubgroup.toZModSubmodule (n := p) (Subgroup.toAddSubgroup K) :=
          x.property
        exact hx⟩
      invFun x := ⟨x.1, by
        have hx : x.1 ∈ Subgroup.toAddSubgroup K := x.property
        exact hx⟩
      left_inv x := by
        apply Subtype.ext
        rfl
      right_inv x := by
        apply Subtype.ext
        rfl }
    let eK : Subgroup.toAddSubgroup K ≃ K := {
      toFun x := ⟨Additive.toMul x.1, (Additive.mem_toAddSubgroup K x.1).1 x.property⟩
      invFun x := ⟨Additive.ofMul (x : MF ⧸ H0.subgroupOf MF),
        (Additive.mem_toAddSubgroup K _).2 x.property⟩
      left_inv x := by
        apply Subtype.ext
        rfl
      right_inv x := by
        apply Subtype.ext
        rfl }
    exact (Nat.card_congr eη).trans (Nat.card_congr eK)
  have hSdim :
      ∀ i, Module.finrank (ZMod p) (S i).toSubmodule =
        Module.finrank (ZMod p) (S i0).toSubmodule := by
    intro i
    have hnat_i :
        Nat.card (S i).toSubmodule =
          p ^ Module.finrank (ZMod p) (S i).toSubmodule := by
      simpa [ZMod.card] using
        Module.natCard_eq_pow_finrank (K := ZMod p) (V := (S i).toSubmodule)
    have hnat_0 :
        Nat.card (S i0).toSubmodule =
          p ^ Module.finrank (ZMod p) (S i0).toSubmodule := by
      simpa [ZMod.card] using
        Module.natCard_eq_pow_finrank (K := ZMod p) (V := (S i0).toSubmodule)
    have hcardS_i : Nat.card (S i).toSubmodule = Nat.card (H i) := by
      rw [hS i]
      exact hcard_submodule (H i)
    have hcardS_0 : Nat.card (S i0).toSubmodule = Nat.card (H i0) := by
      rw [hS i0]
      exact hcard_submodule (H i0)
    have hHcard_i0 : Nat.card (H i) = Nat.card (H i0) := by
      rw [hHcardEqQ i, hHzero_eq_Q]
    apply Nat.pow_right_injective hpprime.two_le
    calc
      p ^ Module.finrank (ZMod p) (S i).toSubmodule =
          Nat.card (S i).toSubmodule := hnat_i.symm
      _ = Nat.card (H i) := hcardS_i
      _ = Nat.card (H i0) := hHcard_i0
      _ = Nat.card (S i0).toSubmodule := hcardS_0.symm
      _ = p ^ Module.finrank (ZMod p) (S i0).toSubmodule := hnat_0
  have hdvd :
      Module.finrank (ZMod p) (S i0).toSubmodule ∣ q := by
    have hdvd_total :=
      theorem_9_7_finrank_dvd_finrank_iSup_irreducible_equal_dim_sec9
        ρ S i0 hSirr hSdim
    have hsupZ :
        (⨆ i, (S i).toSubmodule :
            Submodule (ZMod p) (Additive (MF ⧸ H0.subgroupOf MF))) = ⊤ := by
      calc
        (⨆ i, (S i).toSubmodule :
            Submodule (ZMod p) (Additive (MF ⧸ H0.subgroupOf MF))) =
            ⨆ i, η (H i) := by
              apply le_antisymm
              · refine iSup_le ?_
                intro i
                rw [hS i]
                exact le_iSup (fun i => η (H i)) i
              · refine iSup_le ?_
                intro i
                rw [← hS i]
                exact le_iSup (fun i => (S i).toSubmodule) i
        _ = η (iSup H) := (η.map_iSup H).symm
        _ = η ⊤ := by rw [hHsup]
        _ = ⊤ := by simp [η]
    have htotal :
        Module.finrank (ZMod p)
            (⨆ i, (S i).toSubmodule :
              Submodule (ZMod p) (Additive (MF ⧸ H0.subgroupOf MF))) = q := by
      rw [hsupZ]
      simpa using hbarFinrank
    simpa [htotal] using hdvd_total
  have hQrank : Module.finrank (ZMod p) (η Q) = 1 := by
    let d : ℕ := Module.finrank (ZMod p) (S i0).toSubmodule
    have hdvd' : d ∣ q := by simpa [d] using hdvd
    rcases hqprime.eq_one_or_self_of_dvd d hdvd' with hd_one | hd_q
    · have hS0 : (S i0).toSubmodule = η Q := by
        simpa [i0, hHzero_eq_Q, η] using hS i0
      rw [← hS0]
      simpa [d] using hd_one
    · exfalso
      have hS0top : (S i0).toSubmodule = ⊤ := by
        apply Submodule.eq_top_of_finrank_eq
        change d = Module.finrank (ZMod p) (Additive (MF ⧸ H0.subgroupOf MF))
        rw [hd_q, hbarFinrank]
      have hH0top : H i0 = ⊤ := by
        have hηtop : η (H i0) = ⊤ := by
          rw [← hS i0, hS0top]
        have hηtop' : η (H i0) = η ⊤ := by
          simpa [η] using hηtop
        exact η.injective hηtop'
      exact hHneTop i0 hH0top
  have hQcard : Nat.card Q = p :=
    theorem_9_7_prime_card_of_zmod_submodule_finrank_one_sec9
      (V := MF ⧸ H0.subgroupOf MF) (p := p) Q (by simpa [η] using hQrank)
  have hHindep : iSupIndep H :=
    theorem_9_7_iSupIndep_of_equal_prime_card_span_sec9
      hpprime hbarElem hbarFinrank Q H hQcard hHcardEqQ hHsup
  change iSupIndep
    ((Subgroup.toAddSubgroup.trans
      (AddSubgroup.toZModSubmodule
        (M := Additive (MF ⧸ H0.subgroupOf MF)) (n := p))) ∘ H)
  exact theorem_9_7_zmod_submodule_iSupIndep_of_iSupIndep_sec9
    (V := MF ⧸ H0.subgroupOf MF) (p := p) H hHindep

private theorem
    theorem_9_7_clifford_dimension_eq_of_minimal_generator_orbit_ne_two_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {MF H0 U W1 : Subgroup G}
    (p q : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hW1normU : Subgroup.Normalizes W1 U]
    (hpprime : Nat.Prime p)
    (hqprime : Nat.Prime q)
    (hbarElem : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF))
    (hbarFinrank :
      letI : Fact p.Prime := ⟨hpprime⟩
      letI : (H0.subgroupOf MF).Normal := hnormalH0
      letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
      Module.finrank (ZMod p) (Additive (MF ⧸ H0.subgroupOf MF)) = q)
    (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G))
    (hH0invU :
      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
      IsInvariant U MF (H0.subgroupOf MF))
    (hW1normMF : W1 ≤ Subgroup.normalizer (MF : Set G))
    (hH0invW1 :
      letI : Subgroup.Normalizes W1 MF := ⟨hW1normMF⟩
      IsInvariant W1 MF (H0.subgroupOf MF))
    (w0 : W1)
    (hW1card : Nat.card W1 = q)
    (hw0gen : Subgroup.zpowers w0 = ⊤)
    (hUW1minimal :
      ∀ R : Subgroup (MF ⧸ H0.subgroupOf MF),
        quotientSubgroupNormalizedBy MF H0 U R →
          quotientSubgroupNormalizedBy MF H0 W1 R →
            R = ⊥ ∨ R = ⊤)
    (Q : Subgroup (MF ⧸ H0.subgroupOf MF))
    (hQnorm : quotientSubgroupNormalizedBy MF H0 U Q)
    (hQneBot : Q ≠ ⊥)
    (hQneTop : Q ≠ ⊤)
    (hQminimal :
      ∀ R : Subgroup (MF ⧸ H0.subgroupOf MF),
        quotientSubgroupNormalizedBy MF H0 U R →
          R ≠ ⊥ → R ≤ Q → Q ≤ R)
    (hQnotW1 : ¬ quotientSubgroupNormalizedBy MF H0 W1 Q)
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHzero_eq_Q : H ⟨0, hqprime.pos⟩ = Q)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHneBot : ∀ i, H i ≠ ⊥)
    (hHneTop : ∀ i, H i ≠ ⊤)
    (hHnotW1 : ∀ i, ¬ quotientSubgroupNormalizedBy MF H0 W1 (H i))
    (hHcardEqQ : ∀ i, Nat.card (H i) = Nat.card Q)
    (hHsup : iSup H = ⊤)
    (hsucc :
      ∀ i : Fin q,
        quotientSubgroupConjugateByElement MF H0
          (H i) (H (theorem_9_7_fin_cyclic_succ_sec9 hqprime.pos i)) (w0 : G))
    (hHsucc_ne :
      ∀ i : Fin q, H (theorem_9_7_fin_cyclic_succ_sec9 hqprime.pos i) ≠ H i)
    (_hqne_two : q ≠ 2) :
    letI : Fact p.Prime := ⟨hpprime⟩
    letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
    let η : Subgroup (MF ⧸ H0.subgroupOf MF) ≃o
        Submodule (ZMod p) (Additive (MF ⧸ H0.subgroupOf MF)) :=
      Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule (n := p))
    q = q * Module.finrank (ZMod p) (η Q) := by
  classical
  letI : Fact p.Prime := ⟨hpprime⟩
  letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
  let η : Subgroup (MF ⧸ H0.subgroupOf MF) ≃o
      Submodule (ZMod p) (Additive (MF ⧸ H0.subgroupOf MF)) :=
    Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule (n := p))
  have hHindepZ : iSupIndep fun i => η (H i) := by
    simpa [η] using
      theorem_9_7_clifford_zmod_submodule_iSupIndep_of_minimal_generator_orbit_ne_two_source_bridge_sec9
        (MF := MF) (H0 := H0) (U := U) (W1 := W1)
        p q hpprime hqprime hbarElem hbarFinrank hUnormMF hH0invU
        hW1normMF hH0invW1 w0 hW1card hw0gen hUW1minimal Q hQnorm
        hQneBot hQneTop hQminimal hQnotW1 H hHzero_eq_Q hHnorm hHneBot hHneTop
        hHnotW1 hHcardEqQ hHsup hsucc hHsucc_ne _hqne_two
  have hQrank : Module.finrank (ZMod p) (η Q) = 1 :=
    theorem_9_7_base_finrank_one_of_zmod_submodule_iSupIndep_equal_card_span_sec9
      hpprime hqprime hbarElem hbarFinrank Q H hHcardEqQ hHsup
      (by simpa [η] using hHindepZ)
  change q = q * Module.finrank (ZMod p) (η Q)
  rw [hQrank, Nat.mul_one]


private theorem
    theorem_9_7_base_card_eq_prime_of_minimal_generator_orbit_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {MF H0 U W1 _C : Subgroup G}
    (p q : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hW1normU : Subgroup.Normalizes W1 U]
    (hpprime : Nat.Prime p)
    (hqprime : Nat.Prime q)
    (hbarElem : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF))
    (hbarFinrank :
      letI : Fact p.Prime := ⟨hpprime⟩
      letI : (H0.subgroupOf MF).Normal := hnormalH0
      letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
      Module.finrank (ZMod p) (Additive (MF ⧸ H0.subgroupOf MF)) = q)
    (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G))
    (hH0invU :
      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
      IsInvariant U MF (H0.subgroupOf MF))
    (hW1normMF : W1 ≤ Subgroup.normalizer (MF : Set G))
    (hH0invW1 :
      letI : Subgroup.Normalizes W1 MF := ⟨hW1normMF⟩
      IsInvariant W1 MF (H0.subgroupOf MF))
    (w0 : W1)
    (hW1card : Nat.card W1 = q)
    (hw0gen : Subgroup.zpowers w0 = ⊤)
    (hUW1minimal :
      ∀ R : Subgroup (MF ⧸ H0.subgroupOf MF),
        quotientSubgroupNormalizedBy MF H0 U R →
          quotientSubgroupNormalizedBy MF H0 W1 R →
            R = ⊥ ∨ R = ⊤)
    (Q : Subgroup (MF ⧸ H0.subgroupOf MF))
    (hQnorm : quotientSubgroupNormalizedBy MF H0 U Q)
    (hQneBot : Q ≠ ⊥)
    (hQneTop : Q ≠ ⊤)
    (hQminimal :
      ∀ R : Subgroup (MF ⧸ H0.subgroupOf MF),
        quotientSubgroupNormalizedBy MF H0 U R →
          R ≠ ⊥ → R ≤ Q → Q ≤ R)
    (hQnotW1 : ¬ quotientSubgroupNormalizedBy MF H0 W1 Q)
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHzero_eq_Q : H ⟨0, hqprime.pos⟩ = Q)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHneBot : ∀ i, H i ≠ ⊥)
    (hHneTop : ∀ i, H i ≠ ⊤)
    (hHnotW1 : ∀ i, ¬ quotientSubgroupNormalizedBy MF H0 W1 (H i))
    (hHcardEqQ : ∀ i, Nat.card (H i) = Nat.card Q)
    (hHsup : iSup H = ⊤)
    (hsucc :
      ∀ i : Fin q,
        quotientSubgroupConjugateByElement MF H0
          (H i) (H (theorem_9_7_fin_cyclic_succ_sec9 hqprime.pos i)) (w0 : G))
    (hHsucc_ne :
      ∀ i : Fin q, H (theorem_9_7_fin_cyclic_succ_sec9 hqprime.pos i) ≠ H i) :
    Nat.card Q = p := by
  classical
  by_cases hq2 : q = 2
  · letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
    letI : Subgroup.Normalizes W1 MF := ⟨hW1normMF⟩
    have hH0notW1 :
        ¬ quotientSubgroupNormalizedBy MF H0 W1 (H ⟨0, hqprime.pos⟩) := by
      intro hnorm
      exact hQnotW1 (by simpa [hHzero_eq_Q] using hnorm)
    have hpair :
        ∀ ⦃i j : Fin q⦄, i ≠ j → Disjoint (H i) (H j) :=
      theorem_9_7_pairwise_disjoint_of_minimal_generator_orbit_sec9
        hH0invU hH0invW1 hqprime hW1card w0 hw0gen hQminimal H hHzero_eq_Q
        hH0notW1 hHnorm hHcardEqQ hsucc
    exact
      theorem_9_7_base_card_eq_prime_of_pairwise_disjoint_card_two_span_sec9
        hpprime hqprime hbarElem hbarFinrank Q H hHcardEqQ hHsup hq2 hpair
  · have hdim :
        letI : Fact p.Prime := ⟨hpprime⟩
        letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
        let η : Subgroup (MF ⧸ H0.subgroupOf MF) ≃o
            Submodule (ZMod p) (Additive (MF ⧸ H0.subgroupOf MF)) :=
          Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule (n := p))
        q = q * Module.finrank (ZMod p) (η Q) :=
      theorem_9_7_clifford_dimension_eq_of_minimal_generator_orbit_ne_two_source_bridge_sec9
        (MF := MF) (H0 := H0) (U := U) (W1 := W1)
        p q hpprime hqprime hbarElem hbarFinrank hUnormMF hH0invU
        hW1normMF hH0invW1 w0 hW1card hw0gen hUW1minimal Q hQnorm
        hQneBot hQneTop hQminimal hQnotW1 H hHzero_eq_Q hHnorm hHneBot hHneTop
        hHnotW1 hHcardEqQ hHsup hsucc hHsucc_ne hq2
    exact
      theorem_9_7_base_card_eq_prime_of_clifford_dimension_sec9
        (V := MF ⧸ H0.subgroupOf MF) hpprime hqprime hbarElem Q hdim

private theorem
    theorem_9_7_zmod_submodule_internal_direct_sum_of_minimal_generator_orbit_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {MF H0 U W1 C : Subgroup G}
    (p q : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hW1normU : Subgroup.Normalizes W1 U]
    (hpprime : Nat.Prime p)
    (hqprime : Nat.Prime q)
    (hbarElem : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF))
    (hbarFinrank :
      letI : Fact p.Prime := ⟨hpprime⟩
      letI : (H0.subgroupOf MF).Normal := hnormalH0
      letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
      Module.finrank (ZMod p) (Additive (MF ⧸ H0.subgroupOf MF)) = q)
    (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G))
    (hH0invU :
      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
      IsInvariant U MF (H0.subgroupOf MF))
    (hW1normMF : W1 ≤ Subgroup.normalizer (MF : Set G))
    (hH0invW1 :
      letI : Subgroup.Normalizes W1 MF := ⟨hW1normMF⟩
      IsInvariant W1 MF (H0.subgroupOf MF))
    (w0 : W1)
    (hW1card : Nat.card W1 = q)
    (hw0gen : Subgroup.zpowers w0 = ⊤)
    (hUW1minimal :
      ∀ R : Subgroup (MF ⧸ H0.subgroupOf MF),
        quotientSubgroupNormalizedBy MF H0 U R →
          quotientSubgroupNormalizedBy MF H0 W1 R →
            R = ⊥ ∨ R = ⊤)
    (Q : Subgroup (MF ⧸ H0.subgroupOf MF))
    (hQnorm : quotientSubgroupNormalizedBy MF H0 U Q)
    (hQneBot : Q ≠ ⊥)
    (hQneTop : Q ≠ ⊤)
    (hQminimal :
      ∀ R : Subgroup (MF ⧸ H0.subgroupOf MF),
        quotientSubgroupNormalizedBy MF H0 U R →
          R ≠ ⊥ → R ≤ Q → Q ≤ R)
    (hQnotW1 : ¬ quotientSubgroupNormalizedBy MF H0 W1 Q)
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHzero_eq_Q : H ⟨0, hqprime.pos⟩ = Q)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHneBot : ∀ i, H i ≠ ⊥)
    (hHneTop : ∀ i, H i ≠ ⊤)
    (hHnotW1 : ∀ i, ¬ quotientSubgroupNormalizedBy MF H0 W1 (H i))
    (hHcardEqQ : ∀ i, Nat.card (H i) = Nat.card Q)
    (hHsup : iSup H = ⊤)
    (hsucc :
      ∀ i : Fin q,
        quotientSubgroupConjugateByElement MF H0
          (H i) (H (theorem_9_7_fin_cyclic_succ_sec9 hqprime.pos i)) (w0 : G))
    (hHsucc_ne :
      ∀ i : Fin q, H (theorem_9_7_fin_cyclic_succ_sec9 hqprime.pos i) ≠ H i) :
    letI : Fact p.Prime := ⟨hpprime⟩
    letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
    let η : Subgroup (MF ⧸ H0.subgroupOf MF) ≃o
        Submodule (ZMod p) (Additive (MF ⧸ H0.subgroupOf MF)) :=
      Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule (n := p))
    DirectSum.IsInternal fun i => η (H i) := by
  classical
  letI : Fact p.Prime := ⟨hpprime⟩
  letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
  let η : Subgroup (MF ⧸ H0.subgroupOf MF) ≃o
      Submodule (ZMod p) (Additive (MF ⧸ H0.subgroupOf MF)) :=
    Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule (n := p))
  have hQcard : Nat.card Q = p :=
    theorem_9_7_base_card_eq_prime_of_minimal_generator_orbit_source_bridge_sec9
      (MF := MF) (H0 := H0) (U := U) (W1 := W1) (_C := C)
      p q hpprime hqprime hbarElem hbarFinrank hUnormMF hH0invU
      hW1normMF hH0invW1 w0 hW1card hw0gen hUW1minimal Q hQnorm
      hQneBot hQneTop hQminimal hQnotW1 H hHzero_eq_Q hHnorm hHneBot hHneTop
      hHnotW1 hHcardEqQ hHsup hsucc hHsucc_ne
  have hHindep : iSupIndep H :=
    theorem_9_7_iSupIndep_of_equal_prime_card_span_sec9
      (V := MF ⧸ H0.subgroupOf MF) hpprime hbarElem hbarFinrank
      Q H hQcard hHcardEqQ hHsup
  simpa [η] using
    theorem_9_7_zmod_submodule_internal_direct_sum_of_iSupIndep_span_sec9
      (V := MF ⧸ H0.subgroupOf MF) (p := p) H hHindep hHsup

private theorem
    theorem_9_7_zmod_submodule_iSupIndep_of_minimal_generator_orbit_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {MF H0 U W1 C : Subgroup G}
    (p q : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hW1normU : Subgroup.Normalizes W1 U]
    (hpprime : Nat.Prime p)
    (hqprime : Nat.Prime q)
    (hbarElem : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF))
    (hbarFinrank :
      letI : Fact p.Prime := ⟨hpprime⟩
      letI : (H0.subgroupOf MF).Normal := hnormalH0
      letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
      Module.finrank (ZMod p) (Additive (MF ⧸ H0.subgroupOf MF)) = q)
    (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G))
    (hH0invU :
      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
      IsInvariant U MF (H0.subgroupOf MF))
    (hW1normMF : W1 ≤ Subgroup.normalizer (MF : Set G))
    (hH0invW1 :
      letI : Subgroup.Normalizes W1 MF := ⟨hW1normMF⟩
      IsInvariant W1 MF (H0.subgroupOf MF))
    (w0 : W1)
    (hW1card : Nat.card W1 = q)
    (hw0gen : Subgroup.zpowers w0 = ⊤)
    (hUW1minimal :
      ∀ R : Subgroup (MF ⧸ H0.subgroupOf MF),
        quotientSubgroupNormalizedBy MF H0 U R →
          quotientSubgroupNormalizedBy MF H0 W1 R →
            R = ⊥ ∨ R = ⊤)
    (Q : Subgroup (MF ⧸ H0.subgroupOf MF))
    (hQnorm : quotientSubgroupNormalizedBy MF H0 U Q)
    (hQneBot : Q ≠ ⊥)
    (hQneTop : Q ≠ ⊤)
    (hQminimal :
      ∀ R : Subgroup (MF ⧸ H0.subgroupOf MF),
        quotientSubgroupNormalizedBy MF H0 U R →
          R ≠ ⊥ → R ≤ Q → Q ≤ R)
    (hQnotW1 : ¬ quotientSubgroupNormalizedBy MF H0 W1 Q)
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHzero_eq_Q : H ⟨0, hqprime.pos⟩ = Q)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHneBot : ∀ i, H i ≠ ⊥)
    (hHneTop : ∀ i, H i ≠ ⊤)
    (hHnotW1 : ∀ i, ¬ quotientSubgroupNormalizedBy MF H0 W1 (H i))
    (hHcardEqQ : ∀ i, Nat.card (H i) = Nat.card Q)
    (hHsup : iSup H = ⊤)
    (hsucc :
      ∀ i : Fin q,
        quotientSubgroupConjugateByElement MF H0
          (H i) (H (theorem_9_7_fin_cyclic_succ_sec9 hqprime.pos i)) (w0 : G))
    (hHsucc_ne :
      ∀ i : Fin q, H (theorem_9_7_fin_cyclic_succ_sec9 hqprime.pos i) ≠ H i) :
    letI : Fact p.Prime := ⟨hpprime⟩
    letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
    let η : Subgroup (MF ⧸ H0.subgroupOf MF) ≃o
        Submodule (ZMod p) (Additive (MF ⧸ H0.subgroupOf MF)) :=
      Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule (n := p))
    iSupIndep fun i => η (H i) := by
  classical
  letI : Fact p.Prime := ⟨hpprime⟩
  letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
  let η : Subgroup (MF ⧸ H0.subgroupOf MF) ≃o
      Submodule (ZMod p) (Additive (MF ⧸ H0.subgroupOf MF)) :=
    Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule (n := p))
  have hInternal : DirectSum.IsInternal fun i => η (H i) := by
    simpa [η] using
      theorem_9_7_zmod_submodule_internal_direct_sum_of_minimal_generator_orbit_source_bridge_sec9
        (MF := MF) (H0 := H0) (U := U) (W1 := W1) (C := C)
        p q hpprime hqprime hbarElem hbarFinrank hUnormMF hH0invU
        hW1normMF hH0invW1 w0 hW1card hw0gen hUW1minimal Q hQnorm
        hQneBot hQneTop hQminimal hQnotW1 H hHzero_eq_Q hHnorm hHneBot hHneTop
        hHnotW1 hHcardEqQ hHsup hsucc hHsucc_ne
  exact
    ((DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top
      (R := ZMod p) (ι := Fin q) (M := Additive (MF ⧸ H0.subgroupOf MF))
      (A := fun i => η (H i))).mp hInternal).1


private theorem
    theorem_9_7_orderedCliffordZModSubmoduleIndep_of_minimal_generator_orbit_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {MF H0 U W1 C : Subgroup G}
    (p q : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hW1normU : Subgroup.Normalizes W1 U]
    (hpprime : Nat.Prime p)
    (hqprime : Nat.Prime q)
    (hbarElem : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF))
    (hbarFinrank :
      letI : Fact p.Prime := ⟨hpprime⟩
      letI : (H0.subgroupOf MF).Normal := hnormalH0
      letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
      Module.finrank (ZMod p) (Additive (MF ⧸ H0.subgroupOf MF)) = q)
    (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G))
    (hH0invU :
      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
      IsInvariant U MF (H0.subgroupOf MF))
    (hW1normMF : W1 ≤ Subgroup.normalizer (MF : Set G))
    (hH0invW1 :
      letI : Subgroup.Normalizes W1 MF := ⟨hW1normMF⟩
      IsInvariant W1 MF (H0.subgroupOf MF))
    (w0 : W1)
    (hW1card : Nat.card W1 = q)
    (hw0gen : Subgroup.zpowers w0 = ⊤)
    (hUW1minimal :
      ∀ R : Subgroup (MF ⧸ H0.subgroupOf MF),
        quotientSubgroupNormalizedBy MF H0 U R →
          quotientSubgroupNormalizedBy MF H0 W1 R →
            R = ⊥ ∨ R = ⊤)
    (Q : Subgroup (MF ⧸ H0.subgroupOf MF))
    (hQnorm : quotientSubgroupNormalizedBy MF H0 U Q)
    (hQneBot : Q ≠ ⊥)
    (hQneTop : Q ≠ ⊤)
    (hQminimal :
      ∀ R : Subgroup (MF ⧸ H0.subgroupOf MF),
        quotientSubgroupNormalizedBy MF H0 U R →
          R ≠ ⊥ → R ≤ Q → Q ≤ R)
    (hQnotW1 : ¬ quotientSubgroupNormalizedBy MF H0 W1 Q)
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHzero_eq_Q : H ⟨0, hqprime.pos⟩ = Q)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHneBot : ∀ i, H i ≠ ⊥)
    (hHneTop : ∀ i, H i ≠ ⊤)
    (hHnotW1 : ∀ i, ¬ quotientSubgroupNormalizedBy MF H0 W1 (H i))
    (hHcardEqQ : ∀ i, Nat.card (H i) = Nat.card Q)
    (hHsup : iSup H = ⊤)
    (hsucc :
      ∀ i : Fin q,
        quotientSubgroupConjugateByElement MF H0
          (H i) (H (theorem_9_7_fin_cyclic_succ_sec9 hqprime.pos i)) (w0 : G))
    (hHsucc_ne :
      ∀ i : Fin q, H (theorem_9_7_fin_cyclic_succ_sec9 hqprime.pos i) ≠ H i) :
    letI : Fact p.Prime := ⟨hpprime⟩
    letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
    let η : Subgroup (MF ⧸ H0.subgroupOf MF) ≃o
        Submodule (ZMod p) (Additive (MF ⧸ H0.subgroupOf MF)) :=
      Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule (n := p))
    iSupIndep fun i => η (H i) := by
  classical
  letI : Fact p.Prime := ⟨hpprime⟩
  letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
  simpa using
    theorem_9_7_zmod_submodule_iSupIndep_of_minimal_generator_orbit_source_bridge_sec9
      (MF := MF) (H0 := H0) (U := U) (W1 := W1) (C := C)
      p q hpprime hqprime hbarElem hbarFinrank hUnormMF hH0invU
      hW1normMF hH0invW1 w0 hW1card hw0gen hUW1minimal Q hQnorm
      hQneBot hQneTop hQminimal hQnotW1 H hHzero_eq_Q hHnorm hHneBot hHneTop hHnotW1
      hHcardEqQ hHsup hsucc hHsucc_ne

private theorem
    theorem_9_7_orderedCliffordSubrepresentationIndep_of_minimal_generator_orbit_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {MF H0 U W1 C : Subgroup G}
    (p q : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hW1normU : Subgroup.Normalizes W1 U]
      (hpprime : Nat.Prime p)
      (hqprime : Nat.Prime q)
      (hbarElem : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF))
      (hbarFinrank :
        letI : Fact p.Prime := ⟨hpprime⟩
        letI : (H0.subgroupOf MF).Normal := hnormalH0
        letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
        Module.finrank (ZMod p) (Additive (MF ⧸ H0.subgroupOf MF)) = q)
      (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G))
      (hH0invU :
        letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
        IsInvariant U MF (H0.subgroupOf MF))
      (hW1normMF : W1 ≤ Subgroup.normalizer (MF : Set G))
      (hH0invW1 :
        letI : Subgroup.Normalizes W1 MF := ⟨hW1normMF⟩
        IsInvariant W1 MF (H0.subgroupOf MF))
      (w0 : W1)
      (hW1card : Nat.card W1 = q)
      (hw0gen : Subgroup.zpowers w0 = ⊤)
      (hUW1minimal :
        ∀ R : Subgroup (MF ⧸ H0.subgroupOf MF),
          quotientSubgroupNormalizedBy MF H0 U R →
            quotientSubgroupNormalizedBy MF H0 W1 R →
              R = ⊥ ∨ R = ⊤)
      (Q : Subgroup (MF ⧸ H0.subgroupOf MF))
      (hQnorm : quotientSubgroupNormalizedBy MF H0 U Q)
      (hQneBot : Q ≠ ⊥)
      (hQneTop : Q ≠ ⊤)
      (hQminimal :
        ∀ R : Subgroup (MF ⧸ H0.subgroupOf MF),
          quotientSubgroupNormalizedBy MF H0 U R →
            R ≠ ⊥ → R ≤ Q → Q ≤ R)
      (hQnotW1 : ¬ quotientSubgroupNormalizedBy MF H0 W1 Q)
      (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
      (hHzero_eq_Q : H ⟨0, hqprime.pos⟩ = Q)
      (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
      (hHneBot : ∀ i, H i ≠ ⊥)
      (hHneTop : ∀ i, H i ≠ ⊤)
      (hHnotW1 : ∀ i, ¬ quotientSubgroupNormalizedBy MF H0 W1 (H i))
      (hHcardEqQ : ∀ i, Nat.card (H i) = Nat.card Q)
      (hHsup : iSup H = ⊤)
      (hsucc :
        ∀ i : Fin q,
          quotientSubgroupConjugateByElement MF H0
            (H i) (H (theorem_9_7_fin_cyclic_succ_sec9 hqprime.pos i)) (w0 : G))
      (hHsucc_ne :
        ∀ i : Fin q, H (theorem_9_7_fin_cyclic_succ_sec9 hqprime.pos i) ≠ H i) :
      letI : Fact p.Prime := ⟨hpprime⟩
      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
      letI : MulAction.QuotientAction U (H0.subgroupOf MF) :=
        quotientAction_of_isInvariant (A := U) (G := MF)
          (H0.subgroupOf MF) hH0invU
      letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
        quotientMulDistribMulAction (A := U) (G := MF)
          (H0.subgroupOf MF) hH0invU
      letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
      let ρ : Representation (ZMod p) U (Additive (MF ⧸ H0.subgroupOf MF)) :=
        Theory.Representation.ofElementaryAbelianAction
          (A := U) (G := MF ⧸ H0.subgroupOf MF) (p := p)
      let η : Subgroup (MF ⧸ H0.subgroupOf MF) ≃o
          Submodule (ZMod p) (Additive (MF ⧸ H0.subgroupOf MF)) :=
        Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule (n := p))
      ∃ S : Fin q → Subrepresentation ρ,
        (∀ i, (S i).toSubmodule = η (H i)) ∧
          iSupIndep fun i => (S i).toSubmodule := by
    classical
    letI : Fact p.Prime := ⟨hpprime⟩
    letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
    letI : MulAction.QuotientAction U (H0.subgroupOf MF) :=
      quotientAction_of_isInvariant (A := U) (G := MF)
        (H0.subgroupOf MF) hH0invU
    letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
      quotientMulDistribMulAction (A := U) (G := MF)
        (H0.subgroupOf MF) hH0invU
    letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
    let ρ : Representation (ZMod p) U (Additive (MF ⧸ H0.subgroupOf MF)) :=
      Theory.Representation.ofElementaryAbelianAction
        (A := U) (G := MF ⧸ H0.subgroupOf MF) (p := p)
    let η : Subgroup (MF ⧸ H0.subgroupOf MF) ≃o
        Submodule (ZMod p) (Additive (MF ⧸ H0.subgroupOf MF)) :=
      Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule (n := p))
    have hSindep : iSupIndep fun i => η (H i) := by
      simpa [η] using
        theorem_9_7_orderedCliffordZModSubmoduleIndep_of_minimal_generator_orbit_source_bridge_sec9
          (MF := MF) (H0 := H0) (U := U) (W1 := W1) (C := C)
          p q hpprime hqprime hbarElem hbarFinrank
          hUnormMF hH0invU hW1normMF hH0invW1 w0 hW1card hw0gen
          hUW1minimal Q hQnorm hQneBot hQneTop hQminimal hQnotW1 H hHzero_eq_Q hHnorm
          hHneBot hHneTop hHnotW1 hHcardEqQ hHsup hsucc hHsucc_ne
    have hSexists : ∀ i, ∃ S : Subrepresentation ρ, S.toSubmodule = η (H i) := by
      intro i
      simpa [ρ, η] using
        theorem_9_7_subrepresentation_of_quotientSubgroupNormalizedBy_sec9
          (MF := MF) (H0 := H0) (U := U) (p := p)
          hbarElem hUnormMF hH0invU (H i) (hHnorm i)
    choose S hS using hSexists
    refine ⟨S, hS, ?_⟩
    convert hSindep using 1
    ext i x
    simp [hS i]

private theorem
    theorem_9_7_iSupIndep_of_minimal_generator_orbit_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {MF H0 U W1 C : Subgroup G}
    (p q : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hW1normU : Subgroup.Normalizes W1 U]
    (hpprime : Nat.Prime p)
    (hqprime : Nat.Prime q)
    (hbarElem : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF))
    (hbarFinrank :
      letI : Fact p.Prime := ⟨hpprime⟩
      letI : (H0.subgroupOf MF).Normal := hnormalH0
      letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
      Module.finrank (ZMod p) (Additive (MF ⧸ H0.subgroupOf MF)) = q)
    (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G))
    (hH0invU :
      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
      IsInvariant U MF (H0.subgroupOf MF))
    (hW1normMF : W1 ≤ Subgroup.normalizer (MF : Set G))
    (hH0invW1 :
      letI : Subgroup.Normalizes W1 MF := ⟨hW1normMF⟩
      IsInvariant W1 MF (H0.subgroupOf MF))
    (w0 : W1)
    (hW1card : Nat.card W1 = q)
    (hw0gen : Subgroup.zpowers w0 = ⊤)
    (hUW1minimal :
      ∀ R : Subgroup (MF ⧸ H0.subgroupOf MF),
        quotientSubgroupNormalizedBy MF H0 U R →
          quotientSubgroupNormalizedBy MF H0 W1 R →
            R = ⊥ ∨ R = ⊤)
    (Q : Subgroup (MF ⧸ H0.subgroupOf MF))
    (hQnorm : quotientSubgroupNormalizedBy MF H0 U Q)
    (hQneBot : Q ≠ ⊥)
    (hQneTop : Q ≠ ⊤)
    (hQminimal :
      ∀ R : Subgroup (MF ⧸ H0.subgroupOf MF),
        quotientSubgroupNormalizedBy MF H0 U R →
          R ≠ ⊥ → R ≤ Q → Q ≤ R)
    (hQnotW1 : ¬ quotientSubgroupNormalizedBy MF H0 W1 Q)
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHzero_eq_Q : H ⟨0, hqprime.pos⟩ = Q)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHneBot : ∀ i, H i ≠ ⊥)
    (hHneTop : ∀ i, H i ≠ ⊤)
    (hHnotW1 : ∀ i, ¬ quotientSubgroupNormalizedBy MF H0 W1 (H i))
    (hHcardEqQ : ∀ i, Nat.card (H i) = Nat.card Q)
    (hHsup : iSup H = ⊤)
    (hsucc :
      ∀ i : Fin q,
        quotientSubgroupConjugateByElement MF H0
          (H i) (H (theorem_9_7_fin_cyclic_succ_sec9 hqprime.pos i)) (w0 : G))
    (hHsucc_ne :
      ∀ i : Fin q, H (theorem_9_7_fin_cyclic_succ_sec9 hqprime.pos i) ≠ H i) :
    iSupIndep H := by
  classical
  letI : Fact p.Prime := ⟨hpprime⟩
  letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
  letI : MulAction.QuotientAction U (H0.subgroupOf MF) :=
    quotientAction_of_isInvariant (A := U) (G := MF)
      (H0.subgroupOf MF) hH0invU
  letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
    quotientMulDistribMulAction (A := U) (G := MF)
      (H0.subgroupOf MF) hH0invU
  letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
  let ρ : Representation (ZMod p) U (Additive (MF ⧸ H0.subgroupOf MF)) :=
    Theory.Representation.ofElementaryAbelianAction
      (A := U) (G := MF ⧸ H0.subgroupOf MF) (p := p)
  rcases
      theorem_9_7_orderedCliffordSubrepresentationIndep_of_minimal_generator_orbit_source_bridge_sec9
        (MF := MF) (H0 := H0) (U := U) (W1 := W1) (C := C)
        p q hpprime hqprime hbarElem hbarFinrank hUnormMF hH0invU
        hW1normMF hH0invW1 w0 hW1card hw0gen hUW1minimal Q hQnorm
        hQneBot hQneTop hQminimal hQnotW1 H hHzero_eq_Q hHnorm hHneBot hHneTop
        hHnotW1 hHcardEqQ hHsup hsucc hHsucc_ne with
    ⟨S, hScarrier, hSindep⟩
  exact
    theorem_9_7_iSupIndep_of_subrepresentation_carriers_sec9
      (V := MF ⧸ H0.subgroupOf MF) (A := U) (p := p) ρ H S hScarrier hSindep

private theorem
    theorem_9_7_orderedCliffordOrbitIndepFactorData_of_minimal_generator_orbit_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {MF H0 U W1 C : Subgroup G}
    (p q : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hW1normU : Subgroup.Normalizes W1 U]
    (hpprime : Nat.Prime p)
    (hqprime : Nat.Prime q)
    (hbarElem : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF))
    (hbarFinrank :
      letI : Fact p.Prime := ⟨hpprime⟩
      letI : (H0.subgroupOf MF).Normal := hnormalH0
      letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
      Module.finrank (ZMod p) (Additive (MF ⧸ H0.subgroupOf MF)) = q)
    (hnormalC : (C.subgroupOf U).Normal)
    (hC : quotientCentralizerIn MF H0 U C)
    (hbarComm :
      letI : (C.subgroupOf U).Normal := hnormalC
      IsMulCommutative (U ⧸ C.subgroupOf U))
    (hCinv : IsInvariant W1 U (C.subgroupOf U))
    (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G))
    (hH0invU :
      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
      IsInvariant U MF (H0.subgroupOf MF))
    (hW1normMF : W1 ≤ Subgroup.normalizer (MF : Set G))
    (hH0invW1 :
      letI : Subgroup.Normalizes W1 MF := ⟨hW1normMF⟩
      IsInvariant W1 MF (H0.subgroupOf MF))
    (w0 : W1)
    (hW1card : Nat.card W1 = q)
    (hw0gen : Subgroup.zpowers w0 = ⊤)
    (hUW1minimal :
      ∀ R : Subgroup (MF ⧸ H0.subgroupOf MF),
        quotientSubgroupNormalizedBy MF H0 U R →
          quotientSubgroupNormalizedBy MF H0 W1 R →
            R = ⊥ ∨ R = ⊤)
    (Q : Subgroup (MF ⧸ H0.subgroupOf MF))
    (hQnorm : quotientSubgroupNormalizedBy MF H0 U Q)
    (hQneBot : Q ≠ ⊥)
    (hQneTop : Q ≠ ⊤)
    (hQminimal :
      ∀ R : Subgroup (MF ⧸ H0.subgroupOf MF),
        quotientSubgroupNormalizedBy MF H0 U R →
          R ≠ ⊥ → R ≤ Q → Q ≤ R)
    (hQnotW1 : ¬ quotientSubgroupNormalizedBy MF H0 W1 Q)
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHzero_eq_Q : H ⟨0, hqprime.pos⟩ = Q)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHneBot : ∀ i, H i ≠ ⊥)
    (hHneTop : ∀ i, H i ≠ ⊤)
    (hHnotW1 : ∀ i, ¬ quotientSubgroupNormalizedBy MF H0 W1 (H i))
    (hHcardEqQ : ∀ i, Nat.card (H i) = Nat.card Q)
    (hHsup : iSup H = ⊤)
    (hsucc :
      ∀ i : Fin q,
        quotientSubgroupConjugateByElement MF H0
          (H i) (H (theorem_9_7_fin_cyclic_succ_sec9 hqprime.pos i)) (w0 : G))
      (hHsucc_ne :
        ∀ i : Fin q, H (theorem_9_7_fin_cyclic_succ_sec9 hqprime.pos i) ≠ H i) :
      ∃ a : ℕ,
        Nat.card Q = p ∧
          ∀ i, quotientFactorActionCentralizerData MF H0 U C (H i) a := by
    have hHindep : iSupIndep H :=
      theorem_9_7_iSupIndep_of_minimal_generator_orbit_source_bridge_sec9
        (MF := MF) (H0 := H0) (U := U) (W1 := W1) (C := C)
        p q hpprime hqprime hbarElem hbarFinrank hUnormMF hH0invU
        hW1normMF hH0invW1 w0 hW1card hw0gen hUW1minimal Q hQnorm
        hQneBot hQneTop hQminimal hQnotW1 H hHzero_eq_Q hHnorm hHneBot hHneTop
        hHnotW1 hHcardEqQ hHsup hsucc hHsucc_ne
    have hQcard :
        Nat.card Q = p :=
      theorem_9_7_base_card_eq_prime_of_iSupIndep_equal_card_span_sec9
        hpprime hqprime hbarElem hbarFinrank Q H hHcardEqQ hHsup hHindep
    have hHcard : ∀ i, Nat.card (H i) = p := by
      intro i
      rw [hHcardEqQ i, hQcard]
    rcases
        theorem_9_7_quotientFactorActions_of_prime_card_ordered_components_sec9
          (MF := MF) (H0 := H0) (U := U) (W1 := W1) (C := C)
          hpprime hqprime.pos hnormalC hC hbarComm hCinv hUnormMF hH0invU
          w0 H hHcard hHnorm hsucc with
      ⟨a, hfac⟩
    exact ⟨a, hQcard, hfac⟩

private theorem
    theorem_9_7_orderedCliffordOrbitBaseFactorData_of_minimal_generator_orbit_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {MF H0 U W1 C : Subgroup G}
    (p q : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hW1normU : Subgroup.Normalizes W1 U]
    (hpprime : Nat.Prime p)
    (hqprime : Nat.Prime q)
    (hbarElem : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF))
    (hbarFinrank :
      letI : Fact p.Prime := ⟨hpprime⟩
      letI : (H0.subgroupOf MF).Normal := hnormalH0
      letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
      Module.finrank (ZMod p) (Additive (MF ⧸ H0.subgroupOf MF)) = q)
    (hnormalC : (C.subgroupOf U).Normal)
    (hC : quotientCentralizerIn MF H0 U C)
    (hbarComm :
      letI : (C.subgroupOf U).Normal := hnormalC
      IsMulCommutative (U ⧸ C.subgroupOf U))
    (hCinv : IsInvariant W1 U (C.subgroupOf U))
    (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G))
    (hH0invU :
      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
      IsInvariant U MF (H0.subgroupOf MF))
    (hW1normMF : W1 ≤ Subgroup.normalizer (MF : Set G))
    (hH0invW1 :
      letI : Subgroup.Normalizes W1 MF := ⟨hW1normMF⟩
      IsInvariant W1 MF (H0.subgroupOf MF))
    (w0 : W1)
    (hW1card : Nat.card W1 = q)
    (hw0gen : Subgroup.zpowers w0 = ⊤)
    (hUW1minimal :
      ∀ R : Subgroup (MF ⧸ H0.subgroupOf MF),
        quotientSubgroupNormalizedBy MF H0 U R →
          quotientSubgroupNormalizedBy MF H0 W1 R →
            R = ⊥ ∨ R = ⊤)
    (Q : Subgroup (MF ⧸ H0.subgroupOf MF))
    (hQnorm : quotientSubgroupNormalizedBy MF H0 U Q)
    (hQneBot : Q ≠ ⊥)
    (hQneTop : Q ≠ ⊤)
    (hQminimal :
      ∀ R : Subgroup (MF ⧸ H0.subgroupOf MF),
        quotientSubgroupNormalizedBy MF H0 U R →
          R ≠ ⊥ → R ≤ Q → Q ≤ R)
    (hQnotW1 : ¬ quotientSubgroupNormalizedBy MF H0 W1 Q)
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHzero_eq_Q : H ⟨0, hqprime.pos⟩ = Q)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHneBot : ∀ i, H i ≠ ⊥)
    (hHneTop : ∀ i, H i ≠ ⊤)
    (hHnotW1 : ∀ i, ¬ quotientSubgroupNormalizedBy MF H0 W1 (H i))
    (hHcardEqQ : ∀ i, Nat.card (H i) = Nat.card Q)
    (hHsup : iSup H = ⊤)
    (hsucc :
      ∀ i : Fin q,
        quotientSubgroupConjugateByElement MF H0
          (H i) (H (theorem_9_7_fin_cyclic_succ_sec9 hqprime.pos i)) (w0 : G))
    (hHsucc_ne :
      ∀ i : Fin q, H (theorem_9_7_fin_cyclic_succ_sec9 hqprime.pos i) ≠ H i) :
    ∃ a : ℕ,
      Nat.card Q = p ∧
        iSupIndep H ∧
        ∀ i, quotientFactorActionCentralizerData MF H0 U C (H i) a := by
  rcases
      theorem_9_7_orderedCliffordOrbitIndepFactorData_of_minimal_generator_orbit_source_bridge_sec9
        (MF := MF) (H0 := H0) (U := U) (W1 := W1) (C := C)
        p q hpprime hqprime hbarElem hbarFinrank hnormalC hC hbarComm hCinv
        hUnormMF hH0invU hW1normMF hH0invW1 w0 hW1card hw0gen
        hUW1minimal Q hQnorm hQneBot hQneTop hQminimal hQnotW1 H hHzero_eq_Q
        hHnorm hHneBot hHneTop hHnotW1 hHcardEqQ hHsup hsucc hHsucc_ne with
    ⟨a, hQcard, hHfac⟩
  have hHindep : iSupIndep H :=
    theorem_9_7_iSupIndep_of_equal_prime_card_span_sec9
      (V := MF ⧸ H0.subgroupOf MF) hpprime hbarElem hbarFinrank
      Q H hQcard hHcardEqQ hHsup
  exact ⟨a, hQcard, hHindep, hHfac⟩

private theorem
    theorem_9_7_orderedCliffordOrbitFactorData_of_minimal_generator_orbit_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {MF H0 U W1 C : Subgroup G}
    (p q : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hW1normU : Subgroup.Normalizes W1 U]
    (hpprime : Nat.Prime p)
    (hqprime : Nat.Prime q)
    (hbarElem : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF))
    (hbarFinrank :
      letI : Fact p.Prime := ⟨hpprime⟩
      letI : (H0.subgroupOf MF).Normal := hnormalH0
      letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
      Module.finrank (ZMod p) (Additive (MF ⧸ H0.subgroupOf MF)) = q)
    (hnormalC : (C.subgroupOf U).Normal)
    (hC : quotientCentralizerIn MF H0 U C)
    (hbarComm :
      letI : (C.subgroupOf U).Normal := hnormalC
      IsMulCommutative (U ⧸ C.subgroupOf U))
    (hCinv : IsInvariant W1 U (C.subgroupOf U))
    (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G))
    (hH0invU :
      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
      IsInvariant U MF (H0.subgroupOf MF))
    (hW1normMF : W1 ≤ Subgroup.normalizer (MF : Set G))
    (hH0invW1 :
      letI : Subgroup.Normalizes W1 MF := ⟨hW1normMF⟩
      IsInvariant W1 MF (H0.subgroupOf MF))
    (w0 : W1)
    (hW1card : Nat.card W1 = q)
    (hw0gen : Subgroup.zpowers w0 = ⊤)
    (hUW1minimal :
      ∀ R : Subgroup (MF ⧸ H0.subgroupOf MF),
        quotientSubgroupNormalizedBy MF H0 U R →
          quotientSubgroupNormalizedBy MF H0 W1 R →
            R = ⊥ ∨ R = ⊤)
    (Q : Subgroup (MF ⧸ H0.subgroupOf MF))
    (hQnorm : quotientSubgroupNormalizedBy MF H0 U Q)
    (hQneBot : Q ≠ ⊥)
    (hQneTop : Q ≠ ⊤)
    (hQminimal :
      ∀ R : Subgroup (MF ⧸ H0.subgroupOf MF),
        quotientSubgroupNormalizedBy MF H0 U R →
          R ≠ ⊥ → R ≤ Q → Q ≤ R)
    (hQnotW1 : ¬ quotientSubgroupNormalizedBy MF H0 W1 Q)
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHzero_eq_Q : H ⟨0, hqprime.pos⟩ = Q)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHneBot : ∀ i, H i ≠ ⊥)
    (hHneTop : ∀ i, H i ≠ ⊤)
    (hHnotW1 : ∀ i, ¬ quotientSubgroupNormalizedBy MF H0 W1 (H i))
    (hHcardEqQ : ∀ i, Nat.card (H i) = Nat.card Q)
    (hHsup : iSup H = ⊤)
    (hsucc :
      ∀ i : Fin q,
        quotientSubgroupConjugateByElement MF H0
          (H i) (H (theorem_9_7_fin_cyclic_succ_sec9 hqprime.pos i)) (w0 : G))
    (hHsucc_ne :
      ∀ i : Fin q, H (theorem_9_7_fin_cyclic_succ_sec9 hqprime.pos i) ≠ H i) :
    ∃ a : ℕ,
      theorem_9_7_orderedCliffordOrbitFactorData_sec9
        MF H0 U C p a H := by
  rcases
      theorem_9_7_orderedCliffordOrbitBaseFactorData_of_minimal_generator_orbit_source_bridge_sec9
        (MF := MF) (H0 := H0) (U := U) (W1 := W1) (C := C)
        p q hpprime hqprime hbarElem hbarFinrank hnormalC hC hbarComm hCinv
        hUnormMF hH0invU hW1normMF hH0invW1 w0 hW1card hw0gen
        hUW1minimal Q hQnorm hQneBot hQneTop hQminimal hQnotW1 H hHzero_eq_Q
        hHnorm hHneBot hHneTop hHnotW1 hHcardEqQ hHsup hsucc hHsucc_ne with
    ⟨a, hQcard, hHindep, hHfac⟩
  exact ⟨a, fun i => (hHcardEqQ i).trans hQcard, hHindep, hHfac⟩

private theorem
    theorem_9_7_orderedCliffordComponentData_of_minimal_U_factor_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {MF H0 U W1 C : Subgroup G}
    (p q : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hW1normU : Subgroup.Normalizes W1 U]
    (hpprime : Nat.Prime p)
    (hqprime : Nat.Prime q)
    (hbarElem : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF))
    (hbarFinrank :
      letI : Fact p.Prime := ⟨hpprime⟩
      letI : (H0.subgroupOf MF).Normal := hnormalH0
      letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
      Module.finrank (ZMod p) (Additive (MF ⧸ H0.subgroupOf MF)) = q)
    (hnormalC : (C.subgroupOf U).Normal)
    (hC : quotientCentralizerIn MF H0 U C)
    (hbarComm :
      letI : (C.subgroupOf U).Normal := hnormalC
      IsMulCommutative (U ⧸ C.subgroupOf U))
    (hCinv : IsInvariant W1 U (C.subgroupOf U))
    (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G))
    (hH0invU :
      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
      IsInvariant U MF (H0.subgroupOf MF))
    (hW1normMF : W1 ≤ Subgroup.normalizer (MF : Set G))
    (hH0invW1 :
      letI : Subgroup.Normalizes W1 MF := ⟨hW1normMF⟩
      IsInvariant W1 MF (H0.subgroupOf MF))
    (w0 : W1)
    (hW1card : Nat.card W1 = q)
    (hw0gen : Subgroup.zpowers w0 = ⊤)
    (hUW1minimal :
      ∀ R : Subgroup (MF ⧸ H0.subgroupOf MF),
        quotientSubgroupNormalizedBy MF H0 U R →
          quotientSubgroupNormalizedBy MF H0 W1 R →
            R = ⊥ ∨ R = ⊤)
    (Q : Subgroup (MF ⧸ H0.subgroupOf MF))
    (hQnorm : quotientSubgroupNormalizedBy MF H0 U Q)
    (hQneBot : Q ≠ ⊥)
    (hQneTop : Q ≠ ⊤)
    (hQminimal :
      ∀ R : Subgroup (MF ⧸ H0.subgroupOf MF),
        quotientSubgroupNormalizedBy MF H0 U R →
          R ≠ ⊥ → R ≤ Q → Q ≤ R)
    (hQnotW1 : ¬ quotientSubgroupNormalizedBy MF H0 W1 Q) :
    ∃ a : ℕ,
      theorem_9_7_orderedCliffordComponentData_sec9
        MF H0 U W1 C p q a w0 hqprime.pos := by
  classical
  letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
  letI : Subgroup.Normalizes W1 MF := ⟨hW1normMF⟩
  letI : MulAction.QuotientAction W1 (H0.subgroupOf MF) :=
    quotientAction_of_isInvariant (A := W1) (G := MF)
      (H0.subgroupOf MF) hH0invW1
  letI : MulDistribMulAction W1 (MF ⧸ H0.subgroupOf MF) :=
    quotientMulDistribMulAction (A := W1) (G := MF)
      (H0.subgroupOf MF) hH0invW1
  let φ : MulAut (MF ⧸ H0.subgroupOf MF) :=
    (MulDistribMulAction.toMulAut W1
      (MF ⧸ H0.subgroupOf MF)) (w0⁻¹ : W1)
  have hQminDichotomy :
      ∀ R : Subgroup (MF ⧸ H0.subgroupOf MF),
        quotientSubgroupNormalizedBy MF H0 U R →
          R ≤ Q → R = ⊥ ∨ R = Q := by
    intro R hRnorm hRQ
    by_cases hRbot : R = ⊥
    · exact Or.inl hRbot
    · exact Or.inr (le_antisymm hRQ (hQminimal R hRnorm hRbot hRQ))
  have hQnotW0 :
      ¬ quotientSubgroupConjugateByElement MF H0 Q Q (w0 : G) :=
    theorem_9_7_generator_not_conjugates_quotientSubgroup_self_of_not_normalized_sec9
      w0 hw0gen hQnotW1
  have hφpow : φ ^ q = 1 := by
    simpa [φ] using
      theorem_9_7_generator_MF_quotient_action_inv_pow_eq_one_sec9
        (MF := MF) (H0 := H0) (W1 := W1) hH0invW1 w0 hW1card hw0gen
  let Hpow : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF) :=
    fun i => Q.map ((φ ^ i.1).toMonoidHom)
  have hHpow_succ_map :
      ∀ i : Fin q,
        (Hpow i).map φ.toMonoidHom =
          Hpow (theorem_9_7_fin_cyclic_succ_sec9 hqprime.pos i) := by
    intro i
    by_cases hnext : i.1 + 1 < q
    · have hidx :
          theorem_9_7_fin_cyclic_succ_sec9 hqprime.pos i =
            ⟨i.1 + 1, hnext⟩ := by
        apply Fin.ext
        simp [theorem_9_7_fin_cyclic_succ_sec9, hnext]
      simpa [Hpow, hidx] using
        theorem_9_7_subgroup_map_mulAut_pow_succ_sec9 φ Q i.1
    · have hiq : i.1 + 1 = q := by omega
      have hidx :
          theorem_9_7_fin_cyclic_succ_sec9 hqprime.pos i =
            ⟨0, hqprime.pos⟩ := by
        apply Fin.ext
        simp [theorem_9_7_fin_cyclic_succ_sec9, hnext]
      have htarget :
          Hpow (theorem_9_7_fin_cyclic_succ_sec9 hqprime.pos i) = Q := by
        rw [hidx]
        change Q.map ((φ ^ (0 : ℕ)).toMonoidHom) = Q
        ext x
        simp
      calc
        (Hpow i).map φ.toMonoidHom =
            Q.map ((φ ^ (i.1 + 1)).toMonoidHom) := by
              simpa [Hpow] using
                theorem_9_7_subgroup_map_mulAut_pow_succ_sec9 φ Q i.1
        _ = Q.map ((φ ^ q).toMonoidHom) := by rw [hiq]
        _ = Q := theorem_9_7_subgroup_map_mulAut_pow_eq_self_sec9 φ Q hφpow
        _ = Hpow (theorem_9_7_fin_cyclic_succ_sec9 hqprime.pos i) := htarget.symm
  have hHpow_succ_conj :
      ∀ i : Fin q,
        quotientSubgroupConjugateByElement MF H0 (Hpow i)
          (Hpow (theorem_9_7_fin_cyclic_succ_sec9 hqprime.pos i)) (w0 : G) := by
    intro i
    have hstep :=
      theorem_9_7_quotientSubgroupConjugateByElement_action_map_sec9
        (MF := MF) (H0 := H0) (A := W1) hH0invW1 (Hpow i) w0
    change
      quotientSubgroupConjugateByElement MF H0 (Hpow i)
        ((Hpow i).map φ.toMonoidHom) (w0 : G) at hstep
    have htarget := hHpow_succ_map i
    change Subgroup.map (↑φ) (Hpow i) =
      Hpow (theorem_9_7_fin_cyclic_succ_sec9 hqprime.pos i) at htarget
    simpa [htarget] using hstep
  have hHpow_neBot : ∀ i : Fin q, Hpow i ≠ ⊥ := by
    intro i
    simpa [Hpow] using
      theorem_9_7_subgroup_map_mulAut_ne_bot_sec9 (φ ^ i.1) Q hQneBot
  have hHpow_neTop : ∀ i : Fin q, Hpow i ≠ ⊤ := by
    intro i
    simpa [Hpow] using
      theorem_9_7_subgroup_map_mulAut_ne_top_sec9 (φ ^ i.1) Q hQneTop
  have hHpow_card_eq_Q : ∀ i : Fin q, Nat.card (Hpow i) = Nat.card Q := by
    intro i
    simpa [Hpow] using theorem_9_7_subgroup_map_mulAut_card_sec9 (φ ^ i.1) Q
  have hHpow_norm :
      ∀ i : Fin q, quotientSubgroupNormalizedBy MF H0 U (Hpow i) := by
    intro i
    have haction_pow :
        MulDistribMulAction.toMulAut W1 (MF ⧸ H0.subgroupOf MF)
            ((w0 ^ i.1)⁻¹ : W1) =
          φ ^ i.1 := by
      calc
        MulDistribMulAction.toMulAut W1 (MF ⧸ H0.subgroupOf MF)
            ((w0 ^ i.1)⁻¹ : W1) =
            MulDistribMulAction.toMulAut W1 (MF ⧸ H0.subgroupOf MF)
              ((w0⁻¹ : W1) ^ i.1) := by
              rw [← inv_pow]
        _ =
            (MulDistribMulAction.toMulAut W1 (MF ⧸ H0.subgroupOf MF)
              (w0⁻¹ : W1)) ^ i.1 := by
              rw [map_pow]
        _ = φ ^ i.1 := rfl
    have hnorm :=
      theorem_9_7_quotientSubgroupNormalizedBy_w1_conjugate_sec9
        (MF := MF) (H0 := H0) (U := U) (W1 := W1)
        hH0invU hH0invW1 Q hQnorm (w0 ^ i.1)
    simpa [Hpow, haction_pow] using hnorm
  have hHpow_minimal :
      ∀ i : Fin q, ∀ R : Subgroup (MF ⧸ H0.subgroupOf MF),
        quotientSubgroupNormalizedBy MF H0 U R →
          R ≠ ⊥ → R ≤ Hpow i → Hpow i ≤ R := by
    intro i R hRnorm hRneBot hRle
    have haction_symm :
        MulDistribMulAction.toMulAut W1 (MF ⧸ H0.subgroupOf MF)
            (w0 ^ i.1) =
          (φ ^ i.1).symm := by
      rw [map_pow]
      change
        (MulDistribMulAction.toMulAut W1 (MF ⧸ H0.subgroupOf MF)
            w0) ^ i.1 =
          ((MulDistribMulAction.toMulAut W1 (MF ⧸ H0.subgroupOf MF)
            (w0⁻¹ : W1)) ^ i.1).symm
      rw [map_inv]
      simp
    have hRpre_norm :
        quotientSubgroupNormalizedBy MF H0 U
          (R.map ((φ ^ i.1).symm.toMonoidHom)) := by
      have hnorm :=
        theorem_9_7_quotientSubgroupNormalizedBy_w1_conjugate_symm_sec9
          (MF := MF) (H0 := H0) (U := U) (W1 := W1)
          hH0invU hH0invW1 R hRnorm (w0 ^ i.1)
      change
        quotientSubgroupNormalizedBy MF H0 U
          (R.map (MulDistribMulAction.toMulAut W1
            (MF ⧸ H0.subgroupOf MF) (w0 ^ i.1)).toMonoidHom) at hnorm
      change
        quotientSubgroupNormalizedBy MF H0 U
          (R.map ((φ ^ i.1).symm.toMonoidHom))
      rwa [haction_symm] at hnorm
    have hRpre_neBot :
        R.map ((φ ^ i.1).symm.toMonoidHom) ≠ ⊥ := by
      simpa using
        theorem_9_7_subgroup_map_mulAut_ne_bot_sec9
          (φ ^ i.1).symm R hRneBot
    have hRpre_le_Q :
        R.map ((φ ^ i.1).symm.toMonoidHom) ≤ Q := by
      simpa [Hpow] using
        (theorem_9_7_subgroup_le_map_mulAut_iff_sec9
          (φ ^ i.1) R Q).1 hRle
    have hQ_le_Rpre :
        Q ≤ R.map ((φ ^ i.1).symm.toMonoidHom) :=
      hQminimal (R.map ((φ ^ i.1).symm.toMonoidHom))
        hRpre_norm hRpre_neBot hRpre_le_Q
    simpa [Hpow] using
      (theorem_9_7_subgroup_map_mulAut_le_iff_sec9
        (φ ^ i.1) Q R).2 hQ_le_Rpre
  have hHpow_notW1 :
      ∀ i : Fin q, ¬ quotientSubgroupNormalizedBy MF H0 W1 (Hpow i) := by
    intro i
    exact
      theorem_9_7_not_W1_normalized_of_UW1_minimal_sec9
        (MF := MF) (H0 := H0) (U := U) (W1 := W1)
        hUW1minimal (hHpow_norm i) (hHpow_neBot i) (hHpow_neTop i)
  have hHpow_succ_ne :
      ∀ i : Fin q,
        Hpow (theorem_9_7_fin_cyclic_succ_sec9 hqprime.pos i) ≠ Hpow i := by
    intro i hsame
    have hself :
        quotientSubgroupConjugateByElement MF H0 (Hpow i) (Hpow i) (w0 : G) := by
      simpa [hsame] using hHpow_succ_conj i
    exact hHpow_notW1 i
      (theorem_9_7_quotientSubgroupNormalizedBy_of_generator_conjugates_self_sec9
        w0 hw0gen hself)
  have hHpow_sup_top : iSup Hpow = ⊤ := by
    have hSupNormU :
        quotientSubgroupNormalizedBy MF H0 U (iSup Hpow) :=
      theorem_9_7_quotientSubgroupNormalizedBy_iSup_fin_sec9
        hqprime.pos Hpow hHpow_norm
    have hSupConjW0 :
        quotientSubgroupConjugateByElement MF H0
          (iSup Hpow) (iSup Hpow) (w0 : G) :=
      theorem_9_7_quotientSubgroupConjugateByElement_iSup_of_fin_cyclic_successor_sec9
        hqprime.pos Hpow w0 hHpow_succ_conj
    have hSupNormW1 : quotientSubgroupNormalizedBy MF H0 W1 (iSup Hpow) :=
      theorem_9_7_quotientSubgroupNormalizedBy_of_generator_conjugates_self_sec9
        w0 hw0gen hSupConjW0
    rcases hUW1minimal (iSup Hpow) hSupNormU hSupNormW1 with hbot | htop
    · exfalso
      have hH0leBot : Hpow ⟨0, hqprime.pos⟩ ≤ ⊥ := by
        simpa [hbot] using (le_iSup Hpow ⟨0, hqprime.pos⟩)
      exact hHpow_neBot ⟨0, hqprime.pos⟩ (le_bot_iff.mp hH0leBot)
    · exact htop
  have hHpow_zero_eq_Q : Hpow ⟨0, hqprime.pos⟩ = Q := by
    change Q.map ((φ ^ (0 : ℕ)).toMonoidHom) = Q
    ext x
    simp
  rcases
      theorem_9_7_orderedCliffordOrbitFactorData_of_minimal_generator_orbit_source_bridge_sec9
        (MF := MF) (H0 := H0) (U := U) (W1 := W1) (C := C)
        p q hpprime hqprime hbarElem hbarFinrank hnormalC hC hbarComm hCinv
        hUnormMF hH0invU hW1normMF hH0invW1 w0 hW1card hw0gen
        hUW1minimal Q hQnorm hQneBot hQneTop hQminimal hQnotW1 Hpow
        hHpow_zero_eq_Q
        hHpow_norm hHpow_neBot hHpow_neTop hHpow_notW1 hHpow_card_eq_Q
        hHpow_sup_top hHpow_succ_conj hHpow_succ_ne with
    ⟨a, hHpow_card, hHpow_indep, hHpow_fac⟩
  exact
    ⟨a, Hpow, hHpow_card, hHpow_norm, hHpow_indep, hHpow_sup_top, hHpow_fac,
      hHpow_succ_conj⟩

private theorem
    theorem_9_7_orderedCliffordComponentData_of_reducible_action_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {MF H0 U W1 C : Subgroup G}
    (p q : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hW1normU : Subgroup.Normalizes W1 U]
    (hpprime : Nat.Prime p)
    (hqprime : Nat.Prime q)
    (hbarElem : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF))
    (hbarFinrank :
      letI : Fact p.Prime := ⟨hpprime⟩
      letI : (H0.subgroupOf MF).Normal := hnormalH0
      letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
      Module.finrank (ZMod p) (Additive (MF ⧸ H0.subgroupOf MF)) = q)
    (hnormalC : (C.subgroupOf U).Normal)
    (hC : quotientCentralizerIn MF H0 U C)
    (hbarComm :
      letI : (C.subgroupOf U).Normal := hnormalC
      IsMulCommutative (U ⧸ C.subgroupOf U))
    (hCinv : IsInvariant W1 U (C.subgroupOf U))
    (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G))
    (hH0invU :
      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
      IsInvariant U MF (H0.subgroupOf MF))
    (hW1normMF : W1 ≤ Subgroup.normalizer (MF : Set G))
    (hH0invW1 :
      letI : Subgroup.Normalizes W1 MF := ⟨hW1normMF⟩
      IsInvariant W1 MF (H0.subgroupOf MF))
    (w0 : W1)
    (hW1card : Nat.card W1 = q)
    (hw0gen : Subgroup.zpowers w0 = ⊤)
    (hUW1minimal :
      ∀ R : Subgroup (MF ⧸ H0.subgroupOf MF),
        quotientSubgroupNormalizedBy MF H0 U R →
          quotientSubgroupNormalizedBy MF H0 W1 R →
            R = ⊥ ∨ R = ⊤)
    (hnonUirred : ¬ quotientIrreducibleActionData MF H0 U) :
    ∃ a : ℕ,
      theorem_9_7_orderedCliffordComponentData_sec9
        MF H0 U W1 C p q a w0 hqprime.pos := by
  rcases
      theorem_9_7_exists_minimal_U_normalized_not_W1_of_reducible_minimal_sec9
        (MF := MF) (H0 := H0) (U := U) (W1 := W1)
        hnormalH0 hUW1minimal hnonUirred with
    ⟨Q, hQnorm, hQneBot, hQneTop, hQminimal, hQnotW1⟩
  exact
    theorem_9_7_orderedCliffordComponentData_of_minimal_U_factor_source_bridge_sec9
      (MF := MF) (H0 := H0) (U := U) (W1 := W1) (C := C)
      (p := p) (q := q) hpprime hqprime hbarElem hbarFinrank hnormalC
      hC hbarComm hCinv hUnormMF hH0invU hW1normMF hH0invW1 w0 hW1card
      hw0gen hUW1minimal Q hQnorm hQneBot hQneTop hQminimal hQnotW1

private theorem
    theorem_9_7_orderedCliffordComponentData_of_proper_factor_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    {MF H0 U W1 C : Subgroup G}
    (p q : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hW1normU : Subgroup.Normalizes W1 U]
    (hpprime : Nat.Prime p)
    (hqprime : Nat.Prime q)
    (hbarElem : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF))
    (hbarFinrank :
      letI : Fact p.Prime := ⟨hpprime⟩
      letI : (H0.subgroupOf MF).Normal := hnormalH0
      letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
      Module.finrank (ZMod p) (Additive (MF ⧸ H0.subgroupOf MF)) = q)
    (hnormalC : (C.subgroupOf U).Normal)
      (hC : quotientCentralizerIn MF H0 U C)
      (hbarComm :
        letI : (C.subgroupOf U).Normal := hnormalC
        IsMulCommutative (U ⧸ C.subgroupOf U))
      (hCinv : IsInvariant W1 U (C.subgroupOf U))
      (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G))
      (hH0invU :
        letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
        IsInvariant U MF (H0.subgroupOf MF))
      (hW1normMF : W1 ≤ Subgroup.normalizer (MF : Set G))
      (hH0invW1 :
        letI : Subgroup.Normalizes W1 MF := ⟨hW1normMF⟩
        IsInvariant W1 MF (H0.subgroupOf MF))
      (w0 : W1)
      (hW1card : Nat.card W1 = q)
      (hw0gen : Subgroup.zpowers w0 = ⊤)
    (hUW1minimal :
      ∀ R : Subgroup (MF ⧸ H0.subgroupOf MF),
        quotientSubgroupNormalizedBy MF H0 U R →
          quotientSubgroupNormalizedBy MF H0 W1 R →
            R = ⊥ ∨ R = ⊤)
    (Q : Subgroup (MF ⧸ H0.subgroupOf MF))
    (hQnorm : quotientSubgroupNormalizedBy MF H0 U Q)
    (hQneBot : Q ≠ ⊥)
    (hQneTop : Q ≠ ⊤)
    (_hQnotW1 : ¬ quotientSubgroupNormalizedBy MF H0 W1 Q) :
    ∃ a : ℕ,
      theorem_9_7_orderedCliffordComponentData_sec9
        MF H0 U W1 C p q a w0 hqprime.pos := by
  have hnonUirred : ¬ quotientIrreducibleActionData MF H0 U := by
    intro hirred
    rcases hirred with ⟨_hnormalIrred, hmin⟩
    rcases hmin Q hQnorm with hbot | htop
    · exact hQneBot hbot
    · exact hQneTop htop
  exact
    theorem_9_7_orderedCliffordComponentData_of_reducible_action_source_bridge_sec9
      (MF := MF) (H0 := H0) (U := U) (W1 := W1) (C := C)
      (p := p) (q := q) hpprime hqprime hbarElem hbarFinrank hnormalC
      hC hbarComm hCinv hUnormMF hH0invU hW1normMF hH0invW1 w0
      hW1card hw0gen hUW1minimal hnonUirred

private theorem
    theorem_9_7_clifford_case_a_quotient_component_ordered_decomposition_from_reducible_factor_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
          quotientChiefFactorData_9_6 M MF H0 W1 hp) →
          quotientCentralizerIn MF H0 U C →
            quotientBarUCardinality U C u →
              (hpprime : Nat.Prime p) →
                (hqprime : Nat.Prime q) →
                  (hnormalH0 : (H0.subgroupOf MF).Normal) →
                    (hbarElem :
                      letI : (H0.subgroupOf MF).Normal := hnormalH0
                      IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF)) →
                    (letI : Fact p.Prime := ⟨hpprime⟩
                    letI : (H0.subgroupOf MF).Normal := hnormalH0
                    letI : IsElementaryAbelian p
                      (MF ⧸ H0.subgroupOf MF) := hbarElem
                    Module.finrank (ZMod p)
                      (Additive (MF ⧸ H0.subgroupOf MF)) = q) →
                    (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G)) →
                    (hH0invU :
                      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                      IsInvariant U MF (H0.subgroupOf MF)) →
                    (hnormalC : (C.subgroupOf U).Normal) →
                      (letI : (C.subgroupOf U).Normal := hnormalC
                      IsMulCommutative (U ⧸ C.subgroupOf U)) →
                    (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G)) →
                    (hCinv :
                        letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
                        IsInvariant W1 U (C.subgroupOf U)) →
                    (w0 : W1) →
                    (hw0gen : Subgroup.zpowers w0 = ⊤) →
                    letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
                    letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
                      quotientMulDistribMulAction (A := W1) (G := U)
                        (C.subgroupOf U) hCinv
                    letI : (C.subgroupOf U).Normal := hnormalC
                    ∀ Q : Subgroup (MF ⧸ H0.subgroupOf MF),
                      quotientSubgroupNormalizedBy MF H0 U Q →
                        Q ≠ ⊥ →
                          Q ≠ ⊤ →
                            ¬ quotientSubgroupNormalizedBy MF H0 W1 Q →
                            ∃ a : ℕ,
                      letI : (H0.subgroupOf MF).Normal := hnormalH0
                      theorem_9_7_orderedCliffordComponentData_sec9
                        MF H0 U W1 C p q a w0 hqprime.pos := by
  classical
  intro h92 hp96 hC _hBarU hpprime hqprime hnormalH0 hbarElem hbarFinrank
    hUnormMF hH0invU hnormalC hbarComm hW1normU hCinv w0 hw0gen Q hQnorm
    hQneBot hQneTop hQnotW1
  have h92Full : hypothesis_9_2_statement M MF U W1 W2 q := h92
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
  have hW1card : Nat.card W1 = q := by
    exact h92.q_eq
  rcases hp96 with ⟨hp, _hp_eq, hpData, h96⟩
  have hUW1minimal :
      ∀ R : Subgroup (MF ⧸ H0.subgroupOf MF),
        quotientSubgroupNormalizedBy MF H0 U R →
          quotientSubgroupNormalizedBy MF H0 W1 R →
            R = ⊥ ∨ R = ⊤ := by
    intro R hRnormU hRnormW1
    exact
      quotientSubgroup_dichotomy_of_quotientChiefFactorData_sec9
        M MF U W1 W2 H0 q hp h92Full hpData h96 hnormalH0 R hRnormU
        hRnormW1
  have hW1normMF : W1 ≤ Subgroup.normalizer (MF : Set G) := by
    have hUW1normMF :
        (U ⊔ W1 : Subgroup G) ≤ Subgroup.normalizer (MF : Set G) :=
      (theorem_9_3_action_normalizes_and_solvable_sec9 M MF U W1 W2 q h92Full).1
    exact le_sup_right.trans hUW1normMF
  have hH0invW1 :
      letI : Subgroup.Normalizes W1 MF := ⟨hW1normMF⟩
      IsInvariant W1 MF (H0.subgroupOf MF) := by
    letI : Subgroup.Normalizes W1 MF := ⟨hW1normMF⟩
    rcases hpData with
      ⟨_hH0leMF, hMFleM, hH0normalM, _hH0normalMF, _hH0lt, _helem,
        _htypeIIIIV⟩
    rcases h92Full.typePDefinitionData with
      ⟨_hMFsource, _hW1cyc, _hW1ne, ⟨hW1leM, _hW1hall⟩,
        _hcompMW1, _hUleD, _hUnil, _hW1normU, _hcompDU, _hMFnotcyc,
        _hM2le, _hFitEq, _hFitLeD, _hW2le, _hW2cyc, _hW2ne,
        _hcentW1, _hnormX⟩
    exact
      subgroupOf_MF_isInvariant_of_subgroupOf_M_normal_sec9 M MF W1 H0
        hMFleM hW1leM hH0normalM hW1normMF
  exact
    theorem_9_7_orderedCliffordComponentData_of_proper_factor_source_bridge_sec9
      (MF := MF) (H0 := H0) (U := U) (W1 := W1) (C := C)
      (p := p) (q := q) hpprime hqprime hbarElem hbarFinrank hnormalC
      hC hbarComm hCinv hUnormMF hH0invU hW1normMF hH0invW1 w0 hW1card
      hw0gen hUW1minimal Q hQnorm hQneBot hQneTop hQnotW1

private theorem
    theorem_9_7_clifford_case_a_quotient_component_character_transition_from_ordered_decomposition_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u a : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
          quotientChiefFactorData_9_6 M MF H0 W1 hp) →
          quotientCentralizerIn MF H0 U C →
            quotientBarUCardinality U C u →
              (hpprime : Nat.Prime p) →
                (hqprime : Nat.Prime q) →
                  (hnormalH0 : (H0.subgroupOf MF).Normal) →
                    (hbarElem :
                      letI : (H0.subgroupOf MF).Normal := hnormalH0
                      IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF)) →
                    (letI : Fact p.Prime := ⟨hpprime⟩
                    letI : (H0.subgroupOf MF).Normal := hnormalH0
                    letI : IsElementaryAbelian p
                      (MF ⧸ H0.subgroupOf MF) := hbarElem
                    Module.finrank (ZMod p)
                      (Additive (MF ⧸ H0.subgroupOf MF)) = q) →
                    (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G)) →
                    (hH0invU :
                      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                      IsInvariant U MF (H0.subgroupOf MF)) →
                    (hnormalC : (C.subgroupOf U).Normal) →
                      (letI : (C.subgroupOf U).Normal := hnormalC
                      IsMulCommutative (U ⧸ C.subgroupOf U)) →
                    (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G)) →
                    (hCinv :
                        letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
                        IsInvariant W1 U (C.subgroupOf U)) →
                    (w0 : W1) →
                    (hw0gen : Subgroup.zpowers w0 = ⊤) →
                    letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
                    letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
                      quotientMulDistribMulAction (A := W1) (G := U)
                        (C.subgroupOf U) hCinv
                    letI : (C.subgroupOf U).Normal := hnormalC
                    ∀ Q : Subgroup (MF ⧸ H0.subgroupOf MF),
                      quotientSubgroupNormalizedBy MF H0 U Q →
                        Q ≠ ⊥ →
                          Q ≠ ⊤ →
                            ¬ quotientSubgroupNormalizedBy MF H0 W1 Q →
                            letI : (H0.subgroupOf MF).Normal := hnormalH0
                            ∀ H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF),
                              (∀ i, Nat.card (H i) = p) →
                              (∀ i, quotientSubgroupNormalizedBy MF H0 U (H i)) →
                              iSupIndep H →
                              iSup H = ⊤ →
                              (∀ i, quotientFactorActionCentralizerData MF H0 U C
                                (H i) a) →
                              (∀ i : Fin q,
                                quotientSubgroupConjugateByElement MF H0
                                  (H i)
                                  (H (theorem_9_7_fin_cyclic_succ_sec9
                                    hqprime.pos i)) (w0 : G)) →
                              theorem_9_7_orderedCliffordCharacterTransitionData_sec9
                                MF H0 U W1 C q a hnormalC w0 H hqprime.pos := by
  classical
  intro h92 _hp96 _hC _hBarU _hpprime hqprime hnormalH0 _hbarElem _hbarFinrank
    _hUnormMF _hH0invU hnormalC _hbarComm hW1normU hCinv w0 hw0gen Q
    _hQnorm _hQneBot _hQneTop _hQnotW1 H _hcard _hUnorm _hindep _hSup hfac
    hsucc
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
  have hW1card : Nat.card W1 = q := by
    exact h92.q_eq
  exact
    theorem_9_7_orderedCliffordCharacterTransitionData_of_ordered_components_source_bridge_sec9
      (MF := MF) (H0 := H0) (U := U) (W1 := W1) (C := C)
      (q := q) (a := a) hnormalC hCinv w0 H hqprime.pos hW1card hw0gen
      hfac hsucc

private theorem
    theorem_9_7_clifford_case_a_quotient_component_generator_character_transition_ordered_from_reducible_factor_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
          quotientChiefFactorData_9_6 M MF H0 W1 hp) →
          quotientCentralizerIn MF H0 U C →
            quotientBarUCardinality U C u →
              (hpprime : Nat.Prime p) →
                (hqprime : Nat.Prime q) →
                  (hnormalH0 : (H0.subgroupOf MF).Normal) →
                    (hbarElem :
                      letI : (H0.subgroupOf MF).Normal := hnormalH0
                      IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF)) →
                    (letI : Fact p.Prime := ⟨hpprime⟩
                    letI : (H0.subgroupOf MF).Normal := hnormalH0
                    letI : IsElementaryAbelian p
                      (MF ⧸ H0.subgroupOf MF) := hbarElem
                    Module.finrank (ZMod p)
                      (Additive (MF ⧸ H0.subgroupOf MF)) = q) →
                    (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G)) →
                    (hH0invU :
                      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                      IsInvariant U MF (H0.subgroupOf MF)) →
                    (hnormalC : (C.subgroupOf U).Normal) →
                      (letI : (C.subgroupOf U).Normal := hnormalC
                      IsMulCommutative (U ⧸ C.subgroupOf U)) →
                    (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G)) →
                    (hCinv :
                        letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
                        IsInvariant W1 U (C.subgroupOf U)) →
                    (w0 : W1) →
                    (hw0gen : Subgroup.zpowers w0 = ⊤) →
                    letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
                    letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
                      quotientMulDistribMulAction (A := W1) (G := U)
                        (C.subgroupOf U) hCinv
                    letI : (C.subgroupOf U).Normal := hnormalC
                    ∀ Q : Subgroup (MF ⧸ H0.subgroupOf MF),
                      quotientSubgroupNormalizedBy MF H0 U Q →
                        Q ≠ ⊥ →
                          Q ≠ ⊤ →
                            ¬ quotientSubgroupNormalizedBy MF H0 W1 Q →
                            ∃ a : ℕ,
                      letI : (H0.subgroupOf MF).Normal := hnormalH0
                      ∃ H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF),
                          (∀ i, Nat.card (H i) = p) ∧
                            (∀ i, quotientSubgroupNormalizedBy MF H0 U (H i)) ∧
                            iSupIndep H ∧
                            iSup H = ⊤ ∧
                            (∀ i, quotientFactorActionCentralizerData MF H0 U C
                              (H i) a) ∧
                            (∀ i : Fin q,
                              quotientSubgroupConjugateByElement MF H0
                                (H i)
                                (H (theorem_9_7_fin_cyclic_succ_sec9
                                  hqprime.pos i)) (w0 : G)) ∧
                            ∃ χbar : Fin q →
                                (U ⧸ C.subgroupOf U) →* Multiplicative (ZMod a),
                              (∀ i,
                                ∃ ρ : (U ⧸ C.subgroupOf U) →* MulAut (H i),
                                  IsCyclic ρ.range ∧
                                    Nat.card ρ.range = a ∧
                                    (∀ x : U ⧸ C.subgroupOf U,
                                      ∀ u : U,
                                        QuotientGroup.mk' (C.subgroupOf U) u = x →
                                        ∃ hconjMF : ∀ h : MF,
                                          (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
                                          ∀ h : MF,
                                          ∀ hhQ :
                                            QuotientGroup.mk'
                                              (H0.subgroupOf MF) h ∈ H i,
                                            (ρ x
                                              ⟨QuotientGroup.mk'
                                                (H0.subgroupOf MF) h, hhQ⟩ :
                                                MF ⧸ H0.subgroupOf MF) =
                                              QuotientGroup.mk'
                                                (H0.subgroupOf MF)
                                                ⟨(u : G)⁻¹ * (h : G) * (u : G),
                                                  hconjMF h⟩) ∧
                                    (∀ x : U ⧸ C.subgroupOf U,
                                      ρ x = 1 ↔
                                        ∀ u : U,
                                          QuotientGroup.mk' (C.subgroupOf U) u =
                                            x →
                                          quotientSubgroupCentralizedByElement
                                            MF H0 (H i) (u : G)) ∧
                                    ∀ x y : U ⧸ C.subgroupOf U,
                                      χbar i x = χbar i y → ρ x = ρ y) ∧
                                ∀ x : U,
                                  ∀ i,
                                    χbar i
                                        (QuotientGroup.mk' (C.subgroupOf U)
                                          (w0 • x)) =
                                      χbar
                                        (theorem_9_7_fin_cyclic_succ_sec9
                                          hqprime.pos i)
                                        (QuotientGroup.mk' (C.subgroupOf U) x) := by
  classical
  intro h92 hp96 hC hBarU hpprime hqprime hnormalH0 hbarElem hbarFinrank
    hUnormMF hH0invU hnormalC hbarComm hW1normU hCinv w0 hw0gen Q hQnorm
    hQneBot hQneTop hQnotW1
  letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
  letI : (C.subgroupOf U).Normal := hnormalC
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  rcases
      theorem_9_7_clifford_case_a_quotient_component_ordered_decomposition_from_reducible_factor_source_bridge_sec9
        M MF U W1 W2 H0 C p q u h92 hp96 hC hBarU hpprime hqprime
        hnormalH0 hbarElem hbarFinrank hUnormMF hH0invU hnormalC hbarComm
        hW1normU hCinv w0 hw0gen Q hQnorm hQneBot hQneTop hQnotW1 with
    ⟨a, H, hcard, hUnorm, hindep, hSup, hfac, hsucc⟩
  rcases
      theorem_9_7_clifford_case_a_quotient_component_character_transition_from_ordered_decomposition_source_bridge_sec9
        M MF U W1 W2 H0 C p q u a h92 hp96 hC hBarU hpprime hqprime
        hnormalH0 hbarElem hbarFinrank hUnormMF hH0invU hnormalC hbarComm
        hW1normU hCinv w0 hw0gen Q hQnorm hQneBot hQneTop hQnotW1 H
        hcard hUnorm hindep hSup hfac hsucc with
    ⟨χbar, hχdata, hχtransition⟩
  exact
    ⟨a, H, hcard, hUnorm, hindep, hSup, hfac, hsucc, χbar, hχdata,
      hχtransition⟩

private theorem
    theorem_9_7_clifford_case_a_quotient_component_generator_character_transition_ordered_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
          quotientChiefFactorData_9_6 M MF H0 W1 hp) →
          quotientCentralizerIn MF H0 U C →
            quotientBarUCardinality U C u →
              (hpprime : Nat.Prime p) →
                (hqprime : Nat.Prime q) →
                  (hnormalH0 : (H0.subgroupOf MF).Normal) →
                    (hbarElem :
                      letI : (H0.subgroupOf MF).Normal := hnormalH0
                      IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF)) →
                    (letI : Fact p.Prime := ⟨hpprime⟩
                    letI : (H0.subgroupOf MF).Normal := hnormalH0
                    letI : IsElementaryAbelian p
                      (MF ⧸ H0.subgroupOf MF) := hbarElem
                    Module.finrank (ZMod p)
                      (Additive (MF ⧸ H0.subgroupOf MF)) = q) →
                    (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G)) →
                    (hH0invU :
                      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                      IsInvariant U MF (H0.subgroupOf MF)) →
                    (hnormalC : (C.subgroupOf U).Normal) →
                      (letI : (C.subgroupOf U).Normal := hnormalC
                      IsMulCommutative (U ⧸ C.subgroupOf U)) →
                    (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G)) →
                    (hCinv :
                        letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
                        IsInvariant W1 U (C.subgroupOf U)) →
                    (w0 : W1) →
                    (hw0gen : Subgroup.zpowers w0 = ⊤) →
                    letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
                    letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
                      quotientMulDistribMulAction (A := W1) (G := U)
                        (C.subgroupOf U) hCinv
                    letI : (C.subgroupOf U).Normal := hnormalC
                    ∀ Q : Subgroup (MF ⧸ H0.subgroupOf MF),
                      quotientSubgroupNormalizedBy MF H0 U Q →
                        Q ≠ ⊥ →
                          Q ≠ ⊤ →
                            ¬ quotientSubgroupNormalizedBy MF H0 W1 Q →
                            ∃ a : ℕ,
                      letI : (H0.subgroupOf MF).Normal := hnormalH0
                      ∃ H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF),
                          (∀ i, Nat.card (H i) = p) ∧
                            (∀ i, quotientSubgroupNormalizedBy MF H0 U (H i)) ∧
                            iSupIndep H ∧
                            iSup H = ⊤ ∧
                            (∀ i, quotientFactorActionCentralizerData MF H0 U C
                              (H i) a) ∧
                            (∀ i : Fin q,
                              quotientSubgroupConjugateByElement MF H0 (H i)
                                (H (theorem_9_7_fin_cyclic_succ_sec9
                                  hqprime.pos i)) (w0 : G)) ∧
                            ∃ χbar : Fin q →
                                (U ⧸ C.subgroupOf U) →* Multiplicative (ZMod a),
                              (∀ i,
                                ∃ ρ : (U ⧸ C.subgroupOf U) →* MulAut (H i),
                                  IsCyclic ρ.range ∧
                                    Nat.card ρ.range = a ∧
                                    (∀ x : U ⧸ C.subgroupOf U,
                                      ∀ u : U,
                                        QuotientGroup.mk' (C.subgroupOf U) u = x →
                                        ∃ hconjMF : ∀ h : MF,
                                          (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
                                          ∀ h : MF,
                                          ∀ hhQ :
                                            QuotientGroup.mk'
                                              (H0.subgroupOf MF) h ∈ H i,
                                            (ρ x
                                              ⟨QuotientGroup.mk'
                                                (H0.subgroupOf MF) h, hhQ⟩ :
                                                MF ⧸ H0.subgroupOf MF) =
                                              QuotientGroup.mk'
                                                (H0.subgroupOf MF)
                                                ⟨(u : G)⁻¹ * (h : G) * (u : G),
                                                  hconjMF h⟩) ∧
                                    (∀ x : U ⧸ C.subgroupOf U,
                                      ρ x = 1 ↔
                                        ∀ u : U,
                                          QuotientGroup.mk' (C.subgroupOf U) u =
                                            x →
                                          quotientSubgroupCentralizedByElement
                                            MF H0 (H i) (u : G)) ∧
                                    ∀ x y : U ⧸ C.subgroupOf U,
                                      χbar i x = χbar i y → ρ x = ρ y) ∧
                                ∀ x : U,
                                  ∀ i,
                                    χbar i
                                        (QuotientGroup.mk' (C.subgroupOf U)
                                          (w0 • x)) =
                                      χbar
                                        (theorem_9_7_fin_cyclic_succ_sec9
                                          hqprime.pos i)
                                        (QuotientGroup.mk' (C.subgroupOf U) x) := by
  exact
    theorem_9_7_clifford_case_a_quotient_component_generator_character_transition_ordered_from_reducible_factor_source_bridge_sec9
      M MF U W1 W2 H0 C p q u

private theorem
    theorem_9_7_clifford_case_a_quotient_component_generator_character_transition_from_reducible_factor_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
          quotientChiefFactorData_9_6 M MF H0 W1 hp) →
          quotientCentralizerIn MF H0 U C →
            quotientBarUCardinality U C u →
              (hpprime : Nat.Prime p) →
                (hqprime : Nat.Prime q) →
                  (hnormalH0 : (H0.subgroupOf MF).Normal) →
                    (hbarElem :
                      letI : (H0.subgroupOf MF).Normal := hnormalH0
                      IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF)) →
                    (letI : Fact p.Prime := ⟨hpprime⟩
                    letI : (H0.subgroupOf MF).Normal := hnormalH0
                    letI : IsElementaryAbelian p
                      (MF ⧸ H0.subgroupOf MF) := hbarElem
                    Module.finrank (ZMod p)
                      (Additive (MF ⧸ H0.subgroupOf MF)) = q) →
                    (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G)) →
                    (hH0invU :
                      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                      IsInvariant U MF (H0.subgroupOf MF)) →
                    (hnormalC : (C.subgroupOf U).Normal) →
                      (letI : (C.subgroupOf U).Normal := hnormalC
                      IsMulCommutative (U ⧸ C.subgroupOf U)) →
                    (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G)) →
                    (hCinv :
                        letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
                        IsInvariant W1 U (C.subgroupOf U)) →
                    (w0 : W1) →
                    (hw0gen : Subgroup.zpowers w0 = ⊤) →
                    letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
                    letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
                      quotientMulDistribMulAction (A := W1) (G := U)
                        (C.subgroupOf U) hCinv
                    letI : (C.subgroupOf U).Normal := hnormalC
                    ∀ Q : Subgroup (MF ⧸ H0.subgroupOf MF),
                      quotientSubgroupNormalizedBy MF H0 U Q →
                        Q ≠ ⊥ →
                          Q ≠ ⊤ →
                            ¬ quotientSubgroupNormalizedBy MF H0 W1 Q →
                            ∃ a : ℕ,
                      letI : (H0.subgroupOf MF).Normal := hnormalH0
                      ∃ H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF),
                          (∀ i, Nat.card (H i) = p) ∧
                            (∀ i, quotientSubgroupNormalizedBy MF H0 U (H i)) ∧
                            iSupIndep H ∧
                            iSup H = ⊤ ∧
                            (∀ i, quotientFactorActionCentralizerData MF H0 U C
                              (H i) a) ∧
                            (∃ hqpos : 0 < q,
                              ∀ i : Fin q,
                                ∃ w : W1,
                                  quotientSubgroupConjugateByElement MF H0
                                    (H ⟨0, hqpos⟩) (H i) (w : G)) ∧
                            ∃ χbar : Fin q →
                                (U ⧸ C.subgroupOf U) →* Multiplicative (ZMod a),
                              (∀ i,
                                ∃ ρ : (U ⧸ C.subgroupOf U) →* MulAut (H i),
                                  IsCyclic ρ.range ∧
                                    Nat.card ρ.range = a ∧
                                    (∀ x : U ⧸ C.subgroupOf U,
                                      ∀ u : U,
                                        QuotientGroup.mk' (C.subgroupOf U) u = x →
                                        ∃ hconjMF : ∀ h : MF,
                                          (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
                                          ∀ h : MF,
                                          ∀ hhQ :
                                            QuotientGroup.mk'
                                              (H0.subgroupOf MF) h ∈ H i,
                                            (ρ x
                                              ⟨QuotientGroup.mk'
                                                (H0.subgroupOf MF) h, hhQ⟩ :
                                                MF ⧸ H0.subgroupOf MF) =
                                              QuotientGroup.mk'
                                                (H0.subgroupOf MF)
                                                ⟨(u : G)⁻¹ * (h : G) * (u : G),
                                                  hconjMF h⟩) ∧
                                    (∀ x : U ⧸ C.subgroupOf U,
                                      ρ x = 1 ↔
                                        ∀ u : U,
                                          QuotientGroup.mk' (C.subgroupOf U) u =
                                            x →
                                          quotientSubgroupCentralizedByElement
                                            MF H0 (H i) (u : G)) ∧
                                    ∀ x y : U ⧸ C.subgroupOf U,
                                      χbar i x = χbar i y → ρ x = ρ y) ∧
                                ∀ x : U,
                                  ∀ i,
                                    χbar i
                                        (QuotientGroup.mk' (C.subgroupOf U)
                                          (w0 • x)) =
                                      χbar
                                        (theorem_9_7_fin_cyclic_succ_sec9
                                          hqprime.pos i)
                                        (QuotientGroup.mk' (C.subgroupOf U) x) := by
  classical
  intro h92 hp96 hC hBarU hpprime hqprime hnormalH0 hbarElem hbarFinrank
    hUnormMF hH0invU hnormalC hbarComm hW1normU hCinv w0 hw0gen Q hQnorm
    hQneBot hQneTop hQnotW1
  letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
  letI : (C.subgroupOf U).Normal := hnormalC
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  rcases
      theorem_9_7_clifford_case_a_quotient_component_generator_character_transition_ordered_source_bridge_sec9
        M MF U W1 W2 H0 C p q u h92 hp96 hC hBarU hpprime hqprime
        hnormalH0 hbarElem hbarFinrank hUnormMF hH0invU hnormalC hbarComm
        hW1normU hCinv w0 hw0gen Q hQnorm hQneBot hQneTop hQnotW1 with
    ⟨a, H, hcard, hUnorm, hindep, hSup, hfac, hsucc, χbar, hχdata,
      hχtransition⟩
  refine ⟨a, H, hcard, hUnorm, hindep, hSup, hfac, ?_, χbar, hχdata,
    hχtransition⟩
  exact
    ⟨hqprime.pos,
      theorem_9_7_weak_orbit_of_successor_conjugates_sec9
        (MF := MF) (H0 := H0) (W1 := W1) hqprime.pos H w0 hsucc⟩

@[expose] public def theorem_9_7_orderedCaseAComponentTransitionData_sec9
    {G : Type u} [Group G] [Finite G]
    (MF H0 U W1 C : Subgroup G)
    (p q : ℕ) : Prop :=
  ∃ a : ℕ,
    ∃ hnormalH0 : (H0.subgroupOf MF).Normal,
      letI : (H0.subgroupOf MF).Normal := hnormalH0
      ∃ hW1normU : W1 ≤ Subgroup.normalizer (U : Set G),
        letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
      ∃ hnormalC : (C.subgroupOf U).Normal,
        letI : (C.subgroupOf U).Normal := hnormalC
        ∃ w0 : W1,
          Subgroup.zpowers w0 = ⊤ ∧
            ∃ H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF),
              (∀ i, Nat.card (H i) = p) ∧
                (∀ i, quotientSubgroupNormalizedBy MF H0 U (H i)) ∧
                iSupIndep H ∧
                iSup H = ⊤ ∧
                (∀ i, quotientFactorActionCentralizerData MF H0 U C (H i) a) ∧
                ∃ hqpos : 0 < q,
                  (∀ i : Fin q,
                    quotientSubgroupConjugateByElement MF H0
                      (H i) (H (theorem_9_7_fin_cyclic_succ_sec9 hqpos i))
                      (w0 : G)) ∧
                    ∃ χbar : Fin q →
                        (U ⧸ C.subgroupOf U) →* Multiplicative (ZMod a),
                      (∀ i,
                        ∃ ρ : (U ⧸ C.subgroupOf U) →* MulAut (H i),
                          IsCyclic ρ.range ∧
                            Nat.card ρ.range = a ∧
                            (∀ x : U ⧸ C.subgroupOf U,
                              ∀ u : U,
                                QuotientGroup.mk' (C.subgroupOf U) u = x →
                                ∃ hconjMF : ∀ h : MF,
                                  (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
                                  ∀ h : MF,
                                  ∀ hhQ :
                                    QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H i,
                                    (ρ x
                                      ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                                        MF ⧸ H0.subgroupOf MF) =
                                      QuotientGroup.mk' (H0.subgroupOf MF)
                                        ⟨(u : G)⁻¹ * (h : G) * (u : G),
                                          hconjMF h⟩) ∧
                            (∀ x : U ⧸ C.subgroupOf U,
                              ρ x = 1 ↔
                                ∀ u : U,
                                  QuotientGroup.mk' (C.subgroupOf U) u = x →
                                  quotientSubgroupCentralizedByElement
                                    MF H0 (H i) (u : G)) ∧
                            ∀ x y : U ⧸ C.subgroupOf U,
                              χbar i x = χbar i y → ρ x = ρ y) ∧
                      ∀ x : U,
                        ∀ i,
                          χbar i (QuotientGroup.mk' (C.subgroupOf U) (w0 • x)) =
                            χbar (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)
                              (QuotientGroup.mk' (C.subgroupOf U) x)

public theorem theorem_9_7_orderedCaseAComponentTransitionData_of_case_a_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a u : ℕ) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        theorem_9_7_orderedCaseAComponentTransitionData_sec9 MF H0 U W1 C p q := by
  classical
  intro hcase hBarU
  have h92 : hypothesis_9_2_statement M MF U W1 W2 q :=
    case_9_7_a_hypothesis_9_2_sec9 hcase
  have hC : quotientCentralizerIn MF H0 U C :=
    case_9_7_a_quotientCentralizerIn_sec9 hcase
  have hpprime : Nat.Prime p := case_9_7_a_p_prime_sec9 hcase
  have hqprime : Nat.Prime q := case_9_7_a_q_prime_sec9 hcase
  have hp96 :
      ∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
            quotientChiefFactorData_9_6 M MF H0 W1 hp := by
    rcases hcase with
      ⟨_h92, _hH0MF, _hC, _hpprime, _hqprime, hpData, _hrest⟩
    exact hpData
  have hp96Full :
      ∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
            quotientChiefFactorData_9_6 M MF H0 W1 hp := hp96
  rcases hcase with
    ⟨_h92, _hH0MF, _hC, _hpprime, _hqprime, _hpData, hdecomp, _hcard,
      _hadiv, hinj⟩
  rcases hdecomp with
    ⟨hnormalH0, Hweak, _hHcardWeak, _hHnormWeak, _hHindepWeak, _hHsupWeak,
      _hfacWeak, hweakConj⟩
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  rcases hinj with ⟨_hCU, hnormalC, _φ, _hφinj⟩
  letI : (C.subgroupOf U).Normal := hnormalC
  rcases hp96 with ⟨hp, hp_eq, hpData, h96⟩
  rcases h96 with ⟨hH0MF96, hMFM96, hnormalH096, hchief96, hWbar96, hcardRaw96⟩
  have hpDataFull : hoReductionData M MF U W2 H0 hp := hpData
  rcases hpData with
    ⟨_hH0MF_hp, _hMFM_hp, hH0normalM_hp, _hH0normalMF_hp, _hH0lt_hp,
      hbarElemRaw, _htypeIIIIVData_hp⟩
  rcases hbarElemRaw with ⟨_hnormalElem, hbarElemRaw⟩
  have hbarElem :
      (letI : (H0.subgroupOf MF).Normal := hnormalH0;
        IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF)) := by
    letI : (H0.subgroupOf MF).Normal := hnormalH0
    simpa [hp_eq] using hbarElemRaw
  have hbarCard :
      (letI : (H0.subgroupOf MF).Normal := hnormalH0;
        Nat.card (MF ⧸ H0.subgroupOf MF) = p ^ q) := by
    letI : (H0.subgroupOf MF).Normal := hnormalH0
    simpa using
      theorem_9_7_quotient_cardinality_from_chief_data_sec9 h92 hp_eq
        ⟨hH0MF96, hMFM96, hnormalH096, hchief96, hWbar96, hcardRaw96⟩
  have hbarFinrank :
      letI : Fact p.Prime := ⟨hpprime⟩
      letI : (H0.subgroupOf MF).Normal := hnormalH0
      letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
      Module.finrank (ZMod p) (Additive (MF ⧸ H0.subgroupOf MF)) = q := by
    exact theorem_9_7_quotient_finrank_eq_q_sec9 hpprime hnormalH0 hbarElem hbarCard
  have hUnormMF : U ≤ Subgroup.normalizer (MF : Set G) := by
    have hUW1normMF :
        (U ⊔ W1 : Subgroup G) ≤ Subgroup.normalizer (MF : Set G) :=
      (theorem_9_3_action_normalizes_and_solvable_sec9 M MF U W1 W2 q h92).1
    exact le_sup_left.trans hUW1normMF
  have hH0invU :
      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
      IsInvariant U MF (H0.subgroupOf MF) := by
    letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
    have hUleM : U ≤ M := by
      rcases h92.typePDefinitionData with
        ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, hUleD,
          _hUnil, _hW1normU, _hcompDU, _hMFnotcyc, _hsecond, _hfitEq,
          _hfitLeD, _hW2le, _hW2cyc, _hW2ne, _hcentW1, _hnormX⟩
      exact hUleD.trans section12_ambientDerivedSubgroup_le
    exact
      subgroupOf_MF_isInvariant_of_subgroupOf_M_normal_sec9 M MF U H0
        hMFM96 hUleM hH0normalM_hp hUnormMF
  have hbarComm :
      letI : (C.subgroupOf U).Normal := hnormalC
      IsMulCommutative (U ⧸ C.subgroupOf U) :=
    theorem_9_7_barU_isMulCommutative_sec9 h92 hC hnormalC
  have hW1normU : W1 ≤ Subgroup.normalizer (U : Set G) :=
    theorem_9_7_W1_le_normalizer_U_of_hypothesis_9_2_sec9 h92
  have hW1normMF : W1 ≤ Subgroup.normalizer (MF : Set G) :=
    theorem_9_7_W1_le_normalizer_MF_of_hypothesis_9_2_sec9 h92
  have hCinv :
      letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
      IsInvariant W1 U (C.subgroupOf U) := by
    letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
    exact theorem_9_7_quotientCentralizerIn_isInvariant_W1_sec9 h92 hpDataFull hC
      hW1normU hW1normMF
  have hW1cyc : IsCyclic W1 := by
    rcases h92.typePDefinitionData with
      ⟨_hMFsource, hW1cyc, _hW1ne, _hrest⟩
    exact hW1cyc
  letI : IsCyclic W1 := hW1cyc
  rcases IsCyclic.exists_generator (α := W1) with ⟨w0, hw0mem⟩
  have hw0gen : Subgroup.zpowers w0 = ⊤ :=
    eq_top_iff.mpr (fun w _hw => hw0mem w)
  rcases hweakConj with ⟨hqposWeak, _hworbit⟩
  let Q : Subgroup (MF ⧸ H0.subgroupOf MF) := Hweak ⟨0, hqposWeak⟩
  have hQnorm : quotientSubgroupNormalizedBy MF H0 U Q := by
    dsimp [Q]
    exact _hHnormWeak ⟨0, hqposWeak⟩
  have hQneBot : Q ≠ ⊥ := by
    dsimp [Q]
    intro hbot
    have hcardBot : Nat.card (Hweak ⟨0, hqposWeak⟩) =
        Nat.card (⊥ : Subgroup (MF ⧸ H0.subgroupOf MF)) := by
      rw [hbot]
    have hpone : p = 1 := by
      rw [_hHcardWeak ⟨0, hqposWeak⟩] at hcardBot
      simpa using hcardBot
    exact hpprime.ne_one hpone
  have hQneTop : Q ≠ ⊤ := by
    dsimp [Q]
    intro htop
    have hcardTop : Nat.card (Hweak ⟨0, hqposWeak⟩) =
        Nat.card (MF ⧸ H0.subgroupOf MF) := by
      calc
        Nat.card (Hweak ⟨0, hqposWeak⟩) =
            Nat.card (⊤ : Subgroup (MF ⧸ H0.subgroupOf MF)) := by rw [htop]
        _ = Nat.card (MF ⧸ H0.subgroupOf MF) := Subgroup.card_top
    have hp_eq_pow : p = p ^ q := by
      rw [_hHcardWeak ⟨0, hqposWeak⟩, hbarCard] at hcardTop
      exact hcardTop
    have hpow_gt : p < p ^ q := by
      simpa using Nat.pow_lt_pow_right hpprime.one_lt hqprime.one_lt
    exact (Nat.ne_of_lt hpow_gt) hp_eq_pow
  have hQnotW1 : ¬ quotientSubgroupNormalizedBy MF H0 W1 Q :=
    quotientSubgroup_not_W1_normalized_of_proper_U_normalized_quotientChiefFactorData_sec9
      M MF U W1 W2 H0 q hp h92 hpDataFull
      ⟨hH0MF96, hMFM96, hnormalH096, hchief96, hWbar96, hcardRaw96⟩
      hnormalH0 Q hQnorm hQneBot hQneTop
  letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
  letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
    quotientMulDistribMulAction (A := W1) (G := U) (C.subgroupOf U) hCinv
  rcases
      theorem_9_7_clifford_case_a_quotient_component_generator_character_transition_ordered_source_bridge_sec9
        M MF U W1 W2 H0 C p q u h92 hp96Full hC hBarU hpprime hqprime
        hnormalH0 hbarElem hbarFinrank hUnormMF hH0invU hnormalC hbarComm
        hW1normU hCinv w0 hw0gen Q hQnorm hQneBot hQneTop hQnotW1 with
    ⟨a0, H, hHcard, hHnorm, hHindep, hHsup, hfac, hsucc, χbar, hχdata,
      hχtransition⟩
  exact
    ⟨a0, hnormalH0, hW1normU, hnormalC, w0, hw0gen, H, hHcard, hHnorm, hHindep,
      hHsup, hfac, hqprime.pos, hsucc, χbar, hχdata, hχtransition⟩

private theorem
    theorem_9_7_clifford_case_a_quotient_component_generator_character_agreement_from_reducible_factor_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
          quotientChiefFactorData_9_6 M MF H0 W1 hp) →
          quotientCentralizerIn MF H0 U C →
            quotientBarUCardinality U C u →
              (hpprime : Nat.Prime p) →
                (hqprime : Nat.Prime q) →
                  (hnormalH0 : (H0.subgroupOf MF).Normal) →
                    (hbarElem :
                      letI : (H0.subgroupOf MF).Normal := hnormalH0
                      IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF)) →
                    (letI : Fact p.Prime := ⟨hpprime⟩
                    letI : (H0.subgroupOf MF).Normal := hnormalH0
                    letI : IsElementaryAbelian p
                      (MF ⧸ H0.subgroupOf MF) := hbarElem
                    Module.finrank (ZMod p)
                      (Additive (MF ⧸ H0.subgroupOf MF)) = q) →
                    (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G)) →
                    (hH0invU :
                      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                      IsInvariant U MF (H0.subgroupOf MF)) →
                    (hnormalC : (C.subgroupOf U).Normal) →
                      (letI : (C.subgroupOf U).Normal := hnormalC
                      IsMulCommutative (U ⧸ C.subgroupOf U)) →
                    (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G)) →
                    (hCinv :
                        letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
                        IsInvariant W1 U (C.subgroupOf U)) →
                    (w0 : W1) →
                    (hw0gen : Subgroup.zpowers w0 = ⊤) →
                    letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
                    letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
                      quotientMulDistribMulAction (A := W1) (G := U)
                        (C.subgroupOf U) hCinv
                    letI : (C.subgroupOf U).Normal := hnormalC
                    ∀ Q : Subgroup (MF ⧸ H0.subgroupOf MF),
                      quotientSubgroupNormalizedBy MF H0 U Q →
                        Q ≠ ⊥ →
                          Q ≠ ⊤ →
                            ¬ quotientSubgroupNormalizedBy MF H0 W1 Q →
                            ∃ a : ℕ,
                      letI : (H0.subgroupOf MF).Normal := hnormalH0
                      ∃ H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF),
                          (∀ i, Nat.card (H i) = p) ∧
                            (∀ i, quotientSubgroupNormalizedBy MF H0 U (H i)) ∧
                            iSupIndep H ∧
                            iSup H = ⊤ ∧
                            (∀ i, quotientFactorActionCentralizerData MF H0 U C
                              (H i) a) ∧
                            (∃ hqpos : 0 < q,
                              ∀ i : Fin q,
                                ∃ w : W1,
                                  quotientSubgroupConjugateByElement MF H0
                                    (H ⟨0, hqpos⟩) (H i) (w : G)) ∧
                            ∃ χbar : Fin q →
                                (U ⧸ C.subgroupOf U) →* Multiplicative (ZMod a),
                              (∀ i,
                                ∃ ρ : (U ⧸ C.subgroupOf U) →* MulAut (H i),
                                  IsCyclic ρ.range ∧
                                    Nat.card ρ.range = a ∧
                                    (∀ x : U ⧸ C.subgroupOf U,
                                      ∀ u : U,
                                        QuotientGroup.mk' (C.subgroupOf U) u = x →
                                        ∃ hconjMF : ∀ h : MF,
                                          (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
                                          ∀ h : MF,
                                          ∀ hhQ :
                                            QuotientGroup.mk'
                                              (H0.subgroupOf MF) h ∈ H i,
                                            (ρ x
                                              ⟨QuotientGroup.mk'
                                                (H0.subgroupOf MF) h, hhQ⟩ :
                                                MF ⧸ H0.subgroupOf MF) =
                                              QuotientGroup.mk'
                                                (H0.subgroupOf MF)
                                                ⟨(u : G)⁻¹ * (h : G) * (u : G),
                                                  hconjMF h⟩) ∧
                                    (∀ x : U ⧸ C.subgroupOf U,
                                      ρ x = 1 ↔
                                        ∀ u : U,
                                          QuotientGroup.mk' (C.subgroupOf U) u =
                                            x →
                                          quotientSubgroupCentralizedByElement
                                            MF H0 (H i) (u : G)) ∧
                                    ∀ x y : U ⧸ C.subgroupOf U,
                                      χbar i x = χbar i y → ρ x = ρ y) ∧
                                ∀ x : U,
                                  (∀ j : Fin (q - 1),
                                    ((χbar
                                      (theorem_9_7_fin_succ_of_sub_one_sec9
                                        hqprime.pos j)).comp
                                        (QuotientGroup.mk'
                                          (C.subgroupOf U))) x =
                                      ((χbar ⟨0, hqprime.pos⟩).comp
                                        (QuotientGroup.mk'
                                          (C.subgroupOf U))) x) →
                                  ∀ i,
                                    χbar i
                                        (QuotientGroup.mk' (C.subgroupOf U)
                                          (w0 • x)) =
                                      χbar i
                                        (QuotientGroup.mk' (C.subgroupOf U) x) := by
  classical
  intro h92 hp96 hC hBarU hpprime hqprime hnormalH0 hbarElem hbarFinrank
    hUnormMF hH0invU hnormalC hbarComm hW1normU hCinv w0 hw0gen Q hQnorm
    hQneBot hQneTop hQnotW1
  letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
  letI : (C.subgroupOf U).Normal := hnormalC
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  rcases
      theorem_9_7_clifford_case_a_quotient_component_generator_character_transition_from_reducible_factor_source_bridge_sec9
        M MF U W1 W2 H0 C p q u h92 hp96 hC hBarU hpprime hqprime
        hnormalH0 hbarElem hbarFinrank hUnormMF hH0invU hnormalC hbarComm
        hW1normU hCinv w0 hw0gen Q hQnorm hQneBot hQneTop hQnotW1 with
    ⟨a, H, hcard, hUnorm, hindep, hSup, hfac, horbit, χbar, hχdata,
      hχtransition⟩
  refine ⟨a, H, hcard, hUnorm, hindep, hSup, hfac, horbit, χbar, hχdata, ?_⟩
  intro x hx
  exact
    theorem_9_7_component_character_generator_agreement_of_transition_sec9
      hqprime.pos (fun i y => χbar i y)
      (QuotientGroup.mk' (C.subgroupOf U) x)
      (QuotientGroup.mk' (C.subgroupOf U) (w0 • x))
      (hχtransition x) hx

private theorem
    theorem_9_7_clifford_case_a_quotient_component_generator_action_agreement_from_reducible_factor_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
          quotientChiefFactorData_9_6 M MF H0 W1 hp) →
          quotientCentralizerIn MF H0 U C →
            quotientBarUCardinality U C u →
              (hpprime : Nat.Prime p) →
                (hqprime : Nat.Prime q) →
                  (hnormalH0 : (H0.subgroupOf MF).Normal) →
                    (hbarElem :
                      letI : (H0.subgroupOf MF).Normal := hnormalH0
                      IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF)) →
                    (letI : Fact p.Prime := ⟨hpprime⟩
                    letI : (H0.subgroupOf MF).Normal := hnormalH0
                    letI : IsElementaryAbelian p
                      (MF ⧸ H0.subgroupOf MF) := hbarElem
                    Module.finrank (ZMod p)
                      (Additive (MF ⧸ H0.subgroupOf MF)) = q) →
                    (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G)) →
                    (hH0invU :
                      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                      IsInvariant U MF (H0.subgroupOf MF)) →
                    (hnormalC : (C.subgroupOf U).Normal) →
                      (letI : (C.subgroupOf U).Normal := hnormalC
                      IsMulCommutative (U ⧸ C.subgroupOf U)) →
                    (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G)) →
                    (hCinv :
                        letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
                        IsInvariant W1 U (C.subgroupOf U)) →
                    (w0 : W1) →
                    (hw0gen : Subgroup.zpowers w0 = ⊤) →
                    letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
                    letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
                      quotientMulDistribMulAction (A := W1) (G := U)
                        (C.subgroupOf U) hCinv
                    letI : (C.subgroupOf U).Normal := hnormalC
                    ∀ Q : Subgroup (MF ⧸ H0.subgroupOf MF),
                      quotientSubgroupNormalizedBy MF H0 U Q →
                        Q ≠ ⊥ →
                          Q ≠ ⊤ →
                            ¬ quotientSubgroupNormalizedBy MF H0 W1 Q →
                            ∃ a : ℕ,
                      letI : (H0.subgroupOf MF).Normal := hnormalH0
                      ∃ H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF),
                          (∀ i, Nat.card (H i) = p) ∧
                            (∀ i, quotientSubgroupNormalizedBy MF H0 U (H i)) ∧
                            iSupIndep H ∧
                            iSup H = ⊤ ∧
                            (∃ hqpos : 0 < q,
                              ∀ i : Fin q,
                                ∃ w : W1,
                                  quotientSubgroupConjugateByElement MF H0
                                    (H ⟨0, hqpos⟩) (H i) (w : G)) ∧
                            ∃ χbar : Fin q →
                                (U ⧸ C.subgroupOf U) →* Multiplicative (ZMod a),
                              ∀ i,
                                letI : (C.subgroupOf U).Normal := hnormalC
                                ∃ ρ : (U ⧸ C.subgroupOf U) →* MulAut (H i),
                                    IsCyclic ρ.range ∧
                                      Nat.card ρ.range = a ∧
                                      (∀ x : U ⧸ C.subgroupOf U,
                                        ∀ u : U,
                                          QuotientGroup.mk' (C.subgroupOf U) u = x →
                                          ∃ hconjMF : ∀ h : MF,
                                            (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
                                            ∀ h : MF,
                                            ∀ hhQ :
                                              QuotientGroup.mk'
                                                (H0.subgroupOf MF) h ∈ H i,
                                              (ρ x
                                                ⟨QuotientGroup.mk'
                                                  (H0.subgroupOf MF) h, hhQ⟩ :
                                                  MF ⧸ H0.subgroupOf MF) =
                                                QuotientGroup.mk'
                                                  (H0.subgroupOf MF)
                                                  ⟨(u : G)⁻¹ * (h : G) * (u : G),
                                                    hconjMF h⟩) ∧
                                      (∀ x : U ⧸ C.subgroupOf U,
                                        ρ x = 1 ↔
                                          ∀ u : U,
                                            QuotientGroup.mk' (C.subgroupOf U) u =
                                              x →
                                            quotientSubgroupCentralizedByElement
                                              MF H0 (H i) (u : G)) ∧
                                      ∀ x : U,
                                        (∀ j : Fin (q - 1),
                                          ((χbar
                                            (theorem_9_7_fin_succ_of_sub_one_sec9
                                              hqprime.pos j)).comp
                                              (QuotientGroup.mk'
                                                (C.subgroupOf U))) x =
                                            ((χbar ⟨0, hqprime.pos⟩).comp
                                              (QuotientGroup.mk'
                                                (C.subgroupOf U))) x) →
                                        ρ (QuotientGroup.mk' (C.subgroupOf U)
                                          (w0 • x)) =
                                          ρ (QuotientGroup.mk'
                                            (C.subgroupOf U) x) := by
  classical
  intro h92 hp96 hC hBarU hpprime hqprime hnormalH0 hbarElem hbarFinrank
    hUnormMF hH0invU hnormalC hbarComm hW1normU hCinv w0 hw0gen Q hQnorm
    hQneBot hQneTop hQnotW1
  letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
  letI : (C.subgroupOf U).Normal := hnormalC
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  rcases
      theorem_9_7_clifford_case_a_quotient_component_generator_character_agreement_from_reducible_factor_source_bridge_sec9
        M MF U W1 W2 H0 C p q u h92 hp96 hC hBarU hpprime hqprime
        hnormalH0 hbarElem hbarFinrank hUnormMF hH0invU hnormalC hbarComm
        hW1normU hCinv w0 hw0gen Q hQnorm hQneBot hQneTop hQnotW1 with
    ⟨a, H, hcard, hUnorm, hindep, hSup, _hfac, horbit, χbar, hχdata,
      hχsource⟩
  refine ⟨a, H, hcard, hUnorm, hindep, hSup, horbit, χbar, ?_⟩
  intro i
  rcases hχdata i with
    ⟨ρ, hcyc, hρcard, haction, hker, hχinj⟩
  refine ⟨ρ, hcyc, hρcard, haction, hker, ?_⟩
  intro x hx
  exact hχinj _ _ (hχsource x hx i)

private theorem
    theorem_9_7_clifford_case_a_quotient_component_generator_error_inv_centralizes_factors_from_reducible_factor_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
          quotientChiefFactorData_9_6 M MF H0 W1 hp) →
          quotientCentralizerIn MF H0 U C →
            quotientBarUCardinality U C u →
              (hpprime : Nat.Prime p) →
                (hqprime : Nat.Prime q) →
                  (hnormalH0 : (H0.subgroupOf MF).Normal) →
                    (hbarElem :
                      letI : (H0.subgroupOf MF).Normal := hnormalH0
                      IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF)) →
                    (letI : Fact p.Prime := ⟨hpprime⟩
                    letI : (H0.subgroupOf MF).Normal := hnormalH0
                    letI : IsElementaryAbelian p
                      (MF ⧸ H0.subgroupOf MF) := hbarElem
                    Module.finrank (ZMod p)
                      (Additive (MF ⧸ H0.subgroupOf MF)) = q) →
                    (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G)) →
                    (hH0invU :
                      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                      IsInvariant U MF (H0.subgroupOf MF)) →
                    (hnormalC : (C.subgroupOf U).Normal) →
                      (letI : (C.subgroupOf U).Normal := hnormalC
                      IsMulCommutative (U ⧸ C.subgroupOf U)) →
                    (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G)) →
                    (hCinv :
                        letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
                        IsInvariant W1 U (C.subgroupOf U)) →
                    (w0 : W1) →
                    (hw0gen : Subgroup.zpowers w0 = ⊤) →
                    letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
                    letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
                      quotientMulDistribMulAction (A := W1) (G := U)
                        (C.subgroupOf U) hCinv
                    letI : (C.subgroupOf U).Normal := hnormalC
                    ∀ Q : Subgroup (MF ⧸ H0.subgroupOf MF),
                      quotientSubgroupNormalizedBy MF H0 U Q →
                        Q ≠ ⊥ →
                          Q ≠ ⊤ →
                            ¬ quotientSubgroupNormalizedBy MF H0 W1 Q →
                            ∃ a : ℕ,
                      ∃ hnormal : (H0.subgroupOf MF).Normal,
                        letI : (H0.subgroupOf MF).Normal := hnormal
                        ∃ H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF),
                          (∀ i, Nat.card (H i) = p) ∧
                            (∀ i, quotientSubgroupNormalizedBy MF H0 U (H i)) ∧
                            iSupIndep H ∧
                            iSup H = ⊤ ∧
                            (∀ i, quotientFactorActionCentralizerData MF H0 U C
                              (H i) a) ∧
                            (∃ hqpos : 0 < q,
                              ∀ i : Fin q,
                                ∃ w : W1,
                                  quotientSubgroupConjugateByElement MF H0
                                    (H ⟨0, hqpos⟩) (H i) (w : G)) ∧
                            ∃ χbar : Fin q →
                                (U ⧸ C.subgroupOf U) →* Multiplicative (ZMod a),
                              ∀ x : U,
                                (∀ j : Fin (q - 1),
                                  ((χbar
                                    (theorem_9_7_fin_succ_of_sub_one_sec9
                                      hqprime.pos j)).comp
                                      (QuotientGroup.mk' (C.subgroupOf U))) x =
                                    ((χbar ⟨0, hqprime.pos⟩).comp
                                      (QuotientGroup.mk' (C.subgroupOf U))) x) →
                                letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                                letI : (H0.subgroupOf MF).Normal := hnormalH0
                                letI : MulDistribMulAction U
                                    (MF ⧸ H0.subgroupOf MF) :=
                                  quotientMulDistribMulAction (A := U) (G := MF)
                                    (H0.subgroupOf MF) hH0invU
                                ∀ i,
                                  quotientSubgroupCentralizedByElement MF H0 (H i)
                                    (((((w0 • x) / x : U) : G)⁻¹)) := by
  classical
  intro h92 hp96 hC hBarU hpprime hqprime hnormalH0 hbarElem hbarFinrank
    hUnormMF hH0invU hnormalC hbarComm hW1normU hCinv w0 hw0gen Q hQnorm
    hQneBot hQneTop hQnotW1
  letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
  letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
    quotientMulDistribMulAction (A := U) (G := MF)
      (H0.subgroupOf MF) hH0invU
  rcases
      theorem_9_7_clifford_case_a_quotient_component_generator_action_agreement_from_reducible_factor_source_bridge_sec9
        M MF U W1 W2 H0 C p q u h92 hp96 hC hBarU hpprime hqprime
        hnormalH0 hbarElem hbarFinrank hUnormMF hH0invU hnormalC hbarComm
        hW1normU hCinv w0 hw0gen Q hQnorm hQneBot hQneTop hQnotW1 with
    ⟨a, H, hcard, hUnorm, hindep, hSup, horbit, χbar, hagreementData⟩
  have hfac : ∀ i, quotientFactorActionCentralizerData MF H0 U C (H i) a := by
    intro i
    rcases hagreementData i with
      ⟨ρ, hcyc, hρcard, haction, hker, _hρagreement⟩
    exact ⟨hnormalC, ρ, hcyc, hρcard, haction, hker⟩
  refine ⟨a, hnormalH0, H, hcard, hUnorm, hindep, hSup, hfac, horbit, χbar, ?_⟩
  intro x hx i
  rcases hagreementData i with
    ⟨ρ, _hcyc, _hcardρ, _haction, hker, hρagreement⟩
  letI : (C.subgroupOf U).Normal := hnormalC
  have hρkernel :
      ρ (QuotientGroup.mk' (C.subgroupOf U)
        ((((w0 • x) / x : U)⁻¹))) = 1 :=
    theorem_9_7_factorActionKernel_of_generator_action_eq_sec9
      hW1normU ρ w0 x (hρagreement x hx)
  have hcent :
      quotientSubgroupCentralizedByElement MF H0 (H i)
        (((((w0 • x) / x : U)⁻¹ : U) : G)) :=
    theorem_9_7_quotientSubgroupCentralizedByElement_of_factorActionKernel_sec9
      hker ((((w0 • x) / x : U)⁻¹)) hρkernel
  simpa using hcent

private theorem
    theorem_9_7_clifford_case_a_quotient_component_generator_error_fixes_factors_from_reducible_factor_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
          quotientChiefFactorData_9_6 M MF H0 W1 hp) →
          quotientCentralizerIn MF H0 U C →
            quotientBarUCardinality U C u →
              (hpprime : Nat.Prime p) →
                (hqprime : Nat.Prime q) →
                  (hnormalH0 : (H0.subgroupOf MF).Normal) →
                    (hbarElem :
                      letI : (H0.subgroupOf MF).Normal := hnormalH0
                      IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF)) →
                    (letI : Fact p.Prime := ⟨hpprime⟩
                    letI : (H0.subgroupOf MF).Normal := hnormalH0
                    letI : IsElementaryAbelian p
                      (MF ⧸ H0.subgroupOf MF) := hbarElem
                    Module.finrank (ZMod p)
                      (Additive (MF ⧸ H0.subgroupOf MF)) = q) →
                    (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G)) →
                    (hH0invU :
                      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                      IsInvariant U MF (H0.subgroupOf MF)) →
                    (hnormalC : (C.subgroupOf U).Normal) →
                      (letI : (C.subgroupOf U).Normal := hnormalC
                      IsMulCommutative (U ⧸ C.subgroupOf U)) →
                    (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G)) →
                    (hCinv :
                        letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
                        IsInvariant W1 U (C.subgroupOf U)) →
                    (w0 : W1) →
                    (hw0gen : Subgroup.zpowers w0 = ⊤) →
                    letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
                    letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
                      quotientMulDistribMulAction (A := W1) (G := U)
                        (C.subgroupOf U) hCinv
                    letI : (C.subgroupOf U).Normal := hnormalC
                    ∀ Q : Subgroup (MF ⧸ H0.subgroupOf MF),
                      quotientSubgroupNormalizedBy MF H0 U Q →
                        Q ≠ ⊥ →
                          Q ≠ ⊤ →
                            ¬ quotientSubgroupNormalizedBy MF H0 W1 Q →
                            ∃ a : ℕ,
                      ∃ hnormal : (H0.subgroupOf MF).Normal,
                        letI : (H0.subgroupOf MF).Normal := hnormal
                        ∃ H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF),
                          (∀ i, Nat.card (H i) = p) ∧
                            (∀ i, quotientSubgroupNormalizedBy MF H0 U (H i)) ∧
                            iSupIndep H ∧
                            iSup H = ⊤ ∧
                            (∀ i, quotientFactorActionCentralizerData MF H0 U C
                              (H i) a) ∧
                            (∃ hqpos : 0 < q,
                              ∀ i : Fin q,
                                ∃ w : W1,
                                  quotientSubgroupConjugateByElement MF H0
                                    (H ⟨0, hqpos⟩) (H i) (w : G)) ∧
                            ∃ χbar : Fin q →
                                (U ⧸ C.subgroupOf U) →* Multiplicative (ZMod a),
                              ∀ x : U,
                                (∀ j : Fin (q - 1),
                                  ((χbar
                                    (theorem_9_7_fin_succ_of_sub_one_sec9
                                      hqprime.pos j)).comp
                                      (QuotientGroup.mk' (C.subgroupOf U))) x =
                                    ((χbar ⟨0, hqprime.pos⟩).comp
                                      (QuotientGroup.mk' (C.subgroupOf U))) x) →
                                letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                                letI : (H0.subgroupOf MF).Normal := hnormalH0
                                letI : MulDistribMulAction U
                                    (MF ⧸ H0.subgroupOf MF) :=
                                  quotientMulDistribMulAction (A := U) (G := MF)
                                    (H0.subgroupOf MF) hH0invU
                                ∀ i, ∀ y : MF ⧸ H0.subgroupOf MF,
                                  y ∈ H i → ((w0 • x) / x : U) • y = y := by
  classical
  intro h92 hp96 hC hBarU hpprime hqprime hnormalH0 hbarElem hbarFinrank
    hUnormMF hH0invU hnormalC hbarComm hW1normU hCinv w0 hw0gen Q hQnorm
    hQneBot hQneTop hQnotW1
  letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
  letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
    quotientMulDistribMulAction (A := U) (G := MF)
      (H0.subgroupOf MF) hH0invU
  rcases
      theorem_9_7_clifford_case_a_quotient_component_generator_error_inv_centralizes_factors_from_reducible_factor_source_bridge_sec9
        M MF U W1 W2 H0 C p q u h92 hp96 hC hBarU hpprime hqprime
        hnormalH0 hbarElem hbarFinrank hUnormMF hH0invU hnormalC hbarComm
        hW1normU hCinv w0 hw0gen Q hQnorm hQneBot hQneTop hQnotW1 with
    ⟨a, hnormal, H, hcard, hUnorm, hindep, hSup, hfac, horbit, χbar, hχcent⟩
  refine ⟨a, hnormal, H, hcard, hUnorm, hindep, hSup, hfac, horbit, χbar, ?_⟩
  intro x hx i y hy
  exact
    theorem_9_7_quotient_action_fixed_of_inv_quotientSubgroupCentralizedByElement_sec9
      hnormalH0 hUnormMF hH0invU (((w0 • x) / x : U))
      (hχcent x hx i) y hy

private theorem
    theorem_9_7_clifford_case_a_quotient_component_generator_error_fixes_quotient_from_reducible_factor_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
          quotientChiefFactorData_9_6 M MF H0 W1 hp) →
          quotientCentralizerIn MF H0 U C →
            quotientBarUCardinality U C u →
              (hpprime : Nat.Prime p) →
                (hqprime : Nat.Prime q) →
                  (hnormalH0 : (H0.subgroupOf MF).Normal) →
                    (hbarElem :
                      letI : (H0.subgroupOf MF).Normal := hnormalH0
                      IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF)) →
                    (letI : Fact p.Prime := ⟨hpprime⟩
                    letI : (H0.subgroupOf MF).Normal := hnormalH0
                    letI : IsElementaryAbelian p
                      (MF ⧸ H0.subgroupOf MF) := hbarElem
                    Module.finrank (ZMod p)
                      (Additive (MF ⧸ H0.subgroupOf MF)) = q) →
                    (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G)) →
                    (hH0invU :
                      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                      IsInvariant U MF (H0.subgroupOf MF)) →
                    (hnormalC : (C.subgroupOf U).Normal) →
                      (letI : (C.subgroupOf U).Normal := hnormalC
                      IsMulCommutative (U ⧸ C.subgroupOf U)) →
                    (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G)) →
                    (hCinv :
                        letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
                        IsInvariant W1 U (C.subgroupOf U)) →
                    (w0 : W1) →
                    (hw0gen : Subgroup.zpowers w0 = ⊤) →
                    letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
                    letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
                      quotientMulDistribMulAction (A := W1) (G := U)
                        (C.subgroupOf U) hCinv
                    letI : (C.subgroupOf U).Normal := hnormalC
                    ∀ Q : Subgroup (MF ⧸ H0.subgroupOf MF),
                      quotientSubgroupNormalizedBy MF H0 U Q →
                        Q ≠ ⊥ →
                          Q ≠ ⊤ →
                            ¬ quotientSubgroupNormalizedBy MF H0 W1 Q →
                            ∃ a : ℕ,
                      (∃ hnormal : (H0.subgroupOf MF).Normal,
                        letI : (H0.subgroupOf MF).Normal := hnormal
                        ∃ H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF),
                          (∀ i, Nat.card (H i) = p) ∧
                            (∀ i, quotientSubgroupNormalizedBy MF H0 U (H i)) ∧
                            iSupIndep H ∧
                            iSup H = ⊤ ∧
                            (∀ i, quotientFactorActionCentralizerData MF H0 U C
                              (H i) a) ∧
                            ∃ hqpos : 0 < q,
                              ∀ i : Fin q,
                                ∃ w : W1,
                                  quotientSubgroupConjugateByElement MF H0
                                    (H ⟨0, hqpos⟩) (H i) (w : G)) ∧
                      ∃ χbar : Fin q →
                          (U ⧸ C.subgroupOf U) →* Multiplicative (ZMod a),
                        ∀ x : U,
                          (∀ j : Fin (q - 1),
                            ((χbar
                              (theorem_9_7_fin_succ_of_sub_one_sec9 hqprime.pos j)).comp
                                (QuotientGroup.mk' (C.subgroupOf U))) x =
                              ((χbar ⟨0, hqprime.pos⟩).comp
                                (QuotientGroup.mk' (C.subgroupOf U))) x) →
                          letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                          letI : (H0.subgroupOf MF).Normal := hnormalH0
                          letI : MulDistribMulAction U
                              (MF ⧸ H0.subgroupOf MF) :=
                            quotientMulDistribMulAction (A := U) (G := MF)
                              (H0.subgroupOf MF) hH0invU
                          ∀ h : MF,
                            ((w0 • x) / x : U) •
                                QuotientGroup.mk' (H0.subgroupOf MF) h =
                              QuotientGroup.mk' (H0.subgroupOf MF) h := by
  classical
  intro h92 hp96 hC hBarU hpprime hqprime hnormalH0 hbarElem hbarFinrank
    hUnormMF hH0invU hnormalC hbarComm hW1normU hCinv w0 hw0gen Q hQnorm
    hQneBot hQneTop hQnotW1
  letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
  letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
    quotientMulDistribMulAction (A := U) (G := MF)
      (H0.subgroupOf MF) hH0invU
  rcases
    theorem_9_7_clifford_case_a_quotient_component_generator_error_fixes_factors_from_reducible_factor_source_bridge_sec9
      M MF U W1 W2 H0 C p q u h92 hp96 hC hBarU hpprime hqprime
      hnormalH0 hbarElem hbarFinrank hUnormMF hH0invU hnormalC hbarComm
      hW1normU hCinv w0 hw0gen Q hQnorm hQneBot hQneTop hQnotW1 with
    ⟨a, hnormal, H, hcard, hUnorm, hindep, hSup, hfac, horbit, χbar, hχfactor⟩
  refine ⟨a, ?_, χbar, ?_⟩
  · exact ⟨hnormal, H, hcard, hUnorm, hindep, hSup, hfac, horbit⟩
  · intro x hx
    exact
      theorem_9_7_quotient_action_fixed_of_iSup_factors_fixed_sec9
        hnormalH0 hUnormMF hH0invU H hSup (((w0 • x) / x : U))
        (hχfactor x hx)

private theorem
    theorem_9_7_clifford_case_a_quotient_component_generator_error_centralizes_from_reducible_factor_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
          quotientChiefFactorData_9_6 M MF H0 W1 hp) →
          quotientCentralizerIn MF H0 U C →
            quotientBarUCardinality U C u →
              (hpprime : Nat.Prime p) →
                (hqprime : Nat.Prime q) →
                  (hnormalH0 : (H0.subgroupOf MF).Normal) →
                    (hbarElem :
                      letI : (H0.subgroupOf MF).Normal := hnormalH0
                      IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF)) →
                    (letI : Fact p.Prime := ⟨hpprime⟩
                    letI : (H0.subgroupOf MF).Normal := hnormalH0
                    letI : IsElementaryAbelian p
                      (MF ⧸ H0.subgroupOf MF) := hbarElem
                    Module.finrank (ZMod p)
                      (Additive (MF ⧸ H0.subgroupOf MF)) = q) →
                    (hnormalC : (C.subgroupOf U).Normal) →
                      (letI : (C.subgroupOf U).Normal := hnormalC
                      IsMulCommutative (U ⧸ C.subgroupOf U)) →
                    (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G)) →
                    (hCinv :
                        letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
                        IsInvariant W1 U (C.subgroupOf U)) →
                    (w0 : W1) →
                    (hw0gen : Subgroup.zpowers w0 = ⊤) →
                    letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
                    letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
                      quotientMulDistribMulAction (A := W1) (G := U)
                        (C.subgroupOf U) hCinv
                    letI : (C.subgroupOf U).Normal := hnormalC
                    ∀ Q : Subgroup (MF ⧸ H0.subgroupOf MF),
                      quotientSubgroupNormalizedBy MF H0 U Q →
                        Q ≠ ⊥ →
                          Q ≠ ⊤ →
                            ¬ quotientSubgroupNormalizedBy MF H0 W1 Q →
                            ∃ a : ℕ,
                      (∃ hnormal : (H0.subgroupOf MF).Normal,
                        letI : (H0.subgroupOf MF).Normal := hnormal
                        ∃ H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF),
                          (∀ i, Nat.card (H i) = p) ∧
                            (∀ i, quotientSubgroupNormalizedBy MF H0 U (H i)) ∧
                            iSupIndep H ∧
                            iSup H = ⊤ ∧
                            (∀ i, quotientFactorActionCentralizerData MF H0 U C
                              (H i) a) ∧
                            ∃ hqpos : 0 < q,
                              ∀ i : Fin q,
                                ∃ w : W1,
                                  quotientSubgroupConjugateByElement MF H0
                                    (H ⟨0, hqpos⟩) (H i) (w : G)) ∧
                      ∃ χbar : Fin q →
                          (U ⧸ C.subgroupOf U) →* Multiplicative (ZMod a),
                        ∀ x : U,
                          (∀ j : Fin (q - 1),
                            ((χbar
                              (theorem_9_7_fin_succ_of_sub_one_sec9 hqprime.pos j)).comp
                                (QuotientGroup.mk' (C.subgroupOf U))) x =
                              ((χbar ⟨0, hqprime.pos⟩).comp
                                (QuotientGroup.mk' (C.subgroupOf U))) x) →
                          ∀ h : G, h ∈ MF →
                            ⁅(((w0 • x) / x : U) : G), h⁆ ∈ H0 := by
  classical
  intro h92 hp96 hC hBarU hpprime hqprime hnormalH0 hbarElem hbarFinrank
    hnormalC hbarComm hW1normU hCinv w0 hw0gen Q hQnorm hQneBot hQneTop hQnotW1
  rcases hp96 with ⟨hp, hp_eq, hpData, h96⟩
  have hp96Full :
      ∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
          quotientChiefFactorData_9_6 M MF H0 W1 hp :=
    ⟨hp, hp_eq, hpData, h96⟩
  have hUnormMF : U ≤ Subgroup.normalizer (MF : Set G) :=
    le_sup_left.trans
      (theorem_9_3_action_normalizes_and_solvable_sec9 M MF U W1 W2 q h92).1
  have hUleM : U ≤ M := by
    rcases h92.typePDefinitionData with
      ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, hUleD,
        _hUnil, _hW1normU, _hcompDU, _hMFnotcyc, _hsecond, _hfitEq,
        _hfitLeD, _hW2le, _hW2cyc, _hW2ne, _hcentW1, _hnormX⟩
    exact hUleD.trans section12_ambientDerivedSubgroup_le
  rcases hpData with
    ⟨_hH0MF_hp, hMFM_hp, hH0normalM_hp, _hH0normalMF_hp, _hH0lt_hp,
      _hbarElemRaw, _htypeIIIIVData_hp⟩
  letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
  have hH0invU : IsInvariant U MF (H0.subgroupOf MF) :=
    subgroupOf_MF_isInvariant_of_subgroupOf_M_normal_sec9 M MF U H0
      hMFM_hp hUleM hH0normalM_hp hUnormMF
  letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
  rcases
    theorem_9_7_clifford_case_a_quotient_component_generator_error_fixes_quotient_from_reducible_factor_source_bridge_sec9
      M MF U W1 W2 H0 C p q u h92 hp96Full hC hBarU hpprime hqprime
      hnormalH0 hbarElem hbarFinrank hUnormMF hH0invU hnormalC hbarComm
      hW1normU hCinv w0 hw0gen Q hQnorm hQneBot hQneTop hQnotW1 with
    ⟨a, hproduct, χbar, hχfix⟩
  refine ⟨a, hproduct, χbar, ?_⟩
  intro x hx h hhMF
  exact
    theorem_9_7_quotient_action_fixed_to_commutator_sec9 hnormalH0
      hUnormMF hH0invU (((w0 • x) / x : U)) (hχfix x hx) h hhMF

private theorem
    theorem_9_7_clifford_case_a_quotient_component_generator_div_mem_C_from_reducible_factor_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
          quotientChiefFactorData_9_6 M MF H0 W1 hp) →
          quotientCentralizerIn MF H0 U C →
            quotientBarUCardinality U C u →
              (hpprime : Nat.Prime p) →
                (hqprime : Nat.Prime q) →
                  (hnormalH0 : (H0.subgroupOf MF).Normal) →
                    (hbarElem :
                      letI : (H0.subgroupOf MF).Normal := hnormalH0
                      IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF)) →
                    (letI : Fact p.Prime := ⟨hpprime⟩
                    letI : (H0.subgroupOf MF).Normal := hnormalH0
                    letI : IsElementaryAbelian p
                      (MF ⧸ H0.subgroupOf MF) := hbarElem
                    Module.finrank (ZMod p)
                      (Additive (MF ⧸ H0.subgroupOf MF)) = q) →
                    (hnormalC : (C.subgroupOf U).Normal) →
                      (letI : (C.subgroupOf U).Normal := hnormalC
                      IsMulCommutative (U ⧸ C.subgroupOf U)) →
                    (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G)) →
                    (hCinv :
                        letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
                        IsInvariant W1 U (C.subgroupOf U)) →
                    (w0 : W1) →
                    (hw0gen : Subgroup.zpowers w0 = ⊤) →
                    letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
                    letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
                      quotientMulDistribMulAction (A := W1) (G := U)
                        (C.subgroupOf U) hCinv
                    letI : (C.subgroupOf U).Normal := hnormalC
                    ∀ Q : Subgroup (MF ⧸ H0.subgroupOf MF),
                      quotientSubgroupNormalizedBy MF H0 U Q →
                        Q ≠ ⊥ →
                          Q ≠ ⊤ →
                            ¬ quotientSubgroupNormalizedBy MF H0 W1 Q →
                            ∃ a : ℕ,
                      (∃ hnormal : (H0.subgroupOf MF).Normal,
                        letI : (H0.subgroupOf MF).Normal := hnormal
                        ∃ H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF),
                          (∀ i, Nat.card (H i) = p) ∧
                            (∀ i, quotientSubgroupNormalizedBy MF H0 U (H i)) ∧
                            iSupIndep H ∧
                            iSup H = ⊤ ∧
                            (∀ i, quotientFactorActionCentralizerData MF H0 U C
                              (H i) a) ∧
                            ∃ hqpos : 0 < q,
                              ∀ i : Fin q,
                                ∃ w : W1,
                                  quotientSubgroupConjugateByElement MF H0
                                    (H ⟨0, hqpos⟩) (H i) (w : G)) ∧
                      ∃ χbar : Fin q →
                          (U ⧸ C.subgroupOf U) →* Multiplicative (ZMod a),
                        ∀ x : U,
                          (∀ j : Fin (q - 1),
                            ((χbar
                              (theorem_9_7_fin_succ_of_sub_one_sec9 hqprime.pos j)).comp
                                (QuotientGroup.mk' (C.subgroupOf U))) x =
                              ((χbar ⟨0, hqprime.pos⟩).comp
                                (QuotientGroup.mk' (C.subgroupOf U))) x) →
                          (w0 • x) / x ∈ C.subgroupOf U := by
  intro h92 hp96 hC hBarU hpprime hqprime hnormalH0 hbarElem hbarFinrank
    hnormalC hbarUcomm hW1normU hCinv w0 hw0gen
  classical
  letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
  letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
    quotientMulDistribMulAction (A := W1) (G := U) (C.subgroupOf U) hCinv
  letI : (C.subgroupOf U).Normal := hnormalC
  intro Q hQnorm hQneBot hQneTop hQnotW1
  rcases
      theorem_9_7_clifford_case_a_quotient_component_generator_error_centralizes_from_reducible_factor_source_bridge_sec9
        M MF U W1 W2 H0 C p q u h92 hp96 hC hBarU hpprime hqprime
        hnormalH0 hbarElem hbarFinrank hnormalC hbarUcomm hW1normU hCinv
        w0 hw0gen Q hQnorm hQneBot hQneTop hQnotW1 with
    ⟨a, hdecomp, χbar, hχbar⟩
  refine ⟨a, hdecomp, χbar, ?_⟩
  intro x hx
  exact
    theorem_9_7_smul_div_mem_C_of_quotient_centralizes_sec9
      hC hW1normU w0 x (hχbar x hx)

private theorem
    theorem_9_7_clifford_case_a_quotient_component_generator_fixed_coset_from_reducible_factor_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
          quotientChiefFactorData_9_6 M MF H0 W1 hp) →
          quotientCentralizerIn MF H0 U C →
            quotientBarUCardinality U C u →
              (hpprime : Nat.Prime p) →
                (hqprime : Nat.Prime q) →
                  (hnormalH0 : (H0.subgroupOf MF).Normal) →
                    (hbarElem :
                      letI : (H0.subgroupOf MF).Normal := hnormalH0
                      IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF)) →
                    (letI : Fact p.Prime := ⟨hpprime⟩
                    letI : (H0.subgroupOf MF).Normal := hnormalH0
                    letI : IsElementaryAbelian p
                      (MF ⧸ H0.subgroupOf MF) := hbarElem
                    Module.finrank (ZMod p)
                      (Additive (MF ⧸ H0.subgroupOf MF)) = q) →
                    (hnormalC : (C.subgroupOf U).Normal) →
                      (letI : (C.subgroupOf U).Normal := hnormalC
                      IsMulCommutative (U ⧸ C.subgroupOf U)) →
                    (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G)) →
                    (hCinv :
                        letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
                        IsInvariant W1 U (C.subgroupOf U)) →
                    (w0 : W1) →
                    (hw0gen : Subgroup.zpowers w0 = ⊤) →
                    letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
                    letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
                      quotientMulDistribMulAction (A := W1) (G := U)
                        (C.subgroupOf U) hCinv
                    letI : (C.subgroupOf U).Normal := hnormalC
                    ∀ Q : Subgroup (MF ⧸ H0.subgroupOf MF),
                      quotientSubgroupNormalizedBy MF H0 U Q →
                        Q ≠ ⊥ →
                          Q ≠ ⊤ →
                            ¬ quotientSubgroupNormalizedBy MF H0 W1 Q →
                            ∃ a : ℕ,
                      (∃ hnormal : (H0.subgroupOf MF).Normal,
                        letI : (H0.subgroupOf MF).Normal := hnormal
                        ∃ H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF),
                          (∀ i, Nat.card (H i) = p) ∧
                            (∀ i, quotientSubgroupNormalizedBy MF H0 U (H i)) ∧
                            iSupIndep H ∧
                            iSup H = ⊤ ∧
                            (∀ i, quotientFactorActionCentralizerData MF H0 U C
                              (H i) a) ∧
                            ∃ hqpos : 0 < q,
                              ∀ i : Fin q,
                                ∃ w : W1,
                                  quotientSubgroupConjugateByElement MF H0
                                    (H ⟨0, hqpos⟩) (H i) (w : G)) ∧
                      ∃ χbar : Fin q →
                          (U ⧸ C.subgroupOf U) →* Multiplicative (ZMod a),
                        ∀ x : U,
                          (∀ j : Fin (q - 1),
                            ((χbar
                              (theorem_9_7_fin_succ_of_sub_one_sec9 hqprime.pos j)).comp
                                (QuotientGroup.mk' (C.subgroupOf U))) x =
                              ((χbar ⟨0, hqprime.pos⟩).comp
                                (QuotientGroup.mk' (C.subgroupOf U))) x) →
                          w0 • (QuotientGroup.mk' (C.subgroupOf U) x) =
                            QuotientGroup.mk' (C.subgroupOf U) x := by
  intro h92 hp96 hC hBarU hpprime hqprime hnormalH0 hbarElem hbarFinrank
    hnormalC hbarUcomm hW1normU hCinv w0 hw0gen
  classical
  letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
  letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
    quotientMulDistribMulAction (A := W1) (G := U) (C.subgroupOf U) hCinv
  letI : (C.subgroupOf U).Normal := hnormalC
  intro Q hQnorm hQneBot hQneTop hQnotW1
  rcases
      theorem_9_7_clifford_case_a_quotient_component_generator_div_mem_C_from_reducible_factor_source_bridge_sec9
        M MF U W1 W2 H0 C p q u h92 hp96 hC hBarU hpprime hqprime
        hnormalH0 hbarElem hbarFinrank hnormalC hbarUcomm hW1normU hCinv
        w0 hw0gen Q hQnorm hQneBot hQneTop hQnotW1 with
    ⟨a, hdecomp, χbar, hχbar⟩
  refine ⟨a, hdecomp, χbar, ?_⟩
  intro x hx
  exact
    theorem_9_7_generator_fixed_coset_of_smul_div_mem_C_sec9
      hnormalC hW1normU hCinv w0 x (hχbar x hx)

private theorem
    theorem_9_7_clifford_case_a_quotient_component_fixed_coset_from_reducible_factor_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
          quotientChiefFactorData_9_6 M MF H0 W1 hp) →
          quotientCentralizerIn MF H0 U C →
            quotientBarUCardinality U C u →
              (hpprime : Nat.Prime p) →
                (hqprime : Nat.Prime q) →
                  (hnormalH0 : (H0.subgroupOf MF).Normal) →
                    (hbarElem :
                      letI : (H0.subgroupOf MF).Normal := hnormalH0
                      IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF)) →
                    (letI : Fact p.Prime := ⟨hpprime⟩
                    letI : (H0.subgroupOf MF).Normal := hnormalH0
                    letI : IsElementaryAbelian p
                      (MF ⧸ H0.subgroupOf MF) := hbarElem
                    Module.finrank (ZMod p)
                      (Additive (MF ⧸ H0.subgroupOf MF)) = q) →
                    (hnormalC : (C.subgroupOf U).Normal) →
                      (letI : (C.subgroupOf U).Normal := hnormalC
                      IsMulCommutative (U ⧸ C.subgroupOf U)) →
                    (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G)) →
                      (hCinv :
                        letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
                        IsInvariant W1 U (C.subgroupOf U)) →
                    letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
                    letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
                      quotientMulDistribMulAction (A := W1) (G := U)
                        (C.subgroupOf U) hCinv
                    letI : (C.subgroupOf U).Normal := hnormalC
                    ∀ Q : Subgroup (MF ⧸ H0.subgroupOf MF),
                      quotientSubgroupNormalizedBy MF H0 U Q →
                        Q ≠ ⊥ →
                          Q ≠ ⊤ →
                            ¬ quotientSubgroupNormalizedBy MF H0 W1 Q →
                            ∃ a : ℕ,
                      (∃ hnormal : (H0.subgroupOf MF).Normal,
                        letI : (H0.subgroupOf MF).Normal := hnormal
                        ∃ H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF),
                          (∀ i, Nat.card (H i) = p) ∧
                            (∀ i, quotientSubgroupNormalizedBy MF H0 U (H i)) ∧
                            iSupIndep H ∧
                            iSup H = ⊤ ∧
                            (∀ i, quotientFactorActionCentralizerData MF H0 U C
                              (H i) a) ∧
                            ∃ hqpos : 0 < q,
                              ∀ i : Fin q,
                                ∃ w : W1,
                                  quotientSubgroupConjugateByElement MF H0
                                    (H ⟨0, hqpos⟩) (H i) (w : G)) ∧
                      ∃ χbar : Fin q → (U ⧸ C.subgroupOf U) →* Multiplicative (ZMod a),
                        ∀ x : U,
                          (∀ j : Fin (q - 1),
                            ((χbar
                              (theorem_9_7_fin_succ_of_sub_one_sec9 hqprime.pos j)).comp
                                (QuotientGroup.mk' (C.subgroupOf U))) x =
                              ((χbar ⟨0, hqprime.pos⟩).comp
                                (QuotientGroup.mk' (C.subgroupOf U))) x) →
                          QuotientGroup.mk' (C.subgroupOf U) x ∈
                            fixedPointSubgroup W1 (U ⧸ C.subgroupOf U) := by
  intro h92 hp96 hC hBarU hpprime hqprime hnormalH0 hbarElem hbarFinrank
    hnormalC hbarUcomm hW1normU hCinv
  classical
  letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
  letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
    quotientMulDistribMulAction (A := W1) (G := U) (C.subgroupOf U) hCinv
  letI : (C.subgroupOf U).Normal := hnormalC
  have hW1cyc : IsCyclic W1 := by
    rcases h92.typePDefinitionData with
      ⟨_hMFsource, hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD,
        _hUnil, _hW1normU, _hcompDU, _hMFnotcyc, _hsecond, _hfitEq,
        _hfitLeD, _hW2le, _hW2cyc, _hW2ne, _hcentW1, _hnormX⟩
    exact hW1cyc
  letI : IsCyclic W1 := hW1cyc
  rcases IsCyclic.exists_generator (α := W1) with ⟨w0, hw0mem⟩
  have hw0gen : Subgroup.zpowers w0 = ⊤ := by
    exact eq_top_iff.mpr (fun w _hw => hw0mem w)
  intro Q hQnorm hQneBot hQneTop hQnotW1
  rcases
      theorem_9_7_clifford_case_a_quotient_component_generator_fixed_coset_from_reducible_factor_source_bridge_sec9
        M MF U W1 W2 H0 C p q u h92 hp96 hC hBarU hpprime hqprime
        hnormalH0 hbarElem hbarFinrank hnormalC hbarUcomm hW1normU hCinv
        w0 hw0gen Q hQnorm hQneBot hQneTop hQnotW1 with
    ⟨a, hdecomp, χbar, hχbar⟩
  refine ⟨a, hdecomp, χbar, ?_⟩
  intro x hx
  exact
    theorem_9_7_fixedPointSubgroup_mem_of_generator_fixed_sec9 hw0gen
      (hχbar x hx)

public theorem
    theorem_9_7_clifford_case_a_quotient_component_equalizer_from_reducible_factor_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
          quotientChiefFactorData_9_6 M MF H0 W1 hp) →
          quotientCentralizerIn MF H0 U C →
            quotientBarUCardinality U C u →
              (hpprime : Nat.Prime p) →
                (hqprime : Nat.Prime q) →
                  (hnormalH0 : (H0.subgroupOf MF).Normal) →
                    (hbarElem :
                      letI : (H0.subgroupOf MF).Normal := hnormalH0
                      IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF)) →
                    (letI : Fact p.Prime := ⟨hpprime⟩
                    letI : (H0.subgroupOf MF).Normal := hnormalH0
                    letI : IsElementaryAbelian p
                      (MF ⧸ H0.subgroupOf MF) := hbarElem
                    Module.finrank (ZMod p)
                      (Additive (MF ⧸ H0.subgroupOf MF)) = q) →
                    (hnormalC : (C.subgroupOf U).Normal) →
                      (letI : (C.subgroupOf U).Normal := hnormalC
                      IsMulCommutative (U ⧸ C.subgroupOf U)) →
                    letI : (C.subgroupOf U).Normal := hnormalC
                    ∀ Q : Subgroup (MF ⧸ H0.subgroupOf MF),
                      quotientSubgroupNormalizedBy MF H0 U Q →
                        Q ≠ ⊥ →
                          Q ≠ ⊤ →
                            ¬ quotientSubgroupNormalizedBy MF H0 W1 Q →
                            ∃ a : ℕ,
                      (∃ hnormal : (H0.subgroupOf MF).Normal,
                        letI : (H0.subgroupOf MF).Normal := hnormal
                        ∃ H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF),
                          (∀ i, Nat.card (H i) = p) ∧
                            (∀ i, quotientSubgroupNormalizedBy MF H0 U (H i)) ∧
                            iSupIndep H ∧
                            iSup H = ⊤ ∧
                            (∀ i, quotientFactorActionCentralizerData MF H0 U C
                              (H i) a) ∧
                            ∃ hqpos : 0 < q,
                              ∀ i : Fin q,
                                ∃ w : W1,
                                  quotientSubgroupConjugateByElement MF H0
                                    (H ⟨0, hqpos⟩) (H i) (w : G)) ∧
                      ∃ χbar : Fin q → (U ⧸ C.subgroupOf U) →* Multiplicative (ZMod a),
                          ∀ x : U,
                            (∀ j : Fin (q - 1),
                              ((χbar
                                (theorem_9_7_fin_succ_of_sub_one_sec9 hqprime.pos j)).comp
                                (QuotientGroup.mk' (C.subgroupOf U))) x =
                              ((χbar ⟨0, hqprime.pos⟩).comp
                                (QuotientGroup.mk' (C.subgroupOf U))) x) →
                          x ∈ C.subgroupOf U := by
  intro h92 hp96 hC hBarU hpprime hqprime hnormalH0 hbarElem hbarFinrank
    hnormalC hbarUcomm
  classical
  rcases hp96 with ⟨hp, hp_eq, hpData, h96⟩
  have hW1normU : W1 ≤ Subgroup.normalizer (U : Set G) :=
    theorem_9_7_W1_le_normalizer_U_of_hypothesis_9_2_sec9 h92
  have hW1normMF : W1 ≤ Subgroup.normalizer (MF : Set G) :=
    theorem_9_7_W1_le_normalizer_MF_of_hypothesis_9_2_sec9 h92
  letI : (C.subgroupOf U).Normal := hnormalC
  letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
  have hCinv : IsInvariant W1 U (C.subgroupOf U) :=
    theorem_9_7_quotientCentralizerIn_isInvariant_W1_sec9 h92 hpData hC
      hW1normU hW1normMF
  letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
    quotientMulDistribMulAction (A := W1) (G := U) (C.subgroupOf U) hCinv
  have hfixedBot :
      fixedPointSubgroup W1 (U ⧸ C.subgroupOf U) = ⊥ :=
    theorem_9_7_fixedPointSubgroup_W1_barU_eq_bot_of_isInvariant_sec9
      h92 hnormalC hW1normU hCinv
  intro Q hQnorm hQneBot hQneTop hQnotW1
  rcases
      theorem_9_7_clifford_case_a_quotient_component_fixed_coset_from_reducible_factor_source_bridge_sec9
        M MF U W1 W2 H0 C p q u h92 ⟨hp, hp_eq, hpData, h96⟩ hC hBarU
        hpprime hqprime hnormalH0 hbarElem hbarFinrank hnormalC hbarUcomm
        hW1normU hCinv Q hQnorm hQneBot hQneTop hQnotW1 with
    ⟨a, hdecomp, χbar, hfixed⟩
  refine ⟨a, hdecomp, χbar, ?_⟩
  intro x hx
  exact
    theorem_9_7_mem_C_of_barU_fixed_sec9 hnormalC hW1normU hCinv
      hfixedBot x (hfixed x hx)

private theorem theorem_9_7_clifford_case_a_quotient_component_homs_from_reducible_factor_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
          quotientChiefFactorData_9_6 M MF H0 W1 hp) →
          quotientCentralizerIn MF H0 U C →
            quotientBarUCardinality U C u →
              (hpprime : Nat.Prime p) →
                (hqprime : Nat.Prime q) →
                  (hnormalH0 : (H0.subgroupOf MF).Normal) →
                    (hbarElem :
                      letI : (H0.subgroupOf MF).Normal := hnormalH0
                      IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF)) →
                    (letI : Fact p.Prime := ⟨hpprime⟩
                    letI : (H0.subgroupOf MF).Normal := hnormalH0
                    letI : IsElementaryAbelian p
                      (MF ⧸ H0.subgroupOf MF) := hbarElem
                    Module.finrank (ZMod p)
                      (Additive (MF ⧸ H0.subgroupOf MF)) = q) →
                    (hnormalC : (C.subgroupOf U).Normal) →
                      (letI : (C.subgroupOf U).Normal := hnormalC
                      IsMulCommutative (U ⧸ C.subgroupOf U)) →
                    letI : (C.subgroupOf U).Normal := hnormalC
                    ∀ Q : Subgroup (MF ⧸ H0.subgroupOf MF),
                      quotientSubgroupNormalizedBy MF H0 U Q →
                        Q ≠ ⊥ →
                          Q ≠ ⊤ →
                            ¬ quotientSubgroupNormalizedBy MF H0 W1 Q →
                            ∃ a : ℕ,
                      (∃ hnormal : (H0.subgroupOf MF).Normal,
                        letI : (H0.subgroupOf MF).Normal := hnormal
                        ∃ H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF),
                          (∀ i, Nat.card (H i) = p) ∧
                            (∀ i, quotientSubgroupNormalizedBy MF H0 U (H i)) ∧
                            iSupIndep H ∧
                            iSup H = ⊤ ∧
                            (∀ i, quotientFactorActionCentralizerData MF H0 U C
                              (H i) a) ∧
                            ∃ hqpos : 0 < q,
                              ∀ i : Fin q,
                                ∃ w : W1,
                                  quotientSubgroupConjugateByElement MF H0
                                    (H ⟨0, hqpos⟩) (H i) (w : G)) ∧
                      ∃ χbar : Fin q → (U ⧸ C.subgroupOf U) →* Multiplicative (ZMod a),
                        (theorem_9_7_relative_product_hom_sec9 hqprime.pos
                          (fun i =>
                            (χbar i).comp (QuotientGroup.mk' (C.subgroupOf U)))).ker ≤
                          C.subgroupOf U := by
  classical
  intro h92 h94 hC hbarU hpprime hqprime hnormalH0 hbarElem hbarFinrank hnormalC hbarUcomm
  letI : (C.subgroupOf U).Normal := hnormalC
  intro Q hQnorm hQneBot hQneTop hQnotW1
  rcases
      theorem_9_7_clifford_case_a_quotient_component_equalizer_from_reducible_factor_source_bridge_sec9
        M MF U W1 W2 H0 C p q u h92 h94 hC hbarU hpprime hqprime
        hnormalH0 hbarElem hbarFinrank hnormalC hbarUcomm Q hQnorm hQneBot hQneTop
        hQnotW1 with
    ⟨a, hpayload⟩
  rcases hpayload with ⟨hdecomp, hchars⟩
  rcases hchars with ⟨χbar, hequalizer⟩
  refine ⟨a, hdecomp, χbar, ?_⟩
  exact theorem_9_7_relative_product_hom_ker_le_of_equalizer_sec9
    hqprime.pos (C.subgroupOf U)
    (fun i => (χbar i).comp (QuotientGroup.mk' (C.subgroupOf U)))
    hequalizer

private theorem theorem_9_7_clifford_case_a_component_homs_from_reducible_factor_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
          quotientChiefFactorData_9_6 M MF H0 W1 hp) →
          quotientCentralizerIn MF H0 U C →
            quotientBarUCardinality U C u →
              (hpprime : Nat.Prime p) →
                (hqprime : Nat.Prime q) →
                  (hnormalH0 : (H0.subgroupOf MF).Normal) →
                    (hbarElem :
                      letI : (H0.subgroupOf MF).Normal := hnormalH0
                      IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF)) →
                    (letI : Fact p.Prime := ⟨hpprime⟩
                    letI : (H0.subgroupOf MF).Normal := hnormalH0
                    letI : IsElementaryAbelian p
                      (MF ⧸ H0.subgroupOf MF) := hbarElem
                    Module.finrank (ZMod p)
                      (Additive (MF ⧸ H0.subgroupOf MF)) = q) →
                    (hnormalC : (C.subgroupOf U).Normal) →
                      (letI : (C.subgroupOf U).Normal := hnormalC
                      IsMulCommutative (U ⧸ C.subgroupOf U)) →
                    ∀ Q : Subgroup (MF ⧸ H0.subgroupOf MF),
                      quotientSubgroupNormalizedBy MF H0 U Q →
                        Q ≠ ⊥ →
                          Q ≠ ⊤ →
                            ¬ quotientSubgroupNormalizedBy MF H0 W1 Q →
                            ∃ a : ℕ,
                      (∃ hnormal : (H0.subgroupOf MF).Normal,
                        letI : (H0.subgroupOf MF).Normal := hnormal
                        ∃ H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF),
                          (∀ i, Nat.card (H i) = p) ∧
                            (∀ i, quotientSubgroupNormalizedBy MF H0 U (H i)) ∧
                            iSupIndep H ∧
                            iSup H = ⊤ ∧
                            (∀ i, quotientFactorActionCentralizerData MF H0 U C
                              (H i) a) ∧
                            ∃ hqpos : 0 < q,
                              ∀ i : Fin q,
                                ∃ w : W1,
                                  quotientSubgroupConjugateByElement MF H0
                                    (H ⟨0, hqpos⟩) (H i) (w : G)) ∧
                      ∃ χ : Fin q → U →* Multiplicative (ZMod a),
                        (∀ i, C.subgroupOf U ≤ (χ i).ker) ∧
                          (theorem_9_7_relative_product_hom_sec9 hqprime.pos χ).ker ≤
                            C.subgroupOf U := by
  intro h92 hp96 hC hBarU hpprime hqprime hnormalH0 hbarElem hbarFinrank
    hnormalC hbarUcomm Q hQnorm hQneBot hQneTop hQnotW1
  classical
  letI : (C.subgroupOf U).Normal := hnormalC
  rcases theorem_9_7_clifford_case_a_quotient_component_homs_from_reducible_factor_source_bridge_sec9
      M MF U W1 W2 H0 C p q u h92 hp96 hC hBarU hpprime hqprime hnormalH0
      hbarElem hbarFinrank hnormalC hbarUcomm Q hQnorm hQneBot hQneTop hQnotW1 with
    ⟨a, hdecomp, χbar, hkerC⟩
  let χ : Fin q → U →* Multiplicative (ZMod a) :=
    fun i => (χbar i).comp (QuotientGroup.mk' (C.subgroupOf U))
  have hχC : ∀ i, C.subgroupOf U ≤ (χ i).ker := by
    intro i
    simpa [χ] using
      theorem_9_7_quotient_component_pullback_C_le_ker_sec9
        (C.subgroupOf U) (χbar i)
  refine ⟨a, hdecomp, χ, hχC, ?_⟩
  simpa [χ] using hkerC

public theorem theorem_9_7_clifford_case_a_product_hom_from_reducible_factor_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
          quotientChiefFactorData_9_6 M MF H0 W1 hp) →
          quotientCentralizerIn MF H0 U C →
            quotientBarUCardinality U C u →
              (hpprime : Nat.Prime p) →
                (hqprime : Nat.Prime q) →
                  (hnormalH0 : (H0.subgroupOf MF).Normal) →
                    (hbarElem :
                      letI : (H0.subgroupOf MF).Normal := hnormalH0
                      IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF)) →
                    (letI : Fact p.Prime := ⟨hpprime⟩
                    letI : (H0.subgroupOf MF).Normal := hnormalH0
                    letI : IsElementaryAbelian p
                      (MF ⧸ H0.subgroupOf MF) := hbarElem
                    Module.finrank (ZMod p)
                      (Additive (MF ⧸ H0.subgroupOf MF)) = q) →
                    (hnormalC : (C.subgroupOf U).Normal) →
                      (letI : (C.subgroupOf U).Normal := hnormalC
                      IsMulCommutative (U ⧸ C.subgroupOf U)) →
                    ∀ Q : Subgroup (MF ⧸ H0.subgroupOf MF),
                      quotientSubgroupNormalizedBy MF H0 U Q →
                        Q ≠ ⊥ →
                          Q ≠ ⊤ →
                            ¬ quotientSubgroupNormalizedBy MF H0 W1 Q →
                            ∃ a : ℕ,
                      (∃ hnormal : (H0.subgroupOf MF).Normal,
                        letI : (H0.subgroupOf MF).Normal := hnormal
                        ∃ H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF),
                          (∀ i, Nat.card (H i) = p) ∧
                            (∀ i, quotientSubgroupNormalizedBy MF H0 U (H i)) ∧
                            iSupIndep H ∧
                            iSup H = ⊤ ∧
                            (∀ i, quotientFactorActionCentralizerData MF H0 U C
                              (H i) a) ∧
                            ∃ hqpos : 0 < q,
                              ∀ i : Fin q,
                                ∃ w : W1,
                                  quotientSubgroupConjugateByElement MF H0
                                    (H ⟨0, hqpos⟩) (H i) (w : G)) ∧
                      ∃ ψ : U →* (Fin (q - 1) → Multiplicative (ZMod a)),
                        C.subgroupOf U ≤ ψ.ker ∧ ψ.ker ≤ C.subgroupOf U := by
  intro h92 hp96 hC hBarU hpprime hqprime hnormalH0 hbarElem hbarFinrank
    hnormalC hbarUcomm Q hQnorm hQneBot hQneTop hQnotW1
  classical
  rcases theorem_9_7_clifford_case_a_component_homs_from_reducible_factor_source_bridge_sec9
      M MF U W1 W2 H0 C p q u h92 hp96 hC hBarU hpprime hqprime hnormalH0
      hbarElem hbarFinrank hnormalC hbarUcomm Q hQnorm hQneBot hQneTop hQnotW1 with
    ⟨a, hdecomp, χ, hχC, hkerC⟩
  let ψ : U →* (Fin (q - 1) → Multiplicative (ZMod a)) :=
    theorem_9_7_relative_product_hom_sec9 hqprime.pos χ
  have hCker : C.subgroupOf U ≤ ψ.ker := by
    simpa [ψ] using
      theorem_9_7_relative_product_hom_C_le_ker_sec9
        hqprime.pos (C.subgroupOf U) χ hχC
  refine ⟨a, hdecomp, ψ, hCker, ?_⟩
  simpa [ψ] using hkerC

public theorem theorem_9_7_clifford_case_a_product_embedding_from_reducible_factor_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
          quotientChiefFactorData_9_6 M MF H0 W1 hp) →
          quotientCentralizerIn MF H0 U C →
            quotientBarUCardinality U C u →
              (hpprime : Nat.Prime p) →
                (hqprime : Nat.Prime q) →
                  (hnormalH0 : (H0.subgroupOf MF).Normal) →
                    (hbarElem :
                      letI : (H0.subgroupOf MF).Normal := hnormalH0
                      IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF)) →
                    (letI : Fact p.Prime := ⟨hpprime⟩
                    letI : (H0.subgroupOf MF).Normal := hnormalH0
                    letI : IsElementaryAbelian p
                      (MF ⧸ H0.subgroupOf MF) := hbarElem
                    Module.finrank (ZMod p)
                      (Additive (MF ⧸ H0.subgroupOf MF)) = q) →
                    (hnormalC : (C.subgroupOf U).Normal) →
                      (letI : (C.subgroupOf U).Normal := hnormalC
                      IsMulCommutative (U ⧸ C.subgroupOf U)) →
                    ∀ Q : Subgroup (MF ⧸ H0.subgroupOf MF),
                      quotientSubgroupNormalizedBy MF H0 U Q →
                        Q ≠ ⊥ →
                          Q ≠ ⊤ →
                            ¬ quotientSubgroupNormalizedBy MF H0 W1 Q →
                            ∃ a : ℕ,
                      (∃ hnormal : (H0.subgroupOf MF).Normal,
                        letI : (H0.subgroupOf MF).Normal := hnormal
                        ∃ H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF),
                          (∀ i, Nat.card (H i) = p) ∧
                            (∀ i, quotientSubgroupNormalizedBy MF H0 U (H i)) ∧
                            iSupIndep H ∧
                            iSup H = ⊤ ∧
                            (∀ i, quotientFactorActionCentralizerData MF H0 U C
                              (H i) a) ∧
                            ∃ hqpos : 0 < q,
                              ∀ i : Fin q,
                                ∃ w : W1,
                                  quotientSubgroupConjugateByElement MF H0
                                    (H ⟨0, hqpos⟩) (H i) (w : G)) ∧
                      ∃ hnormal : (C.subgroupOf U).Normal,
                        letI : (C.subgroupOf U).Normal := hnormal
                        ∃ φ : (U ⧸ C.subgroupOf U) →*
                          (Fin (q - 1) → Multiplicative (ZMod a)),
                          Function.Injective φ := by
  intro h92 hp96 hC hBarU hpprime hqprime hnormalH0 hbarElem hbarFinrank
    hnormalC hbarUcomm Q hQnorm hQneBot hQneTop hQnotW1
  classical
  rcases theorem_9_7_clifford_case_a_product_hom_from_reducible_factor_source_bridge_sec9
      M MF U W1 W2 H0 C p q u h92 hp96 hC hBarU hpprime hqprime hnormalH0
      hbarElem hbarFinrank hnormalC hbarUcomm Q hQnorm hQneBot hQneTop hQnotW1 with
    ⟨a, hdecomp, ψ, hCker, hkerC⟩
  refine ⟨a, hdecomp, hnormalC, ?_⟩
  letI : (C.subgroupOf U).Normal := hnormalC
  exact theorem_9_7_quotient_hom_injective_of_kernel_eq_sec9
    (C.subgroupOf U) ψ hCker hkerC

private theorem theorem_9_7_clifford_case_a_product_embedding_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
          quotientChiefFactorData_9_6 M MF H0 W1 hp) →
          quotientCentralizerIn MF H0 U C →
            quotientBarUCardinality U C u →
              Nat.Prime p →
                Nat.Prime q →
                  ¬ quotientIrreducibleActionData MF H0 U →
                    ∃ a : ℕ,
                      (∃ hnormal : (H0.subgroupOf MF).Normal,
                        letI : (H0.subgroupOf MF).Normal := hnormal
                        ∃ H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF),
                          (∀ i, Nat.card (H i) = p) ∧
                            (∀ i, quotientSubgroupNormalizedBy MF H0 U (H i)) ∧
                            iSupIndep H ∧
                            iSup H = ⊤ ∧
                            (∀ i, quotientFactorActionCentralizerData MF H0 U C
                              (H i) a) ∧
                            ∃ hqpos : 0 < q,
                              ∀ i : Fin q,
                                ∃ w : W1,
                                  quotientSubgroupConjugateByElement MF H0
                                    (H ⟨0, hqpos⟩) (H i) (w : G)) ∧
                      ∃ hnormal : (C.subgroupOf U).Normal,
                        letI : (C.subgroupOf U).Normal := hnormal
                        ∃ φ : (U ⧸ C.subgroupOf U) →*
                          (Fin (q - 1) → Multiplicative (ZMod a)),
                          Function.Injective φ := by
  intro h92 hp96 hC hBarU hpprime hqprime hnon
  rcases hp96 with ⟨hp, hp_eq, hpData, h96⟩
  rcases h96 with ⟨hH0MF, hMFM, hnormalH0, hchief, hWbar, hcardRaw⟩
  rcases hBarU with ⟨hCU, hnormalC, hBarUcard⟩
  have hpDataFull : hoReductionData M MF U W2 H0 hp := hpData
  rcases hpData with
    ⟨_hH0MF_hp, _hMFM_hp, _hH0normalM_hp, _hH0normalMF_hp, _hH0lt_hp,
      hbarElemRaw, _htypeIIIIVData_hp⟩
  rcases hbarElemRaw with ⟨_hnormalElem, hbarElemRaw⟩
  have hbarElem :
      (letI : (H0.subgroupOf MF).Normal := hnormalH0;
        IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF)) := by
    letI : (H0.subgroupOf MF).Normal := hnormalH0
    simpa [hp_eq] using hbarElemRaw
  have hbarCard :
      (letI : (H0.subgroupOf MF).Normal := hnormalH0;
        Nat.card (MF ⧸ H0.subgroupOf MF) = p ^ q) := by
    letI : (H0.subgroupOf MF).Normal := hnormalH0
    simpa using
      theorem_9_7_quotient_cardinality_from_chief_data_sec9 h92 hp_eq
        ⟨hH0MF, hMFM, hnormalH0, hchief, hWbar, hcardRaw⟩
  have hbarFinrank :
      (letI : Fact p.Prime := ⟨hpprime⟩
      letI : (H0.subgroupOf MF).Normal := hnormalH0
      letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
      Module.finrank (ZMod p) (Additive (MF ⧸ H0.subgroupOf MF)) = q) :=
    theorem_9_7_quotient_finrank_eq_q_sec9 hpprime hnormalH0
      hbarElem hbarCard
  have hbarUcomm :
      (letI : (C.subgroupOf U).Normal := hnormalC
      IsMulCommutative (U ⧸ C.subgroupOf U)) :=
    theorem_9_7_barU_isMulCommutative_sec9 h92 hC hnormalC
  have hproper :=
    theorem_9_7_exists_proper_U_normalized_quotient_subgroup_of_not_irreducible_sec9
      (MF := MF) (H0 := H0) (U := U) hnormalH0 hnon
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  rcases hproper with ⟨Q, hQnorm, hQneBot, hQneTop⟩
  have hQnotW1 :
      ¬ quotientSubgroupNormalizedBy MF H0 W1 Q :=
    quotientSubgroup_not_W1_normalized_of_proper_U_normalized_quotientChiefFactorData_sec9
      M MF U W1 W2 H0 q hp h92 hpDataFull
      ⟨hH0MF, hMFM, hnormalH0, hchief, hWbar, hcardRaw⟩
      hnormalH0 Q hQnorm hQneBot hQneTop
  exact
    theorem_9_7_clifford_case_a_product_embedding_from_reducible_factor_source_bridge_sec9
      M MF U W1 W2 H0 C p q u h92
      ⟨hp, hp_eq, hpDataFull,
        ⟨hH0MF, hMFM, hnormalH0, hchief, hWbar, hcardRaw⟩⟩
      hC ⟨hCU, hnormalC, hBarUcard⟩ hpprime hqprime hnormalH0 hbarElem
      hbarFinrank hnormalC hbarUcomm Q hQnorm hQneBot hQneTop hQnotW1

private theorem theorem_9_7_clifford_module_dichotomy_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
          quotientChiefFactorData_9_6 M MF H0 W1 hp) →
          quotientCentralizerIn MF H0 U C →
            quotientBarUCardinality U C u →
              Nat.Prime p →
                Nat.Prime q →
                  (∃ a : ℕ,
                    (∃ hnormal : (H0.subgroupOf MF).Normal,
                      letI : (H0.subgroupOf MF).Normal := hnormal
                      ∃ H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF),
                        (∀ i, Nat.card (H i) = p) ∧
                          (∀ i, quotientSubgroupNormalizedBy MF H0 U (H i)) ∧
                          iSupIndep H ∧
                          iSup H = ⊤ ∧
                          (∀ i, quotientFactorActionCentralizerData MF H0 U C
                            (H i) a) ∧
                          ∃ hqpos : 0 < q,
                            ∀ i : Fin q,
                              ∃ w : W1,
                                quotientSubgroupConjugateByElement MF H0
                                  (H ⟨0, hqpos⟩) (H i) (w : G)) ∧
                      (∃ _hCU : C ≤ U,
                        ∃ hnormal : (C.subgroupOf U).Normal,
                          letI : (C.subgroupOf U).Normal := hnormal
                          ∃ φ : (U ⧸ C.subgroupOf U) →*
                            (Fin (q - 1) → Multiplicative (ZMod a)),
                            Function.Injective φ)) ∨
                    quotientIrreducibleActionData MF H0 U := by
  intro h92 hp96 hC hBarU hpprime hqprime
  by_cases hirred : quotientIrreducibleActionData MF H0 U
  · exact Or.inr hirred
  · rcases theorem_9_7_clifford_case_a_product_embedding_source_bridge_sec9
      M MF U W1 W2 H0 C p q u h92 hp96 hC hBarU hpprime hqprime hirred with
      ⟨a, hdecomp, hproduct⟩
    rcases hBarU with ⟨hCU, _hnormalBarU, _hBarCard⟩
    rcases hproduct with ⟨hnormalC, φ, hφinj⟩
    exact Or.inl ⟨a, hdecomp, hCU, hnormalC, φ, hφinj⟩

private def theorem_9_7_schurEndFieldData_sec9
    {G : Type u} [Group G] [Finite G]
    (MF H0 U : Subgroup G) (p : ℕ)
    (hpprime : Nat.Prime p)
    (hnormalH0 : (H0.subgroupOf MF).Normal)
    (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G))
    (hH0inv :
      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
      IsInvariant U MF (H0.subgroupOf MF))
    (hbarElem :
      letI : (H0.subgroupOf MF).Normal := hnormalH0
      IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF)) : Prop :=
  letI : Fact (Nat.Prime p) := ⟨hpprime⟩
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
  letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
  letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
    quotientMulDistribMulAction (A := U) (G := MF) (H0.subgroupOf MF) hH0inv
  let ρ := Theory.Representation.ofElementaryAbelianAction (A := U)
    (G := MF ⧸ H0.subgroupOf MF) (p := p)
  let E := Module.End (MonoidAlgebra (ZMod p) U) ρ.asModule
  ∃ fieldInst : Field E, ∃ fintypeInst : Fintype E,
    letI : Field E := fieldInst
    letI : Fintype E := fintypeInst
    letI : Module E ρ.asModule := endFieldModule ρ
    Nontrivial E ∧ Nat.card E = Fintype.card E ∧
      ringChar E = p ∧ (∃ n : ℕ+, Nat.card E = p ^ (n : ℕ)) ∧
      Nat.card (MF ⧸ H0.subgroupOf MF) =
        (Nat.card E) ^ Module.finrank E ρ.asModule

private def theorem_9_7_schurEndFieldFullData_sec9
    {G : Type u} [Group G] [Finite G]
    (MF H0 U : Subgroup G) (p q : ℕ)
    (hpprime : Nat.Prime p)
    (hnormalH0 : (H0.subgroupOf MF).Normal)
    (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G))
    (hH0inv :
      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
      IsInvariant U MF (H0.subgroupOf MF))
    (hbarElem :
      letI : (H0.subgroupOf MF).Normal := hnormalH0
      IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF)) : Prop :=
  letI : Fact (Nat.Prime p) := ⟨hpprime⟩
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
  letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
  letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
    quotientMulDistribMulAction (A := U) (G := MF) (H0.subgroupOf MF) hH0inv
  let ρ := Theory.Representation.ofElementaryAbelianAction (A := U)
    (G := MF ⧸ H0.subgroupOf MF) (p := p)
  let E := Module.End (MonoidAlgebra (ZMod p) U) ρ.asModule
  Nat.card E = p ^ q ∧ Module.finrank E ρ.asModule = 1

private theorem theorem_9_7_schurEndFieldData_of_irreducible_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 U : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hnormalH0 : (H0.subgroupOf MF).Normal)
    (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G))
    (hH0inv :
      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
      IsInvariant U MF (H0.subgroupOf MF))
    (hbarElem :
      letI : (H0.subgroupOf MF).Normal := hnormalH0
      IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF))
    (hirredRep :
      letI : (H0.subgroupOf MF).Normal := hnormalH0
      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
      letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
      letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
        quotientMulDistribMulAction (A := U) (G := MF)
          (H0.subgroupOf MF) hH0inv
      Representation.IsIrreducible
        (Theory.Representation.ofElementaryAbelianAction (A := U)
          (G := MF ⧸ H0.subgroupOf MF) (p := p))) :
    theorem_9_7_schurEndFieldData_sec9 MF H0 U p Fact.out
      hnormalH0 hUnormMF hH0inv hbarElem := by
  classical
  dsimp [theorem_9_7_schurEndFieldData_sec9]
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
  letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
  letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
    quotientMulDistribMulAction (A := U) (G := MF)
      (H0.subgroupOf MF) hH0inv
  let ρ := Theory.Representation.ofElementaryAbelianAction (A := U)
    (G := MF ⧸ H0.subgroupOf MF) (p := p)
  have hρirr : Representation.IsIrreducible ρ := by
    simpa [ρ] using hirredRep
  letI : Representation.IsIrreducible ρ := hρirr
  haveI : FiniteDimensional (ZMod p) (Additive (MF ⧸ H0.subgroupOf MF)) :=
    finiteDimensional_of_irreducible_finite_group ρ hρirr
  let E := Module.End (MonoidAlgebra (ZMod p) U) ρ.asModule
  let fieldInst : Field E := endField_field ρ
  let fintypeInst : Fintype E := Fintype.ofFinite E
  refine ⟨fieldInst, fintypeInst, ?_⟩
  letI : Field E := fieldInst
  letI : Fintype E := fintypeInst
  let instModuleE : Module E ρ.asModule := endFieldModule ρ
  letI : Module E ρ.asModule := instModuleE
  have hρasFinite : Finite ρ.asModule :=
    Finite.of_equiv (Additive (MF ⧸ H0.subgroupOf MF))
      ρ.asModuleEquiv.symm.toEquiv
  let instFiniteE : Module.Finite E ρ.asModule := Module.Finite.of_finite
  haveI : Module.Finite E ρ.asModule := instFiniteE
  have h_as :
      Nat.card ρ.asModule =
        Nat.card (Additive (MF ⧸ H0.subgroupOf MF)) :=
    Nat.card_congr ρ.asModuleEquiv.toEquiv
  have h_add :
      Nat.card (Additive (MF ⧸ H0.subgroupOf MF)) =
        Nat.card (MF ⧸ H0.subgroupOf MF) :=
    Nat.card_congr
      { toFun := Additive.toMul
        invFun := Additive.ofMul
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl }
  have hquot_as :
      Nat.card (MF ⧸ H0.subgroupOf MF) = Nat.card ρ.asModule := by
    rw [← h_add, ← h_as]
  have hρcard :
      Nat.card ρ.asModule =
        (Nat.card E) ^ Module.finrank E ρ.asModule := by
    simpa [Nat.card_eq_fintype_card] using
      (@Module.natCard_eq_pow_finrank E ρ.asModule
        (@Field.toDivisionRing E fieldInst) ρ.instAddCommGroupAsModule
        instModuleE instFiniteE)
  let instAlgebraZE : Algebra (ZMod p) E :=
    Module.End.instAlgebra (ZMod p) (MonoidAlgebra (ZMod p) U) ρ.asModule
  have hringCharE : ringChar E = p := by
    have hEZ : ringChar E = ringChar (ZMod p) := by
      have h :=
        @Algebra.ringChar_eq (ZMod p) E inferInstance inferInstance
          inferInstance instAlgebraZE
      exact h.symm
    simpa [ZMod.ringChar_zmod_n] using hEZ
  have hcharE : CharP E p := ringChar.of_eq hringCharE
  have hEcardPow : ∃ n : ℕ+, Nat.card E = p ^ (n : ℕ) := by
    rcases @FiniteField.card E fieldInst fintypeInst p hcharE with
      ⟨n, _hp, hcard⟩
    exact ⟨n, by simpa [Nat.card_eq_fintype_card] using hcard⟩
  exact
    ⟨inferInstance, (Nat.card_eq_fintype_card : Nat.card E = Fintype.card E),
      hringCharE, hEcardPow, hquot_as.trans hρcard⟩

private theorem theorem_9_7_schurEndField_card_eq_prime_or_full_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 U : Subgroup G} {p q : ℕ}
    (hpprime : Nat.Prime p)
    (hqprime : Nat.Prime q)
    (hnormalH0 : (H0.subgroupOf MF).Normal)
    (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G))
    (hH0inv :
      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
      IsInvariant U MF (H0.subgroupOf MF))
    (hbarElem :
      letI : (H0.subgroupOf MF).Normal := hnormalH0
      IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF))
    (hbarCard :
      letI : (H0.subgroupOf MF).Normal := hnormalH0
      Nat.card (MF ⧸ H0.subgroupOf MF) = p ^ q)
    (hEndField :
      theorem_9_7_schurEndFieldData_sec9 MF H0 U p
        hpprime hnormalH0 hUnormMF hH0inv hbarElem) :
    letI : Fact p.Prime := ⟨hpprime⟩
    letI : (H0.subgroupOf MF).Normal := hnormalH0
    letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
    letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
    letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
      quotientMulDistribMulAction (A := U) (G := MF)
        (H0.subgroupOf MF) hH0inv
    let ρ := Theory.Representation.ofElementaryAbelianAction (A := U)
      (G := MF ⧸ H0.subgroupOf MF) (p := p)
    let E := Module.End (MonoidAlgebra (ZMod p) U) ρ.asModule
    Nat.card E = p ∨ Nat.card E = p ^ q := by
  classical
  dsimp [theorem_9_7_schurEndFieldData_sec9] at hEndField
  letI : Fact p.Prime := ⟨hpprime⟩
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
  letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
  letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
    quotientMulDistribMulAction (A := U) (G := MF)
      (H0.subgroupOf MF) hH0inv
  let ρ := Theory.Representation.ofElementaryAbelianAction (A := U)
    (G := MF ⧸ H0.subgroupOf MF) (p := p)
  let E := Module.End (MonoidAlgebra (ZMod p) U) ρ.asModule
  change Nat.card E = p ∨ Nat.card E = p ^ q
  rcases hEndField with
    ⟨fieldInst, fintypeInst, hnontriv, _hcardFintype, _hringCharE,
      hEcardPow, hquotCard⟩
  letI : Field E := fieldInst
  letI : Fintype E := fintypeInst
  letI : Module E ρ.asModule := endFieldModule ρ
  rcases hEcardPow with ⟨n, hncard⟩
  have hbarCard' : Nat.card (MF ⧸ H0.subgroupOf MF) = p ^ q := by
    simpa using hbarCard
  have hpow :
      p ^ q = p ^ ((n : ℕ) * Module.finrank E ρ.asModule) := by
    calc
      p ^ q = Nat.card (MF ⧸ H0.subgroupOf MF) := hbarCard'.symm
      _ = (Nat.card E) ^ Module.finrank E ρ.asModule := hquotCard
      _ = (p ^ (n : ℕ)) ^ Module.finrank E ρ.asModule := by rw [hncard]
      _ = p ^ ((n : ℕ) * Module.finrank E ρ.asModule) := by
        rw [pow_mul]
  have hn_mul : q = (n : ℕ) * Module.finrank E ρ.asModule :=
    Nat.pow_right_injective hpprime.two_le hpow
  have hn_dvd_q : (n : ℕ) ∣ q := by
    rw [hn_mul]
    exact dvd_mul_right (n : ℕ) (Module.finrank E ρ.asModule)
  rcases (Nat.dvd_prime hqprime).1 hn_dvd_q with hn_one | hn_q
  · left
    rw [hncard, hn_one, pow_one]
  · right
    rw [hncard, hn_q]

private theorem theorem_9_7_schurEndField_card_finrank_alternative_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 U : Subgroup G} {p q : ℕ}
    (hpprime : Nat.Prime p)
    (hqprime : Nat.Prime q)
    (hnormalH0 : (H0.subgroupOf MF).Normal)
    (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G))
    (hH0inv :
      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
      IsInvariant U MF (H0.subgroupOf MF))
    (hbarElem :
      letI : (H0.subgroupOf MF).Normal := hnormalH0
      IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF))
    (hbarCard :
      letI : (H0.subgroupOf MF).Normal := hnormalH0
      Nat.card (MF ⧸ H0.subgroupOf MF) = p ^ q)
    (hEndField :
      theorem_9_7_schurEndFieldData_sec9 MF H0 U p
        hpprime hnormalH0 hUnormMF hH0inv hbarElem)
    (hEndFieldCardAlt :
      letI : Fact p.Prime := ⟨hpprime⟩
      letI : (H0.subgroupOf MF).Normal := hnormalH0
      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
      letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
      letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
        quotientMulDistribMulAction (A := U) (G := MF)
          (H0.subgroupOf MF) hH0inv
      let ρ := Theory.Representation.ofElementaryAbelianAction (A := U)
        (G := MF ⧸ H0.subgroupOf MF) (p := p)
      let E := Module.End (MonoidAlgebra (ZMod p) U) ρ.asModule
      Nat.card E = p ∨ Nat.card E = p ^ q) :
    letI : Fact p.Prime := ⟨hpprime⟩
    letI : (H0.subgroupOf MF).Normal := hnormalH0
    letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
    letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
    letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
      quotientMulDistribMulAction (A := U) (G := MF)
        (H0.subgroupOf MF) hH0inv
    let ρ := Theory.Representation.ofElementaryAbelianAction (A := U)
      (G := MF ⧸ H0.subgroupOf MF) (p := p)
    let E := Module.End (MonoidAlgebra (ZMod p) U) ρ.asModule
    (Nat.card E = p ∧ Module.finrank E ρ.asModule = q) ∨
      (Nat.card E = p ^ q ∧ Module.finrank E ρ.asModule = 1) := by
  classical
  dsimp [theorem_9_7_schurEndFieldData_sec9] at hEndField
  letI : Fact p.Prime := ⟨hpprime⟩
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
  letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
  letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
    quotientMulDistribMulAction (A := U) (G := MF)
      (H0.subgroupOf MF) hH0inv
  let ρ := Theory.Representation.ofElementaryAbelianAction (A := U)
    (G := MF ⧸ H0.subgroupOf MF) (p := p)
  let E := Module.End (MonoidAlgebra (ZMod p) U) ρ.asModule
  change (Nat.card E = p ∧ Module.finrank E ρ.asModule = q) ∨
    (Nat.card E = p ^ q ∧ Module.finrank E ρ.asModule = 1)
  change Nat.card E = p ∨ Nat.card E = p ^ q at hEndFieldCardAlt
  rcases hEndField with
    ⟨fieldInst, fintypeInst, _hnontriv, _hcardFintype, _hringCharE,
      _hEcardPow, hquotCard⟩
  letI : Field E := fieldInst
  letI : Fintype E := fintypeInst
  letI : Module E ρ.asModule := endFieldModule ρ
  have hbarCard' : Nat.card (MF ⧸ H0.subgroupOf MF) = p ^ q := by
    simpa using hbarCard
  have hpow :
      p ^ q = (Nat.card E) ^ Module.finrank E ρ.asModule := by
    calc
      p ^ q = Nat.card (MF ⧸ H0.subgroupOf MF) := hbarCard'.symm
      _ = (Nat.card E) ^ Module.finrank E ρ.asModule := hquotCard
  rcases hEndFieldCardAlt with hEcardPrime | hEcardFull
  · left
    refine ⟨hEcardPrime, ?_⟩
    have hpowPrime := hpow
    rw [hEcardPrime] at hpowPrime
    exact (Nat.pow_right_injective hpprime.two_le hpowPrime).symm
  · right
    refine ⟨hEcardFull, ?_⟩
    have hbase : 2 ≤ p ^ q := one_lt_pow₀ hpprime.one_lt hqprime.ne_zero
    have hpowFull : (p ^ q) ^ 1 = (p ^ q) ^ Module.finrank E ρ.asModule := by
      have hpowFull' := hpow
      rw [hEcardFull] at hpowFull'
      simpa using hpowFull'
    exact (Nat.pow_right_injective hbase hpowFull).symm

private theorem theorem_9_7_quotientCentralizerIn_subgroupOf_le_elementary_action_ker_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 U C : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hnormalH0 : (H0.subgroupOf MF).Normal)
    (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G))
    (hH0invU :
      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
      IsInvariant U MF (H0.subgroupOf MF))
    (hbarElem :
      letI : (H0.subgroupOf MF).Normal := hnormalH0
      IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF))
    (hC : quotientCentralizerIn MF H0 U C) :
    letI : (H0.subgroupOf MF).Normal := hnormalH0
    letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
    letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
    letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
      quotientMulDistribMulAction (A := U) (G := MF)
        (H0.subgroupOf MF) hH0invU
    C.subgroupOf U ≤
      (Theory.Representation.ofElementaryAbelianAction (A := U)
        (G := MF ⧸ H0.subgroupOf MF) (p := p)).ker := by
  classical
  let H0MF : Subgroup MF := H0.subgroupOf MF
  haveI : H0MF.Normal := hnormalH0
  letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
  have hH0invU' : IsInvariant U MF H0MF := by
    simpa [H0MF] using hH0invU
  letI : MulDistribMulAction U (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := U) (G := MF) H0MF hH0invU'
  haveI : IsElementaryAbelian p (MF ⧸ H0MF) := by
    simpa [H0MF] using hbarElem
  intro c hc
  rw [Theory.Representation.ker_ofElementaryAbelianAction_eq_fixingSubgroup]
  refine
    (mem_fixingSubgroup_iff
      (M := U) (s := (Set.univ : Set (MF ⧸ H0MF)))).2 ?_
  intro y _hy
  refine QuotientGroup.induction_on y ?_
  intro h
  change c • QuotientGroup.mk' H0MF h = QuotientGroup.mk' H0MF h
  have hsmul_mk :
      c • QuotientGroup.mk' H0MF h = QuotientGroup.mk' H0MF (c • h) := by
    simpa only [QuotientGroup.mk'_apply] using
      (MulAction.Quotient.smul_mk (H := H0MF) c h)
  rw [hsmul_mk]
  apply QuotientGroup.eq.mpr
  dsimp [H0MF]
  change ((c • h : MF)⁻¹ * h : MF) ∈ H0.subgroupOf MF
  have hcC : ((c : U) : G) ∈ C := by
    simpa [Subgroup.mem_subgroupOf] using hc
  have hcent : ∀ z : G, z ∈ MF → ⁅((c : U) : G), z⁆ ∈ H0 :=
    (hC.2 ((c : U) : G) c.property).mp hcC
  have hcomm_mem : ⁅((c : U) : G), ((h : G)⁻¹)⁆ ∈ H0 :=
    hcent ((h : G)⁻¹) (MF.inv_mem h.property)
  have htarget_eq :
      (((c • h : MF)⁻¹ * h : MF) : G) =
        ⁅((c : U) : G), ((h : G)⁻¹)⁆ := by
    simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
      commutatorElement_def, mul_assoc]
  simpa [Subgroup.mem_subgroupOf, htarget_eq] using hcomm_mem

private theorem theorem_9_7_elementary_action_ker_le_quotientCentralizerIn_subgroupOf_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 U C : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hnormalH0 : (H0.subgroupOf MF).Normal)
    (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G))
    (hH0invU :
      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
      IsInvariant U MF (H0.subgroupOf MF))
    (hbarElem :
      letI : (H0.subgroupOf MF).Normal := hnormalH0
      IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF))
    (hC : quotientCentralizerIn MF H0 U C) :
    letI : (H0.subgroupOf MF).Normal := hnormalH0
    letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
    letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
    letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
      quotientMulDistribMulAction (A := U) (G := MF)
        (H0.subgroupOf MF) hH0invU
    (Theory.Representation.ofElementaryAbelianAction (A := U)
      (G := MF ⧸ H0.subgroupOf MF) (p := p)).ker ≤ C.subgroupOf U := by
  classical
  let H0MF : Subgroup MF := H0.subgroupOf MF
  haveI : H0MF.Normal := hnormalH0
  letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
  have hH0invU' : IsInvariant U MF H0MF := by
    simpa [H0MF] using hH0invU
  letI : MulDistribMulAction U (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := U) (G := MF) H0MF hH0invU'
  haveI : IsElementaryAbelian p (MF ⧸ H0MF) := by
    simpa [H0MF] using hbarElem
  intro c hcKer
  rw [Theory.Representation.ker_ofElementaryAbelianAction_eq_fixingSubgroup] at hcKer
  have hfix_univ :
      ∀ y : MF ⧸ H0MF, y ∈ Set.univ → c • y = y :=
    (mem_fixingSubgroup_iff
      (M := U) (s := (Set.univ : Set (MF ⧸ H0MF)))).1 hcKer
  have hfix : ∀ y : MF ⧸ H0MF, c • y = y := fun y =>
    hfix_univ y (Set.mem_univ y)
  have hcC : ((c : U) : G) ∈ C := by
    rw [(hC.2 ((c : U) : G) c.property)]
    intro h hhMF
    let hinv : MF := ⟨h⁻¹, MF.inv_mem hhMF⟩
    have hfixInv :
        c • QuotientGroup.mk' H0MF hinv =
          QuotientGroup.mk' H0MF hinv :=
      hfix (QuotientGroup.mk' H0MF hinv)
    have hsmul_mk :
        c • QuotientGroup.mk' H0MF hinv =
          QuotientGroup.mk' H0MF (c • hinv) := by
      simpa only [QuotientGroup.mk'_apply] using
        (MulAction.Quotient.smul_mk (H := H0MF) c hinv)
    rw [hsmul_mk] at hfixInv
    have hmem : (((c • hinv : MF)⁻¹ * hinv : MF) ∈ H0MF) :=
      QuotientGroup.eq.mp hfixInv
    have htarget_eq :
        (((c • hinv : MF)⁻¹ * hinv : MF) : G) =
          ⁅((c : U) : G), h⁆ := by
      simp [hinv, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
        commutatorElement_def, mul_assoc]
    simpa [H0MF, Subgroup.mem_subgroupOf, htarget_eq] using hmem
  simpa [Subgroup.mem_subgroupOf] using hcC

private theorem theorem_9_7_endFieldRep_ker_le_ker_sec9
    {F : Type*} [Field F]
    {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) :
    (endFieldRep ρ).ker ≤ ρ.ker := by
  intro g hg
  rw [MonoidHom.mem_ker] at hg ⊢
  ext v
  let m : ρ.asModule := ρ.asModuleEquiv.symm v
  have hgm :
      ρ.asModuleEquiv (((endFieldRep ρ) g) m) =
        ρ.asModuleEquiv m := by
    simpa [m] using congrArg (fun f => ρ.asModuleEquiv (f m)) hg
  change ρ g v = v
  calc
    ρ g v = ρ.asModuleEquiv (((endFieldRep ρ) g) m) := by
      simpa only [m, ρ.asModuleEquiv.apply_symm_apply] using
        (endFieldRep_apply' ρ g m).symm
    _ = ρ.asModuleEquiv m := hgm
    _ = v := ρ.asModuleEquiv.apply_symm_apply v

private theorem theorem_9_7_le_endFieldRep_ker_of_le_ker_sec9
    {F : Type*} [Field F]
    {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) {H : Subgroup G}
    (hHker : H ≤ ρ.ker) :
    H ≤ (endFieldRep ρ).ker := by
  intro g hg
  have hgρ : ρ g = 1 := MonoidHom.mem_ker.mp (hHker hg)
  rw [MonoidHom.mem_ker]
  ext m
  apply ρ.asModuleEquiv.injective
  rw [endFieldRep_apply']
  rw [hgρ]
  simp

private theorem theorem_9_7_quotientCentralizerIn_subgroupOf_eq_endFieldRep_ker_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 U C : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hnormalH0 : (H0.subgroupOf MF).Normal)
    (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G))
    (hH0invU :
      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
      IsInvariant U MF (H0.subgroupOf MF))
    (hbarElem :
      letI : (H0.subgroupOf MF).Normal := hnormalH0
      IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF))
    (hC : quotientCentralizerIn MF H0 U C) :
    letI : (H0.subgroupOf MF).Normal := hnormalH0
    letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
    letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
    letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
      quotientMulDistribMulAction (A := U) (G := MF)
        (H0.subgroupOf MF) hH0invU
    let ρ := Theory.Representation.ofElementaryAbelianAction (A := U)
      (G := MF ⧸ H0.subgroupOf MF) (p := p)
    C.subgroupOf U = (endFieldRep ρ).ker := by
  classical
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
  letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
  letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
    quotientMulDistribMulAction (A := U) (G := MF)
      (H0.subgroupOf MF) hH0invU
  let ρ := Theory.Representation.ofElementaryAbelianAction (A := U)
    (G := MF ⧸ H0.subgroupOf MF) (p := p)
  apply le_antisymm
  · exact
      theorem_9_7_le_endFieldRep_ker_of_le_ker_sec9 ρ
        (by
          simpa [ρ] using
            theorem_9_7_quotientCentralizerIn_subgroupOf_le_elementary_action_ker_sec9
              (MF := MF) (H0 := H0) (U := U) (C := C) (p := p)
              hnormalH0 hUnormMF hH0invU hbarElem hC)
  · exact
      le_trans (theorem_9_7_endFieldRep_ker_le_ker_sec9 ρ)
        (by
          simpa [ρ] using
            theorem_9_7_elementary_action_ker_le_quotientCentralizerIn_subgroupOf_sec9
              (MF := MF) (H0 := H0) (U := U) (C := C) (p := p)
              hnormalH0 hUnormMF hH0invU hbarElem hC)

set_option backward.isDefEq.respectTransparency false in
private theorem theorem_9_7_schurEndFieldFullData_of_commutative_barU_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 U C : Subgroup G} {p q : ℕ}
    (hpprime : Nat.Prime p)
    (hqprime : Nat.Prime q)
    (hnormalH0 : (H0.subgroupOf MF).Normal)
    (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G))
    (hH0inv :
      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
      IsInvariant U MF (H0.subgroupOf MF))
    (hbarElem :
      letI : (H0.subgroupOf MF).Normal := hnormalH0
      IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF))
    (hirredRep :
      letI : Fact p.Prime := ⟨hpprime⟩
      letI : (H0.subgroupOf MF).Normal := hnormalH0
      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
      letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
      letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
        quotientMulDistribMulAction (A := U) (G := MF)
          (H0.subgroupOf MF) hH0inv
      Representation.IsIrreducible
        (Theory.Representation.ofElementaryAbelianAction (A := U)
          (G := MF ⧸ H0.subgroupOf MF) (p := p)))
    (hEndFieldCardAlt :
      letI : Fact p.Prime := ⟨hpprime⟩
      letI : (H0.subgroupOf MF).Normal := hnormalH0
      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
      letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
      letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
        quotientMulDistribMulAction (A := U) (G := MF)
          (H0.subgroupOf MF) hH0inv
      let ρ := Theory.Representation.ofElementaryAbelianAction (A := U)
        (G := MF ⧸ H0.subgroupOf MF) (p := p)
      let E := Module.End (MonoidAlgebra (ZMod p) U) ρ.asModule
      (Nat.card E = p ∧ Module.finrank E ρ.asModule = q) ∨
        (Nat.card E = p ^ q ∧ Module.finrank E ρ.asModule = 1))
    (hC : quotientCentralizerIn MF H0 U C)
    (hnormalC : (C.subgroupOf U).Normal)
    (hbarUcomm :
      letI : (C.subgroupOf U).Normal := hnormalC
      IsMulCommutative (U ⧸ C.subgroupOf U)) :
    theorem_9_7_schurEndFieldFullData_sec9 MF H0 U p q
      hpprime hnormalH0 hUnormMF hH0inv hbarElem := by
  classical
  dsimp [theorem_9_7_schurEndFieldFullData_sec9]
  letI : Fact p.Prime := ⟨hpprime⟩
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
  letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
  letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
    quotientMulDistribMulAction (A := U) (G := MF)
      (H0.subgroupOf MF) hH0inv
  let ρ := Theory.Representation.ofElementaryAbelianAction (A := U)
    (G := MF ⧸ H0.subgroupOf MF) (p := p)
  let E := Module.End (MonoidAlgebra (ZMod p) U) ρ.asModule
  change Nat.card E = p ^ q ∧ Module.finrank E ρ.asModule = 1
  have hρirr : Representation.IsIrreducible ρ := by
    simpa [ρ] using hirredRep
  letI : Representation.IsIrreducible ρ := hρirr
  haveI : FiniteDimensional (ZMod p) (Additive (MF ⧸ H0.subgroupOf MF)) :=
    finiteDimensional_of_irreducible_finite_group ρ hρirr
  have hCkerEnd :
      C.subgroupOf U = (endFieldRep ρ).ker := by
    simpa [ρ] using
      theorem_9_7_quotientCentralizerIn_subgroupOf_eq_endFieldRep_ker_sec9
        (MF := MF) (H0 := H0) (U := U) (C := C) (p := p)
        hnormalH0 hUnormMF hH0inv hbarElem hC
  letI : (C.subgroupOf U).Normal := hnormalC
  letI : (endFieldRep ρ).ker.Normal := MonoidHom.normal_ker (endFieldRep ρ)
  have hEndQuotComm :
      IsMulCommutative (U ⧸ (endFieldRep ρ).ker) :=
    theorem_9_7_quotient_commutative_of_eq_kernel_sec9
      (G := U) (C := C.subgroupOf U) (K := (endFieldRep ρ).ker)
      hbarUcomm hCkerEnd
  have hEndFinrankOne :
      Module.finrank E ρ.asModule = 1 := by
    simpa [ρ, E] using
      theorem_9_7_endFieldRep_finrank_eq_one_of_quotient_kernel_commutative_sec9
        ρ hEndQuotComm
  change (Nat.card E = p ∧ Module.finrank E ρ.asModule = q) ∨
      (Nat.card E = p ^ q ∧ Module.finrank E ρ.asModule = 1) at hEndFieldCardAlt
  rcases hEndFieldCardAlt with hprime | hfull
  · exfalso
    have hq_one : q = 1 := hprime.2.symm.trans hEndFinrankOne
    exact hqprime.ne_one hq_one
  · exact hfull


private noncomputable def theorem_9_7_oneDimLinearEquivOfFinrankEqOne_sec9
    {E W : Type*} [Field E] [AddCommGroup W] [Module E W]
    [Module.Finite E W] [Module.Free E W]
    (hfin : Module.finrank E W = 1) : W ≃ₗ[E] E :=
  (Module.nonempty_linearEquiv_of_finrank_eq_one hfin).some.symm

private theorem theorem_9_7_exists_oneDimLinearEquiv_apply_eq_one_sec9
    {E W : Type*} [Field E] [AddCommGroup W] [Module E W]
    [Module.Finite E W] [Module.Free E W]
    (hfin : Module.finrank E W = 1) (v : W) (hv : v ≠ 0) :
    ∃ e : W ≃ₗ[E] E, e v = 1 := by
  classical
  let e0 : W ≃ₗ[E] E :=
    theorem_9_7_oneDimLinearEquivOfFinrankEqOne_sec9
      (E := E) (W := W) hfin
  have hc : e0 v ≠ 0 := by
    intro h
    apply hv
    exact e0.injective (by simpa using h)
  let c : Eˣ := Units.mk0 (e0 v) hc
  let m : E ≃ₗ[E] E :=
    { toFun := fun z => (↑c)⁻¹ * z
      invFun := fun z => ↑c * z
      left_inv := by intro z; simp
      right_inv := by intro z; simp
      map_add' := by intro x y; simp [mul_add]
      map_smul' := by
        intro a x
        change (↑c)⁻¹ * (a * x) = a * ((↑c)⁻¹ * x)
        ring }
  refine ⟨e0.trans m, ?_⟩
  change (e0 v)⁻¹ * e0 v = 1
  exact inv_mul_cancel₀ hc


private noncomputable def theorem_9_7_endUnitScalarEquivOfLinearEquiv_sec9
    {E W : Type*} [Field E] [AddCommGroup W] [Module E W]
    (e : W ≃ₗ[E] E) : (Module.End E W)ˣ ≃* Eˣ :=
  (Units.mapEquiv e.conjRingEquiv.toMulEquiv).trans
    ((Units.mapEquiv (RingEquiv.moduleEndSelf E).symm.toMulEquiv).trans
      (Units.mapEquiv (MulOpposite.opMulEquiv : E ≃* Eᵐᵒᵖ).symm))

private theorem theorem_9_7_endUnitScalarEquiv_apply_sec9
    {E W : Type*} [Field E] [AddCommGroup W] [Module E W]
    (e : W ≃ₗ[E] E) (T : (Module.End E W)ˣ) (m : W) :
    e ((T : Module.End E W) m) =
      ((theorem_9_7_endUnitScalarEquivOfLinearEquiv_sec9 e T : Eˣ) : E) * e m := by
  let f : Module.End E E := e.conjRingEquiv (T : Module.End E W)
  have hf_apply : f (e m) = e ((T : Module.End E W) m) := by
    simp [f, LinearEquiv.conjRingEquiv_apply_apply]
  have hf_linear : f (e m) = e m * f 1 := by
    calc
      f (e m) = f ((e m) • (1 : E)) := by simp
      _ = (e m) • f 1 := by rw [map_smul]
      _ = e m * f 1 := by simp [smul_eq_mul]
  have hscalar :
      ((theorem_9_7_endUnitScalarEquivOfLinearEquiv_sec9 e T : Eˣ) : E) = f 1 := by
    dsimp [theorem_9_7_endUnitScalarEquivOfLinearEquiv_sec9]
    change MulOpposite.unop ((RingEquiv.moduleEndSelf E).symm
      (e.conjRingEquiv (T : Module.End E W))) = f 1
    rw [RingEquiv.moduleEndSelf_symm_apply]
    simp [f, LinearEquiv.conjRingEquiv_apply_apply]
  rw [← hf_apply, hf_linear, hscalar, mul_comm]

private def theorem_9_7_schurFieldHomRawData_sec9
    {G : Type u} [Group G] [Finite G]
    (MF H0 U C W1 : Subgroup G)
    (hnormalH0 : (H0.subgroupOf MF).Normal)
    (hnormalC : (C.subgroupOf U).Normal)
    (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G))
    (hCinv :
      letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
      IsInvariant W1 U (C.subgroupOf U)) : Prop :=
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  letI : (C.subgroupOf U).Normal := hnormalC
  letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
  letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
    quotientMulDistribMulAction (A := W1) (G := U)
      (C.subgroupOf U) hCinv
  ∃ F : Type u, ∃ fieldInst : Field F, ∃ fintypeInst : Fintype F,
    letI : Field F := fieldInst
    letI : Fintype F := fintypeInst
    ∃ Ustar : Subgroup Fˣ,
      AddSubgroup.closure
        (((fun x : Ustar => ((x : Fˣ) : F)) '' Set.univ) : Set F) = ⊤ ∧
        ∃ φH : (MF ⧸ H0.subgroupOf MF) ≃* Multiplicative F,
          ∃ φU : (U ⧸ C.subgroupOf U) ≃* Ustar,
            ∃ φW : W1 →* RingAut F,
              Function.Injective φW ∧
              (∀ x : U ⧸ C.subgroupOf U, ∀ h : MF,
                ∃ hconjMF : ∀ y : MF,
                  (x.out : U)⁻¹ * (y : G) * (x.out : U) ∈ MF,
                  φH (QuotientGroup.mk' (H0.subgroupOf MF)
                    ⟨(x.out : U)⁻¹ * (h : G) * (x.out : U), hconjMF h⟩) =
                    Multiplicative.ofAdd (((φU x : Ustar) : Fˣ) *
                      Multiplicative.toAdd
                        (φH (QuotientGroup.mk' (H0.subgroupOf MF) h)))) ∧
                ∀ w : W1, ∀ h : MF,
                  ∃ hconjMF : ∀ y : MF,
                    (w : G)⁻¹ * (y : G) * (w : G) ∈ MF,
                    φH (QuotientGroup.mk' (H0.subgroupOf MF)
                      ⟨(w : G)⁻¹ * (h : G) * (w : G), hconjMF h⟩) =
                      Multiplicative.ofAdd
                        ((φW w) (Multiplicative.toAdd
                          (φH (QuotientGroup.mk' (H0.subgroupOf MF) h)))) ∧
                  ∀ x : U ⧸ C.subgroupOf U,
                    ((φU x : Ustar) : Fˣ) ∈ Ustar ∧
                      Units.map (φW w).toMonoidHom (φU x : Ustar) ∈ Ustar ∧
                      Units.map (φW w).toMonoidHom (φU x : Ustar) =
                        (φU ((w⁻¹ : W1) • x) : Ustar)

private def theorem_9_7_schurFieldHomCompatibilityRawData_sec9
    {G : Type u} [Group G] [Finite G]
    (MF H0 U C W1 : Subgroup G)
    (hnormalH0 : (H0.subgroupOf MF).Normal)
    (hnormalC : (C.subgroupOf U).Normal)
    (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G))
    (hCinv :
      letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
      IsInvariant W1 U (C.subgroupOf U)) : Prop :=
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  letI : (C.subgroupOf U).Normal := hnormalC
  letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
  letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
    quotientMulDistribMulAction (A := W1) (G := U)
      (C.subgroupOf U) hCinv
  ∃ F : Type u, ∃ fieldInst : Field F, ∃ fintypeInst : Fintype F,
    letI : Field F := fieldInst
    letI : Fintype F := fintypeInst
    ∃ Ustar : Subgroup Fˣ,
      AddSubgroup.closure
        (((fun x : Ustar => ((x : Fˣ) : F)) '' Set.univ) : Set F) = ⊤ ∧
        ∃ φH : (MF ⧸ H0.subgroupOf MF) ≃* Multiplicative F,
          ∃ φU : (U ⧸ C.subgroupOf U) ≃* Ustar,
            ∃ φW : W1 →* RingAut F,
              Function.Injective φW ∧
              (∀ x : U ⧸ C.subgroupOf U, ∀ h : MF,
                ∃ hconjMF : ∀ y : MF,
                  (x.out : U)⁻¹ * (y : G) * (x.out : U) ∈ MF,
                  φH (QuotientGroup.mk' (H0.subgroupOf MF)
                    ⟨(x.out : U)⁻¹ * (h : G) * (x.out : U), hconjMF h⟩) =
                    Multiplicative.ofAdd (((φU x : Ustar) : Fˣ) *
                      Multiplicative.toAdd
                        (φH (QuotientGroup.mk' (H0.subgroupOf MF) h)))) ∧
                ∀ w : W1, ∀ h : MF,
                  ∃ hconjMF : ∀ y : MF,
                    (w : G)⁻¹ * (y : G) * (w : G) ∈ MF,
                    φH (QuotientGroup.mk' (H0.subgroupOf MF)
                      ⟨(w : G)⁻¹ * (h : G) * (w : G), hconjMF h⟩) =
                      Multiplicative.ofAdd
                        ((φW w) (Multiplicative.toAdd
                          (φH (QuotientGroup.mk' (H0.subgroupOf MF) h)))) ∧
                  ∀ x : U ⧸ C.subgroupOf U,
                    Units.map (φW w).toMonoidHom (φU x : Ustar) =
                      (φU ((w⁻¹ : W1) • x) : Ustar)

private def theorem_9_7_schurFieldHomCompatibilityNoninjectiveRawData_sec9
    {G : Type u} [Group G] [Finite G]
    (MF H0 U C W1 : Subgroup G)
    (hnormalH0 : (H0.subgroupOf MF).Normal)
    (hnormalC : (C.subgroupOf U).Normal)
    (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G))
    (hCinv :
      letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
      IsInvariant W1 U (C.subgroupOf U)) : Prop :=
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  letI : (C.subgroupOf U).Normal := hnormalC
  letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
  letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
    quotientMulDistribMulAction (A := W1) (G := U)
      (C.subgroupOf U) hCinv
  ∃ F : Type u, ∃ fieldInst : Field F, ∃ fintypeInst : Fintype F,
    letI : Field F := fieldInst
    letI : Fintype F := fintypeInst
    ∃ Ustar : Subgroup Fˣ,
      AddSubgroup.closure
        (((fun x : Ustar => ((x : Fˣ) : F)) '' Set.univ) : Set F) = ⊤ ∧
        ∃ φH : (MF ⧸ H0.subgroupOf MF) ≃* Multiplicative F,
          ∃ φU : (U ⧸ C.subgroupOf U) ≃* Ustar,
            ∃ φW : W1 →* RingAut F,
              (∀ x : U ⧸ C.subgroupOf U, ∀ h : MF,
                ∃ hconjMF : ∀ y : MF,
                  (x.out : U)⁻¹ * (y : G) * (x.out : U) ∈ MF,
                  φH (QuotientGroup.mk' (H0.subgroupOf MF)
                    ⟨(x.out : U)⁻¹ * (h : G) * (x.out : U), hconjMF h⟩) =
                    Multiplicative.ofAdd (((φU x : Ustar) : Fˣ) *
                      Multiplicative.toAdd
                        (φH (QuotientGroup.mk' (H0.subgroupOf MF) h)))) ∧
                ∀ w : W1, ∀ h : MF,
                  ∃ hconjMF : ∀ y : MF,
                    (w : G)⁻¹ * (y : G) * (w : G) ∈ MF,
                    φH (QuotientGroup.mk' (H0.subgroupOf MF)
                      ⟨(w : G)⁻¹ * (h : G) * (w : G), hconjMF h⟩) =
                      Multiplicative.ofAdd
                        ((φW w) (Multiplicative.toAdd
                          (φH (QuotientGroup.mk' (H0.subgroupOf MF) h)))) ∧
                  ∀ x : U ⧸ C.subgroupOf U,
                      Units.map (φW w).toMonoidHom (φU x : Ustar) =
                        (φU ((w⁻¹ : W1) • x) : Ustar)

private def theorem_9_7_schurFieldHomCompatibilityAdditiveActionRawData_sec9
    {G : Type u} [Group G] [Finite G]
    (MF H0 U C W1 : Subgroup G)
    (hnormalH0 : (H0.subgroupOf MF).Normal)
    (hnormalC : (C.subgroupOf U).Normal)
    (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G))
    (hCinv :
      letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
      IsInvariant W1 U (C.subgroupOf U)) : Prop :=
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  letI : (C.subgroupOf U).Normal := hnormalC
  letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
  letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
    quotientMulDistribMulAction (A := W1) (G := U)
      (C.subgroupOf U) hCinv
  ∃ F : Type u, ∃ fieldInst : Field F, ∃ fintypeInst : Fintype F,
    letI : Field F := fieldInst
    letI : Fintype F := fintypeInst
    ∃ Ustar : Subgroup Fˣ,
      AddSubgroup.closure
        (((fun x : Ustar => ((x : Fˣ) : F)) '' Set.univ) : Set F) = ⊤ ∧
        ∃ φH : (MF ⧸ H0.subgroupOf MF) ≃* Multiplicative F,
          ∃ φU : (U ⧸ C.subgroupOf U) ≃* Ustar,
            ∃ φWadd : W1 → F ≃+ F,
              (∀ x : U ⧸ C.subgroupOf U, ∀ h : MF,
                ∃ hconjMF : ∀ y : MF,
                  (x.out : U)⁻¹ * (y : G) * (x.out : U) ∈ MF,
                  φH (QuotientGroup.mk' (H0.subgroupOf MF)
                    ⟨(x.out : U)⁻¹ * (h : G) * (x.out : U), hconjMF h⟩) =
                    Multiplicative.ofAdd (((φU x : Ustar) : Fˣ) *
                      Multiplicative.toAdd
                        (φH (QuotientGroup.mk' (H0.subgroupOf MF) h)))) ∧
                ∀ w : W1, ∀ h : MF,
                  ∃ hconjMF : ∀ y : MF,
                    (w : G)⁻¹ * (y : G) * (w : G) ∈ MF,
                    φH (QuotientGroup.mk' (H0.subgroupOf MF)
                      ⟨(w : G)⁻¹ * (h : G) * (w : G), hconjMF h⟩) =
                      Multiplicative.ofAdd
                        ((φWadd w) (Multiplicative.toAdd
                          (φH (QuotientGroup.mk' (H0.subgroupOf MF) h)))) ∧
                  ∀ x : U ⧸ C.subgroupOf U,
                    (φWadd w) ((((φU x : Ustar) : Fˣ) : F)) =
                      (((φU ((w⁻¹ : W1) • x) : Ustar) : Fˣ) : F)

private noncomputable def theorem_9_7_addEquivToMulEquivMultiplicative_sec9
    (A F : Type u) [Group A] [AddGroup F]
    (e : Additive A ≃+ F) : A ≃* Multiplicative F :=
  { toFun := fun x => Multiplicative.ofAdd (e (Additive.ofMul x))
    invFun := fun y => Additive.toMul (e.symm (Multiplicative.toAdd y))
    left_inv := by
      intro x
      change Additive.toMul (e.symm (e (Additive.ofMul x))) = x
      simp
    right_inv := by
      intro y
      change Multiplicative.ofAdd (e (e.symm (Multiplicative.toAdd y))) = y
      simp
    map_mul' := by
      intro x y
      simp }

private def theorem_9_7_schurFieldCoordinateAdditiveActionRawData_sec9
    {G : Type u} [Group G] [Finite G]
    (MF H0 U C W1 : Subgroup G)
    (hnormalH0 : (H0.subgroupOf MF).Normal)
    (hnormalC : (C.subgroupOf U).Normal)
    (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G))
    (hCinv :
      letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
      IsInvariant W1 U (C.subgroupOf U)) : Prop :=
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  letI : (C.subgroupOf U).Normal := hnormalC
  letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
  letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
    quotientMulDistribMulAction (A := W1) (G := U)
      (C.subgroupOf U) hCinv
  ∃ F : Type u, ∃ fieldInst : Field F, ∃ fintypeInst : Fintype F,
    letI : Field F := fieldInst
    letI : Fintype F := fintypeInst
    ∃ Ustar : Subgroup Fˣ,
      AddSubgroup.closure
        (((fun x : Ustar => ((x : Fˣ) : F)) '' Set.univ) : Set F) = ⊤ ∧
        ∃ s : MF ⧸ H0.subgroupOf MF,
          s ≠ 1 ∧
          ∃ φHadd : Additive (MF ⧸ H0.subgroupOf MF) ≃+ F,
            ∃ φU : (U ⧸ C.subgroupOf U) ≃* Ustar,
              ∃ φWadd : W1 → F ≃+ F,
                (∀ x : U ⧸ C.subgroupOf U, ∀ h : MF,
                  ∃ hconjMF : ∀ y : MF,
                    (x.out : U)⁻¹ * (y : G) * (x.out : U) ∈ MF,
                    φHadd (Additive.ofMul
                      (QuotientGroup.mk' (H0.subgroupOf MF)
                        ⟨(x.out : U)⁻¹ * (h : G) * (x.out : U),
                          hconjMF h⟩)) =
                      (((φU x : Ustar) : Fˣ) : F) *
                        φHadd (Additive.ofMul
                          (QuotientGroup.mk' (H0.subgroupOf MF) h))) ∧
                  ∀ w : W1, ∀ h : MF,
                    ∃ hconjMF : ∀ y : MF,
                      (w : G)⁻¹ * (y : G) * (w : G) ∈ MF,
                      φHadd (Additive.ofMul
                        (QuotientGroup.mk' (H0.subgroupOf MF)
                          ⟨(w : G)⁻¹ * (h : G) * (w : G),
                            hconjMF h⟩)) =
                        (φWadd w) (φHadd (Additive.ofMul
                          (QuotientGroup.mk' (H0.subgroupOf MF) h))) ∧
                      ∀ x : U ⧸ C.subgroupOf U,
                        (φWadd w) ((((φU x : Ustar) : Fˣ) : F)) =
                          (((φU ((w⁻¹ : W1) • x) : Ustar) : Fˣ) : F)

private def theorem_9_7_schurFieldCoordinateAdditiveActionNoVectorRawData_sec9
    {G : Type u} [Group G] [Finite G]
    (MF H0 U C W1 : Subgroup G)
    (hnormalH0 : (H0.subgroupOf MF).Normal)
    (hnormalC : (C.subgroupOf U).Normal)
    (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G))
    (hCinv :
      letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
      IsInvariant W1 U (C.subgroupOf U)) : Prop :=
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  letI : (C.subgroupOf U).Normal := hnormalC
  letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
  letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
    quotientMulDistribMulAction (A := W1) (G := U)
      (C.subgroupOf U) hCinv
  ∃ F : Type u, ∃ fieldInst : Field F, ∃ fintypeInst : Fintype F,
    letI : Field F := fieldInst
    letI : Fintype F := fintypeInst
    ∃ Ustar : Subgroup Fˣ,
      AddSubgroup.closure
        (((fun x : Ustar => ((x : Fˣ) : F)) '' Set.univ) : Set F) = ⊤ ∧
        ∃ φHadd : Additive (MF ⧸ H0.subgroupOf MF) ≃+ F,
          ∃ φU : (U ⧸ C.subgroupOf U) ≃* Ustar,
            ∃ φWadd : W1 → F ≃+ F,
              (∀ x : U ⧸ C.subgroupOf U, ∀ h : MF,
                ∃ hconjMF : ∀ y : MF,
                  (x.out : U)⁻¹ * (y : G) * (x.out : U) ∈ MF,
                  φHadd (Additive.ofMul
                    (QuotientGroup.mk' (H0.subgroupOf MF)
                      ⟨(x.out : U)⁻¹ * (h : G) * (x.out : U),
                        hconjMF h⟩)) =
                    (((φU x : Ustar) : Fˣ) : F) *
                      φHadd (Additive.ofMul
                        (QuotientGroup.mk' (H0.subgroupOf MF) h))) ∧
                ∀ w : W1, ∀ h : MF,
                  ∃ hconjMF : ∀ y : MF,
                    (w : G)⁻¹ * (y : G) * (w : G) ∈ MF,
                    φHadd (Additive.ofMul
                      (QuotientGroup.mk' (H0.subgroupOf MF)
                        ⟨(w : G)⁻¹ * (h : G) * (w : G),
                          hconjMF h⟩)) =
                      (φWadd w) (φHadd (Additive.ofMul
                        (QuotientGroup.mk' (H0.subgroupOf MF) h))) ∧
                    ∀ x : U ⧸ C.subgroupOf U,
                      (φWadd w) ((((φU x : Ustar) : Fˣ) : F)) =
                        (((φU ((w⁻¹ : W1) • x) : Ustar) : Fˣ) : F)

private def theorem_9_7_schurFieldCoordinateAdditiveActionUData_sec9
    {G : Type u} [Group G] [Finite G]
    (MF H0 U C W1 : Subgroup G)
    (hnormalH0 : (H0.subgroupOf MF).Normal)
    (hnormalC : (C.subgroupOf U).Normal)
    (hW1normMF : W1 ≤ Subgroup.normalizer (MF : Set G))
    (hH0invW1 :
      letI : Subgroup.Normalizes W1 MF := ⟨hW1normMF⟩
      IsInvariant W1 MF (H0.subgroupOf MF)) : Prop :=
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  letI : (C.subgroupOf U).Normal := hnormalC
  letI : Subgroup.Normalizes W1 MF := ⟨hW1normMF⟩
  letI : MulDistribMulAction W1 (MF ⧸ H0.subgroupOf MF) :=
    quotientMulDistribMulAction (A := W1) (G := MF)
      (H0.subgroupOf MF) hH0invW1
  ∃ F : Type u, ∃ fieldInst : Field F, ∃ fintypeInst : Fintype F,
    letI : Field F := fieldInst
    letI : Fintype F := fintypeInst
    ∃ Ustar : Subgroup Fˣ,
      ∃ φHadd : Additive (MF ⧸ H0.subgroupOf MF) ≃+ F,
        ∃ φU : (U ⧸ C.subgroupOf U) ≃* Ustar,
          (∀ x : U, ∀ h : MF,
              ∃ hconjMF : ∀ y : MF,
                (x : G)⁻¹ * (y : G) * (x : G) ∈ MF,
                φHadd (Additive.ofMul
                  (QuotientGroup.mk' (H0.subgroupOf MF)
                    ⟨(x : G)⁻¹ * (h : G) * (x : G),
                      hconjMF h⟩)) =
                  (((φU (QuotientGroup.mk' (C.subgroupOf U) x) : Ustar) : Fˣ) : F) *
                    φHadd (Additive.ofMul
                      (QuotientGroup.mk' (H0.subgroupOf MF) h))) ∧
            ∀ w : W1,
              (φHadd.symm.trans
                ((MulEquiv.toAdditive
                  (MulDistribMulAction.toMulAut W1 (MF ⧸ H0.subgroupOf MF)
                    (w⁻¹ : W1))).trans φHadd)) 1 = 1

private noncomputable def theorem_9_7_schurQuotientWAddEquiv_sec9
    {G : Type u} [Group G] [Finite G]
    (MF H0 W1 : Subgroup G)
    (hnormalH0 : (H0.subgroupOf MF).Normal)
    (hW1normMF : W1 ≤ Subgroup.normalizer (MF : Set G))
    (hH0invW1 :
      letI : Subgroup.Normalizes W1 MF := ⟨hW1normMF⟩
      IsInvariant W1 MF (H0.subgroupOf MF))
    (F : Type u) [AddCommGroup F]
    (φHadd : Additive (MF ⧸ H0.subgroupOf MF) ≃+ F) :
    W1 → F ≃+ F := by
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  letI : Subgroup.Normalizes W1 MF := ⟨hW1normMF⟩
  letI : MulDistribMulAction W1 (MF ⧸ H0.subgroupOf MF) :=
    quotientMulDistribMulAction (A := W1) (G := MF)
      (H0.subgroupOf MF) hH0invW1
  exact fun w =>
    φHadd.symm.trans
      ((MulEquiv.toAdditive
        (MulDistribMulAction.toMulAut W1 (MF ⧸ H0.subgroupOf MF)
          (w⁻¹ : W1))).trans φHadd)

private theorem theorem_9_7_schurQuotientWAddEquiv_action_sec9
    {G : Type u} [Group G] [Finite G]
    (MF H0 W1 : Subgroup G)
    (hnormalH0 : (H0.subgroupOf MF).Normal)
    (hW1normMF : W1 ≤ Subgroup.normalizer (MF : Set G))
    (hH0invW1 :
      letI : Subgroup.Normalizes W1 MF := ⟨hW1normMF⟩
      IsInvariant W1 MF (H0.subgroupOf MF))
    (F : Type u) [AddCommGroup F]
    (φHadd : Additive (MF ⧸ H0.subgroupOf MF) ≃+ F) :
    letI : (H0.subgroupOf MF).Normal := hnormalH0
    letI : Subgroup.Normalizes W1 MF := ⟨hW1normMF⟩
    letI : MulDistribMulAction W1 (MF ⧸ H0.subgroupOf MF) :=
      quotientMulDistribMulAction (A := W1) (G := MF)
        (H0.subgroupOf MF) hH0invW1
    ∀ w : W1, ∀ h : MF,
      ∃ hconjMF : ∀ y : MF,
        (w : G)⁻¹ * (y : G) * (w : G) ∈ MF,
        φHadd (Additive.ofMul
          (QuotientGroup.mk' (H0.subgroupOf MF)
            ⟨(w : G)⁻¹ * (h : G) * (w : G), hconjMF h⟩)) =
          (theorem_9_7_schurQuotientWAddEquiv_sec9
            MF H0 W1 hnormalH0 hW1normMF hH0invW1 F φHadd w)
            (φHadd (Additive.ofMul
              (QuotientGroup.mk' (H0.subgroupOf MF) h))) := by
  classical
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  letI : Subgroup.Normalizes W1 MF := ⟨hW1normMF⟩
  letI : MulDistribMulAction W1 (MF ⧸ H0.subgroupOf MF) :=
    quotientMulDistribMulAction (A := W1) (G := MF)
      (H0.subgroupOf MF) hH0invW1
  intro w h
  let winv : W1 := w⁻¹
  have hconjMF : ∀ y : MF, (w : G)⁻¹ * (y : G) * (w : G) ∈ MF := by
    intro y
    have hy : (((winv : W1) • y : MF) : G) ∈ MF :=
      (((winv : W1) • y : MF).property)
    simpa [winv, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
      mul_assoc] using hy
  refine ⟨hconjMF, ?_⟩
  let H0MF : Subgroup MF := H0.subgroupOf MF
  let qh : MF ⧸ H0MF := QuotientGroup.mk' H0MF h
  let hConj : MF :=
    ⟨(w : G)⁻¹ * (h : G) * (w : G), hconjMF h⟩
  let qconj : MF ⧸ H0MF := QuotientGroup.mk' H0MF hConj
  have hsmul_eq : ((winv : W1) • h : MF) = hConj := by
    apply Subtype.ext
    simp [winv, hConj, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
      mul_assoc]
  have hsmul_mk :
      (winv : W1) • QuotientGroup.mk' H0MF h =
        QuotientGroup.mk' H0MF ((winv : W1) • h) := by
    simpa only [QuotientGroup.mk'_apply] using
      (MulAction.Quotient.smul_mk (H := H0MF) (winv : W1) h)
  have hq : (winv : W1) • qh = qconj := by
    rw [hsmul_mk, hsmul_eq]
  change φHadd (Additive.ofMul qconj) =
    (theorem_9_7_schurQuotientWAddEquiv_sec9
      MF H0 W1 hnormalH0 hW1normMF hH0invW1 F φHadd w)
      (φHadd (Additive.ofMul qh))
  rw [← hq]
  simp [theorem_9_7_schurQuotientWAddEquiv_sec9, winv,
    MulDistribMulAction.toMulAut_apply]

private theorem theorem_9_7_additive_span_units_of_irreducible_scalar_action_sec9
    {A Q F : Type u} [Group A] [Group Q] [Field F]
    {p : ℕ} [Fact p.Prime]
    [IsElementaryAbelian p Q] [MulDistribMulAction A Q]
    (hirred :
      Representation.IsIrreducible
        (Theory.Representation.ofElementaryAbelianAction (A := A) (G := Q) (p := p)))
    (Ustar : Subgroup Fˣ)
    (φ : Additive Q ≃+ F)
    (ψ : A → Ustar)
    (hψsurj : Function.Surjective ψ)
    (haction : ∀ a : A, ∀ q : Q,
      φ (Additive.ofMul (a • q)) =
        (((ψ a : Ustar) : Fˣ) : F) * φ (Additive.ofMul q)) :
    AddSubgroup.closure
      (((fun x : Ustar => ((x : Fˣ) : F)) '' Set.univ) : Set F) = ⊤ := by
  classical
  let S : Set F := (((fun x : Ustar => ((x : Fˣ) : F)) '' Set.univ) : Set F)
  let B : AddSubgroup F := AddSubgroup.closure S
  have hB_mul (a : A) {z : F} (hz : z ∈ B) :
      (((ψ a : Ustar) : Fˣ) : F) * z ∈ B := by
    exact AddSubgroup.closure_induction (k := S)
      (p := fun z _hz => (((ψ a : Ustar) : Fˣ) : F) * z ∈ B)
      (fun z hzS => by
        rcases hzS with ⟨u, _hu, rfl⟩
        have hgen :
            ((((ψ a) * u : Ustar) : Fˣ) : F) ∈ B := by
          exact AddSubgroup.subset_closure
            (show ((((ψ a) * u : Ustar) : Fˣ) : F) ∈ S from
              ⟨(ψ a) * u, Set.mem_univ _, rfl⟩)
        simpa using hgen)
      (by simp [B])
      (fun x y _hx _hy hx hy => by
        change (((ψ a : Ustar) : Fˣ) : F) * (x + y) ∈ B
        rw [mul_add]
        exact B.add_mem hx hy)
      (fun x _hx hx => by
        change (((ψ a : Ustar) : Fˣ) : F) * (-x) ∈ B
        rw [mul_neg]
        exact B.neg_mem hx)
      hz
  let Padd : AddSubgroup (Additive Q) := B.comap φ.toAddMonoidHom
  let Psub : Submodule (ZMod p) (Additive Q) :=
    AddSubgroup.toZModSubmodule (n := p) Padd
  let ρ := Theory.Representation.ofElementaryAbelianAction (A := A) (G := Q) (p := p)
  let R : Subrepresentation ρ :=
    { toSubmodule := Psub
      apply_mem_toSubmodule := by
        intro a v hv
        have hvB : φ v ∈ B := by
          simpa [Psub, Padd] using hv
        have hmem : (((ψ a : Ustar) : Fˣ) : F) * φ v ∈ B :=
          hB_mul a hvB
        have hmem' : φ (Additive.ofMul (a • Additive.toMul v)) ∈ B := by
          rw [haction a (Additive.toMul v)]
          simpa using hmem
        change φ ((ρ a) v) ∈ B
        simpa [ρ] using hmem' }
  letI : Representation.IsIrreducible ρ := hirred
  have hR_ne_bot : R ≠ ⊥ := by
    intro hbot
    have hpre_one : φ.symm 1 ∈ R.toSubmodule := by
      have hgen : (1 : F) ∈ B := by
        rcases hψsurj 1 with ⟨a, ha⟩
        exact AddSubgroup.subset_closure
          (show (1 : F) ∈ S from by
            refine ⟨ψ a, Set.mem_univ _, ?_⟩
            simp [ha])
      simpa [R, Psub, Padd] using hgen
    have hzero : φ.symm 1 = 0 :=
      (Representation.eq_bot_iff.mp hbot) (φ.symm 1) hpre_one
    have hone_zero := congrArg φ hzero
    simp at hone_zero
  have hR_top : R = ⊤ := by
    rcases (inferInstance : Representation.IsIrreducible ρ).eq_bot_or_eq_top R with
      hbot | htop
    · exact False.elim (hR_ne_bot hbot)
    · exact htop
  apply eq_top_iff.mpr
  intro z _hz
  rcases φ.surjective z with ⟨v, rfl⟩
  have hvR : v ∈ R.toSubmodule := by
    rw [hR_top]
    exact trivial
  simpa [R, Psub, Padd, B, S, Set.image_univ]
    using hvR

set_option maxHeartbeats 800000 in
private theorem theorem_9_7_schurQuotientWAddEquiv_unit_compat_of_fixed_one_sec9
    {G : Type u} [Group G] [Finite G]
    (MF H0 U C W1 : Subgroup G)
    (hnormalH0 : (H0.subgroupOf MF).Normal)
    (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G))
    (hH0invU :
      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
      IsInvariant U MF (H0.subgroupOf MF))
    (hnormalC : (C.subgroupOf U).Normal)
    (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G))
    (hCinv :
      letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
      IsInvariant W1 U (C.subgroupOf U))
    (hW1normMF : W1 ≤ Subgroup.normalizer (MF : Set G))
    (hH0invW1 :
      letI : Subgroup.Normalizes W1 MF := ⟨hW1normMF⟩
      IsInvariant W1 MF (H0.subgroupOf MF))
    (F : Type u) [Field F]
    (Ustar : Subgroup Fˣ)
    (φHadd : Additive (MF ⧸ H0.subgroupOf MF) ≃+ F)
    (φU : (U ⧸ C.subgroupOf U) ≃* Ustar)
    (hUactionRep : ∀ x : U, ∀ h : MF,
      ∃ hconjMF : ∀ y : MF,
        (x : G)⁻¹ * (y : G) * (x : G) ∈ MF,
        φHadd (Additive.ofMul
          (QuotientGroup.mk' (H0.subgroupOf MF)
            ⟨(x : G)⁻¹ * (h : G) * (x : G), hconjMF h⟩)) =
          (((φU (QuotientGroup.mk' (C.subgroupOf U) x) :
                Ustar) : Fˣ) : F) *
            φHadd (Additive.ofMul
              (QuotientGroup.mk' (H0.subgroupOf MF) h)))
    (hfixedOne : ∀ w : W1,
      (theorem_9_7_schurQuotientWAddEquiv_sec9
        MF H0 W1 hnormalH0 hW1normMF hH0invW1 F φHadd w) 1 = 1) :
    letI : (C.subgroupOf U).Normal := hnormalC
    letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
    letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
      quotientMulDistribMulAction (A := W1) (G := U)
        (C.subgroupOf U) hCinv
    ∀ w : W1, ∀ x : U ⧸ C.subgroupOf U,
      (theorem_9_7_schurQuotientWAddEquiv_sec9
        MF H0 W1 hnormalH0 hW1normMF hH0invW1 F φHadd w)
        ((((φU x : Ustar) : Fˣ) : F)) =
        (((φU ((w⁻¹ : W1) • x) : Ustar) : Fˣ) : F) := by
  classical
  let H0MF : Subgroup MF := H0.subgroupOf MF
  let CMU : Subgroup U := C.subgroupOf U
  letI : H0MF.Normal := hnormalH0
  letI : CMU.Normal := hnormalC
  letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
  letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
  letI : Subgroup.Normalizes W1 MF := ⟨hW1normMF⟩
  letI : MulDistribMulAction U (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := U) (G := MF) H0MF hH0invU
  letI : MulDistribMulAction W1 (U ⧸ CMU) :=
    quotientMulDistribMulAction (A := W1) (G := U) CMU hCinv
  letI : MulDistribMulAction W1 (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := W1) (G := MF) H0MF hH0invW1
  let η : W1 → F ≃+ F :=
    theorem_9_7_schurQuotientWAddEquiv_sec9
      MF H0 W1 hnormalH0 hW1normMF hH0invW1 F φHadd
  have hη_apply :
      ∀ w : W1, ∀ qh : MF ⧸ H0MF,
        η w (φHadd (Additive.ofMul qh)) =
          φHadd (Additive.ofMul ((w⁻¹ : W1) • qh)) := by
    intro w qh
    change
      (theorem_9_7_schurQuotientWAddEquiv_sec9
        MF H0 W1 hnormalH0 hW1normMF hH0invW1 F φHadd w)
        (φHadd (Additive.ofMul qh)) =
        φHadd (Additive.ofMul ((w⁻¹ : W1) • qh))
    simp [theorem_9_7_schurQuotientWAddEquiv_sec9,
      MulDistribMulAction.toMulAut_apply]
  have hscalarAction :
      ∀ a : U, ∀ qh : MF ⧸ H0MF,
        φHadd (Additive.ofMul (a • qh)) =
          (((φU (QuotientGroup.mk' CMU a⁻¹) : Ustar) : Fˣ) : F) *
            φHadd (Additive.ofMul qh) := by
    intro a qh
    refine QuotientGroup.induction_on qh ?_
    intro h
    rcases hUactionRep a⁻¹ h with ⟨hconjMF, hφ⟩
    let hConj : MF :=
      ⟨((a⁻¹ : U) : G)⁻¹ * (h : G) * ((a⁻¹ : U) : G), hconjMF h⟩
    have hsmul_eq : (a • h : MF) = hConj := by
      apply Subtype.ext
      simp [hConj, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
        mul_assoc]
    have hsmul_mk :
        a • QuotientGroup.mk' H0MF h =
          QuotientGroup.mk' H0MF (a • h : MF) := by
      simpa only [QuotientGroup.mk'_apply] using
        (MulAction.Quotient.smul_mk (H := H0MF) a h)
    calc
      φHadd (Additive.ofMul (a • QuotientGroup.mk' H0MF h)) =
          φHadd (Additive.ofMul (QuotientGroup.mk' H0MF hConj)) := by
            rw [hsmul_mk, hsmul_eq]
      _ = (((φU (QuotientGroup.mk' CMU a⁻¹) : Ustar) : Fˣ) : F) *
          φHadd (Additive.ofMul (QuotientGroup.mk' H0MF h)) := by
            simpa [H0MF, CMU, hConj] using hφ
  have hconj_action :
      ∀ w : W1, ∀ a : U, ∀ qh : MF ⧸ H0MF,
        w • (a • qh) = ((w • a : U) • (w • qh) : MF ⧸ H0MF) := by
    intro w a qh
    refine QuotientGroup.induction_on qh ?_
    intro h
    have hleft₁ :
        a • QuotientGroup.mk' H0MF h =
          QuotientGroup.mk' H0MF (a • h : MF) := by
      simpa only [QuotientGroup.mk'_apply] using
        (MulAction.Quotient.smul_mk (H := H0MF) a h)
    have hleft₂ :
        w • QuotientGroup.mk' H0MF (a • h : MF) =
          QuotientGroup.mk' H0MF (w • (a • h : MF) : MF) := by
      simpa only [QuotientGroup.mk'_apply] using
        (MulAction.Quotient.smul_mk (H := H0MF) w (a • h : MF))
    have hright₁ :
        w • QuotientGroup.mk' H0MF h =
          QuotientGroup.mk' H0MF (w • h : MF) := by
      simpa only [QuotientGroup.mk'_apply] using
        (MulAction.Quotient.smul_mk (H := H0MF) w h)
    have hright₂ :
        (w • a : U) • QuotientGroup.mk' H0MF (w • h : MF) =
          QuotientGroup.mk' H0MF ((w • a : U) • (w • h : MF) : MF) := by
      simpa only [QuotientGroup.mk'_apply] using
        (MulAction.Quotient.smul_mk (H := H0MF) (w • a : U) (w • h : MF))
    calc
      w • (a • QuotientGroup.mk' H0MF h) =
          QuotientGroup.mk' H0MF (w • (a • h : MF) : MF) := by
            rw [hleft₁, hleft₂]
      _ = QuotientGroup.mk' H0MF ((w • a : U) • (w • h : MF) : MF) := by
            apply congrArg (QuotientGroup.mk' H0MF)
            apply Subtype.ext
            simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
              mul_assoc]
      _ = (w • a : U) • (w • QuotientGroup.mk' H0MF h) := by
            rw [hright₁, hright₂]
  intro w x
  refine QuotientGroup.induction_on x ?_
  intro a
  let qone : MF ⧸ H0MF := Additive.toMul (φHadd.symm 1)
  have hφone : φHadd (Additive.ofMul qone) = 1 := by
    change φHadd (φHadd.symm 1) = 1
    simp
  let winv : W1 := w⁻¹
  have hfixed_qone :
      φHadd (Additive.ofMul (winv • qone : MF ⧸ H0MF)) = 1 := by
    have hη := hη_apply w qone
    have hfix : η w (φHadd (Additive.ofMul qone)) = 1 := by
      simpa [η, hφone] using hfixedOne w
    exact hη.symm.trans hfix
  have hleft_scalar :
      (((φU (QuotientGroup.mk' CMU a) : Ustar) : Fˣ) : F) =
        φHadd (Additive.ofMul (a⁻¹ • qone : MF ⧸ H0MF)) := by
    have hscalar := hscalarAction a⁻¹ qone
    rw [hφone, mul_one] at hscalar
    simpa only [inv_inv] using hscalar.symm
  have hright_scalar :
      (((φU (QuotientGroup.mk' CMU (winv • a : U)) : Ustar) : Fˣ) : F) =
        φHadd (Additive.ofMul
          (((winv • a : U)⁻¹ : U) • (winv • qone : MF ⧸ H0MF))) := by
    have hscalar := hscalarAction ((winv • a : U)⁻¹) (winv • qone)
    rw [hfixed_qone, mul_one] at hscalar
    simpa only [inv_inv] using hscalar.symm
  calc
    η w ((((φU (QuotientGroup.mk' CMU a) : Ustar) : Fˣ) : F)) =
        η w (φHadd (Additive.ofMul (a⁻¹ • qone : MF ⧸ H0MF))) := by
          rw [hleft_scalar]
    _ = φHadd (Additive.ofMul
          (winv • (a⁻¹ • qone : MF ⧸ H0MF) : MF ⧸ H0MF)) := by
          simpa [η, winv] using hη_apply w (a⁻¹ • qone : MF ⧸ H0MF)
    _ = φHadd (Additive.ofMul
          (((winv • a : U)⁻¹ : U) • (winv • qone : MF ⧸ H0MF))) := by
          congr 2
          have hcompat := hconj_action winv (a⁻¹) qone
          simpa [winv, inv_smul_eq_iff] using hcompat
    _ = (((φU (QuotientGroup.mk' CMU (winv • a : U)) : Ustar) : Fˣ) : F) := by
          rw [← hright_scalar]
    _ = (((φU ((w⁻¹ : W1) • QuotientGroup.mk' CMU a) : Ustar) : Fˣ) : F) := by
          simp [CMU, winv]

private theorem
    theorem_9_7_schur_field_model_coordinate_additive_action_tail_compat_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
          quotientChiefFactorData_9_6 M MF H0 W1 hp) →
          quotientCentralizerIn MF H0 U C →
            quotientBarUCardinality U C u →
              (hpprime : Nat.Prime p) →
                (hqprime : Nat.Prime q) →
                    (hnormalH0 : (H0.subgroupOf MF).Normal) →
                      (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G)) →
                        (hH0invU :
                          letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                          IsInvariant U MF (H0.subgroupOf MF)) →
                      (hbarElem :
                        letI : (H0.subgroupOf MF).Normal := hnormalH0
                        IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF)) →
                        (hbarCard :
                          letI : (H0.subgroupOf MF).Normal := hnormalH0
                          Nat.card (MF ⧸ H0.subgroupOf MF) = p ^ q) →
                          (hbarFinrank :
                            letI : Fact p.Prime := ⟨hpprime⟩
                            letI : (H0.subgroupOf MF).Normal := hnormalH0
                            letI : IsElementaryAbelian p
                                (MF ⧸ H0.subgroupOf MF) := hbarElem
                            Module.finrank (ZMod p)
                              (Additive (MF ⧸ H0.subgroupOf MF)) = q) →
                          (hirredRep :
                            letI : Fact p.Prime := ⟨hpprime⟩
                            letI : (H0.subgroupOf MF).Normal := hnormalH0
                            letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                            letI : IsElementaryAbelian p
                                (MF ⧸ H0.subgroupOf MF) := hbarElem
                            letI : MulDistribMulAction U
                                (MF ⧸ H0.subgroupOf MF) :=
                              quotientMulDistribMulAction (A := U) (G := MF)
                                (H0.subgroupOf MF) hH0invU
                            Representation.IsIrreducible
                              (Theory.Representation.ofElementaryAbelianAction (A := U)
                                (G := MF ⧸ H0.subgroupOf MF) (p := p))) →
                          (hnormalC : (C.subgroupOf U).Normal) →
                            (letI : (C.subgroupOf U).Normal := hnormalC
                            IsMulCommutative (U ⧸ C.subgroupOf U)) →
                            (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G)) →
                            (hCinv :
                              letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
                              IsInvariant W1 U (C.subgroupOf U)) →
                            (hW1normMF : W1 ≤ Subgroup.normalizer (MF : Set G)) →
                            (hH0invW1 :
                              letI : Subgroup.Normalizes W1 MF := ⟨hW1normMF⟩
                              IsInvariant W1 MF (H0.subgroupOf MF)) →
                            ∀ F : Type u, ∀ fieldInst : Field F,
                              ∀ fintypeInst : Fintype F,
                              letI : Field F := fieldInst
                              letI : Fintype F := fintypeInst
                              ∀ Ustar : Subgroup Fˣ,
                              ∀ φHadd : Additive (MF ⧸ H0.subgroupOf MF) ≃+ F,
                              ∀ φU : (U ⧸ C.subgroupOf U) ≃* Ustar,
                              (∀ x : U, ∀ h : MF,
                                ∃ hconjMF : ∀ y : MF,
                                  (x : G)⁻¹ * (y : G) * (x : G) ∈ MF,
                                  φHadd (Additive.ofMul
                                    (QuotientGroup.mk' (H0.subgroupOf MF)
                                      ⟨(x : G)⁻¹ * (h : G) * (x : G),
                                        hconjMF h⟩)) =
                                    (((φU (QuotientGroup.mk' (C.subgroupOf U) x) :
                                          Ustar) : Fˣ) : F) *
                                      φHadd (Additive.ofMul
                                        (QuotientGroup.mk' (H0.subgroupOf MF) h))) →
                              (∀ w : W1,
                                (theorem_9_7_schurQuotientWAddEquiv_sec9
                                  MF H0 W1 hnormalH0 hW1normMF hH0invW1
                                  F φHadd w) 1 = 1) →
                              letI : (C.subgroupOf U).Normal := hnormalC
                              letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
                              letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
                                quotientMulDistribMulAction (A := W1) (G := U)
                                  (C.subgroupOf U) hCinv
                              ∀ w : W1, ∀ x : U ⧸ C.subgroupOf U,
                                (theorem_9_7_schurQuotientWAddEquiv_sec9
                                  MF H0 W1 hnormalH0 hW1normMF hH0invW1 F φHadd w)
                                  ((((φU x : Ustar) : Fˣ) : F)) =
                                  (((φU ((w⁻¹ : W1) • x) : Ustar) : Fˣ) : F) := by
  intro _h92 _hp96 _hC _hBarU _hpprime _hqprime hnormalH0 hUnormMF hH0invU
    _hbarElem _hbarCard _hbarFinrank _hirredRep hnormalC _hbarUcomm hW1normU
    hCinv hW1normMF hH0invW1 F fieldInst _fintypeInst Ustar φHadd φU
    hUactionRep hfixedOne
  letI : Field F := fieldInst
  exact
    theorem_9_7_schurQuotientWAddEquiv_unit_compat_of_fixed_one_sec9
      MF H0 U C W1 hnormalH0 hUnormMF hH0invU hnormalC hW1normU hCinv
      hW1normMF hH0invW1 F Ustar φHadd φU hUactionRep hfixedOne

private theorem
    theorem_9_7_schur_field_model_coordinate_additive_action_tail_span_compat_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
          quotientChiefFactorData_9_6 M MF H0 W1 hp) →
          quotientCentralizerIn MF H0 U C →
            quotientBarUCardinality U C u →
              (hpprime : Nat.Prime p) →
                (hqprime : Nat.Prime q) →
                    (hnormalH0 : (H0.subgroupOf MF).Normal) →
                      (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G)) →
                        (hH0invU :
                          letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                          IsInvariant U MF (H0.subgroupOf MF)) →
                      (hbarElem :
                        letI : (H0.subgroupOf MF).Normal := hnormalH0
                        IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF)) →
                        (hbarCard :
                          letI : (H0.subgroupOf MF).Normal := hnormalH0
                          Nat.card (MF ⧸ H0.subgroupOf MF) = p ^ q) →
                          (hbarFinrank :
                            letI : Fact p.Prime := ⟨hpprime⟩
                            letI : (H0.subgroupOf MF).Normal := hnormalH0
                            letI : IsElementaryAbelian p
                                (MF ⧸ H0.subgroupOf MF) := hbarElem
                            Module.finrank (ZMod p)
                              (Additive (MF ⧸ H0.subgroupOf MF)) = q) →
                          (hirredRep :
                            letI : Fact p.Prime := ⟨hpprime⟩
                            letI : (H0.subgroupOf MF).Normal := hnormalH0
                            letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                            letI : IsElementaryAbelian p
                                (MF ⧸ H0.subgroupOf MF) := hbarElem
                            letI : MulDistribMulAction U
                                (MF ⧸ H0.subgroupOf MF) :=
                              quotientMulDistribMulAction (A := U) (G := MF)
                                (H0.subgroupOf MF) hH0invU
                            Representation.IsIrreducible
                              (Theory.Representation.ofElementaryAbelianAction (A := U)
                                (G := MF ⧸ H0.subgroupOf MF) (p := p))) →
                          (hnormalC : (C.subgroupOf U).Normal) →
                            (letI : (C.subgroupOf U).Normal := hnormalC
                            IsMulCommutative (U ⧸ C.subgroupOf U)) →
                            (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G)) →
                            (hCinv :
                              letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
                              IsInvariant W1 U (C.subgroupOf U)) →
                            (hW1normMF : W1 ≤ Subgroup.normalizer (MF : Set G)) →
                            (hH0invW1 :
                              letI : Subgroup.Normalizes W1 MF := ⟨hW1normMF⟩
                              IsInvariant W1 MF (H0.subgroupOf MF)) →
                            ∀ F : Type u, ∀ fieldInst : Field F,
                              ∀ fintypeInst : Fintype F,
                              letI : Field F := fieldInst
                              letI : Fintype F := fintypeInst
                              ∀ Ustar : Subgroup Fˣ,
                              ∀ φHadd : Additive (MF ⧸ H0.subgroupOf MF) ≃+ F,
                              ∀ φU : (U ⧸ C.subgroupOf U) ≃* Ustar,
                              (∀ x : U, ∀ h : MF,
                                ∃ hconjMF : ∀ y : MF,
                                  (x : G)⁻¹ * (y : G) * (x : G) ∈ MF,
                                  φHadd (Additive.ofMul
                                    (QuotientGroup.mk' (H0.subgroupOf MF)
                                      ⟨(x : G)⁻¹ * (h : G) * (x : G),
                                        hconjMF h⟩)) =
                                    (((φU (QuotientGroup.mk' (C.subgroupOf U) x) :
                                          Ustar) : Fˣ) : F) *
                                      φHadd (Additive.ofMul
                                        (QuotientGroup.mk' (H0.subgroupOf MF) h))) →
                              (∀ w : W1,
                                (theorem_9_7_schurQuotientWAddEquiv_sec9
                                  MF H0 W1 hnormalH0 hW1normMF hH0invW1
                                  F φHadd w) 1 = 1) →
                              AddSubgroup.closure
                                (((fun x : Ustar => ((x : Fˣ) : F)) '' Set.univ) :
                                  Set F) = ⊤ ∧
                              letI : (C.subgroupOf U).Normal := hnormalC
                              letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
                              letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
                                quotientMulDistribMulAction (A := W1) (G := U)
                                  (C.subgroupOf U) hCinv
                              ∀ w : W1, ∀ x : U ⧸ C.subgroupOf U,
                                (theorem_9_7_schurQuotientWAddEquiv_sec9
                                  MF H0 W1 hnormalH0 hW1normMF hH0invW1 F φHadd w)
                                  ((((φU x : Ustar) : Fˣ) : F)) =
                                  (((φU ((w⁻¹ : W1) • x) : Ustar) : Fˣ) : F) := by
  intro h92 hp96 hC hBarU hpprime hqprime hnormalH0 hUnormMF hH0invU
    hbarElem hbarCard hbarFinrank hirredRep hnormalC hbarUcomm hW1normU hCinv
    hW1normMF hH0invW1 F fieldInst fintypeInst Ustar φHadd φU hUactionRep
    hfixedOne
  classical
  letI : Field F := fieldInst
  letI : Fintype F := fintypeInst
  letI : Fact p.Prime := ⟨hpprime⟩
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
  letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
  letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
    quotientMulDistribMulAction (A := U) (G := MF)
      (H0.subgroupOf MF) hH0invU
  letI : (C.subgroupOf U).Normal := hnormalC
  letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
  letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
    quotientMulDistribMulAction (A := W1) (G := U) (C.subgroupOf U) hCinv
  let ψ : U → Ustar := fun x => φU (QuotientGroup.mk' (C.subgroupOf U) x⁻¹)
  have hψsurj : Function.Surjective ψ := by
    intro y
    rcases φU.surjective y with ⟨x, rfl⟩
    rcases QuotientGroup.mk'_surjective (C.subgroupOf U) x with ⟨u, rfl⟩
    refine ⟨u⁻¹, ?_⟩
    simp [ψ]
  have hscalarAction :
      ∀ a : U, ∀ qh : MF ⧸ H0.subgroupOf MF,
        φHadd (Additive.ofMul (a • qh)) =
          (((ψ a : Ustar) : Fˣ) : F) * φHadd (Additive.ofMul qh) := by
    intro a qh
    refine QuotientGroup.induction_on qh ?_
    intro h
    rcases hUactionRep a⁻¹ h with ⟨hconjMF, hφ⟩
    let H0MF : Subgroup MF := H0.subgroupOf MF
    let hConj : MF :=
      ⟨((a⁻¹ : U) : G)⁻¹ * (h : G) * ((a⁻¹ : U) : G), hconjMF h⟩
    have hsmul_eq : (a • h : MF) = hConj := by
      apply Subtype.ext
      simp [hConj, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
        mul_assoc]
    have hsmul_mk :
        a • QuotientGroup.mk' H0MF h =
          QuotientGroup.mk' H0MF (a • h : MF) := by
      simpa only [QuotientGroup.mk'_apply] using
        (MulAction.Quotient.smul_mk (H := H0MF) a h)
    calc
      φHadd (Additive.ofMul (a • QuotientGroup.mk' H0MF h)) =
          φHadd (Additive.ofMul (QuotientGroup.mk' H0MF hConj)) := by
            rw [hsmul_mk, hsmul_eq]
      _ = (((ψ a : Ustar) : Fˣ) : F) *
          φHadd (Additive.ofMul (QuotientGroup.mk' H0MF h)) := by
            simpa [ψ, H0MF, hConj] using hφ
  have hspan :
      AddSubgroup.closure
        (((fun x : Ustar => ((x : Fˣ) : F)) '' Set.univ) : Set F) = ⊤ := by
    exact
      theorem_9_7_additive_span_units_of_irreducible_scalar_action_sec9
        (A := U) (Q := MF ⧸ H0.subgroupOf MF) (F := F) (p := p)
        (by simpa using hirredRep) Ustar φHadd ψ hψsurj hscalarAction
  have hcompat :
      ∀ w : W1, ∀ x : U ⧸ C.subgroupOf U,
        (theorem_9_7_schurQuotientWAddEquiv_sec9
          MF H0 W1 hnormalH0 hW1normMF hH0invW1 F φHadd w)
          ((((φU x : Ustar) : Fˣ) : F)) =
          (((φU ((w⁻¹ : W1) • x) : Ustar) : Fˣ) : F) :=
    theorem_9_7_schur_field_model_coordinate_additive_action_tail_compat_source_bridge_sec9
      M MF U W1 W2 H0 C p q u h92 hp96 hC hBarU hpprime hqprime
      hnormalH0 hUnormMF hH0invU hbarElem hbarCard hbarFinrank hirredRep
      hnormalC hbarUcomm hW1normU hCinv hW1normMF hH0invW1
      F fieldInst fintypeInst Ustar φHadd φU hUactionRep hfixedOne
  exact ⟨hspan, hcompat⟩


private def theorem_9_7_schurFieldHomCompatibilityAdditiveRawData_sec9
    {G : Type u} [Group G] [Finite G]
    (MF H0 U C W1 : Subgroup G)
    (hnormalH0 : (H0.subgroupOf MF).Normal)
    (hnormalC : (C.subgroupOf U).Normal)
    (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G))
    (hCinv :
      letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
      IsInvariant W1 U (C.subgroupOf U)) : Prop :=
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  letI : (C.subgroupOf U).Normal := hnormalC
  letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
  letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
    quotientMulDistribMulAction (A := W1) (G := U)
      (C.subgroupOf U) hCinv
  ∃ F : Type u, ∃ fieldInst : Field F, ∃ fintypeInst : Fintype F,
    letI : Field F := fieldInst
    letI : Fintype F := fintypeInst
    ∃ Ustar : Subgroup Fˣ,
      AddSubgroup.closure
        (((fun x : Ustar => ((x : Fˣ) : F)) '' Set.univ) : Set F) = ⊤ ∧
        ∃ φH : (MF ⧸ H0.subgroupOf MF) ≃* Multiplicative F,
          ∃ φU : (U ⧸ C.subgroupOf U) ≃* Ustar,
            ∃ φWadd : W1 → F ≃+ F,
              (∀ x : U ⧸ C.subgroupOf U, ∀ h : MF,
                ∃ hconjMF : ∀ y : MF,
                  (x.out : U)⁻¹ * (y : G) * (x.out : U) ∈ MF,
                  φH (QuotientGroup.mk' (H0.subgroupOf MF)
                    ⟨(x.out : U)⁻¹ * (h : G) * (x.out : U), hconjMF h⟩) =
                    Multiplicative.ofAdd (((φU x : Ustar) : Fˣ) *
                      Multiplicative.toAdd
                        (φH (QuotientGroup.mk' (H0.subgroupOf MF) h)))) ∧
                ∀ w : W1, ∀ h : MF,
                  ∃ hconjMF : ∀ y : MF,
                    (w : G)⁻¹ * (y : G) * (w : G) ∈ MF,
                    φH (QuotientGroup.mk' (H0.subgroupOf MF)
                      ⟨(w : G)⁻¹ * (h : G) * (w : G), hconjMF h⟩) =
                      Multiplicative.ofAdd
                        ((φWadd w) (Multiplicative.toAdd
                          (φH (QuotientGroup.mk' (H0.subgroupOf MF) h)))) ∧
                  (∀ z : F, ∀ u : Ustar,
                    (φWadd w) (z * (((u : Ustar) : Fˣ) : F)) =
                      (φWadd w) z * (φWadd w) ((((u : Ustar) : Fˣ) : F))) ∧
                  ∀ x : U ⧸ C.subgroupOf U,
                    (φWadd w) ((((φU x : Ustar) : Fˣ) : F)) =
                      (((φU ((w⁻¹ : W1) • x) : Ustar) : Fˣ) : F)

private def theorem_9_7_schurFieldHomCompatibilityPointwiseRawData_sec9
    {G : Type u} [Group G] [Finite G]
    (MF H0 U C W1 : Subgroup G)
    (hnormalH0 : (H0.subgroupOf MF).Normal)
    (hnormalC : (C.subgroupOf U).Normal)
    (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G))
    (hCinv :
      letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
      IsInvariant W1 U (C.subgroupOf U)) : Prop :=
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  letI : (C.subgroupOf U).Normal := hnormalC
  letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
  letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
    quotientMulDistribMulAction (A := W1) (G := U)
      (C.subgroupOf U) hCinv
  ∃ F : Type u, ∃ fieldInst : Field F, ∃ fintypeInst : Fintype F,
    letI : Field F := fieldInst
    letI : Fintype F := fintypeInst
    ∃ Ustar : Subgroup Fˣ,
      AddSubgroup.closure
        (((fun x : Ustar => ((x : Fˣ) : F)) '' Set.univ) : Set F) = ⊤ ∧
        ∃ φH : (MF ⧸ H0.subgroupOf MF) ≃* Multiplicative F,
          ∃ φU : (U ⧸ C.subgroupOf U) ≃* Ustar,
            ∃ φW : W1 → RingAut F,
              (∀ x : U ⧸ C.subgroupOf U, ∀ h : MF,
                ∃ hconjMF : ∀ y : MF,
                  (x.out : U)⁻¹ * (y : G) * (x.out : U) ∈ MF,
                  φH (QuotientGroup.mk' (H0.subgroupOf MF)
                    ⟨(x.out : U)⁻¹ * (h : G) * (x.out : U), hconjMF h⟩) =
                    Multiplicative.ofAdd (((φU x : Ustar) : Fˣ) *
                      Multiplicative.toAdd
                        (φH (QuotientGroup.mk' (H0.subgroupOf MF) h)))) ∧
                ∀ w : W1, ∀ h : MF,
                  ∃ hconjMF : ∀ y : MF,
                    (w : G)⁻¹ * (y : G) * (w : G) ∈ MF,
                    φH (QuotientGroup.mk' (H0.subgroupOf MF)
                      ⟨(w : G)⁻¹ * (h : G) * (w : G), hconjMF h⟩) =
                      Multiplicative.ofAdd
                        ((φW w) (Multiplicative.toAdd
                          (φH (QuotientGroup.mk' (H0.subgroupOf MF) h)))) ∧
                  ∀ x : U ⧸ C.subgroupOf U,
                    Units.map (φW w).toMonoidHom (φU x : Ustar) =
                      (φU ((w⁻¹ : W1) • x) : Ustar)

private theorem
    theorem_9_7_schur_field_model_coordinate_additive_action_no_vector_raw_from_endField_unit_full_tail_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
          quotientChiefFactorData_9_6 M MF H0 W1 hp) →
          quotientCentralizerIn MF H0 U C →
            quotientBarUCardinality U C u →
              (hpprime : Nat.Prime p) →
                (hqprime : Nat.Prime q) →
                    (hnormalH0 : (H0.subgroupOf MF).Normal) →
                      (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G)) →
                        (hH0invU :
                          letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                          IsInvariant U MF (H0.subgroupOf MF)) →
                      (hbarElem :
                        letI : (H0.subgroupOf MF).Normal := hnormalH0
                        IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF)) →
                        (hbarCard :
                          letI : (H0.subgroupOf MF).Normal := hnormalH0
                          Nat.card (MF ⧸ H0.subgroupOf MF) = p ^ q) →
                          (hbarFinrank :
                            letI : Fact p.Prime := ⟨hpprime⟩
                            letI : (H0.subgroupOf MF).Normal := hnormalH0
                            letI : IsElementaryAbelian p
                                (MF ⧸ H0.subgroupOf MF) := hbarElem
                            Module.finrank (ZMod p)
                              (Additive (MF ⧸ H0.subgroupOf MF)) = q) →
                          (hirredRep :
                            letI : Fact p.Prime := ⟨hpprime⟩
                            letI : (H0.subgroupOf MF).Normal := hnormalH0
                            letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                            letI : IsElementaryAbelian p
                                (MF ⧸ H0.subgroupOf MF) := hbarElem
                            letI : MulDistribMulAction U
                                (MF ⧸ H0.subgroupOf MF) :=
                              quotientMulDistribMulAction (A := U) (G := MF)
                                (H0.subgroupOf MF) hH0invU
                            Representation.IsIrreducible
                              (Theory.Representation.ofElementaryAbelianAction (A := U)
                                (G := MF ⧸ H0.subgroupOf MF) (p := p))) →
                          (hnormalC : (C.subgroupOf U).Normal) →
                            (letI : (C.subgroupOf U).Normal := hnormalC
                            IsMulCommutative (U ⧸ C.subgroupOf U)) →
                            (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G)) →
                            (hCinv :
                              letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
                              IsInvariant W1 U (C.subgroupOf U)) →
                            (hW1normMF : W1 ≤ Subgroup.normalizer (MF : Set G)) →
                            (hH0invW1 :
                              letI : Subgroup.Normalizes W1 MF := ⟨hW1normMF⟩
                              IsInvariant W1 MF (H0.subgroupOf MF)) →
                            theorem_9_7_schurFieldCoordinateAdditiveActionUData_sec9
                              MF H0 U C W1 hnormalH0 hnormalC hW1normMF
                              hH0invW1 →
                                theorem_9_7_schurFieldCoordinateAdditiveActionNoVectorRawData_sec9
                                  MF H0 U C W1 hnormalH0 hnormalC hW1normU hCinv := by
  intro h92 hp96 hC hBarU hpprime hqprime hnormalH0 hUnormMF hH0invU
    hbarElem hbarCard hbarFinrank hirredRep hnormalC hbarUcomm hW1normU hCinv
    hW1normMF hH0invW1 hUData
  classical
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  letI : (C.subgroupOf U).Normal := hnormalC
  letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
  letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
    quotientMulDistribMulAction (A := W1) (G := U)
      (C.subgroupOf U) hCinv
  letI : Subgroup.Normalizes W1 MF := ⟨hW1normMF⟩
  letI : MulDistribMulAction W1 (MF ⧸ H0.subgroupOf MF) :=
    quotientMulDistribMulAction (A := W1) (G := MF)
      (H0.subgroupOf MF) hH0invW1
  rcases hUData with
    ⟨F, fieldInst, fintypeInst, Ustar, φHadd, φU, hUactionRep, hfixedOne⟩
  letI : Field F := fieldInst
  letI : Fintype F := fintypeInst
  let φWadd : W1 → F ≃+ F :=
    theorem_9_7_schurQuotientWAddEquiv_sec9
      MF H0 W1 hnormalH0 hW1normMF hH0invW1 F φHadd
  rcases
      theorem_9_7_schur_field_model_coordinate_additive_action_tail_span_compat_source_bridge_sec9
        M MF U W1 W2 H0 C p q u h92 hp96 hC hBarU hpprime hqprime
        hnormalH0 hUnormMF hH0invU hbarElem hbarCard hbarFinrank hirredRep
        hnormalC hbarUcomm hW1normU hCinv hW1normMF hH0invW1
        F fieldInst fintypeInst Ustar φHadd φU hUactionRep hfixedOne with
    ⟨hspan, hcompat⟩
  have hUaction :
      ∀ x : U ⧸ C.subgroupOf U, ∀ h : MF,
        ∃ hconjMF : ∀ y : MF,
          (x.out : U)⁻¹ * (y : G) * (x.out : U) ∈ MF,
          φHadd (Additive.ofMul
            (QuotientGroup.mk' (H0.subgroupOf MF)
              ⟨(x.out : U)⁻¹ * (h : G) * (x.out : U), hconjMF h⟩)) =
            (((φU x : Ustar) : Fˣ) : F) *
              φHadd (Additive.ofMul
                (QuotientGroup.mk' (H0.subgroupOf MF) h)) := by
    intro x h
    rcases hUactionRep x.out h with ⟨hconjMF, hφ⟩
    refine ⟨hconjMF, ?_⟩
    have hxout : QuotientGroup.mk' (C.subgroupOf U) x.out = x := by
      simpa only [QuotientGroup.mk'_apply] using (Quotient.out_eq x)
    simpa [hxout] using hφ
  have hWactionBase :=
    theorem_9_7_schurQuotientWAddEquiv_action_sec9
      MF H0 W1 hnormalH0 hW1normMF hH0invW1 F φHadd
  have hWaction :
      ∀ w : W1, ∀ h : MF,
        ∃ hconjMF : ∀ y : MF,
          (w : G)⁻¹ * (y : G) * (w : G) ∈ MF,
          φHadd (Additive.ofMul
            (QuotientGroup.mk' (H0.subgroupOf MF)
              ⟨(w : G)⁻¹ * (h : G) * (w : G), hconjMF h⟩)) =
            (φWadd w) (φHadd (Additive.ofMul
              (QuotientGroup.mk' (H0.subgroupOf MF) h))) ∧
            ∀ x : U ⧸ C.subgroupOf U,
              (φWadd w) ((((φU x : Ustar) : Fˣ) : F)) =
                (((φU ((w⁻¹ : W1) • x) : Ustar) : Fˣ) : F) := by
    intro w h
    rcases hWactionBase w h with ⟨hconjMF, hφ⟩
    refine ⟨hconjMF, ?_, ?_⟩
    · simpa [φWadd] using hφ
    · intro x
      simpa [φWadd] using hcompat w x
  exact ⟨F, fieldInst, fintypeInst, Ustar, hspan, φHadd, φU, φWadd,
    hUaction, hWaction⟩

private noncomputable def theorem_9_7_ringAut_of_addEquiv_on_unit_span_sec9
    (F : Type u) [Field F] (Ustar : Subgroup Fˣ)
    (hspan : AddSubgroup.closure
      (((fun x : Ustar => ((x : Fˣ) : F)) '' Set.univ) : Set F) = ⊤)
    (ψ : F ≃+ F)
    (hright : ∀ z : F, ∀ u : Ustar,
      ψ (z * (((u : Ustar) : Fˣ) : F)) =
        ψ z * ψ ((((u : Ustar) : Fˣ) : F))) : RingAut F := by
  classical
  let S : Set F := (((fun x : Ustar => ((x : Fˣ) : F)) '' Set.univ) : Set F)
  have hmul : ∀ z y : F, ψ (z * y) = ψ z * ψ y := by
    intro z y
    have hy : y ∈ AddSubgroup.closure S := by
      rw [hspan]
      exact trivial
    exact AddSubgroup.closure_induction (k := S)
      (p := fun y _hy => ψ (z * y) = ψ z * ψ y)
      (fun y hyS => by
        rcases hyS with ⟨u, _hu, rfl⟩
        exact hright z u)
      (by simp)
      (fun x y _hx _hy hx hy => by
        calc
          ψ (z * (x + y)) = ψ (z * x + z * y) := by rw [mul_add]
          _ = ψ (z * x) + ψ (z * y) := map_add ψ (z * x) (z * y)
          _ = ψ z * ψ x + ψ z * ψ y := by rw [hx, hy]
          _ = ψ z * (ψ x + ψ y) := by rw [mul_add]
          _ = ψ z * ψ (x + y) := by rw [map_add])
      (fun x _hx hx => by
        calc
          ψ (z * -x) = ψ (-(z * x)) := by rw [mul_neg]
          _ = -ψ (z * x) := map_neg ψ (z * x)
          _ = -(ψ z * ψ x) := by rw [hx]
          _ = ψ z * -ψ x := by rw [mul_neg]
          _ = ψ z * ψ (-x) := by rw [map_neg])
      hy
  exact
    { toFun := ψ
      invFun := ψ.symm
      left_inv := ψ.left_inv
      right_inv := ψ.right_inv
      map_mul' := hmul
      map_add' := map_add ψ }

private def theorem_9_7_schur_phiW_hom_of_pointwise_action_sec9
    {G : Type u} [Group G] [Finite G]
    (MF H0 W1 : Subgroup G)
    (hnormalH0 : (H0.subgroupOf MF).Normal)
    (hW1cyc : IsCyclic W1)
    (F : Type u) [Field F]
    (φH :
      letI : (H0.subgroupOf MF).Normal := hnormalH0
      (MF ⧸ H0.subgroupOf MF) ≃* Multiplicative F)
    (φWfun : W1 → RingAut F)
    (hWaction :
      letI : (H0.subgroupOf MF).Normal := hnormalH0
      ∀ w : W1, ∀ h : MF,
        ∃ hconjMF : ∀ y : MF,
          (w : G)⁻¹ * (y : G) * (w : G) ∈ MF,
          φH (QuotientGroup.mk' (H0.subgroupOf MF)
            ⟨(w : G)⁻¹ * (h : G) * (w : G), hconjMF h⟩) =
            Multiplicative.ofAdd
              ((φWfun w) (Multiplicative.toAdd
                (φH (QuotientGroup.mk' (H0.subgroupOf MF) h))))) :
    W1 →* RingAut F := by
  classical
  let H0MF : Subgroup MF := H0.subgroupOf MF
  letI : H0MF.Normal := hnormalH0
  haveI : IsCyclic W1 := hW1cyc
  refine
    { toFun := φWfun
      map_one' := ?_
      map_mul' := ?_ }
  · apply RingEquiv.ext
    intro z
    rcases φH.surjective (Multiplicative.ofAdd z) with ⟨y, hy⟩
    revert hy
    refine QuotientGroup.induction_on y ?_
    intro h hy
    rcases hWaction 1 h with ⟨hconjMF, hφH⟩
    change φH (QuotientGroup.mk' H0MF h) = Multiplicative.ofAdd z at hy
    have hleft :
        QuotientGroup.mk' H0MF
            ⟨((1 : W1) : G)⁻¹ * (h : G) * ((1 : W1) : G), hconjMF h⟩ =
          QuotientGroup.mk' H0MF h := by
      apply congrArg (QuotientGroup.mk' H0MF)
      apply Subtype.ext
      simp
    rw [hleft] at hφH
    change φH (QuotientGroup.mk' H0MF h) =
      Multiplicative.ofAdd ((φWfun 1)
        (Multiplicative.toAdd (φH (QuotientGroup.mk' H0MF h)))) at hφH
    rw [hy] at hφH
    have htoAdd := congrArg Multiplicative.toAdd hφH
    simpa using htoAdd.symm
  · intro w1 w2
    apply RingEquiv.ext
    intro z
    rcases φH.surjective (Multiplicative.ofAdd z) with ⟨y, hy⟩
    revert hy
    refine QuotientGroup.induction_on y ?_
    intro h hy
    rcases hWaction w2 h with ⟨hconjMF2, hφH2⟩
    change φH (QuotientGroup.mk' H0MF h) = Multiplicative.ofAdd z at hy
    let h2 : MF := ⟨(w2 : G)⁻¹ * (h : G) * (w2 : G), hconjMF2 h⟩
    rcases hWaction w1 h2 with ⟨hconjMF1, hφH1⟩
    rcases hWaction (w2 * w1) h with ⟨hconjMF21, hφH21⟩
    have hleft :
        QuotientGroup.mk' H0MF
            ⟨((w2 * w1 : W1) : G)⁻¹ * (h : G) * ((w2 * w1 : W1) : G),
              hconjMF21 h⟩ =
          QuotientGroup.mk' H0MF
            ⟨(w1 : G)⁻¹ * (h2 : G) * (w1 : G), hconjMF1 h2⟩ := by
      apply congrArg (QuotientGroup.mk' H0MF)
      apply Subtype.ext
      simp [h2, mul_assoc]
    have hφH2z :
        φH (QuotientGroup.mk' H0MF h2) =
          Multiplicative.ofAdd ((φWfun w2) z) := by
      change φH (QuotientGroup.mk' H0MF h2) =
        Multiplicative.ofAdd ((φWfun w2)
          (Multiplicative.toAdd (φH (QuotientGroup.mk' H0MF h)))) at hφH2
      rw [hy] at hφH2
      simpa [h2] using hφH2
    have hφH1z :
        φH (QuotientGroup.mk' H0MF
            ⟨(w1 : G)⁻¹ * (h2 : G) * (w1 : G), hconjMF1 h2⟩) =
          Multiplicative.ofAdd ((φWfun w1) ((φWfun w2) z)) := by
      change φH (QuotientGroup.mk' H0MF
          ⟨(w1 : G)⁻¹ * (h2 : G) * (w1 : G), hconjMF1 h2⟩) =
        Multiplicative.ofAdd ((φWfun w1)
          (Multiplicative.toAdd (φH (QuotientGroup.mk' H0MF h2)))) at hφH1
      rw [hφH2z] at hφH1
      simpa [h2] using hφH1
    rw [hleft] at hφH21
    change φH (QuotientGroup.mk' H0MF
        ⟨(w1 : G)⁻¹ * (h2 : G) * (w1 : G), hconjMF1 h2⟩) =
      Multiplicative.ofAdd ((φWfun (w2 * w1))
        (Multiplicative.toAdd (φH (QuotientGroup.mk' H0MF h)))) at hφH21
    rw [hy] at hφH21
    have hpoint :
        Multiplicative.ofAdd ((φWfun (w2 * w1)) z) =
          Multiplicative.ofAdd ((φWfun w1) ((φWfun w2) z)) := by
      exact hφH21.symm.trans hφH1z
    have htoAdd := congrArg Multiplicative.toAdd hpoint
    have hcomm : w2 * w1 = w1 * w2 := by
      rcases IsCyclic.exists_generator (α := W1) with ⟨g, hg⟩
      rcases Subgroup.mem_zpowers_iff.mp (hg w1) with ⟨m, hm⟩
      rcases Subgroup.mem_zpowers_iff.mp (hg w2) with ⟨n, hn⟩
      rw [← hm, ← hn]
      exact zpow_mul_comm g n m
    rw [← hcomm]
    simpa using htoAdd

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
private theorem
    theorem_9_7_schur_field_model_coordinate_additive_action_no_vector_raw_from_endField_unit_full_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
          quotientChiefFactorData_9_6 M MF H0 W1 hp) →
          quotientCentralizerIn MF H0 U C →
            quotientBarUCardinality U C u →
              (hpprime : Nat.Prime p) →
                (hqprime : Nat.Prime q) →
                    (hnormalH0 : (H0.subgroupOf MF).Normal) →
                      (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G)) →
                        (hH0invU :
                          letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                          IsInvariant U MF (H0.subgroupOf MF)) →
                      (hbarElem :
                        letI : (H0.subgroupOf MF).Normal := hnormalH0
                        IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF)) →
                        (hbarCard :
                          letI : (H0.subgroupOf MF).Normal := hnormalH0
                          Nat.card (MF ⧸ H0.subgroupOf MF) = p ^ q) →
                          (hbarFinrank :
                            letI : Fact p.Prime := ⟨hpprime⟩
                            letI : (H0.subgroupOf MF).Normal := hnormalH0
                            letI : IsElementaryAbelian p
                                (MF ⧸ H0.subgroupOf MF) := hbarElem
                            Module.finrank (ZMod p)
                              (Additive (MF ⧸ H0.subgroupOf MF)) = q) →
                          (hirredRep :
                            letI : Fact p.Prime := ⟨hpprime⟩
                            letI : (H0.subgroupOf MF).Normal := hnormalH0
                            letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                            letI : IsElementaryAbelian p
                                (MF ⧸ H0.subgroupOf MF) := hbarElem
                            letI : MulDistribMulAction U
                                (MF ⧸ H0.subgroupOf MF) :=
                              quotientMulDistribMulAction (A := U) (G := MF)
                                (H0.subgroupOf MF) hH0invU
                            Representation.IsIrreducible
                              (Theory.Representation.ofElementaryAbelianAction (A := U)
                                (G := MF ⧸ H0.subgroupOf MF) (p := p))) →
    theorem_9_7_schurEndFieldData_sec9 MF H0 U p
      hpprime hnormalH0 hUnormMF hH0invU hbarElem →
    theorem_9_7_schurEndFieldFullData_sec9 MF H0 U p q
      hpprime hnormalH0 hUnormMF hH0invU hbarElem →
                          (hnormalC : (C.subgroupOf U).Normal) →
                            (letI : (C.subgroupOf U).Normal := hnormalC
                            letI : Fact p.Prime := ⟨hpprime⟩
                            letI : (H0.subgroupOf MF).Normal := hnormalH0
                            letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                            letI : IsElementaryAbelian p
                                (MF ⧸ H0.subgroupOf MF) := hbarElem
                            letI : MulDistribMulAction U
                                (MF ⧸ H0.subgroupOf MF) :=
                              quotientMulDistribMulAction (A := U) (G := MF)
                                (H0.subgroupOf MF) hH0invU
                            let ρ := Theory.Representation.ofElementaryAbelianAction (A := U)
                              (G := MF ⧸ H0.subgroupOf MF) (p := p)
                            let E := Module.End (MonoidAlgebra (ZMod p) U) ρ.asModule
                            let A := Module.End E ρ.asModule
                            ∃ Ustar : Subgroup Aˣ,
                              ∃ φU : (U ⧸ C.subgroupOf U) ≃* Ustar,
                                ∀ x : U,
                                  ((φU (QuotientGroup.mk' (C.subgroupOf U) x) :
                                      Ustar) : Aˣ) =
                                    (endFieldRep ρ).toHomUnits x) →
                            (letI : (C.subgroupOf U).Normal := hnormalC
                            IsMulCommutative (U ⧸ C.subgroupOf U)) →
                            (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G)) →
                            (hCinv :
                              letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
                              IsInvariant W1 U (C.subgroupOf U)) →
                                theorem_9_7_schurFieldCoordinateAdditiveActionNoVectorRawData_sec9
                                  MF H0 U C W1 hnormalH0 hnormalC hW1normU hCinv := by
  intro h92 hp96 hC hBarU hpprime hqprime hnormalH0 hUnormMF hH0invU
    hbarElem hbarCard hbarFinrank hirredRep _hEndField _hEndFieldFull hnormalC
    hEndFieldUnitQuotient hbarUcomm hW1normU hCinv
  classical
  letI : Fact p.Prime := ⟨hpprime⟩
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
  letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
  letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
    quotientMulDistribMulAction (A := U) (G := MF)
      (H0.subgroupOf MF) hH0invU
  let ρ := Theory.Representation.ofElementaryAbelianAction (A := U)
    (G := MF ⧸ H0.subgroupOf MF) (p := p)
  let E := Module.End (MonoidAlgebra (ZMod p) U) ρ.asModule
  have hρirr : Representation.IsIrreducible ρ := by
    simpa [ρ] using hirredRep
  letI : Representation.IsIrreducible ρ := hρirr
  haveI : FiniteDimensional (ZMod p) (Additive (MF ⧸ H0.subgroupOf MF)) :=
    finiteDimensional_of_irreducible_finite_group ρ hρirr
  letI : Field E := endField_field ρ
  letI : Fintype E := Fintype.ofFinite E
  letI : Module E ρ.asModule := endFieldModule ρ
  have hCkerEnd :
      C.subgroupOf U = (endFieldRep ρ).ker := by
    simpa [ρ] using
      theorem_9_7_quotientCentralizerIn_subgroupOf_eq_endFieldRep_ker_sec9
        (MF := MF) (H0 := H0) (U := U) (C := C) (p := p)
        hnormalH0 hUnormMF hH0invU hbarElem hC
  haveI : (endFieldRep ρ).ker.Normal := MonoidHom.normal_ker (endFieldRep ρ)
  have hEndQuotComm :
      IsMulCommutative (U ⧸ (endFieldRep ρ).ker) :=
    theorem_9_7_quotient_commutative_of_eq_kernel_sec9
      (G := U) (C := C.subgroupOf U) (K := (endFieldRep ρ).ker)
      hbarUcomm hCkerEnd
  have hfinOne : Module.finrank E ρ.asModule = 1 := by
    simpa [ρ, E] using
      theorem_9_7_endFieldRep_finrank_eq_one_of_quotient_kernel_commutative_sec9
        ρ hEndQuotComm
  have hρasFinite : Finite ρ.asModule :=
    Finite.of_equiv (Additive (MF ⧸ H0.subgroupOf MF))
      ρ.asModuleEquiv.symm.toEquiv
  letI : Module.Finite E ρ.asModule := Module.Finite.of_finite
  haveI : Module.Free E ρ.asModule := inferInstance
  have hW1normMF : W1 ≤ Subgroup.normalizer (MF : Set G) :=
    theorem_9_7_W1_le_normalizer_MF_of_hypothesis_9_2_sec9 h92
  letI : Subgroup.Normalizes W1 MF := ⟨hW1normMF⟩
  have hW1leM : W1 ≤ M := by
    rcases h92.typePDefinitionData with
      ⟨_hMFsource, _hW1cyc, _hW1ne, hW1hall, _hcompMW1, _hUleD,
        _hUnil, _hW1normU, _hcompDU, _hMFnotcyc, _hsecond, _hfitEq,
        _hfitLeD, _hW2le, _hW2cyc, _hW2ne, _hcentW1, _hnormX⟩
    exact hW1hall.1
  have hMFleM : MF ≤ M := by
    rcases hp96 with ⟨_hp, _hp_eq, hpData, _h96⟩
    exact hpData.2.1
  have hH0normalM : (H0.subgroupOf M).Normal := by
    rcases hp96 with ⟨_hp, _hp_eq, hpData, _h96⟩
    exact hpData.2.2.1
  have hH0invW1 : IsInvariant W1 MF (H0.subgroupOf MF) :=
    subgroupOf_MF_isInvariant_of_subgroupOf_M_normal_sec9 M MF W1 H0
      hMFleM hW1leM hH0normalM hW1normMF
  letI : MulDistribMulAction W1 (MF ⧸ H0.subgroupOf MF) :=
    quotientMulDistribMulAction (A := W1) (G := MF)
      (H0.subgroupOf MF) hH0invW1
  have hfixedCard :
      Nat.card (fixedPointSubgroup W1 (MF ⧸ H0.subgroupOf MF)) = p := by
    rcases hp96 with ⟨hp, hp_eq, _hpData, h96⟩
    rcases h96 with ⟨_hH0MF, _hMFM, _hnormal96, _hchief, hsourceFixed, _hcard⟩
    rcases hsourceFixed with ⟨_hnormalSrc, hsourceCard⟩
    have hsourceCard' :
        Nat.card {x : MF ⧸ H0.subgroupOf MF //
          ∀ h : MF, QuotientGroup.mk' (H0.subgroupOf MF) h = x →
            ∀ w : G, w ∈ W1 → ⁅w, (h : G)⁆ ∈ H0} = p := by
      simpa [hp_eq] using hsourceCard
    have hsource_eq_fixed :
        Nat.card {x : MF ⧸ H0.subgroupOf MF //
          ∀ h : MF, QuotientGroup.mk' (H0.subgroupOf MF) h = x →
            ∀ w : G, w ∈ W1 → ⁅w, (h : G)⁆ ∈ H0} =
          Nat.card (fixedPointSubgroup W1 (MF ⧸ H0.subgroupOf MF)) := by
      simpa using
        theorem_9_7_W1_fixedPointSubgroup_card_eq_source_subtype_sec9
          MF W1 H0 hH0invW1 hnormalH0
    exact hsource_eq_fixed.symm.trans hsourceCard'
  have hfixedNontriv :
      Nontrivial (fixedPointSubgroup W1 (MF ⧸ H0.subgroupOf MF)) := by
    exact Finite.one_lt_card_iff_nontrivial.mp (by
      rw [hfixedCard]
      exact hpprime.one_lt)
  rcases exists_ne (1 : fixedPointSubgroup W1 (MF ⧸ H0.subgroupOf MF)) with
    ⟨sFixed, hsFixed_ne⟩
  let sQ : MF ⧸ H0.subgroupOf MF := sFixed
  have hsQne : sQ ≠ 1 := by
    intro hs
    apply hsFixed_ne
    ext
    exact hs
  have hsQfixed : sQ ∈ fixedPointSubgroup W1 (MF ⧸ H0.subgroupOf MF) :=
    sFixed.property
  let v : ρ.asModule := ρ.asModuleEquiv.symm (Additive.ofMul sQ)
  have hv : v ≠ 0 := by
    intro hv0
    apply hsQne
    have hAdd : Additive.ofMul sQ = 0 := by
      have h := congrArg ρ.asModuleEquiv hv0
      simpa [v] using h
    simpa using congrArg Additive.toMul hAdd
  rcases
      theorem_9_7_exists_oneDimLinearEquiv_apply_eq_one_sec9
        (E := E) (W := ρ.asModule) hfinOne v hv with
    ⟨e, he_v⟩
  let φHadd : Additive (MF ⧸ H0.subgroupOf MF) ≃+ E :=
    ρ.asModuleEquiv.symm.toAddEquiv.trans e.toAddEquiv
  have hφs : φHadd (Additive.ofMul sQ) = 1 := by
    change e (ρ.asModuleEquiv.symm (Additive.ofMul sQ)) = 1
    simpa [v] using he_v
  have hfixedOne :
      ∀ w : W1,
        (theorem_9_7_schurQuotientWAddEquiv_sec9
          MF H0 W1 hnormalH0 hW1normMF hH0invW1 E φHadd w) 1 = 1 := by
    intro w
    let η : W1 → E ≃+ E :=
      theorem_9_7_schurQuotientWAddEquiv_sec9
        MF H0 W1 hnormalH0 hW1normMF hH0invW1 E φHadd
    have hηs :
        η w (φHadd (Additive.ofMul sQ)) =
          φHadd (Additive.ofMul ((w⁻¹ : W1) • sQ)) := by
      change
        (theorem_9_7_schurQuotientWAddEquiv_sec9
          MF H0 W1 hnormalH0 hW1normMF hH0invW1 E φHadd w)
          (φHadd (Additive.ofMul sQ)) =
          φHadd (Additive.ofMul ((w⁻¹ : W1) • sQ))
      simp [theorem_9_7_schurQuotientWAddEquiv_sec9,
        MulDistribMulAction.toMulAut_apply]
    have hfix_s : (w⁻¹ : W1) • sQ = sQ := by
      change ∀ w : W1, w • sQ = sQ at hsQfixed
      exact hsQfixed (w⁻¹)
    change η w 1 = 1
    calc
      η w 1 = η w (φHadd (Additive.ofMul sQ)) := by rw [hφs]
      _ =
          φHadd (Additive.ofMul ((w⁻¹ : W1) • sQ)) := hηs
      _ = φHadd (Additive.ofMul sQ) := by rw [hfix_s]
      _ = 1 := hφs
  let A := Module.End E ρ.asModule
  change
    ∃ Ustar : Subgroup Aˣ,
      ∃ φU : (U ⧸ C.subgroupOf U) ≃* Ustar,
        ∀ x : U,
          ((φU (QuotientGroup.mk' (C.subgroupOf U) x) : Ustar) : Aˣ) =
            (endFieldRep ρ).toHomUnits x at hEndFieldUnitQuotient
  rcases hEndFieldUnitQuotient with ⟨UstarA, φUA, hφUA⟩
  let scalarEquiv : Aˣ ≃* Eˣ :=
    theorem_9_7_endUnitScalarEquivOfLinearEquiv_sec9 e
  letI : (C.subgroupOf U).Normal := hnormalC
  letI : IsMulCommutative (U ⧸ C.subgroupOf U) := hbarUcomm
  let invQ : U ⧸ C.subgroupOf U ≃* U ⧸ C.subgroupOf U :=
    MulEquiv.inv (U ⧸ C.subgroupOf U)
  let ψU : U ⧸ C.subgroupOf U →* Eˣ :=
    scalarEquiv.toMonoidHom.comp
      (UstarA.subtype.comp (φUA.toMonoidHom.comp invQ.toMonoidHom))
  have hψUinj : Function.Injective ψU := by
    exact scalarEquiv.injective.comp
      (UstarA.subtype_injective.comp (φUA.injective.comp invQ.injective))
  let Ustar : Subgroup Eˣ := ψU.range
  let φU : U ⧸ C.subgroupOf U ≃* Ustar :=
    MonoidHom.ofInjective hψUinj
  have hUaction :
      ∀ x : U, ∀ h : MF,
        ∃ hconjMF : ∀ y : MF,
          (x : G)⁻¹ * (y : G) * (x : G) ∈ MF,
          φHadd (Additive.ofMul
            (QuotientGroup.mk' (H0.subgroupOf MF)
              ⟨(x : G)⁻¹ * (h : G) * (x : G),
                hconjMF h⟩)) =
            (((φU (QuotientGroup.mk' (C.subgroupOf U) x) : Ustar) : Eˣ) : E) *
              φHadd (Additive.ofMul
                (QuotientGroup.mk' (H0.subgroupOf MF) h)) := by
    intro x h
    let xinv : U := x⁻¹
    have hconjMF : ∀ y : MF, (x : G)⁻¹ * (y : G) * (x : G) ∈ MF := by
      intro y
      have hy : (((xinv : U) • y : MF) : G) ∈ MF :=
        (((xinv : U) • y : MF).property)
      simpa [xinv, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
        mul_assoc] using hy
    refine ⟨hconjMF, ?_⟩
    let qh : MF ⧸ H0.subgroupOf MF :=
      QuotientGroup.mk' (H0.subgroupOf MF) h
    let hConj : MF :=
      ⟨(x : G)⁻¹ * (h : G) * (x : G), hconjMF h⟩
    let qconj : MF ⧸ H0.subgroupOf MF :=
      QuotientGroup.mk' (H0.subgroupOf MF) hConj
    let m : ρ.asModule := ρ.asModuleEquiv.symm (Additive.ofMul qh)
    let T : Aˣ := (endFieldRep ρ).toHomUnits xinv
    have hscalarMk :
        (((φU (QuotientGroup.mk' (C.subgroupOf U) x) : Ustar) : Eˣ) : E) =
          (((theorem_9_7_endUnitScalarEquivOfLinearEquiv_sec9 e) T : Eˣ) : E) := by
      change ((ψU (QuotientGroup.mk' (C.subgroupOf U) x) : Eˣ) : E) =
        (((theorem_9_7_endUnitScalarEquivOfLinearEquiv_sec9 e) T : Eˣ) : E)
      dsimp [ψU, scalarEquiv]
      have hinvQ :
          invQ (x : U ⧸ C.subgroupOf U) =
            (xinv : U ⧸ C.subgroupOf U) := by
        change (QuotientGroup.mk' (C.subgroupOf U) x)⁻¹ =
          QuotientGroup.mk' (C.subgroupOf U) x⁻¹
        rw [map_inv]
      rw [hinvQ]
      exact congrArg
        (fun a : Aˣ =>
          (((theorem_9_7_endUnitScalarEquivOfLinearEquiv_sec9 e) a : Eˣ) : E))
        (hφUA xinv)
    have hρ_apply :
        ρ xinv (Additive.ofMul qh) = Additive.ofMul qconj := by
      have hact : xinv • qh = qconj := by
        have hsmul_mk :
            xinv • QuotientGroup.mk' (H0.subgroupOf MF) h =
              QuotientGroup.mk' (H0.subgroupOf MF) (xinv • h) := by
          simpa only [QuotientGroup.mk'_apply] using
            (MulAction.Quotient.smul_mk (H := H0.subgroupOf MF) xinv h)
        rw [hsmul_mk]
        apply congrArg (QuotientGroup.mk' (H0.subgroupOf MF))
        apply Subtype.ext
        simp [xinv, hConj,
          Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, mul_assoc]
      dsimp [ρ]
      rw [Theory.Representation.ofElementaryAbelianAction_apply_ofMul]
      exact congrArg Additive.ofMul hact
    have hrep :
        ((T : A) m) =
          ρ.asModuleEquiv.symm (Additive.ofMul qconj) := by
      dsimp [T]
      change ((endFieldRep ρ) xinv) m =
        ρ.asModuleEquiv.symm (Additive.ofMul qconj)
      apply ρ.asModuleEquiv.injective
      change
        ρ.asModuleEquiv (((endFieldRep ρ) xinv) m) =
          ρ.asModuleEquiv (ρ.asModuleEquiv.symm (Additive.ofMul qconj))
      rw [endFieldRep_apply']
      have hm : ρ.asModuleEquiv m = Additive.ofMul qh := by
        change
          ρ.asModuleEquiv (ρ.asModuleEquiv.symm (Additive.ofMul qh)) =
            Additive.ofMul qh
        simp
      rw [hm]
      exact hρ_apply
    have hscalar :=
      theorem_9_7_endUnitScalarEquiv_apply_sec9
        (E := E) (W := ρ.asModule) e T m
    change
      e (ρ.asModuleEquiv.symm (Additive.ofMul qconj)) =
        (((φU (QuotientGroup.mk' (C.subgroupOf U) x) : Ustar) : Eˣ) : E) * e m
    calc
      e (ρ.asModuleEquiv.symm (Additive.ofMul qconj)) = e ((T : A) m) := by
        exact (congrArg e hrep).symm
      _ = (((theorem_9_7_endUnitScalarEquivOfLinearEquiv_sec9 e) T : Eˣ) : E) *
            e m := hscalar
      _ = (((φU (QuotientGroup.mk' (C.subgroupOf U) x) : Ustar) : Eˣ) : E) *
            e m := by
        rw [← hscalarMk]
  let fieldE : Field E := inferInstance
  let fintypeE : Fintype E := inferInstance
  have hUData :
      theorem_9_7_schurFieldCoordinateAdditiveActionUData_sec9
        MF H0 U C W1 hnormalH0 hnormalC hW1normMF hH0invW1 := by
    exact ⟨E, fieldE, fintypeE, Ustar, φHadd, φU, hUaction, hfixedOne⟩
  exact
    theorem_9_7_schur_field_model_coordinate_additive_action_no_vector_raw_from_endField_unit_full_tail_source_bridge_sec9
      M MF U W1 W2 H0 C p q u h92 hp96 hC hBarU hpprime hqprime
      hnormalH0 hUnormMF hH0invU hbarElem hbarCard hbarFinrank hirredRep
      hnormalC hbarUcomm hW1normU hCinv hW1normMF hH0invW1 hUData

private theorem
    theorem_9_7_schur_field_model_coordinate_additive_action_no_vector_raw_from_endField_unit_quotient_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
          quotientChiefFactorData_9_6 M MF H0 W1 hp) →
          quotientCentralizerIn MF H0 U C →
            quotientBarUCardinality U C u →
              (hpprime : Nat.Prime p) →
                (hqprime : Nat.Prime q) →
                    (hnormalH0 : (H0.subgroupOf MF).Normal) →
                      (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G)) →
                        (hH0invU :
                          letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                          IsInvariant U MF (H0.subgroupOf MF)) →
                      (hbarElem :
                        letI : (H0.subgroupOf MF).Normal := hnormalH0
                        IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF)) →
                        (hbarCard :
                          letI : (H0.subgroupOf MF).Normal := hnormalH0
                          Nat.card (MF ⧸ H0.subgroupOf MF) = p ^ q) →
                          (hbarFinrank :
                            letI : Fact p.Prime := ⟨hpprime⟩
                            letI : (H0.subgroupOf MF).Normal := hnormalH0
                            letI : IsElementaryAbelian p
                                (MF ⧸ H0.subgroupOf MF) := hbarElem
                            Module.finrank (ZMod p)
                              (Additive (MF ⧸ H0.subgroupOf MF)) = q) →
                          (hirredRep :
                            letI : Fact p.Prime := ⟨hpprime⟩
                            letI : (H0.subgroupOf MF).Normal := hnormalH0
                            letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                            letI : IsElementaryAbelian p
                                (MF ⧸ H0.subgroupOf MF) := hbarElem
                            letI : MulDistribMulAction U
                                (MF ⧸ H0.subgroupOf MF) :=
                              quotientMulDistribMulAction (A := U) (G := MF)
                                (H0.subgroupOf MF) hH0invU
                            Representation.IsIrreducible
                              (Theory.Representation.ofElementaryAbelianAction (A := U)
                                (G := MF ⧸ H0.subgroupOf MF) (p := p))) →
    theorem_9_7_schurEndFieldData_sec9 MF H0 U p
      hpprime hnormalH0 hUnormMF hH0invU hbarElem →
                          (letI : Fact p.Prime := ⟨hpprime⟩
                          letI : (H0.subgroupOf MF).Normal := hnormalH0
                          letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                          letI : IsElementaryAbelian p
                              (MF ⧸ H0.subgroupOf MF) := hbarElem
                          letI : MulDistribMulAction U
                              (MF ⧸ H0.subgroupOf MF) :=
                            quotientMulDistribMulAction (A := U) (G := MF)
                              (H0.subgroupOf MF) hH0invU
                          let ρ := Theory.Representation.ofElementaryAbelianAction (A := U)
                            (G := MF ⧸ H0.subgroupOf MF) (p := p)
                          let E := Module.End (MonoidAlgebra (ZMod p) U) ρ.asModule
                          (Nat.card E = p ∧ Module.finrank E ρ.asModule = q) ∨
                            (Nat.card E = p ^ q ∧
                              Module.finrank E ρ.asModule = 1)) →
                          (hnormalC : (C.subgroupOf U).Normal) →
                            (letI : (C.subgroupOf U).Normal := hnormalC
                            letI : Fact p.Prime := ⟨hpprime⟩
                            letI : (H0.subgroupOf MF).Normal := hnormalH0
                            letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                            letI : IsElementaryAbelian p
                                (MF ⧸ H0.subgroupOf MF) := hbarElem
                            letI : MulDistribMulAction U
                                (MF ⧸ H0.subgroupOf MF) :=
                              quotientMulDistribMulAction (A := U) (G := MF)
                                (H0.subgroupOf MF) hH0invU
                            let ρ := Theory.Representation.ofElementaryAbelianAction (A := U)
                              (G := MF ⧸ H0.subgroupOf MF) (p := p)
                            let E := Module.End (MonoidAlgebra (ZMod p) U) ρ.asModule
                            let A := Module.End E ρ.asModule
                            ∃ Ustar : Subgroup Aˣ,
                              ∃ φU : (U ⧸ C.subgroupOf U) ≃* Ustar,
                                ∀ x : U,
                                  ((φU (QuotientGroup.mk' (C.subgroupOf U) x) :
                                      Ustar) : Aˣ) =
                                    (endFieldRep ρ).toHomUnits x) →
                            (letI : (C.subgroupOf U).Normal := hnormalC
                            IsMulCommutative (U ⧸ C.subgroupOf U)) →
                            (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G)) →
                            (hCinv :
                              letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
                              IsInvariant W1 U (C.subgroupOf U)) →
                                theorem_9_7_schurFieldCoordinateAdditiveActionNoVectorRawData_sec9
                                  MF H0 U C W1 hnormalH0 hnormalC hW1normU hCinv := by
  intro h92 hp96 hC hBarU hpprime hqprime hnormalH0 hUnormMF hH0invU
    hbarElem hbarCard hbarFinrank hirredRep hEndField hEndFieldCardAlt hnormalC
    hEndFieldUnitQuotient hbarUcomm hW1normU hCinv
  have hFullData :
      theorem_9_7_schurEndFieldFullData_sec9 MF H0 U p q
        hpprime hnormalH0 hUnormMF hH0invU hbarElem :=
    theorem_9_7_schurEndFieldFullData_of_commutative_barU_sec9
      (MF := MF) (H0 := H0) (U := U) (C := C) (p := p) (q := q)
      hpprime hqprime hnormalH0 hUnormMF hH0invU hbarElem hirredRep
      hEndFieldCardAlt hC hnormalC hbarUcomm
  exact
    theorem_9_7_schur_field_model_coordinate_additive_action_no_vector_raw_from_endField_unit_full_source_bridge_sec9
      M MF U W1 W2 H0 C p q u h92 hp96 hC hBarU hpprime hqprime
      hnormalH0 hUnormMF hH0invU hbarElem hbarCard hbarFinrank hirredRep
      hEndField hFullData hnormalC hEndFieldUnitQuotient hbarUcomm hW1normU
      hCinv

private theorem
    theorem_9_7_schur_field_model_coordinate_additive_action_no_vector_raw_from_elementary_irreducible_hom_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
          quotientChiefFactorData_9_6 M MF H0 W1 hp) →
          quotientCentralizerIn MF H0 U C →
            quotientBarUCardinality U C u →
              (hpprime : Nat.Prime p) →
                (hqprime : Nat.Prime q) →
                    (hnormalH0 : (H0.subgroupOf MF).Normal) →
                      (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G)) →
                        (hH0invU :
                          letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                          IsInvariant U MF (H0.subgroupOf MF)) →
                      (hbarElem :
                        letI : (H0.subgroupOf MF).Normal := hnormalH0
                        IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF)) →
                        (hbarCard :
                          letI : (H0.subgroupOf MF).Normal := hnormalH0
                          Nat.card (MF ⧸ H0.subgroupOf MF) = p ^ q) →
                          (hbarFinrank :
                            letI : Fact p.Prime := ⟨hpprime⟩
                            letI : (H0.subgroupOf MF).Normal := hnormalH0
                            letI : IsElementaryAbelian p
                                (MF ⧸ H0.subgroupOf MF) := hbarElem
                            Module.finrank (ZMod p)
                              (Additive (MF ⧸ H0.subgroupOf MF)) = q) →
                          (hirredRep :
                            letI : Fact p.Prime := ⟨hpprime⟩
                            letI : (H0.subgroupOf MF).Normal := hnormalH0
                            letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                            letI : IsElementaryAbelian p
                                (MF ⧸ H0.subgroupOf MF) := hbarElem
                            letI : MulDistribMulAction U
                                (MF ⧸ H0.subgroupOf MF) :=
                              quotientMulDistribMulAction (A := U) (G := MF)
                                (H0.subgroupOf MF) hH0invU
                            Representation.IsIrreducible
                              (Theory.Representation.ofElementaryAbelianAction (A := U)
                                (G := MF ⧸ H0.subgroupOf MF) (p := p))) →
    theorem_9_7_schurEndFieldData_sec9 MF H0 U p
      hpprime hnormalH0 hUnormMF hH0invU hbarElem →
                          (letI : Fact p.Prime := ⟨hpprime⟩
                          letI : (H0.subgroupOf MF).Normal := hnormalH0
                          letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                          letI : IsElementaryAbelian p
                              (MF ⧸ H0.subgroupOf MF) := hbarElem
                          letI : MulDistribMulAction U
                              (MF ⧸ H0.subgroupOf MF) :=
                            quotientMulDistribMulAction (A := U) (G := MF)
                              (H0.subgroupOf MF) hH0invU
                          let ρ := Theory.Representation.ofElementaryAbelianAction (A := U)
                            (G := MF ⧸ H0.subgroupOf MF) (p := p)
                          let E := Module.End (MonoidAlgebra (ZMod p) U) ρ.asModule
                          (Nat.card E = p ∧ Module.finrank E ρ.asModule = q) ∨
                            (Nat.card E = p ^ q ∧
                              Module.finrank E ρ.asModule = 1)) →
                          (hnormalC : (C.subgroupOf U).Normal) →
                            (letI : (C.subgroupOf U).Normal := hnormalC
                            IsMulCommutative (U ⧸ C.subgroupOf U)) →
                            (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G)) →
                            (hCinv :
                              letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
                              IsInvariant W1 U (C.subgroupOf U)) →
                                theorem_9_7_schurFieldCoordinateAdditiveActionNoVectorRawData_sec9
                                  MF H0 U C W1 hnormalH0 hnormalC hW1normU hCinv := by
  intro h92 hp96 hC hBarU hpprime hqprime hnormalH0 hUnormMF hH0invU
    hbarElem hbarCard hbarFinrank hirredRep hEndField hEndFieldCardAlt hnormalC
    hbarUcomm hW1normU hCinv
  classical
  letI : Fact p.Prime := ⟨hpprime⟩
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
  letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
  letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
    quotientMulDistribMulAction (A := U) (G := MF)
      (H0.subgroupOf MF) hH0invU
  let ρ := Theory.Representation.ofElementaryAbelianAction (A := U)
    (G := MF ⧸ H0.subgroupOf MF) (p := p)
  have hCkerEnd :
      C.subgroupOf U = ((endFieldRep ρ).toHomUnits).ker := by
    rw [MonoidHom.ker_toHomUnits]
    simpa [ρ] using
      theorem_9_7_quotientCentralizerIn_subgroupOf_eq_endFieldRep_ker_sec9
        (MF := MF) (H0 := H0) (U := U) (C := C) (p := p)
        hnormalH0 hUnormMF hH0invU hbarElem hC
  have hEndFieldUnitQuotient :
      (letI : (C.subgroupOf U).Normal := hnormalC
      letI : Fact p.Prime := ⟨hpprime⟩
      letI : (H0.subgroupOf MF).Normal := hnormalH0
      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
      letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
      letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
        quotientMulDistribMulAction (A := U) (G := MF)
          (H0.subgroupOf MF) hH0invU
      let ρ := Theory.Representation.ofElementaryAbelianAction (A := U)
        (G := MF ⧸ H0.subgroupOf MF) (p := p)
      let E := Module.End (MonoidAlgebra (ZMod p) U) ρ.asModule
      let A := Module.End E ρ.asModule
      ∃ Ustar : Subgroup Aˣ,
        ∃ φU : (U ⧸ C.subgroupOf U) ≃* Ustar,
          ∀ x : U,
            ((φU (QuotientGroup.mk' (C.subgroupOf U) x) : Ustar) :
                Aˣ) =
              (endFieldRep ρ).toHomUnits x) := by
    letI : (C.subgroupOf U).Normal := hnormalC
    change
      ∃ Ustar : Subgroup
          (Module.End
            (Module.End (MonoidAlgebra (ZMod p) U) ρ.asModule)
              ρ.asModule)ˣ,
        ∃ φU : (U ⧸ C.subgroupOf U) ≃* Ustar,
          ∀ x : U,
            ((φU (QuotientGroup.mk' (C.subgroupOf U) x) : Ustar) :
                (Module.End
                  (Module.End (MonoidAlgebra (ZMod p) U) ρ.asModule)
                    ρ.asModule)ˣ) =
              (endFieldRep ρ).toHomUnits x
    exact theorem_9_7_quotient_equiv_range_of_eq_ker_sec9
      (C.subgroupOf U) ((endFieldRep ρ).toHomUnits) hCkerEnd
  exact
    theorem_9_7_schur_field_model_coordinate_additive_action_no_vector_raw_from_endField_unit_quotient_source_bridge_sec9
      M MF U W1 W2 H0 C p q u h92 hp96 hC hBarU hpprime hqprime
      hnormalH0 hUnormMF hH0invU hbarElem hbarCard hbarFinrank hirredRep
      hEndField hEndFieldCardAlt hnormalC hEndFieldUnitQuotient hbarUcomm
      hW1normU hCinv

private theorem
    theorem_9_7_schur_field_model_coordinate_additive_action_raw_from_elementary_irreducible_hom_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
          quotientChiefFactorData_9_6 M MF H0 W1 hp) →
          quotientCentralizerIn MF H0 U C →
            quotientBarUCardinality U C u →
              (hpprime : Nat.Prime p) →
                (hqprime : Nat.Prime q) →
                    (hnormalH0 : (H0.subgroupOf MF).Normal) →
                      (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G)) →
                        (hH0invU :
                          letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                          IsInvariant U MF (H0.subgroupOf MF)) →
                      (hbarElem :
                        letI : (H0.subgroupOf MF).Normal := hnormalH0
                        IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF)) →
                        (hbarCard :
                          letI : (H0.subgroupOf MF).Normal := hnormalH0
                          Nat.card (MF ⧸ H0.subgroupOf MF) = p ^ q) →
                          (hbarFinrank :
                            letI : Fact p.Prime := ⟨hpprime⟩
                            letI : (H0.subgroupOf MF).Normal := hnormalH0
                            letI : IsElementaryAbelian p
                                (MF ⧸ H0.subgroupOf MF) := hbarElem
                            Module.finrank (ZMod p)
                              (Additive (MF ⧸ H0.subgroupOf MF)) = q) →
                          (hirredRep :
                            letI : Fact p.Prime := ⟨hpprime⟩
                            letI : (H0.subgroupOf MF).Normal := hnormalH0
                            letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                            letI : IsElementaryAbelian p
                                (MF ⧸ H0.subgroupOf MF) := hbarElem
                            letI : MulDistribMulAction U
                                (MF ⧸ H0.subgroupOf MF) :=
                              quotientMulDistribMulAction (A := U) (G := MF)
                                (H0.subgroupOf MF) hH0invU
                            Representation.IsIrreducible
                              (Theory.Representation.ofElementaryAbelianAction (A := U)
                                (G := MF ⧸ H0.subgroupOf MF) (p := p))) →
    theorem_9_7_schurEndFieldData_sec9 MF H0 U p
      hpprime hnormalH0 hUnormMF hH0invU hbarElem →
                          (letI : Fact p.Prime := ⟨hpprime⟩
                          letI : (H0.subgroupOf MF).Normal := hnormalH0
                          letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                          letI : IsElementaryAbelian p
                              (MF ⧸ H0.subgroupOf MF) := hbarElem
                          letI : MulDistribMulAction U
                              (MF ⧸ H0.subgroupOf MF) :=
                            quotientMulDistribMulAction (A := U) (G := MF)
                              (H0.subgroupOf MF) hH0invU
                          let ρ := Theory.Representation.ofElementaryAbelianAction (A := U)
                            (G := MF ⧸ H0.subgroupOf MF) (p := p)
                          let E := Module.End (MonoidAlgebra (ZMod p) U) ρ.asModule
                          (Nat.card E = p ∧ Module.finrank E ρ.asModule = q) ∨
                            (Nat.card E = p ^ q ∧
                              Module.finrank E ρ.asModule = 1)) →
                          (hnormalC : (C.subgroupOf U).Normal) →
                            (letI : (C.subgroupOf U).Normal := hnormalC
                            IsMulCommutative (U ⧸ C.subgroupOf U)) →
                            (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G)) →
                            (hCinv :
                              letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
                              IsInvariant W1 U (C.subgroupOf U)) →
                                theorem_9_7_schurFieldCoordinateAdditiveActionRawData_sec9
                                  MF H0 U C W1 hnormalH0 hnormalC hW1normU hCinv := by
  intro h92 hp96 hC hBarU hpprime hqprime hnormalH0 hUnormMF hH0invU
    hbarElem hbarCard hbarFinrank hirredRep hEndField hEndFieldCardAlt hnormalC
    hbarUcomm hW1normU hCinv
  classical
  rcases
      theorem_9_7_schur_field_model_coordinate_additive_action_no_vector_raw_from_elementary_irreducible_hom_source_bridge_sec9
        M MF U W1 W2 H0 C p q u h92 hp96 hC hBarU hpprime hqprime
        hnormalH0 hUnormMF hH0invU hbarElem hbarCard hbarFinrank hirredRep
        hEndField hEndFieldCardAlt hnormalC hbarUcomm hW1normU hCinv with
    ⟨F, fieldInst, fintypeInst, Ustar, hspan, φHadd, φU, φWadd, hUaction,
      hWaction⟩
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  have hbarCardOneLt : 1 < Nat.card (MF ⧸ H0.subgroupOf MF) := by
    rw [hbarCard]
    exact one_lt_pow₀ hpprime.one_lt hqprime.ne_zero
  haveI : Nontrivial (MF ⧸ H0.subgroupOf MF) :=
    Finite.one_lt_card_iff_nontrivial.mp hbarCardOneLt
  rcases exists_ne (1 : MF ⧸ H0.subgroupOf MF) with ⟨s, hs⟩
  exact ⟨F, fieldInst, fintypeInst, Ustar, hspan, s, hs, φHadd, φU, φWadd,
    hUaction, hWaction⟩

private theorem
    theorem_9_7_schur_field_model_compatibility_additive_action_raw_from_elementary_irreducible_hom_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
          quotientChiefFactorData_9_6 M MF H0 W1 hp) →
          quotientCentralizerIn MF H0 U C →
            quotientBarUCardinality U C u →
              (hpprime : Nat.Prime p) →
                (hqprime : Nat.Prime q) →
                    (hnormalH0 : (H0.subgroupOf MF).Normal) →
                      (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G)) →
                        (hH0invU :
                          letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                          IsInvariant U MF (H0.subgroupOf MF)) →
                      (hbarElem :
                        letI : (H0.subgroupOf MF).Normal := hnormalH0
                        IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF)) →
                        (hbarCard :
                          letI : (H0.subgroupOf MF).Normal := hnormalH0
                          Nat.card (MF ⧸ H0.subgroupOf MF) = p ^ q) →
                          (hbarFinrank :
                            letI : Fact p.Prime := ⟨hpprime⟩
                            letI : (H0.subgroupOf MF).Normal := hnormalH0
                            letI : IsElementaryAbelian p
                                (MF ⧸ H0.subgroupOf MF) := hbarElem
                            Module.finrank (ZMod p)
                              (Additive (MF ⧸ H0.subgroupOf MF)) = q) →
                          (hirredRep :
                            letI : Fact p.Prime := ⟨hpprime⟩
                            letI : (H0.subgroupOf MF).Normal := hnormalH0
                            letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                            letI : IsElementaryAbelian p
                                (MF ⧸ H0.subgroupOf MF) := hbarElem
                            letI : MulDistribMulAction U
                                (MF ⧸ H0.subgroupOf MF) :=
                              quotientMulDistribMulAction (A := U) (G := MF)
                                (H0.subgroupOf MF) hH0invU
                            Representation.IsIrreducible
                              (Theory.Representation.ofElementaryAbelianAction (A := U)
                                (G := MF ⧸ H0.subgroupOf MF) (p := p))) →
    theorem_9_7_schurEndFieldData_sec9 MF H0 U p
      hpprime hnormalH0 hUnormMF hH0invU hbarElem →
                          (letI : Fact p.Prime := ⟨hpprime⟩
                          letI : (H0.subgroupOf MF).Normal := hnormalH0
                          letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                          letI : IsElementaryAbelian p
                              (MF ⧸ H0.subgroupOf MF) := hbarElem
                          letI : MulDistribMulAction U
                              (MF ⧸ H0.subgroupOf MF) :=
                            quotientMulDistribMulAction (A := U) (G := MF)
                              (H0.subgroupOf MF) hH0invU
                          let ρ := Theory.Representation.ofElementaryAbelianAction (A := U)
                            (G := MF ⧸ H0.subgroupOf MF) (p := p)
                          let E := Module.End (MonoidAlgebra (ZMod p) U) ρ.asModule
                          (Nat.card E = p ∧ Module.finrank E ρ.asModule = q) ∨
                            (Nat.card E = p ^ q ∧
                              Module.finrank E ρ.asModule = 1)) →
                          (hnormalC : (C.subgroupOf U).Normal) →
                            (letI : (C.subgroupOf U).Normal := hnormalC
                            IsMulCommutative (U ⧸ C.subgroupOf U)) →
                            (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G)) →
                            (hCinv :
                              letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
                              IsInvariant W1 U (C.subgroupOf U)) →
                                theorem_9_7_schurFieldHomCompatibilityAdditiveActionRawData_sec9
                                  MF H0 U C W1 hnormalH0 hnormalC hW1normU hCinv := by
  intro h92 hp96 hC hBarU hpprime hqprime hnormalH0 hUnormMF hH0invU
    hbarElem hbarCard hbarFinrank hirredRep hEndField hEndFieldCardAlt hnormalC
    hbarUcomm hW1normU hCinv
  classical
  rcases
      theorem_9_7_schur_field_model_coordinate_additive_action_raw_from_elementary_irreducible_hom_source_bridge_sec9
        M MF U W1 W2 H0 C p q u h92 hp96 hC hBarU hpprime hqprime
        hnormalH0 hUnormMF hH0invU hbarElem hbarCard hbarFinrank hirredRep
        hEndField hEndFieldCardAlt hnormalC hbarUcomm hW1normU hCinv with
    ⟨F, fieldInst, fintypeInst, Ustar, hspan, _s, _hsne, φHadd, φU,
      φWadd, hUactionAdd, hWactionAdd⟩
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  letI : (C.subgroupOf U).Normal := hnormalC
  letI : Field F := fieldInst
  letI : Fintype F := fintypeInst
  letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
  letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
    quotientMulDistribMulAction (A := W1) (G := U)
      (C.subgroupOf U) hCinv
  let φH : (MF ⧸ H0.subgroupOf MF) ≃* Multiplicative F :=
    theorem_9_7_addEquivToMulEquivMultiplicative_sec9
      (MF ⧸ H0.subgroupOf MF) F φHadd
  refine ⟨F, fieldInst, fintypeInst, Ustar, hspan, φH, φU, φWadd, ?_, ?_⟩
  · intro x h
    rcases hUactionAdd x h with ⟨hconjMF, hφHadd⟩
    refine ⟨hconjMF, ?_⟩
    change Multiplicative.ofAdd
        (φHadd (Additive.ofMul (QuotientGroup.mk' (H0.subgroupOf MF)
          ⟨(x.out : U)⁻¹ * (h : G) * (x.out : U), hconjMF h⟩))) =
      Multiplicative.ofAdd
        ((((φU x : Ustar) : Fˣ) : F) *
          φHadd (Additive.ofMul (QuotientGroup.mk' (H0.subgroupOf MF) h)))
    exact congrArg Multiplicative.ofAdd hφHadd
  · intro w h
    rcases hWactionAdd w h with ⟨hconjMF, hφHadd, hunit⟩
    refine ⟨hconjMF, ?_, hunit⟩
    change Multiplicative.ofAdd
        (φHadd (Additive.ofMul (QuotientGroup.mk' (H0.subgroupOf MF)
          ⟨(w : G)⁻¹ * (h : G) * (w : G), hconjMF h⟩))) =
      Multiplicative.ofAdd
        ((φWadd w)
          (φHadd (Additive.ofMul (QuotientGroup.mk' (H0.subgroupOf MF) h))))
    exact congrArg Multiplicative.ofAdd hφHadd

private theorem
    theorem_9_7_schur_additive_right_mul_of_action_raw_sec9
    {G : Type u} [Group G] [Finite G]
    {MF H0 U C W1 : Subgroup G}
    (hnormalH0 : (H0.subgroupOf MF).Normal)
    (hnormalC : (C.subgroupOf U).Normal)
    (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G))
    (hCinv :
      letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
      IsInvariant W1 U (C.subgroupOf U))
    (F : Type u) [Field F] [Fintype F]
    (Ustar : Subgroup Fˣ)
    (hspan : AddSubgroup.closure
      (((fun x : Ustar => ((x : Fˣ) : F)) '' Set.univ) : Set F) = ⊤)
    (φH : (MF ⧸ H0.subgroupOf MF) ≃* Multiplicative F)
    (φU : (U ⧸ C.subgroupOf U) ≃* Ustar)
    (φWadd : W1 → F ≃+ F)
    (hWaction :
      letI : (C.subgroupOf U).Normal := hnormalC
      letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
      letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
        quotientMulDistribMulAction (A := W1) (G := U)
          (C.subgroupOf U) hCinv
      ∀ w : W1, ∀ h : MF,
        ∃ hconjMF : ∀ y : MF,
          (w : G)⁻¹ * (y : G) * (w : G) ∈ MF,
          φH (QuotientGroup.mk' (H0.subgroupOf MF)
            ⟨(w : G)⁻¹ * (h : G) * (w : G), hconjMF h⟩) =
            Multiplicative.ofAdd
              ((φWadd w) (Multiplicative.toAdd
                (φH (QuotientGroup.mk' (H0.subgroupOf MF) h)))) ∧
          ∀ x : U ⧸ C.subgroupOf U,
            (φWadd w) ((((φU x : Ustar) : Fˣ) : F)) =
              (((φU ((w⁻¹ : W1) • x) : Ustar) : Fˣ) : F)) :
    ∀ w : W1, ∀ z : F, ∀ u : Ustar,
      (φWadd w) (z * (((u : Ustar) : Fˣ) : F)) =
        (φWadd w) z * (φWadd w) ((((u : Ustar) : Fˣ) : F)) := by
  classical
  letI : (C.subgroupOf U).Normal := hnormalC
  letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
  letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
    quotientMulDistribMulAction (A := W1) (G := U)
      (C.subgroupOf U) hCinv
  intro w z u
  let ψ : F ≃+ F := φWadd w
  let uF : F := (((u : Ustar) : Fˣ) : F)
  let S : Set F := (((fun x : Ustar => ((x : Fˣ) : F)) '' Set.univ) : Set F)
  have hunit_mul :
      ∀ v u : Ustar,
        ψ (((v * u : Ustar) : Fˣ) : F) =
          ψ (((v : Ustar) : Fˣ) : F) * ψ (((u : Ustar) : Fˣ) : F) := by
    intro v u
    rcases hWaction w (1 : MF) with ⟨_hconjMF, _hφH, hunit⟩
    have hv :
        ψ (((v : Ustar) : Fˣ) : F) =
          (((φU ((w⁻¹ : W1) • (φU.symm v)) : Ustar) : Fˣ) : F) := by
      simpa [ψ] using hunit (φU.symm v)
    have hu :
        ψ (((u : Ustar) : Fˣ) : F) =
          (((φU ((w⁻¹ : W1) • (φU.symm u)) : Ustar) : Fˣ) : F) := by
      simpa [ψ] using hunit (φU.symm u)
    have hprod :
        ψ (((v * u : Ustar) : Fˣ) : F) =
          (((φU ((w⁻¹ : W1) • (φU.symm (v * u))) : Ustar) : Fˣ) : F) := by
      simpa [ψ] using hunit (φU.symm (v * u))
    have hquot :
        (w⁻¹ : W1) • (φU.symm (v * u)) =
          ((w⁻¹ : W1) • (φU.symm v)) *
            ((w⁻¹ : W1) • (φU.symm u)) := by
      calc
        (w⁻¹ : W1) • (φU.symm (v * u)) =
            (w⁻¹ : W1) • (φU.symm v * φU.symm u) := by
              simp
        _ = ((w⁻¹ : W1) • (φU.symm v)) *
            ((w⁻¹ : W1) • (φU.symm u)) := by
              simp
    calc
      ψ (((v * u : Ustar) : Fˣ) : F) =
          (((φU ((w⁻¹ : W1) • (φU.symm (v * u))) : Ustar) : Fˣ) : F) := hprod
      _ = (((φU ((w⁻¹ : W1) • (φU.symm v)) : Ustar) : Fˣ) : F) *
          (((φU ((w⁻¹ : W1) • (φU.symm u)) : Ustar) : Fˣ) : F) := by
            simp
      _ = ψ (((v : Ustar) : Fˣ) : F) *
          ψ (((u : Ustar) : Fˣ) : F) := by
            rw [hv, hu]
  have hgen : ∀ z ∈ S, ψ (z * uF) = ψ z * ψ uF := by
    intro z hz
    rcases hz with ⟨v, _hv, rfl⟩
    simpa [uF, ψ] using hunit_mul v u
  have hzmem : z ∈ AddSubgroup.closure S := by
    rw [hspan]
    exact (show z ∈ (⊤ : AddSubgroup F) from AddSubgroup.mem_top z)
  have hclosed : ∀ z ∈ AddSubgroup.closure S, ψ (z * uF) = ψ z * ψ uF := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
        exact hgen z hz
    | zero =>
        simp [uF, ψ]
    | add x y _hx _hy hx hy =>
        calc
          ψ ((x + y) * uF) = ψ (x * uF + y * uF) := by
            rw [add_mul]
          _ = ψ (x * uF) + ψ (y * uF) := by
            simp [ψ]
          _ = ψ x * ψ uF + ψ y * ψ uF := by
            rw [hx, hy]
          _ = (ψ x + ψ y) * ψ uF := by
            rw [add_mul]
          _ = ψ (x + y) * ψ uF := by
            simp [ψ]
    | neg x _hx hx =>
        calc
          ψ ((-x) * uF) = ψ (-(x * uF)) := by
            rw [neg_mul]
          _ = -ψ (x * uF) := by
            simp [ψ]
          _ = -(ψ x * ψ uF) := by
            rw [hx]
          _ = ψ (-x) * ψ uF := by
            simp [ψ, neg_mul]
  simpa [uF, ψ] using hclosed z hzmem

private theorem
    theorem_9_7_schur_field_model_compatibility_additive_raw_from_elementary_irreducible_hom_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
          quotientChiefFactorData_9_6 M MF H0 W1 hp) →
          quotientCentralizerIn MF H0 U C →
            quotientBarUCardinality U C u →
              (hpprime : Nat.Prime p) →
                (hqprime : Nat.Prime q) →
                    (hnormalH0 : (H0.subgroupOf MF).Normal) →
                      (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G)) →
                        (hH0invU :
                          letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                          IsInvariant U MF (H0.subgroupOf MF)) →
                      (hbarElem :
                        letI : (H0.subgroupOf MF).Normal := hnormalH0
                        IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF)) →
                        (hbarCard :
                          letI : (H0.subgroupOf MF).Normal := hnormalH0
                          Nat.card (MF ⧸ H0.subgroupOf MF) = p ^ q) →
                          (hbarFinrank :
                            letI : Fact p.Prime := ⟨hpprime⟩
                            letI : (H0.subgroupOf MF).Normal := hnormalH0
                            letI : IsElementaryAbelian p
                                (MF ⧸ H0.subgroupOf MF) := hbarElem
                            Module.finrank (ZMod p)
                              (Additive (MF ⧸ H0.subgroupOf MF)) = q) →
                          (hirredRep :
                            letI : Fact p.Prime := ⟨hpprime⟩
                            letI : (H0.subgroupOf MF).Normal := hnormalH0
                            letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                            letI : IsElementaryAbelian p
                                (MF ⧸ H0.subgroupOf MF) := hbarElem
                            letI : MulDistribMulAction U
                                (MF ⧸ H0.subgroupOf MF) :=
                              quotientMulDistribMulAction (A := U) (G := MF)
                                (H0.subgroupOf MF) hH0invU
                            Representation.IsIrreducible
                              (Theory.Representation.ofElementaryAbelianAction (A := U)
                                (G := MF ⧸ H0.subgroupOf MF) (p := p))) →
                          theorem_9_7_schurEndFieldData_sec9 MF H0 U p
                            hpprime hnormalH0 hUnormMF hH0invU hbarElem →
                          (letI : Fact p.Prime := ⟨hpprime⟩
                          letI : (H0.subgroupOf MF).Normal := hnormalH0
                          letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                          letI : IsElementaryAbelian p
                              (MF ⧸ H0.subgroupOf MF) := hbarElem
                          letI : MulDistribMulAction U
                              (MF ⧸ H0.subgroupOf MF) :=
                            quotientMulDistribMulAction (A := U) (G := MF)
                              (H0.subgroupOf MF) hH0invU
                          let ρ := Theory.Representation.ofElementaryAbelianAction (A := U)
                            (G := MF ⧸ H0.subgroupOf MF) (p := p)
                          let E := Module.End (MonoidAlgebra (ZMod p) U) ρ.asModule
                          (Nat.card E = p ∧ Module.finrank E ρ.asModule = q) ∨
                            (Nat.card E = p ^ q ∧
                              Module.finrank E ρ.asModule = 1)) →
                          (hnormalC : (C.subgroupOf U).Normal) →
                            (letI : (C.subgroupOf U).Normal := hnormalC
                            IsMulCommutative (U ⧸ C.subgroupOf U)) →
                            (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G)) →
                              (hCinv :
                                letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
                                IsInvariant W1 U (C.subgroupOf U)) →
                                theorem_9_7_schurFieldHomCompatibilityAdditiveRawData_sec9
                                  MF H0 U C W1 hnormalH0 hnormalC hW1normU hCinv := by
  intro h92 hp96 hC hBarU hpprime hqprime hnormalH0 hUnormMF hH0invU
    hbarElem hbarCard hbarFinrank hirredRep hEndField hEndFieldCardAlt hnormalC
    hbarUcomm hW1normU hCinv
  classical
  rcases
      theorem_9_7_schur_field_model_compatibility_additive_action_raw_from_elementary_irreducible_hom_source_bridge_sec9
        M MF U W1 W2 H0 C p q u h92 hp96 hC hBarU hpprime hqprime
        hnormalH0 hUnormMF hH0invU hbarElem hbarCard hbarFinrank hirredRep
        hEndField hEndFieldCardAlt hnormalC hbarUcomm hW1normU hCinv with
    ⟨F, fieldInst, fintypeInst, Ustar, hspan, φH, φU, φWadd, hUaction,
      hWactionRaw⟩
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  letI : (C.subgroupOf U).Normal := hnormalC
  letI : Field F := fieldInst
  letI : Fintype F := fintypeInst
  letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
  letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
    quotientMulDistribMulAction (A := W1) (G := U) (C.subgroupOf U) hCinv
  refine ⟨F, fieldInst, fintypeInst, Ustar, hspan, φH, φU, φWadd, hUaction, ?_⟩
  intro w h
  rcases hWactionRaw w h with ⟨hconjMF, hφH, hunit⟩
  refine ⟨hconjMF, hφH, ?_, hunit⟩
  exact theorem_9_7_schur_additive_right_mul_of_action_raw_sec9
    hnormalH0 hnormalC hW1normU hCinv F Ustar hspan φH φU
    φWadd hWactionRaw w

private theorem
    theorem_9_7_schur_field_model_compatibility_pointwise_raw_from_elementary_irreducible_hom_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
          quotientChiefFactorData_9_6 M MF H0 W1 hp) →
          quotientCentralizerIn MF H0 U C →
            quotientBarUCardinality U C u →
              (hpprime : Nat.Prime p) →
                (hqprime : Nat.Prime q) →
                    (hnormalH0 : (H0.subgroupOf MF).Normal) →
                      (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G)) →
                        (hH0invU :
                          letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                          IsInvariant U MF (H0.subgroupOf MF)) →
                      (hbarElem :
                        letI : (H0.subgroupOf MF).Normal := hnormalH0
                        IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF)) →
                        (hbarCard :
                          letI : (H0.subgroupOf MF).Normal := hnormalH0
                          Nat.card (MF ⧸ H0.subgroupOf MF) = p ^ q) →
                          (hbarFinrank :
                            letI : Fact p.Prime := ⟨hpprime⟩
                            letI : (H0.subgroupOf MF).Normal := hnormalH0
                            letI : IsElementaryAbelian p
                                (MF ⧸ H0.subgroupOf MF) := hbarElem
                            Module.finrank (ZMod p)
                              (Additive (MF ⧸ H0.subgroupOf MF)) = q) →
                          (hirredRep :
                            letI : Fact p.Prime := ⟨hpprime⟩
                            letI : (H0.subgroupOf MF).Normal := hnormalH0
                            letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                            letI : IsElementaryAbelian p
                                (MF ⧸ H0.subgroupOf MF) := hbarElem
                            letI : MulDistribMulAction U
                                (MF ⧸ H0.subgroupOf MF) :=
                              quotientMulDistribMulAction (A := U) (G := MF)
                                (H0.subgroupOf MF) hH0invU
                            Representation.IsIrreducible
                              (Theory.Representation.ofElementaryAbelianAction (A := U)
                                (G := MF ⧸ H0.subgroupOf MF) (p := p))) →
                          theorem_9_7_schurEndFieldData_sec9 MF H0 U p
                            hpprime hnormalH0 hUnormMF hH0invU hbarElem →
                          (letI : Fact p.Prime := ⟨hpprime⟩
                          letI : (H0.subgroupOf MF).Normal := hnormalH0
                          letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                          letI : IsElementaryAbelian p
                              (MF ⧸ H0.subgroupOf MF) := hbarElem
                          letI : MulDistribMulAction U
                              (MF ⧸ H0.subgroupOf MF) :=
                            quotientMulDistribMulAction (A := U) (G := MF)
                              (H0.subgroupOf MF) hH0invU
                          let ρ := Theory.Representation.ofElementaryAbelianAction (A := U)
                            (G := MF ⧸ H0.subgroupOf MF) (p := p)
                          let E := Module.End (MonoidAlgebra (ZMod p) U) ρ.asModule
                          (Nat.card E = p ∧ Module.finrank E ρ.asModule = q) ∨
                            (Nat.card E = p ^ q ∧
                              Module.finrank E ρ.asModule = 1)) →
                          (hnormalC : (C.subgroupOf U).Normal) →
                            (letI : (C.subgroupOf U).Normal := hnormalC
                            IsMulCommutative (U ⧸ C.subgroupOf U)) →
                            (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G)) →
                              (hCinv :
                                letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
                                IsInvariant W1 U (C.subgroupOf U)) →
                                theorem_9_7_schurFieldHomCompatibilityPointwiseRawData_sec9
                                  MF H0 U C W1 hnormalH0 hnormalC hW1normU hCinv := by
  intro h92 hp96 hC hBarU hpprime hqprime hnormalH0 hUnormMF hH0invU
    hbarElem hbarCard hbarFinrank hirredRep hEndField hEndFieldCardAlt hnormalC
    hbarUcomm hW1normU hCinv
  classical
  rcases
      theorem_9_7_schur_field_model_compatibility_additive_raw_from_elementary_irreducible_hom_source_bridge_sec9
        M MF U W1 W2 H0 C p q u h92 hp96 hC hBarU hpprime hqprime
        hnormalH0 hUnormMF hH0invU hbarElem hbarCard hbarFinrank hirredRep
        hEndField hEndFieldCardAlt hnormalC hbarUcomm hW1normU hCinv with
    ⟨F, fieldInst, fintypeInst, Ustar, hspan, φH, φU, φWadd, hUaction,
      hWactionAdd⟩
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  letI : (C.subgroupOf U).Normal := hnormalC
  letI : Field F := fieldInst
  letI : Fintype F := fintypeInst
  letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
  letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
    quotientMulDistribMulAction (A := W1) (G := U) (C.subgroupOf U) hCinv
  let φW : W1 → RingAut F := fun w =>
    theorem_9_7_ringAut_of_addEquiv_on_unit_span_sec9 F Ustar hspan (φWadd w)
      (fun z u => by
        rcases hWactionAdd w 1 with ⟨_hconjMF, _hφH, hright, _hunit⟩
        exact hright z u)
  refine ⟨F, fieldInst, fintypeInst, Ustar, hspan, φH, φU, φW, hUaction, ?_⟩
  intro w h
  rcases hWactionAdd w h with ⟨hconjMF, hφH, _hright, hunit⟩
  refine ⟨hconjMF, ?_, ?_⟩
  · change
      φH (QuotientGroup.mk' (H0.subgroupOf MF)
        ⟨(w : G)⁻¹ * (h : MF) * (w : G), hconjMF h⟩) =
        Multiplicative.ofAdd
          ((φWadd w) (Multiplicative.toAdd
            (φH (QuotientGroup.mk' (H0.subgroupOf MF) h))))
    exact hφH
  · intro x
    apply Units.ext
    change (φW w) ((((φU x : Ustar) : Fˣ) : F)) =
      (((φU ((w⁻¹ : W1) • x) : Ustar) : Fˣ) : F)
    change (φWadd w) ((((φU x : Ustar) : Fˣ) : F)) =
      (((φU ((w⁻¹ : W1) • x) : Ustar) : Fˣ) : F)
    exact hunit x

private theorem
    theorem_9_7_schur_field_model_compatibility_noninjective_raw_from_elementary_irreducible_hom_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
          quotientChiefFactorData_9_6 M MF H0 W1 hp) →
          quotientCentralizerIn MF H0 U C →
            quotientBarUCardinality U C u →
              (hpprime : Nat.Prime p) →
                (hqprime : Nat.Prime q) →
                    (hnormalH0 : (H0.subgroupOf MF).Normal) →
                      (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G)) →
                        (hH0invU :
                          letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                          IsInvariant U MF (H0.subgroupOf MF)) →
                      (hbarElem :
                        letI : (H0.subgroupOf MF).Normal := hnormalH0
                        IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF)) →
                        (hbarCard :
                          letI : (H0.subgroupOf MF).Normal := hnormalH0
                          Nat.card (MF ⧸ H0.subgroupOf MF) = p ^ q) →
                          (hbarFinrank :
                            letI : Fact p.Prime := ⟨hpprime⟩
                            letI : (H0.subgroupOf MF).Normal := hnormalH0
                            letI : IsElementaryAbelian p
                                (MF ⧸ H0.subgroupOf MF) := hbarElem
                            Module.finrank (ZMod p)
                              (Additive (MF ⧸ H0.subgroupOf MF)) = q) →
                          (hirredRep :
                            letI : Fact p.Prime := ⟨hpprime⟩
                            letI : (H0.subgroupOf MF).Normal := hnormalH0
                            letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                            letI : IsElementaryAbelian p
                                (MF ⧸ H0.subgroupOf MF) := hbarElem
                            letI : MulDistribMulAction U
                                (MF ⧸ H0.subgroupOf MF) :=
                              quotientMulDistribMulAction (A := U) (G := MF)
                                (H0.subgroupOf MF) hH0invU
                            Representation.IsIrreducible
                              (Theory.Representation.ofElementaryAbelianAction (A := U)
                                (G := MF ⧸ H0.subgroupOf MF) (p := p))) →
                          theorem_9_7_schurEndFieldData_sec9 MF H0 U p
                            hpprime hnormalH0 hUnormMF hH0invU hbarElem →
                          (letI : Fact p.Prime := ⟨hpprime⟩
                          letI : (H0.subgroupOf MF).Normal := hnormalH0
                          letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                          letI : IsElementaryAbelian p
                              (MF ⧸ H0.subgroupOf MF) := hbarElem
                          letI : MulDistribMulAction U
                              (MF ⧸ H0.subgroupOf MF) :=
                            quotientMulDistribMulAction (A := U) (G := MF)
                              (H0.subgroupOf MF) hH0invU
                          let ρ := Theory.Representation.ofElementaryAbelianAction (A := U)
                            (G := MF ⧸ H0.subgroupOf MF) (p := p)
                          let E := Module.End (MonoidAlgebra (ZMod p) U) ρ.asModule
                          (Nat.card E = p ∧ Module.finrank E ρ.asModule = q) ∨
                            (Nat.card E = p ^ q ∧
                              Module.finrank E ρ.asModule = 1)) →
                          (hnormalC : (C.subgroupOf U).Normal) →
                            (letI : (C.subgroupOf U).Normal := hnormalC
                            IsMulCommutative (U ⧸ C.subgroupOf U)) →
                            (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G)) →
                              (hCinv :
                                letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
                                IsInvariant W1 U (C.subgroupOf U)) →
                                theorem_9_7_schurFieldHomCompatibilityNoninjectiveRawData_sec9
                                  MF H0 U C W1 hnormalH0 hnormalC hW1normU hCinv := by
  intro h92 hp96 hC hBarU hpprime hqprime hnormalH0 hUnormMF hH0invU
    hbarElem hbarCard hbarFinrank hirredRep hEndField hEndFieldCardAlt hnormalC
    hbarUcomm hW1normU hCinv
  classical
  rcases
      theorem_9_7_schur_field_model_compatibility_pointwise_raw_from_elementary_irreducible_hom_source_bridge_sec9
        M MF U W1 W2 H0 C p q u h92 hp96 hC hBarU hpprime hqprime
        hnormalH0 hUnormMF hH0invU hbarElem hbarCard hbarFinrank hirredRep
        hEndField hEndFieldCardAlt hnormalC hbarUcomm hW1normU hCinv with
    ⟨F, fieldInst, fintypeInst, Ustar, hspan, φH, φU, φWfun, hUaction, hWaction⟩
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  letI : (C.subgroupOf U).Normal := hnormalC
  letI : Field F := fieldInst
  letI : Fintype F := fintypeInst
  letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
  letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
    quotientMulDistribMulAction (A := W1) (G := U) (C.subgroupOf U) hCinv
  have hW1cyc : IsCyclic W1 := by
    rcases h92.typePDefinitionData with
      ⟨_hMFsource, hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD,
        _hUnil, _hW1normU, _hcompDU, _hMFnotcyc, _hsecond, _hfitEq,
        _hfitLeD, _hW2le, _hW2cyc, _hW2ne, _hcentW1, _hnormX⟩
    exact hW1cyc
  let φW : W1 →* RingAut F :=
    theorem_9_7_schur_phiW_hom_of_pointwise_action_sec9
      MF H0 W1 hnormalH0 hW1cyc F φH φWfun (fun w h => by
        rcases hWaction w h with ⟨hconjMF, hφH, _hcompat⟩
        exact ⟨hconjMF, hφH⟩)
  have hWactionHom :
      ∀ w : W1, ∀ h : MF,
        ∃ hconjMF : ∀ y : MF,
          (w : G)⁻¹ * (y : G) * (w : G) ∈ MF,
          φH (QuotientGroup.mk' (H0.subgroupOf MF)
            ⟨(w : G)⁻¹ * (h : G) * (w : G), hconjMF h⟩) =
            Multiplicative.ofAdd
              ((φW w) (Multiplicative.toAdd
                (φH (QuotientGroup.mk' (H0.subgroupOf MF) h)))) ∧
          ∀ x : U ⧸ C.subgroupOf U,
            Units.map (φW w).toMonoidHom (φU x : Ustar) =
              (φU ((w⁻¹ : W1) • x) : Ustar) := by
    intro w h
    rcases hWaction w h with ⟨hconjMF, hφH, hcompat⟩
    refine ⟨hconjMF, ?_, ?_⟩
    · simpa [φW, theorem_9_7_schur_phiW_hom_of_pointwise_action_sec9] using hφH
    · intro x
      simpa [φW, theorem_9_7_schur_phiW_hom_of_pointwise_action_sec9] using hcompat x
  exact ⟨F, fieldInst, fintypeInst, Ustar, hspan, φH, φU, φW, hUaction, hWactionHom⟩

private theorem
    theorem_9_7_schur_field_model_compatibility_raw_from_elementary_irreducible_hom_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
          quotientChiefFactorData_9_6 M MF H0 W1 hp) →
          quotientCentralizerIn MF H0 U C →
            quotientBarUCardinality U C u →
              (hpprime : Nat.Prime p) →
                (hqprime : Nat.Prime q) →
                    (hnormalH0 : (H0.subgroupOf MF).Normal) →
                      (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G)) →
                        (hH0invU :
                          letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                          IsInvariant U MF (H0.subgroupOf MF)) →
                      (hbarElem :
                        letI : (H0.subgroupOf MF).Normal := hnormalH0
                        IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF)) →
                        (hbarCard :
                          letI : (H0.subgroupOf MF).Normal := hnormalH0
                          Nat.card (MF ⧸ H0.subgroupOf MF) = p ^ q) →
                          (hbarFinrank :
                            letI : Fact p.Prime := ⟨hpprime⟩
                            letI : (H0.subgroupOf MF).Normal := hnormalH0
                            letI : IsElementaryAbelian p
                                (MF ⧸ H0.subgroupOf MF) := hbarElem
                            Module.finrank (ZMod p)
                              (Additive (MF ⧸ H0.subgroupOf MF)) = q) →
                          (hirredRep :
                            letI : Fact p.Prime := ⟨hpprime⟩
                            letI : (H0.subgroupOf MF).Normal := hnormalH0
                            letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                            letI : IsElementaryAbelian p
                                (MF ⧸ H0.subgroupOf MF) := hbarElem
                            letI : MulDistribMulAction U
                                (MF ⧸ H0.subgroupOf MF) :=
                              quotientMulDistribMulAction (A := U) (G := MF)
                                (H0.subgroupOf MF) hH0invU
                            Representation.IsIrreducible
                              (Theory.Representation.ofElementaryAbelianAction (A := U)
                                (G := MF ⧸ H0.subgroupOf MF) (p := p))) →
                          theorem_9_7_schurEndFieldData_sec9 MF H0 U p
                            hpprime hnormalH0 hUnormMF hH0invU hbarElem →
                          (letI : Fact p.Prime := ⟨hpprime⟩
                          letI : (H0.subgroupOf MF).Normal := hnormalH0
                          letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                          letI : IsElementaryAbelian p
                              (MF ⧸ H0.subgroupOf MF) := hbarElem
                          letI : MulDistribMulAction U
                              (MF ⧸ H0.subgroupOf MF) :=
                            quotientMulDistribMulAction (A := U) (G := MF)
                              (H0.subgroupOf MF) hH0invU
                          let ρ := Theory.Representation.ofElementaryAbelianAction (A := U)
                            (G := MF ⧸ H0.subgroupOf MF) (p := p)
                          let E := Module.End (MonoidAlgebra (ZMod p) U) ρ.asModule
                          (Nat.card E = p ∧ Module.finrank E ρ.asModule = q) ∨
                            (Nat.card E = p ^ q ∧
                              Module.finrank E ρ.asModule = 1)) →
                          (hnormalC : (C.subgroupOf U).Normal) →
                            (letI : (C.subgroupOf U).Normal := hnormalC
                            IsMulCommutative (U ⧸ C.subgroupOf U)) →
                            (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G)) →
                              (hCinv :
                                letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
                                IsInvariant W1 U (C.subgroupOf U)) →
                                theorem_9_7_schurFieldHomCompatibilityRawData_sec9
                                  MF H0 U C W1 hnormalH0 hnormalC hW1normU hCinv := by
  intro h92 hp96 hC hBarU hpprime hqprime hnormalH0 hUnormMF hH0invU
    hbarElem hbarCard hbarFinrank hirredRep hEndField hEndFieldCardAlt hnormalC
    hbarUcomm hW1normU hCinv
  classical
  rcases
      theorem_9_7_schur_field_model_compatibility_noninjective_raw_from_elementary_irreducible_hom_source_bridge_sec9
        M MF U W1 W2 H0 C p q u h92 hp96 hC hBarU hpprime hqprime
        hnormalH0 hUnormMF hH0invU hbarElem hbarCard hbarFinrank hirredRep
        hEndField hEndFieldCardAlt hnormalC hbarUcomm hW1normU hCinv with
    ⟨F, fieldInst, fintypeInst, Ustar, hspan, φH, φU, φW, hUaction, hWaction⟩
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  letI : (C.subgroupOf U).Normal := hnormalC
  letI : Field F := fieldInst
  letI : Fintype F := fintypeInst
  letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
  letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
    quotientMulDistribMulAction (A := W1) (G := U) (C.subgroupOf U) hCinv
  have hW1normMF : W1 ≤ Subgroup.normalizer (MF : Set G) :=
    theorem_9_7_W1_le_normalizer_MF_of_hypothesis_9_2_sec9 h92
  letI : Subgroup.Normalizes W1 MF := ⟨hW1normMF⟩
  have hW1leM : W1 ≤ M := by
    rcases h92.typePDefinitionData with
      ⟨_hMFsource, _hW1cyc, _hW1ne, hW1hall, _hcompMW1, _hUleD,
        _hUnil, _hW1normU, _hcompDU, _hMFnotcyc, _hsecond, _hfitEq,
        _hfitLeD, _hW2le, _hW2cyc, _hW2ne, _hcentW1, _hnormX⟩
    exact hW1hall.1
  have hMFleM : MF ≤ M := by
    rcases hp96 with ⟨_hp, _hp_eq, hpData, _h96⟩
    exact hpData.2.1
  have hH0normalM : (H0.subgroupOf M).Normal := by
    rcases hp96 with ⟨_hp, _hp_eq, hpData, _h96⟩
    exact hpData.2.2.1
  have hH0invW1 : IsInvariant W1 MF (H0.subgroupOf MF) :=
    subgroupOf_MF_isInvariant_of_subgroupOf_M_normal_sec9 M MF W1 H0
      hMFleM hW1leM hH0normalM hW1normMF
  letI : MulDistribMulAction W1 (MF ⧸ H0.subgroupOf MF) :=
    quotientMulDistribMulAction (A := W1) (G := MF)
      (H0.subgroupOf MF) hH0invW1
  have hfixed_ne_top :
      fixedPointSubgroup W1 (MF ⧸ H0.subgroupOf MF) ≠ ⊤ :=
    theorem_9_7_W1_fixedPointSubgroup_ne_top_of_chief_data_sec9
      h92 hp96 hpprime hqprime hnormalH0 hW1normMF hH0invW1 hbarCard
  have hW1card : Nat.card W1 = q := by
    exact h92.q_eq
  have hW1prime : Nat.Prime (Nat.card W1) := by
    simpa [hW1card] using hqprime
  have hφW_inj : Function.Injective φW := by
    intro w1 w2 hw
    suffices hker : w2⁻¹ * w1 = 1 by
      have hmul := congrArg (fun z : W1 => w2 * z) hker
      simpa [mul_assoc] using hmul
    let w : W1 := w2⁻¹ * w1
    have hφWw : φW w = 1 := by
      calc
        φW w = (φW w2)⁻¹ * φW w1 := by
          simp [w]
        _ = 1 := by
          rw [hw]
          simp
    by_contra hwne
    have hwinv_ne : (w⁻¹ : W1) ≠ 1 := by
      intro hwinv
      exact hwne (inv_eq_one.mp hwinv)
    have hfix_gen : ∀ x : MF ⧸ H0.subgroupOf MF, (w⁻¹ : W1) • x = x := by
      intro x
      refine QuotientGroup.induction_on x ?_
      intro h
      rcases hWaction w h with ⟨hconjMF, hφH, _hcompat⟩
      have hφH_same :
          φH (QuotientGroup.mk' (H0.subgroupOf MF)
              ⟨(w : G)⁻¹ * (h : G) * (w : G), hconjMF h⟩) =
            φH (QuotientGroup.mk' (H0.subgroupOf MF) h) := by
        have hφH' := hφH
        rw [hφWw] at hφH'
        simpa using hφH'
      have hquot_eq :
          QuotientGroup.mk' (H0.subgroupOf MF)
              ⟨(w : G)⁻¹ * (h : G) * (w : G), hconjMF h⟩ =
            QuotientGroup.mk' (H0.subgroupOf MF) h :=
        φH.injective hφH_same
      have hsmul_eq :
          (w⁻¹ : W1) • h =
            ⟨(w : G)⁻¹ * (h : G) * (w : G), hconjMF h⟩ := by
        apply Subtype.ext
        simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
      change QuotientGroup.mk' (H0.subgroupOf MF) ((w⁻¹ : W1) • h) =
        QuotientGroup.mk' (H0.subgroupOf MF) h
      rw [hsmul_eq]
      exact hquot_eq
    have hzp_top : Subgroup.zpowers (w⁻¹ : W1) = ⊤ :=
      zpowers_eq_top_of_prime_card_of_ne_one hW1prime hwinv_ne
    have hfixed_top : fixedPointSubgroup W1 (MF ⧸ H0.subgroupOf MF) = ⊤ := by
      apply eq_top_iff.mpr
      intro x _hx
      change ∀ v : W1, v • x = x
      intro v
      have hv_mem : v ∈ Subgroup.zpowers (w⁻¹ : W1) := by
        rw [hzp_top]
        exact Subgroup.mem_top v
      exact smul_eq_self_of_mem_zpowers hv_mem (hfix_gen x)
    exact hfixed_ne_top hfixed_top
  exact ⟨F, fieldInst, fintypeInst, Ustar, hspan, φH, φU, φW, hφW_inj,
    hUaction, hWaction⟩

private theorem theorem_9_7_schur_field_model_raw_from_elementary_irreducible_hom_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
          quotientChiefFactorData_9_6 M MF H0 W1 hp) →
          quotientCentralizerIn MF H0 U C →
            quotientBarUCardinality U C u →
              (hpprime : Nat.Prime p) →
                (hqprime : Nat.Prime q) →
                    (hnormalH0 : (H0.subgroupOf MF).Normal) →
                      (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G)) →
                        (hH0invU :
                          letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                          IsInvariant U MF (H0.subgroupOf MF)) →
                      (hbarElem :
                        letI : (H0.subgroupOf MF).Normal := hnormalH0
                        IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF)) →
                        (hbarCard :
                          letI : (H0.subgroupOf MF).Normal := hnormalH0
                          Nat.card (MF ⧸ H0.subgroupOf MF) = p ^ q) →
                          (hbarFinrank :
                            letI : Fact p.Prime := ⟨hpprime⟩
                            letI : (H0.subgroupOf MF).Normal := hnormalH0
                            letI : IsElementaryAbelian p
                                (MF ⧸ H0.subgroupOf MF) := hbarElem
                            Module.finrank (ZMod p)
                              (Additive (MF ⧸ H0.subgroupOf MF)) = q) →
                          (hirredRep :
                            letI : Fact p.Prime := ⟨hpprime⟩
                            letI : (H0.subgroupOf MF).Normal := hnormalH0
                            letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                            letI : IsElementaryAbelian p
                                (MF ⧸ H0.subgroupOf MF) := hbarElem
                            letI : MulDistribMulAction U
                                (MF ⧸ H0.subgroupOf MF) :=
                              quotientMulDistribMulAction (A := U) (G := MF)
                                (H0.subgroupOf MF) hH0invU
                            Representation.IsIrreducible
                              (Theory.Representation.ofElementaryAbelianAction (A := U)
                                (G := MF ⧸ H0.subgroupOf MF) (p := p))) →
                          theorem_9_7_schurEndFieldData_sec9 MF H0 U p
                            hpprime hnormalH0 hUnormMF hH0invU hbarElem →
                          (letI : Fact p.Prime := ⟨hpprime⟩
                          letI : (H0.subgroupOf MF).Normal := hnormalH0
                          letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                          letI : IsElementaryAbelian p
                              (MF ⧸ H0.subgroupOf MF) := hbarElem
                          letI : MulDistribMulAction U
                              (MF ⧸ H0.subgroupOf MF) :=
                            quotientMulDistribMulAction (A := U) (G := MF)
                              (H0.subgroupOf MF) hH0invU
                          let ρ := Theory.Representation.ofElementaryAbelianAction (A := U)
                            (G := MF ⧸ H0.subgroupOf MF) (p := p)
                          let E := Module.End (MonoidAlgebra (ZMod p) U) ρ.asModule
                          (Nat.card E = p ∧ Module.finrank E ρ.asModule = q) ∨
                            (Nat.card E = p ^ q ∧
                              Module.finrank E ρ.asModule = 1)) →
                          (hnormalC : (C.subgroupOf U).Normal) →
                            (letI : (C.subgroupOf U).Normal := hnormalC
                            IsMulCommutative (U ⧸ C.subgroupOf U)) →
                            (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G)) →
                              (hCinv :
                                letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
                                IsInvariant W1 U (C.subgroupOf U)) →
                                theorem_9_7_schurFieldHomRawData_sec9
                                  MF H0 U C W1 hnormalH0 hnormalC hW1normU hCinv := by
  intro h92 hp96 hC hBarU hpprime hqprime hnormalH0 hUnormMF hH0invU
    hbarElem hbarCard hbarFinrank hirredRep hEndField hEndFieldCardAlt hnormalC
    hbarUcomm hW1normU hCinv
  classical
  rcases theorem_9_7_schur_field_model_compatibility_raw_from_elementary_irreducible_hom_source_bridge_sec9
      M MF U W1 W2 H0 C p q u h92 hp96 hC hBarU hpprime hqprime
      hnormalH0 hUnormMF hH0invU hbarElem hbarCard hbarFinrank hirredRep
      hEndField hEndFieldCardAlt hnormalC hbarUcomm hW1normU hCinv with
    ⟨F, fieldInst, fintypeInst, Ustar, hspan, φH, φU, φW, hφW_inj,
      hUaction, hWaction⟩
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  letI : (C.subgroupOf U).Normal := hnormalC
  letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
  letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
    quotientMulDistribMulAction (A := W1) (G := U) (C.subgroupOf U) hCinv
  exact ⟨F, fieldInst, fintypeInst, Ustar, hspan, φH, φU, φW, hφW_inj,
    hUaction, fun w h => by
      rcases hWaction w h with ⟨hconjMF, hφH, hcompat⟩
      refine ⟨hconjMF, hφH, fun x => ?_⟩
      have hcompatx :
          Units.map (φW w).toMonoidHom (φU x : Ustar) =
            (φU ((w⁻¹ : W1) • x) : Ustar) :=
        hcompat x
      refine ⟨(φU x).property, ?_, hcompatx⟩
      rw [hcompatx]
      exact (φU ((w⁻¹ : W1) • x)).property⟩

private theorem theorem_9_7_schur_field_model_from_elementary_irreducible_hom_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
          quotientChiefFactorData_9_6 M MF H0 W1 hp) →
          quotientCentralizerIn MF H0 U C →
            quotientBarUCardinality U C u →
              (hpprime : Nat.Prime p) →
                (hqprime : Nat.Prime q) →
                    (hnormalH0 : (H0.subgroupOf MF).Normal) →
                      (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G)) →
                        (hH0invU :
                          letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                          IsInvariant U MF (H0.subgroupOf MF)) →
                      (hbarElem :
                        letI : (H0.subgroupOf MF).Normal := hnormalH0
                        IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF)) →
                        (hbarCard :
                          letI : (H0.subgroupOf MF).Normal := hnormalH0
                          Nat.card (MF ⧸ H0.subgroupOf MF) = p ^ q) →
                          (hbarFinrank :
                            letI : Fact p.Prime := ⟨hpprime⟩
                            letI : (H0.subgroupOf MF).Normal := hnormalH0
                            letI : IsElementaryAbelian p
                                (MF ⧸ H0.subgroupOf MF) := hbarElem
                            Module.finrank (ZMod p)
                              (Additive (MF ⧸ H0.subgroupOf MF)) = q) →
                          (hirredRep :
                            letI : Fact p.Prime := ⟨hpprime⟩
                            letI : (H0.subgroupOf MF).Normal := hnormalH0
                            letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                            letI : IsElementaryAbelian p
                                (MF ⧸ H0.subgroupOf MF) := hbarElem
                            letI : MulDistribMulAction U
                                (MF ⧸ H0.subgroupOf MF) :=
                              quotientMulDistribMulAction (A := U) (G := MF)
                                (H0.subgroupOf MF) hH0invU
                            Representation.IsIrreducible
                              (Theory.Representation.ofElementaryAbelianAction (A := U)
                                (G := MF ⧸ H0.subgroupOf MF) (p := p))) →
                          theorem_9_7_schurEndFieldData_sec9 MF H0 U p
                            hpprime hnormalH0 hUnormMF hH0invU hbarElem →
                          (letI : Fact p.Prime := ⟨hpprime⟩
                          letI : (H0.subgroupOf MF).Normal := hnormalH0
                          letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                          letI : IsElementaryAbelian p
                              (MF ⧸ H0.subgroupOf MF) := hbarElem
                          letI : MulDistribMulAction U
                              (MF ⧸ H0.subgroupOf MF) :=
                            quotientMulDistribMulAction (A := U) (G := MF)
                              (H0.subgroupOf MF) hH0invU
                          let ρ := Theory.Representation.ofElementaryAbelianAction (A := U)
                            (G := MF ⧸ H0.subgroupOf MF) (p := p)
                          let E := Module.End (MonoidAlgebra (ZMod p) U) ρ.asModule
                          (Nat.card E = p ∧ Module.finrank E ρ.asModule = q) ∨
                            (Nat.card E = p ^ q ∧
                              Module.finrank E ρ.asModule = 1)) →
                          (hnormalC : (C.subgroupOf U).Normal) →
                            (letI : (C.subgroupOf U).Normal := hnormalC
                            IsMulCommutative (U ⧸ C.subgroupOf U)) →
                            (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G)) →
                              (hCinv :
                                letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
                                IsInvariant W1 U (C.subgroupOf U)) →
                                letI : (H0.subgroupOf MF).Normal := hnormalH0
                                letI : (C.subgroupOf U).Normal := hnormalC
                                letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
                                letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
                                  quotientMulDistribMulAction (A := W1) (G := U)
                                    (C.subgroupOf U) hCinv
                                ∃ F : Type u, ∃ fieldInst : Field F,
                                  ∃ fintypeInst : Fintype F,
                                  letI : Field F := fieldInst
                                  letI : Fintype F := fintypeInst
                                  ∃ Ustar : Subgroup Fˣ,
                                      Nat.card F = p ^ q ∧
                                      Nat.card Ustar = u ∧
                                      IsCyclic Ustar ∧
                                      AddSubgroup.closure
                                        (((fun x : Ustar => ((x : Fˣ) : F)) ''
                                          Set.univ) : Set F) = ⊤ ∧
                                      ∃ φH : (MF ⧸ H0.subgroupOf MF) ≃* Multiplicative F,
                                        ∃ φU : (U ⧸ C.subgroupOf U) ≃* Ustar,
                                          ∃ φW : W1 →* RingAut F,
                                            Function.Injective φW ∧
                                            (∀ x : U ⧸ C.subgroupOf U, ∀ h : MF,
                                              ∃ hconjMF : ∀ y : MF,
                                                (x.out : U)⁻¹ * (y : G) *
                                                    (x.out : U) ∈ MF,
                                                φH (QuotientGroup.mk' (H0.subgroupOf MF)
                                                  ⟨(x.out : U)⁻¹ * (h : G) *
                                                    (x.out : U), hconjMF h⟩) =
                                                  Multiplicative.ofAdd
                                                    (((φU x : Ustar) : Fˣ) *
                                                      Multiplicative.toAdd
                                                        (φH (QuotientGroup.mk'
                                                          (H0.subgroupOf MF) h)))) ∧
                                              ∀ w : W1, ∀ h : MF,
                                                ∃ hconjMF : ∀ y : MF,
                                                  (w : G)⁻¹ * (y : G) * (w : G) ∈ MF,
                                                  φH (QuotientGroup.mk' (H0.subgroupOf MF)
                                                    ⟨(w : G)⁻¹ * (h : G) * (w : G),
                                                      hconjMF h⟩) =
                                                    Multiplicative.ofAdd
                                                      ((φW w) (Multiplicative.toAdd
                                                        (φH (QuotientGroup.mk'
                                                          (H0.subgroupOf MF) h)))) ∧
                                                ∀ x : U ⧸ C.subgroupOf U,
                                                  ((φU x : Ustar) : Fˣ) ∈ Ustar ∧
                                                    Units.map (φW w).toMonoidHom
                                                      (φU x : Ustar) ∈ Ustar ∧
                                                      Units.map (φW w).toMonoidHom
                                                        (φU x : Ustar) =
                                                        (φU ((w⁻¹ : W1) • x) : Ustar) := by
  intro h92 hp96 hC hBarU hpprime hqprime hnormalH0 hUnormMF hH0invU
    hbarElem hbarCard hbarFinrank hirredRep hEndField hEndFieldCardAlt hnormalC
    hbarUcomm hW1normU hCinv
  classical
  rcases theorem_9_7_schur_field_model_raw_from_elementary_irreducible_hom_source_bridge_sec9
      M MF U W1 W2 H0 C p q u h92 hp96 hC hBarU hpprime hqprime
      hnormalH0 hUnormMF hH0invU hbarElem hbarCard hbarFinrank hirredRep
      hEndField hEndFieldCardAlt hnormalC hbarUcomm hW1normU hCinv with
    ⟨F, fieldInst, fintypeInst, Ustar, hspan, φH, φU, φW, hφW_inj,
      hUaction, hWaction⟩
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  letI : (C.subgroupOf U).Normal := hnormalC
  letI : Field F := fieldInst
  letI : Fintype F := fintypeInst
  have hFcard : Nat.card F = p ^ q := by
    have hbarCard' : Nat.card (MF ⧸ H0.subgroupOf MF) = p ^ q := by
      simpa using hbarCard
    have hFmult : Nat.card F = Nat.card (Multiplicative F) :=
      Nat.card_congr
        { toFun := Multiplicative.ofAdd
          invFun := Multiplicative.toAdd
          left_inv := by intro x; rfl
          right_inv := by intro x; rfl }
    exact hFmult.trans ((Nat.card_congr φH.toEquiv).symm.trans hbarCard')
  have hUstarCard : Nat.card Ustar = u := by
    have hBarCard : Nat.card (U ⧸ C.subgroupOf U) = u := by
      rcases hBarU with ⟨_hCU, _hnormalC, hcard⟩
      simpa using hcard
    exact (Nat.card_congr φU.toEquiv).symm.trans hBarCard
  have hUstarCyc : IsCyclic Ustar :=
    isCyclic_subgroup_units Ustar
  exact ⟨F, fieldInst, fintypeInst, Ustar, hFcard, hUstarCard, hUstarCyc,
    hspan, φH, φU, φW, hφW_inj, hUaction, hWaction⟩

private theorem theorem_9_7_schur_field_model_from_elementary_irreducible_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
          quotientChiefFactorData_9_6 M MF H0 W1 hp) →
          quotientCentralizerIn MF H0 U C →
            quotientBarUCardinality U C u →
              (hpprime : Nat.Prime p) →
                (hqprime : Nat.Prime q) →
                    (hnormalH0 : (H0.subgroupOf MF).Normal) →
                      (hUnormMF : U ≤ Subgroup.normalizer (MF : Set G)) →
                        (hH0invU :
                          letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                          IsInvariant U MF (H0.subgroupOf MF)) →
                      (hbarElem :
                        letI : (H0.subgroupOf MF).Normal := hnormalH0
                        IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF)) →
                        (hbarCard :
                          letI : (H0.subgroupOf MF).Normal := hnormalH0
                          Nat.card (MF ⧸ H0.subgroupOf MF) = p ^ q) →
                          (hbarFinrank :
                            letI : Fact p.Prime := ⟨hpprime⟩
                            letI : (H0.subgroupOf MF).Normal := hnormalH0
                            letI : IsElementaryAbelian p
                                (MF ⧸ H0.subgroupOf MF) := hbarElem
                            Module.finrank (ZMod p)
                              (Additive (MF ⧸ H0.subgroupOf MF)) = q) →
                          (hirredRep :
                            letI : Fact p.Prime := ⟨hpprime⟩
                            letI : (H0.subgroupOf MF).Normal := hnormalH0
                            letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                            letI : IsElementaryAbelian p
                                (MF ⧸ H0.subgroupOf MF) := hbarElem
                            letI : MulDistribMulAction U
                                (MF ⧸ H0.subgroupOf MF) :=
                              quotientMulDistribMulAction (A := U) (G := MF)
                                (H0.subgroupOf MF) hH0invU
                            Representation.IsIrreducible
                              (Theory.Representation.ofElementaryAbelianAction (A := U)
                                (G := MF ⧸ H0.subgroupOf MF) (p := p))) →
                          theorem_9_7_schurEndFieldData_sec9 MF H0 U p
                            hpprime hnormalH0 hUnormMF hH0invU hbarElem →
                          (letI : Fact p.Prime := ⟨hpprime⟩
                          letI : (H0.subgroupOf MF).Normal := hnormalH0
                          letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
                          letI : IsElementaryAbelian p
                              (MF ⧸ H0.subgroupOf MF) := hbarElem
                          letI : MulDistribMulAction U
                              (MF ⧸ H0.subgroupOf MF) :=
                            quotientMulDistribMulAction (A := U) (G := MF)
                              (H0.subgroupOf MF) hH0invU
                          let ρ := Theory.Representation.ofElementaryAbelianAction (A := U)
                            (G := MF ⧸ H0.subgroupOf MF) (p := p)
                          let E := Module.End (MonoidAlgebra (ZMod p) U) ρ.asModule
                          (Nat.card E = p ∧ Module.finrank E ρ.asModule = q) ∨
                            (Nat.card E = p ^ q ∧
                              Module.finrank E ρ.asModule = 1)) →
                          (hnormalC : (C.subgroupOf U).Normal) →
                            (letI : (C.subgroupOf U).Normal := hnormalC
                            IsMulCommutative (U ⧸ C.subgroupOf U)) →
                            (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G)) →
                              (hCinv :
                                letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
                                IsInvariant W1 U (C.subgroupOf U)) →
                                letI : (H0.subgroupOf MF).Normal := hnormalH0
                                letI : (C.subgroupOf U).Normal := hnormalC
                                letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
                                letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
                                  quotientMulDistribMulAction (A := W1) (G := U)
                                    (C.subgroupOf U) hCinv
                                ∃ F : Type u, ∃ fieldInst : Field F,
                                  ∃ fintypeInst : Fintype F,
                                  letI : Field F := fieldInst
                                  letI : Fintype F := fintypeInst
                                  ∃ Ustar : Subgroup Fˣ,
                                      Nat.card F = p ^ q ∧
                                      Nat.card Ustar = u ∧
                                      IsCyclic Ustar ∧
                                      AddSubgroup.closure
                                        (((fun x : Ustar => ((x : Fˣ) : F)) ''
                                          Set.univ) : Set F) = ⊤ ∧
                                      ∃ φH : (MF ⧸ H0.subgroupOf MF) ≃* Multiplicative F,
                                        ∃ φU : (U ⧸ C.subgroupOf U) ≃* Ustar,
                                          ∃ φW : W1 ≃* RingAut F,
                                            (∀ x : U ⧸ C.subgroupOf U, ∀ h : MF,
                                              ∃ hconjMF : ∀ y : MF,
                                                (x.out : U)⁻¹ * (y : G) *
                                                    (x.out : U) ∈ MF,
                                                φH (QuotientGroup.mk' (H0.subgroupOf MF)
                                                  ⟨(x.out : U)⁻¹ * (h : G) *
                                                    (x.out : U), hconjMF h⟩) =
                                                  Multiplicative.ofAdd
                                                    (((φU x : Ustar) : Fˣ) *
                                                      Multiplicative.toAdd
                                                        (φH (QuotientGroup.mk'
                                                          (H0.subgroupOf MF) h)))) ∧
                                              ∀ w : W1, ∀ h : MF,
                                                ∃ hconjMF : ∀ y : MF,
                                                  (w : G)⁻¹ * (y : G) * (w : G) ∈ MF,
                                                  φH (QuotientGroup.mk' (H0.subgroupOf MF)
                                                    ⟨(w : G)⁻¹ * (h : G) * (w : G),
                                                      hconjMF h⟩) =
                                                    Multiplicative.ofAdd
                                                      ((φW w) (Multiplicative.toAdd
                                                        (φH (QuotientGroup.mk'
                                                          (H0.subgroupOf MF) h)))) ∧
                                                ∀ x : U ⧸ C.subgroupOf U,
                                                  ((φU x : Ustar) : Fˣ) ∈ Ustar ∧
                                                    Units.map (φW w).toMonoidHom
                                                      (φU x : Ustar) ∈ Ustar ∧
                                                    Units.map (φW w).toMonoidHom
                                                      (φU x : Ustar) =
                                                      (φU ((w⁻¹ : W1) • x) : Ustar) := by
  intro h92 hp96 hC hBarU hpprime hqprime hnormalH0 hUnormMF hH0invU
    hbarElem hbarCard hbarFinrank hirredRep hEndField hEndFieldCardAlt hnormalC
    hbarUcomm hW1normU hCinv
  classical
  rcases theorem_9_7_schur_field_model_from_elementary_irreducible_hom_source_bridge_sec9
      M MF U W1 W2 H0 C p q u h92 hp96 hC hBarU hpprime hqprime
      hnormalH0 hUnormMF hH0invU hbarElem hbarCard hbarFinrank hirredRep
      hEndField hEndFieldCardAlt hnormalC hbarUcomm hW1normU hCinv with
    ⟨F, fieldInst, fintypeInst, Ustar, hFcard, hUstarCard, hUstarCyc, hspan,
      φH, φU, φW, hφW_inj, hUaction, hWaction⟩
  letI : Field F := fieldInst
  letI : Fintype F := fintypeInst
  have hW1card : Nat.card W1 = q := by
    exact h92.q_eq
  have hRingAutCard : Nat.card (RingAut F) = q :=
    theorem_9_7_ringAut_card_eq_q_of_finite_field_card_sec9 F hpprime hFcard
  have hcard : Nat.card W1 = Nat.card (RingAut F) :=
    hW1card.trans hRingAutCard.symm
  haveI : Finite (RingAut F) := by
    haveI : Fact p.Prime := ⟨hpprime⟩
    have hcardFintype : Fintype.card F = p ^ q := by
      simpa [Nat.card_eq_fintype_card] using hFcard
    haveI : CharP F p := charP_of_card_eq_prime_pow hcardFintype
    letI : Algebra (ZMod p) F := ZMod.algebra F p
    exact Finite.of_equiv (F ≃ₐ[ZMod p] F)
      (theorem_9_7_ringAutEquivAlgEquivZMod_sec9 F p).symm
  let φWequiv : W1 ≃* RingAut F :=
    theorem_9_7_mulEquivOfInjectiveHomCardEq_sec9 φW hφW_inj hcard
  refine ⟨F, fieldInst, fintypeInst, Ustar, hFcard, hUstarCard, hUstarCyc,
    hspan, φH, φU, φWequiv, ?_⟩
  constructor
  · exact hUaction
  · intro w h
    rcases hWaction w h with ⟨hconjMF, hφH, hcompat⟩
    refine ⟨hconjMF, ?_, ?_⟩
    · simpa [φWequiv, theorem_9_7_mulEquivOfInjectiveHomCardEq_sec9] using hφH
    · intro x
      simpa [φWequiv, theorem_9_7_mulEquivOfInjectiveHomCardEq_sec9] using hcompat x

private theorem theorem_9_7_irreducible_field_model_data_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
          quotientChiefFactorData_9_6 M MF H0 W1 hp) →
          quotientCentralizerIn MF H0 U C →
            quotientBarUCardinality U C u →
              Nat.Prime p →
                Nat.Prime q →
                  quotientIrreducibleActionData MF H0 U →
                    quotientFieldSemidirectModelData MF H0 U C W1 p q u := by
  intro h92 hp96 hC hBarU hpprime hqprime hirred
  rcases hp96 with ⟨hp, hp_eq, hpData, h96⟩
  rcases h96 with ⟨_hH0MF, _hMFM, hnormalH0, _hchief, _hWbar, _hcardRaw⟩
  rcases hBarU with ⟨_hCU, hnormalC, _hBarCard⟩
  have hW1normU : W1 ≤ Subgroup.normalizer (U : Set G) :=
    theorem_9_7_W1_le_normalizer_U_of_hypothesis_9_2_sec9 h92
  have hW1normMF : W1 ≤ Subgroup.normalizer (MF : Set G) :=
    theorem_9_7_W1_le_normalizer_MF_of_hypothesis_9_2_sec9 h92
  have hUnormMF : U ≤ Subgroup.normalizer (MF : Set G) :=
    le_sup_left.trans
      (theorem_9_3_action_normalizes_and_solvable_sec9 M MF U W1 W2 q h92).1
  letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
  have hCinv : IsInvariant W1 U (C.subgroupOf U) :=
    theorem_9_7_quotientCentralizerIn_isInvariant_W1_sec9 h92 hpData hC
      hW1normU hW1normMF
  have hpDataFull : hoReductionData M MF U W2 H0 hp := hpData
  rcases hpData with
    ⟨_hH0MF_hp, _hMFM_hp, _hH0normalM_hp, _hH0normalMF_hp, _hH0lt_hp,
      hbarElemRaw, _htypeIIIIVData_hp⟩
  rcases hbarElemRaw with ⟨hnormalElem, hbarElemRaw⟩
  have hbarElem :
      (letI : (H0.subgroupOf MF).Normal := hnormalH0;
        IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF)) := by
    letI : (H0.subgroupOf MF).Normal := hnormalH0
    simpa [hp_eq] using hbarElemRaw
  have hbarCard :
      (letI : (H0.subgroupOf MF).Normal := hnormalH0;
        Nat.card (MF ⧸ H0.subgroupOf MF) = p ^ q) := by
    letI : (H0.subgroupOf MF).Normal := hnormalH0
    simpa using
      theorem_9_7_quotient_cardinality_from_chief_data_sec9 h92 hp_eq
        ⟨_hH0MF, _hMFM, hnormalH0, _hchief, _hWbar, _hcardRaw⟩
  have hbarFinrank :
      (letI : Fact p.Prime := ⟨hpprime⟩
      letI : (H0.subgroupOf MF).Normal := hnormalH0
      letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
      Module.finrank (ZMod p) (Additive (MF ⧸ H0.subgroupOf MF)) = q) :=
    theorem_9_7_quotient_finrank_eq_q_sec9 hpprime hnormalH0 hbarElem hbarCard
  letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
  have hUleM : U ≤ M := by
    rcases h92.typePDefinitionData with
      ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, hUleD,
        _hUnil, _hW1normU, _hcompDU, _hMFnotcyc, _hsecond, _hfitEq,
        _hfitLeD, _hW2le, _hW2cyc, _hW2ne, _hcentW1, _hnormX⟩
    exact hUleD.trans section12_ambientDerivedSubgroup_le
  have hH0invU : IsInvariant U MF (H0.subgroupOf MF) :=
    subgroupOf_MF_isInvariant_of_subgroupOf_M_normal_sec9 M MF U H0
      _hMFM hUleM _hH0normalM_hp hUnormMF
  haveI : Fact p.Prime := ⟨hpprime⟩
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  have hbarElemInst : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
  letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElemInst
  have hbarCardOneLt : 1 < Nat.card (MF ⧸ H0.subgroupOf MF) := by
    rw [hbarCard]
    exact one_lt_pow₀ hpprime.one_lt hqprime.ne_zero
  haveI : Nontrivial (MF ⧸ H0.subgroupOf MF) :=
    Finite.one_lt_card_iff_nontrivial.mp hbarCardOneLt
  have hirredRep :
      Representation.IsIrreducible
        (Theory.Representation.ofElementaryAbelianAction (A := U)
          (G := MF ⧸ H0.subgroupOf MF) (p := p)) := by
    exact
      theorem_9_7_irreducible_representation_of_quotientIrreducible_sec9
        hnormalH0 hUnormMF hH0invU hbarElem hirred
  have hEndField :
      theorem_9_7_schurEndFieldData_sec9 MF H0 U p
        hpprime hnormalH0 hUnormMF hH0invU hbarElem :=
    theorem_9_7_schurEndFieldData_of_irreducible_sec9
      hnormalH0 hUnormMF hH0invU hbarElem hirredRep
  have hEndFieldCardAlt :
      (letI : Fact p.Prime := ⟨hpprime⟩
      letI : (H0.subgroupOf MF).Normal := hnormalH0
      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
      letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
      letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
        quotientMulDistribMulAction (A := U) (G := MF)
          (H0.subgroupOf MF) hH0invU
      let ρ := Theory.Representation.ofElementaryAbelianAction (A := U)
        (G := MF ⧸ H0.subgroupOf MF) (p := p)
      let E := Module.End (MonoidAlgebra (ZMod p) U) ρ.asModule
      Nat.card E = p ∨ Nat.card E = p ^ q) :=
    theorem_9_7_schurEndField_card_eq_prime_or_full_sec9 hpprime hqprime
      hnormalH0 hUnormMF hH0invU hbarElem hbarCard hEndField
  have hEndFieldDimAlt :
      (letI : Fact p.Prime := ⟨hpprime⟩
      letI : (H0.subgroupOf MF).Normal := hnormalH0
      letI : Subgroup.Normalizes U MF := ⟨hUnormMF⟩
      letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hbarElem
      letI : MulDistribMulAction U (MF ⧸ H0.subgroupOf MF) :=
        quotientMulDistribMulAction (A := U) (G := MF)
          (H0.subgroupOf MF) hH0invU
      let ρ := Theory.Representation.ofElementaryAbelianAction (A := U)
        (G := MF ⧸ H0.subgroupOf MF) (p := p)
      let E := Module.End (MonoidAlgebra (ZMod p) U) ρ.asModule
      (Nat.card E = p ∧ Module.finrank E ρ.asModule = q) ∨
      (Nat.card E = p ^ q ∧ Module.finrank E ρ.asModule = 1)) :=
    theorem_9_7_schurEndField_card_finrank_alternative_sec9 hpprime hqprime
      hnormalH0 hUnormMF hH0invU hbarElem hbarCard hEndField hEndFieldCardAlt
  have hbarUcomm :
      (letI : (C.subgroupOf U).Normal := hnormalC
      IsMulCommutative (U ⧸ C.subgroupOf U)) :=
    theorem_9_7_barU_isMulCommutative_sec9 h92 hC hnormalC
  have htail :=
    theorem_9_7_schur_field_model_from_elementary_irreducible_source_bridge_sec9
      M MF U W1 W2 H0 C p q u h92
      ⟨hp, hp_eq, hpDataFull,
        ⟨_hH0MF, _hMFM, hnormalH0, _hchief, _hWbar, _hcardRaw⟩⟩
      hC ⟨_hCU, hnormalC, _hBarCard⟩ hpprime hqprime hnormalH0
      hUnormMF hH0invU hbarElem hbarCard hbarFinrank hirredRep hEndField
      hEndFieldDimAlt hnormalC hbarUcomm hW1normU hCinv
  exact ⟨hnormalH0, hnormalC, hW1normU, hCinv, htail⟩

private theorem theorem_9_7_irreducible_field_model_and_prime_exclusion_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
          quotientChiefFactorData_9_6 M MF H0 W1 hp) →
                    quotientCentralizerIn MF H0 U C →
                      quotientBarUCardinality U C u →
                        Nat.Prime p →
                          Nat.Prime q →
                            quotientIrreducibleActionData MF H0 U →
                              quotientFieldSemidirectModelData MF H0 U C W1 p q u ∧
                                ∀ hnormal : (C.subgroupOf U).Normal,
                                  letI : (C.subgroupOf U).Normal := hnormal
                                  ∀ x : U ⧸ C.subgroupOf U, orderOf x ∣ p - 1 → x = 1 := by
  classical
  intro h92 hp96 hC hBarU hpprime hqprime hirred
  have hfield :
      quotientFieldSemidirectModelData MF H0 U C W1 p q u :=
    theorem_9_7_irreducible_field_model_data_source_bridge_sec9
      M MF U W1 W2 H0 C p q u h92 hp96 hC hBarU hpprime hqprime hirred
  refine ⟨hfield, ?_⟩
  intro hnormal
  letI : (C.subgroupOf U).Normal := hnormal
  intro x hxorder
  rcases hfield with
    ⟨_hnH0, _hnC, hW1normU, hCinv, F, fieldInst, fintypeInst, Ustar,
      hFcard, _hUstarCard, _hUstarCyc, _hspan, _φH, φU, φW, _hactU,
      hactW⟩
  letI : Field F := fieldInst
  letI : Fintype F := fintypeInst
  letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
  letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
    quotientMulDistribMulAction (A := W1) (G := U) (C.subgroupOf U) hCinv
  have hfixBot : fixedPointSubgroup W1 (U ⧸ C.subgroupOf U) = ⊥ :=
    theorem_9_7_fixedPointSubgroup_W1_barU_eq_bot_of_isInvariant_sec9
      h92 hnormal hW1normU hCinv
  have hunitOrder : orderOf (((φU x : Ustar) : Fˣ)) ∣ p - 1 := by
    rwa [Subgroup.orderOf_coe, MulEquiv.orderOf_eq φU x]
  have hunitFixed :
      ∀ w : W1,
        Units.map (φW w).toMonoidHom (((φU x : Ustar) : Fˣ)) =
          (((φU x : Ustar) : Fˣ)) :=
    fun w =>
      theorem_9_7_finite_field_unit_fixed_of_order_dvd_prime_pred_sec9
        hpprime hFcard (((φU x : Ustar) : Fˣ)) hunitOrder (φW w)
  have hxFixedByInv : ∀ w : W1, (w⁻¹ : W1) • x = x := by
    intro w
    rcases hactW w (1 : MF) with ⟨_hconjMF, _hact, hUstarCompat⟩
    have hcompat :
        Units.map (φW w).toMonoidHom (φU x : Ustar) =
          (φU ((w⁻¹ : W1) • x) : Ustar) :=
      (hUstarCompat x).2.2
    apply φU.injective
    apply Subtype.ext
    calc
      ((φU ((w⁻¹ : W1) • x) : Ustar) : Fˣ) =
          Units.map (φW w).toMonoidHom (φU x : Ustar) := hcompat.symm
      _ = ((φU x : Ustar) : Fˣ) := hunitFixed w
  have hxFixed : x ∈ fixedPointSubgroup W1 (U ⧸ C.subgroupOf U) := by
    intro w
    simpa using hxFixedByInv w⁻¹
  have hxBot : x ∈ (⊥ : Subgroup (U ⧸ C.subgroupOf U)) := by
    rw [← hfixBot]
    exact hxFixed
  simpa using hxBot

private theorem theorem_9_7_irreducible_barU_prime_order_pred_exclusion_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
          quotientChiefFactorData_9_6 M MF H0 W1 hp) →
          quotientCentralizerIn MF H0 U C →
            quotientBarUCardinality U C u →
              Nat.Prime p →
                Nat.Prime q →
                  quotientIrreducibleActionData MF H0 U →
                    quotientFieldSemidirectModelData MF H0 U C W1 p q u →
                      ∀ hnormal : (C.subgroupOf U).Normal,
                        letI : (C.subgroupOf U).Normal := hnormal
                        ∀ x : U ⧸ C.subgroupOf U, orderOf x ∣ p - 1 → x = 1 := by
  intro h92 hp96 hC hBarU hpprime hqprime hirred _hfield hnormal x hx
  exact
    (theorem_9_7_irreducible_field_model_and_prime_exclusion_source_bridge_sec9
      M MF U W1 W2 H0 C p q u h92 hp96 hC hBarU hpprime hqprime hirred).2
      hnormal x hx

private theorem theorem_9_7_irreducible_barU_prime_field_disjoint_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
          quotientChiefFactorData_9_6 M MF H0 W1 hp) →
          quotientCentralizerIn MF H0 U C →
            quotientBarUCardinality U C u →
              Nat.Prime p →
                Nat.Prime q →
                  quotientIrreducibleActionData MF H0 U →
                    quotientFieldSemidirectModelData MF H0 U C W1 p q u →
                      ∀ r : ℕ, Nat.Prime r → r ∣ u → r ∣ p - 1 → False := by
  intro h92 hp96 hC hBarU hpprime hqprime hirred hfield r hr hru hrp
  rcases hBarU with ⟨_hCU, hnormalC, hcardBarU⟩
  letI : (C.subgroupOf U).Normal := hnormalC
  haveI : Fact (Nat.Prime r) := ⟨hr⟩
  have hru_bar : r ∣ Nat.card (U ⧸ C.subgroupOf U) := by
    simpa [hcardBarU] using hru
  rcases exists_prime_orderOf_dvd_card' (G := U ⧸ C.subgroupOf U) r hru_bar with
    ⟨x, hxorder⟩
  have hxone : x = 1 :=
    theorem_9_7_irreducible_barU_prime_order_pred_exclusion_source_bridge_sec9
      M MF U W1 W2 H0 C p q u h92 hp96 hC
      ⟨hC.1, hnormalC, hcardBarU⟩ hpprime hqprime hirred hfield hnormalC x
      (by simpa [hxorder] using hrp)
  have hr_eq_one : r = 1 := by
    rw [← hxorder]
    simp [hxone]
  exact hr.ne_one hr_eq_one

private theorem theorem_9_7_irreducible_barU_common_divisors_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
          quotientChiefFactorData_9_6 M MF H0 W1 hp) →
          quotientCentralizerIn MF H0 U C →
            quotientBarUCardinality U C u →
              Nat.Prime p →
                Nat.Prime q →
                  quotientIrreducibleActionData MF H0 U →
                    quotientFieldSemidirectModelData MF H0 U C W1 p q u →
                      ∀ d : ℕ, d ∣ u → d ∣ p - 1 → d = 1 := by
  intro h92 hp96 hC hBarU hpprime hqprime hirred hfield
  exact theorem_9_7_common_divisors_eq_one_of_no_common_prime_sec9
    (theorem_9_7_irreducible_barU_prime_field_disjoint_source_bridge_sec9
      M MF U W1 W2 H0 C p q u h92 hp96 hC hBarU hpprime hqprime hirred hfield)

private theorem theorem_9_7_irreducible_field_model_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
          quotientChiefFactorData_9_6 M MF H0 W1 hp) →
          quotientCentralizerIn MF H0 U C →
            quotientBarUCardinality U C u →
              Nat.Prime p →
                Nat.Prime q →
                  quotientIrreducibleActionData MF H0 U →
                    quotientFieldSemidirectModelData MF H0 U C W1 p q u ∧
                      Nat.Coprime u (p - 1) := by
  intro h92 hp96 hC hBarU hpprime hqprime hirred
  have hfield :=
    theorem_9_7_irreducible_field_model_data_source_bridge_sec9
      M MF U W1 W2 H0 C p q u h92 hp96 hC hBarU hpprime hqprime hirred
  have hcommon :=
    theorem_9_7_irreducible_barU_common_divisors_source_bridge_sec9
      M MF U W1 W2 H0 C p q u h92 hp96 hC hBarU hpprime hqprime hirred hfield
  exact ⟨hfield, theorem_9_7_coprime_of_common_divisors_eq_one_sec9 hcommon⟩

public theorem theorem_9_7_case_a_barU_card_dvd_p_minus_one_pow_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a u : ℕ) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        u ∣ (p - 1) ^ (q - 1) := by
  intro hcase hBarU
  rcases hcase with
    ⟨_h92, _hH0MF, _hC, _hpprime, _hqprime, _hpData, _hdecomp,
      _hcard, hadiv, hinj⟩
  rcases hinj with ⟨_hCU, hnormal, φ, hφinj⟩
  letI : (C.subgroupOf U).Normal := hnormal
  rcases hBarU with ⟨_hCUbar, _hnormalBar, hcardUbar⟩
  have hbar_card : Nat.card (U ⧸ C.subgroupOf U) = u := by
    simpa using hcardUbar
  have htarget_card : Nat.card (Fin (q - 1) → Multiplicative (ZMod a)) =
      a ^ (q - 1) := by
    rw [Nat.card_fun, Nat.card_fin]
    rw [Nat.card_congr
      (Multiplicative.toAdd : Multiplicative (ZMod a) ≃ ZMod a), Nat.card_zmod]
  have hrange_card : Nat.card (MonoidHom.range φ) = u := by
    have hcongr :
        Nat.card (U ⧸ C.subgroupOf U) = Nat.card (MonoidHom.range φ) :=
      Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv
    exact hcongr ▸ hbar_card
  have hrange_dvd_target :
      Nat.card (MonoidHom.range φ) ∣
        Nat.card (Fin (q - 1) → Multiplicative (ZMod a)) :=
    Subgroup.card_subgroup_dvd_card (MonoidHom.range φ)
  have hu_dvd_a : u ∣ a ^ (q - 1) := by
    rw [← hrange_card, ← htarget_card]
    exact hrange_dvd_target
  exact dvd_trans hu_dvd_a (pow_dvd_pow_of_dvd hadiv (q - 1))

private theorem theorem_9_7_case_split_with_centralizer_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
          quotientChiefFactorData_9_6 M MF H0 W1 hp) →
          quotientCentralizerIn MF H0 U C →
            quotientBarUCardinality U C u →
              Nat.Prime p →
                Nat.Prime q →
                  (∃ a : ℕ,
                    (∃ hnormal : (H0.subgroupOf MF).Normal,
                      letI : (H0.subgroupOf MF).Normal := hnormal
                      ∃ H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF),
                        (∀ i, Nat.card (H i) = p) ∧
                          (∀ i, quotientSubgroupNormalizedBy MF H0 U (H i)) ∧
                          iSupIndep H ∧
                          iSup H = ⊤ ∧
                          (∀ i, quotientFactorActionCentralizerData MF H0 U C
                            (H i) a) ∧
                          ∃ hqpos : 0 < q,
                            ∀ i : Fin q,
                              ∃ w : W1,
                                quotientSubgroupConjugateByElement MF H0
                                  (H ⟨0, hqpos⟩) (H i) (w : G)) ∧
                      (∃ _hCU : C ≤ U,
                        ∃ hnormal : (C.subgroupOf U).Normal,
                          letI : (C.subgroupOf U).Normal := hnormal
                          ∃ φ : (U ⧸ C.subgroupOf U) →*
                            (Fin (q - 1) → Multiplicative (ZMod a)),
                            Function.Injective φ)) ∨
                (quotientIrreducibleActionData MF H0 U ∧
                    quotientFieldSemidirectModelData MF H0 U C W1 p q u ∧
                    Nat.Coprime u (p - 1)) := by
  intro h92 hp96 hC hBarU hpprime hqprime
  rcases theorem_9_7_clifford_module_dichotomy_source_bridge_sec9
      M MF U W1 W2 H0 C p q u h92 hp96 hC hBarU hpprime hqprime with
    hcaseA | hirred
  · exact Or.inl hcaseA
  · rcases theorem_9_7_irreducible_field_model_source_bridge_sec9
      M MF U W1 W2 H0 C p q u h92 hp96 hC hBarU hpprime hqprime hirred with
      ⟨hfield, hcop⟩
    exact Or.inr ⟨hirred, hfield, hcop⟩

private theorem theorem_9_7_irreducible_field_model_with_prime_field_image_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
          quotientChiefFactorData_9_6 M MF H0 W1 hp) →
          quotientCentralizerIn MF H0 U C →
            quotientBarUCardinality U C u →
              Nat.Prime p →
                Nat.Prime q →
                  quotientIrreducibleActionData MF H0 U →
                    quotientFieldSemidirectModelData MF H0 U C W1 p q u →
                      quotientFieldSemidirectModelWithPrimeFieldImageData
                        MF H0 U C W1 W2 p q u := by
  intro h92 hp96 hC hBarU hpprime hqprime hirred hfield
  -- `phi @* W2bar = <[1]>`.  The existing Lean field-model bridge kept only
  -- the semidirect-product fields, so this source endpoint is split out here.
  classical
  rcases hfield with
    ⟨hnormalH0, hnormalC, hW1normU, hCinv, F, fieldInst, fintypeInst, Ustar,
      hFcard, hUstarCard, hUstarCyc, hspan, φH, φU, φW, hUaction, hWaction⟩
  let H0MF : Subgroup MF := H0.subgroupOf MF
  letI : H0MF.Normal := hnormalH0
  letI : (C.subgroupOf U).Normal := hnormalC
  letI : Field F := fieldInst
  letI : Fintype F := fintypeInst
  haveI : Fact (Nat.Prime p) := ⟨hpprime⟩
  have hFcard_fintype : Fintype.card F = p ^ q := by
    simpa [Nat.card_eq_fintype_card] using hFcard
  haveI : CharP F p := charP_of_card_eq_prime_pow hFcard_fintype
  have hW1normMF : W1 ≤ Subgroup.normalizer (MF : Set G) :=
    theorem_9_7_W1_le_normalizer_MF_of_hypothesis_9_2_sec9 h92
  letI : Subgroup.Normalizes W1 MF := ⟨hW1normMF⟩
  have hW1leM : W1 ≤ M := by
    rcases h92.typePDefinitionData with
      ⟨_hMFsource, _hW1cyc, _hW1ne, hW1hall, _hcompMW1, _hUleD,
        _hUnil, _hW1normU, _hcompDU, _hMFnotcyc, _hsecond, _hfitEq,
        _hfitLeD, _hW2le, _hW2cyc, _hW2ne, _hcentW1, _hnormX⟩
    exact hW1hall.1
  have hMFleM : MF ≤ M := by
    rcases hp96 with ⟨_hp, _hp_eq, hpData, _h96⟩
    exact hpData.2.1
  have hH0normalM : (H0.subgroupOf M).Normal := by
    rcases hp96 with ⟨_hp, _hp_eq, hpData, _h96⟩
    exact hpData.2.2.1
  have hH0invW1 : IsInvariant W1 MF H0MF :=
    subgroupOf_MF_isInvariant_of_subgroupOf_M_normal_sec9 M MF W1 H0
      hMFleM hW1leM hH0normalM hW1normMF
  letI : MulDistribMulAction W1 (MF ⧸ H0MF) :=
    quotientMulDistribMulAction (A := W1) (G := MF) H0MF hH0invW1
  have hfixedCard :
      Nat.card (fixedPointSubgroup W1 (MF ⧸ H0MF)) = p := by
    rcases hp96 with ⟨hp, hp_eq, _hpData, h96⟩
    rcases h96 with ⟨_hH0MF, _hMFM, _hnormal96, _hchief, hsourceFixed, _hcard⟩
    rcases hsourceFixed with ⟨_hnormalSrc, hsourceCard⟩
    have hsourceCard' :
        Nat.card {x : MF ⧸ H0MF //
          ∀ h : MF, QuotientGroup.mk' H0MF h = x →
            ∀ w : G, w ∈ W1 → ⁅w, (h : G)⁆ ∈ H0} = p := by
      simpa [H0MF, hp_eq] using hsourceCard
    have hsource_eq_fixed :
        Nat.card {x : MF ⧸ H0MF //
          ∀ h : MF, QuotientGroup.mk' H0MF h = x →
            ∀ w : G, w ∈ W1 → ⁅w, (h : G)⁆ ∈ H0} =
          Nat.card (fixedPointSubgroup W1 (MF ⧸ H0MF)) := by
      simpa [H0MF] using
        theorem_9_7_W1_fixedPointSubgroup_card_eq_source_subtype_sec9
          MF W1 H0 hH0invW1 hnormalH0
    exact hsource_eq_fixed.symm.trans hsourceCard'
  have hfixed_eq :
      fixedPointSubgroup W1 (MF ⧸ H0MF) =
        (W2.subgroupOf MF).map (QuotientGroup.mk' H0MF) := by
    simpa [H0MF] using
      quotient_W1_fixedPointSubgroup_eq_W2_map_of_hypothesis_9_2_sec9
        M MF U W1 W2 H0 q h92 hnormalH0 hH0invW1
  let W2bar : Subgroup (MF ⧸ H0MF) :=
    (W2.subgroupOf MF).map (QuotientGroup.mk' H0MF)
  let primeLine : Subgroup (Multiplicative F) :=
    Subgroup.zpowers (Multiplicative.ofAdd (1 : F))
  have himage_le : Subgroup.map φH.toMonoidHom W2bar ≤ primeLine := by
    intro y hy
    rcases hy with ⟨x, hxW2bar, rfl⟩
    have hxFixed : x ∈ fixedPointSubgroup W1 (MF ⧸ H0MF) := by
      rw [hfixed_eq]
      exact hxW2bar
    revert hxFixed
    refine QuotientGroup.induction_on x ?_
    intro h hxFixed
    let z : F := Multiplicative.toAdd (φH (QuotientGroup.mk' H0MF h))
    let σ : RingAut F := frobeniusEquiv F p
    rcases φW.surjective σ with ⟨w, hw⟩
    rcases hWaction w h with ⟨hconjMF, hφH, _hcompat⟩
    have hfixed_mk :
        (w⁻¹ : W1) • QuotientGroup.mk' H0MF h = QuotientGroup.mk' H0MF h := by
      change ∀ w : W1, w • QuotientGroup.mk' H0MF h =
        QuotientGroup.mk' H0MF h at hxFixed
      exact hxFixed w⁻¹
    have hsmul_eq :
        (w⁻¹ : W1) • h =
          ⟨(w : G)⁻¹ * (h : G) * (w : G), hconjMF h⟩ := by
      apply Subtype.ext
      simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
    have hfixed_conj :
        QuotientGroup.mk' H0MF
            ⟨(w : G)⁻¹ * (h : G) * (w : G), hconjMF h⟩ =
          QuotientGroup.mk' H0MF h := by
      have hq :
          QuotientGroup.mk' H0MF ((w⁻¹ : W1) • h) =
            QuotientGroup.mk' H0MF h := by
        simpa using hfixed_mk
      simpa [hsmul_eq] using hq
    have hcoord_fixed : σ z = z := by
      have hφH' := hφH
      rw [hfixed_conj] at hφH'
      have hcoord := congrArg Multiplicative.toAdd hφH'
      have hz : z = (φW w) z := by
        simpa [z] using hcoord
      rw [← hw]
      exact hz.symm
    have hzpow : z ^ p = z := by
      calc
        z ^ p = (frobeniusEquiv F p) z := (frobeniusEquiv_def F p z).symm
        _ = z := by simpa [σ] using hcoord_fixed
    have hzmem : Multiplicative.ofAdd z ∈ primeLine := by
      simpa [primeLine] using
        theorem_9_7_mem_prime_field_zpowers_of_frobenius_fixed_sec9
          (F := F) (p := p) hzpow
    change Multiplicative.ofAdd z ∈ primeLine
    exact hzmem
  have hW2bar_card : Nat.card W2bar = p := by
    have hW2bar_eq :
        W2bar = fixedPointSubgroup W1 (MF ⧸ H0MF) := by
      simpa [W2bar] using hfixed_eq.symm
    calc
      Nat.card W2bar =
          Nat.card (fixedPointSubgroup W1 (MF ⧸ H0MF)) := by
            rw [hW2bar_eq]
      _ = p := hfixedCard
  have himageCard : Nat.card (Subgroup.map φH.toMonoidHom W2bar) = p := by
    calc
      Nat.card (Subgroup.map φH.toMonoidHom W2bar) = Nat.card W2bar := by
        exact Subgroup.card_map_of_injective (K := W2bar) (f := φH.toMonoidHom)
          φH.injective
      _ = p := hW2bar_card
  have hprimeLineCard : Nat.card primeLine = p := by
    simpa [primeLine] using
      theorem_9_7_prime_field_zpowers_card_sec9 (F := F) (p := p)
  have hW2image :
      Subgroup.map φH.toMonoidHom
          ((W2.subgroupOf MF).map (QuotientGroup.mk' H0MF)) =
        Subgroup.zpowers (Multiplicative.ofAdd (1 : F)) := by
    change Subgroup.map φH.toMonoidHom W2bar = primeLine
    exact Subgroup.eq_of_le_of_card_ge himage_le (by
      rw [himageCard, hprimeLineCard])
  have hW2leMF : W2 ≤ MF := by
    rcases h92.typePDefinitionData with
      ⟨_hMFsource, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD,
        _hUnil, _hW1normU, _hcompDU, _hMFnotcyc, _hsecond, _hfitEq,
        _hfitLeD, hW2le, _hW2cyc, _hW2ne, _hcentW1, _hnormX⟩
    exact (le_inf_iff.mp hW2le).1
  exact
    ⟨hnormalH0, hnormalC, hW1normU, hCinv, F, fieldInst, fintypeInst,
      Ustar, hFcard, hUstarCard, hUstarCyc, hspan, φH, φU, φW,
      ⟨hUaction, hWaction⟩, ⟨hW2leMF, hW2image⟩⟩

private theorem theorem_9_7_case_split_with_centralizer_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
          quotientChiefFactorData_9_6 M MF H0 W1 hp) →
          quotientCentralizerIn MF H0 U C →
            quotientBarUCardinality U C u →
              Nat.Prime p →
                Nat.Prime q →
                (∃ a : ℕ,
                  case_9_7_a_data M MF U W1 W2 H0 C p q a) ∨
          case_9_7_b_data M MF U W1 W2 H0 C p q u := by
  intro h92 hp96 hC hBarU hpprime hqprime
  rcases hp96 with ⟨hp, hp_eq, hpData, h96⟩
  rcases h96 with ⟨hH0MF, hMFM, hH0normal, hchief, hWbar, hcardRaw⟩
  have hcard :
      Nat.card (MF ⧸ H0.subgroupOf MF) = p ^ q :=
    theorem_9_7_quotient_cardinality_from_chief_data_sec9 h92 hp_eq
      ⟨hH0MF, hMFM, hH0normal, hchief, hWbar, hcardRaw⟩
  rcases theorem_9_7_case_split_with_centralizer_source_bridge_sec9
      M MF U W1 W2 H0 C p q u h92
      ⟨hp, hp_eq, hpData, ⟨hH0MF, hMFM, hH0normal, hchief, hWbar, hcardRaw⟩⟩
      hC hBarU hpprime hqprime with hcaseA | hcaseB
  · rcases hcaseA with ⟨a, hdecomp, hinj⟩
    left
    have hadiv : a ∣ p - 1 :=
      theorem_9_7_case_a_divides_p_minus_one_sec9 hpprime hqprime hdecomp
    refine ⟨a, ?_⟩
    exact
      ⟨h92, hH0MF, hC, hpprime, hqprime,
        ⟨hp, hp_eq, hpData, ⟨hH0MF, hMFM, hH0normal, hchief, hWbar, hcardRaw⟩⟩,
        hdecomp, hcard, hadiv, hinj⟩
  · rcases hcaseB with ⟨hirred, hfield, hcop⟩
    right
    have hprimeField :
        quotientFieldSemidirectModelWithPrimeFieldImageData
          MF H0 U C W1 W2 p q u :=
      theorem_9_7_irreducible_field_model_with_prime_field_image_source_bridge_sec9
        M MF U W1 W2 H0 C p q u h92
        ⟨hp, hp_eq, hpData, ⟨hH0MF, hMFM, hH0normal, hchief, hWbar, hcardRaw⟩⟩
        hC hBarU hpprime hqprime hirred hfield
    have hCcentralized : quotientCentralizedBy MF H0 C :=
      theorem_9_7_quotientCentralizedBy_C_sec9 hC
    have hBarUCyclic : quotientBarUCyclicData U C u :=
      theorem_9_7_quotientBarUCyclicData_of_field_model_sec9 hC.1 hfield
    have hdiv_total : u ∣ p ^ q - 1 :=
      theorem_9_7_case_b_divides_field_units_sec9 hfield
    have hdiv : u ∣ (p ^ q - 1) / (p - 1) :=
      theorem_9_7_case_b_quotient_divisibility_sec9 hpprime hcop hdiv_total
    exact
      ⟨h92, hH0MF, hC, hpprime, hqprime,
        ⟨hp, hp_eq, hpData, ⟨hH0MF, hMFM, hH0normal, hchief, hWbar, hcardRaw⟩⟩,
        ⟨hH0normal, hcard⟩, hCcentralized, hBarUCyclic, hirred, hfield, hcop,
        hdiv, hprimeField⟩

public theorem theorem_9_7_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q u : ℕ) :
    hypothesis_9_2_statement M MF U W1 W2 q →
      (∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
          quotientChiefFactorData_9_6 M MF H0 W1 hp) →
        quotientCentralizerIn MF H0 U C →
        quotientBarUCardinality U C u →
            (∃ a : ℕ, case_9_7_a_data M MF U W1 W2 H0 C p q a) ∨
          case_9_7_b_data M MF U W1 W2 H0 C p q u := by
  intro h92 hp96 hC hBarU
  rcases hp96 with ⟨hp, hp_eq, hpData, h96⟩
  have hpprime : Nat.Prime p := by
    rw [← hp_eq]
    exact hp.property
  have hqprime : Nat.Prime q :=
    q_prime_of_hypothesis_9_2_sec9 M MF U W1 W2 q h92
  exact theorem_9_7_case_split_with_centralizer_source_core_sec9
    M MF U W1 W2 H0 C p q u h92 ⟨hp, hp_eq, hpData, h96⟩ hC hBarU
      hpprime hqprime


end CFSG.Section9
