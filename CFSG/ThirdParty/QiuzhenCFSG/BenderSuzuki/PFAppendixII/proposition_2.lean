module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixII.proposition_1
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.RightNearField.Linear
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixI.proposition_2
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection2.EndFieldRep
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.Maschke

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi Appendix II, Proposition 2

The statement follows the authoritative Part II source, printed page 138.
-/

namespace CFSG.BenderSuzuki
namespace PFAppendixII

universe u

/-- The cardinal identity used at the start of the printed irreducibility
argument: an index-two subgroup of the unit group has half of the nonzero
elements. -/
public theorem rightNearField_card_eq_two_mul_card_add_one_of_index_two
    {F : Type u} [RightNearField F] [Finite F]
    (A : Subgroup Fˣ) (hA_index : A.index = 2) :
    Nat.card F = 2 * Nat.card A + 1 := by
  have hmul := Subgroup.card_mul_index A
  rw [hA_index] at hmul
  have hF := Nat.card_eq_card_units_add_one F
  omega

/-- The numerical contradiction in the irreducibility paragraph of the
source. Two nonzero invariant summands would each have at least |A| + 1
elements, which is incompatible with |F| = 2|A| + 1. -/
public theorem indexTwo_irreducibility_card_contradiction
    {a f₁ f₂ : ℕ} (ha : 0 < a)
    (h₁ : a + 1 ≤ f₁) (h₂ : a + 1 ≤ f₂)
    (hcard : 2 * a + 1 = f₁ * f₂) : False := by
  have hprod : (a + 1) * (a + 1) ≤ f₁ * f₂ :=
    Nat.mul_le_mul h₁ h₂
  nlinarith

/-- Right multiplication by the unit group is fixed-point-free on the
nonzero additive elements. -/
public theorem rightNearField_mul_right_fixed_of_ne_zero
    {F : Type u} [RightNearField F] {x : F} (hx : x ≠ 0)
    (a : Fˣ) (hfix : x * (a : F) = x) : a = 1 := by
  apply Units.ext
  apply mul_left_cancel₀ hx
  simpa using hfix

/-- An additive subgroup is invariant under the right-multiplication action
of a subgroup of the near-field unit group. -/
@[expose] public def RightInvariantAddSubgroup
    (F : Type u) [RightNearField F] (A : Subgroup Fˣ)
    (U : AddSubgroup F) : Prop :=
  ∀ x : F, x ∈ U → ∀ a : A, x * (a : Fˣ) ∈ U

/-- A nonzero invariant additive subgroup has at least |A| + 1 elements.
The proof injects Option A: none maps to zero and some a maps to x*a for a
fixed nonzero x in the subgroup. -/
public theorem rightInvariantAddSubgroup_card_lower_bound
    {F : Type u} [RightNearField F] [Finite F]
    (A : Subgroup Fˣ) (U : AddSubgroup F)
    (hU : RightInvariantAddSubgroup F A U) (hU_ne : U ≠ ⊥) :
    Nat.card A + 1 ≤ Nat.card U := by
  classical
  obtain ⟨x, hxU, hx0⟩ : ∃ x : F, x ∈ U ∧ x ≠ 0 := by
    by_contra h
    push Not at h
    apply hU_ne
    apply le_antisymm
    · intro y hy
      simpa using h y hy
    · exact bot_le
  let f : Option A → U
    | none => 0
    | some a => ⟨x * (a : Fˣ), hU x hxU a⟩
  have hf : Function.Injective f := by
    intro a b hab
    cases a with
    | none =>
        cases b with
        | none => rfl
        | some b =>
            exfalso
            have hv := congrArg (fun z : U => (z : F)) hab
            simp only [f, AddSubgroup.coe_zero] at hv
            exact (mul_ne_zero hx0 (Units.ne_zero (b : Fˣ))) hv.symm
    | some a =>
        cases b with
        | none =>
            exfalso
            have hv := congrArg (fun z : U => (z : F)) hab
            simp only [f, AddSubgroup.coe_zero] at hv
            exact (mul_ne_zero hx0 (Units.ne_zero (a : Fˣ))) hv
        | some b =>
            congr
            apply Subtype.ext
            apply Units.ext
            apply mul_left_cancel₀ hx0
            exact congrArg (fun z : U => (z : F)) hab
  have hcard := Nat.card_le_card_of_injective f hf
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype U := Fintype.ofFinite U
  simpa [Nat.card_eq_fintype_card] using hcard

/-- Cardinality of an internal direct sum of finite additive subgroups. -/
public theorem addSubgroup_card_eq_mul_of_disjoint_sup_eq_top
    {F : Type u} [AddCommGroup F] [Finite F]
    (U V : AddSubgroup F) (hdisj : Disjoint U V) (hsup : U ⊔ V = ⊤) :
    Nat.card F = Nat.card U * Nat.card V := by
  classical
  let f : U × V → F := fun p => (p.1 : F) + (p.2 : F)
  have hf_inj : Function.Injective f := by
    rintro ⟨u₁, v₁⟩ ⟨u₂, v₂⟩ huv
    have hdiff : (u₁ : F) - (u₂ : F) = (v₂ : F) - (v₁ : F) := by
      change (u₁ : F) + (v₁ : F) = (u₂ : F) + (v₂ : F) at huv
      calc
        (u₁ : F) - (u₂ : F) =
            ((u₁ : F) + (v₁ : F)) - ((u₂ : F) + (v₁ : F)) := by abel
        _ = ((u₂ : F) + (v₂ : F)) - ((u₂ : F) + (v₁ : F)) := by rw [huv]
        _ = (v₂ : F) - (v₁ : F) := by abel
    have hdiff_mem : (u₁ : F) - (u₂ : F) ∈ U ⊓ V := by
      constructor
      · exact U.sub_mem u₁.property u₂.property
      · rw [hdiff]
        exact V.sub_mem v₂.property v₁.property
    have hdiff_zero : (u₁ : F) - (u₂ : F) = 0 := by
      have hbot : (u₁ : F) - (u₂ : F) ∈ (⊥ : AddSubgroup F) :=
        hdisj.le_bot hdiff_mem
      simpa using hbot
    have hu : (u₁ : F) = (u₂ : F) := sub_eq_zero.mp hdiff_zero
    have hv : (v₁ : F) = (v₂ : F) := by
      change (u₁ : F) + (v₁ : F) = (u₂ : F) + (v₂ : F) at huv
      simpa [hu] using huv
    exact Prod.ext (Subtype.ext hu) (Subtype.ext hv)
  have hf_surj : Function.Surjective f := by
    intro x
    have hx : x ∈ U ⊔ V := by rw [hsup]; simp
    rcases AddSubgroup.mem_sup.mp hx with ⟨a, ha, b, hb, hab⟩
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), hab⟩
  have hcard := Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)
  rw [Nat.card_prod] at hcard
  exact hcard.symm

/-- The cyclic index-two subgroup is irreducible in the exact direct-sum sense
used in the printed proof: two nonzero invariant complementary summands are
impossible. -/
public theorem proposition_2_indexTwoCyclic_irreducible
    {F : Type u} [RightNearField F] [Finite F]
    (A : Subgroup Fˣ) (hA_index : A.index = 2)
    (U V : AddSubgroup F)
    (hU : RightInvariantAddSubgroup F A U)
    (hV : RightInvariantAddSubgroup F A V)
    (hU_ne : U ≠ ⊥) (hV_ne : V ≠ ⊥)
    (hdisj : Disjoint U V) (hsup : U ⊔ V = ⊤) : False := by
  apply indexTwo_irreducibility_card_contradiction
      (a := Nat.card A) (f₁ := Nat.card U) (f₂ := Nat.card V)
  · exact Nat.card_pos
  · exact rightInvariantAddSubgroup_card_lower_bound A U hU hU_ne
  · exact rightInvariantAddSubgroup_card_lower_bound A V hV hV_ne
  · have hF := rightNearField_card_eq_two_mul_card_add_one_of_index_two A hA_index
    have hUV := addSubgroup_card_eq_mul_of_disjoint_sup_eq_top U V hdisj hsup
    omega


/-- The additive characteristic does not divide the cardinality of an
index-two subgroup of the near-field unit group. This is the Maschke
coprimality input. -/
public theorem rightNearField_addOrderOf_one_not_dvd_indexTwoSubgroup_card
    {F : Type u} [RightNearField F] [Finite F]
    (A : Subgroup Fˣ) (hA_index : A.index = 2) :
    ¬ addOrderOf (1 : F) ∣ Nat.card A := by
  let p := addOrderOf (1 : F)
  have hp : Nat.Prime p := rightNearField_addOrderOf_one_prime
  obtain ⟨n, hcardpow⟩ :=
    rightNearField_natCard_eq_addOrderOf_one_pow (F := F)
  have hFgt : 1 < Nat.card F := by
    letI : Fintype F := Fintype.ofFinite F
    simpa [Nat.card_eq_fintype_card] using Fintype.one_lt_card (α := F)
  have hn : n ≠ 0 := by
    intro hn
    subst n
    simp at hcardpow
    omega
  have hpF : p ∣ Nat.card F := by
    rw [hcardpow]
    exact dvd_pow_self p hn
  have hFcard :=
    rightNearField_card_eq_two_mul_card_add_one_of_index_two A hA_index
  intro hpA
  have hp_twoA : p ∣ 2 * Nat.card A := dvd_mul_of_dvd_right hpA 2
  rw [hFcard] at hpF
  have hp_one : p ∣ 1 := (Nat.dvd_add_iff_right hp_twoA).mpr hpF
  exact hp.ne_one (Nat.dvd_one.mp hp_one)


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 500000 in
set_option backward.isDefEq.respectTransparency false in
private theorem proposition_2_appendixI_field_coordinates
    {F : Type u} [RightNearField F] [Finite F]
    (A : Subgroup Fˣ) (hA_cyclic : IsCyclic A) (hA_index : A.index = 2) :
    ∃ (p n : ℕ) (K : Type u) (_ : CommRing K) (_ : Finite K)
        (_ : Algebra (ZMod p) K) (e : F ≃+ K),
      IsField K ∧ Nat.Prime p ∧ Nat.card K = p ^ n ∧ e 1 = 1 ∧
        (∀ (x : F) (a : A),
          e (x * ((a : A) : Fˣ)) = e x * e (((a : A) : Fˣ) : F)) ∧
        Subring.closure
          (Set.range (algebraMap (ZMod p) K) ∪
            Set.range (fun a : A => e (((a : A) : Fˣ) : F))) = ⊤ := by
  let p := addOrderOf (1 : F)
  letI : Fact (Nat.Prime p) := ⟨rightNearField_addOrderOf_one_prime⟩
  letI : Module (ZMod p) F := rightNearFieldZModModule F
  letI : MulDistribMulAction A (Multiplicative F) := {
    smul a x := Multiplicative.ofAdd (Multiplicative.toAdd x * ((a : A) : Fˣ))
    one_smul x := by
      change Multiplicative.toAdd x * (1 : F) = Multiplicative.toAdd x
      simp
    mul_smul a b x := by
      change Multiplicative.toAdd x * (((a * b : A) : Fˣ) : F) =
        (Multiplicative.toAdd x * ((b : A) : Fˣ)) * ((a : A) : Fˣ)
      rw [Subgroup.coe_mul, Units.val_mul]
      have habU : (a : Fˣ) * (b : Fˣ) = (b : Fˣ) * (a : Fˣ) :=
        congrArg Subtype.val (hA_cyclic.isMulCommutative.is_comm.comm a b)
      have habF : ((a : Fˣ) : F) * (b : Fˣ) =
          ((b : Fˣ) : F) * (a : Fˣ) := congrArg Units.val habU
      rw [habF, mul_assoc]
    smul_mul a x y := by
      change (Multiplicative.toAdd x + Multiplicative.toAdd y) * ((a : A) : Fˣ) =
        Multiplicative.toAdd x * ((a : A) : Fˣ) +
          Multiplicative.toAdd y * ((a : A) : Fˣ)
      exact RightNearField.right_distrib _ _ _
    smul_one a := by
      change (0 : F) * ((a : A) : Fˣ) = 0
      exact zero_mul _ }
  letI : FaithfulSMul A (Multiplicative F) := {
    eq_of_smul_eq_smul h := by
      have h1 := h (Multiplicative.ofAdd (1 : F))
      change (1 : F) * ((_ : A) : Fˣ) = 1 * ((_ : A) : Fˣ) at h1
      apply Subtype.ext
      apply Units.ext
      simpa using h1 }
  letI : IsElementaryAbelian p (Multiplicative F) :=
    { toIsMulCommutative := { is_comm := ⟨mul_comm⟩ }
      exponent_dvd_p := by
        refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
        intro x
        change addOrderOf (1 : F) • Multiplicative.toAdd x = 0
        exact rightNearField_addOrderOf_one_nsmul_eq_zero
          (F := F) (Multiplicative.toAdd x) }
  let T : Subgroup A := ⊤
  letI : T.Normal := inferInstance
  letI : IsCyclic A := hA_cyclic
  letI : IsCyclic T := inferInstance
  let rhoT := PFAppendixI.AppendixIRepresentationOfT
    (p := p) (E := Multiplicative F) T
  have hIrr : Representation.IsIrreducible rhoT := by
    have hnotA : ¬ p ∣ Nat.card A :=
      rightNearField_addOrderOf_one_not_dvd_indexTwoSubgroup_card A hA_index
    have hnot : ¬ p ∣ Nat.card T := by
      simpa [T, Subgroup.card_top] using hnotA
    have hring : ringChar (ZMod p) = p := ringChar.eq (ZMod p) p
    have hchar :
        ringChar (ZMod p) = 0 ∨
          Nat.Prime (ringChar (ZMod p)) ∧
            (ringChar (ZMod p)).Coprime (Nat.card T) := by
      right
      rw [hring]
      exact ⟨Fact.out, (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mpr hnot⟩
    letI : Module (MonoidAlgebra (ZMod p) T) (Additive (Multiplicative F)) :=
      rhoT.instModuleMonoidAlgebraAsModule
    have hsemi : IsSemisimpleModule
        (MonoidAlgebra (ZMod p) T) (Additive (Multiplicative F)) :=
      Representation.isCompletelyReducible_of_ringChar_eq_zero_or_prime_coprime
        rhoT hchar
    apply (Representation.irreducible_iff_isSimpleModule_asModule rhoT).mpr
    rw [isSimpleModule_iff]
    have hbot_ne_top :
        (⊥ : Submodule (MonoidAlgebra (ZMod p) T) (Additive (Multiplicative F))) ≠ ⊤ :=
      bot_ne_top
    refine
      { exists_pair_ne := ⟨⊥, ⊤, hbot_ne_top⟩
        eq_bot_or_eq_top := ?_ }
    intro S
    by_cases hSbot : S = ⊥
    · exact Or.inl hSbot
    right
    by_contra hStop
    obtain ⟨V, hSV⟩ := hsemi.exists_isCompl S
    have hVbot : V ≠ ⊥ := by
      intro hV
      apply hStop
      have hsup := hSV.sup_eq_top
      rw [hV, sup_bot_eq] at hsup
      exact hsup
    exfalso
    apply proposition_2_indexTwoCyclic_irreducible A hA_index
        S.toAddSubgroup V.toAddSubgroup
    · intro x hx a
      have hxS : x ∈ S := (Submodule.mem_toAddSubgroup S).mp hx
      let x' : Additive (Multiplicative F) := x
      let t : T := ⟨a, by simp [T]⟩
      have hsmul' : (MonoidAlgebra.single t (1 : ZMod p)) • (x' : rhoT.asModule) ∈ S := by
        have hxS' : (x' : rhoT.asModule) ∈ S := hxS
        exact S.smul_mem' (MonoidAlgebra.single t (1 : ZMod p)) hxS'
      have htemp_eq : (MonoidAlgebra.single t (1 : ZMod p)) • (x' : rhoT.asModule) = (rhoT t) x' := by
        calc
          (MonoidAlgebra.single t (1 : ZMod p)) • (x' : rhoT.asModule) =
              (1 : ZMod p) • rhoT t (rhoT.asModuleEquiv (x' : rhoT.asModule)) :=
            Representation.single_smul (t := (1 : ZMod p)) (g := t) (v := (x' : rhoT.asModule)) (ρ := rhoT)
          _ = rhoT t (rhoT.asModuleEquiv (x' : rhoT.asModule)) := by simp
          _ = (rhoT t) x' := by
            have h_cast : rhoT.asModuleEquiv (x' : rhoT.asModule) = (x' : Additive (Multiplicative F)) := rfl
            simp [h_cast]
      have hval' : rhoT t x' ∈ S := by
        rw [← htemp_eq]
        exact hsmul'
      have h_eq : rhoT t x' = (x : F) * (((a : A) : Fˣ) : F) := by
        calc
          rhoT t x' = Additive.ofMul (t • Additive.toMul x') := by
            simpa using (Theory.Representation.ofElementaryAbelianAction_apply_ofMul
              (a := t) (x := Additive.toMul x'))
          _ = (x : F) * (((a : A) : Fˣ) : F) := by
            dsimp [t, x']
            rfl
      have hX : (x : F) * (((a : A) : Fˣ) : F) ∈ S := by
        rw [← h_eq]
        exact hval'
      exact (Submodule.mem_toAddSubgroup S).mpr hX
    · intro x hx a
      have hxV : x ∈ V := (Submodule.mem_toAddSubgroup V).mp hx
      let x' : Additive (Multiplicative F) := x
      let t : T := ⟨a, by simp [T]⟩
      have hsmul' : (MonoidAlgebra.single t (1 : ZMod p)) • (x' : rhoT.asModule) ∈ V := by
        have hxV' : (x' : rhoT.asModule) ∈ V := hxV
        exact V.smul_mem' (MonoidAlgebra.single t (1 : ZMod p)) hxV'
      have htemp_eq : (MonoidAlgebra.single t (1 : ZMod p)) • (x' : rhoT.asModule) = (rhoT t) x' := by
        calc
          (MonoidAlgebra.single t (1 : ZMod p)) • (x' : rhoT.asModule) =
              (1 : ZMod p) • rhoT t (rhoT.asModuleEquiv (x' : rhoT.asModule)) :=
            Representation.single_smul (t := (1 : ZMod p)) (g := t) (v := (x' : rhoT.asModule)) (ρ := rhoT)
          _ = rhoT t (rhoT.asModuleEquiv (x' : rhoT.asModule)) := by simp
          _ = (rhoT t) x' := by
            have h_cast : rhoT.asModuleEquiv (x' : rhoT.asModule) = (x' : Additive (Multiplicative F)) := rfl
            simp [h_cast]
      have hval' : rhoT t x' ∈ V := by
        rw [← htemp_eq]
        exact hsmul'
      have h_eq : rhoT t x' = (x : F) * (((a : A) : Fˣ) : F) := by
        calc
          rhoT t x' = Additive.ofMul (t • Additive.toMul x') := by
            simpa using (Theory.Representation.ofElementaryAbelianAction_apply_ofMul
              (a := t) (x := Additive.toMul x'))
          _ = (x : F) * (((a : A) : Fˣ) : F) := by
            dsimp [t, x']
            rfl
      have hX : (x : F) * (((a : A) : Fˣ) : F) ∈ V := by
        rw [← h_eq]
        exact hval'
      exact (Submodule.mem_toAddSubgroup V).mpr hX
    · intro h
      apply hSbot
      exact Submodule.toAddSubgroup_injective h
    · intro h
      apply hVbot
      exact Submodule.toAddSubgroup_injective h
    · rw [disjoint_iff]
      have hinf : (S ⊓ V).toAddSubgroup = S.toAddSubgroup ⊓ V.toAddSubgroup := by
        ext x; simp
      simpa [hinf] using congrArg Submodule.toAddSubgroup hSV.inf_eq_bot
    · simpa [Submodule.sup_toAddSubgroup] using
        congrArg Submodule.toAddSubgroup hSV.sup_eq_top
  letI : Representation.IsIrreducible rhoT := hIrr
  obtain ⟨n, hcard⟩ := rightNearField_natCard_eq_addOrderOf_one_pow (F := F)
  let K := PFAppendixI.AppendixIFpT (p := p) (E := Multiplicative F) T
  have hKisField : IsField K := Finite.isField_of_domain K
  obtain ⟨fieldInst, hfield⟩ :=
    PFAppendixI.peterfalvi_appendixI_proposition_2_a
      (p := p) (n := n) (U := A) (E := Multiplicative F) T hcard
  letI : Field K := fieldInst
  obtain ⟨moduleInst, hmodule⟩ := hfield
  letI : Module K (Additive (Multiplicative F)) := moduleInst
  have hKcard := hmodule.1
  have hsmul := hmodule.2.2
  let v1 : Additive (Multiplicative F) :=
    Additive.ofMul (Multiplicative.ofAdd (1 : F))
  have hv1 : v1 ≠ 0 := by
    intro h
    change (1 : F) = 0 at h
    exact one_ne_zero h
  let eval : K →ₗ[K] Additive (Multiplicative F) :=
    LinearMap.toSpanSingleton K (Additive (Multiplicative F)) v1
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype (Additive (Multiplicative F)) :=
    Fintype.ofFinite (Additive (Multiplicative F))
  have hcards : Fintype.card K = Fintype.card (Additive (Multiplicative F)) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hKcard.trans hcard.symm
  have heval_injective : Function.Injective eval := by
    intro k l hkl
    change k • v1 = l • v1 at hkl
    rw [hsmul k v1, hsmul l v1] at hkl
    let d : Module.End (MonoidAlgebra (ZMod p) T) rhoT.asModule := k.1 - l.1
    have hdv1 : d v1 = 0 := by
      change k.1 v1 - l.1 v1 = 0
      exact sub_eq_zero.mpr hkl
    let W : Subrepresentation rhoT :=
      { toSubmodule := LinearMap.ker (d.restrictScalars (ZMod p))
        apply_mem_toSubmodule := by
          intro t x hx
          let x_as_rho : rhoT.asModule := x
          have hdx : d x_as_rho = 0 := hx
          rw [LinearMap.mem_ker]
          have htemp : d ((rhoT t) x_as_rho : rhoT.asModule) = 0 := by
            have h_cast : rhoT.asModuleEquiv x_as_rho = (x_as_rho : Additive (Multiplicative F)) := rfl
            have h1 : (rhoT t) (rhoT.asModuleEquiv x_as_rho) = (rhoT t) x_as_rho := by
              simp [h_cast]
            have h_smul : d ((MonoidAlgebra.single t (1 : ZMod p)) • x_as_rho) =
              (MonoidAlgebra.single t (1 : ZMod p)) • d x_as_rho :=
              d.map_smul (MonoidAlgebra.single t (1 : ZMod p)) x_as_rho
            calc
              d ((rhoT t) x_as_rho : rhoT.asModule) =
                  d ((rhoT t) (rhoT.asModuleEquiv x_as_rho) : rhoT.asModule) := by
                simp [h1]
              _ = d ((MonoidAlgebra.single t (1 : ZMod p)) • x_as_rho) := by
                simp [Representation.single_smul, one_smul]
              _ = (MonoidAlgebra.single t (1 : ZMod p)) • d x_as_rho := h_smul
              _ = 0 := by simp [hdx]
          exact htemp }
    have hW_ne_bot : W ≠ ⊥ := by
      intro hW
      have hv1bot : v1 ∈ (⊥ : Subrepresentation rhoT) := by
        rw [← hW]
        exact hdv1
      have hv1zero : v1 = 0 := (Submodule.mem_bot _).mp hv1bot
      exact hv1 hv1zero
    have hWtop : W = ⊤ := by
      rcases hIrr.eq_bot_or_eq_top W with hW | hW
      · exact (hW_ne_bot hW).elim
      · exact hW
    apply Subtype.ext
    apply sub_eq_zero.mp
    change d = 0
    ext x
    have hxW : x ∈ W := by
      rw [hWtop]
      exact Submodule.mem_top
    exact hxW
  have heval_surjective : Function.Surjective eval := by
    by_contra hsurj
    have hlt := Fintype.card_lt_of_injective_not_surjective eval
      heval_injective hsurj
    omega
  let eKV : K ≃ₗ[K] Additive (Multiplicative F) :=
    LinearEquiv.ofBijective eval ⟨heval_injective, heval_surjective⟩
  let e : F ≃+ K := eKV.symm.toAddEquiv
  have he1 : e 1 = 1 := by
    apply eKV.injective
    change eKV (eKV.symm (Additive.ofMul (Multiplicative.ofAdd (1 : F)))) = eKV 1
    rw [eKV.apply_symm_apply]
    change Additive.ofMul (Multiplicative.ofAdd (1 : F)) = eval 1
    rw [LinearMap.toSpanSingleton_apply_one]
  have he_apply (x : F) :
      eKV (e x) = Additive.ofMul (Multiplicative.ofAdd x) :=
    eKV.apply_symm_apply (Additive.ofMul (Multiplicative.ofAdd x))
  let kt (t : T) : K :=
    ⟨PFAppendixI.AppendixITActionEnd (p := p) (E := Multiplicative F) T t,
      Algebra.subset_adjoin (Set.mem_range_self t)⟩
  have hkt_smul (t : T) (z : Additive (Multiplicative F)) :
      kt t • z = Additive.ofMul
        (Multiplicative.ofAdd
          (Multiplicative.toAdd (Additive.toMul z) * (((t : T) : A) : Fˣ))) := by
    rw [hsmul]
    change PFAppendixI.AppendixITActionEnd
      (p := p) (E := Multiplicative F) T t z = _
    rw [PFAppendixI.AppendixITActionEnd_apply]
    rfl
  have hcoordT (t : T) :
      e (((((t : T) : A) : Fˣ) : F)) = kt t := by
    apply eKV.injective
    rw [he_apply]
    change Additive.ofMul (Multiplicative.ofAdd (((((t : T) : A) : Fˣ) : F))) =
      eval (kt t)
    change Additive.ofMul (Multiplicative.ofAdd (((((t : T) : A) : Fˣ) : F))) =
      kt t • v1
    rw [hkt_smul]
    change (((((t : T) : A) : Fˣ) : F)) =
      (1 : F) * (((((t : T) : A) : Fˣ) : F))
    simp
  have hscalar : ∀ (x : F) (a : A),
      e (x * ((a : A) : Fˣ)) = e x * e (((a : A) : Fˣ) : F) := by
    intro x a
    let t : T := ⟨a, by simp [T]⟩
    have hta : ((((t : T) : A) : Fˣ) : F) = (((a : A) : Fˣ) : F) := rfl
    apply eKV.injective
    rw [he_apply, ← hta, hcoordT t]
    calc
      Additive.ofMul (Multiplicative.ofAdd (x * ((a : A) : Fˣ))) =
          kt t • Additive.ofMul (Multiplicative.ofAdd x) := by
        rw [hkt_smul]
        rfl
      _ = kt t • eKV (e x) := by rw [he_apply]
      _ = eKV (kt t • e x) := (eKV.map_smul (kt t) (e x)).symm
      _ = eKV (kt t * e x) := by rfl
      _ = eKV (e x * kt t) := congrArg eKV (mul_comm (kt t) (e x))
  let S : Set K :=
    Set.range (algebraMap (ZMod p) K) ∪
      Set.range (fun a : A => e (((a : A) : Fˣ) : F))
  have hclosure : Subring.closure S = ⊤ := by
    apply (Subring.eq_top_iff' _).2
    intro k
    refine Algebra.adjoin_induction
      (p := fun x hx => (⟨x, hx⟩ : K) ∈ Subring.closure S) ?_ ?_ ?_ ?_ k.2
    · intro x hx
      obtain ⟨t, rfl⟩ := hx
      change kt t ∈ Subring.closure S
      rw [← hcoordT t]
      exact Subring.subset_closure
        (Or.inr ⟨((t : T) : A), rfl⟩)
    · intro r
      exact Subring.subset_closure (Or.inl ⟨r, rfl⟩)
    · intro x y hx hy hx' hy'
      exact Subring.add_mem _ hx' hy'
    · intro x y hx hy hx' hy'
      exact Subring.mul_mem _ hx' hy'
  exact ⟨p, n, K, inferInstance, inferInstance, inferInstance, e, hKisField,
    rightNearField_addOrderOf_one_prime, hKcard, he1, hscalar, hclosure⟩

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 500000 in
set_option backward.isDefEq.respectTransparency false in
private theorem proposition_2_semilinear_coordinates
    {F K : Type u} [RightNearField F] [Finite F]
    {p : ℕ} [Fact (Nat.Prime p)] [Field K] [Finite K] [Algebra (ZMod p) K]
    (A : Subgroup Fˣ) (hA_index : A.index = 2) (e : F ≃+ K) (he1 : e 1 = 1)
    (hscalar : ∀ (x : F) (a : A),
      e (x * ((a : A) : Fˣ)) = e x * e (((a : A) : Fˣ) : F))
    (hclosure : Subring.closure
      (Set.range (algebraMap (ZMod p) K) ∪
        Set.range (fun a : A => e (((a : A) : Fˣ) : F))) = ⊤) :
    ∃ σHom : (Fˣ)ᵐᵒᵖ →* (K ≃+* K), ∀ (x : F) (y : Fˣ),
      e (x * (y : F)) = σHom (MulOpposite.op y) (e x) * e (y : F) := by
  letI : Module (ZMod p) F :=
    AddCommGroup.zmodModule (n := p) (by
      intro x
      apply e.injective
      rw [map_nsmul, map_zero]
      rw [← Nat.cast_smul_eq_nsmul (ZMod p)]
      simp)
  let Q0 : Subgroup (Multiplicative F) := ⊤
  let q0Top : Q0 ≃* Multiplicative F := Subgroup.topEquiv
  let q0_add : Q0 ≃* Multiplicative K :=
    q0Top.trans e.toMultiplicative
  let u_add : (Fˣ)ᵐᵒᵖ →* (Q0 ≃* Q0) := {
    toFun u :=
      (q0Top.trans
        (rightNearFieldRightMulAddEquiv u.unop).toMultiplicative).trans q0Top.symm
    map_one' := by
      ext x
      change Multiplicative.toAdd (q0Top x) * (1 : F) =
        Multiplicative.toAdd (q0Top x)
      simp
    map_mul' := by
      intro u v
      ext x
      change Multiplicative.toAdd (q0Top x) *
          ((v.unop * u.unop : Fˣ) : F) =
        (Multiplicative.toAdd (q0Top x) * (v.unop : F)) * (u.unop : F)
      rw [Units.val_mul, mul_assoc] }
  have hu_add_injective : Function.Injective u_add := by
    intro u v huv
    let oneQ : Q0 := ⟨Multiplicative.ofAdd (1 : F), by simp [Q0]⟩
    have h := congrArg (fun g : Q0 ≃* Q0 => q0Top (g oneQ)) huv
    have hval : (u.unop : F) = (v.unop : F) := by
      simpa [u_add, oneQ, q0Top, rightNearFieldRightMulAddEquiv,
        rightNearFieldRightMulAddHom] using congrArg Multiplicative.toAdd h
    apply MulOpposite.unop_injective
    apply Units.ext
    exact hval
  let s : Q0 := ⟨Multiplicative.ofAdd (1 : F), by simp [Q0]⟩
  have hs : (s : Multiplicative F) ≠ 1 := by
    change (1 : F) ≠ 0
    exact one_ne_zero
  let S : Set K :=
    Set.range (algebraMap (ZMod p) K) ∪
      Set.range (fun a : A => e (((a : A) : Fˣ) : F))
  have hAnormal : A.Normal := Subgroup.normal_of_index_eq_two hA_index
  have hconjT : ∀ (u : (Fˣ)ᵐᵒᵖ) (lambda : K), lambda ∈ S →
      ∃ c : K, ∀ x : Q0,
        u_add u (q0_add.symm
            (Multiplicative.ofAdd (lambda * Multiplicative.toAdd (q0_add x)))) =
          q0_add.symm
            (Multiplicative.ofAdd
              (c * Multiplicative.toAdd (q0_add (u_add u x)))) := by
    intro u lambda hlambda
    rcases hlambda with hlambda | hlambda
    · obtain ⟨r, rfl⟩ := hlambda
      refine ⟨algebraMap (ZMod p) K r, ?_⟩
      intro x
      apply q0Top.injective
      let z : F := Multiplicative.toAdd (q0Top x)
      change e.symm (algebraMap (ZMod p) K r * e z) * (u.unop : F) =
        e.symm
          (algebraMap (ZMod p) K r * e (z * (u.unop : F)))
      rw [← Algebra.smul_def, ← Algebra.smul_def]
      calc
        e.symm (r • e z) * (u.unop : F) =
            (r • z) * (u.unop : F) := by
          rw [ZMod.map_smul, e.symm_apply_apply]
        _ = r • (z * (u.unop : F)) :=
          ZMod.map_smul (rightNearFieldRightMulAddHom (u.unop : F)) r z
        _ = e.symm (r • e (z * (u.unop : F))) := by
          rw [ZMod.map_smul, e.symm_apply_apply]
    · obtain ⟨a, rfl⟩ := hlambda
      let a' : A :=
        ⟨u.unop⁻¹ * (a : Fˣ) * u.unop, hAnormal.conj_mem' a.1 a.2 u.unop⟩
      refine ⟨e (((a' : A) : Fˣ) : F), ?_⟩
      intro x
      apply q0Top.injective
      let z : F := Multiplicative.toAdd (q0Top x)
      change e.symm (e (((a : A) : Fˣ) : F) * e z) * (u.unop : F) =
        e.symm
          (e (((a' : A) : Fˣ) : F) * e (z * (u.unop : F)))
      have hleft :
          e.symm (e (((a : A) : Fˣ) : F) * e z) =
            z * ((a : A) : Fˣ) := by
        apply e.injective
        rw [e.apply_symm_apply, hscalar]
        exact mul_comm _ _
      have hright :
          e.symm
              (e (((a' : A) : Fˣ) : F) * e (z * (u.unop : F))) =
            (z * (u.unop : F)) * ((a' : A) : Fˣ) := by
        apply e.injective
        rw [e.apply_symm_apply, hscalar]
        exact mul_comm _ _
      rw [hleft, hright]
      simp [a', mul_assoc]
  obtain ⟨σHom, hsemi, _⟩ :=
    PFAppendixI.peterfalvi_appendixI_proposition_2_b
      Q0 q0_add u_add hu_add_injective s hs S hclosure hconjT
  refine ⟨σHom, ?_⟩
  intro x y
  have h := hsemi (MulOpposite.op y) (e x) s
  have h' :=
    congrArg (fun z : Q0 => Multiplicative.toAdd (q0_add z)) h
  have hq0s : Multiplicative.toAdd (q0_add s) = 1 := by
    change e 1 = 1
    exact he1
  have htopS : Multiplicative.toAdd (q0Top s) = 1 := rfl
  rw [hq0s, mul_one] at h'
  simpa [q0_add, q0Top, u_add, s, he1, htopS,
    rightNearFieldRightMulAddEquiv, rightNearFieldRightMulAddHom] using h'

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
private theorem finiteField_orderTwo_aut_coordinates
    {p : ℕ} [Fact (Nat.Prime p)]
    {K : Type u} [Field K] [Finite K] [Algebra (ZMod p) K]
    (τ : K ≃+* K) (hτ_order : orderOf τ = 2) :
    ∃ m : ℕ, 0 < m ∧ Nat.card K = p ^ (2 * m) ∧
      (∀ x : K, τ x = x ^ (p ^ m)) ∧
      Nat.card {u : Kˣ // τ (u : K) = (u : K)} = p ^ (m : ℕ) - 1 := by
  letI : Fintype K := Fintype.ofFinite K
  have hτ_sq : τ ^ 2 = 1 := by
    rw [← hτ_order]
    exact pow_orderOf_eq_one τ
  have hτ_ne : τ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hτ_order
    omega
  let τAlg : K ≃ₐ[ZMod p] K :=
    AlgEquiv.ofRingEquiv (f := τ) (fun r => by
      simpa [Algebra.smul_def] using
        (ZMod.map_smul τ.toAddMonoidHom r (1 : K)))
  have hτAlg_order : orderOf τAlg = 2 := by
    apply orderOf_eq_prime
    · apply AlgEquiv.ext
      intro x
      exact DFunLike.congr_fun hτ_sq x
    · intro h
      apply hτ_ne
      apply RingEquiv.ext
      intro x
      exact DFunLike.congr_fun (congrArg AlgEquiv.toRingEquiv h) x
  let H : Subgroup Gal(K / ZMod p) := Subgroup.zpowers τAlg
  let L : IntermediateField (ZMod p) K := IntermediateField.fixedField H
  have hfinrank : Module.finrank L K = 2 := by
    change Module.finrank (IntermediateField.fixedField H) K = 2
    rw [IntermediateField.finrank_fixedField_eq_card,
      Nat.card_zpowers, hτAlg_order]
  let τL : K ≃ₐ[L] K :=
    AlgEquiv.ofRingEquiv (f := τ) (fun z => by
      have hz := z.2
      change (z : K) ∈ IntermediateField.fixedField H at hz
      rw [IntermediateField.mem_fixedField_iff] at hz
      simpa [τAlg] using hz τAlg (by simp [H]))
  have hτL_order : orderOf τL = 2 := by
    apply orderOf_eq_prime
    · apply AlgEquiv.ext
      intro x
      exact DFunLike.congr_fun hτ_sq x
    · intro h
      apply hτ_ne
      apply RingEquiv.ext
      intro x
      exact DFunLike.congr_fun (congrArg AlgEquiv.toRingEquiv h) x
  letI : Fintype L := Fintype.ofFinite L
  let fr : Gal(K / L) :=
    FiniteField.frobeniusAlgEquivOfAlgebraic L K
  have hfr_order : orderOf fr = 2 := by
    dsimp [fr]
    rw [FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic, hfinrank]
  have hGalcard : Nat.card Gal(K / L) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, hfinrank]
  have hτL_ne : τL ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hτL_order
    omega
  have hfr_ne : fr ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hfr_order
    omega
  have hτfr : τL = fr := by
    obtain ⟨g, hg, huniq⟩ :=
      (Nat.card_eq_two_iff' (1 : Gal(K / L))).mp hGalcard
    exact (huniq τL hτL_ne).trans (huniq fr hfr_ne).symm
  have hτpow : ∀ x : K, τ x = x ^ Nat.card L := by
    intro x
    change τL x = _
    rw [hτfr]
    change x ^ Fintype.card L = x ^ Nat.card L
    rw [Nat.card_eq_fintype_card]
  letI : CharP L p := by
    rw [← Algebra.charP_iff (ZMod p) L p]
    exact ZMod.charP p
  obtain ⟨m, _, hLcard⟩ := FiniteField.card L p
  have hcardKL := Module.card_eq_pow_finrank (K := L) (V := K)
  have hKcard : Nat.card K = p ^ (2 * (m : ℕ)) := by
    calc
      Nat.card K = Nat.card L ^ 2 := by
        simpa [Nat.card_eq_fintype_card, hfinrank] using hcardKL
      _ = (p ^ (m : ℕ)) ^ 2 := by
        simp [Nat.card_eq_fintype_card, hLcard]
      _ = p ^ (2 * (m : ℕ)) := by
        rw [← pow_mul]
        congr 1
        omega
  have hfixed_mem {x : K} (hx : τAlg x = x) : x ∈ L := by
    rw [IntermediateField.mem_fixedField_iff]
    intro f hf
    have hτ_smul : τAlg • x = x := by
      simpa [AlgEquiv.smul_def] using hx
    have hf_smul := smul_eq_self_of_mem_zpowers hf hτ_smul
    simpa [AlgEquiv.smul_def] using hf_smul
  let eNonzero :
      {x : L // x ≠ 0} ≃ {u : Kˣ // τAlg (u : K) = (u : K)} := {
    toFun := fun x =>
      ⟨Units.mk0 (x.1 : K) (by
        intro hx
        apply x.2
        apply Subtype.ext
        exact hx),
        (IntermediateField.mem_fixedField_iff (H := H) (x.1 : K)).mp
          x.1.property τAlg (Subgroup.mem_zpowers τAlg)⟩
    invFun := fun u =>
      ⟨⟨(u.1 : K), hfixed_mem u.2⟩, by
        intro hzero
        apply Units.ne_zero u.1
        exact congrArg Subtype.val hzero⟩
    left_inv := by
      intro x
      apply Subtype.ext
      apply Subtype.ext
      rfl
    right_inv := by
      intro u
      apply Subtype.ext
      apply Units.ext
      rfl }
  let eUnits :
      Lˣ ≃ {u : Kˣ // τAlg (u : K) = (u : K)} :=
    unitsEquivNeZero.trans eNonzero
  have hfixedCardAlg :
      Nat.card {u : Kˣ // τAlg (u : K) = (u : K)} = p ^ (m : ℕ) - 1 := by
    have hcard := Nat.card_congr eUnits
    have hLcardNat : Nat.card L = p ^ (m : ℕ) := by
      simpa [Nat.card_eq_fintype_card] using hLcard
    have hLunits : Nat.card Lˣ = p ^ (m : ℕ) - 1 := by
      have h := Nat.card_eq_card_units_add_one L
      omega
    exact hcard.symm.trans hLunits
  have hfixedCard :
      Nat.card {u : Kˣ // τ (u : K) = (u : K)} = p ^ (m : ℕ) - 1 := by
    simpa [τAlg] using hfixedCardAlg
  exact ⟨m, m.pos, hKcard, by simpa [hLcard] using hτpow, hfixedCard⟩
set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
private theorem proposition_2_coordinate_square_iff_mem
    {F K : Type u} [RightNearField F] [Finite F]
    {p m : ℕ} [Fact (Nat.Prime p)]
    [Field K] [Finite K] [Algebra (ZMod p) K]
    (A : Subgroup Fˣ) (hA_index : A.index = 2)
    (e : F ≃+ K) (he1 : e 1 = 1)
    (hscalar : ∀ (x : F) (a : A),
      e (x * ((a : A) : Fˣ)) = e x * e (((a : A) : Fˣ) : F))
    (hm : 0 < m) (hKcard : Nat.card K = p ^ (2 * m)) :
    p ≠ 2 ∧ ∀ y : Fˣ, IsSquare (e (y : F)) ↔ y ∈ A := by
  let aCoord : A →* Kˣ := {
    toFun a := Units.mk0 (e (((a : A) : Fˣ) : F))
      ((e.map_ne_zero_iff).2 (Units.ne_zero ((a : A) : Fˣ)))
    map_one' := by
      apply Units.ext
      exact he1
    map_mul' := by
      intro a b
      apply Units.ext
      exact hscalar (((a : A) : Fˣ) : F) b }
  have haCoord_injective : Function.Injective aCoord := by
    intro a b hab
    apply Subtype.ext
    apply Units.ext
    apply e.injective
    exact congrArg Units.val hab
  let B : Subgroup Kˣ := aCoord.range
  have hBcard : Nat.card B = Nat.card A := by
    exact (Nat.card_congr (Equiv.ofInjective aCoord haCoord_injective)).symm
  have hunitcards : Nat.card Kˣ = Nat.card Fˣ := by
    rw [Nat.card_units, Nat.card_units, Nat.card_congr e.toEquiv]
  have hAcard := Subgroup.card_mul_index A
  rw [hA_index] at hAcard
  have hB_index : B.index = 2 := by
    have hBmul := Subgroup.card_mul_index B
    rw [hBcard, hunitcards, ← hAcard] at hBmul
    exact Nat.mul_left_cancel (Nat.card_pos (α := A)) hBmul
  have htwo_dvd_units : 2 ∣ Nat.card Kˣ := by
    refine ⟨Nat.card A, ?_⟩
    simpa [mul_comm] using hunitcards.trans hAcard.symm
  let Sq : Subgroup Kˣ := (powMonoidHom 2 : Kˣ →* Kˣ).range
  have hSq_index : Sq.index = 2 := by
    dsimp [Sq]
    rw [IsCyclic.index_powMonoidHom_range, Nat.gcd_eq_right_iff_dvd]
    exact htwo_dvd_units
  have hSq_le_B : Sq ≤ B := by
    rintro z ⟨w, rfl⟩
    exact Subgroup.sq_mem_of_index_two hB_index w
  have hB_le_Sq : B ≤ Sq := by
    have hrel := Subgroup.relIndex_mul_index hSq_le_B
    rw [hSq_index, hB_index] at hrel
    apply Subgroup.relIndex_eq_one.mp
    omega
  have hSqB : Sq = B := le_antisymm hSq_le_B hB_le_Sq
  have hp_ne_two : p ≠ 2 := by
    intro hp
    subst p
    have hFcard :=
      rightNearField_card_eq_two_mul_card_add_one_of_index_two A hA_index
    have hpow :
        2 ^ (2 * m) = 2 * Nat.card A + 1 := by
      rw [← hKcard, ← Nat.card_congr e.toEquiv]
      exact hFcard
    have hexp : 2 * m ≠ 0 := by omega
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hexp
    rw [hk, pow_succ] at hpow
    omega
  refine ⟨hp_ne_two, ?_⟩
  intro y
  let ey : Kˣ := Units.mk0 (e (y : F))
    ((e.map_ne_zero_iff).2 (Units.ne_zero y))
  have hsquare_iff : IsSquare (e (y : F)) ↔ ey ∈ Sq := by
    constructor
    · rintro ⟨z, hz⟩
      have hz_ne : z ≠ 0 := by
        intro hzero
        apply e.map_ne_zero_iff.2 (Units.ne_zero y)
        rw [hz, hzero, mul_zero]
      refine ⟨Units.mk0 z hz_ne, ?_⟩
      apply Units.ext
      simpa [ey, pow_two] using hz.symm
    · rintro ⟨z, hz⟩
      refine ⟨(z : K), ?_⟩
      have hval := congrArg Units.val hz
      simpa [ey, pow_two] using hval.symm
  have hB_iff : ey ∈ B ↔ y ∈ A := by
    constructor
    · rintro ⟨a, ha⟩
      have hay : ((a : A) : Fˣ) = y := by
        apply Units.ext
        apply e.injective
        exact congrArg Units.val ha
      rw [← hay]
      exact a.2
    · intro hy
      exact ⟨(⟨y, hy⟩ : A), rfl⟩
  rw [hsquare_iff, hSqB, hB_iff]
set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
private theorem proposition_2_semilinear_kernel_cases
    {F K : Type u} [RightNearField F] [Finite F]
    [Field K] [Finite K]
    (A : Subgroup Fˣ) (hA_index : A.index = 2) (e : F ≃+ K)
    (hscalar : ∀ (x : F) (a : A),
      e (x * ((a : A) : Fˣ)) = e x * e (((a : A) : Fˣ) : F))
    (σHom : (Fˣ)ᵐᵒᵖ →* (K ≃+* K))
    (hsemi : ∀ (x : F) (y : Fˣ),
      e (x * (y : F)) =
        σHom (MulOpposite.op y) (e x) * e (y : F)) :
    (∀ x y : F, x * y = y * x) ∨
      σHom.ker = A.map (MulEquiv.inv' Fˣ) := by
  let Aop : Subgroup (Fˣ)ᵐᵒᵖ := A.map (MulEquiv.inv' Fˣ)
  have hAop_index : Aop.index = 2 := by
    dsimp [Aop]
    rw [Subgroup.index_map_equiv]
    exact hA_index
  have hAop_ker : Aop ≤ σHom.ker := by
    intro u hu
    rcases hu with ⟨a, ha, rfl⟩
    apply MonoidHom.mem_ker.mpr
    apply RingEquiv.ext
    intro z
    obtain ⟨x, rfl⟩ := e.surjective z
    have hsemi_a := hsemi x a⁻¹
    have hscalar_a := hscalar x (⟨a⁻¹, A.inv_mem ha⟩ : A)
    have hea_ne : e ((a⁻¹ : Fˣ) : F) ≠ 0 := by
      intro hea
      apply Units.ne_zero a⁻¹
      apply e.injective
      simpa [map_zero] using hea
    exact mul_right_cancel₀ hea_ne (hsemi_a.symm.trans hscalar_a)
  have hrel := Subgroup.relIndex_mul_index hAop_ker
  have hp : (Aop.relIndex σHom.ker * σHom.ker.index).Prime := by
    rw [hrel, hAop_index]
    exact Nat.prime_two
  have hker_cases : σHom.ker = Aop ∨ σHom.ker = ⊤ := by
    rcases Nat.prime_mul_iff.mp hp with ⟨_, hindex_one⟩ | ⟨_, hrel_one⟩
    · exact Or.inr (Subgroup.index_eq_one.mp hindex_one)
    · exact Or.inl (le_antisymm
        (Subgroup.relIndex_eq_one.mp hrel_one) hAop_ker)
  rcases hker_cases with hker | hker
  · exact Or.inr hker
  · left
    have hσ : σHom = 1 := MonoidHom.ker_eq_top_iff.mp hker
    intro x y
    by_cases hx : x = 0
    · simp [hx]
    by_cases hy : y = 0
    · simp [hy]
    let ux : Fˣ := Units.mk0 x hx
    let uy : Fˣ := Units.mk0 y hy
    have hxy := hsemi x uy
    have hyx := hsemi y ux
    apply e.injective
    calc
      e (x * y) = e x * e y := by simpa [hσ, uy] using hxy
      _ = e y * e x := mul_comm _ _
      _ = e (y * x) := by simpa [hσ, ux] using hyx.symm
set_option maxHeartbeats 2000000 in
set_option backward.isDefEq.respectTransparency false in
private theorem proposition_2_center_card
    {F K : Type u} [RightNearField F] [Finite F]
    {p m : ℕ} [Fact (Nat.Prime p)]
    [Field K] [Finite K] [Algebra (ZMod p) K]
    (A : Subgroup Fˣ) (hA_cyclic : IsCyclic A) (hA_index : A.index = 2)
    (e : F ≃+ K)
    (hscalar : ∀ (x : F) (a : A),
      e (x * ((a : A) : Fˣ)) = e x * e (((a : A) : Fˣ) : F))
    (hclosure : Subring.closure
      (Set.range (algebraMap (ZMod p) K) ∪
        Set.range (fun a : A => e (((a : A) : Fˣ) : F))) = ⊤)
    (σHom : (Fˣ)ᵐᵒᵖ →* (K ≃+* K))
    (hsemi : ∀ (x : F) (y : Fˣ),
      e (x * (y : F)) =
        σHom (MulOpposite.op y) (e x) * e (y : F))
    (hker : σHom.ker = A.map (MulEquiv.inv' Fˣ))
    (u : (Fˣ)ᵐᵒᵖ) (hu : u ∉ A.map (MulEquiv.inv' Fˣ))
    (hτ_order : orderOf (σHom u) = 2)
    (hp_ne_two : p ≠ 2)
    (hKcard : Nat.card K = p ^ (2 * m))
    (hτpow : ∀ x : K, σHom u x = x ^ (p ^ m))
    (hsquare_mem : ∀ y : Fˣ, IsSquare (e (y : F)) ↔ y ∈ A)
    (hfixedCard :
      Nat.card {z : Kˣ // σHom u (z : K) = (z : K)} = p ^ m - 1) :
    Nat.card (Subgroup.center Fˣ) = p ^ m - 1 := by
  classical
  let Aop : Subgroup (Fˣ)ᵐᵒᵖ := A.map (MulEquiv.inv' Fˣ)
  let τ : K ≃+* K := σHom u
  change σHom.ker = Aop at hker
  change u ∉ Aop at hu
  have hAop_index : Aop.index = 2 := by
    dsimp [Aop]
    rw [Subgroup.index_map_equiv]
    exact hA_index
  have mem_Aop_iff (v : Fˣ) :
      MulOpposite.op v ∈ Aop ↔ v ∈ A := by
    dsimp [Aop]
    constructor
    · rintro ⟨a, ha, hav⟩
      have hav' : a⁻¹ = v := MulOpposite.op_injective hav
      rw [← hav']
      exact A.inv_mem ha
    · intro hv
      refine ⟨v⁻¹, A.inv_mem hv, ?_⟩
      simp
  have sigma_eq_of_not_mem {v w : (Fˣ)ᵐᵒᵖ}
      (hv : v ∉ Aop) (hw : w ∉ Aop) :
      σHom v = σHom w := by
    have hvw : v⁻¹ * w ∈ Aop := by
      rw [Aop.mul_mem_iff_of_index_two hAop_index, Aop.inv_mem_iff]
      simp [hv, hw]
    have hvw_ker : v⁻¹ * w ∈ σHom.ker := hker.symm ▸ hvw
    have hmap := MonoidHom.mem_ker.mp hvw_ker
    simp only [map_mul, map_inv] at hmap
    have h' : σHom w = σHom v := by
      simpa using (inv_mul_eq_iff_eq_mul.mp hmap)
    exact h'.symm
  have hτ_ne : τ ≠ 1 := by
    intro h
    change σHom u = 1 at h
    rw [h, orderOf_one] at hτ_order
    omega
  have hcenter_iff (y : Fˣ) :
      y ∈ Subgroup.center Fˣ ↔
        y ∈ A ∧ τ (e (y : F)) = e (y : F) := by
    constructor
    · intro hycenter
      have hyA : y ∈ A := by
        by_contra hyA
        have hyop : MulOpposite.op y ∉ Aop := by
          intro hyop
          exact hyA ((mem_Aop_iff y).mp hyop)
        have hsigmay : σHom (MulOpposite.op y) = τ :=
          sigma_eq_of_not_mem hyop hu
        have hcoord_fixed (a : A) :
            τ (e (((a : A) : Fˣ) : F)) =
              e (((a : A) : Fˣ) : F) := by
          have hsemi_y := hsemi (((a : A) : Fˣ) : F) y
          have hscalar_y := hscalar (y : F) a
          have hcommU :=
            (Subgroup.mem_center_iff.mp hycenter) ((a : A) : Fˣ)
          have hcommF := congrArg Units.val hcommU
          have heq :
              σHom (MulOpposite.op y)
                    (e (((a : A) : Fˣ) : F)) * e (y : F) =
                e (y : F) * e (((a : A) : Fˣ) : F) :=
            hsemi_y.symm.trans ((congrArg e hcommF).trans hscalar_y)
          rw [hsigmay] at heq
          apply mul_right_cancel₀
            ((e.map_ne_zero_iff).2 (Units.ne_zero y))
          calc
            τ (e (((a : A) : Fˣ) : F)) * e (y : F) =
                e (y : F) * e (((a : A) : Fˣ) : F) := heq
            _ = e (((a : A) : Fˣ) : F) * e (y : F) := mul_comm _ _
        let R : Subring K := {
          carrier := {x | τ x = x}
          zero_mem' := map_zero τ
          one_mem' := map_one τ
          add_mem' := by
            intro x y hx hy
            simp only [Set.mem_setOf_eq] at hx hy ⊢
            rw [map_add, hx, hy]
          mul_mem' := by
            intro x y hx hy
            simp only [Set.mem_setOf_eq] at hx hy ⊢
            rw [map_mul, hx, hy]
          neg_mem' := by
            intro x hx
            simp only [Set.mem_setOf_eq] at hx ⊢
            rw [map_neg, hx] }
        have hSle :
            Set.range (algebraMap (ZMod p) K) ∪
                Set.range (fun a : A => e (((a : A) : Fˣ) : F)) ⊆ R := by
          rintro z (hz | hz)
          · obtain ⟨r, rfl⟩ := hz
            change τ (algebraMap (ZMod p) K r) =
              algebraMap (ZMod p) K r
            simpa [Algebra.smul_def] using
              (ZMod.map_smul τ.toAddMonoidHom r (1 : K))
          · obtain ⟨a, rfl⟩ := hz
            exact hcoord_fixed a
        have hRtop : R = ⊤ := by
          apply top_unique
          rw [← hclosure]
          exact Subring.closure_le.mpr hSle
        have hτone : τ = 1 := by
          apply RingEquiv.ext
          intro (x : K)
          have hxR : x ∈ R := by simp [hRtop]
          exact hxR
        exact (hτ_ne hτone).elim
      refine ⟨hyA, ?_⟩
      let a : A := ⟨y, hyA⟩
      have hcommU := (Subgroup.mem_center_iff.mp hycenter) u.unop
      have hcommF := congrArg Units.val hcommU
      have hscalar_u := hscalar (u.unop : F) a
      have hsemi_u := hsemi (y : F) u.unop
      have heq :
          e (u.unop : F) * e (y : F) =
            τ (e (y : F)) * e (u.unop : F) :=
        hscalar_u.symm.trans ((congrArg e hcommF).trans hsemi_u)
      apply mul_right_cancel₀
        ((e.map_ne_zero_iff).2 (Units.ne_zero u.unop))
      calc
        τ (e (y : F)) * e (u.unop : F) =
            e (u.unop : F) * e (y : F) := heq.symm
        _ = e (y : F) * e (u.unop : F) := mul_comm _ _
    · rintro ⟨hyA, hyfix⟩
      rw [Subgroup.mem_center_iff]
      intro g
      by_cases hgA : g ∈ A
      · have hcomm :=
          hA_cyclic.isMulCommutative.is_comm.comm (⟨g, hgA⟩ : A) (⟨y, hyA⟩ : A)
        exact congrArg Subtype.val hcomm
      · have hgop : MulOpposite.op g ∉ Aop := by
          intro hgop
          exact hgA ((mem_Aop_iff g).mp hgop)
        have hsigmag : σHom (MulOpposite.op g) = τ :=
          sigma_eq_of_not_mem hgop hu
        apply Units.ext
        apply e.injective
        calc
          e ((g : F) * (y : F)) = e (g : F) * e (y : F) :=
            hscalar (g : F) (⟨y, hyA⟩ : A)
          _ = e (y : F) * e (g : F) := mul_comm _ _
          _ = τ (e (y : F)) * e (g : F) := by rw [hyfix]
          _ = e ((y : F) * (g : F)) := by
            rw [← hsigmag]
            exact (hsemi (y : F) g).symm
  let q := p ^ m
  have hq0 : q ≠ 0 := pow_ne_zero m (Fact.out : Nat.Prime p).ne_zero
  have hqodd : Odd q :=
    ((Fact.out : Nat.Prime p).odd_of_ne_two hp_ne_two).pow
  letI : Fintype K := Fintype.ofFinite K
  have hKcardF : Fintype.card K = q ^ 2 := by
    rw [Fintype.card_eq_nat_card, hKcard]
    simp [q, ← pow_mul, Nat.mul_comm]
  have hexp : Fintype.card K / 2 = (q - 1) * ((q + 1) / 2) := by
    have hqplus : 2 ∣ q + 1 := hqodd.add_one.two_dvd
    have hq2mod : q ^ 2 % 2 = 1 := Nat.odd_iff.mp hqodd.pow
    rw [hKcardF]
    apply Nat.mul_left_cancel (n := 2) (by omega)
    rw [Nat.two_mul_odd_div_two hq2mod]
    calc
      q ^ 2 - 1 = (q + 1) * (q - 1) := by
        simpa using Nat.sq_sub_sq q 1
      _ = (q - 1) * (q + 1) := Nat.mul_comm _ _
      _ = (q - 1) * (2 * ((q + 1) / 2)) := by
        rw [Nat.mul_div_cancel' hqplus]
      _ = 2 * ((q - 1) * ((q + 1) / 2)) := by ring
  letI : CharP K p := charP_of_injective_algebraMap' (ZMod p) p
  have hchar : ringChar K ≠ 2 := by
    rw [ringChar.eq K p]
    exact hp_ne_two
  have hfixed_square (z : Kˣ) (hz : τ (z : K) = (z : K)) :
      IsSquare (z : K) := by
    have hzpow : (z : K) ^ (q - 1) = 1 := by
      apply mul_right_cancel₀ (Units.ne_zero z)
      rw [pow_sub_one_mul hq0, one_mul]
      exact (hτpow (z : K)).symm.trans hz
    apply (FiniteField.isSquare_iff hchar (Units.ne_zero z)).2
    rw [hexp, pow_mul, hzpow, one_pow]
  let toFixed :
      Subgroup.center Fˣ → {z : Kˣ // τ (z : K) = (z : K)} :=
    fun y =>
      ⟨Units.mk0 (e ((y : Fˣ) : F))
          ((e.map_ne_zero_iff).2 (Units.ne_zero (y : Fˣ))),
        (hcenter_iff (y : Fˣ)).mp y.2 |>.2⟩
  let fromFixed :
      {z : Kˣ // τ (z : K) = (z : K)} → Subgroup.center Fˣ :=
    fun z =>
      let y : Fˣ :=
        Units.mk0 (e.symm ((z : Kˣ) : K))
          ((e.symm.map_ne_zero_iff).2 (Units.ne_zero (z : Kˣ)))
      ⟨y, (hcenter_iff y).mpr
        ⟨(hsquare_mem y).mp (by
            simpa [y] using hfixed_square (z : Kˣ) z.2),
          by simpa [y] using z.2⟩⟩
  let centerEquiv :
      Subgroup.center Fˣ ≃ {z : Kˣ // τ (z : K) = (z : K)} := {
    toFun := toFixed
    invFun := fromFixed
    left_inv := by
      intro y
      apply Subtype.ext
      apply Units.ext
      simp [toFixed, fromFixed]
    right_inv := by
      intro z
      apply Subtype.ext
      apply Units.ext
      simp [toFixed, fromFixed] }
  change Nat.card (Subgroup.center Fˣ) = p ^ m - 1
  calc
    Nat.card (Subgroup.center Fˣ) =
        Nat.card {z : Kˣ // τ (z : K) = (z : K)} :=
      Nat.card_congr centerEquiv
    _ = p ^ m - 1 := by simpa [τ] using hfixedCard
/-- The exceptional near-field from the displayed definition in the source.
The additive equivalence transports the near-field multiplication to GF(r²);
the right factor decides whether Frobenius is applied. -/
@[expose] public def IsDicksonIndexTwoModel
    (F : Type u) [RightNearField F] (p n : ℕ) : Prop :=
  Nat.Prime p ∧ p ≠ 2 ∧ 0 < n ∧
    let r := p ^ n
    ∃ _ : Fact (Nat.Prime p), ∃ e : F ≃+ GaloisField p (2 * n),
      e 1 = 1 ∧
      (∀ x y : F, IsSquare (e y) → e (x * y) = e x * e y) ∧
      (∀ x y : F, ¬ IsSquare (e y) →
        e (x * y) = (e x) ^ r * e y) ∧
      Nat.card (Subgroup.center Fˣ) = r - 1

/-- Peterfalvi, Appendix II, Proposition 2.

A finite near-field whose multiplicative group has a cyclic subgroup of index
two is either a field, or is the displayed exceptional near-field. In the
latter case the center of its multiplicative group has order r - 1. -/
public theorem proposition_2
    {F : Type u} [RightNearField F] [Finite F]
    (A : Subgroup Fˣ) (hA_cyclic : IsCyclic A) (hA_index : A.index = 2) :
    (∀ x y : F, x * y = y * x) ∨
      ∃ p n : ℕ, IsDicksonIndexTwoModel F p n := by
  -- Printed route: irreducibility of A by the cardinality contradiction;
  -- Appendix I, Proposition 2; the semilinear kernel dichotomy; Frobenius of
  -- order two; and the fixed-field calculation of the multiplicative center.
  obtain ⟨p, _, K, commRingK, finiteK, algebraK, e, hKisField, hp,
    _, he1, hscalar, hclosure⟩ :=
    proposition_2_appendixI_field_coordinates A hA_cyclic hA_index
  letI : CommRing K := commRingK
  letI : Finite K := finiteK
  letI : Algebra (ZMod p) K := algebraK
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  letI : Field K := hKisField.toField
  obtain ⟨σHom, hsemi⟩ :=
    proposition_2_semilinear_coordinates A hA_index e he1 hscalar hclosure
  rcases proposition_2_semilinear_kernel_cases
      A hA_index e hscalar σHom hsemi with hcomm | hker
  · exact Or.inl hcomm
  right
  let Aop : Subgroup (Fˣ)ᵐᵒᵖ := A.map (MulEquiv.inv' Fˣ)
  have hAop_index : Aop.index = 2 := by
    dsimp [Aop]
    rw [Subgroup.index_map_equiv]
    exact hA_index
  have hex_u : ∃ u : (Fˣ)ᵐᵒᵖ, u ∉ Aop := by
    by_contra h
    push Not at h
    have htop : Aop = ⊤ := by
      apply eq_top_iff.mpr
      intro x hx
      exact h x
    rw [htop] at hAop_index
    simp at hAop_index
  obtain ⟨u, hu⟩ := hex_u
  change σHom.ker = Aop at hker
  have hu_sq : u ^ 2 ∈ Aop :=
    Subgroup.sq_mem_of_index_two hAop_index u
  have hτ_sq : (σHom u) ^ 2 = 1 := by
    rw [← map_pow]
    exact MonoidHom.mem_ker.mp (hker.symm ▸ hu_sq)
  have hτ_ne : σHom u ≠ 1 := by
    intro h
    apply hu
    rw [← hker]
    exact MonoidHom.mem_ker.mpr h
  have hτ_order : orderOf (σHom u) = 2 := by
    apply orderOf_eq_prime
    · exact hτ_sq
    · exact hτ_ne
  obtain ⟨m, hm, hKcard, hτpow, hfixedCard⟩ :=
    finiteField_orderTwo_aut_coordinates (p := p) (K := K) (σHom u) hτ_order
  obtain ⟨hp_ne_two, hsquare_mem⟩ :=
    proposition_2_coordinate_square_iff_mem
      A hA_index e he1 hscalar hm hKcard
  have hcenterCard : Nat.card (Subgroup.center Fˣ) = p ^ m - 1 :=
    proposition_2_center_card A hA_cyclic hA_index e hscalar hclosure
      σHom hsemi hker u hu hτ_order hp_ne_two hKcard hτpow
      hsquare_mem hfixedCard
  let g : K ≃ₐ[ZMod p] GaloisField p (2 * m) :=
    GaloisField.algEquivGaloisField p (2 * m) hKcard
  let eG : F ≃+ GaloisField p (2 * m) := e.trans g.toAddEquiv
  have heG1 : eG 1 = 1 := by
    simp [eG, he1]
  have hsquare_e_iff (y : F) :
      IsSquare (eG y) ↔ IsSquare (e y) := by
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨g.symm z, ?_⟩
      have hz' := congrArg g.symm hz
      simpa [eG] using hz'
    · rintro ⟨z, hz⟩
      refine ⟨g z, ?_⟩
      have hz' := congrArg g hz
      simpa [eG] using hz'
  have sigma_eq_u_of_not_mem {v : (Fˣ)ᵐᵒᵖ} (hv : v ∉ Aop) :
      σHom v = σHom u := by
    have hvu : v⁻¹ * u ∈ Aop := by
      rw [Aop.mul_mem_iff_of_index_two hAop_index, Aop.inv_mem_iff]
      simp [hv, hu]
    have hvu_ker : v⁻¹ * u ∈ σHom.ker := hker.symm ▸ hvu
    have hmap := MonoidHom.mem_ker.mp hvu_ker
    simp only [map_mul, map_inv] at hmap
    have h' : σHom u = σHom v := by
      simpa using (inv_mul_eq_iff_eq_mul.mp hmap)
    exact h'.symm
  refine ⟨p, m, hp, hp_ne_two, hm, ?_⟩
  dsimp
  refine ⟨inferInstance, eG, heG1, ?_, ?_, hcenterCard⟩
  · intro x y hySquare
    by_cases hy0 : y = 0
    · simp [hy0]
    let uy : Fˣ := Units.mk0 y hy0
    have hyA : uy ∈ A := by
      apply (hsquare_mem uy).mp
      exact (hsquare_e_iff y).mp hySquare
    have hmul := hscalar x (⟨uy, hyA⟩ : A)
    have hmap := congrArg g hmul
    simpa [eG, uy] using hmap
  · intro x y hyNonsquare
    have hy0 : y ≠ 0 := by
      intro hy0
      subst y
      exact hyNonsquare ⟨0, by simp⟩
    let uy : Fˣ := Units.mk0 y hy0
    have hyNotA : uy ∉ A := by
      intro hyA
      apply hyNonsquare
      apply (hsquare_e_iff y).mpr
      exact (hsquare_mem uy).mpr hyA
    have huyop : MulOpposite.op uy ∉ Aop := by
      intro huyop
      rcases huyop with ⟨a, ha, hau⟩
      have hau' : a⁻¹ = uy := MulOpposite.op_injective hau
      apply hyNotA
      rw [← hau']
      exact A.inv_mem ha
    have hsigma : σHom (MulOpposite.op uy) = σHom u :=
      sigma_eq_u_of_not_mem huyop
    have hmul := hsemi x uy
    rw [hsigma, hτpow] at hmul
    have hmap := congrArg g hmul
    simpa [eG, uy] using hmap

end PFAppendixII
end CFSG.BenderSuzuki
