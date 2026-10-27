module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.theorem_1a
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.theorem_1b
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.theorem_1e_isomorphic_summands
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.lemma_12
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ElementaryAbelianAction
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.CentralizerCondition
import Mathlib.GroupTheory.Complement

namespace CFSG
end CFSG
open CFSG

/-!
# Higman's classification theorem: Type-B scalar action coordinates
-/

namespace CFSG.BenderSuzuki
namespace External
namespace Higman

open PFAppendixIII
open scoped Pointwise commutatorElement

universe u

set_option maxHeartbeats 800000 in
public theorem scalar_coordinates_of_fixed_point_free_cyclic_action
    {K E : Type u} [Group K] [Finite K] [Group E] [Finite E]
    [MulDistribMulAction K E]
    (hEcomm : IsMulCommutative E)
    (hEsq : ∀ x : E, x ^ 2 = 1)
    (hKcyclic : IsCyclic K)
    (hKfixedFree : ∀ k : K, k ≠ 1 → ∀ x : E, k • x = x → x = 1)
    (q : ℕ) (hKcard : Nat.card K = q - 1)
    (hEcard : Nat.card E = q) :
    ∃ (n : ℕ) (_ : n ≠ 0)
        (eK : K ≃* (BinaryGaloisField n)ˣ)
        (eE : E ≃* Multiplicative (BinaryGaloisField n)),
      Nat.card (BinaryGaloisField n) = q ∧
      ∀ k : K, ∀ x : E,
        (eE (k • x)).toAdd =
          (eK k : BinaryGaloisField n) * (eE x).toAdd := by
  classical
  let : IsMulCommutative E := hEcomm
  let : CommGroup E := IsMulCommutative.instCommGroup
  have hq_gt : 1 < q := by
    have hpos : 0 < Nat.card K := Nat.card_pos
    omega
  let : Nontrivial E :=
    Finite.one_lt_card_iff_nontrivial.mp (by simpa [hEcard] using hq_gt)
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsElementaryAbelian 2 E := by
    refine
      { toIsMulCommutative := inferInstance
        exponent_dvd_p :=
          Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_ }
    exact hEsq
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := K)
  let rho :=
    Theory.Representation.ofElementaryAbelianAction (A := K) (G := E) (p := 2)
  let rhoEquiv : K →* (Additive E ≃ₗ[ZMod 2] Additive E) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv
      (ZMod 2) (Additive E)).toMonoidHom.comp rho.asGroupHom
  let T : Additive E ≃ₗ[ZMod 2] Additive E := rhoEquiv g
  have hrho_val (k : K) (v : Additive E) :
      rhoEquiv k v = Additive.ofMul (k • v.toMul) := by
    change rho k v = Additive.ofMul (k • v.toMul)
    exact Theory.Representation.ofElementaryAbelianAction_apply k v
  have hT_val (v : Additive E) :
      T v = Additive.ofMul (g • v.toMul) := by
    exact hrho_val g v
  have hT_pow_val :
      ∀ j : ℕ, ∀ v : Additive E,
        (T ^ j) v = Additive.ofMul (g ^ j • v.toMul) := by
    intro j
    induction j with
    | zero => intro v; simp
    | succ j ih =>
        intro v
        rw [show T ^ (j + 1) = T * T ^ j by rw [pow_succ'],
          LinearEquiv.mul_apply, hT_val, ih]
        simp [pow_succ', smul_smul]
  have hT_irreducible :
      ∀ W : Submodule (ZMod 2) (Additive E),
        (∀ v : Additive E, v ∈ W → T v ∈ W) →
        W = ⊥ ∨ W = ⊤ := by
    intro W hW
    by_cases hWbot : W = ⊥
    · exact Or.inl hWbot
    right
    obtain ⟨vW, hv0W⟩ :=
      W.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr hWbot)
    let v : Additive E := vW
    have hvW : v ∈ W := vW.property
    have hv0 : v ≠ 0 := by
      intro hv
      apply hv0W
      apply Subtype.ext
      exact hv
    have hW_pow :
        ∀ j : ℕ, ∀ w : Additive E, w ∈ W → (T ^ j) w ∈ W := by
      intro j
      induction j with
      | zero => intro w hw; simpa using hw
      | succ j ih =>
          intro w hw
          rw [show T ^ (j + 1) = T * T ^ j by rw [pow_succ'],
            LinearEquiv.mul_apply]
          exact hW _ (ih w hw)
    let f : Option K → W
      | none => 0
      | some k =>
          ⟨Additive.ofMul (k • v.toMul), by
            obtain ⟨j, rfl⟩ := mem_powers_iff_mem_zpowers.mpr (hg k)
            have hmem := hW_pow j v hvW
            rw [hT_pow_val] at hmem
            exact hmem⟩
    have hf : Function.Injective f := by
      intro a b hab
      cases a with
      | none =>
          cases b with
          | none => rfl
          | some k =>
              exfalso
              have hzero : Additive.ofMul (k • v.toMul) = 0 := by
                exact (congrArg (fun z : W => (z : Additive E)) hab).symm
              have hkone : k • v.toMul = 1 := by
                apply Additive.ofMul.injective
                simpa using hzero
              have hvone : v.toMul = 1 := by
                calc
                  v.toMul = k⁻¹ • (k • v.toMul) := by simp [smul_smul]
                  _ = k⁻¹ • 1 := by rw [hkone]
                  _ = 1 := by simp
              apply hv0
              apply Additive.toMul.injective
              simpa using hvone
      | some k =>
          cases b with
          | none =>
              exfalso
              have hzero : Additive.ofMul (k • v.toMul) = 0 := by
                exact congrArg (fun z : W => (z : Additive E)) hab
              have hkone : k • v.toMul = 1 := by
                apply Additive.ofMul.injective
                simpa using hzero
              have hvone : v.toMul = 1 := by
                calc
                  v.toMul = k⁻¹ • (k • v.toMul) := by simp [smul_smul]
                  _ = k⁻¹ • 1 := by rw [hkone]
                  _ = 1 := by simp
              apply hv0
              apply Additive.toMul.injective
              simpa using hvone
          | some l =>
              congr 1
              have hact : k • v.toMul = l • v.toMul := by
                apply Additive.ofMul.injective
                exact congrArg (fun z : W => (z : Additive E)) hab
              have hfix : (l⁻¹ * k) • v.toMul = v.toMul := by
                calc
                  (l⁻¹ * k) • v.toMul = l⁻¹ • (k • v.toMul) := by
                    rw [mul_smul]
                  _ = l⁻¹ • (l • v.toMul) := by rw [hact]
                  _ = v.toMul := by simp [smul_smul]
              have hfactor : l⁻¹ * k = 1 := by
                by_contra hne
                have hvone :=
                  hKfixedFree (l⁻¹ * k) hne v.toMul hfix
                apply hv0
                apply Additive.toMul.injective
                simpa using hvone
              calc
                k = l * (l⁻¹ * k) := by group
                _ = l := by rw [hfactor]; simp
    have hcard_lower : q ≤ Nat.card W := by
      calc
        q = Nat.card K + 1 := by omega
        _ = Nat.card (Option K) := Finite.card_option.symm
        _ ≤ Nat.card W := Nat.card_le_card_of_injective f hf
    have hcard_upper : Nat.card W ≤ Nat.card (Additive E) :=
      Nat.card_le_card_of_injective W.subtype Subtype.val_injective
    have hEcard_add : Nat.card (Additive E) = q := by
      exact (Nat.card_congr Additive.toMul).trans hEcard
    have hWcard : Nat.card W = Nat.card (Additive E) := by
      apply Nat.le_antisymm hcard_upper
      simpa [hEcard_add] using hcard_lower
    have hWtop :
        W.toAddSubgroup = (⊤ : AddSubgroup (Additive E)) :=
      AddSubgroup.eq_top_of_card_eq W.toAddSubgroup hWcard
    apply Submodule.toAddSubgroup_injective
    simpa using hWtop
  obtain ⟨n, hnpos, lambda, coordinates, _basis,
      hEcardField, hlambda, hTcoordinates, _heigen, _hexpansion⟩ :=
    lemma5_irreducible_conjugate_eigenbasis T hT_irreducible
  have hrhoEquiv_injective : Function.Injective rhoEquiv := by
    intro k l hkl
    obtain ⟨x, hx⟩ := exists_ne (1 : E)
    have hact : k • x = l • x := by
      apply Additive.ofMul.injective
      calc
        Additive.ofMul (k • x) =
            rhoEquiv k (Additive.ofMul x) := (hrho_val k _).symm
        _ = rhoEquiv l (Additive.ofMul x) := by rw [hkl]
        _ = Additive.ofMul (l • x) := hrho_val l _
    have hfix : (l⁻¹ * k) • x = x := by
      calc
        (l⁻¹ * k) • x = l⁻¹ • (k • x) := by rw [mul_smul]
        _ = l⁻¹ • (l • x) := by rw [hact]
        _ = x := by simp [smul_smul]
    have hfactor : l⁻¹ * k = 1 := by
      by_contra hne
      exact hx (hKfixedFree (l⁻¹ * k) hne x hfix)
    calc
      k = l * (l⁻¹ * k) := by group
      _ = l := by rw [hfactor]; simp
  have hg_order : orderOf g = Nat.card K :=
    orderOf_eq_card_of_forall_mem_zpowers hg
  have hT_order : orderOf T = q - 1 := by
    calc
      orderOf T = orderOf g := by
        simpa [T] using orderOf_injective rhoEquiv hrhoEquiv_injective g
      _ = Nat.card K := hg_order
      _ = q - 1 := hKcard
  let F := BinaryGaloisField n
  let lambdaUnit : Fˣ := Units.mk0 lambda hlambda
  have hT_coordinate_pow : ∀ j : ℕ, ∀ alpha : F,
      (T ^ j) (coordinates alpha) =
        coordinates (((lambdaUnit ^ j : Fˣ) : F) * alpha) := by
    intro j
    induction j with
    | zero => intro alpha; simp
    | succ j ih =>
        intro alpha
        simpa only [pow_succ, LinearEquiv.mul_apply, Units.val_mul] using
          (calc
            (T ^ j) (T (coordinates alpha)) =
                (T ^ j) (coordinates (lambda * alpha)) := by
                  rw [hTcoordinates]
            _ = coordinates
                (((lambdaUnit ^ j : Fˣ) : F) * (lambda * alpha)) :=
              ih (lambda * alpha)
            _ = coordinates
                ((((lambdaUnit ^ j * lambdaUnit : Fˣ) : F) * alpha)) := by
              congr 1
              simp only [lambdaUnit, Units.val_mul, Units.val_mk0]
              rw [mul_assoc])
  have hT_dvd_lambda : orderOf T ∣ orderOf lambdaUnit := by
    apply (orderOf_dvd_iff_pow_eq_one).2
    apply LinearEquiv.ext
    intro x
    obtain ⟨alpha, rfl⟩ := coordinates.surjective x
    rw [hT_coordinate_pow]
    rw [pow_orderOf_eq_one]
    simp
  have hlambda_dvd_T : orderOf lambdaUnit ∣ orderOf T := by
    apply (orderOf_dvd_iff_pow_eq_one).2
    apply Units.ext
    have hpow := LinearEquiv.congr_fun (pow_orderOf_eq_one T)
      (coordinates (1 : F))
    rw [hT_coordinate_pow] at hpow
    simpa using coordinates.injective hpow
  have hlambda_order : orderOf lambdaUnit = q - 1 := by
    calc
      orderOf lambdaUnit = orderOf T :=
        Nat.dvd_antisymm hlambda_dvd_T hT_dvd_lambda
      _ = q - 1 := hT_order
  have hn : n ≠ 0 := Nat.ne_of_gt hnpos
  have hq_pow : q = 2 ^ n := by
    calc
      q = Nat.card E := hEcard.symm
      _ = Nat.card (Additive E) := rfl
      _ = 2 ^ n := hEcardField
  have hFcard : Nat.card F = q := by
    calc
      Nat.card F = 2 ^ n := GaloisField.card 2 n hn
      _ = q := hq_pow.symm
  have hlambda_units_card : Nat.card Fˣ = q - 1 := by
    rw [Nat.card_units, hFcard]
  have hlambda_generator : ∀ x : Fˣ,
      x ∈ Subgroup.zpowers lambdaUnit := by
    have htop : Subgroup.zpowers lambdaUnit = ⊤ := by
      rw [← Subgroup.card_eq_iff_eq_top, Nat.card_zpowers,
        hlambda_order, hlambda_units_card]
    intro x
    rw [htop]
    trivial
  let eK : K ≃* Fˣ :=
    mulEquivOfOrderOfEq hg hlambda_generator
      (hg_order.trans (hKcard.trans hlambda_order.symm))
  have heK_g : eK g = lambdaUnit := by
    exact mulEquivOfOrderOfEq_apply_gen _ _ _
  let eE : E ≃* Multiplicative F :=
    (MulEquiv.multiplicativeAdditive _).symm.trans
      coordinates.symm.toAddEquiv.toMultiplicative
  have heE_pow (j : ℕ) (x : E) :
      (eE (g ^ j • x)).toAdd =
        (((lambdaUnit ^ j : Fˣ) : F) * (eE x).toAdd) := by
    change coordinates.symm (Additive.ofMul (g ^ j • x)) =
      (((lambdaUnit ^ j : Fˣ) : F) *
        coordinates.symm (Additive.ofMul x))
    have hpow : (T ^ j) (Additive.ofMul x) =
        Additive.ofMul (g ^ j • x) := by
      simpa using hT_pow_val j (Additive.ofMul x)
    rw [← hpow]
    conv_lhs =>
      rw [← coordinates.apply_symm_apply (Additive.ofMul x)]
    rw [hT_coordinate_pow, coordinates.symm_apply_apply]
  have heE_action (k : K) (x : E) :
      (eE (k • x)).toAdd =
        ((eK k : F) * (eE x).toAdd) := by
    obtain ⟨j, rfl⟩ := mem_powers_iff_mem_zpowers.mpr (hg k)
    simpa [map_pow, heK_g] using heE_pow j x
  exact ⟨n, hn, eK, eE, by simpa [F] using hFcard, heE_action⟩

set_option maxHeartbeats 800000 in
public theorem quotient_scalar_coordinates_from_isomorphic_summands
    {K E : Type u} [Group K] [Finite K] [Group E] [Finite E]
    [MulDistribMulAction K E]
    (hEcomm : IsMulCommutative E)
    (hEsq : ∀ x : E, x ^ 2 = 1)
    (hKcyclic : IsCyclic K)
    (hKfixedFree : ∀ k : K, k ≠ 1 → ∀ x : E, k • x = x → x = 1)
    (q : ℕ) (hKcard : Nat.card K = q - 1)
    (U V : Subgroup E)
    (hUinv : IsXInvariantSubgroup K U)
    (hVinv : IsXInvariantSubgroup K V)
    (hUcard : Nat.card U = q)
    (_hVcard : Nat.card V = q)
    (hUVinf : U ⊓ V = ⊥)
    (hUVsup : U ⊔ V = ⊤)
    (e : U ≃* V)
    (he : ∀ k : K, ∀ u : U,
      ((e ⟨k • (u : E), (hUinv k (u : E)).mp u.property⟩ : V) : E) =
        k • ((e u : V) : E)) :
    ∃ (n : ℕ) (_ : n ≠ 0)
        (eK : K ≃* (BinaryGaloisField n)ˣ)
        (eQ : E ≃*
          Multiplicative (BinaryGaloisField n × BinaryGaloisField n)),
      Nat.card (BinaryGaloisField n) = q ∧
      ∀ k : K, ∀ x : E,
        (eQ (k • x)).toAdd =
          ((eK k : BinaryGaloisField n) * (eQ x).toAdd.1,
            (eK k : BinaryGaloisField n) * (eQ x).toAdd.2) := by
  classical
  letI : IsMulCommutative E := hEcomm
  letI : CommGroup E := IsMulCommutative.instCommGroup
  letI : IsInvariant K E U := ⟨hUinv⟩
  have hUcomm : IsMulCommutative U := inferInstance
  have hUsq : ∀ u : U, u ^ 2 = 1 := by
    intro u
    apply Subtype.ext
    exact hEsq (u : E)
  have hUfixedFree : ∀ k : K, k ≠ 1 →
      ∀ u : U, k • u = u → u = 1 := by
    intro k hk u hu
    apply Subtype.ext
    exact hKfixedFree k hk (u : E) (congrArg Subtype.val hu)
  rcases scalar_coordinates_of_fixed_point_free_cyclic_action
      hUcomm hUsq hKcyclic hUfixedFree q hKcard hUcard with
    ⟨n, hn, eK, eU, hFcard, heU_action⟩
  let F := BinaryGaloisField n
  letI : IsInvariant K E V := ⟨hVinv⟩
  let eV : V ≃* Multiplicative F := e.symm.trans eU
  have he_subtype (k : K) (u : U) : e (k • u) = k • e u := by
    apply Subtype.ext
    exact he k u
  have he_symm_subtype (k : K) (v : V) :
      e.symm (k • v) = k • e.symm v := by
    apply e.injective
    rw [e.apply_symm_apply, he_subtype, e.apply_symm_apply]
  have heV_action (k : K) (v : V) :
      (eV (k • v)).toAdd =
        ((eK k : F) * (eV v).toAdd) := by
    simpa [eV, he_symm_subtype] using heU_action k (e.symm v)
  letI : U.Normal := Subgroup.normal_of_isMulCommutative U
  have hUVdisjoint : Disjoint U V := disjoint_iff.mpr hUVinf
  have hUVmul : (U : Set E) * (V : Set E) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    have hx : x ∈ U ⊔ V := by rw [hUVsup]; simp
    rcases (Subgroup.mem_sup_of_normal_left (x := x) (s := U) (t := V)).1 hx with
      ⟨u, hu, v, hv, huv⟩
    exact ⟨u, hu, v, hv, huv⟩
  have hUVcomp : U.IsComplement' V :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hUVdisjoint hUVmul
  let decompFun : U × V → E := fun uv => (uv.1 : E) * (uv.2 : E)
  have hdecompBijective : Function.Bijective decompFun := hUVcomp
  let decompEquiv : U × V ≃ E :=
    Equiv.ofBijective decompFun hdecompBijective
  let decomp : U × V ≃* E :=
    { decompEquiv with
      map_mul' := by
        intro a b
        change ((a.1 * b.1 : U) : E) * ((a.2 * b.2 : V) : E) =
          ((a.1 : E) * (a.2 : E)) * ((b.1 : E) * (b.2 : E))
        rw [Subgroup.coe_mul, Subgroup.coe_mul]
        ac_rfl }
  let pairMultiplicative :
      Multiplicative F × Multiplicative F ≃*
        Multiplicative (F × F) := MulEquiv.refl _
  let eQ : E ≃* Multiplicative (F × F) :=
    decomp.symm.trans ((eU.prodCongr eV).trans pairMultiplicative)
  have hscalar (k : K) (x : E) :
      (eQ (k • x)).toAdd =
        ((eK k : F) * (eQ x).toAdd.1,
          (eK k : F) * (eQ x).toAdd.2) := by
    obtain ⟨⟨u, v⟩, rfl⟩ := decomp.surjective x
    have hact : k • decomp (u, v) = decomp (k • u, k • v) := by
      change k • ((u : E) * (v : E)) =
        ((k • u : U) : E) * ((k • v : V) : E)
      exact smul_mul' k (u : E) (v : E)
    rw [hact]
    simp only [eQ, MulEquiv.trans_apply, decomp.symm_apply_apply]
    change ((eU (k • u)).toAdd, (eV (k • v)).toAdd) =
      ((eK k : F) * (eU u).toAdd, (eK k : F) * (eV v).toAdd)
    rw [heU_action, heV_action]
  exact ⟨n, hn, eK, eQ, by simpa [F] using hFcard, hscalar⟩

set_option maxHeartbeats 800000 in
public theorem theorem1_isomorphic_summands_scalar_coordinates
    {K P : Type u} [Group K] [Group P] [MulDistribMulAction K P]
    (hP : IsSuzukiTwoGroup P)
    (hKcyclic : IsCyclic K) (hKfaithful : FaithfulSMul K P)
    (hKregular : ActionRegularOn K P (involutions P))
    (hIso : Theorem1IsomorphicSummands K P) :
    ∃ (n : ℕ) (_ : n ≠ 0)
        (theta : BinaryGaloisField n ≃+* BinaryGaloisField n)
        (eK : K ≃* (BinaryGaloisField n)ˣ)
        (eQ : (P ⧸ Subgroup.center P) ≃*
          Multiplicative (BinaryGaloisField n × BinaryGaloisField n))
        (eZ : Subgroup.center P ≃*
          Multiplicative (BinaryGaloisField n)),
      (∃ r : ℕ, Odd r ∧ 0 < r ∧
        ∀ x : BinaryGaloisField n, theta^[r] x = x) ∧
      (∀ k : K, ∀ p : P,
        (eQ (QuotientGroup.mk' (Subgroup.center P) (k • p))).toAdd =
          ((eK k : BinaryGaloisField n) *
              (eQ (QuotientGroup.mk' (Subgroup.center P) p)).toAdd.1,
            (eK k : BinaryGaloisField n) *
              (eQ (QuotientGroup.mk' (Subgroup.center P) p)).toAdd.2)) ∧
      ∀ k : K, ∀ z : BinaryGaloisField n,
        k • ((eZ.symm (Multiplicative.ofAdd z) : Subgroup.center P) : P) =
          ((eZ.symm (Multiplicative.ofAdd
            ((eK k : BinaryGaloisField n) *
              theta (eK k : BinaryGaloisField n) * z)) :
                Subgroup.center P) : P) := by
  classical
  letI : Finite P := finite_of_isSuzukiTwoGroup hP
  letI : FaithfulSMul K P := hKfaithful
  letI : Finite K := Finite.of_injective
    (MulDistribMulAction.toMulAut K P) (by
      intro k l hkl
      apply FaithfulSMul.eq_of_smul_eq_smul (α := P)
      intro p
      exact congrArg (fun f : MulAut P => f p) hkl)
  have hB : IsSuzukiTwoTypeB (⊤ : Subgroup P) :=
    theorem1_typeB_of_isomorphic_summands
      hP hKcyclic hKfaithful hKregular hIso
  let q := Nat.card (Subgroup.center P)
  have hcenterExp : ∀ z : Subgroup.center P, z ^ 2 = 1 :=
    (theorem1b_typeB_data hB).2.1
  have hinvolutions := (theorem1_involutions_center hP).1
  let involEquiv : {x : P // x ∈ involutions P} ≃
      {z : Subgroup.center P // z ≠ 1} :=
    { toFun := fun x =>
        ⟨⟨x, (by
          have hx := (Set.ext_iff.mp hinvolutions (x : P)).mp x.property
          exact hx.1)⟩,
          fun hz => x.property.ne_one (congrArg Subtype.val hz)⟩
      invFun := fun z =>
        ⟨z, by
          rw [hinvolutions]
          exact ⟨z.1.property, fun hz => z.2 (Subtype.ext hz)⟩⟩
      left_inv := by intro x; apply Subtype.ext; rfl
      right_inv := by intro z; apply Subtype.ext; apply Subtype.ext; rfl }
  have hinvolutionCard :
      Nat.card {x : P // x ∈ involutions P} = q - 1 := by
    calc
      Nat.card {x : P // x ∈ involutions P} =
          Nat.card {z : Subgroup.center P // z ≠ 1} :=
        Nat.card_congr involEquiv
      _ = Nat.card (Subgroup.center P) - 1 := by
        letI : Fintype (Subgroup.center P) := Fintype.ofFinite _
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
        simp
      _ = q - 1 := rfl
  obtain ⟨x0, _y0, hx0, _hy0, _hxy0⟩ := hP.2.2.1
  let orbit : K → {x : P // x ∈ involutions P} :=
    fun k => ⟨k • x0, hKregular.1 x0 hx0 k⟩
  have horbitInjective : Function.Injective orbit := by
    intro k l hkl
    have heq : k • x0 = l • x0 := congrArg Subtype.val hkl
    rcases hKregular.2 x0 hx0 (k • x0)
        (hKregular.1 x0 hx0 k) with ⟨a, _ha, huniq⟩
    exact (huniq k rfl).trans (huniq l heq).symm
  have horbitSurjective : Function.Surjective orbit := by
    rintro ⟨y, hy⟩
    rcases hKregular.2 x0 hx0 y hy with ⟨k, hk, _huniq⟩
    exact ⟨k, Subtype.ext hk.symm⟩
  have hKcard : Nat.card K = q - 1 := by
    calc
      Nat.card K = Nat.card {x : P // x ∈ involutions P} :=
        Nat.card_congr (Equiv.ofBijective orbit
          ⟨horbitInjective, horbitSurjective⟩)
      _ = q - 1 := hinvolutionCard
  obtain ⟨hQAction, U, V, hU, hV, eUV, hQAction_mk,
      hUcard, hVcard, hUVinf, hUVsup, heUV⟩ :=
    hIso
  letI : MulDistribMulAction K (P ⧸ Subgroup.center P) := hQAction
  have hQfixedFree : ∀ k : K, k ≠ 1 →
      ∀ x : P ⧸ Subgroup.center P,
        @SMul.smul K (P ⧸ Subgroup.center P)
          hQAction.toMulAction.toSMul k x = x → x = 1 := by
    intro k hk x hfix
    obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective
      (Subgroup.center P) x
    by_contra hmk
    have hpNotCenter : p ∉ Subgroup.center P := by
      intro hp
      exact hmk ((QuotientGroup.eq_one_iff p).2 hp)
    have hpNe : p ≠ 1 := by
      intro hp
      apply hpNotCenter
      rw [hp]
      exact (Subgroup.center P).one_mem
    have hpSqCenter : p ^ 2 ∈ Subgroup.center P :=
      (theorem1b_typeB_data hB).2.2 p
    have hpSqNe : p ^ 2 ≠ 1 := by
      intro hpSq
      have hpInv : IsInvolution p := ⟨hpNe, hpSq⟩
      apply hpNotCenter
      rw [Subgroup.mem_center_iff]
      intro y
      exact (hB.commute_of_isInvolution (by simp) hpInv (by simp)).eq.symm
    have hpSqInv : IsInvolution (p ^ 2) := by
      refine ⟨hpSqNe, ?_⟩
      let z : Subgroup.center P := ⟨p ^ 2, hpSqCenter⟩
      exact congrArg Subtype.val (hcenterExp z)
    have hquotEq : QuotientGroup.mk' (Subgroup.center P) (k • p) =
        QuotientGroup.mk' (Subgroup.center P) p := by
      rw [← hQAction_mk]
      exact hfix
    have hdiffCenter : (k • p) / p ∈ Subgroup.center P :=
      QuotientGroup.eq_iff_div_mem.mp hquotEq
    let z : Subgroup.center P := ⟨(k • p) / p, hdiffCenter⟩
    have hzSq : ((z : P) ^ 2) = 1 :=
      congrArg Subtype.val (hcenterExp z)
    have hkP : k • p = (z : P) * p := by
      dsimp [z]
      rw [div_eq_mul_inv]
      group
    have hfixSq : k • (p ^ 2) = p ^ 2 := by
      calc
        k • (p ^ 2) = (k • p) ^ 2 := by
          exact map_pow (MulDistribMulAction.toMulAut K P k) p 2
        _ = ((z : P) * p) ^ 2 := by rw [hkP]
        _ = (z : P) ^ 2 * p ^ 2 := by
          exact (Commute.symm
            (Subgroup.mem_center_iff.mp z.property p)).mul_pow 2
        _ = p ^ 2 := by rw [hzSq, one_mul]
    rcases hKregular.2 (p ^ 2) hpSqInv (p ^ 2) hpSqInv with
      ⟨a, _ha, huniq⟩
    have hkA : k = a := huniq k hfixSq.symm
    have hOneA : (1 : K) = a := huniq 1 (by simp)
    exact hk (hkA.trans hOneA.symm)
  have hQdata := theorem1_center_quotient_orders_and_exponent hP
  rcases @quotient_scalar_coordinates_from_isomorphic_summands
      K (P ⧸ Subgroup.center P) _ _ _ _ hQAction
      hQdata.1 hQdata.2.1 hKcyclic hQfixedFree q hKcard
      U V hU hV hUcard hVcard hUVinf hUVsup eUV heUV with
    ⟨n, hn, eKQ, eQ, hFcard, hQscalar⟩
  letI : IsInvariant K P (Subgroup.center P) := center_isInvariant
  have hCenterFixedFree : ∀ k : K, k ≠ 1 →
      ∀ z : Subgroup.center P, k • z = z → z = 1 := by
    intro k hk z hfix
    by_cases hz : z = 1
    · exact hz
    have hzInvP : IsInvolution (z : P) := by
      exact ⟨fun h => hz (Subtype.ext h),
        congrArg Subtype.val (hcenterExp z)⟩
    rcases hKregular.2 (z : P) hzInvP (z : P) hzInvP with
      ⟨a, _ha, huniq⟩
    have hkFix : k • (z : P) = (z : P) := by
      exact congrArg Subtype.val hfix
    have hkA : k = a := huniq k hkFix.symm
    have hOneA : (1 : K) = a := huniq 1 (by simp)
    exact False.elim (hk (hkA.trans hOneA.symm))
  have hCenterComm : IsMulCommutative (Subgroup.center P) := by
    exact ⟨⟨fun x y => Subtype.ext
      (Subgroup.mem_center_iff.mp x.property (y : P)).symm⟩⟩
  rcases scalar_coordinates_of_fixed_point_free_cyclic_action
      hCenterComm hcenterExp hKcyclic hCenterFixedFree q hKcard rfl with
    ⟨m, hm, eKZ, eZ, hFmcard, hZscalar⟩
  have hpowEq : 2 ^ n = 2 ^ m := by
    calc
      2 ^ n = Nat.card (BinaryGaloisField n) :=
        (GaloisField.card 2 n hn).symm
      _ = q := hFcard
      _ = Nat.card (BinaryGaloisField m) := hFmcard.symm
      _ = 2 ^ m := GaloisField.card 2 m hm
  have hnm : n = m := Nat.pow_right_injective (by norm_num) hpowEq
  subst m
  rcases hB with
    ⟨nB, hnB, thetaB, epsilonB, tripleLift, cocycle, hepsilonB,
      hperiodB, hanisotropicB, haddLeft, haddRight, hdiag,
      hmem, hone, hsurj, hinj, hmul⟩
  let FB := BinaryGaloisField nB
  have hzeroLeft : ∀ a b : FB, cocycle 0 0 a b = 0 := by
    intro a b
    have h := haddLeft 0 0 0 0 a b
    simpa only [zero_add, CharTwo.add_self_eq_zero] using h
  have hzeroRight : ∀ a b : FB, cocycle a b 0 0 = 0 := by
    intro a b
    have h := haddRight a b 0 0 0 0
    simpa only [zero_add, CharTwo.add_self_eq_zero] using h
  let centerMap : Multiplicative FB →* Subgroup.center P :=
    { toFun := fun c =>
        ⟨tripleLift c.toAdd 0 0, by
          rw [Subgroup.mem_center_iff]
          intro x
          rcases hsurj x (Subgroup.mem_top x) with ⟨d, a, b, hx⟩
          rw [hx, hmul, hmul, hzeroLeft, hzeroRight]
          simp [add_comm]⟩
      map_one' := by
        apply Subtype.ext
        simpa using hone
      map_mul' := by
        intro c d
        apply Subtype.ext
        change tripleLift (c.toAdd + d.toAdd) 0 0 =
          tripleLift c.toAdd 0 0 * tripleLift d.toAdd 0 0
        rw [hmul, hzeroRight]
        simp }
  have hcenterMapInjective : Function.Injective centerMap := by
    intro c d hEq
    apply Multiplicative.toAdd.injective
    have hval := congrArg
      (fun x : Subgroup.center P => (x : P)) hEq
    exact (hinj c.toAdd 0 0 d.toAdd 0 0 hval).1
  have hcenterMapSurjective : Function.Surjective centerMap := by
    intro x
    rcases hsurj (x : P) (Subgroup.mem_top x) with ⟨c, a, b, hx⟩
    have hcocycleSymm :
        ∀ e f : FB, cocycle a b e f = cocycle e f a b := by
      intro e f
      have hcomm :=
        Subgroup.mem_center_iff.mp x.property (tripleLift 0 e f)
      have hcommEq :
          tripleLift c a b * tripleLift 0 e f =
            tripleLift 0 e f * tripleLift c a b := by
        simpa [hx] using hcomm.symm
      rw [hmul, hmul] at hcommEq
      have hcoord := (hinj _ _ _ _ _ _ hcommEq).1
      have hcoord' :
          c + 0 + cocycle a b e f =
            c + 0 + cocycle e f a b := by
        calc
          c + 0 + cocycle a b e f =
              0 + c + cocycle e f a b := hcoord
          _ = c + 0 + cocycle e f a b := by abel
      exact add_left_cancel hcoord'
    have hpolar : ∀ e f : FB,
        a * thetaB e + e * thetaB a +
            epsilonB * (a * thetaB f + e * thetaB b) +
            b * thetaB f + f * thetaB b = 0 := by
      intro e f
      calc
        a * thetaB e + e * thetaB a +
              epsilonB * (a * thetaB f + e * thetaB b) +
              b * thetaB f + f * thetaB b =
            ((a + e) * thetaB (a + e) +
              epsilonB * (a + e) * thetaB (b + f) +
              (b + f) * thetaB (b + f)) +
              (a * thetaB a + epsilonB * a * thetaB b + b * thetaB b) +
              (e * thetaB e + epsilonB * e * thetaB f + f * thetaB f) := by
                rw [map_add, map_add]
                ring_nf
                simp only [CharTwo.two_eq_zero, mul_zero, add_zero]
        _ = cocycle (a + e) (b + f) (a + e) (b + f) +
              cocycle a b a b + cocycle e f e f := by
                rw [hdiag, hdiag, hdiag]
        _ = (cocycle a b a b + cocycle a b e f +
              (cocycle e f a b + cocycle e f e f)) +
              cocycle a b a b + cocycle e f e f := by
                rw [haddLeft, haddRight, haddRight]
        _ = 0 := by
          rw [hcocycleSymm e f]
          calc
            (cocycle a b a b + cocycle e f a b +
                (cocycle e f a b + cocycle e f e f)) +
                cocycle a b a b + cocycle e f e f =
              (cocycle a b a b + cocycle a b a b) +
                (cocycle e f a b + cocycle e f a b) +
                (cocycle e f e f + cocycle e f e f) := by abel
            _ = 0 := by
              simp only [CharTwo.add_self_eq_zero]
    have hab : a = 0 ∧ b = 0 := by
      by_cases ha : a = 0
      · subst a
        by_cases hb : b = 0
        · exact ⟨rfl, hb⟩
        · have h := hpolar 1 0
          simp only [map_zero, map_one, zero_mul, one_mul, mul_zero,
            add_zero, zero_add] at h
          exact False.elim
            ((mul_ne_zero hepsilonB ((map_ne_zero thetaB).mpr hb)) h)
      · by_cases hb : b = 0
        · subst b
          have h := hpolar 0 1
          simp only [map_zero, map_one, zero_mul, mul_zero,
            add_zero, zero_add] at h
          have h' : epsilonB * a = 0 := by simpa [mul_assoc] using h
          exact False.elim ((mul_ne_zero hepsilonB ha) h')
        · have h := hpolar a 0
          simp only [map_zero, mul_zero, add_zero,
            CharTwo.add_self_eq_zero, zero_add] at h
          have h' : epsilonB * a * thetaB b = 0 := by
            simpa [mul_assoc] using h
          exact False.elim
            ((mul_ne_zero (mul_ne_zero hepsilonB ha)
              ((map_ne_zero thetaB).mpr hb)) h')
    rcases hab with ⟨rfl, rfl⟩
    refine ⟨Multiplicative.ofAdd c, ?_⟩
    apply Subtype.ext
    exact hx.symm
  let eNatZ : Subgroup.center P ≃* Multiplicative FB :=
    (MulEquiv.ofBijective centerMap
      ⟨hcenterMapInjective, hcenterMapSurjective⟩).symm
  have hcenterCardB : Nat.card (Subgroup.center P) = 2 ^ nB := by
    calc
      Nat.card (Subgroup.center P) = Nat.card (Multiplicative FB) :=
        Nat.card_congr eNatZ.toEquiv
      _ = Nat.card FB := rfl
      _ = 2 ^ nB := GaloisField.card 2 nB hnB
  have hpowEqB : 2 ^ nB = 2 ^ n := by
    calc
      2 ^ nB = Nat.card (Subgroup.center P) := hcenterCardB.symm
      _ = q := rfl
      _ = Nat.card (BinaryGaloisField n) := hFcard.symm
      _ = 2 ^ n := GaloisField.card 2 n hn
  have hnBn : nB = n := Nat.pow_right_injective (by norm_num) hpowEqB
  subst nB
  let tripleFun : FB × FB × FB → P := fun cab =>
    tripleLift cab.1 cab.2.1 cab.2.2
  have htripleBijective : Function.Bijective tripleFun := by
    constructor
    · intro cab dbf hEq
      rcases hinj cab.1 cab.2.1 cab.2.2
          dbf.1 dbf.2.1 dbf.2.2 hEq with ⟨h1, h2, h3⟩
      exact Prod.ext h1 (Prod.ext h2 h3)
    · intro x
      rcases hsurj x (Subgroup.mem_top x) with ⟨c, a, b, hx⟩
      exact ⟨(c, a, b), hx.symm⟩
  let tripleEquiv : FB × FB × FB ≃ P :=
    Equiv.ofBijective tripleFun htripleBijective
  have htripleEquiv_apply (c a b : FB) :
      tripleEquiv (c, a, b) = tripleLift c a b := rfl
  let piNat : P →* Multiplicative (FB × FB) :=
    { toFun := fun p => Multiplicative.ofAdd (tripleEquiv.symm p).2
      map_one' := by
        apply Multiplicative.ofAdd.injective
        have hcoords : tripleEquiv.symm (1 : P) = (0, 0, 0) := by
          apply tripleEquiv.injective
          rw [tripleEquiv.apply_symm_apply, htripleEquiv_apply, hone]
        rw [hcoords]
        rfl
      map_mul' := by
        intro x y
        obtain ⟨⟨c, a, b⟩, rfl⟩ := tripleEquiv.surjective x
        obtain ⟨⟨d, e, f⟩, rfl⟩ := tripleEquiv.surjective y
        simp only [tripleEquiv.symm_apply_apply]
        rw [htripleEquiv_apply, htripleEquiv_apply]
        change Multiplicative.ofAdd
            (tripleEquiv.symm
              (tripleLift c a b * tripleLift d e f)).2 =
          Multiplicative.ofAdd ((a, b) + (e, f))
        apply Multiplicative.ofAdd.injective
        rw [hmul]
        have hcoords : tripleEquiv.symm
            (tripleLift (c + d + cocycle a b e f) (a + e) (b + f)) =
              (c + d + cocycle a b e f, a + e, b + f) := by
          apply tripleEquiv.injective
          rw [tripleEquiv.apply_symm_apply, htripleEquiv_apply]
        rw [hcoords]
        rfl }
  have hpiNat_ker : piNat.ker = Subgroup.center P := by
    ext p
    constructor
    · intro hp
      have hpOne : piNat p = 1 := MonoidHom.mem_ker.mp hp
      let cab := tripleEquiv.symm p
      have hab : cab.2 = 0 := by
        apply Multiplicative.ofAdd.injective
        simpa [piNat, cab] using hpOne
      have ha : cab.2.1 = 0 := congrArg Prod.fst hab
      have hb : cab.2.2 = 0 := congrArg Prod.snd hab
      have hpCoord : p = tripleLift cab.1 cab.2.1 cab.2.2 := by
        exact (tripleEquiv.apply_symm_apply p).symm
      rw [hpCoord, ha, hb]
      exact (centerMap (Multiplicative.ofAdd cab.1)).property
    · intro hp
      rcases hcenterMapSurjective ⟨p, hp⟩ with ⟨c, hc⟩
      apply MonoidHom.mem_ker.mpr
      have hpEq : p = tripleLift c.toAdd 0 0 := by
        exact congrArg Subtype.val hc.symm
      rw [hpEq]
      change Multiplicative.ofAdd
          (tripleEquiv.symm (tripleLift c.toAdd 0 0)).2 = 1
      have hcoords : tripleEquiv.symm (tripleLift c.toAdd 0 0) =
          (c.toAdd, 0, 0) := by
        apply tripleEquiv.injective
        rw [tripleEquiv.apply_symm_apply, htripleEquiv_apply]
      rw [hcoords]
      rfl
  have hpiNat_surj : Function.Surjective piNat := by
    intro ab
    let p := tripleLift 0 ab.toAdd.1 ab.toAdd.2
    refine ⟨p, ?_⟩
    apply Multiplicative.ofAdd.injective
    change (tripleEquiv.symm p).2 = ab.toAdd
    have hcoords : tripleEquiv.symm p =
        (0, ab.toAdd.1, ab.toAdd.2) := by
      apply tripleEquiv.injective
      rw [tripleEquiv.apply_symm_apply, htripleEquiv_apply]
    rw [hcoords]
  let eNatQ : (P ⧸ Subgroup.center P) ≃*
      Multiplicative (FB × FB) :=
    (QuotientGroup.quotientMulEquivOfEq hpiNat_ker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective piNat hpiNat_surj)
  have heNatQ_mk (p : P) :
      eNatQ (QuotientGroup.mk' (Subgroup.center P) p) = piNat p := by
    change QuotientGroup.kerLift piNat
        (QuotientGroup.quotientMulEquivOfEq hpiNat_ker.symm
          (QuotientGroup.mk' (Subgroup.center P) p)) = piNat p
    calc
      QuotientGroup.kerLift piNat
          (QuotientGroup.quotientMulEquivOfEq hpiNat_ker.symm
            (QuotientGroup.mk' (Subgroup.center P) p)) =
        QuotientGroup.kerLift piNat (QuotientGroup.mk' piNat.ker p) := by
          exact congrArg (QuotientGroup.kerLift piNat)
            (QuotientGroup.quotientMulEquivOfEq_mk hpiNat_ker.symm p)
      _ = piNat p := QuotientGroup.kerLift_mk piNat p
  have hpolarCross :
      cocycle 1 0 0 1 + cocycle 0 1 1 0 = epsilonB := by
    have hsplitLeft :
        cocycle 1 1 1 1 = cocycle 1 0 1 1 + cocycle 0 1 1 1 := by
      simpa using haddLeft 1 0 0 1 1 1
    have hsplitFirst :
        cocycle 1 0 1 1 = cocycle 1 0 1 0 + cocycle 1 0 0 1 := by
      simpa using haddRight 1 0 1 0 0 1
    have hsplitSecond :
        cocycle 0 1 1 1 = cocycle 0 1 1 0 + cocycle 0 1 0 1 := by
      simpa using haddRight 0 1 1 0 0 1
    calc
      cocycle 1 0 0 1 + cocycle 0 1 1 0 =
          (1 + cocycle 1 0 0 1) +
            (cocycle 0 1 1 0 + 1) := by
              rw [show (1 + cocycle 1 0 0 1) +
                  (cocycle 0 1 1 0 + 1) =
                (1 + 1) +
                  (cocycle 1 0 0 1 + cocycle 0 1 1 0) by abel,
                CharTwo.add_self_eq_zero, zero_add]
      _ = (cocycle 1 0 1 0 + cocycle 1 0 0 1) +
            (cocycle 0 1 1 0 + cocycle 0 1 0 1) := by
              rw [hdiag, hdiag]
              simp only [map_one, map_zero, mul_one, mul_zero,
                add_zero, zero_add]
      _ = cocycle 1 0 1 1 + cocycle 0 1 1 1 := by
              rw [hsplitFirst, hsplitSecond]
      _ = cocycle 1 1 1 1 := hsplitLeft.symm
      _ = epsilonB := by
        rw [hdiag]
        simp only [map_one, mul_one]
        rw [show (1 : FB) + epsilonB + 1 =
            epsilonB + (1 + 1) by ring,
          CharTwo.add_self_eq_zero, add_zero]
  have hcommutatorCoord (p r : P) :
      let cab := tripleEquiv.symm p
      let rdf := tripleEquiv.symm r
      ⁅p, r⁆ = tripleLift
        (cocycle cab.2.1 cab.2.2 rdf.2.1 rdf.2.2 +
          cocycle rdf.2.1 rdf.2.2 cab.2.1 cab.2.2) 0 0 := by
    dsimp
    let cab := tripleEquiv.symm p
    let rdf := tripleEquiv.symm r
    have hp : p = tripleLift cab.1 cab.2.1 cab.2.2 :=
      (tripleEquiv.apply_symm_apply p).symm
    have hr : r = tripleLift rdf.1 rdf.2.1 rdf.2.2 :=
      (tripleEquiv.apply_symm_apply r).symm
    let delta := cocycle cab.2.1 cab.2.2 rdf.2.1 rdf.2.2 +
      cocycle rdf.2.1 rdf.2.2 cab.2.1 cab.2.2
    have hpMul : p * r = tripleLift delta 0 0 * (r * p) := by
      rw [hp, hr, hmul, hmul, hmul, hzeroLeft]
      dsimp [delta]
      simp only [zero_add, add_zero]
      congr 1
      · rw [show
          (cocycle cab.2.1 cab.2.2 rdf.2.1 rdf.2.2 +
              cocycle rdf.2.1 rdf.2.2 cab.2.1 cab.2.2) +
                (rdf.1 + cab.1 +
                  cocycle rdf.2.1 rdf.2.2 cab.2.1 cab.2.2) =
            (cab.1 + rdf.1 +
              cocycle cab.2.1 cab.2.2 rdf.2.1 rdf.2.2) +
                (cocycle rdf.2.1 rdf.2.2 cab.2.1 cab.2.2 +
                  cocycle rdf.2.1 rdf.2.2 cab.2.1 cab.2.2) by abel,
            CharTwo.add_self_eq_zero, add_zero]
      · abel
      · abel
    rw [commutatorElement_def, hpMul]
    group
    rfl
  let coordChangeMul : Multiplicative (FB × FB) ≃*
      Multiplicative (FB × FB) := eQ.symm.trans eNatQ
  let coordChange : FB × FB ≃+ FB × FB :=
    { toFun := fun v =>
        (coordChangeMul (Multiplicative.ofAdd v)).toAdd
      invFun := fun v =>
        (coordChangeMul.symm (Multiplicative.ofAdd v)).toAdd
      left_inv := by
        intro v
        apply Multiplicative.ofAdd.injective
        change coordChangeMul.symm
            (coordChangeMul (Multiplicative.ofAdd v)) =
          Multiplicative.ofAdd v
        exact coordChangeMul.symm_apply_apply _
      right_inv := by
        intro v
        apply Multiplicative.ofAdd.injective
        change coordChangeMul
            (coordChangeMul.symm (Multiplicative.ofAdd v)) =
          Multiplicative.ofAdd v
        exact coordChangeMul.apply_symm_apply _
      map_add' := by
        intro v w
        apply Multiplicative.ofAdd.injective
        change coordChangeMul
            (Multiplicative.ofAdd (v + w)) =
          coordChangeMul (Multiplicative.ofAdd v) *
            coordChangeMul (Multiplicative.ofAdd w)
        exact coordChangeMul.map_mul _ _ }
  let centerChange : FB ≃+ FB :=
    { toFun := fun c =>
        (eZ (eNatZ.symm (Multiplicative.ofAdd c))).toAdd
      invFun := fun c =>
        (eNatZ (eZ.symm (Multiplicative.ofAdd c))).toAdd
      left_inv := by
        intro c
        apply Multiplicative.ofAdd.injective
        change eNatZ (eZ.symm
            (eZ (eNatZ.symm (Multiplicative.ofAdd c)))) =
          Multiplicative.ofAdd c
        rw [eZ.symm_apply_apply, eNatZ.apply_symm_apply]
      right_inv := by
        intro c
        apply Multiplicative.ofAdd.injective
        change eZ (eNatZ.symm
            (eNatZ (eZ.symm (Multiplicative.ofAdd c)))) =
          Multiplicative.ofAdd c
        rw [eNatZ.symm_apply_apply, eZ.apply_symm_apply]
      map_add' := by
        intro c d
        apply Multiplicative.ofAdd.injective
        change eZ (eNatZ.symm
            (Multiplicative.ofAdd (c + d))) =
          eZ (eNatZ.symm (Multiplicative.ofAdd c)) *
            eZ (eNatZ.symm (Multiplicative.ofAdd d))
        rw [show Multiplicative.ofAdd (c + d) =
            Multiplicative.ofAdd c * Multiplicative.ofAdd d by rfl,
          map_mul, map_mul] }
  let polarAdd : (FB × FB) →+
      (FB × FB) →+ FB :=
    { toFun := fun x =>
        { toFun := fun y =>
            cocycle x.1 x.2 y.1 y.2 + cocycle y.1 y.2 x.1 x.2
          map_zero' := by
            change cocycle x.1 x.2 0 0 + cocycle 0 0 x.1 x.2 = 0
            rw [hzeroRight, hzeroLeft, add_zero]
          map_add' := by
            intro y z
            change
              cocycle x.1 x.2 (y.1 + z.1) (y.2 + z.2) +
                  cocycle (y.1 + z.1) (y.2 + z.2) x.1 x.2 = _
            rw [haddRight, haddLeft]
            abel }
      map_zero' := by
        apply AddMonoidHom.ext
        intro y
        change cocycle 0 0 y.1 y.2 + cocycle y.1 y.2 0 0 = 0
        rw [hzeroLeft, hzeroRight, add_zero]
      map_add' := by
        intro x y
        apply AddMonoidHom.ext
        intro z
        change
          cocycle (x.1 + y.1) (x.2 + y.2) z.1 z.2 +
              cocycle z.1 z.2 (x.1 + y.1) (x.2 + y.2) =
            (cocycle x.1 x.2 z.1 z.2 + cocycle z.1 z.2 x.1 x.2) +
              (cocycle y.1 y.2 z.1 z.2 + cocycle z.1 z.2 y.1 y.2)
        rw [haddLeft, haddRight]
        abel }
  let polarInnerEquiv :
      ((FB × FB) →+ FB) ≃+ ((FB × FB) →ₗ[ZMod 2] FB) :=
    AddMonoidHom.toZModLinearMapEquiv 2
  let polar : (FB × FB) →ₗ[ZMod 2]
      (FB × FB) →ₗ[ZMod 2] FB :=
    (polarInnerEquiv.toAddMonoidHom.toZModLinearMap 2).comp
      (polarAdd.toZModLinearMap 2)
  let BcoordAdd : (FB × FB) →+
      (FB × FB) →+ FB :=
    { toFun := fun v =>
        { toFun := fun w => centerChange (polar (coordChange v) (coordChange w))
          map_zero' := by
            simp only [map_zero]
          map_add' := by
            intro w x
            rw [map_add, map_add, map_add] }
      map_zero' := by
        apply AddMonoidHom.ext
        intro w
        change centerChange (polar (coordChange 0) (coordChange w)) = 0
        simp only [map_zero, LinearMap.zero_apply]
      map_add' := by
        intro v w
        apply AddMonoidHom.ext
        intro x
        change centerChange (polar (coordChange (v + w)) (coordChange x)) =
          centerChange (polar (coordChange v) (coordChange x)) +
            centerChange (polar (coordChange w) (coordChange x))
        rw [map_add, map_add, LinearMap.add_apply, map_add] }
  let BcoordInnerEquiv :
      ((FB × FB) →+ FB) ≃+ ((FB × FB) →ₗ[ZMod 2] FB) :=
    AddMonoidHom.toZModLinearMapEquiv 2
  let Bcoord : (FB × FB) →ₗ[ZMod 2]
      (FB × FB) →ₗ[ZMod 2] FB :=
    (BcoordInnerEquiv.toAddMonoidHom.toZModLinearMap 2).comp
      (BcoordAdd.toZModLinearMap 2)
  have hcoordChange_mk (p : P) :
      coordChange
          (eQ (QuotientGroup.mk' (Subgroup.center P) p)).toAdd =
        (tripleEquiv.symm p).2 := by
    apply Multiplicative.ofAdd.injective
    change coordChangeMul
        (eQ (QuotientGroup.mk' (Subgroup.center P) p)) =
      Multiplicative.ofAdd (tripleEquiv.symm p).2
    change eNatQ (eQ.symm
        (eQ (QuotientGroup.mk' (Subgroup.center P) p))) = _
    rw [eQ.symm_apply_apply, heNatQ_mk]
    rfl
  have hcenterChange_apply (c : FB) :
      centerChange c =
        (eZ (centerMap (Multiplicative.ofAdd c))).toAdd := by
    change (eZ (eNatZ.symm (Multiplicative.ofAdd c))).toAdd = _
    congr 2
  let commCenter (p r : P) : Subgroup.center P :=
    ⟨⁅p, r⁆, by
      rw [hcommutatorCoord]
      exact (centerMap (Multiplicative.ofAdd
        (cocycle (tripleEquiv.symm p).2.1 (tripleEquiv.symm p).2.2
            (tripleEquiv.symm r).2.1 (tripleEquiv.symm r).2.2 +
          cocycle (tripleEquiv.symm r).2.1 (tripleEquiv.symm r).2.2
            (tripleEquiv.symm p).2.1 (tripleEquiv.symm p).2.2))).property⟩
  have hBcoord_comm (p r : P) :
      Bcoord
          (eQ (QuotientGroup.mk' (Subgroup.center P) p)).toAdd
          (eQ (QuotientGroup.mk' (Subgroup.center P) r)).toAdd =
        (eZ (commCenter p r)).toAdd := by
    rw [show Bcoord
          (eQ (QuotientGroup.mk' (Subgroup.center P) p)).toAdd
          (eQ (QuotientGroup.mk' (Subgroup.center P) r)).toAdd =
        centerChange
          (polar
            (coordChange
              (eQ (QuotientGroup.mk' (Subgroup.center P) p)).toAdd)
            (coordChange
              (eQ (QuotientGroup.mk' (Subgroup.center P) r)).toAdd)) by rfl,
      hcoordChange_mk, hcoordChange_mk]
    change centerChange
        (cocycle (tripleEquiv.symm p).2.1 (tripleEquiv.symm p).2.2
            (tripleEquiv.symm r).2.1 (tripleEquiv.symm r).2.2 +
          cocycle (tripleEquiv.symm r).2.1 (tripleEquiv.symm r).2.2
            (tripleEquiv.symm p).2.1 (tripleEquiv.symm p).2.2) = _
    rw [hcenterChange_apply]
    apply congrArg (fun z : Subgroup.center P => (eZ z).toAdd)
    apply Subtype.ext
    exact (hcommutatorCoord p r).symm
  have hBcoord_nonzero : Bcoord ≠ 0 := by
    let v := coordChange.symm ((1, 0) : FB × FB)
    let w := coordChange.symm ((0, 1) : FB × FB)
    intro hzero
    have hval : Bcoord v w = 0 := by rw [hzero]; rfl
    change centerChange
        (polar (coordChange v) (coordChange w)) = 0 at hval
    rw [coordChange.apply_symm_apply, coordChange.apply_symm_apply] at hval
    change centerChange (cocycle 1 0 0 1 + cocycle 0 1 1 0) = 0 at hval
    rw [hpolarCross] at hval
    exact hepsilonB (centerChange.injective (hval.trans centerChange.map_zero.symm))
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := K)
  let lambda : FB := (eKQ g : FB)
  let mu : FB := (eKZ g : FB)
  have hlambda : lambda ≠ 0 := Units.ne_zero (eKQ g)
  have hmu : mu ≠ 0 := Units.ne_zero (eKZ g)
  have hQscalar_mk (p : P) :
      (eQ (QuotientGroup.mk' (Subgroup.center P) (g • p))).toAdd =
        lambda •
          (eQ (QuotientGroup.mk' (Subgroup.center P) p)).toAdd := by
    have h := hQscalar g
      (QuotientGroup.mk' (Subgroup.center P) p)
    change (eQ (@SMul.smul K (P ⧸ Subgroup.center P)
      hQAction.toMulAction.toSMul g
      (QuotientGroup.mk' (Subgroup.center P) p))).toAdd = _ at h
    rw [hQAction_mk] at h
    have hsmul :
        lambda •
            (eQ (QuotientGroup.mk' (Subgroup.center P) p)).toAdd =
          (lambda *
              (eQ (QuotientGroup.mk' (Subgroup.center P) p)).toAdd.1,
            lambda *
              (eQ (QuotientGroup.mk' (Subgroup.center P) p)).toAdd.2) := by
      ext <;> simp [smul_eq_mul]
    rw [hsmul]
    simpa [lambda] using h
  have hcommCenter_action (p r : P) :
      g • commCenter p r = commCenter (g • p) (g • r) := by
    apply Subtype.ext
    exact map_commutatorElement (MulDistribMulAction.toMulAut K P g) p r
  have hBcoord_equivariant (v w : FB × FB) :
      Bcoord (lambda • v) (lambda • w) = mu * Bcoord v w := by
    obtain ⟨p, hp⟩ := QuotientGroup.mk'_surjective
      (Subgroup.center P)
      (eQ.symm (Multiplicative.ofAdd v))
    obtain ⟨r, hr⟩ := QuotientGroup.mk'_surjective
      (Subgroup.center P)
      (eQ.symm (Multiplicative.ofAdd w))
    have hpCoord :
        (eQ (QuotientGroup.mk' (Subgroup.center P) p)).toAdd = v := by
      rw [hp, eQ.apply_symm_apply]
      rfl
    have hrCoord :
        (eQ (QuotientGroup.mk' (Subgroup.center P) r)).toAdd = w := by
      rw [hr, eQ.apply_symm_apply]
      rfl
    calc
      Bcoord (lambda • v) (lambda • w) =
          Bcoord
            (eQ (QuotientGroup.mk' (Subgroup.center P) (g • p))).toAdd
            (eQ (QuotientGroup.mk' (Subgroup.center P) (g • r))).toAdd := by
              rw [hQscalar_mk, hQscalar_mk, hpCoord, hrCoord]
      _ = (eZ (commCenter (g • p) (g • r))).toAdd :=
        hBcoord_comm _ _
      _ = (eZ (g • commCenter p r)).toAdd := by
        rw [hcommCenter_action]
      _ = mu * (eZ (commCenter p r)).toAdd := by
        simpa [mu] using hZscalar g (commCenter p r)
      _ = mu * Bcoord v w := by
        congr 1
        rw [← hpCoord, ← hrCoord, hBcoord_comm]
  have hBcoord_value : ∃ v w : FB × FB, Bcoord v w ≠ 0 := by
    by_contra h
    push Not at h
    apply hBcoord_nonzero
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    exact h v w
  obtain ⟨v0, w0, hBv0w0⟩ := hBcoord_value
  let BaxisAdd : FB →+ FB →+ FB :=
    { toFun := fun a =>
        { toFun := fun b => Bcoord (a • v0) (b • w0)
          map_zero' := by simp only [zero_smul, map_zero]
          map_add' := by intro b c; rw [add_smul, map_add]
        }
      map_zero' := by
        apply AddMonoidHom.ext
        intro b
        change Bcoord (0 • v0) (b • w0) = 0
        simp only [zero_smul, map_zero, LinearMap.zero_apply]
      map_add' := by
        intro a b
        apply AddMonoidHom.ext
        intro c
        change Bcoord ((a + b) • v0) (c • w0) =
          Bcoord (a • v0) (c • w0) + Bcoord (b • v0) (c • w0)
        rw [add_smul, map_add, LinearMap.add_apply] }
  let BaxisInnerEquiv : (FB →+ FB) ≃+ (FB →ₗ[ZMod 2] FB) :=
    AddMonoidHom.toZModLinearMapEquiv 2
  let Baxis : FB →ₗ[ZMod 2] FB →ₗ[ZMod 2] FB :=
    (BaxisInnerEquiv.toAddMonoidHom.toZModLinearMap 2).comp
      (BaxisAdd.toZModLinearMap 2)
  have hBaxis_nonzero : Baxis 1 1 ≠ 0 := by
    change Bcoord (1 • v0) (1 • w0) ≠ 0
    simpa only [one_smul] using hBv0w0
  have hBaxis_equivariant (a b : FB) :
      Baxis (lambda * a) (lambda * b) = mu * Baxis a b := by
    change Bcoord ((lambda * a) • v0) ((lambda * b) • w0) =
      mu * Bcoord (a • v0) (b • w0)
    rw [mul_smul, mul_smul, hBcoord_equivariant]
  obtain ⟨coeff, hcoeffExpansion, hcoeffSupport⟩ :=
    frobeniusBilinear_expansion_with_support_of_equivariant
      n (Nat.pos_of_ne_zero hn) Baxis lambda lambda mu hBaxis_equivariant
  have hcoeff_nonzero : ∃ i j : Fin n, coeff i j ≠ 0 := by
    by_contra h
    push Not at h
    apply hBaxis_nonzero
    rw [hcoeffExpansion]
    simp [h]
  obtain ⟨i, j, hij⟩ := hcoeff_nonzero
  have heigenRelation :
      lambda ^ (2 ^ (i : ℕ)) * lambda ^ (2 ^ (j : ℕ)) = mu :=
    hcoeffSupport i j hij
  have hg_order : orderOf g = Nat.card K :=
    orderOf_eq_card_of_forall_mem_zpowers hg
  have hq_pow : q = 2 ^ n := by
    calc
      q = Nat.card (BinaryGaloisField n) := hFcard.symm
      _ = 2 ^ n := GaloisField.card 2 n hn
  have hg_field_order : orderOf g = 2 ^ n - 1 := by
    calc
      orderOf g = Nat.card K := hg_order
      _ = q - 1 := hKcard
      _ = 2 ^ n - 1 := by rw [hq_pow]
  have hlambda_unit_order : orderOf (eKQ g) = 2 ^ n - 1 := by
    calc
      orderOf (eKQ g) = orderOf g :=
        orderOf_injective eKQ.toMonoidHom eKQ.injective g
      _ = 2 ^ n - 1 := hg_field_order
  have hmu_unit_order : orderOf (eKZ g) = 2 ^ n - 1 := by
    calc
      orderOf (eKZ g) = orderOf g :=
        orderOf_injective eKZ.toMonoidHom eKZ.injective g
      _ = 2 ^ n - 1 := hg_field_order
  have hlambda_order : orderOf lambda = 2 ^ n - 1 := by
    calc
      orderOf lambda = orderOf (eKQ g) := by
        simpa [lambda] using (orderOf_units (G := FB) (y := eKQ g))
      _ = 2 ^ n - 1 := hlambda_unit_order
  have hmu_order : orderOf mu = 2 ^ n - 1 := by
    calc
      orderOf mu = orderOf (eKZ g) := by
        simpa [mu] using (orderOf_units (G := FB) (y := eKZ g))
      _ = 2 ^ n - 1 := hmu_unit_order
  let sigma : FB ≃ₐ[ZMod 2] FB :=
    FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) FB
  let rho : FB ≃ₐ[ZMod 2] FB := sigma ^ (i : ℕ)
  let thetaAlg : FB ≃ₐ[ZMod 2] FB :=
    sigma ^ (j : ℕ) * rho.symm
  let theta : FB ≃+* FB := thetaAlg.toRingEquiv
  have hsigma_apply (x : FB) (t : ℕ) :
      (sigma ^ t) x = x ^ (2 ^ t) := by
    rw [AlgEquiv.coe_pow,
      FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
    simp [ZMod.card]
  have hsigma_order : orderOf sigma = n := by
    rw [FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic,
      GaloisField.finrank 2 hn]
  have hthetaPeriod :
      ∃ period : ℕ, Odd period ∧ 0 < period ∧
        ∀ x : FB, theta^[period] x = x := by
    let gap := lemma6_finPairGap i j
    let e := 2 ^ (i : ℕ) + 2 ^ (j : ℕ)
    have he_pos : 0 < e := by simp [e]
    have heigenPow : lambda ^ e = mu := by
      simpa [e, pow_add] using heigenRelation
    have hlambda_e_order : orderOf (lambda ^ e) = 2 ^ n - 1 := by
      rw [heigenPow]
      exact hmu_order
    have hcop_e : Nat.Coprime (2 ^ n - 1) e := by
      have hformula := orderOf_pow' lambda he_pos.ne'
      rw [hlambda_order] at hformula
      have hdiv : (2 ^ n - 1) / (2 ^ n - 1).gcd e = 2 ^ n - 1 :=
        hformula.symm.trans hlambda_e_order
      have hcancel := Nat.div_mul_cancel
        (Nat.gcd_dvd_left (2 ^ n - 1) e)
      rw [hdiv] at hcancel
      have hbase_pos : 0 < 2 ^ n - 1 := by
        have hpow : 1 < 2 ^ n := Nat.one_lt_two_pow hn
        omega
      apply Nat.coprime_iff_gcd_eq_one.mpr
      apply (mul_left_cancel_iff_of_pos hbase_pos).mp
      simpa using hcancel
    have hgap_dvd : 2 ^ gap + 1 ∣ e := by
      dsimp only [gap, e, lemma6_finPairGap]
      rcases le_total (i : ℕ) (j : ℕ) with hij' | hji'
      · refine ⟨2 ^ (i : ℕ), ?_⟩
        calc
          2 ^ (i : ℕ) + 2 ^ (j : ℕ) =
              2 ^ (i : ℕ) +
                2 ^ ((i : ℕ) + ((j : ℕ) - (i : ℕ))) := by
                  rw [Nat.add_sub_of_le hij']
          _ = (2 ^ (((i : ℕ) - (j : ℕ)) +
                ((j : ℕ) - (i : ℕ))) + 1) * 2 ^ (i : ℕ) := by
                  rw [Nat.sub_eq_zero_of_le hij', zero_add, pow_add]
                  ring
      · refine ⟨2 ^ (j : ℕ), ?_⟩
        calc
          2 ^ (i : ℕ) + 2 ^ (j : ℕ) =
              2 ^ ((j : ℕ) + ((i : ℕ) - (j : ℕ))) +
                2 ^ (j : ℕ) := by
                  rw [Nat.add_sub_of_le hji']
          _ = (2 ^ (((i : ℕ) - (j : ℕ)) +
                ((j : ℕ) - (i : ℕ))) + 1) * 2 ^ (j : ℕ) := by
                  rw [Nat.sub_eq_zero_of_le hji', add_zero, pow_add]
                  ring
    have hcop_gap : Nat.Coprime (2 ^ n - 1) (2 ^ gap + 1) :=
      hcop_e.of_dvd_right hgap_dvd
    let period := n / n.gcd gap
    have hperiod_odd : Odd period := by
      let d := n.gcd gap
      have hd_pos : 0 < d := Nat.gcd_pos_of_pos_left gap
        (Nat.pos_of_ne_zero hn)
      have hquot_coprime : (n / d).Coprime (gap / d) := by
        simpa [d] using Nat.coprime_div_gcd_div_gcd hd_pos
      apply Nat.not_even_iff_odd.mp
      intro hn_even
      have htwo_dvd : 2 ∣ n / d := by
        rcases (show Even (n / d) by
          simpa [period, d] using hn_even) with ⟨k, hk⟩
        exact ⟨k, by omega⟩
      have hgap_odd : Odd (gap / d) := by
        apply Nat.Coprime.odd_of_left
        exact Nat.Coprime.of_dvd htwo_dvd (dvd_refl _) hquot_coprime
      have hd_dvd_n : d ∣ n := by
        simpa [d] using Nat.gcd_dvd_left n gap
      have hd_dvd_gap : d ∣ gap := by
        simpa [d] using Nat.gcd_dvd_right n gap
      have hn_eq : d * (n / d) = n := Nat.mul_div_cancel' hd_dvd_n
      have hgap_eq : d * (gap / d) = gap :=
        Nat.mul_div_cancel' hd_dvd_gap
      let c := 2 ^ d + 1
      have hc_base : c ∣ (2 ^ d) ^ 2 - 1 := by
        refine ⟨2 ^ d - 1, ?_⟩
        simpa [c, pow_two] using mul_self_tsub_one (2 ^ d)
      have hc_dvd_n : c ∣ 2 ^ n - 1 := by
        have h := hc_base.trans
          (Nat.pow_sub_one_dvd_pow_sub_one (2 ^ d) htwo_dvd)
        simpa [c, ← pow_mul, hn_eq] using h
      have hc_dvd_gap : c ∣ 2 ^ gap + 1 := by
        have h := hgap_odd.nat_add_dvd_pow_add_pow (2 ^ d) 1
        simpa [c, ← pow_mul, hgap_eq] using h
      have hc_one := Nat.eq_one_of_dvd_coprimes
        hcop_gap hc_dvd_n hc_dvd_gap
      have hc_gt : 1 < c := by simp [c]
      exact (ne_of_gt hc_gt) hc_one
    have hsigma_gap_order : orderOf (sigma ^ gap) = period := by
      dsimp [period]
      rw [orderOf_pow, hsigma_order]
    have hthetaAlg_gap :
        thetaAlg = sigma ^ gap ∨ thetaAlg = (sigma ^ gap)⁻¹ := by
      rcases le_total (i : ℕ) (j : ℕ) with hij' | hji'
      · left
        change sigma ^ (j : ℕ) * (sigma ^ (i : ℕ))⁻¹ =
          sigma ^ gap
        rw [← pow_sub sigma hij']
        congr 1
        simp [gap, lemma6_finPairGap, Nat.sub_eq_zero_of_le hij']
      · right
        change sigma ^ (j : ℕ) * (sigma ^ (i : ℕ))⁻¹ =
          (sigma ^ gap)⁻¹
        rw [show gap = (i : ℕ) - (j : ℕ) by
          simp [gap, lemma6_finPairGap, Nat.sub_eq_zero_of_le hji']]
        rw [pow_sub sigma hji', mul_inv_rev, inv_inv]
    have hthetaAlg_order : orderOf thetaAlg = period := by
      rcases hthetaAlg_gap with hthetaAlg | hthetaAlg
      · rw [hthetaAlg, hsigma_gap_order]
      · rw [hthetaAlg, orderOf_inv, hsigma_gap_order]
    have hthetaAlg_pow : thetaAlg ^ period = 1 := by
      rw [← hthetaAlg_order]
      exact pow_orderOf_eq_one thetaAlg
    refine ⟨period, hperiod_odd, hperiod_odd.pos, ?_⟩
    intro x
    have h := DFunLike.congr_fun hthetaAlg_pow x
    simpa [theta, AlgEquiv.coe_pow] using h
  let eK' : K ≃* FBˣ :=
    eKQ.trans (Units.mapEquiv rho.toMulEquiv)
  let rhoAdd : FB ≃+ FB := rho.toRingEquiv.toAddEquiv
  let rhoProd : FB × FB ≃+ FB × FB :=
    AddEquiv.prodCongr rhoAdd rhoAdd
  let eQ' : (P ⧸ Subgroup.center P) ≃*
      Multiplicative (FB × FB) :=
    eQ.trans rhoProd.toMultiplicative
  have heK'_val (k : K) :
      (eK' k : FB) = rho (eKQ k : FB) := by
    rfl
  have heQ'_val (x : P ⧸ Subgroup.center P) :
      (eQ' x).toAdd =
        (rho (eQ x).toAdd.1, rho (eQ x).toAdd.2) := by
    rfl
  have hrho_lambda : rho lambda = lambda ^ (2 ^ (i : ℕ)) := by
    exact hsigma_apply lambda (i : ℕ)
  have htheta_rho_lambda :
      theta (rho lambda) = lambda ^ (2 ^ (j : ℕ)) := by
    change thetaAlg (rho lambda) = _
    change (sigma ^ (j : ℕ)) (rho.symm (rho lambda)) = _
    rw [rho.symm_apply_apply, hsigma_apply]
  have hgeneratorScalarRelation :
      (eKZ g : FB) = (eK' g : FB) * theta (eK' g : FB) := by
    rw [heK'_val]
    change mu = rho lambda * theta (rho lambda)
    rw [htheta_rho_lambda, hrho_lambda]
    exact heigenRelation.symm
  have hscalarRelation (k : K) :
      (eKZ k : FB) = (eK' k : FB) * theta (eK' k : FB) := by
    obtain ⟨t, rfl⟩ := mem_powers_iff_mem_zpowers.mpr (hg k)
    simp only [map_pow]
    change (eKZ g : FB) ^ t =
      (eK' g : FB) ^ t * theta ((eK' g : FB) ^ t)
    rw [map_pow, ← mul_pow, ← hgeneratorScalarRelation]
  have hQnew (k : K) (p : P) :
      (eQ' (QuotientGroup.mk' (Subgroup.center P) (k • p))).toAdd =
        ((eK' k : FB) *
            (eQ' (QuotientGroup.mk' (Subgroup.center P) p)).toAdd.1,
          (eK' k : FB) *
            (eQ' (QuotientGroup.mk' (Subgroup.center P) p)).toAdd.2) := by
    have h := hQscalar k
      (QuotientGroup.mk' (Subgroup.center P) p)
    change (eQ (@SMul.smul K (P ⧸ Subgroup.center P)
      hQAction.toMulAction.toSMul k
      (QuotientGroup.mk' (Subgroup.center P) p))).toAdd = _ at h
    rw [hQAction_mk] at h
    rw [heQ'_val, heQ'_val, h]
    rw [heK'_val]
    simp only [map_mul]
  have hZnew (k : K) (z : FB) :
      k • ((eZ.symm (Multiplicative.ofAdd z) : Subgroup.center P) : P) =
        ((eZ.symm (Multiplicative.ofAdd
          ((eK' k : FB) * theta (eK' k : FB) * z)) :
            Subgroup.center P) : P) := by
    change
      ((k • (eZ.symm (Multiplicative.ofAdd z) : Subgroup.center P) :
          Subgroup.center P) : P) = _
    apply congrArg Subtype.val
    apply eZ.injective
    apply Multiplicative.toAdd.injective
    rw [eZ.apply_symm_apply]
    rw [hZscalar]
    rw [eZ.apply_symm_apply, hscalarRelation]
    rfl
  exact ⟨n, hn, theta, eK', eQ', eZ, hthetaPeriod, hQnew, hZnew⟩

end Higman
end External
end CFSG.BenderSuzuki
