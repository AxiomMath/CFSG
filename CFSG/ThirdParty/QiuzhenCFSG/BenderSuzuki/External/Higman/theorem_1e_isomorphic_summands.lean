module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.theorem_1b
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.lemma_12
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Quotient

namespace CFSG
end CFSG
open CFSG

/-!
# Higman's classification theorem for Suzuki 2-groups: extracted branch
-/

namespace CFSG.BenderSuzuki
namespace External
namespace Higman

open PFAppendixIII

universe u

private theorem submodule_eq_of_le_of_natCard_ge
    {R E : Type*} [Semiring R] [AddCommMonoid E] [Module R E]
    [Finite E]
    {U V : Submodule R E} (hUV : U ≤ V)
    (hcard : Nat.card V ≤ Nat.card U) : U = V := by
  exact SetLike.coe_injective
    (Set.Finite.eq_of_subset_of_card_le (Set.toFinite _) hUV hcard)

private theorem irreducible_eq_or_disjoint
    {R E : Type*} [Semiring R] [AddCommMonoid E] [Module R E]
    [Finite E]
    (T : E ≃ₗ[R] E) (U : Submodule R E) (TU : U ≃ₗ[R] U)
    (hTU : ∀ u : U, ((TU u : U) : E) = T (u : E))
    (hUirreducible : ∀ W : Submodule R U,
      (∀ u : U, u ∈ W → TU u ∈ W) → W = ⊥ ∨ W = ⊤)
    (A : Submodule R E) (hA : ∀ a ∈ A, T a ∈ A)
    (hcard : Nat.card A = Nat.card U) : A = U ∨ Disjoint A U := by
  let W : Submodule R U := A.comap U.subtype
  have hWinvariant : ∀ u : U, u ∈ W → TU u ∈ W := by
    intro u hu
    change ((TU u : U) : E) ∈ A
    rw [hTU]
    exact hA (u : E) hu
  rcases hUirreducible W hWinvariant with hWbot | hWtop
  · right
    rw [disjoint_iff]
    apply le_antisymm
    · intro x hx
      have hxW : (⟨x, hx.2⟩ : U) ∈ W := hx.1
      rw [hWbot] at hxW
      have hxzero : (⟨x, hx.2⟩ : U) = 0 := by simpa using hxW
      simpa using congrArg Subtype.val hxzero
    · exact bot_le
  · left
    have hUleA : U ≤ A := by
      intro u hu
      have huW : (⟨u, hu⟩ : U) ∈ W := by rw [hWtop]; trivial
      exact huW
    exact (submodule_eq_of_le_of_natCard_ge hUleA hcard.le).symm

private theorem isCompl_of_disjoint_of_natCard_eq
    {K E : Type*} [DivisionRing K] [AddCommGroup E] [Module K E]
    [Finite K] [Finite E] [FiniteDimensional K E]
    (U V T : Submodule K E) (hUV : IsCompl U V)
    (hdisjoint : Disjoint T U) (hcard : Nat.card T = Nat.card V) :
    IsCompl T U := by
  have hfinrank : Module.finrank K T = Module.finrank K V := by
    apply Nat.pow_right_injective (Nat.succ_le_iff.mpr (Finite.one_lt_card (α := K)))
    calc
      Nat.card K ^ Module.finrank K T = Nat.card T :=
        (Module.natCard_eq_pow_finrank (K := K) (V := T)).symm
      _ = Nat.card V := hcard
      _ = Nat.card K ^ Module.finrank K V :=
        Module.natCard_eq_pow_finrank (K := K) (V := V)
  apply (Submodule.isCompl_iff_disjoint T U ?_).2 hdisjoint
  rw [← Submodule.finrank_add_eq_of_isCompl hUV, hfinrank, add_comm]

private theorem equivariant_linearEquiv_of_common_complement
    {K E : Type*} [Ring K] [AddCommGroup E] [Module K E]
    (T U V : Submodule K E) (A : E ≃ₗ[K] E)
    (AU : U ≃ₗ[K] U) (AV : V ≃ₗ[K] V)
    (hAU : ∀ u : U, ((AU u : U) : E) = A (u : E))
    (hAV : ∀ v : V, ((AV v : V) : E) = A (v : E))
    (hT : ∀ t ∈ T, A t ∈ T)
    (hTU : IsCompl T U) (hTV : IsCompl T V) :
    ∃ e : U ≃ₗ[K] V, ∀ u : U, e (AU u) = AV (e u) := by
  let e : U ≃ₗ[K] V :=
    (T.quotientEquivOfIsCompl U hTU).symm.trans
      (T.quotientEquivOfIsCompl V hTV)
  refine ⟨e, ?_⟩
  intro u
  apply (T.quotientEquivOfIsCompl V hTV).symm.injective
  simp only [e, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    Submodule.quotientEquivOfIsCompl_symm_apply]
  rw [hAU, hAV]
  apply (Submodule.Quotient.eq T).2
  rw [← map_sub]
  apply hT
  apply (Submodule.Quotient.eq T).1
  exact (Submodule.mk_quotientEquivOfIsCompl_apply
    (p := T) (q := V) hTV (Submodule.Quotient.mk u)).symm

private theorem canonical_equivariant_iso_of_isomorphic_complements
    {K E : Type*} [DivisionRing K] [Finite K]
    [AddCommGroup E] [Module K E] [Finite E] [FiniteDimensional K E]
    (T : E ≃ₗ[K] E)
    (U V W Z : Submodule K E)
    (TU : U ≃ₗ[K] U) (TV : V ≃ₗ[K] V)
    (TW : W ≃ₗ[K] W) (TZ : Z ≃ₗ[K] Z)
    (hTU : ∀ u : U, ((TU u : U) : E) = T (u : E))
    (hTV : ∀ v : V, ((TV v : V) : E) = T (v : E))
    (hTW : ∀ w : W, ((TW w : W) : E) = T (w : E))
    (hTZ : ∀ z : Z, ((TZ z : Z) : E) = T (z : E))
    (hUirreducible : ∀ A : Submodule K U,
      (∀ u : U, u ∈ A → TU u ∈ A) → A = ⊥ ∨ A = ⊤)
    (hVirreducible : ∀ A : Submodule K V,
      (∀ v : V, v ∈ A → TV v ∈ A) → A = ⊥ ∨ A = ⊤)
    (hUV : IsCompl U V) (hWZ : IsCompl W Z)
    (hUcard : Nat.card U = Nat.card V)
    (hWcard : Nat.card W = Nat.card U)
    (hZcard : Nat.card Z = Nat.card U)
    (eWZ : W ≃ₗ[K] Z) (heWZ : ∀ w : W, eWZ (TW w) = TZ (eWZ w)) :
    ∃ e : U ≃ₗ[K] V, ∀ u : U, e (TU u) = TV (e u) := by
  have hWinvariant : ∀ w ∈ W, T w ∈ W := by
    intro w hw
    rw [← hTW ⟨w, hw⟩]
    exact (TW ⟨w, hw⟩).property
  have hZinvariant : ∀ z ∈ Z, T z ∈ Z := by
    intro z hz
    rw [← hTZ ⟨z, hz⟩]
    exact (TZ ⟨z, hz⟩).property
  by_cases hWU : W = U
  · subst W
    have hTW_eq_TU : TW = TU := by
      apply LinearEquiv.ext
      intro u
      apply Subtype.ext
      exact (hTW u).trans (hTU u).symm
    by_cases hZV : Z = V
    · subst Z
      have hTZ_eq_TV : TZ = TV := by
        apply LinearEquiv.ext
        intro v
        apply Subtype.ext
        exact (hTZ v).trans (hTV v).symm
      rw [hTW_eq_TU, hTZ_eq_TV] at heWZ
      exact ⟨eWZ, heWZ⟩
    · have hZVdisjoint : Disjoint Z V :=
        (irreducible_eq_or_disjoint T V TV hTV hVirreducible
          Z hZinvariant (hZcard.trans hUcard)).resolve_left hZV
      have hZVcompl : IsCompl Z V :=
        isCompl_of_disjoint_of_natCard_eq V U Z hUV.symm
          hZVdisjoint hZcard
      exact equivariant_linearEquiv_of_common_complement
        Z U V T TU TV hTU hTV hZinvariant hWZ.symm hZVcompl
  · by_cases hWV : W = V
    · subst W
      have hTW_eq_TV : TW = TV := by
        apply LinearEquiv.ext
        intro v
        apply Subtype.ext
        exact (hTW v).trans (hTV v).symm
      by_cases hZU : Z = U
      · subst Z
        have hTZ_eq_TU : TZ = TU := by
          apply LinearEquiv.ext
          intro u
          apply Subtype.ext
          exact (hTZ u).trans (hTU u).symm
        rw [hTW_eq_TV, hTZ_eq_TU] at heWZ
        exact ⟨eWZ.symm, fun u => by
          apply eWZ.injective
          simpa using (heWZ (eWZ.symm u)).symm⟩
      · have hZUdisjoint : Disjoint Z U :=
          (irreducible_eq_or_disjoint T U TU hTU hUirreducible
            Z hZinvariant hZcard).resolve_left hZU
        have hZUcompl : IsCompl Z U :=
          isCompl_of_disjoint_of_natCard_eq U V Z hUV
            hZUdisjoint (hZcard.trans hUcard)
        exact equivariant_linearEquiv_of_common_complement
          Z U V T TU TV hTU hTV hZinvariant hZUcompl hWZ.symm
    · have hWUdisjoint : Disjoint W U :=
        (irreducible_eq_or_disjoint T U TU hTU hUirreducible
          W hWinvariant hWcard).resolve_left hWU
      have hWVdisjoint : Disjoint W V :=
        (irreducible_eq_or_disjoint T V TV hTV hVirreducible
          W hWinvariant (hWcard.trans hUcard)).resolve_left hWV
      have hWUcompl : IsCompl W U :=
        isCompl_of_disjoint_of_natCard_eq U V W hUV
          hWUdisjoint (hWcard.trans hUcard)
      have hWVcompl : IsCompl W V :=
        isCompl_of_disjoint_of_natCard_eq V U W hUV.symm
          hWVdisjoint hWcard
      exact equivariant_linearEquiv_of_common_complement
        W U V T TU TV hTU hTV hWinvariant hWUcompl hWVcompl

private def zmod2SubmoduleOfSubgroup
    {G : Type*} [CommGroup G] [Module (ZMod 2) (Additive G)]
    (U : Subgroup G) : Submodule (ZMod 2) (Additive G) :=
  (Subgroup.toAddSubgroup.trans
    (AddSubgroup.toZModSubmodule (n := 2))) U

private theorem natCard_zmod2SubmoduleOfSubgroup
    {G : Type*} [CommGroup G] [Module (ZMod 2) (Additive G)]
    (U : Subgroup G) : Nat.card (zmod2SubmoduleOfSubgroup U) =
      Nat.card U := by
  let e : zmod2SubmoduleOfSubgroup U ≃ U :=
    { toFun := fun u => ⟨u.1.toMul, u.property⟩
      invFun := fun u => ⟨Additive.ofMul u.1, u.property⟩
      left_inv := by intro u; rfl
      right_inv := by intro u; rfl }
  exact Nat.card_congr e

private noncomputable def zmod2LinearEquivOfSubgroupMulEquiv
    {G : Type*} [CommGroup G] [Module (ZMod 2) (Additive G)]
    (U V : Subgroup G) (e : U ≃* V) :
    zmod2SubmoduleOfSubgroup U ≃ₗ[ZMod 2]
      zmod2SubmoduleOfSubgroup V := by
  let Φ : Subgroup G ≃o Submodule (ZMod 2) (Additive G) :=
    Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule (n := 2))
  let eAdd : (Φ U) ≃+ (Φ V) :=
    { toFun := fun u =>
        ⟨Additive.ofMul (e ⟨u.1.toMul, by
            exact u.property⟩), by
          change (e ⟨u.1.toMul, by
            exact u.property⟩ : V).1 ∈ V
          exact (e ⟨u.1.toMul, by
            exact u.property⟩).property⟩
      invFun := fun v =>
        ⟨Additive.ofMul (e.symm ⟨v.1.toMul, by
            exact v.property⟩), by
          change (e.symm ⟨v.1.toMul, by
            exact v.property⟩ : U).1 ∈ U
          exact (e.symm ⟨v.1.toMul, by
            exact v.property⟩).property⟩
      left_inv := by
        intro u
        apply Subtype.ext
        exact congrArg (fun x : U => Additive.ofMul (x : G))
          (e.symm_apply_apply ⟨u.1.toMul, by
            exact u.property⟩)
      right_inv := by
        intro v
        apply Subtype.ext
        exact congrArg (fun x : V => Additive.ofMul (x : G))
          (e.apply_symm_apply ⟨v.1.toMul, by
            exact v.property⟩)
      map_add' := by
        intro u v
        apply Subtype.ext
        change Additive.ofMul
            (e (⟨u.1.toMul, by
                exact u.property⟩ *
              ⟨v.1.toMul, by
                exact v.property⟩ : U) : G) = _
        rw [map_mul]
        rfl }
  exact
    { toLinearMap := eAdd.toAddMonoidHom.toZModLinearMap 2
      invFun := eAdd.symm
      left_inv := eAdd.left_inv
      right_inv := eAdd.right_inv }


private noncomputable def LinearEquiv.restrictInvariantFinite
    {K E : Type*} [DivisionRing K] [AddCommGroup E] [Module K E]
    [FiniteDimensional K E]
    (T : E ≃ₗ[K] E) (U : Submodule K E)
    (hU : ∀ x ∈ U, T x ∈ U) : U ≃ₗ[K] U := by
  let f : U →ₗ[K] U :=
    { toFun := fun u => ⟨T u, hU u u.property⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        exact map_add T (x : E) (y : E)
      map_smul' := by
        intro c x
        apply Subtype.ext
        exact map_smul T c (x : E) }
  apply LinearEquiv.ofBijective f
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply T.injective
    exact congrArg Subtype.val hxy
  exact ⟨hf, LinearMap.injective_iff_surjective.mp hf⟩


/-- Explicit actor-equivariant isomorphic summands in the central quotient. -/
@[expose] public def Theorem1IsomorphicSummands
    (K P : Type u) [Group K] [Group P] [MulDistribMulAction K P] : Prop :=
  ∃ (quotientAction : MulDistribMulAction K (P ⧸ Subgroup.center P))
      (U V : Subgroup (P ⧸ Subgroup.center P))
      (hU : @IsXInvariantSubgroup K (P ⧸ Subgroup.center P)
        _ _ quotientAction U)
      (_hV : @IsXInvariantSubgroup K (P ⧸ Subgroup.center P)
        _ _ quotientAction V)
      (e : U ≃* V),
    (∀ k : K, ∀ p : P,
      @SMul.smul K (P ⧸ Subgroup.center P)
          quotientAction.toMulAction.toSMul k
          (QuotientGroup.mk' (Subgroup.center P) p) =
        QuotientGroup.mk' (Subgroup.center P) (k • p)) ∧
    Nat.card U = Nat.card (Subgroup.center P) ∧
    Nat.card V = Nat.card (Subgroup.center P) ∧
    U ⊓ V = ⊥ ∧ U ⊔ V = ⊤ ∧
    ∀ k : K, ∀ u : U,
      ((e ⟨@SMul.smul K (P ⧸ Subgroup.center P)
            quotientAction.toMulAction.toSMul k
            (u : P ⧸ Subgroup.center P),
        (hU k (u : P ⧸ Subgroup.center P)).mp u.property⟩ : V) :
          P ⧸ Subgroup.center P) =
        @SMul.smul K (P ⧸ Subgroup.center P)
          quotientAction.toMulAction.toSMul k
          ((e u : V) : P ⧸ Subgroup.center P)

set_option maxHeartbeats 800000 in
/-- Explicit actor-equivariant quotient summands force the actor-relative
Type-B branch retained by Lemma 12. -/
public theorem theorem1_typeB_actor_of_isomorphic_summands
    {K P : Type u} [Group K] [Group P] [MulDistribMulAction K P]
    (hP : IsSuzukiTwoGroup P)
    (hKcyclic : IsCyclic K) (hKfaithful : FaithfulSMul K P)
    (hKregular : ActionRegularOn K P (involutions P))
    (hIso : Theorem1IsomorphicSummands K P) :
    ∃ (B : Subgroup P) (actor : K),
      Lemma12TypeBActorBranchData K P actor B := by
  classical
  letI : Finite P := finite_of_isSuzukiTwoGroup hP
  rcases hIso with
    ⟨hQAction, Uq, Vq, hUq, hVq, eUV, hQAction_mk,
      hUqcard, hVqcard, hUqVqinf, hUqVqsup, heUV⟩
  letI : MulDistribMulAction K (P ⧸ Subgroup.center P) := hQAction
  have hQdata := theorem1_center_quotient_orders_and_exponent hP
  letI : IsMulCommutative (P ⧸ Subgroup.center P) := hQdata.1
  letI : CommGroup (P ⧸ Subgroup.center P) := IsMulCommutative.instCommGroup
  letI : Uq.Normal := Subgroup.normal_of_isMulCommutative Uq
  have hUqVqcompl : Uq.IsComplement' Vq := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [disjoint_iff]
      exact hUqVqinf
    · rw [Set.eq_univ_iff_forall]
      intro x
      have hx : x ∈ Uq ⊔ Vq := by rw [hUqVqsup]; trivial
      rcases (Subgroup.mem_sup_of_normal_left (x := x) (s := Uq) (t := Vq)).1 hx with
        ⟨u, hu, v, hv, huv⟩
      exact ⟨u, hu, v, hv, huv⟩
  have hquotient_card :
      Nat.card (P ⧸ Subgroup.center P) =
        Nat.card (Subgroup.center P) ^ 2 := by
    have hmul := hUqVqcompl.card_mul
    rw [hUqcard, hVqcard] at hmul
    simpa [pow_two] using hmul.symm
  have hPcard : Nat.card P = Nat.card (Subgroup.center P) ^ 3 := by
    calc
      Nat.card P = Nat.card (P ⧸ Subgroup.center P) *
          Nat.card (Subgroup.center P) :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center P)
      _ = Nat.card (Subgroup.center P) ^ 3 := by
        rw [hquotient_card]
        ring
  have hLen3 : OmegaLength K P 3 :=
    omegaLength_three_of_card_center_cube
      hP hKcyclic hKfaithful hKregular hPcard
  have hKtrans : ∀ a : P, a ∈ involutions P →
      ∀ b : P, b ∈ involutions P → ∃ k : K, b = k • a := by
    intro a ha b hb
    rcases hKregular.2 a ha b hb with ⟨k, hk, _huniq⟩
    exact ⟨k, hk⟩
  obtain ⟨x0, _y0, hx0, _hy0, _hxy0⟩ := hP.2.2.1
  let orbit : K → {x : P // x ∈ involutions P} :=
    fun k => ⟨k • x0, hKregular.1 x0 hx0 k⟩
  have horbit_injective : Function.Injective orbit := by
    intro k l hkl
    have heq : k • x0 = l • x0 := congrArg Subtype.val hkl
    rcases hKregular.2 x0 hx0 (k • x0)
        (hKregular.1 x0 hx0 k) with ⟨a, _ha, huniq⟩
    exact (huniq k rfl).trans (huniq l heq).symm
  have horbit_surjective : Function.Surjective orbit := by
    rintro ⟨y, hy⟩
    rcases hKregular.2 x0 hx0 y hy with ⟨k, hk, _huniq⟩
    exact ⟨k, Subtype.ext hk.symm⟩
  have hKcard_invol : Nat.card K =
      Nat.card {x : P // x ∈ involutions P} :=
    Nat.card_congr (Equiv.ofBijective orbit
      ⟨horbit_injective, horbit_surjective⟩)
  have hKprimeSupport : ∀ p : ℕ, p.Prime → p ∣ Nat.card K →
      p ∣ Nat.card {x : P // x ∈ involutions P} := by
    intro p _hp hp
    rw [← hKcard_invol]
    exact hp
  rcases lemma12_length_three_typeBCD_with_isomorphic_criterion
      hP hKcyclic hKfaithful hKtrans hKprimeSupport hLen3 with
    ⟨_hclassification, B, _hbranch, _hsummands, hcriterionData⟩
  rcases hcriterionData with
    ⟨n, actor, xi, q0, U, V, xiU, xiV, hn, hxi_actor,
      hq0_ker, hq0_surj, hq0_equivariant, hUV, hxiU_val, hxiV_val,
      hxiU_irreducible, hxiV_irreducible, hU_card, hV_card,
      hB_le_center, hB_card, hfactor0_card, _hinvolution_card,
      hcriterion⟩
  letI : B.Normal := by
    rw [← hq0_ker]
    infer_instance
  let eB : P ⧸ B ≃* LowerCentralFactor P 0 :=
    (QuotientGroup.quotientMulEquivOfEq hq0_ker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q0 hq0_surj)
  have hquotientB_card :
      Nat.card (P ⧸ B) = Nat.card (LowerCentralFactor P 0) :=
    Nat.card_congr eB.toEquiv
  have hP_card_n : Nat.card P = (2 ^ n) ^ 3 := by
    calc
      Nat.card P = Nat.card (P ⧸ B) * Nat.card B :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup B
      _ = (2 ^ n) ^ 3 := by
        rw [hquotientB_card, hfactor0_card, hB_card]
        ring
  have hcenter_card : Nat.card (Subgroup.center P) = 2 ^ n := by
    apply Nat.pow_left_injective (by norm_num : (3 : ℕ) ≠ 0)
    exact hPcard.symm.trans hP_card_n
  have hB_eq_center : B = Subgroup.center P := by
    apply Subgroup.eq_of_le_of_card_ge hB_le_center
    rw [hB_card, hcenter_card]
  have hq0_ker_center : q0.ker = Subgroup.center P :=
    hq0_ker.trans hB_eq_center
  let eQ : P ⧸ Subgroup.center P ≃* LowerCentralFactor P 0 :=
    (QuotientGroup.quotientMulEquivOfEq hq0_ker_center.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q0 hq0_surj)
  have heQ_mk (p : P) :
      eQ (QuotientGroup.mk' (Subgroup.center P) p) = q0 p := by
    change QuotientGroup.kerLift q0
        (QuotientGroup.quotientMulEquivOfEq hq0_ker_center.symm
          (QuotientGroup.mk' (Subgroup.center P) p)) = q0 p
    calc
      QuotientGroup.kerLift q0
          (QuotientGroup.quotientMulEquivOfEq hq0_ker_center.symm
            (QuotientGroup.mk' (Subgroup.center P) p)) =
        QuotientGroup.kerLift q0 (QuotientGroup.mk' q0.ker p) := by
          congr 1
      _ = q0 p := QuotientGroup.kerLift_mk q0 p
  have hcanonicalIso :
      ∃ e : U ≃ₗ[ZMod 2] V, ∀ u : U, e (xiU u) = xiV (e u) := by
    let T : Additive (LowerCentralFactor P 0) ≃ₗ[ZMod 2]
        Additive (LowerCentralFactor P 0) := lowerCentralFactorLinearAut xi 0
    let qsmul : K → (P ⧸ Subgroup.center P) →
        (P ⧸ Subgroup.center P) :=
      fun k q => @SMul.smul K (P ⧸ Subgroup.center P)
        hQAction.toMulAction.toSMul k q
    have heQ_actor (q : P ⧸ Subgroup.center P) :
        Additive.ofMul (eQ (qsmul actor q)) = T (Additive.ofMul (eQ q)) := by
      obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center P) q
      dsimp only [qsmul]
      rw [hQAction_mk, heQ_mk, heQ_mk, hq0_equivariant, ← hxi_actor]
    let Wgroup : Subgroup (LowerCentralFactor P 0) :=
      (MulEquiv.mapSubgroup eQ) Uq
    let Zgroup : Subgroup (LowerCentralFactor P 0) :=
      (MulEquiv.mapSubgroup eQ) Vq
    let W : Submodule (ZMod 2) (Additive (LowerCentralFactor P 0)) :=
      zmod2SubmoduleOfSubgroup Wgroup
    let Z : Submodule (ZMod 2) (Additive (LowerCentralFactor P 0)) :=
      zmod2SubmoduleOfSubgroup Zgroup
    have hWforward : ∀ x ∈ W, T x ∈ W := by
      intro x hx
      let xg : Wgroup := ⟨x.toMul, hx⟩
      let q : Uq := (eQ.subgroupMap Uq).symm xg
      have hqmap : eQ (q : P ⧸ Subgroup.center P) = x.toMul := by
        exact congrArg Subtype.val ((eQ.subgroupMap Uq).apply_symm_apply xg)
      let actorQ : Uq :=
        ⟨qsmul actor (q : P ⧸ Subgroup.center P),
          (hUq actor (q : P ⧸ Subgroup.center P)).mp q.property⟩
      have hTmul : (T x).toMul = eQ (actorQ : P ⧸ Subgroup.center P) := by
        apply Additive.ofMul.injective
        change T x = Additive.ofMul (eQ (qsmul actor (q : P ⧸ Subgroup.center P)))
        calc
          T x = T (Additive.ofMul (eQ (q : P ⧸ Subgroup.center P))) :=
            congrArg T (congrArg Additive.ofMul hqmap).symm
          _ = Additive.ofMul
              (eQ (qsmul actor (q : P ⧸ Subgroup.center P))) :=
            (heQ_actor (q : P ⧸ Subgroup.center P)).symm
      change (T x).toMul ∈ Wgroup
      rw [hTmul]
      exact (eQ.subgroupMap Uq actorQ).property
    have hZforward : ∀ x ∈ Z, T x ∈ Z := by
      intro x hx
      let xg : Zgroup := ⟨x.toMul, hx⟩
      let q : Vq := (eQ.subgroupMap Vq).symm xg
      have hqmap : eQ (q : P ⧸ Subgroup.center P) = x.toMul := by
        exact congrArg Subtype.val ((eQ.subgroupMap Vq).apply_symm_apply xg)
      let actorQ : Vq :=
        ⟨qsmul actor (q : P ⧸ Subgroup.center P),
          (hVq actor (q : P ⧸ Subgroup.center P)).mp q.property⟩
      have hTmul : (T x).toMul = eQ (actorQ : P ⧸ Subgroup.center P) := by
        apply Additive.ofMul.injective
        change T x = Additive.ofMul (eQ (qsmul actor (q : P ⧸ Subgroup.center P)))
        calc
          T x = T (Additive.ofMul (eQ (q : P ⧸ Subgroup.center P))) :=
            congrArg T (congrArg Additive.ofMul hqmap).symm
          _ = Additive.ofMul
              (eQ (qsmul actor (q : P ⧸ Subgroup.center P))) :=
            (heQ_actor (q : P ⧸ Subgroup.center P)).symm
      change (T x).toMul ∈ Zgroup
      rw [hTmul]
      exact (eQ.subgroupMap Vq actorQ).property
    let TW : W ≃ₗ[ZMod 2] W :=
      LinearEquiv.restrictInvariantFinite T W hWforward
    let TZ : Z ≃ₗ[ZMod 2] Z :=
      LinearEquiv.restrictInvariantFinite T Z hZforward
    have hTW_val (w : W) : ((TW w : W) :
        Additive (LowerCentralFactor P 0)) = T w := rfl
    have hTZ_val (z : Z) : ((TZ z : Z) :
        Additive (LowerCentralFactor P 0)) = T z := rfl
    have hUqVq : IsCompl Uq Vq := by
      constructor
      · rw [disjoint_iff]
        exact hUqVqinf
      · rw [codisjoint_iff]
        exact hUqVqsup
    have hWgroupZgroup : IsCompl Wgroup Zgroup := by
      exact (MulEquiv.mapSubgroup eQ).isCompl_iff.mp hUqVq
    let Φ : Subgroup (LowerCentralFactor P 0) ≃o
        Submodule (ZMod 2) (Additive (LowerCentralFactor P 0)) :=
      Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule (n := 2))
    have hWZ : IsCompl W Z := by
      exact Φ.isCompl_iff.mp hWgroupZgroup
    let eWgroupZgroup : Wgroup ≃* Zgroup :=
      (eQ.subgroupMap Uq).symm.trans (eUV.trans (eQ.subgroupMap Vq))
    let eWZ : W ≃ₗ[ZMod 2] Z :=
      zmod2LinearEquivOfSubgroupMulEquiv Wgroup Zgroup eWgroupZgroup
    have heWZ_val (w : W) :
        ((eWZ w : Z) : Additive (LowerCentralFactor P 0)) =
          Additive.ofMul
            (eQ ((eUV ((eQ.subgroupMap Uq).symm
              (⟨w.1.toMul, w.property⟩ : Wgroup)) : Vq) :
                P ⧸ Subgroup.center P)) := by
      rfl
    have heWZ : ∀ w : W, eWZ (TW w) = TZ (eWZ w) := by
      intro w
      let wg : Wgroup := ⟨w.1.toMul, w.property⟩
      let q : Uq := (eQ.subgroupMap Uq).symm wg
      have hqmap : eQ (q : P ⧸ Subgroup.center P) = w.1.toMul := by
        exact congrArg Subtype.val ((eQ.subgroupMap Uq).apply_symm_apply wg)
      let actorQ : Uq :=
        ⟨qsmul actor (q : P ⧸ Subgroup.center P),
          (hUq actor (q : P ⧸ Subgroup.center P)).mp q.property⟩
      let twg : Wgroup := ⟨(T w).toMul, hWforward w w.property⟩
      have hactorMap : eQ (actorQ : P ⧸ Subgroup.center P) = (T w).toMul := by
        apply Additive.ofMul.injective
        change Additive.ofMul
          (eQ (qsmul actor (q : P ⧸ Subgroup.center P))) = T w
        calc
          Additive.ofMul
              (eQ (qsmul actor (q : P ⧸ Subgroup.center P))) =
            T (Additive.ofMul (eQ (q : P ⧸ Subgroup.center P))) :=
              heQ_actor (q : P ⧸ Subgroup.center P)
          _ = T w := congrArg T (congrArg Additive.ofMul hqmap)
      have hpreimage : (eQ.subgroupMap Uq).symm twg = actorQ := by
        apply Subtype.ext
        apply eQ.injective
        calc
          eQ (((eQ.subgroupMap Uq).symm twg : Uq) :
              P ⧸ Subgroup.center P) = (twg : Wgroup) :=
            congrArg Subtype.val ((eQ.subgroupMap Uq).apply_symm_apply twg)
          _ = eQ (actorQ : P ⧸ Subgroup.center P) := hactorMap.symm
      have htwg :
          (⟨(TW w).1.toMul, (TW w).property⟩ : Wgroup) = twg := by
        apply Subtype.ext
        exact congrArg Additive.toMul (hTW_val w)
      apply Subtype.ext
      rw [heWZ_val (TW w), hTZ_val (eWZ w), heWZ_val w, htwg]
      change Additive.ofMul
          (eQ ((eUV ((eQ.subgroupMap Uq).symm twg) : Vq) :
            P ⧸ Subgroup.center P)) =
        T (Additive.ofMul
          (eQ ((eUV q : Vq) : P ⧸ Subgroup.center P)))
      rw [hpreimage]
      calc
        Additive.ofMul
            (eQ ((eUV actorQ : Vq) : P ⧸ Subgroup.center P)) =
          Additive.ofMul
            (eQ (qsmul actor ((eUV q : Vq) : P ⧸ Subgroup.center P))) := by
              exact congrArg (fun z : P ⧸ Subgroup.center P =>
                Additive.ofMul (eQ z)) (heUV actor q)
        _ = T (Additive.ofMul
            (eQ ((eUV q : Vq) : P ⧸ Subgroup.center P))) :=
          heQ_actor ((eUV q : Vq) : P ⧸ Subgroup.center P)
    have hW_card : Nat.card W = Nat.card U := by
      calc
        Nat.card W = Nat.card Wgroup :=
          natCard_zmod2SubmoduleOfSubgroup Wgroup
        _ = Nat.card Uq :=
          (Nat.card_congr (eQ.subgroupMap Uq).toEquiv).symm
        _ = Nat.card (Subgroup.center P) := hUqcard
        _ = 2 ^ n := hcenter_card
        _ = Nat.card U := hU_card.symm
    have hZ_card : Nat.card Z = Nat.card U := by
      calc
        Nat.card Z = Nat.card Zgroup :=
          natCard_zmod2SubmoduleOfSubgroup Zgroup
        _ = Nat.card Vq :=
          (Nat.card_congr (eQ.subgroupMap Vq).toEquiv).symm
        _ = Nat.card (Subgroup.center P) := hVqcard
        _ = 2 ^ n := hcenter_card
        _ = Nat.card U := hU_card.symm
    exact canonical_equivariant_iso_of_isomorphic_complements
      T U V W Z xiU xiV TW TZ hxiU_val hxiV_val hTW_val hTZ_val
      hxiU_irreducible hxiV_irreducible hUV hWZ
      (hU_card.trans hV_card.symm) hW_card hZ_card eWZ heWZ
  exact ⟨B, actor, hcriterion hcanonicalIso⟩


/-- Explicit actor-equivariant quotient summands force abstract Suzuki Type B. -/
public theorem theorem1_typeB_of_isomorphic_summands
    {K P : Type u} [Group K] [Group P] [MulDistribMulAction K P]
    (hP : IsSuzukiTwoGroup P)
    (hKcyclic : IsCyclic K) (hKfaithful : FaithfulSMul K P)
    (hKregular : ActionRegularOn K P (involutions P))
    (hIso : Theorem1IsomorphicSummands K P) :
    IsSuzukiTwoTypeB (⊤ : Subgroup P) := by
  rcases theorem1_typeB_actor_of_isomorphic_summands
      hP hKcyclic hKfaithful hKregular hIso with
    ⟨B, actor, hactorData⟩
  rcases hactorData with
    ⟨n, xi, q0, squareMap, hn, hxi_actor, hq0_ker, hq0_surj,
      hq0_actor, hL1_eq_B, hkernel1_bot, hB_le_center, hB_card,
      hfactor0_card, hinvolution_card, hactorCoordinates⟩
  rcases hactorCoordinates with
    ⟨theta, epsilon, tripleLift, cocycle, quotientCoordinates,
      centerCoordinates, lambdaUnit, hepsilon, hperiod, hanisotropic,
      hcocycle_left, hcocycle_right, hcocycle_diag, htriple_mem,
      htriple_one, htriple_surj, htriple_inj, htriple_mul,
      hsquareCoordinates, hlambda_order, hquotientCoordinates_actor,
      hcenterCoordinates_actor⟩
  refine ⟨n, hn, theta, epsilon, tripleLift, cocycle,
    hepsilon, hperiod, hanisotropic, hcocycle_left, hcocycle_right,
    hcocycle_diag, htriple_mem, htriple_one, ?_, htriple_inj, htriple_mul⟩
  intro x _hx
  exact htriple_surj x

end Higman
end External
end CFSG.BenderSuzuki
