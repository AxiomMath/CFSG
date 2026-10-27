module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreA3LatticeE6
public import CFSG.LocalAnalysis.StandardType.GGLieCoreA3DictTorus
public import CFSG.LocalAnalysis.StandardType.GGKGOrthPairs

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (StatedLieTag)
open CFSG.LieType.Steinberg.Adjoint (iform)
open scoped Matrix

private noncomputable def ggLieE6A_zeta : GGLˣ := ggZeta 3 Nat.prime_three (by norm_num)
private theorem ggLieE6A_zeta_order : orderOf ggLieE6A_zeta = 3 := by
  show orderOf (ggZeta 3 Nat.prime_three (by norm_num)) = 3
  exact (exists_zeta GGL (p := 3) Nat.prime_three (by norm_num)).choose_spec

private theorem ggLieE6A_exists_exp (a : Fin (langTag .E6).rank → GGLˣ) (h : ∀ i, a i ^ 3 = 1) :
    ∃ c : Fin (langTag .E6).rank → ZMod 3, ∀ i, a i = ggLieE6A_zeta ^ (c i).val := by
  have horder := ggLieE6A_zeta_order
  choose k hk using fun i =>
    (IsPrimitiveRoot.iff_orderOf.2 horder).eq_pow_of_mem_rootsOfUnity
      ((mem_rootsOfUnity 3 (a i)).2 (h i))
  refine ⟨fun i => (k i : ZMod 3), fun i => ?_⟩
  have hki : ggLieE6A_zeta ^ k i = a i := (hk i).2
  rw [ZMod.val_natCast, ← hki]
  exact (pow_eq_pow_of_modEq (Nat.mod_modEq (k i) 3)
    (by rw [← horder]; exact pow_orderOf_eq_one _)).symm

private theorem ggLieE6A_pair_sub_smul (a b : Fin (langTag .E6).rank → ℤ) (k : ℤ)
    (c : Fin (langTag .E6).rank → ZMod 3) :
    ggLiePair (a - k • b) c = ggLiePair a c - (k : ZMod 3) * ggLiePair b c := by
  have h : ∀ i, ((a - k • b) i : ZMod 3) * c i =
      (a i : ZMod 3) * c i - (k : ZMod 3) * ((b i : ZMod 3) * c i) := by
    intro i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sub, Int.cast_mul, sub_mul]
    ring
  unfold ggLiePair
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.mul_sum]
  exact Finset.sum_sub_distrib _ _

private theorem ggLieE6A_rootChar_eq (a : Fin (langTag .E6).rank → GGLˣ)
    (c : Fin (langTag .E6).rank → ZMod 3) (ha : ∀ i, a i = ggLieE6A_zeta ^ (c i).val)
    (γ : Fin (langTag .E6).rank → ℤ) :
    rootChar a γ = ggLieE6A_zeta ^ (ggLiePair γ c).val := by
  have hN : ((∑ i, γ i * ((c i).val : ℤ) : ℤ) : ZMod 3) = ggLiePair γ c := by
    rw [ggLiePair]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ZMod.natCast_zmod_val]
  have h1 : rootChar a γ = ggLieE6A_zeta ^ (∑ i, γ i * ((c i).val : ℤ)) := by
    rw [rootChar]
    trans ∏ i, ggLieE6A_zeta ^ (γ i * ((c i).val : ℤ))
    · refine Finset.prod_congr rfl fun i _ => ?_
      rw [ha i, ← zpow_natCast, ← zpow_mul, mul_comm]
    · rw [Finset.prod_zpow_eq_zpow_sum]
  rw [h1, ← zpow_natCast, zpow_eq_zpow_iff_modEq, ggLieE6A_zeta_order]
  exact (ZMod.intCast_eq_intCast_iff _ _ 3).mp (by
    rw [hN]
    push_cast
    rw [ZMod.natCast_zmod_val])

private theorem ggLieE6A_rootChar_eq_one_iff (a : Fin (langTag .E6).rank → GGLˣ)
    (c : Fin (langTag .E6).rank → ZMod 3) (ha : ∀ i, a i = ggLieE6A_zeta ^ (c i).val)
    (γ : Fin (langTag .E6).rank → ℤ) : rootChar a γ = 1 ↔ ggLiePair γ c = 0 := by
  rw [ggLieE6A_rootChar_eq a c ha γ]
  constructor
  · intro h
    have hdvd : 3 ∣ (ggLiePair γ c).val := by
      simpa [ggLieE6A_zeta_order] using
        (orderOf_dvd_iff_pow_eq_one (x := ggLieE6A_zeta)
          (n := (ggLiePair γ c).val)).mpr h
    exact (ZMod.val_eq_zero _).mp (Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt _))
  · intro h
    rw [h, ZMod.val_zero, pow_zero]

private theorem ggLieE6A_rootChar_sq_iff (a : Fin (langTag .E6).rank → GGLˣ)
    (c : Fin (langTag .E6).rank → ZMod 3) (ha : ∀ i, a i = ggLieE6A_zeta ^ (c i).val)
    (γ γ' : Fin (langTag .E6).rank → ℤ) :
    rootChar a γ' = rootChar a γ ^ 2 ↔ ggLiePair γ' c = 2 * ggLiePair γ c := by
  have htwo : rootChar a ((2 : ℤ) • γ) = rootChar a γ ^ 2 := by
    rw [two_zsmul, rootChar_add, pow_two]
  have hlin : (ggLiePair (γ' - (2 : ℤ) • γ) c = 0) ↔
      (ggLiePair γ' c = 2 * ggLiePair γ c) := by
    rw [ggLieE6A_pair_sub_smul]
    constructor
    · intro h; exact sub_eq_zero.mp h
    · intro h; rw [h]; ring
  have hroot : (rootChar a γ' = rootChar a γ ^ 2) ↔
      (rootChar a (γ' - (2 : ℤ) • γ) = 1) := by
    rw [rootChar_sub, htwo]
    exact mul_inv_eq_one.symm
  rw [hroot, ← hlin, ggLieE6A_rootChar_eq_one_iff a c ha (γ' - (2 : ℤ) • γ)]

private noncomputable def ggLieE6A_iotaFun (c : Fin (langTag .E6).rank → ZMod 3) :
    ModGL (langTag .E6) GGL :=
  rootDiagUnit (langTag .E6) (fun j => ggLieE6A_zeta ^ (c j).val)

private noncomputable def ggLieE6A_iota :
    Multiplicative (Fin (langTag .E6).rank → ZMod 3) →* ModGL (langTag .E6) GGL where
  toFun c := ggLieE6A_iotaFun c.toAdd
  map_one' := by
    show ggLieE6A_iotaFun (Multiplicative.toAdd (1 : Multiplicative _)) = 1
    rw [show Multiplicative.toAdd (1 : Multiplicative (Fin (langTag .E6).rank → ZMod 3)) = 0
      from toAdd_ofAdd 0]
    rw [ggLieE6A_iotaFun]
    have h : (fun j => ggLieE6A_zeta ^ ((0 : Fin (langTag .E6).rank → ZMod 3) j).val) = 1 := by
      funext j; simp
    rw [h, rootDiagUnit_one]
  map_mul' u v := by
    show ggLieE6A_iotaFun (u * v).toAdd = ggLieE6A_iotaFun u.toAdd * ggLieE6A_iotaFun v.toAdd
    rw [toAdd_mul, ggLieE6A_iotaFun, ggLieE6A_iotaFun, ggLieE6A_iotaFun, ← rootDiagUnit_mul]
    congr 1
    funext j
    rw [Pi.add_apply, Pi.mul_apply, ← pow_add]
    exact pow_eq_pow_of_modEq (by rw [ZMod.val_add]; exact Nat.mod_modEq _ 3)
      (by rw [← ggLieE6A_zeta_order]; exact pow_orderOf_eq_one _)

private theorem ggLieE6A_iota_ofAdd (c : Fin (langTag .E6).rank → ZMod 3) :
    ggLieE6A_iota (Multiplicative.ofAdd c) = ggLieE6A_iotaFun c := rfl
private theorem ggLieE6A_span_image (c₁ c₂ : Fin (langTag .E6).rank → ZMod 3) :
    Subgroup.closure {ggLieE6A_iotaFun c₁, ggLieE6A_iotaFun c₂} =
      Subgroup.closure (ggLieE6A_iotaFun ''
        (Submodule.span (ZMod 3) ({c₁, c₂} : Set (Fin (langTag .E6).rank → ZMod 3)))) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact Subgroup.subset_closure ⟨c₁, Submodule.subset_span (by simp), rfl⟩
    · exact Subgroup.subset_closure ⟨c₂, Submodule.subset_span (by simp), rfl⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨v, hv, rfl⟩
    refine Submodule.span_induction (p := fun x _ => ggLieE6A_iotaFun x ∈
      Subgroup.closure {ggLieE6A_iotaFun c₁, ggLieE6A_iotaFun c₂}) ?_ ?_ ?_ ?_ hv
    · rintro x (rfl | rfl) <;> exact Subgroup.subset_closure (by simp)
    · rw [show ggLieE6A_iotaFun 0 = 1 from by
        simp only [ggLieE6A_iotaFun, Pi.zero_apply, ZMod.val_zero, pow_zero]
        exact rootDiagUnit_one]
      exact Subgroup.one_mem _
    · intro x y _ _ hx hy
      rw [show ggLieE6A_iotaFun (x + y) = ggLieE6A_iotaFun x * ggLieE6A_iotaFun y from by
        rw [← ggLieE6A_iota_ofAdd (x + y), ofAdd_add, map_mul, ggLieE6A_iota_ofAdd,
          ggLieE6A_iota_ofAdd]]
      exact Subgroup.mul_mem _ hx hy
    · intro a x _ hx
      have hax : a • x = a.val • x := by
        conv_lhs => rw [← ZMod.natCast_zmod_val a]
        rw [Nat.cast_smul_eq_nsmul]
      rw [show ggLieE6A_iotaFun (a • x) = (ggLieE6A_iotaFun x) ^ a.val from by
        rw [hax, ← ggLieE6A_iota_ofAdd (a.val • x), ofAdd_nsmul, map_pow, ggLieE6A_iota_ofAdd]]
      exact Subgroup.pow_mem _ hx a.val

private theorem ggLieE6A_card_closure_le_three (x y : ModGL (langTag .E6) GGL) (hx : x ^ 3 = 1)
    (h : y ∈ Subgroup.zpowers x) : Nat.card (Subgroup.closure {x, y}) ≤ 3 := by
  have hclos : Subgroup.closure {x, y} = Subgroup.zpowers x := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro z hz
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with hz | hz
      · rw [hz]; exact Subgroup.mem_zpowers x
      · rw [hz]; exact h
    · rw [Subgroup.zpowers_le]
      exact Subgroup.subset_closure (by simp)
  rw [hclos, Nat.card_zpowers]
  exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hx)

private theorem ggLieE6A_indep (a₁ a₂ : Fin (langTag .E6).rank → GGLˣ)
    (c₁ c₂ : Fin (langTag .E6).rank → ZMod 3) (ha₁ : ∀ i, a₁ i = ggLieE6A_zeta ^ (c₁ i).val)
    (ha₂ : ∀ i, a₂ i = ggLieE6A_zeta ^ (c₂ i).val)
    (hcard : Nat.card (Subgroup.closure
      {rootDiagUnit (langTag .E6) a₁, rootDiagUnit (langTag .E6) a₂}) = 3 ^ 2) :
    ∀ s t : ZMod 3, s • c₁ + t • c₂ = 0 → s = 0 ∧ t = 0 := by
  intro s t hst
  by_contra hne
  push Not at hne
  have hζ3 : ggLieE6A_zeta ^ 3 = 1 := by
    rw [← ggLieE6A_zeta_order]; exact pow_orderOf_eq_one _
  have hx3 : (rootDiagUnit (langTag .E6) a₁) ^ 3 = 1 := by
    rw [rootDiagUnit_pow]
    have h1 : a₁ ^ 3 = 1 := by
      funext j
      show (a₁ j) ^ 3 = 1
      rw [ha₁ j, ← pow_mul, mul_comm, pow_mul, hζ3, one_pow]
    rw [h1, rootDiagUnit_one]
  have hy3 : (rootDiagUnit (langTag .E6) a₂) ^ 3 = 1 := by
    rw [rootDiagUnit_pow]
    have h2 : a₂ ^ 3 = 1 := by
      funext j
      show (a₂ j) ^ 3 = 1
      rw [ha₂ j, ← pow_mul, mul_comm, pow_mul, hζ3, one_pow]
    rw [h2, rootDiagUnit_one]
  have hd₁ : rootDiagUnit (langTag .E6) a₁ = ggLieE6A_iotaFun c₁ := by
    rw [show a₁ = fun j => ggLieE6A_zeta ^ (c₁ j).val from funext ha₁]; rfl
  have hd₂ : rootDiagUnit (langTag .E6) a₂ = ggLieE6A_iotaFun c₂ := by
    rw [show a₂ = fun j => ggLieE6A_zeta ^ (c₂ j).val from funext ha₂]; rfl
  have hmem : (rootDiagUnit (langTag .E6) a₂) ∈
      Subgroup.zpowers (rootDiagUnit (langTag .E6) a₁) ∨
      (rootDiagUnit (langTag .E6) a₁) ∈ Subgroup.zpowers (rootDiagUnit (langTag .E6) a₂) := by
    rcases eq_or_ne t 0 with ht | ht
    · right
      have hs : s ≠ 0 := fun hs0 => hne hs0 ht
      have h0 : s • c₁ = 0 := by simpa [ht] using hst
      have hc₁ : c₁ = 0 := (smul_eq_zero.mp h0).resolve_left hs
      have h1 : a₁ = 1 := by
        funext j; rw [ha₁ j, hc₁]; simp
      rw [h1, rootDiagUnit_one]
      exact Subgroup.one_mem _
    · left
      have h2 : c₂ = -((t⁻¹ * s) • c₁) := by
        have h1 : t⁻¹ • (s • c₁ + t • c₂) = 0 := by rw [hst, smul_zero]
        rw [smul_add, smul_smul, smul_smul, inv_mul_cancel₀ ht, one_smul] at h1
        exact eq_neg_of_add_eq_zero_right h1
      obtain ⟨a, ha⟩ : ∃ a : ZMod 3, a • c₁ = c₂ := by
        refine Submodule.mem_span_singleton.mp ?_
        rw [h2]
        exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      have haval : a • c₁ = a.val • c₁ := by
        conv_lhs => rw [← ZMod.natCast_zmod_val a]
        rw [Nat.cast_smul_eq_nsmul]
      have hpow : rootDiagUnit (langTag .E6) a₂ =
          (rootDiagUnit (langTag .E6) a₁) ^ a.val := by
        have hof : Multiplicative.ofAdd c₂ = (Multiplicative.ofAdd c₁) ^ a.val := by
          rw [← ha, haval, ofAdd_nsmul]
        rw [hd₁, hd₂, ← ggLieE6A_iota_ofAdd c₂, ← ggLieE6A_iota_ofAdd c₁, ← map_pow, hof]
      exact Subgroup.mem_zpowers_iff.mpr ⟨a.val, hpow.symm⟩
  rcases hmem with h | h
  · have hle := ggLieE6A_card_closure_le_three _ _ hx3 h
    omega
  · have hle := ggLieE6A_card_closure_le_three _ _ hy3 h
    rw [show ({rootDiagUnit (langTag .E6) a₁, rootDiagUnit (langTag .E6) a₂} :
      Set (ModGL (langTag .E6) GGL)) =
      {rootDiagUnit (langTag .E6) a₂, rootDiagUnit (langTag .E6) a₁} from by
        ext z; simp [or_comm]] at hcard
    omega

private theorem ggLieE6A_plane_eq (a₁ a₂ : Fin (langTag .E6).rank → GGLˣ)
    (c₁ c₂ e₀ e₁ : Fin (langTag .E6).rank → ZMod 3)
    (ha₁ : ∀ i, a₁ i = ggLieE6A_zeta ^ (c₁ i).val) (ha₂ : ∀ i, a₂ i = ggLieE6A_zeta ^ (c₂ i).val)
    (hspan : Submodule.span (ZMod 3) {c₁, c₂} = Submodule.span (ZMod 3) {e₀, e₁}) :
    Subgroup.closure {rootDiagUnit (langTag .E6) a₁, rootDiagUnit (langTag .E6) a₂} =
      Subgroup.closure {rootDiagUnit (langTag .E6) (fun j => ggLieE6A_zeta ^ (e₀ j).val),
        rootDiagUnit (langTag .E6) (fun j => ggLieE6A_zeta ^ (e₁ j).val)} := by
  have h₁ : rootDiagUnit (langTag .E6) a₁ = ggLieE6A_iotaFun c₁ := by
    rw [show a₁ = fun j => ggLieE6A_zeta ^ (c₁ j).val from funext ha₁]; rfl
  have h₂ : rootDiagUnit (langTag .E6) a₂ = ggLieE6A_iotaFun c₂ := by
    rw [show a₂ = fun j => ggLieE6A_zeta ^ (c₂ j).val from funext ha₂]; rfl
  rw [h₁, h₂, ggLieE6A_span_image c₁ c₂]
  change Subgroup.closure (ggLieE6A_iotaFun ''
      (Submodule.span (ZMod 3) ({c₁, c₂} : Set (Fin (langTag .E6).rank → ZMod 3)))) =
    Subgroup.closure {ggLieE6A_iotaFun e₀, ggLieE6A_iotaFun e₁}
  rw [hspan, ggLieE6A_span_image e₀ e₁]

private def ggLieE6A_cvec (β : Fin (langTag .E6).rank → ℤ) : Fin (langTag .E6).rank → ZMod 3 :=
  fun j => ((iform (Pi.single j 1) β : ℤ) : ZMod 3)

private theorem ggLieE6A_zpow_eq_val (n : ℤ) :
    ggLieE6A_zeta ^ n = ggLieE6A_zeta ^ ((n : ZMod 3).val) := by
  rw [← zpow_natCast, zpow_eq_zpow_iff_modEq, ggLieE6A_zeta_order]
  exact (ZMod.intCast_eq_intCast_iff _ _ 3).mp (by push_cast; rw [ZMod.natCast_zmod_val])

private theorem ggLieE6A_corootUnit_eq (β : Fin (langTag .E6).rank → ℤ) :
    ggLieCorootUnit β = fun j => ggLieE6A_zeta ^ (ggLieE6A_cvec β j).val := by
  funext j
  show ggLieE6A_zeta ^ iform (Pi.single j 1) β = ggLieE6A_zeta ^ (ggLieE6A_cvec β j).val
  rw [ggLieE6A_zpow_eq_val]
  rfl

private theorem ggLieE6A_pair_cvec
    (γ β : Fin (langTag .E6).rank → ℤ) :
    ggLiePair γ (ggLieE6A_cvec β) = ((iform γ β : ℤ) : ZMod 3) := by
  rw [ggLiePair, CFSG.LieType.Chevalley.iform_eq_sum_single γ β]
  simp only [ggLieE6A_cvec]
  push_cast
  rfl

private lemma ggLieE6A_jointChar_ofAdd {τ : Tag} {L : Type} [Field L]
    (a₁ a₂ : Fin τ.rank → Lˣ) (γ : Fin τ.rank → ℤ) :
    jointChar a₁ a₂ (Multiplicative.ofAdd γ) = (rootChar a₁ γ, rootChar a₂ γ) := rfl
private lemma ggLieE6A_mem_iff_of_eqvGen {τ : Tag} {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) {a b : Fin τ.rank → ℤ}
    (h : Relation.EqvGen (fun (u v : Fin τ.rank → ℤ) =>
        u ∈ kernelRoots χ ∧ v ∈ kernelRoots χ ∧
        u ⬝ᵥ (τ.symmetrizedCartan *ᵥ v) ≠ 0) a b) :
    a ∈ kernelRoots χ ↔ b ∈ kernelRoots χ := by
  induction h with
  | rel x y hxy => exact ⟨fun _ => hxy.2.1, fun _ => hxy.1⟩
  | refl x => exact Iff.rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

private lemma ggLieE6A_eqvGen_transfer_forward {τ : Tag} {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) :
    ∀ (a b : kernelRoots χ),
      Relation.EqvGen (fun (u v : kernelRoots χ) =>
        (u : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (v : Fin τ.rank → ℤ)) ≠ 0) a b →
      ∀ (hα : a.1 ∈ kernelRoots χ) (hβ : b.1 ∈ kernelRoots χ),
        Relation.EqvGen (fun (u v : Fin τ.rank → ℤ) =>
          u ∈ kernelRoots χ ∧ v ∈ kernelRoots χ ∧
          u ⬝ᵥ (τ.symmetrizedCartan *ᵥ v) ≠ 0) a.1 b.1 := by
  intro a b h
  refine Relation.EqvGen.rec (motive := fun (x y : kernelRoots χ)
      (_ : Relation.EqvGen (fun (u v : kernelRoots χ) =>
        (u : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (v : Fin τ.rank → ℤ)) ≠ 0) x y) =>
    ∀ (hα : x.1 ∈ kernelRoots χ) (hβ : y.1 ∈ kernelRoots χ),
      Relation.EqvGen (fun (u v : Fin τ.rank → ℤ) =>
        u ∈ kernelRoots χ ∧ v ∈ kernelRoots χ ∧
        u ⬝ᵥ (τ.symmetrizedCartan *ᵥ v) ≠ 0) x.1 y.1) ?_ ?_ ?_ ?_ h
  · intro x y hxy hα hβ
    exact Relation.EqvGen.rel _ _ ⟨hα, hβ, hxy⟩
  · intro x hα hβ
    exact Relation.EqvGen.refl x.1
  · intro x y hxy ih hα hβ
    exact Relation.EqvGen.symm _ _ (ih hβ hα)
  · intro x y z hxy hyz ih1 ih2 hα hβ
    exact Relation.EqvGen.trans _ _ _ (ih1 hα y.2) (ih2 y.2 hβ)

private lemma ggLieE6A_eqvGen_transfer_backward {τ : Tag} {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) :
    ∀ (a b : Fin τ.rank → ℤ),
      Relation.EqvGen (fun (u v : Fin τ.rank → ℤ) =>
        u ∈ kernelRoots χ ∧ v ∈ kernelRoots χ ∧
        u ⬝ᵥ (τ.symmetrizedCartan *ᵥ v) ≠ 0) a b →
      ∀ (hα : a ∈ kernelRoots χ) (hβ : b ∈ kernelRoots χ),
        Relation.EqvGen (fun (u v : kernelRoots χ) =>
          (u : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (v : Fin τ.rank → ℤ)) ≠ 0)
          ⟨a, hα⟩ ⟨b, hβ⟩ := by
  intro a b h
  refine Relation.EqvGen.rec (motive := fun (x y : Fin τ.rank → ℤ)
      (_ : Relation.EqvGen (fun (u v : Fin τ.rank → ℤ) =>
        u ∈ kernelRoots χ ∧ v ∈ kernelRoots χ ∧
        u ⬝ᵥ (τ.symmetrizedCartan *ᵥ v) ≠ 0) x y) =>
    ∀ (hα : x ∈ kernelRoots χ) (hβ : y ∈ kernelRoots χ),
      Relation.EqvGen (fun (u v : kernelRoots χ) =>
        (u : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (v : Fin τ.rank → ℤ)) ≠ 0)
        ⟨x, hα⟩ ⟨y, hβ⟩) ?_ ?_ ?_ ?_ h
  · intro x y hxy hα hβ
    exact Relation.EqvGen.rel _ _ hxy.2.2
  · intro x hα hβ
    exact Relation.EqvGen.refl _
  · intro x y hxy ih hα hβ
    exact Relation.EqvGen.symm _ _ (ih hβ hα)
  · intro x y z hxy hyz ih1 ih2 hα hβ
    have hy : y ∈ kernelRoots χ := (ggLieE6A_mem_iff_of_eqvGen χ hxy).1 hα
    exact Relation.EqvGen.trans _ _ _ (ih1 hα hy) (ih2 hy hβ)

private lemma ggLieE6A_eqvGen_transfer {τ : Tag} {M : Type*} [CommGroup M]
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) {α β : Fin τ.rank → ℤ}
    (hα : α ∈ kernelRoots χ) (hβ : β ∈ kernelRoots χ) :
    Relation.EqvGen (fun (u v : kernelRoots χ) =>
        (u : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (v : Fin τ.rank → ℤ)) ≠ 0)
        ⟨α, hα⟩ ⟨β, hβ⟩ ↔
      Relation.EqvGen (fun (u v : Fin τ.rank → ℤ) =>
        u ∈ kernelRoots χ ∧ v ∈ kernelRoots χ ∧
        u ⬝ᵥ (τ.symmetrizedCartan *ᵥ v) ≠ 0) α β := by
  constructor
  · intro h
    exact ggLieE6A_eqvGen_transfer_forward χ ⟨α, hα⟩ ⟨β, hβ⟩ h hα hβ
  · intro h
    exact ggLieE6A_eqvGen_transfer_backward χ α β h hα hβ

private lemma ggLieE6A_kernelRoots_eq {τ : Tag} {L : Type} [Field L]
    (a₁ a₂ : Fin τ.rank → Lˣ) (c₁ c₂ : Fin τ.rank → ZMod 3)
    (hd1 : ∀ γ, rootChar a₁ γ = 1 ↔ ggLiePair γ c₁ = 0)
    (hd2 : ∀ γ, rootChar a₂ γ = 1 ↔ ggLiePair γ c₂ = 0) :
    kernelRoots (jointChar a₁ a₂) = a3Ker τ c₁ c₂ := by
  ext γ
  simp only [kernelRoots, Set.mem_setOf_eq, a3Ker, ggLieE6A_jointChar_ofAdd,
    Prod.mk_eq_one, hd1 γ, hd2 γ]

private lemma ggLieE6A_componentRoots_eq {τ : Tag} {L : Type} [Field L]
    (a₁ a₂ : Fin τ.rank → Lˣ) (c₁ c₂ : Fin τ.rank → ZMod 3)
    (hK : kernelRoots (jointChar a₁ a₂) = a3Ker τ c₁ c₂)
    (i : KernelComponent (jointChar a₁ a₂)) (m : Fin τ.rank → ℤ)
    (hm : m ∈ componentRoots (jointChar a₁ a₂) i) :
    componentRoots (jointChar a₁ a₂) i = a3Comp τ c₁ c₂ m := by
  obtain ⟨hmk, hmi⟩ := hm
  ext α
  constructor
  · intro hα
    obtain ⟨hαk, hαi⟩ := hα
    have hαk' : α ∈ a3Ker τ c₁ c₂ := by rwa [hK] at hαk
    refine ⟨hαk', ?_⟩
    have hsub : (kernelRootSetoid (jointChar a₁ a₂)).r ⟨α, hαk⟩ ⟨m, hmk⟩ :=
      Quotient.exact (hαi.trans hmi.symm)
    have hamb := (ggLieE6A_eqvGen_transfer (jointChar a₁ a₂) hαk hmk).1 hsub
    rw [hK] at hamb
    exact Relation.EqvGen.symm _ _ hamb
  · intro hα
    obtain ⟨hαk', hEqv⟩ := hα
    have hαk : α ∈ kernelRoots (jointChar a₁ a₂) := by rwa [← hK] at hαk'
    refine ⟨hαk, ?_⟩
    have hEqv' : Relation.EqvGen (fun (u v : Fin τ.rank → ℤ) =>
        u ∈ kernelRoots (jointChar a₁ a₂) ∧ v ∈ kernelRoots (jointChar a₁ a₂) ∧
        u ⬝ᵥ (τ.symmetrizedCartan *ᵥ v) ≠ 0) α m := by
      rw [← hK] at hEqv
      exact Relation.EqvGen.symm _ _ hEqv
    exact (Quotient.sound
      ((ggLieE6A_eqvGen_transfer (jointChar a₁ a₂) hαk hmk).2 hEqv')).trans hmi

private theorem ggLieE6A_pair_single (j : Fin (langTag .E6).rank)
    (c : Fin (langTag .E6).rank → ZMod 3) :
    ggLiePair (Pi.single j 1) c = c j := by
  rw [ggLiePair, Finset.sum_eq_single j (fun b _ hb => by simp [Pi.single_eq_of_ne hb])
    (fun hj => absurd (Finset.mem_univ j) hj)]
  simp

private theorem ggLieE6A_pair_add (γ : Fin (langTag .E6).rank → ℤ)
    (x y : Fin (langTag .E6).rank → ZMod 3) :
    ggLiePair γ (x + y) = ggLiePair γ x + ggLiePair γ y := by
  simp only [ggLiePair, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private theorem ggLieE6A_pair_smul (γ : Fin (langTag .E6).rank → ℤ) (a : ZMod 3)
    (x : Fin (langTag .E6).rank → ZMod 3) :
    ggLiePair γ (a • x) = a * ggLiePair γ x := by
  simp only [ggLiePair, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem ggLieE6A_solve (p v x : ZMod 3) (h : x - v * p = 2 * x) :
    x = (-p) * v := by
  have h6 : x - 2 * x = v * p := by
    calc x - 2 * x = (x - v * p - 2 * x) + v * p := by abel
      _ = 0 + v * p := by congr 1; rw [h]; abel
      _ = v * p := zero_add _
  have h8 : -x = v * p := by
    have hx2 : x - 2 * x = -x := by rw [two_mul]; abel
    rwa [hx2] at h6
  have h1 : -(v * p) = (-p) * v := by rw [mul_comm v p]; exact (neg_mul p v).symm
  calc x = -(-x) := (neg_neg x).symm
    _ = -(v * p) := by rw [h8]
    _ = (-p) * v := h1

private theorem ggLieE6A_solve_two (p₀ v₀ p₁ v₁ x : ZMod 3)
    (h : x - v₀ * p₀ - v₁ * p₁ = 2 * x) :
    x = (-p₀) * v₀ + (-p₁) * v₁ := by
  have h6 : x - 2 * x = v₀ * p₀ + v₁ * p₁ := by
    calc x - 2 * x = (x - v₀ * p₀ - v₁ * p₁ - 2 * x) + (v₀ * p₀ + v₁ * p₁) := by abel
      _ = 0 + (v₀ * p₀ + v₁ * p₁) := by congr 1; rw [h]; abel
      _ = v₀ * p₀ + v₁ * p₁ := zero_add _
  have h8 : -x = v₀ * p₀ + v₁ * p₁ := by
    have hx2 : x - 2 * x = -x := by rw [two_mul]; abel
    rwa [hx2] at h6
  have h1 : -(v₀ * p₀) = (-p₀) * v₀ := by rw [mul_comm v₀ p₀]; exact (neg_mul p₀ v₀).symm
  have h2 : -(v₁ * p₁) = (-p₁) * v₁ := by rw [mul_comm v₁ p₁]; exact (neg_mul p₁ v₁).symm
  calc x = -(-x) := (neg_neg x).symm
    _ = -(v₀ * p₀ + v₁ * p₁) := by rw [h8]
    _ = (-p₀) * v₀ + (-p₁) * v₁ := by
      rw [show -(v₀ * p₀ + v₁ * p₁) = -(v₀ * p₀) + -(v₁ * p₁) from
        neg_add (v₀ * p₀) (v₁ * p₁), h1, h2]

private theorem ggLieE6A_pair_refl
    {β : Fin (langTag .E6).rank → ℤ} (hβ : IsRoot (langTag .E6) β)
    (γ : Fin (langTag .E6).rank → ℤ) (c : Fin (langTag .E6).rank → ZMod 3) :
    ggLiePair (rootReflection β • γ) c =
      ggLiePair γ c - ((iform β γ : ℤ) : ZMod 3) * ggLiePair β c := by
  have hβ2 : iform β β = 2 := CFSG.SeitzReduction.EPilot.iform_self_eq_two (Or.inl rfl) hβ
  have hcp : corootPair β γ = iform β γ := by
    have h := corootPair_mul hβ γ
    rw [hβ2] at h
    omega
  rw [rootReflection_smul hβ γ, hcp]
  exact ggLieE6A_pair_sub_smul γ β (iform β γ) c

private theorem ggLieE6A_pair_invariant
    (c : Fin (langTag .E6).rank → ZMod 3) (S : Set (Fin (langTag .E6).rank → ℤ))
    (hS : ∀ ψ ∈ S, IsRoot (langTag .E6) ψ ∧ ggLiePair ψ c = 0) {u : WeylGroup (langTag .E6)}
    (hu : u ∈ Subgroup.closure {s : WeylGroup (langTag .E6) | ∃ γ ∈ S, s = rootReflection γ}) :
    ∀ γ, ggLiePair (u • γ) c = ggLiePair γ c := by
  refine Subgroup.closure_induction (p := fun u _ => ∀ γ, ggLiePair (u • γ) c = ggLiePair γ c)
    ?_ ?_ ?_ ?_ hu
  · rintro x ⟨ψ, hψ, rfl⟩ γ
    rw [ggLieE6A_pair_refl (hS ψ hψ).1 γ c, (hS ψ hψ).2]
    simp
  · intro γ; rw [one_smul]
  · intro x y _ _ hx hy γ; rw [mul_smul, hx, hy]
  · intro x _ hx γ
    have h := hx (x⁻¹ • γ)
    rw [← mul_smul, mul_inv_cancel, one_smul] at h
    exact h.symm

private theorem ggLieE6A_pair_refl_refl
    {β₀ β₁ : Fin (langTag .E6).rank → ℤ} (h₀ : IsRoot (langTag .E6) β₀)
    (h₁ : IsRoot (langTag .E6) β₁) (horth : iform β₀ β₁ = 0) (γ : Fin (langTag .E6).rank → ℤ)
    (c : Fin (langTag .E6).rank → ZMod 3) :
    ggLiePair ((rootReflection β₀ * rootReflection β₁) • γ) c =
      ggLiePair γ c - ((iform β₀ γ : ℤ) : ZMod 3) * ggLiePair β₀ c -
        ((iform β₁ γ : ℤ) : ZMod 3) * ggLiePair β₁ c := by
  have horth' : iform β₀ (rootReflection β₁ • γ) = iform β₀ γ := by
    rw [rootReflection_smul h₁ γ, CFSG.LieType.Steinberg.Adjoint.iform_sub_right,
      CFSG.LieType.Steinberg.Adjoint.iform_smul_right, horth, mul_zero, sub_zero]
  rw [mul_smul, ggLieE6A_pair_refl h₀ (rootReflection β₁ • γ) c,
    ggLieE6A_pair_refl h₁ γ c, horth']
  abel

private theorem ggLieE6A_of_refl
    {β : Fin (langTag .E6).rank → ℤ} (hβ : IsRoot (langTag .E6) β)
    (c : Fin (langTag .E6).rank → ZMod 3)
    (hl : ∀ γ, IsRoot (langTag .E6) γ →
      ggLiePair (rootReflection β • γ) c = 2 * ggLiePair γ c) :
    c = (-ggLiePair β c) • ggLieE6A_cvec β := by
  funext j
  have h := hl (Pi.single j 1) (IsRoot.basis j)
  rw [ggLieE6A_pair_refl hβ (Pi.single j 1) c, ggLieE6A_pair_single] at h
  have hcv : ((iform β (Pi.single j 1) : ℤ) : ZMod 3) = ggLieE6A_cvec β j := by
    rw [ggLieE6A_cvec, CFSG.LieType.Steinberg.Adjoint.iform_comm]
  rw [hcv] at h
  have := ggLieE6A_solve (ggLiePair β c) (ggLieE6A_cvec β j) (c j) h
  simpa [Pi.smul_apply, smul_eq_mul] using this

private theorem ggLieE6A_of_refl_refl
    {β₀ β₁ : Fin (langTag .E6).rank → ℤ} (h₀ : IsRoot (langTag .E6) β₀)
    (h₁ : IsRoot (langTag .E6) β₁) (horth : iform β₀ β₁ = 0)
    (c : Fin (langTag .E6).rank → ZMod 3)
    (hl : ∀ γ, IsRoot (langTag .E6) γ →
      ggLiePair ((rootReflection β₀ * rootReflection β₁) • γ) c = 2 * ggLiePair γ c) :
    c ∈ Submodule.span (ZMod 3) {ggLieE6A_cvec β₀, ggLieE6A_cvec β₁} := by
  rw [Submodule.mem_span_pair]
  refine ⟨-ggLiePair β₀ c, -ggLiePair β₁ c, ?_⟩
  funext j
  have h := hl (Pi.single j 1) (IsRoot.basis j)
  rw [ggLieE6A_pair_refl_refl h₀ h₁ horth (Pi.single j 1) c, ggLieE6A_pair_single] at h
  have hcv₀ : ((iform β₀ (Pi.single j 1) : ℤ) : ZMod 3) = ggLieE6A_cvec β₀ j := by
    rw [ggLieE6A_cvec, CFSG.LieType.Steinberg.Adjoint.iform_comm]
  have hcv₁ : ((iform β₁ (Pi.single j 1) : ℤ) : ZMod 3) = ggLieE6A_cvec β₁ j := by
    rw [ggLieE6A_cvec, CFSG.LieType.Steinberg.Adjoint.iform_comm]
  rw [hcv₀, hcv₁] at h
  have := ggLieE6A_solve_two (ggLiePair β₀ c) (ggLieE6A_cvec β₀ j)
    (ggLiePair β₁ c) (ggLieE6A_cvec β₁ j) (c j) h
  rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  exact this.symm

private theorem ggLieE6A_not_dep (c₁ c₂ : Fin (langTag .E6).rank → ZMod 3)
    (hind : ∀ s t : ZMod 3, s • c₁ + t • c₂ = 0 → s = 0 ∧ t = 0)
    (v : Fin (langTag .E6).rank → ZMod 3) (lam₁ lam₂ : ZMod 3)
    (h₁ : c₁ = lam₁ • v) (h₂ : c₂ = lam₂ • v) : False := by
  rcases eq_or_ne lam₂ 0 with h | h
  · rcases eq_or_ne lam₁ 0 with h1 | h1
    · have hc : c₁ = 0 := by rw [h₁, h1, zero_smul]
      exact one_ne_zero (hind 1 0 (by simp [hc])).1
    · have hc : c₂ = 0 := by rw [h₂, h, zero_smul]
      exact one_ne_zero (hind 0 1 (by simp [hc])).2
  · have hzero : lam₂ • c₁ + (-lam₁) • c₂ = 0 := by
      rw [h₁, h₂, smul_smul, smul_smul, ← add_smul,
        show (-lam₁) * lam₂ = -(lam₁ * lam₂) from neg_mul lam₁ lam₂,
        show lam₂ * lam₁ + -(lam₁ * lam₂) = 0 from by rw [mul_comm lam₂ lam₁]; abel, zero_smul]
    exact h (hind lam₂ (-lam₁) hzero).1

private theorem ggLieE6A_cases
    (c₁ c₂ : Fin (langTag .E6).rank → ZMod 3)
    (hind : ∀ s t : ZMod 3, s • c₁ + t • c₂ = 0 → s = 0 ∧ t = 0)
    {β₀ β₁ : Fin (langTag .E6).rank → ℤ} (h₀ : IsRoot (langTag .E6) β₀)
    (h₁ : IsRoot (langTag .E6) β₁) (horth : iform β₀ β₁ = 0) (x : WeylGroup (langTag .E6))
    (hx : x = 1 ∨ x = rootReflection β₀ ∨ x = rootReflection β₁ ∨
      x = rootReflection β₀ * rootReflection β₁)
    (hl₁ : ∀ γ, IsRoot (langTag .E6) γ → ggLiePair (x • γ) c₁ = 2 * ggLiePair γ c₁)
    (hl₂ : ∀ γ, IsRoot (langTag .E6) γ → ggLiePair (x • γ) c₂ = 2 * ggLiePair γ c₂) :
    x = rootReflection β₀ * rootReflection β₁ ∧
      Submodule.span (ZMod 3) {c₁, c₂} ≤
        Submodule.span (ZMod 3) {ggLieE6A_cvec β₀, ggLieE6A_cvec β₁} := by
  have hzero_of : ∀ c : Fin (langTag .E6).rank → ZMod 3,
      (∀ j, c j = 2 * c j) → c = 0 := by
    intro c hc
    funext j
    have h2 : c j - 2 * c j = 0 := sub_eq_zero.mpr (hc j)
    have h3 : -c j = 0 := by
      rwa [show c j - 2 * c j = -c j from by rw [two_mul]; abel] at h2
    exact neg_eq_zero.mp h3
  rcases hx with hx | hx | hx | hx
  · exfalso
    have hc₁ : c₁ = 0 := hzero_of c₁ fun j => by
      have h := hl₁ (Pi.single j 1) (IsRoot.basis j)
      rwa [hx, one_smul, ggLieE6A_pair_single] at h
    have hc₂ : c₂ = 0 := hzero_of c₂ fun j => by
      have h := hl₂ (Pi.single j 1) (IsRoot.basis j)
      rwa [hx, one_smul, ggLieE6A_pair_single] at h
    exact one_ne_zero (hind 1 0 (by simp [hc₁])).1
  · exfalso
    exact ggLieE6A_not_dep c₁ c₂ hind (ggLieE6A_cvec β₀) (-ggLiePair β₀ c₁) (-ggLiePair β₀ c₂)
      (ggLieE6A_of_refl h₀ c₁ (fun γ hγ => by rw [← hx]; exact hl₁ γ hγ))
      (ggLieE6A_of_refl h₀ c₂ (fun γ hγ => by rw [← hx]; exact hl₂ γ hγ))
  · exfalso
    exact ggLieE6A_not_dep c₁ c₂ hind (ggLieE6A_cvec β₁) (-ggLiePair β₁ c₁) (-ggLiePair β₁ c₂)
      (ggLieE6A_of_refl h₁ c₁ (fun γ hγ => by rw [← hx]; exact hl₁ γ hγ))
      (ggLieE6A_of_refl h₁ c₂ (fun γ hγ => by rw [← hx]; exact hl₂ γ hγ))
  · refine ⟨hx, ?_⟩
    rw [Submodule.span_le]
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with hv | hv
    · rw [hv]
      exact ggLieE6A_of_refl_refl h₀ h₁ horth c₁ (fun γ hγ => by rw [← hx]; exact hl₁ γ hγ)
    · rw [hv]
      exact ggLieE6A_of_refl_refl h₀ h₁ horth c₂ (fun γ hγ => by rw [← hx]; exact hl₂ γ hγ)

private theorem ggLieE6A_span_eq (c₁ c₂ e₀ e₁ : Fin (langTag .E6).rank → ZMod 3)
    (hind : ∀ s t : ZMod 3, s • c₁ + t • c₂ = 0 → s = 0 ∧ t = 0)
    (hle : Submodule.span (ZMod 3) {c₁, c₂} ≤ Submodule.span (ZMod 3) {e₀, e₁}) :
    Submodule.span (ZMod 3) {c₁, c₂} = Submodule.span (ZMod 3) {e₀, e₁} := by
  refine le_antisymm hle ?_
  rw [Submodule.span_le]
  obtain ⟨a₁, b₁, h₁⟩ := Submodule.mem_span_pair.mp
    (hle (Submodule.subset_span (by simp : c₁ ∈ ({c₁, c₂} : Set _))))
  obtain ⟨a₂, b₂, h₂⟩ := Submodule.mem_span_pair.mp
    (hle (Submodule.subset_span (by simp : c₂ ∈ ({c₁, c₂} : Set _))))
  have h1i : ∀ i, a₁ * e₀ i + b₁ * e₁ i = c₁ i := fun i => by
    have := congrFun h₁ i
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this
  have h2i : ∀ i, a₂ * e₀ i + b₂ * e₁ i = c₂ i := fun i => by
    have := congrFun h₂ i
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this
  have hD : a₁ * b₂ - a₂ * b₁ ≠ 0 := by
    intro hD0
    have hrel : a₁ * b₂ = a₂ * b₁ := sub_eq_zero.mp hD0
    have hnull : ∃ s t : ZMod 3, (s, t) ≠ 0 ∧ a₁ * s + a₂ * t = 0 ∧ b₁ * s + b₂ * t = 0 := by
      rcases eq_or_ne (a₁, a₂) 0 with ha | ha
      · have ha1 : a₁ = 0 := (Prod.ext_iff.mp ha).1
        have ha2 : a₂ = 0 := (Prod.ext_iff.mp ha).2
        rcases eq_or_ne (b₁, b₂) 0 with hb | hb
        · have hb1 : b₁ = 0 := (Prod.ext_iff.mp hb).1
          refine ⟨1, 0, by simp, by simp [ha1, ha2], by simp [hb1]⟩
        · refine ⟨b₂, -b₁, ?_, by simp [ha1, ha2], ?_⟩
          · intro h
            have h1 : b₂ = 0 := (Prod.ext_iff.mp h).1
            have h2 : -b₁ = 0 := (Prod.ext_iff.mp h).2
            exact hb (Prod.ext (neg_eq_zero.mp h2) h1)
          · fin_cases b₁ <;> fin_cases b₂ <;> decide
      · refine ⟨a₂, -a₁, ?_, by fin_cases a₁ <;> fin_cases a₂ <;> decide, ?_⟩
        · intro h
          have h1 : a₂ = 0 := (Prod.ext_iff.mp h).1
          have h2 : -a₁ = 0 := (Prod.ext_iff.mp h).2
          exact ha (Prod.ext (neg_eq_zero.mp h2) h1)
        · have : b₁ * a₂ + b₂ * (-a₁) = -(a₁ * b₂ - a₂ * b₁) := by
            fin_cases a₁ <;> fin_cases b₁ <;> fin_cases a₂ <;> fin_cases b₂ <;> decide
          rw [this, hD0]
          rfl
    obtain ⟨s, t, hne, hs, ht⟩ := hnull
    have hzero : s • c₁ + t • c₂ = 0 := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
      rw [← h1i i, ← h2i i]
      have : s * (a₁ * e₀ i + b₁ * e₁ i) + t * (a₂ * e₀ i + b₂ * e₁ i) =
          (a₁ * s + a₂ * t) * e₀ i + (b₁ * s + b₂ * t) * e₁ i := by ring_nf
      rw [this, hs, ht]
      ring_nf
    obtain ⟨hs0, ht0⟩ := hind s t hzero
    exact hne (Prod.ext hs0 ht0)
  have he₀ : e₀ ∈ Submodule.span (ZMod 3) {c₁, c₂} := by
    have h : (a₁ * b₂ - a₂ * b₁) • e₀ = b₂ • c₁ - b₁ • c₂ := by
      funext i
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rw [← h1i i, ← h2i i]
      ring
    rw [show e₀ = (a₁ * b₂ - a₂ * b₁)⁻¹ • (b₂ • c₁ - b₁ • c₂) by
      rw [← h, smul_smul, inv_mul_cancel₀ hD, one_smul]]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
  have he₁ : e₁ ∈ Submodule.span (ZMod 3) {c₁, c₂} := by
    have h : (a₁ * b₂ - a₂ * b₁) • e₁ = a₁ • c₂ - a₂ • c₁ := by
      funext i
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      rw [← h1i i, ← h2i i]
      ring
    rw [show e₁ = (a₁ * b₂ - a₂ * b₁)⁻¹ • (a₁ • c₂ - a₂ • c₁) by
      rw [← h, smul_smul, inv_mul_cancel₀ hD, one_smul]]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
  intro x hx
  rcases hx with rfl | rfl
  · exact he₀
  · exact he₁


private theorem ggLieE6A_kernel_iff
    {β₀ β₁ : Fin (langTag .E6).rank → ℤ} (h₀ : IsRoot (langTag .E6) β₀)
    (h₁ : IsRoot (langTag .E6) β₁) (c₁ c₂ : Fin (langTag .E6).rank → ZMod 3)
    (hspan : Submodule.span (ZMod 3) {c₁, c₂} =
      Submodule.span (ZMod 3) {ggLieE6A_cvec β₀, ggLieE6A_cvec β₁})
    {γ : Fin (langTag .E6).rank → ℤ} (hγ : IsRoot (langTag .E6) γ) :
    (ggLiePair γ c₁ = 0 ∧ ggLiePair γ c₂ = 0) ↔ (iform γ β₀ = 0 ∧ iform γ β₁ = 0) := by
  have key : (ggLiePair γ c₁ = 0 ∧ ggLiePair γ c₂ = 0) ↔
      (ggLiePair γ (ggLieE6A_cvec β₀) = 0 ∧ ggLiePair γ (ggLieE6A_cvec β₁) = 0) := by
    constructor
    · intro h
      have hm₀ : ggLieE6A_cvec β₀ ∈ Submodule.span (ZMod 3) {c₁, c₂} := by
        rw [hspan]; exact Submodule.subset_span (by simp)
      have hm₁ : ggLieE6A_cvec β₁ ∈ Submodule.span (ZMod 3) {c₁, c₂} := by
        rw [hspan]; exact Submodule.subset_span (by simp)
      obtain ⟨r₀, s₀, hr₀⟩ := Submodule.mem_span_pair.mp hm₀
      obtain ⟨r₁, s₁, hr₁⟩ := Submodule.mem_span_pair.mp hm₁
      constructor
      · rw [← hr₀, ggLieE6A_pair_add, ggLieE6A_pair_smul, ggLieE6A_pair_smul, h.1, h.2]
        ring
      · rw [← hr₁, ggLieE6A_pair_add, ggLieE6A_pair_smul, ggLieE6A_pair_smul, h.1, h.2]
        ring
    · intro h
      have hm₁ : c₁ ∈ Submodule.span (ZMod 3) {ggLieE6A_cvec β₀, ggLieE6A_cvec β₁} := by
        rw [← hspan]; exact Submodule.subset_span (by simp)
      have hm₂ : c₂ ∈ Submodule.span (ZMod 3) {ggLieE6A_cvec β₀, ggLieE6A_cvec β₁} := by
        rw [← hspan]; exact Submodule.subset_span (by simp)
      obtain ⟨r₁, s₁, hr₁⟩ := Submodule.mem_span_pair.mp hm₁
      obtain ⟨r₂, s₂, hr₂⟩ := Submodule.mem_span_pair.mp hm₂
      constructor
      · rw [← hr₁, ggLieE6A_pair_add, ggLieE6A_pair_smul, ggLieE6A_pair_smul, h.1, h.2]
        ring
      · rw [← hr₂, ggLieE6A_pair_add, ggLieE6A_pair_smul, ggLieE6A_pair_smul, h.1, h.2]
        ring
  rw [key, ggLieE6A_pair_cvec γ β₀, ggLieE6A_pair_cvec γ β₁]
  exact ⟨fun h => ⟨(CFSG.StandardType.KGL.iform_zmod_three_eq_zero_iff hγ h₀).mp h.1,
      (CFSG.StandardType.KGL.iform_zmod_three_eq_zero_iff hγ h₁).mp h.2⟩,
    fun h => ⟨(CFSG.StandardType.KGL.iform_zmod_three_eq_zero_iff hγ h₀).mpr h.1,
      (CFSG.StandardType.KGL.iform_zmod_three_eq_zero_iff hγ h₁).mpr h.2⟩⟩

theorem ggLieA3LatticeE6_of_struct
    (hS : A3SpecE6Struct) : GGLieA3LatticeE6 := by
  intro w w' a₁ a₂ h₃₁ h₃₂ hch₁ hch₂ hcard i hnc hw' hww'
  obtain ⟨c₁, hc₁⟩ := ggLieE6A_exists_exp a₁ h₃₁
  obtain ⟨c₂, hc₂⟩ := ggLieE6A_exists_exp a₂ h₃₂
  have hindep := ggLieE6A_indep a₁ a₂ c₁ c₂ hc₁ hc₂ hcard
  have hd1 : ∀ γ, rootChar a₁ γ = 1 ↔ ggLiePair γ c₁ = 0 :=
    fun γ => ggLieE6A_rootChar_eq_one_iff a₁ c₁ hc₁ γ
  have hd2 : ∀ γ, rootChar a₂ γ = 1 ↔ ggLiePair γ c₂ = 0 :=
    fun γ => ggLieE6A_rootChar_eq_one_iff a₂ c₂ hc₂ γ
  have hK := ggLieE6A_kernelRoots_eq a₁ a₂ c₁ c₂ hd1 hd2
  obtain ⟨m, hm⟩ : (componentRoots (jointChar a₁ a₂) i).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by rw [hnc]; norm_num)
  have hcomp := ggLieE6A_componentRoots_eq a₁ a₂ c₁ c₂ hK i m hm
  have hmk : m ∈ a3Ker (langTag .E6) c₁ c₂ := by
    rw [← hK]
    exact hm.1
  have hnc' : (a3Comp (langTag .E6) c₁ c₂ m).ncard = 12 := by
    rw [← hcomp]
    exact hnc
  obtain ⟨β₀, β₁, h₀, h₁, horth, -, horthc, ⟨ψ₀, hψ₀, ψ₁, hψ₁, hψ⟩, hsum, hstab⟩ :=
    hS c₁ c₂ hindep m hmk hnc'
  have hker : ∀ ψ ∈ componentRoots (jointChar a₁ a₂) i,
      IsRoot (langTag .E6) ψ ∧ ggLiePair ψ c₁ = 0 ∧ ggLiePair ψ c₂ = 0 := by
    intro ψ hψ'
    have h := hψ'.1
    rw [hK] at h
    exact h
  have hxfix : ∀ γ ∈ a3Comp (langTag .E6) c₁ c₂ m, (w'⁻¹ * w) • γ = γ := by
    intro γ hγ
    rw [← hcomp] at hγ
    rw [mul_smul, hww' γ hγ, inv_smul_smul]
  have hx := hstab (w'⁻¹ * w) hxfix
  have hinv₁ := ggLieE6A_pair_invariant c₁ (componentRoots (jointChar a₁ a₂) i)
    (fun ψ hψ' => ⟨(hker ψ hψ').1, (hker ψ hψ').2.1⟩) (Subgroup.inv_mem _ hw')
  have hinv₂ := ggLieE6A_pair_invariant c₂ (componentRoots (jointChar a₁ a₂) i)
    (fun ψ hψ' => ⟨(hker ψ hψ').1, (hker ψ hψ').2.2⟩) (Subgroup.inv_mem _ hw')
  have hl₁ : ∀ γ, IsRoot (langTag .E6) γ →
      ggLiePair ((w'⁻¹ * w) • γ) c₁ = 2 * ggLiePair γ c₁ := by
    intro γ hγ
    rw [mul_smul, hinv₁ (w • γ)]
    exact (ggLieE6A_rootChar_sq_iff a₁ c₁ hc₁ γ (w • γ)).1 (hch₁ γ hγ)
  have hl₂ : ∀ γ, IsRoot (langTag .E6) γ →
      ggLiePair ((w'⁻¹ * w) • γ) c₂ = 2 * ggLiePair γ c₂ := by
    intro γ hγ
    rw [mul_smul, hinv₂ (w • γ)]
    exact (ggLieE6A_rootChar_sq_iff a₂ c₂ hc₂ γ (w • γ)).1 (hch₂ γ hγ)
  obtain ⟨hxeq, hle⟩ := ggLieE6A_cases c₁ c₂ hindep h₀ h₁ horth (w'⁻¹ * w) hx hl₁ hl₂
  have hspan := ggLieE6A_span_eq c₁ c₂ (ggLieE6A_cvec β₀) (ggLieE6A_cvec β₁) hindep hle
  have hker_eq : a3Ker (langTag .E6) c₁ c₂ =
      {γ | IsRoot (langTag .E6) γ ∧ iform γ β₀ = 0 ∧ iform γ β₁ = 0} := by
    ext γ
    constructor
    · rintro ⟨hγ, p₁, p₂⟩
      exact ⟨hγ, (ggLieE6A_kernel_iff h₀ h₁ c₁ c₂ hspan hγ).1 ⟨p₁, p₂⟩⟩
    · rintro ⟨hγ, o₀, o₁⟩
      obtain ⟨p₁, p₂⟩ := (ggLieE6A_kernel_iff h₀ h₁ c₁ c₂ hspan hγ).2 ⟨o₀, o₁⟩
      exact ⟨hγ, p₁, p₂⟩
  have hcomp_eq : a3Comp (langTag .E6) c₁ c₂ m =
      {γ | IsRoot (langTag .E6) γ ∧ iform γ β₀ = 0 ∧ iform γ β₁ = 0} := by
    ext γ
    constructor
    · intro hγ
      have hγ' : γ ∈ a3Ker (langTag .E6) c₁ c₂ := hγ.1
      rw [hker_eq] at hγ'
      exact hγ'
    · rintro ⟨hγ, o₀, o₁⟩
      exact (horthc γ hγ).1 ⟨o₀, o₁⟩
  refine ⟨β₀, β₁, h₀, h₁, horth, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hK, hcomp, hker_eq, hcomp_eq]
  · rw [hcomp, hcomp_eq]
  · calc w = w' * (w'⁻¹ * w) := by group
      _ = w' * (rootReflection β₀ * rootReflection β₁) := by rw [hxeq]
      _ = w' * rootReflection β₀ * rootReflection β₁ := by rw [mul_assoc]
  · exact ⟨ψ₀, by rw [hcomp]; exact hψ₀, ψ₁, by rw [hcomp]; exact hψ₁, hψ⟩
  · intro ψ hψ'
    rw [hcomp] at hψ'
    obtain ⟨x, hx', y, hy', hxy⟩ := hsum ψ hψ'
    exact ⟨x, by rw [hcomp]; exact hx', y, by rw [hcomp]; exact hy', hxy⟩
  · rw [ggLieE6A_plane_eq a₁ a₂ c₁ c₂ (ggLieE6A_cvec β₀) (ggLieE6A_cvec β₁) hc₁ hc₂ hspan,
      ggLieE6A_corootUnit_eq β₀, ggLieE6A_corootUnit_eq β₁]

theorem ggLieA3LatticeE6_of_certificate :
    GGLieA3LatticeE6 :=
  ggLieA3LatticeE6_of_struct a3SpecE6Struct_of_certificate

end CFSG.StandardType.LieCore
