module

public import CFSG.LocalAnalysis.StandardType.GGSporKOrd7Defs
public import CFSG.LocalAnalysis.StandardType.GGSporKOrd7Lift
public import CFSG.LieType.ChevTwo.OppCl.AutLifts
public import CFSG.LieType.BorelTits.OrthogonalModels
public import CFSG.LieType.Universal.Spin.Forms
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalModelAbelianization
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
public import CFSG.ClassicalGroups.Orthogonal.Matrix
public import CFSG.ClassicalGroups.Orthogonal.Simple
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalAnisotropicPlaneRegular
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasThree
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.Open

private lemma lr2oom_scalars_subgroupOf_statedOmega_eq_bot
    {K : Type} [Field K] [CharP K 2] {ι : Type} [Fintype ι] [DecidableEq ι]
    (Q : (ι → K) → K)
    (hQsmul : ∀ (c : K) (v : ι → K), Q (c • v) = c ^ 2 * Q v)
    (hv : ∃ v : ι → K, Q v ≠ 0) :
    (StatedScalars ι K).subgroupOf (StatedOmega Q) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  rintro x hx
  rw [Subgroup.mem_subgroupOf] at hx
  obtain ⟨c, hc⟩ := hx
  obtain ⟨v, hv⟩ := hv
  have hmem := CFSG.LieType.BorelTits.statedOmega_le_orthGroup Q x.2
  have hpres := CFSG.LieType.BorelTits.orthGroup_preserves Q hmem v
  rw [← hc] at hpres
  have hscalar : Matrix.mulVec
      (((Matrix.GeneralLinearGroup.scalar ι c : GL ι K) : Matrix ι ι K)) v = c • v := by
    simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.mulVec_diagonal, Units.smul_def]
  rw [hscalar] at hpres
  have hpresK : Q ((c : K) • v) = Q v := by simpa only [Units.smul_def] using hpres
  have hc2 : (c : K) ^ 2 = 1 := by
    apply mul_right_cancel₀ hv
    have h := hQsmul (c : K) v
    rw [hpresK] at h
    rw [one_mul]
    exact h.symm
  have hc1 : c = 1 := by
    apply Units.ext
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    have hzero : ((c : K) - 1) ^ 2 = 0 := by
      have h : ((c : K) - 1) ^ 2 = c ^ 2 + 1 ^ 2 := by
        rw [sub_sq]
        linear_combination (-(c * 1)) * h2
      rw [h, hc2, one_pow, ← two_mul, h2, zero_mul]
    have hcK : (c : K) = 1 := sub_eq_zero.mp (sq_eq_zero_iff.mp hzero)
    exact hcK
  apply Subtype.ext
  rw [← hc, hc1, map_one]
  rfl

private lemma lr2oom_semiIsoQ_tau_eq_one
    {K V : Type} [Field K] [AddCommGroup V] [Module K V] [CharP K 2]
    {Φ : CFSG.LieType.BorelTits.QuadForm K V} {r : Equiv.Perm V}
    (hsmul : ∀ (c : K) (v : V), r (c • v) = c • r v)
    (hP : CFSG.LieType.ChevTwo.OppCl.SemiIsoQ Φ r)
    {v₀ : V} (hv₀ : Φ.Q v₀ ≠ 0) :
    ∀ v, Φ.Q (r v) = Φ.Q v := by
  obtain ⟨τ, hτ⟩ := hP
  have hτv : τ (Φ.Q v₀) ≠ 0 := fun h => hv₀ (τ.injective (by rw [h, map_zero]))
  have key : ∀ c : K, τ c = c := by
    intro c
    have h1 := hτ (c • v₀)
    rw [hsmul c v₀, Φ.Q_smul c (r v₀), Φ.Q_smul c v₀, map_mul, map_pow, hτ v₀] at h1
    have hc : c ^ 2 = τ c ^ 2 := mul_right_cancel₀ hτv h1
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    have hzero : ((c : K) - τ c) ^ 2 = 0 := by
      have h : ((c : K) - τ c) ^ 2 = c ^ 2 + (τ c) ^ 2 := by
        rw [sub_sq]
        linear_combination (-(c * τ c)) * h2
      rw [h, hc, ← two_mul, h2, zero_mul]
    exact (sub_eq_zero.mp (sq_eq_zero_iff.mp hzero)).symm
  intro v
  rw [hτ v, key (Φ.Q v)]

private lemma lr2oom_pow_apply_of_apply_eq
    {K V : Type} [Field K] [AddCommMonoid V] [Module K V]
    (e : V ≃ₗ[K] V) (r : Equiv.Perm V) (he : ∀ v, e v = r v) (k : ℕ) (v : V) :
    ((e ^ k : V ≃ₗ[K] V) : V → V) v = (r ^ k) v := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ, pow_succ]
      change (e ^ k) (e v) = (r ^ k) (r v)
      rw [ih (e v), he v]

private lemma lr2oom_quadMinus_exists_ne_zero
    {K : Type} [Field K] [Finite K] (n : ℕ) (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∃ v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K,
      (CFSG.LieType.BorelTits.quadMinusForm n K b c hirr).Q v ≠ 0 := by
  refine ⟨Pi.single (.inr (.inr 0)) 1, ?_⟩
  change CFSG.Open.StatedQuadMinus n K b c (Pi.single (.inr (.inr 0)) 1) ≠ 0
  rw [show CFSG.Open.StatedQuadMinus n K b c (Pi.single (.inr (.inr 0)) 1) = 1 from ?_]
  exact one_ne_zero
  simp [CFSG.Open.StatedQuadMinus, CFSG.MatrixModel.minusQuadCore, Pi.single_apply]

private lemma lr2oom_linear_isometry_mem_statedOmega
    {K : Type} [Field K] [Finite K]
    {n : ℕ} (b c : K)
    (hbound : CFSG.LocalAnalysis.ComponentInitial.IsometryAbelianizationBound 2
      (CFSG.LieType.Universal.Spin.quadMinus n K b c))
    (r : Equiv.Perm (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K))
    (hadd : ∀ u v, r (u + v) = r u + r v)
    (hsmul : ∀ (c' : K) (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K),
      r (c' • v) = c' • r v)
    (hiso : ∀ v, CFSG.LieType.Universal.Spin.quadMinus n K b c (r v) =
      CFSG.LieType.Universal.Spin.quadMinus n K b c v)
    (hm : ∃ m : ℕ, r ^ (7 ^ m) = 1) :
    ∃ h : StatedOmega (CFSG.Open.StatedQuadMinus n K b c),
      ∀ v, r v =
        CFSG.LieType.BorelTits.natRep (StatedOmega (CFSG.Open.StatedQuadMinus n K b c)) h v := by
  classical
  let rL : (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) ≃ₗ[K]
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :=
    LinearEquiv.ofBijective
      { toFun := r, map_add' := hadd, map_smul' := hsmul } r.bijective
  have hrL_apply : ∀ v, rL v = r v := fun v => rfl
  set Q := CFSG.LieType.Universal.Spin.quadMinus n K b c with hQ
  have hrL_mem : rL ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (fun v => by
      rw [hrL_apply]; exact hiso v)
  set O := TauCeti.QuadraticMap.orthogonalGroup Q with hO
  haveI : Finite ((Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) ≃ₗ[K]
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K)) :=
    Finite.of_injective (fun e : _ ≃ₗ[K] _ => (e : _ → _))
      (fun a b h => LinearEquiv.ext fun x => congrFun h x)
  haveI : Finite O := by rw [hO]; exact Subtype.finite
  have hcard : Nat.card (Abelianization O) ≤ 2 := hbound.2.2 rfl
  have hcard_dvd : Nat.card (Abelianization O) ∣ 2 := by
    have hpos : 0 < Nat.card (Abelianization O) := Nat.card_pos
    have h1 : Nat.card (Abelianization O) = 1 ∨ Nat.card (Abelianization O) = 2 := by omega
    rcases h1 with h | h <;> rw [h] <;> norm_num
  have hgm : (⟨rL, hrL_mem⟩ : O) ^ (7 ^ hm.choose) = 1 := by
    apply Subtype.ext
    change rL ^ (7 ^ hm.choose) = 1
    apply LinearEquiv.ext
    intro v
    rw [lr2oom_pow_apply_of_apply_eq rL r (fun v => rfl) (7 ^ hm.choose) v,
      hm.choose_spec]
    rfl
  have hz : Abelianization.of (⟨rL, hrL_mem⟩ : O) = 1 := by
    have hdvd7 : orderOf (Abelianization.of (⟨rL, hrL_mem⟩ : O)) ∣ 7 ^ hm.choose :=
      orderOf_dvd_iff_pow_eq_one.mpr (by rw [← map_pow, hgm, map_one])
    have hdvd2 : orderOf (Abelianization.of (⟨rL, hrL_mem⟩ : O)) ∣ 2 :=
      (orderOf_dvd_natCard _).trans hcard_dvd
    have hunit : orderOf (Abelianization.of (⟨rL, hrL_mem⟩ : O)) = 1 :=
      Nat.dvd_one.mp (by
        have := Nat.dvd_gcd hdvd2 hdvd7
        rwa [Nat.Coprime.gcd_eq_one
          (Nat.Coprime.pow_right hm.choose (by norm_num : Nat.Coprime 2 7))] at this)
    exact orderOf_eq_one_iff.mp hunit
  have hmemO' : rL ∈ ⁅O, O⁆ := by
    have hg : (⟨rL, hrL_mem⟩ : O) ∈ commutator O := by
      rw [← Abelianization.ker_of O, MonoidHom.mem_ker]
      exact hz
    have hmap : rL ∈ (commutator O).map O.subtype := ⟨⟨rL, hrL_mem⟩, hg, rfl⟩
    rwa [Subgroup.map_subtype_commutator O] at hmap
  let A : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K :=
    (CFSG.ClassicalGroups.Orthogonal.toLinEquiv
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K).symm rL
  have hA_apply : ∀ v, CFSG.ClassicalGroups.Orthogonal.toLinEquiv
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K A v = r v := by
    intro v
    rw [show CFSG.ClassicalGroups.Orthogonal.toLinEquiv
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K A = rL from
        MulEquiv.apply_symm_apply _ rL]
    exact hrL_apply v
  have hA : A ∈ StatedOmega (CFSG.Open.StatedQuadMinus n K b c) := by
    rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap
      (Q := Q) (Q₀ := CFSG.Open.StatedQuadMinus n K b c)
      (CFSG.LieType.Universal.Spin.coe_quadMinus n K b c)]
    refine Subgroup.mem_comap.mpr ?_
    change CFSG.ClassicalGroups.Orthogonal.toLinEquiv
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K A ∈ ⁅O, O⁆
    rw [show CFSG.ClassicalGroups.Orthogonal.toLinEquiv
      (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K A = rL from
        MulEquiv.apply_symm_apply _ rL]
    exact hmemO'
  refine ⟨⟨A, hA⟩, fun v => ?_⟩
  rw [LieType.BorelTits.natRep_apply]
  exact ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply A v).trans
    (hA_apply v)).symm

theorem ord7Param_POmegaMinus {n f : ℕ} (h7 : ¬ 7 ∣ f) : Ord7Param .POmegaMinus n 2 f := by
  intro R _ _ hR hmodel
  have hclass : StatedClassicalModel R .POmegaMinus n 2 f :=
    hmodel.statedClassicalModel (by decide)
  have hcl := hclass
  obtain ⟨hadm, K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hcl
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hn : 4 ≤ n := hadm.2.2
  have hf : 1 ≤ f := hadm.2.1
  have hp2 : Nat.Prime 2 := hadm.1
  haveI : CharP K 2 := by
    rw [← ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq hp2 hf hK]
    infer_instance
  have h7F : ¬ 7 ∣ Nat.card (K ≃+* K) := by
    rw [show Nat.card (K ≃+* K) = f from
      (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hp2 K hK).1]
    exact h7
  have hbound : CFSG.LocalAnalysis.ComponentInitial.IsometryAbelianizationBound 2
      (CFSG.LieType.Universal.Spin.quadMinus n K b c) :=
    CFSG.LocalAnalysis.ComponentInitial.orthogonal_model_isometry_abelianization_order_bound
      R .POmegaMinus (.inr (.inr rfl)) n 2 f hclass K hK b c hirr
      (CFSG.LieType.Universal.Spin.quadMinus n K b c)
      (CFSG.LieType.Universal.Spin.coe_quadMinus n K b c) e
  have hbot : (StatedScalars (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K).subgroupOf
      (StatedOmega (CFSG.Open.StatedQuadMinus n K b c)) = ⊥ :=
    lr2oom_scalars_subgroupOf_statedOmega_eq_bot
      (CFSG.Open.StatedQuadMinus n K b c)
      (fun c' v => (CFSG.LieType.BorelTits.quadMinusForm n K b c hirr).Q_smul c' v)
      (lr2oom_quadMinus_exists_ne_zero n b c hirr)
  have h7k : ¬ 7 ∣ Nat.card
      (QuotientGroup.mk' ((StatedScalars (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K).subgroupOf
        (StatedOmega (CFSG.Open.StatedQuadMinus n K b c)))).ker := by
    rw [QuotientGroup.ker_mk', hbot, Subgroup.card_bot]
    norm_num
  rw [Nat.card_congr (MulAut.congr e).toEquiv, Nat.card_congr e.toEquiv]
  refine ord7_factorization_le_of_lift
    (QuotientGroup.mk' ((StatedScalars (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K).subgroupOf
      (StatedOmega (CFSG.Open.StatedQuadMinus n K b c))))
    (QuotientGroup.mk'_surjective _)
    (CFSG.LieType.BorelTits.natRep (StatedOmega (CFSG.Open.StatedQuadMinus n K b c)))
    (LieType.BorelTits.natRep_injective _)
    (CFSG.LieType.ChevTwo.OppCl.SemiIsoQ
      (CFSG.LieType.BorelTits.quadMinusForm n K b c hirr))
    (CFSG.LieType.ChevTwo.OppCl.semiIsoQ_one _)
    (fun r s => CFSG.LieType.ChevTwo.OppCl.semiIsoQ_mul _)
    (fun r => CFSG.LieType.ChevTwo.OppCl.semiIsoQ_inv _)
    h7F h7k ?_ ?_
  · intro S hS α hα
    exact CFSG.LieType.ChevTwo.OppCl.induced_POmegaMinus K 7 (by norm_num) n hn b c hirr S hS α hα
  · intro r hr hP hlinr h7r
    have hadd : ∀ u v, r (u + v) = r u + r v := hr.1
    have hiso : ∀ v, CFSG.LieType.Universal.Spin.quadMinus n K b c (r v) =
        CFSG.LieType.Universal.Spin.quadMinus n K b c v := by
      have hΦ := lr2oom_semiIsoQ_tau_eq_one hlinr hP
        (lr2oom_quadMinus_exists_ne_zero n b c hirr).choose_spec
      intro v
      have := hΦ v
      rwa [show (CFSG.LieType.BorelTits.quadMinusForm n K b c hirr).Q =
          ⇑(CFSG.LieType.Universal.Spin.quadMinus n K b c) from
          (CFSG.LieType.Universal.Spin.coe_quadMinus n K b c).symm] at this
    obtain ⟨m, hm⟩ : ∃ m : ℕ, r ^ (7 ^ m) = 1 := by
      obtain ⟨m, hm⟩ := h7r ⟨r, Subgroup.mem_zpowers r⟩
      exact ⟨m, by simpa using congrArg Subtype.val hm⟩
    exact lr2oom_linear_isometry_mem_statedOmega b c hbound r hadd hlinr hiso ⟨m, hm⟩

end CFSG.StandardType.SporadicShape
