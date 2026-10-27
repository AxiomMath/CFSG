module

public import CFSG.LocalAnalysis.StandardType.GGPRankBoundsSU
public import CFSG.LocalAnalysis.StandardType.GGPRankBoundsEigen
public import CFSG.LieType.BorelTits.UnitaryForm
public import CFSG.Open.StatedAPI
import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Model

public section

namespace CFSG.StandardType

namespace PRankBounds

open Matrix CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits

section SUInner

variable {K : Type} [Field K]

theorem det_eq_one_of_mem_statedSU {n q : ℕ} {A : GL (Fin n) K} (hA : A ∈ StatedSU n q K) :
    (A : Matrix (Fin n) (Fin n) K).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSU hA

theorem charP_two_of_card_four (hK : Nat.card K = (2 ^ 1) ^ 2) : CharP K 2 :=
  (⟨Nat.prime_two, le_rfl, by rw [hK]; norm_num⟩ :
    CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 K).charP

variable [Finite K]

theorem scalars_statedSU_five_eq_bot (hK : Nat.card K = (2 ^ 1) ^ 2) :
    (StatedScalars (Fin 5) K).subgroupOf (StatedSU 5 (2 ^ 1) K) = ⊥ :=
  CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.statedScalars_subgroupOf_eq_bot hK

end SUInner

theorem exists_ne_ne_fin_five : ∀ a c : Fin 5, ∃ a₀ : Fin 5, a₀ ≠ a ∧ a₀ ≠ c := by
  decide

theorem card_subtype_ne_ne_fin_five :
    ∀ c a₀ : Fin 5, a₀ ≠ c → Fintype.card {i : Fin 5 // i ≠ c ∧ i ≠ a₀} = 3 := by
  decide

section SUFive

variable {K : Type} [Field K] [Finite K] [Fact (Nat.Prime 2)] [CharP K 2]

theorem eq_zero_of_orbit_suFive (hK : Nat.card K = (2 ^ 1) ^ 2)
    (E : Subgroup (StatedSU 5 (2 ^ 1) K)) (hE : IsElemAbelian 3 E) (h81 : 3 ^ 4 ≤ Nat.card E)
    (v : Fin 5 → K)
    (hv : ∀ x ∈ E, (unitaryForm 2 1 hK 5).β
      (((x : StatedSU 5 (2 ^ 1) K) : GL (Fin 5) K) *ᵥ v) v = 0) : v = 0 := by
  classical
  set L := AlgebraicClosure K
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  have : ExpChar L 2 := ExpChar.prime Nat.prime_two
  set ι' : K →+* L := algebraMap K L with hι'
  set Φ : GL (Fin 5) K →* GL (Fin 5) L := Matrix.GeneralLinearGroup.map ι' with hΦdef
  have hΦ : Function.Injective Φ := CFSG.RankThree.PartTwo.Sec4.map_injective_GL ι'
  set E₀ : Subgroup (GL (Fin 5) K) := E.map (StatedSU 5 (2 ^ 1) K).subtype with hE₀
  set EL : Subgroup (GL (Fin 5) L) := E₀.map Φ with hEL
  have hΦmat : ∀ x : GL (Fin 5) K, ((Φ x : GL (Fin 5) L) : Matrix (Fin 5) (Fin 5) L) =
      (x : Matrix (Fin 5) (Fin 5) K).map ι' := fun x => rfl
  have hmemEL : ∀ y ∈ EL, ∃ x ∈ E, y = Φ ((x : StatedSU 5 (2 ^ 1) K) : GL (Fin 5) K) := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩
  have hcomm : ∀ x ∈ EL, ∀ y ∈ EL, x * y = y * x := by
    intro x hx y hy
    obtain ⟨x₀, hx₀, rfl⟩ := hmemEL x hx
    obtain ⟨y₀, hy₀, rfl⟩ := hmemEL y hy
    rw [← map_mul, ← map_mul]
    congr 1
    have h : x₀ * y₀ = y₀ * x₀ :=
      congrArg Subtype.val ((isMulCommutative_iff.mp hE.1) ⟨x₀, hx₀⟩ ⟨y₀, hy₀⟩)
    exact congrArg Subtype.val h
  have hexp : ∀ x ∈ EL, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨x₀, hx₀, rfl⟩ := hmemEL x hx
    rw [← map_pow, ← Subgroup.coe_pow, hE.2 x₀ hx₀, Subgroup.coe_one, map_one]
  have hdet : ∀ x ∈ EL, (x : Matrix (Fin 5) (Fin 5) L).det = 1 := by
    intro x hx
    obtain ⟨x₀, hx₀, rfl⟩ := hmemEL x hx
    rw [hΦmat]
    change (ι'.mapMatrix ((x₀ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)).det = 1
    rw [← RingHom.map_det, det_eq_one_of_mem_statedSU x₀.2, map_one]
  have : Finite E₀ :=
    Finite.of_surjective _ ((StatedSU 5 (2 ^ 1) K).subtype.subgroupMap_surjective E)
  have : Finite EL := Finite.of_surjective _ (Φ.subgroupMap_surjective E₀)
  have hcard : Nat.card EL = Nat.card E := by
    rw [hEL, Subgroup.card_map_of_injective hΦ, hE₀,
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  have h3 : (3 : L) ≠ 0 := by
    have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
    have : (3 : L) = 1 := by linear_combination h2
    rw [this]
    exact one_ne_zero
  obtain ⟨b, d, hb⟩ := CFSG.RankThree.PartTwo.Sec4.exists_common_eigenbasis_pow_three h3 EL
    hcomm hexp
  set τ : L →+* L := frobenius L 2 with hτ
  have hτinj : Function.Injective τ := frobenius_inj L 2
  have hiso : ∀ x ∈ EL, (((x : GL (Fin 5) L) : Matrix (Fin 5) (Fin 5) L).map τ)ᵀ * 1 *
      (x : Matrix (Fin 5) (Fin 5) L) = 1 := by
    intro x hx
    obtain ⟨x₀, hx₀, rfl⟩ := hmemEL x hx
    have hU := (unitaryForm_preserves_iff hK
      ((x₀ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)).mp (statedSU_preserves hK x₀.2)
    rw [Matrix.mul_one, hΦmat]
    have hmap : (((x₀ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).map ι').map τ =
        (((x₀ : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).map
          (unitaryInvolution K 2 1)).map ι' := by
      ext i j
      simp only [Matrix.map_apply, hτ, frobenius_def, unitaryInvolution_apply, pow_one, map_pow]
    rw [hmap, ← Matrix.transpose_map, ← Matrix.map_mul, hU, Matrix.map_one _ (map_zero ι')
      (map_one ι')]
  have hdist : ∀ a c, (∀ x ∈ EL, d x a = d x c) → a = c := by
    intro a c hac
    by_contra hne
    obtain ⟨a₀, ha₀a, ha₀c⟩ := exists_ne_ne_fin_five a c
    have hall : ∀ x ∈ EL, ∀ y ∈ EL, (∀ i, i ≠ c → i ≠ a₀ → d x i = d y i) → x = y := by
      intro x hx y hy hxy
      have h1 : ∀ i, i ≠ a₀ → d x i = d y i := by
        intro i hi
        by_cases hic : i = c
        · rw [hic, ← hac x hx, ← hac y hy]
          exact hxy a hne (Ne.symm ha₀a)
        · exact hxy i hic hi
      refine CFSG.RankThree.PartTwo.Sec4.eigen_ext hb hx hy fun i => ?_
      by_cases hi : i = a₀
      · rw [hi]
        have hx' := (CFSG.RankThree.PartTwo.Sec4.eigen_det hb hx).symm.trans (hdet x hx)
        have hy' := (CFSG.RankThree.PartTwo.Sec4.eigen_det hb hy).symm.trans (hdet y hy)
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a₀)] at hx' hy'
        have hp : ∏ j ∈ Finset.univ.erase a₀, d x j = ∏ j ∈ Finset.univ.erase a₀, d y j :=
          Finset.prod_congr rfl fun j hj => h1 j (Finset.ne_of_mem_erase hj)
        rw [hp] at hx'
        have hne0 : ∏ j ∈ Finset.univ.erase a₀, d y j ≠ 0 := by
          intro h0
          rw [h0, mul_zero] at hy'
          exact zero_ne_one hy'
        exact mul_right_cancel₀ hne0 (hx'.trans hy'.symm)
      · exact h1 i hi
    have hinj : Function.Injective
        (fun (x : EL) (i : {i : Fin 5 // i ≠ c ∧ i ≠ a₀}) => d x i) := by
      intro x y hxy
      exact Subtype.ext (hall x x.2 y y.2 fun i h1 h2 => congrFun hxy ⟨i, h1, h2⟩)
    have h := CFSG.RankThree.PartTwo.Sec4.card_le_three_pow_of_injective _ hinj
      (fun x i => CFSG.RankThree.PartTwo.Sec4.eigen_pow_three hb x.2 (hexp x x.2) i)
    rw [card_subtype_ne_ne_fin_five c a₀ ha₀c, hcard] at h
    norm_num at h h81
    omega
  set vL : Fin 5 → L := fun i => ι' (v i) with hvL
  have horbL : ∀ x ∈ EL, sForm τ 1 ((x : Matrix (Fin 5) (Fin 5) L) *ᵥ vL) vL = 0 := by
    intro x hx
    obtain ⟨x₀, hx₀, rfl⟩ := hmemEL x hx
    have h0 := hv x₀ hx₀
    rw [unitaryForm_β] at h0
    have hxe : sForm τ 1 (((Φ ((x₀ : StatedSU 5 (2 ^ 1) K) : GL (Fin 5) K) : GL (Fin 5) L) :
        Matrix (Fin 5) (Fin 5) L) *ᵥ vL) vL = ι' (∑ i, unitaryInvolution K 2 1
          (((((x₀ : StatedSU 5 (2 ^ 1) K) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ v) i) *
            v i) := by
      simp only [sForm, Matrix.one_mulVec, dotProduct, hΦmat, map_sum, map_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      have e1 : ((((x₀ : StatedSU 5 (2 ^ 1) K) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K).map ι' *ᵥ
          vL) i = ι' (((((x₀ : StatedSU 5 (2 ^ 1) K) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ
            v) i) := (RingHom.map_mulVec ι' _ v i).symm
      rw [e1, unitaryInvolution_apply, hτ, frobenius_def, map_pow]
      norm_num
      exact Or.inl rfl
    rw [hxe, h0, map_zero]
  have hcoef := coeff_mul_sForm_eq_zero hb hdist τ hτinj 1 vL horbL
  have horth : ∀ a c, sForm τ 1 (b a) (b c) ≠ 0 → c = a := by
    intro a c hne
    refine (hdist a c fun x hx => ?_).symm
    have h1 := sForm_eigen_ne_zero hb τ 1 hiso hne hx
    have h3a := CFSG.RankThree.PartTwo.Sec4.eigen_pow_three hb hx (hexp x hx) a
    rw [hτ, frobenius_def] at h1
    calc d x a = d x a * (d x a ^ 2 * d x c) := by rw [h1, mul_one]
      _ = d x a ^ 3 * d x c := by ring
      _ = d x c := by rw [h3a, one_mul]
  have hself : ∀ a, sForm τ 1 (b a) (b a) ≠ 0 := by
    intro a
    obtain ⟨c, hc⟩ := exists_sForm_ne_zero (b := b) τ hτinj
      (by rw [Matrix.det_one]; exact one_ne_zero) (b.ne_zero a)
    have := horth a c hc
    rwa [this] at hc
  have hzero : ∀ a, b.repr vL a = 0 := by
    intro a
    have h1 := hcoef a
    rw [sForm_eq_sum_right (b := b), Finset.sum_eq_single a (fun c _ hca => by
      rw [show sForm τ 1 (b a) (b c) = 0 from by_contra fun hne => hca (horth a c hne),
        mul_zero]) (by simp)] at h1
    rw [hτ, frobenius_def] at h1
    have h2 : b.repr vL a ^ 3 * sForm τ 1 (b a) (b a) = 0 := by linear_combination h1
    rcases mul_eq_zero.mp h2 with h | h
    · exact pow_eq_zero_iff (by norm_num) |>.mp h
    · exact absurd h (hself a)
  have hvL0 : vL = 0 := by
    rw [← b.sum_repr vL]
    simp [hzero]
  funext i
  have := congrFun hvL0 i
  exact ι'.injective (by simpa [hvL] using this)

theorem false_of_suFive (hK : Nat.card K = (2 ^ 1) ^ 2) (E T : Subgroup (StatedSU 5 (2 ^ 1) K))
    (hE : IsElemAbelian 3 E) (h81 : 3 ^ 4 ≤ Nat.card E) (hT1 : T ≠ ⊥) (hT2 : IsPGroup 2 T)
    (hET : E ≤ Subgroup.normalizer (T : Set (StatedSU 5 (2 ^ 1) K))) : False := by
  set ρ := natRep (StatedSU 5 (2 ^ 1) K) with hρ
  refine false_of_fixSub_inf_perp 2 (unitaryForm 2 1 hK 5) ρ (isIsometric_natRep_statedSU hK 5)
    (natRep_injective _) T hT2 hT1 ?_
  rw [eq_bot_iff]
  rintro v ⟨hvW, hvP⟩
  rw [Submodule.mem_bot]
  refine eq_zero_of_orbit_suFive hK E hE h81 v fun x hx => ?_
  have hxv : ρ x v ∈ fixSub ρ T := apply_mem_fixSub (hET hx) hvW
  have h := ((unitaryForm 2 1 hK 5).mem_perp.mp hvP) _ hxv
  rwa [hρ, natRep_apply] at h

end SUFive

end PRankBounds

open PRankBounds CFSG.Assembly.LowTwoRank in
theorem ggUFiveTwoLocalInnerInput_holds : GGUFiveTwoLocalInnerInput := by
  intro X _ _ hmod E T hE h81 hT1 hT2 hET
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_two_of_card_four hK
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  let e₁ : StatedProj (StatedSU 5 (2 ^ 1) K) ≃* StatedSU 5 (2 ^ 1) K :=
    (QuotientGroup.quotientMulEquivOfEq (scalars_statedSU_five_eq_bot hK)).trans
      QuotientGroup.quotientBot
  set j : X ≃* StatedSU 5 (2 ^ 1) K := e.trans e₁
  refine false_of_suFive hK (E.comap j.symm.toMonoidHom) (T.comap j.symm.toMonoidHom)
    (isElemAbelian_comap_of_inj _ j.symm.injective hE) ?_ ?_
    (hT2.comap_of_injective _ j.symm.injective) (comap_le_normalizer_comap _ hET)
  · have hcard : Nat.card (E.comap j.symm.toMonoidHom) = Nat.card E :=
      Nat.card_congr
        { toFun := fun y => ⟨j.symm y, y.2⟩
          invFun := fun x => ⟨j x, by
            change j.symm (j x) ∈ E
            rw [MulEquiv.symm_apply_apply]
            exact x.2⟩
          left_inv := fun y => Subtype.ext (by simp)
          right_inv := fun x => Subtype.ext (by simp) }
    rw [hcard]
    exact h81
  · intro h
    apply hT1
    rw [eq_bot_iff]
    intro t ht
    have hjt : j t ∈ T.comap j.symm.toMonoidHom := by
      change j.symm (j t) ∈ T
      rw [MulEquiv.symm_apply_apply]
      exact ht
    rw [h, Subgroup.mem_bot] at hjt
    rw [Subgroup.mem_bot]
    simpa using congrArg j.symm hjt

end CFSG.StandardType
