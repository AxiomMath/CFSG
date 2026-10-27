module

public import CFSG.LieType.BorelTits.OrthogonalForm
import CFSG.ClassicalGroups.Orthogonal.CharTwoReflectGen
import CFSG.ClassicalGroups.Orthogonal.ElementaryGroupIrreducible
import CFSG.CGT.Harada80.Orbits
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalGroups.Orthogonal.Simple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LieType.BorelTits

open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration QuadraticMap
open CFSG.CGT.Harada80
open scoped commutatorElement

private theorem w183_orth_index_two {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] [IsF2 K] {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K} (hQ : ⇑Q = Q₀)
    (hQnd : (polarBilin Q).Nondegenerate)
    (hgen : TauCeti.QuadraticMap.orthogonalGroup Q =
      Subgroup.closure ((reflect Q) '' {v | Q v = 1}))
    {v₀ : ι → K} (hv₀ : Q v₀ = 1) (hd : 4 ≤ Module.finrank K (ι → K)) :
    ∃ s ∈ orthGroup Q₀, s ^ 2 = 1 ∧
      ∀ g ∈ orthGroup Q₀, g ∈ StatedOmega Q₀ ∨ g * s ∈ StatedOmega Q₀ := by
  classical
  haveI : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero IsF2.two_eq_zero
  have horth : orthGroup Q₀ =
      Subgroup.closure {A : GL ι K | ∀ v, Q₀ (Matrix.mulVec (A : Matrix ι ι K) v) = Q₀ v} := by
    rfl
  set s : GL ι K := (toLinEquiv ι K).symm (reflect Q v₀) with hsdef
  have hsO : s ∈ orthGroup Q₀ := by
    rw [horth, closure_isometries_eq_comap hQ, Subgroup.mem_comap, hsdef]
    simpa using reflect_mem_orthogonalGroup Q v₀
  have hs2 : s ^ 2 = 1 := by
    apply (toLinEquiv ι K).injective
    rw [map_pow, map_one, hsdef, MulEquiv.apply_symm_apply, pow_two]
    exact reflect_mul_self Q v₀
  have hs2' : s * s = 1 := by rw [← pow_two]; exact hs2
  have hs_inv : s⁻¹ = s := inv_eq_of_mul_eq_one_left hs2'
  have hΩeq : StatedOmega Q₀ = ⁅orthGroup Q₀, orthGroup Q₀⁆ := by
    rw [statedOmega_eq_comap hQ, horth, closure_isometries_eq_comap hQ]
    rw [Subgroup.comap_equiv_eq_map_symm' (toLinEquiv ι K)
          (⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆),
        Subgroup.comap_equiv_eq_map_symm' (toLinEquiv ι K)
          (TauCeti.QuadraticMap.orthogonalGroup Q)]
    exact Subgroup.map_commutator (TauCeti.QuadraticMap.orthogonalGroup Q)
      (TauCeti.QuadraticMap.orthogonalGroup Q) (toLinEquiv ι K).symm.toMonoidHom
  have hconj : ∀ a ∈ StatedOmega Q₀, s * a * s⁻¹ ∈ StatedOmega Q₀ := by
    intro a ha
    have hcomm : ⁅s, a⁆ ∈ StatedOmega Q₀ := by
      rw [hΩeq]
      exact Subgroup.commutator_mem_commutator hsO
        (Subgroup.commutator_le_self _ (hΩeq ▸ ha))
    have heq : s * a * s⁻¹ = ⁅s, a⁆ * a := by
      rw [commutatorElement_def]; group
    rw [heq]
    exact Subgroup.mul_mem _ hcomm ha
  let R : Set (GL ι K) := (toLinEquiv ι K).symm '' ((reflect Q) '' {v | Q v = 1})
  have hOgen : orthGroup Q₀ = Subgroup.closure R := by
    rw [horth, closure_isometries_eq_comap hQ,
      Subgroup.comap_equiv_eq_map_symm' (toLinEquiv ι K)
        (TauCeti.QuadraticMap.orthogonalGroup Q), hgen, MonoidHom.map_closure]
    rfl
  have hp : ∀ x ∈ Subgroup.closure R, x ∈ StatedOmega Q₀ ∨ x * s ∈ StatedOmega Q₀ := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      change y ∈ (toLinEquiv ι K).symm '' ((reflect Q) '' {v | Q v = 1}) at hy
      rcases hy with ⟨w, hw, rfl⟩
      rcases hw with ⟨v, hv1, rfl⟩
      refine Or.inr ?_
      obtain ⟨h, hhE, hhv⟩ :=
        exists_mem_elementaryGroup_apply_eq_of_map_eq_one hQnd hd hv₀ hv1
      have hconjv := reflect_conj (Q := Q) (elementaryGroup_le_orthogonalGroup Q hhE) v₀
      rw [hhv] at hconjv
      set H : GL ι K := (toLinEquiv ι K).symm h with hH
      have hHO : H ∈ orthGroup Q₀ := by
        rw [horth, closure_isometries_eq_comap hQ, Subgroup.mem_comap, hH]
        simpa using elementaryGroup_le_orthogonalGroup Q hhE
      have hxdecomp : (toLinEquiv ι K).symm (reflect Q v) = H * s * H⁻¹ := by
        rw [hconjv.symm]
        simp only [map_mul, map_inv, hH, hsdef]
      have hxs : (toLinEquiv ι K).symm (reflect Q v) * s = ⁅H, s⁆ := by
        rw [hxdecomp, commutatorElement_def, hs_inv]
      rw [hxs]
      have : ⁅H, s⁆ ∈ StatedOmega Q₀ := by
        rw [hΩeq]
        exact Subgroup.commutator_mem_commutator hHO hsO
      exact this
    | one => exact Or.inl (Subgroup.one_mem _)
    | mul y z hy hz ihy ihz =>
      set a : GL ι K := y * s with ha
      set b : GL ι K := z * s with hb
      have hydecomp : y = a * s := by rw [ha, mul_assoc, hs2', mul_one]
      have hzdecomp : z = b * s := by rw [hb, mul_assoc, hs2', mul_one]
      rcases ihy with hyΩ | haΩ
      · rcases ihz with hzΩ | hbΩ
        · exact Or.inl (Subgroup.mul_mem _ hyΩ hzΩ)
        · exact Or.inr (by rw [mul_assoc]; exact Subgroup.mul_mem _ hyΩ hbΩ)
      · rcases ihz with hzΩ | hbΩ
        · refine Or.inr ?_
          have h1 : s * z * s⁻¹ ∈ StatedOmega Q₀ := hconj z hzΩ
          have heq : (y * z) * s = a * (s * z * s⁻¹) := by
            rw [hydecomp, hs_inv]; group
          rw [heq]
          exact Subgroup.mul_mem _ haΩ h1
        · refine Or.inl ?_
          have h1 : s * b * s⁻¹ ∈ StatedOmega Q₀ := hconj b hbΩ
          have heq : y * z = a * (s * b * s⁻¹) := by
            rw [hydecomp, hzdecomp, hs_inv]; group
          rw [heq]
          exact Subgroup.mul_mem _ haΩ h1
    | inv y hy ihy =>
      set a : GL ι K := y * s with ha
      have hydecomp : y = a * s := by rw [ha, mul_assoc, hs2', mul_one]
      rcases ihy with hyΩ | haΩ
      · exact Or.inl (Subgroup.inv_mem _ hyΩ)
      · refine Or.inr ?_
        have h1 : s * a⁻¹ * s⁻¹ ∈ StatedOmega Q₀ := hconj a⁻¹ (Subgroup.inv_mem _ haΩ)
        have heq : y⁻¹ * s = s * a⁻¹ * s⁻¹ := by
          rw [hydecomp, mul_inv_rev, hs_inv]
        rw [heq]
        exact h1
  refine ⟨s, hsO, hs2, ?_⟩
  intro g hg
  rw [hOgen] at hg
  exact hp g hg

private theorem w183_omega_fix {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    [Finite K] {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K} (hQ : ⇑Q = Q₀)
    (hQnd : (polarBilin Q).Nondegenerate)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (hP : ∃ P : Fin 2 → HypPair Q, ∀ i j, i ≠ j → (P i).Orth (P j))
    (hbig : 1 < Module.finrank K (ι → K)) (v : ι → K)
    (hv : ∀ A ∈ StatedOmega Q₀, (A : Matrix ι ι K).mulVec v = v) : v = 0 := by
  classical
  have hΩmap : StatedOmega Q₀ =
      (elementaryGroup Q).map (toLinEquiv ι K).symm.toMonoidHom :=
    statedOmega_eq_map_elementaryGroup hQ hE
  have hfix : ∀ e ∈ elementaryGroup Q, e v = v := by
    intro e he
    have hmem : (toLinEquiv ι K).symm e ∈ StatedOmega Q₀ := by
      rw [hΩmap]
      exact Subgroup.mem_map_of_mem (toLinEquiv ι K).symm.toMonoidHom he
    have h1 := hv ((toLinEquiv ι K).symm e) hmem
    rw [← toLinEquiv_apply ((toLinEquiv ι K).symm e) v, MulEquiv.apply_symm_apply] at h1
    exact h1
  by_cases hv0 : v = 0
  · exact hv0
  · exfalso
    set W : Submodule K (ι → K) := K ∙ v with hW
    have hWin : ∀ g ∈ elementaryGroup Q, ∀ x ∈ W, g x ∈ W := by
      intro g hg x hx
      rw [hW] at hx
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
      rw [map_smul, hfix g hg]
      exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton v))
    rcases submodule_eq_bot_or_top_of_elementaryGroup_invariant hQnd hP W hWin with hbot | htop
    · have hvW : v ∈ W := by
        rw [hW]; exact Submodule.subset_span (Set.mem_singleton v)
      rw [hbot] at hvW
      exact hv0 (by simpa using hvW)
    · have hfin : Module.finrank K W = 1 := by
        rw [hW]; exact finrank_span_singleton hv0
      rw [htop, finrank_top] at hfin
      omega

theorem s16nt_orth_index_two_plus_two {K : Type} [Field K] [Finite K] {r : ℕ} (hr : 3 ≤ r)
    (hK : Nat.card K = 2) :
    ∃ s ∈ orthGroup (StatedQuadPlus r K), s ^ 2 = 1 ∧
      ∀ g ∈ orthGroup (StatedQuadPlus r K),
        g ∈ StatedOmega (StatedQuadPlus r K) ∨ g * s ∈ StatedOmega (StatedQuadPlus r K) := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : IsF2 K := IsF2.of_natCard_eq_two hK
  haveI : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero IsF2.two_eq_zero
  have hQ := coe_quadPlus r K
  have hQnd := nondegenerate_polarBilin_quadPlus r K
  have hdim : Module.finrank K (Fin r ⊕ Fin r → K) = 2 * r := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  have hgen := orthogonalGroup_eq_closure_reflect_of_finite (Q := quadPlus r K) hQnd
    (by rw [hdim]; omega)
  have hv₀ : quadPlus r K ((plusPair K ⟨0, by omega⟩).e + (plusPair K ⟨0, by omega⟩).f) = 1 := by
    rw [QuadraticMap.map_add (quadPlus r K), (plusPair K ⟨0, by omega⟩).Q_e,
      (plusPair K ⟨0, by omega⟩).Q_f, (plusPair K ⟨0, by omega⟩).polar_ef]
    ring
  exact w183_orth_index_two hQ hQnd hgen hv₀ (by rw [hdim]; omega)

theorem s16nt_orth_index_two_minus_two {K : Type} [Field K] [Finite K] {r : ℕ} (hr : 3 ≤ r)
    (hK : Nat.card K = 2) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∃ s ∈ orthGroup (StatedQuadMinus r K b c), s ^ 2 = 1 ∧
      ∀ g ∈ orthGroup (StatedQuadMinus r K b c),
        g ∈ StatedOmega (StatedQuadMinus r K b c) ∨
          g * s ∈ StatedOmega (StatedQuadMinus r K b c) := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : IsF2 K := IsF2.of_natCard_eq_two hK
  haveI : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero IsF2.two_eq_zero
  have hQ := coe_quadMinus r K b c
  have hQnd := nondegenerate_polarBilin_quadMinus_of_finite r K hirr
  have hdim : Module.finrank K (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2 → K) = 2 * r := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
    omega
  have hgen := orthogonalGroup_eq_closure_reflect_of_finite (Q := quadMinus r K b c) hQnd
    (by rw [hdim]; omega)
  have hv₀ : quadMinus r K b c (Pi.single (Sum.inr (Sum.inr 0)) 1) = 1 :=
    quadMinus_single_u (K := K) (b := b) (c := c) (m := r)
  exact w183_orth_index_two hQ hQnd hgen hv₀ (by rw [hdim]; omega)

theorem s16nt_omega_fix_plus_two {K : Type} [Field K] [Finite K] {r : ℕ} (hr : 3 ≤ r)
    (hK : Nat.card K = 2) (v : Fin r ⊕ Fin r → K)
    (hv : ∀ A ∈ StatedOmega (StatedQuadPlus r K),
      (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).mulVec v = v) : v = 0 := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : IsF2 K := IsF2.of_natCard_eq_two hK
  haveI : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero IsF2.two_eq_zero
  have hQ := coe_quadPlus r K
  have hQnd := nondegenerate_polarBilin_quadPlus r K
  have hE := commutator_orthogonalGroup_quadPlus (K := K) (n := r) hr
  have hP : ∃ P : Fin 2 → HypPair (quadPlus r K), ∀ i j, i ≠ j → (P i).Orth (P j) :=
    ⟨fun i => plusPair K (Fin.castLE (by omega) i),
      fun _ _ hij => plusPair_orth (fun h => hij (Fin.castLE_injective _ h))⟩
  have hbig : 1 < Module.finrank K (Fin r ⊕ Fin r → K) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  exact w183_omega_fix hQ hQnd hE hP hbig v hv

theorem s16nt_omega_fix_minus_two {K : Type} [Field K] [Finite K] {r : ℕ} (hr : 3 ≤ r)
    (hK : Nat.card K = 2) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (v : Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2 → K)
    (hv : ∀ A ∈ StatedOmega (StatedQuadMinus r K b c),
      (A : Matrix (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2) (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2) K).mulVec
        v = v) : v = 0 := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : IsF2 K := IsF2.of_natCard_eq_two hK
  haveI : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero IsF2.two_eq_zero
  have hQ := coe_quadMinus r K b c
  have hQnd := nondegenerate_polarBilin_quadMinus_of_finite r K hirr
  have hE := commutator_orthogonalGroup_quadMinus_of_two_le (K := K) (n := r) (b := b) (c := c)
    (by omega) hirr
  have hP : ∃ P : Fin 2 → HypPair (quadMinus r K b c), ∀ i j, i ≠ j → (P i).Orth (P j) :=
    ⟨fun i => minusPair K b c (Fin.castLE (by omega) i),
      fun _ _ hij => minusPair_orth (fun h => hij (Fin.castLE_injective _ h))⟩
  have hbig : 1 < Module.finrank K (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2 → K) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
    omega
  exact w183_omega_fix hQ hQnd hE hP hbig v hv

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
