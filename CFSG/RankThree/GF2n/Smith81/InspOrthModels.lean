module

public import CFSG.RankThree.GF2n.Stroth80.Conclusion
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.RankThree.PartTwo.Sec14.Wales1411WHJCoreA5J2
import CFSG.RankThree.PartOne.S11d.PSUModel
import CFSG.Timmesfeld.Orders.Classical
public import CFSG.Timmesfeld.Final.Simple
import CFSG.RankThree.GF2n.Stroth80.GriessOrthSmall
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotKleinThreeModel
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation

public section

namespace CFSG.RankThree.GF2n.Smith81.Insp

open CFSG CFSG.Blueprint CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n.Stroth80
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

section ProdAut

open CFSG.RankThree.PartTwo.Sec14.Wales1411W.HJProd

variable {A B : Type} [Group A] [Group B] [Finite A] [Finite B] [IsSimpleGroup B]

theorem card_mulAut_prod_dvd (hAB : Nat.card A < Nat.card B)
    (hA : Function.Injective (MulAut.conj : A →* MulAut A)) :
    Nat.card (MulAut (A × B)) ∣ Nat.card (MulAut A) * Nat.card (MulAut B) := by
  have hfA : ∀ (σ : MulAut (A × B)) (a : A), σ (a, 1) = ((σ (a, 1)).1, 1) := fun σ a =>
    Prod.ext rfl (snd_eq_one_of_aut hAB σ rfl)
  have hfB : ∀ (σ : MulAut (A × B)) (b : B), σ (1, b) = (1, (σ (1, b)).2) := fun σ b =>
    Prod.ext (fst_eq_one_of_aut hAB hA σ rfl) rfl
  let rA : MulAut (A × B) →* MulAut A :=
    { toFun := fun σ =>
        { toFun := fun a => (σ (a, 1)).1
          invFun := fun a => (σ.symm (a, 1)).1
          left_inv := fun a => by
            show (σ.symm ((σ (a, 1)).1, 1)).1 = a
            rw [← hfA σ a, MulEquiv.symm_apply_apply]
          right_inv := fun a => by
            show (σ ((σ.symm (a, 1)).1, 1)).1 = a
            rw [← hfA σ.symm a, MulEquiv.apply_symm_apply]
          map_mul' := fun a b => by
            show (σ (a * b, 1)).1 = (σ (a, 1)).1 * (σ (b, 1)).1
            rw [show ((a * b, 1) : A × B) = (a, 1) * (b, 1) by simp, map_mul, Prod.fst_mul] }
      map_one' := by
        ext a
        rfl
      map_mul' := fun σ τ => by
        ext a
        show (σ (τ (a, 1))).1 = (σ ((τ (a, 1)).1, 1)).1
        rw [← hfA τ a] }
  let rB : MulAut (A × B) →* MulAut B :=
    { toFun := fun σ =>
        { toFun := fun b => (σ (1, b)).2
          invFun := fun b => (σ.symm (1, b)).2
          left_inv := fun b => by
            show (σ.symm (1, (σ (1, b)).2)).2 = b
            rw [← hfB σ b, MulEquiv.symm_apply_apply]
          right_inv := fun b => by
            show (σ (1, (σ.symm (1, b)).2)).2 = b
            rw [← hfB σ.symm b, MulEquiv.apply_symm_apply]
          map_mul' := fun a b => by
            show (σ (1, a * b)).2 = (σ (1, a)).2 * (σ (1, b)).2
            rw [show ((1, a * b) : A × B) = (1, a) * (1, b) by simp, map_mul, Prod.snd_mul] }
      map_one' := by
        ext b
        rfl
      map_mul' := fun σ τ => by
        ext b
        show (σ (τ (1, b))).2 = (σ (1, (τ (1, b)).2)).2
        rw [← hfB τ b] }
  let ρ := rA.prod rB
  have hinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro σ hσ
    rw [MonoidHom.mem_ker, MonoidHom.prod_apply, Prod.mk_eq_one] at hσ
    obtain ⟨h1, h2⟩ := hσ
    rw [Subgroup.mem_bot]
    refine MulEquiv.ext fun x => ?_
    have ha : σ (x.1, 1) = (x.1, 1) := by
      rw [hfA σ x.1]
      exact Prod.ext (congrArg (fun α : MulAut A => α x.1) h1) rfl
    have hb : σ (1, x.2) = (1, x.2) := by
      rw [hfB σ x.2]
      exact Prod.ext rfl (congrArg (fun α : MulAut B => α x.2) h2)
    have hx : x = (x.1, 1) * (1, x.2) := by simp
    rw [MulAut.one_apply, hx, map_mul, ha, hb]
  haveI : Finite (MulAut A) :=
    Finite.of_injective (fun α : MulAut A => (α : A → A)) DFunLike.coe_injective
  haveI : Finite (MulAut B) :=
    Finite.of_injective (fun α : MulAut B => (α : B → B)) DFunLike.coe_injective
  have h1 : Nat.card (MulAut (A × B)) = Nat.card ρ.range :=
    Nat.card_congr (Equiv.ofInjective ρ hinj)
  rw [h1, ← Nat.card_prod]
  exact Subgroup.card_subgroup_dvd_card _

end ProdAut

theorem exists_not_commute_of_simple {X : Type} [Group X] (hS : IsSimpleGroup X)
    (h4 : 4 ∣ Nat.card X) : ∃ x y : X, x * y ≠ y * x := by
  by_contra hc
  push Not at hc
  haveI : IsMulCommutative X := ⟨⟨hc⟩⟩
  have hp := (Group.is_simple_iff_prime_card (α := X)).mp hS
  have h2 : 2 ∣ Nat.card X := (dvd_trans (by norm_num : 2 ∣ 4) h4)
  rcases hp.eq_one_or_self_of_dvd 2 h2 with h | h
  · omega
  · rw [← h] at h4
    omega

theorem sl2_model_facts {A : Type} [Group A] {f : ℕ} (hf : 2 ≤ f)
    (hA : IsSLModel 2 (2 ^ f) A) :
    IsSimpleGroup A ∧ Nat.card A = 2 ^ f * ((2 ^ f) ^ 2 - 1) ∧ Nat.card (Outer A) ∣ f := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hA
  haveI := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  let e₀ : Matrix.SpecialLinearGroup (Fin 2) K ≃* ↥(StatedSL 2 K) :=
    (MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective).trans
      (MulEquiv.subgroupCongr (StatedAPI.statedSL_eq_range_toGL 2 K).symm)
  have e' : A ≃* StatedProj (StatedSL 2 K) :=
    (e.trans e₀.symm).trans (CFSG.RankThree.PartOne.nonempty_SL2_mulEquiv_statedProj').some
  have hq : (2, 2 ^ f) ≠ (2, 2) := by
    intro h
    have : 2 ^ f = 2 ^ 1 := by simpa using h
    have := Nat.pow_right_injective (le_refl 2) this
    omega
  have hq3 : (2, 2 ^ f) ≠ (2, 3) := by
    intro h
    have h' : 2 ^ f = 3 := by simpa using h
    have : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    omega
  have h : StatedClassicalModel A .PSL 2 2 f :=
    ⟨⟨Nat.prime_two, by omega, le_refl 2, hq, hq3⟩, K, inferInstance, inferInstance, hK, ⟨e'⟩⟩
  refine ⟨Timmesfeld.isSimpleGroup_of_lieModel (Or.inl ⟨by decide, h⟩), ?_, ?_⟩
  · rw [Nat.card_congr e.toEquiv, StatedAPI.card_statedSL_two, hK]
  · have h2 := (LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound A 2 2 f h).2.2.2.1
      rfl
    have hg : Nat.gcd 2 (2 ^ f - 1) = 1 := by
      have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
      have h2' : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
      have hodd : ¬ 2 ∣ 2 ^ f - 1 := by omega
      rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two _ (Nat.gcd_dvd_left 2 (2 ^ f - 1)) with
        h | h
      · exact h
      · have h3 := Nat.gcd_dvd_right 2 (2 ^ f - 1)
        rw [h] at h3
        exact absurd h3 hodd
    rwa [hg, mul_one] at h2

theorem omegaPlus_model_facts {B : Type} [Group B] {m f : ℕ} (hm : 4 ≤ m) (hf : 1 ≤ f)
    (hB : IsOmegaPlus m (2 ^ f) B) :
    IsSimpleGroup B ∧ Nat.card B = ordD m (2 ^ f) ∧
      ordProj[2] (Nat.card (Outer B)) ≤ 4 * ordProj[2] f := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hB
  haveI := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have hv : ∃ v, (LieType.Universal.Spin.quadPlus m K) v ≠ 0 := by
    refine ⟨Pi.single (Sum.inl ⟨0, by omega⟩) 1 + Pi.single (Sum.inr ⟨0, by omega⟩) 1, ?_⟩
    rw [LieType.Universal.Spin.quadPlus_apply, Finset.sum_eq_single (⟨0, by omega⟩ : Fin m)]
    · simp
    · intro i _ hi
      simp [Pi.single_apply, hi]
    · simp
  let eP : StatedProj (StatedOmega (StatedQuadPlus m K)) ≃* ↥(StatedOmega (StatedQuadPlus m K)) :=
    (QuotientGroup.quotientMulEquivOfEq
      (CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot
      (LieType.Universal.Spin.coe_quadPlus m K) hv)).trans QuotientGroup.quotientBot
  have h : StatedClassicalModel B .POmegaPlus m 2 f :=
    ⟨⟨Nat.prime_two, hf, hm⟩, K, inferInstance, inferInstance, hK, ⟨e.trans eP.symm⟩⟩
  refine ⟨Timmesfeld.isSimpleGroup_of_lieModel (Or.inl ⟨by decide, h⟩),
    (Timmesfeld.card_statedClassicalModel_two h).2.2.2.1 rfl, ?_⟩
  exact (LocalAnalysis.ComponentInitial.orthogonal_model_outer_two_part_bound B .POmegaPlus
    (Or.inr (Or.inl rfl)) m 2 f h).2.2.1 rfl

theorem omegaMinus_model_facts {B : Type} [Group B] {m f : ℕ} (hm : 4 ≤ m) (hf : 1 ≤ f)
    (hB : IsOmegaMinus m (2 ^ f) B) :
    IsSimpleGroup B ∧ Nat.card B = ordTwistedD m (2 ^ f) ∧
      ordProj[2] (Nat.card (Outer B)) ≤ 4 * ordProj[2] f := by
  obtain ⟨K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hB
  haveI := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have hv : ∃ v, (LieType.Universal.Spin.quadMinus m K b c) v ≠ 0 := by
    refine ⟨Pi.single (Sum.inr (Sum.inr 0)) 1, ?_⟩
    rw [LieType.Universal.Spin.quadMinus_apply]
    simp
  let eP : StatedProj (StatedOmega (StatedQuadMinus m K b c)) ≃*
      ↥(StatedOmega (StatedQuadMinus m K b c)) :=
    (QuotientGroup.quotientMulEquivOfEq
      (CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot
      (LieType.Universal.Spin.coe_quadMinus m K b c) hv)).trans QuotientGroup.quotientBot
  have h : StatedClassicalModel B .POmegaMinus m 2 f :=
    ⟨⟨Nat.prime_two, hf, hm⟩, K, inferInstance, inferInstance, hK, b, c, hirr, ⟨e.trans eP.symm⟩⟩
  refine ⟨Timmesfeld.isSimpleGroup_of_lieModel (Or.inl ⟨by decide, h⟩),
    (Timmesfeld.card_statedClassicalModel_two h).2.2.2.2 rfl, ?_⟩
  exact (LocalAnalysis.ComponentInitial.orthogonal_model_outer_two_part_bound B .POmegaMinus
    (Or.inr (Or.inr rfl)) m 2 f h).2.2.1 rfl

theorem ordA_three_eq_ordD_three {f : ℕ} (hf : 1 ≤ f) : ordA 3 (2 ^ f) = ordD 3 (2 ^ f) := by
  set q := 2 ^ f with hq
  have hq2 : 2 ∣ q := dvd_pow_self 2 (by omega)
  have hq1 : 1 ≤ q := Nat.one_le_two_pow
  have hq3 : 2 ∣ q ^ 3 := dvd_pow hq2 (by norm_num)
  have hq31 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hg1 : Nat.gcd (3 + 1) (q - 1) = 1 :=
    Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr (by rw [Nat.odd_iff]; omega))
  have hg2 : Nat.gcd 4 (q ^ 3 - 1) = 1 :=
    Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr (by rw [Nat.odd_iff]; omega))
  unfold ordA ordD
  rw [hg1, hg2, Nat.div_one, Nat.div_one, show Finset.Icc 2 (3 + 1) = {2, 3, 4} by decide,
    show Finset.Icc 1 (3 - 1) = {1, 2} by decide]
  simp only [Finset.prod_insert (by decide : (2 : ℕ) ∉ ({3, 4} : Finset ℕ)),
    Finset.prod_insert (by decide : (3 : ℕ) ∉ ({4} : Finset ℕ)),
    Finset.prod_insert (by decide : (1 : ℕ) ∉ ({2} : Finset ℕ)), Finset.prod_singleton]
  ring_nf

theorem omegaPlus_three_model_facts {B : Type} [Group B] {f : ℕ} (hf : 2 ≤ f)
    (hB : IsOmegaPlus 3 (2 ^ f) B) :
    IsSimpleGroup B ∧ Nat.card B = ordD 3 (2 ^ f) ∧
      ordProj[2] (Nat.card (Outer B)) ≤ 4 * ordProj[2] f := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hB
  haveI := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨eGS⟩ := CFSG.RankThree.GF2n.Stroth80.nonempty_statedOmega_quadPlus_three_mulEquiv
    (K := K) hK4
  have hc : Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) K) = ⊥ :=
    (LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 4 K).symm.trans
      (CFSG.SeitzReduction.OmegaPilot.scalars_four_eq_bot_of_charTwo K)
  let eP : Matrix.SpecialLinearGroup (Fin 4) K ≃* StatedProj (StatedSL 4 K) :=
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).symm.trans
      (projectiveSpecialLinearGroupEquivStatedProj 4 K)
  have e' : B ≃* StatedProj (StatedSL 4 K) :=
    (e.trans eGS).trans ((specialLinearGroupEquivStatedSL 4 K).symm.trans eP)
  have h : StatedClassicalModel B .PSL 4 2 f :=
    ⟨⟨Nat.prime_two, by omega, by norm_num, by simp, by simp⟩, K, inferInstance, inferInstance,
      hK, ⟨e'⟩⟩
  haveI : Finite B := Finite.of_equiv _ e'.toEquiv.symm
  haveI : Finite (MulAut B) :=
    Finite.of_injective (fun α : MulAut B => (α : B → B)) DFunLike.coe_injective
  refine ⟨Timmesfeld.isSimpleGroup_of_lieModel (Or.inl ⟨by decide, h⟩), ?_, ?_⟩
  · rw [(Timmesfeld.card_statedClassicalModel_two h).1 rfl, ordA_three_eq_ordD_three (by omega)]
  · have h2 := (LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound B 4 2 f h).2.2.2.2
      (by norm_num)
    have hg : Nat.gcd 4 (2 ^ f - 1) = 1 := by
      have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
      have h2' : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
      exact Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr (by rw [Nat.odd_iff]; omega))
    rw [hg, mul_one] at h2
    have h3 := Nat.ordProj_dvd_ordProj_of_dvd (by omega : 2 * f ≠ 0) h2 2
    have h4 : ordProj[2] (2 * f) = 2 * ordProj[2] f := by
      rw [Nat.ordProj_mul 2 (by norm_num) (by omega), Nat.Prime.factorization_self Nat.prime_two,
        pow_one]
    have h5 := Nat.le_of_dvd (by rw [h4]; positivity) h3
    have h6 : 0 < ordProj[2] f := Nat.ordProj_pos f 2
    omega

end CFSG.RankThree.GF2n.Smith81.Insp
