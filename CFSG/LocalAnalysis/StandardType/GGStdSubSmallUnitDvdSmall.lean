module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallUnitDvdBlock
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestThreeUnitary
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable
public import CFSG.GH74.E2.U5Component

public section

namespace CFSG.StandardType.SmallU

open scoped commutatorElement

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.SectionRank.OddCover CFSG.StandardType.LineU CFSG.StandardType.UnitTB CFSG.Assembly
  CFSG.RankThree.Classical CFSG.RankThree.Classical2 CFSG.StandardType.TableBUE

variable {K : Type} [Field K] {d : ℕ} {L' : Type} [Group L']

theorem isSolvable_unitarySU_small [Finite K] (h : UnitaryFieldData 2 1 K) {m : ℕ} (hm1 : 1 ≤ m)
    (hm3 : m ≤ 3) : Group.IsSolvable ↥(unitarySU 2 1 K m) := by
  have hc := CFSG.GH74.E2.U5.card_unitarySU_int h hm1
  refine isSolvable_of_card_primeFactors_le_two ?_
  interval_cases m
  · have h1 : Nat.card ↥(unitarySU 2 1 K 1) = 1 :=
      Subgroup.card_eq_one.mpr (by norm_num at hc; exact hc)
    rw [h1]
    simp
  · have h1 : Nat.card ↥(unitarySU 2 1 K 2) = 6 := by
      norm_num [Finset.prod_Icc_succ_top] at hc
      exact_mod_cast hc
    have h6 : Nat.primeFactors 6 = {2, 3} := by
      rw [show (6 : ℕ) = 2 * 3 by norm_num, Nat.primeFactors_mul (by norm_num) (by norm_num),
        Nat.Prime.primeFactors Nat.prime_two, Nat.Prime.primeFactors Nat.prime_three]
      rfl
    rw [h1, h6]
    decide
  · have h1 : Nat.card ↥(unitarySU 2 1 K 3) = 216 := by
      norm_num [Finset.prod_Icc_succ_top] at hc
      exact_mod_cast hc
    have h216 : Nat.primeFactors 216 = {2, 3} := by
      rw [show (216 : ℕ) = 2 ^ 3 * 3 ^ 3 by norm_num,
        Nat.primeFactors_mul (by norm_num) (by norm_num),
        Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two,
        Nat.primeFactors_prime_pow (by norm_num) Nat.prime_three]
      rfl
    rw [h1, h216]
    decide


theorem layer_le_cent0 [Finite L'] {n : ℕ} {φ : ↥(unitarySU 2 n K d) →* L'} (hM : Model φ)
    {a : MulAut L'} {σ : Fin d → Kˣ} (ha : ActsU φ a σ)
    (hE : IsComponentOf (LargeEvenLayer (ggFix a)) (ggFix a)) :
    LargeEvenLayer (ggFix a) ≤ cent0 φ (diagHom d σ) := by
  set E := LargeEvenLayer (ggFix a) with hEdef
  have hEperf : ⁅E, E⁆ = E := Subgroup.isPerfect_iff.1 (Group.isPerfect_def.mpr hE.2.2.1)
  have hEle : E ≤ ggFix a := hE.1
  rw [← hEperf]
  refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
  exact comm_mem_cent0 hM ha (hEle hx) (hEle hy)

theorem layer_conj_mem [Finite L'] {a : MulAut L'}
    (hE : IsComponentOf (LargeEvenLayer (ggFix a)) (ggFix a)) {c x : L'} (hc : c ∈ ggFix a)
    (hx : x ∈ LargeEvenLayer (ggFix a)) : c * x * c⁻¹ ∈ LargeEvenLayer (ggFix a) := by
  have h1 := isComponentOf_conjSub_of_mem hE hc
  have h2 := (le_sSup h1 : _ ≤ LargeEvenLayer (ggFix a))
  exact h2 ⟨x, hx, by simp⟩

theorem not_isComponentOf_of_solvable {H : Type*} [Group H] {E C : Subgroup H}
    (hE : IsComponentOf E C) (hs : Group.IsSolvable ↥E) : False := by
  have hn : Nontrivial ↥E :=
    CFSG.LocalCores.isQuasisimple_nontrivial ((TableBSymp.isQuasisimple_iff E).mp hE.2.2)
  have hp : Group.IsPerfect ↥E := Group.isPerfect_def.mpr hE.2.2.1
  exact Group.IsPerfect.not_isSolvable ↥E hs

theorem not_isComponentOf_of_comm {H : Type*} [Group H] {E C : Subgroup H}
    (hE : IsComponentOf E C) (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) : False := by
  have hperf : ⁅E, E⁆ = E := Subgroup.isPerfect_iff.1 (Group.isPerfect_def.mpr hE.2.2.1)
  have hbot : E = ⊥ := by
    rw [← hperf, eq_bot_iff]
    refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
    rw [Subgroup.mem_bot, commutatorElement_def, hc x hx y hy, mul_inv_cancel_right,
      mul_inv_cancel]
  have hn : Nontrivial ↥E :=
    CFSG.LocalCores.isQuasisimple_nontrivial ((TableBSymp.isQuasisimple_iff E).mp hE.2.2)
  rw [hbot] at hn
  exact not_nontrivial_iff_subsingleton.mpr inferInstance hn


theorem not_isComponentOf_of_small_classes [Finite K] [Finite L'] {φ : ↥(unitarySU 2 1 K d) →* L'}
    (hM : Model φ) (hd : 4 ≤ d) {a : MulAut L'} {σ : Fin d → Kˣ} (ha : ActsU φ a σ)
    (hsmall : ∀ i, (cls σ i).card ≤ 3)
    (hE : IsComponentOf (LargeEvenLayer (ggFix a)) (ggFix a)) : False := by
  classical
  set E := LargeEvenLayer (ggFix a) with hEdef
  have hEq : CFSG.IsQuasisimple E := (TableBSymp.isQuasisimple_iff E).mp hE.2.2
  have hEc : E ≤ cent0 φ (diagHom d σ) := layer_le_cent0 hM ha hE
  have hEn : ∀ c ∈ cent0 φ (diagHom d σ), ∀ x ∈ E, c * x * c⁻¹ ∈ E := fun c hc x hx =>
    layer_conj_mem hE (cent0_le_fix ha hc) hx
  set B : Fin d → Subgroup L' := fun k => (blockSU (cls σ k)).map φ with hB
  have hBC : ∀ k, B k ≤ cent0 φ (diagHom d σ) := by
    intro k
    refine Subgroup.map_mono (fun y hy => ?_)
    rw [mem_centSU]
    exact (diagHom_mul_comm_of_isBlockOn
      (fun i hi j hj => ((cls_isCls σ k i hi j).mp hj).symm) hy).symm
  have hBn : ∀ k, ∀ c ∈ cent0 φ (diagHom d σ), ∀ b ∈ B k, c * b * c⁻¹ ∈ B k := by
    intro k c hc b hb
    obtain ⟨g, hg, rfl⟩ := hc
    obtain ⟨y, hy, rfl⟩ := hb
    exact ⟨g * y * g⁻¹, conj_mem_blockSU_of_cent hg (cls_isCls σ k) hy, by
      simp only [map_mul, map_inv]⟩
  by_cases hex : ∃ k, E ≤ B k
  · obtain ⟨k, hk⟩ := hex
    haveI hsolU : Group.IsSolvable ↥(unitarySU 2 1 K (cls σ k).card) :=
      isSolvable_unitarySU_small hM.field (Finset.card_pos.mpr ⟨k, mem_cls.mpr rfl⟩) (hsmall k)
    haveI hsolBlock : Group.IsSolvable ↥(blockSU (K := K) (n := 1) (cls σ k)) :=
      solvable_of_surjective (f := (blockSUEquiv (cls σ k) hM.field).toMonoidHom)
        (blockSUEquiv (cls σ k) hM.field).surjective
    haveI hsolB : Group.IsSolvable ↥(B k) := by
      have h1 : Group.IsSolvable ↥(φ.comp (blockSU (cls σ k)).subtype).range :=
        solvable_of_surjective (MonoidHom.rangeRestrict_surjective _)
      rw [SUTorus.range_comp_subtype_blockSU] at h1
      exact h1
    have hsolE : Group.IsSolvable ↥E :=
      solvable_of_solvable_injective (Subgroup.inclusion_injective hk)
    exact not_isComponentOf_of_solvable hE hsolE
  · push Not at hex
    have hcomm : ∀ k, ∀ e ∈ E, ∀ b ∈ B k, e * b = b * e := fun k =>
      (StdSubRestThree.le_or_commute_of_quasisimple hEc (hBC k) hEn (hBn k) hEq).resolve_left
        (hex k)
    obtain ⟨ζ, hζo, hζq⟩ := exists_orderOf_eq_norm_one hM.field Nat.prime_three (by norm_num)
    have hζ3 : ζ ^ 3 = 1 := hζo ▸ pow_orderOf_eq_one ζ
    have hζinv : ζ ≠ ζ⁻¹ := by
      intro he
      have h2 : ζ ^ 2 = 1 := by
        calc ζ ^ 2 = ζ * ζ := sq ζ
          _ = ζ * ζ⁻¹ := by rw [← he]
          _ = 1 := mul_inv_cancel ζ
      have h4 := orderOf_dvd_of_pow_eq_one h2
      rw [hζo] at h4
      omega
    have hζroot : ζ ∈ rootsOfUnity 3 K := by
      rw [mem_rootsOfUnity]
      exact hζ3
    have hdg : ∀ e ∈ E, ∃ g : ↥(unitarySU 2 1 K d), φ g = e ∧
        ∀ i j, i ≠ j → ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j = 0 := by
      intro e he
      obtain ⟨g, hg, rfl⟩ := hEc he
      refine ⟨g, rfl, fun i j hij => ?_⟩
      by_cases hσij : σ i = σ j
      · set S := cls σ i with hSdef
        have hiS : i ∈ S := mem_cls.mpr rfl
        have hjS : j ∈ S := mem_cls.mpr hσij.symm
        set τ : Fin d → Kˣ := Pi.mulSingle i ζ * Pi.mulSingle j ζ⁻¹ with hτ
        have hτi : τ i = ζ := by
          simp only [hτ, Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hij, mul_one]
        have hτj : τ j = ζ⁻¹ := by
          simp only [hτ, Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hij.symm,
            one_mul]
        have hτroot : ∀ k, τ k ∈ rootsOfUnity 3 K := fun k => by
          simp only [hτ, Pi.mul_apply]
          exact (rootsOfUnity 3 K).mul_mem (StdSubRestU.mulSingle_mem hζroot k)
            (StdSubRestU.mulSingle_mem ((rootsOfUnity 3 K).inv_mem hζroot) k)
        have hτq : ∀ k, τ k ^ (2 ^ 1 + 1) = 1 := fun k => by
          have h1 := hτroot k
          rw [mem_rootsOfUnity] at h1
          exact h1
        have hτprod : ∏ k, τ k = 1 := by
          simp only [hτ, Pi.mul_apply, Finset.prod_mul_distrib, Fintype.prod_pi_mulSingle']
          group
        set y : ↥(unitarySU 2 1 K d) :=
          ⟨diagHom d τ, diagHom_mem_unitarySU hM.field hτq hτprod⟩ with hy
        have hyS : y ∈ blockSU S := StdSubRestU.isBlockOn_diagHom fun k hk => by
          have hki : k ≠ i := fun h' => hk (h' ▸ hiS)
          have hkj : k ≠ j := fun h' => hk (h' ▸ hjS)
          simp only [hτ, Pi.mul_apply, Pi.mulSingle_eq_of_ne hki, Pi.mulSingle_eq_of_ne hkj,
            mul_one]
        have hc1 := hcomm i (φ g) he (φ y) ⟨y, hyS, rfl⟩
        have hz : φ (g * y * g⁻¹ * y⁻¹) = 1 := by
          rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc1]
          group
        have hzS : g * y * g⁻¹ * y⁻¹ ∈ blockSU S :=
          (blockSU S).mul_mem (conj_mem_blockSU_of_cent hg (cls_isCls σ i) hyS)
            ((blockSU S).inv_mem hyS)
        obtain ⟨c, hcz⟩ := hM.ker _ hz
        obtain ⟨k₀, hk₀⟩ : ∃ k₀, k₀ ∉ S := by
          by_contra hall
          push Not at hall
          have h1 : S = Finset.univ := Finset.eq_univ_of_forall hall
          have h2 := hsmall i
          rw [← hSdef, h1, Finset.card_univ, Fintype.card_fin] at h2
          omega
        have hc1' : c = 1 := by
          have h1 := (mem_blockSU.mp hzS) k₀ k₀ (Or.inl hk₀)
          rw [hcz, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h1
          exact h1
        have hz1 : g * y * g⁻¹ * y⁻¹ = 1 := by
          apply Subtype.ext
          apply Units.ext
          rw [Subgroup.coe_one, Units.val_one, hcz, hc1']
          exact Matrix.diagonal_one
        have hgy : g * y = y * g := by
          calc g * y = (g * y * g⁻¹ * y⁻¹) * (y * g) := by group
            _ = y * g := by rw [hz1, one_mul]
        exact entry_eq_zero_of_commute (congrArg Subtype.val hgy) (by rw [hτi, hτj]; exact hζinv)
      · exact entry_eq_zero_of_commute (mem_centSU.mp hg) hσij
    refine not_isComponentOf_of_comm hE fun x hx y hy => ?_
    obtain ⟨g₁, rfl, hg₁⟩ := hdg x hx
    obtain ⟨g₂, rfl, hg₂⟩ := hdg y hy
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    apply Units.ext
    exact StdSubRestThreeU.commute_of_offDiag_eq_zero hg₁ hg₂

end CFSG.StandardType.SmallU

end
