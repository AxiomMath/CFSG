module

public import CFSG.RankThree.PartOne.FOC.PSLLie
public import CFSG.RankThree.PartOne.FOC.LieAssemble
import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialTorusDickson
public import CFSG.RankThree.PartOne.FOC.Equiv
public import CFSG.RankThree.PartOne.FOC.PSLFamily
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearTwoAutomorphism
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearTwoEven
import CFSG.RankThree.SteinbergR3ELinearTwoOddFieldFixed

public section

namespace CFSG.RankThree.PartOne.FOC

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GorensteinWalter (PSL2)
open CFSG.RankThree.PartOne.Sec66T (fixSub innerAut mem_innerAut_congr orderOf_congr fixSubEquiv)
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.ComponentClassification.CatalogueBLinearTwoDescent (fixedSubfield)
open CFSG.ComponentClassification.UnbalancedGS.SubfieldCentralizer (subfieldD)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  (coordinateD_eq_G fieldExtension_mem_E linear_two_automorphism_semilinear_isomorphism)
open CFSG.RankThree.LinearTwo
  (linear_two_prime_semilinear_field_descent linear_two_odd_field_fixed_group_and_centralizer)

theorem mem_coordinateG_of_odd {K : Type} [Field K] [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hK : Nat.card K = ℓ ^ f) {a : Equiv.Perm (Omega K)} (haD : a ∈ coordinateD K)
    (ha : Odd (orderOf a)) : a ∈ coordinateG K := by
  by_cases hℓ2 : ℓ = 2
  · subst hℓ2
    have : Fintype K := Fintype.ofFinite K
    have : CharP K 2 := charP_of_card_eq_prime_pow (f := f) (by
      rw [← Nat.card_eq_fintype_card, hK])
    rw [← coordinateD_eq_G]
    exact haD
  · have hX : Odd (Nat.card (Subgroup.zpowers a)) := by
      rw [Nat.card_zpowers]
      exact ha
    exact CFSG.Semidihedral.FixedCoreNontrivial.le_coordinateG_of_odd hℓ (hℓ.odd_of_ne_two hℓ2) hK
      (X := Subgroup.zpowers a) ((Subgroup.zpowers_le).mpr haD) hX (Subgroup.mem_zpowers a)

theorem psl_two_fixSub_equiv_gen {T : Type} [Group T] {K : Type} [Field K] [Finite K]
    {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (ψ : T ≃* coordinateG K) {α : MulAut T} (hord : orderOf α = p)
    (hαinn : α ∉ innerAut T) :
    p ∣ f ∧ ∃ k : Subfield K, Nat.card k = ℓ ^ (f / p) ∧
      Nonempty (↥(fixSub α) ≃* coordinateG ↥k) := by
  obtain ⟨c, hcapp, hcG, -⟩ := linear_two_automorphism_semilinear_isomorphism K
  set α'' : MulAut (coordinateG K) := MulAut.congr ψ α
  have hα''ord : orderOf α'' = p := (orderOf_congr ψ α).trans hord
  set a : coordinateE K := c.symm α'' with ha
  have hca : c a = α'' := by rw [ha, MulEquiv.apply_symm_apply]
  have hao : orderOf (a : Equiv.Perm (Omega K)) = p := by
    rw [Subgroup.orderOf_coe, ha, MulEquiv.orderOf_eq c.symm, hα''ord]
  have haD : (a : Equiv.Perm (Omega K)) ∉ coordinateD K := by
    intro haD
    have haG : (a : Equiv.Perm (Omega K)) ∈ coordinateG K :=
      mem_coordinateG_of_odd hℓ hK haD (by rw [hao]; exact hp.odd_of_ne_two hp2)
    apply hαinn
    exact (mem_innerAut_congr ψ α).mp ⟨⟨a, haG⟩, (hcG ⟨a, haG⟩).symm.trans hca⟩
  obtain ⟨hpf, σ, hσord, ⟨h, hhD, hah⟩, hkcard⟩ :=
    linear_two_prime_semilinear_field_descent hℓ hp hf K hK a.2 haD hao
  let hE : coordinateE K := ⟨h, coordinateD_le_E K hhD⟩
  let sE : coordinateE K := ⟨fieldExtension K σ, fieldExtension_mem_E σ⟩
  have haeq : a = hE * sE * hE⁻¹ := Subtype.ext hah
  have hconj : (c hE)⁻¹ * α'' * ((c hE)⁻¹)⁻¹ = c sE := by
    have h1 : α'' = c hE * c sE * (c hE)⁻¹ := by
      rw [← hca, haeq, map_mul, map_mul, map_inv]
    rw [h1]
    group
  obtain ⟨e1⟩ : Nonempty (↥(fixSub α) ≃* ↥(fixSub (c sE))) :=
    ⟨((fixSubEquiv ψ α).trans (fixSubEquiv (c hE)⁻¹ α'')).trans
      (MulEquiv.subgroupCongr (show fixSub ((c hE)⁻¹ * α'' * ((c hE)⁻¹)⁻¹) =
        fixSub (c sE) by rw [hconj]))⟩
  obtain ⟨-, hinj, -, hCG, -⟩ :=
    linear_two_odd_field_fixed_group_and_centralizer K σ (hp.odd_of_ne_two hp2) hσord
  set k := fixedSubfield K σ
  set j := (coordinateD K).subtype.comp (subfieldD k)
  set jG := ((coordinateG k).subgroupOf (coordinateD k)).map j
  have hjGle : jG ≤ coordinateG K := by
    rw [← hCG]
    exact inf_le_left
  have hfixeq : fixSub (c sE) = jG.subgroupOf (coordinateG K) := by
    ext x
    rw [Subgroup.mem_subgroupOf, ← hCG, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hx
      have hx' : c sE x = x := hx
      have h1 : (sE : Equiv.Perm (Omega K)) * (x : Equiv.Perm (Omega K)) *
          (sE : Equiv.Perm (Omega K))⁻¹ = x := by
        have := hcapp sE x
        rw [hx'] at this
        exact this.symm
      refine ⟨x.2, ?_⟩
      rw [mul_inv_eq_iff_eq_mul] at h1
      exact h1.symm
    · rintro ⟨-, hx⟩
      have hx' : c sE x = x := by
        apply Subtype.ext
        rw [hcapp sE x, mul_inv_eq_iff_eq_mul]
        exact hx.symm
      exact hx'
  have hjinj : Function.Injective j := (coordinateD K).subtype_injective.comp hinj
  let e2 : ↥(fixSub (c sE)) ≃* ↥jG :=
    (MulEquiv.subgroupCongr hfixeq).trans (Subgroup.subgroupOfEquivOfLe hjGle)
  let e3 : ↥jG ≃* ↥((coordinateG k).subgroupOf (coordinateD k)) :=
    (Subgroup.equivMapOfInjective _ j hjinj).symm
  let e4 : ↥((coordinateG k).subgroupOf (coordinateD k)) ≃* ↥(coordinateG k) :=
    Subgroup.subgroupOfEquivOfLe (coordinateG_le_D k)
  exact ⟨hpf, k, hkcard, ⟨e1.trans (e2.trans (e3.trans e4))⟩⟩

theorem psl_two_outer : PSLTwoOuter := by
  intro K _ _ p hp hp5 _ α hαp hαinn x hx hxp E hE
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hαord : orderOf α = p := by
    refine orderOf_eq_prime hαp ?_
    intro h1
    exact hαinn (h1 ▸ (innerAut (projectiveSL 2 K)).one_mem)
  obtain ⟨ℓ, hℓchar⟩ := CharP.exists K
  have hℓ : ℓ.Prime := CharP.char_is_prime K ℓ
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ', hcard⟩ := FiniteField.card K ℓ
  have hK : Nat.card K = ℓ ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hcard
  have hf : 1 ≤ (f : ℕ) := f.pos
  let ψ : projectiveSL 2 K ≃* coordinateG K :=
    (LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 K).symm.trans (pslEquivCoordinateG K)
  obtain ⟨-, k, hkcard, ⟨eX⟩⟩ := psl_two_fixSub_equiv_gen hℓ hp hp2 hf hK ψ hαord hαinn
  by_cases h4 : 4 ≤ Nat.card k
  · have hs : IsSimpleGroup (PSL2 ↥k) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
    have : IsSimpleGroup (coordinateG ↥k) := (pslEquivCoordinateG ↥k).symm.isSimpleGroup
    have : IsSimpleGroup ↥(fixSub α) := eX.isSimpleGroup
    rw [eq_of_isComponentOf_simple hE]
    exact hx
  · have hN : ¬ p ∣ Nat.card (fixSub α) := by
      intro hd
      have h1 : Nat.card (fixSub α) ∣ Nat.card (Equiv.Perm (Omega ↥k)) := by
        rw [Nat.card_congr eX.toEquiv]
        exact Subgroup.card_subgroup_dvd_card (coordinateG ↥k)
      have h2 : p ∣ (Nat.card (Omega ↥k)).factorial := by
        rw [← Nat.card_perm]
        exact hd.trans h1
      have h3 := (Nat.Prime.dvd_factorial hp).mp h2
      have h5 : Nat.card (Omega ↥k) = Nat.card ↥k + 1 := by simp [Omega]
      omega
    have hx1 : x = 1 := by
      have h1 : orderOf (⟨x, hx⟩ : ↥(fixSub α)) ∣ p :=
        orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hxp))
      have h2 : orderOf (⟨x, hx⟩ : ↥(fixSub α)) ∣ Nat.card (fixSub α) := orderOf_dvd_natCard _
      have hcop : Nat.Coprime p (Nat.card (fixSub α)) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hN
      have h3 : orderOf (⟨x, hx⟩ : ↥(fixSub α)) = 1 :=
        Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd h1 h2)
      exact congrArg Subtype.val (orderOf_eq_one_iff.mp h3)
    rw [hx1]
    exact E.one_mem

theorem fieldInnerT_psl_model {T : Type} [Group T] [Finite T] {n f ℓ p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpℓ : p ≠ ℓ) (hs : IsSimpleGroup T) (hnab : ∃ a b : T, a * b ≠ b * a)
    (hadm : StatedLieAdmissible .PSL n ℓ f) (hmodel : LieModel T .PSL n ℓ f) :
    FieldInnerT p T := by
  obtain ⟨hn2, K, _, _, hchar, hK, ⟨e⟩⟩ := exists_equiv_projectiveSL_gen hmodel
  have hℓ : ℓ.Prime := hadm.1
  have hpK : (p : K) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff K ℓ p).mp h
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp this).symm
  have hs' : IsSimpleGroup (projectiveSL n K) := e.symm.isSimpleGroup
  have hnab' : ∃ a b : projectiveSL n K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨e a, e b, fun h => hab (e.injective (by rw [map_mul, map_mul]; exact h))⟩
  exact FieldInnerT.of_mulEquiv e hp (fieldInnerT_psl psl_two_outer hp hp5 hpK hn2 hs' hnab')

theorem fieldInnerLie_PSL'' (hdefI : DefInnerComponent) (hdefO : DefOuterComponent) (ℓ : ℕ) :
    FieldInnerLie .PSL ℓ :=
  fieldInnerLie_of_nondef hdefI hdefO fun _ _ _ _ _ _ hp hp5 hpℓ hs hnab hadm hmodel =>
    fieldInnerT_psl_model hp hp5 hpℓ hs hnab hadm hmodel

end CFSG.RankThree.PartOne.FOC
