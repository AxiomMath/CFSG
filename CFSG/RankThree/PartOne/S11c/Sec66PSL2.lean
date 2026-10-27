module

public import CFSG.RankThree.PartOne.S11c.Sec66PSL
public import CFSG.RankThree.PartOne.S11c.Sec66Degen
public import CFSG.RankThree.SteinbergR3ELinearTwoOddFieldFixed
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearTwoEven
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearTwoAutomorphism

public section

namespace CFSG.RankThree.PartOne.Sec66T

open CFSG CFSG.Blueprint
open CFSG.Assembly.LowTwoRank
  (StatedClassicalModel projectiveSpecialLinearGroupEquivStatedProj)
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.ComponentClassification.CatalogueBLinearTwoDescent (fixedSubfield)
open CFSG.ComponentClassification.UnbalancedGS.SubfieldCentralizer (subfieldD)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  (coordinateD_eq_G fieldExtension_mem_E linear_two_automorphism_semilinear_isomorphism)
open CFSG.RankThree.LinearTwo
  (linear_two_prime_semilinear_field_descent linear_two_odd_field_fixed_group_and_centralizer)

theorem psl_two_exists_fixSub_equiv {T : Type} [Group T] {K : Type} [Field K] [Finite K] [CharP K 2]
    {f p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (ψ : T ≃* coordinateG K) {α : MulAut T} (hord : orderOf α = p) (hαinn : α ∉ innerAut T) :
    p ∣ f ∧ ∃ k : Subfield K, Nat.card k = 2 ^ (f / p) ∧
      Nonempty (↥(fixSub α) ≃* coordinateG ↥k) := by
  obtain ⟨c, hcapp, hcG, -⟩ := linear_two_automorphism_semilinear_isomorphism K
  set α'' : MulAut (coordinateG K) := MulAut.congr ψ α
  have hα''ord : orderOf α'' = p := (orderOf_congr ψ α).trans hord
  set a : coordinateE K := c.symm α'' with ha
  have hca : c a = α'' := by rw [ha, MulEquiv.apply_symm_apply]
  have hao : orderOf (a : Equiv.Perm (Omega K)) = p := by
    rw [Subgroup.orderOf_coe, ha, MulEquiv.orderOf_eq c.symm, hα''ord]
  have hDG : coordinateD K = coordinateG K := coordinateD_eq_G
  have haD : (a : Equiv.Perm (Omega K)) ∉ coordinateD K := by
    intro haD
    rw [hDG] at haD
    apply hαinn
    exact (mem_innerAut_congr ψ α).mp ⟨⟨a, haD⟩, (hcG ⟨a, haD⟩).symm.trans hca⟩
  obtain ⟨hpf, σ, hσord, ⟨h, hhD, hah⟩, hkcard⟩ :=
    linear_two_prime_semilinear_field_descent Nat.prime_two hp hf K hK a.2 haD hao
  have hhG : h ∈ coordinateG K := by rw [← hDG]; exact hhD
  let hG : coordinateG K := ⟨h, hhG⟩
  let hE : coordinateE K := ⟨h, coordinateD_le_E K hhD⟩
  let sE : coordinateE K := ⟨fieldExtension K σ, fieldExtension_mem_E σ⟩
  have haeq : a = hE * sE * hE⁻¹ := Subtype.ext hah
  have hcE : c hE = MulAut.conj hG := hcG hG
  have hconj : (MulAut.conj hG)⁻¹ * α'' * ((MulAut.conj hG)⁻¹)⁻¹ = c sE := by
    have h1 : α'' = MulAut.conj hG * c sE * (MulAut.conj hG)⁻¹ := by
      rw [← hca, haeq, map_mul, map_mul, map_inv, hcE]
    rw [h1]
    group
  obtain ⟨e1⟩ : Nonempty (↥(fixSub α) ≃* ↥(fixSub (c sE))) :=
    ⟨((fixSubEquiv ψ α).trans (fixSubEquiv (MulAut.conj hG)⁻¹ α'')).trans
      (MulEquiv.subgroupCongr (show fixSub ((MulAut.conj hG)⁻¹ * α'' * ((MulAut.conj hG)⁻¹)⁻¹) =
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

theorem psl_two_k1 : PSLTwoK1 := by
  intro T _ _ p hp hp5 hmodel _ α q _ hord hαinn hq1 hqp hαq _ _ _ _ _
  obtain ⟨f, hadm, hM⟩ := hmodel
  have hC : StatedClassicalModel T .PSL 2 2 f := (lieModel_classical_iff (by decide)).mp hM
  obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := hC
  have hf : 1 ≤ f := hadm.2.1
  have hp2 : p ≠ 2 := by omega
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK])
  let ψ : T ≃* coordinateG K :=
    (e0.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm).trans
      (pslEquivCoordinateG K)
  obtain ⟨hpf, k, hkcard, ⟨eX⟩⟩ := psl_two_exists_fixSub_equiv hp hp2 hf hK ψ hord hαinn
  obtain ⟨m, hm⟩ := hpf
  have hfp : f / p = m := by rw [hm]; exact Nat.mul_div_cancel_left m hp.pos
  rw [hfp] at hkcard
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0] at hm
      omega
    · exact h0
  by_cases hm2 : m = 1
  ·
    exfalso
    subst hm2
    have : Fact p.Prime := ⟨hp⟩
    have : Fintype k := Fintype.ofFinite k
    have hΩ : Nat.card (Omega k) = 3 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_option, ← Nat.card_eq_fintype_card, hkcard]
      norm_num
    have hcard6 : Nat.card (Equiv.Perm (Omega k)) = 6 := by
      rw [Nat.card_perm, hΩ]
      rfl
    have hdvd6 : Nat.card (coordinateG k) ∣ 6 := by
      rw [← hcard6]
      exact Subgroup.card_subgroup_dvd_card (coordinateG k)
    have hqfix : q ∈ fixSub α := hαq
    have hordq : orderOf q = p := orderOf_eq_prime hqp hq1
    have hdvd : p ∣ Nat.card (fixSub α) := by
      have h1 := orderOf_dvd_natCard (⟨q, hqfix⟩ : fixSub α)
      rw [Subgroup.orderOf_mk, hordq] at h1
      exact h1
    rw [Nat.card_congr eX.toEquiv] at hdvd
    have hp6 : p ∣ 2 * 3 := hdvd.trans hdvd6
    rcases (Nat.Prime.dvd_mul hp).mp hp6 with h | h
    · have := Nat.le_of_dvd (by norm_num) h
      omega
    · have := Nat.le_of_dvd (by norm_num) h
      omega
  ·
    have hm2' : 2 ≤ m := by omega
    have h4k : 4 ≤ Nat.card k := by
      rw [hkcard]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2'
    have : Fintype k := Fintype.ofFinite k
    have : CharP k 2 := charP_of_card_eq_prime_pow (f := m) (by
      rw [← Nat.card_eq_fintype_card, hkcard])
    let eS : coordinateG k ≃* KCRootAxis.SL₂ k :=
      (pslEquivCoordinateG k).symm.trans (KCRootAxis.slEquivPSL k).symm
    have hsimple : IsSimpleGroup (KCRootAxis.SL₂ k) := KCRootAxis.sl2_isSimpleGroup h4k
    have hnab : ∃ x y : KCRootAxis.SL₂ k, x * y ≠ y * x :=
      exists_noncomm_of_perfect (KCRootAxis.sl2_isPerfect h4k).commutator_eq_top
    have hXmodel : LieModel (KCRootAxis.SL₂ k) .PSL 2 2 m :=
      (lieModel_classical_iff (by decide)).mpr
        ⟨⟨Nat.prime_two, hm1, le_refl 2, fun hc => by
            have h2 : 2 ^ m = 2 := (Prod.mk.inj hc).2
            have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2'
            omega,
          fun hc => by
            have h2 : 2 ^ m = 3 := (Prod.mk.inj hc).2
            have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2'
            omega⟩,
          k, inferInstance, inferInstance, hkcard,
          ⟨(KCRootAxis.slEquivPSL k).trans (projectiveSpecialLinearGroupEquivStatedProj 2 k)⟩⟩
    have hfix := lieModel_fixRes_of_simple hnab (eX.trans eS) hXmodel
    refine ⟨.PSL, 2, m, hm1, ?_, Or.inl hfix⟩
    rw [← hm]
    exact hM

end CFSG.RankThree.PartOne.Sec66T
