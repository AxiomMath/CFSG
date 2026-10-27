module

public import CFSG.RankThree.PartOne.S11c.Sec66PSUFive
public import CFSG.RankThree.PartOne.S11c.Sec66TorusPSU
public import CFSG.RankThree.PartOne.S11c.Sec66ClassCommon
public import CFSG.RankThree.PartOne.S11c.Sec66Conj
public import CFSG.RankThree.PartOne.KC.EvenUnitaryFiveFieldActor
public import CFSG.RankThree.Classical.SteinbergBTHigherUnitaryPrimeSubfield
public import CFSG.RankThree.PartOne.S11d.OutUnitary

public section

namespace CFSG.RankThree.PartOne.Sec66T

open Matrix CFSG CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.Classical CFSG.RankThree.PartOne CFSG.LieType.Chevalley
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel StatedProj
  StatedSU)

section Model

theorem psu_prime_form_model {T : Type} [Group T] {n f : ℕ}
    (hC : StatedClassicalModel T .PSU n 2 f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (h : UnitaryFieldData 2 f K), 3 ≤ n ∧
      ¬(n = 3 ∧ 2 ^ f = 2) ∧
      Nonempty (T ≃* primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  obtain ⟨⟨hℓ, hf, hn3, hne⟩, K, _, _, hK, ⟨e⟩⟩ := hC
  have hU : UnitaryFieldData 2 f K := ⟨hℓ, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq : ¬(n = 3 ∧ 2 ^ f = 2) := fun ⟨h1, h2⟩ => hne (by rw [h1, h2])
  obtain ⟨⟨eT⟩, -⟩ := unitary_prime_form_full_semilinear_realization hU
    (isPrimeFormGram_one (n := n)) hn3 hq
  exact ⟨K, inferInstance, inferInstance, hU, hn3, hq,
    ⟨(e.trans (unitaryPSUEquiv hU (by omega)).symm).trans eT.symm⟩⟩

end Model

section Diagonal

variable {f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem innerAut_le_primeFormD' :
    innerAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ≤
      primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  rintro _ ⟨y, rfl⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  refine ⟨⟨(g : GL (Fin n) K), ((mem_gramSU_iff_unitary h).mp g.2).1⟩, ?_⟩
  refine MulEquiv.ext fun x => QuotientGroup.induction_on x fun g' => ?_
  rw [primeFormConjHom_mk, MulAut.conj_apply]
  have : (⟨(g : GL (Fin n) K) * (g' : GL (Fin n) K) * (g : GL (Fin n) K)⁻¹,
      conj_mem_gramSU h _ ((mem_gramSU_iff_unitary h).mp g.2).1 g'.2⟩ :
        gramSU h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) = g * g' * g⁻¹ :=
    Subtype.ext rfl
  rw [this]
  rfl

theorem mem_innerAut_of_mem_D (hn : 3 ≤ n) (hq : ¬(n = 3 ∧ 2 ^ f = 2)) {p : ℕ} (hp : p.Prime)
    (hdiag : ¬ p ∣ Nat.gcd n (2 ^ f + 1))
    {α : MulAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))}
    (hD : α ∈ primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (hαp : α ^ p = 1) :
    α ∈ innerAut (primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  classical
  have hfin : Finite K := h.finite
  obtain ⟨-, -, hcard, -⟩ := unitary_full_diagonal_outer_order h hn hq
  set T := primeFormP h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
  set D := primeFormD h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hDdef
  set I : Subgroup (MulAut T) := CFSG.ComponentClassification.OuterAutomorphisms.inner T
  set x : D ⧸ I.subgroupOf D := QuotientGroup.mk (⟨α, hD⟩ : D) with hx
  have hxp : x ^ p = 1 := by
    rw [hx, ← QuotientGroup.mk_pow]
    have : (⟨α, hD⟩ : D) ^ p = 1 := Subtype.ext (by simpa using hαp)
    rw [this]
    rfl
  have hdvd1 : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hxp
  have hdvd2 : orderOf x ∣ Nat.gcd n (2 ^ f + 1) := hcard ▸ orderOf_dvd_natCard x
  have hcop : Nat.Coprime p (Nat.gcd n (2 ^ f + 1)) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hdiag
  have hx1 : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd1 hdvd2
  have : x = 1 := orderOf_eq_one_iff.mp hx1
  have hmem := (QuotientGroup.eq_one_iff (⟨α, hD⟩ : D)).mp this
  exact Subgroup.mem_subgroupOf.mp hmem

end Diagonal

section Fixed

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem lieModel_fixRes_fieldHom {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {σ : K ≃+* K}
    (hσ : orderOf σ = p) (hn : 3 ≤ n) (hq₀ : ¬(n = 3 ∧ 2 ^ (f / p) = 2)) :
    LieModel (↥(fixRes (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ)) ⧸
      Subgroup.center ↥(fixRes (primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ)))
      .PSU n 2 (f / p) := by
  classical
  have hfin : Finite K := h.finite
  set h₀ := fixSubfield_unitaryFieldData h hp hp2 hσ with hh₀
  have hbar := fixSubfield_unitaryFieldData_bar h hp hp2 hσ
  set β := primeFormFieldHom h (isPrimeFormGram_one (n := n)) σ with hβ
  set N := (subfieldPSU h h₀ hbar n).range with hN
  have hder : ⁅fixSub β, fixSub β⁆ = N :=
    KCEvenUnitaryFive.commutator_fieldFixedPSU_eq_range h hbar n hn hq₀
  have hNΓ : N ≤ fixSub β := range_subfieldPSU_le h n h₀ hbar
  have hNsub : N.subgroupOf (fixSub β) = commutator ↥(fixSub β) := by
    rw [← hder, ← Subgroup.map_subtype_commutator]
    exact Subgroup.comap_map_eq_self_of_injective (fixSub β).subtype_injective _
  have hNnormal : (N.subgroupOf (fixSub β)).Normal := by
    rw [hNsub]
    exact inferInstance
  have hsolv : Group.IsSolvable (↥(fixSub β) ⧸ N.subgroupOf (fixSub β)) := by
    have : (N.subgroupOf (fixSub β)).Normal := hNnormal
    have : CommGroup (↥(fixSub β) ⧸ commutator ↥(fixSub β)) :=
      inferInstanceAs (CommGroup (Abelianization ↥(fixSub β)))
    have : Group.IsSolvable (↥(fixSub β) ⧸ commutator ↥(fixSub β)) := inferInstance
    exact Group.isSolvable_of_surjective
      (f := (QuotientGroup.quotientMulEquivOfEq hNsub.symm).toMonoidHom)
      (QuotientGroup.quotientMulEquivOfEq hNsub.symm).surjective
  have hperf0 : Group.IsPerfect (gramSU h₀ ((1 : GL (Fin n) (fixSubfield σ)) :
      Matrix (Fin n) (Fin n) (fixSubfield σ))) := isPerfect_gramSU_one h₀ hn hq₀
  have hperfX : Group.IsPerfect (primeFormP h₀ ((1 : GL (Fin n) (fixSubfield σ)) :
      Matrix (Fin n) (Fin n) (fixSubfield σ))) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have hjinj := subfieldPSU_injective h h₀ hbar n (by omega)
  let eJ : primeFormP h₀ ((1 : GL (Fin n) (fixSubfield σ)) :
      Matrix (Fin n) (Fin n) (fixSubfield σ)) ≃* ↥N := MonoidHom.ofInjective hjinj
  have hNperf : Group.IsPerfect ↥N :=
    Group.IsPerfect.ofSurjective (f := eJ.toMonoidHom) eJ.surjective
  have hsimple := isSimpleGroup_primeFormP_one h₀ hn hq₀
  have hnab : ∃ x y : primeFormP h₀ ((1 : GL (Fin n) (fixSubfield σ)) :
      Matrix (Fin n) (Fin n) (fixSubfield σ)), x * y ≠ y * x := by
    have := not_commute_primeFormP_one h₀ hn hq₀
    push Not at this
    exact this
  have hZ : Subgroup.center (primeFormP h₀ ((1 : GL (Fin n) (fixSubfield σ)) :
      Matrix (Fin n) (Fin n) (fixSubfield σ))) = ⊥ := center_eq_bot_of_simple' hnab
  let eN : ↥N ⧸ Subgroup.center ↥N ≃* primeFormP h₀ ((1 : GL (Fin n) (fixSubfield σ)) :
      Matrix (Fin n) (Fin n) (fixSubfield σ)) :=
    (centerQuotientCongr eJ.symm).trans (centerQuotientEquivSelf hZ)
  have hfpos : 1 ≤ f / p := h₀.one_le
  have hXmodel : LieModel (primeFormP h₀ ((1 : GL (Fin n) (fixSubfield σ)) :
      Matrix (Fin n) (Fin n) (fixSubfield σ))) .PSU n 2 (f / p) := by
    refine (lieModel_classical_iff (by decide)).mpr ⟨⟨Nat.prime_two, hfpos, hn, ?_⟩,
      fixSubfield σ, inferInstance, inferInstance, ?_, ?_⟩
    · intro hc
      exact hq₀ ⟨(Prod.mk.inj hc).1, (Prod.mk.inj hc).2⟩
    · rw [h₀.card, ← pow_mul, mul_comm]
    · obtain ⟨⟨eT⟩, -⟩ := unitary_prime_form_full_semilinear_realization h₀
        (isPrimeFormGram_one (n := n)) hn hq₀
      exact ⟨eT.trans (unitaryPSUEquiv h₀ (by omega))⟩
  exact lieModel_fixRes_of_normal hNΓ hNnormal hNperf hsolv eN hXmodel

end Fixed

theorem sec66T_K2_PSU : Sec66T_K2 .PSU := by
  intro T _ _ p hp hp5 hmodel hrank E hE hcard hEinn hra
  obtain ⟨n, f, hadm, hM⟩ := hmodel
  have hC : StatedClassicalModel T .PSU n 2 f := (lieModel_classical_iff (by decide)).mp hM
  by_cases hdiag : p ∣ Nat.gcd n (2 ^ f + 1)
  · have hpn : p ∣ n := hdiag.trans (Nat.gcd_dvd_left _ _)
    have hpq : p ∣ 2 ^ f + 1 := hdiag.trans (Nat.gcd_dvd_right _ _)
    by_cases hn6 : 6 ≤ n
    · exact psu_torus_rank T n f p hp hp5 hpn hn6 hpq hC hrank
    · have hn3 : 3 ≤ n := hadm.2.2.1
      have hpn' : p ≤ n := Nat.le_of_dvd (by omega) hpn
      have hn5 : n = 5 := by omega
      have hp5' : p = 5 := by omega
      subst hn5
      subst hp5'
      obtain ⟨K, _, _, hU, -, hq, ⟨e⟩⟩ := psu_prime_form_model hC
      have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
      let E' : Subgroup (MulAut (psu5 hU)) := E.map (MulAut.congr e).toMonoidHom
      have hE' : IsElementaryAbelian 5 ↥E' := IsElementaryAbelian.map (A := E) _
      have hcard' : Nat.card E' = 5 ^ 2 := by
        rw [Subgroup.card_map_of_injective (MulAut.congr e).injective, hcard]
      have hEinn' : E' ⊓ innerAut (psu5 hU) = ⊥ := by
        rw [eq_bot_iff]
        rintro x ⟨⟨α, hα, rfl⟩, hxinn⟩
        have hαinn : α ∈ innerAut T := (mem_innerAut_congr e α).mp hxinn
        have : α ∈ E ⊓ innerAut T := ⟨hα, hαinn⟩
        rw [hEinn, Subgroup.mem_bot] at this
        rw [this, map_one]
        exact Subgroup.one_mem _
      have hra' : ∀ x ∈ E', LocalRankAut 5 (psu5 hU) x := by
        rintro _ ⟨α, hα, rfl⟩
        exact localRankAut_congr e hp (hra α hα)
      exact psu5_K2_core hU hpq E' hE' hcard' hEinn' hra'
  · exact no_plane_of_outPNice hp (OutStructure.outPNice_PSU hp hC hdiag) E hE hcard hEinn

theorem sec66T_K1_PSU : Sec66T_K1 .PSU := by
  intro T _ _ p hp hp5 hmodel hrank α q U hord hαinn hq1 hqp hαq hU1 hU2 hαU hqU hmv hra
  obtain ⟨n, f, hadm, hM⟩ := hmodel
  have hC : StatedClassicalModel T .PSU n 2 f := (lieModel_classical_iff (by decide)).mp hM
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, _, _, hU, hn3, hq, ⟨e⟩⟩ := psu_prime_form_model hC
  have hfinP : Finite (primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
    Finite.of_equiv T e.toEquiv
  set α' := MulAut.congr e α with hα'
  have hα'ord : orderOf α' = p := (orderOf_congr e α).trans hord
  have hα'inn : α' ∉ innerAut (primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) :=
    fun hmem => hαinn ((mem_innerAut_congr e α).mp hmem)
  have hα'p : α' ^ p = 1 := by
    have := pow_orderOf_eq_one α'
    rwa [hα'ord] at this
  have hra' : LocalRankAut p (primeFormP hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) α' :=
    localRankAut_congr e hp hra
  have hC1 : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  set σ := primeFormFieldFactor hU hC1 hn3 hq α' with hσ
  by_cases hσ1 : σ = 1
  · exfalso
    have hαD : α' ∈ primeFormD hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      rw [← ker_primeFormFieldFactor hU hC1 hn3 hq]
      exact hσ1
    by_cases hdiag : p ∣ Nat.gcd n (2 ^ f + 1)
    · have hpn : p ∣ n := hdiag.trans (Nat.gcd_dvd_left _ _)
      have hpq : p ∣ 2 ^ f + 1 := hdiag.trans (Nat.gcd_dvd_right _ _)
      by_cases hn6 : 6 ≤ n
      · exact psu_torus_rank T n f p hp hp5 hpn hn6 hpq hC hrank
      · have hpn' : p ≤ n := Nat.le_of_dvd (by omega) hpn
        have hn5 : n = 5 := by omega
        have hp5' : p = 5 := by omega
        subst hn5
        subst hp5'
        rcases psu5_aut_classification hU α' hα'p with ⟨P, c, hc, hP5, hαP⟩ |
          ⟨φ, M, -, -, -, hnD, -⟩
        · have hU'1 : U.map e.toMonoidHom ≠ ⊥ := by
            intro hbot
            exact hU1 ((Subgroup.map_eq_bot_iff_of_injective U e.injective).mp hbot)
          have hU'α : ∀ u ∈ U.map e.toMonoidHom, α' u ∈ U.map e.toMonoidHom := by
            rintro _ ⟨u, hu, rfl⟩
            refine ⟨α u, hαU u hu, ?_⟩
            show e (α u) = MulAut.congr e α (e u)
            simp [MulAut.congr_apply]
          rw [hαP] at hα'inn hra' hU'α
          exact psu5_D_case hU hpq hc hP5 hα'inn hU'1 (hU2.map _) hU'α hra'
        · exact hnD hαD
    · exact hα'inn (mem_innerAut_of_mem_D hU hn3 hq hp hdiag hαD hα'p)
  · have hσp : σ ^ p = 1 := by rw [hσ, ← map_pow, hα'p, map_one]
    have hσord : orderOf σ = p := orderOf_eq_prime hσp hσ1
    obtain ⟨hpf, -, -, -, -, M, hMconj⟩ :=
      CFSG.RankThree.UnitaryDescent.unitary_prime_semilinear_field_descent hU hn3 hq hp hp2 hp2
        α' hα'ord σ rfl hσord
    obtain ⟨f', hff'⟩ := hpf
    have hf : 1 ≤ f := hadm.2.1
    have hf'1 : 1 ≤ f' := by
      rcases Nat.eq_zero_or_pos f' with h0 | h0
      · rw [h0, mul_zero] at hff'
        omega
      · exact h0
    have hdiv : f / p = f' := by rw [hff', Nat.mul_div_cancel_left _ hp.pos]
    set β := primeFormFieldHom hU hC1 σ with hβ
    set ψ := (primeFormConjHom hU ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) M)⁻¹ with hψ
    have hψα : ψ * α' * ψ⁻¹ = β := by
      rw [hψ, inv_inv]
      exact hMconj
    have hfix : LieModel (↥(fixRes β) ⧸ Subgroup.center ↥(fixRes β)) .PSU n 2 f' := by
      by_cases hq₀ : n = 3 ∧ 2 ^ f' = 2
      · exfalso
        obtain ⟨-, -, -, -, -, -, -, -, -, -, h72⟩ :=
          higher_unitary_prime_subfield_fixed_group_and_full_centralizer hU hn3
            (by omega : n < p) hp hq σ hσord
        obtain ⟨-, hno⟩ := h72 ⟨hq₀.1, by rw [hdiv]; exact hq₀.2⟩
        have hq'1 : e q ≠ 1 := fun h1 => hq1 (e.injective (by rw [h1, map_one]))
        have hq'p : (e q) ^ p = 1 := by rw [← map_pow, hqp, map_one]
        have hfixq : α' (e q) = e q := by
          show MulAut.congr e α (e q) = e q
          simp [MulAut.congr_apply, hαq]
        have hmem : ψ (e q) ∈ fieldFixedPSU hU n σ := by
          show β (ψ (e q)) = ψ (e q)
          have h1 : β (ψ (e q)) = ψ (α' (e q)) := by
            have := congrArg (fun γ : MulAut _ => γ (ψ (e q))) hψα
            simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply] at this
            exact this.symm
          rw [h1, hfixq]
        have hq''1 : ψ (e q) ≠ 1 := fun h1 => hq'1 (ψ.injective (by rw [h1, map_one]))
        have hq''p : (ψ (e q)) ^ p = 1 := by rw [← map_pow, hq'p, map_one]
        exact hno _ hmem (orderOf_eq_prime hq''p hq''1)
      · have := lieModel_fixRes_fieldHom hU hp hp2 hσord hn3 (n := n)
          (fun hc => hq₀ ⟨hc.1, by rw [← hdiv]; exact hc.2⟩)
        rwa [hdiv] at this
    exact fieldAutT_of_conj_fix e hM hff' hf'1 α β ψ hψα hfix

end CFSG.RankThree.PartOne.Sec66T
