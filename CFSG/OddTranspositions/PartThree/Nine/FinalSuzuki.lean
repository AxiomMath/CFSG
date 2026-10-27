module

public import CFSG.OddTranspositions.PartThree.Nine.FinalNonabelian
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma315Sz
public import CFSG.Adapters.FrobeniusKernel
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.CentralResidueMaps
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalizerClassLifting
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.PrincipalClassDefects
public import CFSG.Foundations
public import CFSG.Goldschmidt.StatementsG4
public import CFSG.Goldschmidt.Steps.G37Transport
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherGoldschmidtFour
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixCaseOne
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixProper
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitGlaubermanCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma314Perm
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Lemma39
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2S0LeQuotientTorus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import CFSG.Walter.Bender1970.S2
public import CFSG.Walter.Bender1970.S3.Basic
public import CFSG.Walter.Bender1970.S3.OStar
public import CFSG.Walter.PSL2Facts
public import CFSG.Walter.W67.W2Lemma26A
public import Certificates.Certificate7000
public import Certificates.Certificate7001
public import Certificates.Certificate7002
public import Certificates.Certificate7003
public import Certificates.Certificate7004
public import Certificates.Certificate7005
public import Certificates.Certificate7006
public import Certificates.Certificate7007
public import Certificates.Certificate7008
public import Certificates.Certificate7009
public import Certificates.Certificate7010
public import Certificates.Certificate7011
public import Certificates.Certificate8046
public import Certificates.Certificate8049
public import Certificates.Certificate8052

public section

namespace CFSG.OddTranspositions.PartThree.Nine

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.BenderSuzuki
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem exists_mem_inf_of_mem_sylow_map {hC : HypothesisC D} {T : Sylow 2 (Halpha D hC.alpha)}
    (h3 : Conclusion9_3 D hC) {t : G}
    (htT : t ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype) :
    ∃ r ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
      CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha), t = r ∨ t = hC.d * r := by
  have hu2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  have huT := d_mem_sylow_map hC h3 T
  rcases mem_or_mul_mem_of_conclusion9_3 hC h3 (Subgroup.map_subtype_le _ htT) with htL | htL
  · exact ⟨t, ⟨htT, htL⟩, Or.inl rfl⟩
  · refine ⟨hC.d * t, ⟨Subgroup.mul_mem _ huT htT, htL⟩, Or.inr ?_⟩
    rw [← mul_assoc, hu2, one_mul]

theorem commute_d_of_mem_sylow_map {hC : HypothesisC D} {T : Sylow 2 (Halpha D hC.alpha)} {t : G}
    (htT : t ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype) :
    Commute hC.d t :=
  (Subgroup.mem_centralizer_singleton_iff.mp
    (PartThree.Halpha_le_centralizer_d hC (Subgroup.map_subtype_le _ htT))).symm

namespace DeltaSetup

variable {hC : HypothesisC D} {T : Sylow 2 (Halpha D hC.alpha)} {S : Sylow 2 G}
  {U : Subgroup G}

theorem mem_regularCore_of_pow_eq_one (h3 : Conclusion9_3 D hC) (hU : DeltaSetup hC T S U)
    {Q : Subgroup G} (hQ : IsRegularCore ((S : Set G) ∩ D) Q) {n : ℕ} (hn : Nat.card U = 2 ^ n)
    (hnodd : Odd n) {x : G}
    (hxN : x ∈ Subgroup.normalizer ((fun v : G => hC.d * v) '' (U : Set G))) {j : ℕ}
    (hx : x ^ 2 ^ j = 1) : x ∈ Q := by
  classical
  have := hU.isElementaryAbelian
  obtain ⟨-, -, ⟨φ, -, hφ⟩, -⟩ := hU.affine h3
  have hQ' : IsRegularCore ((fun v : G => hC.d * v) '' (U : Set G)) Q := hU.sylow_inter ▸ hQ
  obtain ⟨-, -, -, d, hdn, hcard⟩ :=
    hU.exists_semilinear_coordinates_of_isRegularCore h3 hQ' φ hφ hn
  set ℓ := AffineEquiv.linearHom.comp φ with hℓ
  set y : Subgroup.normalizer ((fun v : G => hC.d * v) '' (U : Set G)) := ⟨x, hxN⟩ with hy
  have hodd : Odd (Nat.card ℓ.range) := by
    rw [hcard]
    refine Nat.odd_mul.mpr ⟨?_, Odd.of_dvd_nat hnodd hdn⟩
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hnodd.pos; omega⟩
    refine ⟨2 ^ m - 1, ?_⟩
    have := Nat.one_le_two_pow (n := m)
    rw [pow_succ]
    omega
  have hdvd1 : orderOf (ℓ y) ∣ 2 ^ j := by
    refine (orderOf_map_dvd ℓ y).trans (orderOf_dvd_of_pow_eq_one ?_)
    exact Subtype.ext (by simpa [hy] using hx)
  have hdvd2 : orderOf (ℓ y) ∣ Nat.card ℓ.range := by
    have h := orderOf_dvd_natCard (⟨ℓ y, ⟨y, rfl⟩⟩ : ℓ.range)
    rwa [← Subgroup.orderOf_coe] at h
  have h1 : orderOf (ℓ y) = 1 := by
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd1
    rcases i with _ | i
    · simpa using hi
    · exfalso
      rw [hi, pow_succ] at hdvd2
      have h2 : 2 ∣ Nat.card ℓ.range := (Dvd.intro_left _ rfl).trans hdvd2
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  have hly : (φ y).linear = 1 := orderOf_eq_one_iff.mp h1
  exact hU.mem_regularCore_of_linear_eq_one h3 hQ' φ hφ hly

theorem regularCore_eq_sylow (h3 : Conclusion9_3 D hC) (h4 : Conclusion9_4 D hC T S)
    (hU : DeltaSetup hC T S U) {Q : Subgroup G} (hQ : IsRegularCore ((S : Set G) ∩ D) Q)
    {n : ℕ} (hn : Nat.card U = 2 ^ n) (hnodd : Odd n) : Q = S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm (regularCore_le_sylow hQ S h4.2.1) fun s hs => ?_
  have hsN : s ∈ Subgroup.normalizer ((fun v : G => hC.d * v) '' (U : Set G)) := by
    rw [← hU.sylow_inter]
    exact h4.2.1 hs
  obtain ⟨j, hj⟩ := (S.isPGroup') ⟨s, hs⟩
  have hj' : s ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  exact hU.mem_regularCore_of_pow_eq_one h3 hQ hn hnodd hsN hj'

theorem conj_mem_sylow_map (h5 : Conclusion9_5 D hC T S) (hU : DeltaSetup hC T S U) {x t : G}
    (hxN : x ∈ Subgroup.normalizer ((fun v : G => hC.d * v) '' (U : Set G)))
    (htT : t ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype) :
    x * t * x⁻¹ ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype := by
  rw [← h5.1, hU.sylow_inter] at htT ⊢
  rw [Subgroup.mem_centralizer_iff] at htT ⊢
  intro v hv
  have hv' : x⁻¹ * v * x ∈ (fun v : G => hC.d * v) '' (U : Set G) := by
    have h := (Subgroup.inv_mem _ hxN v).mp hv
    simpa using h
  have h := htT _ hv'
  calc v * (x * t * x⁻¹) = x * ((x⁻¹ * v * x) * t) * x⁻¹ := by group
    _ = x * (t * (x⁻¹ * v * x)) * x⁻¹ := by rw [h]
    _ = x * t * x⁻¹ * v := by group

theorem mem_of_mem_sylowCenter (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC)
    (h5 : Conclusion9_5 D hC T S) (hU : DeltaSetup hC T S U)
    {R : Sylow 2 (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha))}
    (hR : (R : Subgroup _).map (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)).subtype =
      (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
        CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha))
    {x : CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)}
    (hx : x ∈ CFSG.ComponentClassification.AschbacherToolkit.Bender.sylowCenter
      (R : Subgroup (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)))) :
    (x : G) ∈ U := by
  obtain ⟨eL⟩ := nonempty_pResidualOf_mulEquiv h3 hU h5.1
  have hLB : IsBenderGroup (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) :=
    isBenderGroup_of_mulEquiv eL hH.bender
  obtain ⟨hxR, hxc⟩ :=
    CFSG.ComponentClassification.AschbacherToolkit.Bender.mem_sylowCenter.mp hx
  have hx2 : x * x = 1 :=
    IsBenderGroup.mul_self_eq_one_of_commute hLB R hxR fun y hy => (hxc y hy).symm
  by_cases hx1 : x = 1
  · rw [hx1]
    exact U.one_mem
  rw [hU.eq_closure]
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · rw [← hR]
    exact Subgroup.mem_map_of_mem _ hxR
  · rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1

theorem mul_self_mem_of_sz (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC)
    (h5 : Conclusion9_5 D hC T S) (hU : DeltaSetup hC T S U) {m : ℕ} (hm : 1 ≤ m)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* SzModel m) {r : G}
    (hr : r ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
      CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) : r * r ∈ U := by
  obtain ⟨eL⟩ := nonempty_pResidualOf_mulEquiv h3 hU h5.1
  obtain ⟨R, hR⟩ := exists_sylow_pResidualOf T
  set e := (eL.trans eH).trans (MulEquiv.subgroupCongr (CFSG.Models.benderSzModel_eq_sz m))
  have hrR : (⟨r, hr.2⟩ : CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) ∈
      (R : Subgroup _) := by
    have hr' : r ∈ (R : Subgroup _).map
        (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)).subtype := hR ▸ hr
    obtain ⟨x, hx, hxr⟩ := Subgroup.mem_map.mp hr'
    have : x = ⟨r, hr.2⟩ := Subtype.ext hxr
    rwa [← this]
  have h := CFSG.ComponentClassification.GMS78.sq_mem_sylowCenter_of_sz hm e R _ hrR
  have h' := hU.mem_of_mem_sylowCenter hH h3 h5 hR h
  simpa [pow_two] using h'

theorem inv_mul_mem_of_mul_self_eq_of_sz (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC)
    (h5 : Conclusion9_5 D hC T S) (hU : DeltaSetup hC T S U) {m : ℕ} (hm : 1 ≤ m)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* SzModel m) {r r' : G}
    (hr : r ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
      CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha))
    (hr' : r' ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
      CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha))
    (hsq : r * r = r' * r') : r⁻¹ * r' ∈ U := by
  obtain ⟨eL⟩ := nonempty_pResidualOf_mulEquiv h3 hU h5.1
  obtain ⟨R, hR⟩ := exists_sylow_pResidualOf T
  set e := (eL.trans eH).trans (MulEquiv.subgroupCongr (CFSG.Models.benderSzModel_eq_sz m))
  have hmem : ∀ {y : G} (hy : y ∈ (T : Subgroup (Halpha D hC.alpha)).map
      (Halpha D hC.alpha).subtype ⊓ CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)),
      (⟨y, hy.2⟩ : CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) ∈ (R : Subgroup _) := by
    intro y hy
    have hy' : y ∈ (R : Subgroup _).map
        (CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)).subtype := hR ▸ hy
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy'
    have : x = ⟨y, hy.2⟩ := Subtype.ext hxy
    rwa [← this]
  have hsq' : (⟨r, hr.2⟩ : CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) ^ 2 =
      (⟨r', hr'.2⟩ : CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) ^ 2 :=
    Subtype.ext (by simpa [pow_two] using hsq)
  have h := CFSG.ComponentClassification.GMS78.inv_mul_mem_sylowCenter_of_sq_eq_of_sz hm e R
    (hmem hr) (hmem hr') hsq'
  exact hU.mem_of_mem_sylowCenter hH h3 h5 hR h

theorem mul_self_mem_of_mem_sylow_map_of_sz (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC)
    (h5 : Conclusion9_5 D hC T S) (hU : DeltaSetup hC T S U) {m : ℕ} (hm : 1 ≤ m)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* SzModel m) {t : G}
    (htT : t ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype) :
    t * t ∈ U := by
  have hu2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  obtain ⟨r, hr, rfl | rfl⟩ := exists_mem_inf_of_mem_sylow_map h3 htT
  · exact hU.mul_self_mem_of_sz hH h3 h5 hm eH hr
  · have hc := commute_d_of_mem_sylow_map hr.1
    have : hC.d * r * (hC.d * r) = r * r := by
      calc hC.d * r * (hC.d * r) = hC.d * (r * hC.d) * r := by group
        _ = hC.d * (hC.d * r) * r := by rw [hc.eq]
        _ = r * r := by rw [← mul_assoc, hu2, one_mul]
    rw [this]
    exact hU.mul_self_mem_of_sz hH h3 h5 hm eH hr

theorem inv_mul_mem_or_of_mul_self_eq_of_sz (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC)
    (h5 : Conclusion9_5 D hC T S) (hU : DeltaSetup hC T S U) {m : ℕ} (hm : 1 ≤ m)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* SzModel m) {t t' : G}
    (htT : t ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype)
    (ht'T : t' ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype)
    (hsq : t * t = t' * t') : t⁻¹ * t' ∈ U ∨ hC.d * (t⁻¹ * t') ∈ U := by
  have hu2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  have hsqr : ∀ r ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype,
      hC.d * r * (hC.d * r) = r * r := by
    intro r hr
    have hc := commute_d_of_mem_sylow_map hr
    calc hC.d * r * (hC.d * r) = hC.d * (r * hC.d) * r := by group
      _ = hC.d * (hC.d * r) * r := by rw [hc.eq]
      _ = r * r := by rw [← mul_assoc, hu2, one_mul]
  have hinj := fun {r r'} hr hr' hs => hU.inv_mul_mem_of_mul_self_eq_of_sz hH h3 h5 hm eH
    (r := r) (r' := r') hr hr' hs
  obtain ⟨r, hr, hrt⟩ := exists_mem_inf_of_mem_sylow_map h3 htT
  obtain ⟨r', hr', hrt'⟩ := exists_mem_inf_of_mem_sylow_map h3 ht'T
  have hcri := commute_d_of_mem_sylow_map (Subgroup.inv_mem _ hr.1)
  rcases hrt with hrt | hrt <;> rcases hrt' with hrt' | hrt' <;> rw [hrt, hrt'] at hsq ⊢
  · exact Or.inl (hinj hr hr' hsq)
  · right
    have h := hinj hr hr' (by rw [hsq, hsqr r' hr'.1])
    have : hC.d * (r⁻¹ * (hC.d * r')) = r⁻¹ * r' := by
      calc hC.d * (r⁻¹ * (hC.d * r')) = hC.d * r⁻¹ * hC.d * r' := by group
        _ = r⁻¹ * (hC.d * hC.d) * r' := by rw [hcri.eq]; group
        _ = r⁻¹ * r' := by rw [hu2, mul_one]
    rwa [this]
  · right
    have h := hinj hr hr' (by rw [← hsq, hsqr r hr.1])
    have : hC.d * ((hC.d * r)⁻¹ * r') = r⁻¹ * r' := by
      calc hC.d * ((hC.d * r)⁻¹ * r') = hC.d * r⁻¹ * hC.d⁻¹ * r' := by group
        _ = r⁻¹ * (hC.d * hC.d⁻¹) * r' := by rw [hcri.eq]; group
        _ = r⁻¹ * r' := by rw [mul_inv_cancel, mul_one]
    rwa [this]
  · left
    have h := hinj hr hr' (by rw [← hsqr r hr.1, hsq, hsqr r' hr'.1])
    have : (hC.d * r)⁻¹ * (hC.d * r') = r⁻¹ * r' := by group
    rwa [this]

theorem inv_mul_conj_mem_of_sz (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC)
    (h5 : Conclusion9_5 D hC T S) (hU : DeltaSetup hC T S U) {Q : Subgroup G}
    (hQ : IsRegularCore ((S : Set G) ∩ D) Q)
    (h7 : ∀ d ∈ D, ∀ e ∈ D, d ≠ e → Commute d e →
      d * e ∈ Subgroup.normalizer ((S : Set G) ∩ D) → d * e ∈ Q)
    {m : ℕ} (hm : 1 ≤ m)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* SzModel m)
    {z : G} (hzU : z ∈ U) (hz1 : z ≠ 1) {g : G} (hgz : Commute (g * z * g⁻¹) z)
    (he : g * z * g⁻¹ ∉ U) {a : G} (haU : a ∈ U) {t : G}
    (htT : t ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype) :
    t⁻¹ * ((g * a * g⁻¹) * t * (g * a * g⁻¹)⁻¹) ∈ U := by
  have := hU.isElementaryAbelian
  have hu2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  have hQC := hU.regularCore_eq_centralizer hH h3 h5 hQ
  have hQN : Q ≤ Subgroup.normalizer ((fun v : G => hC.d * v) '' (U : Set G)) :=
    hU.sylow_inter ▸ hQ.1
  have hAQ := hU.conj_mem_regularCore hH h3 h5 hQ h7 hzU hz1 hgz haU
  have hA2 : g * a * g⁻¹ * (g * a * g⁻¹) = 1 := by
    calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
      _ = 1 := by
        rw [← pow_two, CFSG.elemPow_eq_one_of_isElementaryAbelian a haU, mul_one, mul_inv_cancel]
  have hAT1 : g * a * g⁻¹ ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype →
      g * a * g⁻¹ = 1 := fun h => by
    rw [hU.eq_one_of_conj_mem_sylow_map hH h3 h5 hzU he haU h, mul_one, mul_inv_cancel]
  generalize g * a * g⁻¹ = A at hAQ hA2 hAT1 ⊢
  have hAC : A ∈ Subgroup.centralizer (U : Set G) := hQC ▸ hAQ
  have hAinv : A⁻¹ = A := inv_eq_of_mul_eq_one_right hA2
  have ht'T : A * t * A⁻¹ ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype :=
    hU.conj_mem_sylow_map h5 (hQN hAQ) htT
  have htt := hU.mul_self_mem_of_mem_sylow_map_of_sz hH h3 h5 hm eH htT
  have hsq : t * t = A * t * A⁻¹ * (A * t * A⁻¹) := by
    calc t * t = A * (t * t) * A⁻¹ := by
          rw [← (Subgroup.mem_centralizer_iff.mp hAC _ htt), mul_inv_cancel_right]
      _ = A * t * A⁻¹ * (A * t * A⁻¹) := by group
  rcases hU.inv_mul_mem_or_of_mul_self_eq_of_sz hH h3 h5 hm eH htT ht'T hsq with hc | hc
  · exact hc
  · exfalso
    have hcT : t⁻¹ * (A * t * A⁻¹) ∈
        (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ htT) ht'T
    have h1' : A * (t⁻¹ * (A * t * A⁻¹)) * A⁻¹ = (t⁻¹ * (A * t * A⁻¹))⁻¹ := by
      simp only [hAinv, mul_inv_rev, inv_inv, mul_assoc, hA2, mul_one]
    generalize hcdef : t⁻¹ * (A * t * A⁻¹) = c at hc hcT h1'
    have huc := commute_d_of_mem_sylow_map hcT
    have hb2 : hC.d * c * (hC.d * c) = 1 := by
      rw [← pow_two]
      exact CFSG.elemPow_eq_one_of_isElementaryAbelian _ hc
    have hc2 : c * c = 1 := by
      rw [← hb2]
      calc c * c = hC.d * (hC.d * c) * c := by rw [← mul_assoc, hu2, one_mul]
        _ = hC.d * (c * hC.d) * c := by rw [huc.eq]
        _ = hC.d * c * (hC.d * c) := by group
    have h1 : A * c * A⁻¹ = c := by rw [h1', inv_eq_of_mul_eq_one_right hc2]
    have hAb : A * (hC.d * c) * A⁻¹ = hC.d * c := by
      rw [← (Subgroup.mem_centralizer_iff.mp hAC _ hc), mul_inv_cancel_right]
    have hub : hC.d = c * (hC.d * c) := by
      rw [← mul_assoc, ← huc.eq, mul_assoc, hc2, mul_one]
    have hAu : A * hC.d * A⁻¹ = hC.d := by
      calc A * hC.d * A⁻¹ = A * c * A⁻¹ * (A * (hC.d * c) * A⁻¹) := by
            conv_lhs => rw [hub]
            group
        _ = hC.d := by rw [h1, hAb, ← hub]
    have hA1 := hAT1 (hU.mem_sylow_map_of_mem_centralizer h5 hAC hAu)
    have hc1 : c = 1 := by rw [← hcdef, hA1]; group
    apply hU.d_not_mem h3
    rwa [hc1, mul_one] at hc

theorem commute_of_mem_sylow_map (h5 : Conclusion9_5 D hC T S) (hU : DeltaSetup hC T S U)
    {t v : G} (htT : t ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype)
    (hv : v ∈ U) : Commute t v := by
  have hu2 : hC.d * hC.d = 1 := hC.setup.oddT.mul_self_eq_one hC.hd
  rw [← h5.1, hU.sylow_inter, Subgroup.mem_centralizer_iff] at htT
  have h1 : hC.d * t = t * hC.d := htT _ ⟨1, U.one_mem, mul_one _⟩
  have h2 : hC.d * v * t = t * (hC.d * v) := htT _ ⟨v, hv, rfl⟩
  calc t * v = t * hC.d * (hC.d * v) := by rw [mul_assoc, ← mul_assoc hC.d, hu2, one_mul]
    _ = hC.d * (t * (hC.d * v)) := by rw [← h1, mul_assoc]
    _ = v * t := by rw [← h2, ← mul_assoc, ← mul_assoc, hu2, one_mul]

theorem mul_self_mem_of_mem_regularCore_of_sz (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC)
    (h5 : Conclusion9_5 D hC T S) (hU : DeltaSetup hC T S U) {Q : Subgroup G}
    (hQ : IsRegularCore ((S : Set G) ∩ D) Q)
    (h7 : ∀ d ∈ D, ∀ e ∈ D, d ≠ e → Commute d e →
      d * e ∈ Subgroup.normalizer ((S : Set G) ∩ D) → d * e ∈ Q)
    {m : ℕ} (hm : 1 ≤ m)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* SzModel m)
    {z : G} (hzU : z ∈ U) (hz1 : z ≠ 1) {g : G} (hgz : Commute (g * z * g⁻¹) z)
    (he : g * z * g⁻¹ ∉ U) {x : G} (hxQ : x ∈ Q) : x * x ∈ U := by
  have := hU.isElementaryAbelian
  obtain ⟨a, haU, t, htT, rfl⟩ :=
    hU.exists_eq_conj_mul_of_mem_regularCore hH h3 h5 hQ h7 hzU hz1 hgz he hxQ
  have hc := hU.inv_mul_conj_mem_of_sz hH h3 h5 hQ h7 hm eH hzU hz1 hgz he haU htT
  have hA2 : g * a * g⁻¹ * (g * a * g⁻¹) = 1 := by
    calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
      _ = 1 := by
        rw [← pow_two, CFSG.elemPow_eq_one_of_isElementaryAbelian a haU, mul_one, mul_inv_cancel]
  have hAinv : (g * a * g⁻¹)⁻¹ = g * a * g⁻¹ := inv_eq_of_mul_eq_one_right hA2
  generalize g * a * g⁻¹ = A at hc hAinv ⊢
  generalize hcdef : t⁻¹ * (A * t * A⁻¹) = c at hc
  have hAt : A * t * A⁻¹ = t * c := by rw [← hcdef]; group
  have htc := commute_of_mem_sylow_map h5 hU htT hc
  have htt := hU.mul_self_mem_of_mem_sylow_map_of_sz hH h3 h5 hm eH htT
  have h : A * t * (A * t) = t * t * c := by
    calc A * t * (A * t) = A * t * A⁻¹ * t := by rw [hAinv]; group
      _ = t * c * t := by rw [hAt]
      _ = t * t * c := by rw [mul_assoc, ← htc.eq, ← mul_assoc]
  rw [h]
  exact U.mul_mem htt hc

theorem conj_mem_inf_of_sz (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC)
    (h5 : Conclusion9_5 D hC T S) (hU : DeltaSetup hC T S U) {Q : Subgroup G}
    (hQ : IsRegularCore ((S : Set G) ∩ D) Q)
    (h7 : ∀ d ∈ D, ∀ e ∈ D, d ≠ e → Commute d e →
      d * e ∈ Subgroup.normalizer ((S : Set G) ∩ D) → d * e ∈ Q)
    {m : ℕ} (hm : 1 ≤ m)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* SzModel m)
    {z : G} (hzU : z ∈ U) (hz1 : z ≠ 1) {g : G} (hgz : Commute (g * z * g⁻¹) z)
    (he : g * z * g⁻¹ ∉ U) {a : G} (haU : a ∈ U) {r : G}
    (hr : r ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
      CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) :
    g * a * g⁻¹ * r * (g * a * g⁻¹)⁻¹ ∈
      (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
        CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha) := by
  have hc := hU.inv_mul_conj_mem_of_sz hH h3 h5 hQ h7 hm eH hzU hz1 hgz he haU hr.1
  have h : g * a * g⁻¹ * r * (g * a * g⁻¹)⁻¹ =
      r * (r⁻¹ * (g * a * g⁻¹ * r * (g * a * g⁻¹)⁻¹)) := by group
  rw [h]
  exact Subgroup.mul_mem _ hr ⟨hU.le_sylow_map hc, hU.le_pResidualOf hc⟩

theorem mem_of_commute_conj_of_sz (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC)
    (h5 : Conclusion9_5 D hC T S) (hU : DeltaSetup hC T S U) {Q : Subgroup G}
    (hQ : IsRegularCore ((S : Set G) ∩ D) Q)
    (h7 : ∀ d ∈ D, ∀ e ∈ D, d ≠ e → Commute d e →
      d * e ∈ Subgroup.normalizer ((S : Set G) ∩ D) → d * e ∈ Q)
    {m : ℕ} (hm : 1 ≤ m)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* SzModel m)
    (hUn : Nat.card U = 2 ^ (2 * m + 1))
    {z : G} (hzU : z ∈ U) (hz1 : z ≠ 1) {g : G} (hgz : Commute (g * z * g⁻¹) z)
    (he : g * z * g⁻¹ ∉ U) {a : G} (haU : a ∈ U) (ha1 : a ≠ 1) {r : G}
    (hr : r ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
      CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha))
    (hra : Commute r (g * a * g⁻¹)) : r ∈ U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hca : g⁻¹ * r * g ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := (Commute.conj_iff g⁻¹).mpr hra
    have h' : g⁻¹ * (g * a * g⁻¹) * g⁻¹⁻¹ = a := by group
    rw [h', inv_inv] at h
    exact h.eq
  have hxN := hU.centralizer_le_normalizer_delta hH h3 h5 haU ha1 hca
  obtain ⟨j, hj⟩ : ∃ j : ℕ, r ^ 2 ^ j = 1 := by
    have hp : IsPGroup 2 ((T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype) :=
      T.isPGroup'.map _
    obtain ⟨j, hj⟩ := hp ⟨r, hr.1⟩
    exact ⟨j, by simpa using congrArg Subtype.val hj⟩
  have hxj : (g⁻¹ * r * g) ^ 2 ^ j = 1 := by
    have h : (g⁻¹ * r * g⁻¹⁻¹) ^ 2 ^ j = g⁻¹ * r ^ 2 ^ j * g⁻¹⁻¹ := conj_pow
    rw [inv_inv] at h
    rw [h, hj, mul_one, inv_mul_cancel]
  have hxQ := hU.mem_regularCore_of_pow_eq_one h3 hQ hUn
    (by rw [Nat.odd_iff]; omega) hxN hxj
  have hsq := hU.mul_self_mem_of_mem_regularCore_of_sz hH h3 h5 hQ h7 hm eH hzU hz1 hgz he hxQ
  have hr2 : g * (g⁻¹ * r * g * (g⁻¹ * r * g)) * g⁻¹ = r * r := by group
  have hr2T : g * (g⁻¹ * r * g * (g⁻¹ * r * g)) * g⁻¹ ∈
      (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype := by
    rw [hr2]
    exact Subgroup.mul_mem _ hr.1 hr.1
  have hw1 := hU.eq_one_of_conj_mem_sylow_map hH h3 h5 hzU he hsq hr2T
  have hrr : r * r = 1 * 1 := by rw [← hr2, hw1, mul_one, mul_one, mul_inv_cancel]
  have h := hU.inv_mul_mem_of_mul_self_eq_of_sz hH h3 h5 hm eH hr (Subgroup.one_mem _) hrr
  rw [mul_one] at h
  exact inv_mem_iff.mp h

theorem eq_of_mul_self_eq_one_of_sz (hH : Th91Hyp D hC) (h3 : Conclusion9_3 D hC)
    (h5 : Conclusion9_5 D hC T S) (hU : DeltaSetup hC T S U) {Q : Subgroup G}
    (hQ : IsRegularCore ((S : Set G) ∩ D) Q)
    (h7 : ∀ d ∈ D, ∀ e ∈ D, d ≠ e → Commute d e →
      d * e ∈ Subgroup.normalizer ((S : Set G) ∩ D) → d * e ∈ Q)
    {m : ℕ} (hm : 1 ≤ m)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* SzModel m)
    (hUn : Nat.card U = 2 ^ (2 * m + 1))
    {z : G} (hzU : z ∈ U) (hz1 : z ≠ 1) {g : G} (hgz : Commute (g * z * g⁻¹) z)
    (he : g * z * g⁻¹ ∉ U) {a a' : G} (haU : a ∈ U) (ha'U : a' ∈ U) {r : G}
    (hr : r ∈ (T : Subgroup (Halpha D hC.alpha)).map (Halpha D hC.alpha).subtype ⊓
      CFSG.Quasithin.pResidualOf 2 (Halpha D hC.alpha)) (hrU : r ∉ U)
    (h1 : g * a * g⁻¹ * r * (g * a * g⁻¹ * r) = 1)
    (h2 : g * a' * g⁻¹ * r * (g * a' * g⁻¹ * r) = 1) : a = a' := by
  have := hU.isElementaryAbelian
  by_contra hne
  have hb : a⁻¹ * a' ∈ U := U.mul_mem (U.inv_mem haU) ha'U
  have hb1 : a⁻¹ * a' ≠ 1 := fun h => hne (inv_mul_eq_one.mp h)
  apply hrU
  refine hU.mem_of_commute_conj_of_sz hH h3 h5 hQ h7 hm eH hUn hzU hz1 hgz he hb hb1 hr ?_
  have hsq : ∀ x ∈ U, g * x * g⁻¹ * (g * x * g⁻¹) = 1 := fun x hx => by
    calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by
        rw [← pow_two, CFSG.elemPow_eq_one_of_isElementaryAbelian x hx, mul_one, mul_inv_cancel]
  have hA2 := hsq a haU
  have hA'2 := hsq a' ha'U
  have hgb : g * (a⁻¹ * a') * g⁻¹ = (g * a * g⁻¹)⁻¹ * (g * a' * g⁻¹) := by group
  rw [hgb]
  generalize g * a * g⁻¹ = A at h1 hA2 ⊢
  generalize g * a' * g⁻¹ = A' at h2 hA'2 ⊢
  have hAi : A⁻¹ = A := inv_eq_of_mul_eq_one_right hA2
  have e1 : A * r * A = r⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    simpa only [mul_assoc] using h1
  have e2 : A' * r * A' = r⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    simpa only [mul_assoc] using h2
  show r * (A⁻¹ * A') = A⁻¹ * A' * r
  rw [hAi]
  calc r * (A * A') = A * A * r * (A * A') := by rw [hA2, one_mul]
    _ = A * (A * r * A) * A' := by group
    _ = A * (A' * r * A') * A' := by rw [e1, e2]
    _ = A * A' * r * (A' * A') := by group
    _ = A * A' * r := by rw [hA'2, mul_one]

end DeltaSetup

end CFSG.OddTranspositions.PartThree.Nine
