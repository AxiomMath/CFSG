module

public import CFSG.Quasithin.Vol2.KGFactC31KG443Sec
public import CFSG.Quasithin.Vol2.KGFactC31Act
public import CFSG.Sporadic.J4.QT2LocX0CentMain
public import CFSG.Sporadic.J4
public import CFSG.Sporadic.Mathieu.M24
public import Mathlib.GroupTheory.Perm.Centralizer
public import CFSG.Certificates.Kernel.ThDemp.OrbCent
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Vol2.KGFactC31A7
public import CFSG.Quasithin.Vol2.KGFactC31M22Ref
public import CFSG.RankThree.PartOne.K133.Moving
public import CFSG.RankThree.PartOne.K133.SylowKill
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
public import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldCentralizer
public import CFSG.RankThree.PartOne.KF.R7Final
public import CFSG.RankThree.PartOne.KF.SUGram
public import CFSG.RankThree.PartOne.KFOUT3.KtySUQuot
public import CFSG.RankThree.PartOne.KLAY.Core
public import CFSG.RankThree.PartOne.Q1327T.Item7Inv
public import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutUnitary
public import CFSG.RankThree.PartOne.S12.InputsSec15
public import CFSG.RankThree.PartOne.S12.Sec136Pair
public import CFSG.RankThree.PartOne.S12.Sec136Setup
public import CFSG.RankThree.PartOne.S12.Sec141Row
public import CFSG.RankThree.PartOne.S12.Sec15FA
public import CFSG.RankThree.PartOne.S12.Sec15Items
public import CFSG.RankThree.PartOne.S15K.PSylowOrth
public import CFSG.RankThree.PerfectCover.HopfCentralCoversFinite
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import CFSG.Sporadic.J4.QT2LocCntProof
public import CFSG.Sporadic.J4.QT2LocFiveProof
public import CFSG.Sporadic.J4.QT2LocFixMain
public import CFSG.Sporadic.J4.QT2LocScanCheckBase
public import CFSG.Sporadic.J4.QT2LocX0CentMainBase1
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CommutatorNormalizer
public import CFSG.Walter.Defs
public import Certificates.Certificate1
public import Certificates.Certificate2
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.Quasithin.KGC31.KG443

open Function CFSG.Blueprint

theorem false_of_cent_prime {S T : Type} [Group S] [Group T] [Finite S] [Finite T]
    (hZ : Subgroup.center T = ⊥) {Y : Subgroup S} {φ : ↥Y →* T} (hφ : Surjective φ)
    {l : S} (hl : ∀ y ∈ Y, l * y = y * l) {r : ℕ} (hr : r.Prime) (hlr : orderOf l = r)
    (hrT : r ∣ Nat.card T) (hrS : ¬ r ^ 2 ∣ Nat.card S) : False := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' r hrT
  obtain ⟨y, rfl⟩ := hφ t
  have hn0 : orderOf y ≠ 0 := (orderOf_pos y).ne'
  obtain ⟨e, m, hrm, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 r hr.one_lt.ne'
  have hm0 : m ≠ 0 := by rintro rfl; exact hrm (dvd_zero r)
  have hφm : φ (y ^ m) ≠ 1 := by
    rw [map_pow]
    intro h
    exact hrm (ht ▸ orderOf_dvd_of_pow_eq_one h)
  have hord : orderOf (y ^ m) = r ^ e := by
    rw [orderOf_pow_of_dvd hm0 (by rw [hn]; exact dvd_mul_left m _), hn,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
  set z : S := ((y ^ m : ↥Y) : S) with hz
  have hzord : orderOf z = r ^ e := by rw [hz, Subgroup.orderOf_coe, hord]
  have he1 : e = 1 := by
    rcases Nat.lt_or_ge e 2 with h2 | h2
    · rcases Nat.eq_zero_or_pos e with h0 | h0
      · exfalso
        rw [h0, pow_zero, orderOf_eq_one_iff] at hord
        exact hφm (by rw [hord, map_one])
      · omega
    · exfalso
      exact hrS ((pow_dvd_pow r h2).trans (hzord ▸ orderOf_dvd_natCard z))
  rw [he1, pow_one] at hzord
  have hcomm : Commute l z := hl z (y ^ m).2
  have hPl : IsPGroup r ↥(Subgroup.zpowers l) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hlr, pow_one])
  have hPz : IsPGroup r ↥(Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzord, pow_one])
  have hnorm : Subgroup.zpowers l ≤ Subgroup.normalizer (Subgroup.zpowers z : Set S) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact ((hcomm.zpow_right k).eq).symm
  have hP := IsPGroup.to_sup_of_normal_right' hPl hPz hnorm
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  have hk1 : k ≤ 1 := by
    by_contra hk2
    exact hrS ((pow_dvd_pow r (by omega)).trans
      (hk ▸ Subgroup.card_subgroup_dvd_card (Subgroup.zpowers l ⊔ Subgroup.zpowers z)))
  have heq : Subgroup.zpowers l = Subgroup.zpowers l ⊔ Subgroup.zpowers z := by
    refine Subgroup.eq_of_le_of_card_ge le_sup_left ?_
    rw [hk, Nat.card_zpowers, hlr]
    calc r ^ k ≤ r ^ 1 := Nat.pow_le_pow_right hr.pos hk1
      _ = r := pow_one r
  have hzl : z ∈ Subgroup.zpowers l := by
    rw [heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hzl
  have hcen : (y ^ m : ↥Y) ∈ Subgroup.center ↥Y := by
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    show (w : S) * z = z * (w : S)
    rw [← hj]
    exact ((Commute.zpow_left (hl w w.2) j).eq).symm
  have hφc : φ (y ^ m) ∈ Subgroup.center T := by
    rw [Subgroup.mem_center_iff]
    intro t'
    obtain ⟨w, rfl⟩ := hφ t'
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hcen w]
  rw [hZ, Subgroup.mem_bot] at hφc
  exact hφm hφc

theorem card_centralizer_of_order_23 {σ : Equiv.Perm (Fin 24)} (hσ : orderOf σ = 23) :
    Nat.card (Subgroup.centralizer ({σ} : Set (Equiv.Perm (Fin 24)))) = 23 := by
  classical
  have hmem : ∀ n ∈ σ.cycleType, n = 23 := fun n hn => by
    have h1 := Equiv.Perm.dvd_of_mem_cycleType hn
    rw [hσ] at h1
    have h2 := Equiv.Perm.two_le_of_mem_cycleType hn
    rcases (Nat.dvd_prime (by norm_num)).mp h1 with h | h
    · omega
    · exact h
  have hsum : σ.cycleType.sum ≤ 24 := by
    rw [Equiv.Perm.sum_cycleType]
    exact (Finset.card_le_univ _).trans (by simp)
  have hne : σ.cycleType ≠ 0 := by
    rw [Ne, Equiv.Perm.cycleType_eq_zero]
    rintro rfl
    simp at hσ
  have hk : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 23 :=
    Multiset.eq_replicate.mpr ⟨rfl, hmem⟩
  have hct : σ.cycleType = {23} := by
    rw [hk] at hsum hne ⊢
    rw [Multiset.sum_replicate, smul_eq_mul] at hsum
    have h1 : Multiset.card σ.cycleType = 1 := by
      rcases Nat.lt_or_ge (Multiset.card σ.cycleType) 1 with h | h
      · exfalso
        apply hne
        rw [Nat.lt_one_iff.mp h, Multiset.replicate_zero]
      · omega
    rw [h1, Multiset.replicate_one]
  rw [Equiv.Perm.nat_card_centralizer, hct]
  simp

theorem prime_dvd_m24_card {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) (h : r ∣ 244823040) :
    r = 5 ∨ r = 7 ∨ r = 11 ∨ r = 23 := by
  have h' : r ∣ 2 ^ 10 * 3 ^ 3 * 5 * 7 * 11 * 23 := by norm_num; exact h
  have hpp : ∀ q : ℕ, q.Prime → r ∣ q → r = q := fun q hq hrq =>
    (Nat.prime_dvd_prime_iff_eq hr hq).mp hrq
  rcases (Nat.Prime.dvd_mul hr).mp h' with h1 | h1
  · rcases (Nat.Prime.dvd_mul hr).mp h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hr).mp h2 with h3 | h3
      · rcases (Nat.Prime.dvd_mul hr).mp h3 with h4 | h4
        · rcases (Nat.Prime.dvd_mul hr).mp h4 with h6 | h6
          · have := hpp 2 Nat.prime_two (hr.dvd_of_dvd_pow h6); omega
          · have := hpp 3 Nat.prime_three (hr.dvd_of_dvd_pow h6); omega
        · exact Or.inl (hpp 5 (by norm_num) h4)
      · exact Or.inr (Or.inl (hpp 7 (by norm_num) h3))
    · exact Or.inr (Or.inr (Or.inl (hpp 11 (by norm_num) h2)))
  · exact Or.inr (Or.inr (Or.inr (hpp 23 (by norm_num) h1)))

theorem false_of_cent_m24 {S : Type}
    [Group S] [Finite S] (e : S ≃* NativeSporadic.Carrier .M24) {Y : Subgroup S}
    {φ : ↥Y →* NativeSporadic.Carrier .M22} (hφ : Surjective φ) {l : S}
    (hl : ∀ y ∈ Y, l * y = y * l) {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) (hlr : orderOf l = r) :
    False := by
  have : Finite (NativeSporadic.Carrier .M22) := (inferInstance : Finite M22.G₀)
  have hS : Nat.card S = 244823040 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M24
  have hM22 : Nat.card (NativeSporadic.Carrier .M22) = 443520 := CFSG.Sporadic.Mathieu.card_M22
  have hrS : r ∣ 244823040 := hS ▸ (hlr ▸ orderOf_dvd_natCard l)
  rcases prime_dvd_m24_card hr h5 hrS with rfl | rfl | rfl | rfl
  · exact false_of_cent_prime center_m22 hφ hl hr hlr (by rw [hM22]; norm_num)
      (by rw [hS]; norm_num)
  · exact false_of_cent_prime center_m22 hφ hl hr hlr (by rw [hM22]; norm_num)
      (by rw [hS]; norm_num)
  · exact false_of_cent_prime center_m22 hφ hl hr hlr (by rw [hM22]; norm_num)
      (by rw [hS]; norm_num)
  ·
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have h5Y : 5 ∣ Nat.card Y :=
      (show 5 ∣ Nat.card (NativeSporadic.Carrier .M22) by rw [hM22]; norm_num).trans
        (card_dvd_of_surjective hφ)
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 5 h5Y
    let eM : S ≃* ↥NativeSporadic.M24 := e
    let ι : S →* Equiv.Perm (Fin 24) := NativeSporadic.M24.subtype.comp eM.toMonoidHom
    have hι : Injective ι := Subtype.val_injective.comp eM.injective
    have hσ : orderOf (ι l) = 23 := by rw [orderOf_injective ι hι, hlr]
    have hτ : orderOf (ι (u : S)) = 5 := by
      rw [orderOf_injective ι hι, Subgroup.orderOf_coe, hu]
    have hτσ : ι (u : S) ∈ Subgroup.centralizer ({ι l} : Set (Equiv.Perm (Fin 24))) := by
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hl (u : S) u.2]
    have hd := Subgroup.orderOf_dvd_natCard _ hτσ
    rw [hτ, card_centralizer_of_order_23 hσ] at hd
    exact absurd hd (by norm_num)

theorem orderOf_conj_inv {X : Type*} [Group X] (g x : X) : orderOf (g⁻¹ * x * g) = orderOf x := by
  rw [show g⁻¹ * x * g = MulAut.conj g⁻¹ x by simp, MulEquiv.orderOf_eq]

theorem conj_mem_centralizer {X : Type*} [Group X] {x v g ξ : X} (hxv : x * v = v * x) {k : ℤ}
    (hk : (g⁻¹ * v * g) ^ k = ξ) : g⁻¹ * x * g ∈ Subgroup.centralizer ({ξ} : Set X) := by
  rw [Subgroup.mem_centralizer_singleton_iff, ← hk]
  have hc : Commute (g⁻¹ * x * g) (g⁻¹ * v * g) := by
    show (g⁻¹ * x * g) * (g⁻¹ * v * g) = (g⁻¹ * v * g) * (g⁻¹ * x * g)
    simp only [mul_assoc, mul_inv_cancel_left]
    rw [← mul_assoc x, hxv, mul_assoc]
  exact (hc.zpow_right k).eq

theorem le_seven_of_dvd_6720 {r : ℕ} (hr : r.Prime) (h : r ∣ 6720) : r ≤ 7 := by
  have hd' : r ∣ 2 ^ 6 * 3 * 5 * 7 := by norm_num; exact h
  have hpp : ∀ q : ℕ, q.Prime → r ∣ q → r = q := fun q hq hrq =>
    (Nat.prime_dvd_prime_iff_eq hr hq).mp hrq
  rcases (Nat.Prime.dvd_mul hr).mp hd' with h1 | h1
  · rcases (Nat.Prime.dvd_mul hr).mp h1 with h2 | h2
    · rcases (Nat.Prime.dvd_mul hr).mp h2 with h3 | h3
      · have := hpp 2 Nat.prime_two (hr.dvd_of_dvd_pow h3); omega
      · have := hpp 3 Nat.prime_three h3; omega
    · have := hpp 5 (by norm_num) h2; omega
  · have := hpp 7 (by norm_num) h1; omega

theorem false_of_cent_j4
    {S : Type} [Group S] [Finite S] (e : S ≃* NativeSporadic.Carrier .J4) {Y : Subgroup S}
    {φ : ↥Y →* NativeSporadic.Carrier .M22} (hφ : Surjective φ) {l : S}
    (hl : ∀ y ∈ Y, l * y = y * l) {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) (hlr : orderOf l = r) :
    False := by
  have : Finite (NativeSporadic.Carrier .M22) := (inferInstance : Finite M22.G₀)
  have hF := CFSG.Sporadic.J4.j4Facts
  let e' : S ≃* ↥CFSG.Sporadic.J4.J := e.trans (CFSG.Sporadic.J4.seedEquiv hF.mat)
  have hS : Nat.card S = 86775571046077562880 := by
    rw [Nat.card_congr e'.toEquiv]
    exact CFSG.Sporadic.J4.card_J hF
  have hM22 : Nat.card (NativeSporadic.Carrier .M22) = 443520 := CFSG.Sporadic.Mathieu.card_M22
  by_cases h57 : r = 5 ∨ r = 7
  · rcases h57 with rfl | rfl
    · exact false_of_cent_prime center_m22 hφ hl hr hlr (by rw [hM22]; norm_num)
        (by rw [hS]; norm_num)
    · exact false_of_cent_prime center_m22 hφ hl hr hlr (by rw [hM22]; norm_num)
        (by rw [hS]; norm_num)
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h5Y : 5 ∣ Nat.card Y :=
    (show 5 ∣ Nat.card (NativeSporadic.Carrier .M22) by rw [hM22]; norm_num).trans
      (card_dvd_of_surjective hφ)
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 5 h5Y
  set x : ↥CFSG.Sporadic.J4.J := e' l with hx
  set v : ↥CFSG.Sporadic.J4.J := e' (u : S) with hv
  have hxv : x * v = v * x := by
    rw [hx, hv, ← map_mul, ← map_mul, hl (u : S) u.2]
  have hxo : orderOf x = r := by rw [hx, MulEquiv.orderOf_eq, hlr]
  have hvo : orderOf v = 5 := by
    rw [hv, MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hu]
  have hξ := CFSG.Sporadic.J4.QT2.orderOf_fiveElt hF.mat
  have hcardJ := CFSG.Sporadic.J4.card_J hF
  have hP : IsPGroup 5 ↥(Subgroup.zpowers CFSG.Sporadic.J4.QT2.fiveElt) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hξ, pow_one])
  have hPi : ¬ 5 ∣ (Subgroup.zpowers CFSG.Sporadic.J4.QT2.fiveElt).index := by
    have h := (Subgroup.zpowers CFSG.Sporadic.J4.QT2.fiveElt).card_mul_index
    rw [Nat.card_zpowers, hξ, hcardJ] at h
    have hi : (Subgroup.zpowers CFSG.Sporadic.J4.QT2.fiveElt).index = 17355114209215512576 := by
      omega
    rw [hi]
    norm_num
  obtain ⟨g, hg⟩ := exists_conj_mem_of_sylow hP hPi (y := v) ⟨1, by rw [pow_one, ← hvo,
    pow_orderOf_eq_one]⟩
  have hvo' : orderOf (g⁻¹ * v * g) = 5 := by rw [orderOf_conj_inv, hvo]
  have hzeq : Subgroup.zpowers (g⁻¹ * v * g) = Subgroup.zpowers CFSG.Sporadic.J4.QT2.fiveElt :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hg)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hvo', hξ])
  have hmemξ : CFSG.Sporadic.J4.QT2.fiveElt ∈ Subgroup.zpowers (g⁻¹ * v * g) := by
    rw [hzeq]
    exact Subgroup.mem_zpowers _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmemξ
  have hmem : g⁻¹ * x * g ∈
      Subgroup.centralizer ({CFSG.Sporadic.J4.QT2.fiveElt} : Set ↥CFSG.Sporadic.J4.J) :=
    conj_mem_centralizer (X := ↥CFSG.Sporadic.J4.J) hxv hk
  have hd : orderOf (g⁻¹ * x * g) ∣
      Nat.card ↥(Subgroup.centralizer ({CFSG.Sporadic.J4.QT2.fiveElt} : Set ↥CFSG.Sporadic.J4.J)) :=
    Subgroup.orderOf_dvd_natCard _ hmem
  rw [CFSG.Sporadic.J4.QT2.card_centralizer_fiveElt hF, orderOf_conj_inv, hxo] at hd
  have h7 := le_seven_of_dvd_6720 hr hd
  have : r = 5 ∨ r = 7 := by
    interval_cases r <;> simp_all (config := { decide := true })
  exact h57 this

end CFSG.Quasithin.KGC31.KG443

end
