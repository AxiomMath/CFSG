module

public import CFSG.RankThree.PartTwo.Sec15.Item1513Proof
public import CFSG.RankThree.PartTwo.KFacts.KS18A7M22Proof
import CFSG.RankThree.PartTwo.KFacts.KS14MathieuAutCore
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.Sec13.Item133
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
import CFSG.RankThree.PartTwo.Sec14.Item1413ProofTools
import CFSG.RankThree.PartTwo.Sec14.Item1413Res2ProofTools
import CFSG.RankThree.PartTwo.Sec14.Item148PtRes2ProofTypes
import CFSG.RankThree.PartTwo.Sec15.Item1510ProofTools
import CFSG.RankThree.PartTwo.Sec15.Item1511ProofTools
import CFSG.RankThree.PartTwo.Sec15.Item1514Steps1515
import CFSG.RankThree.PartTwo.Sec15.Item1513StepsProofTransv
import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec15.Proof1511

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem res1_commute_of_threeElem_normalizer {c w : G} (hc3 : c ^ 3 = 1) {m : ℕ}
    (hw : w ^ 3 ^ m = 1) (hN : w ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
    w * c = c * w := by
  have hwc : w * c * w⁻¹ ∈ Subgroup.zpowers c :=
    (Subgroup.mem_normalizer_iff.mp hN c).mp (Subgroup.mem_zpowers c)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hwc
  have hjmod : c ^ j = c ^ (j % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv j 3, zpow_add, zpow_mul]
    rw [show ((3 : ℤ)) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hc3, one_zpow, mul_one]
  rw [hjmod] at hj
  obtain h0 | h1 | h2 : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
  · rw [h0, zpow_zero] at hj
    have : c = 1 := by
      have e : c = w⁻¹ * (w * c * w⁻¹) * w := by group
      rw [e, ← hj]
      group
    rw [this, mul_one, one_mul]
  · rw [h1, zpow_one] at hj
    calc w * c = w * c * w⁻¹ * w := by group
      _ = c * w := by rw [← hj]
  · rw [h2] at hj
    have hinv : w * c * w⁻¹ = c⁻¹ := by
      rw [← hj]
      have : c ^ (2 : ℤ) = c⁻¹ * c ^ 3 := by group
      rw [this, hc3, mul_one]
    have hw2 : w ^ 2 * c = c * w ^ 2 := by
      have e : w ^ 2 * c * (w ^ 2)⁻¹ = w * (w * c * w⁻¹) * w⁻¹ := by
        rw [sq]
        group
      have e2 : w ^ 2 * c * (w ^ 2)⁻¹ = c := by
        rw [e, hinv]
        have : w * c⁻¹ * w⁻¹ = (w * c * w⁻¹)⁻¹ := by group
        rw [this, hinv, inv_inv]
      calc w ^ 2 * c = w ^ 2 * c * (w ^ 2)⁻¹ * w ^ 2 := by group
        _ = c * w ^ 2 := by rw [e2]
    obtain ⟨t, ht⟩ : ∃ t, 3 ^ m + 1 = 2 * t := by
      obtain ⟨u, hu⟩ : Odd (3 ^ m) := Odd.pow (by decide)
      exact ⟨u + 1, by omega⟩
    have hwt : w = (w ^ 2) ^ t := by
      rw [← pow_mul, ← ht, pow_succ, hw, one_mul]
    rw [hwt]
    exact (Commute.pow_left (show Commute (w ^ 2) c from hw2) t).eq


theorem card_inf_irreducible_of_a7_m22 (h131 : Item131) {A L : Subgroup G} {c : G}
    (h : Sec15R G A c L)
    (hL : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7))) :
    Nat.card (A ⊓ L : Subgroup G) = 9 ∧ A = Subgroup.zpowers c ⊔ (A ⊓ L) ∧
      Sec21.IsIrreducibleOn (Sec4.autIn (L ⊓ Subgroup.normalizer (A : Set G)) (A ⊓ L)) := by
  have hD := h.toSec13Data
  have hcL : c ∉ L := h.hypS.2.2 c h.zpowers_mem_omegaA L h.mem_lA
  have hA7c : Nat.card (alternatingGroup (Fin 7)) = 2520 :=
    KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1
  rcases hL with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · have hcardL : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) = 443520 :=
      (Nat.card_congr φ.toEquiv).trans KFacts.KS14.card_nativeM22
    have hJ2e : IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
        CFSG.Blueprint.NativeSporadic.J2) := ⟨fun χ => by
      have h1 := (Nat.card_congr χ.toEquiv).symm.trans hcardL
      rw [KFacts.KS14.card_nativeJ2] at h1
      omega⟩
    have hnPGL : ¬ Sec8.IsZ3PGLThreePi (lBarA c L A) := fun hP =>
      not_isLThreePi_of_mulEquiv φ (fun p e _ => KFacts.KS14.not_isoLThreePi_M22 p e)
        (facts_of_isZ3PGLThreePi hD hP).1
    exact Proof1413Res2.irreducible_of_cases131 h131 hD hcL
      (Proof1514.isEmpty_mulEquiv_M12_of_M22 φ) hJ2e hnPGL
  · have hcardL : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) = 2520 :=
      (Nat.card_congr φ.toEquiv).trans hA7c
    have hJ2e : IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃*
        CFSG.Blueprint.NativeSporadic.J2) := ⟨fun χ => by
      have h1 := (Nat.card_congr χ.toEquiv).symm.trans hcardL
      rw [KFacts.KS14.card_nativeJ2] at h1
      omega⟩
    have hnPGL : ¬ Sec8.IsZ3PGLThreePi (lBarA c L A) := fun hP =>
      not_isLThreePi_of_mulEquiv φ not_isoLThreePi_alternating_seven
        (facts_of_isZ3PGLThreePi hD hP).1
    exact Proof1413Res2.irreducible_of_cases131 h131 hD hcL
      (Proof1514.isEmpty_mulEquiv_M12_of_A7 φ) hJ2e hnPGL


theorem mem_centralizer_of_threeElem_of_a7_m22 (h131 : Item131) {A L : Subgroup G} {c : G}
    (h : Sec15R G A c L)
    (hL : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)))
    {w : G}
    (hw : w ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
      Subgroup.normalizer (A : Set G))
    {v : ℕ} (hwv : w ^ 3 ^ v = 1) : w ∈ Subgroup.centralizer (A : Set G) := by
  have hD := h.toSec13Data
  have hcL : c ∉ L := h.hypS.2.2 c h.zpowers_mem_omegaA L h.mem_lA
  obtain ⟨-, hZ, hinn, hexp, hcomm3⟩ :=
    KFacts.KS14.ks18A7M22 (↥L ⧸ aschbacherSolvableCore 3 ↥L) hL.symm
  obtain ⟨h9, hAa, -⟩ := card_inf_irreducible_of_a7_m22 h131 h hL
  obtain ⟨f, hfA, hfL, hfc⟩ := exists_mem_inf_not_mem_of_card_nine hD.card_zpowers h9
  have hwL : w ∈ Subgroup.normalizer (L : Set G) :=
    normalizer_inf_le_of_mem hD.mem_thetaComponentsAt hD.le_normalizer hD.sectionCentralizer_eq
      hfA hfL hfc hw
  have hwA : w ∈ Subgroup.normalizer (A : Set G) := hw.2
  set σ := Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨w, hwL⟩) with hσ
  have hσ3 : σ ^ 3 ^ v = 1 := by
    have h1 : (⟨w, hwL⟩ : Subgroup.normalizer (L : Set G)) ^ 3 ^ v = 1 :=
      Subtype.ext (by simpa using hwv)
    rw [hσ, ← map_pow, ← map_pow, h1, map_one, map_one]
  obtain ⟨x, hx⟩ := hinn σ ⟨v, hσ3⟩
  have hx3 : x ^ 3 = 1 := by
    refine hexp x ⟨v, ?_⟩
    apply KFacts.KS14.conj_injective_of_center_eq_bot hZ
    rw [map_pow, ← hx, hσ3, map_one]
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) with hπ
  set E := ((A ⊓ L).subgroupOf L).map π with hE
  have hσE : ∀ y ∈ (A ⊓ L).subgroupOf L, σ (π y) = π ⟨w * y * w⁻¹,
      (Subgroup.mem_normalizer_iff.mp hwL y).mp y.2⟩ := fun y _ => rfl
  have hxE : Subgroup.zpowers x ≤ Subgroup.normalizer (E : Set _) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    obtain ⟨y, hy, rfl⟩ := hz
    have h1 : x * π y * x⁻¹ = σ (π y) := by rw [hx, MulAut.conj_apply]
    rw [h1, hσE y hy]
    refine ⟨_, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩
    have hyA : (y : G) ∈ A := (Subgroup.mem_subgroupOf.mp hy).1
    exact ⟨(Subgroup.mem_normalizer_iff.mp hwA _).mp hyA,
      (Subgroup.mem_normalizer_iff.mp hwL _).mp y.2⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx3g : IsPGroup 3 (Subgroup.zpowers x) := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hx3) with h1 | h1
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h1, pow_one])
  have hE3 : IsPGroup 3 E := by
    refine IsPGroup.map ?_ π
    intro y
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    have hyA : ((y : ↥L) : G) ∈ A := (Subgroup.mem_subgroupOf.mp y.2).1
    simpa using hD.isElemAbelian.2 _ hyA
  have hQ := IsPGroup.to_sup_of_normal_right' hx3g hE3 hxE
  have hcomm := hcomm3 _ hQ
  have hfix : ∀ y ∈ (A ⊓ L).subgroupOf L, σ (π y) = π y := by
    intro y hy
    have hyE : π y ∈ Subgroup.zpowers x ⊔ E :=
      Subgroup.mem_sup_right ⟨y, hy, rfl⟩
    have hxQ : x ∈ Subgroup.zpowers x ⊔ E := Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
    have hc := congrArg Subtype.val
      (hcomm.is_comm.comm (⟨x, hxQ⟩ : ↥(Subgroup.zpowers x ⊔ E)) ⟨π y, hyE⟩)
    simp only [Subgroup.coe_mul] at hc
    rw [hx, MulAut.conj_apply, hc, mul_inv_cancel_right]
  have hθ3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 ↥L) :=
    (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).2.2.1
  have hcentAL : A ⊓ L ≤ Subgroup.centralizer ({w} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hyL : (⟨y, hy.2⟩ : ↥L) ∈ (A ⊓ L).subgroupOf L := Subgroup.mem_subgroupOf.mpr hy
    have h1 := hfix _ hyL
    rw [hσE _ hyL, hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq] at h1
    set u : ↥L := (⟨w * y * w⁻¹, (Subgroup.mem_normalizer_iff.mp hwL y).mp hy.2⟩ : ↥L)⁻¹ *
      ⟨y, hy.2⟩ with hu
    have huθ : u ∈ aschbacherSolvableCore 3 ↥L := h1
    have huA : (u : G) ∈ A := by
      rw [hu]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact A.mul_mem (A.inv_mem ((Subgroup.mem_normalizer_iff.mp hwA y).mp hy.1)) hy.1
    have hu3 : u ^ 3 = 1 := Subtype.ext (by simpa using hD.isElemAbelian.2 _ huA)
    have hu1 : u = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hu3) with h2 | h2
      · exact orderOf_eq_one_iff.mp h2
      · have hθdvd := Subgroup.orderOf_dvd_natCard _ huθ
        rw [h2] at hθdvd
        exact absurd hθdvd hθ3
    have h2 := congrArg Subtype.val hu1
    rw [hu] at h2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] at h2
    have h3 : w * y * w⁻¹ = y := inv_mul_eq_one.mp h2
    calc y * w = (w * y * w⁻¹) * w := by rw [h3]
      _ = w * y := by group
  have hwc : w * c = c * w :=
    res1_commute_of_threeElem_normalizer (hD.isElemAbelian.2 c hD.mem_A) hwv hw.1
  have hcC : Subgroup.zpowers c ≤ Subgroup.centralizer ({w} : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
    exact hwc.symm
  have hAC : A ≤ Subgroup.centralizer ({w} : Set G) := hAa ▸ sup_le hcC hcentAL
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact Subgroup.mem_centralizer_singleton_iff.mp (hAC hy)

theorem false_of_case_four_of_a7_m22 (h131 : Item131) {A L : Subgroup G} {c : G}
    (h : Sec15R G A c L)
    (hL : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)))
    (hWH : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    {a : G} (ha : Subgroup.zpowers a ∈ omegaA A) {K : Subgroup G} (hK : K ∈ lA A a)
    (htype : Sec8.IsZ3PGLThreePi (lBarA a K A) ∨
      Nonempty (lBarA a K A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.M12) ∨
      Nonempty (lBarA a K A ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.J2)) :
    False := by
  have hDa := (sec15R_point h ha hK).toSec13Data
  have haK : a ∉ K := h.hypS.2.2 a ha K hK
  obtain ⟨-, ⟨hM12p, hM12z⟩, ⟨hJ2p, hJ2z⟩⟩ := sporadicModels131
  have hA7c : Nat.card (alternatingGroup (Fin 7)) = 2520 :=
    KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1
  obtain ⟨k, hk, ⟨v, hkv⟩, hkC⟩ : ∃ k ∈ K ⊓ Subgroup.normalizer (A : Set G),
      (∃ v : ℕ, k ^ 3 ^ v = 1) ∧ k ∉ Subgroup.centralizer (A : Set G) := by
    rcases cases131 h131 sporadicModels131 slTwoCenter hDa with ⟨-, -, hprod, htyp⟩ |
        ⟨-, -, -, ⟨e3⟩⟩ | ⟨-, -, ⟨e3⟩, -⟩ | ⟨haK', -⟩
    ·
      exfalso
      rcases htype with hP | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
      · exact Proof1514.false_of_prod_of_isZ3PGLThreePi hDa haK hprod hP
      · obtain ⟨-, -, -, ⟨ψ⟩⟩ := facts_of_prod hDa hM12p hM12z φ
        rcases htyp with ⟨hL3, -⟩ | ⟨⟨χ⟩, -⟩ | ⟨⟨χ⟩, -⟩
        · exact not_isLThreePi_of_mulEquiv ψ KFacts.KS14.not_isoLThreePi_M12 hL3
        · exact (Proof1514.isEmpty_mulEquiv_M12_of_A7 χ).false ψ
        · exact (Proof1514.isEmpty_mulEquiv_M12_of_M22 χ).false ψ
      · obtain ⟨-, -, -, ⟨ψ⟩⟩ := facts_of_prod hDa hJ2p hJ2z φ
        rcases htyp with ⟨hL3, -⟩ | ⟨⟨χ⟩, -⟩ | ⟨⟨χ⟩, -⟩
        · exact not_isLThreePi_of_mulEquiv ψ Item148PtRes2.not_isoLThreePi_J2 hL3
        · exact (Proof1413.isEmpty_mulEquiv_of_card_ne (by
            rw [hA7c, KFacts.KS14.card_nativeJ2]; norm_num)).false (χ.symm.trans ψ)
        · exact (Proof1413.isEmpty_mulEquiv_of_card_ne (by
            rw [KFacts.KS14.card_nativeM22, KFacts.KS14.card_nativeJ2]; norm_num)).false
              (χ.symm.trans ψ)
    ·
      have hcard : Nat.card (Sec4.autIn K A) = 6 := by
        rw [Nat.card_congr e3.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card,
          Fintype.card_fin]
        rfl
      obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card' (G := Sec4.autIn K A) 3
        (by rw [hcard]; norm_num)
      exact Proof1513Steps.exists_threeElem_of_autIn σ.2
        (by rw [← Subgroup.orderOf_coe] at hσ; exact hσ)
    ·
      obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card' (G := Sec4.autIn K A) 3
        (by rw [Nat.card_congr e3.toEquiv, Nat.card_congr (Multiplicative.toAdd (α := ZMod 3)),
          Nat.card_zmod])
      exact Proof1513Steps.exists_threeElem_of_autIn σ.2
        (by rw [← Subgroup.orderOf_coe] at hσ; exact hσ)
    · exact (haK haK').elim
  exact hkC (mem_centralizer_of_threeElem_of_a7_m22 h131 h hL ⟨hWH hk.2, hk.2⟩ hkv)

theorem omegaA_eq_singleton_of_a7_m22 (h131 : Item131) (h133 : Item133)
    (hset : Item13SetupAt) {A L : Subgroup G} {c : G} (h : Sec15R G A c L)
    (hL : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)))
    (hWH : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
    omegaA A = {Subgroup.zpowers c} := by
  have hD := h.toSec13Data
  have hcL : c ∉ L := h.hypS.2.2 c h.zpowers_mem_omegaA L h.mem_lA
  obtain ⟨h9, -, hirr⟩ := card_inf_irreducible_of_a7_m22 h131 h hL
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨h.zpowers_mem_omegaA, fun F hF => ?_⟩
  obtain ⟨-, -, a, rfl, -⟩ := id hF
  by_contra hac
  obtain ⟨K, hK⟩ := hset G h.toPartTwoStanding h.partTwoS_eq A h.mem_partTwoF
    h.not_mem_partTwoT a hF
  have hDa := (sec15R_point h hF hK).toSec13Data
  rcases h133 G A a K hDa h.hypS_or_hypT with hWa | ⟨-, -, -, htra, -⟩ |
      ⟨-, -, -, -, -, hΩa, -, -, -⟩ | h4 | h4 | h4
  · exact hac (Proof1510.zpowers_eq_of_le_normalizer hD hcL h9 hirr hDa.mem_A
      hDa.card_zpowers (inf_le_right.trans hWa))
  · obtain ⟨w, hw, hcw⟩ := htra _ h.zpowers_mem_omegaA
    exact hac (Proof1510.eq_of_eq_map_conj hcw (hWH hw))
  · have hc' := h.zpowers_mem_omegaA
    rw [hΩa] at hc'
    obtain ⟨w, hw, hcw⟩ := hc'
    exact hac (Proof1510.eq_of_eq_map_conj hcw (hWH hw))
  · exact false_of_case_four_of_a7_m22 h131 h hL hWH hF hK (Or.inl h4)
  · exact false_of_case_four_of_a7_m22 h131 h hL hWH hF hK (Or.inr (Or.inl h4))
  · exact false_of_case_four_of_a7_m22 h131 h hL hWH hF hK (Or.inr (Or.inr h4))

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
