module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P2213Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22Sec7K2
public import CFSG.LocalAnalysis.UniquenessCase.UC22DataExt
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21d
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataKParam
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214c
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214d
import CFSG.LocalAnalysis.UniquenessCase.UC22P22l
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rj
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ry
import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
import CFSG.LocalAnalysis.UniquenessCase.UC22P20d
import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76 StronglyEmbeddedFive)

variable {G : Type} [Group G] [Finite G]

theorem uc22p2213e_exists_centralizesBar {K : Subgroup G} {n p : ℕ} (hL2 : IsL2 (Bar2 K) n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpn : ¬ p ∣ n) {B : Subgroup G} (hB : IsElemAbelian p B)
    (hBN : B ≤ normalizer (K : Set G)) :
    ∃ C : Subgroup G, C ≤ B ∧ (∀ c ∈ C, CentralizesBar c K) ∧ Nat.card B ≤ p * Nat.card C := by
  let φ : ↥B →* MulAut (Bar2 K) := (UC6S846.rhoL K).comp (Subgroup.inclusion hBN)
  have hinj : Function.Injective (MulAut.conj : Bar2 K →* MulAut (Bar2 K)) :=
    CFSG.mulAutConj_injective_of_center_eq_bot (uc22p22g_center_bot hL2)
  have hpow : ∀ b : ↥B, φ b ^ p = 1 := by
    intro b
    rw [← map_pow]
    have : b ^ p = 1 := Subtype.ext (by simpa using hB.2 _ b.2)
    rw [this, map_one]
  have hinn : φ.range ≤ (MulAut.conj : Bar2 K →* MulAut (Bar2 K)).range := by
    rintro _ ⟨b, rfl⟩
    exact uc22p2214_inner_of_prime_L2 hL2 hp hpn (hpow b)
  set Q : Subgroup (Bar2 K) := φ.range.comap MulAut.conj with hQ
  have hQcard : Nat.card Q = Nat.card φ.range := by
    rw [← Subgroup.map_comap_eq_self hinn, Subgroup.card_map_of_injective hinj]
  have hQel : IsElemAbelian p Q := by
    refine ⟨⟨⟨fun x y => Subtype.ext (hinj ?_)⟩⟩, fun x hx => hinj ?_⟩
    · obtain ⟨a, ha⟩ : MulAut.conj (x : Bar2 K) ∈ φ.range := x.2
      obtain ⟨b, hb⟩ : MulAut.conj (y : Bar2 K) ∈ φ.range := y.2
      have hab : a * b = b * a := by
        haveI := hB.1
        exact mul_comm' a b
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul, ← ha, ← hb, ← map_mul, hab,
        map_mul]
    · obtain ⟨a, ha⟩ : MulAut.conj x ∈ φ.range := hx
      rw [map_pow, ← ha, hpow, map_one]
  haveI := hQel.isElementaryAbelian
  have hQle : Nat.card Q ≤ p := uc22p22g_rank hp hp2 hL2 Q
  refine ⟨φ.ker.map B.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rintro _ ⟨b, hb, rfl⟩
    refine ⟨hBN b.2, fun l hl => ?_⟩
    have h1 : UC6S846.rhoL K (Subgroup.inclusion hBN b) = 1 := hb
    have h2 : UC6S846.rhoL K (Subgroup.inclusion hBN b) (QuotientGroup.mk ⟨l, hl⟩) =
        QuotientGroup.mk ⟨l, hl⟩ := by
      rw [h1, MulAut.one_apply]
    exact (UC6S846.rhoL_fix_iff K _ ⟨l, hl⟩).1 h2
  · rw [Subgroup.card_map_of_injective B.subtype_injective, ← Subgroup.card_ker_mul_card_range φ,
      mul_comm p]
    exact Nat.mul_le_mul_left _ (hQcard ▸ hQle)

theorem uc22p2213e_eq_one_of_mem_inf {M K₁ K₂ : Subgroup G} (h₁ : K₁ ∈ calC M)
    (h₂ : K₂ ∈ calC M) (hne : K₁ ≠ K₂) (hZ : center (Bar2 K₁) = ⊥) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) {x : G} (hx₁ : x ∈ K₁) (hx₂ : x ∈ K₂) (hxq : x ^ q = 1) : x = 1 := by
  have hxM : x ∈ M := uc22p22a_le_of_isSubnormal h₁.1 hx₁
  set m : ↥M := ⟨x, hxM⟩ with hm
  have hb₁ : uc22p21cPi M m ∈ barImage M K₁ := uc22p21c_mem_barImage.2 ⟨m, hx₁, rfl⟩
  have hb₂ : uc22p21cPi M m ∈ barImage M K₂ := uc22p21c_mem_barImage.2 ⟨m, hx₂, rfl⟩
  obtain ⟨e, -⟩ := uc22p22l_barImage_equiv h₁
  have hcen : e.symm ⟨_, hb₁⟩ ∈ center (Bar2 K₁) := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact Subtype.ext (uc22p22l_barImage_commute h₁ h₂ hne _ (e y).2 _ hb₂)
  rw [hZ, Subgroup.mem_bot] at hcen
  have hpi : uc22p21cPi M m = 1 := by
    have h := congrArg (fun z => ((e z : ↥(barImage M K₁)) : Bar2 M)) hcen
    simpa using h
  have hmO : m ∈ CFSG.pCore 2 ↥M := (QuotientGroup.eq_one_iff m).1 hpi
  obtain ⟨b, hb⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥M)) ⟨m, hmO⟩
  have hb' : m ^ 2 ^ b = 1 := congrArg Subtype.val hb
  have hmq : m ^ q = 1 := Subtype.ext (by simpa [hm] using hxq)
  have hcop : Nat.Coprime q (2 ^ b) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hq Nat.prime_two).2 hq2)
  have h1 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hmq) (orderOf_dvd_of_pow_eq_one hb')
  rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h1
  exact congrArg Subtype.val h1

theorem uc22p2213e_comm_mem_pCoreOf {M K₁ K₂ : Subgroup G} (h₁ : K₁ ∈ calC M)
    (h₂ : K₂ ∈ calC M) {a : G} (ha₁ : CentralizesBar a K₁) (ha₂ : CentralizesBar a K₂) {e : G}
    (he : e ∈ K₁ ⊔ K₂) : e * a * e⁻¹ * a⁻¹ ∈ pCoreOf 2 M := by
  set O : Subgroup G := pCoreOf 2 M with hO
  have hMO : M ≤ normalizer (O : Set G) :=
    Subgroup.le_normalizer.trans (UC6S846.normalizer_le_normalizer_pCoreOf M)
  let S : Subgroup G :=
    { carrier := {g | g ∈ M ∧ g * a * g⁻¹ * a⁻¹ ∈ O}
      mul_mem' := fun {g h} hg hh => ⟨M.mul_mem hg.1 hh.1, by
        have h1 := (Subgroup.mem_normalizer_iff.1 (hMO hg.1) _).1 hh.2
        have e : g * h * a * (g * h)⁻¹ * a⁻¹ =
            (g * (h * a * h⁻¹ * a⁻¹) * g⁻¹) * (g * a * g⁻¹ * a⁻¹) := by group
        rw [e]
        exact O.mul_mem h1 hg.2⟩
      one_mem' := ⟨M.one_mem, by simp⟩
      inv_mem' := fun {g} hg => ⟨M.inv_mem hg.1, by
        have h1 := (Subgroup.mem_normalizer_iff.1 (hMO (M.inv_mem hg.1)) _).1 (O.inv_mem hg.2)
        have e : g⁻¹ * a * g⁻¹⁻¹ * a⁻¹ = g⁻¹ * (g * a * g⁻¹ * a⁻¹)⁻¹ * g⁻¹⁻¹ := by group
        rw [e]
        exact h1⟩ }
  have hK : ∀ {K : Subgroup G}, K ∈ calC M → CentralizesBar a K → K ≤ S := by
    intro K hK ha k hk
    refine ⟨uc22p22a_le_of_isSubnormal hK.1 hk, ?_⟩
    have h1 := O.inv_mem (uc22p22r_pCoreOf_le_of_isSubnormal hK.1 (ha.2 k hk))
    have e : (a * k * a⁻¹ * k⁻¹)⁻¹ = k * a * k⁻¹ * a⁻¹ := by group
    rwa [e] at h1
  exact (sup_le (hK h₁ ha₁) (hK h₂ ha₂) he).2

theorem r8100E_of_conclusion76 (D : Data G) (hx : DataExt D) (hSg : UC6S846.SigmaStd D)
    (h614 : UC6.R6_14 D)
    (h76 : D.k = 2 → ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p) :
    R8100E D := by
  intro he K hK hc2 n hn hpow hL2
  by_contra h3
  have hns := UC6S846.not_solvable_of_mem_calC hK
  have h3σ : 3 ∉ D.sig := fun h => h3 (UC6S846.sp_of_mem_sig hSg hns h)
  obtain ⟨p, hp⟩ := hSg.nonempty
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have h76p := h76 ((Data.k_eq_two_iff D).2 h3) p hp (UC6S846.sp_of_mem_sig hSg hns hp)
  haveI : Fact p.Prime := ⟨hpp⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K₁, K₂, hne, hS⟩ := Set.ncard_eq_two.1 hc2
  have h1S : K₁ ∈ conjSetOf D.M K := by
    rw [hS]
    exact Set.mem_insert _ _
  have h2S : K₂ ∈ conjSetOf D.M K := by
    rw [hS]
    exact Set.mem_insert_of_mem _ rfl
  have h1C := uc22p2214_calC_of_mem_conjSetOf hK h1S
  have h2C := uc22p2214_calC_of_mem_conjSetOf hK h2S
  have hL : ∀ A ∈ conjSetOf D.M K, IsL2 (Bar2 A) n := by
    rintro A ⟨g, -, rfl⟩
    obtain ⟨e⟩ := uc22p20d_bar2_conj g K
    exact CFSG.Blueprint.LieModel.of_mulEquiv e hL2
  have hN : ∀ A ∈ conjSetOf D.M K, ∀ g ∈ D.M, Odd (orderOf g) →
      g ∈ normalizer (A : Set G) := fun A hA g hg hodd =>
    uc22p2214_mem_normalizer_of_odd (by rw [uc22p2214_conjSetOf_eq hA]; exact hc2) hg hodd
  obtain ⟨j, rfl⟩ := hpow
  have hj0 : j ≠ 0 := by
    rintro rfl
    simp at hn
  have hpn : ¬ p ∣ 2 ^ j := fun h =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 (hpp.dvd_of_dvd_pow h))
  obtain ⟨A₀, hA₀M, hA₀el, hA₀c⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank hpp (hx.four_le he p hp)
  have hA₀N : ∀ A ∈ conjSetOf D.M K, A₀ ≤ normalizer (A : Set G) := fun A hA g hg =>
    hN A hA g (hA₀M hg)
      ((hpp.odd_of_ne_two hp2).of_dvd_nat (orderOf_dvd_of_pow_eq_one (hA₀el.2 g hg)))
  obtain ⟨B₁, hB₁, hB₁c, hB₁card⟩ :=
    uc22p2213e_exists_centralizesBar (hL K₁ h1S) hpp hp2 hpn hA₀el (hA₀N K₁ h1S)
  obtain ⟨B₂, hB₂, hB₂c, hB₂card⟩ := uc22p2213e_exists_centralizesBar (hL K₂ h2S) hpp hp2 hpn
    (hA₀el.mono hB₁) (hB₁.trans (hA₀N K₂ h2S))
  have hB₂p : p ^ 2 ≤ Nat.card B₂ := by
    rw [hA₀c] at hB₁card
    have h4 : p ^ 2 * p ^ 2 ≤ p ^ 2 * Nat.card B₂ :=
      calc p ^ 2 * p ^ 2 = p ^ 4 := by ring
        _ ≤ p * Nat.card B₁ := hB₁card
        _ ≤ p * (p * Nat.card B₂) := Nat.mul_le_mul_left _ hB₂card
        _ = p ^ 2 * Nat.card B₂ := by ring
    exact Nat.le_of_mul_le_mul_left h4 (pow_pos hpp.pos 2)
  obtain ⟨A, hAB, hAel, hAc⟩ := UC6S846.exists_card_p_sq hpp (hA₀el.mono (hB₂.trans hB₁)) hB₂p
  have hAM : A ≤ D.M := hAB.trans (hB₂.trans (hB₁.trans hA₀M))
  obtain ⟨R, hR⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 D.M
  have hRp : IsPGroup 3 R := hR.isPGroup
  have hRM : R ≤ D.M := hR.le
  have hRN : ∀ A ∈ conjSetOf D.M K, R ≤ normalizer (A : Set G) := fun A hA g hg => by
    obtain ⟨k, hk⟩ := hRp ⟨g, hg⟩
    have hg3 : g ^ 3 ^ k = 1 := congrArg Subtype.val hk
    exact hN A hA g (hRM hg) ((Nat.prime_three.odd_of_ne_two (by norm_num)).pow.of_dvd_nat
      (orderOf_dvd_of_pow_eq_one hg3))
  have hRK : ∀ A ∈ conjSetOf D.M K, R ⊓ A ≠ ⊥ := by
    intro A hA hbot
    have hAM : A ≤ D.M := uc22p22a_le_of_isSubnormal (uc22p2214_calC_of_mem_conjSetOf hK hA).1
    have hRA := (hR.of_le (le_inf hRM (hRN A hA)) inf_le_left).inf_of_le_normalizer
      (le_inf hAM Subgroup.le_normalizer) inf_le_right
    have h3A : 3 ∣ Nat.card A := by
      have h3 : 3 ∣ 2 ^ (2 ^ j) - 1 := Nat.pow_sub_one_dvd_pow_sub_one 2 (dvd_pow_self 2 hj0)
      refine Dvd.dvd.trans ?_ (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥A))
      rw [uc22p22r_L2_card (hL A hA)]
      exact Dvd.dvd.mul_left (h3.trans (Nat.sub_one_dvd_pow_sub_one (2 ^ 2 ^ j) 2)) _
    have hv : 1 ≤ (Nat.card A).factorization 3 :=
      (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_three Nat.card_pos.ne').1 h3A
    have hc := hRA.card_eq
    rw [hbot, Subgroup.card_bot] at hc
    have : 3 ^ 1 ≤ 3 ^ (Nat.card A).factorization 3 := Nat.pow_le_pow_right (by norm_num) hv
    omega
  have hZ : ∀ A ∈ conjSetOf D.M K,
      ∃ a ∈ R ⊓ A, orderOf a = 3 ∧ a ∈ centralizer (R : Set G) := fun A hA =>
    CFSG.AGLEmbeddingD2.exists_orderOf_eq_mem_centralizer_of_le_normalizer Nat.prime_three hRp
      inf_le_left ((le_inf Subgroup.le_normalizer (hRN A hA)).trans
        Subgroup.inf_normalizer_le_normalizer_inf) (hRK A hA)
  obtain ⟨a₁, ha₁, ha₁o, ha₁c⟩ := hZ K₁ h1S
  obtain ⟨a₂, ha₂, ha₂o, ha₂c⟩ := hZ K₂ h2S
  have hna : a₂ ∉ zpowers a₁ := by
    intro h
    have h1 : a₂ = 1 := uc22p2213e_eq_one_of_mem_inf h1C h2C hne
      (uc22p22g_center_bot (hL K₁ h1S)) Nat.prime_three (by norm_num)
      (zpowers_le.2 (Subgroup.mem_inf.1 ha₁).2 h) (Subgroup.mem_inf.1 ha₂).2
      (by rw [← ha₂o]; exact pow_orderOf_eq_one a₂)
    rw [h1, orderOf_one] at ha₂o
    omega
  obtain ⟨hEel', hEc⟩ :=
    CFSG.ComponentClassification.UnbalancedGS.RankOneCenter.pair_isElementaryAbelian_card ha₁o
      ha₂o (Subgroup.mem_centralizer_iff.1 ha₂c a₁ (Subgroup.mem_inf.1 ha₁).1) hna
  set E : Subgroup G := zpowers a₁ ⊔ zpowers a₂ with hE
  have hEel : IsElemAbelian 3 E :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 E).1 hEel'
  have hEZ : E ≤ R ⊓ centralizer (R : Set G) :=
    sup_le (zpowers_le.2 (Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 ha₁).1, ha₁c⟩))
      (zpowers_le.2 (Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 ha₂).1, ha₂c⟩))
  have hEK : E ≤ K₁ ⊔ K₂ :=
    sup_le_sup (zpowers_le.2 (Subgroup.mem_inf.1 ha₁).2) (zpowers_le.2 (Subgroup.mem_inf.1 ha₂).2)
  have hEM : E ≤ D.M := hEZ.trans (inf_le_left.trans hRM)
  have hMO : D.M ≤ normalizer (pCoreOf 2 D.M : Set G) :=
    Subgroup.le_normalizer.trans (UC6S846.normalizer_le_normalizer_pCoreOf D.M)
  obtain ⟨A', hA'C, hA'le, ⟨eA⟩⟩ := UC6S846.exists_centralizing_copy Nat.prime_three
    (by norm_num) hpp hp2 (pCoreOf 2 D.M) A E (UC6S846.isPGroup_pCoreOf D.M) (hAM.trans hMO)
    (hEM.trans hMO) hAel.isPGroup hEel.isPGroup (fun e he a ha =>
      uc22p2213e_comm_mem_pCoreOf h1C h2C (hB₁c a (hB₂ (hAB ha))) (hB₂c a (hAB ha)) (hEK he))
  have hA'M : A' ≤ D.M := hA'le.trans (sup_le hAM (Subgroup.map_subtype_le _))
  have hA'el : IsElemAbelian p A' := UC6S846.isElemAbelian_of_mulEquiv eA hAel
  have hA'c : Nat.card A' = p ^ 2 := by rw [Nat.card_congr eA.toEquiv, hAc]
  have hΓ := h76p 3 Nat.prime_three E hEM hEel hEc
    (lt_of_lt_of_le (by norm_num) (UC6S846.le_pRank' hpp (le_inf hA'M hA'C) hA'el hA'c))
    (fun X hXE _ => lt_of_lt_of_le (by norm_num) (UC6S846.le_pRank' hpp
      (le_inf hA'M (hA'C.trans ((Subgroup.centralizer_le hXE).trans
        (Subgroup.centralizer_le_normalizer _)))) hA'el hA'c))
  exact h3 (h614 (UC6S846.sig_subset_sig1 hSg hns) 3 Nat.prime_three (by norm_num) h3σ R hR E hEZ
    hEel hEc hΓ)

open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4) in
theorem r8100E_setup4 (hSE : StronglyEmbeddedFive) (hS : Standing4 G)
    (hU : uniqueFourUnique G) (S : Setup4 G) (hσ : S.InMSigma)
    (h614 : UC6.R6_14 (UC6.dataOfSetup4 hS hU S)) : R8100E (UC6.dataOfSetup4 hS hU S) :=
  r8100E_of_conclusion76 _ (dataExt_ofSetup4 hS hU S) (UC6S846.sigmaStd_dataOfSetup4 hS hU S) h614
    (fun hk _ hp hsp => conclusion76_setup4_k_eq_two hSE hS hU S hσ hk hp hsp)

end CFSG.LocalAnalysis.UniquenessCase.UC22
