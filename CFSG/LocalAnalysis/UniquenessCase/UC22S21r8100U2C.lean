module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3Cent
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8100U2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SigmaRankThree13
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4Exc
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rs
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ry
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
import CFSG.LocalAnalysis.UniquenessCase.UC22P2213e
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229ZB
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3Rank
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Facts13
import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.P812Fusion
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.LocalAnalysis.StronglyEmbedded.Normalizer
import CFSG.SignalizerFunctorTheorem.McBride.Models.Suzuki.Local
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_FinalAux
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedFive
  StronglyEmbeddedFiveZ StronglyEmbeddedThree)
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (Gls3StronglyThreeEmbeddedPlus)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three (dataOfSetup)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

@[expose] def R8100U2D (D : Data G) : Prop :=
  evenRank G = 3 → ∀ (L K : Subgroup G) (n s r p : ℕ), L ∈ calC D.M → K ∈ calC D.M → K ≠ L →
    conjSetOf D.M L = {L, K} →
    ((IsL2 (Bar2 L) n ∧ (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)]) ∨
      (IsSz (Bar2 L) n ∧ (2 : ℤ) ^ (2 * n) ≡ -1 [ZMOD (p : ℤ)])) →
    Odd s → s ∣ n → r.Prime → r ∣ 2 ^ s - 1 → p ∈ D.sig → ¬ IsStronglyPEmbedded r D.M →
    (∀ c ∈ D.M, orderOf c = p → ∃ y ∈ L ⊔ K, c * y * c⁻¹ * y⁻¹ ∉ pCoreOf 2 D.M) →
    ∀ A : Subgroup G, A ≤ L → Nat.card A = r → A ∈ uniqueSet D.M

private theorem uc22r8u2_card_bar2_of_isSz {L : Subgroup G} {n : ℕ} (hSz : IsSz (Bar2 L) n) :
    Nat.card (Bar2 L) = ((2 ^ n) ^ 2 + 1) * (2 ^ n) ^ 2 * (2 ^ n - 1) := by
  obtain ⟨a, ha, rfl, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.EvenBN.GMSK.exists_mulEquiv_sz_of_lieModel_twistedB2 hSz
  rw [Nat.card_congr (e.trans (CFSG.SignalizerFunctorTheorem.McBride.SzModel.szEquiv a)).toEquiv,
    CFSG.SectionRank.card_suzukiMatrixGroup a ha]

private theorem uc22r8u2_dvd_card_of_dvd {L : Subgroup G} {n q : ℕ}
    (hLS : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) (hq : q ∣ 2 ^ n - 1) : q ∣ Nat.card L := by
  have hbar : q ∣ Nat.card (Bar2 L) := by
    rcases hLS with h | h
    · rw [uc22p22r_L2_card h]
      exact (hq.trans (Nat.sub_one_dvd_pow_sub_one (2 ^ n) 2)).mul_left _
    · rw [uc22r8u2_card_bar2_of_isSz h]
      exact hq.mul_left _
  exact hbar.trans (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥L))

private theorem uc22r8u2_dvd_card_of_cong {L : Subgroup G} {n p : ℕ}
    (hcong : (IsL2 (Bar2 L) n ∧ (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)]) ∨
      (IsSz (Bar2 L) n ∧ (2 : ℤ) ^ (2 * n) ≡ -1 [ZMOD (p : ℤ)])) : p ∣ Nat.card L := by
  have hbar : p ∣ Nat.card (Bar2 L) := by
    rcases hcong with ⟨h, hc⟩ | ⟨h, hc⟩
    · have h1 : p ∣ 2 ^ n + 1 := by
        have h2 := hc.symm.dvd
        rw [sub_neg_eq_add] at h2
        exact_mod_cast h2
      have h3 : 2 ^ n + 1 ∣ (2 ^ n) ^ 2 - 1 := by
        refine ⟨2 ^ n - 1, ?_⟩
        have h4 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
        zify [h4, Nat.one_le_pow 2 (2 ^ n) h4]
        ring
      rw [uc22p22r_L2_card h]
      exact (h1.trans h3).mul_left _
    · have h1 : p ∣ (2 ^ n) ^ 2 + 1 := by
        have h2 := hc.symm.dvd
        rw [sub_neg_eq_add, pow_mul'] at h2
        exact_mod_cast h2
      rw [uc22r8u2_card_bar2_of_isSz h]
      exact (h1.mul_right _).mul_right _
  exact hbar.trans (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥L))

private theorem uc22r8u2_card_eq {M L K : Subgroup G} (hK : K ∈ conjSetOf M L) :
    Nat.card K = Nat.card L := by
  obtain ⟨g, -, rfl⟩ := hK
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

private theorem uc22r8u2_center_bot {M L : Subgroup G} (hL : L ∈ calC M) {n : ℕ}
    (hLS : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) : center (Bar2 L) = ⊥ := by
  rcases hLS with hX | hX
  · exact uc22p22g_center_bot hX
  · haveI := CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hX
    exact uc22p21k_center_eq_bot hL.2.2

private theorem uc22r8u2_exists_comm_subgroup (M Y : Subgroup G) : ∃ S : Subgroup G,
    ∀ g, g ∈ S ↔ g ∈ M ∧ ∀ y ∈ Y, g * y * g⁻¹ * y⁻¹ ∈ pCoreOf 2 M := by
  have hMO : M ≤ normalizer (pCoreOf 2 M : Set G) :=
    Subgroup.le_normalizer.trans (UC6S846.normalizer_le_normalizer_pCoreOf M)
  refine ⟨{ carrier := {g | g ∈ M ∧ ∀ y ∈ Y, g * y * g⁻¹ * y⁻¹ ∈ pCoreOf 2 M}
            mul_mem' := fun {g h} hg hh => ⟨M.mul_mem hg.1 hh.1, fun y hy => by
              have h1 := (Subgroup.mem_normalizer_iff.1 (hMO hg.1) _).1 (hh.2 y hy)
              have e : g * h * y * (g * h)⁻¹ * y⁻¹ =
                  (g * (h * y * h⁻¹ * y⁻¹) * g⁻¹) * (g * y * g⁻¹ * y⁻¹) := by group
              rw [e]
              exact (pCoreOf 2 M).mul_mem h1 (hg.2 y hy)⟩
            one_mem' := ⟨M.one_mem, fun y _ => by simp⟩
            inv_mem' := fun {g} hg => ⟨M.inv_mem hg.1, fun y hy => by
              have h1 := (Subgroup.mem_normalizer_iff.1 (hMO (M.inv_mem hg.1)) _).1
                ((pCoreOf 2 M).inv_mem (hg.2 y hy))
              have e : g⁻¹ * y * g⁻¹⁻¹ * y⁻¹ = g⁻¹ * (g * y * g⁻¹ * y⁻¹)⁻¹ * g⁻¹⁻¹ := by group
              rw [e]
              exact h1⟩ }, fun g => Iff.rfl⟩

private theorem uc22r8u2_pCoreOf_comm {M Y : Subgroup G} (hYM : Y ≤ M) {o : G}
    (ho : o ∈ pCoreOf 2 M) {y : G} (hy : y ∈ Y) : o * y * o⁻¹ * y⁻¹ ∈ pCoreOf 2 M := by
  have hMO : M ≤ normalizer (pCoreOf 2 M : Set G) :=
    Subgroup.le_normalizer.trans (UC6S846.normalizer_le_normalizer_pCoreOf M)
  have h1 := (Subgroup.mem_normalizer_iff.1 (hMO (hYM hy)) _).1 ((pCoreOf 2 M).inv_mem ho)
  have e : o * y * o⁻¹ * y⁻¹ = o * (y * o⁻¹ * y⁻¹) := by group
  rw [e]
  exact (pCoreOf 2 M).mul_mem ho h1

private theorem uc22r8u2_eq_one_of_comm {M K : Subgroup G} (hK : K ∈ calC M)
    (hZ : center (Bar2 K) = ⊥) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {x : G} (hxK : x ∈ K)
    (hxc : ∀ y ∈ K, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 M) (hxq : x ^ q = 1) : x = 1 := by
  have hxM : x ∈ M := uc22p22a_le_of_isSubnormal hK.1 hxK
  set m : ↥M := ⟨x, hxM⟩ with hm
  have hb : uc22p21cPi M m ∈ barImage M K := uc22p21c_mem_barImage.2 ⟨m, hxK, rfl⟩
  obtain ⟨e, he⟩ := uc22p22l_barImage_equiv hK
  have hcen : e.symm ⟨_, hb⟩ ∈ center (Bar2 K) := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, he k]
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.1 (hxc k k.2)
    have hz1 : (QuotientGroup.mk z : Bar2 M) = 1 := (QuotientGroup.eq_one_iff z).2 hz
    have hzm : z = m * Subgroup.inclusion (CFSG.Quasithin.A3.subnormal_le hK.1) k * m⁻¹ *
        (Subgroup.inclusion (CFSG.Quasithin.A3.subnormal_le hK.1) k)⁻¹ :=
      Subtype.ext (by simpa [hm] using hzx)
    rw [hzm, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv, QuotientGroup.mk_inv] at hz1
    exact (mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 hz1)).symm
  rw [hZ, Subgroup.mem_bot] at hcen
  have hpi : uc22p21cPi M m = 1 := by
    have h := congrArg (fun z => ((e z : ↥(barImage M K)) : Bar2 M)) hcen
    simpa using h
  have hmO : m ∈ CFSG.pCore 2 ↥M := (QuotientGroup.eq_one_iff m).1 hpi
  obtain ⟨b, hb'⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥M)) ⟨m, hmO⟩
  have hb2 : m ^ 2 ^ b = 1 := congrArg Subtype.val hb'
  have hmq : m ^ q = 1 := Subtype.ext (by simpa [hm] using hxq)
  have hcop : Nat.Coprime q (2 ^ b) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hq Nat.prime_two).2 hq2)
  have h1 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hmq) (orderOf_dvd_of_pow_eq_one hb2)
  rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at h1
  exact congrArg Subtype.val h1

theorem uc22r8u2_pRank_le_two {D : Data G} (hSg : UC6S846.SigmaStd D)
    (h13 : PartTwo.SigmaRankThree13 D) (he : evenRank G = 3) {p : ℕ} (hp : p ∈ D.sig)
    {r : ℕ} (hr : r.Prime) (hr7 : 7 ≤ r) (hrσ : r ∉ D.sig) :
    CFSG.Open.pRank r D.M ≤ 2 := by
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have hle := CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank p hpp hp2 D.M
    D.maxLocal.1
  have h3 := hSg.three_le p hp
  by_contra h
  exact hrσ (h13 ⟨p, hp, by omega⟩ r hr hr7 (by omega))

theorem uc22r8u2_exists_B₀ {M L K : Subgroup G} (hL : L ∈ calC M) (hK : K ∈ calC M)
    (hne : K ≠ L) (hset : conjSetOf M L = {L, K}) {n p : ℕ}
    (hcong : (IsL2 (Bar2 L) n ∧ (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)]) ∨
      (IsSz (Bar2 L) n ∧ (2 : ℤ) ^ (2 * n) ≡ -1 [ZMOD (p : ℤ)])) (hp : p.Prime) (hp2 : p ≠ 2)
    {c : G} (hcM : c ∈ M) (hco : orderOf c = p)
    (hcX : ∀ y ∈ L ⊔ K, c * y * c⁻¹ * y⁻¹ ∈ pCoreOf 2 M) :
    ∃ B₀ : Subgroup G, B₀ ≤ M ∧ IsElemAbelian p B₀ ∧ Nat.card B₀ = p ^ 2 ∧
      ∀ b ∈ B₀, ∀ y ∈ L, b * y * b⁻¹ * y⁻¹ ∈ pCoreOf 2 M := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hLM : L ≤ M := uc22p22a_le_of_isSubnormal hL.1
  have hKM : K ≤ M := uc22p22a_le_of_isSubnormal hK.1
  have hMO : M ≤ normalizer (pCoreOf 2 M : Set G) :=
    Subgroup.le_normalizer.trans (UC6S846.normalizer_le_normalizer_pCoreOf M)
  have hKmem : K ∈ conjSetOf M L := by
    rw [hset]
    exact Set.mem_insert_of_mem L (Set.mem_singleton K)
  have hZK : center (Bar2 K) = ⊥ :=
    uc22r8u2_center_bot hK (uc22s21ru4e_shape_conj hKmem (hcong.imp And.left And.left))
  have hpK : p ∣ Nat.card K := by
    rw [uc22r8u2_card_eq hKmem]
    exact uc22r8u2_dvd_card_of_cong hcong
  obtain ⟨k₀, hk₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) p hpK
  have hkK : (k₀ : G) ∈ K := k₀.2
  have hko : orderOf (k₀ : G) = p := by rw [Subgroup.orderOf_coe, hk₀]
  obtain ⟨S₁, hS₁⟩ := uc22r8u2_exists_comm_subgroup M (L ⊔ K)
  obtain ⟨S₂, hS₂⟩ := uc22r8u2_exists_comm_subgroup M L
  have hcS₁ : zpowers c ⊔ pCoreOf 2 M ≤ S₁ :=
    sup_le (zpowers_le.2 ((hS₁ c).2 ⟨hcM, hcX⟩)) fun o ho =>
      (hS₁ o).2 ⟨(Subgroup.map_subtype_le _ : pCoreOf 2 M ≤ M) ho,
        fun y hy => uc22r8u2_pCoreOf_comm (sup_le hLM hKM) ho hy⟩
  have hkS₂ : (k₀ : G) ∈ S₂ :=
    (hS₂ _).2 ⟨hKM hkK, fun y hy => uc22ine229_commutator_mem_of_ne hK hL hne hkK hy⟩
  have hS₁₂ : S₁ ≤ S₂ := fun g hg =>
    (hS₂ g).2 ⟨((hS₁ g).1 hg).1, fun y hy => ((hS₁ g).1 hg).2 y (Subgroup.mem_sup_left hy)⟩
  obtain ⟨A', hA'C, hA'le, ⟨eA⟩⟩ := UC6S846.exists_centralizing_copy hp hp2 hp hp2
    (pCoreOf 2 M) (zpowers c) (zpowers (k₀ : G)) (UC6S846.isPGroup_pCoreOf M)
    (zpowers_le.2 (hMO hcM)) (zpowers_le.2 (hMO (hKM hkK)))
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hco, pow_one]))
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hko, pow_one])) fun e he a ha => by
      have h1 := ((hS₁ a).1 (hcS₁ (Subgroup.mem_sup_left ha))).2 e
        (Subgroup.mem_sup_right (zpowers_le.2 hkK he))
      have e' : (a * e * a⁻¹ * e⁻¹)⁻¹ = e * a * e⁻¹ * a⁻¹ := by group
      rw [← e']
      exact (pCoreOf 2 M).inv_mem h1
  set c' : G := ((eA.symm ⟨c, mem_zpowers c⟩ : ↥A') : G) with hc'
  have hc'A : c' ∈ A' := (eA.symm ⟨c, mem_zpowers c⟩).2
  have hc'o : orderOf c' = p := by
    rw [hc', Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hco]
  have hc'k : (k₀ : G) * c' = c' * k₀ :=
    Subgroup.mem_centralizer_iff.1 (hA'C hc'A) _ (mem_zpowers _)
  have hc'S₁ : c' ∈ S₁ := hcS₁ (hA'le hc'A)
  have hc'M : c' ∈ M := ((hS₁ c').1 hc'S₁).1
  have hc'n : c' ∉ zpowers (k₀ : G) := by
    intro h
    have h1 := uc22r8u2_eq_one_of_comm hK hZK hp hp2 (zpowers_le.2 hkK h)
      (fun y hy => ((hS₁ c').1 hc'S₁).2 y (Subgroup.mem_sup_right hy))
      (by rw [← hc'o]; exact pow_orderOf_eq_one c')
    rw [h1, orderOf_one] at hc'o
    exact hp.one_lt.ne hc'o
  obtain ⟨hB, hBc⟩ :=
    CFSG.ComponentClassification.UnbalancedGS.RankOneCenter.pair_isElementaryAbelian_card hko
      hc'o hc'k hc'n
  refine ⟨zpowers (k₀ : G) ⊔ zpowers c', sup_le (zpowers_le.2 (hKM hkK)) (zpowers_le.2 hc'M),
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).1 hB, hBc, fun b hb y hy => ?_⟩
  exact ((hS₂ b).1 (sup_le (zpowers_le.2 hkS₂) (zpowers_le.2 (hS₁₂ hc'S₁)) hb)).2 y hy

theorem uc22r8u2_exists_omega {M L K : Subgroup G} (hL : L ∈ calC M) (hK : K ∈ calC M)
    (hne : K ≠ L) (hset : conjSetOf M L = {L, K}) {n : ℕ}
    (hLS : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrn : r ∣ 2 ^ n - 1) (h2 : CFSG.Open.pRank r M ≤ 2) {A : Subgroup G} (hAL : A ≤ L)
    (hAr : Nat.card A = r) :
    ∃ R E : Subgroup G, CFSG.ABGLocalTools.IsSylowOf r R M ∧ A ≤ E ∧ E ≤ R ∧ E ≤ L ⊔ K ∧
      IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧ ∀ x ∈ R, x ^ r = 1 → x ∈ E := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hLM : L ≤ M := uc22p22a_le_of_isSubnormal hL.1
  have hKM : K ≤ M := uc22p22a_le_of_isSubnormal hK.1
  have hLmem : L ∈ conjSetOf M L := by
    rw [hset]
    exact Set.mem_insert L _
  have hKmem : K ∈ conjSetOf M L := by
    rw [hset]
    exact Set.mem_insert_of_mem L (Set.mem_singleton K)
  have hc2 : (conjSetOf M L).ncard = 2 := by
    rw [hset]
    exact Set.ncard_pair hne.symm
  have hZL : center (Bar2 L) = ⊥ := uc22r8u2_center_bot hL hLS
  have hrL : CFSG.Open.pRank r L ≤ 1 := by
    rw [← pRank_bar2_eq_of_odd (Y := L) hr hr2]
    exact pRank_le_one_of_isL2_or_isSz hLS hr hr2
  have hA1 : A ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hAr
    exact hr.one_lt.ne hAr
  have hAp : IsPGroup r A := IsPGroup.of_card (n := 1) (by rw [hAr, pow_one])
  obtain ⟨Q, hQ⟩ := (hAp.comap_of_injective M.subtype M.subtype_injective).exists_le_sylow
  set R : Subgroup G := (Q : Subgroup ↥M).map M.subtype with hRdef
  have hR : CFSG.ABGLocalTools.IsSylowOf r R M := ⟨Q, rfl⟩
  have hAR : A ≤ R := fun x hx => ⟨⟨x, hLM (hAL hx)⟩, hQ hx, rfl⟩
  have hRp : IsPGroup r R := hR.isPGroup
  have hRM : R ≤ M := hR.le
  have hRN : ∀ J ∈ conjSetOf M L, R ≤ normalizer (J : Set G) := fun J hJ g hg => by
    obtain ⟨k, hk⟩ := hRp ⟨g, hg⟩
    have hg3 : g ^ r ^ k = 1 := congrArg Subtype.val hk
    have hc2J : (conjSetOf M J).ncard = 2 := by
      rw [uc22p2214_conjSetOf_eq hJ]
      exact hc2
    exact uc22p2214_mem_normalizer_of_odd hc2J (hRM hg)
      (Odd.of_dvd_nat ((hr.odd_of_ne_two hr2).pow) (orderOf_dvd_of_pow_eq_one hg3))
  have hZR : ∀ J ∈ conjSetOf M L, R ⊓ J ≠ ⊥ →
      ∃ a ∈ R ⊓ J, orderOf a = r ∧ a ∈ centralizer (R : Set G) := fun J hJ hRJ =>
    CFSG.AGLEmbeddingD2.exists_orderOf_eq_mem_centralizer_of_le_normalizer hr hRp
      inf_le_left ((le_inf Subgroup.le_normalizer (hRN J hJ)).trans
        Subgroup.inf_normalizer_le_normalizer_inf) hRJ
  obtain ⟨z₁, hz₁, hz₁o, hz₁c⟩ :=
    hZR L hLmem fun h => hA1 (le_bot_iff.1 (h ▸ le_inf hAR hAL))
  have hAz : A ≤ zpowers z₁ := by
    intro a ha
    by_contra haz
    have ha1 : a ≠ 1 := fun h => haz (h ▸ (zpowers z₁).one_mem)
    have hdvd : orderOf a ∣ r := by
      rw [← hAr, ← Subgroup.orderOf_mk a ha]
      exact orderOf_dvd_natCard _
    have hao : orderOf a = r :=
      (hr.eq_one_or_self_of_dvd _ hdvd).resolve_left fun h => ha1 (orderOf_eq_one_iff.1 h)
    obtain ⟨hP, hPc⟩ :=
      CFSG.ComponentClassification.UnbalancedGS.RankOneCenter.pair_isElementaryAbelian_card
        hz₁o hao (Subgroup.mem_centralizer_iff.1 hz₁c a (hAR ha)).symm haz
    have h := CFSG.SectionRank.le_pRank hr.one_lt
      (sup_le (zpowers_le.2 (Subgroup.mem_inf.1 hz₁).2) (zpowers_le.2 (hAL ha)))
      ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian r _).1 hP) hPc
    omega
  have hRK : R ⊓ K ≠ ⊥ := by
    intro hbot
    have hRK' := (hR.of_le (le_inf hRM (hRN K hKmem)) inf_le_left).inf_of_le_normalizer
      (le_inf hKM Subgroup.le_normalizer) inf_le_right
    have hrK : r ∣ Nat.card K :=
      uc22r8u2_dvd_card_of_dvd (uc22s21ru4e_shape_conj hKmem hLS) hrn
    have hv : 1 ≤ (Nat.card K).factorization r :=
      (Nat.Prime.dvd_iff_one_le_factorization hr Nat.card_pos.ne').1 hrK
    have hc := hRK'.card_eq
    rw [hbot, Subgroup.card_bot] at hc
    have h1 : r ^ 1 ≤ r ^ (Nat.card K).factorization r := Nat.pow_le_pow_right hr.pos hv
    rw [pow_one] at h1
    have := hr.two_le
    omega
  obtain ⟨z₂, hz₂, hz₂o, hz₂c⟩ := hZR K hKmem hRK
  have hz₂n : z₂ ∉ zpowers z₁ := by
    intro h
    have h1 : z₂ = 1 := uc22p2213e_eq_one_of_mem_inf hL hK hne.symm hZL hr hr2
      (zpowers_le.2 (Subgroup.mem_inf.1 hz₁).2 h) (Subgroup.mem_inf.1 hz₂).2
      (by rw [← hz₂o]; exact pow_orderOf_eq_one z₂)
    rw [h1, orderOf_one] at hz₂o
    exact hr.one_lt.ne hz₂o
  obtain ⟨hEel', hEc⟩ :=
    CFSG.ComponentClassification.UnbalancedGS.RankOneCenter.pair_isElementaryAbelian_card hz₁o
      hz₂o (Subgroup.mem_centralizer_iff.1 hz₂c z₁ (Subgroup.mem_inf.1 hz₁).1) hz₂n
  set E : Subgroup G := zpowers z₁ ⊔ zpowers z₂ with hEdef
  have hEel : IsElemAbelian r E :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian r E).1 hEel'
  have hEZ : E ≤ centralizer (R : Set G) := sup_le (zpowers_le.2 hz₁c) (zpowers_le.2 hz₂c)
  have hER : E ≤ R :=
    sup_le (zpowers_le.2 (Subgroup.mem_inf.1 hz₁).1) (zpowers_le.2 (Subgroup.mem_inf.1 hz₂).1)
  refine ⟨R, E, hR, hAz.trans le_sup_left, hER,
    sup_le_sup (zpowers_le.2 (Subgroup.mem_inf.1 hz₁).2) (zpowers_le.2 (Subgroup.mem_inf.1 hz₂).2),
    hEel, hEc, fun x hx hxr => ?_⟩
  by_contra hxE
  have hx1 : x ≠ 1 := fun h => hxE (h ▸ E.one_mem)
  have h3 := CFSG.AGLEmbedding.three_le_pRank_of_isElemAbelian_sq_of_mem_centralizer hr hEel hEc
    (orderOf_eq_prime hxr hx1) hxE
    (Subgroup.mem_centralizer_iff.2 fun e he => (Subgroup.mem_centralizer_iff.1 (hEZ he) x hx).symm)
    (hER.trans hRM) (hRM hx)
  omega

theorem uc22r8u2_mem_uniqueSet_of_cent {D : Data G} (hSg : UC6S846.SigmaStd D)
    (h13 : PartTwo.SigmaRankThree13 D) (h847 : R847E3Cent D) (he : evenRank G = 3)
    {L K : Subgroup G} (hL : L ∈ calC D.M) (hK : K ∈ calC D.M) (hne : K ≠ L)
    (hset : conjSetOf D.M L = {L, K}) {n s r p : ℕ}
    (hcong : (IsL2 (Bar2 L) n ∧ (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)]) ∨
      (IsSz (Bar2 L) n ∧ (2 : ℤ) ^ (2 * n) ≡ -1 [ZMOD (p : ℤ)]))
    (hs : Odd s) (hsn : s ∣ n) (hr : r.Prime) (hrs : r ∣ 2 ^ s - 1) (hp : p ∈ D.sig)
    (hrσ : r ∉ D.sig) {c : G} (hcM : c ∈ D.M) (hco : orderOf c = p)
    (hcX : ∀ y ∈ L ⊔ K, c * y * c⁻¹ * y⁻¹ ∈ pCoreOf 2 D.M) {A : Subgroup G} (hAL : A ≤ L)
    (hAr : Nat.card A = r) : A ∈ uniqueSet D.M := by
  obtain ⟨hpP, hp2⟩ := D.sig_prime p hp
  haveI : Fact p.Prime := ⟨hpP⟩
  haveI : Fact r.Prime := ⟨hr⟩
  have hr7 : 7 ≤ r := PartTwo.s13_seven_le_of_dvd hs hr hrs
  have hr2 : r ≠ 2 := by omega
  have hrn : r ∣ 2 ^ n - 1 := hrs.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hsn)
  have h2 := uc22r8u2_pRank_le_two hSg h13 he hp hr hr7 hrσ
  have hLS : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n := hcong.imp And.left And.left
  have hKmem : K ∈ conjSetOf D.M L := by
    rw [hset]
    exact Set.mem_insert_of_mem L (Set.mem_singleton K)
  have hKS : IsL2 (Bar2 K) n ∨ IsSz (Bar2 K) n := uc22s21ru4e_shape_conj hKmem hLS
  have hthin : F08.Thin8 L := fun q hq hq2 => by
    rw [← pRank_bar2_eq_of_odd (Y := L) hq hq2]
    exact pRank_le_one_of_isL2_or_isSz hLS hq hq2
  have hMO : D.M ≤ normalizer (pCoreOf 2 D.M : Set G) :=
    Subgroup.le_normalizer.trans (UC6S846.normalizer_le_normalizer_pCoreOf D.M)
  have hNA : normalizer (A : Set G) ≤ D.M := by
    rcases h847 L hL hthin p hp (uc22r8u2_exists_B₀ hL hK hne hset hcong hpP hp2 hcM hco hcX)
        A hAL r hr hr2 hAr with h | ⟨rfl, h⟩
    · exact h
    · exfalso
      have h4 := pRank_add_pRank_add_pRank_centE_le Nat.prime_three (by norm_num) hL hK hne.symm
        (by rw [uc22r8u2_center_bot hL hLS, Subgroup.card_bot]; norm_num)
        (by rw [uc22r8u2_center_bot hK hKS, Subgroup.card_bot]; norm_num)
      have hL3 := CFSG.HardMathSupport.Timmesfeld.ComponentBalance.i112_one_le_pRank_of_dvd
        Nat.prime_three L (uc22r8u2_dvd_card_of_cong hcong)
      have hK3 := CFSG.HardMathSupport.Timmesfeld.ComponentBalance.i112_one_le_pRank_of_dvd
        Nat.prime_three K (by rw [uc22r8u2_card_eq hKmem]; exact uc22r8u2_dvd_card_of_cong hcong)
      have h3 := CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank 3 Nat.prime_three
        (by norm_num) D.M D.maxLocal.1
      omega
  obtain ⟨R, E, hR, hAE, hER, hEX, hEel, hEc, hΩ⟩ :=
    uc22r8u2_exists_omega hL hK hne hset hLS hr hr2 hrn h2 hAL hAr
  have hEM : E ≤ D.M := hER.trans hR.le
  obtain ⟨S₁, hS₁⟩ := uc22r8u2_exists_comm_subgroup D.M (L ⊔ K)
  have hcS₁ : zpowers c ≤ S₁ := zpowers_le.2 ((hS₁ c).2 ⟨hcM, hcX⟩)
  obtain ⟨A', hA'C, -, ⟨eA⟩⟩ := UC6S846.exists_centralizing_copy hr hr2 hpP hp2
    (pCoreOf 2 D.M) (zpowers c) E (UC6S846.isPGroup_pCoreOf D.M) (zpowers_le.2 (hMO hcM))
    (hEM.trans hMO) (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hco, pow_one]))
    hEel.isPGroup fun e he a ha => by
      have h1 := ((hS₁ a).1 (hcS₁ ha)).2 e (hEX he)
      have e' : (a * e * a⁻¹ * e⁻¹)⁻¹ = e * a * e⁻¹ * a⁻¹ := by group
      rw [← e']
      exact (pCoreOf 2 D.M).inv_mem h1
  have hdvd : p ∣ Nat.card (centralizer (E : Set G)) := by
    have hA'c : Nat.card A' = p := by rw [Nat.card_congr eA.toEquiv, Nat.card_zpowers, hco]
    rw [← hA'c]
    exact Subgroup.card_dvd_of_le hA'C
  have hCE : centralizer (E : Set G) ≤ D.M :=
    (Subgroup.centralizer_le hAE).trans ((Subgroup.centralizer_le_normalizer _).trans hNA)
  have hsp := UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hL) hp
  have hNE : normalizer (E : Set G) ≤ D.M := hsp.normalizer_le_of_centralizer_le hCE hdvd
  exact CFSG.LocalAnalysis.AGL81TheoremCD.Section8.mem_uniqueSet_of_normalizer_le_of_omega hR hER
    hEel hΩ hNE hAE hNA

theorem r8100U2_of_r8100U2D {D : Data G} (hSg : UC6S846.SigmaStd D)
    (h13 : PartTwo.SigmaRankThree13 D) (h847 : R847E3Cent D) (hD : R8100U2D D) :
    R8100U2 D := by
  intro he L n s r p hL hc2 hcong hs hsn hr hrs hp A hAL hAr
  obtain ⟨K, hne, hset, hK⟩ := uc22s21ru4e_exists_second_member hc2 hL
  by_cases hsp : IsStronglyPEmbedded r D.M
  · haveI : Fact r.Prime := ⟨hr⟩
    refine uc22p22r_mem_uniqueSet_of_sp D hr hsp (hAL.trans hL.1.le)
      (IsPGroup.of_card (n := 1) (by rw [hAr, pow_one])) ?_
    rintro rfl
    rw [Subgroup.card_bot] at hAr
    exact hr.one_lt.ne hAr
  have hrσ : r ∉ D.sig := fun h =>
    hsp (UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hL) h)
  by_cases hc : ∃ c ∈ D.M, orderOf c = p ∧ ∀ y ∈ L ⊔ K, c * y * c⁻¹ * y⁻¹ ∈ pCoreOf 2 D.M
  · obtain ⟨c, hcM, hco, hcX⟩ := hc
    exact uc22r8u2_mem_uniqueSet_of_cent hSg h13 h847 he hL hK hne hset hcong hs hsn hr hrs hp
      hrσ hcM hco hcX hAL hAr
  · refine hD he L K n s r p hL hK hne hset hcong hs hsn hr hrs hp hsp (fun c hcM hco => ?_) A
      hAL hAr
    by_contra h
    exact hc ⟨c, hcM, hco, fun y hy => Classical.byContradiction fun hy' => h ⟨y, hy, hy'⟩⟩

theorem r8100U2D_of_r8100U2 {D : Data G} (h : R8100U2 D) : R8100U2D D :=
  fun he L K n s r p hL _ hne hset hcong hs hsn hr hrs hp _ _ A hAL hAr =>
    h he L n s r p hL (by rw [hset]; exact Set.ncard_pair hne.symm) hcong hs hsn hr hrs hp A hAL
      hAr

theorem r8100U2_dataOfSetup_of_r8100U2D (hSE : StronglyEmbeddedFive)
    (hSEZ : StronglyEmbeddedFiveZ) (hG3 : Gls3StronglyThreeEmbeddedPlus)
    (hRee : CFSG.AGLEmbedding.KFactReeInvolution) (hK3 : StronglyEmbeddedThree)
    (hS : Standing G) (hUC : rankThreeUC G) (S : Setup G) (hD : R8100U2D (dataOfSetup hS S)) :
    R8100U2 (dataOfSetup hS S) :=
  r8100U2_of_r8100U2D (UC6S846.sigmaStd_dataOfSetup hS S)
    (PartTwo.Three.sigmaRankThree13_dataOfSetup hS hUC S)
    (r847E3Cent_dataOfSetup hSE hSEZ hG3 hRee hK3 hS S) hD

end CFSG.LocalAnalysis.UniquenessCase.UC22
