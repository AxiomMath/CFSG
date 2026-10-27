module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight106Chief
import CFSG.GroupTheory.CoprimeSectionStability
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenNineSolv
import CFSG.GroupTheory.SteinbergCBFTPSolvable
import CFSG.GroupTheory.ChiefFactors.OddElement
import CFSG.GroupTheory.IsCyclicOfLeOfPRankLeOne

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenNine
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem exists_maximal_invariant_normal_of_solvable {K R : Subgroup G}
    (hRK : K ≤ normalizer (R : Set G)) (hRs : IsSolvable ↥R) (hRnt : Nontrivial ↥R) :
    ∃ N : Subgroup G, ⁅R, R⁆ ≤ N ∧ N < R ∧ K ≤ normalizer (N : Set G) ∧
      ∀ X : Subgroup G, ⁅R, R⁆ ≤ X → X < R → K ≤ normalizer (X : Set G) →
        N ≤ X → X = N := by
  haveI : Group.IsSolvable ↥R := hRs
  have hRRlt : ⁅R, R⁆ < R := CFSG.commutator_lt_self_of_isSolvable R
  have hKRR : K ≤ normalizer (⁅R, R⁆ : Subgroup G) :=
    CFSG.GroupTheory.FT63ChII.le_normalizer_commutator hRK hRK
  obtain ⟨N, -, hmax⟩ := Finite.exists_le_maximal
    (p := fun X : Subgroup G => ⁅R, R⁆ ≤ X ∧ X < R ∧ K ≤ normalizer (X : Set G))
    ⟨le_rfl, hRRlt, hKRR⟩
  obtain ⟨hN_RR, hNlt, hKN⟩ := hmax.prop
  refine ⟨N, hN_RR, hNlt, hKN, fun X hXR hXlt hKX hNX => ?_⟩
  exact (hmax.eq_of_le ⟨hXR, hXlt, hKX⟩ hNX).symm

private theorem exists_isChiefFactorUnder_of_maximal_invariant {K R N : Subgroup G}
    (hRK : K ≤ normalizer (R : Set G)) (hKN : K ≤ normalizer (N : Set G))
    (hNR : R ≤ normalizer (N : Set G)) (hNlt : N < R) (hRR : ⁅R, R⁆ ≤ N)
    (hmax : ∀ X : Subgroup G, ⁅R, R⁆ ≤ X → X < R → K ≤ normalizer (X : Set G) →
      N ≤ X → X = N) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ CFSG.ABGLocalTools.IsChiefFactorUnder ℓ K R N := by
  have hNmax : ∀ X : Subgroup G, N ≤ X → X ≤ R → K ≤ normalizer (X : Set G) →
      X = N ∨ X = R := by
    intro X hNX hXR hKX
    rcases eq_or_lt_of_le hXR with hXR' | hXRlt
    · exact Or.inr hXR'
    · exact Or.inl (hmax X (hRR.trans hNX) hXRlt hKX hNX)
  have hminH : ∀ X : Subgroup G, N ≤ X → X ≤ R → R ⊔ K ≤ normalizer (X : Set G) →
      X = N ∨ X = R :=
    fun X hNX hXR hHX => hNmax X hNX hXR (le_trans le_sup_right hHX)
  obtain ⟨ℓ, hℓp, hChiefH⟩ :=
    exists_isChiefFactorUnder_of_minimal
      hNlt le_sup_left (sup_le hNR hKN) (sup_le Subgroup.le_normalizer hRK) hminH hRR
  refine ⟨ℓ, hℓp, hNlt, hRK, hKN, hChiefH.2.2.2.1, hChiefH.2.2.2.2.1,
    hChiefH.2.2.2.2.2.1, fun X hNX hXR hKX => ?_⟩
  have hRX : R ≤ normalizer (X : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_left]
    exact (Subgroup.commutator_mono hXR le_rfl).trans (hRR.trans hNX)
  exact hChiefH.2.2.2.2.2.2 X hNX hXR (sup_le hRX hKX)

private theorem dvd_card_of_isChiefFactorUnder {K R N : Subgroup G} {ℓ : ℕ} [Fact ℓ.Prime]
    (hNlt : N < R) (hNR : R ≤ normalizer (N : Set G))
    (hChief : CFSG.ABGLocalTools.IsChiefFactorUnder ℓ K R N) :
    ℓ ∣ Nat.card R := by
  let Q := ↥R ⧸ N.subgroupOf R
  haveI hNsub : (N.subgroupOf R).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hNR
  have hNsub_top : N.subgroupOf R ≠ ⊤ := by
    intro htop
    exact (ne_of_lt hNlt) (le_antisymm hNlt.le (Subgroup.subgroupOf_eq_top.mp htop))
  have hQnt : Nontrivial Q := QuotientGroup.nontrivial_iff.mpr hNsub_top
  have hQcard : Nat.card Q ≠ 1 := by
    intro h1
    exact not_subsingleton_iff_nontrivial.mpr hQnt (Nat.card_eq_one_iff_unique.mp h1).1
  have hQp : IsPGroup ℓ Q := (hChief.isElementaryAbelian).isPGroup
  have hℓdvdQ : ℓ ∣ Nat.card Q := by
    rcases hQp.card_eq_or_dvd with h1 | h
    · exact absurd h1 hQcard
    · exact h
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf R)
  rw [h]
  exact dvd_mul_of_dvd_left hℓdvdQ _

private theorem two_lt_of_isChiefFactorUnder_of_coprime_six {K R N : Subgroup G} {ℓ : ℕ}
    [Fact ℓ.Prime] (hNlt : N < R) (hNR : R ≤ normalizer (N : Set G))
    (hChief : CFSG.ABGLocalTools.IsChiefFactorUnder ℓ K R N)
    (hR : Nat.Coprime (Nat.card R) 6) : 2 < ℓ := by
  have hℓdvdR := dvd_card_of_isChiefFactorUnder hNlt hNR hChief
  have hℓ2 : ℓ ≠ 2 := by
    intro h2
    have h2dvd : 2 ∣ Nat.card R := h2 ▸ hℓdvdR
    have hcop2 : Nat.Coprime 2 (Nat.card R) :=
      ((Nat.Coprime.of_dvd_right (by norm_num : 2 ∣ 6) hR)).symm
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hcop2 h2dvd
  exact lt_of_le_of_ne (Nat.Prime.two_le Fact.out) (Ne.symm hℓ2)

private theorem exists_mem_centralizer_not_mem_of_fixed_mod {R N D : Subgroup G}
    (hNleR : N ≤ R) (hNR : R ≤ normalizer (N : Set G))
    (hDR : D ≤ normalizer (R : Set G)) (hDN : D ≤ normalizer (N : Set G))
    (hRs : IsSolvable ↥R) (hcop : Nat.Coprime (Nat.card D) (Nat.card R))
    {w : G} (hwR : w ∈ R) (hwD : ∀ d ∈ D, ⁅d, w⁆ ∈ N) (hwN : w ∉ N) :
    ∃ c ∈ R, c ∉ N ∧ c ∈ centralizer (D : Set G) := by
  have hwSup : w ∈ (R ⊓ centralizer (D : Set G)) ⊔ N :=
    (CFSG.GroupTheory.CoprimeSection.mem_centralizer_sup_iff hNleR hNR hDR hDN
      hcop hRs hwR).mp hwD
  have hsupN : (R ⊓ centralizer (D : Set G)) ≤ normalizer (N : Set G) :=
    fun x hx => hNR hx.1
  have hwSup' : w ∈ (↑((R ⊓ centralizer (D : Set G)) ⊔ N) : Set G) := hwSup
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ N hsupN] at hwSup'
  obtain ⟨c, hc, m, hm, hcm⟩ := hwSup'
  refine ⟨c, (Subgroup.mem_inf.mp hc).1, ?_, (Subgroup.mem_inf.mp hc).2⟩
  intro hcN
  exact hwN (hcm ▸ N.mul_mem hcN hm)

private theorem commutator_le_of_chiefFactor_of_centralizer (hK462 : UCK.K462)
    {K R N D : Subgroup G} {ℓ : ℕ} [Fact ℓ.Prime] (hK : ⁅K, K⁆ = K)
    (hKk : CFSG.Open.IsKGroup ↥K) {m : ℕ} (hm4 : 4 ≤ m) (hme : Even m) (hL2 : IsL2 (Bar2 K) m)
    (hℓgt : 2 < ℓ) (hNlt : N < R) (hRK : K ≤ normalizer (R : Set G))
    (hKN : K ≤ normalizer (N : Set G)) (hNR : R ≤ normalizer (N : Set G))
    (hChief : CFSG.ABGLocalTools.IsChiefFactorUnder ℓ K R N) (hRs : IsSolvable ↥R)
    (hcopR : Nat.Coprime (Nat.card R) 3) {D : Subgroup G} (hDK : D ≤ K)
    (hD3 : Nat.card D = 3)
    (hCD : ∀ x ∈ R, (∀ d ∈ D, x * d = d * x) → x ∈ centralizer (K : Set G)) :
    ⁅R, K⁆ ≤ N := by
  classical
  by_cases hfix : ∀ w ∈ R, (∀ d ∈ D, w * d * w⁻¹ * d⁻¹ ∈ N) → w ∈ N
  · exact absurd
      (false_of_isChiefFactorUnder_of_isL2 hK462 hK hKk hm4 hme hL2 hℓgt hChief hDK hD3 hfix)
      not_false
  push Not at hfix
  obtain ⟨w, hwR, hwD, hwN⟩ := hfix
  have hwD' : ∀ d ∈ D, ⁅d, w⁆ ∈ N := fun d hd =>
    (by rw [← commutatorElement_inv]
        exact N.inv_mem (by simpa [commutatorElement_def] using hwD d hd))
  obtain ⟨c, hcR, hcN, hcC⟩ :=
    exists_mem_centralizer_not_mem_of_fixed_mod hNlt.le hNR (hDK.trans hRK) (hDK.trans hKN)
      hRs (by rw [hD3]; exact hcopR.symm) hwR hwD' hwN
  have hcK : c ∈ centralizer (K : Set G) :=
    hCD c hcR (fun d hd => (Subgroup.mem_centralizer_iff.mp hcC d hd).symm)
  by_contra hntriv
  rw [Subgroup.commutator_le] at hntriv
  push Not at hntriv
  obtain ⟨r, hrR, k, hkK, hrkN⟩ := hntriv
  have hkrN : k * r * k⁻¹ * r⁻¹ ∉ N := fun h =>
    hrkN (by simpa [commutatorElement_def, mul_assoc] using N.inv_mem h)
  exact hcN (CFSG.GroupTheory.mem_of_commutator_mem_of_chief (N := K) (K := K) le_rfl
    Subgroup.le_normalizer hNlt hRK hKN hNR
    (fun X hNX hXR hKX => hChief.2.2.2.2.2.2 X hNX hXR hKX)
    ⟨k, hkK, r, hrR, hkrN⟩ hcR (fun k' hk' => by
      have hcomm : k' * c = c * k' := Subgroup.mem_centralizer_iff.mp hcK k' hk'
      have h1 : k' * c * k'⁻¹ * c⁻¹ = 1 := by rw [hcomm]; group
      simpa [h1] using N.one_mem))

private theorem toMulAut_eq_one_of_isPerfect_of_isCyclic {K Q : Type*} [Group K] [Group Q]
    [Finite Q] [MulDistribMulAction K Q] (hK : Group.IsPerfect K) (hcyc : IsCyclic Q) :
    MulDistribMulAction.toMulAut K Q = 1 := by
  have hcomm : ∀ a b : MulAut Q, a * b = b * a := by
    intro a b
    apply (IsCyclic.mulAutMulEquiv Q).injective
    rw [map_mul, map_mul, mul_comm]
  haveI : IsMulCommutative (MulAut Q) := IsMulCommutative.of_comm hcomm
  let φ : K →* MulAut Q := MulDistribMulAction.toMulAut K Q
  have hker : (⊤ : Subgroup K) ≤ φ.ker := by
    rw [← hK.commutator_eq_top]
    exact Abelianization.commutator_subset_ker φ
  ext a x
  exact congrArg (fun f : MulAut Q => f x)
    (MonoidHom.mem_ker.mp (hker (Subgroup.mem_top a)))

private theorem commutator_le_of_cyclic_quotient_of_isPerfect {K R : Subgroup G} {Rc : Subgroup ↥R}
    [Rc.Normal] (hRK : K ≤ normalizer (R : Set G))
    (hKRc : K ≤ normalizer (Rc.map R.subtype : Set G)) (hK : ⁅K, K⁆ = K)
    (hcyc : IsCyclic (↥R ⧸ Rc)) :
    ⁅R, K⁆ ≤ Rc.map R.subtype := by
  classical
  haveI : Subgroup.Normalizes K R := ⟨hRK⟩
  letI : MulDistribMulAction ↥K ↥R :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer K R hRK
  have hRc_sub : (Rc.map R.subtype).subgroupOf R = Rc :=
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective R) Rc
  have hRcInv : CFSG.IsInvariant ↥K ↥R Rc := by
    refine ⟨fun a g => ?_⟩
    have hg : g ∈ Rc ↔ (g : G) ∈ Rc.map R.subtype := by
      simpa [hRc_sub] using Subgroup.mem_subgroupOf (H := Rc.map R.subtype) (K := R) (h := g)
    have hga : (a • g) ∈ Rc ↔ ((a • g : ↥R) : G) ∈ Rc.map R.subtype := by
      simpa [hRc_sub] using
        Subgroup.mem_subgroupOf (H := Rc.map R.subtype) (K := R) (h := a • g)
    rw [hg, hga,
      Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe (A := K) (K := R) a g]
    exact Subgroup.mem_normalizer_iff.mp (hKRc a.2) (g : G)
  haveI : MulAction.QuotientAction ↥K Rc :=
    CFSG.quotientAction_of_isInvariant (A := ↥K) (G := ↥R) Rc hRcInv
  letI : MulDistribMulAction ↥K (↥R ⧸ Rc) :=
    CFSG.quotientMulDistribMulAction (A := ↥K) (G := ↥R) Rc hRcInv
  have hφ1 := toMulAut_eq_one_of_isPerfect_of_isCyclic
    (Subgroup.isPerfect_iff.mpr hK) hcyc
  rw [Subgroup.commutator_le]; intro r hr k hk
  let a : ↥K := ⟨k, hk⟩; let g : ↥R := ⟨r, hr⟩
  have hfix : a • (QuotientGroup.mk g) = (QuotientGroup.mk g : ↥R ⧸ Rc) := by
    have h1 : MulDistribMulAction.toMulAut ↥K (↥R ⧸ Rc) a = 1 := by rw [hφ1]; rfl
    simpa using congrArg (fun f : MulAut (↥R ⧸ Rc) => f (QuotientGroup.mk g)) h1
  have hq : ((a • g : ↥R) : ↥R ⧸ Rc) = (QuotientGroup.mk g : ↥R ⧸ Rc) := by
    rw [← MulAction.Quotient.smul_mk (H := Rc) a g]
    exact hfix
  have hmem : ((a • g) / g : ↥R) ∈ Rc := QuotientGroup.eq_iff_div_mem.mp hq
  have hmemR : k * r * k⁻¹ * r⁻¹ ∈ Rc.map R.subtype := by
    refine Subgroup.mem_map.mpr ⟨(a • g) / g, hmem, ?_⟩
    change (((a • g) / g : ↥R) : G) = k * r * k⁻¹ * r⁻¹
    rw [Subgroup.coe_div,
      Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe (A := K) (K := R) a g,
      div_eq_mul_inv]
  simpa [commutatorElement_def, mul_assoc] using (Rc.map R.subtype).inv_mem hmemR

private theorem pRank_three_le_one_of_order_three_mem {R B₀ : Subgroup G}
    (hB₀ : Nat.card B₀ = 3) (hB₀R : ∀ x ∈ R, x ^ 3 = 1 → x ∈ B₀) :
    CFSG.Open.pRank 3 R ≤ 1 := by
  refine CFSG.SectionRank.pRank_le (p := 3) (k := 1) (by norm_num) ?_
  intro E hER hE
  have hEB₀ : E ≤ B₀ := fun y hy => hB₀R y (hER hy) (hE.2 y hy)
  have hdvd : Nat.card E ∣ 3 := by
    have := Subgroup.card_dvd_of_le hEB₀
    rwa [hB₀] at this
  simpa using Nat.le_of_dvd (by norm_num : 0 < 3) hdvd

private theorem minFac_eq_three_of_odd_of_dvd {n : ℕ} (hodd : Odd n) (h3 : 3 ∣ n) (hn : n ≠ 1) :
    n.minFac = 3 := by
  have hp : n.minFac.Prime := Nat.minFac_prime hn
  have hdvd : n.minFac ∣ n := Nat.minFac_dvd n
  have hle : n.minFac ≤ 3 := Nat.minFac_le_of_dvd (by norm_num) h3
  have hne2 : n.minFac ≠ 2 := fun h2 => hodd.not_two_dvd_nat (h2 ▸ hdvd)
  have h2le : 2 ≤ n.minFac := Nat.Prime.two_le hp
  omega

private theorem characteristic_complement_image_properties {R : Subgroup G} {Rc : Subgroup ↥R}
    [Rc.Normal] (hRcChar : Rc.Characteristic) (hRs : IsSolvable ↥R)
    (hRodd : Odd (Nat.card R)) (h3Rc : ¬ 3 ∣ Nat.card Rc) :
    Rc.map R.subtype ≤ R ∧ R ≤ normalizer (Rc.map R.subtype : Set G) ∧
      IsSolvable ↥(Rc.map R.subtype) ∧ Nat.Coprime (Nat.card (Rc.map R.subtype)) 6 := by
  haveI : Group.IsSolvable ↥R := hRs
  have hR₀_le_R : Rc.map R.subtype ≤ R := Subgroup.map_subtype_le Rc
  have hcard : Nat.card (Rc.map R.subtype) = Nat.card Rc :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective R)
  have hsub : (Rc.map R.subtype).subgroupOf R = Rc :=
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective R) Rc
  have hnormal : ((Rc.map R.subtype).subgroupOf R).Normal := by
    rw [hsub]; exact inferInstance
  have hR_norm : R ≤ normalizer (Rc.map R.subtype : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hR₀_le_R).mp hnormal
  have h3 : ¬ 3 ∣ Nat.card (Rc.map R.subtype) := by rw [hcard]; exact h3Rc
  have h2 : ¬ 2 ∣ Nat.card (Rc.map R.subtype) := fun h =>
    hRodd.not_two_dvd_nat (h.trans (Subgroup.card_dvd_of_le hR₀_le_R))
  have hcop : Nat.Coprime (Nat.card (Rc.map R.subtype)) 6 := by
    rw [show 6 = 2 * 3 by norm_num]
    exact Nat.Coprime.mul_right
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2).symm
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3).symm
  exact ⟨hR₀_le_R, hR_norm, Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion hR₀_le_R) (Subgroup.inclusion_injective hR₀_le_R), hcop⟩

private theorem le_centralizer_of_coprime_six_of_maximal (hK462 : UCK.K462) {K R : Subgroup G}
    (hK : ⁅K, K⁆ = K) (hKk : CFSG.Open.IsKGroup ↥K) {m : ℕ} (hm4 : 4 ≤ m) (hme : Even m)
    (hL2 : IsL2 (Bar2 K) m) (hRK : K ≤ normalizer (R : Set G)) (hRs : IsSolvable ↥R)
    (hR : Nat.Coprime (Nat.card R) 6) {D : Subgroup G} (hDK : D ≤ K)
    (hD3 : Nat.card D = 3)
    (hCD : ∀ x ∈ R, (∀ d ∈ D, x * d = d * x) → x ∈ centralizer (K : Set G))
    {N : Subgroup G} (hN_RR : ⁅R, R⁆ ≤ N) (hNlt : N < R)
    (hKN : K ≤ normalizer (N : Set G))
    (hNmax : ∀ X : Subgroup G, ⁅R, R⁆ ≤ X → X < R → K ≤ normalizer (X : Set G) →
      N ≤ X → X = N)
    (hN_le_C : N ≤ centralizer (K : Set G)) :
    R ≤ centralizer (K : Set G) := by
  have hNleR : N ≤ R := hNlt.le
  have hNR : R ≤ normalizer (N : Set G) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_left]
    exact (Subgroup.commutator_mono hNleR le_rfl).trans hN_RR
  obtain ⟨ℓ, hℓp, hChief⟩ :=
    exists_isChiefFactorUnder_of_maximal_invariant hRK hKN hNR hNlt hN_RR hNmax
  haveI : Fact ℓ.Prime := ⟨hℓp⟩
  have hℓgt : 2 < ℓ := two_lt_of_isChiefFactorUnder_of_coprime_six hNlt hNR hChief hR
  have hRK_le_N : ⁅R, K⁆ ≤ N :=
    commutator_le_of_chiefFactor_of_centralizer hK462 (D := D) hK hKk hm4 hme hL2 hℓgt
      hNlt hRK hKN hNR hChief hRs (hR.of_dvd_right (by norm_num : 3 ∣ 6)) hDK hD3 hCD
  have hNKbot : ⁅N, K⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hN_le_C
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (CFSG.GroupTheory.CoprimeSection.commutator_eq_bot_of_two_step hK hRK_le_N hNKbot)

theorem le_centralizer_of_coprime_six (hK462 : UCK.K462) {K R : Subgroup G} (hK : ⁅K, K⁆ = K)
    (hKk : CFSG.Open.IsKGroup ↥K) {m : ℕ} (hm4 : 4 ≤ m) (hme : Even m) (hL2 : IsL2 (Bar2 K) m)
    (hRK : K ≤ normalizer (R : Set G)) (hRs : IsSolvable ↥R) (hR : Nat.Coprime (Nat.card R) 6)
    {D : Subgroup G} (hDK : D ≤ K) (hD3 : Nat.card D = 3)
    (hCD : ∀ x ∈ R, (∀ d ∈ D, x * d = d * x) → x ∈ centralizer (K : Set G)) :
    R ≤ centralizer (K : Set G) := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ R : Subgroup G, Nat.card R = n → K ≤ normalizer (R : Set G) → IsSolvable ↥R →
      Nat.Coprime (Nat.card R) 6 →
      (∀ x ∈ R, (∀ d ∈ D, x * d = d * x) → x ∈ centralizer (K : Set G)) →
      R ≤ centralizer (K : Set G)
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro R hcard hRK hRs hR hCD
      by_cases hbot : R = ⊥
      · rw [hbot]; exact bot_le
      haveI hRnt : Nontrivial ↥R := (Subgroup.nontrivial_iff_ne_bot R).mpr hbot
      obtain ⟨N, hN_RR, hNlt, hKN, hNmax⟩ :=
        exists_maximal_invariant_normal_of_solvable hRK hRs hRnt
      have hNleR : N ≤ R := hNlt.le
      haveI hRsolv : Group.IsSolvable ↥R := hRs
      have hNsolv : Group.IsSolvable ↥N :=
        Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hNleR)
          (Subgroup.inclusion_injective hNleR)
      have hNcoprime : Nat.Coprime (Nat.card N) 6 :=
        Nat.Coprime.of_dvd_left (Subgroup.card_dvd_of_le hNleR) hR
      have hNlt_n : Nat.card N < n := by rw [← hcard]; exact Subgroup.card_lt_of_lt hNlt
      have hN_le_C : N ≤ centralizer (K : Set G) :=
        ih (Nat.card N) hNlt_n N rfl hKN hNsolv hNcoprime
          (fun x hx hxd => hCD x (hNleR hx) hxd)
      exact le_centralizer_of_coprime_six_of_maximal hK462 hK hKk hm4 hme hL2 hRK hRs hR
        hDK hD3 hCD hN_RR hNlt hKN hNmax hN_le_C
  exact hP (Nat.card R) R rfl hRK hRs hR hCD

private theorem le_centralizer_of_odd_of_characteristic_complement (hK462 : UCK.K462)
    {K R : Subgroup G} (hK : ⁅K, K⁆ = K) (hKk : CFSG.Open.IsKGroup ↥K)
    {m : ℕ} (hm4 : 4 ≤ m) (hme : Even m) (hL2 : IsL2 (Bar2 K) m)
    (hRK : K ≤ normalizer (R : Set G)) (hRs : IsSolvable ↥R) (hRodd : Odd (Nat.card R))
    {D : Subgroup G} (hDK : D ≤ K) (hD3 : Nat.card D = 3)
    (hCD : ∀ x ∈ R, (∀ d ∈ D, x * d = d * x) → x ∈ centralizer (K : Set G))
    {Rc : Subgroup ↥R} [Rc.Normal] (hRcChar : Rc.Characteristic)
    (h3Rc : ¬ 3 ∣ Nat.card Rc) (hcyc : IsCyclic (↥R ⧸ Rc)) :
    R ≤ centralizer (K : Set G) := by
  obtain ⟨hR₀_le_R, -, hR₀solv, hR₀coprime⟩ :=
    characteristic_complement_image_properties hRcChar hRs hRodd h3Rc
  have hK_norm_R₀ : K ≤ normalizer (Rc.map R.subtype : Set G) :=
    hRK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic Rc)
  have hR₀cent : Rc.map R.subtype ≤ centralizer (K : Set G) :=
    le_centralizer_of_coprime_six hK462 hK hKk hm4 hme hL2 hK_norm_R₀ hR₀solv hR₀coprime
      hDK hD3 (fun y hy hyd => hCD y (hR₀_le_R hy) hyd)
  have hRK_le_R₀ : ⁅R, K⁆ ≤ Rc.map R.subtype :=
    commutator_le_of_cyclic_quotient_of_isPerfect hRK hK_norm_R₀ hK hcyc
  have hR₀K : ⁅Rc.map R.subtype, K⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hR₀cent
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (CFSG.GroupTheory.CoprimeSection.commutator_eq_bot_of_two_step hK hRK_le_R₀ hR₀K)

theorem le_centralizer_of_odd (hK462 : UCK.K462) {K R : Subgroup G} (hK : ⁅K, K⁆ = K)
    (hKk : CFSG.Open.IsKGroup ↥K) {m : ℕ} (hm4 : 4 ≤ m) (hme : Even m) (hL2 : IsL2 (Bar2 K) m)
    (hRK : K ≤ normalizer (R : Set G)) (hRs : IsSolvable ↥R) (hRodd : Odd (Nat.card R))
    {B₀ : Subgroup G}
    (hB₀ : Nat.card B₀ = 3) (hB₀R : ∀ x ∈ R, x ^ 3 = 1 → x ∈ B₀)
    {D : Subgroup G} (hDK : D ≤ K) (hD3 : Nat.card D = 3)
    (hCD : ∀ x ∈ R, (∀ d ∈ D, x * d = d * x) → x ∈ centralizer (K : Set G)) :
    R ≤ centralizer (K : Set G) := by
  classical
  by_cases h3R : 3 ∣ Nat.card R
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hRne1 : Nat.card R ≠ 1 := by
      intro h1; rw [h1] at h3R; norm_num at h3R
    have hmin : (Nat.card R).minFac = 3 := minFac_eq_three_of_odd_of_dvd hRodd h3R hRne1
    obtain ⟨S⟩ := Sylow.nonempty (p := 3) (G := ↥R)
    have hRankR : CFSG.Open.pRank 3 R ≤ 1 :=
      pRank_three_le_one_of_order_three_mem hB₀ hB₀R
    have hRankTop : CFSG.Open.pRank 3 (⊤ : Subgroup ↥R) ≤ 1 := by
      rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup R]
      exact hRankR
    have hScyc : IsCyclic ↥(S : Subgroup ↥R) :=
      CFSG.isCyclic_of_le_of_pRank_le_one Nat.prime_three (by norm_num) S.isPGroup'
        le_top hRankTop
    have hNleC : normalizer ((S : Subgroup ↥R) : Set ↥R) ≤
        centralizer ((S : Subgroup ↥R) : Set ↥R) :=
      IsCyclic.normalizer_le_centralizer (G := ↥R) (p := 3) hmin hScyc
    obtain ⟨Rc, hRcNormal, h3Rc, -, -, hRcChar, -, -, -, ⟨e, -⟩, -⟩ :=
      CFSG.GroupTheory.burnside_normal_complement (p := 3) S hNleC
    letI : Rc.Normal := hRcNormal
    haveI : Rc.Characteristic := hRcChar
    have hcyc : IsCyclic (↥R ⧸ Rc) := (MulEquiv.isCyclic e).mp hScyc
    exact le_centralizer_of_odd_of_characteristic_complement hK462 hK hKk hm4 hme hL2
      hRK hRs hRodd hDK hD3 hCD hRcChar h3Rc hcyc
  · have h2R : ¬ 2 ∣ Nat.card R := hRodd.not_two_dvd_nat
    have hcop : Nat.Coprime (Nat.card R) 6 := by
      rw [show 6 = 2 * 3 by norm_num]
      exact Nat.Coprime.mul_right
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2R).symm
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3R).symm
    exact le_centralizer_of_coprime_six hK462 hK hKk hm4 hme hL2 hRK hRs hcop hDK hD3 hCD

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
