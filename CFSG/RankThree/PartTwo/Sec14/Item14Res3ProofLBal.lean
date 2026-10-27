module

public import CFSG.RankThree.PartTwo.Sec14.Item14Res2ProofLBalComp
import CFSG.GroupTheory.PCore.PrimeSetCore
import CFSG.RankThree.GroupTheory.ComponentCubeObstruction
import CFSG.RankThree.GroupTheory.CentralLineComponentAction
import CFSG.RankThree.OddKernel.ComponentRanks
import CFSG.RankThree.OddKernel.ThreeComplementQuotient
import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual
import CFSG.RankThree.PartOne.KF.LayerCover
public import CFSG.CharacterTheory.Burnside
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.RankThree.PartTwo.Sec14.Item14Res2ProofLBal

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.GH74.GLS CFSG.RankThree.LocalRank
open CFSG.Assembly.RankThreeEven (localRank)

@[expose] def KS143LBalComp2 : Prop :=
  ∀ (C : Type) [Group C] [Finite C], SectionFourHyp C →
    ∀ K : Subgroup (C ⧸ CFSG.pPrimeCore 3 C), IsComponent K →
    ∀ b : C ⧸ CFSG.pPrimeCore 3 C, b ^ 3 = 1 →
      b ∈ Subgroup.normalizer (K : Set (C ⧸ CFSG.pPrimeCore 3 C)) →
      b ∉ Subgroup.centralizer (K : Set (C ⧸ CFSG.pPrimeCore 3 C)) →
        ∀ P : Subgroup (C ⧸ CFSG.pPrimeCore 3 C),
          P ≤ Subgroup.normalizer (K : Set (C ⧸ CFSG.pPrimeCore 3 C)) →
          P ≤ Subgroup.centralizer {b} →
          Subgroup.centralizer {b} ⊓ Subgroup.normalizer (K : Set (C ⧸ CFSG.pPrimeCore 3 C)) ≤
            Subgroup.normalizer (P : Set (C ⧸ CFSG.pPrimeCore 3 C)) →
          Group.IsPerfect P → ¬ 3 ∣ Nat.card P →
          P ≤ Subgroup.centralizer (K : Set (C ⧸ CFSG.pPrimeCore 3 C))

namespace Res3LBal

open Res2LBal
open CFSG.RankThree.PartOne.EmbeddingFixedResidual
  (ne_bot_inSubgroup_perfectResidual_of_not_isSolvable isPerfect_inSubgroup_perfectResidual)

variable {X : Type} [Group X]

theorem not_isSolvable_of_isComponent {K : Subgroup X} (hK : IsComponent K) :
    ¬ Group.IsSolvable K := by
  have : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hK.1
  have : Group.IsPerfect K := hK.1.1
  exact Group.IsPerfect.not_isSolvable K

theorem exists_involution [Finite X] {K : Subgroup X} (hK : IsComponent K) :
    ∃ t ∈ K, orderOf t = 2 := by
  have h2 : 2 ∣ Nat.card K := by
    by_contra h2
    exact not_isSolvable_of_isComponent hK
      (CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h2)))
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 h2
  exact ⟨t, t.2, by rw [Subgroup.orderOf_coe, ht]⟩

theorem exists_prime_gt_three_dvd [Finite X] {K : Subgroup X} (hK : IsComponent K) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ p ∣ Nat.card K := by
  by_contra hno
  push Not at hno
  apply not_isSolvable_of_isComponent hK
  obtain ⟨a, m, hm, hcard⟩ := Nat.exists_eq_two_pow_mul_odd (n := Nat.card K) Nat.card_pos.ne'
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact Nat.not_odd_zero hm
  obtain ⟨b, r, hr3, hmr⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0 3 (by norm_num)
  have hr1 : r = 1 := by
    by_contra hr1
    obtain ⟨q, hq, hqr⟩ := Nat.exists_prime_and_dvd hr1
    have hq2 : q ≠ 2 := by
      rintro rfl
      have hr2 : 2 ∣ m := hqr.trans (hmr ▸ Dvd.intro_left _ rfl)
      exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr hr2)
    have hq3 : q ≠ 3 := by
      rintro rfl
      exact hr3 hqr
    have hq4 : 3 < q := by
      have := hq.two_le
      omega
    apply hno q hq hq4
    rw [hcard, hmr]
    exact (hqr.mul_left _).mul_left _
  have : Fintype K := Fintype.ofFinite K
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (a := a) (b := b)
    (by rw [Fintype.card_eq_nat_card, hcard, hmr, hr1, mul_one])

theorem aschbacherSolvableCore_eq_bot [Finite X] (hX : CFSG.pPrimeCore 3 X = ⊥) :
    aschbacherSolvableCore 3 X = ⊥ := by
  obtain ⟨-, -, h3, -⟩ :=
    solvable_prime_complement_core_characterization (H := X) Nat.prime_three
  have hle : aschbacherSolvableCore 3 X ≤ CFSG.pPrimeCore 3 X :=
    le_sSup ⟨inferInstance, (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3⟩
  rw [hX] at hle
  exact le_bot_iff.mp hle

theorem not_mem_centralizer_of_orderOf [Finite X] (hX : CFSG.pPrimeCore 3 X = ⊥)
    {K : Subgroup X} (hK : IsComponent K) {y : X} (hyK : y ∈ K) {p : ℕ} (hp : p.Prime)
    (hp3 : p ≠ 3) (hy : orderOf y = p) : y ∉ Subgroup.centralizer (K : Set X) := by
  intro hyc
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ := CFSG.RankThree.center_component_le_pCore Nat.prime_three
    (aschbacherSolvableCore_eq_bot hX) hK
  have hyZ : y ∈ (Subgroup.center K).map K.subtype := by
    refine ⟨⟨y, hyK⟩, ?_, rfl⟩
    show (⟨y, hyK⟩ : K) ∈ Subgroup.center K
    rw [Subgroup.mem_center_iff]
    intro k
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hyc k k.2)
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 3) (G := X)) ⟨y, hZ hyZ⟩
  have h1 : y ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h2 : p ∣ 3 ^ k := hy ▸ orderOf_dvd_of_pow_eq_one h1
  exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow h2))

theorem elemAbelian_sup_step [Finite X] {p : ℕ} (hp : p.Prime) {W : Subgroup X}
    (hWc : IsMulCommutative W) (hWp : ∀ w ∈ W, w ^ p = 1) {r : ℕ} (hWcard : Nat.card W = p ^ r)
    {K : Subgroup X} (hWK : W ≤ Subgroup.centralizer (K : Set X)) {y : X} (hyK : y ∈ K)
    (hy : orderOf y = p) (hyZ : y ∉ Subgroup.centralizer (K : Set X)) :
    IsMulCommutative (W ⊔ Subgroup.zpowers y : Subgroup X) ∧
      (∀ w ∈ W ⊔ Subgroup.zpowers y, w ^ p = 1) ∧
      Nat.card (W ⊔ Subgroup.zpowers y : Subgroup X) = p ^ (r + 1) := by
  have hyW : y ∉ W := fun h => hyZ (hWK h)
  have hdisj : W ⊓ Subgroup.zpowers y = ⊥ := by
    rw [inf_comm]
    exact CFSG.RankThree.zpowers_inf_eq_bot_of_not_mem hp hy hyW
  have hvW : y ∈ Subgroup.centralizer (W : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (Subgroup.mem_centralizer_iff.mp (hWK hw) y hyK).symm
  obtain ⟨hcard, hc, hpow⟩ := CFSG.RankThree.card_sup_zpowers_of_disjoint hvW hWc hWp hy hdisj
  exact ⟨hc, hpow, by rw [hcard, hWcard, pow_succ]⟩

theorem false_of_five_components [Finite X] (hX : CFSG.pPrimeCore 3 X = ⊥) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hloc : localRank p X ≤ 3) (K : Fin 5 → Subgroup X)
    (hK : ∀ i, IsComponent (K i)) (hinj : Function.Injective K)
    (hpK : ∀ i, p ∣ Nat.card (K i)) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have hcent : ∀ i j, i ≠ j → K i ≤ Subgroup.centralizer (K j : Set X) := fun i j hij =>
    CFSG.RankThree.OddKernel.le_centralizer_of_components (hK i) (hK j) (hinj.ne hij)
  have hy : ∀ i, ∃ y ∈ K i, orderOf y = p := fun i => by
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := K i) p (hpK i)
    exact ⟨y, y.2, by rw [Subgroup.orderOf_coe, hy]⟩
  choose y hyK hyp using hy
  have hyZ : ∀ i, y i ∉ Subgroup.centralizer (K i : Set X) := fun i =>
    not_mem_centralizer_of_orderOf hX (hK i) (hyK i) hp (by omega) (hyp i)
  have hzc : ∀ i j, i ≠ j → Subgroup.zpowers (y i) ≤ Subgroup.centralizer (K j : Set X) :=
    fun i j hij => (Subgroup.zpowers_le.mpr (hyK i)).trans (hcent i j hij)
  obtain ⟨t, htK, ht⟩ := exists_involution (hK 0)
  set W₀ : Subgroup X := ⊥ with hW₀
  set W₁ := W₀ ⊔ Subgroup.zpowers (y 1) with hW₁
  set W₂ := W₁ ⊔ Subgroup.zpowers (y 2) with hW₂
  set W₃ := W₂ ⊔ Subgroup.zpowers (y 3) with hW₃
  set W₄ := W₃ ⊔ Subgroup.zpowers (y 4) with hW₄
  have h0c : IsMulCommutative W₀ :=
    ⟨⟨fun a b => Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.mem_bot.1 a.2, Subgroup.mem_bot.1 b.2])⟩⟩
  have h0p : ∀ w ∈ W₀, w ^ p = 1 := fun w hw => by rw [Subgroup.mem_bot.1 hw, one_pow]
  have h0card : Nat.card W₀ = p ^ 0 := by rw [hW₀, Subgroup.card_bot, pow_zero]
  have hW₀K : ∀ j, W₀ ≤ Subgroup.centralizer (K j : Set X) := fun j => bot_le
  obtain ⟨h1c, h1p, h1card⟩ := elemAbelian_sup_step hp h0c h0p h0card (hW₀K 1) (hyK 1) (hyp 1)
    (hyZ 1)
  have hW₁K : ∀ j, j ≠ 1 → W₁ ≤ Subgroup.centralizer (K j : Set X) := fun j hj =>
    sup_le (hW₀K j) (hzc 1 j (Ne.symm hj))
  obtain ⟨h2c, h2p, h2card⟩ := elemAbelian_sup_step hp h1c h1p h1card (hW₁K 2 (by decide))
    (hyK 2) (hyp 2) (hyZ 2)
  have hW₂K : ∀ j, j ≠ 1 → j ≠ 2 → W₂ ≤ Subgroup.centralizer (K j : Set X) := fun j hj1 hj2 =>
    sup_le (hW₁K j hj1) (hzc 2 j (Ne.symm hj2))
  obtain ⟨h3c, h3p, h3card⟩ := elemAbelian_sup_step hp h2c h2p h2card
    (hW₂K 3 (by decide) (by decide)) (hyK 3) (hyp 3) (hyZ 3)
  have hW₃K : ∀ j, j ≠ 1 → j ≠ 2 → j ≠ 3 → W₃ ≤ Subgroup.centralizer (K j : Set X) :=
    fun j hj1 hj2 hj3 => sup_le (hW₂K j hj1 hj2) (hzc 3 j (Ne.symm hj3))
  obtain ⟨h4c, h4p, h4card⟩ := elemAbelian_sup_step hp h3c h3p h3card
    (hW₃K 4 (by decide) (by decide) (by decide)) (hyK 4) (hyp 4) (hyZ 4)
  have hW₄K : W₄ ≤ Subgroup.centralizer (K 0 : Set X) :=
    sup_le (hW₃K 0 (by decide) (by decide) (by decide)) (hzc 4 0 (by decide))
  have hW₄t : W₄ ≤ Subgroup.centralizer ({t} : Set X) :=
    hW₄K.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr htK))
  have h4 : 4 ≤ CFSG.Open.pRank p (Subgroup.centralizer ({t} : Set X)) :=
    CFSG.SectionRank.le_pRank hp.one_lt hW₄t ⟨h4c, h4p⟩ h4card
  have h5 := CFSG.RankThree.OddKernel.pRank_centralizer_le_localRank (p := p) hp.one_lt ht
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top, ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    at h5
  omega

theorem eq_top_of_index_le_four {P : Type*} [Group P] [Finite P] [Group.IsPerfect P]
    (hP3 : ¬ 3 ∣ Nat.card P) (H : Subgroup P) (hH : H.index ≤ 4) : H = ⊤ := by
  set N := H.normalCore with hN
  have hdvd1 : N.index ∣ 24 :=
    (H.index_normalCore_dvd_factorial_index).trans (Nat.factorial_dvd_factorial hH)
  have hdvd2 : N.index ∣ Nat.card P := N.index_dvd_card
  have hcop : Nat.Coprime N.index 3 :=
    Nat.Coprime.coprime_dvd_left hdvd2
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hP3).symm
  have hdvd8 : N.index ∣ 2 ^ 3 :=
    hcop.dvd_of_dvd_mul_right (show N.index ∣ 2 ^ 3 * 3 by simpa using hdvd1)
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd8
  have h2 : IsPGroup 2 (P ⧸ N) := IsPGroup.of_card (n := k) (by rw [← Subgroup.index, hk])
  have hsol : Group.IsSolvable (P ⧸ N) := by
    have := h2.isNilpotent
    infer_instance
  have hperf : Group.IsPerfect (P ⧸ N) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  have hsub : Subsingleton (P ⧸ N) := by
    by_contra hnt
    rw [not_subsingleton_iff_nontrivial] at hnt
    exact Group.IsPerfect.not_isSolvable (P ⧸ N) hsol
  have hNtop : N = ⊤ := by
    rw [← Subgroup.index_eq_one, Subgroup.index]
    exact Nat.card_eq_one_iff_unique.mpr ⟨hsub, inferInstance⟩
  exact top_le_iff.mp (hNtop ▸ H.normalCore_le)

theorem le_normalizer_component_of_perfect [Finite X] (hX : CFSG.pPrimeCore 3 X = ⊥)
    (hloc : ∀ p : ℕ, p.Prime → 3 < p → localRank p X ≤ 3) {P : Subgroup X}
    (hPp : Group.IsPerfect P) (hP3 : ¬ 3 ∣ Nat.card P) {K : Subgroup X} (hK : IsComponent K) :
    P ≤ Subgroup.normalizer (K : Set X) := by
  classical
  set H : Subgroup ↥P := (Subgroup.normalizer (K : Set X)).subgroupOf P with hH
  by_cases hidx : H.index ≤ 4
  · have hHtop := eq_top_of_index_le_four hP3 H hidx
    intro n hn
    have : (⟨n, hn⟩ : ↥P) ∈ H := hHtop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  exfalso
  push Not at hidx
  have : Fintype (↥P ⧸ H) := Fintype.ofFinite _
  have hcard : Fintype.card (Fin 5) ≤ Fintype.card (↥P ⧸ H) := by
    rw [Fintype.card_fin, Fintype.card_eq_nat_card, ← Subgroup.index]
    omega
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  set n : Fin 5 → ↥P := fun i => Quotient.out (e i) with hn
  set Kc : Fin 5 → Subgroup X := fun i => K.map (MulAut.conj ((n i : ↥P) : X)).toMonoidHom
    with hKc
  have hKcc : ∀ i, IsComponent (Kc i) := fun i => isComponent_conj hK _
  have hinj : Function.Injective Kc := by
    intro i j hij
    have hij' : K.map (MulAut.conj ((n i : ↥P) : X)).toMonoidHom =
        K.map (MulAut.conj ((n j : ↥P) : X)).toMonoidHom := hij
    have h1 := congrArg (fun L : Subgroup X =>
      L.map (MulAut.conj ((n i : ↥P) : X)⁻¹).toMonoidHom) hij'
    simp only [map_conj_map_conj, inv_mul_cancel, map_conj_one] at h1
    have hmem : ((n i)⁻¹ * n j : ↥P) ∈ H := by
      rw [hH, Subgroup.mem_subgroupOf]
      refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
      simpa using h1.symm
    have he : e i = e j := by
      rw [← Quotient.out_eq (e i), ← Quotient.out_eq (e j)]
      exact QuotientGroup.eq.mpr hmem
    exact e.injective he
  obtain ⟨p, hp, hp3, hpK⟩ := exists_prime_gt_three_dvd hK
  have hpKc : ∀ i, p ∣ Nat.card (Kc i) := fun i => by
    rw [hKc, Subgroup.card_map_of_injective (MulAut.conj _).injective]
    exact hpK
  exact false_of_five_components hX hp hp3 (hloc p hp hp3) Kc hKcc hinj hpKc

theorem le_centralizer_of_mem_centralizer [Finite X] (hX : CFSG.pPrimeCore 3 X = ⊥) {b : X}
    {K : Subgroup X} (hK : IsComponent K) (hbK : b ∈ Subgroup.centralizer (K : Set X))
    {P : Subgroup X} (hPN : Subgroup.centralizer {b} ≤ Subgroup.normalizer (P : Set X))
    (hPK : P ≤ Subgroup.normalizer (K : Set X)) (hP3 : ¬ 3 ∣ Nat.card P) :
    P ≤ Subgroup.centralizer (K : Set X) := by
  have hKb : K ≤ Subgroup.centralizer {b} := by
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hbK k hk
  have hKP : K ≤ Subgroup.normalizer (P : Set X) := hKb.trans hPN
  set R : Subgroup K := (P ⊓ K).subgroupOf K with hR
  have hRn : R.Normal := by
    refine ⟨fun r hr g => ?_⟩
    rw [hR, Subgroup.mem_subgroupOf] at hr ⊢
    obtain ⟨hrP, hrK⟩ := hr
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hKP g.2) r).mp hrP,
      K.mul_mem (K.mul_mem g.2 hrK) (K.inv_mem g.2)⟩
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hK.1 hRn with hRt | hRZ
  ·
    exfalso
    obtain ⟨y, hyK, hyZ, m, hym⟩ := exists_three_elem hX hK
    have hyR : (⟨y, hyK⟩ : K) ∈ R := hRt ▸ Subgroup.mem_top _
    rw [hR, Subgroup.mem_subgroupOf] at hyR
    have hy1 : y = 1 := eq_one_of_mem_of_pow hP3 hyR.1 hym
    rw [hy1] at hyZ
    exact hyZ (Subgroup.one_mem _)
  intro n hn
  have hnK : n ∈ Subgroup.normalizer (K : Set X) := hPK hn
  let φ : K →* K := (K.normalizerMonoidHom ⟨n, hnK⟩).toMonoidHom
  have hφ : ∀ k : K, ((φ k : K) : X) = n * k * n⁻¹ := fun k =>
    Subgroup.normalizerMonoidHom_apply_apply_coe K ⟨n, hnK⟩ k
  have hKp : Group.IsPerfect K := hK.1.1
  have hcen : ∀ k : K, k⁻¹ * φ k ∈ Subgroup.center K := by
    intro k
    apply hRZ
    rw [hR, Subgroup.mem_subgroupOf]
    refine ⟨?_, (k⁻¹ * φ k).2⟩
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hφ]
    have h1 : (k : X)⁻¹ * n * k ∈ P := by
      have h0 := (Subgroup.mem_normalizer_iff.mp (hKP (K.inv_mem k.2)) n).mp hn
      rwa [inv_inv] at h0
    have h2 : (k : X)⁻¹ * (n * k * n⁻¹) = ((k : X)⁻¹ * n * k) * n⁻¹ := by group
    rw [h2]
    exact P.mul_mem h1 (P.inv_mem hn)
  have hid := CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement
    φ hcen
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have h1 : φ ⟨k, hk⟩ = ⟨k, hk⟩ := by rw [hid]; rfl
  have h2 := congrArg Subtype.val h1
  rw [hφ] at h2
  calc k * n = n * k * n⁻¹ * n := by rw [h2]
    _ = n * k := by group

theorem le_centralizer_component2 [Finite X] (hX : CFSG.pPrimeCore 3 X = ⊥) {b : X}
    (hb3 : b ^ 3 = 1) {P : Subgroup X} (hPb : P ≤ Subgroup.centralizer {b})
    (hPN : Subgroup.centralizer {b} ≤ Subgroup.normalizer (P : Set X)) (hPp : Group.IsPerfect P)
    (hP3 : ¬ 3 ∣ Nat.card P)
    (hB : ∀ K : Subgroup X, IsComponent K → b ∈ Subgroup.normalizer (K : Set X) →
      b ∉ Subgroup.centralizer (K : Set X) →
      ∀ Q : Subgroup X, Q ≤ Subgroup.normalizer (K : Set X) → Q ≤ Subgroup.centralizer {b} →
        Subgroup.centralizer {b} ⊓ Subgroup.normalizer (K : Set X) ≤
          Subgroup.normalizer (Q : Set X) →
        Group.IsPerfect Q → ¬ 3 ∣ Nat.card Q → Q ≤ Subgroup.centralizer (K : Set X))
    {K : Subgroup X} (hK : IsComponent K) (hPK : P ≤ Subgroup.normalizer (K : Set X)) :
    P ≤ Subgroup.centralizer (K : Set X) := by
  by_cases hbK : b ∈ Subgroup.normalizer (K : Set X)
  · by_cases hbc : b ∈ Subgroup.centralizer (K : Set X)
    · exact le_centralizer_of_mem_centralizer hX hK hbc hPN hPK hP3
    · exact hB K hK hbK hbc P hPK hPb (inf_le_left.trans hPN) hPp hP3
  obtain ⟨hK1, hK2, hK12⟩ := orbit_ne hb3 hbK
  have hKic : ∀ i : ℕ, IsComponent (K.map (MulAut.conj (b ^ i)).toMonoidHom) := fun i =>
    isComponent_conj hK _
  have hmem : ∀ i : ℕ, ∀ k ∈ K, b ^ i * k * (b ^ i)⁻¹ ∈ K.map (MulAut.conj (b ^ i)).toMonoidHom :=
    fun i k hk => conj_mem_map hk _
  have hc1 : ∀ k ∈ K, ∀ k' ∈ K, Commute k' (b ^ 1 * k * (b ^ 1)⁻¹) := fun k hk k' hk' =>
    commute_of_ne hK (hKic 1) hK1 hk' (hmem 1 k hk)
  have hc2 : ∀ k ∈ K, ∀ k' ∈ K, Commute k' (b ^ 2 * k * (b ^ 2)⁻¹) := fun k hk k' hk' =>
    commute_of_ne hK (hKic 2) hK2 hk' (hmem 2 k hk)
  have hc12 : ∀ k ∈ K, ∀ k' ∈ K, Commute (b ^ 1 * k' * (b ^ 1)⁻¹) (b ^ 2 * k * (b ^ 2)⁻¹) :=
    fun k hk k' hk' => commute_of_ne (hKic 1) (hKic 2) hK12 (hmem 1 k' hk') (hmem 2 k hk)
  set d : X → X := fun k => k * (b ^ 1 * k * (b ^ 1)⁻¹) * (b ^ 2 * k * (b ^ 2)⁻¹) with hd
  have hdmul : ∀ k ∈ K, ∀ k' ∈ K, d (k * k') = d k * d k' := fun k hk k' hk' =>
    diag_mul (hc1 k hk k' hk') (hc2 k hk k' hk') (hc12 k hk k' hk')
  have hd1 : d 1 = 1 := by simp [hd]
  have hdinv : ∀ k ∈ K, d k⁻¹ = (d k)⁻¹ := by
    intro k hk
    have h := hdmul k⁻¹ (inv_mem hk) k hk
    rw [inv_mul_cancel, hd1] at h
    exact eq_inv_of_mul_eq_one_left h.symm
  have hdb : ∀ k ∈ K, d k ∈ Subgroup.centralizer {b} := fun k hk =>
    diag_mem_centralizer hb3 (hc1 k hk k hk) (hc2 k hk k hk)
  let T : Subgroup K :=
    { carrier := {k | d (k : X) ∈ P}
      mul_mem' := by
        intro x y hx hy
        change d ((x : X) * (y : X)) ∈ P
        rw [hdmul _ x.2 _ y.2]
        exact mul_mem hx hy
      one_mem' := by
        change d 1 ∈ P
        rw [hd1]
        exact one_mem P
      inv_mem' := by
        intro x hx
        change d ((x : X)⁻¹) ∈ P
        rw [hdinv _ x.2]
        exact inv_mem hx }
  have hTn : T.Normal := by
    refine ⟨fun t ht g => ?_⟩
    change d ((g : X) * (t : X) * (g : X)⁻¹) ∈ P
    rw [hdmul _ (mul_mem g.2 t.2) _ (inv_mem g.2), hdmul _ g.2 _ t.2, hdinv _ g.2]
    exact (Subgroup.mem_normalizer_iff.mp (hPN (hdb _ g.2)) _).mp ht
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hK.1 hTn with hT | hT
  ·
    exfalso
    obtain ⟨y, hyK, hyZ, m, hym⟩ := exists_three_elem hX hK
    have hyT : (⟨y, hyK⟩ : K) ∈ T := hT ▸ Subgroup.mem_top _
    have hdy : d y ∈ P := hyT
    have hdy3 : d y ^ 3 ^ ((m + m) + m) = 1 :=
      pow_mul_eq_one_of_commute ((hc2 y hyK y hyK).mul_left (hc12 y hyK y hyK))
        (pow_mul_eq_one_of_commute (hc1 y hyK y hyK) hym (conj_pow_eq_one _ hym))
        (conj_pow_eq_one _ hym)
    have hdy1 := eq_one_of_mem_of_pow hP3 hdy hdy3
    apply hyZ
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hzk : Commute ((b ^ 1 * y * (b ^ 1)⁻¹) * (b ^ 2 * y * (b ^ 2)⁻¹)) k :=
      ((hc1 y hyK k hk).symm.mul_left (hc2 y hyK k hk).symm)
    have hyeq : y = ((b ^ 1 * y * (b ^ 1)⁻¹) * (b ^ 2 * y * (b ^ 2)⁻¹))⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← mul_assoc]
      exact hdy1
    rw [hyeq]
    exact (hzk.inv_left).eq.symm
  intro n hn
  have hnb : n * b = b * n := Subgroup.mem_centralizer_singleton_iff.mp (hPb hn)
  have hnK : n ∈ Subgroup.normalizer (K : Set X) := hPK hn
  let φ : K →* K := (K.normalizerMonoidHom ⟨n, hnK⟩).toMonoidHom
  have hφ : ∀ k : K, ((φ k : K) : X) = n * k * n⁻¹ := fun k =>
    Subgroup.normalizerMonoidHom_apply_apply_coe K ⟨n, hnK⟩ k
  have hKp : Group.IsPerfect K := hK.1.1
  have hcen : ∀ k : K, k⁻¹ * φ k ∈ Subgroup.center K := by
    intro k
    have hck : (n * k * n⁻¹ * (k : X)⁻¹) ∈ K := by
      have := (φ k).2
      rw [hφ] at this
      exact mul_mem this (inv_mem k.2)
    have hcT : (⟨_, hck⟩ : K) ∈ T := by
      change d (n * k * n⁻¹ * (k : X)⁻¹) ∈ P
      have hnkn : n * (k : X) * n⁻¹ ∈ K := by
        have := (φ k).2
        rwa [hφ] at this
      have hdc : d (n * (k : X) * n⁻¹) = n * d k * n⁻¹ := diag_conj hnb k
      rw [hdmul _ hnkn _ (inv_mem k.2), hdinv _ k.2, hdc]
      exact commutator_mem hn (hPN (hdb _ k.2))
    have hcZ := hT hcT
    have heq : k⁻¹ * φ k = k⁻¹ * (⟨_, hck⟩ : K) * k := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hφ]
      group
    rw [heq]
    have := Subgroup.mem_center_iff.mp hcZ k⁻¹
    rw [this, inv_mul_cancel_right]
    exact hcZ
  have hid := CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement
    φ hcen
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have h1 : φ ⟨k, hk⟩ = ⟨k, hk⟩ := by rw [hid]; rfl
  have h2 := congrArg Subtype.val h1
  rw [hφ] at h2
  calc k * n = n * k * n⁻¹ * n := by rw [h2]
    _ = n * k := by group

theorem eq_bot_of_components2 [Finite X] (hX : CFSG.pPrimeCore 3 X = ⊥)
    (hloc : ∀ p : ℕ, p.Prime → 3 < p → localRank p X ≤ 3) {b : X} (hb3 : b ^ 3 = 1)
    (hB : ∀ K : Subgroup X, IsComponent K → b ∈ Subgroup.normalizer (K : Set X) →
      b ∉ Subgroup.centralizer (K : Set X) →
      ∀ Q : Subgroup X, Q ≤ Subgroup.normalizer (K : Set X) → Q ≤ Subgroup.centralizer {b} →
        Subgroup.centralizer {b} ⊓ Subgroup.normalizer (K : Set X) ≤
          Subgroup.normalizer (Q : Set X) →
        Group.IsPerfect Q → ¬ 3 ∣ Nat.card Q → Q ≤ Subgroup.centralizer (K : Set X))
    {P : Subgroup X} (hPb : P ≤ Subgroup.centralizer {b})
    (hPN : Subgroup.centralizer {b} ≤ Subgroup.normalizer (P : Set X)) (hPp : Group.IsPerfect P)
    (hP3 : ¬ 3 ∣ Nat.card P) : P = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine eq_bot_of_le_centralizer hPp ?_ fun K hK =>
    le_centralizer_component2 hX hb3 hPb hPN hPp hP3 hB hK
      (le_normalizer_component_of_perfect hX hloc hPp hP3 hK)
  rw [CFSG.Fitting_eq_pcore X 3 hX]
  exact le_centralizer_pCore hb3 hPb hPN hP3

theorem isSolvable_of_components2 [Finite X] (hX : CFSG.pPrimeCore 3 X = ⊥)
    (hloc : ∀ p : ℕ, p.Prime → 3 < p → localRank p X ≤ 3) {b : X} (hb3 : b ^ 3 = 1)
    (hB : ∀ K : Subgroup X, IsComponent K → b ∈ Subgroup.normalizer (K : Set X) →
      b ∉ Subgroup.centralizer (K : Set X) →
      ∀ Q : Subgroup X, Q ≤ Subgroup.normalizer (K : Set X) → Q ≤ Subgroup.centralizer {b} →
        Subgroup.centralizer {b} ⊓ Subgroup.normalizer (K : Set X) ≤
          Subgroup.normalizer (Q : Set X) →
        Group.IsPerfect Q → ¬ 3 ∣ Nat.card Q → Q ≤ Subgroup.centralizer (K : Set X)) :
    Group.IsSolvable (pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set X))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set X)) with hN
  set P := inSubgroup perfectResidual N with hP
  by_contra hsol
  apply ne_bot_inSubgroup_perfectResidual_of_not_isSolvable hsol
  have hPN' : P ≤ N := Subgroup.map_subtype_le _
  have hNC : N ≤ Subgroup.centralizer {b} := pPrimeCoreOf_le 3 _
  have hPp : Group.IsPerfect P := isPerfect_inSubgroup_perfectResidual N
  have hP3 : ¬ 3 ∣ Nat.card P := fun h3 =>
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _))
      (h3.trans (Subgroup.card_dvd_of_le hPN'))
  have hPnorm : Subgroup.centralizer {b} ≤ Subgroup.normalizer (P : Set X) := by
    intro g hg
    have hgN : N.map (MulAut.conj g).toMonoidHom = N :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (le_normalizer_pPrimeCoreOf 3 _ hg)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change P.map (MulAut.conj g).toMonoidHom = P
    rw [hP, CFSG.RankThree.PartOne.KFU.map_inSubgroup_perfectResidual, hgN]
  exact eq_bot_of_components2 hX hloc hb3 hB (hPN'.trans hNC) hPnorm hPp hP3

end Res3LBal

open Res3LBal

theorem ks143LBalSec4_of_comp2 (h : KS143LBalComp2) : KS143LBalSec4 := by
  intro C _ _ hC b hb3
  have hX : CFSG.pPrimeCore 3 (C ⧸ CFSG.pPrimeCore 3 C) = ⊥ :=
    CFSG.pPrimeCore_quotient_eq_bot Nat.prime_three
  have hloc : ∀ p : ℕ, p.Prime → 3 < p → localRank p (C ⧸ CFSG.pPrimeCore 3 C) ≤ 3 :=
    fun p hp hp3 => CFSG.RankThree.OddKernel.localRank_quotient_le_three hp hp3 _
      (Nat.lt_succ_iff.mp (hC.localRank_lt p hp hp3))
  have hb3' : (QuotientGroup.mk' (CFSG.pPrimeCore 3 C) b) ^ 3 = 1 := by
    rw [← map_pow, hb3, map_one]
  exact isSolvable_of_components2 hX hloc hb3'
    (fun K hK hbK hbc Q hQK hQb hQN hQp hQ3 => h C hC K hK _ hb3' hbK hbc Q hQK hQb hQN hQp hQ3)

theorem step143BalanceSz_of_comp2 (h : KS143LBalComp2) : Step143BalanceSz :=
  step143BalanceSz_of_sec4 (ks143LBalSec4_of_comp2 h)

end CFSG.RankThree.PartTwo.Sec14
