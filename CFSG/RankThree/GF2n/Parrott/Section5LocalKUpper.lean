module

public import CFSG.RankThree.GF2n.Parrott.Section5LocalT
public import CFSG.RankThree.GF2n.Parrott.Section5LocalJ
public import CFSG.RankThree.GF2n.Parrott.SylowHFacts
public import CFSG.RankThree.GF2n.Parrott.Section4EWeak
public import CFSG.RankThree.GF2n.Parrott.Section4Lemma42
public import CFSG.RankThree.GF2n.Parrott.LiftSquare
public import CFSG.RankThree.GF2n.Parrott.Cardinality
public import CFSG.Holt.PSL2Natural.Defs
public import CFSG.Holt.PermFacts
public import CFSG.Holt.ThreePoint
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalBender
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatSuzuki
public import CFSG.Quasithin.Background.E2NParamStar
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS3
public import CFSG.Quasithin.Vol2.E2TenEight
public import CFSG.RankThree.GF2n.Parrott.ZFusionControl
public import CFSG.RankThree.Holt.Basic

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

private abbrev kUpperA : Type := ↥QA45.originalSubgroup

private noncomputable def commutatorWithJ (h : Tim79a.ParrottHyp z) (j : J z) :
    J z →* Subgroup.zpowers z where
  toFun y := ⟨⁅(y : G), (j : G)⁆, commutator_mem_zpowers_z h y.2 j.2⟩
  map_one' := by
    apply Subtype.ext
    simp [commutatorElement_def]
  map_mul' y₁ y₂ := by
    apply Subtype.ext
    have hcomm : Commute (y₁ : G) ⁅(y₂ : G), (j : G)⁆ := by
      have hmem : ⁅(y₂ : G), (j : G)⁆ ∈ Subgroup.zpowers z :=
        commutator_mem_zpowers_z h y₂.2 j.2
      exact Subgroup.mem_centralizer_iff.mp (zpowers_centralizes_H h hmem) (y₁ : G)
        (J_le_H y₁.2)
    have hcommut : ⁅((y₁ * y₂ : J z) : G), (j : G)⁆ =
        ⁅(y₂ : G), (j : G)⁆ * ⁅(y₁ : G), (j : G)⁆ := by
      simpa using CFSG.GroupTheory.SuzukiTwoGroup.commutatorElement_mul_left_of_commute
        (x := (y₁ : G)) (x' := (y₂ : G)) (y := (j : G)) hcomm
    show ⁅((y₁ * y₂ : J z) : G), (j : G)⁆ =
      ⁅((y₁ : J z) : G), (j : G)⁆ * ⁅((y₂ : J z) : G), (j : G)⁆
    rw [hcommut]
    exact zpowers_commute h (commutator_mem_zpowers_z h y₂.2 j.2)
      (commutator_mem_zpowers_z h y₁.2 j.2)

private theorem ker_commutatorWithJ (h : Tim79a.ParrottHyp z) (j : J z) :
    (commutatorWithJ h j).ker =
      (J z ⊓ Subgroup.centralizer ({(j : G)} : Set G)).subgroupOf (J z) := by
  ext y
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro hy
    have hcomm : Commute (y : G) (j : G) :=
      commutatorElement_eq_one_iff_commute.mp (Subtype.ext_iff.mp hy)
    exact ⟨y.2, Subgroup.mem_centralizer_singleton_iff.mpr hcomm⟩
  · intro hy
    exact Subtype.ext (commutatorElement_eq_one_iff_commute.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp hy.2))

private theorem range_commutatorWithJ_eq_top (h : Tim79a.ParrottHyp z) (j : J z)
    (hjZ : (j : G) ∉ centerIn (J z)) : (commutatorWithJ h j).range = ⊤ := by
  classical
  haveI : Fact (Nat.card (Subgroup.zpowers z)).Prime :=
    ⟨by rw [Nat.card_zpowers, h.1]; exact Nat.prime_two⟩
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card (commutatorWithJ h j).range with hbot | htop
  · exfalso
    apply hjZ
    refine Subgroup.mem_inf.mpr ⟨j.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyker : (⟨y, hy⟩ : J z) ∈ (commutatorWithJ h j).ker := by
      rw [MonoidHom.mem_ker]
      have hmem : (commutatorWithJ h j) ⟨y, hy⟩ ∈ (commutatorWithJ h j).range :=
        ⟨⟨y, hy⟩, rfl⟩
      rw [hbot] at hmem
      simpa using hmem
    rw [ker_commutatorWithJ h j] at hyker
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_subgroupOf.mp hyker).2
  · exact htop

private theorem card_inf_centralizer_J_eq_two_pow_nine (h : Tim79a.ParrottHyp z) {j : G}
    (hj : j ∈ J z) (hjZ : j ∉ centerIn (J z)) :
    Nat.card ↥(J z ⊓ Subgroup.centralizer ({j} : Set G)) = 2 ^ 9 := by
  let jJ : J z := ⟨j, hj⟩
  have htop : (commutatorWithJ h jJ).range = ⊤ :=
    range_commutatorWithJ_eq_top h jJ (by simpa using hjZ)
  have h1 := Subgroup.card_ker_mul_card_range (commutatorWithJ h jJ)
  rw [htop, Subgroup.card_top, Nat.card_zpowers, h.1] at h1
  have hker : Nat.card (commutatorWithJ h jJ).ker =
      Nat.card ↥(J z ⊓ Subgroup.centralizer ({j} : Set G)) := by
    rw [ker_commutatorWithJ h jJ]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [hker, card_J h] at h1
  norm_num at h1 ⊢
  omega

private theorem inf_J_eq_inf_centralizer_of_isSylow (h : Tim79a.ParrottHyp z) {j : G}
    {K : Subgroup G} (hK : IsSylowOf 2 K (H z ⊓ centralizer ({j} : Set G))) :
    K ⊓ J z = J z ⊓ Subgroup.centralizer ({j} : Set G) := by
  apply le_antisymm
  · intro x hx
    exact Subgroup.mem_inf.mpr ⟨hx.2, (hK.le hx.1).2⟩
  · intro x hx
    exact Subgroup.mem_inf.mpr ⟨J_inf_centralizer_le_of_isSylowOf h hK hx, hx.1⟩

private noncomputable def imageQuotientJ {K : Subgroup G} (hK : K ≤ H z) :
    Subgroup (↥(H z) ⧸ (J z).subgroupOf (H z)) :=
  ((QuotientGroup.mk' ((J z).subgroupOf (H z))).comp (Subgroup.inclusion hK)).range

private theorem card_eq_card_inf_J_mul_card_imageQuotientJ {K : Subgroup G} (hK : K ≤ H z) :
    Nat.card K = Nat.card ↥(K ⊓ J z) * Nat.card (imageQuotientJ hK) := by
  have h1 := Subgroup.card_ker_mul_card_range
    ((QuotientGroup.mk' ((J z).subgroupOf (H z))).comp (Subgroup.inclusion hK))
  have h2 : Nat.card ((QuotientGroup.mk' ((J z).subgroupOf (H z))).comp
      (Subgroup.inclusion hK)).ker = Nat.card ↥(K ⊓ J z) := by
    have hker : ∀ x : ↥K,
        x ∈ ((QuotientGroup.mk' ((J z).subgroupOf (H z))).comp
          (Subgroup.inclusion hK)).ker ↔ (x : G) ∈ J z := by
      intro x
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      rfl
    apply Nat.card_congr
    refine Equiv.ofBijective
      (fun x => (⟨(x.1 : G), x.1.2, (hker x.1).mp x.2⟩ : ↥(K ⊓ J z))) ⟨?_, ?_⟩
    · intro a b hab
      have h3 := congrArg (fun y : ↥(K ⊓ J z) => (y : G)) hab
      exact Subtype.ext (Subtype.ext h3)
    · intro y
      refine ⟨⟨⟨(y : G), (Subgroup.mem_inf.mp y.2).1⟩,
        (hker _).mpr (Subgroup.mem_inf.mp y.2).2⟩, ?_⟩
      exact Subtype.ext rfl
  rw [h2] at h1
  exact h1.symm

private theorem isPGroup_imageQuotientJ {j : G} {K : Subgroup G}
    (hK : IsSylowOf 2 K (H z ⊓ centralizer ({j} : Set G))) :
    IsPGroup 2 (imageQuotientJ (hK.le.trans inf_le_left)) := by
  have hle : K ≤ H z := hK.le.trans inf_le_left
  exact hK.isPGroup.of_surjective
    (((QuotientGroup.mk' ((J z).subgroupOf (H z))).comp
      (Subgroup.inclusion hle)).rangeRestrict) (MonoidHom.rangeRestrict_surjective _)

private theorem card_imageQuotientJ_le_two_pow_seven (h : Tim79a.ParrottHyp z) {j : G}
    {K : Subgroup G} (hK : IsSylowOf 2 K (H z ⊓ centralizer ({j} : Set G))) :
    Nat.card (imageQuotientJ (hK.le.trans inf_le_left)) ≤ 2 ^ 7 := by
  have hle : K ≤ H z := hK.le.trans inf_le_left
  obtain ⟨m, hm⟩ := IsPGroup.exists_card_eq (isPGroup_imageQuotientJ hK)
  have hdvd : Nat.card (imageQuotientJ hle) ∣ 51840 := by
    rw [← card_quotient_J h]
    exact Subgroup.card_subgroup_dvd_card _
  rw [hm, show (51840 : ℕ) = 2 ^ 7 * 405 by norm_num] at hdvd
  have hcop : Nat.Coprime (2 ^ m) 405 :=
    Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr (by norm_num : Odd 405))
  have hdvd' : 2 ^ m ∣ 2 ^ 7 := hcop.dvd_of_dvd_mul_right hdvd
  have hm7 : m ≤ 7 := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp hdvd'
  rw [hm]
  exact Nat.pow_le_pow_right (by norm_num : 0 < 2) hm7

theorem card_isSylowOf_centralizer_le (h : Tim79a.ParrottHyp z) {j : G} (hj : j ∈ J z)
    (hjZ : j ∉ centerIn (J z)) {K : Subgroup G}
    (hK : IsSylowOf 2 K (H z ⊓ centralizer ({j} : Set G))) :
    Nat.card K ≤ 2 ^ 16 := by
  have hKleH : K ≤ H z := hK.le.trans inf_le_left
  have hform := card_eq_card_inf_J_mul_card_imageQuotientJ hKleH
  rw [inf_J_eq_inf_centralizer_of_isSylow h hK,
    card_inf_centralizer_J_eq_two_pow_nine h hj hjZ] at hform
  rw [hform]
  calc 2 ^ 9 * Nat.card (imageQuotientJ hKleH) ≤ 2 ^ 9 * 2 ^ 7 :=
        Nat.mul_le_mul_left _ (card_imageQuotientJ_le_two_pow_seven h hK)
    _ = 2 ^ 16 := by rw [← pow_add]

private theorem orderOf_tA :
    orderOf (⟨t, t_mem_A⟩ : ↥QA45.originalSubgroup) = 2 := by
  refine orderOf_eq_prime ?_ ?_
  · rw [pow_two]
    exact Subtype.ext t_sq
  · intro h
    exact t_ne_one (by simpa using congrArg Subtype.val h)

private theorem seven_le_fixDimV_of_mem_centerIn (h : Tim79a.ParrottHyp z) {j : G}
    (hj : j ∈ J z) (hjZ : j ∉ centerIn (J z)) {K : Subgroup G}
    (hK : IsSylowOf 2 K (H z ⊓ centralizer ({j} : Set G))) {k : G} (hkK : k ∈ K)
    (hkC : k ∈ Subgroup.centralizer (K : Set G)) :
    7 ≤ fixDimV h ⟨k, (hK.le hkK).1⟩ := by
  let CJ : Subgroup G := J z ⊓ Subgroup.centralizer ({j} : Set G)
  have hKleH : K ≤ H z := hK.le.trans inf_le_left
  have hCJleJ : CJ ≤ J z := inf_le_left
  have hCJleK : CJ ≤ K := J_inf_centralizer_le_of_isSylowOf h hK
  have hCJcard : Nat.card CJ = 2 ^ 9 := card_inf_centralizer_J_eq_two_pow_nine h hj hjZ
  have hZleCJ : centerIn (J z) ≤ CJ := by
    intro x hx
    exact Subgroup.mem_inf.mpr ⟨hx.1,
      Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hx.2 j hj).symm⟩
  have hinfZ : CJ ⊓ centerIn (J z) = centerIn (J z) := inf_eq_right.mpr hZleCJ
  have h1 := card_eq_card_inf_centerIn_mul_card_imageInV (z := z) hCJleJ
  rw [hinfZ, card_centerIn_J h, hCJcard] at h1
  have himg : Nat.card (imageInV (z := z) hCJleJ) = 2 ^ 7 := by
    have h2 : (4 : ℕ) * Nat.card (imageInV (z := z) hCJleJ) = 4 * 2 ^ 7 := by
      rw [← h1]
      norm_num
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h2
  have hleF : imageInV (z := z) hCJleJ ≤
      autFixedSubgroup (conjV h ⟨k, (hK.le hkK).1⟩) := by
    intro v hv
    obtain ⟨y, hyCJ, rfl⟩ := (mem_imageInV_iff hCJleJ v).mp hv
    exact pi_mem_autFixedSubgroup_conjV h (Subgroup.mem_inf.mp hyCJ).1
      (Subgroup.mem_centralizer_iff.mp hkC y (hCJleK hyCJ)).symm
  have hcardF : 2 ^ 7 ≤ Nat.card (autFixedSubgroup (conjV h ⟨k, (hK.le hkK).1⟩)) := by
    rw [← himg]
    exact Subgroup.card_le_of_le hleF
  rw [card_fix h ⟨k, (hK.le hkK).1⟩] at hcardF
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hcardF

private theorem card_imageQA45_eq_two_pow_seven (h : Tim79a.ParrottHyp z) {j : G}
    (hj : j ∈ J z) (hjZ : j ∉ centerIn (J z)) {K : Subgroup G}
    (hK : IsSylowOf 2 K (H z ⊓ centralizer ({j} : Set G)))
    (hcard : Nat.card K = 2 ^ 16) :
    Nat.card (imageQA45 (z := z) D (hK.le.trans inf_le_left)) = 2 ^ 7 := by
  have hKleH : K ≤ H z := hK.le.trans inf_le_left
  have hform := card_eq_card_inf_J_mul_card_imageQA45 D hKleH
  rw [inf_J_eq_inf_centralizer_of_isSylow h hK,
    card_inf_centralizer_J_eq_two_pow_nine h hj hjZ, hcard] at hform
  rw [show (2 : ℕ) ^ 16 = 2 ^ 9 * 2 ^ 7 by rw [← pow_add]] at hform
  exact (Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2 ^ 9) hform).symm

private theorem zmod2_eq_one_of_ne_zero {x : ZMod 2} (hx : x ≠ 0) : x = 1 :=
  (by decide : ∀ y : ZMod 2, y ≠ 0 → y = 1) x hx

private theorem polarVZMod_eq_one_or_eq_of_forall_orthogonal (h : Tim79a.ParrottHyp z)
    {u v : QuotientV.V z}
    (huv : ∀ w, polarVZMod h u w = 0 → polarVZMod h v w = 0) :
    v = 1 ∨ v = u := by
  by_cases hv : ∀ w, polarVZMod h v w = 0
  · exact Or.inl (polarVZMod_nondegenerate h v hv)
  · right
    push Not at hv
    obtain ⟨w₀, hw₀⟩ := hv
    have hu0 : polarVZMod h u w₀ = 1 :=
      zmod2_eq_one_of_ne_zero (fun h0 => hw₀ (huv w₀ h0))
    have hvw0 : polarVZMod h v w₀ = 1 := zmod2_eq_one_of_ne_zero hw₀
    have hfun : ∀ w, polarVZMod h v w = polarVZMod h u w := by
      intro w
      by_cases huw : polarVZMod h u w = 0
      · rw [huw]
        exact huv w huw
      · have huw1 : polarVZMod h u w = 1 := zmod2_eq_one_of_ne_zero huw
        have huw0 : polarVZMod h u (w * w₀) = 0 := by
          rw [polarVZMod_add_right, huw1, hu0]
          decide
        have hv0 : polarVZMod h v (w * w₀) = 0 := huv _ huw0
        rw [polarVZMod_add_right, hvw0] at hv0
        rw [huw1]
        exact (by decide : ∀ x : ZMod 2, x + 1 = 0 → x = 1) _ hv0
    have hvu : v * u = 1 := by
      refine polarVZMod_nondegenerate h (v * u) ?_
      intro w
      rw [polarVZMod_add h v u w, hfun w]
      exact (by decide : ∀ x : ZMod 2, x + x = 0) _
    have hu2 : u * u = 1 := by
      simpa [pow_two] using QuotientV.pow_two_eq_one_V h u
    calc v = v * 1 := (mul_one v).symm
      _ = v * (u * u) := by rw [hu2]
      _ = (v * u) * u := by rw [mul_assoc]
      _ = 1 * u := by rw [hvu]
      _ = u := one_mul u

private theorem exists_mem_conj_sylowTwoQA45 (h : Tim79a.ParrottHyp z) {j : G} (hj : j ∈ J z)
    (hjZ : j ∉ centerIn (J z)) {K : Subgroup G}
    (hK : IsSylowOf 2 K (H z ⊓ centralizer ({j} : Set G)))
    (hcard : Nat.card K = 2 ^ 16) :
    ∃ a : kUpperA, ∀ x : kUpperA, x ∈ sylowTwoQA45 ↔
      a⁻¹ * x * a ∈ imageQA45 (z := z) D (hK.le.trans inf_le_left) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let qK : Subgroup kUpperA := imageQA45 (z := z) D (hK.le.trans inf_le_left)
  have hKleH : K ≤ H z := hK.le.trans inf_le_left
  have hqKcard : Nat.card qK = 2 ^ 7 :=
    card_imageQA45_eq_two_pow_seven (z := z) D h hj hjZ hK hcard
  have hqKp : IsPGroup 2 qK := isPGroup_imageQA45 D hKleH hK.isPGroup
  have hqKindex : qK.index = 3 ^ 4 * 5 := by
    rw [Subgroup.index_eq_card_div]
    change Nat.card kUpperA / Nat.card qK = 3 ^ 4 * 5
    rw [card_QA45, hqKcard]
    norm_num
  have hqKnotdvd : ¬ 2 ∣ qK.index := by
    rw [hqKindex]
    norm_num
  let Q : Sylow 2 kUpperA := hqKp.toSylow hqKnotdvd
  have hQcoe : (Q : Subgroup kUpperA) = qK := hqKp.toSylow_coe hqKnotdvd
  have hTnotdvd : ¬ 2 ∣ sylowTwoQA45.index := by
    rw [index_sylowTwoQA45]
    norm_num
  let T : Sylow 2 kUpperA := isPGroup_sylowTwoQA45.toSylow hTnotdvd
  have hTcoe : (T : Subgroup kUpperA) = sylowTwoQA45 :=
    isPGroup_sylowTwoQA45.toSylow_coe hTnotdvd
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq kUpperA Q T
  refine ⟨a, fun x => ?_⟩
  have h1 : x ∈ (T : Subgroup kUpperA) ↔ a⁻¹ * x * a ∈ (Q : Subgroup kUpperA) := by
    rw [← ha]
    change x ∈ MulAut.conj a • (Q : Subgroup kUpperA) ↔ _
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply]
  rwa [hTcoe, hQcoe] at h1

private theorem conj_mem_center_sylowTwoQA45_of_mem_centerIn (h : Tim79a.ParrottHyp z) {j : G}
    (hj : j ∈ J z) (hjZ : j ∉ centerIn (J z)) {K : Subgroup G}
    (hK : IsSylowOf 2 K (H z ⊓ centralizer ({j} : Set G)))
    (hcard : Nat.card K = 2 ^ 16) {k : G} (hkK : k ∈ K)
    (hkC : k ∈ Subgroup.centralizer (K : Set G)) {a : kUpperA}
    (hmem : ∀ x : kUpperA, x ∈ sylowTwoQA45 ↔
      a⁻¹ * x * a ∈ imageQA45 (z := z) D (hK.le.trans inf_le_left)) :
    a * qH D ⟨k, (hK.le hkK).1⟩ * a⁻¹ ∈ sylowTwoQA45 ⊓
      Subgroup.centralizer (sylowTwoQA45 : Set kUpperA) := by
  let qK : Subgroup kUpperA := imageQA45 (z := z) D (hK.le.trans inf_le_left)
  let qk : kUpperA := qH D ⟨k, (hK.le hkK).1⟩
  have hKleH : K ≤ H z := hK.le.trans inf_le_left
  have hqk_mem_qK : qk ∈ qK := by
    rw [show qK = imageQA45 (z := z) D (hK.le.trans inf_le_left) from rfl]
    exact (mem_imageQA45_iff D (hK.le.trans inf_le_left) qk).mpr ⟨k, hkK, rfl⟩
  have hqk_centQ : qk ∈ Subgroup.centralizer (qK : Set kUpperA) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨k', hk'K, rfl⟩ := (mem_imageQA45_iff D hKleH x).mp hx
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hkC k' hk'K
  have hqk_centT : a * qk * a⁻¹ ∈ Subgroup.centralizer (sylowTwoQA45 : Set kUpperA) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxQ : a⁻¹ * x * a ∈ qK := (hmem x).mp hx
    have hcomm := Subgroup.mem_centralizer_iff.mp hqk_centQ (a⁻¹ * x * a) hxQ
    have hcomm' := congrArg (fun t : kUpperA => a * t * a⁻¹) hcomm
    simpa only [mul_assoc, mul_inv_cancel, inv_mul_cancel, mul_inv_cancel_left,
      inv_mul_cancel_left, one_mul, mul_one] using hcomm'
  have hmemT : a * qk * a⁻¹ ∈ sylowTwoQA45 := by
    refine (hmem (a * qk * a⁻¹)).mpr ?_
    rw [show a⁻¹ * (a * qk * a⁻¹) * a = qk by
      simp only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left, inv_mul_cancel, mul_one]]
    exact hqk_mem_qK
  exact Subgroup.mem_inf.mpr ⟨hmemT, hqk_centT⟩

private theorem isConj_tA_of_mem_centerIn (h : Tim79a.ParrottHyp z) {j : G} (hj : j ∈ J z)
    (hjZ : j ∉ centerIn (J z)) {K : Subgroup G}
    (hK : IsSylowOf 2 K (H z ⊓ centralizer ({j} : Set G)))
    (hcard : Nat.card K = 2 ^ 16) {k : G} (hkK : k ∈ K)
    (hkC : k ∈ Subgroup.centralizer (K : Set G))
    (hqne : qH D ⟨k, (hK.le hkK).1⟩ ≠ 1) :
    IsConj (qH D ⟨k, (hK.le hkK).1⟩) (⟨t, t_mem_A⟩ : ↥QA45.originalSubgroup) := by
  classical
  let qk : kUpperA := qH D ⟨k, (hK.le hkK).1⟩
  obtain ⟨a, hmem⟩ := exists_mem_conj_sylowTwoQA45 (z := z) D h hj hjZ hK hcard
  have hmemInf := conj_mem_center_sylowTwoQA45_of_mem_centerIn (z := z) D h hj hjZ hK hcard
    hkK hkC hmem
  have hcenter : a * qk * a⁻¹ ∈ Subgroup.zpowers (⟨t, t_mem_A⟩ : kUpperA) := by
    rw [sylowTwoQA45_inf_centralizer] at hmemInf
    simpa [qk] using hmemInf
  rcases CFSG.GF2Type.Aschbacher1976Full.Z4Q8.mem_zpowers_two orderOf_tA hcenter with h1 | h1
  · exfalso
    apply hqne
    have h2 := congrArg (fun x : kUpperA => a⁻¹ * x * a) h1
    simpa [qk, mul_assoc, inv_mul_cancel] using h2
  · exact isConj_iff.mpr ⟨a, h1⟩

private theorem not_mem_centerIn_of_z1_of_isSylow
    (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    {j : G} (hj : j ∈ J z) (hjZ : j ∉ centerIn (J z)) {K : Subgroup G}
    (hK : IsSylowOf 2 K (H z ⊓ centralizer ({j} : Set G)))
    (hcard : Nat.card K = 2 ^ 16)
    (hqcard : Nat.card (imageQA45 (z := z) D (hK.le.trans inf_le_left)) = 2 ^ 7)
    (hz₁K : z₁ ∈ centerIn K) : False := by
  have hKleH : K ≤ H z := hK.le.trans inf_le_left
  let qK : Subgroup ↥QA45.originalSubgroup := imageQA45 (z := z) D hKleH
  have hnotle : ¬ qK ≤ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup := by
    intro hle
    have hdvd : Nat.card qK ∣ 25920 := by
      rw [← card_QP45_subgroupOf]
      exact Subgroup.card_dvd_of_le hle
    rw [hqcard] at hdvd
    exact absurd hdvd (by norm_num)
  have hnotle' : ¬ (qK : Set ↥QA45.originalSubgroup) ⊆
      (QP45.originalSubgroup.subgroupOf QA45.originalSubgroup :
        Set ↥QA45.originalSubgroup) := hnotle
  obtain ⟨x, hxq, hxQ⟩ := Set.not_subset.mp hnotle'
  obtain ⟨k', hk'K, hqk'⟩ := (mem_imageQA45_iff D hKleH x).mp hxq
  have hk'cent : (k' : G) ∈ Subgroup.centralizer ({z₁} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hz₁K.2 k' hk'K)
  have hqk'P : qH D ⟨k', hKleH hk'K⟩ ∈
      QP45.originalSubgroup.subgroupOf QA45.originalSubgroup :=
    (mem_centralizer_z1_iff_qH_mem_QP45 (z := z) D h hZ hz₁ hz₁z hord
      ⟨k', hKleH hk'K⟩).mp hk'cent
  rw [hqk'] at hqk'P
  exact hxQ hqk'P

private theorem closure_pair_le_centerIn (h : Tim79a.ParrottHyp z) {j : G} (hj : j ∈ J z)
    {K : Subgroup G} (hK : IsSylowOf 2 K (H z ⊓ centralizer ({j} : Set G))) :
    Subgroup.closure ({z, j} : Set G) ≤ centerIn K := by
  have hKleH : K ≤ H z := hK.le.trans inf_le_left
  have hCJleK : J z ⊓ Subgroup.centralizer ({j} : Set G) ≤ K :=
    J_inf_centralizer_le_of_isSylowOf h hK
  have hzK : z ∈ K := by
    have hzCJ : z ∈ J z ⊓ Subgroup.centralizer ({j} : Set G) :=
      Subgroup.mem_inf.mpr ⟨z_mem_J h,
        Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp (z_centralizes_J h) j hj).symm⟩
    exact hCJleK hzCJ
  have hjK : j ∈ K := by
    have hjCJ : j ∈ J z ⊓ Subgroup.centralizer ({j} : Set G) :=
      Subgroup.mem_inf.mpr ⟨hj, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    exact hCJleK hjCJ
  have hzKcent : z ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.centralizer_le hKleH (z_centralizes_H h)
  have hjKcent : j ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (hK.le.trans inf_le_right hy)
  have hzcenter : z ∈ centerIn K := Subgroup.mem_inf.mpr ⟨hzK, hzKcent⟩
  have hjcenter : j ∈ centerIn K := Subgroup.mem_inf.mpr ⟨hjK, hjKcent⟩
  rw [Subgroup.closure_le]
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · exact hzcenter
  · rw [Set.mem_singleton_iff] at hx
    exact hx ▸ hjcenter

private theorem mem_centerIn_J_or_mul_of_mem_centerIn (h : Tim79a.ParrottHyp z) {j : G}
    (hj : j ∈ J z) (hjZ : j ∉ centerIn (J z)) {K : Subgroup G}
    (hK : IsSylowOf 2 K (H z ⊓ centralizer ({j} : Set G))) {k : G}
    (hk : k ∈ centerIn K) (hqk1 : qH D ⟨k, (hK.le hk.1).1⟩ = 1) :
    k ∈ centerIn (J z) ∨ k * j ∈ centerIn (J z) := by
  have hkJ : k ∈ J z := by
    have hker : (⟨k, (hK.le hk.1).1⟩ : ↥(H z)) ∈ (qH D).ker :=
      MonoidHom.mem_ker.mpr hqk1
    rw [ker_qH] at hker
    exact Subgroup.mem_subgroupOf.mp hker
  have hCJleK : J z ⊓ Subgroup.centralizer ({j} : Set G) ≤ K :=
    J_inf_centralizer_le_of_isSylowOf h hK
  let jJ : J z := ⟨j, hj⟩
  let kJ : J z := ⟨k, hkJ⟩
  have horth : ∀ w : QuotientV.V z,
      polarVZMod h (QuotientV.pi z jJ) w = 0 →
        polarVZMod h (QuotientV.pi z kJ) w = 0 := by
    intro w hw
    obtain ⟨y, rfl⟩ := QuotientV.pi_surjective z w
    have hyj : Commute (y : G) (j : G) :=
      ((polarVZMod_pi_eq_zero_iff h jJ y).mp hw).symm
    have hyCJ : (y : G) ∈ J z ⊓ Subgroup.centralizer ({j} : Set G) :=
      Subgroup.mem_inf.mpr ⟨y.2, Subgroup.mem_centralizer_singleton_iff.mpr hyj⟩
    have hky : Commute (k : G) (y : G) :=
      (Subgroup.mem_centralizer_iff.mp hk.2 (y : G) (hCJleK hyCJ)).symm
    exact (polarVZMod_pi_eq_zero_iff h kJ y).mpr hky
  rcases polarVZMod_eq_one_or_eq_of_forall_orthogonal h horth with h1 | h1
  · exact Or.inl ((pi_eq_one_iff_mem_centerIn hkJ).mp h1)
  · refine Or.inr ?_
    have h1' : QuotientV.pi z (kJ * jJ) = 1 := by
      rw [map_mul, h1]
      simpa [pow_two] using QuotientV.pow_two_eq_one_V h (QuotientV.pi z jJ)
    exact (pi_eq_one_iff_mem_centerIn ((J z).mul_mem hkJ hj)).mp h1'

private theorem mem_closure_of_mem_centerIn_J
    (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    {j : G} (hj : j ∈ J z) (hjZ : j ∉ centerIn (J z)) {K : Subgroup G}
    (hK : IsSylowOf 2 K (H z ⊓ centralizer ({j} : Set G)))
    (hcard : Nat.card K = 2 ^ 16)
    (hqcardK : Nat.card (imageQA45 (z := z) D (hK.le.trans inf_le_left)) = 2 ^ 7)
    {k : G} (hk : k ∈ centerIn K) (hZk : k ∈ centerIn (J z)) :
    k ∈ Subgroup.closure {z, j} := by
  have hnotz1 : z₁ ∉ centerIn K := fun hz1 =>
    not_mem_centerIn_of_z1_of_isSylow (z := z) D h hZ hz₁ hz₁z hord hj hjZ hK hcard hqcardK hz1
  have hzcenter : z ∈ centerIn K :=
    closure_pair_le_centerIn h hj hK (Subgroup.subset_closure (by simp))
  have hz_sq : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [h.1, pow_two] at this
  rcases (mem_centerIn_J_iff h hz₁ hz₁z hord).mp hZk with rfl | rfl | rfl | rfl
  · exact Subgroup.one_mem _
  · exact Subgroup.subset_closure (by simp)
  · exact absurd hk hnotz1
  · have hz1mem : z₁ ∈ centerIn K := by
      have hzmem : z ∈ centerIn K := hzcenter
      have hmem : z * z₁ ∈ centerIn K := hk
      rw [← show z * (z * z₁) = z₁ by rw [← mul_assoc, hz_sq, one_mul]]
      exact Subgroup.mul_mem _ hzmem hmem
    exact absurd hz1mem hnotz1

private theorem mem_closure_of_mul_mem_centerIn_J
    (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    {j : G} (hj : j ∈ J z) (hj2 : orderOf j = 2) (hjZ : j ∉ centerIn (J z))
    {K : Subgroup G} (hK : IsSylowOf 2 K (H z ⊓ centralizer ({j} : Set G)))
    (hcard : Nat.card K = 2 ^ 16)
    (hqcardK : Nat.card (imageQA45 (z := z) D (hK.le.trans inf_le_left)) = 2 ^ 7)
    {k : G} (hk : k ∈ centerIn K) (hZkj : k * j ∈ centerIn (J z)) :
    k ∈ Subgroup.closure {z, j} := by
  have hnotz1 : z₁ ∉ centerIn K := fun hz1 =>
    not_mem_centerIn_of_z1_of_isSylow (z := z) D h hZ hz₁ hz₁z hord hj hjZ hK hcard hqcardK hz1
  have hzcenter : z ∈ centerIn K :=
    closure_pair_le_centerIn h hj hK (Subgroup.subset_closure (by simp))
  have hjcenter : j ∈ centerIn K :=
    closure_pair_le_centerIn h hj hK (Subgroup.subset_closure (by simp))
  have hkjcenter : k * j ∈ centerIn K := Subgroup.mul_mem _ hk hjcenter
  have hj_sq : j * j = 1 := by
    have := pow_orderOf_eq_one j
    rwa [hj2, pow_two] at this
  have hz_sq : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [h.1, pow_two] at this
  rcases (mem_centerIn_J_iff h hz₁ hz₁z hord).mp hZkj with he | he | he | he
  · have hk_eq : k = j := by
      calc k = k * (j * j) := by rw [hj_sq, mul_one]
        _ = (k * j) * j := by rw [mul_assoc]
        _ = 1 * j := by rw [he]
        _ = j := one_mul j
    exact hk_eq ▸ Subgroup.subset_closure (by simp)
  · have hk_eq : k = z * j := by
      calc k = k * (j * j) := by rw [hj_sq, mul_one]
        _ = (k * j) * j := by rw [mul_assoc]
        _ = z * j := by rw [he]
    exact hk_eq ▸ Subgroup.mul_mem _
      (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  · have hz1mem : z₁ ∈ centerIn K := by
      rw [← he]
      exact hkjcenter
    exact absurd hz1mem hnotz1
  · have hz1mem : z₁ ∈ centerIn K := by
      have hzmem : z ∈ centerIn K := hzcenter
      have hmem : z * z₁ ∈ centerIn K := by
        rw [← he]
        exact hkjcenter
      rw [← show z * (z * z₁) = z₁ by rw [← mul_assoc, hz_sq, one_mul]]
      exact Subgroup.mul_mem _ hzmem hmem
    exact absurd hz1mem hnotz1

private theorem mem_closure_of_mem_centerIn_J_or_mul
    (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    {j : G} (hj : j ∈ J z) (hj2 : orderOf j = 2) (hjZ : j ∉ centerIn (J z))
    {K : Subgroup G} (hK : IsSylowOf 2 K (H z ⊓ centralizer ({j} : Set G)))
    (hcard : Nat.card K = 2 ^ 16)
    (hqcardK : Nat.card (imageQA45 (z := z) D (hK.le.trans inf_le_left)) = 2 ^ 7)
    {k : G} (hk : k ∈ centerIn K)
    (hZcases : k ∈ centerIn (J z) ∨ k * j ∈ centerIn (J z)) :
    k ∈ Subgroup.closure {z, j} := by
  rcases hZcases with hZk | hZkj
  · exact mem_closure_of_mem_centerIn_J (z := z) D h hZ hz₁ hz₁z hord hj hjZ hK hcard hqcardK
      hk hZk
  · exact mem_closure_of_mul_mem_centerIn_J (z := z) D h hZ hz₁ hz₁z hord hj hj2 hjZ hK hcard
      hqcardK hk hZkj

theorem centerIn_isSylowOf_centralizer_eq (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    (ht : ∀ k : ↥(H z), IsConj (qH D k) (⟨t, t_mem_A⟩ : ↥QA45.originalSubgroup) →
      fixDimV h k < 7)
    {j : G} (hj : j ∈ J z) (hj2 : orderOf j = 2) (hjZ : j ∉ centerIn (J z)) {K : Subgroup G}
    (hK : IsSylowOf 2 K (H z ⊓ centralizer ({j} : Set G))) (hcard : Nat.card K = 2 ^ 16) :
    centerIn K = Subgroup.closure {z, j} := by
  have hKleH : K ≤ H z := hK.le.trans inf_le_left
  have hqcardK : Nat.card (imageQA45 (z := z) D (hK.le.trans inf_le_left)) = 2 ^ 7 :=
    card_imageQA45_eq_two_pow_seven (z := z) D h hj hjZ hK hcard
  refine le_antisymm ?_ (closure_pair_le_centerIn h hj hK)
  intro k hk
  have hkK : k ∈ K := hk.1
  have hkC : k ∈ Subgroup.centralizer (K : Set G) := hk.2
  have hkH : k ∈ H z := hKleH hkK
  let kH : ↥(H z) := ⟨k, hkH⟩
  have hfix7 : 7 ≤ fixDimV h kH :=
    seven_le_fixDimV_of_mem_centerIn h hj hjZ hK hkK hkC
  have hqk1 : qH D kH = 1 := by
    by_contra hqne
    have hconj : IsConj (qH D kH) (⟨t, t_mem_A⟩ : ↥QA45.originalSubgroup) :=
      isConj_tA_of_mem_centerIn (z := z) D h hj hjZ hK hcard hkK hkC hqne
    exact absurd (ht kH hconj) (not_lt.mpr hfix7)
  exact mem_closure_of_mem_centerIn_J_or_mul (z := z) D h hZ hz₁ hz₁z hord hj hj2 hjZ hK hcard
    hqcardK hk (mem_centerIn_J_or_mul_of_mem_centerIn (z := z) D h hj hjZ hK hk hqk1)

end CFSG.RankThree.GF2n.Parrott
