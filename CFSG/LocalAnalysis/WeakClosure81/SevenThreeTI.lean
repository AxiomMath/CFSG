module

public import CFSG.LocalAnalysis.WeakClosure81.SevenFive
public import CFSG.RankThree.GF2n.Tim78RootType
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped commutatorElement Pointwise

section General

variable {G : Type*} [Group G]

theorem map_conjSubgroup_hom {G' : Type*} [Group G'] (f : G →* G') (A : Subgroup G) (x : G) :
    conjSubgroup (A.map f) (f x) = (conjSubgroup A x).map f := by
  ext q
  constructor
  · intro hq
    rw [mem_conjSubgroup_iff, Subgroup.mem_map] at hq
    obtain ⟨a, ha, haq⟩ := hq
    refine Subgroup.mem_map.mpr ⟨x⁻¹ * a * x, ?_, ?_⟩
    · rw [mem_conjSubgroup_iff, show x * (x⁻¹ * a * x) * x⁻¹ = a by group]
      exact ha
    · rw [map_mul, map_mul, map_inv, haq]
      group
  · intro hq
    rw [Subgroup.mem_map] at hq
    obtain ⟨b, hb, hbq⟩ := hq
    rw [mem_conjSubgroup_iff] at hb
    rw [mem_conjSubgroup_iff, ← hbq]
    exact Subgroup.mem_map.mpr ⟨x * b * x⁻¹, hb, by rw [map_mul, map_mul, map_inv]⟩

theorem map_conjSubgroup_subgroupOf' {H A : Subgroup G} (hA : A ≤ H) {x : G} (hx : x ∈ H) :
    (conjSubgroup (A.subgroupOf H) ⟨x, hx⟩).map H.subtype = conjSubgroup A x := by
  rw [← map_conjSubgroup_hom H.subtype (A.subgroupOf H) ⟨x, hx⟩,
    Subgroup.map_subgroupOf_eq_of_le hA]
  rfl

theorem isPGroup_of_map_mk_isPGroup {X J H : Subgroup G} (hXH : X ≤ H) (hJH : J ≤ H)
    (hJnorm : (J.subgroupOf H).Normal) (hJ2 : IsPGroup 2 J)
    (h : IsPGroup 2 ((X.subgroupOf H).map (QuotientGroup.mk' (J.subgroupOf H)))) :
    IsPGroup 2 X := by
  haveI : (J.subgroupOf H).Normal := hJnorm
  let π : ↥H →* (↥H ⧸ (J.subgroupOf H)) := QuotientGroup.mk' (J.subgroupOf H)
  have hker : IsPGroup 2 π.ker := by
    rw [show π.ker = J.subgroupOf H from QuotientGroup.ker_mk' (J.subgroupOf H)]
    exact hJ2.of_equiv (Subgroup.subgroupOfEquivOfLe hJH).symm
  have hcomap : IsPGroup 2 (((X.subgroupOf H).map π).comap π) :=
    IsPGroup.comap_of_ker_isPGroup h π hker
  have hXsub : IsPGroup 2 (X.subgroupOf H) :=
    hcomap.to_le (Subgroup.le_comap_map π (X.subgroupOf H))
  exact hXsub.of_equiv (Subgroup.subgroupOfEquivOfLe hXH)

theorem eq_one_of_mem_isPGroup_of_odd {J : Subgroup G} (hJ2 : IsPGroup 2 J) {x : G}
    (hx : x ∈ J) (hodd : Odd (orderOf x)) : x = 1 := by
  obtain ⟨k, hk⟩ := CFSG.CGT.Timmesfeld75.exists_orderOf_eq_two_pow_of_mem hJ2 hx
  have hcop : Nat.Coprime (orderOf x) (2 ^ k) := (Nat.coprime_two_right.mpr hodd).pow_right k
  have hdvd : orderOf x ∣ 2 ^ k := by rw [hk]
  exact orderOf_eq_one_iff.mp (hcop.eq_one_of_dvd hdvd)

theorem conj_zpow_inv_eq {a u : G} (h : u * a * u⁻¹ = a⁻¹) (n : ℤ) :
    u * a ^ n * u⁻¹ = (a ^ n)⁻¹ := by
  rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, h, inv_zpow]

theorem invol_mul_zpow_mul {a u : G} (hu : u * u = 1) (h : u * a * u⁻¹ = a⁻¹) (n : ℤ) :
    u * a ^ n * u = a ^ (-n) := by
  have h1 : u * a ^ n * u⁻¹ = a ^ (-n) := by rw [conj_zpow_inv_eq h n, zpow_neg]
  rwa [inv_eq_of_mul_eq_one_right hu] at h1

theorem inv_zpow_mul_mul_zpow_of_inverts {a u : G} (h : u * a * u⁻¹ = a⁻¹) (n : ℤ) :
    (a ^ n)⁻¹ * u * a ^ n = (a ^ (2 * n))⁻¹ * u := by
  have h1 : u * a ^ n * u⁻¹ = (a ^ n)⁻¹ := conj_zpow_inv_eq h n
  have h2 : u * a ^ n = (a ^ n)⁻¹ * u := mul_inv_eq_iff_eq_mul.1 h1
  calc (a ^ n)⁻¹ * u * a ^ n = (a ^ n)⁻¹ * (u * a ^ n) := mul_assoc _ _ _
    _ = (a ^ n)⁻¹ * ((a ^ n)⁻¹ * u) := by rw [h2]
    _ = ((a ^ n)⁻¹ * (a ^ n)⁻¹) * u := (mul_assoc _ _ _).symm
    _ = (a ^ (2 * n))⁻¹ * u := by rw [← mul_inv_rev, ← zpow_add, two_mul]

theorem inv_zpow_mul_mul_zpow_self (u : G) (n : ℤ) : (u ^ n)⁻¹ * u * u ^ n = u := by
  calc (u ^ n)⁻¹ * u * u ^ n = (u ^ n)⁻¹ * (u * u ^ n) := mul_assoc _ _ _
    _ = (u ^ n)⁻¹ * u ^ (1 + n) := by rw [zpow_one_add]
    _ = (u ^ n)⁻¹ * u ^ (n + 1) := by rw [show (1 : ℤ) + n = n + 1 by ring]
    _ = (u ^ n)⁻¹ * (u ^ n * u) := by rw [zpow_add_one]
    _ = u := by group

theorem exists_conj_inv_mul_of_involutions_odd {u w : G} (hu : u * u = 1) (hw : w * w = 1)
    (hodd : Odd (orderOf (u * w))) :
    ∃ x ∈ Subgroup.closure ({u, w} : Set G), x⁻¹ * u * x = w := by
  obtain ⟨k, hk⟩ := hodd
  have huw : u * w ∈ Subgroup.closure ({u, w} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))
  refine ⟨(u * w) ^ (k + 1), Subgroup.pow_mem _ huw _, ?_⟩
  have h1 := inv_pow_mul_mul_pow_of_inverts (left_invol_inverts hu hw) (k + 1)
  rw [h1]
  have h2 : (u * w) ^ (2 * (k + 1)) = u * w := by
    rw [show 2 * (k + 1) = orderOf (u * w) + 1 by omega, pow_succ, pow_orderOf_eq_one, one_mul]
  rw [h2]
  exact (invol_eq_inv_mul_mul hw).symm

theorem mem_sup_zpowers_of_conj_mem_isPGroup {u w y : G} (hu : u * u = 1) (hw : w * w = 1)
    (hodd : Odd (orderOf (u * w))) {J : Subgroup G} (hJ2 : IsPGroup 2 J)
    (hy : y ∈ Subgroup.closure ({u, w} : Set G))
    (hconj : y⁻¹ * u * y * u⁻¹ ∈ J) :
    y ∈ Subgroup.zpowers u ⊔ J := by
  set a := u * w with ha
  have hodd_a : Odd (orderOf a) := by rwa [ha]
  have hua : u * a * u⁻¹ = a⁻¹ := by rw [ha]; exact left_invol_inverts hu hw
  obtain ⟨n, hn | hn⟩ := CFSG.RankThree.GF2n.Tim78.mem_closure_pair_involutions hu hw hy
  · have hmem : (a ^ (2 * n))⁻¹ ∈ J := by
      have h := hconj
      rw [hn] at h
      rw [inv_zpow_mul_mul_zpow_of_inverts hua n] at h
      simpa using h
    have hmem' : a ^ (2 * n) ∈ J := by
      rw [← inv_inv (a ^ (2 * n))]
      exact J.inv_mem hmem
    have hodd2 : Odd (orderOf (a ^ (2 * n))) :=
      hodd_a.of_dvd_nat (orderOf_dvd_of_mem_zpowers
        (Subgroup.mem_zpowers_iff.mpr ⟨2 * n, rfl⟩))
    have h1 : a ^ (2 * n) = 1 := eq_one_of_mem_isPGroup_of_odd hJ2 hmem' hodd2
    have h2 : a ^ n = 1 := by
      refine eq_one_of_mul_self_eq_one_of_odd ?_ ?_
      · rw [← zpow_add, show n + n = 2 * n by ring]
        exact h1
      · exact hodd_a.of_dvd_nat (orderOf_dvd_of_mem_zpowers
          (Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩))
    rw [hn, h2]
    exact Subgroup.mem_sup_left (Subgroup.one_mem _)
  · have hmem : a ^ (2 * n) ∈ J := by
      have h := hconj
      rw [hn] at h
      have he : (a ^ n * u)⁻¹ * u * (a ^ n * u) = a ^ (2 * n) * u := by
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hu, ← zpow_neg,
          invol_mul_zpow_mul hu hua (-n)]
        rw [neg_neg]
        rw [show a ^ n * (a ^ n * u) = a ^ n * a ^ n * u by group]
        rw [← zpow_add, show n + n = 2 * n by ring]
      rw [he] at h
      simpa using h
    have hodd2 : Odd (orderOf (a ^ (2 * n))) :=
      hodd_a.of_dvd_nat (orderOf_dvd_of_mem_zpowers
        (Subgroup.mem_zpowers_iff.mpr ⟨2 * n, rfl⟩))
    have h1 : a ^ (2 * n) = 1 := eq_one_of_mem_isPGroup_of_odd hJ2 hmem hodd2
    have h2 : a ^ n = 1 := by
      refine eq_one_of_mul_self_eq_one_of_odd ?_ ?_
      · rw [← zpow_add, show n + n = 2 * n by ring]
        exact h1
      · exact hodd_a.of_dvd_nat (orderOf_dvd_of_mem_zpowers
          (Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩))
    rw [hn, h2, one_mul]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers u)

end General

variable {G : Type} [Group G] [Finite G]

theorem isElemAbelian_of_mem_omegaSet {V H E U : Subgroup G} (hV : IsElemAbelian 2 V)
    (hU : U ∈ omegaSet V H E) : IsElemAbelian 2 U := by
  obtain ⟨g, rfl, -, -⟩ := mem_omegaSet.mp hU
  exact isElemAbelian_conjSubgroup' hV g

theorem inf_iSub_eq_inf_pCoreOf {V H E U : Subgroup G} (hU : U ∈ omegaSet V H E) :
    U ⊓ iSub V H E = U ⊓ pCoreOf 2 H := by
  refine le_antisymm ?_ ?_
  · exact inf_le_inf le_rfl (iSup_le fun W => iSup_le fun _ => inf_le_right)
  · exact le_inf inf_le_left (inf_pCoreOf_le_iSub hU)

theorem inf_iSub_eq_inf_J {V H E J U : Subgroup G} (hU : U ∈ omegaSet V H E)
    (hIJ : iSub V H E ≤ J) (hJ : J ≤ pCoreOf 2 H) : U ⊓ iSub V H E = U ⊓ J := by
  refine le_antisymm (inf_le_inf le_rfl hIJ) ?_
  calc U ⊓ J ≤ U ⊓ pCoreOf 2 H := inf_le_inf le_rfl hJ
    _ = U ⊓ iSub V H E := (inf_iSub_eq_inf_pCoreOf hU).symm

theorem inf_pCoreOf_ne_bot_of_mem_omegaSet {V H E U : Subgroup G}
    (hV : IsElemAbelian 2 V) (hE : IsMulCommutative E) (hEH : E ≤ H)
    (hEnorm : (E.subgroupOf H).Normal) (hU : U ∈ omegaSet V H E) :
    U ⊓ pCoreOf 2 H ≠ ⊥ := by
  obtain ⟨g, rfl, hEU, -⟩ := mem_omegaSet.mp hU
  have hUe : IsElemAbelian 2 (conjSubgroup V g) := isElemAbelian_conjSubgroup' hV g
  have hUE_le_O : conjSubgroup V g ⊓ E ≤ pCoreOf 2 H := by
    have hp : IsPGroup 2 ↥(conjSubgroup V g ⊓ E : Subgroup G) :=
      (CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian hUe).to_le inf_le_left
    have hnorm' : ((conjSubgroup V g ⊓ E).subgroupOf E).Normal := by
      haveI : IsMulCommutative E := hE
      infer_instance
    have h1 : conjSubgroup V g ⊓ E ≤ pCoreOf 2 E :=
      CFSG.LieType.BorelTits.le_pCoreOf 2 inf_le_right hnorm' hp
    have h2 : pCoreOf 2 E ≤ pCoreOf 2 H := by
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le (r := 2) E).trans hEH) ?_
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) E)
      intro h hh
      exact (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) E)
        (le_normalizer_of_subgroupOf_normal hEH hEnorm hh)
    exact h1.trans h2
  have hne : conjSubgroup V g ⊓ E ≠ ⊥ := by rwa [inf_comm] at hEU
  intro hbot
  apply hne
  apply le_bot_iff.mp
  intro x hx
  have hx' : x ∈ conjSubgroup V g ⊓ pCoreOf 2 H := ⟨hx.1, hUE_le_O hx⟩
  rw [hbot] at hx'
  exact hx'

theorem mem_dSet_of_mem_of_not_mem_J {V H E J U : Subgroup G} (hU : U ∈ omegaSet V H E)
    (hIJ : iSub V H E ≤ J) (hJ : J ≤ pCoreOf 2 H) {u : G} (hu : u ∈ U) (huJ : u ∉ J) :
    u ∈ dSet V H E := by
  have hle : U ⊓ pCoreOf 2 H ≤ U ⊓ J := by
    calc U ⊓ pCoreOf 2 H ≤ U ⊓ iSub V H E := le_inf inf_le_left (inf_pCoreOf_le_iSub hU)
      _ = U ⊓ J := inf_iSub_eq_inf_J hU hIJ hJ
  refine mem_dSet.mpr ⟨U, hU, hu, ?_⟩
  intro huO
  exact huJ (hle ⟨hu, huO⟩).2

theorem kSub_subgroupOf_normal {V H E : Subgroup G} (hEH : E ≤ H)
    (hEnorm : (E.subgroupOf H).Normal) (hOmH : ∀ W ∈ omegaSet V H E, W ≤ H) :
    ((kSub V H E).subgroupOf H).Normal := by
  have hKle : kSub V H E ≤ H := kSub_le_of_forall_le hOmH
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hKle).2 ?_
  intro h hh
  rw [← conjSubgroup_eq_iff_mem_normalizer]
  have hmap : conjSubgroup (kSub V H E) h =
      ⨆ U ∈ omegaSet V H E, conjSubgroup U h := by
    rw [kSub]
    simp only [CFSG.Quasithin.conjSubgroup, Subgroup.map_iSup]
  rw [hmap]
  refine le_antisymm ?_ ?_
  · refine iSup_le fun U => iSup_le fun hU => ?_
    exact le_iSup₂_of_le (conjSubgroup U h) (conjSubgroup_mem_omegaSet hEH hEnorm hU hh) le_rfl
  · refine iSup_le fun U => iSup_le fun hU => ?_
    have hUinv : conjSubgroup U h⁻¹ ∈ omegaSet V H E :=
      conjSubgroup_mem_omegaSet hEH hEnorm hU (H.inv_mem hh)
    refine le_iSup₂_of_le (conjSubgroup U h⁻¹) hUinv ?_
    rw [CFSG.Quasithin.conjSubgroup_conjSubgroup, inv_mul_cancel, CFSG.Quasithin.conjSubgroup_one]

theorem pCoreOf_kSub_le_pCoreOf {V H E : Subgroup G} (hEH : E ≤ H)
    (hEnorm : (E.subgroupOf H).Normal) (hOmH : ∀ W ∈ omegaSet V H E, W ≤ H) :
    pCoreOf 2 (kSub V H E) ≤ pCoreOf 2 H := by
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) (kSub V H E))
  · exact (CFSG.LieType.BorelTits.pCoreOf_le (r := 2) (kSub V H E)).trans
      (kSub_le_of_forall_le hOmH)
  · refine (le_normalizer_of_subgroupOf_normal (kSub_le_of_forall_le hOmH)
      (kSub_subgroupOf_normal hEH hEnorm hOmH)).trans ?_
    exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) (kSub V H E)

theorem seven_three_three {V H E J : Subgroup G}
    (hV : IsElemAbelian 2 V) (hTI : IsTI V) (hE : IsMulCommutative E)
    (hEH : E ≤ H) (hEnorm : (E.subgroupOf H).Normal)
    (hOmH : ∀ W ∈ omegaSet V H E, W ≤ H)
    (hJ : J ≤ pCoreOf 2 H) (hJnorm : (J.subgroupOf H).Normal)
    {u v : G} (hu : u ∈ dSet V H E) (hv : v ∈ dSet V H E) (huv : u⁻¹ * v ∈ J) :
    ∃ j ∈ J, u = j⁻¹ * v * j := by
  have hJleH : J ≤ H := hJ.trans (CFSG.LieType.BorelTits.pCoreOf_le (r := 2) H)
  have hJ2 : IsPGroup 2 J := (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) H).to_le hJ
  have hKle : kSub V H E ≤ H := kSub_le_of_forall_le hOmH
  have hKnorm : ((kSub V H E).subgroupOf H).Normal := kSub_subgroupOf_normal hEH hEnorm hOmH
  have hpcoreK : pCoreOf 2 (kSub V H E) ≤ pCoreOf 2 H :=
    pCoreOf_kSub_le_pCoreOf hEH hEnorm hOmH
  have huK : u ∈ kSub V H E := mem_kSub_of_mem_dSet hu
  have hvK : v ∈ kSub V H E := mem_kSub_of_mem_dSet hv
  obtain ⟨Uv, hUv, hvUv, hvO⟩ := mem_dSet.mp hv
  obtain ⟨k, hkK, hknot⟩ : ∃ k ∈ kSub V H E,
      ¬ IsPGroup 2 (Subgroup.closure ({v, k⁻¹ * v * k} : Set G)) := by
    by_contra h
    push Not at h
    apply hvO
    apply hpcoreK
    refine mem_pCoreOf_of_forall_closure_isPGroup hvK ?_
    intro g hg
    have hg' := h g⁻¹ ((kSub V H E).inv_mem hg)
    rw [inv_inv] at hg'
    exact hg'
  have hkH : k ∈ H := hKle hkK
  set w : G := k⁻¹ * v * k with hwdef
  have hwU : conjSubgroup Uv k ∈ omegaSet V H E :=
    conjSubgroup_mem_omegaSet hEH hEnorm hUv hkH
  have hw_mem : w ∈ conjSubgroup Uv k := by
    rw [hwdef, mem_conjSubgroup_iff]
    rw [show k * (k⁻¹ * v * k) * k⁻¹ = v by group]
    exact hvUv
  have hwO : w ∉ pCoreOf 2 H := by
    intro hwO'
    apply hvO
    have hv_eq : v = k * w * k⁻¹ := by rw [hwdef]; group
    rw [hv_eq]
    exact (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) H hkH) w).mp hwO'
  have hvw_odd : Odd (orderOf (v * w)) :=
    seven_three_A hV hTI hE hUv hwU hvUv hw_mem (by rwa [hwdef])
  have huH : u ∈ H := hKle huK
  have hwK : w ∈ kSub V H E := le_kSub hwU hw_mem
  have hu2 : u * u = 1 := by
    obtain ⟨Uu, hUu, huUu, -⟩ := mem_dSet.mp hu
    exact CFSG.CGT.Timmesfeld75.elemAbelian_mul_self
      (isElemAbelian_of_mem_omegaSet hV hUu) huUu
  have hv2 : v * v = 1 := CFSG.CGT.Timmesfeld75.elemAbelian_mul_self
    (isElemAbelian_of_mem_omegaSet hV hUv) hvUv
  have hw2 : w * w = 1 :=
    CFSG.CGT.Timmesfeld75.elemAbelian_mul_self
      (isElemAbelian_of_mem_omegaSet hV hwU) hw_mem
  have hclHuw : Subgroup.closure ({u, w} : Set G) ≤ H :=
    (Subgroup.closure_le H).mpr (by
      rintro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact huH
      · exact hKle hwK)
  have hclN : Subgroup.closure ({u, w} : Set G) ≤ Subgroup.normalizer (J : Set G) :=
    hclHuw.trans (le_normalizer_of_subgroupOf_normal hJleH hJnorm)
  have huw_not : ¬ IsPGroup 2 (Subgroup.closure ({u, w} : Set G)) := by
    intro h2
    haveI : (J.subgroupOf H).Normal := hJnorm
    let π : ↥H →* (↥H ⧸ (J.subgroupOf H)) := QuotientGroup.mk' (J.subgroupOf H)
    have h2sub : IsPGroup 2 ((Subgroup.closure ({u, w} : Set G)).subgroupOf H) :=
      IsPGroup.comap_of_injective h2 H.subtype H.subtype_injective
    have hJmap : (J.subgroupOf H).map π = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      exact (QuotientGroup.eq_one_iff y).mpr hy
    have hImS : ((Subgroup.closure ({u, w} : Set G) ⊔ J).subgroupOf H).map π =
        ((Subgroup.closure ({u, w} : Set G)).subgroupOf H).map π := by
      rw [Subgroup.subgroupOf_sup hclHuw hJleH, Subgroup.map_sup, hJmap, sup_bot_eq]
    have hS_image : IsPGroup 2 (((Subgroup.closure ({u, w} : Set G) ⊔ J).subgroupOf H).map π) := by
      rw [hImS]
      exact h2sub.map π
    have hSleH : Subgroup.closure ({u, w} : Set G) ⊔ J ≤ H := sup_le hclHuw hJleH
    have hS2 : IsPGroup 2 ((Subgroup.closure ({u, w} : Set G) ⊔ J : Subgroup G)) :=
      isPGroup_of_map_mk_isPGroup (G := G) (X := Subgroup.closure ({u, w} : Set G) ⊔ J)
        (J := J) (H := H) hSleH hJleH hJnorm hJ2 hS_image
    have hvS : v ∈ Subgroup.closure ({u, w} : Set G) ⊔ J := by
      have hu_cl : u ∈ Subgroup.closure ({u, w} : Set G) :=
        Subgroup.subset_closure (by simp)
      have := (Subgroup.closure ({u, w} : Set G) ⊔ J).mul_mem
        (Subgroup.mem_sup_left hu_cl) (Subgroup.mem_sup_right huv)
      rwa [show u * (u⁻¹ * v) = v by group] at this
    have hwS : w ∈ Subgroup.closure ({u, w} : Set G) ⊔ J :=
      Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
    have : IsPGroup 2 (Subgroup.closure ({v, w} : Set G)) :=
      hS2.to_le ((Subgroup.closure_le _).mpr (by
        rintro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact hvS
        · exact hwS))
    exact hknot (by rwa [hwdef] at this)
  have huw_odd : Odd (orderOf (u * w)) := by
    obtain ⟨Uu, hUu, huUu, -⟩ := mem_dSet.mp hu
    exact seven_three_A hV hTI hE hUu hwU huUu hw_mem huw_not
  obtain ⟨x₁, hx₁mem, hx₁⟩ := exists_conj_inv_mul_of_involutions_odd hu2 hw2 huw_odd
  obtain ⟨x₂, hx₂mem, hx₂⟩ := exists_conj_inv_mul_of_involutions_odd hw2 hv2
    (by rwa [CFSG.RankThree.GF2n.Tim78.orderOf_mul_comm'])
  set x : G := x₁ * x₂ with hxdef
  have hx : x⁻¹ * u * x = v := by
    rw [hxdef, mul_inv_rev]
    calc x₂⁻¹ * x₁⁻¹ * u * (x₁ * x₂) = x₂⁻¹ * (x₁⁻¹ * u * x₁) * x₂ := by group
      _ = x₂⁻¹ * w * x₂ := by rw [hx₁]
      _ = v := hx₂
  have hxX : x ∈ Subgroup.closure ({u, v, w} : Set G) := by
    have h1 : x₁ ∈ Subgroup.closure ({u, v, w} : Set G) :=
      Subgroup.closure_mono (by
        intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
        tauto) hx₁mem
    have h2 : x₂ ∈ Subgroup.closure ({u, v, w} : Set G) :=
      Subgroup.closure_mono (by
        intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
        tauto) hx₂mem
    exact Subgroup.mul_mem _ h1 h2
  have hvSW : v ∈ Subgroup.closure ({u, w} : Set G) ⊔ J := by
    have hu_cl : u ∈ Subgroup.closure ({u, w} : Set G) := Subgroup.subset_closure (by simp)
    have := (Subgroup.closure ({u, w} : Set G) ⊔ J).mul_mem
      (Subgroup.mem_sup_left hu_cl) (Subgroup.mem_sup_right huv)
    rwa [show u * (u⁻¹ * v) = v by group] at this
  have hxSW : x ∈ Subgroup.closure ({u, w} : Set G) ⊔ J := by
    refine (Subgroup.closure_le _).mpr ?_ hxX
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
    · exact hvSW
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
  have hxSW' : x ∈ ((Subgroup.closure ({u, w} : Set G) : Set G) * (J : Set G)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.closure ({u, w} : Set G)) J hclN]
    exact hxSW
  obtain ⟨y, hy, j', hj', hxy⟩ := hxSW'
  have hyc : y⁻¹ * u * y * u⁻¹ ∈ J := by
    have h2 : y⁻¹ * u * y = j' * v * j'⁻¹ := by
      have h := hx
      rw [← hxy] at h
      rw [mul_inv_rev] at h
      calc y⁻¹ * u * y = j' * (j'⁻¹ * y⁻¹ * u * (y * j')) * j'⁻¹ := by group
        _ = j' * v * j'⁻¹ := by rw [h]
    have hvN : v ∈ Subgroup.normalizer (J : Set G) :=
      le_normalizer_of_subgroupOf_normal hJleH hJnorm (hKle hvK)
    have h3 : j' * v * j'⁻¹ * v⁻¹ ∈ J := by
      have hmem : v * j'⁻¹ * v⁻¹ ∈ J :=
        (Subgroup.mem_normalizer_iff.mp hvN j'⁻¹).mp (J.inv_mem hj')
      have := J.mul_mem hj' hmem
      rwa [show j' * (v * j'⁻¹ * v⁻¹) = j' * v * j'⁻¹ * v⁻¹ by group] at this
    have h4 : v * u⁻¹ ∈ J := by
      have := (Subgroup.mem_normalizer_iff.mp hvN (u⁻¹ * v)).mp huv
      rwa [show v * (u⁻¹ * v) * v⁻¹ = v * u⁻¹ by group] at this
    rw [h2, show j' * v * j'⁻¹ * u⁻¹ = (j' * v * j'⁻¹ * v⁻¹) * (v * u⁻¹) by group]
    exact J.mul_mem h3 h4
  have hy_sup : y ∈ Subgroup.zpowers u ⊔ J :=
    mem_sup_zpowers_of_conj_mem_isPGroup hu2 hw2 huw_odd hJ2 hy hyc
  have hzuN : Subgroup.zpowers u ≤ Subgroup.normalizer (J : Set G) :=
    (Subgroup.zpowers_le.mpr huH).trans (le_normalizer_of_subgroupOf_normal hJleH hJnorm)
  have hy_split : y ∈ ((Subgroup.zpowers u : Set G) * (J : Set G)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers u) J hzuN]
    exact hy_sup
  obtain ⟨un, hun, jy, hjy, hy_eq⟩ := hy_split
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hun
  refine ⟨(jy * j')⁻¹, J.inv_mem (J.mul_mem hjy hj'), ?_⟩
  have hyu : y⁻¹ * u * y = jy⁻¹ * u * jy := by
    rw [← hy_eq, ← hn]
    calc (u ^ n * jy)⁻¹ * u * (u ^ n * jy)
        = jy⁻¹ * ((u ^ n)⁻¹ * u * u ^ n) * jy := by group
      _ = jy⁻¹ * u * jy := by rw [inv_zpow_mul_mul_zpow_self]
  have hv_eq : v = (jy * j')⁻¹ * u * (jy * j') := by
    calc v = x⁻¹ * u * x := hx.symm
      _ = (y * j')⁻¹ * u * (y * j') := by rw [← hxy]
      _ = j'⁻¹ * (y⁻¹ * u * y) * j' := by group
      _ = j'⁻¹ * (jy⁻¹ * u * jy) * j' := by rw [hyu]
      _ = (jy * j')⁻¹ * u * (jy * j') := by group
  rw [hv_eq]
  group

theorem seven_three_four_ti {V H E J : Subgroup G}
    (hV : IsElemAbelian 2 V) (hTI : IsTI V) (hE : IsMulCommutative E)
    (hEH : E ≤ H) (hEnorm : (E.subgroupOf H).Normal)
    (hVOm : V ∈ omegaSet V H E) (hOmH : ∀ W ∈ omegaSet V H E, W ≤ H)
    (hJ : J ≤ pCoreOf 2 H) (hJnorm : (J.subgroupOf H).Normal) (hIJ : iSub V H E ≤ J)
    {h : G} (hh : h ∈ H) {a a' : G} (ha : a ∈ V) (haJ : a ∉ J)
    (ha' : a' ∈ conjSubgroup V h) (haJ' : a⁻¹ * a' ∈ J) :
    ∃ x ∈ J, conjSubgroup V h = conjSubgroup V x := by
  have haD : a ∈ dSet V H E := mem_dSet_of_mem_of_not_mem_J hVOm hIJ hJ ha haJ
  have hVhOm : conjSubgroup V h ∈ omegaSet V H E :=
    conjSubgroup_mem_omegaSet hEH hEnorm hVOm hh
  have ha'J : a' ∉ J := by
    intro ha'J'
    apply haJ
    have : a' * (a⁻¹ * a')⁻¹ ∈ J := J.mul_mem ha'J' (J.inv_mem haJ')
    rwa [show a' * (a⁻¹ * a')⁻¹ = a by group] at this
  have ha'D : a' ∈ dSet V H E := mem_dSet_of_mem_of_not_mem_J hVhOm hIJ hJ ha' ha'J
  have hconv : a'⁻¹ * a ∈ J := by
    have := J.inv_mem haJ'
    rwa [mul_inv_rev, inv_inv] at this
  obtain ⟨j, hj, hconj⟩ :=
    seven_three_three hV hTI hE hEH hEnorm hOmH hJ hJnorm ha'D haD hconv
  refine ⟨j, hj, ?_⟩
  have hmem_inf : a' ∈ conjSubgroup V h ⊓ conjSubgroup V j := by
    refine ⟨ha', ?_⟩
    change a' ∈ conjSubgroup V j
    rw [mem_conjSubgroup_iff]
    rw [hconj]
    rw [show j * (j⁻¹ * a * j) * j⁻¹ = a by group]
    exact ha
  have hne : conjSubgroup V h ⊓ conjSubgroup V j ≠ ⊥ := by
    intro hbot
    have h1 : a' = 1 := Subgroup.mem_bot.mp (by rw [← hbot]; exact hmem_inf)
    exact ha'J (by rw [h1]; exact J.one_mem)
  rcases inf_conjSubgroup_eq_bot_or_eq hTI h j with h | h
  · exact absurd h hne
  · exact h

theorem seven_three_four_normalizer {V H E J : Subgroup G}
    (hV : IsElemAbelian 2 V) (hTI : IsTI V) (hE : IsMulCommutative E)
    (hEH : E ≤ H) (hEnorm : (E.subgroupOf H).Normal)
    (hVOm : V ∈ omegaSet V H E) (hOmH : ∀ W ∈ omegaSet V H E, W ≤ H)
    (hJ : J ≤ pCoreOf 2 H) (hJnorm : (J.subgroupOf H).Normal) (hIJ : iSub V H E ≤ J)
    {h : G} (hh : h ∈ H)
    (hNh : h ∈ Subgroup.normalizer ((V ⊔ J : Subgroup G) : Set G)) :
    ∃ m ∈ H ⊓ Subgroup.normalizer (V : Set G), ∃ j ∈ J, h = m * j := by
  have hJleH : J ≤ H := hJ.trans (CFSG.LieType.BorelTits.pCoreOf_le (r := 2) H)
  have hVleH : V ≤ H := hOmH V hVOm
  obtain ⟨g0, hg0, -, hVnotO⟩ := mem_omegaSet.mp hVOm
  have hOleJ : V ⊓ pCoreOf 2 H ≤ J := by
    calc V ⊓ pCoreOf 2 H = V ⊓ iSub V H E := (inf_iSub_eq_inf_pCoreOf hVOm).symm
      _ = V ⊓ J := inf_iSub_eq_inf_J hVOm hIJ hJ
      _ ≤ J := inf_le_right
  have hVnotJ : ¬ V ≤ J := fun hVJ => hVnotO (hVJ.trans hJ)
  obtain ⟨a, haV, haJ⟩ : ∃ a : G, a ∈ V ∧ a ∉ J := by
    by_contra h
    push Not at h
    exact hVnotJ fun x hx => h x hx
  have hahVJ : h⁻¹ * a * h ∈ V ⊔ J := by
    have hconj : conjSubgroup (V ⊔ J) h = V ⊔ J :=
      conjSubgroup_eq_iff_mem_normalizer.mpr hNh
    have hmem : h⁻¹ * a * h ∈ conjSubgroup V h := by
      rw [mem_conjSubgroup_iff]
      rw [show h * (h⁻¹ * a * h) * h⁻¹ = a by group]
      exact haV
    have hle : conjSubgroup V h ≤ conjSubgroup (V ⊔ J) h := Subgroup.map_mono le_sup_left
    rw [hconj] at hle
    exact hle hmem
  have hV_N_J : V ≤ Subgroup.normalizer (J : Set G) :=
    hVleH.trans (le_normalizer_of_subgroupOf_normal hJleH hJnorm)
  have hah' : h⁻¹ * a * h ∈ ((V : Set G) * (J : Set G)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right V J hV_N_J]
    exact hahVJ
  obtain ⟨b, hbV, j, hjJ, hbj⟩ := hah'
  have hbJ : b ∉ J := by
    intro hbJ'
    apply haJ
    have hmem : h⁻¹ * a * h ∈ J := by rw [← hbj]; exact J.mul_mem hbJ' hjJ
    have hNhJ : h ∈ Subgroup.normalizer (J : Set G) :=
      le_normalizer_of_subgroupOf_normal hJleH hJnorm hh
    have := (Subgroup.mem_normalizer_iff.mp hNhJ (h⁻¹ * a * h)).mp hmem
    rwa [show h * (h⁻¹ * a * h) * h⁻¹ = a by group] at this
  have hb'J : b⁻¹ * (h⁻¹ * a * h) ∈ J := by
    rw [← hbj, show b⁻¹ * (b * j) = j by group]
    exact hjJ
  have ha'Vh : h⁻¹ * a * h ∈ conjSubgroup V h := by
    rw [mem_conjSubgroup_iff]
    rw [show h * (h⁻¹ * a * h) * h⁻¹ = a by group]
    exact haV
  obtain ⟨x, hxJ, hxconj⟩ := seven_three_four_ti hV hTI hE hEH hEnorm hVOm hOmH hJ hJnorm
    hIJ hh hbV hbJ ha'Vh hb'J
  refine ⟨h * x⁻¹, ?_, x, hxJ, by group⟩
  refine ⟨H.mul_mem hh (H.inv_mem (hJleH hxJ)), conjSubgroup_eq_iff_mem_normalizer.mp ?_⟩
  rw [← CFSG.Quasithin.conjSubgroup_conjSubgroup, hxconj, CFSG.Quasithin.conjSubgroup_conjSubgroup,
    mul_inv_cancel, CFSG.Quasithin.conjSubgroup_one]

theorem seven_three_five {V H E J R : Subgroup G}
    (hV : IsElemAbelian 2 V) (hTI : IsTI V) (hE : IsMulCommutative E)
    (hEH : E ≤ H) (hEnorm : (E.subgroupOf H).Normal)
    (hVOm : V ∈ omegaSet V H E) (hOmH : ∀ W ∈ omegaSet V H E, W ≤ H)
    (hJ : J ≤ pCoreOf 2 H) (hJnorm : (J.subgroupOf H).Normal) (hIJ : iSub V H E ≤ J)
    (hVbig : 2 < J.relIndex V) (hJR : J ≤ R) (hRH : R ≤ H)
    (hVN : V ≤ Subgroup.normalizer (R : Set G)) (hRodd : Odd (J.relIndex R)) :
    ⁅V, R⁆ ≤ J := by
  have hVleH : V ≤ H := hOmH V hVOm
  have hJleH : J ≤ H := hJ.trans (CFSG.LieType.BorelTits.pCoreOf_le (r := 2) H)
  haveI : (J.subgroupOf H).Normal := hJnorm
  let π : ↥H →* (↥H ⧸ (J.subgroupOf H)) := QuotientGroup.mk' (J.subgroupOf H)
  let Vq : Subgroup (↥H ⧸ (J.subgroupOf H)) := (V.subgroupOf H).map π
  let Rq : Subgroup (↥H ⧸ (J.subgroupOf H)) := (R.subgroupOf H).map π
  have hVH_ea : IsElemAbelian 2 (V.subgroupOf H) :=
    CFSG.Open.IsElemAbelian.comap hV H.subtype_injective
  have hVq_ea : IsElemAbelian 2 Vq := CFSG.Open.IsElemAbelian.map hVH_ea π
  have hcardVq : Nat.card Vq = J.relIndex V := by
    change Nat.card ((V.subgroupOf H).map π) = J.relIndex V
    rw [← Subgroup.relIndex_ker (K := V.subgroupOf H) π]
    rw [show π.ker = J.subgroupOf H from QuotientGroup.ker_mk' (J.subgroupOf H)]
    exact Subgroup.relIndex_subgroupOf hVleH
  have hcardRq : Nat.card Rq = J.relIndex R := by
    change Nat.card ((R.subgroupOf H).map π) = J.relIndex R
    rw [← Subgroup.relIndex_ker (K := R.subgroupOf H) π]
    rw [show π.ker = J.subgroupOf H from QuotientGroup.ker_mk' (J.subgroupOf H)]
    exact Subgroup.relIndex_subgroupOf hRH
  have hVq_isPGroup : IsPGroup 2 Vq :=
    CFSG.CGT.Timmesfeld75.isPGroup_two_of_isElemAbelian hVq_ea
  have hRq_oddNat : Odd (Nat.card Rq) := by rw [hcardRq]; exact hRodd
  have hRq_coprime : Nat.Coprime 2 (Nat.card Rq) :=
    Nat.coprime_comm.mpr (Nat.coprime_two_right.mpr hRq_oddNat)
  have hrankV : 2 ^ 2 ≤ Nat.card Vq := by
    obtain ⟨nv, hnv⟩ := (IsPGroup.iff_card (p := 2) (G := Vq)).mp hVq_isPGroup
    have hbig : 2 < 2 ^ nv := by rw [← hnv]; rwa [hcardVq]
    have hnv2 : 2 ≤ nv := by
      by_contra h
      interval_cases nv <;> simp at hbig
    calc 2 ^ 2 ≤ 2 ^ nv := Nat.pow_le_pow_right (by norm_num) hnv2
      _ = Nat.card Vq := hnv.symm
  have hcommVHRH : ⁅V.subgroupOf H, R.subgroupOf H⁆ ≤ R.subgroupOf H := by
    rw [Subgroup.commutator_le]
    intro v hv r hr
    rw [Subgroup.mem_subgroupOf] at hv hr ⊢
    have hvN : (v : G) ∈ Subgroup.normalizer (R : Set G) := hVN hv
    have hvr : (v : G) * (r : G) * (v : G)⁻¹ ∈ R :=
      (Subgroup.mem_normalizer_iff.mp hvN (r : G)).mp hr
    simpa [commutatorElement_def] using R.mul_mem hvr (R.inv_mem hr)
  have hVqN : Vq ≤ Subgroup.normalizer (Rq : Set (↥H ⧸ (J.subgroupOf H))) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_right]
    change ⁅(V.subgroupOf H).map π, (R.subgroupOf H).map π⁆ ≤ (R.subgroupOf H).map π
    rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono hcommVHRH
  have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity
    (G := ↥H ⧸ (J.subgroupOf H)) (p := 2) Nat.prime_two hVq_ea hrankV hVqN hRq_coprime
  have hRqN : Rq ≤ Subgroup.normalizer (Vq : Set (↥H ⧸ (J.subgroupOf H))) := by
    rw [← hgen]
    refine iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => ?_
    intro g hg
    obtain ⟨hgR, hgC⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨bH, hbH, hba⟩ := Subgroup.mem_map.mp ha
    obtain ⟨rH, hrH, hrg⟩ := Subgroup.mem_map.mp hgR
    subst hba
    subst hrg
    have hbJ : (bH : G) ∉ J := by
      intro hbJ'
      apply ha1
      change (bH : ↥H ⧸ (J.subgroupOf H)) = 1
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hbJ'
    have hcommQ : (π rH)⁻¹ * π bH * π rH = π bH := by
      have h1 : π bH * π rH = π rH * π bH :=
        Subgroup.mem_centralizer_iff.mp hgC (π bH) (Set.mem_singleton _)
      calc (π rH)⁻¹ * π bH * π rH = (π rH)⁻¹ * (π bH * π rH) := by group
        _ = (π rH)⁻¹ * (π rH * π bH) := by rw [h1]
        _ = π bH := by group
    have hq : ((rH⁻¹ * bH * rH : ↥H) : ↥H ⧸ (J.subgroupOf H)) =
        (bH : ↥H ⧸ (J.subgroupOf H)) := by
      change π (rH⁻¹ * bH * rH) = π bH
      rw [map_mul, map_mul, map_inv]
      exact hcommQ
    have hmemJ : (rH : G)⁻¹ * (bH : G) * (rH : G) * (bH : G)⁻¹ ∈ J := by
      have h := QuotientGroup.eq_iff_div_mem.mp hq
      rw [div_eq_mul_inv] at h
      simpa [Subgroup.mem_subgroupOf, mul_assoc] using h
    have hmemJ' : (bH : G)⁻¹ * ((rH : G)⁻¹ * (bH : G) * (rH : G)) ∈ J := by
      have hbN : (bH : G) ∈ Subgroup.normalizer (J : Set G) :=
        le_normalizer_of_subgroupOf_normal hJleH hJnorm bH.2
      have hbiN : (bH : G)⁻¹ ∈ Subgroup.normalizer (J : Set G) :=
        (Subgroup.normalizer (J : Set G)).inv_mem hbN
      have := (Subgroup.mem_normalizer_iff.mp hbiN
        ((rH : G)⁻¹ * (bH : G) * (rH : G) * (bH : G)⁻¹)).mp hmemJ
      rwa [show (bH : G)⁻¹ * ((rH : G)⁻¹ * (bH : G) * (rH : G) * (bH : G)⁻¹) *
          (bH : G)⁻¹⁻¹ =
        (bH : G)⁻¹ * ((rH : G)⁻¹ * (bH : G) * (rH : G)) by group] at this
    have hbV : (bH : G) ∈ V := Subgroup.mem_subgroupOf.mp hbH
    have ha' : (rH : G)⁻¹ * (bH : G) * (rH : G) ∈ conjSubgroup V (rH : G) := by
      rw [mem_conjSubgroup_iff]
      rw [show (rH : G) * ((rH : G)⁻¹ * (bH : G) * (rH : G)) * (rH : G)⁻¹ = (bH : G) by group]
      exact hbV
    obtain ⟨x, hxJ, hxconj⟩ := seven_three_four_ti hV hTI hE hEH hEnorm hVOm hOmH hJ hJnorm hIJ
      rH.2 hbV hbJ ha' hmemJ'
    have hxH : ∃ xH : ↥H, (xH : G) = x := ⟨⟨x, hJleH hxJ⟩, rfl⟩
    obtain ⟨xH, rfl⟩ := hxH
    have hx1 : π xH = 1 := by
      change (xH : ↥H ⧸ (J.subgroupOf H)) = 1
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hxJ
    have hVqconj : conjSubgroup Vq (π rH) = Vq := by
      have heqH : conjSubgroup (V.subgroupOf H) rH = conjSubgroup (V.subgroupOf H) xH := by
        refine Subgroup.map_injective H.subtype_injective ?_
        rw [map_conjSubgroup_subgroupOf' hVleH rH.2,
          map_conjSubgroup_subgroupOf' hVleH xH.2, hxconj]
      have hmap1 : conjSubgroup Vq (π rH) = (conjSubgroup (V.subgroupOf H) rH).map π := by
        change conjSubgroup ((V.subgroupOf H).map π) (π rH) = _
        exact map_conjSubgroup_hom π (V.subgroupOf H) rH
      have hmap2 : (conjSubgroup (V.subgroupOf H) rH).map π =
          (conjSubgroup (V.subgroupOf H) xH).map π := by rw [heqH]
      have hmap3 : (conjSubgroup (V.subgroupOf H) xH).map π = Vq := by
        change (conjSubgroup (V.subgroupOf H) xH).map π = (V.subgroupOf H).map π
        rw [← map_conjSubgroup_hom π (V.subgroupOf H) xH, hx1, CFSG.Quasithin.conjSubgroup_one]
      rw [hmap1, hmap2, hmap3]
    exact (conjSubgroup_eq_iff_mem_normalizer).mp hVqconj
  have hcomm2 : ⁅Vq, Rq⁆ ≤ Vq :=
    (Subgroup.le_normalizer_iff_commutator_le_left).mp hRqN
  have hcomm1 : ⁅Vq, Rq⁆ ≤ Rq :=
    (Subgroup.le_normalizer_iff_commutator_le_right).mp hVqN
  have hVqRq_bot : Vq ⊓ Rq = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxV : x ∈ Vq := (Subgroup.mem_inf.mp hx).1
    have hxR : x ∈ Rq := (Subgroup.mem_inf.mp hx).2
    refine eq_one_of_mem_isPGroup_of_odd hVq_isPGroup hxV ?_
    have hdvd : orderOf x ∣ Nat.card Rq := by
      have := orderOf_dvd_natCard (⟨x, hxR⟩ : Rq)
      rwa [Subgroup.orderOf_mk] at this
    exact hRq_oddNat.of_dvd_nat hdvd
  have hcomm_bot : ⁅Vq, Rq⁆ = ⊥ := by
    apply le_bot_iff.mp
    calc ⁅Vq, Rq⁆ ≤ Vq ⊓ Rq := le_inf hcomm2 hcomm1
      _ = ⊥ := hVqRq_bot
  rw [Subgroup.commutator_le]
  intro v hv r hr
  have hvq : π ⟨v, hVleH hv⟩ ∈ Vq :=
    Subgroup.mem_map.mpr ⟨⟨v, hVleH hv⟩, Subgroup.mem_subgroupOf.mpr hv, rfl⟩
  have hrq : π ⟨r, hRH hr⟩ ∈ Rq :=
    Subgroup.mem_map.mpr ⟨⟨r, hRH hr⟩, Subgroup.mem_subgroupOf.mpr hr, rfl⟩
  have hcommq : ⁅π ⟨v, hVleH hv⟩, π ⟨r, hRH hr⟩⁆ = 1 := by
    have hmem : ⁅π ⟨v, hVleH hv⟩, π ⟨r, hRH hr⟩⁆ ∈ (⊥ : Subgroup (↥H ⧸ (J.subgroupOf H))) := by
      rw [← hcomm_bot]
      exact Subgroup.commutator_mem_commutator hvq hrq
    exact Subgroup.mem_bot.mp hmem
  have hq : ((⁅(⟨v, hVleH hv⟩ : ↥H), (⟨r, hRH hr⟩ : ↥H)⁆ : ↥H) :
      ↥H ⧸ (J.subgroupOf H)) = 1 := by
    change π (⁅(⟨v, hVleH hv⟩ : ↥H), (⟨r, hRH hr⟩ : ↥H)⁆) = 1
    rw [map_commutatorElement]
    exact hcommq
  have hmem : (⁅(⟨v, hVleH hv⟩ : ↥H), (⟨r, hRH hr⟩ : ↥H)⁆ : ↥H) ∈ J.subgroupOf H :=
    (QuotientGroup.eq_one_iff _).mp hq
  rw [Subgroup.mem_subgroupOf] at hmem
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def] using hmem

end CFSG.LocalAnalysis.WeakClosure81