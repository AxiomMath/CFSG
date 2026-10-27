module

public import CFSG.RankThree.GF2n.Parrott.CaseII
public import CFSG.RankThree.GF2n.Parrott.J1Sub
public import CFSG.RankThree.GF2n.Parrott.OmegaOneSylow
public import CFSG.RankThree.GF2n.Parrott.ZFusionControl
import all CFSG.RankThree.GF2n.Parrott.ZFusionControl
public import CFSG.RankThree.GF2n.Parrott.Section2Products
public import CFSG.GroupTheory.CentralizerSylowFusion
public import CFSG.GroupTheory.ConjTransport
public import CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialInvolutionDoubleCentralizer
public import CFSG.GroupTheory.SmallFixedTwoGroup.LemmaAIndex
public import TauCeti.Algebra.Group.Subgroup.ZPowers
public import CFSG.GroupTheory.ExtraspecialInvolutionIndexTwo

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

theorem parrott_cases_facts
    (h : Tim79a.ParrottHyp z ∨ Tim79a.ParrottHypA z ∨ Tim79a.ParrottHypA1 z) :
    orderOf z = 2 ∧ z ∈ J z ∧ ⁅J z, J z⁆ = Subgroup.zpowers z ∧
      H z ⊓ Subgroup.centralizer (J z : Set G) ≤ J z ∧
      ∀ x ∈ J z, x * x ∈ centerIn (J z) := by
  have hA : CFSG.LargeExtraspecial.Timmesfeld.IsExtraspecial2 (J z) →
      ⁅J z, J z⁆ = Subgroup.zpowers z →
      H z ⊓ Subgroup.centralizer (J z : Set G) ≤ J z →
      orderOf z = 2 ∧ z ∈ J z ∧ ⁅J z, J z⁆ = Subgroup.zpowers z ∧
        H z ⊓ Subgroup.centralizer (J z : Set G) ≤ J z ∧
        ∀ x ∈ J z, x * x ∈ centerIn (J z) := by
    intro hE hJ' hCH
    refine ⟨?_, ?_, hJ', hCH, ?_⟩
    · have hcard : Nat.card (Subgroup.zpowers z) = 2 := by
        rw [← hJ']
        exact hE.2.2
      rwa [Nat.card_zpowers] at hcard
    · have hz : z ∈ ⁅J z, J z⁆ := by
        rw [hJ']
        exact Subgroup.mem_zpowers z
      exact Subgroup.commutator_le_self (J z) hz
    · intro x hx
      have hsq := CFSG.IsExtraspecial2.pow_two_mem_center hE ⟨x, hx⟩
      rw [centerIn_eq_map_center]
      exact Subgroup.mem_map.mpr ⟨_, hsq, by simp [pow_two]⟩
  rcases h with h | h | h
  · exact ⟨h.1, z_mem_J h, h.2.2.1, h.2.2.2.1, fun x hx => sq_mem_centerIn_J h hx⟩
  · exact hA h.extraspecial h.commutator h.centralizer_le
  · exact hA h.extraspecial h.commutator h.centralizer_le

private theorem centerIn_J_eq_zpowers_of_A (h : Tim79a.ParrottHypA z ∨ Tim79a.ParrottHypA1 z) :
    centerIn (J z) = Subgroup.zpowers z ∧ orderOf z = 2 := by
  rcases h with h | h
  · exact ⟨centerIn_J_eq_zpowers_A h, orderOf_z_A h⟩
  · refine ⟨by rw [CFSG.centerIn_eq_map_center, ← h.extraspecial.2.1, h.commutator], ?_⟩
    have hcard : Nat.card (Subgroup.zpowers z) = 2 := by
      rw [← h.commutator]
      exact h.extraspecial.2.2
    rwa [Nat.card_zpowers] at hcard

private theorem omega_one_center_le_of_isExtraspecial2
    (hE : CFSG.LargeExtraspecial.Timmesfeld.IsExtraspecial2 (J z))
    (hJ' : ⁅J z, J z⁆ = Subgroup.zpowers z)
    (hCH : H z ⊓ Subgroup.centralizer (J z : Set G) ≤ J z) {j : J z}
    {K : Subgroup ↥(H z)}
    (hCK : (Subgroup.centralizer ({j} : Set (J z))).map
      (Subgroup.inclusion (J_le_H (z := z))) ≤ K)
    {w : ↥(H z)} (hwK : w ∈ Subgroup.centralizer (K : Set ↥(H z)))
    (hw2 : (w : G) ^ 2 = 1) :
    (w : G) ∈ Subgroup.zpowers (j : G) ⊔ (Subgroup.center (J z)).map (J z).subtype := by
  have hwc : ∀ c ∈ Subgroup.centralizer ({j} : Set (J z)),
      (c : G) * (w : G) = (w : G) * (c : G) := by
    intro c hc
    have hcK : Subgroup.inclusion (J_le_H (z := z)) c ∈ K := hCK (Subgroup.mem_map_of_mem _ hc)
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hwK _ hcK)
  by_cases hwJ : (w : G) ∈ J z
  ·
    let wJ : J z := ⟨(w : G), hwJ⟩
    have hP := CFSG.IsExtraspecial2.toIsExtraspecialPGroup hE
    have hSetup : CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialInvolutionDoubleCentralizer.Setup
        ↥(J z) :=
      ⟨hP.2.2.2, fun x y => by
        rw [← hP.2.1, _root_.commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)⟩
    have hmem : wJ ∈ Subgroup.zpowers j ⊔ Subgroup.center (J z) := by
      by_contra hnot
      obtain ⟨x, hxS, hxw⟩ :=
        CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialInvolutionDoubleCentralizer.key
          hSetup (Subgroup.zpowers j ⊔ Subgroup.center (J z)) le_sup_right wJ hnot
      apply hxw
      have hxj : x ∈ Subgroup.centralizer ({j} : Set (J z)) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact commutatorElement_eq_one_iff_mul_comm.mp
          (hxS j (Subgroup.mem_sup_left (Subgroup.mem_zpowers j)))
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact Subtype.ext (hwc x hxj)
    have hmap := Subgroup.mem_map_of_mem (J z).subtype hmem
    rwa [Subgroup.map_sup, MonoidHom.map_zpowers] at hmap
  ·
    exfalso
    have hz2 : orderOf z = 2 := by
      have hcard : Nat.card (Subgroup.zpowers z) = 2 := by
        rw [← hJ']
        exact hE.2.2
      rwa [Nat.card_zpowers] at hcard
    have hzJ : z ∈ J z := by
      have hz : z ∈ ⁅J z, J z⁆ := by
        rw [hJ']
        exact Subgroup.mem_zpowers z
      exact Subgroup.commutator_le_self (J z) hz
    have hHN : H z ≤ Subgroup.normalizer (J z : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (J_le_H (z := z))).mp
        (J_subgroupOf_normal z)
    have hsq : (w : G) ^ 2 ∈ Subgroup.centralizer (J z : Set G) := by
      rw [hw2]
      exact Subgroup.one_mem _
    apply CFSG.GroupTheory.relIndex_centralizer_ne_two_of_sq_mem_centralizer hE
      (J_le_H (z := z)) hHN hCH w.2 hwJ hsq
    have hle : Subgroup.centralizer ({j} : Set (J z)) ≤
        (Subgroup.centralizer ({(w : G)} : Set G)).subgroupOf (J z) := by
      intro c hc
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
      exact hwc c hc
    have hidx : (Subgroup.centralizer ({j} : Set (J z))).index ≤ 2 := by
      apply CFSG.GroupTheory.SmallFixedTwoGroup.index_centralizer_le_two
        (z := (⟨z, hzJ⟩ : J z))
      intro g
      have hc : ((⁅g, j⁆ : J z) : G) ∈ Subgroup.zpowers z := by
        rw [← hJ']
        exact Subgroup.commutator_mem_commutator g.2 j.2
      have hgj : g * j * g⁻¹ = ⁅g, j⁆ * j := by
        rw [commutatorElement_def]
        group
      rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hz2).mp hc with h1 | h1
      · left
        rw [hgj, show ⁅g, j⁆ = 1 from Subtype.ext h1, one_mul]
      · right
        rw [hgj, show ⁅g, j⁆ = (⟨z, hzJ⟩ : J z) from Subtype.ext h1]
    have hne1 : ((Subgroup.centralizer ({(w : G)} : Set G)).subgroupOf (J z)).index ≠ 1 := by
      intro h1
      apply hwJ
      refine hCH (Subgroup.mem_inf.mpr ⟨w.2, ?_⟩)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy' : (⟨y, hy⟩ : J z) ∈
          (Subgroup.centralizer ({(w : G)} : Set G)).subgroupOf (J z) := by
        rw [Subgroup.index_eq_one.mp h1]
        exact Subgroup.mem_top _
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff] at hy'
      exact hy'
    have hdvd := Subgroup.index_dvd_of_le hle
    have hj0 : (Subgroup.centralizer ({j} : Set (J z))).index ≠ 0 :=
      Subgroup.index_ne_zero_of_finite
    have hw0 : ((Subgroup.centralizer ({(w : G)} : Set G)).subgroupOf (J z)).index ≠ 0 :=
      Subgroup.index_ne_zero_of_finite
    have hwle := Nat.le_of_dvd (Nat.pos_of_ne_zero hj0) hdvd
    change ((Subgroup.centralizer ({(w : G)} : Set G)).subgroupOf (J z)).index = 2
    omega

theorem omega_one_center_le_cases
    (h : Tim79a.ParrottHyp z ∨ Tim79a.ParrottHypA z ∨ Tim79a.ParrottHypA1 z) {j : J z}
    (hj : j ∉ Subgroup.center (J z)) {K : Subgroup ↥(H z)}
    (hCK : (Subgroup.centralizer ({j} : Set (J z))).map
      (Subgroup.inclusion (J_le_H (z := z))) ≤ K)
    {w : ↥(H z)} (hwK : w ∈ Subgroup.centralizer (K : Set ↥(H z)))
    (hw2 : (w : G) ^ 2 = 1) :
    (w : G) ∈ Subgroup.zpowers (j : G) ⊔ (Subgroup.center (J z)).map (J z).subtype := by
  rcases h with h | h | h
  · exact omega_one_center_le h hj hCK hwK hw2
  · exact omega_one_center_le_of_isExtraspecial2 h.extraspecial h.commutator h.centralizer_le
      hCK hwK hw2
  · exact omega_one_center_le_of_isExtraspecial2 h.extraspecial h.commutator h.centralizer_le
      hCK hwK hw2

private theorem conj_z_mem_centerIn_eq_cases
    (h : Tim79a.ParrottHyp z ∨ Tim79a.ParrottHypA z ∨ Tim79a.ParrottHypA1 z)
    (hF : NormalizerControlsCenterJFusion z) {g : G}
    (hg : g * z * g⁻¹ ∈ centerIn (J z)) : g * z * g⁻¹ = z := by
  rcases h with h | hA
  · exact conj_z_mem_centerIn_eq h hF hg
  · obtain ⟨hZ, hz2⟩ := centerIn_J_eq_zpowers_of_A hA
    rw [hZ] at hg
    rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hz2).mp hg with h1 | h1
    · exfalso
      have hz : z = 1 := by
        calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
          _ = 1 := by rw [h1]; group
      simp [hz] at hz2
    · exact h1

theorem involution_mem_centerIn_of_mem_secondDerived_cases
    (h : Tim79a.ParrottHyp z ∨ Tim79a.ParrottHypA z ∨ Tim79a.ParrottHypA1 z)
    {J₁ : Subgroup G} (hZJ₁ : centerIn (J z) ≤ J₁) {j : J z}
    (hjZ : j ∉ Subgroup.center (J z)) (hj1 : (j : G) ∉ J₁)
    (hder : ⁅H z, ⁅H z, H z⁆⁆ ⊓ J z ≤ J₁)
    {K : Subgroup ↥(H z)}
    (hCK : (Subgroup.centralizer ({j} : Set (J z))).map
      (Subgroup.inclusion (J_le_H (z := z))) ≤ K)
    {x : ↥(H z)} (hx : x ∈ ⁅K, ⁅K, K⁆⁆)
    (hxc : x ∈ Subgroup.centralizer (K : Set ↥(H z)))
    (hx2 : (x : G) ^ 2 = 1) :
    (x : G) ∈ centerIn (J z) := by
  have hxH' : (x : G) ∈ ⁅H z, ⁅H z, H z⁆⁆ := by
    have hxmap : (x : G) ∈ (⁅K, ⁅K, K⁆⁆).map (H z).subtype :=
      Subgroup.mem_map_of_mem (H z).subtype hx
    rw [Subgroup.map_commutator] at hxmap
    have hK' : (⁅K, K⁆).map (H z).subtype ≤ ⁅H z, H z⁆ := by
      rw [Subgroup.map_commutator]
      exact Subgroup.commutator_mono (Subgroup.map_subtype_le _) (Subgroup.map_subtype_le _)
    exact Subgroup.commutator_mono (Subgroup.map_subtype_le _) hK' hxmap
  have hxsup : (x : G) ∈ Subgroup.zpowers (j : G) ⊔
      (Subgroup.center (J z)).map (J z).subtype :=
    omega_one_center_le_cases h hjZ hCK hxc hx2
  have hxJ : (x : G) ∈ J z := by
    have hsupJ : Subgroup.zpowers (j : G) ⊔
        (Subgroup.center (J z)).map (J z).subtype ≤ J z :=
      sup_le (Subgroup.zpowers_le.mpr j.2) (Subgroup.map_subtype_le _)
    exact hsupJ hxsup
  have hxinf : (x : G) ∈ (Subgroup.zpowers (j : G) ⊔ centerIn (J z)) ⊓ J₁ := by
    refine Subgroup.mem_inf.mpr ⟨?_, hder ⟨hxH', hxJ⟩⟩
    rwa [centerIn_eq_map_center]
  have hEq := sup_zpowers_center_inf_eq (parrott_cases_facts h).2.2.2.2 hZJ₁ hj1
  rwa [hEq] at hxinf

theorem conj_z_eq_of_mem_normalizer_cases
    (h : Tim79a.ParrottHyp z ∨ Tim79a.ParrottHypA z ∨ Tim79a.ParrottHypA1 z)
    {J₁ : Subgroup G} (hZJ₁ : centerIn (J z) ≤ J₁) {j : J z}
    (hjZ : j ∉ Subgroup.center (J z)) (hj1 : (j : G) ∉ J₁)
    (hder : ⁅H z, ⁅H z, H z⁆⁆ ⊓ J z ≤ J₁)
    (hF : NormalizerControlsCenterJFusion z)
    {K : Subgroup ↥(H z)}
    (hCK : (Subgroup.centralizer ({j} : Set (J z))).map
      (Subgroup.inclusion (J_le_H (z := z))) ≤ K)
    (hZ : Subgroup.zpowers z ≤ ⁅K, ⁅K, K⁆⁆.map (H z).subtype)
    {n : G} (hn : n ∈ Subgroup.normalizer ((K.map (H z).subtype) : Set G)) :
    n * z * n⁻¹ = z := by
  have hzo : orderOf z = 2 := (parrott_cases_facts h).1
  let K' : Subgroup ↥(H z) := ⁅K, K⁆
  let K'' : Subgroup ↥(H z) := ⁅K, ⁅K, K⁆⁆
  have hzK'' : z ∈ K''.map (H z).subtype :=
    hZ (Subgroup.mem_zpowers z)
  have hzK : (⟨z, z_mem_H (z := z)⟩ : ↥(H z)) ∈ K := by
    have hzJ : z ∈ J z := (parrott_cases_facts h).2.1
    have hzCJ : (⟨z, hzJ⟩ : J z) ∈ Subgroup.centralizer ({j} : Set (J z)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp (z_centralizes_H_A (z := z))
        (j : G) (J_le_H j.2)).symm)
    have hzmap : (Subgroup.inclusion (J_le_H (z := z)) ⟨z, hzJ⟩ : ↥(H z)) ∈
        (Subgroup.centralizer ({j} : Set (J z))).map
          (Subgroup.inclusion (J_le_H (z := z))) :=
      Subgroup.mem_map_of_mem _ hzCJ
    exact hCK hzmap
  have hKmap_norm : (K.map (H z).subtype).map (MulAut.conj n).toMonoidHom =
      K.map (H z).subtype :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hn
  have hK'norm : (K'.map (H z).subtype).map (MulAut.conj n).toMonoidHom =
      K'.map (H z).subtype := by
    change ((⁅K, K⁆).map (H z).subtype).map (MulAut.conj n).toMonoidHom =
      (⁅K, K⁆).map (H z).subtype
    rw [Subgroup.map_commutator, Subgroup.map_commutator, hKmap_norm]
  have hK''norm : (K''.map (H z).subtype).map (MulAut.conj n).toMonoidHom =
      K''.map (H z).subtype := by
    change ((⁅K, K'⁆).map (H z).subtype).map (MulAut.conj n).toMonoidHom =
      (⁅K, K'⁆).map (H z).subtype
    rw [Subgroup.map_commutator, Subgroup.map_commutator, hKmap_norm, hK'norm]
  have hzK''n : n * z * n⁻¹ ∈ K''.map (H z).subtype := by
    have hmem : (MulAut.conj n) z ∈
        (K''.map (H z).subtype).map (MulAut.conj n).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hzK''
    rw [hK''norm] at hmem
    simpa [MulAut.conj_apply] using hmem
  have hzKmap : n * z * n⁻¹ ∈ K.map (H z).subtype := by
    have hmem : (MulAut.conj n) z ∈
        (K.map (H z).subtype).map (MulAut.conj n).toMonoidHom :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hzK)
    rw [hKmap_norm] at hmem
    simpa [MulAut.conj_apply] using hmem
  have hznH : n * z * n⁻¹ ∈ H z :=
    Subgroup.map_subtype_le _ hzKmap
  have hzKcenter : n * z * n⁻¹ ∈
      Subgroup.centralizer ((K.map (H z).subtype) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hk' : n⁻¹ * k * n ∈ K.map (H z).subtype := by
      have hmem : (MulAut.conj n⁻¹) k ∈
          (K.map (H z).subtype).map (MulAut.conj n⁻¹).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hk
      have hKmap_norm_inv : (K.map (H z).subtype).map
          (MulAut.conj n⁻¹).toMonoidHom = K.map (H z).subtype :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (inv_mem hn)
      rw [hKmap_norm_inv] at hmem
      simpa [MulAut.conj_apply] using hmem
    have hzc : (n⁻¹ * k * n) * z = z * (n⁻¹ * k * n) :=
      Subgroup.mem_centralizer_iff.mp (z_centralizes_H_A (z := z)) _
        (Subgroup.map_subtype_le _ hk')
    calc k * (n * z * n⁻¹)
        = n * ((n⁻¹ * k * n) * z) * n⁻¹ := by group
      _ = n * (z * (n⁻¹ * k * n)) * n⁻¹ := by rw [hzc]
      _ = (n * z * n⁻¹) * k := by group
  have hz2 : z ^ 2 = 1 := by
    rw [← hzo]
    exact pow_orderOf_eq_one z
  have hx2 : (n * z * n⁻¹) ^ 2 = 1 := by
    rw [pow_two]
    calc n * z * n⁻¹ * (n * z * n⁻¹) = n * (z * z) * n⁻¹ := by group
      _ = n * z ^ 2 * n⁻¹ := by rw [pow_two]
      _ = 1 := by rw [hz2]; group
  let x : ↥(H z) := ⟨n * z * n⁻¹, hznH⟩
  have hxK'' : x ∈ K'' := by
    rw [← Subgroup.mem_map_iff_mem (H z).subtype_injective (K := K'')]
    simpa [x] using hzK''n
  have hxc : x ∈ Subgroup.centralizer (K : Set ↥(H z)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subtype.ext (hzKcenter (k : G) (Subgroup.mem_map_of_mem _ hk))
  have hmem : (x : G) ∈ centerIn (J z) :=
    involution_mem_centerIn_of_mem_secondDerived_cases h hZJ₁ hjZ hj1 hder hCK
      (by simpa [K''] using hxK'') hxc hx2
  simpa [x] using conj_z_mem_centerIn_eq_cases h hF hmem

theorem no_conj_z_eq_of_mem_J_minus_J1_cases
    (h : Tim79a.ParrottHyp z ∨ Tim79a.ParrottHypA z ∨ Tim79a.ParrottHypA1 z)
    {J₁ : Subgroup G} (hZJ₁ : centerIn (J z) ≤ J₁) {j : J z}
    (hjZ : j ∉ Subgroup.center (J z)) (hj1 : (j : G) ∉ J₁)
    (hder : ⁅H z, ⁅H z, H z⁆⁆ ⊓ J z ≤ J₁)
    (hF : NormalizerControlsCenterJFusion z)
    {K : Subgroup ↥(H z)}
    (hCK : (Subgroup.centralizer ({j} : Set (J z))).map
      (Subgroup.inclusion (J_le_H (z := z))) ≤ K)
    (hKS : IsSylowOf 2 (K.map (H z).subtype)
      (H z ⊓ Subgroup.centralizer ({(j : G)} : Set G)))
    (hZ : Subgroup.zpowers z ≤ ⁅K, ⁅K, K⁆⁆.map (H z).subtype) :
    ∀ g : G, g * z * g⁻¹ ≠ (j : G) := by
  have hJp : IsPGroup 2 (J z) := (pCore_isPGroup (p := 2) (G := ↥(H z))).map (H z).subtype
  have hHN : H z ≤ Subgroup.normalizer (J z : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (J_le_H (z := z))).mp (J_subgroupOf_normal z)
  have hJy : ¬ J z ≤ Subgroup.centralizer ({(j : G)} : Set G) := by
    intro hle
    have hjc : (j : G) ∈ Subgroup.centralizer (J z : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
    have hmem : (j : G) ∈ centerIn (J z) := Subgroup.mem_inf.mpr ⟨j.2, hjc⟩
    have hjcenter : j ∈ Subgroup.center (J z) := by
      rw [← QuotientV.centerIn_subgroupOf_eq_center]
      exact Subgroup.mem_subgroupOf.mpr hmem
    exact hjZ hjcenter
  have hdvd : 2 ∣ (Subgroup.centralizer ({z} : Set G) ⊓
      Subgroup.centralizer ({(j : G)} : Set G)).relIndex
      (Subgroup.centralizer ({z} : Set G)) := by
    have h := CFSG.GroupTheory.dvd_relIndex_inf_centralizer_of_normal_pGroup
      (p := 2) (H := H z) (J := J z) (y := (j : G)) (J_le_H (z := z)) hHN hJp hJy
    simpa [H] using h
  have hN : ∀ g ∈ Subgroup.centralizer ({(j : G)} : Set G),
      g ∈ Subgroup.normalizer ((K.map (H z).subtype) : Set G) →
      IsPGroup 2 (Subgroup.zpowers g) → g ∈ Subgroup.centralizer ({z} : Set G) := by
    intro g _ hgn _
    have hgz : g * z * g⁻¹ = z :=
      conj_z_eq_of_mem_normalizer_cases h hZJ₁ hjZ hj1 hder hF hCK hZ hgn
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * z = (g * z * g⁻¹) * g := by group
      _ = z * g := by rw [hgz]
  have hnot : ¬ IsConj z (j : G) :=
    CFSG.GroupTheory.not_isConj_of_isSylowOf_inf_centralizer
      (p := 2) (z := z) (y := (j : G)) (K := K.map (H z).subtype)
      (by simpa [H] using hKS) hN (by simpa [H] using hdvd)
  intro g hg
  exact hnot (isConj_iff.mpr ⟨g, hg⟩)

theorem false_of_involution_centralizer_eq_center_gen {J₁ : Subgroup G} {j : J z}
    {B : Subgroup G}
    (hjZ : j ∉ Subgroup.center (J z))
    (hj1 : (j : G) ∈ J₁)
    (hjB : (j : G) ∈ Subgroup.centralizer (B : Set G))
    (hx_exists : ∃ x : G, x ∈ H z ∧ x ∉ J z ∧ orderOf x = 2 ∧
      x * (j : G) = (j : G) * x ∧ x ∈ Subgroup.centralizer (B : Set G))
    (hx : ∀ x : G, x ∈ H z → x ∉ J z → orderOf x = 2 →
      x ∈ Subgroup.centralizer (B : Set G) →
      Subgroup.centralizer ({x} : Set G) ⊓ (J₁ ⊓ Subgroup.centralizer (B : Set G)) =
      centerIn (J z)) :
    False := by
  obtain ⟨x, hxH, hxJ, hx2, hxj, hxB⟩ := hx_exists
  have hxmem : (j : G) ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hxj.symm
  have hjinf : (j : G) ∈ J₁ ⊓ Subgroup.centralizer (B : Set G) :=
    Subgroup.mem_inf.mpr ⟨hj1, hjB⟩
  have hjcenterIn : (j : G) ∈ centerIn (J z) := by
    rw [← hx x hxH hxJ hx2 hxB]
    exact Subgroup.mem_inf.mpr ⟨hxmem, hjinf⟩
  have hjcenter : j ∈ Subgroup.center (J z) := by
    rw [← QuotientV.centerIn_subgroupOf_eq_center]
    exact Subgroup.mem_subgroupOf.mpr hjcenterIn
  exact hjZ hjcenter

theorem no_conj_z_eq_of_mem_J1_minus_centerJ_gen {J₁ : Subgroup G} {j : J z}
    (hj2 : orderOf (j : G) = 2) (hjZ : j ∉ Subgroup.center (J z))
    {B : Subgroup G}
    (hconjB : ∃ k : ↥(H z),
      k * (j : G) * k⁻¹ ∈ J z ∧
      k * (j : G) * k⁻¹ ∈ J₁ ∧
      k * (j : G) * k⁻¹ ∈ Subgroup.centralizer (B : Set G))
    (hP7 : (∃ g : G, g * z * g⁻¹ = (j : G)) →
      ∀ k : ↥(H z),
        k * (j : G) * k⁻¹ ∈ J z →
        k * (j : G) * k⁻¹ ∈ J₁ →
        k * (j : G) * k⁻¹ ∈ Subgroup.centralizer (B : Set G) →
        orderOf (k * (j : G) * k⁻¹) = 2 →
        ∃ x : G, x ∈ H z ∧ x ∉ J z ∧ orderOf x = 2 ∧
          x * (k * (j : G) * k⁻¹) = (k * (j : G) * k⁻¹) * x ∧
          x ∈ Subgroup.centralizer (B : Set G))
    (hx : ∀ x : G, x ∈ H z → x ∉ J z → orderOf x = 2 →
      x ∈ Subgroup.centralizer (B : Set G) →
      Subgroup.centralizer ({x} : Set G) ⊓ (J₁ ⊓ Subgroup.centralizer (B : Set G)) =
      centerIn (J z)) :
    ∀ g : G, g * z * g⁻¹ ≠ (j : G) := by
  intro g hg
  obtain ⟨k, hkJ, hkJ1, hkB⟩ := hconjB
  have hcenter_conj : ∀ {k' : G}, k' ∈ H z → ∀ {y : G},
      y ∈ centerIn (J z) → k' * y * k'⁻¹ ∈ centerIn (J z) := by
    intro k' hk' y hy
    have hk'N : k' ∈ Subgroup.normalizer (J z : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (J_le_H (z := z))).mp
        (J_subgroupOf_normal z) hk'
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hk'N y).mp hy.1
    · rw [Subgroup.mem_centralizer_iff]
      intro t ht
      have ht' : k'⁻¹ * t * k' ∈ J z := by
        have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hk'N) t).mp ht
        simpa using h
      have hcomm := Subgroup.mem_centralizer_iff.mp hy.2 (k'⁻¹ * t * k') ht'
      calc t * (k' * y * k'⁻¹)
          = k' * ((k'⁻¹ * t * k') * y) * k'⁻¹ := by group
        _ = k' * (y * (k'⁻¹ * t * k')) * k'⁻¹ := by rw [hcomm]
        _ = (k' * y * k'⁻¹) * t := by group
  let j' : J z := ⟨k * (j : G) * k⁻¹, hkJ⟩
  have hj'2 : orderOf (j' : G) = 2 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj (k : G)) (j : G)
    rw [MulAut.conj_apply] at h
    simpa [j'] using h.trans hj2
  have hj'Z : j' ∉ Subgroup.center (J z) := by
    intro hj'
    apply hjZ
    have hj'centerIn : (j' : G) ∈ centerIn (J z) := by
      rw [centerIn_eq_map_center]
      exact Subgroup.mem_map.mpr ⟨j', hj', rfl⟩
    have hjk : (j : G) = (k : G)⁻¹ * (j' : G) * (k : G) := by
      have hj'val : (j' : G) = (k : G) * (j : G) * (k : G)⁻¹ := rfl
      rw [hj'val]
      group
    have hcenter : (j : G) ∈ centerIn (J z) := by
      rw [hjk]
      simpa using hcenter_conj ((H z).inv_mem k.2) hj'centerIn
    rw [← QuotientV.centerIn_subgroupOf_eq_center]
    exact Subgroup.mem_subgroupOf.mpr hcenter
  obtain ⟨x, hxH, hxJ, hx2, hxj', hxB⟩ := hP7 ⟨g, hg⟩ k hkJ hkJ1 hkB hj'2
  exact false_of_involution_centralizer_eq_center_gen hj'Z hkJ1 hkB
    ⟨x, hxH, hxJ, hx2, hxj', hxB⟩ hx

theorem card_centralizer_of_mem_zpowers_sigma1_mul_sigma2_inv
    {y : QA45.originalSubgroup}
    (hy : y ∈ Subgroup.zpowers
      ((⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup) *
        (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)⁻¹))
    (hy1 : y ≠ 1) :
    Nat.card (Subgroup.centralizer ({y} : Set QA45.originalSubgroup)) = 108 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set y0 : QA45.originalSubgroup :=
    (⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup) *
      (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)⁻¹ with hy0
  have hy0_model : y0 = ⟨sigma1 * sigma2⁻¹, sigma1_mul_sigma2_inv_mem_A⟩ := rfl
  have hcomm : Commute (⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup)
      (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) :=
    Subtype.ext sigma1_commute_sigma2
  have hord1 : orderOf (⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup) = 3 :=
    orderOf_sigma1_subtype
  have hord2 : orderOf (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) = 3 :=
    orderOf_sigma2_subtype
  have hy0_ord : orderOf y0 = 3 := by
    rw [hy0]
    apply orderOf_eq_prime
    · have h1 : (⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup) ^ 3 = 1 := by
        rw [← hord1]
        exact pow_orderOf_eq_one _
      have h2 : (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) ^ 3 = 1 := by
        rw [← hord2]
        exact pow_orderOf_eq_one _
      calc ((⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup) *
            (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)⁻¹) ^ 3
          = (⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup) ^ 3 *
              ((⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)⁻¹) ^ 3 :=
            hcomm.inv_right.mul_pow 3
        _ = 1 := by rw [h1, inv_pow, h2, inv_one, mul_one]
    · intro h1
      exact sigma1_mul_sigma2_inv_ne_one h1
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hkmod : k % (3 : ℤ) = 0 ∨ k % (3 : ℤ) = 1 ∨ k % (3 : ℤ) = 2 := by
    have hnonneg : 0 ≤ k % (3 : ℤ) := Int.emod_nonneg k (by norm_num)
    have hlt : k % (3 : ℤ) < 3 := Int.emod_lt_of_pos k (by norm_num)
    omega
  have hkne : k % (3 : ℤ) ≠ 0 := by
    intro h0
    have h0' : k % ((3 : ℕ) : ℤ) = 0 := h0
    apply hy1
    rw [← hk, ← zpow_mod_orderOf y0 k, hy0_ord, h0', zpow_zero]
  rcases hkmod with h0 | h1 | h2
  · exact absurd h0 hkne
  · have h1' : k % ((3 : ℕ) : ℤ) = 1 := h1
    have hy_eq : y = y0 := by
      rw [← hk, ← zpow_mod_orderOf y0 k, hy0_ord, h1', zpow_one]
    rw [hy_eq, hy0_model]
    exact card_centralizer_sigma1_mul_sigma2_inv_QA45
  · have h2' : k % ((3 : ℕ) : ℤ) = 2 := h2
    have hy_eq : y = y0 * y0 := by
      rw [← hk, ← zpow_mod_orderOf y0 k, hy0_ord, h2', zpow_two]
    rw [hy_eq]
    have hzp : Subgroup.zpowers (y0 * y0) = Subgroup.zpowers y0 := by
      apply le_antisymm
      · rw [Subgroup.zpowers_le]
        exact Subgroup.mul_mem _ (Subgroup.mem_zpowers y0) (Subgroup.mem_zpowers y0)
      · rw [Subgroup.zpowers_le]
        have hcube : y0 ^ 3 = 1 := by
          rw [← hy0_ord]
          exact pow_orderOf_eq_one _
        have hsq : (y0 * y0) * (y0 * y0) = y0 := by
          calc (y0 * y0) * (y0 * y0) = y0 ^ 4 := by
                rw [← pow_two, ← pow_two, ← pow_mul]
            _ = y0 ^ 3 * y0 := by
                rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_add, pow_one]
            _ = y0 := by rw [hcube, one_mul]
        have hmem : (y0 * y0) * (y0 * y0) ∈ Subgroup.zpowers (y0 * y0) :=
          Subgroup.mul_mem (Subgroup.zpowers (y0 * y0))
            (Subgroup.mem_zpowers (y0 * y0)) (Subgroup.mem_zpowers (y0 * y0))
        rwa [hsq] at hmem
    rw [← CFSG.GroupTheory.centralizer_zpowers_eq,
      hzp, CFSG.GroupTheory.centralizer_zpowers_eq, hy0_model]
    exact card_centralizer_sigma1_mul_sigma2_inv_QA45

set_option linter.unusedSectionVars false in
theorem not_isConj_of_mem_zpowers_sigma1_mul_sigma2_inv_of_hom
    (q : ↥(H z) →* QA45.originalSubgroup) {σ₁ σ₂ : ↥(H z)}
    (hq₁ : q σ₁ = (⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup))
    (hq₂ : q σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    {y : ↥(H z)} (hy : y ∈ Subgroup.zpowers (σ₁ * σ₂⁻¹)) :
    ¬ IsConj σ₁ y := by
  intro hconj
  have hqconj : IsConj (q σ₁) (q y) := q.map_isConj hconj
  have hqx : q (σ₁ * σ₂⁻¹) =
      (⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup) *
        (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)⁻¹ := by
    rw [map_mul, map_inv, hq₁, hq₂]
  have hqy_mem : q y ∈ Subgroup.zpowers
      ((⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup) *
        (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)⁻¹) := by
    have hmem := Subgroup.mem_map_of_mem q hy
    rwa [MonoidHom.map_zpowers, hqx] at hmem
  have hqy_ne : q y ≠ 1 := by
    intro h1
    have hconj1 : IsConj (⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup)
        (1 : QA45.originalSubgroup) := by
      simpa [hq₁, h1] using hqconj
    have hs1ne : (⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup) ≠ 1 := by
      intro h2
      exact sigma1_ne_one (by simpa using congrArg Subtype.val h2)
    exact hs1ne (isConj_one_left.mp hconj1)
  have hcard := CFSG.GroupTheory.card_centralizer_singleton_congr_of_isConj hqconj
  rw [hq₁, card_centralizer_of_mem_zpowers_sigma1_mul_sigma2_inv hqy_mem hqy_ne,
    card_centralizer_sigma1_QA45] at hcard
  norm_num at hcard

set_option linter.unusedSectionVars false in
theorem orderOf_mul_inv_of_commute_of_hom
    (q : ↥(H z) →* QA45.originalSubgroup) {σ₁ σ₂ : ↥(H z)}
    (hσ₁ : orderOf σ₁ = 3) (hσ₂ : orderOf σ₂ = 3)
    (hq₁ : q σ₁ = (⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup))
    (hq₂ : q σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute σ₁ σ₂) :
    orderOf (σ₁ * σ₂⁻¹) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply orderOf_eq_prime
  · have h1 : σ₁ ^ 3 = 1 := by
      rw [← hσ₁]
      exact pow_orderOf_eq_one _
    have h2 : σ₂ ^ 3 = 1 := by
      rw [← hσ₂]
      exact pow_orderOf_eq_one _
    calc (σ₁ * σ₂⁻¹) ^ 3 = σ₁ ^ 3 * (σ₂⁻¹) ^ 3 := hcomm.inv_right.mul_pow 3
      _ = 1 := by rw [h1, inv_pow, h2, inv_one, mul_one]
  · intro h1
    have hq : q (σ₁ * σ₂⁻¹) =
        (⟨sigma1 * sigma2⁻¹, sigma1_mul_sigma2_inv_mem_A⟩ : QA45.originalSubgroup) := by
      rw [map_mul, map_inv, hq₁, hq₂]
      rfl
    rw [h1, map_one] at hq
    exact sigma1_mul_sigma2_inv_ne_one hq.symm

theorem not_conj_of_isSylowOf_centralizer_of_commutator_le
    {L K J : Subgroup G} {z x : G}
    (hK : IsSylowOf 2 K (Subgroup.centralizer ({x} : Set G) ⊓ L))
    (hzK' : z ∈ ⁅K, K⁆)
    (hK'J : ⁅K, K⁆ ≤ J)
    (hxJ : x ∉ J)
    (hzcent : z ∈ Subgroup.centralizer (K : Set G)) :
    ¬ ∃ m ∈ L, m * z * m⁻¹ = x := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro ⟨m, hmL, hmz⟩
  have hzK : z ∈ K := Subgroup.commutator_le_self K hzK'
  let M : Subgroup G := Subgroup.centralizer ({x} : Set G) ⊓ L
  let Km : Subgroup G := K.map (MulAut.conj m).toMonoidHom
  have hKm_le : Km ≤ M := by
    intro y hy
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hy
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      have hzk : z * k = k * z := (Subgroup.mem_centralizer_iff.mp hzcent k hk).symm
      calc (m * k * m⁻¹) * x
          = (m * k * m⁻¹) * (m * z * m⁻¹) := by rw [hmz]
        _ = m * (k * z) * m⁻¹ := by group
        _ = m * (z * k) * m⁻¹ := by rw [hzk]
        _ = (m * z * m⁻¹) * (m * k * m⁻¹) := by group
        _ = x * (m * k * m⁻¹) := by rw [hmz]
    · have hkL : k ∈ L := (Subgroup.mem_inf.mp (hK.le hk)).2
      exact L.mul_mem (L.mul_mem hmL hkL) (L.inv_mem hmL)
  have hKm_card : Nat.card Km = 2 ^ (Nat.card M).factorization 2 := by
    have hcard : Nat.card Km = Nat.card K :=
      Subgroup.card_map_of_injective (MulAut.conj m).injective
    rw [hcard]
    exact hK.card_eq
  have hKm : IsSylowOf 2 Km M := isSylowOf_of_card hKm_le hKm_card
  obtain ⟨c, hcM, hconj⟩ := hK.exists_mem_conj hKm
  have hcL : c ∈ L := (Subgroup.mem_inf.mp hcM).2
  have hcx : c * x = x * c :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hcM).1
  let n : G := c⁻¹ * m
  have hnL : n ∈ L := L.mul_mem (L.inv_mem hcL) hmL
  have hnN : n ∈ Subgroup.normalizer (K : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have hyKm : m * y * m⁻¹ ∈ Km := Subgroup.mem_map_of_mem _ hy
      have hmem : c⁻¹ * (m * y * m⁻¹) * c ∈ K := (hconj _).mp hyKm
      have heq : n * y * n⁻¹ = c⁻¹ * (m * y * m⁻¹) * c := by
        simp only [n]
        group
      rwa [heq]
    · intro hy
      have hmem : c⁻¹ * (m * y * m⁻¹) * c ∈ K := by
        have heq : n * y * n⁻¹ = c⁻¹ * (m * y * m⁻¹) * c := by
          simp only [n]
          group
        rwa [heq] at hy
      have hyKm : m * y * m⁻¹ ∈ Km := (hconj _).mpr hmem
      obtain ⟨k, hk, hky⟩ := Subgroup.mem_map.mp hyKm
      have hkeq : k = y := by
        have := congrArg (fun t => m⁻¹ * t * m) hky
        simpa [mul_assoc] using this
      rwa [← hkeq]
  have hKmap : K.map (MulAut.conj n).toMonoidHom = K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hnN
  have hK'map : (⁅K, K⁆).map (MulAut.conj n).toMonoidHom = ⁅K, K⁆ := by
    rw [Subgroup.map_commutator, hKmap]
  have hzn : n * z * n⁻¹ ∈ ⁅K, K⁆ := by
    have hmem : (MulAut.conj n) z ∈ (⁅K, K⁆).map (MulAut.conj n).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hzK'
    rw [hK'map] at hmem
    simpa [MulAut.conj_apply] using hmem
  have hnx : n * z * n⁻¹ = x := by
    have hcx' : c⁻¹ * x = x * c⁻¹ := by
      calc c⁻¹ * x = c⁻¹ * (x * c) * c⁻¹ := by group
        _ = c⁻¹ * (c * x) * c⁻¹ := by rw [← hcx]
        _ = x * c⁻¹ := by group
    calc n * z * n⁻¹ = c⁻¹ * (m * z * m⁻¹) * c := by
          simp only [n]
          group
      _ = c⁻¹ * x * c := by rw [hmz]
      _ = (c⁻¹ * x) * c := by group
      _ = (x * c⁻¹) * c := by rw [hcx']
      _ = x := by group
  exact hxJ (hK'J (hnx ▸ hzn))

theorem false_of_mem_utJ_of_data_gen [hN : ((J z).subgroupOf (H z)).Normal]
    {w : ↥(H z)} {x : G} (hxw : (w : G)⁻¹ * x ∈ J z)
    {K : Subgroup (J z)}
    (hKiso : Nonempty (↥K ≃* CFSG.Quasithin.Z4StarQ8Model))
    {X : Subgroup G}
    (hX : IsSylowOf 2 X (H z ⊓ Subgroup.centralizer ({x} : Set G)))
    (hKX : K.map (J z).subtype ≤ X)
    {Y : Subgroup G} (hXY : X ≤ Y) (hYidx : X.relIndex Y = 2)
    {y : G} (hyY : y ∈ Y)
    (hKyJ : (K.map (J z).subtype).map (MulAut.conj y).toMonoidHom ⊓ J z = ⊥)
    (hnoK : ∀ L : Subgroup (↥(H z) ⧸ (J z).subgroupOf (H z)),
      L ≤ Subgroup.centralizer
        ({QuotientGroup.mk' ((J z).subgroupOf (H z)) w} :
          Set (↥(H z) ⧸ (J z).subgroupOf (H z))) →
      ¬ Nonempty (↥L ≃* CFSG.Quasithin.Z4StarQ8Model)) :
    False := by
  classical
  have hxH : x ∈ H z := by
    have hx_eq : x = (w : G) * ((w : G)⁻¹ * x) := by group
    rw [hx_eq]
    exact (H z).mul_mem w.2 (J_le_H hxw)
  have hxq : QuotientGroup.mk' ((J z).subgroupOf (H z)) (⟨x, hxH⟩ : ↥(H z)) =
      QuotientGroup.mk' ((J z).subgroupOf (H z)) w := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    simpa [mul_inv_rev] using (J z).inv_mem hxw
  let KG : Subgroup G := K.map (J z).subtype
  let Ky : Subgroup G := KG.map (MulAut.conj y).toMonoidHom
  have hKyJ' : Ky ⊓ J z = ⊥ := hKyJ
  have hXnormal : (X.subgroupOf Y).Normal := Subgroup.normal_of_index_eq_two hYidx
  have hYnormX : Y ≤ Subgroup.normalizer (X : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXY).mp hXnormal
  have hXH : X ≤ H z := hX.le.trans inf_le_left
  have hXC : X ≤ Subgroup.centralizer ({x} : Set G) := hX.le.trans inf_le_right
  have hKy_le_X : Ky ≤ X := by
    intro k hk
    change k ∈ KG.map (MulAut.conj y).toMonoidHom at hk
    rw [Subgroup.mem_map] at hk
    obtain ⟨k0, hk0, hk_eq⟩ := hk
    have hk0X : k0 ∈ X := hKX hk0
    have hconjX : y * k0 * y⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp (hYnormX hyY) k0).mp hk0X
    rw [← hk_eq]
    simpa [MulAut.conj_apply] using hconjX
  have hKy_le_H : Ky ≤ H z := hKy_le_X.trans hXH
  have hKy_le_C : Ky ≤ Subgroup.centralizer ({x} : Set G) := hKy_le_X.trans hXC
  let Φ : ↥Ky →* ↥(H z) ⧸ (J z).subgroupOf (H z) :=
    (QuotientGroup.mk' ((J z).subgroupOf (H z))).comp (Subgroup.inclusion hKy_le_H)
  have hΦ_apply : ∀ k : ↥Ky,
      Φ k = QuotientGroup.mk' ((J z).subgroupOf (H z))
        (⟨(k : G), hKy_le_H k.2⟩ : ↥(H z)) := fun k => rfl
  have hker_Φ : Φ.ker = ⊥ := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_bot]
    constructor
    · intro hk
      have hk1 : QuotientGroup.mk' ((J z).subgroupOf (H z))
          (⟨(k : G), hKy_le_H k.2⟩ : ↥(H z)) = 1 := by
        simpa [hΦ_apply] using hk
      rw [QuotientGroup.mk'_apply] at hk1
      have hkJH : (⟨(k : G), hKy_le_H k.2⟩ : ↥(H z)) ∈ (J z).subgroupOf (H z) :=
        (QuotientGroup.eq_one_iff _).mp hk1
      have hkJ : (k : G) ∈ J z := Subgroup.mem_subgroupOf.mp hkJH
      have hmem : (k : G) ∈ Ky ⊓ J z := ⟨k.2, hkJ⟩
      rw [hKyJ'] at hmem
      exact Subtype.ext (Subgroup.mem_bot.mp hmem)
    · intro hk
      rw [hk, map_one]
  have hΦ_inj : Function.Injective Φ := (MonoidHom.ker_eq_bot_iff Φ).mp hker_Φ
  let L : Subgroup (↥(H z) ⧸ (J z).subgroupOf (H z)) := Φ.range
  have hLle : L ≤ Subgroup.centralizer
      ({QuotientGroup.mk' ((J z).subgroupOf (H z)) w} :
        Set (↥(H z) ⧸ (J z).subgroupOf (H z))) := by
    intro l hl
    rw [Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨k, rfl⟩ := hl
    have hkcomm : (k : G) * x = x * (k : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hKy_le_C k.2)
    have hcommH : (⟨(k : G), hKy_le_H k.2⟩ : ↥(H z)) * (⟨x, hxH⟩ : ↥(H z)) =
        (⟨x, hxH⟩ : ↥(H z)) * (⟨(k : G), hKy_le_H k.2⟩ : ↥(H z)) :=
      Subtype.ext hkcomm
    have hcommq : QuotientGroup.mk' ((J z).subgroupOf (H z))
          (⟨(k : G), hKy_le_H k.2⟩ : ↥(H z)) *
        QuotientGroup.mk' ((J z).subgroupOf (H z)) (⟨x, hxH⟩ : ↥(H z)) =
        QuotientGroup.mk' ((J z).subgroupOf (H z)) (⟨x, hxH⟩ : ↥(H z)) *
        QuotientGroup.mk' ((J z).subgroupOf (H z))
          (⟨(k : G), hKy_le_H k.2⟩ : ↥(H z)) := by
      simpa only [map_mul] using congrArg (QuotientGroup.mk' ((J z).subgroupOf (H z))) hcommH
    rw [hxq] at hcommq
    rw [hΦ_apply k]
    exact hcommq
  have hLiso : Nonempty (↥L ≃* ↥K) := by
    let e1 : ↥Ky ≃* ↥L := MonoidHom.ofInjective hΦ_inj
    let e2 : ↥Ky ≃* ↥KG := ((MulAut.conj y).subgroupMap KG).symm
    let e3 : ↥KG ≃* ↥K :=
      (K.equivMapOfInjective (J z).subtype (J z).subtype_injective).symm
    exact ⟨e1.symm.trans (e2.trans e3)⟩
  obtain ⟨eL⟩ := hLiso
  obtain ⟨eK⟩ := hKiso
  exact hnoK L hLle ⟨eL.trans eK⟩

theorem no_conj_z_eq_of_mem_utJ_gen [hN : ((J z).subgroupOf (H z)).Normal]
    {w : ↥(H z)} {x : G} (hxw : (w : G)⁻¹ * x ∈ J z)
    {K : Subgroup (J z)}
    (hKiso : Nonempty (↥K ≃* CFSG.Quasithin.Z4StarQ8Model))
    {X : Subgroup G}
    (hX : IsSylowOf 2 X (H z ⊓ Subgroup.centralizer ({x} : Set G)))
    (hKX : K.map (J z).subtype ≤ X)
    {Y : Subgroup G} (hXY : X ≤ Y) (hYidx : X.relIndex Y = 2)
    {y : G} (hyY : y ∈ Y)
    (hKyJ : (K.map (J z).subtype).map (MulAut.conj y).toMonoidHom ⊓ J z = ⊥)
    (hnoK : ∀ L : Subgroup (↥(H z) ⧸ (J z).subgroupOf (H z)),
      L ≤ Subgroup.centralizer
        ({QuotientGroup.mk' ((J z).subgroupOf (H z)) w} :
          Set (↥(H z) ⧸ (J z).subgroupOf (H z))) →
      ¬ Nonempty (↥L ≃* CFSG.Quasithin.Z4StarQ8Model)) :
    ∀ g : G, g * z * g⁻¹ ≠ x := fun _ _ =>
  (false_of_mem_utJ_of_data_gen hxw hKiso hX hKX hXY hYidx hyY hKyJ hnoK).elim

end CFSG.RankThree.GF2n.Parrott
