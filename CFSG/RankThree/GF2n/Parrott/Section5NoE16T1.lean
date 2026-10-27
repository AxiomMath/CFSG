module

public import CFSG.GroupTheory.QuaternionQuotientElementaryAbelian
public import CFSG.RankThree.GF2n.Parrott.Section5CenterT1
public import CFSG.RankThree.GF2n.Parrott.Section2CJ
public import CFSG.RankThree.GF2n.Parrott.HPrimeJ1
public import CFSG.RankThree.GF2n.Parrott.CommutatorNormalSigma1
public import CFSG.RankThree.GF2n.Parrott.Section4EWeak
public import TauCeti.Algebra.Group.Subgroup.ZPowers
public import CFSG.RankThree.GF2n.Parrott.Section5LocalSigma

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools CFSG.GroupTheory Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

omit [Finite G] in
theorem commutator_eq_one_or_eq_of_mem_J (h : Tim79a.ParrottHyp z) {x y : G} (hx : x ∈ J z)
    (hy : y ∈ J z) : x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = z := by
  have hmem : ⁅x, y⁆ ∈ ⁅J z, J z⁆ := Subgroup.commutator_mem_commutator hx hy
  rw [commutatorElement_def] at hmem
  have hJ' : ⁅J z, J z⁆ = Subgroup.zpowers z := by
    obtain ⟨-, -, hcomm, -, -⟩ := h
    simpa [J, H] using hcomm
  rw [hJ'] at hmem
  exact (Subgroup.mem_zpowers_iff_of_orderOf_eq_two h.1).mp hmem

theorem mul_self_eq_one_or_eq_of_mem_J (h : Tim79a.ParrottHyp z) {x : G} (hx : x ∈ J z) :
    x * x = 1 ∨ x * x = z := by
  obtain ⟨T, F, hT, hF, -, -, hcomm, hTF⟩ := exists_decomposition h
  rw [← hTF] at hx
  obtain ⟨t, ht, f, hf, rfl⟩ := (CFSG.mem_sup_of_commute hcomm).mp hx
  have ht2 : t * t = 1 := by
    have h1 : (⟨t, ht⟩ : T) ^ Nat.card T = 1 := pow_card_eq_one'
    rw [hT] at h1
    have := congrArg Subtype.val h1
    simpa [pow_two] using this
  have hff : f * f ∈ (Subgroup.center F).map F.subtype :=
    CFSG.IsExtraspecial2.mul_self_mem_center_map hF hf
  have hFJ : F ≤ J z := hTF ▸ le_sup_right
  have hJ' : ⁅J z, J z⁆ = Subgroup.zpowers z := by
    obtain ⟨-, -, hcommJ, -, -⟩ := h
    simpa [J, H] using hcommJ
  have hmem : f * f ∈ Subgroup.zpowers z := by
    rw [← hJ']
    rw [← hF.2.1] at hff
    exact Subgroup.commutator_mono hFJ hFJ hff
  have heq : (t * f) * (t * f) = f * f := by
    have htf : Commute t f := hcomm t ht f hf
    calc (t * f) * (t * f) = t * (f * (t * f)) := by rw [mul_assoc]
      _ = t * ((f * t) * f) := by rw [mul_assoc]
      _ = t * ((t * f) * f) := by rw [htf.eq]
      _ = (t * t) * (f * f) := by group
      _ = f * f := by rw [ht2, one_mul]
  rw [heq]
  exact (Subgroup.mem_zpowers_iff_of_orderOf_eq_two h.1).mp hmem

variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

theorem card_centralizerJ_of_qH_eq_sigma2 (h : Tim79a.ParrottHyp z) {σ₂ : ↥(H z)}
    (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)) :
    Nat.card (centralizerJ σ₂) = 16 := by
  have hcop : Nat.Coprime (orderOf σ₂) (Nat.card (J z)) := by
    rw [hσ₂, card_J h]
    norm_num
  have hcopNine : Nat.Coprime (orderOf (sigma2Nine (z := z) D)) (Nat.card (J z)) := by
    rw [orderOf_sigma2Nine, card_J h]
    norm_num
  have hconjV : conjV h σ₂ = conjV h (sigma2Nine (z := z) D) :=
    conjV_eq_of_qH_eq (z := z) h D (hq₂.trans (qH_sigma2Nine (z := z) D).symm)
  have hcenter_le : Subgroup.center (J z) ≤ centralizerJ σ₂ := by
    intro j hj
    rw [mem_centralizerJ_iff]
    have hjZ : (j : G) ∈ centerIn (J z) := by
      have hj' : j ∈ (centerIn (J z)).subgroupOf (J z) := by
        rwa [QuotientV.centerIn_subgroupOf_eq_center]
      exact Subgroup.mem_subgroupOf.mp hj'
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (centerIn_le_centralizer_of_conjZ_eq_one (z := z)
        (conjZ_eq_one_of_qH_eq_sigma2 (z := z) D h hq₂) hjZ)
  have hcenter_leNine : Subgroup.center (J z) ≤ centralizerJ (sigma2Nine (z := z) D) := by
    intro j hj
    rw [mem_centralizerJ_iff]
    have hjZ : (j : G) ∈ centerIn (J z) := by
      have hj' : j ∈ (centerIn (J z)).subgroupOf (J z) := by
        rwa [QuotientV.centerIn_subgroupOf_eq_center]
      exact Subgroup.mem_subgroupOf.mp hj'
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (centerIn_le_centralizer_of_conjZ_eq_one (z := z)
        (conjZ_sigma2Nine (z := z) h D) hjZ)
  have hform := card_centralizerJ_eq_card_inf_mul_card_autFixed (z := z) (h := h) (x := σ₂) hcop
  rw [inf_eq_right.mpr hcenter_le, hconjV, card_center_subgroupOf_J (z := z) h] at hform
  have hformNine := card_centralizerJ_eq_card_inf_mul_card_autFixed (z := z) (h := h)
    (x := sigma2Nine (z := z) D) hcopNine
  rw [inf_eq_right.mpr hcenter_leNine, card_center_subgroupOf_J (z := z) h,
    card_centralizerJ_sigma2Nine (z := z) h D] at hformNine
  omega

theorem mul_self_eq_of_mem_J_inf_centralizer_sigma1Nine_of_not_mem_centerIn
    (h : Tim79a.ParrottHyp z) (hIII : ¬ ParrottEqualityBranch (z := z) (D := D) h) :
    ∀ x ∈ J z ⊓ centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G),
      x ∉ centerIn (J z) → x * x = z := by
  obtain ⟨σ₂, hσ₂ord, hq₂, hcommH⟩ := exists_commuting_order_three_lift_sigma2 (z := z) D h
  set N : Subgroup G :=
    J z ⊓ centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G) with hNdef
  have hZN : centerIn N = centerIn (J z) := by
    rw [hNdef]
    exact centerIn_J_inf_centralizer_sigma1Nine_eq (z := z) D h
  have hidx : Nat.card N = 4 * Nat.card (centerIn N) := by
    rw [hNdef, card_J_inf_centralizer_sigma1Nine (z := z) D h, hZN, card_centerIn_J h]
  have hZ2 : ∀ x ∈ centerIn N, x * x = 1 := by
    intro x hx
    rw [hZN] at hx
    exact centerIn_J_sq h hx
  have hz : z ∈ centerIn N := by
    rw [hZN]
    exact z_mem_centerIn_J h
  have hcommN : ∀ x ∈ N, ∀ y ∈ N, x * y * x⁻¹ * y⁻¹ = 1 ∨ x * y * x⁻¹ * y⁻¹ = z := by
    intro x hx y hy
    exact commutator_eq_one_or_eq_of_mem_J h (hNdef ▸ hx).1 (hNdef ▸ hy).1
  have hσN : ∀ n ∈ N, (σ₂ : G) * n * (σ₂ : G)⁻¹ ∈ N := by
    intro n hn
    have hcommG : (σ₂ : G) * ((sigma1Nine (z := z) D : ↥(H z)) : G) =
        ((sigma1Nine (z := z) D : ↥(H z)) : G) * (σ₂ : G) := by
      simpa using congrArg Subtype.val hcommH
    have hc : (σ₂ : G) ∈
        H z ⊓ centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G) :=
      mem_inf.mpr ⟨σ₂.2, Subgroup.mem_centralizer_singleton_iff.mpr hcommG⟩
    rw [hNdef] at hn ⊢
    exact conj_mem_J_inf_centralizer hc hn
  have hσ3 : (σ₂ : G) ^ 3 = 1 := by
    have h := pow_orderOf_eq_one σ₂
    rw [hσ₂ord] at h
    simpa using congrArg Subtype.val h
  have hσZ : ∀ x ∈ centerIn N, (σ₂ : G) * x = x * (σ₂ : G) := by
    intro x hx
    rw [hZN] at hx
    exact (Subgroup.mem_centralizer_singleton_iff.mp
      (centerIn_le_centralizer_of_conjZ_eq_one (z := z) (x := σ₂)
        (conjZ_eq_one_of_qH_eq_sigma2 (z := z) D h hq₂) hx)).symm
  rcases forall_commute_or_mul_self_eq_of_pow_three_eq_one hidx hZ2 hz hcommN hσN hσ3 hσZ
    with hcentral | hsq
  · exfalso
    apply hIII
    have hle : centralizerJ (sigma1Nine (z := z) D) ≤ centralizerJ σ₂ := by
      intro j hj
      rw [mem_centralizerJ_iff] at hj ⊢
      have hjN : (j : G) ∈ N := by
        rw [hNdef]
        exact mem_inf.mpr ⟨j.2, Subgroup.mem_centralizer_singleton_iff.mpr hj⟩
      exact (hcentral (j : G) hjN).symm
    have hcard₁ : Nat.card (centralizerJ (sigma1Nine (z := z) D)) = 16 :=
      card_centralizerJ_sigma1Nine (z := z) h D
    have hcard₂ : Nat.card (centralizerJ σ₂) = 16 :=
      card_centralizerJ_of_qH_eq_sigma2 (D := D) h hσ₂ord hq₂
    refine ⟨σ₂, hσ₂ord, hq₂, ?_⟩
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard₂, hcard₁])
  · intro x hx hxZ
    exact hsq x hx (by simpa [hZN] using hxZ)

theorem not_elementaryAbelian_of_le_isSylowOf_centralizer_sigma1Nine (h : Tim79a.ParrottHyp z)
    (hIII : ¬ ParrottEqualityBranch (z := z) (D := D) h) {T₁ : Subgroup G}
    (hT₁ : IsSylowOf 2 T₁
      (H z ⊓ centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G))) :
    ∀ F : Subgroup G, F ≤ T₁ → Nat.card F = 16 →
      ¬ ((∀ x ∈ F, ∀ y ∈ F, x * y = y * x) ∧ ∀ x ∈ F, x * x = 1) := by
  obtain ⟨π, -, hker⟩ :=
    exists_quaternion_quotient_of_isSylowOf_centralizer_sigma1Nine (z := z) D h hT₁
  have hker' : ∀ g : ↥T₁, π g = 1 →
      (g : G) ∈ J z ⊓ centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G) := by
    intro g hg
    have hgker : g ∈ π.ker := MonoidHom.mem_ker.mpr hg
    rw [hker] at hgker
    exact Subgroup.mem_subgroupOf.mp hgker
  have hZ : Nat.card ↥(centerIn (J z)) ≤ 4 := by
    simp [card_centerIn_J h]
  have hN2 : ∀ x ∈ J z ⊓ centralizer ({((sigma1Nine (z := z) D : ↥(H z)) : G)} : Set G),
      x * x = 1 → x ∈ centerIn (J z) := by
    intro x hx hx2
    by_contra hxZ
    have hxz :=
      mul_self_eq_of_mem_J_inf_centralizer_sigma1Nine_of_not_mem_centerIn (D := D) h hIII x hx hxZ
    have hz1 : z ≠ 1 := by
      intro hz
      have h2 : orderOf z = 1 := by rw [hz, orderOf_one]
      rw [h.1] at h2
      exact absurd h2 (by decide)
    exact hz1 (hxz.symm.trans hx2)
  intro F hFT hF
  exact not_elementaryAbelian_of_card_eq_sixteen_of_quaternion_quotient π hker' hZ hN2 F hFT hF

end CFSG.RankThree.GF2n.Parrott
