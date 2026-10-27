module

public import CFSG.RankThree.GF2n.Parrott.ActionZSimplicity
public import CFSG.GroupTheory.PCore.NormalPCoreOf

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open

variable {G : Type} [Group G] [Finite G] {z : G}

theorem pCore_centralizer_centerIn_eq (h : Tim79a.ParrottHyp z) :
    CFSG.Open.pCoreOf 2 (Subgroup.centralizer (centerIn (J z) : Set G)) = J z := by
  set C : Subgroup G := Subgroup.centralizer (centerIn (J z) : Set G) with hC
  have hz_mem : z ∈ centerIn (J z) := ⟨z_mem_J h, z_centralizes_J h⟩
  have hC_le_H : C ≤ H z := by
    rw [hC, H_eq_centralizer]
    exact Subgroup.centralizer_le fun w hw => by
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact hz_mem
  have hJ_le_C : J z ≤ C := by
    intro j hj
    rw [hC, Subgroup.mem_centralizer_iff]
    intro w hw
    exact ((Subgroup.mem_centralizer_iff.mp hw.2) j hj).symm
  have hH_norm_J : H z ≤ Subgroup.normalizer (J z : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (J_le_H (z := z))).mp
      (inferInstance : ((J z).subgroupOf (H z)).Normal)
  have hCsub : (Subgroup.centralizer ((centerIn (J z)).subgroupOf (H z) : Set ↥(H z))) =
      C.subgroupOf (H z) := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_subgroupOf, hC, Subgroup.mem_centralizer_iff]
      rw [Subgroup.mem_centralizer_iff] at hx
      intro w hw
      exact congrArg Subtype.val
        (hx ⟨w, centerIn_le_H (z := z) hw⟩ (Subgroup.mem_subgroupOf.mpr hw))
    · intro hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Subgroup.mem_subgroupOf] at hx
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hx) (y : G)
        (Subgroup.mem_subgroupOf.mp hy))
  have hCnorm : (C.subgroupOf (H z)).Normal :=
    hCsub ▸ (inferInstance : (Subgroup.centralizer
      ((centerIn (J z)).subgroupOf (H z) : Set ↥(H z))).Normal)
  have hH_norm_C : H z ≤ Subgroup.normalizer (C : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hC_le_H).mp hCnorm
  have hC_norm_J : C ≤ Subgroup.normalizer (J z : Set G) := hC_le_H.trans hH_norm_J
  have htop : (⊤ : Subgroup ↥(J z)) ≤ CFSG.pCore 2 ↥(J z) := by
    rw [CFSG.pCore_eq_iSup]
    exact le_iSup_of_le ⊤ (le_iSup_of_le inferInstance
      (le_iSup_of_le ((isPGroup_J h).to_subgroup ⊤) le_rfl))
  have hJ_le_pCoreJ : J z ≤ CFSG.Open.pCoreOf 2 (J z) := by
    intro x hx
    exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩, htop (Subgroup.mem_top _), rfl⟩
  have hJ_le : J z ≤ CFSG.Open.pCoreOf 2 C :=
    hJ_le_pCoreJ.trans
      (CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 hJ_le_C hC_norm_J)
  have hle : CFSG.Open.pCoreOf 2 C ≤ J z := by
    have h1 := CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 hC_le_H hH_norm_C
    rwa [show CFSG.Open.pCoreOf 2 (H z) = J z from rfl] at h1
  exact le_antisymm hle hJ_le

section

theorem index_centralizer_centerIn_subgroupOf_le_two (h : Tim79a.ParrottHyp z) :
    (Subgroup.centralizer ((centerIn (J z)).subgroupOf (H z) : Set ↥(H z))).index ≤ 2 := by
  classical
  let fZ : Fintype ↥(centerIn (J z)) := Fintype.ofFinite _
  have hK4 : IsKleinFour ↥(centerIn (J z)) := isKleinFour_centerIn_J (z := z) h
  have hzord : orderOf z = 2 := h.1
  have hz_mem : z ∈ centerIn (J z) := ⟨z_mem_J h, z_centralizes_J h⟩
  obtain ⟨z1, hZsup, hz1_notz, hz1ord⟩ := exists_z1 (z := z) h
  have hz1_mem : z1 ∈ centerIn (J z) := by
    rw [hZsup]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z1)
  have hzz1_mem : z * z1 ∈ centerIn (J z) := mul_mem hz_mem hz1_mem
  have hz_ne : (⟨z, hz_mem⟩ : centerIn (J z)) ≠ 1 := by
    intro hc
    have h1 : z = 1 := congrArg Subtype.val hc
    rw [h1, orderOf_one] at hzord
    exact absurd hzord (by norm_num)
  have hz1_ne : (⟨z1, hz1_mem⟩ : centerIn (J z)) ≠ 1 := by
    intro hc
    have h1 : z1 = 1 := congrArg Subtype.val hc
    rw [h1, orderOf_one] at hz1ord
    exact absurd hz1ord (by norm_num)
  have hz1_notz' : (⟨z1, hz1_mem⟩ : centerIn (J z)) ≠ ⟨z, hz_mem⟩ := by
    intro hc
    exact hz1_notz (by rw [show z1 = z from congrArg Subtype.val hc]; exact Subgroup.mem_zpowers z)
  have hzz1_ne : (⟨z1, hz1_mem⟩ : centerIn (J z)) ≠ ⟨z * z1, hzz1_mem⟩ := by
    intro hc
    have h1 : z1 = z * z1 := congrArg Subtype.val hc
    have h2 : z = 1 := by
      have := congrArg (fun t => t * z1⁻¹) h1
      simpa [mul_assoc] using this.symm
    rw [h2, orderOf_one] at hzord
    exact absurd hzord (by norm_num)
  have hmul : (⟨z * z1, hzz1_mem⟩ : centerIn (J z)) =
      (⟨z, hz_mem⟩ : centerIn (J z)) * ⟨z1, hz1_mem⟩ := Subtype.ext rfl
  have hclass : ∀ x : centerIn (J z),
      x = 1 ∨ x = ⟨z, hz_mem⟩ ∨ x = ⟨z1, hz1_mem⟩ ∨ x = ⟨z * z1, hzz1_mem⟩ := by
    intro x
    by_cases h1 : x = 1
    · exact Or.inl h1
    by_cases h2 : x = ⟨z, hz_mem⟩
    · exact Or.inr (Or.inl h2)
    by_cases h3 : x = ⟨z1, hz1_mem⟩
    · exact Or.inr (Or.inr (Or.inl h3))
    · refine Or.inr (Or.inr (Or.inr ?_))
      have h4 := IsKleinFour.eq_mul_of_ne_all (G := ↥(centerIn (J z)))
        hz_ne hz1_ne hz1_notz'.symm h1 h2 h3
      rw [h4]
      exact hmul.symm
  have hfix_z : ∀ a : (conjZ z).range, (a : MulAut (centerIn (J z))) ⟨z, hz_mem⟩ =
      ⟨z, hz_mem⟩ := by
    intro a
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp a.2
    rw [← hg]
    apply Subtype.ext
    rw [conjZ_apply_coe]
    have hcomm : (g : G) * z = z * (g : G) :=
      Subgroup.mem_centralizer_iff.mp (z_centralizes_H h) (g : G) g.2
    rw [hcomm, mul_inv_cancel_right]
  have hz1_image : ∀ a : (conjZ z).range,
      (a : MulAut (centerIn (J z))) ⟨z1, hz1_mem⟩ = ⟨z1, hz1_mem⟩ ∨
        (a : MulAut (centerIn (J z))) ⟨z1, hz1_mem⟩ = ⟨z * z1, hzz1_mem⟩ := by
    intro a
    by_cases hfix : (a : MulAut (centerIn (J z))) ⟨z1, hz1_mem⟩ = ⟨z1, hz1_mem⟩
    · exact Or.inl hfix
    · refine Or.inr ?_
      have hne1 : (a : MulAut (centerIn (J z))) ⟨z1, hz1_mem⟩ ≠ 1 := by
        intro hc
        have h1 : (⟨z1, hz1_mem⟩ : centerIn (J z)) = 1 := by
          apply (a : MulAut (centerIn (J z))).injective
          rw [hc, map_one]
        exact hz1_ne h1
      have hnez : (a : MulAut (centerIn (J z))) ⟨z1, hz1_mem⟩ ≠ ⟨z, hz_mem⟩ := by
        intro hc
        have h1 : (⟨z1, hz1_mem⟩ : centerIn (J z)) = ⟨z, hz_mem⟩ := by
          apply (a : MulAut (centerIn (J z))).injective
          rw [hc, hfix_z a]
        exact hz1_notz' h1
      have h4 := IsKleinFour.eq_mul_of_ne_all (G := ↥(centerIn (J z)))
        hz_ne hz1_ne hz1_notz'.symm hne1 hnez hfix
      rw [h4]
      exact hmul
  have hdet : ∀ a b : MulAut (centerIn (J z)),
      a ⟨z, hz_mem⟩ = ⟨z, hz_mem⟩ → b ⟨z, hz_mem⟩ = ⟨z, hz_mem⟩ →
      a ⟨z1, hz1_mem⟩ = b ⟨z1, hz1_mem⟩ → a = b := by
    intro a b hza hzb hz1a
    apply MulEquiv.ext
    intro x
    rcases hclass x with hx | hx | hx | hx
    · rw [hx, map_one, map_one]
    · rw [hx, hza, hzb]
    · rw [hx, hz1a]
    · rw [hx, hmul, map_mul, map_mul, hza, hzb, hz1a]
  have hinj : Function.Injective fun a : (conjZ z).range =>
      (⟨(a : MulAut (centerIn (J z))) ⟨z1, hz1_mem⟩, hz1_image a⟩ :
        {w : centerIn (J z) // w = ⟨z1, hz1_mem⟩ ∨ w = ⟨z * z1, hzz1_mem⟩}) := by
    intro a b hab
    have hval : (a : MulAut (centerIn (J z))) ⟨z1, hz1_mem⟩ =
        (b : MulAut (centerIn (J z))) ⟨z1, hz1_mem⟩ := by
      simpa using congrArg Subtype.val hab
    exact Subtype.ext (hdet a b (hfix_z a) (hfix_z b) hval)
  have hcard : Nat.card {w : centerIn (J z) //
      w = ⟨z1, hz1_mem⟩ ∨ w = ⟨z * z1, hzz1_mem⟩} = 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hfilter : (Finset.univ.filter fun w : centerIn (J z) =>
        w = ⟨z1, hz1_mem⟩ ∨ w = ⟨z * z1, hzz1_mem⟩) =
        {⟨z1, hz1_mem⟩, ⟨z * z1, hzz1_mem⟩} := by
      ext w
      simp
    rw [hfilter, Finset.card_pair hzz1_ne]
  have hrange : Nat.card (conjZ z).range ≤ 2 :=
    (Nat.card_le_card_of_injective _ hinj).trans_eq hcard
  have hker : Subgroup.centralizer ((centerIn (J z)).subgroupOf (H z) : Set ↥(H z)) =
      (conjZ z).ker := by
    ext g
    rw [Subgroup.mem_centralizer_iff, MonoidHom.mem_ker]
    constructor
    · intro hg
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      rw [conjZ_apply_coe]
      have hy : (⟨(x : G), centerIn_le_H (z := z) x.2⟩ : ↥(H z)) ∈
          (centerIn (J z)).subgroupOf (H z) := Subgroup.mem_subgroupOf.mpr x.2
      have h1 : (x : G) * (g : G) = (g : G) * (x : G) := by
        simpa using congrArg Subtype.val (hg _ hy)
      show (g : G) * (x : G) * (g : G)⁻¹ = (x : G)
      rw [← h1]
      group
    · intro hg y hy
      have hyZ : (y : G) ∈ centerIn (J z) := Subgroup.mem_subgroupOf.mp hy
      have hfix := congrArg (fun a : MulAut (centerIn (J z)) => a ⟨(y : G), hyZ⟩) hg
      have h1 := congrArg (fun t : centerIn (J z) => (t : G)) hfix
      rw [conjZ_apply_coe] at h1
      have h2 : (g : G) * (y : G) * (g : G)⁻¹ = (y : G) := by simpa using h1
      have h3 : (g : G) * (y : G) = (y : G) * (g : G) := by
        simpa [mul_assoc] using congrArg (fun t => t * (g : G)) h2
      exact Subtype.ext h3.symm
  rw [hker, Subgroup.index_ker]
  exact hrange

end

end CFSG.RankThree.GF2n.Parrott
