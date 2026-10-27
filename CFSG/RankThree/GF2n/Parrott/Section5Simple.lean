module

public import CFSG.RankThree.GF2n.Parrott.Section5Basic
public import CFSG.RankThree.GF2n.Parrott.Section5Hunt
public import CFSG.RankThree.GF2n.Parrott.Section4Lemma45Aux

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

private theorem z_ne_one_of_parrottHyp (h : Tim79a.ParrottHyp z) : z ≠ 1 := by
  intro hz
  have hordz : orderOf z = 2 := h.1
  rw [hz, orderOf_one] at hordz
  exact absurd hordz (by norm_num)

private theorem eq_one_or_eq_of_mem_center {z₁ : G} (hord : orderOf z₁ = 2)
    (h2 : Nat.card (center (centralizer ({z₁} : Set G))) = 2)
    {y : centralizer ({z₁} : Set G)} (hy : y ∈ center (centralizer ({z₁} : Set G))) :
    (y : G) = 1 ∨ (y : G) = z₁ := by
  have hz₁C : z₁ ∈ centralizer ({z₁} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hz₁_center : (⟨z₁, hz₁C⟩ : centralizer ({z₁} : Set G)) ∈ center _ := by
    rw [Subgroup.mem_center_iff]
    intro c
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp c.2
  have hordC : orderOf (⟨z₁, hz₁C⟩ : centralizer ({z₁} : Set G)) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hord
  have hcenter_eq : Subgroup.zpowers (⟨z₁, hz₁C⟩ : centralizer ({z₁} : Set G)) = center _ :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz₁_center)
      (by rw [h2, Nat.card_zpowers, hordC])
  rw [← hcenter_eq] at hy
  rcases CFSG.GF2Type.Aschbacher1976Full.Z4Q8.mem_zpowers_two hordC hy with h1 | h1
  · exact Or.inl (congrArg Subtype.val h1)
  · exact Or.inr (congrArg Subtype.val h1)

private theorem centralizer_le_of_normal (h : Tim79a.ParrottHyp z) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    (hQ : CFSG.IsQuasisimple (centralizer ({z₁} : Set G)))
    (h2 : Nat.card (center (centralizer ({z₁} : Set G))) = 2)
    {N : Subgroup G} (hN : N.Normal) (hzN : z ∈ N) :
    centralizer ({z₁} : Set G) ≤ N := by
  let C : Subgroup G := centralizer ({z₁} : Set G)
  have hzC : z ∈ C := by
    change z ∈ Subgroup.centralizer ({z₁} : Set G)
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hz₁.2 z (z_mem_J h))
  haveI : (N.subgroupOf C).Normal := hN.subgroupOf C
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hQ (N.subgroupOf C)
    with hle | htop
  · exfalso
    have hzNc : (⟨z, hzC⟩ : C) ∈ N.subgroupOf C := Subgroup.mem_subgroupOf.mpr hzN
    rcases eq_one_or_eq_of_mem_center hord h2 (hle hzNc) with h1 | h1
    · exact z_ne_one_of_parrottHyp h h1
    · apply hz₁z
      rw [← (h1 : z = z₁)]
      exact Subgroup.mem_zpowers z
  · intro c hc
    have hmem : (⟨c, hc⟩ : C) ∈ N.subgroupOf C := by
      rw [htop]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hmem

private theorem H_le_of_normal (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    {N : Subgroup G} (hN : N.Normal) (hCN : centralizer ({z₁} : Set G) ≤ N)
    {y u : G} (hyH : y ∈ H z) (hyz₁ : y ∉ centralizer ({z₁} : Set G))
    (huy : u * y * u⁻¹ ∈ centralizer ({z₁} : Set G)) : H z ≤ N := by
  classical
  let C : Subgroup G := centralizer ({z₁} : Set G)
  have hyN : y ∈ N := by
    have h1 := hN.conj_mem _ (hCN huy) u⁻¹
    rwa [inv_inv, show u⁻¹ * (u * y * u⁻¹) * u = y by group] at h1
  let K : Subgroup G := H z ⊓ C
  let M : Subgroup G := N ⊓ H z
  have hKM : K ≤ M := by
    intro a ha
    exact Subgroup.mem_inf.mpr ⟨hCN ha.2, ha.1⟩
  have hMH : M ≤ H z := inf_le_right
  have hKrel : K.relIndex (H z) = 2 := by
    change (H z ⊓ Subgroup.centralizer ({z₁} : Set G)).relIndex (H z) = 2
    exact relIndex_inf_centralizer_z1 h hZ hz₁ hz₁z hord
  have hmul : K.relIndex M * M.relIndex (H z) = K.relIndex (H z) :=
    Subgroup.relIndex_mul_relIndex (H := K) (K := M) (L := H z) hKM hMH
  have hyM : y ∈ M := Subgroup.mem_inf.mpr ⟨hyN, hyH⟩
  have hyK : y ∉ K := fun hx => hyz₁ hx.2
  have hdvd : K.relIndex M ∣ 2 := by
    rw [← hKrel, ← hmul]
    exact dvd_mul_right _ _
  have hKne : K.relIndex M ≠ 1 := by
    intro hone
    exact hyK (Subgroup.relIndex_eq_one.mp hone hyM)
  have hKtwo : K.relIndex M = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact absurd h1 hKne
    · exact h1
  have hMone : M.relIndex (H z) = 1 := by
    have hm := hmul
    rw [hKrel, hKtwo] at hm
    refine Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) ?_
    simpa using hm
  intro a ha
  exact (Subgroup.mem_inf.mp (Subgroup.relIndex_eq_one.mp hMone ha)).1

theorem isSimpleGroup_of_lemma57 (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    (hO : pPrimeCore 2 G = ⊥)
    (hQ : CFSG.IsQuasisimple (centralizer ({z₁} : Set G)))
    (h2 : Nat.card (center (centralizer ({z₁} : Set G))) = 2)
    {y u : G} (hyH : y ∈ H z) (hyz₁ : y ∉ centralizer ({z₁} : Set G))
    (huy : u * y * u⁻¹ ∈ centralizer ({z₁} : Set G)) :
    IsSimpleGroup G := by
  classical
  have hnt : Nontrivial G := ⟨⟨1, z, (z_ne_one_of_parrottHyp h).symm⟩⟩
  refine ⟨fun N hN => ?_⟩
  by_cases hNbot : N = ⊥
  · exact Or.inl hNbot
  · right
    haveI hN' : N.Normal := hN
    have h2dvd : 2 ∣ Nat.card N := by
      by_contra h2dvd
      have hcop : Nat.Coprime 2 (Nat.card N) :=
        (Nat.prime_two.coprime_iff_not_dvd).mpr h2dvd
      exact hNbot ((pPrimeCore_eq_bot_iff.mp hO) N hN hcop)
    have hzN : z ∈ N := z_mem_of_normal_of_two_dvd h hZ hN h2dvd
    have hCN : centralizer ({z₁} : Set G) ≤ N :=
      centralizer_le_of_normal h hz₁ hz₁z hord hQ h2 hN hzN
    have hHN : H z ≤ N := H_le_of_normal h hZ hz₁ hz₁z hord hN hCN hyH hyz₁ huy
    obtain ⟨T, hT⟩ := exists_isSylowOf 2 (H z)
    have hTtop : IsSylowOf 2 T ⊤ := isSylowOf_top_of_isSylowOf_H_of_ne h hZ T hT
    have hTN : T ≤ N := le_trans hT.le hHN
    have hTsylowN : IsSylowOf 2 T N := by
      have hs := hTtop.inf_of_le_normalizer (N := N) le_top
        (le_of_eq (Subgroup.normalizer_eq_top_iff.mpr hN).symm)
      rwa [inf_eq_left.mpr hTN] at hs
    obtain ⟨Q, hQ⟩ := hTsylowN
    have hfrat : normalizer (T : Set G) ⊔ N = ⊤ := by
      have hs := Sylow.normalizer_sup_eq_top Q
      rwa [hQ] at hs
    rw [eq_top_iff, ← hfrat]
    exact sup_le (le_trans (normalizer_le_H_of_isSylowOf_of_ne h hZ T hT) hHN) le_rfl

theorem fi22_of_lemma57
    (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    (hU : ∃ (_ : ((Subgroup.zpowers z₁).subgroupOf (centralizer ({z₁} : Set G))).Normal)
      (X : Type) (_ : Group X), CFSG.Blueprint.LieModel X .PSU 6 2 1 ∧
        Nonempty (↥(centralizer ({z₁} : Set G)) ⧸
          (Subgroup.zpowers z₁).subgroupOf (centralizer ({z₁} : Set G)) ≃* X))
    (hder : z₁ ∈ ⁅centralizer ({z₁} : Set G), centralizer ({z₁} : Set G)⁆)
    (hO : pPrimeCore 2 G = ⊥)
    {y u : G} (hyH : y ∈ H z) (hyz₁ : y ∉ centralizer ({z₁} : Set G))
    (huy : u * y * u⁻¹ ∈ centralizer ({z₁} : Set G)) :
    CFSG.Blueprint.NativeSporadic.IsSporadic G .Fi22 := by
  have hU' := hU
  obtain ⟨hN, X, hXgrp, hX, ⟨e⟩⟩ := hU'
  letI : Group X := hXgrp
  haveI : ((Subgroup.zpowers z₁).subgroupOf (centralizer ({z₁} : Set G))).Normal := hN
  have hq := quasisimple_centralizer_of_quotient_psu_six (z₁ := z₁) hord hX e hder
  have hsimple : IsSimpleGroup G :=
    isSimpleGroup_of_lemma57 h hZ hz₁ hz₁z hord hO hq.1 hq.2.1 hyH hyz₁ huy
  haveI : IsSimpleGroup G := hsimple
  have hnonab : ∃ a b : G, a * b ≠ b * a :=
    ⟨y, z₁, fun hcomm => hyz₁ (Subgroup.mem_centralizer_singleton_iff.mpr hcomm)⟩
  exact fi22_of_centralizer_quotient_psu_six hnonab hord hU hder

theorem fi22_of_section5_fusion
    (h : Tim79a.ParrottHyp z) (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G}
    (hz₁ : z₁ ∈ centerIn (J z)) (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    (hT2 : (∃ g ∈ centralizer ({z₁} : Set G),
        g * z * g⁻¹ ∈ H z ⊓ centralizer ({z₁} : Set G) ∧ g * z * g⁻¹ ≠ z) →
      ∃ (_ : ((Subgroup.zpowers z₁).subgroupOf (centralizer ({z₁} : Set G))).Normal)
        (X : Type) (_ : Group X), CFSG.Blueprint.LieModel X .PSU 6 2 1 ∧
          Nonempty (↥(centralizer ({z₁} : Set G)) ⧸
            (Subgroup.zpowers z₁).subgroupOf (centralizer ({z₁} : Set G)) ≃* X))
    {g : G} (hg : g ∈ centralizer ({z₁} : Set G))
    (hgz : g * z * g⁻¹ ∈ H z ⊓ centralizer ({z₁} : Set G)) (hgz' : g * z * g⁻¹ ≠ z)
    (hder : z₁ ∈ ⁅centralizer ({z₁} : Set G), centralizer ({z₁} : Set G)⁆)
    {t' j₀ : G} (ht' : orderOf t' = 2) (hzt' : IsConj z t') (hj₀ : j₀ ∈ J z)
    (hj₀c : j₀ ∉ centerIn (J z)) (hconj : IsConj (t' * z) j₀)
    {y u : G} (hyH : y ∈ H z) (hyz₁ : y ∉ centralizer ({z₁} : Set G))
    (huy : u * y * u⁻¹ ∈ centralizer ({z₁} : Set G)) :
    CFSG.Blueprint.NativeSporadic.IsSporadic G .Fi22 := by
  have hO : pPrimeCore 2 G = ⊥ :=
    pPrimeCore_eq_bot_of_fusion h ht' hzt' hj₀ hj₀c hconj
  have hU := hT2 ⟨g, hg, hgz, hgz'⟩
  exact fi22_of_lemma57 h hZ hz₁ hz₁z hord hU hder hO hyH hyz₁ huy

end CFSG.RankThree.GF2n.Parrott
