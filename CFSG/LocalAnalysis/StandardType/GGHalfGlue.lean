module

public import CFSG.LocalAnalysis.StandardType.GGHalfTorusNormalizer
public import CFSG.LocalAnalysis.StandardType.GGHalfBlockCentral
public import CFSG.LocalAnalysis.StandardType.GGHalfBlockEmbed
public import CFSG.LocalAnalysis.StandardType.GGHalfSlOnLevi

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

namespace GGHalfCtx

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J K : Subgroup G} {m : ℕ} {y : G}
  {φ₁ φ₂ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G}

private theorem inv_mul_centralizes_of_conj {G : Type} [Group G] {L : Subgroup G} {m : ℕ}
    {φ₁ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G} {b : G}
    {t : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2}
    (htl : ∀ l ∈ L, b * l * b⁻¹ = φ₁ t * l * (φ₁ t)⁻¹) :
    ∀ l ∈ L, (φ₁ t)⁻¹ * b * l = l * ((φ₁ t)⁻¹ * b) := by
  intro l hl
  have h1 : b * l = φ₁ t * l * (φ₁ t)⁻¹ * b := by
    calc b * l = b * l * b⁻¹ * b := by group
      _ = φ₁ t * l * (φ₁ t)⁻¹ * b := by rw [htl l hl]
  calc (φ₁ t)⁻¹ * b * l = (φ₁ t)⁻¹ * (b * l) := by group
    _ = (φ₁ t)⁻¹ * (φ₁ t * l * (φ₁ t)⁻¹ * b) := by rw [h1]
    _ = l * ((φ₁ t)⁻¹ * b) := by group

variable (h : GGHalfCtx p B Bs x L D J m y K φ₁ φ₂)

include h

theorem bs_eq_sup : Bs = Subgroup.zpowers x ⊔ (halfTorus (m + 1 + 1)).map φ₁ ∧
    Disjoint (Subgroup.zpowers x) ((halfTorus (m + 1 + 1)).map φ₁) := by
  obtain ⟨_, _, hxB, _, _, _, hxL, _, _, hcent⟩ := h.basic
  constructor
  · apply le_antisymm
    · intro b hb
      obtain ⟨t, ht, htl⟩ := h.coords.actL b hb
      have hφtB : φ₁ t ∈ Bs := h.torusL_le (Subgroup.mem_map.mpr ⟨t, ht, rfl⟩)
      have hb'B : (φ₁ t)⁻¹ * b ∈ Bs := Bs.mul_mem (Bs.inv_mem hφtB) hb
      have hb'z : (φ₁ t)⁻¹ * b ∈ Subgroup.zpowers x :=
        hcent _ hb'B (inv_mul_centralizes_of_conj htl)
      have heq : b = φ₁ t * ((φ₁ t)⁻¹ * b) := by group
      rw [heq]
      have hmem : φ₁ t * ((φ₁ t)⁻¹ * b) ∈
          (halfTorus (m + 1 + 1)).map φ₁ ⊔ Subgroup.zpowers x :=
        Subgroup.mul_mem_sup (Subgroup.mem_map.mpr ⟨t, ht, rfl⟩) hb'z
      rwa [sup_comm] at hmem
    · exact sup_le (Subgroup.zpowers_le.mpr hxB) h.torusL_le
  · rw [Subgroup.disjoint_def]
    intro g hgx hgt
    obtain ⟨t, ht, hgt'⟩ := Subgroup.mem_map.mp hgt
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hgx
    have hcommL : ∀ s, φ₁ t * φ₁ s = φ₁ s * φ₁ t := by
      intro s
      have hsL : φ₁ s ∈ L := by rw [← h.coords.range₁]; exact ⟨s, rfl⟩
      have hc : Commute x (φ₁ s) := hxL (φ₁ s) hsL
      have hxk : Commute (x ^ k) (φ₁ s) := hc.zpow_left k
      rw [hgt', ← hk]
      exact hxk
    have ht1 : t = 1 := eq_one_of_commute_range h.coords.inj₁ hcommL
    rw [← hgt', ht1, map_one]

theorem vElt_mem : vElt φ₁ ∈ Bs :=
  h.torusL_le (Subgroup.mem_map.mpr
    ⟨omegaBlock (m + 1 + 1) ⟨0, by omega⟩,
      Subgroup.subset_closure ⟨⟨0, by omega⟩, by simp, rfl⟩, rfl⟩)

theorem uElt_mem : uElt φ₂ ∈ Bs :=
  h.torusK_le (Subgroup.mem_map.mpr
    ⟨omegaBlock (m + 1 + 1) ⟨0, by omega⟩,
      Subgroup.subset_closure
        ⟨⟨0, by omega⟩, Or.inr ⟨by simp, by
          have h5 := h.nbr.2.2.1
          simp only [Fin.val_mk]
          omega⟩, rfl⟩, rfl⟩)

theorem wElt_mem : wElt φ₂ ∈ Bs :=
  h.torusK_le (Subgroup.mem_map.mpr
    ⟨omegaBlock (m + 1 + 1) ⟨m + 1, by omega⟩,
      Subgroup.subset_closure ⟨⟨m + 1, by omega⟩,
        Or.inl (by simp only [Fin.val_mk]), rfl⟩, rfl⟩)

theorem uElt_eq :
    uElt φ₂ = φ₁ (omegaBlock (m + 1 + 1) ⟨2, by have := h.nbr.2.2.1; omega⟩) := by
  have hm : 0 < m := by have := h.nbr.2.2.1; omega
  have hagree : (φ₁.comp (slLower2Hom m)) (omegaBlock m ⟨0, hm⟩) =
      (φ₂.comp (slUpper2Hom m)) (omegaBlock m ⟨0, hm⟩) := by rw [h.coords.agree]
  simp only [MonoidHom.comp_apply] at hagree
  rw [slLower2Hom_omegaBlock, slUpper2Hom_omegaBlock] at hagree
  simp only [Fin.val_zero, Nat.zero_add] at hagree
  simpa only [uElt] using hagree.symm

theorem exists_eq_x_pow_mul_v_pow {b : G} (hb : b ∈ Bs) (hbJ : ∀ j ∈ J, b * j = j * b) :
    ∃ i j : ℤ, b = x ^ i * vElt φ₁ ^ j := by
  obtain ⟨hcomm, _, hxB, _, _, _, _, _, _, hcent⟩ := h.basic
  have hm : 0 < m := by have := h.nbr.2.2.1; omega
  obtain ⟨t, ht, htl⟩ := h.coords.actL b hb
  have hφtB : φ₁ t ∈ Bs := h.torusL_le (Subgroup.mem_map.mpr ⟨t, ht, rfl⟩)
  have hb'B : (φ₁ t)⁻¹ * b ∈ Bs := Bs.mul_mem (Bs.inv_mem hφtB) hb
  have hb'z : (φ₁ t)⁻¹ * b ∈ Subgroup.zpowers x :=
    hcent _ hb'B (inv_mul_centralizes_of_conj htl)
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hb'z
  have htcomm : ∀ s : SpecialLinearGroup (Fin (m + 1)) F2,
      t * slLower2Hom m s = slLower2Hom m s * t := by
    intro s
    apply h.coords.inj₁
    rw [map_mul, map_mul]
    have hsL : φ₁ (slLower2Hom m s) ∈ L := by
      rw [← h.coords.range₁]; exact ⟨slLower2Hom m s, rfl⟩
    have hsJ : φ₁ (slLower2Hom m s) ∈ J := by
      rw [← h.coords.rangeJ]; exact ⟨s, rfl⟩
    have hconj := htl (φ₁ (slLower2Hom m s)) hsL
    have hbJ' := hbJ (φ₁ (slLower2Hom m s)) hsJ
    have h1 : φ₁ t * φ₁ (slLower2Hom m s) * (φ₁ t)⁻¹ = φ₁ (slLower2Hom m s) := by
      rw [← hconj, hbJ']
      group
    calc φ₁ t * φ₁ (slLower2Hom m s)
        = φ₁ t * φ₁ (slLower2Hom m s) * (φ₁ t)⁻¹ * φ₁ t := by group
      _ = φ₁ (slLower2Hom m s) * φ₁ t := by rw [h1]
  have htZ : t ∈ Subgroup.zpowers (omegaBlock (m + 1 + 1) ⟨0, by omega⟩) :=
    mem_zpowers_omegaBlock_of_commute_lower ht htcomm
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp htZ
  refine ⟨i, j, ?_⟩
  have hval : vElt φ₁ ^ j = φ₁ t := by
    rw [show vElt φ₁ = φ₁ (omegaBlock (m + 1 + 1) ⟨0, by omega⟩) from rfl,
      ← map_zpow, hj]
  have hb_eq : b = φ₁ t * x ^ i := by
    calc b = φ₁ t * ((φ₁ t)⁻¹ * b) := by group
      _ = φ₁ t * x ^ i := by rw [hi.symm]
  rw [hval, hb_eq]
  exact Commute.zpow_right (hcomm (φ₁ t) hφtB x hxB) i

theorem independent {p q r : ℤ} (hpqr : x ^ p * vElt φ₁ ^ q * uElt φ₂ ^ r = 1) :
    (3 : ℤ) ∣ p ∧ (3 : ℤ) ∣ q ∧ (3 : ℤ) ∣ r := by
  obtain ⟨_, hexp, hxB, _, hx1, _, _, _, _, _⟩ := h.basic
  have hm : 0 < m := by have := h.nbr.2.2.1; omega
  have hx3 : x ^ (3 : ℕ) = 1 := hexp x hxB
  have hv_mem : vElt φ₁ ∈ (halfTorus (m + 1 + 1)).map φ₁ :=
    Subgroup.mem_map.mpr
      ⟨omegaBlock (m + 1 + 1) ⟨0, by omega⟩,
        Subgroup.subset_closure ⟨⟨0, by omega⟩, by simp, rfl⟩, rfl⟩
  have hu_mem : uElt φ₂ ∈ (halfTorus (m + 1 + 1)).map φ₁ := by
    rw [uElt_eq h]
    apply Subgroup.mem_map.mpr
    refine ⟨slLower2Hom m (omegaBlock m ⟨0, hm⟩), ?_, ?_⟩
    · rw [slLower2Hom_omegaBlock]
      exact Subgroup.subset_closure
        ⟨⟨0 + 2, by omega⟩, by simp, rfl⟩
    · rw [slLower2Hom_omegaBlock]
  have hxT : x ^ p ∈ (halfTorus (m + 1 + 1)).map φ₁ := by
    have h1 : x ^ p = (vElt φ₁ ^ q * uElt φ₂ ^ r)⁻¹ := by
      have h2 : x ^ p * (vElt φ₁ ^ q * uElt φ₂ ^ r) = 1 := by
        simpa only [mul_assoc] using hpqr
      calc x ^ p = x ^ p * (vElt φ₁ ^ q * uElt φ₂ ^ r) *
            (vElt φ₁ ^ q * uElt φ₂ ^ r)⁻¹ := by group
        _ = 1 * (vElt φ₁ ^ q * uElt φ₂ ^ r)⁻¹ := by rw [h2]
        _ = (vElt φ₁ ^ q * uElt φ₂ ^ r)⁻¹ := by rw [one_mul]
    rw [h1]
    exact Subgroup.inv_mem _
      (Subgroup.mul_mem _ (Subgroup.zpow_mem _ hv_mem q) (Subgroup.zpow_mem _ hu_mem r))
  have hxp1 : x ^ p = 1 := by
    have hdisj := (bs_eq_sup h).2
    rw [Subgroup.disjoint_def] at hdisj
    exact hdisj (Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) p) hxT
  have hpdvd : (3 : ℤ) ∣ p := by
    have hxord : orderOf x = 3 := by
      haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
      exact orderOf_eq_prime hx3 hx1
    have := orderOf_dvd_iff_zpow_eq_one.mpr hxp1
    rwa [hxord] at this
  have hvur : vElt φ₁ ^ q * uElt φ₂ ^ r = 1 := by
    have := hpqr
    rw [hxp1, one_mul] at this
    exact this
  have hvq : vElt φ₁ ^ q = φ₁ ((omegaBlock (m + 1 + 1) ⟨0, by omega⟩) ^ q) := by
    rw [show vElt φ₁ = φ₁ (omegaBlock (m + 1 + 1) ⟨0, by omega⟩) from rfl, map_zpow]
  have hu_eq : uElt φ₂ = φ₁ (slLower2Hom m (omegaBlock m ⟨0, hm⟩)) := by
    rw [uElt_eq h, slLower2Hom_omegaBlock]
  have hur : uElt φ₂ ^ r = φ₁ ((slLower2Hom m (omegaBlock m ⟨0, hm⟩)) ^ r) := by
    rw [hu_eq, map_zpow]
  have hmap1 : (omegaBlock (m + 1 + 1) ⟨0, by omega⟩) ^ q *
      (slLower2Hom m (omegaBlock m ⟨0, hm⟩)) ^ r = 1 := by
    apply h.coords.inj₁
    rw [map_mul, map_one, ← hvq, ← hur]
    exact hvur
  have hmem1 : (omegaBlock (m + 1 + 1) ⟨0, by omega⟩) ^ q ∈
      Subgroup.zpowers (omegaBlock (m + 1 + 1) ⟨0, by omega⟩) :=
    Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) q
  have hmem2 : (omegaBlock (m + 1 + 1) ⟨0, by omega⟩) ^ q ∈
      (halfTorus m).map (slLower2Hom m) := by
    have hω0_eq : (omegaBlock (m + 1 + 1) ⟨0, by omega⟩) ^ q =
        ((slLower2Hom m (omegaBlock m ⟨0, hm⟩)) ^ r)⁻¹ := by
      calc (omegaBlock (m + 1 + 1) ⟨0, by omega⟩) ^ q
          = (omegaBlock (m + 1 + 1) ⟨0, by omega⟩) ^ q *
              (slLower2Hom m (omegaBlock m ⟨0, hm⟩)) ^ r *
              ((slLower2Hom m (omegaBlock m ⟨0, hm⟩)) ^ r)⁻¹ := by group
        _ = 1 * ((slLower2Hom m (omegaBlock m ⟨0, hm⟩)) ^ r)⁻¹ := by rw [hmap1]
        _ = ((slLower2Hom m (omegaBlock m ⟨0, hm⟩)) ^ r)⁻¹ := by rw [one_mul]
    rw [hω0_eq]
    apply Subgroup.inv_mem
    rw [← map_zpow]
    have ha : omegaBlock m ⟨0, hm⟩ ∈ halfTorus m :=
      Subgroup.subset_closure ⟨⟨0, hm⟩, by simp, rfl⟩
    refine Subgroup.mem_map.mpr ?_
    exact ⟨(omegaBlock m ⟨0, hm⟩) ^ r, Subgroup.zpow_mem _ ha r, rfl⟩
  have hω0 : (omegaBlock (m + 1 + 1) ⟨0, by omega⟩) ^ q = 1 := by
    have hdisj := disjoint_zpowers_omegaBlock_lower m
    rw [Subgroup.disjoint_def] at hdisj
    exact hdisj hmem1 hmem2
  have hq : (3 : ℤ) ∣ q := by
    have hω0ord : orderOf (omegaBlock (m + 1 + 1) ⟨0, by omega⟩) = 3 := by
      haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
      exact orderOf_eq_prime (omegaBlock_pow_three _ _) (omegaBlock_ne_one _ _)
    have := orderOf_dvd_iff_zpow_eq_one.mpr hω0
    rwa [hω0ord] at this
  have hω2 : (slLower2Hom m (omegaBlock m ⟨0, hm⟩)) ^ r = 1 := by
    have := hmap1
    rw [hω0, one_mul] at this
    exact this
  have har : (omegaBlock m ⟨0, hm⟩) ^ r = 1 := by
    apply slLower2Hom_injective m
    rw [map_one, map_zpow]
    exact hω2
  have hr : (3 : ℤ) ∣ r := by
    have haord : orderOf (omegaBlock m ⟨0, hm⟩) = 3 := by
      haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
      exact orderOf_eq_prime (omegaBlock_pow_three m ⟨0, hm⟩) (omegaBlock_ne_one m ⟨0, hm⟩)
    have := orderOf_dvd_iff_zpow_eq_one.mpr har
    rwa [haord] at this
  exact ⟨hpdvd, hq, hr⟩

theorem zSet_le : zSet φ₁ ⊆ Bs := by
  intro z hz
  simp only [zSet, Set.mem_setOf_eq] at hz
  obtain ⟨k, hk2, -, rfl⟩ := hz
  exact h.torusL_le (Subgroup.mem_map.mpr
    ⟨omegaBlock (m + 1 + 1) k, Subgroup.subset_closure ⟨k, hk2, rfl⟩, rfl⟩)

theorem bs_le_closure :
    Bs ≤ Subgroup.closure ({x, vElt φ₁, uElt φ₂} ∪ zSet φ₁) := by
  rw [(bs_eq_sup h).1]
  apply sup_le
  · rw [Subgroup.zpowers_le]
    exact Subgroup.subset_closure (Or.inl (by simp))
  · unfold halfTorus
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro z ⟨t, ht, rfl⟩
    obtain ⟨k, hk2, rfl⟩ := ht
    apply Subgroup.subset_closure
    by_cases hk0 : k.val = 0
    · left
      have hk_eq : k = ⟨0, by omega⟩ := Fin.ext hk0
      have hval : φ₁ (omegaBlock (m + 1 + 1) k) = vElt φ₁ := by
        rw [hk_eq]
        rfl
      rw [hval]
      simp
    · by_cases hk2' : k.val = 2
      · left
        have hk_eq : k = ⟨2, by have := h.nbr.2.2.1; omega⟩ := Fin.ext hk2'
        have hval : φ₁ (omegaBlock (m + 1 + 1) k) = uElt φ₂ := by
          rw [hk_eq, ← uElt_eq h]
        rw [hval]
        simp
      · right
        have hk4 : 4 ≤ k.val := by
          obtain ⟨c, hc⟩ := (Nat.dvd_iff_mod_eq_zero).mpr hk2
          omega
        exact ⟨k, hk2, hk4, rfl⟩

end GGHalfCtx

end CFSG.StandardType

end
