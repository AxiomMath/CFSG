module

public import CFSG.RankThree.Co2.DistCert
public import CFSG.RankThree.Co2.Fusion

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.Co2

open CFSG.Monster CFSG.Monster.B.Co2 CFSG.Monster.B.Short CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Census CFSG.Monster.B.TwoA.Co2Inv

theorem subW_eq_C4 : subW pWords4 = Subgroup.centralizer ({rep 4} : Set Cr) :=
  Subgroup.eq_of_le_of_card_ge sylLe4 (by
    rw [card_C 4 (by norm_num) (m := 32768) (by decide) (classSizes_pos (by norm_num)), sylCard4]
    norm_num)

theorem pWords4_letters : ∀ k < pWords4.size, ∀ l ∈ pWords4[k]!, l < 42 := by
  decide +kernel

theorem not_mem_class_of_central4 {y : Cr} (hy : y ∈ Subgroup.centralizer ({rep 4} : Set Cr))
    (hc : ∀ x ∈ Subgroup.centralizer ({rep 4} : Set Cr), x * y = y * x) :
    ¬ IsConj (rep 2) y ∧ ¬ IsConj (rep 7) y := by
  rw [← subW_eq_C4] at hy hc
  have hcard : Nat.card (matGrp pWords4) ≤ 2 ^ 15 :=
    (card_matGrp_le pWords4_letters).trans
      (le_of_eq sylCard4)
  have hm : crMat y ∈ matGrp pWords4 := map_subW_le pWords4_letters ⟨y, hy, rfl⟩
  have hz : ∀ z ∈ matGrp pWords4, crMat y * z = z * crMat y := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := matGrp_le_map pWords4_letters hz
    rw [← map_mul, ← map_mul, hc x hx]
  obtain ⟨h2, h7⟩ := zp4Facts_cert hcard _ hm hz
  exact ⟨fun h => h2 ((isConj_iff_crConj (by norm_num)).1 h),
    fun h => h7 ((isConj_iff_crConj (by norm_num)).1 h)⟩

namespace Co2CentHyp

variable {G : Type} [Group G] (h : Co2CentHyp G)

abbrev rG (c : ℕ) : G := ((h.φ.symm (rep c) : h.H) : G)

theorem rG_zero : h.rG 0 = h.z := by
  show ((h.φ.symm (rep 0) : h.H) : G) = h.z
  rw [rep_zero, h.φ_symm_rCr]
  rfl

@[expose] def liftG (S : Subgroup Cr) : Subgroup G :=
  (S.map h.φ.symm.toMonoidHom).map h.H.subtype

theorem φ_symm_mem_liftG {S : Subgroup Cr} {y : Cr} (hy : y ∈ S) :
    ((h.φ.symm y : h.H) : G) ∈ h.liftG S :=
  ⟨_, ⟨y, hy, rfl⟩, rfl⟩

theorem mem_liftG {S : Subgroup Cr} {x : G} :
    x ∈ h.liftG S ↔ ∃ hx : x ∈ h.H, h.φ ⟨x, hx⟩ ∈ S := by
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨(h.φ.symm y).2, ?_⟩
    have e : h.φ ⟨((h.φ.symm y : h.H) : G), (h.φ.symm y).2⟩ = y := h.φ.apply_symm_apply y
    show h.φ ⟨((h.φ.symm y : h.H) : G), (h.φ.symm y).2⟩ ∈ S
    rw [e]
    exact hy
  · rintro ⟨hx, hS⟩
    refine ⟨⟨x, hx⟩, ⟨h.φ ⟨x, hx⟩, hS, ?_⟩, rfl⟩
    exact h.φ.symm_apply_apply _

theorem card_liftG (S : Subgroup Cr) : Nat.card (h.liftG S) = Nat.card S := by
  rw [liftG, Subgroup.card_map_of_injective h.H.subtype_injective,
    Subgroup.card_map_of_injective h.φ.symm.injective]

theorem liftG_le_H (S : Subgroup Cr) : h.liftG S ≤ h.H := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

theorem commute_iff (a : h.H) (x : Cr) :
    (a : G) * (h.φ.symm x : G) = (h.φ.symm x : G) * a ↔ h.φ a * x = x * h.φ a := by
  constructor
  · intro e
    have e' : a * h.φ.symm x = h.φ.symm x * a := Subtype.ext e
    have := congrArg h.φ e'
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at this
  · intro e
    have e' : a * h.φ.symm x = h.φ.symm x * a := by
      apply h.φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, e]
    exact congrArg Subtype.val e'

theorem inf_centralizer (x : Cr) :
    Subgroup.centralizer {h.z} ⊓ Subgroup.centralizer {((h.φ.symm x : h.H) : G)} =
      h.liftG (Subgroup.centralizer {x}) := by
  ext g
  rw [Subgroup.mem_inf, h.mem_liftG]
  constructor
  · rintro ⟨hg, hgx⟩
    refine ⟨hg, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hgx ⊢
    exact (h.commute_iff ⟨g, hg⟩ x).1 hgx
  · rintro ⟨hg, hgx⟩
    refine ⟨hg, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hgx ⊢
    exact (h.commute_iff ⟨g, hg⟩ x).2 hgx

theorem liftG_le_centralizer {S : Subgroup Cr} {x : Cr} (hS : S ≤ Subgroup.centralizer {x}) :
    h.liftG S ≤ Subgroup.centralizer {((h.φ.symm x : h.H) : G)} := by
  intro g hg
  obtain ⟨hgH, hgS⟩ := h.mem_liftG.1 hg
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (h.commute_iff ⟨g, hgH⟩ x).2 (Subgroup.mem_centralizer_singleton_iff.1 (hS hgS))

theorem factorization_card_C4 :
    (Nat.card (Subgroup.centralizer ({h.rG 4} : Set G))).factorization 2 = 15 := by
  haveI := h.finite
  have hT₁C : h.liftG (Subgroup.centralizer {rep 4}) ≤
      Subgroup.centralizer ({h.rG 4} : Set G) :=
    h.liftG_le_centralizer le_rfl
  have hcard : Nat.card ((h.liftG (Subgroup.centralizer {rep 4})).subgroupOf
      (Subgroup.centralizer ({h.rG 4} : Set G))) = 2 ^ 15 := by
    rw [card_subgroupOf_eq hT₁C, card_liftG, ← subW_eq_C4, sylCard4]
  have hN : Subgroup.normalizer
      (((h.liftG (Subgroup.centralizer {rep 4})).subgroupOf
        (Subgroup.centralizer ({h.rG 4} : Set G)) : Subgroup _) : Set _) ≤
      (h.liftG (Subgroup.centralizer {rep 4})).subgroupOf
        (Subgroup.centralizer ({h.rG 4} : Set G)) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff] at hn
    have hzC : h.z ∈ Subgroup.centralizer ({h.rG 4} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.1 (h.φ.symm (rep 4)).2).symm
    have hzT : h.z ∈ h.liftG (Subgroup.centralizer {rep 4}) := by
      rw [← h.rG_zero]
      apply h.φ_symm_mem_liftG
      rw [Subgroup.mem_centralizer_singleton_iff, rep_zero]
      exact (Subgroup.mem_center_iff.1 rCr_mem_center (rep 4)).symm
    have hu : (n : G) * h.z * (n : G)⁻¹ ∈ h.liftG (Subgroup.centralizer {rep 4}) :=
      Subgroup.mem_subgroupOf.1 ((hn ⟨h.z, hzC⟩).1 (Subgroup.mem_subgroupOf.2 hzT))
    obtain ⟨huH, huC⟩ := h.mem_liftG.1 hu
    have hcen : ∀ x ∈ Subgroup.centralizer ({rep 4} : Set Cr),
        x * h.φ ⟨_, huH⟩ = h.φ ⟨_, huH⟩ * x := by
      intro x hx
      have hxT : ((h.φ.symm x : h.H) : G) ∈ h.liftG (Subgroup.centralizer {rep 4}) :=
        h.φ_symm_mem_liftG hx
      have hmemC : (n : G)⁻¹ * (h.φ.symm x : G) * n ∈
          Subgroup.centralizer ({h.rG 4} : Set G) :=
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ n.2) (hT₁C hxT)) n.2
      have hn' : (n : G)⁻¹ * (h.φ.symm x : G) * n ∈ h.liftG (Subgroup.centralizer {rep 4}) := by
        refine Subgroup.mem_subgroupOf.1 ((hn ⟨_, hmemC⟩).2 (Subgroup.mem_subgroupOf.2 ?_))
        have e : ((n * ⟨_, hmemC⟩ * n⁻¹ : Subgroup.centralizer ({h.rG 4} : Set G)) : G) =
            (h.φ.symm x : G) := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
        rw [e]
        exact hxT
      have hzc : (n : G)⁻¹ * (h.φ.symm x : G) * n * h.z =
          h.z * ((n : G)⁻¹ * (h.φ.symm x : G) * n) :=
        Subgroup.mem_centralizer_singleton_iff.1 (h.liftG_le_H _ hn')
      have hux : ((h.φ.symm x : h.H) : G) * ((n : G) * h.z * (n : G)⁻¹) =
          ((n : G) * h.z * (n : G)⁻¹) * (h.φ.symm x : G) := by
        calc ((h.φ.symm x : h.H) : G) * ((n : G) * h.z * (n : G)⁻¹) =
            (n : G) * (((n : G)⁻¹ * (h.φ.symm x : G) * n) * h.z) * (n : G)⁻¹ := by group
          _ = (n : G) * (h.z * ((n : G)⁻¹ * (h.φ.symm x : G) * n)) * (n : G)⁻¹ := by rw [hzc]
          _ = ((n : G) * h.z * (n : G)⁻¹) * (h.φ.symm x : G) := by group
      exact ((h.commute_iff ⟨_, huH⟩ x).1 hux.symm).symm
    have hφu : h.φ ⟨_, huH⟩ = rCr := by
      have hzu : IsConj h.z (((⟨_, huH⟩ : h.H)) : G) := isConj_iff.2 ⟨(n : G), rfl⟩
      rcases (h.isConj_z_iff ⟨_, huH⟩).1 hzu with e | e | e
      · exact e
      · exact absurd e.symm (not_mem_class_of_central4 huC hcen).1
      · exact absurd e.symm (not_mem_class_of_central4 huC hcen).2
    have hnz : (n : G) * h.z * (n : G)⁻¹ = h.z := by
      have : (⟨_, huH⟩ : h.H) = h.zG := by
        apply h.φ.injective
        rw [hφu, h.φ_zG]
      exact congrArg Subtype.val this
    have hnH : (n : G) ∈ h.H := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (n : G) * h.z = (n : G) * h.z * (n : G)⁻¹ * n := by group
        _ = h.z * n := by rw [hnz]
    rw [Subgroup.mem_subgroupOf, h.mem_liftG]
    refine ⟨hnH, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (h.commute_iff ⟨_, hnH⟩ (rep 4)).1 (Subgroup.mem_centralizer_singleton_iff.1 n.2)
  obtain ⟨P, hP⟩ := exists_sylow_eq_of_normalizer_le (IsPGroup.of_card hcard) hN
  have h1 := P.card_eq_multiplicity
  rw [hP, hcard] at h1
  exact (Nat.pow_right_injective le_rfl h1).symm

theorem not_isConj_one_four : ¬ IsConj (h.rG 1) (h.rG 4) := by
  haveI := h.finite
  intro hc
  obtain ⟨c, hc⟩ := isConj_iff.1 hc
  have hle : h.liftG (subW pWords1) ≤ Subgroup.centralizer ({h.rG 1} : Set G) :=
    h.liftG_le_centralizer sylLe1
  have hKC : (h.liftG (subW pWords1)).map (MulAut.conj c).toMonoidHom ≤
      Subgroup.centralizer ({h.rG 4} : Set G) := by
    rintro _ ⟨w, hw, rfl⟩
    have hw1 : w * h.rG 1 = h.rG 1 * w := Subgroup.mem_centralizer_singleton_iff.1 (hle hw)
    rw [Subgroup.mem_centralizer_singleton_iff, ← hc]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc c * w * c⁻¹ * (c * h.rG 1 * c⁻¹) = c * (w * h.rG 1) * c⁻¹ := by group
      _ = c * (h.rG 1 * w) * c⁻¹ := by rw [hw1]
      _ = c * h.rG 1 * c⁻¹ * (c * w * c⁻¹) := by group
  have hK : Nat.card (((h.liftG (subW pWords1)).map (MulAut.conj c).toMonoidHom).subgroupOf
      (Subgroup.centralizer ({h.rG 4} : Set G))) = 2 ^ 17 := by
    rw [card_subgroupOf_eq hKC, Subgroup.card_map_of_injective (MulAut.conj c).injective,
      card_liftG, sylCard1]
  obtain ⟨P, hP⟩ := (IsPGroup.of_card hK).exists_le_sylow
  have h1 := Subgroup.card_le_of_le hP
  rw [hK, P.card_eq_multiplicity, h.factorization_card_C4] at h1
  norm_num at h1

end Co2CentHyp

end CFSG.RankThree.Co2
