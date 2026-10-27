module

public import CFSG.OddTranspositions.HalphaQuotient
public import CFSG.GroupTheory.ThreeTranspositions.NoLine

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Bridge.OddTransp CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem not_isSolvable_Halpha_of_meetsSq (hC : HypothesisC D)
    (hsq : MeetsSq (imageClass hC)) : ¬ Group.IsSolvable (Halpha D hC.alpha) := by
  intro hsol
  haveI := hsol
  have htop : CFSG.solvableRadical (Halpha D hC.alpha) = ⊤ :=
    top_le_iff.mp (le_solvableRadical (N := ⊤) Subgroup.normal_top inferInstance)
  have h1 : ∀ x ∈ imageClass hC, x = 1 := by
    rintro x ⟨y, -, rfl⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, htop]
    exact Subgroup.mem_top y
  obtain ⟨u, hu, v, hv, hne, -, -⟩ := hsq
  exact hne ((h1 u hu).trans (h1 v hv).symm)

theorem not_threeTransp_of_meetsSq (hC : HypothesisC D) (hsq : MeetsSq (imageClass hC)) :
    ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ) := by
  intro h3D
  have hHns : ¬ Group.IsSolvable (Halpha D hC.alpha) :=
    not_isSolvable_Halpha_of_meetsSq hC hsq
  have hinv : ∀ d ∈ imageClass hC, orderOf d = 2 := imageClass_involutions hC hHns
  have h3 : ∀ d ∈ imageClass hC, ∀ e ∈ imageClass hC, orderOf (d * e) ≤ 3 := by
    intro d hd e he
    obtain ⟨x, hx, rfl⟩ := hd
    obtain ⟨y, hy, rfl⟩ := he
    have hDx : (x : G) ∈ D :=
      DalphaStar_subset hC.isBlock_alpha ((mem_DstarH_iff hC).mp hx)
    have hDy : (y : G) ∈ D :=
      DalphaStar_subset hC.isBlock_alpha ((mem_DstarH_iff hC).mp hy)
    have hxy : orderOf ((x : G) * (y : G)) ≤ 3 := by
      have h := h3D (x : G) hDx (y : G) hDy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      omega
    have hxy' : orderOf (x * y) ≤ 3 := by
      rw [← Subgroup.orderOf_coe]
      simpa using hxy
    have hdvd : orderOf (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) x *
        QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) y) ∣ orderOf (x * y) := by
      simpa using orderOf_map_dvd
        (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))) (x * y)
    exact (Nat.le_of_dvd (orderOf_pos (x * y)) hdvd).trans hxy'
  have hclass : ∀ d ∈ imageClass hC, ∀ e ∈ imageClass hC,
      ∃ x ∈ Subgroup.closure (imageClass hC), e = x * d * x⁻¹ := by
    obtain ⟨d₀, hclass₀⟩ := imageClass_isClass hC
    intro d hd e he
    have hd' : IsConj d₀ d := by simpa [hclass₀] using hd
    have he' : IsConj d₀ e := by simpa [hclass₀] using he
    obtain ⟨x, hx⟩ := isConj_iff.mp (hd'.symm.trans he')
    exact ⟨x, by rw [imageClass_gen hC]; exact Subgroup.mem_top x, hx.symm⟩
  obtain ⟨u, hu, v, hv, -, -, huv⟩ := hsq
  exact CFSG.GroupTheory.ThreeTranspositions.mul_not_mem hinv h3 hclass hu hv huv

theorem not_threeTransp_of_pow_ne_one (hC : HypothesisC D)
    {x y : Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)}
    (hx : x ∈ imageClass hC) (hy : y ∈ imageClass hC)
    (hxy : ∀ k : ℕ, 0 < k → k ≤ 3 → (x * y) ^ k ≠ 1) :
    ¬ ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ) := by
  intro h3D
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  have h := h3D (a : G) (DalphaStar_subset hC.isBlock_alpha ((mem_DstarH_iff hC).mp ha))
    (b : G) (DalphaStar_subset hC.isBlock_alpha ((mem_DstarH_iff hC).mp hb))
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  refine hxy (orderOf ((a : G) * (b : G))) (by omega) (by omega) ?_
  have hab : (a * b) ^ orderOf ((a : G) * (b : G)) = 1 := by
    apply Subtype.ext
    simpa using pow_orderOf_eq_one ((a : G) * (b : G))
  rw [← map_mul, ← map_pow, hab, map_one]

end CFSG.OddTranspositions.PartFour
