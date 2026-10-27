module

public import CFSG.Quasithin.Vol2.Ch10SecA1012P5Fix
public import CFSG.Quasithin.Vol2.Ch10SecAFactsTorus
public import CFSG.Quasithin.Vol2.Ch10SecA1012P5Vec

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem centralizes_of_case_seven (hFS : FactSzTorus) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Ch10.Hyp10 G T L I)
    (h7 : Ch10.Case10_1_1Seven T L I) (hC0 : fsuCVM T L I = ⊥) {y : G} (hyL0 : y ∈ fsuL0 T L)
    (hyodd : Odd (orderOf y)) (hyN : y ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G))
    {w : G} (hwU : w ∈ fsuUL T L I) (hwC : w ∉ fsuCVM T L I)
    (hwS : ∀ s ∈ T ⊓ L, s * w * s⁻¹ * w⁻¹ ∈ fsuCVM T L I)
    (hwy : y * w * y⁻¹ * w⁻¹ ∈ fsuCVM T L I) : ∀ u ∈ fsuUL T L I, y * u * y⁻¹ = u := by
  obtain ⟨n, -, hUab, hSz⟩ := h7
  have hloc := hyp.fsu.maximal.1
  have hL0U : fsuL0 T L ≤ Subgroup.normalizer (fsuUL T L I : Set G) :=
    le_normalizer_commutator (fsuL0_le_normalizer_fsuVM T L I) (fsuL0_le_normalizer hloc)
  rw [hC0] at hwC hwS hwy
  have hφ1 : conjAct (fsuUL T L I) ⟨y, hL0U hyL0⟩ = 1 := by
    refine hFS ↥(fsuUL T L I) (autOn L (fsuUL T L I)) n hSz _ (isSylowTwoOf_autOn_inf hyp) _
      (conjAct_mem_autOn_of_mem_fsuL0 h37 h38 hyp hyL0 (hL0U hyL0))
      (conjAct_mem_normalizer_autOn (hL0U hyL0) hyN) (odd_orderOf_conjAct (hL0U hyL0) hyodd)
      ⟨w, hwU⟩ (fun h => hwC (Subgroup.mem_bot.mpr (congrArg Subtype.val h))) ?_ ?_
    · intro p hp
      obtain ⟨g, hgK, rfl⟩ := mem_autOn_iff'.mp hp
      apply Subtype.ext
      rw [coe_conjAct_apply']
      exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp (hwS g hgK))
    · apply Subtype.ext
      rw [coe_conjAct_apply']
      exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp hwy)
  intro u hu
  have h5 := congrArg (fun f : MulAut ↥(fsuUL T L I) => ((f ⟨u, hu⟩ : ↥(fsuUL T L I)) : G)) hφ1
  simp only [coe_conjAct_apply', MulAut.one_apply] at h5
  exact h5

theorem inf_centralizer_eq_bot_of_case_seven
    (hFS : FactSzTorus) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h322 : TmpL6_3_2_2_two) (hyp : Ch10.Hyp10 G T L I)
    (h7 : Ch10.Case10_1_1Seven T L I) (hC0 : fsuCVM T L I = ⊥) {D : Subgroup G}
    (hD : Lin2.IsHallTwoPrimeOf D (B0 T L)) :
    D ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) = ⊥ := by
  obtain ⟨t, ht, htn⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) := by
    by_contra h
    push Not at h
    exact hyp.not_normal h
  obtain ⟨v, hvU, hvC, hvS⟩ := exists_mem_centralizer_of_fsuCVM_eq_bot hyp hC0
  obtain ⟨w₁, hw₁U, hw₁C, hw₁S, w₂, hw₂U, hw₂C, hw₂S, hx⟩ :=
    exists_vectors h37 h38 h322 hyp ht htn hD hvU hvC hvS
  rw [eq_bot_iff]
  intro x hxDZ
  rw [Subgroup.mem_bot]
  have hxX := oTwoUpper_le _ (hD.1 hxDZ.1)
  have hxodd : Odd (orderOf x) := Odd.of_dvd_nat hD.2.1 (Subgroup.orderOf_dvd_natCard _ hxDZ.1)
  obtain ⟨hx1, hx2⟩ := hx x hxDZ
  have hS : ∀ {K : Subgroup G} {w : G}, w ∈ Subgroup.centralizer (K : Set G) →
      ∀ s ∈ K, s * w * s⁻¹ * w⁻¹ ∈ fsuCVM T L I := by
    intro K w hw s hs
    rw [Subgroup.mem_centralizer_iff.mp hw s hs, mul_inv_cancel_right, mul_inv_cancel]
    exact Subgroup.one_mem _
  exact eq_one_of_centralizes h37 h38 hyp
    (fun y hyL0 hyodd hyN w hwU hwC hwS hwy =>
      centralizes_of_case_seven hFS h37 h38 hyp h7 hC0 hyL0 hyodd hyN hwU hwC hwS hwy)
    ht htn hxX.1 hxX.2 hxodd hw₁U hw₁C (hS hw₁S) hx1 hw₂U hw₂C (hS hw₂S) hx2

end CFSG.Quasithin.Vol2.Ch10.SecA
