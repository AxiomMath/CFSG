module

public import CFSG.RankThree.PartOne.KF.SymTorus
public import CFSG.RankThree.PartOne.LSTD.Lines

public section

namespace CFSG.RankThree.PartOne.LSTD

open Matrix CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryCoord CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel

variable {f : ℕ} {K : Type} [Field K]

theorem two_le_of_five_dvd {f : ℕ} (h5 : 5 ∣ 2 ^ f + 1) : 2 ≤ f := by
  by_contra h
  have : f = 0 ∨ f = 1 := by omega
  rcases this with rfl | rfl <;> norm_num at h5

theorem even_of_five_dvd {f : ℕ} (h5 : 5 ∣ 2 ^ f + 1) : Even f := by
  rcases Nat.even_or_odd f with h | ⟨m, rfl⟩
  · exact h
  · exfalso
    have h4 : ∀ m : ℕ, 4 ^ m % 5 = 1 ∨ 4 ^ m % 5 = 4 := by
      intro m
      induction m with
      | zero => simp
      | succ n ih => rw [pow_succ]; omega
    have h2 : 2 ^ (2 * m + 1) = 4 ^ m * 2 := by
      rw [pow_succ, pow_mul]
      norm_num
    rw [h2] at h5
    have := h4 m
    omega

section Torus

variable (hU : UnitaryFieldData 2 f K) (h5 : 5 ∣ 2 ^ f + 1)

include hU h5 in
theorem torusBar_pow_five {x : StatedProj (unitarySU 2 f K 5)} (hx : x ∈ torusBar K f) :
    x ^ 5 = 1 := by
  obtain ⟨v, hv, rfl⟩ := (mem_torusBar_iff hU h5).mp hx
  rw [← map_pow]
  have : tSU hU h5 v hv ^ 5 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, coe_tSU, diagU_pow, show v ^ 5 = 1 from funext hv.1, diagU_one]
    rfl
  rw [this, map_one]

include hU h5 in
theorem torusBar_comm {x y : StatedProj (unitarySU 2 f K 5)} (hx : x ∈ torusBar K f)
    (hy : y ∈ torusBar K f) : x * y = y * x := by
  obtain ⟨v, hv, rfl⟩ := (mem_torusBar_iff hU h5).mp hx
  obtain ⟨w, hw, rfl⟩ := (mem_torusBar_iff hU h5).mp hy
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_tSU, coe_tSU, diagU_mul, diagU_mul, mul_comm]

include hU h5 in
theorem isElementaryAbelian_torusBar : IsElementaryAbelian 5 ↥(torusBar K f) :=
  { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (torusBar_comm hU h5 a.2 b.2)⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2
      fun x => Subtype.ext (by simpa using torusBar_pow_five hU h5 x.2) }

include hU in
theorem scalarsU_le_torus : scalarsU K f ≤ (torusSU 5 5 K).subgroupOf (unitarySU 2 f K 5) := by
  intro z hz
  obtain ⟨c, hc⟩ := exists_of_mem_scalarsU hz
  have hc5 : c ^ 5 = 1 := pow_five_eq_one_of_mem_scalarsU hU hc
  refine Subgroup.mem_subgroupOf.mpr (mem_torusSU_iff.mpr ⟨fun _ => c, fun _ => hc5, ?_, hc.symm⟩)
  simp [Finset.prod_const, hc5]

include hU h5 in
theorem card_torusBar [Finite K] (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ 5) :
    Nat.card ↥(torusBar K f) = 5 ^ 3 := by
  have hcomap : (torusBar K f).comap (projU K f) =
      (torusSU 5 5 K).subgroupOf (unitarySU 2 f K 5) := by
    unfold torusBar
    rw [Subgroup.comap_map_eq, ker_projU]
    exact sup_eq_left.mpr (scalarsU_le_torus hU)
  have h1 := card_comap_projU (K := K) (f := f) (torusBar K f)
  rw [hcomap] at h1
  have h2 : Nat.card ↥((torusSU 5 5 K).subgroupOf (unitarySU 2 f K 5)) = 5 ^ 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (torusSU_le_unitarySU hU h5)).toEquiv,
      torusSU, Subgroup.card_map_of_injective diagU_injective]
    exact KFU.card_torusVec_eq (by norm_num) hζ 4
  have h3 : Nat.card (scalarsU K f) = 5 := by
    obtain ⟨ζ, hζ'⟩ := hζ
    exact card_scalarsU hU h5 (IsPrimitiveRoot.coe_units_iff.mpr hζ')
  rw [h2, h3] at h1
  omega

end Torus

end CFSG.RankThree.PartOne.LSTD
