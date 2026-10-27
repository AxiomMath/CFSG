module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsBorAutMain
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieG2Facts

public section

namespace CFSG.Quasithin.H13.Sec53F.G2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2
open scoped commutatorElement Pointwise

set_option linter.unusedSectionVars false


section Sub

variable {G : Type} [Group G]

theorem mem_perfectCore_subgroupOf {P C : Subgroup G} (hPC : P ≤ C) (x : C) :
    x ∈ perfectCore (P.subgroupOf C) ↔ (x : G) ∈ perfectCore P := by
  have h1 := BA.perfectCore_map_inj C.subtype C.subtype_injective (P.subgroupOf C)
  rw [Subgroup.map_subgroupOf_eq_of_le hPC] at h1
  rw [h1]
  exact (Subgroup.mem_map_iff_mem C.subtype_injective).symm

theorem mem_centerOf_perfectCore_subgroupOf {P C : Subgroup G} (hPC : P ≤ C) (x : C) :
    x ∈ centerOf (perfectCore (P.subgroupOf C)) ↔
      (x : G) ∈ perfectCore P ∧ ∀ y ∈ perfectCore P, y * (x : G) = (x : G) * y := by
  constructor
  · rintro ⟨hx, hxc⟩
    refine ⟨(mem_perfectCore_subgroupOf hPC x).mp hx, fun y hy => ?_⟩
    have hyC : y ∈ C := hPC (perfectCore_le P hy)
    have := Subgroup.mem_centralizer_iff.mp hxc ⟨y, hyC⟩ ((mem_perfectCore_subgroupOf hPC _).mpr hy)
    exact congrArg Subtype.val this
  · rintro ⟨hx, hxc⟩
    refine ⟨(mem_perfectCore_subgroupOf hPC x).mpr hx, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro y hy
    exact Subtype.ext (hxc y ((mem_perfectCore_subgroupOf hPC y).mp hy))

theorem commutator_le_perfectCore {P Q : Subgroup G} (hQP : Q ≤ P) :
    ⁅Q, perfectCore P⁆ ≤ perfectCore P := by
  rw [Subgroup.commutator_le]
  intro q hq x hx
  have hn : q ∈ Subgroup.normalizer (perfectCore P : Set G) :=
    normalizer_le_normalizer_perfectCore P (Subgroup.le_normalizer (hQP hq))
  rw [commutatorElement_def]
  exact mul_mem ((Subgroup.mem_normalizer_iff.mp hn x).mp hx) (inv_mem hx)

theorem comm_mul_right' (g a b : G) : ⁅g, a * b⁆ = ⁅g, a⁆ * (a * ⁅g, b⁆ * a⁻¹) := by
  simp only [commutatorElement_def]
  group

end Sub

variable {K : Type} [Field K] [CharP K 2]

theorem conj_torus (i : Fin Tag.G2.rank) {β : Fin Tag.G2.rank → ℤ} (hβ : IsRoot Tag.G2 β)
    (t : Kˣ) (c : K) :
    torusElt Tag.G2 K i t * gX β c * (torusElt Tag.G2 K i t)⁻¹ =
      gX β (((t ^ ∑ j, Tag.G2.cartan i j * β j : Kˣ) : K) * c) := by
  have h := torus_comm (K := K) i hβ t c
  rw [commutatorElement_def] at h
  have h2 : torusElt Tag.G2 K i t * gX β c * (torusElt Tag.G2 K i t)⁻¹ =
      gX β ((((t ^ ∑ j, Tag.G2.cartan i j * β j : Kˣ) : K) + 1) * c) * gX β c := by
    rw [← h]
    group
  rw [h2, ← gX_add]
  congr 1
  rw [add_mul, one_mul, add_assoc, _root_.CharTwo.add_self_eq_zero, add_zero]

theorem isRoot_rB : IsRoot Tag.G2 rB := (isRoot_pos_iff.2 (by simp)).1

theorem isRoot_rC : IsRoot Tag.G2 rC := (isRoot_pos_iff.2 (by simp)).1

theorem add_one_ne_zero {a : K} (ha : a ≠ 1) : a + 1 ≠ 0 := by
  intro h
  apply ha
  calc a = a + 1 + 1 := by rw [add_assoc, _root_.CharTwo.add_self_eq_zero, add_zero]
    _ = 1 := by rw [h, zero_add]

section Perf

variable [Finite K]

theorem radical_le_parabolic (J : Set (Fin Tag.G2.rank)) :
    parabolicRadical Tag.G2 K J ≤ parabolicSubgroup Tag.G2 K J :=
  (parabolicRadical_le_posUnipotent J).trans (posUnipotent_le_parabolicSubgroup J)

theorem radical_le_perfectCore_zero (hK4 : 4 ≤ Nat.card K) :
    parabolicRadical Tag.G2 K {i0} ≤ perfectCore (parabolicSubgroup Tag.G2 K {i0}) :=
  (generated_zero hK4).trans (commutator_le_perfectCore (radical_le_parabolic _))

theorem radical_le_perfectCore_one (hK4 : 4 ≤ Nat.card K) :
    parabolicRadical Tag.G2 K {i1} ≤ perfectCore (parabolicSubgroup Tag.G2 K {i1}) :=
  (generated_one hK4).trans (commutator_le_perfectCore (radical_le_parabolic _))

theorem posUnipotent_le_perfectCore_of {i : Fin Tag.G2.rank} (hK4 : 4 ≤ Nat.card K)
    (hQ : parabolicRadical Tag.G2 K {i} ≤ perfectCore (parabolicSubgroup Tag.G2 K {i}))
    (hV : ∀ α ∈ parabolicPosRoots Tag.G2 ({i} : Set (Fin Tag.G2.rank)), α = Pi.single i 1) :
    posUnipotent Tag.G2 K ≤ perfectCore (parabolicSubgroup Tag.G2 K {i}) := by
  obtain ⟨L, hLP, hLL, hxL, -, -⟩ := leviL_data (K := K) hK4 i
  have hLc : L ≤ perfectCore (parabolicSubgroup Tag.G2 K {i}) := le_perfectCore_of_perfect hLP hLL
  intro u hu
  have hu' : u ∈ (parabolicRadical Tag.G2 K {i} : Set (ModGL Tag.G2 K)) *
      (parabolicLeviUnipotent Tag.G2 K {i} : Set (ModGL Tag.G2 K)) := by
    rw [← posUnipotent_eq_mul_parabolic {i}]
    exact hu
  obtain ⟨q, hq, v, hv, rfl⟩ := hu'
  refine mul_mem (hQ hq) (hLc ?_)
  have hVL : parabolicLeviUnipotent Tag.G2 K {i} ≤ L := by
    show rootSpan Tag.G2 K (parabolicPosRoots Tag.G2 {i}) ≤ L
    refine iSup₂_le fun α hα => (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    rw [hV α hα, pinnedX_single]
    exact hxL c
  exact hVL hv

theorem parabolicPosRoots_zero :
    ∀ α ∈ parabolicPosRoots Tag.G2 ({i0} : Set (Fin Tag.G2.rank)), α = Pi.single i0 1 := by
  intro α hα
  rcases isRoot_pos_iff.1 hα.2 with h | h | h | h | h | h
  · rw [h, single_i0]
  all_goals
    exfalso
    have hrad : α ∈ parabolicRadicalRoots Tag.G2 ({i0} : Set (Fin Tag.G2.rank)) := by
      rw [radicalRoots_zero]
      simp [h]
    exact hrad.2 hα

theorem parabolicPosRoots_one :
    ∀ α ∈ parabolicPosRoots Tag.G2 ({i1} : Set (Fin Tag.G2.rank)), α = Pi.single i1 1 := by
  intro α hα
  rcases isRoot_pos_iff.1 hα.2 with h | h | h | h | h | h
  swap
  · rw [h, single_i1]
  all_goals
    exfalso
    have hrad : α ∈ parabolicRadicalRoots Tag.G2 ({i1} : Set (Fin Tag.G2.rank)) := by
      rw [radicalRoots_one]
      simp [h]
    exact hrad.2 hα

theorem posUnipotent_le_perfectCore_zero (hK4 : 4 ≤ Nat.card K) :
    posUnipotent Tag.G2 K ≤ perfectCore (parabolicSubgroup Tag.G2 K {i0}) :=
  posUnipotent_le_perfectCore_of hK4 (radical_le_perfectCore_zero hK4) parabolicPosRoots_zero

theorem posUnipotent_le_perfectCore_one (hK4 : 4 ≤ Nat.card K) :
    posUnipotent Tag.G2 K ≤ perfectCore (parabolicSubgroup Tag.G2 K {i1}) :=
  posUnipotent_le_perfectCore_of hK4 (radical_le_perfectCore_one hK4) parabolicPosRoots_one

end Perf

end CFSG.Quasithin.H13.Sec53F.G2
