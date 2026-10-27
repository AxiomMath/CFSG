module

public import CFSG.Quasithin.EmptyFaithful.S151S6A

public section

namespace CFSG.Quasithin.S151S9U

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

theorem mem_centerOf_subgroupOf {G : Type} [Group G] {L B : Subgroup G} (hBL : B ≤ L) (x : ↥L) :
    x ∈ centerOf (B.subgroupOf L) ↔ (x : G) ∈ centerOf B := by
  constructor
  · rintro ⟨hx1, hx2⟩
    refine ⟨hx1, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    have hy' : (⟨y, hBL hy⟩ : ↥L) ∈ B.subgroupOf L := hy
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hx2 _ hy')
  · rintro ⟨hx1, hx2⟩
    refine ⟨hx1, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx2 (y : G) hy)

theorem subgroupOf_inf_centralizer_centerOf {G : Type} [Group G] {L B : Subgroup G} (hBL : B ≤ L) :
    (L ⊓ Subgroup.centralizer (centerOf B : Set G)).subgroupOf L =
      Subgroup.centralizer (centerOf (B.subgroupOf L) : Set ↥L) := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  refine ⟨fun h => ?_, fun h => ⟨x.2, ?_⟩⟩
  · refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
    exact Subtype.ext
      (Subgroup.mem_centralizer_iff.mp h.2 (w : G) ((mem_centerOf_subgroupOf hBL w).mp hw))
  · refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
    have hw' : (⟨w, hBL hw.1⟩ : ↥L) ∈ centerOf (B.subgroupOf L) :=
      (mem_centerOf_subgroupOf hBL _).mpr hw
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp h _ hw')

theorem map_centerOf_le_centerOf_map {H Q : Type*} [Group H] [Group Q] (π : H →* Q)
    (B' : Subgroup H) : (centerOf B').map π ≤ centerOf (B'.map π) := by
  rintro _ ⟨z, hz, rfl⟩
  refine ⟨Subgroup.mem_map_of_mem π hz.1, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
  obtain ⟨b, hb, rfl⟩ := hy
  rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hz.2 b hb]

theorem central_quotient_centralizer {G : Type} [Group G] [Finite G] {L B : Subgroup G} {Q : Type}
    [Group Q] (hB : IsSylowTwoOf B L) (π : ↥L →* Q) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center ↥L) (hK2 : IsPGroup 2 ↥π.ker)
    (hne : ¬ L ≤ Subgroup.centralizer (centerOf B : Set G)) {W : Subgroup Q}
    (hW : W = (centerOf (B.subgroupOf L)).map π) :
    W ≤ centerOf ((B.subgroupOf L).map π) ∧ W ≠ ⊥ ∧
      (L ⊓ Subgroup.centralizer (centerOf B : Set G)).subgroupOf L =
        (Subgroup.centralizer (W : Set Q)).comap π := by
  subst hW
  have _ := hπ
  have hBL : B ≤ L := hB.1
  have hodd : ¬ 2 ∣ (B.subgroupOf L).index := hB.2.2
  refine ⟨map_centerOf_le_centerOf_map π _, ?_, ?_⟩
  · intro hbot
    apply hne
    intro x hx
    refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
    have hw' : (⟨w, hBL hw.1⟩ : ↥L) ∈ centerOf (B.subgroupOf L) :=
      (mem_centerOf_subgroupOf hBL _).mpr hw
    have hker1 : (⟨w, hBL hw.1⟩ : ↥L) ∈ π.ker := by
      have h1 : π ⟨w, hBL hw.1⟩ ∈ (centerOf (B.subgroupOf L)).map π :=
        Subgroup.mem_map_of_mem π hw'
      rw [hbot] at h1
      exact Subgroup.mem_bot.mp h1
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp (hker hker1) ⟨x, hx⟩).symm
  · rw [subgroupOf_inf_centralizer_centerOf hBL]
    ext h
    rw [Subgroup.mem_comap]
    constructor
    · intro hh
      refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
      obtain ⟨w, hw, rfl⟩ := hv
      have h1 := Subgroup.mem_centralizer_iff.mp hh w hw
      rw [← map_mul, ← map_mul, h1]
    · intro hh
      refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
      have h1 := Subgroup.mem_centralizer_iff.mp hh (π w) ⟨w, hw, rfl⟩
      have hl : h * w * h⁻¹ * w⁻¹ ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, ← h1]
        group
      have hz : ∀ x ∈ B.subgroupOf L, x * w = w * x := fun x hx =>
        Subgroup.mem_centralizer_iff.mp hw.2 x hx
      exact (S151S6.comm_eq_one_of_central_ext hker hK2 hodd hz hl).symm

end CFSG.Quasithin.S151S9U
