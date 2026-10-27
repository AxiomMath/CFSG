module

public import CFSG.Quasithin.Vol2.Ch11SecSCartanT3
public import CFSG.Quasithin.Vol2.Ch11SecA12Iface
public import CFSG.Quasithin.Vol2.Ch11SecA14Delta

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_pCoreOf_of_centralizer {A V : Subgroup G} (hA : A ≤ Subgroup.normalizer (V : Set G))
    (hC : IsPGroup 2 ↥(A ⊓ Subgroup.centralizer (V : Set G))) :
    A ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 A :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
    (fun _ ha => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer ha, mem_normalizer_centralizer (hA ha)⟩) hC

omit [Finite G] in
theorem conjV_commutator (V : Subgroup G) {x a : G} (hx : x ∈ Subgroup.normalizer (V : Set G))
    (ha : a ∈ Subgroup.normalizer (V : Set G)) :
    conjV V x hx * conjV V a ha * (conjV V x hx)⁻¹ * (conjV V a ha)⁻¹ =
      conjV V (x * a * x⁻¹ * a⁻¹) (Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.mul_mem _ hx ha) (Subgroup.inv_mem _ hx)) (Subgroup.inv_mem _ ha)) := by
  rw [← conjV_inv, ← conjV_inv, ← conjV_mul, ← conjV_mul, ← conjV_mul]

omit [Finite G] in
theorem autOn_xOne [Finite G] {L V U X : Subgroup G} (hL : L ≤ Subgroup.normalizer (V : Set G))
    (hU : U ≤ V) (hXA : X ≤ Subgroup.normalizer (LOf L U : Set G))
    (hC : IsPGroup 2 ↥(L ⊓ Subgroup.centralizer (V : Set G))) :
    autOn (xOne X (LOf L U)) V = centW (autOn X V) (gammaW (autOn L V) (U.subgroupOf V)) := by
  set A := LOf L U
  have hAL : A ≤ L := (perfectCore_le _).trans inf_le_left
  have hA : A ≤ Subgroup.normalizer (V : Set G) := hAL.trans hL
  have hCA : IsPGroup 2 ↥(A ⊓ Subgroup.centralizer (V : Set G)) :=
    hC.to_le (inf_le_inf_right _ hAL)
  have hO := autOn_pCoreOf hA hCA
  rw [← autOn_lOf hL hU]
  apply le_antisymm
  · intro g hg
    obtain ⟨x, hx, hxV, rfl⟩ := mem_autOn_iff.mp hg
    obtain ⟨hxX, hxN, hxO, hxc⟩ := hx
    refine ⟨conjV_mem_autOn hxX hxV, ?_, ?_, fun h hh => ?_⟩
    · exact autOn_le_normalizer (S := A) le_rfl (conjV_mem_autOn hxN hxV)
    · rw [← hO]
      exact autOn_le_normalizer (S := pCoreOf 2 A) le_rfl (conjV_mem_autOn hxO hxV)
    · obtain ⟨a, ha, haV, rfl⟩ := mem_autOn_iff.mp hh
      rw [conjV_commutator, ← hO]
      exact conjV_mem_autOn (hxc a ha) _
  · rintro g ⟨hgX, hgN, hgO, hgc⟩
    obtain ⟨x, hxX, hxV, rfl⟩ := mem_autOn_iff.mp hgX
    have hxA : x ∈ Subgroup.normalizer (A : Set G) := hXA hxX
    have hxS : x ∈ sectionCentralizer A (pCoreOf 2 A) := by
      refine ⟨hxA, CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 A hxA,
        fun a ha => ?_⟩
      have h1 := hgc _ (conjV_mem_autOn ha (hA ha))
      rw [conjV_commutator, ← hO] at h1
      obtain ⟨o, ho, hoV, hoe⟩ := mem_autOn_iff.mp h1
      have hw : x * a * x⁻¹ * a⁻¹ ∈ A :=
        A.mul_mem ((Subgroup.mem_normalizer_iff.mp hxA a).mp ha) (A.inv_mem ha)
      have hoA : o ∈ A := (CFSG.LieType.BorelTits.pCoreOf_le 2 A) ho
      have hc : o⁻¹ * (x * a * x⁻¹ * a⁻¹) ∈ A ⊓ Subgroup.centralizer (V : Set G) :=
        ⟨A.mul_mem (A.inv_mem hoA) hw, inv_mul_mem_centralizer hoe.symm⟩
      have := (pCoreOf 2 A).mul_mem ho (le_pCoreOf_of_centralizer hA hCA hc)
      rwa [mul_inv_cancel_left] at this
    exact conjV_mem_autOn (Subgroup.mem_inf.mpr ⟨hxX, hxS⟩) hxV

end CFSG.Quasithin.Vol2.Ch11.SecS
