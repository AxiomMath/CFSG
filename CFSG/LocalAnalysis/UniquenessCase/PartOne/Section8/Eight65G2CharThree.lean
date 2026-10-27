module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65Assembly
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65G2CharThreeSylow
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65G2CharThreeTorus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.GH74.GLS.IVK.Proofs2.Ivk47

theorem sylowCenterInverted_of_lieModel_g2_three
    {Y : Type} [Group Y] [Finite Y] {f : ℕ} (hY : LieModel Y .G2 0 3 f) :
    SylowCenterInverted Y := by
  intro Q z hzQ hzc _
  have hmodel : UntwistedChevalleyModel Y .G2 (3 ^ f) := untwisted_of_lieModel_G2 hY
  obtain ⟨F, hFfield, hFfin, φ, hFcard, hQ⟩ :=
    exists_mulEquiv_adjointGroup_map_eq_sylow_g2 Nat.prime_three hmodel Q
  let _ : Field F := hFfield
  let _ : Finite F := hFfin
  let U' : Subgroup ↥(adjointGroup .G2 F) :=
    (posUnipotent .G2 F).subgroupOf (adjointGroup .G2 F)
  have hchar : CharP F 3 := charP_of_natCard_eq_pow Nat.prime_three hFcard
  have h3 : (3 : F) = 0 := by
    exact_mod_cast CharP.cast_eq_zero F 3
  have hQmem : ∀ y : Y, y ∈ (Q : Subgroup Y) ↔ ∃ v ∈ U', φ v = y := by
    intro y
    rw [hQ]
    exact Iff.rfl
  rw [hQmem z] at hzQ
  obtain ⟨u, hu, rfl⟩ := hzQ
  have huc : u ∈ Subgroup.centralizer (U' : Set ↥(adjointGroup .G2 F)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hvQ : φ v ∈ (Q : Subgroup Y) := (hQmem (φ v)).2 ⟨v, hv, rfl⟩
    have hcomm := (Subgroup.mem_centralizer_iff.mp hzc) (φ v) hvQ
    apply φ.injective
    rw [map_mul, map_mul]
    exact hcomm
  obtain ⟨t0, ht0⟩ := exists_conj_eq_inv_of_mem_centralizer_posUnipotent_g2 h3 u hu huc
  refine ⟨φ t0, ?_⟩
  rw [← map_mul, ← map_inv, ← map_mul, ht0, map_inv]

theorem g2CharThreeInversion_holds :
    G2CharThreeInversion := by
  unfold G2CharThreeInversion
  intro Y _ _ f hY
  exact sylowCenterInverted_of_lieModel_g2_three hY

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
