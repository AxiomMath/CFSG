module

public import CFSG.RankThree.PartTwo.Sec21.Item211Res2ProofSmall

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214Even

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open Item211Res2Proof
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem mem_centralizer_of_barAct_eq_one {L : Subgroup G} [Group.IsPerfect L]
    (hθc : aschbacherSolvableCore 3 L ≤ Subgroup.center L) {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) (h : barAct L ⟨g, hg⟩ = 1) :
    g ∈ Subgroup.centralizer (L : Set G) := by
  have hgL : ∀ x : L, g * (x : G) * g⁻¹ ∈ L := fun x =>
    (Subgroup.mem_normalizer_iff.mp hg (x : G)).mp x.2
  let conjL : L →* L := MonoidHom.mk' (fun x => ⟨g * (x : G) * g⁻¹, hgL x⟩) fun a b =>
    Subtype.ext (by
      show g * ((a : G) * (b : G)) * g⁻¹ = (g * (a : G) * g⁻¹) * (g * (b : G) * g⁻¹)
      group)
  have hcen : ∀ x : L, x⁻¹ * conjL x ∈ Subgroup.center L := by
    intro x
    obtain ⟨w, hw, hwx⟩ := Subgroup.mem_map.mp (commutator_mem_of_barAct_eq_one hg h x.2)
    have hwc : w ∈ Subgroup.center L := hθc hw
    have hw1 : (w : G) = (x : G) * g * (x : G)⁻¹ * g⁻¹ := by
      rw [commutatorElement_def] at hwx
      exact hwx
    have hcomm : (x : G) * (w : G) = (w : G) * (x : G) :=
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hwc x)
    have hcw : Commute (w : G) (x : G) := hcomm.symm
    have hgx : g * (x : G) * g⁻¹ = (w : G)⁻¹ * (x : G) := by
      rw [hw1]
      group
    have hc : (w : G)⁻¹ * (x : G) = (x : G) * (w : G)⁻¹ := hcw.inv_left
    have key : (x : G)⁻¹ * (g * (x : G) * g⁻¹) = (w : G)⁻¹ := by
      rw [hgx, hc]
      group
    have hxc : x⁻¹ * conjL x = w⁻¹ := Subtype.ext key
    rw [hxc]
    exact (Subgroup.center L).inv_mem hwc
  have hid := CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement
    conjL hcen
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hl' : g * l * g⁻¹ = l := by
    have h4 := congrArg (fun f : L →* L => ((f ⟨l, hl⟩ : L) : G)) hid
    exact h4
  calc l * g = (g * l * g⁻¹) * g := by rw [hl']
    _ = g * l := by group

end CFSG.RankThree.PartTwo.Sec21.Hering214Even
