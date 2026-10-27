module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBLabelDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBJoinDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBSpSp
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyWeylNS
import CFSG.LocalAnalysis.StandardType.GGTPNI1BC
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.Open.StatedAPI

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank

theorem GGSecFiveRouteCfg.leviCase_of_bCoordinateBlock {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) {m f : ℕ} (hm : 4 ≤ m)
    (e : (CoxeterMatrix.B (m + 1)).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hP : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B (m + 1)) e)
    (eta : ↥Bs ≃* (Fin (m + 1) → Multiplicative (ZMod 3))) {i0 j : Fin (m + 1)} (hj : j ≠ i0)
    (h𝒦 : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull (m + 1) 3)
    (hL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock (m + 1) 3 i0)
    (hLm : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSp m 2 f) {K : Subgroup G}
    (hK𝒦 : K ∈ 𝒦) (hKm : StatedClassicalModel (↥K ⧸ Subgroup.center ↥K) .PSp m 2 f)
    (hK : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock (m + 1) 3 j) :
    GGSecFiveLeviCase 3 B Bs x L D J := by
  obtain ⟨y, hy⟩ := hR.2.2.2.1.2 K hK𝒦
  have hsup : ggAutomizer L Bs ⊔ ggAutomizer K Bs = ggAutomizerJoin L Bs 𝒦 := by
    apply Subgroup.map_injective (f := (MulAut.congr eta).toMonoidHom) (MulAut.congr eta).injective
    rw [Subgroup.map_sup, hL, hK, h𝒦, bCoordinateBlock_sup_bCoordinateBlock 3 (by omega) hj]
  exact Or.inr (Or.inr ⟨m, f, y, K, hLm, hm, ggScalarsPmOne_of_prime_three hR.1.1 rfl, hy, hKm,
    e.trans (MulEquiv.subgroupCongr hsup.symm), fun i => hP.2 i⟩)

theorem GGSecFiveRouteCfg.false_of_qTwoSp_sparse {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {n : ℕ} (hn : 5 ≤ n)
    (e : (CoxeterMatrix.B n).Group ≃* ↥(ggAutomizerJoin L Bs 𝒦))
    (hP : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) (CoxeterMatrix.B n) e)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {i0 j : Fin n} (hj : j ≠ i0)
    (h𝒦 : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p)
    (hL : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    (hLab : GGInnerDiagOnLabel (fun p lab => GGSecFiveBCoordBLabel n p lab ∧
      (lab.n = 1 ∧ (lab.tag = .B ∨ lab.tag = .C))) p Bs L)
    {K : Subgroup G} (hK𝒦 : K ∈ 𝒦)
    (eLK : (↥L ⧸ Subgroup.center ↥L) ≃* (↥K ⧸ Subgroup.center ↥K))
    (hK : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p j) :
    False := by
  obtain ⟨lab, -, hlab, _, _, _, _, _, ⟨hBL, hk1, ht⟩, -⟩ := largeEvenMarking_exists_hasLabel hLab
  obtain ⟨t, r, k⟩ := lab
  obtain rfl : k = 1 := hk1
  replace ht : t = .B ∨ t = .C := ht
  have hp : p.Prime := hR.1.1.tableB_facts.1
  obtain ⟨hr, hp3⟩ : r = n - 1 ∧ p = 3 := by
    rcases hBL with ⟨-, hr, hd | ⟨-, h3⟩⟩ | ⟨htw, -⟩ | ⟨htw, -⟩ | ⟨htw, -⟩
    · exact absurd (by simpa using hd : p = 1) hp.ne_one
    · exact ⟨hr, h3⟩
    all_goals rcases ht with rfl | rfl <;> simp at htw
  subst hr hp3
  have hC : GGHasLabel ⟨.C, n - 1, 1⟩ (↥L ⧸ Subgroup.center ↥L) := by
    rcases ht with rfl | rfl <;> exact hlab
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hLm := tpbc_statedClassicalModel_of_hasLabel_C (by omega) le_rfl hC
  simp only [Nat.add_sub_cancel] at hLm
  have hKm := CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv eLK hLm
  exact hR.2.2.1 (hR.leviCase_of_bCoordinateBlock (by omega) e hP eta hj h𝒦 hL hLm hK𝒦 hKm hK)

end CFSG.StandardType

end
