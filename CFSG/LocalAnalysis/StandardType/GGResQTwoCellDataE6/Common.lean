module

public import CFSG.LocalAnalysis.StandardType.GGResIDisp.E6
public import CFSG.LocalAnalysis.StandardType.GGResQTwoPacked

public section

namespace CFSG.StandardType.GGResQTwoCellDataE6

open CFSG.StandardType
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

abbrev Rq2_05c6cda9782eddb6 : List (Fin 7 × List (Fin 7)) :=
[(0, []), (1, []), (2, []), (3, []), (4, []), (5, []), (0, [2]), (1, [3]), (2, [3]), (3, [4]), (4, [5]), (0, [3, 2]), (1, [2, 3]), (1, [4, 3]), (2, [4, 3]), (3, [5, 4]), (0, [1, 3, 2]), (0, [4, 3, 2]), (1, [4, 2, 3]), (1, [5, 4, 3]), (2, [5, 4, 3]), (0, [4, 1, 3, 2]), (0, [5, 4, 3, 2]), (1, [3, 4, 2, 3]), (1, [5, 4, 2, 3]), (0, [3, 4, 1, 3, 2]), (0, [5, 4, 1, 3, 2]), (1, [5, 3, 4, 2, 3]), (0, [2, 3, 4, 1, 3, 2]), (0, [5, 3, 4, 1, 3, 2]), (1, [4, 5, 3, 4, 2, 3]), (0, [5, 2, 3, 4, 1, 3, 2]), (0, [4, 5, 3, 4, 1, 3, 2]), (0, [4, 5, 2, 3, 4, 1, 3, 2]), (0, [3, 4, 5, 2, 3, 4, 1, 3, 2]), (0, [1, 3, 4, 5, 2, 3, 4, 1, 3, 2])]

@[expose] def pkTabE6 : ℕ := 2952235703262889148450

@[expose] def pkDataE6 : List (ℕ × ℕ × ℕ) :=
[(1, 1, 1180663682709780971522),
  (4, 4, 1180663682984642117633),
  (16, 16, 1180663683809544257553),
  (64, 64, 1180681701507394191361),
  (256, 256, 1475883663075340992513),
  (1024, 1024, 2361543533803327209473),
  (17, 17, 1180663683877760417824),
  (68, 68, 1180682819161031180289),
  (80, 80, 1180686198510757167185),
  (320, 320, 1549562566178631860225),
  (1280, 1280, 590872363470254260225),
  (81, 81, 1180686480121293787296),
  (84, 84, 1180687326609821794389),
  (324, 324, 1554176473210615758849),
  (336, 336, 1568018286670370914641),
  (1344, 1344, 737941996487102971905),
  (85, 85, 1180687608082785247400),
  (337, 337, 1569171771114462204576),
  (340, 340, 1572632247853369655637),
  (1348, 1348, 747165197000216412161),
  (1360, 1360, 774835313132988351825),
  (341, 341, 1573785732366046208680),
  (1361, 1361, 777141156097373330080),
  (404, 404, 1646444012902128042389),
  (1364, 1364, 784058778903349167445),
  (405, 405, 1647596934550968615528),
  (1365, 1365, 786364621936319408808),
  (1428, 1428, 710673838165599470997),
  (421, 421, 1666043636159346655233),
  (1429, 1429, 712979962811203471976),
  (1684, 1684, 1181341474453683455637),
  (1445, 1445, 694537539151481290753),
  (1685, 1685, 1181342037431906486632),
  (1701, 1701, 1181337637541864554497),
  (1573, 1573, 1180663842826151432193),
  (1577, 1577, 1180663682709773721601)]

theorem pkTabE6_spec : ∀ a b : Fin 6, ((CartanMatrix.E 6 a b : ℤ) : ZMod 3) =
    ((GGResQTwoPacked.pkLane pkTabE6 (a.val * 6 + b.val) : ℕ) : ZMod 3) := by
  decide +kernel

theorem pkSharedE6 : GGResQTwoPacked.pkSharedOK pkTabE6 6 ([0, 1, 2, 3, 4, 5] : List (Fin 7))
    Rq2_05c6cda9782eddb6 pkDataE6 = true := by
  decide +kernel

theorem pkListE6 (ib ic : Fin 6) (e₁ e₂ : ℤ) (u v : ZMod 3)
    (h2 : ∀ k, (ggStdTableI (Int.cast) (CartanMatrix.E 6) ib ic e₁ e₂ u v k).get k.castSucc = 2)
    (hx : ∀ k, (ggStdTableI (Int.cast) (CartanMatrix.E 6) ib ic e₁ e₂ u v k).get
      (Fin.last 7) = 0) :
    GGResQTwoListOK (ggStdTableI (Int.cast) (CartanMatrix.E 6) ib ic e₁ e₂ u v)
        [0, 1, 2, 3, 4, 5] Rq2_05c6cda9782eddb6 ∧
      ∀ r ∈ Rq2_05c6cda9782eddb6, ∃ d ∈ pkDataE6, GGResQTwoPacked.pkBlkM 6
        (ggFRefMat (ggStdTableI (Int.cast) (CartanMatrix.E 6) ib ic e₁ e₂ u v) r) = d.2.2 :=
  GGResQTwoPacked.pkShared_sound pkSharedE6 (GGResQTwoPacked.pkTab_std pkTabE6_spec ib ic e₁ e₂ u v)
    h2 hx

end CFSG.StandardType.GGResQTwoCellDataE6
