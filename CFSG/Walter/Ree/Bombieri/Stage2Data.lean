module

public import CFSG.Walter.Ree.Bombieri.Stage2Comp

public section

namespace CFSG.Walter.Ree.Bombieri

namespace Spec

@[expose] def mod7 : F3P := ⟨132, 1⟩

@[expose] def mod8 : F3P := ⟨260, 1⟩

@[expose] def mod9 : F3P := ⟨528, 1⟩

@[expose] def batch9_1 : List Entry := [
  ⟨0, 1, false, [19044]⟩,
  ⟨0, 1, true, [13238]⟩,
  ⟨0, 2, false, [4856]⟩,
  ⟨0, 2, true, [11679]⟩,
  ⟨0, 3, false, [14952]⟩,
  ⟨0, 3, true, [6375]⟩,
  ⟨0, 4, false, [641]⟩,
  ⟨0, 5, true, [17428]⟩,
  ⟨0, 6, false, [15704]⟩,
  ⟨0, 6, true, [17918]⟩]

@[expose] def batch9_2 : List Entry := [
  ⟨0, 7, false, [8077]⟩,
  ⟨0, 7, true, [5518]⟩,
  ⟨0, 8, false, [4277]⟩,
  ⟨0, 8, true, [13797]⟩,
  ⟨1, 1, true, [11281, 12885]⟩,
  ⟨1, 3, false, [2974, 1388]⟩,
  ⟨1, 3, true, [17691, 503]⟩,
  ⟨1, 5, false, [1671, 5400]⟩,
  ⟨1, 5, true, [19514, 12966]⟩,
  ⟨1, 7, false, [13975, 14000]⟩]

@[expose] def batch9_3 : List Entry := [
  ⟨1, 7, true, [12166, 9619]⟩,
  ⟨2, 1, false, [16265, 8989, 8314]⟩,
  ⟨2, 1, true, [11931, 19378, 6146]⟩,
  ⟨2, 2, false, [18268, 17663, 18136]⟩,
  ⟨2, 2, true, [6744, 18173, 17333]⟩,
  ⟨2, 3, false, [1038, 7871, 6387]⟩,
  ⟨2, 3, true, [17218, 12054, 13197]⟩,
  ⟨2, 4, false, [4387, 6791, 13989]⟩,
  ⟨2, 4, true, [2395, 8309, 12163]⟩,
  ⟨2, 5, false, [5984, 18834, 18566]⟩]

@[expose] def batch9_4 : List Entry := [
  ⟨2, 5, true, [9247, 15403, 10416]⟩,
  ⟨2, 6, false, [14085, 17198, 6219]⟩,
  ⟨2, 6, true, [5770, 1098, 15872]⟩,
  ⟨2, 7, false, [16736, 9851, 9711]⟩,
  ⟨2, 7, true, [15650, 15390, 3743]⟩,
  ⟨2, 8, false, [6141, 4855, 13080]⟩,
  ⟨2, 8, true, [4743, 9580, 4916]⟩,
  ⟨2, 9, false, [2080, 9740, 14]⟩,
  ⟨2, 9, true, [15490, 16459, 2999]⟩,
  ⟨3, 1, false, [14347, 12318, 10538, 9581]⟩]

@[expose] def batch9_5 : List Entry := [
  ⟨3, 1, true, [1155, 5127, 528, 7630]⟩,
  ⟨3, 3, false, [8181, 11206, 1166, 5274]⟩,
  ⟨3, 3, true, [3956, 2959, 12933, 15097]⟩,
  ⟨3, 5, false, [1427, 6049, 15056, 3288]⟩,
  ⟨3, 5, true, [2056, 13570, 16891, 19408]⟩,
  ⟨3, 7, false, [3396, 9393, 17768, 13285]⟩,
  ⟨3, 7, true, [12252, 10306, 5529, 127]⟩,
  ⟨3, 9, false, [16929, 17937, 15701, 4919]⟩,
  ⟨3, 9, true, [16149, 5545, 7933, 4820]⟩]

@[expose] def batch8 : List Entry := [
  ⟨0, 5, false, [4845]⟩,
  ⟨0, 9, false, [5758]⟩,
  ⟨0, 9, true, [1923]⟩,
  ⟨1, 9, true, [6220, 4322]⟩]

@[expose] def batch7 : List Entry := [
  ⟨0, 4, true, [374]⟩,
  ⟨1, 9, false, [1928, 770]⟩]

@[expose] def allBatches : List Entry :=
  batch9_1 ++ batch9_2 ++ batch9_3 ++ batch9_4 ++ batch9_5 ++ batch8 ++ batch7

end Spec

end CFSG.Walter.Ree.Bombieri
