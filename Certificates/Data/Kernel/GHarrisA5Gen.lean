module

public import Certificates.Data.GHarrisA5Data

public section

namespace CFSG.KC.GHarrisA5

open CFSG.ComponentClassification.GHarris

@[expose] def c5 : Equiv.Perm (Fin 5) := ⟨![1, 2, 3, 4, 0], ![4, 0, 1, 2, 3], by decide, by decide⟩

@[expose] def c3 : Equiv.Perm (Fin 5) := ⟨![1, 2, 0, 3, 4], ![2, 0, 1, 3, 4], by decide, by decide⟩

@[expose] def gens : List (alternatingGroup (Fin 5)) :=
  [⟨c5, Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩,
    ⟨c3, Equiv.Perm.mem_alternatingGroup.2 (by decide)⟩]

@[expose] noncomputable def wordA5 (w : List ℕ) : alternatingGroup (Fin 5) := w.foldl (fun a i => a * gens.getD i 1) 1

@[expose] def genWords : List (ℕ × List ℕ) := [
  (38, [1, 0, 0, 0, 1, 0, 1]), (44, [0, 1, 0, 1, 1]), (47, [0, 1, 1, 0, 1]), (59, [1, 0, 0, 0, 0]),
  (66, [1, 0, 0, 0, 1, 0]), (73, [0, 0, 1]), (82, [0, 0, 0, 0, 1, 0, 1, 0]), (89, [0, 0, 1, 1]),
  (96, [0, 1, 0, 1]), (108, [0, 1, 0]), (111, [0, 1, 1, 0]), (117, [0, 0]), (139, [0, 0, 1, 0]),
  (142, [0, 0, 1, 1, 0]), (148, [0, 0, 0]), (178, [0, 0, 1, 1, 0, 1]), (194, [1, 0, 1, 0, 1, 1]),
  (195, [0, 0, 1, 0, 1, 1]), (204, [0, 0, 0, 1]), (210, [0, 1, 0, 0, 0, 0]), (222, [1, 0, 1, 0, 1]),
  (227, [0, 0, 1, 0, 1]), (238, [1, 0, 1, 0]), (240, [1, 0, 0]), (258, [0, 0, 0, 1, 0, 1]),
  (269, [0, 1, 0, 1, 0]), (271, [0, 1, 0, 0]), (279, [0, 0, 0, 0]), (290, [0, 0, 0, 1, 0]),
  (298, [1, 0, 0, 0]), (326, [0, 0, 0, 1, 0, 1, 1]), (334, [1, 0, 0, 0, 1]), (345, [1, 1, 0, 1, 0, 1]),
  (353, [1, 1, 0, 1, 0]), (355, [0, 0, 0, 0, 1]), (366, [1, 1, 0, 0]), (384, [0, 1, 1, 0, 1, 0]),
  (386, [1]), (397, [0, 1, 1, 0, 0]), (402, [1, 1]), (414, [0, 0, 0, 0, 1, 0, 1]),
  (420, [0, 0, 1, 0, 1, 0]), (429, [0, 1, 0, 0, 0]), (430, []), (446, [0, 0, 0, 0, 1, 0]),
  (476, [0, 1, 1, 0, 1, 0, 1]), (482, [0, 0, 0, 0, 1, 0, 1, 1]), (485, [0, 1, 0, 0, 0, 1]),
  (507, [0, 0, 1, 1, 0, 1, 0, 1]), (513, [1, 0, 1, 1]), (516, [1, 1, 0, 1]), (528, [1, 1, 0, 1, 1]),
  (535, [0, 0, 1, 1, 0, 1, 0]), (542, [0, 1]), (551, [0, 0, 0, 1, 0, 1, 0]), (558, [0, 1, 1]),
  (565, [1, 0, 1]), (577, [1, 0]), (580, [1, 1, 0]), (586, [0])]

@[expose] def genWord (k : ℕ) : List ℕ := (genWords.lookup k).getD []

abbrev HomGen (j : ℕ) : Prop :=
  ∀ p : alternatingGroup (Fin 5), ∀ s ∈ gens,
    GL42.phiA5 j (p * s) = (GL42.phiA5 j p).mul (GL42.phiA5 j s)

abbrev WordsGen : Prop := ∀ q : alternatingGroup (Fin 5), wordA5 (genWord (GL42.permKey q)) = q

end CFSG.KC.GHarrisA5

end
