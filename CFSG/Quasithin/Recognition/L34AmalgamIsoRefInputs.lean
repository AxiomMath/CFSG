
module

public import CFSG.Quasithin.Recognition.L34AmalgamIsoGL
public import CFSG.Quasithin.Recognition.L34AmalgamGenBase
public meta import CFSG.Quasithin.Recognition.L34AmalgamIsoGL
public meta import CFSG.Quasithin.Recognition.L34AmalgamDataBase
public meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Count
public meta import CFSG.Quasithin.Recognition.M22UniqueData
public meta import CFSG.Quasithin.Recognition.L34AmalgamIsoGLBase
public import CFSG.Quasithin.Recognition.L34AmalgamIsoGLBase

public section

namespace CFSG.Quasithin.L34Amalgam

open MulAction CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94 CFSG.Sporadic.Mathieu

@[expose, irreducible] def refa : M22 := m22OfWord "abaBaBaBabababaBababaBaB"

@[expose, irreducible] def refb : M22 := m22OfWord "abaBabbababbabaBaBaBaBababaBa"

@[expose, irreducible] def refE0 : M22 := m22OfWord "ababaBababbabababbabaBabaBabba"

@[expose, irreducible] def refE1 : M22 := m22OfWord "baBabababbaBaBabababbabb"

@[expose, irreducible] def refE2 : M22 := m22OfWord "BabbabaBabaBababab"

@[expose, irreducible] def refE3 : M22 := m22OfWord "bbabbababbabaBabbaBabbabb"

@[expose] def selM (b : Bool) (g : M22) : M22 := if b then g else 1

@[expose] def crd (x : Fin 16) : M22 :=
  selM (bit 0 x) refE0 * selM (bit 1 x) refE1 * selM (bit 2 x) refE2 * selM (bit 3 x) refE3

@[expose] def cOfWord (s : String) : M22 :=
  s.toList.foldl (fun g c => g * if c = 'a' then refa else if c = 'b' then refb else refb⁻¹) 1

@[expose] def cWords : List String :=
  ["", "B", "a", "b", "Ba", "aB", "ab", "ba", "BaB", "Bab", "aBa", "aba", "baB", "bab", "BaBa",
   "Baba", "aBaB", "aBab", "abaB", "abab", "baBa", "baba", "BaBab", "BabaB", "Babab", "aBaBa",
   "aBaba", "abaBa", "ababa", "baBaB", "baBab", "babaB", "BaBaba", "BabaBa", "aBabaB", "aBabab",
   "abaBaB", "abaBab", "baBaba", "babaBa", "BaBabaB", "BaBabab", "BabaBaB", "BabaBab", "aBabaBa",
   "abaBaba", "baBabaB", "baBabab", "babaBaB", "babaBab", "BabaBaba", "aBabaBaB", "aBabaBab",
   "abaBabaB", "abaBabab", "baBabaBa", "aBabaBaba", "abaBabaBa", "baBabaBab", "abaBabaBab"]

end CFSG.Quasithin.L34Amalgam
