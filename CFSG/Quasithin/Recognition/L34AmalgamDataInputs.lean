module

public import CFSG.Quasithin.Recognition.M22WittData
public import CFSG.Certificates.CosetTablePresented
public meta import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Count
public meta import CFSG.Quasithin.Recognition.M22UniqueData

public section

namespace CFSG.Quasithin.L34Amalgam

open MulAction CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94 CFSG.Sporadic.Mathieu

@[expose] def m22OfWord (s : String) : M22 :=
  s.toList.foldl (fun g c => g * if c = 'a' then m22a else if c = 'b' then m22b
    else if c = 'A' then m22a⁻¹ else m22b⁻¹) 1

@[expose, irreducible] def bC1 : M22 := m22OfWord "ababaBaBabaBababbaBababababb"

@[expose, irreducible] def bC2 : M22 := m22OfWord "aBaBaBabbabababa"

@[expose, irreducible] def bC3 : M22 := m22OfWord "abaBababababbabaBaBaBabbab"

@[expose, irreducible] def bT1 : M22 := m22OfWord "babbaBaBabababbaB"

@[expose, irreducible] def bT2 : M22 := m22OfWord "bababaBababbaBabaBaBaB"

@[expose] def gen : Fin 5 → M22 := ![bC1, bC2, bC3, bT1, bT2]

@[expose] def letter (c : Char) : Fin 5 × Bool :=
  (⟨"pqrsu".toList.idxOf c.toLower % 5, Nat.mod_lt _ (by norm_num)⟩, c.isLower)

@[expose] def word (s : String) : List (Fin 5 × Bool) := s.toList.map letter

@[expose] def evalW {X : Type*} [Group X] (f : Fin 5 → X) (w : List (Fin 5 × Bool)) : X :=
  (w.map fun x => cond x.2 (f x.1) (f x.1)⁻¹).prod

@[expose] def rels1 : List String :=
  ["pp", "ss", "rrr", "qsqS", "RsRsRS", "rqrQrQ", "rprPrP", "pqrpqrPQr", "qRspsQRPSP"]

@[expose] def rels2 : List String :=
  ["pp", "qq", "rrr", "rqrQrQ", "rprPrP", "urpuQPQr", "urqRprQUr", "qurqurQUr"]

@[expose] def amalRels : List (List (Fin 5 × Bool)) := (rels1 ++ rels2).map word

@[expose] def repStr : Fin 12 → String :=
  !["u", "Rquqpu", "pruquR", "uRuru", "rpur", "qpuRq", "pququqp", "Rpu", "rquqR", "puqu",
    "urqRu", "Rur"]

@[expose] def extra (i : Fin 12) (k : ℕ) : List (Fin 5 × Bool) :=
  word (String.join (List.replicate k ("s" ++ repStr i)))

@[expose] def IsGood (i : Fin 12) : Prop := i = 2 ∨ i = 5 ∨ i = 7

instance (i : Fin 12) : Decidable (IsGood i) := by unfold IsGood; infer_instance

end CFSG.Quasithin.L34Amalgam
