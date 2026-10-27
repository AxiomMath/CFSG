
module


public import CFSG.Monster.B.TwoA.Sp8.WordRel
public import CFSG.Monster.B.TwoA.Sp8.P0StructInputs
import Certificates.Kernel.WordRelK.Rel

public section

namespace Certificates

open CertificateChecks.KernelWordRelK.Rel in
open CFSG.Monster.B.TwoA.Sp8.WordRel CFSG.ComponentClassification.RankTwoSporadic.B.TwoDFix in
theorem certificate812461 : 
    (∀ i < 16, ∀ j < 16, wordX (lWord (2 ^ i) ++ lWord (2 ^ j)) =
      wordX (lWord (2 ^ j) ++ lWord (2 ^ i) ++ tWord ((lCommN.getD i []).getD j 0))) ∧
    (∀ i < 16, wordX (lWord (2 ^ i) ++ lWord (2 ^ i)) = 1) ∧
    (∀ k < 10, ∀ j < 16, wordX (uWord k ++ lWord (2 ^ j)) =
      wordX (lWord ((uConjLN.getD k []).getD j (0, 0)).1 ++
        tWord ((uConjLN.getD k []).getD j (0, 0)).2 ++ uWord k)) ∧
    (∀ k < 10, ∀ j < 9, wordX (uWord k ++ tWord (2 ^ j)) =
      wordX (tWord ((uConjTN.getD k []).getD j 0) ++ uWord k)) ∧
    (∀ k < 10, wordX (uWord k ++ uWord k) =
      wordX (lWord (uSqN.getD k (0, 0)).1 ++ tWord (uSqN.getD k (0, 0)).2)) ∧
    (∀ j < 10, ∀ k < 10, wordX (uWord j ++ uWord k) =
      wordX (lWord ((uCommN.getD j []).getD k (0, 0)).1 ++
        tWord ((uCommN.getD j []).getD k (0, 0)).2 ++ uWord k ++ uWord j)) ∧
    (∀ i < 9, wordX ((coGens.getD i []).map .lift) =
      wordX (lWord (coDecN.getD i (0, 0)).1 ++ tWord (coDecN.getD i (0, 0)).2)) ∧
    (∀ i < 15, wordX ((pauliWords.getD i []).map .lift) =
      wordX (lWord (paDecN.getD i (0, 0)).1 ++ tWord (paDecN.getD i (0, 0)).2)) :=
  ⟨fun _ hi _ hj => lComm hi hj, fun _ hi => lSq hi, fun _ hk _ hj => uConjL hk hj,
    fun _ hk _ hj => uConjT hk hj, fun _ hk => uSq hk, fun _ hj _ hk => uComm hj hk,
    fun _ hi => coDec hi, fun _ hi => paDec hi⟩

end Certificates
