module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCover2CertInputs
public import Certificates.Data.Kernel.L34W.Tab42

public section

namespace CFSG.KC.L34Cov

open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.PSL3Four.Native CFSG.KC.L34W CFSG.KC.Enum
open CFSG.KS

@[expose] def cEnc (d : ℕ × ℕ × ℕ × ℕ × ℕ) : ℕ := 1 + d.2.2.1 / 2 + 2 * (d.2.2.2.1 / 2)

@[expose] def cTab (L : List (ℕ × ℕ × ℕ × ℕ × ℕ)) : ℕ :=
  L.foldl (fun t d => t ||| (cEnc d <<< (3 * (64 * d.1 + d.2.1)))) 0

@[expose] def lookC (T k l : ℕ) : ℕ :=
  if k < 64 ∧ l < 64 then (T >>> (3 * (64 * k + l))) % 8 else 0

@[expose] def cbK (T κ k l : ℕ) (f : Bool) : Bool :=
  !(lookC T k l == 0) && kbit κ (2 * ((lookC T k l - 1) % 2)) (2 * ((lookC T k l - 1) / 2)) == f

@[expose] def cOK1 (T : ℕ) : Bool :=
  commData2.all fun d => ((d.2.2.1 == 0 || d.2.2.1 == 2) && (d.2.2.2.1 == 0 || d.2.2.2.1 == 2)) &&
    lookC T d.1 d.2.1 == cEnc d

@[expose] def cOK2 (T : ℕ) : Bool :=
  (List.range 64).all fun k => (List.range 64).all fun l =>
    lookC T k l == 0 || commData2.any fun d => d.1 == k && d.2.1 == l

@[expose] def transK (T : ℕ) : Bool :=
  [0, 1, 2].all fun κ => uIdx.all fun I => I.all fun k₁ => I.all fun k₂ =>
    (k₁ == 0 || k₂ == 0 || k₁ == k₂) || [false, true].all fun f₁ => [false, true].all fun f₂ =>
      I.any fun w => cbK T κ k₁ w f₁ && cbK T κ k₂ w f₂

@[expose] noncomputable def cceK (T : ℕ) (G : ℕ → ℕ) : Bool :=
  cceIdx.all fun d => cbK T d.1 d.2.1 4 false && cbK T d.1 d.2.1 8 false &&
    fourthBit d.1 d.2.1 &&
      pcomp 42 6 (mask 6) (tgK G d.2.1) (tgK G d.2.1) == tgK G d.2.2

end CFSG.KC.L34Cov

end
