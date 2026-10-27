module

public import CFSG.Monster.B.Mathieu.CertData
public import Certificates.Data.Kernel.Mathieu.Raw

public section

namespace CFSG.Monster.B.Mathieu

open CFSG.KD.Mathieu

@[expose] def decLetter (k : ℕ) : ℤ := if k % 2 = 0 then ((k / 2 : ℕ) : ℤ) else -((k / 2 : ℕ) : ℤ)

@[expose] def decWord (w : List ℕ) : List ℤ := w.map decLetter

@[expose] def decStr (l : List ℕ) : String := String.ofList (l.map Char.ofNat)

@[expose] def decChain (n : ℕ) (G : List (List ℕ)) (B : List ℕ) (S D : List (List ℕ)) :
    ChainRecord :=
  { degree := n, generators := G, base := B, strongGenerators := S, derivations := D.map decWord }

@[expose] def decNGs (n : ℕ) : List (List ℕ) → List (List (List ℕ)) → List (List ℕ) →
    List (List (List ℕ)) → List (List (List ℕ)) → List NormalGenRecord
  | r :: R, c :: C, b :: B, s :: S, d :: D =>
    { representative := r, conjugators := c.map decWord,
      chain := decChain n (s.take c.length) b s d } :: decNGs n R C B S D
  | _, _, _, _, _ => []

@[expose] def decSylows (n : ℕ) : List ℕ → List (List (List ℕ)) → List (List (List ℕ)) →
    List (List (List (List ℕ))) → List (List (List ℕ)) → List (List (List (List ℕ))) →
    List (List (List (List ℕ))) → List SylowRecord
  | p :: P, g :: SG, r :: R, c :: C, b :: B, s :: S, d :: D =>
    { prime := p, generators := g, normalGeneration := decNGs n r c b s d } ::
      decSylows n P SG R C B S D
  | _, _, _, _, _, _, _ => []

@[expose] def decGroup (t : List ℕ) (sp : List (List ℕ)) (n : ℕ) (G : List (List ℕ))
    (B : List ℕ) (S D : List (List ℕ)) (P : List ℕ) (SG : List (List (List ℕ)))
    (R : List (List (List ℕ))) (C : List (List (List (List ℕ)))) (NB : List (List (List ℕ)))
    (NS ND : List (List (List (List ℕ)))) : GroupRecord :=
  { group := decStr t, seedPaths := sp.map decStr, chain := decChain n G B S D,
    sylows := decSylows n P SG R C NB NS ND }

@[expose] noncomputable def m11RecordK : GroupRecord :=
  decGroup (tags.getD 0 []) (seeds.getD 0 []) 11 m11G m11B m11S m11D m11P m11SG m11NR m11NC
    m11NB m11NS m11ND

@[expose] noncomputable def m12RecordK : GroupRecord :=
  decGroup (tags.getD 1 []) (seeds.getD 1 []) 12 m12G m12B m12S m12D m12P m12SG m12NR m12NC
    m12NB m12NS m12ND

@[expose] noncomputable def m22RecordK : GroupRecord :=
  decGroup (tags.getD 2 []) (seeds.getD 2 []) 22 m22G m22B m22S m22D m22P m22SG m22NR m22NC
    m22NB m22NS m22ND

@[expose] noncomputable def m23RecordK : GroupRecord :=
  decGroup (tags.getD 3 []) (seeds.getD 3 []) 23 m23G m23B m23S m23D m23P m23SG m23NR m23NC
    m23NB m23NS m23ND

@[expose] noncomputable def m24RecordK : GroupRecord :=
  decGroup (tags.getD 4 []) (seeds.getD 4 []) 24 m24G m24B m24S m24D m24P m24SG m24NR m24NC
    m24NB m24NS m24ND

@[expose] noncomputable def certificateFileK : CertificateFile :=
  { schemaVersion := schema, description := decStr desc, permutationConvention := decStr conv,
    groups := [m11RecordK, m12RecordK, m22RecordK, m23RecordK, m24RecordK] }

@[expose] noncomputable def MathieuCertificateK (t : String) : Option GroupRecord :=
  certificateFileK.groups.find? fun r => r.group == t

@[expose] def natDigits : ℕ → ℕ → List Char → List Char
  | 0, _, acc => acc
  | f + 1, m, acc =>
    if m < 10 then Char.ofNat (48 + m) :: acc else natDigits f (m / 10) (Char.ofNat (48 + m % 10) :: acc)

@[expose] def jsonNat (m : ℕ) : List Char := natDigits (m + 1) m []

@[expose] def jsonInt (z : ℤ) : List Char :=
  if z < 0 then '-' :: jsonNat z.natAbs else jsonNat z.natAbs

@[expose] def jsonStr (s : String) : List Char := '"' :: (s.toList ++ ['"'])

@[expose] def jsonSep {α : Type} (f : α → List Char) : List α → List Char
  | [] => []
  | [a] => f a
  | a :: l => f a ++ (',' :: jsonSep f l)

@[expose] def jsonArr {α : Type} (f : α → List Char) (l : List α) : List Char :=
  '[' :: (jsonSep f l ++ [']'])

@[expose] def jsonKey (k : List Char) : List Char := '"' :: (k ++ ['"', ':'])

@[expose] def jsonChain (c : ChainRecord) : List Char :=
  '{' :: (jsonKey ['d', 'e', 'g', 'r', 'e', 'e'] ++ jsonNat c.degree ++ ',' ::
    jsonKey ['g', 'e', 'n', 'e', 'r', 'a', 't', 'o', 'r', 's'] ++
    jsonArr (jsonArr jsonNat) c.generators ++ ',' :: jsonKey ['b', 'a', 's', 'e'] ++
    jsonArr jsonNat c.base ++ ',' ::
    jsonKey ['s', 't', 'r', 'o', 'n', 'g', '_', 'g', 'e', 'n', 'e', 'r', 'a', 't', 'o', 'r', 's'] ++
    jsonArr (jsonArr jsonNat) c.strongGenerators ++ ',' ::
    jsonKey ['d', 'e', 'r', 'i', 'v', 'a', 't', 'i', 'o', 'n', 's'] ++
    jsonArr (jsonArr jsonInt) c.derivations ++ ['}'])

@[expose] def jsonNG (ng : NormalGenRecord) : List Char :=
  '{' :: (jsonKey ['r', 'e', 'p', 'r', 'e', 's', 'e', 'n', 't', 'a', 't', 'i', 'v', 'e'] ++
    jsonArr jsonNat ng.representative ++ ',' ::
    jsonKey ['c', 'o', 'n', 'j', 'u', 'g', 'a', 't', 'o', 'r', 's'] ++
    jsonArr (jsonArr jsonInt) ng.conjugators ++ ',' :: jsonKey ['c', 'h', 'a', 'i', 'n'] ++
    jsonChain ng.chain ++ ['}'])

@[expose] def jsonSylow (s : SylowRecord) : List Char :=
  '{' :: (jsonKey ['p', 'r', 'i', 'm', 'e'] ++ jsonNat s.prime ++ ',' ::
    jsonKey ['g', 'e', 'n', 'e', 'r', 'a', 't', 'o', 'r', 's'] ++
    jsonArr (jsonArr jsonNat) s.generators ++ ',' ::
    jsonKey ['n', 'o', 'r', 'm', 'a', 'l', '_', 'g', 'e', 'n', 'e', 'r', 'a', 't', 'i', 'o', 'n'] ++
    jsonArr jsonNG s.normalGeneration ++ ['}'])

@[expose] def jsonGroup (r : GroupRecord) : List Char :=
  '{' :: (jsonKey ['g', 'r', 'o', 'u', 'p'] ++ jsonStr r.group ++ ',' ::
    jsonKey ['s', 'e', 'e', 'd', '_', 'p', 'a', 't', 'h', 's'] ++ jsonArr jsonStr r.seedPaths ++
    ',' :: jsonKey ['c', 'h', 'a', 'i', 'n'] ++ jsonChain r.chain ++ ',' ::
    jsonKey ['s', 'y', 'l', 'o', 'w', 's'] ++ jsonArr jsonSylow r.sylows ++ ['}'])

@[expose] def jsonFile (f : CertificateFile) : List Char :=
  '{' :: (jsonKey ['s', 'c', 'h', 'e', 'm', 'a', '_', 'v', 'e', 'r', 's', 'i', 'o', 'n'] ++
    jsonNat f.schemaVersion ++ ',' ::
    jsonKey ['d', 'e', 's', 'c', 'r', 'i', 'p', 't', 'i', 'o', 'n'] ++ jsonStr f.description ++
    ',' :: jsonKey ['p', 'e', 'r', 'm', 'u', 't', 'a', 't', 'i', 'o', 'n', '_', 'c', 'o', 'n', 'v',
      'e', 'n', 't', 'i', 'o', 'n'] ++
    jsonStr f.permutationConvention ++ ',' :: jsonKey ['g', 'r', 'o', 'u', 'p', 's'] ++
    jsonArr jsonGroup f.groups ++ ['}', '\n'])

end CFSG.Monster.B.Mathieu
