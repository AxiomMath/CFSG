module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatQuot

@[expose] public section

namespace CFSG.Quasithin.A312Words

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat

def alphaTabs (n : ℕ) (L : List (Array ℕ)) (xs : List QuotGen) (t : Array ℕ) :
    Array (Array ℕ) :=
  (xs.map (quotGt n L) ++ xs.map (quotGi n L) ++ [t]).toArray

def alphaInv (n : ℕ) (L : List (Array ℕ)) (xs : List QuotGen) (t : Array ℕ) :
    Array (Array ℕ) :=
  (xs.map (quotGi n L) ++ xs.map (quotGt n L) ++ [t]).toArray

def OddElts (n : ℕ) (L : List (Array ℕ)) (xs : List QuotGen) : Prop :=
  ∀ x ∈ xs, (∀ l ∈ x.w, l < L.length) ∧ x.m % 2 = 1 ∧ powTab n (quotGt n L x) x.m = idTab n

def InvElt (n : ℕ) (L : List (Array ℕ)) (tg : QuotGen) : Prop :=
  (∀ l ∈ tg.w, l < L.length) ∧ powTab n (quotGt n L tg) 2 = idTab n

def IdxTwoOK (n : ℕ) (L : List (Array ℕ)) (xs : List QuotGen) (tg : QuotGen)
    (ws : List (List ℕ)) : Prop :=
  OddElts n L xs ∧ InvElt n L tg ∧ ws.length = L.length ∧
    (∀ w ∈ ws, ∀ l ∈ w, l < 2 * xs.length + 1) ∧
    ∀ j < L.length, wordTabA (alphaTabs n L xs (quotGt n L tg)) n ws[j]! = L[j]!

instance (n : ℕ) (L : List (Array ℕ)) (xs : List QuotGen) (tg : QuotGen) (ws : List (List ℕ)) :
    Decidable (IdxTwoOK n L xs tg ws) := by
  unfold IdxTwoOK OddElts InvElt; infer_instance

def SubOK (n : ℕ) (B : List ℕ) (G Gi : List (Array ℕ)) (fuel size : ℕ) : Prop :=
  BaseEnumOK n B G Gi (bfsEnumB n B G Gi fuel).1 (bfsEnumB n B G Gi fuel).2.1
    (bfsEnumB n B G Gi fuel).2.2 ∧ (bfsEnumB n B G Gi fuel).1.size = size

instance (n : ℕ) (B : List ℕ) (G Gi : List (Array ℕ)) (fuel size : ℕ) :
    Decidable (SubOK n B G Gi fuel size) := by
  unfold SubOK; infer_instance

def NormIn (n : ℕ) (B : List ℕ) (G Gi : List (Array ℕ)) (fuel : ℕ)
    (AT AI : Array (Array ℕ)) : Prop :=
  ∀ a ∈ G, ∀ k < AT.size,
    (ptsOf B G).map (conjImg a AT[k]! AI[k]!) ∈ (bfsEnumB n B G Gi fuel).1.toList

instance (n : ℕ) (B : List ℕ) (G Gi : List (Array ℕ)) (fuel : ℕ) (AT AI : Array (Array ℕ)) :
    Decidable (NormIn n B G Gi fuel AT AI) := by
  unfold NormIn; infer_instance

def SixOK (n : ℕ) (AT : Array (Array ℕ)) (pts : List ℕ) (w1 w2 : List ℕ) : Prop :=
  pts.length = 6 ∧ pts.Nodup ∧ (∀ p ∈ pts, p < n) ∧
    (∀ a ∈ AT.toList, ∀ p ∈ pts, img a p ∈ pts) ∧
    (∀ l ∈ w1, l < AT.size) ∧ (∀ l ∈ w2, l < AT.size) ∧
    (∀ i < 6, img (wordTabA AT n w1) pts[i]! = pts[(i + 1) % 6]!) ∧
    ∀ i < 6, img (wordTabA AT n w2) pts[i]! = pts[if i = 0 then 1 else if i = 1 then 0 else i]!

instance (n : ℕ) (AT : Array (Array ℕ)) (pts : List ℕ) (w1 w2 : List ℕ) :
    Decidable (SixOK n AT pts w1 w2) := by
  unfold SixOK; infer_instance

def ElemAbOK (n : ℕ) (B : List ℕ) (AT AI : Array (Array ℕ)) (pts : List ℕ) (G : List (Array ℕ))
    (fuel size : ℕ) : Prop :=
  (∀ a ∈ G, compArr a a = idTab n) ∧ (∀ a ∈ G, ∀ b ∈ G, compArr a b = compArr b a) ∧
    (∀ a ∈ G, ∀ p ∈ pts, img a p = p) ∧ SubOK n B G G fuel size ∧ NormIn n B G G fuel AT AI

instance (n : ℕ) (B : List ℕ) (AT AI : Array (Array ℕ)) (pts : List ℕ) (G : List (Array ℕ))
    (fuel size : ℕ) : Decidable (ElemAbOK n B AT AI pts G fuel size) := by
  unfold ElemAbOK; infer_instance

def cubeTabs (n : ℕ) (G : List (Array ℕ)) : List (Array ℕ) := G.map fun a => powTab n a 3

def ExtraOK (n : ℕ) (B : List ℕ) (AT AI : Array (Array ℕ)) (G : List (Array ℕ))
    (Tz : Array ℕ) (fuel size : ℕ) : Prop :=
  (∀ a ∈ G, ∀ b ∈ G, compArr a b = compArr b a ∨ compArr a b = compArr Tz (compArr b a)) ∧
    (∀ a ∈ G, compArr a a = idTab n ∨ compArr a a = Tz) ∧
    (∀ a ∈ G, compArr Tz a = compArr a Tz) ∧ compArr Tz Tz = idTab n ∧ Tz ≠ idTab n ∧
    SubOK n B G (cubeTabs n G) fuel size ∧
    (ptsOf B G).map (img Tz) ∈ (bfsEnumB n B G (cubeTabs n G) fuel).1.toList ∧
    NormIn n B G (cubeTabs n G) fuel AT AI ∧
    ∀ T ∈ (bfsEnumB n B G (cubeTabs n G) fuel).1.toList,
      (∀ t < G.length, ∀ j < B.length,
        T.getD (B.length * (1 + t) + j) 0 = img (G.getD t #[]) (T.getD j 0)) →
      T = ptsOf B G ∨ T = applyTab Tz (ptsOf B G)

instance (n : ℕ) (B : List ℕ) (AT AI : Array (Array ℕ)) (G : List (Array ℕ)) (Tz : Array ℕ)
    (fuel size : ℕ) : Decidable (ExtraOK n B AT AI G Tz fuel size) := by
  unfold ExtraOK; infer_instance

def HatOK (n : ℕ) (B : List ℕ) (L : List (Array ℕ)) (xs : List QuotGen) (tg : QuotGen)
    (ws : List (List ℕ)) (pts : List ℕ) (w1 w2 : List ℕ) (vws : List (List ℕ)) (fuel size : ℕ) :
    Prop :=
  IdxTwoOK n L xs tg ws ∧ SixOK n (alphaTabs n L xs (quotGt n L tg)) pts w1 w2 ∧
    (∀ w ∈ vws, ∀ l ∈ w, l < 2 * xs.length) ∧
    ElemAbOK n B (alphaTabs n L xs (quotGt n L tg)) (alphaInv n L xs (quotGt n L tg)) pts
      (vws.map (wordTabA (alphaTabs n L xs (quotGt n L tg)) n)) fuel size

instance (n : ℕ) (B : List ℕ) (L : List (Array ℕ)) (xs : List QuotGen) (tg : QuotGen)
    (ws : List (List ℕ)) (pts : List ℕ) (w1 w2 : List ℕ) (vws : List (List ℕ)) (fuel size : ℕ) :
    Decidable (HatOK n B L xs tg ws pts w1 w2 vws fuel size) := by
  unfold HatOK; infer_instance

def ExtraGenOK (n : ℕ) (B : List ℕ) (L : List (Array ℕ)) (xs : List QuotGen) (tg : QuotGen)
    (ws wws : List (List ℕ)) (zw : List ℕ) (fuel size : ℕ) : Prop :=
  IdxTwoOK n L xs tg ws ∧ (∀ w ∈ wws, ∀ l ∈ w, l < L.length) ∧ (∀ l ∈ zw, l < L.length) ∧
    ExtraOK n B (alphaTabs n L xs (quotGt n L tg)) (alphaInv n L xs (quotGt n L tg))
      (wws.map (wordTabA L.toArray n)) (wordTabA L.toArray n zw) fuel size

instance (n : ℕ) (B : List ℕ) (L : List (Array ℕ)) (xs : List QuotGen) (tg : QuotGen)
    (ws wws : List (List ℕ)) (zw : List ℕ) (fuel size : ℕ) :
    Decidable (ExtraGenOK n B L xs tg ws wws zw fuel size) := by
  unfold ExtraGenOK; infer_instance

end CFSG.Quasithin.A312Words
