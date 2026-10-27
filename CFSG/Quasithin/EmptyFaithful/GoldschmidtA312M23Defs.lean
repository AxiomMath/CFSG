module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312WordsDefs

@[expose] public section

namespace CFSG.Quasithin.A312M23

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat CFSG.Quasithin.A312Words

def oddTabs (n : ℕ) (L : List (Array ℕ)) (xs : List QuotGen) : List (Array ℕ) :=
  xs.map (quotGt n L) ++ xs.map (quotGi n L)

def oddInv (n : ℕ) (L : List (Array ℕ)) (xs : List QuotGen) : List (Array ℕ) :=
  xs.map (quotGi n L) ++ xs.map (quotGt n L)

def WitOK (n : ℕ) (L : List (Array ℕ)) (xs : List QuotGen) (tg : QuotGen) (b : List ℕ) : Prop :=
  b.Pairwise (· < ·) ∧ (∀ p ∈ b, p < n) ∧ (∀ a ∈ oddTabs n L xs, (b.map (img a)).Perm b) ∧
    ¬ (b.map (img (quotGt n L tg))).Perm b

instance (n : ℕ) (L : List (Array ℕ)) (xs : List QuotGen) (tg : QuotGen) (b : List ℕ) :
    Decidable (WitOK n L xs tg b) := by
  unfold WitOK; infer_instance

def NormWordsOK (n : ℕ) (L : List (Array ℕ)) (xs : List QuotGen) (tg : QuotGen)
    (wcj : List (List ℕ)) : Prop :=
  wcj.length = 2 * xs.length ∧ (∀ w ∈ wcj, ∀ l ∈ w, l < 2 * xs.length) ∧
    ∀ i < 2 * xs.length, wordTabA (alphaTabs n L xs (quotGt n L tg)) n wcj[i]! =
      compArr (quotGt n L tg) (compArr (alphaTabs n L xs (quotGt n L tg))[i]! (quotGt n L tg))

instance (n : ℕ) (L : List (Array ℕ)) (xs : List QuotGen) (tg : QuotGen) (wcj : List (List ℕ)) :
    Decidable (NormWordsOK n L xs tg wcj) := by
  unfold NormWordsOK; infer_instance

def BlksOK (n : ℕ) (AT : Array (Array ℕ)) (blks : List (List ℕ)) : Prop :=
  blks.Nodup ∧ (∀ b ∈ blks, b.Pairwise (· < ·) ∧ ∀ p ∈ b, p < n) ∧
    ∀ a ∈ AT.toList, ∀ b ∈ blks, ∃ b' ∈ blks, (b.map (img a)).Perm b'

instance (n : ℕ) (AT : Array (Array ℕ)) (blks : List (List ℕ)) : Decidable (BlksOK n AT blks) := by
  unfold BlksOK; infer_instance

def FixBlksOK (G : List (Array ℕ)) (blks : List (List ℕ)) : Prop :=
  ∀ a ∈ G, ∀ b ∈ blks, (b.map (img a)).Perm b

instance (G : List (Array ℕ)) (blks : List (List ℕ)) : Decidable (FixBlksOK G blks) := by
  unfold FixBlksOK; infer_instance

def indTab (blks : List (List ℕ)) (a : Array ℕ) : Array ℕ :=
  (blks.map fun b => blks.findIdx fun b' => (b.map (img a)).isPerm b').toArray

def ImgOK (n : ℕ) (L : List (Array ℕ)) (xs : List QuotGen) (blks : List (List ℕ))
    (fuel size : ℕ) : Prop :=
  SubOK blks.length (List.range blks.length) ((oddTabs n L xs).map (indTab blks))
    ((oddInv n L xs).map (indTab blks)) fuel size

instance (n : ℕ) (L : List (Array ℕ)) (xs : List QuotGen) (blks : List (List ℕ)) (fuel size : ℕ) :
    Decidable (ImgOK n L xs blks fuel size) := by
  unfold ImgOK; infer_instance

def ImgTransOK (n : ℕ) (L : List (Array ℕ)) (xs : List QuotGen) (blks : List (List ℕ))
    (fuel : ℕ) : Prop :=
  ∀ j < blks.length, ∃ T ∈ (bfsEnumB blks.length (List.range blks.length)
    ((oddTabs n L xs).map (indTab blks)) ((oddInv n L xs).map (indTab blks)) fuel).1.toList,
    T.getD 0 0 = j

instance (n : ℕ) (L : List (Array ℕ)) (xs : List QuotGen) (blks : List (List ℕ)) (fuel : ℕ) :
    Decidable (ImgTransOK n L xs blks fuel) := by
  unfold ImgTransOK; infer_instance

def E2AltOK (n : ℕ) (B : List ℕ) (L : List (Array ℕ)) (xs : List QuotGen) (tg : QuotGen)
    (ws wcj : List (List ℕ)) (b : List ℕ) (blks : List (List ℕ)) (vws : List (List ℕ))
    (fuelV sizeV fuelE sizeE sizeY : ℕ) : Prop :=
  IdxTwoOK n L xs tg ws ∧ NormWordsOK n L xs tg wcj ∧ WitOK n L xs tg b ∧
    BlksOK n (alphaTabs n L xs (quotGt n L tg)) blks ∧ (∀ w ∈ vws, ∀ l ∈ w, l < 2 * xs.length) ∧
    ElemAbOK n B (alphaTabs n L xs (quotGt n L tg)) (alphaInv n L xs (quotGt n L tg)) []
      (vws.map (wordTabA (alphaTabs n L xs (quotGt n L tg)) n)) fuelV sizeV ∧
    FixBlksOK (vws.map (wordTabA (alphaTabs n L xs (quotGt n L tg)) n)) blks ∧
    ImgOK n L xs blks fuelE sizeE ∧ sizeY = 2 * sizeV * sizeE

instance (n : ℕ) (B : List ℕ) (L : List (Array ℕ)) (xs : List QuotGen) (tg : QuotGen)
    (ws wcj : List (List ℕ)) (b : List ℕ) (blks : List (List ℕ)) (vws : List (List ℕ))
    (fuelV sizeV fuelE sizeE sizeY : ℕ) :
    Decidable (E2AltOK n B L xs tg ws wcj b blks vws fuelV sizeV fuelE sizeE sizeY) := by
  unfold E2AltOK; infer_instance

def E2PermOK (n : ℕ) (B : List ℕ) (L : List (Array ℕ)) (xs : List QuotGen) (tg : QuotGen)
    (ws : List (List ℕ)) (blks : List (List ℕ)) (vws : List (List ℕ))
    (fuelV sizeV fuelE sizeE sizeY : ℕ) : Prop :=
  IdxTwoOK n L xs tg ws ∧ BlksOK n (alphaTabs n L xs (quotGt n L tg)) blks ∧
    (∀ w ∈ vws, ∀ l ∈ w, l < 2 * xs.length) ∧
    ElemAbOK n B (alphaTabs n L xs (quotGt n L tg)) (alphaInv n L xs (quotGt n L tg)) []
      (vws.map (wordTabA (alphaTabs n L xs (quotGt n L tg)) n)) fuelV sizeV ∧
    FixBlksOK (vws.map (wordTabA (alphaTabs n L xs (quotGt n L tg)) n)) blks ∧
    ImgOK n L xs blks fuelE sizeE ∧ sizeY = sizeV * sizeE

instance (n : ℕ) (B : List ℕ) (L : List (Array ℕ)) (xs : List QuotGen) (tg : QuotGen)
    (ws : List (List ℕ)) (blks : List (List ℕ)) (vws : List (List ℕ))
    (fuelV sizeV fuelE sizeE sizeY : ℕ) :
    Decidable (E2PermOK n B L xs tg ws blks vws fuelV sizeV fuelE sizeE sizeY) := by
  unfold E2PermOK; infer_instance

def relTab (n : ℕ) (tu tv iu iv : Array ℕ) (r : List (ℕ × Bool)) : Array ℕ :=
  wordTabA #[tu, tv, iu, iv] n (r.map fun l => if l.2 then l.1 else 2 + l.1)

def L34OK (n : ℕ) (L : List (Array ℕ)) (xs : List QuotGen) (tg : QuotGen) (ws : List (List ℕ))
    (wcj : List (List ℕ)) (rels : List (List (ℕ × Bool))) (wu wui wv wvi : List ℕ)
    (wxs : List (List ℕ)) : Prop :=
  IdxTwoOK n L xs tg ws ∧ NormWordsOK n L xs tg wcj ∧
    (∀ w ∈ [wu, wui, wv, wvi], ∀ l ∈ w, l < 2 * xs.length) ∧
    compArr (wordTabA (alphaTabs n L xs (quotGt n L tg)) n wu)
      (wordTabA (alphaTabs n L xs (quotGt n L tg)) n wui) = idTab n ∧
    compArr (wordTabA (alphaTabs n L xs (quotGt n L tg)) n wv)
      (wordTabA (alphaTabs n L xs (quotGt n L tg)) n wvi) = idTab n ∧
    (∀ r ∈ rels, relTab n (wordTabA (alphaTabs n L xs (quotGt n L tg)) n wu)
      (wordTabA (alphaTabs n L xs (quotGt n L tg)) n wv)
      (wordTabA (alphaTabs n L xs (quotGt n L tg)) n wui)
      (wordTabA (alphaTabs n L xs (quotGt n L tg)) n wvi) r = idTab n) ∧
    wxs.length = 2 * xs.length ∧ (∀ w ∈ wxs, ∀ l ∈ w, l < 4) ∧
    ∀ i < 2 * xs.length, wordTabA #[wordTabA (alphaTabs n L xs (quotGt n L tg)) n wu,
      wordTabA (alphaTabs n L xs (quotGt n L tg)) n wv,
      wordTabA (alphaTabs n L xs (quotGt n L tg)) n wui,
      wordTabA (alphaTabs n L xs (quotGt n L tg)) n wvi] n wxs[i]! = (alphaTabs n L xs
        (quotGt n L tg))[i]!

instance (n : ℕ) (L : List (Array ℕ)) (xs : List QuotGen) (tg : QuotGen) (ws : List (List ℕ))
    (wcj : List (List ℕ)) (rels : List (List (ℕ × Bool))) (wu wui wv wvi : List ℕ)
    (wxs : List (List ℕ)) : Decidable (L34OK n L xs tg ws wcj rels wu wui wv wvi wxs) := by
  unfold L34OK; infer_instance

def M22OK (n : ℕ) (L : List (Array ℕ)) (blks : List (List ℕ)) (wA wB : List ℕ)
    (gA gB : Array ℕ) : Prop :=
  blks.length = 22 ∧ BlksOK n L.toArray blks ∧ (∀ l ∈ wA, l < L.length) ∧
    (∀ l ∈ wB, l < L.length) ∧ indTab blks (wordTabA L.toArray n wA) = gA ∧
    indTab blks (wordTabA L.toArray n wB) = gB

instance (n : ℕ) (L : List (Array ℕ)) (blks : List (List ℕ)) (wA wB : List ℕ) (gA gB : Array ℕ) :
    Decidable (M22OK n L blks wA wB gA gB) := by
  unfold M22OK; infer_instance

def TriOK (n : ℕ) (L : List (Array ℕ)) (blks : List (List ℕ)) (x : QuotGen) : Prop :=
  blks.length = 3 ∧ BlksOK n L.toArray blks ∧ (∀ l ∈ x.w, l < L.length) ∧ x.m % 2 = 1 ∧
    powTab n (quotGt n L x) x.m = idTab n ∧
    ¬ ((blks.getD 0 []).map (img (quotGt n L x))).Perm (blks.getD 0 [])

instance (n : ℕ) (L : List (Array ℕ)) (blks : List (List ℕ)) (x : QuotGen) :
    Decidable (TriOK n L blks x) := by
  unfold TriOK; infer_instance

end CFSG.Quasithin.A312M23
