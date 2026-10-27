module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28OmCheck
public import Certificates.Data.ONanG28T

public section

namespace CFSG.AGLEmbedding.KFactProofs.G28

open CFSG.Quasithin CFSG.RankThree.PartTwo.Sec4.Item434G28

@[expose] def omLo (k : ℕ) : ℕ :=
  if k = 0 then 0 else if k = 1 then 1 else if k = 2 then 32320 else if k = 3 then 65152 else
    if k = 4 then 97984 else 130816

@[expose] def omSc : Array (Array ℕ) :=
  Array.ofFn (n := 8) fun s =>
    if s.val < 4 then wordCode gW[s.val]! else wordCode (gW[s.val - 4]!).reverse

@[expose] def omSic : Array (Array ℕ) :=
  Array.ofFn (n := 8) fun s =>
    if s.val < 4 then wordCode (gW[s.val]!).reverse else wordCode gW[s.val - 4]!

theorem omSc_getElem {s : ℕ} (hs : s < 8) : omSc[s]! =
    if s < 4 then wordCode gW[s]! else wordCode (gW[s - 4]!).reverse := by
  rw [omSc, getElem!_ofFn_nat' _ hs]

theorem omSic_getElem {s : ℕ} (hs : s < 8) : omSic[s]! =
    if s < 4 then wordCode (gW[s]!).reverse else wordCode gW[s - 4]! := by
  rw [omSic, getElem!_ofFn_nat' _ hs]

theorem omLo_vals : omLo 0 = 0 ∧ omLo 1 = 1 ∧ omLo 2 = 32320 ∧ omLo 3 = 65152 ∧
    omLo 4 = 97984 ∧ omLo 5 = 130816 := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

structure OmCodes where
  pt : ℕ → Array ℕ
  par : ℕ → ℕ
  sym : ℕ → ℕ
  seedW : List (List ℕ)
  schW : List (List ℕ)
  c : ℕ
  hpt : ℕ → Array ℕ
  hpar : ℕ → ℕ
  hsym : ℕ → ℕ

structure OmCodes.OK (D : OmCodes) : Prop where
  quad : ∀ t < 36, (mulCode tzc tzc)[t]! ^^^ tzc[t]! ^^^ idCode[t]! = 0
  eps : ∀ j < 4, mulCode (mulCode (wordCode gW[j]!) tzc) (wordCode (gW[j]!).reverse) =
    if j % 2 = 1 then mulCode tzc tzc else tzc
  seed_len : D.seedW.length = 4
  seed_rev : ∀ w ∈ D.seedW, mulCode (wordCode w) (wordCode w.reverse) = idCode ∧
    mulCode (wordCode w.reverse) (wordCode w) = idCode
  root0 : D.pt 0 = canonCode tzc
  roots : ∀ k, 0 < k → k < 5 → D.pt (omLo k) =
    canonCode (conjCode (wordCode D.seedW[k - 1]!) (wordCode (D.seedW[k - 1]!).reverse) tzc)
  step : ∀ k < 5, ∀ n, omLo k < n → n < omLo (k + 1) →
    omLo k ≤ D.par n ∧ D.par n < n ∧ D.sym n < 4 ∧
      D.pt n = canonCode (conjCode (wordCode gW[D.sym n]!) (wordCode (gW[D.sym n]!).reverse)
        (D.pt (D.par n)))
  inj : ∀ i < 130816, ∀ j < 130816, D.pt i = D.pt j → i = j
  sch_len : D.schW.length = 8
  sch_sym : ∀ w ∈ D.schW, ∀ s ∈ w, s < 8
  fix : ∀ w ∈ D.schW, canonCode (conjCode (schCode omSc w) (schInv omSic w) (D.pt 1)) = D.pt 1
  c_lt : D.c < 130816
  hroot : D.hpt 0 = D.pt D.c
  hstep : ∀ n, 0 < n → n < 1024 → D.hpar n < n ∧ D.hsym n < 8 ∧
    D.hpt n = canonCode (conjCode (schCode omSc D.schW[D.hsym n]!)
      (schInv omSic D.schW[D.hsym n]!) (D.hpt (D.hpar n)))
  hinj : ∀ i < 1024, ∀ j < 1024, D.hpt i = D.hpt j → i = j

end CFSG.AGLEmbedding.KFactProofs.G28
