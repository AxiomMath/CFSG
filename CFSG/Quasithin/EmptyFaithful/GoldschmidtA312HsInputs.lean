module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHSInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatQuot
public import Certificates.Data.CFSGNative.SporLat.BuildPt

public section

namespace CFSG.Quasithin.A312Hs

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.HS
open CFSG.Sporadic.HS.Native (hsData)

@[expose] def explTabs (n : ℕ) (L : List (Array ℕ)) (N : ℕ) (word : ℕ → List ℕ) :
    Array (Array ℕ) :=
  ((List.range N).map fun i => wordTabA L.toArray n (word i)).toArray

@[expose] def ExplOK' (L : List (Array ℕ)) (N : ℕ) (word : ℕ → List ℕ) (mulf : ℕ → ℕ → ℕ)
    (conj : List (List ℕ)) (T : Array (Array ℕ)) : Prop :=
  word 0 = [] ∧ (∀ i < N, ∀ l ∈ word i, l < L.length) ∧
    (∀ i < N, ∀ k < N, i ≠ k → T[i]! ≠ T[k]!) ∧
    (∀ i < N, ∀ k < N, mulf i k < N ∧ compArr T[i]! T[k]! = T[mulf i k]!) ∧
    conj.length = L.length ∧
    ∀ l < L.length, (conj[l]!).length = N ∧
      ∀ i < N, (conj[l]!)[i]! < N ∧ compArr L[l]! T[i]! = compArr T[(conj[l]!)[i]!]! L[l]!

instance (L : List (Array ℕ)) (N : ℕ) (word : ℕ → List ℕ) (mulf : ℕ → ℕ → ℕ)
    (conj : List (List ℕ)) (T : Array (Array ℕ)) : Decidable (ExplOK' L N word mulf conj T) := by
  unfold ExplOK'; infer_instance

@[expose] def ExplOK (n : ℕ) (L : List (Array ℕ)) (N : ℕ) (word : ℕ → List ℕ)
    (mulf : ℕ → ℕ → ℕ) (conj : List (List ℕ)) : Prop :=
  ExplOK' L N word mulf conj (explTabs n L N word)

instance (n : ℕ) (L : List (Array ℕ)) (N : ℕ) (word : ℕ → List ℕ) (mulf : ℕ → ℕ → ℕ)
    (conj : List (List ℕ)) : Decidable (ExplOK n L N word mulf conj) := by
  unfold ExplOK; infer_instance

@[expose] def hsLetters (j : ℕ) : List (Array ℕ) := hsLat.sTabs ++ hsLat.mt[j]!

@[expose] def hsIncl : List (List ℕ) := [[0, 1, 2, 3, 4], [1], [2], [2, 3], [1, 2, 4]]

@[expose] def repWord (w : List ℕ) (a : ℕ) : List ℕ := (List.replicate a w).flatten

@[expose] def bitOf (i t : ℕ) : ℕ := i / 2 ^ t % 2

@[expose] def hsV1CW : List ℕ :=
  [0, 1, 0, 2, 1, 0, 2, 1, 0, 2, 1, 2]

@[expose] def hsV1E1W : List ℕ :=
  [0]

@[expose] def hsV1E2W : List ℕ :=
  [1, 0, 1]

@[expose] def hsV1E3W : List ℕ :=
  [2, 0, 2]

@[expose] def hsV1E4W : List ℕ :=
  [3, 0, 3, 3]

@[expose] def hsV1Conj : List (List ℕ) := [
  [0, 1, 2, 3, 36, 37, 38, 39, 8, 9, 10, 11, 44, 45, 46, 47, 16, 17, 18, 19, 52, 53, 54, 55, 24, 25,
    26, 27, 60, 61, 62, 63, 32, 33, 34, 35, 4, 5, 6, 7, 40, 41, 42, 43, 12, 13, 14, 15, 48, 49, 50,
    51, 20, 21, 22, 23, 56, 57, 58, 59, 28, 29, 30, 31],
  [0, 2, 1, 3, 39, 37, 38, 36, 30, 28, 31, 29, 25, 27, 24, 26, 48, 50, 49, 51, 23, 21, 22, 20, 14,
    12, 15, 13, 9, 11, 8, 10, 32, 34, 33, 35, 7, 5, 6, 4, 62, 60, 63, 61, 57, 59, 56, 58, 16, 18,
    17, 19, 55, 53, 54, 52, 46, 44, 47, 45, 41, 43, 40, 42],
  [0, 36, 13, 9, 33, 37, 12, 40, 39, 3, 42, 46, 6, 2, 43, 15, 16, 52, 29, 25, 49, 53, 28, 56, 55,
    19, 58, 62, 22, 18, 59, 31, 32, 4, 45, 41, 1, 5, 44, 8, 7, 35, 10, 14, 38, 34, 11, 47, 48, 20,
    61, 57, 17, 21, 60, 24, 23, 51, 26, 30, 54, 50, 27, 63],
  [0, 8, 47, 39, 35, 11, 44, 4, 9, 1, 6, 14, 42, 2, 5, 45, 16, 24, 63, 55, 51, 27, 60, 20, 25, 17,
    22, 30, 58, 18, 21, 61, 32, 40, 15, 7, 3, 43, 12, 36, 41, 33, 38, 46, 10, 34, 37, 13, 48, 56,
    31, 23, 19, 59, 28, 52, 57, 49, 54, 62, 26, 50, 53, 29]]

@[expose] def hsV2W1 : List ℕ :=
  [0, 1, 2, 1]

@[expose] def hsV2W2 : List ℕ :=
  [0, 2, 0, 2]

@[expose] def hsV2W3 : List ℕ :=
  [1, 0, 1, 2]

@[expose] def hsV2Conj : List (List ℕ) := [
  [0, 5, 10, 15, 12, 1, 6, 11, 8, 13, 2, 7, 4, 9, 14, 3, 56, 61, 50, 55, 52, 57, 62, 51, 48, 53, 58,
    63, 60, 49, 54, 59, 32, 37, 42, 47, 44, 33, 38, 43, 40, 45, 34, 39, 36, 41, 46, 35, 24, 29, 18,
    23, 20, 25, 30, 19, 16, 21, 26, 31, 28, 17, 22, 27],
  [0, 16, 32, 48, 12, 28, 44, 60, 8, 24, 40, 56, 4, 20, 36, 52, 1, 17, 33, 49, 13, 29, 45, 61, 9,
    25, 41, 57, 5, 21, 37, 53, 2, 18, 34, 50, 14, 30, 46, 62, 10, 26, 42, 58, 6, 22, 38, 54, 3, 19,
    35, 51, 15, 31, 47, 63, 11, 27, 43, 59, 7, 23, 39, 55],
  [0, 11, 2, 9, 12, 7, 14, 5, 8, 3, 10, 1, 4, 15, 6, 13, 28, 23, 30, 21, 24, 19, 26, 17, 20, 31, 22,
    29, 16, 27, 18, 25, 40, 35, 42, 33, 36, 47, 38, 45, 32, 43, 34, 41, 44, 39, 46, 37, 52, 63, 54,
    61, 48, 59, 50, 57, 60, 55, 62, 53, 56, 51, 58, 49],
  [0, 16, 32, 48, 35, 51, 3, 19, 2, 18, 34, 50, 33, 49, 1, 17, 28, 44, 60, 12, 63, 15, 31, 47, 30,
    46, 62, 14, 61, 13, 29, 45, 40, 56, 8, 24, 11, 27, 43, 59, 42, 58, 10, 26, 9, 25, 41, 57, 52, 4,
    20, 36, 23, 39, 55, 7, 54, 6, 22, 38, 21, 37, 53, 5]]

@[expose] def hsQuot2 : List QuotGen := [
  ⟨[0, 2, 2, 1, 2, 3, 1, 2, 0, 3, 2, 1, 1, 2, 0, 3, 1, 1, 1, 0, 1, 2, 2, 0, 3, 2, 0, 3, 0, 0, 1, 1],
    1, 7⟩,
  ⟨[3, 2, 0, 0, 0, 3, 0, 3, 1, 0, 2, 1, 0, 3, 0, 0], 4, 3⟩,
  ⟨[1, 3, 3, 2, 0, 0, 3, 1, 1, 1, 1, 2, 2, 1, 0, 2, 3], 2, 3⟩]

@[expose] def hsV1Word (i : ℕ) : List ℕ :=
  repWord hsV1CW (i / 16) ++ (if bitOf i 0 = 1 then hsV1E1W else []) ++
    (if bitOf i 1 = 1 then hsV1E2W else []) ++ (if bitOf i 2 = 1 then hsV1E3W else []) ++
    (if bitOf i 3 = 1 then hsV1E4W else [])

@[expose] def hsV1B : List (List ℕ) := [[0, 0, 1, 0], [0, 0, 1, 1], [1, 1, 0, 1], [0, 1, 1, 0]]

@[expose] def hsV1Cross (i k : ℕ) : ℕ :=
  (List.range 4).foldl (fun s a => (List.range a).foldl
    (fun s b => s + (hsV1B[a]!)[b]! * bitOf i a * bitOf k b) s) 0

@[expose] def hsV1Mul (i k : ℕ) : ℕ :=
  ((i / 16 + k / 16 + 2 * hsV1Cross i k) % 4) * 16 + ((i % 16) ^^^ (k % 16))

@[expose] def hsV2Word (i : ℕ) : List ℕ :=
  repWord hsV2W1 (i / 16) ++ repWord hsV2W2 (i / 4 % 4) ++ repWord hsV2W3 (i % 4)

@[expose] def hsV2Mul (i k : ℕ) : ℕ :=
  16 * ((i / 16 + k / 16) % 4) + 4 * ((i / 4 % 4 + k / 4 % 4) % 4) + (i % 4 + k % 4) % 4

@[expose] def hsQuot2Enum : Array (List ℕ) × Array ℕ × Array ℕ :=
  bfsEnumB hsData.n hsB (hsQuot2.map (quotGt hsData.n (hsLetters 2)))
    (hsQuot2.map (quotGi hsData.n (hsLetters 2))) 1000000

@[expose] def HsStructOK : Prop :=
  inclPt hsDelta hsLat 5 hsIncl = true ∧
    ExplOK hsData.n (hsLetters 1) 64 hsV1Word hsV1Mul hsV1Conj ∧
    ExplOK hsData.n (hsLetters 2) 64 hsV2Word hsV2Mul hsV2Conj ∧
    QuotOK hsData.n hsB (hsLetters 2) hsQuot2 hsQuot2Enum.1 hsQuot2Enum.2.1 hsQuot2Enum.2.2 10752

instance : Decidable HsStructOK := by
  unfold HsStructOK; infer_instance

end CFSG.Quasithin.A312Hs
