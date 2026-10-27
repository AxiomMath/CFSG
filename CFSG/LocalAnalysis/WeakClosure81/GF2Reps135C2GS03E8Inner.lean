module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneClassListE8
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2GS03E8Gen

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GS03E8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open scoped commutatorElement

@[expose] def innerWords : ℕ → List (List ℕ)
  | 0 =>
    [[7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 6, 5, 4, 3, 1, 7, 6, 5, 4, 3, 2], [7, 6, 5,
      4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 2, 7, 6, 5, 4, 3], [7, 6, 5, 4, 3, 1,
      2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 7, 6, 5, 4, 3], [7, 6, 5, 4, 3, 1, 2, 0, 3,
      2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 7, 6, 5, 4], [7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3,
      1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 7, 6, 5], [7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4,
      3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 7, 6], [7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0,
      6, 5, 4, 3, 1, 2, 3, 4, 5, 7], [7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4,
      3, 1, 2, 3, 4, 5, 6], [7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2,
      3, 4, 5, 6, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5,
      6, 7]]
  | 1 =>
    [[0, 1, 2, 3, 1, 2, 4, 3, 1, 2, 0, 5, 4, 3, 1, 2, 0, 3, 4, 5, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3,
      1, 5, 4, 3, 6, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4],
      [0, 1, 2, 3, 1, 2, 4, 3, 1, 2, 0, 5, 4, 3, 1, 2, 0, 3, 4, 5, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3,
      1, 5, 4, 3, 2, 0, 6, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2,
      3, 7, 6, 5, 4, 3, 2, 0], [0, 1, 2, 3, 1, 2, 4, 3, 1, 2, 0, 5, 4, 3, 1, 2, 0, 3, 6, 5, 4, 3, 1,
      2, 0, 3, 2, 4, 5, 6, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2,
      3, 4], [0, 1, 2, 3, 1, 2, 4, 3, 1, 2, 0, 5, 4, 3, 1, 2, 0, 3, 4, 5, 6, 5, 4, 3, 1, 2, 0, 3, 2,
      4, 3, 1, 5, 4, 3, 2, 0, 6, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3,
      1, 2, 3, 7, 6, 5, 4, 3, 1, 2], [0, 2, 3, 1, 4, 3, 2, 0, 5, 4, 3, 1, 2, 3, 4, 5, 6, 5, 4, 3, 1,
      2, 0, 3, 2, 4, 5, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 4, 6, 5], [0, 1, 2, 3, 1, 2, 4, 3, 1,
      2, 0, 5, 4, 3, 1, 2, 0, 3, 6, 5, 4, 3, 1, 2, 0, 3, 4, 5, 6, 7], [0, 1, 2, 3, 1, 4, 3, 2, 0, 5,
      4, 3, 1, 2, 3, 4, 5, 6, 5, 4, 3, 1, 2, 3, 4, 5, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4]]
  | 2 =>
    [[0, 2, 3, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 7, 6, 5, 4, 3, 1, 2,
      0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 3, 4, 5, 6, 7, 6, 5, 4, 3, 1, 2, 0, 3, 4,
      5], [0, 4, 3, 1, 2, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 6, 7, 6, 5, 4, 3, 1, 2, 0,
      3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 7], [0, 2, 0, 3, 1, 4, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4,
      3, 1, 5, 4, 3, 2, 6, 5, 4, 3, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 6], [0, 2, 3, 1, 4,
      3, 2, 6, 5, 4, 3, 1, 2, 0, 3, 4, 5, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6,
      7], [0, 2, 0, 3, 2, 4, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6, 5, 4, 3, 1, 2, 7,
      6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 6, 5, 4, 3, 7, 6, 5]]
  | _ =>
    [[0, 1, 2, 0, 3, 1, 2, 0, 4, 3, 1, 2, 0, 3, 4, 5, 4, 3, 1, 2, 3, 4, 5, 6, 5, 4, 3, 1, 2, 0, 3,
      2, 4, 3, 1, 5, 4, 3, 7, 6, 5, 4, 3, 1, 2, 0], [1, 2, 3, 2, 0, 4, 3, 1, 2, 5, 4, 3, 1, 2, 6, 5,
      4, 3, 1, 2, 0, 7], [0, 1, 2, 0, 3, 1, 2, 0, 4, 3, 1, 2, 3, 5, 4, 3, 1, 2, 0, 3, 2, 4, 5, 6, 5,
      4, 3, 1, 2, 0, 3, 2, 4, 3, 5, 4, 6, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6,
      5, 4, 3, 1, 2, 3, 7, 6], [0, 1, 2, 3, 1, 2, 3, 4, 3, 1, 2, 0, 3, 2, 5, 4, 3, 1, 2, 0, 3, 4, 5,
      6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 5, 6, 7, 6, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 2, 0, 6,
      5], [0, 1, 2, 3, 1, 2, 0, 4, 3, 1, 2, 0, 5, 4, 3, 1, 2, 0, 6, 5, 4, 3, 1, 2, 0, 3, 4, 7, 6, 5,
      4, 3, 2, 0]]

@[expose] def innerSteps : ℕ → List FrameStep
  | 0 =>
    [.comm 1 3 11, .comm 4 5 17, .comm 6 7 21, .comm 10 11 49, .comm 9 12 75, .comm 3 4 15,
      .comm 2 14 29, .comm 5 6 19, .comm 7 8 237, .comm 16 17 233, .comm 15 18 226, .comm 13 19 196,
      .comm 2 3 13, .comm 1 21 26, .comm 14 16 47, .comm 22 23 90, .comm 0 2 9, .comm 25 14 39,
      .comm 9 10 43, .comm 26 27 98, .comm 24 28 176, .comm 20 29 23, .comm 2 30 8, .comm 21 12 77,
      .comm 25 9 38, .comm 33 23 99, .comm 32 34 171, .comm 1 14 27, .comm 21 10 45, .comm 36 37 89,
      .comm 26 18 223, .comm 38 39 182, .comm 35 40 10, .comm 13 39 188, .comm 42 29 12,
      .comm 4 16 33, .comm 22 44 74, .comm 45 28 168, .comm 22 12 91, .comm 47 39 180,
      .comm 46 48 14, .comm 9 37 73, .comm 33 12 100, .comm 50 51 169, .comm 24 39 181,
      .comm 52 53 16, .comm 9 15 57, .comm 55 51 159, .comm 56 53 32, .comm 4 57 18, .comm 52 40 20,
      .comm 46 53 22]
  | 1 =>
    [.square 0 3 40, .square 2 3 24, .comm 8 6 83, .comm 9 4 38, .comm 7 10 0, .square 0 1 37,
      .comm 12 10 1, .comm 8 5 225, .perm 0 [233, 49], .comm 14 15 41, .comm 12 16 79, .perm 4 [48,
      46], .comm 12 18 81, .comm 19 3 167, .comm 20 4 191, .comm 17 21 222, .comm 14 22 2,
      .perm 6 [3, 43], .comm 12 24 23, .comm 8 25 3, .comm 12 3 132, .comm 27 14 160,
      .comm 7 19 119, .comm 29 4 154, .comm 28 30 4, .comm 12 9 43, .comm 32 16 5, .comm 25 4 66,
      .comm 7 2 85, .perm 5 [22, 213], .comm 35 36 69, .comm 34 37 6, .comm 19 35 7,
      .comm 19 14 193, .comm 27 40 89, .comm 34 16 107, .comm 41 42 8, .comm 14 20 122,
      .comm 44 42 13, .comm 7 45 10, .comm 25 10 11, .comm 7 47 12, .comm 28 10 192, .comm 49 30 53,
      .comm 17 50 14, .comm 9 42 16, .comm 7 40 170, .square 1 2 26, .comm 54 3 64, .comm 7 55 103,
      .comm 56 4 140, .comm 53 57 39, .comm 34 58 18, .comm 29 16 153, .comm 60 49 54,
      .comm 19 61 20, .comm 12 55 96, .comm 63 37 22]
  | 2 =>
    [.perm 0 [199, 78, 94], .perm 1 [178, 78, 94], .square 5 6 32, .perm 4 [28, 42, 152],
      .comm 7 8 60, .perm 2 [54, 131, 171], .comm 9 10 0, .perm 4 [42, 28, 152], .comm 11 12 53,
      .perm 3 [141, 132, 184], .comm 13 14 186, .comm 7 3 156, .comm 16 10 103, .comm 17 14 47,
      .perm 0 [78, 94, 199], .comm 18 19 22, .comm 20 2 145, .comm 21 12 96, .comm 7 10 24,
      .perm 0 [94, 78, 199], .comm 23 24 56, .comm 25 2 172, .comm 26 15 21, .comm 27 10 85,
      .comm 28 19 9, .comm 29 2 114, .comm 22 30 183, .comm 15 31 1, .comm 25 8 86, .comm 33 2 188,
      .comm 34 12 154, .perm 3 [184, 132, 141], .comm 35 36 42, .comm 26 37 133, .comm 38 10 72,
      .comm 26 19 211, .comm 40 15 46, .comm 41 21 174, .comm 42 10 128, .comm 43 14 19,
      .comm 39 44 41, .comm 37 45 2, .comm 17 12 50, .comm 47 14 104, .comm 23 48 136, .comm 49 2 3,
      .comm 25 3 173, .comm 51 2 229, .comm 52 15 106, .comm 53 10 40, .comm 54 37 4,
      .comm 52 36 109, .comm 56 8 132, .strip 57 3, .perm 58 [141, 184], .comm 29 59 162,
      .comm 54 36 160, .comm 61 2 31, .comm 60 62 187, .comm 31 63 5, .comm 51 6 6, .comm 28 37 138,
      .comm 66 2 7, .comm 52 19 239, .comm 68 14 203, .comm 56 6 90, .comm 70 10 148,
      .comm 37 71 184, .comm 72 67 193, .comm 69 73 8, .comm 26 48 80, .comm 75 10 10,
      .comm 18 13 112, .comm 77 2 12, .comm 69 10 164, .comm 37 79 121, .comm 80 30 198,
      .comm 15 81 14, .comm 70 30 16, .comm 26 47 199, .comm 84 15 18, .comm 15 21 59,
      .comm 86 10 125, .comm 37 87 168, .comm 28 70 171, .perm 2 [171, 54, 131], .strip 89 90,
      .perm 91 [131, 54], .comm 88 92 43, .comm 39 93 20]
  | _ =>
    [.perm 0 [171, 104, 129, 218], .perm 3 [34, 104, 129, 218], .square 5 6 149, .perm 0 [218, 104,
      129, 171], .perm 1 [137, 104, 129, 171], .square 8 9 134, .comm 10 6 157, .comm 11 2 239,
      .perm 4 [195, 105, 106, 147], .comm 7 13 238, .comm 14 2 151, .comm 12 15 197, .comm 7 16 71,
      .comm 7 9 225, .comm 18 12 88, .perm 2 [143, 51, 98, 197], .comm 19 20 198, .comm 17 21 223,
      .perm 2 [98, 51, 143, 197], .comm 10 23 36, .comm 7 24 122, .comm 25 15 220, .comm 26 20 139,
      .perm 4 [147, 105, 106, 195], .comm 27 28 224, .comm 22 29 0, .comm 7 12 199, .comm 31 20 237,
      .comm 18 4 179, .comm 33 20 49, .comm 34 28 186, .comm 32 35 154, .comm 24 5 148,
      .comm 37 20 5, .comm 10 4 203, .comm 39 6 214, .comm 40 15 106, .strip 41 4, .perm 42 [147,
      105, 195], .comm 38 43 158, .comm 36 44 1, .comm 10 7 13, .comm 21 35 14, .comm 46 47 2,
      .comm 15 0 118, .comm 25 49 3, .comm 12 33 173, .comm 14 0 105, .perm 4 [105, 106, 147, 195],
      .strip 52 53, .perm 54 [195, 106, 147], .comm 51 55 33, .comm 12 52 218, .strip 57 3,
      .perm 58 [34, 104, 129], .comm 56 59 4, .comm 46 16 181, .comm 61 35 6, .comm 14 32 7,
      .comm 39 14 141, .comm 11 64 8, .comm 51 38 164, .comm 7 66 10, .comm 49 23 12,
      .comm 10 15 19, .comm 69 32 233, .comm 7 38 161, .comm 71 43 230, .comm 70 72 16,
      .comm 31 35 18, .comm 11 27 20, .comm 18 16 69, .perm 3 [129, 34, 104, 218], .comm 12 77 209,
      .comm 78 28 96, .comm 76 79 22]

@[expose] def innerExt : ℕ → ℕ × ℕ × ℕ × ℕ × List ℕ
  | 0 => (0, 2, 0, 9, [])
  | 1 => (0, 3, 49, 63, [233])
  | 2 => (0, 0, 94, 86, [78, 199])
  | _ => (0, 1, 171, 178, [104, 129, 218])

@[expose] def innerFacts (k : ℕ) : List (List ℕ) :=
  (innerWords k).map fun ω => (classListE8RepPos k).map (wordPos Tag.E8.rootCertificate ω)

@[expose] def innerCheck (k : ℕ) : Bool :=
  simpleRootsB (runSteps (innerFacts k) (innerSteps k)) &&
    match innerExt k with
    | (i, g, b, p, L) =>
      ((innerFacts k)[i]?).any (fun L₀ => pairwiseCommB L₀ && L₀.isPerm (b :: L)) &&
        sumB g b p && L.all (commB g)

theorem innerCheck_zero : innerCheck 0 = true := by decide +kernel
theorem innerCheck_one : innerCheck 1 = true := by decide +kernel
theorem innerCheck_two : innerCheck 2 = true := by decide +kernel
theorem innerCheck_three : innerCheck 3 = true := by decide +kernel

variable {K : Type} [Field K]

section Small


private lemma e8FrameProd_mem_adjointGroup (L : List ℕ) :
    e8FrameProd K L ∈ adjointGroup .E8 K := by
  rw [e8FrameProd]
  have h : (L.map fun k => pinnedX .E8 K (Tag.E8.rootCertificate.root k) 1) =
      (L.map Tag.E8.rootCertificate.root).map (fun σ => pinnedX .E8 K σ 1) := by
    rw [List.map_map]
    rfl
  rw [h]
  exact list_prod_map_pinnedX_mem_adjointGroup _

private lemma innerRepsE8_0 :
    (⟨pinnedX .E8 K (highRoot .E8) 1, pinnedX_mem_adjointGroup _ _⟩ :
        adjointGroup .E8 K) =
      ⟨e8FrameProd K (classListE8RepPos 0), e8FrameProd_mem_adjointGroup _⟩ := by
  obtain ⟨h0, _, _, _⟩ := classListE8RepPos_map_root
  apply Subtype.ext
  simp only [e8FrameProd]
  rw [show (classListE8RepPos 0).map
        (fun k => pinnedX .E8 K (Tag.E8.rootCertificate.root k) 1) =
      ((classListE8RepPos 0).map Tag.E8.rootCertificate.root).map
        (fun σ => pinnedX .E8 K σ 1) from by
    rw [List.map_map]
    rfl, h0]
  simp only [List.map_singleton, List.prod_singleton]

private lemma innerRepsE8_1 :
    (⟨(oddDerivE8YFrame.map fun σ => pinnedX .E8 K σ 1).prod,
        list_prod_map_pinnedX_mem_adjointGroup _⟩ : adjointGroup .E8 K) =
      ⟨e8FrameProd K (classListE8RepPos 1), e8FrameProd_mem_adjointGroup _⟩ := by
  obtain ⟨_, h1, _, _⟩ := classListE8RepPos_map_root
  apply Subtype.ext
  simp only [e8FrameProd]
  rw [show (classListE8RepPos 1).map
        (fun k => pinnedX .E8 K (Tag.E8.rootCertificate.root k) 1) =
      ((classListE8RepPos 1).map Tag.E8.rootCertificate.root).map
        (fun σ => pinnedX .E8 K σ 1) from by
    rw [List.map_map]
    rfl, h1]

private lemma innerRepsE8_2 :
    (⟨(oddDerivE8ZFrame.map fun σ => pinnedX .E8 K σ 1).prod,
        list_prod_map_pinnedX_mem_adjointGroup _⟩ : adjointGroup .E8 K) =
      ⟨e8FrameProd K (classListE8RepPos 2), e8FrameProd_mem_adjointGroup _⟩ := by
  obtain ⟨_, _, h2, _⟩ := classListE8RepPos_map_root
  apply Subtype.ext
  simp only [e8FrameProd]
  rw [show (classListE8RepPos 2).map
        (fun k => pinnedX .E8 K (Tag.E8.rootCertificate.root k) 1) =
      ((classListE8RepPos 2).map Tag.E8.rootCertificate.root).map
        (fun σ => pinnedX .E8 K σ 1) from by
    rw [List.map_map]
    rfl, h2]

private lemma innerRepsE8_3 :
    (⟨(oddDerivE8UFrame.map fun σ => pinnedX .E8 K σ 1).prod,
        list_prod_map_pinnedX_mem_adjointGroup _⟩ : adjointGroup .E8 K) =
      ⟨e8FrameProd K (classListE8RepPos 3), e8FrameProd_mem_adjointGroup _⟩ := by
  obtain ⟨_, _, _, h3⟩ := classListE8RepPos_map_root
  apply Subtype.ext
  simp only [e8FrameProd]
  rw [show (classListE8RepPos 3).map
        (fun k => pinnedX .E8 K (Tag.E8.rootCertificate.root k) 1) =
      ((classListE8RepPos 3).map Tag.E8.rootCertificate.root).map
        (fun σ => pinnedX .E8 K σ 1) from by
    rw [List.map_map]
    rfl, h3]

end Small

section Main

private theorem inner_generic [CharP K 2] {k : ℕ} (hcheck : innerCheck k = true)
    (hlen : (innerWords k).length + 1 ≤ 11)
    (hbound : ∀ j ∈ classListE8RepPos k, j < Tag.E8.rootCertificate.roots.length)
    {μ : K} (hμ : ∀ c : K, c ≠ 0 → ∃ n : ℕ, μ ^ n = c) :
    ∃ L : List (ModGL .E8 K), L.length ≤ 11 ∧ (∀ s ∈ L, s ∈ adjointGroup .E8 K) ∧
      adjointGroup .E8 K ≤ Subgroup.closure
        {y | ∃ s ∈ L, y = s * e8FrameProd K (classListE8RepPos k) * s⁻¹} := by
  obtain ⟨i, g, b, p, L', hExt⟩ : ∃ i g b p L', innerExt k = (i, g, b, p, L') :=
    ⟨_, _, _, _, _, rfl⟩
  simp only [innerCheck] at hcheck
  rw [hExt] at hcheck
  simp only [Bool.and_eq_true] at hcheck
  rcases hcheck with ⟨hsimple, ⟨hany, hsum⟩, hcomm⟩
  obtain ⟨L₀, hL₀mem, hL₀prop⟩ := (Option.any_eq_true _ _).1 hany
  simp only [Bool.and_eq_true] at hL₀prop
  obtain ⟨hpair, hperm⟩ := hL₀prop
  have hL₀mem_get : (innerFacts k)[i]? = some L₀ := hL₀mem
  have hmap : (innerFacts k)[i]? =
      ((innerWords k)[i]?).map (fun ω =>
        (classListE8RepPos k).map (wordPos Tag.E8.rootCertificate ω)) := by
    simp only [innerFacts, List.getElem?_map]
  rw [hmap] at hL₀mem
  obtain ⟨ω_i, hω_i, hL₀eq⟩ : ∃ ω_i ∈ (innerWords k)[i]?,
      (classListE8RepPos k).map (wordPos Tag.E8.rootCertificate ω_i) = L₀ := by
    cases hω : (innerWords k)[i]? with
    | none =>
      rw [hω] at hL₀mem
      simp at hL₀mem
    | some ω =>
      rw [hω] at hL₀mem
      simp only [Option.map_some, Option.some.injEq] at hL₀mem
      exact ⟨ω, rfl, hL₀mem⟩
  have hL₀mem' : L₀ ∈ innerFacts k := List.mem_of_getElem? hL₀mem_get
  let r : ModGL .E8 K := e8FrameProd K (classListE8RepPos k)
  let s : ModGL .E8 K := pinnedX .E8 K (Tag.E8.rootCertificate.root g) μ *
    classListE8WordElt .E8 K ω_i
  let L : List (ModGL .E8 K) :=
    (innerWords k).map (classListE8WordElt .E8 K) ++ [s]
  let H : Subgroup (ModGL .E8 K) := Subgroup.closure
    {y | ∃ s ∈ L, y = s * r * s⁻¹}
  have hF : ∀ L₀' ∈ innerFacts k, e8FrameProd K L₀' ∈ H := by
    intro L₀' hL₀'
    obtain ⟨ω', hω', rfl⟩ := List.mem_map.1 hL₀'
    have hs : classListE8WordElt .E8 K ω' ∈ L := by
      simp only [L, List.mem_append, List.mem_map]
      exact Or.inl ⟨ω', hω', rfl⟩
    have hconj : classListE8WordElt .E8 K ω' * r * (classListE8WordElt .E8 K ω')⁻¹ ∈ H :=
      Subgroup.subset_closure ⟨_, hs, rfl⟩
    simp only [r, e8FrameProd] at hconj
    rw [classListE8_wordElt_conj_posProd ω' hbound] at hconj
    simpa only [e8FrameProd] using hconj
  refine ⟨L, ?_, ?_, ?_⟩
  · simp only [L, List.length_append, List.length_map, List.length_singleton]
    exact hlen
  · intro s' hs'
    simp only [L, List.mem_append, List.mem_map, List.mem_singleton] at hs'
    rcases hs' with ⟨ω, hω, rfl⟩ | rfl
    · exact classListE8WordElt_mem_adjointGroup ω
    · exact mul_mem (pinnedX_mem_adjointGroup _ _) (classListE8WordElt_mem_adjointGroup ω_i)
  · change adjointGroup .E8 K ≤ H
    have hmem : ∀ L₀' ∈ runSteps (innerFacts k) (innerSteps k), e8FrameProd K L₀' ∈ H :=
      e8FrameProd_mem_of_mem_runSteps hF (innerSteps k)
    have h1 : ∀ α, IsRoot .E8 α → pinnedX .E8 K α 1 ∈ H :=
      pinnedX_one_mem_of_simpleRootsB hmem hsimple
    have hperm' : L₀.Perm (b :: L') := List.isPerm_iff.1 hperm
    have h2prod : e8FrameProd K (b :: L') ∈ H := by
      rw [← e8FrameProd_perm hpair hperm']
      exact hF L₀ hL₀mem'
    have hs_mem : s ∈ L := by
      simp only [L, List.mem_append, List.mem_singleton]
      exact Or.inr trivial
    have hconj : s * r * s⁻¹ ∈ H := Subgroup.subset_closure ⟨s, hs_mem, rfl⟩
    have heq : s * r * s⁻¹ =
        pinnedX .E8 K (Tag.E8.rootCertificate.root g) μ *
          e8FrameProd K (b :: L') *
          (pinnedX .E8 K (Tag.E8.rootCertificate.root g) μ)⁻¹ := by
      simp only [s]
      calc (pinnedX .E8 K (Tag.E8.rootCertificate.root g) μ *
            classListE8WordElt .E8 K ω_i) * r *
            (pinnedX .E8 K (Tag.E8.rootCertificate.root g) μ *
              classListE8WordElt .E8 K ω_i)⁻¹
          = pinnedX .E8 K (Tag.E8.rootCertificate.root g) μ *
              (classListE8WordElt .E8 K ω_i * r *
                (classListE8WordElt .E8 K ω_i)⁻¹) *
              (pinnedX .E8 K (Tag.E8.rootCertificate.root g) μ)⁻¹ := by group
        _ = pinnedX .E8 K (Tag.E8.rootCertificate.root g) μ *
              e8FrameProd K ((classListE8RepPos k).map
                (wordPos Tag.E8.rootCertificate ω_i)) *
              (pinnedX .E8 K (Tag.E8.rootCertificate.root g) μ)⁻¹ := by
            rw [show classListE8WordElt .E8 K ω_i * r *
                (classListE8WordElt .E8 K ω_i)⁻¹ =
                e8FrameProd K ((classListE8RepPos k).map
                  (wordPos Tag.E8.rootCertificate ω_i)) from by
              simp only [r, e8FrameProd]
              exact classListE8_wordElt_conj_posProd ω_i hbound]
        _ = pinnedX .E8 K (Tag.E8.rootCertificate.root g) μ *
              e8FrameProd K L₀ *
              (pinnedX .E8 K (Tag.E8.rootCertificate.root g) μ)⁻¹ := by
            rw [hL₀eq]
        _ = pinnedX .E8 K (Tag.E8.rootCertificate.root g) μ *
              e8FrameProd K (b :: L') *
              (pinnedX .E8 K (Tag.E8.rootCertificate.root g) μ)⁻¹ := by
            rw [e8FrameProd_perm hpair hperm']
    have h2 : pinnedX .E8 K (Tag.E8.rootCertificate.root g) μ *
        e8FrameProd K (b :: L') *
        (pinnedX .E8 K (Tag.E8.rootCertificate.root g) μ)⁻¹ ∈ H := by
      simpa only [heq] using hconj
    have hμH : pinnedX .E8 K (Tag.E8.rootCertificate.root p) μ ∈ H :=
      pinnedX_mem_of_conj_e8FrameProd hsum hcomm μ h2prod h2
    have hp : p < Tag.E8.rootCertificate.roots.length := by
      have h := hsum
      simp only [sumB, Bool.and_eq_true, decide_eq_true_eq] at h
      omega
    exact adjointGroup_le_of_pinnedX_generator h1 hμ
      (RootCertificate.isRoot_root Tag.E8.rootCertificate_check p hp) hμH

theorem adjointGroup_le_closure_conj_rep [CharP K 2] {k : ℕ} (hk : k < 4) {μ : K}
    (hμ : ∀ c : K, c ≠ 0 → ∃ n : ℕ, μ ^ n = c) :
    ∃ L : List (ModGL .E8 K), L.length ≤ 11 ∧ (∀ s ∈ L, s ∈ adjointGroup .E8 K) ∧
      adjointGroup .E8 K ≤ Subgroup.closure
        {y | ∃ s ∈ L, y = s * e8FrameProd K (classListE8RepPos k) * s⁻¹} := by
  interval_cases k
  · exact inner_generic innerCheck_zero (by decide +kernel) (by decide +kernel) hμ
  · exact inner_generic innerCheck_one (by decide +kernel) (by decide +kernel) hμ
  · exact inner_generic innerCheck_two (by decide +kernel) (by decide +kernel) hμ
  · exact inner_generic innerCheck_three (by decide +kernel) (by decide +kernel) hμ

end Main

section Top

theorem exists_closure_conj_eq_top [Finite K] [CharP K 2] {t : adjointGroup .E8 K}
    (ht : t ^ 2 = 1) (ht1 : t ≠ 1) :
    ∃ L : List (adjointGroup .E8 K), L.length ≤ 11 ∧
      Subgroup.closure {y | ∃ s ∈ L, y = s * t * s⁻¹} = ⊤ := by
  obtain ⟨g, hg⟩ := classListE8_exists_conj_mem_innerRepsE8 ht ht1
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hμ : ∀ c : K, c ≠ 0 → ∃ n : ℕ, (u : K) ^ n = c := by
    intro c hc
    let uc : Kˣ := Units.mk0 c hc
    have huc : uc ∈ Subgroup.zpowers u := hu uc
    obtain ⟨n, hn⟩ := (mem_powers_iff_mem_zpowers (x := u) (y := uc)).2 huc
    refine ⟨n, ?_⟩
    have h := congrArg (fun v : Kˣ => (v : K)) hn
    simpa [uc, Units.val_pow_eq_pow_val] using h
  simp only [innerRepsE8, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with hg0 | hg1 | hg2 | hg3
  · have hg0' : g * t * g⁻¹ =
        (⟨e8FrameProd K (classListE8RepPos 0), e8FrameProd_mem_adjointGroup _⟩ :
          adjointGroup .E8 K) := by
      rw [hg0]
      exact innerRepsE8_0
    obtain ⟨L₀, hlen₀, hmem₀, hgen₀⟩ :=
      adjointGroup_le_closure_conj_rep (k := 0) (by decide) (μ := (u : K)) hμ
    let L' : List (adjointGroup .E8 K) :=
      L₀.attach.map (fun ⟨s, hs⟩ => ⟨s * g, mul_mem (hmem₀ s hs) g.2⟩)
    refine ⟨L', ?_, ?_⟩
    · simp only [L', List.length_map, List.length_attach]
      exact hlen₀
    · let S : Set (adjointGroup .E8 K) := {y | ∃ s ∈ L', y = s * t * s⁻¹}
      have hmap : (Subgroup.closure S).map (adjointGroup .E8 K).subtype =
          adjointGroup .E8 K := by
        rw [MonoidHom.map_closure]
        apply le_antisymm
        · rw [Subgroup.closure_le]
          rintro _ ⟨y, hy, rfl⟩
          obtain ⟨s, hs, rfl⟩ := hy
          rw [show (adjointGroup .E8 K).subtype (s * t * s⁻¹) =
              (s : ModGL .E8 K) * (t : ModGL .E8 K) * (s : ModGL .E8 K)⁻¹ from by
            change ((s * t * s⁻¹ : adjointGroup .E8 K) : ModGL .E8 K) =
              (s : ModGL .E8 K) * (t : ModGL .E8 K) * (s : ModGL .E8 K)⁻¹
            rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]]
          exact mul_mem (mul_mem s.2 t.2) (inv_mem s.2)
        · refine le_trans hgen₀ ?_
          rw [Subgroup.closure_le]
          rintro y ⟨s₀, hs₀, rfl⟩
          have hs' : (⟨s₀ * g, mul_mem (hmem₀ s₀ hs₀) g.2⟩ : adjointGroup .E8 K) ∈ L' := by
            simp only [L', List.mem_map]
            exact ⟨⟨s₀, hs₀⟩, List.mem_attach _ _, rfl⟩
          have hconj : (⟨s₀ * g, mul_mem (hmem₀ s₀ hs₀) g.2⟩ : adjointGroup .E8 K) * t *
              (⟨s₀ * g, mul_mem (hmem₀ s₀ hs₀) g.2⟩ : adjointGroup .E8 K)⁻¹ ∈ S :=
            ⟨_, hs', rfl⟩
          have himg : ((⟨s₀ * g, mul_mem (hmem₀ s₀ hs₀) g.2⟩ : adjointGroup .E8 K) * t *
              (⟨s₀ * g, mul_mem (hmem₀ s₀ hs₀) g.2⟩ : adjointGroup .E8 K)⁻¹ :
                ModGL .E8 K) = s₀ * e8FrameProd K (classListE8RepPos 0) * s₀⁻¹ := by
            simp only [Subgroup.coe_inv]
            rw [show (s₀ * g) * (t : ModGL .E8 K) * (s₀ * g)⁻¹ =
                s₀ * ((g : ModGL .E8 K) * (t : ModGL .E8 K) * (g : ModGL .E8 K)⁻¹) *
                  s₀⁻¹ from by group,
              show (g : ModGL .E8 K) * (t : ModGL .E8 K) * (g : ModGL .E8 K)⁻¹ =
                e8FrameProd K (classListE8RepPos 0) from by
                simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
                  congrArg (fun x : adjointGroup .E8 K => (x : ModGL .E8 K)) hg0']
          exact Subgroup.subset_closure ⟨_, hconj, himg⟩
      rw [eq_top_iff]
      intro x hx
      have hxmap : (x : ModGL .E8 K) ∈
          (Subgroup.closure S).map (adjointGroup .E8 K).subtype := by
        rw [hmap]
        exact x.2
      obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.1 hxmap
      have hyx : y = x := (adjointGroup .E8 K).subtype_injective hxy
      rw [hyx] at hy
      exact hy
  · have hg1' : g * t * g⁻¹ =
        (⟨e8FrameProd K (classListE8RepPos 1), e8FrameProd_mem_adjointGroup _⟩ :
          adjointGroup .E8 K) := by
      rw [hg1]
      exact innerRepsE8_1
    obtain ⟨L₀, hlen₀, hmem₀, hgen₀⟩ :=
      adjointGroup_le_closure_conj_rep (k := 1) (by decide) (μ := (u : K)) hμ
    let L' : List (adjointGroup .E8 K) :=
      L₀.attach.map (fun ⟨s, hs⟩ => ⟨s * g, mul_mem (hmem₀ s hs) g.2⟩)
    refine ⟨L', ?_, ?_⟩
    · simp only [L', List.length_map, List.length_attach]
      exact hlen₀
    · let S : Set (adjointGroup .E8 K) := {y | ∃ s ∈ L', y = s * t * s⁻¹}
      have hmap : (Subgroup.closure S).map (adjointGroup .E8 K).subtype =
          adjointGroup .E8 K := by
        rw [MonoidHom.map_closure]
        apply le_antisymm
        · rw [Subgroup.closure_le]
          rintro _ ⟨y, hy, rfl⟩
          obtain ⟨s, hs, rfl⟩ := hy
          rw [show (adjointGroup .E8 K).subtype (s * t * s⁻¹) =
              (s : ModGL .E8 K) * (t : ModGL .E8 K) * (s : ModGL .E8 K)⁻¹ from by
            change ((s * t * s⁻¹ : adjointGroup .E8 K) : ModGL .E8 K) =
              (s : ModGL .E8 K) * (t : ModGL .E8 K) * (s : ModGL .E8 K)⁻¹
            rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]]
          exact mul_mem (mul_mem s.2 t.2) (inv_mem s.2)
        · refine le_trans hgen₀ ?_
          rw [Subgroup.closure_le]
          rintro y ⟨s₀, hs₀, rfl⟩
          have hs' : (⟨s₀ * g, mul_mem (hmem₀ s₀ hs₀) g.2⟩ : adjointGroup .E8 K) ∈ L' := by
            simp only [L', List.mem_map]
            exact ⟨⟨s₀, hs₀⟩, List.mem_attach _ _, rfl⟩
          have hconj : (⟨s₀ * g, mul_mem (hmem₀ s₀ hs₀) g.2⟩ : adjointGroup .E8 K) * t *
              (⟨s₀ * g, mul_mem (hmem₀ s₀ hs₀) g.2⟩ : adjointGroup .E8 K)⁻¹ ∈ S :=
            ⟨_, hs', rfl⟩
          have himg : ((⟨s₀ * g, mul_mem (hmem₀ s₀ hs₀) g.2⟩ : adjointGroup .E8 K) * t *
              (⟨s₀ * g, mul_mem (hmem₀ s₀ hs₀) g.2⟩ : adjointGroup .E8 K)⁻¹ :
                ModGL .E8 K) = s₀ * e8FrameProd K (classListE8RepPos 1) * s₀⁻¹ := by
            simp only [Subgroup.coe_inv]
            rw [show (s₀ * g) * (t : ModGL .E8 K) * (s₀ * g)⁻¹ =
                s₀ * ((g : ModGL .E8 K) * (t : ModGL .E8 K) * (g : ModGL .E8 K)⁻¹) *
                  s₀⁻¹ from by group,
              show (g : ModGL .E8 K) * (t : ModGL .E8 K) * (g : ModGL .E8 K)⁻¹ =
                e8FrameProd K (classListE8RepPos 1) from by
                simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
                  congrArg (fun x : adjointGroup .E8 K => (x : ModGL .E8 K)) hg1']
          exact Subgroup.subset_closure ⟨_, hconj, himg⟩
      rw [eq_top_iff]
      intro x hx
      have hxmap : (x : ModGL .E8 K) ∈
          (Subgroup.closure S).map (adjointGroup .E8 K).subtype := by
        rw [hmap]
        exact x.2
      obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.1 hxmap
      have hyx : y = x := (adjointGroup .E8 K).subtype_injective hxy
      rw [hyx] at hy
      exact hy
  · have hg2' : g * t * g⁻¹ =
        (⟨e8FrameProd K (classListE8RepPos 2), e8FrameProd_mem_adjointGroup _⟩ :
          adjointGroup .E8 K) := by
      rw [hg2]
      exact innerRepsE8_2
    obtain ⟨L₀, hlen₀, hmem₀, hgen₀⟩ :=
      adjointGroup_le_closure_conj_rep (k := 2) (by decide) (μ := (u : K)) hμ
    let L' : List (adjointGroup .E8 K) :=
      L₀.attach.map (fun ⟨s, hs⟩ => ⟨s * g, mul_mem (hmem₀ s hs) g.2⟩)
    refine ⟨L', ?_, ?_⟩
    · simp only [L', List.length_map, List.length_attach]
      exact hlen₀
    · let S : Set (adjointGroup .E8 K) := {y | ∃ s ∈ L', y = s * t * s⁻¹}
      have hmap : (Subgroup.closure S).map (adjointGroup .E8 K).subtype =
          adjointGroup .E8 K := by
        rw [MonoidHom.map_closure]
        apply le_antisymm
        · rw [Subgroup.closure_le]
          rintro _ ⟨y, hy, rfl⟩
          obtain ⟨s, hs, rfl⟩ := hy
          rw [show (adjointGroup .E8 K).subtype (s * t * s⁻¹) =
              (s : ModGL .E8 K) * (t : ModGL .E8 K) * (s : ModGL .E8 K)⁻¹ from by
            change ((s * t * s⁻¹ : adjointGroup .E8 K) : ModGL .E8 K) =
              (s : ModGL .E8 K) * (t : ModGL .E8 K) * (s : ModGL .E8 K)⁻¹
            rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]]
          exact mul_mem (mul_mem s.2 t.2) (inv_mem s.2)
        · refine le_trans hgen₀ ?_
          rw [Subgroup.closure_le]
          rintro y ⟨s₀, hs₀, rfl⟩
          have hs' : (⟨s₀ * g, mul_mem (hmem₀ s₀ hs₀) g.2⟩ : adjointGroup .E8 K) ∈ L' := by
            simp only [L', List.mem_map]
            exact ⟨⟨s₀, hs₀⟩, List.mem_attach _ _, rfl⟩
          have hconj : (⟨s₀ * g, mul_mem (hmem₀ s₀ hs₀) g.2⟩ : adjointGroup .E8 K) * t *
              (⟨s₀ * g, mul_mem (hmem₀ s₀ hs₀) g.2⟩ : adjointGroup .E8 K)⁻¹ ∈ S :=
            ⟨_, hs', rfl⟩
          have himg : ((⟨s₀ * g, mul_mem (hmem₀ s₀ hs₀) g.2⟩ : adjointGroup .E8 K) * t *
              (⟨s₀ * g, mul_mem (hmem₀ s₀ hs₀) g.2⟩ : adjointGroup .E8 K)⁻¹ :
                ModGL .E8 K) = s₀ * e8FrameProd K (classListE8RepPos 2) * s₀⁻¹ := by
            simp only [Subgroup.coe_inv]
            rw [show (s₀ * g) * (t : ModGL .E8 K) * (s₀ * g)⁻¹ =
                s₀ * ((g : ModGL .E8 K) * (t : ModGL .E8 K) * (g : ModGL .E8 K)⁻¹) *
                  s₀⁻¹ from by group,
              show (g : ModGL .E8 K) * (t : ModGL .E8 K) * (g : ModGL .E8 K)⁻¹ =
                e8FrameProd K (classListE8RepPos 2) from by
                simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
                  congrArg (fun x : adjointGroup .E8 K => (x : ModGL .E8 K)) hg2']
          exact Subgroup.subset_closure ⟨_, hconj, himg⟩
      rw [eq_top_iff]
      intro x hx
      have hxmap : (x : ModGL .E8 K) ∈
          (Subgroup.closure S).map (adjointGroup .E8 K).subtype := by
        rw [hmap]
        exact x.2
      obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.1 hxmap
      have hyx : y = x := (adjointGroup .E8 K).subtype_injective hxy
      rw [hyx] at hy
      exact hy
  · have hg3' : g * t * g⁻¹ =
        (⟨e8FrameProd K (classListE8RepPos 3), e8FrameProd_mem_adjointGroup _⟩ :
          adjointGroup .E8 K) := by
      rw [hg3]
      exact innerRepsE8_3
    obtain ⟨L₀, hlen₀, hmem₀, hgen₀⟩ :=
      adjointGroup_le_closure_conj_rep (k := 3) (by decide) (μ := (u : K)) hμ
    let L' : List (adjointGroup .E8 K) :=
      L₀.attach.map (fun ⟨s, hs⟩ => ⟨s * g, mul_mem (hmem₀ s hs) g.2⟩)
    refine ⟨L', ?_, ?_⟩
    · simp only [L', List.length_map, List.length_attach]
      exact hlen₀
    · let S : Set (adjointGroup .E8 K) := {y | ∃ s ∈ L', y = s * t * s⁻¹}
      have hmap : (Subgroup.closure S).map (adjointGroup .E8 K).subtype =
          adjointGroup .E8 K := by
        rw [MonoidHom.map_closure]
        apply le_antisymm
        · rw [Subgroup.closure_le]
          rintro _ ⟨y, hy, rfl⟩
          obtain ⟨s, hs, rfl⟩ := hy
          rw [show (adjointGroup .E8 K).subtype (s * t * s⁻¹) =
              (s : ModGL .E8 K) * (t : ModGL .E8 K) * (s : ModGL .E8 K)⁻¹ from by
            change ((s * t * s⁻¹ : adjointGroup .E8 K) : ModGL .E8 K) =
              (s : ModGL .E8 K) * (t : ModGL .E8 K) * (s : ModGL .E8 K)⁻¹
            rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]]
          exact mul_mem (mul_mem s.2 t.2) (inv_mem s.2)
        · refine le_trans hgen₀ ?_
          rw [Subgroup.closure_le]
          rintro y ⟨s₀, hs₀, rfl⟩
          have hs' : (⟨s₀ * g, mul_mem (hmem₀ s₀ hs₀) g.2⟩ : adjointGroup .E8 K) ∈ L' := by
            simp only [L', List.mem_map]
            exact ⟨⟨s₀, hs₀⟩, List.mem_attach _ _, rfl⟩
          have hconj : (⟨s₀ * g, mul_mem (hmem₀ s₀ hs₀) g.2⟩ : adjointGroup .E8 K) * t *
              (⟨s₀ * g, mul_mem (hmem₀ s₀ hs₀) g.2⟩ : adjointGroup .E8 K)⁻¹ ∈ S :=
            ⟨_, hs', rfl⟩
          have himg : ((⟨s₀ * g, mul_mem (hmem₀ s₀ hs₀) g.2⟩ : adjointGroup .E8 K) * t *
              (⟨s₀ * g, mul_mem (hmem₀ s₀ hs₀) g.2⟩ : adjointGroup .E8 K)⁻¹ :
                ModGL .E8 K) = s₀ * e8FrameProd K (classListE8RepPos 3) * s₀⁻¹ := by
            simp only [Subgroup.coe_inv]
            rw [show (s₀ * g) * (t : ModGL .E8 K) * (s₀ * g)⁻¹ =
                s₀ * ((g : ModGL .E8 K) * (t : ModGL .E8 K) * (g : ModGL .E8 K)⁻¹) *
                  s₀⁻¹ from by group,
              show (g : ModGL .E8 K) * (t : ModGL .E8 K) * (g : ModGL .E8 K)⁻¹ =
                e8FrameProd K (classListE8RepPos 3) from by
                simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
                  congrArg (fun x : adjointGroup .E8 K => (x : ModGL .E8 K)) hg3']
          exact Subgroup.subset_closure ⟨_, hconj, himg⟩
      rw [eq_top_iff]
      intro x hx
      have hxmap : (x : ModGL .E8 K) ∈
          (Subgroup.closure S).map (adjointGroup .E8 K).subtype := by
        rw [hmap]
        exact x.2
      obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.1 hxmap
      have hyx : y = x := (adjointGroup .E8 K).subtype_injective hxy
      rw [hyx] at hy
      exact hy

end Top

end CFSG.LocalAnalysis.WeakClosure81.GS03E8
