module

public import CFSG.Milestones.ASVolI.F48.Small.U42LetterData
public import CFSG.Quasithin.Recognition.CertPermList
public import Certificates.Data.U42F431Perm
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.ASVolI

open CFSG.Quasithin

@[expose] def burnsideF48s_sp43c_word (m : ℕ) (hm : 0 < m) (al s : String) :
    List (Fin m × Bool) :=
  s.toList.map fun c => (⟨al.toList.idxOf c.toLower % m, Nat.mod_lt _ hm⟩, c.isLower)

@[expose] def burnsideF48s_sp43c_invW {m : ℕ} (w : List (Fin m × Bool)) : List (Fin m × Bool) :=
  (w.map fun l => (l.1, !l.2)).reverse

@[expose] def burnsideF48s_sp43c_letL {m : ℕ} (gl gli : Fin m → List ℕ) (l : Fin m × Bool) :
    List ℕ :=
  cond l.2 (gl l.1) (gli l.1)

@[expose] def burnsideF48s_sp43c_evL {m : ℕ} (gl gli : Fin m → List ℕ)
    (w : List (Fin m × Bool)) : List ℕ :=
  w.foldl (fun acc l => compL acc (burnsideF48s_sp43c_letL gl gli l)) (List.range 45)

@[expose] def burnsideF48s_sp43c_LS : List (List ℕ) := [
    [43, 1, 36, 3, 29, 20, 34, 18, 8, 26, 11, 23, 13, 16, 33, 17, 30, 21, 4, 12, 6, 15, 22, 28, 10,
      35, 39, 41, 40, 0, 38, 42, 37, 44, 2, 32, 5, 31, 19, 9, 24, 27, 25, 7, 14],
    [41, 2, 36, 6, 27, 20, 34, 22, 5, 21, 26, 14, 31, 10, 16, 28, 11, 25, 4, 17, 8, 33, 29, 12, 24,
      19, 13, 18, 32, 7, 30, 23, 15, 9, 3, 35, 1, 39, 44, 40, 37, 43, 38, 0, 42],
    [2, 1, 0, 8, 6, 7, 4, 5, 3, 14, 12, 13, 10, 11, 9, 15, 23, 17, 20, 24, 18, 21, 22, 16, 19, 25,
      33, 27, 30, 34, 28, 31, 32, 26, 29, 35, 43, 37, 40, 44, 38, 41, 42, 36, 39],
    [43, 21, 12, 33, 0, 31, 23, 41, 9, 8, 19, 42, 20, 25, 44, 17, 10, 15, 4, 28, 30, 1, 22, 36, 6,
      38, 39, 7, 16, 27, 2, 34, 11, 3, 35, 5, 24, 13, 37, 26, 32, 29, 40, 18, 14]]

@[expose] def burnsideF48s_sp43c_LSi : List (List ℕ) := [
    [29, 1, 34, 3, 18, 36, 20, 43, 8, 39, 24, 10, 19, 12, 44, 21, 13, 15, 7, 38, 5, 17, 22, 11, 40,
      42, 9, 41, 23, 4, 16, 37, 35, 14, 6, 25, 2, 32, 30, 26, 28, 27, 31, 0, 33],
    [43, 36, 1, 34, 18, 8, 3, 29, 20, 33, 13, 16, 23, 26, 11, 32, 14, 19, 27, 25, 5, 9, 7, 31, 24,
      17, 10, 4, 15, 22, 30, 12, 28, 21, 6, 35, 2, 40, 42, 37, 39, 0, 44, 41, 38],
    [2, 1, 0, 8, 6, 7, 4, 5, 3, 14, 12, 13, 10, 11, 9, 15, 23, 17, 20, 24, 18, 21, 22, 16, 19, 25,
      33, 27, 30, 34, 28, 31, 32, 26, 29, 35, 43, 37, 40, 44, 38, 41, 42, 36, 39],
    [4, 21, 30, 33, 18, 35, 24, 27, 9, 8, 16, 32, 2, 37, 44, 17, 28, 15, 43, 10, 12, 1, 22, 6, 36,
      13, 39, 29, 19, 41, 20, 5, 40, 3, 31, 34, 23, 38, 25, 26, 42, 7, 11, 0, 14]]

@[expose] def burnsideF48s_sp43c_L (i : ℕ) : List ℕ := burnsideF48s_sp43c_LS.getD i []

@[expose] def burnsideF48s_sp43c_Li (i : ℕ) : List ℕ := burnsideF48s_sp43c_LSi.getD i []

@[expose] def burnsideF48s_sp43c_gl4 (i : Fin 4) : List ℕ := burnsideF48s_sp43c_L i

@[expose] def burnsideF48s_sp43c_gli4 (i : Fin 4) : List ℕ := burnsideF48s_sp43c_Li i

@[expose] def burnsideF48s_sp43c_evL4 (w : List (Fin 4 × Bool)) : List ℕ :=
  burnsideF48s_sp43c_evL burnsideF48s_sp43c_gl4 burnsideF48s_sp43c_gli4 w

@[expose] def burnsideF48s_sp43c_glB (k : Fin 2) : List ℕ := burnsideF48s_sp43c_L k

@[expose] def burnsideF48s_sp43c_gliB (k : Fin 2) : List ℕ := burnsideF48s_sp43c_Li k

@[expose] def burnsideF48s_sp43c_glP1 (k : Fin 3) : List ℕ := burnsideF48s_sp43c_L k

@[expose] def burnsideF48s_sp43c_gliP1 (k : Fin 3) : List ℕ := burnsideF48s_sp43c_Li k

@[expose] def burnsideF48s_sp43c_glP2 (k : Fin 3) : List ℕ := burnsideF48s_sp43c_L (![0, 1, 3] k)

@[expose] def burnsideF48s_sp43c_gliP2 (k : Fin 3) : List ℕ :=
  burnsideF48s_sp43c_Li (![0, 1, 3] k)

@[expose] def burnsideF48s_sp43c_glS (k : Fin 2) : List ℕ :=
  ![burnsideF48s_sp43c_L 1, compL (burnsideF48s_sp43c_L 0) (burnsideF48s_sp43c_L 0)] k

@[expose] def burnsideF48s_sp43c_gliS (k : Fin 2) : List ℕ :=
  ![burnsideF48s_sp43c_Li 1, compL (burnsideF48s_sp43c_Li 0) (burnsideF48s_sp43c_Li 0)] k

@[expose] def burnsideF48s_sp43c_Bw : List String := [
    "", "a", "A", "b", "B", "aa", "ab", "aB", "AA", "Ab", "AB", "ba", "bA", "Ba", "BA", "aaa",
    "aab", "aaB", "aba", "abA", "aBa", "aBA", "AAb", "AAB", "Aba", "AbA", "ABa", "ABA", "baa",
    "bab", "baB", "bAA", "bAb", "bAB", "Baa", "Bab", "BaB", "BAA", "BAb", "BAB", "aaab", "aaaB",
    "aaba", "aabA", "aaBa", "abaa", "abab", "abaB", "abAb", "abAB", "aBaa", "aBaB", "aBAA", "aBAB",
    "AAbA", "AABa", "AABA", "Abaa", "AbAA", "AbAb", "ABab", "ABaB", "ABAA", "ABAb", "ABAB", "baaa",
    "baab", "baaB", "baba", "babA", "baBA", "bAba", "bAbA", "bABA", "Baaa", "Baba", "BaBA", "BAAB",
    "BAba", "BABA", "aaabA", "aaaBa", "aabaa", "aabab", "aabAb", "aabAB", "aaBaa", "aaBaB", "abaab",
    "abaaB", "ababa", "ababA", "abaBA", "abAba", "abAbA", "abABA", "aBaaa", "aBaBA", "aBAAB",
    "aBABA", "AAbAA", "AAbAb", "AABab", "AABaB", "AABAA", "Abaaa", "Abaab", "AbAbA", "ABaba",
    "ABaBA", "ABAAB", "ABAba", "baaab", "baaaB", "baabA", "babab", "babaB", "babAb", "babAB",
    "baBAA", "baBAB", "bABAb", "bABAB", "Baaab", "BaaaB", "Babab", "BabaB", "BaBAB", "BAABa",
    "BAbaa", "BABAb", "BABAB", "aaabAb", "aaaBaB", "aabaab", "aabaaB", "aabAba", "aabABA", "abaabA",
    "ababab", "ababaB", "ababAb", "ababAB", "abaBAA", "abaBAB", "abABAb", "abABAB", "aBaaab",
    "aBaaaB", "aBAABa", "aBABAb", "aBABAB", "AABAAB", "Abaaab", "AbaabA", "ABabab", "ABabaB",
    "ABaBAB", "baabAB", "baBAAB", "aabABAb", "abaBAAB"]

@[expose] def burnsideF48s_sp43c_Sw : List String := [
    "", "b", "B", "c", "C", "bc", "bC", "Bc", "BC", "cb", "cB", "Cb", "CB", "bcb", "bcB", "bCb",
    "bCB", "Bcb", "BcB", "BCb", "BCB", "cbc", "cbC", "cBc", "cBC", "Cbc", "CbC", "CBc", "CBC",
    "bcbc", "bcbC", "bcBc", "bcBC", "bCbc", "bCbC", "bCBc", "bCBC", "Bcbc", "BcbC", "BcBc", "BcBC",
    "BCbc", "BCbC", "BCBc", "BCBC", "cbcb", "cbCb", "cBcB", "cBCB", "Cbcb", "CbCb", "CBcB", "CBCB",
    "bcbcb", "bcbCb", "bCbcb", "bCbCb", "cbcbc", "cbcbC", "cbCbc", "cbCbC", "cBcBc", "cBcBC",
    "cBCBc", "cBCBC", "Cbcbc", "CbcbC", "CbCbc", "CbCbC", "CBcBc", "CBcBC", "CBCBc", "CBCBC",
    "bcbcbc", "bcbcbC", "bcbCbc", "bcbCbC", "bCbcbc", "bCbcbC", "bCbCbc", "bCbCbC"]

@[expose] def burnsideF48s_sp43c_P1w : List String := [
    "", "a", "A", "b", "B", "p", "aa", "ab", "aB", "ap", "AA", "Ab", "AB", "Ap", "ba", "bA", "bp",
    "Ba", "BA", "Bp", "pb", "pB", "aaa", "aab", "aaB", "aap", "aba", "abA", "abp", "aBa", "aBA",
    "aBp", "apb", "apB", "AAb", "AAB", "AAp", "Aba", "AbA", "Abp", "ABa", "ABA", "ABp", "Apb",
    "ApB", "baa", "bab", "baB", "bap", "bAA", "bAb", "bAB", "bAp", "bpb", "bpB", "Baa", "Bab",
    "BaB", "Bap", "BAA", "BAb", "BAB", "BAp", "Bpb", "BpB", "pba", "pbA", "pbp", "pBa", "pBA",
    "pBp", "aaab", "aaaB", "aaap", "aaba", "aabA", "aabp", "aaBa", "aaBp", "aapb", "aapB", "abaa",
    "abab", "abaB", "abap", "abAb", "abAB", "abAp", "abpb", "abpB", "aBaa", "aBaB", "aBap", "aBAA",
    "aBAB", "aBAp", "aBpb", "aBpB", "apba", "apbA", "apbp", "apBa", "apBA", "apBp", "AAbA", "AAbp",
    "AABa", "AABA", "AABp", "AApb", "AApB", "Abaa", "Abap", "AbAA", "AbAb", "AbAp", "Abpb", "AbpB",
    "ABab", "ABaB", "ABap", "ABAA", "ABAb", "ABAB", "ABAp", "ABpb", "ABpB", "Apba", "ApbA", "Apbp",
    "ApBa", "ApBA", "ApBp", "baaa", "baab", "baaB", "baap", "baba", "babA", "babp", "baBA", "baBp",
    "bapb", "bapB", "bAAp", "bAba", "bAbA", "bAbp", "bABA", "bABp", "bApb", "bApB", "bpba", "bpbA",
    "bpbp", "bpBa", "bpBp", "Baaa", "Baap", "Baba", "Babp", "BaBA", "BaBp", "Bapb", "BapB", "BAAB",
    "BAAp", "BAba", "BAbp", "BABA", "BABp", "BApb", "BApB", "BpbA", "Bpbp", "BpBa", "BpBA", "BpBp",
    "pbaa", "pbaB", "pbap", "pbAA", "pbAb", "pbAB", "pbAp", "pbpB", "pBaa", "pBab", "pBaB", "pBap",
    "pBAA", "pBAb", "pBAp", "pBpb", "aaabA", "aaabp", "aaaBa", "aaaBp", "aaapb", "aaapB", "aabaa",
    "aabab", "aabap", "aabAb", "aabAB", "aabAp", "aabpb", "aabpB", "aaBaa", "aaBaB", "aaBap",
    "aaBpb", "aaBpB", "aapba", "aapbA", "aapbp", "aapBa", "aapBp", "abaab", "abaaB", "abaap",
    "ababa", "ababA", "ababp", "abaBA", "abaBp", "abapB", "abAba", "abAbA", "abAbp", "abABA",
    "abABp", "abApb", "abApB", "abpba", "abpbA", "abpbp", "abpBa", "abpBp", "aBaaa", "aBaap",
    "aBaBA", "aBaBp", "aBapb", "aBapB", "aBAAB", "aBAAp", "aBABA", "aBABp", "aBApb", "aBApB",
    "aBpbA", "aBpbp", "aBpBa", "aBpBA", "aBpBp", "apbaa", "apbaB", "apbAb", "apbAB", "apbAp",
    "apbpB", "apBaa", "apBaB", "apBap", "apBAA", "apBAp", "apBpb", "AAbAA", "AAbAb", "AAbAp",
    "AAbpb", "AAbpB", "AABab", "AABaB", "AABap", "AABAA", "AABAp", "AABpb", "AABpB", "AApbA",
    "AApbp", "AApBa", "AApBA", "AApBp", "Abaaa", "Abaab", "Abaap", "Abapb", "AbapB", "AbAAp",
    "AbAbA", "AbApB", "Abpba", "Abpbp", "AbpBa", "AbpBp", "ABaba", "ABabp", "ABaBA", "ABaBp",
    "ABapb", "ABapB", "ABAAB", "ABAAp", "ABAba", "ABAbp", "ABABp", "ABApb", "ABpbp", "ABpBa",
    "ABpBp", "Apbaa", "Apbap", "ApbAA", "ApbAp", "ApbpB", "ApBab", "ApBaB", "ApBap", "ApBAA",
    "ApBAb", "ApBpb", "baaab", "baaaB", "baaap", "baabA", "baabp", "baaBp", "baapb", "baapB",
    "babab", "babaB", "babap", "babAb", "babAB", "babAp", "baBAA", "baBAB", "baBAp", "baBpb",
    "baBpB", "bapbA", "bapBa", "bapBA", "bapBp", "bAApB", "bAbap", "bAbAp", "bABAb", "bABAB",
    "bABAp", "bABpB", "bApba", "bApbp", "bApBa", "bApBA", "bApBp", "bpbaB", "bpbap", "bpbAB",
    "bpbAp", "bpBaa", "bpBab", "bpBap", "bpBpb", "Baaab", "BaaaB", "Baaap", "Baapb", "Babab",
    "BabaB", "Babap", "BaBAB", "BaBAp", "BapbA", "BapBA", "BapBp", "BAABa", "BAABp", "BAApb",
    "BAApB", "BAbaa", "BAbap", "BAbpb", "BAbpB", "BABAb", "BABAB", "BABAp", "BApba", "BApbA",
    "BApbp", "BApBa", "BpbAA", "BpbAB", "BpbAp", "BpBab", "BpBap", "BpBAp", "pbaaa", "pbaab",
    "pbaap", "pbaBA", "pbaBp", "pbAAp", "pbAba", "pbABA", "pbABp", "pbApb", "pbApB", "pbpBa",
    "pbpBp", "pBaaa", "pBaap", "pBaba", "pBabp", "pBaBA", "pBapb", "pBapB", "pBAAB", "pBAAp",
    "pBAba", "pBAbp", "pBpbA", "pBpbp", "aaabAb", "aaabAp", "aaabpb", "aaabpB", "aaaBaB", "aaaBap",
    "aaaBpb", "aaaBpB", "aaapbA", "aaapbp", "aaapBa", "aaapBp", "aabaab", "aabaaB", "aabaap",
    "aababp", "aabapB", "aabAba", "aabAbp", "aabABA", "aabABp", "aabApb", "aabApB", "aabpbA",
    "aabpbp", "aabpBp", "aaBaap", "aaBpbA", "aaBpbp", "aaBpBA", "aaBpBp", "aapbaa", "aapbAb",
    "aapbAB", "aapbAp", "aapbpB", "aapBaa", "aapBap", "aapBpb", "abaabA", "abaabp", "abaaBp",
    "abaapb", "abaapB", "ababAb", "ababAB", "ababAp", "abaBAA", "abaBAB", "abaBAp", "abapBa",
    "abapBA", "abAbap", "abAbAp", "abABAb", "abABAB", "abABAp", "abABpB", "abApba", "abApbp",
    "abApBa", "abApBA", "abApBp", "abpbap", "abpbAB", "abpbAp", "abpBaa", "abpBap", "aBaaab",
    "aBaaaB", "aBaaap", "aBaBAp", "aBapbA", "aBapBA", "aBapBp", "aBAABa", "aBAABp", "aBAApb",
    "aBAApB", "aBABAb", "aBABAB", "aBABAp", "aBApba", "aBApbA", "aBApbp", "aBApBa", "aBpbAA",
    "aBpbAB", "aBpbAp", "aBpBap", "aBpBAp", "apbaab", "apbaBA", "apbAba", "apbABA", "apbABp",
    "apbApb", "apbApB", "apbpBa", "apBaaa", "apBaap", "apBaBA", "apBapb", "apBapB", "apBAAB",
    "apBAAp", "apBpbA", "AAbAAp", "AAbpbp", "AAbpBp", "AABabp", "AABapb", "AABAAB", "AABAAp",
    "AABpbp", "AABpBp", "AApbAA", "AApbAp", "AApbpB", "AApBab", "AApBap", "AApBAA", "AApBpb",
    "Abaaab", "Abaaap", "AbaabA", "Abaabp", "Abaapb", "AbaapB", "AbapBa", "AbpbaB", "Abpbap",
    "AbpBaa", "AbpBab", "AbpBap", "ABabab", "ABabaB", "ABabap", "ABaBAB", "ABapBA", "ABapBp",
    "ABAABp", "ABAApB", "ABAbap", "ABApba", "ABpBab", "ABpBap", "Apbaaa", "Apbaab", "Apbaap",
    "ApbAAp", "ApbpBa", "ApBaba", "ApBabp", "ApBapB", "ApBAAB", "ApBAba", "baaabp", "baaapb",
    "baabAB", "baapbp", "babAbp", "babABp", "babApb", "babApB", "baBAAB", "baBAAp", "baBABp",
    "baBApB", "baBpbA", "bapbAB", "bAbapB", "bABAbp", "bABpBa", "bABpBp", "bApbpB", "bApBaB",
    "bpbaBA", "bpbaBp", "bpbApb", "bpBaap", "bpBapB", "BaaaBp", "BaaapB", "BaBABp", "BaBApb",
    "BapbAb", "BAApBp", "BAbaap", "BAbapb", "BAbpBa", "BApBab", "BpbAAp", "BpbApb", "BpBapB",
    "pbaaab", "pbaBAA", "pbaBAB", "pbpBaa", "pBaaaB", "pBaBAB", "pBAbaa", "pBpbAA", "aaabpbp",
    "aaaBpBp", "aaapbAp", "aaapBap", "aabaabp", "aabABAb", "aabABpB", "aabApba", "aabApbp",
    "aabpbAB", "aabpbAp", "aaBpbAA", "aaBpbAp", "aaBpBAp", "abaBAAB", "abABAbp", "abpBapB",
    "aBaaaBp", "apBaaaB", "apBpbAA"]

@[expose] def burnsideF48s_sp43c_P2w : List String := [
    "", "a", "A", "b", "B", "q", "Q", "aa", "ab", "aB", "aq", "aQ", "AA", "Ab", "AB", "Aq", "AQ",
    "ba", "bA", "bq", "bQ", "Ba", "BA", "Bq", "BQ", "qa", "qA", "qb", "qB", "qq", "Qa", "QA", "Qb",
    "QB", "aab", "aaB", "aba", "abA", "abq", "abQ", "aBa", "aBA", "aBq", "aBQ", "aqa", "aqA", "aqb",
    "aqB", "aQa", "aQA", "aQb", "aQB", "AAb", "AAB", "Aba", "AbA", "Abq", "AbQ", "ABa", "ABA",
    "ABq", "ABQ", "Aqa", "AqA", "Aqb", "AqB", "AQa", "AQA", "AQb", "AQB", "baa", "bab", "baB",
    "baq", "baQ", "bAA", "bAb", "bAB", "bAq", "bAQ", "bqa", "bqA", "bqb", "bqB", "bqq", "bQa",
    "bQA", "bQb", "bQB", "Baa", "Bab", "BaB", "Baq", "BaQ", "BAA", "BAb", "BAB", "BAq", "BAQ",
    "Bqa", "BqA", "Bqb", "BqB", "Bqq", "BQa", "BQA", "BQb", "BQB", "qab", "qaB", "qAb", "qAB",
    "qba", "qbA", "qbq", "qbQ", "qBa", "qBA", "qBq", "qBQ", "qqb", "qqB", "Qab", "QaB", "QAb",
    "QAB", "Qba", "QbA", "Qbq", "QbQ", "QBa", "QBA", "QBq", "QBQ", "aaba", "aabA", "aabq", "aabQ",
    "aaBa", "aaBq", "aaBQ", "abaa", "abab", "abaB", "abaq", "abaQ", "abAB", "abAq", "abAQ", "abqa",
    "abqA", "abqb", "abqB", "abqq", "abQa", "abQA", "abQb", "abQB", "aBaa", "aBaB", "aBaq", "aBaQ",
    "aBAA", "aBAB", "aBAq", "aBqa", "aBqA", "aBqB", "aBqq", "aBQa", "aBQA", "aBQb", "aBQB", "aqab",
    "aqaB", "aqAb", "aqAB", "aqba", "aqbA", "aqbq", "aqbQ", "aqBa", "aqBA", "aqBq", "aQab", "aQaB",
    "aQAb", "aQAB", "aQba", "aQbA", "aQbq", "aQbQ", "aQBa", "aQBA", "aQBq", "aQBQ", "AAbA", "AAbq",
    "AAbQ", "AABa", "AABA", "AABq", "AABQ", "Abaa", "AbaQ", "AbAA", "AbAq", "Abqa", "AbqA", "Abqb",
    "Abqq", "AbQa", "AbQA", "AbQb", "ABab", "ABaq", "ABaQ", "ABAA", "ABAb", "ABAB", "ABAQ", "ABqa",
    "ABqA", "ABqb", "ABqB", "ABqq", "ABQa", "ABQA", "ABQb", "Aqab", "AqaB", "AqAb", "AqAB", "Aqba",
    "AqbA", "Aqbq", "AqbQ", "AqBa", "AqBA", "AqBq", "AqBQ", "AQab", "AQaB", "AQAb", "AQAB", "AQba",
    "AQbA", "AQbQ", "AQBa", "AQBA", "AQBq", "baab", "baba", "babA", "babq", "babQ", "baBA", "baBq",
    "baqa", "baqA", "baQA", "baQB", "bAbq", "bAqa", "bAqb", "bAQa", "bAQA", "bAQb", "bqab", "bqaB",
    "bqAb", "bqAB", "bqba", "bqbA", "bqbQ", "bqBA", "bqqb", "bqqB", "bQab", "bQaB", "bQAb", "bQba",
    "bQbA", "bQbq", "bQbQ", "bQBa", "bQBA", "BaBQ", "Baqa", "BaqA", "BaQA", "BaQB", "BAAB", "BABA",
    "BABq", "BABQ", "BAqa", "BAqb", "BAQa", "BAQA", "BqaB", "BqAb", "BqAB", "Bqba", "BqbA", "BqBA",
    "BqBq", "BqBQ", "Bqqb", "BqqB", "BQab", "BQaB", "BQAb", "BQba", "BQBa", "BQBA", "qaba", "qabq",
    "qabQ", "qaBA", "qaBq", "qaBQ", "qbab", "qbaB", "qbaq", "qbAb", "qbAQ", "qbqq", "qbQb", "qBaa",
    "qBaq", "qBAA", "qBAB", "qBAQ", "qBqq", "qqbA", "qqbq", "qqbQ", "qqBa", "qqBq", "qqBQ", "QAba",
    "QAbq", "QAbQ", "QABq", "QABQ", "Qbaa", "Qbab", "Qbaq", "QbAA", "QbAQ", "Qbqq", "QBaB", "QBaq",
    "QBAB", "QBAQ", "QBqB", "QBqq", "aabaa", "aabab", "aabaq", "aabAB", "aabAq", "aabqa", "aabqq",
    "aabQa", "aabQb", "aabQB", "aaBaa", "aaBqa", "aaBqB", "aaBqq", "aaBQa", "ababa", "ababA",
    "ababq", "ababQ", "abaBA", "abaqa", "abaqA", "abaQA", "abAqa", "abAqb", "abAQA", "abqab",
    "abqAb", "abqAB", "abqba", "abqbA", "abqBA", "abqqb", "abqqB", "abQaB", "abQba", "abQbA",
    "abQbq", "abQbQ", "abQBa", "abQBA", "aBaBQ", "aBaqa", "aBaqA", "aBaQA", "aBAAB", "aBABA",
    "aBABq", "aBABQ", "aBqaB", "aBqAB", "aBqBA", "aBqBQ", "aBqqb", "aBqqB", "aBQab", "aBQaB",
    "aBQAb", "aBQba", "aBQBa", "aBQBA", "aqaba", "aqabQ", "aqaBA", "aqaBq", "aqaBQ", "aqbab",
    "aqbaB", "aqbAb", "aqbAQ", "aqbqq", "aqbQb", "aqBaa", "aqBAB", "aqBAQ", "aQbaa", "aQbab",
    "aQbAQ", "aQbqq", "aQBAB", "aQBAQ", "aQBqB", "aQBqq", "AAbAA", "AAbqA", "AAbqq", "AAbQb",
    "AABab", "AABaQ", "AABAA", "AABAQ", "AABqA", "AABqb", "AABqB", "AABqq", "AABQA", "Abqab",
    "AbqAb", "Abqba", "AbqbA", "AbqbQ", "Abqqb", "AbqqB", "AbQAb", "AbQba", "AbQbA", "AbQbq",
    "ABaqa", "ABaQA", "ABaQB", "ABABq", "ABABQ", "ABAQA", "ABqAb", "ABqba", "ABqbA", "ABqBA",
    "ABqBq", "ABqBQ", "ABqqb", "ABqqB", "ABQab", "ABQaB", "ABQba", "Aqbab", "AqbaB", "Aqbqq",
    "AqBAB", "AqBqq", "AQAba", "AQAbq", "AQAbQ", "AQABq", "AQbab", "AQBAB", "AQBqB", "baabA",
    "baabQ", "babab", "babaB", "babAq", "babAQ", "babqa", "babqA", "babqB", "babQa", "babQA",
    "babQb", "baqab", "baqaB", "baQBA", "bAbqb", "bAqab", "bAqba", "bAqbA", "bAqbQ", "bAQAb",
    "bAQAB", "bqaba", "bqabq", "bqbAb", "bqBAA", "bqBAQ", "bqqbq", "bqqbQ", "bqqBq", "bQbaa",
    "bQbab", "bQbAA", "bQbAQ", "bQbqq", "bQBAB", "Baqab", "BaqaB", "BaQBa", "BaQBA", "BAABq",
    "BABAb", "BABAB", "BABqA", "BABQa", "BABQA", "BABQb", "BAqba", "BAQAb", "BAQAB", "Bqbab",
    "BqBAA", "BqBqq", "BqqbQ", "BqqBq", "BqqBQ", "BQbaa", "BQbaq", "qaBqB", "qbaba", "qbAbq",
    "qbQba", "qbQbq", "qbQbQ", "qBAAB", "qBABA", "qBABq", "qqbqq", "qqbQb", "qqBqq", "QAbQb",
    "Qbaab", "Qbaba", "QbabQ", "QBaBQ", "QBABA", "QBqBA", "QBqBQ", "aabAqb", "aabqab", "aabqqb",
    "aabQba", "aaBqqB", "ababab", "ababaB", "ababqA", "ababqB", "ababQa", "ababQb", "abaqab",
    "abaqaB", "abAqab", "abAqbQ", "abAQAb", "abAQAB", "abqaba", "abqbAb", "abqqbq", "abqqBq",
    "abQbaa", "abQbab", "abQbAQ", "abQbqq", "abQBAB", "aBaqaB", "aBAABq", "aBABqA", "aBABQa",
    "aBABQA", "aBqqbQ", "aBqqBQ", "aqbQbq", "aqBABq", "aQbaab", "aQbaba", "aQbabQ", "aQBABA",
    "aQBqBA", "aQBqBQ", "AAbqqb", "AABaQB", "AABqBA", "AABqqB", "Abqabq", "AbqbAb", "AbqqBq",
    "ABaqab", "ABaqaB", "ABABqA", "ABABQa", "ABAQAb", "ABAQAB", "ABqbab", "ABqBAA", "ABqBqq",
    "ABqqbQ", "Aqbaba", "AqBABA", "AqBABq", "AQBqBQ", "babAqa", "babAQA", "baqaba", "bAQAbQ",
    "bqbAbq", "bqqbqq", "bQbaba", "bQbabQ", "BAqbaB", "BqqBqq", "qaBqBQ", "qbabab", "qBAABq",
    "QbaabQ"]

@[expose] def burnsideF48s_sp43c_wordB (s : String) : List (Fin 2 × Bool) :=
  burnsideF48s_sp43c_word 2 (by norm_num) "ab" s

@[expose] def burnsideF48s_sp43c_wordS (s : String) : List (Fin 2 × Bool) :=
  burnsideF48s_sp43c_word 2 (by norm_num) "bc" s

@[expose] def burnsideF48s_sp43c_wordP1 (s : String) : List (Fin 3 × Bool) :=
  burnsideF48s_sp43c_word 3 (by norm_num) "abp" s

@[expose] def burnsideF48s_sp43c_wordP2 (s : String) : List (Fin 3 × Bool) :=
  burnsideF48s_sp43c_word 3 (by norm_num) "abq" s

@[expose] def burnsideF48s_sp43c_BW (_ : Unit := ()) : List (List (Fin 2 × Bool)) :=
  burnsideF48s_sp43c_Bw.map burnsideF48s_sp43c_wordB

@[expose] def burnsideF48s_sp43c_SW (_ : Unit := ()) : List (List (Fin 2 × Bool)) :=
  burnsideF48s_sp43c_Sw.map burnsideF48s_sp43c_wordS

@[expose] def burnsideF48s_sp43c_P1W (_ : Unit := ()) : List (List (Fin 3 × Bool)) :=
  burnsideF48s_sp43c_P1w.map burnsideF48s_sp43c_wordP1

@[expose] def burnsideF48s_sp43c_P2W (_ : Unit := ()) : List (List (Fin 3 × Bool)) :=
  burnsideF48s_sp43c_P2w.map burnsideF48s_sp43c_wordP2

@[expose] def burnsideF48s_sp43c_SL (_ : Unit := ()) : List (List ℕ) :=
  (burnsideF48s_sp43c_SW ()).map (burnsideF48s_sp43c_evL burnsideF48s_sp43c_glS
    burnsideF48s_sp43c_gliS)

@[expose] def burnsideF48s_sp43c_P1L (_ : Unit := ()) : List (List ℕ) :=
  (burnsideF48s_sp43c_P1W ()).map (burnsideF48s_sp43c_evL burnsideF48s_sp43c_glP1
    burnsideF48s_sp43c_gliP1)

@[expose] def burnsideF48s_sp43c_P2L (_ : Unit := ()) : List (List ℕ) :=
  (burnsideF48s_sp43c_P2W ()).map (burnsideF48s_sp43c_evL burnsideF48s_sp43c_glP2
    burnsideF48s_sp43c_gliP2)

@[expose] def burnsideF48s_sp43c_Bl (i : ℕ) : List ℕ :=
  burnsideF48s_sp43c_evL burnsideF48s_sp43c_glB burnsideF48s_sp43c_gliB
    (burnsideF48s_sp43c_wordB (burnsideF48s_sp43c_Bw.getD i ""))

@[expose] def burnsideF48s_sp43c_groupB {m : ℕ} (gl gli : Fin m → List ℕ)
    (W : List (List (Fin m × Bool))) (n : ℕ) : Bool :=
  let L := W.map (burnsideF48s_sp43c_evL gl gli)
  decide (W.length = n) && decide ([] ∈ W) && decide L.Nodup &&
    L.all fun x => (List.finRange m).all fun k => L.contains (compL x (gl k))

@[expose] def burnsideF48s_sp43c_Dw : List (List (Fin 4 × Bool)) := [
    [],
    [(2, true)],
    [(3, true)],
    [(2, true), (3, true)],
    [(3, true), (2, true)],
    [(2, true), (3, true), (2, true)],
    [(3, true), (2, true), (3, true)],
    [(2, true), (3, true), (2, true), (3, true)]]

@[expose] def burnsideF48s_sp43c_Dl (j : ℕ) : List ℕ :=
  burnsideF48s_sp43c_evL4 (burnsideF48s_sp43c_Dw.getD j [])

@[expose] def burnsideF48s_sp43c_Dli (j : ℕ) : List ℕ :=
  burnsideF48s_sp43c_evL4 (burnsideF48s_sp43c_invW (burnsideF48s_sp43c_Dw.getD j []))

@[expose] def burnsideF48s_sp43c_trP : List ℕ := [0, 3, 4]

@[expose] def burnsideF48s_sp43c_trQ : List ℕ := [0, 1, 2]

@[expose] def burnsideF48s_sp43c_witP : List (ℕ × ℕ) := [
    (0, 0), (0, 1), (0, 2), (1, 0), (2, 0), (0, 5), (2, 29), (1, 101), (0, 8), (2, 87), (1, 39),
    (1, 1), (1, 2), (2, 1), (2, 2), (0, 15), (1, 59), (2, 72), (2, 68), (2, 69), (1, 72),
    (1, 136), (1, 67), (2, 51), (2, 135), (2, 67), (1, 69), (1, 79), (1, 5), (0, 29), (2, 101),
    (1, 8), (0, 87), (2, 39), (2, 5), (1, 29), (0, 101), (2, 8), (1, 87), (0, 39), (2, 159),
    (1, 158), (1, 94), (1, 107), (2, 32), (2, 83), (0, 46), (1, 160), (0, 133), (1, 132), (1, 32),
    (0, 59), (1, 84), (0, 53), (1, 36), (2, 89), (2, 97), (2, 103), (2, 36), (0, 51), (2, 133),
    (0, 132), (1, 83), (2, 161), (0, 64), (1, 15), (2, 59), (0, 72), (0, 68), (0, 69), (2, 136),
    (0, 135), (0, 67), (2, 79), (2, 15), (1, 68), (0, 136), (1, 51), (1, 135), (0, 79), (2, 148),
    (1, 153), (1, 48), (0, 83), (0, 103), (2, 124), (2, 71), (0, 32), (1, 97), (0, 94), (0, 90),
    (0, 91), (1, 145), (0, 109), (0, 89), (1, 93), (1, 71), (0, 107), (2, 112), (0, 99), (1, 76),
    (0, 36), (1, 112), (0, 84), (2, 61), (2, 76), (1, 124), (0, 97), (2, 109), (0, 93), (2, 94),
    (2, 156), (0, 159), (2, 158), (2, 107), (1, 46), (2, 160), (1, 133), (2, 132), (2, 84),
    (1, 53), (0, 161), (1, 64), (1, 159), (0, 158), (2, 46), (0, 160), (2, 53), (1, 89), (1, 103),
    (1, 161), (2, 64), (0, 61), (0, 48), (2, 153), (0, 71), (0, 76), (2, 126), (1, 61), (2, 90),
    (1, 90), (2, 145), (1, 109), (1, 121), (2, 91), (0, 156), (2, 99), (2, 48), (0, 153),
    (2, 121), (2, 93), (1, 156), (1, 148), (0, 148), (1, 126), (1, 91), (0, 145), (1, 99),
    (0, 124), (0, 112), (0, 126), (0, 121)]

@[expose] def burnsideF48s_sp43c_witQ : List (ℕ × ℕ) := [
    (0, 0), (1, 0), (2, 0), (0, 48), (0, 76), (2, 15), (1, 48), (1, 76), (1, 15), (2, 48),
    (2, 76), (1, 78), (2, 24), (1, 60), (2, 26), (0, 15), (2, 101), (2, 89), (2, 45), (0, 24),
    (2, 50), (0, 26), (1, 101), (1, 89), (0, 78), (1, 42), (0, 60), (1, 44), (2, 58), (1, 154),
    (1, 26), (1, 54), (2, 137), (2, 19), (2, 62), (1, 70), (1, 4), (1, 56), (2, 78), (2, 154),
    (0, 101), (0, 89), (0, 45), (1, 24), (0, 50), (0, 58), (2, 113), (2, 44), (0, 137), (0, 19),
    (0, 62), (2, 41), (2, 21), (0, 154), (0, 42), (2, 60), (0, 44), (1, 49), (0, 54), (1, 65),
    (0, 70), (0, 4), (0, 56), (1, 45), (1, 113), (0, 107), (2, 110), (2, 74), (2, 123), (0, 149),
    (0, 21), (0, 3), (1, 40), (1, 107), (0, 87), (2, 87), (0, 143), (1, 139), (0, 49), (1, 123),
    (2, 42), (1, 50), (1, 58), (0, 113), (1, 137), (1, 19), (1, 62), (0, 41), (0, 110), (0, 74),
    (0, 123), (1, 149), (1, 21), (1, 3), (2, 3), (2, 71), (1, 87), (1, 143), (2, 117), (2, 149),
    (2, 54), (0, 65), (2, 70), (2, 4), (2, 56), (2, 107), (1, 120), (0, 40), (1, 61), (2, 143),
    (0, 139), (2, 49), (0, 112), (0, 90), (1, 69), (2, 140), (2, 88), (0, 118), (0, 127), (2, 61),
    (0, 117), (1, 112), (1, 90), (0, 83), (0, 124), (2, 83), (2, 124), (0, 120), (2, 53), (1, 71),
    (1, 140), (1, 88), (2, 65), (1, 41), (1, 110), (1, 74), (2, 40), (0, 71), (2, 90), (0, 140),
    (0, 88), (1, 118), (1, 127), (0, 61), (1, 117), (2, 160), (2, 69), (1, 83), (1, 124), (0, 53),
    (2, 118), (2, 127), (2, 139), (2, 112), (0, 69), (1, 53), (1, 161), (2, 120), (1, 160),
    (2, 161), (0, 160), (0, 161)]

@[expose] def burnsideF48s_sp43c_decP : List (List (ℕ × ℕ × ℕ)) := [
    [(1, 0, 0), (1, 3, 0), (1, 4, 0)],
    [(0, 0, 0), (1, 3, 139), (1, 4, 140)],
    [(4, 0, 0), (4, 21, 53), (4, 19, 132)],
    [(5, 0, 0), (5, 32, 159), (5, 69, 126)],
    [(2, 0, 0), (4, 21, 56), (4, 19, 128)],
    [(3, 0, 0), (5, 32, 100), (5, 69, 12)],
    [(7, 0, 0), (7, 113, 158), (7, 123, 159)],
    [(6, 0, 0), (7, 113, 81), (7, 123, 80)]]

@[expose] def burnsideF48s_sp43c_decQ : List (List (ℕ × ℕ × ℕ)) := [
    [(2, 0, 0), (2, 1, 0), (2, 2, 0)],
    [(3, 0, 0), (3, 1, 0), (3, 2, 0)],
    [(0, 0, 15), (2, 2, 2), (2, 1, 8)],
    [(1, 0, 15), (3, 2, 2), (3, 1, 8)],
    [(6, 0, 0), (6, 3, 65), (6, 4, 74)],
    [(7, 0, 0), (7, 121, 124), (7, 126, 112)],
    [(4, 0, 15), (6, 4, 34), (6, 3, 11)],
    [(5, 0, 15), (7, 126, 153), (7, 121, 156)]]

@[expose] def burnsideF48s_sp43c_coverB (s : ℕ) (tr : List ℕ) (wit : List (ℕ × ℕ))
    (dec : List (List (ℕ × ℕ × ℕ))) : Bool :=
  ((List.range 162).all fun i =>
    decide ((wit.getD i (0, 0)).1 < 3) &&
      decide (compL (burnsideF48s_sp43c_Bl i) (burnsideF48s_sp43c_L s) =
        compL (compL (burnsideF48s_sp43c_Bl (tr.getD (wit.getD i (0, 0)).1 0))
          (burnsideF48s_sp43c_L s)) (burnsideF48s_sp43c_Bl (wit.getD i (0, 0)).2))) &&
  ((List.range 8).all fun j => (List.range 3).all fun t =>
    decide (((dec.getD j []).getD t (0, 0, 0)).1 < 8) &&
      decide (compL (compL (burnsideF48s_sp43c_Dl j) (burnsideF48s_sp43c_Bl (tr.getD t 0)))
          (burnsideF48s_sp43c_L s) =
        compL (compL (burnsideF48s_sp43c_Bl ((dec.getD j []).getD t (0, 0, 0)).2.1)
          (burnsideF48s_sp43c_Dl ((dec.getD j []).getD t (0, 0, 0)).1))
          (burnsideF48s_sp43c_Bl ((dec.getD j []).getD t (0, 0, 0)).2.2)))

@[expose] def burnsideF48s_sp43c_glF (j : ℕ) (k : Fin 3) : List ℕ :=
  ![burnsideF48s_sp43c_L 0, burnsideF48s_sp43c_L 1, burnsideF48s_sp43c_Dl j] k

@[expose] def burnsideF48s_sp43c_gliF (j : ℕ) (k : Fin 3) : List ℕ :=
  ![burnsideF48s_sp43c_Li 0, burnsideF48s_sp43c_Li 1, burnsideF48s_sp43c_Dli j] k

@[expose] def burnsideF48s_sp43c_farW : List (List (Fin 3 × Bool) × List (Fin 3 × Bool)) :=
  [
    ([(0, true), (2, true), (0, true), (2, false), (0, true), (2, true)],
      [(0, false), (2, false), (0, false), (2, true), (0, false)]),
    ([(0, true), (2, true), (0, true), (2, false), (0, true), (2, true)],
      [(0, false), (2, true), (0, false), (2, false), (0, false)]),
    ([(0, true), (1, false), (2, true), (1, true), (0, true), (1, true), (0, false), (2, false),
       (1, false)],
      [(0, true), (1, true), (2, true), (1, false), (2, true), (1, true), (0, true), (2, false)]),
    ([(0, true), (0, true), (2, true), (0, false), (2, true), (0, false), (2, true)],
      [(0, true), (1, true), (2, true), (1, true), (2, true), (0, true)]),
    ([(0, true), (1, false), (2, true), (0, true), (1, false), (0, false), (0, false), (1, false),
       (0, true), (2, true), (1, false)],
      [(1, true), (2, true), (1, true), (0, true), (1, true), (2, true), (1, true), (2, true)])]

@[expose] def burnsideF48s_sp43c_xw : List (Fin 4 × Bool) :=
  [(2, true), (1, true), (2, true), (1, false), (2, true)]

@[expose] def burnsideF48s_sp43c_yw : List (Fin 4 × Bool) :=
  [(0, true), (3, false), (0, false), (1, false), (2, true), (1, false), (2, true)]

@[expose] def burnsideF48s_sp43c_checkGens (_ : Unit := ()) : Bool :=
  (List.range 4).all fun i =>
    decide (burnsideF48s_sp43c_L i = U42F431.evalW (burnsideF48s_sp43XY.getD i [])) &&
      decide (burnsideF48s_sp43c_Li i =
        U42F431.evalW (U42F431.invW (burnsideF48s_sp43XY.getD i [])))

@[expose] def burnsideF48s_sp43c_checkSub (_ : Unit := ()) : Bool :=
  burnsideF48s_sp43c_groupB burnsideF48s_sp43c_glB burnsideF48s_sp43c_gliB
      (burnsideF48s_sp43c_BW ()) 162 &&
    burnsideF48s_sp43c_groupB burnsideF48s_sp43c_glS burnsideF48s_sp43c_gliS
      (burnsideF48s_sp43c_SW ()) 81 &&
    burnsideF48s_sp43c_groupB burnsideF48s_sp43c_glP1 burnsideF48s_sp43c_gliP1
      (burnsideF48s_sp43c_P1W ()) 648 &&
    burnsideF48s_sp43c_groupB burnsideF48s_sp43c_glP2 burnsideF48s_sp43c_gliP2
      (burnsideF48s_sp43c_P2W ()) 648

@[expose] def burnsideF48s_sp43c_checkCover (_ : Unit := ()) : Bool :=
  burnsideF48s_sp43c_coverB 2 burnsideF48s_sp43c_trP burnsideF48s_sp43c_witP
      burnsideF48s_sp43c_decP &&
    burnsideF48s_sp43c_coverB 3 burnsideF48s_sp43c_trQ burnsideF48s_sp43c_witQ
      burnsideF48s_sp43c_decQ

@[expose] def burnsideF48s_sp43c_checkFar (_ : Unit := ()) : Bool :=
  (List.range 5).all fun i =>
    decide (burnsideF48s_sp43c_evL (burnsideF48s_sp43c_glF (i + 3))
        (burnsideF48s_sp43c_gliF (i + 3)) (burnsideF48s_sp43c_farW.getD i ([], [])).1 =
          burnsideF48s_sp43c_L 2) &&
      decide (burnsideF48s_sp43c_evL (burnsideF48s_sp43c_glF (i + 3))
        (burnsideF48s_sp43c_gliF (i + 3)) (burnsideF48s_sp43c_farW.getD i ([], [])).2 =
          burnsideF48s_sp43c_L 3)

@[expose] def burnsideF48s_sp43c_checkXY (_ : Unit := ()) : Bool :=
  decide (burnsideF48s_sp43c_evL4 burnsideF48s_sp43c_xw = U42F431.xL) &&
    decide (burnsideF48s_sp43c_evL4 burnsideF48s_sp43c_yw = U42F431.yL)

@[expose] def burnsideF48s_sp43c_checkS (_ : Unit := ()) : Bool :=
  let SL := burnsideF48s_sp43c_SL ()
  (SL.all fun x =>
    [(burnsideF48s_sp43c_L 0, burnsideF48s_sp43c_Li 0),
      (burnsideF48s_sp43c_Li 0, burnsideF48s_sp43c_L 0),
      (burnsideF48s_sp43c_L 1, burnsideF48s_sp43c_Li 1),
      (burnsideF48s_sp43c_Li 1, burnsideF48s_sp43c_L 1)].all fun g =>
      SL.contains (compL (compL g.1 x) g.2)) &&
    !(SL.contains (compL (compL (burnsideF48s_sp43c_L 2) (burnsideF48s_sp43c_L 1))
      (burnsideF48s_sp43c_Li 2))) &&
    !(SL.contains (compL (compL (burnsideF48s_sp43c_L 3)
      (compL (burnsideF48s_sp43c_L 0) (burnsideF48s_sp43c_L 0))) (burnsideF48s_sp43c_Li 3)))

@[expose] def burnsideF48s_sp43c_checkNot (_ : Unit := ()) : Bool :=
  !((burnsideF48s_sp43c_P2L ()).contains (burnsideF48s_sp43c_L 2)) &&
    !((burnsideF48s_sp43c_P1L ()).contains (burnsideF48s_sp43c_L 3))

end CFSG.ASVolI
