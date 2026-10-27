module

public section

namespace CFSG.Quasithin.J4Ov

structure RepEntry where
  l : Nat
  xw : String
  exc : Bool
  c : Nat

@[expose] def repData : List RepEntry :=
  [⟨5, "aacbcbcba", false, 0⟩,
    ⟨5, "bbcacaaca", false, 0⟩,
    ⟨5, "aabcacbaac", false, 0⟩,
    ⟨5, "baaaccc", false, 0⟩,
    ⟨5, "baccccaaa", false, 0⟩,
    ⟨5, "aaaacbcbaa", false, 0⟩,
    ⟨5, "cabaacc", false, 0⟩,
    ⟨5, "bbcab", false, 0⟩,
    ⟨5, "bbbabbb", false, 0⟩,
    ⟨5, "aaabbaaab", false, 0⟩,
    ⟨5, "cbcaaacca", false, 0⟩,
    ⟨5, "bbbcbaaba", false, 0⟩,
    ⟨5, "bcccbacbb", false, 0⟩,
    ⟨5, "abcbbbcbb", false, 0⟩,
    ⟨5, "aa", false, 0⟩,
    ⟨5, "bccccaa", false, 0⟩,
    ⟨5, "bccabcb", false, 0⟩,
    ⟨5, "abbbbbbbab", false, 0⟩,
    ⟨5, "cabaac", true, 1243⟩,
    ⟨5, "acbcabbc", false, 0⟩,
    ⟨5, "ccbbabab", false, 0⟩,
    ⟨5, "acaaacabb", false, 0⟩,
    ⟨5, "bbbaccac", false, 0⟩,
    ⟨5, "acca", false, 0⟩,
    ⟨5, "aacbccb", true, 864⟩,
    ⟨5, "bbabcacc", true, 165⟩,
    ⟨5, "cbacbcb", false, 0⟩,
    ⟨5, "cabccabbb", true, 1150⟩,
    ⟨6, "cacaaabb", false, 0⟩,
    ⟨6, "ccbababb", false, 0⟩,
    ⟨6, "acaacccbc", false, 0⟩,
    ⟨6, "ababbaabca", false, 0⟩,
    ⟨6, "ccbaacccc", false, 0⟩,
    ⟨6, "ccabccacb", false, 0⟩,
    ⟨6, "accbcbbcc", false, 0⟩,
    ⟨6, "ababbbaaca", false, 0⟩,
    ⟨6, "cbbbbbaba", false, 0⟩,
    ⟨6, "abaacbbcc", false, 0⟩,
    ⟨6, "ccbacaac", false, 0⟩,
    ⟨6, "bacacccb", false, 0⟩,
    ⟨6, "bbbcabcabb", false, 0⟩,
    ⟨6, "aaaabccbcc", false, 0⟩,
    ⟨6, "caccbcbaba", false, 0⟩,
    ⟨6, "abcbabbac", false, 0⟩,
    ⟨6, "aaabababccb", false, 0⟩,
    ⟨6, "cacbcbbb", false, 0⟩,
    ⟨6, "cbbaacaab", false, 0⟩,
    ⟨6, "cababab", true, 112⟩,
    ⟨6, "bbabbbaac", false, 0⟩]

end CFSG.Quasithin.J4Ov
