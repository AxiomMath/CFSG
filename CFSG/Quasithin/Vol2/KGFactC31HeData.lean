module

public import CFSG.Sporadic.HeldB.OuterArithCheck
public import CFSG.Quasithin.Vol2.KGFactC31BadScan
public import CFSG.Quasithin.Vol2.KGFactC31ArrChain

public section

namespace CFSG.Quasithin.KGC31.He

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.HeldB CFSG.Certificates.Native
  CFSG.Quasithin.KGC31.Native CFSG.Sporadic.Schreier.PairNative CFSG.Quasithin.KGC31

@[expose] def gA : Array (Array ℕ) := #[heGen 0, heGen 1, heUArr]

@[expose] def gAi : Array (Array ℕ) := gA.map (invCand 8330)

@[expose] def wA (w : List ℤ) : Array ℕ := wordA 8330 gA gAi w

@[expose] def wAi (w : List ℤ) : Array ℕ := invCand 8330 (wA w)

@[expose] def invW (w : List ℤ) : List ℤ := (w.map fun l => -l).reverse

@[expose] def bs : List ℕ := [0, 1, 2, 3, 4]

@[expose] def decodeL (c : Char) : ℤ :=
  if c = '1' then 1 else if c = '2' then 2 else if c = '3' then 3 else if c = 'a' then -1 else
    if c = 'b' then -2 else if c = 'c' then -3 else 0

@[expose] def decodeW (s : String) : List ℤ := (s.toList.filter (· ≠ '0')).map decodeL

@[expose] def decodeWs (s : String) : List (List ℤ) :=
  if s = "" then [] else (s.splitOn " ").map decodeW

@[expose] def decodeWss (s : String) : List (List (List ℤ)) := (s.splitOn "|").map decodeWs

@[expose] def noDer (k : ℕ) : Array (List ℤ) := (List.replicate k ([] : List ℤ)).toArray

@[expose] def t1W : List ℤ := decodeW "1222122212221222"

@[expose] def t0A : Array ℕ := wA [1]

@[expose] def t1A : Array ℕ := wA t1W

@[expose] def c0W : List (List ℤ) := decodeWs "bbabbbabababba222ababaaaba2121ba22ababaaaba21212aba\
  baaaba2121221b1bb1222121212a2a2a2a22abb a bbbbabbabababbabbabbbb1221bb1221bb1222ab bababababbbba\
  babba2a22ababaaaba2121ba22a2a22a2a2a2a2a2222aba2abbbb1b1212212121212a"

@[expose] def c0B : Vector (Fin 8330) 2 := #v[7236, 3504]

@[expose] def c0S : Array (Array ℕ) := (c0W.map wA).toArray

@[expose] def c1W : List (List ℤ) := decodeWs "aba222a222abababa21212abababa2121ba22aabababa21212a\
  bababa212122aba2ababbab1b12a22a2a2a2a221b bbbabababbabba2aabababa2121ba22abababa2121ba22abababa2\
  12121222121221bbb122122121212a2a2a2a22ab1ba bbababbbabba222a22aba22abababa21212abababa21212abba2\
  2abba22abba2a2aba2abba221bbb1b1212212121212a bbbabbbbba22aabababa21212a21b122122121bbb12122221b1\
  2a2abbba2abb bbbabbbabababbababbabababa21212abba22abababa21212abababa212122aba2ababba22221b1221b\
  b121b1ba abbabbababa222ababbabababa2121ba22abababa21212a222a2a2a2a2a2222121b122ababa2abba bababb\
  bababba22ab12221bb121b12121b1221b121ba2abb 2221b12a2abbaba2abb1bbb1212abbabbbabababb1221bb12abab\
  1212121bb1221babab1212121221212212221212121 abbba2221b122212abababa21212abba22abababa2121ba22aab\
  ababa21212abba22abba2a2aba2abba22abababababbaba2a222 babbabbabbabbbabbbabababa2121ba22aabababa21\
  21ba22abba22abababa2121b1221bb1221bb1222abbbb1b1212212121212a 122aba2abab1b1b1b1babababbba222aba\
  bba222ababbb12122212212212"

@[expose] def c1B : Vector (Fin 8330) 3 := #v[5, 197, 196]

@[expose] def c1S : Array (Array ℕ) := (c1W.map wA).toArray

@[expose] def reps0W : List (List ℤ) := decodeWs "221b122aba2abba2abba bbabbbabababba222ababaaaba2\
  121ba22ababaaaba21212ababaaaba2121221b1bb12212121b1221b1ba2abb bbabbbabababba222ababaaaba2121ba2\
  2ababaaaba21212ababaaaba2121221b1bb12212121b1221b1ba2abba babbbbbababbba222ababaaaba2121ba22abba\
  22ababaaaba21212ababaaaba21212aba2ababa22221b12121bba2ababa bababbbabbaba22ababbababaaaba21212a2\
  21bbb121222121b12221b12121bba2ababa"

@[expose] def fix0 : List ℕ := [346, 346, 42, 42, 346]

@[expose] def size0 : List ℕ := [240, 315, 315, 630, 2]

@[expose] def scan0I : List ℕ := [0, 1, 4]

@[expose] def scan0H : List (List ℤ) := decodeWs "bbbbbababababbbabbabbaababaaaba2121ba22ababaaaba\
  21212a2abba2aba22aba2aba2ab abbbbbabbab122212121222aba2aba2abb abbbabbabbbabbabbabbbba22ababaaab\
  a2122ababbbaba222abba2a2aba22abba2abb"

@[expose] def scan0D : List (List (List ℤ)) := decodeWss "|bbcbbc222abbbbabbbababbababbabbbabbbabc\
  bb1bbb1bbaba2a2a bcbc22cbbb1b121babcbbabbab3b123212acbab3b123212 babba22a2a222abba22ababaaaba212\
  1ba22abba22ababaaaba21212abba22abba221221b121b121bba bbabbabbababbababaaaba2121ba22abba22ababaaa\
  ba21212aba2ababa222121212a2a2a2a22ab1b|"

@[expose] def scan0K : List (List ℕ) := [[], [0, 0, 0, 0], []]

@[expose] def reps1W : List (List ℤ) := decodeWs "bbbbbabba222abbbababaaaba2121ba22aababaaaba21212\
  ababaaaba2121ba22aababaaaba21212ababaaaba2121ba22ababaaaba21212abababa2a2a2221bb1b1b1b1bababba a\
  babbabbababbbba22ababaaaba21212abba22aababaaaba2121ba22ababaaaba212122aba2ababba2ababababbaba2a2\
  2221ba aba222a222ababaaaba21212abba22abba22ababaaaba21212ababaaaba21212ababaaaba212122aba2ababba\
  222121212a2a2a2a22abba bbbbabbbbabbabbabbbba22aababaaaba21212ababaaaba2121ba22ababaaaba21212abba\
  22abba22ababaaaba21212abba22abba22a2a21bb1b1b1b1bababab bbb1b1bbb12ababaaaba21212abba22aababaaab\
  a21212ababaaaba21212aba2ababbbaba222ababa2aba bbbbabbababbababbbabbbbba22ababaaaba21212ababaaaba\
  2121ba22ababaaaba21212ababaaaba2121ba22ababaaaba21212abba22abababa2a2a2121b1221b121ba2abba abbba\
  2221b12221ba22ababaaaba2121ba22aababaaaba2121ba22ababaaaba2121ba22abba22a2abba21b122aba2abbbb1b1\
  212212121212"

@[expose] def fix1 : List ℕ := [346, 42, 42, 42, 346, 42, 42]

@[expose] def size1 : List ℕ := [84, 168, 84, 168, 42, 14, 14]

@[expose] def scan1I : List ℕ := [1, 2, 3, 5, 6]

@[expose] def scan1H : List (List ℤ) := decodeWs "ababababbabbbbabbbababbababaaaba2121ba22ababaaab\
  a21212abba2221bb121b1221babba22221bb1b1b1b1bababb bbb1b12122121212121bb1221b121b1b1221bb12abab12\
  1112121bb12abab121112121babab1211121211b1bb1221212212212121 2121b12221b1ba2abbbb1b1b1212121bb122\
  1bb12abab121112121bb12abab121112121babab12111212122122122121221221 bbbbababbabbabbabba22ababaaab\
  a21212abababa2a2a22aba2abbbb1b1212212121212 bbbaba2abbabbbbba22aababaaaba2121ba22ababaaaba21212a\
  bba22ababaaaba2121ba22ababaaaba21212abba22abba22221b12121bba2abab"

@[expose] def scan1D : List (List (List ℤ)) := decodeWss "bababababbaba2a22221b121bbb122121b121212\
  1bb122122212 1221212a2a2a2a2121b121bbb12221222121222122abab121112121222121222122121221212221 0 2\
  121b122abababb121222121bbab121112121babab1211121211bb1b1221bb12122 0||b1b12121babbaba2a2a2a23212\
  221222122132122212221223b1bb1 bbabbb1b3212aba2a2cb3b31b12ac2c2c21 21232212ababbcbababbab312a22c2\
  12232122121 ababbbcbabbabbbabababa2a22a22cabbabbaba2ababcbaba2ababa cbbcbcbbababbabbabb323123223\
  2ababa2ababbb1b3212aba2a2ca|1221b121b121bbbb1221bb12221212221b1212221 a2a2abbababbbba22aababaaab\
  a2121ba22abba22ababaaaba21212abba22abba2a2a2ababbbabab121bbba abbbaba222aba22221b1bb1221bb122212\
  1212a2a2a2a22ab1ba 12abb1b1b1b1bb1ba2a222221bbb121222121bbab121112121babab121112121bbb1212122122\
  122212222 2abbbab1b121bbb122221b12121bba2abab bbbababbabbabab1bb1b12221b1bb1bababababababbaba2a2\
  22|babbbcbabcbabcabbab3b321b1bacbbabba22abba2ababbababbabbbabc 21bb1bbcbbbc23212221221212322121b\
  abbcbab 3b1b121babc2a2221223bb1bb1ba2a2212221 abbabacbbabbbababbabbb1b1bb1ba2a222121b1212a 1bb1b\
  1bb1ba2a222121b12123b1b121221 1bbababbaba212221223212212122121221212221221b1"

@[expose] def scan1K : List (List ℕ) := [[1, 1, 1, 0, 0], [], [1, 0, 0, 1, 1], [0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0]]

@[expose] def w5W : List (List ℤ) := decodeWs "1222122212221222 ababbabbababbbba22ababaaaba21212ab\
  ba22aababaaaba2121ba22ababaaaba212122aba2ababba2ababababbaba2a22221ba bbbbabbbbbababbababbbba22a\
  babaaaba21212ababaaaba2121ba22ababaaaba21212ababaaaba21212ababaaaba2121b1221bb1221bb122221bb1b1b\
  1b1bababba bbabbbbabbababa221b1221b1221baba21221b121b121bb"

@[expose] def eW : List (List ℤ) := decodeWs "1222122212221222 ababbabbababbbba22ababaaaba21212abb\
  a22aababaaaba2121ba22ababaaaba212122aba2ababba2ababababbaba2a22221ba bbbbabbbbbababbababbbba22ab\
  abaaaba21212ababaaaba2121ba22ababaaaba21212ababaaaba21212ababaaaba2121b1221bb1221bb122221bb1b1b1\
  b1bababba bbabbbbabbababa221b1221b1221baba21221b121b121bb babbababbabba2ababaaaba21212abba22abab\
  aaaba2121ba22abba22ababaaaba2121ba22abba2a2aba2abbab1b1212212121212 abbbabba22abbba222ab12221222\
  1212221222a2ab"

@[expose] def w7W : List (List ℤ) := decodeWs "1222122212221222 ababbabbababbbba22ababaaaba21212ab\
  ba22aababaaaba2121ba22ababaaaba212122aba2ababba2ababababbaba2a22221ba babbababababbbababbababaaa\
  ba21212ababaaaba21211212abba2abba2a2221b1221bb121b1ba"

@[expose] def qW : List (List ℤ) := decodeWs "1222122212221222 ababbabbababbbba22ababaaaba21212abb\
  a22aababaaaba2121ba22ababaaaba212122aba2ababba2ababababbaba2a22221ba babbababababbbababbababaaab\
  a21212ababaaaba21211212abba2abba2a2221b1221bb121b1ba bbba2abbbabbbababaaaba21212abba22abba22abab\
  aaaba21212ababaaaba2121ba22ababaaaba21212ababaaaba21212abba22abba22221212a2a2a2a22abb"

@[expose] def sigmaW : List ℤ := decodeW "bcba2cbbbabcbbabbbabbb1bbb1bbbabbbab1212212122a"

@[expose] def nsW : List (List ℤ) := decodeWs "22a2aba2222aba21221b1ba2a222a 221b1221bb121b1b1bba2\
  22ababba22a2abbb122212222221212222221bb122212222222221bb12212221212 bbb1b1bbb1babbbbabbbabbbbabb\
  ba22abbbbbbabbba22abbabbbbabbb1221bb1221bb122222aba21221b1ba2a222 bbab1b121bbb122221ba2a2abba2ab\
  b bbbbabbababbababbbabbbbbabbbbababbbbbbabbbabbbbabbba22abba22abbbbbbabbba22a2abbba22abba222abbb\
  b1b1212212121212a babbbabbababbba222abbabbbbabba22aba2a2a222a222121b122ababa2abba bbbabbbababbbb\
  abbbbababba22abbabbbbababba2221bbb122121bbb122221ba2a2abba2abb bbba2abbbabbbabbbbbbababbbbbbabbb\
  a221bb12221b121bbb1222221b12a2abbba2abba a222a22abbbba22abbabbbbababbbbbbabbba22abba22a2abbba222\
  21212a2a2a2a22ab1ba bababababbababba22aba22a2abba2aba22abbba22221b1221bb121b1ba bababbbabba22abb\
  bbbbbbbabbba22abbbbbbababbbbbbabbba2221b1bb122121bbb122a2a2aba22abba2abb abbabbabbbababbbbbabbbb\
  abbbabbbbabbba22abbbbbbabbba22abba222abbba22a2aba bbababbba2a2abbbaba22abbabbbbababba22abba222ab\
  bba22abba22221212a2a2a2a22ab1b 1221212a2a2a2a22ab1bbb12221b1bb122121b1212222221bb122212222122212\
  2222222121221212122 bbbbabbbbbababbababbabbabbbbababbabbbbabbba22abba22a2abbba222121212a2a2a2a21\
  21b121bb ababa2ababbbababbbbabbbabababababa22a222121212a2a2a2a22abba 2ab121b1221b121ba2abbbba222\
  1bbb12221b1bb122212222221212222221bb1222212122212122121222122 bbabababbababbbbbbbbabbbabbbbabbba\
  22abbbbbbaba2ababba22a2abbba222a21bb1b1b1b1bababba bbabbbababbababbbababbbba22abbbbbbababbbbbbab\
  bba22a2abbba222abbb122221b12aba2abba2aba21b babba22aba2aba22abbbbbbababbabbbbabbb12212aba2ababba\
  2222aba2aba2abab 121b1bb12221bbb1221bb122212222221bb1222122221222122221222221212221221221 12a2ab\
  a22abba2abbbb12221bb121b1221b1bb121bb1221212212121212 bbbbbabbbbbababba22a2abbbbbbababbbbbbabbba\
  22abbbbbbabbbabbbbababba222abbba22abba222121212a2a2a2a22ab1ba"

@[expose] def nsB : Vector (Fin 8330) 4 := #v[2464, 1, 0, 161]

@[expose] def nsS : Array (Array ℕ) := (nsW.map wA).toArray

@[expose] def n7W : List (List ℤ) := decodeWs "aba222abbbababbbbbbab1bb12221b121bbb1b1b12a22a2a2a2\
  a221b aba22a2abbbabbbabbbbababbabbbbabbba22abbbbbbabbba22abba2221b1bb1221bb122221b1221bb121b1ba \
  babbababbabba2abbabbbbababba22221bb1b1b121bb122122121212a2a2a2a22abba ba2a22abbbabbbbbabbba22abb\
  a22a2aba2ababba221bbb1b1212212121212 bbababbbabba222a22abbbbbababbbbbbabbbabbbbababbbbbbababba22\
  21bbb122121bbb12ababababbaba2a22221ba 2121b12221b1ba2abbbbb1221bb12221b1bb122212222221bb12212122\
  221221b12212121 babbabbba222a2aba22abbabbbbababbabbbbaba2ababba22a2abbba22222aba21221b1ba2a222 b\
  bbbbababbbbbababba22aba22abba222abbba2ababababbaba2a22221b121ba bababababbaba2a22221b121bbb12212\
  1b121b1bb1221bb122212222221bb12221222212222121221212212 1bbb1b12122121212121bba22abba222aba2abbb\
  1221212222122212222122122212212121222121 bbbabbbabababa2222221b1bb121bbb1212 babbababbababbbbabb\
  bbabbba22abbbbbbabbba22abba22a2aba2ababba222aba2abbbb1b1212212121212 ababbbabababbabbbabbabbbbab\
  bbabbbbababba2221b121bbb1221bb122abababababbaba2a222a bbbababbababbababbbbbbbbababbabbbbabbbabbb\
  baba2abbba222ababba222121212a2a2a2a2121b121bb ababbbabbbabbbbbbbbbababbabbbbabbba22abbbbbbabbba2\
  2abba22a2abbba22221212a2a2a2a22abba bbb1b12a2abbab121bbbbb12221b1bb122121b121222212212122221221b\
  b121b1bbb122212212 ababbbababbbbbbbbababbbbbbabbba22121b1bb12221babba22221212a2a2a2a22ab1b babba\
  bba222ababbbbbbbbabbba22a222a2a2a2a2a222221b12121bba2ababa abbb1bb1bbb12abbbbbbabbba22abbbbbbabb\
  babbbbababbbbbbababba22abba22abbbbbbabbb1221bb1221bb1222121212a2a2a2a22ab1b babbbbbbabbbabbababb\
  bbbbbbabbba22abbbbbbababbabbbbaba2ababba22a2abbba222abbbb1b1212212121212a"

@[expose] def n7B : Vector (Fin 8330) 4 := #v[5, 203, 202, 201]

@[expose] def n7S : Array (Array ℕ) := (n7W.map wA).toArray

@[expose] def y5W : List ℤ := decodeW "2a21bb1b1b1b1babababbb1bb1b122212221221bb12abab121112121bab\
  ab12111212122121bbb12222122121"

@[expose] def njW : List (List ℤ) := decodeWs "bbbaba2a22abbbba22abba22ababaaaba2121ba22ababaaaba2\
  12121222121221bbb122122abb1b1b1b1bb1ba2a222 21b121b1bb12122aba22aba2abbbabab121112121babab121112\
  12112221bb1b1bb1"

@[expose] def lsDer : List (List ℤ) := decodeWs "a2231cba211b1b1b c2a312aba212a 1b1b1cac1 121c1ba2\
  1 2 3 1"

@[expose] def lsGenW : List (List ℤ) := y5W :: njW.map fun n => n ++ y5W ++ invW n

@[expose] def lsS : Array (Array ℕ) :=
  lsDer.foldl (fun S w => S.push (wordA 8330 S (S.map (invCand 8330)) w)) (lsGenW.map wA).toArray

@[expose] def lsWd : Array (List ℤ) := (List.replicate lsGenW.length ([] : List ℤ) ++ lsDer).toArray

@[expose] def lsB : Vector (Fin 8330) 2 := #v[0, 1]

@[expose] def bB : List ℕ := [2464, 7750, 8271, 8281, 5830, 6837]

@[expose] def w5A : List (Array ℕ) := w5W.map wA

@[expose] def eA : List (Array ℕ) := eW.map wA

@[expose] def w7A : List (Array ℕ) := w7W.map wA

@[expose] def qA : List (Array ℕ) := qW.map wA

@[expose] def sigA : Array ℕ := wA sigmaW

@[expose] def sigAi : Array ℕ := wAi sigmaW

@[expose] def refA (k : ℕ) : List (Array ℕ) := if k = 0 then w5A else w7A

@[expose] def candsOf (D : List (List ℤ)) (K : List ℕ) : List (List (List (Array ℕ))) :=
  (D.zip K).map fun p => (refA p.2).map fun b => [wAi p.1, b, wA p.1]

@[expose] def heL : Array Level := rawLevels 8330 heStrongArrs heBase.toArray

@[expose] def fixA (t : Array ℕ) : ℕ := (List.range 8330).countP fun i => t[i]! == i

@[expose] def commA (g t : Array ℕ) : Bool := baseImgs bs [g, t] == baseImgs bs [t, g]

@[expose] def conjOK (t : Array ℕ) (reps : List (List ℤ)) (I : List ℕ) (H : List (List ℤ)) :
    Bool :=
  (I.zip H).all fun p => baseImgs bs [wAi p.2, t, wA p.2] == baseImgs bs [wA (reps.getD p.1 [])]

@[expose] def fixOK (t : Array ℕ) (reps : List (List ℤ)) (I : List ℕ) : Bool :=
  (List.range reps.length).all fun i => I.contains i || fixA (wA (reps.getD i [])) != fixA t

@[expose] def scanCount (S : Array (Array ℕ)) (B : Array ℕ) (k : ℕ) (t : Array ℕ)
    (reps : List (List ℤ)) (I : List ℕ) (H : List (List ℤ)) (D : List (List (List ℤ)))
    (K : List (List ℕ)) (j : ℕ) : ℕ :=
  countWI (badTest bs t (wA (reps.getD (I.getD j 0) [])) [25, 343, 17] [5, 7, 17] false
    (candsOf (D.getD j []) (K.getD j []))) (levBlocksI (rawLevels 8330 S B) k)
    [wA (H.getD j [])] [wAi (H.getD j [])]

@[expose] def blk1 : List (Array (Array ℕ)) := blocksOf 8330 (rawLevels 8330 c1S (arrBase c1B))
  [[0], [1], [2]]

@[expose] def centIn (B : List (Array ℕ)) (w : List (Array ℕ)) : Bool :=
  B.all fun b => baseImgs bs (w ++ [b]) == baseImgs bs (b :: w)

@[expose] def centOut (B : List (Array ℕ)) (w : List (Array ℕ)) : Bool :=
  B.all fun b => baseImgs bs (b :: w) == baseImgs bs (w ++ [sigA, b, sigAi])

@[expose] def fixesB (w : List (Array ℕ)) : Bool := bB.all fun p => evR w p == p

end CFSG.Quasithin.KGC31.He

end
