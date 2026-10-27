module

public import Certificates.Data.CFSGNative.F3.Basic

public section

namespace CFSG.Sporadic.McL.Native

open CFSG.F3.Native

@[expose] def letterOf (c : Char) : Int :=
  if c = 'a' then 1 else if c = 'A' then -1 else if c = 'b' then 2 else -2

@[expose] def wordOf (s : String) : List Int := s.toList.map letterOf

@[expose] def seedA : String := include_str "../../../../CFSG/Blueprint/Data/McLG1-f3r21B0.m1"

@[expose] def seedB : String := include_str "../../../../CFSG/Blueprint/Data/McLG1-f3r21B0.m2"

@[expose] def rootVec : V := ⟨132229, 1392752⟩

@[expose] def chainBase : Array Nat := #[0, 1, 2, 3, 4, 5]

@[expose] def chainQ : Array Nat := #[
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 19, 20, 26]

@[expose] def chainQb (_ : Unit := ()) : Array Nat := #[0, 1, 2, 3, 4, 5]

@[expose] def chainWords (_ : Unit := ()) : Array (List Int) := #[
    wordOf ("a"),
    wordOf ("b"),
    wordOf ("ABAbabbbbaba"),
    wordOf ("BABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAA"),
    wordOf ("ABABBBBABabaaaBaBabbbaaabbABAbabbbbababbABAbabbbbababABABBBBABabaBABABBBBABabaBB" ++
      "ABABBBBABabaBBAAABBBAbAbAABABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAAABABBBBABabaB" ++
      "ABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAAAbbbaBBBA"),
    wordOf ("ABABBBBABabaBABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAbbbABBBaaaBaBabbbaaabbABAbab" ++
      "bbbababbABAbabbbbababABAbabbbbabaaaBaBabbbaaabbABAbabbbbababbABAbabbbbababaaBaBa" ++
      "bbbaaabbABAbabbbbababbABAbabbbbababABAbabbbbabaBABABBBBABabaBBABABBBBABabaBBAAAB" ++
      "BBAbAbAAABAbabbbbabaabbbABBBaaaBaBabbbaaabbABAbabbbbababbABAbabbbbababABAbabbbba" ++
      "baaaBaBabbbaaabbABAbabbbbababbABAbabbbbababaaBaBabbbaaabbABAbabbbbababbABAbabbbb" ++
      "ababABAbabbbbabaBABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAAABAbabbbbabaBBBABABBBBA" ++
      "BabaBBABABBBBABabaBBAAABBBAbAbAAbaBBabbaab"),
    wordOf ("BAABBAbbABaaBaBabbbaaabbABAbabbbbababbABAbabbbbababbbABABBBBABabaaaBaBabbbaaabbA" ++
      "BAbabbbbababbABAbabbbbababABABBBBABabaBABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAAB" ++
      "ABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAAABABBBBABabaBABABBBBABabaBBABABBBBABabaB" ++
      "BAAABBBAbAbAAAbbbaBBBAABABBBBABabaaaBaBabbbaaabbABAbabbbbababbABAbabbbbababABABB" ++
      "BBABabaBABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAABABABBBBABabaBBABABBBBABabaBBAAA" ++
      "BBBAbAbAAABABBBBABabaBABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAAAbbbaBBBaBaBabbbaa" ++
      "abbABAbabbbbababbABAbabbbbababABAbabbbbabaBAABBAbbABaaBaBabbbaaabbABAbabbbbababb" ++
      "ABAbabbbbababbbABABBBBABabaaaBaBabbbaaabbABAbabbbbababbABAbabbbbababABABBBBABaba" ++
      "BABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAABABABBBBABabaBBABABBBBABabaBBAAABBBAbAb" ++
      "AAABABBBBABabaBABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAAAbbbaBBBAABABBBBABabaaaBa" ++
      "BabbbaaabbABAbabbbbababbABAbabbbbababABABBBBABabaBABABBBBABabaBBABABBBBABabaBBAA" ++
      "ABBBAbAbAABABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAAABABBBBABabaBABABBBBABabaBBAB" ++
      "ABBBBABabaBBAAABBBAbAbAAAbbbaBBBaBaBabbbaaabbABAbabbbbababbABAbabbbbabababbbABBB" ++
      "aaaBaBabbbaaabbABAbabbbbababbABAbabbbbababABAbabbbbabaaaBaBabbbaaabbABAbabbbbaba" ++
      "bbABAbabbbbababaaBaBabbbaaabbABAbabbbbababbABAbabbbbababABAbabbbbabaBABABBBBABab" ++
      "aBBABABBBBABabaBBAAABBBAbAbAAABAbabbbbabaaaBaBabbbaaabbABAbabbbbababbABAbabbbbab" ++
      "abABABBBBABababaaBaBabbbaaabbABAbabbbbababbABAbabbbbabababbbABBBaaaBaBabbbaaabbA" ++
      "BAbabbbbababbABAbabbbbababABAbabbbbabaaaBaBabbbaaabbABAbabbbbababbABAbabbbbababa" ++
      "aBaBabbbaaabbABAbabbbbababbABAbabbbbababABAbabbbbabaBABABBBBABabaBBABABBBBABabaB" ++
      "BAAABBBAbAbAAABAbabbbbabababbAba"),
    wordOf ("ABABBBBABabaBABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAbbbABBBaaaBaBabbbaaabbABAbab" ++
      "bbbababbABAbabbbbababABAbabbbbabaaaBaBabbbaaabbABAbabbbbababbABAbabbbbababaaBaBa" ++
      "bbbaaabbABAbabbbbababbABAbabbbbababABAbabbbbabaBABABBBBABabaBBABABBBBABabaBBAAAB" ++
      "BBAbAbAAABAbabbbbabaabbbABBBaaaBaBabbbaaabbABAbabbbbababbABAbabbbbababABAbabbbba" ++
      "baaaBaBabbbaaabbABAbabbbbababbABAbabbbbababaaBaBabbbaaabbABAbabbbbababbABAbabbbb" ++
      "ababABAbabbbbabaBABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAAABAbabbbbabaBBBABABBBBA" ++
      "BabaBBABABBBBABabaBBAAABBBAbAbAAbaBBabbaabABABBBBABabaaaBaBabbbaaabbABAbabbbbaba" ++
      "bbABAbabbbbababABABBBBABabaBABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAABABABBBBABab" ++
      "aBBABABBBBABabaBBAAABBBAbAbAAABABBBBABabaBABABBBBABabaBBABABBBBABabaBBAAABBBAbAb" ++
      "AAAbbbaBBBAABABBBBABabaaaBaBabbbaaabbABAbabbbbababbABAbabbbbabababbbABBBaaaBaBab" ++
      "bbaaabbABAbabbbbababbABAbabbbbababABAbabbbbabaaaBaBabbbaaabbABAbabbbbababbABAbab" ++
      "bbbababaaBaBabbbaaabbABAbabbbbababbABAbabbbbababABAbabbbbabaBABABBBBABabaBBABABB" ++
      "BBABabaBBAAABBBAbAbAAABAbabbbABBBBABabaBBABABBBBABabaBBAAABBBAbAbAAABABBBBABabbb" ++
      "abaaaaBB"),
    wordOf ("ABABBBBABabaBABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAbbbABBBaaaBaBabbbaaabbABAbab" ++
      "bbbababbABAbabbbbababABAbabbbbabaaaBaBabbbaaabbABAbabbbbababbABAbabbbbababaaBaBa" ++
      "bbbaaabbABAbabbbbababbABAbabbbbababABAbabbbbabaBABABBBBABabaBBABABBBBABabaBBAAAB" ++
      "BBAbAbAAABAbabbbbabaabbbABBBaaaBaBabbbaaabbABAbabbbbababbABAbabbbbababABAbabbbba" ++
      "baaaBaBabbbaaabbABAbabbbbababbABAbabbbbababaaBaBabbbaaabbABAbabbbbababbABAbabbbb" ++
      "ababABAbabbbbabaBABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAAABAbabbbbabaBBBABABBBBA" ++
      "BabaBBABABBBBABabaBBAAABBBAbAbAAbaBBabbaabABABBBBABabaaaBaBabbbaaabbABAbabbbbaba" ++
      "bbABAbabbbbababABABBBBABabaBABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAABABABBBBABab" ++
      "aBBABABBBBABabaBBAAABBBAbAbAAABABBBBABabaBABABBBBABabaBBABABBBBABabaBBAAABBBAbAb" ++
      "AAAbbbaBBBAABABBBBABabaaaBaBabbbaaabbABAbabbbbababbABAbabbbbabababbbABBBaaaBaBab" ++
      "bbaaabbABAbabbbbababbABAbabbbbababABAbabbbbabaaaBaBabbbaaabbABAbabbbbababbABAbab" ++
      "bbbababaaBaBabbbaaabbABAbabbbbababbABAbabbbbababABAbabbbbabaBABABBBBABabaBBABABB" ++
      "BBABabaBBAAABBBAbAbAAABAbabbbABBBBABabaBBABABBBBABabaBBAAABBBAbAbAAABABBBBABabbb" ++
      "abaaaaBBABaBBABABABBBBABabaaaBaBabbbaaabbABAbabbbbababbABAbabbbbababABABBBBABaba" ++
      "BABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAABABABBBBABabaBBABABBBBABabaBBAAABBBAbAb" ++
      "AAABABBBBABabaBABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAAAbbbaBBBABABABBBBABabaBBA" ++
      "BABBBBABabaBBAAABBBAbAbAABABAbabbbbabaBABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAAA" ++
      "BABBBBABabaaaBaBabbbaaabbABAbabbbbababbABAbabbbbababABABBBBABabaBABABBBBABabaBBA" ++
      "BABBBBABabaBBAAABBBAbAbAABABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAAABABBBBABabaBA" ++
      "BABBBBABabaBBABABBBBABabaBBAAABBBAbAbAAAbbbaBBBABABABBBBABabaBBABABBBBABabaBBAAA" ++
      "BBBAbAbAbbbABBBaaaBaBabbbaaabbABAbabbbbababbABAbabbbbababABAbabbbbabaaaBaBabbbaa" ++
      "abbABAbabbbbababbABAbabbbbababaaBaBabbbaaabbABAbabbbbababbABAbabbbbababABAbabbbb" ++
      "abaBABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAAABAbabbbbabaabbbABBBaaaBaBabbbaaabbA" ++
      "BAbabbbbababbABAbabbbbababABAbabbbbabaaaBaBabbbaaabbABAbabbbbababbABAbabbbbababa" ++
      "aBaBabbbaaabbABAbabbbbababbABAbabbbbababABAbabbbbabaBABABBBBABabaBBABABBBBABabaB" ++
      "BAAABBBAbAbAAABAbabbbbabaBBBABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAAbaBBabbaabAB" ++
      "ABBBBABabaBABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAbbbABBBaaaBaBabbbaaabbABAbabbb" ++
      "bababbABAbabbbbababABAbabbbbabaaaBaBabbbaaabbABAbabbbbababbABAbabbbbababaaBaBabb" ++
      "baaabbABAbabbbbababbABAbabbbbababABAbabbbbabaBABABBBBABabaBBABABBBBABabaBBAAABBB" ++
      "AbAbAAABAbabbbbabaabbbABBBaaaBaBabbbaaabbABAbabbbbababbABAbabbbbababABAbabbbbaba" ++
      "aaBaBabbbaaabbABAbabbbbababbABAbabbbbababaaBaBabbbaaabbABAbabbbbababbABAbabbbbab" ++
      "abABAbabbbbabaBABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAAABAbabbbbabaBBBABABBBBABa" ++
      "baBBABABBBBABabaBBAAABBBAbAbAAbaBBabbaabbbAAAABABBBAbabbbbabaaaBaBabbbaaabbABAba" ++
      "bbbbababbABAbabbbbaBBBABabaaaBaBabbbaaabbABAbabbbbababbABAbabbbbababABABBBBABaba" ++
      "BABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAABABABBBBABabaBBABABBBBABabaBBAAABBBAbAb" ++
      "AAABABBBBABabaBABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAAAbbbaBBBABABABBBBABabaBBA" ++
      "BABBBBABabaBBAAABBBAbAbAAABAbabbbbabaabbbABBBaaaBaBabbbaaabbABAbabbbbababbABAbab" ++
      "bbbababABAbabbbbabaaaBaBabbbaaabbABAbabbbbababbABAbabbbbababaaBaBabbbaaabbABAbab" ++
      "bbbababbABAbabbbbababABAbabbbbabaBABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAAABAbab" ++
      "bbbabaBAABBAbbABaaBaBabbbaaabbABAbabbbbababbABAbabbbbababbbABABBBBABabaaaBaBabbb" ++
      "aaabbABAbabbbbababbABAbabbbbababABABBBBABabaBABABBBBABabaBBABABBBBABabaBBAAABBBA" ++
      "bAbAABABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAAABABBBBABabaBABABBBBABabaBBABABBBB" ++
      "ABabaBBAAABBBAbAbAAAbbbaBBBAABABBBBABabaaaBaBabbbaaabbABAbabbbbababbABAbabbbbaba" ++
      "bABABBBBABabaBABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAABABABBBBABabaBBABABBBBABab" ++
      "aBBAAABBBAbAbAAABABBBBABabaBABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAAAbbbaBBBaBaB" ++
      "abbbaaabbABAbabbbbababbABAbabbbbababABAbabbbbabaBAABBAbbABaaBaBabbbaaabbABAbabbb" ++
      "bababbABAbabbbbababbbABABBBBABabaaaBaBabbbaaabbABAbabbbbababbABAbabbbbababABABBB" ++
      "BABabaBABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAABABABBBBABabaBBABABBBBABabaBBAAAB" ++
      "BBAbAbAAABABBBBABabaBABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAAAbbbaBBBAABABBBBABa" ++
      "baaaBaBabbbaaabbABAbabbbbababbABAbabbbbababABABBBBABabaBABABBBBABabaBBABABBBBABa" ++
      "baBBAAABBBAbAbAABABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAAABABBBBABabaBABABBBBABa" ++
      "baBBABABBBBABabaBBAAABBBAbAbAAAbbbaBBBaBaBabbbaaabbABAbabbbbababbABAbabbbbababAB" ++
      "AbabbbbabaBAABBAbbABaaBaBabbbaaabbABAbabbbbababbABAbabbbbababbbABABBBBABabaaaBaB" ++
      "abbbaaabbABAbabbbbababbABAbabbbbababABABBBBABabaBABABBBBABabaBBABABBBBABabaBBAAA" ++
      "BBBAbAbAABABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAAABABBBBABabaBABABBBBABabaBBABA" ++
      "BBBBABabaBBAAABBBAbAbAAAbbbaBBBAABABBBBABabaaaBaBabbbaaabbABAbabbbbababbABAbabbb" ++
      "bababABABBBBABabaBABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAABABABBBBABabaBBABABBBB" ++
      "ABabaBBAAABBBAbAbAAABABBBBABabaBABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAAAbbbaBBB" ++
      "aBaBabbbaaabbABAbabbbbababbABAbabbbbabababbbABBBaaaBaBabbbaaabbABAbabbbbababbABA" ++
      "babbbbababABAbabbbbabaaaBaBabbbaaabbABAbabbbbababbABAbabbbbababaaBaBabbbaaabbABA" ++
      "babbbbababbABAbabbbbababABAbabbbbabaBABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAAABA" ++
      "babbbbabaaaBaBabbbaaabbABAbabbbbababbABAbabbbbababABABBBBABababaaBaBabbbaaabbABA" ++
      "babbbbababbABAbabbbbabababbbABBBaaaBaBabbbaaabbABAbabbbbababbABAbabbbbababABAbab" ++
      "bbbabaaaBaBabbbaaabbABAbabbbbababbABAbabbbbababaaBaBabbbaaabbABAbabbbbababbABAba" ++
      "bbbbababABAbabbbbabaBABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAAABAbabbbbabababbAba" ++
      "bbAAAABABBBAbabbbbabaaaBaBabbbaaabbABAbabbbbababbABAbabbbbaBBBABabaaaBaBabbbaaab" ++
      "bABAbabbbbababbABAbabbbbababABABBBBABabaBABABBBBABabaBBABABBBBABabaBBAAABBBAbAbA" ++
      "ABABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAAABABBBBABabaBABABBBBABabaBBABABBBBABab" ++
      "aBBAAABBBAbAbAAAbbbaBBBABABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAAABAbabbbbabaabb" ++
      "bABBBaaaBaBabbbaaabbABAbabbbbababbABAbabbbbababABAbabbbbabaaaBaBabbbaaabbABAbabb" ++
      "bbababbABAbabbbbababaaBaBabbbaaabbABAbabbbbababbABAbabbbbababABAbabbbbabaBABABBB" ++
      "BABabaBBABABBBBABabaBBAAABBBAbAbAAABAbabbbbabaBAABBAbbABaaBaBabbbaaabbABAbabbbba" ++
      "babbABAbabbbbababbbABABBBBABabaaaBaBabbbaaabbABAbabbbbababbABAbabbbbababABABBBBA" ++
      "BabaBABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAABABABBBBABabaBBABABBBBABabaBBAAABBB" ++
      "AbAbAAABABBBBABabaBABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAAAbbbaBBBAABABBBBABaba" ++
      "aaBaBabbbaaabbABAbabbbbababbABAbabbbbababABABBBBABabaBABABBBBABabaBBABABBBBABaba" ++
      "BBAAABBBAbAbAABABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAAABABBBBABabaBABABBBBABaba" ++
      "BBABABBBBABabaBBAAABBBAbAbAAAbbbaBBBaBaBabbbaaabbABAbabbbbababbABAbabbbbababaaBa" ++
      "BabbbaaabbABAbabbbbababbABAbabbbbababABABBBBABabaBABABBBBABabaBBABABBBBABabaBBAA" ++
      "ABBBAbAbAABABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAAABABBBBABabaBABABBBBABabaBBAB" ++
      "ABBBBABabaBBAAABBBAbAbAAAbbbaBBBAbbAAAABABBBAbabbbbabaaaBaBabbbaaabbABAbabbbbaba" ++
      "bbABAbabbbbaBBBABabaaaBaBabbbaaabbABAbabbbbababbABAbabbbbababABABBBBABabaBABABBB" ++
      "BABabaBBABABBBBABabaBBAAABBBAbAbAABABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAAABABB" ++
      "BBABabaBABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAAAbbbaBBBABABABBBBABabaBBABABBBBA" ++
      "BabaBBAAABBBAbAbAAABAbabbbbabaabbbABBBaaaBaBabbbaaabbABAbabbbbababbABAbabbbbabab" ++
      "ABAbabbbbabaaaBaBabbbaaabbABAbabbbbababbABAbabbbbababaaBaBabbbaaabbABAbabbbbabab" ++
      "bABAbabbbbababABAbabbbbabaBABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAAABAbabbbbabaB" ++
      "AABBAbbABaaBaBabbbaaabbABAbabbbbababbABAbabbbbababbbABABBBBABabaaaBaBabbbaaabbAB" ++
      "AbabbbbababbABAbabbbbababABABBBBABabaBABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAABA" ++
      "BABBBBABabaBBABABBBBABabaBBAAABBBAbAbAAABABBBBABabaBABABBBBABabaBBABABBBBABabaBB" ++
      "AAABBBAbAbAAAbbbaBBBAABABBBBABabaaaBaBabbbaaabbABAbabbbbababbABAbabbbbababABABBB" ++
      "BABabaBABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAABABABBBBABabaBBABABBBBABabaBBAAAB" ++
      "BBAbAbAAABABBBBABabaBABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAAAbbbaBBBaBaBabbbaaa" ++
      "bbABAbabbbbababbABAbabbbbababABAbabbbbabaaaBaBabbbaaabbABAbabbbbababbABAbabbbbab" ++
      "abABABBBBABaaBBABABABBBBABabaaaBaBabbbaaabbABAbabbbbababbABAbabbbbababABABBBBABa" ++
      "baBABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAABABABBBBABabaBBABABBBBABabaBBAAABBBAb" ++
      "AbAAABABBBBABabaBABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAAAbbbaBBBABABABBBBABabaB" ++
      "BABABBBBABabaBBAAABBBAbAbAABABAbabbbbabaBABABBBBABabaBBABABBBBABabaBBAAABBBAbAbA" ++
      "AABABBBBABabaaaBaBabbbaaabbABAbabbbbababbABAbabbbbababABABBBBABabaBABABBBBABabaB" ++
      "BABABBBBABabaBBAAABBBAbAbAABABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAAABABBBBABaba" ++
      "BABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAAAbbbaBBBABABABBBBABabaBBABABBBBABabaBBA" ++
      "AABBBAbAbAbbbABBBaaaBaBabbbaaabbABAbabbbbababbABAbabbbbababABAbabbbbabaaaBaBabbb" ++
      "aaabbABAbabbbbababbABAbabbbbababaaBaBabbbaaabbABAbabbbbababbABAbabbbbababABAbabb" ++
      "bbabaBABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAAABAbabbbbabaabbbABBBaaaBaBabbbaaab" ++
      "bABAbabbbbababbABAbabbbbababABAbabbbbabaaaBaBabbbaaabbABAbabbbbababbABAbabbbbaba" ++
      "baaBaBabbbaaabbABAbabbbbababbABAbabbbbababABAbabbbbabaBABABBBBABabaBBABABBBBABab" ++
      "aBBAAABBBAbAbAAABAbabbbbabaBBBABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAAbaBBabbaab" ++
      "ABABBBBABabaBABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAbbbABBBaaaBaBabbbaaabbABAbab" ++
      "bbbababbABAbabbbbababABAbabbbbabaaaBaBabbbaaabbABAbabbbbababbABAbabbbbababaaBaBa" ++
      "bbbaaabbABAbabbbbababbABAbabbbbababABAbabbbbabaBABABBBBABabaBBABABBBBABabaBBAAAB" ++
      "BBAbAbAAABAbabbbbabaabbbABBBaaaBaBabbbaaabbABAbabbbbababbABAbabbbbababABAbabbbba" ++
      "baaaBaBabbbaaabbABAbabbbbababbABAbabbbbababaaBaBabbbaaabbABAbabbbbababbABAbabbbb" ++
      "ababABAbabbbbabaBABABBBBABabaBBABABBBBABabaBBAAABBBAbAbAAABAbabbbbabaBBBABABBBBA" ++
      "BabaBBABABBBBABabaBBAAABBBAbAbAAbaBBabbaabABaaBaBabbbaaabbABAbabbbbababbABAbabbb" ++
      "bababbABabAbaB")]

@[expose] def basisTinv : Array V := #[
    ⟨49680, 926122⟩,
    ⟨573526, 1456384⟩,
    ⟨1443856, 30055⟩,
    ⟨545344, 404876⟩,
    ⟨262429, 1640450⟩,
    ⟨1316178, 116741⟩,
    ⟨1966564, 124442⟩,
    ⟨1313280, 83268⟩,
    ⟨924865, 33566⟩,
    ⟨771224, 1049155⟩,
    ⟨1192000, 543160⟩,
    ⟨65588, 174144⟩,
    ⟨1622433, 69136⟩,
    ⟨91016, 662628⟩,
    ⟨336139, 1065588⟩,
    ⟨1762528, 268820⟩,
    ⟨1770160, 321856⟩,
    ⟨594944, 1220868⟩,
    ⟨1475345, 24750⟩,
    ⟨853560, 1212483⟩,
    ⟨591884, 34387⟩]

@[expose] def subRoot (_ : Unit := ()) : Nat := 2

end CFSG.Sporadic.McL.Native
