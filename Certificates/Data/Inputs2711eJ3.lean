module

public import Certificates.Data.Inputs2711eGen
public import CFSG.RankThree.Asc83Table.J3Data
public import Certificates.Data.CFSGNative.SectionRank.F2Fast
public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711e

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native CFSG.Blueprint

@[expose] def j3GenProg : List Op := [
      .pow 1 0 2, .pow 2 1 3, .pow 1 0 4, .mul 4 1 4, .mul 4 0 4, .mul 4 1 4, .mul 4 0 4,
      .mul 4 1 4, .mul 4 2 4, .mul 4 1 4, .mul 4 2 4, .mul 4 3 4, .mul 4 2 4, .mul 4 1 4,
      .mul 4 2 4, .mul 4 3 4, .mul 4 2 4, .mul 4 3 4, .mul 4 2 4, .mul 4 1 4, .mul 4 2 4,
      .mul 4 3 4, .mul 4 2 4, .mul 4 3 4, .mul 4 2 4, .mul 4 3 4, .mul 4 2 4, .mul 4 3 4,
      .mul 4 2 4, .mul 4 1 4, .mul 4 2 4, .mul 4 1 4, .mul 4 2 4, .mul 4 1 4, .mul 4 2 4,
      .mul 4 3 4, .mul 4 2 4, .mul 4 3 4, .mul 4 2 4, .mul 4 3 4, .mul 4 2 4, .mul 4 1 4,
      .mul 4 2 4, .mul 4 1 4, .mul 4 2 4, .mul 4 1 4, .mul 4 2 4, .mul 4 3 4, .mul 4 2 4,
      .mul 4 3 4, .mul 4 2 4, .mul 4 1 4, .mul 4 2 4, .mul 4 1 4, .mul 4 2 4, .mul 4 1 4,
      .pow 1 1 5, .mul 5 0 5, .mul 5 1 5, .mul 5 2 5, .mul 5 3 5, .mul 5 2 5, .mul 5 3 5,
      .mul 5 2 5, .mul 5 1 5, .mul 5 2 5, .mul 5 1 5, .mul 5 2 5, .mul 5 3 5, .mul 5 2 5,
      .mul 5 1 5, .mul 5 2 5, .mul 5 3 5, .mul 5 2 5, .mul 5 1 5, .mul 5 2 5, .mul 5 3 5,
      .mul 5 2 5, .mul 5 1 5, .mul 5 1 5, .mul 5 0 5, .mul 5 1 5, .mul 5 1 5, .mul 5 0 5,
      .mul 5 1 5, .mul 5 1 5, .mul 5 0 5, .mul 5 1 5, .mul 5 0 5, .mul 5 1 5, .mul 5 0 5,
      .mul 5 3 5, .mul 5 0 5, .mul 5 3 5, .mul 5 0 5, .mul 5 3 5, .mul 5 2 5, .mul 5 1 5,
      .mul 5 2 5, .mul 5 1 5, .mul 5 2 5, .mul 5 1 5, .mul 5 2 5, .mul 5 3 5, .mul 5 2 5,
      .mul 5 3 5, .mul 5 2 5, .mul 5 3 5, .mul 5 2 5, .mul 5 3 5, .mul 5 2 5, .mul 5 3 5,
      .mul 5 2 5, .mul 5 1 5, .mul 5 2 5, .pow 1 0 6, .mul 6 3 6, .mul 6 0 6, .mul 6 1 6,
      .mul 6 0 6, .mul 6 1 6, .mul 6 0 6, .mul 6 3 6, .mul 6 0 6, .mul 6 3 6, .mul 6 0 6,
      .mul 6 1 6, .mul 6 0 6, .mul 6 3 6, .mul 6 0 6, .mul 6 1 6, .mul 6 0 6, .mul 6 3 6,
      .mul 6 0 6, .mul 6 3 6, .mul 6 0 6, .mul 6 1 6, .mul 6 0 6, .mul 6 3 6, .mul 6 0 6,
      .mul 6 1 6, .mul 6 0 6, .mul 6 1 6, .mul 6 0 6, .mul 6 3 6, .mul 6 0 6, .mul 6 3 6,
      .mul 6 2 6, .mul 6 3 6, .mul 6 3 6, .mul 6 2 6, .mul 6 3 6, .mul 6 0 6, .mul 6 3 6,
      .mul 6 2 6, .mul 6 3 6, .mul 6 3 6, .mul 6 2 6, .mul 6 3 6, .mul 6 3 6, .mul 6 0 6,
      .mul 6 3 6, .mul 6 2 6, .mul 6 3 6, .mul 6 3 6, .mul 6 2 6, .mul 6 3 6, .mul 6 3 6,
      .mul 6 0 6, .mul 6 1 6, .mul 6 0 6, .mul 6 3 6, .mul 6 0 6, .mul 6 3 6, .mul 6 0 6,
      .mul 6 1 6, .mul 6 0 6, .mul 6 3 6, .mul 6 0 6, .mul 6 1 6, .mul 6 0 6, .mul 6 1 6,
      .mul 6 0 6, .mul 6 1 6, .mul 6 0 6, .mul 6 3 6, .mul 6 0 6, .mul 6 3 6, .mul 6 2 6,
      .mul 6 3 6, .mul 6 2 6, .mul 6 3 6, .pow 1 3 7, .mul 7 0 7, .mul 7 3 7, .mul 7 0 7,
      .mul 7 1 7, .mul 7 0 7, .mul 7 3 7, .mul 7 0 7, .mul 7 3 7, .mul 7 0 7, .mul 7 1 7,
      .mul 7 0 7, .mul 7 3 7, .mul 7 0 7, .mul 7 3 7, .mul 7 0 7, .mul 7 1 7, .mul 7 0 7,
      .mul 7 1 7, .mul 7 0 7, .mul 7 3 7, .mul 7 0 7, .mul 7 1 7, .mul 7 0 7, .mul 7 3 7,
      .mul 7 0 7, .mul 7 3 7, .mul 7 0 7, .mul 7 1 7, .mul 7 0 7, .mul 7 1 7, .mul 7 0 7,
      .mul 7 3 7, .mul 7 0 7, .mul 7 1 7, .mul 7 0 7, .mul 7 1 7, .mul 7 0 7, .mul 7 3 7,
      .mul 7 0 7, .mul 7 3 7, .mul 7 0 7, .mul 7 1 7, .mul 7 0 7, .mul 7 3 7, .mul 7 0 7,
      .mul 7 1 7, .mul 7 0 7, .mul 7 3 7, .mul 7 0 7, .mul 7 3 7, .mul 7 2 7, .mul 7 1 7,
      .mul 7 2 7, .mul 7 3 7, .mul 7 2 7, .mul 7 3 7, .mul 7 3 7, .mul 7 0 7, .mul 7 1 7,
      .mul 7 0 7, .mul 7 1 7, .mul 7 0 7, .mul 7 3 7, .mul 7 0 7, .mul 7 3 7, .mul 7 0 7,
      .mul 7 1 7, .mul 7 0 7, .mul 7 3 7, .mul 7 0 7, .mul 7 1 7, .mul 7 0 7, .mul 7 1 7,
      .mul 7 0 7, .mul 7 3 7, .mul 7 0 7, .mul 7 1 7, .mul 7 0 7, .mul 7 3 7, .mul 7 0 7,
      .mul 7 1 7, .mul 7 0 7, .mul 7 1 7, .mul 7 0 7, .mul 7 3 7, .mul 7 0 7, .mul 7 3 7,
      .mul 7 2 7, .mul 7 3 7, .mul 7 3 7, .mul 7 2 7, .mul 7 3 7, .mul 7 3 7, .mul 7 0 7,
      .mul 7 1 7, .mul 7 0 7, .mul 7 3 7, .mul 7 0 7, .mul 7 3 7, .mul 7 0 7, .mul 7 3 7,
      .mul 7 0 7, .mul 7 3 7, .mul 7 0 7, .mul 7 3 7, .mul 7 0 7, .mul 7 1 7, .mul 7 0 7,
      .mul 7 3 7, .mul 7 0 7, .mul 7 3 7, .mul 7 0 7, .mul 7 3 7, .mul 7 2 7, .mul 7 3 7,
      .mul 7 2 7, .mul 7 3 7, .pow 1 1 8, .mul 8 1 8, .mul 8 0 8, .mul 8 1 8, .mul 8 0 8,
      .mul 8 3 8, .mul 8 2 8, .mul 8 3 8, .mul 8 2 8, .mul 8 1 8, .mul 8 2 8, .mul 8 1 8,
      .mul 8 2 8, .mul 8 3 8, .mul 8 2 8, .mul 8 3 8, .mul 8 2 8, .mul 8 1 8, .mul 8 2 8,
      .mul 8 3 8, .mul 8 2 8, .mul 8 1 8, .mul 8 2 8, .mul 8 3 8, .mul 8 3 8, .mul 8 0 8,
      .mul 8 3 8, .mul 8 0 8, .mul 8 1 8, .mul 8 0 8, .mul 8 1 8, .mul 8 0 8, .mul 8 3 8,
      .mul 8 2 8, .mul 8 3 8, .mul 8 2 8, .mul 8 3 8, .mul 8 2 8, .mul 8 1 8, .mul 8 2 8,
      .mul 8 1 8, .mul 8 2 8, .mul 8 1 8, .mul 8 2 8, .mul 8 3 8, .mul 8 2 8, .mul 8 3 8,
      .mul 8 2 8, .mul 8 1 8, .mul 8 2 8, .mul 8 1 8, .mul 8 2 8, .mul 8 3 8, .pow 1 0 9,
      .mul 9 3 9, .mul 9 0 9, .mul 9 1 9, .mul 9 0 9, .mul 9 3 9, .mul 9 0 9, .mul 9 3 9,
      .mul 9 0 9, .mul 9 1 9, .mul 9 0 9, .mul 9 3 9, .mul 9 0 9, .mul 9 3 9, .mul 9 0 9,
      .mul 9 1 9, .mul 9 0 9, .mul 9 3 9, .mul 9 0 9, .mul 9 3 9, .mul 9 0 9, .mul 9 1 9,
      .mul 9 0 9, .mul 9 3 9, .mul 9 0 9, .mul 9 3 9, .mul 9 0 9, .mul 9 1 9, .mul 9 0 9,
      .mul 9 1 9, .mul 9 0 9, .mul 9 3 9, .mul 9 2 9, .mul 9 3 9, .mul 9 3 9, .mul 9 2 9,
      .mul 9 3 9, .mul 9 3 9, .mul 9 0 9, .mul 9 1 9, .mul 9 0 9, .mul 9 3 9, .mul 9 0 9,
      .mul 9 1 9, .mul 9 0 9, .mul 9 1 9, .mul 9 0 9, .mul 9 1 9, .mul 9 0 9, .mul 9 1 9,
      .mul 9 0 9, .mul 9 1 9, .mul 9 0 9, .mul 9 3 9, .mul 9 0 9, .mul 9 3 9, .mul 9 0 9,
      .mul 9 1 9, .mul 9 2 9, .mul 9 3 9, .mul 9 2 9, .mul 9 3 9, .mul 9 2 9]

@[expose] def j3GenGens : List GenItem := [⟨6, 5, [4]⟩, ⟨7, 4, [4]⟩, ⟨8, 4, [5]⟩, ⟨9, 5, [5]⟩]

@[expose] def j3GenWA : Word := [
      (8, 3), (6, 4), (8, 1), (7, 2), (8, 3), (6, 1), (8, 1), (6, 4), (7, 1), (9, 2), (7, 3),
      (8, 3), (7, 1), (9, 4), (7, 3), (9, 1), (7, 3), (9, 4), (7, 1), (6, 3)]

@[expose] def j3GenWB : Word := [
      (6, 1), (8, 3), (9, 1), (8, 1), (9, 4), (6, 4), (8, 2), (7, 3), (6, 1), (9, 1), (7, 1),
      (9, 1), (8, 1)]

@[expose] def j3GenData : GenData where
  nregs := 10
  prog := j3GenProg
  oA := 2
  oB := 3
  fixOrd := [(4, 3), (5, 3)]
  gens := j3GenGens
  der := []
  wA := j3GenWA
  wB := j3GenWB
  extra := []

@[expose] def j3GenCross : Bool :=
  let O := ops2fr 80
  let R := O.regsOf NativeSporadic.J3Seed1 NativeSporadic.J3Seed2 j3GenData.nregs j3GenData.prog
  let R' := O.regsOf NativeSporadic.J3Seed1 NativeSporadic.J3Seed2
    CFSG.RankThree.Asc83Table.J3.j3Cert.nregs CFSG.RankThree.Asc83Table.J3.j3Cert.prog
  O.eq R[4]! (evalW O R' (basisW CFSG.RankThree.Asc83Table.J3.j3Cert.rb 9)) &&
    O.eq R[5]! (evalW O R' (basisW CFSG.RankThree.Asc83Table.J3.j3Cert.rb 10))

@[expose] def j3GenCheck : Bool :=
  genCheck (ops2fr 80) 3 NativeSporadic.J3Seed1 NativeSporadic.J3Seed2 j3GenData && j3GenCross

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2711e
