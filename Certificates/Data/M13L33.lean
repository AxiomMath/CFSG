module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenAInputs
public import Certificates.Data.M13L33Rels
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenInputs
public import CFSG.YGroups.DCE.MaximalB
public import CFSG.YGroups.Y443.Native.AlignB
public import CFSG.YGroups.Y443.Native.AlignW
public import CFSG.YGroups.Y443.Native.CosetData
public import CFSG.YGroups.Y443.Native.Image

public section

namespace CFSG.HardMathSupport.Dickson.BMRows.M13L33

open CFSG.Monster CFSG.Monster.AxisCount CFSG.AGLEmbedding.Norton.MON5_7
  CFSG.AGLEmbedding.Norton.GenD13 CFSG.AGLEmbedding.Norton.MON11_13 CFSG.YGroups.Y443
  CFSG.YGroups.Y443Native CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterEleven
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThreeBNF
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteen

@[expose] def yW : List Native.Gen :=
  [.tau, .tau, .rho (false, 4073, 240), .tau, .rho (true, 1353, 185), .rho (false, 0, 54),
    .perm #[9, 17, 20, 19, 22, 14, 12, 11, 21, 10, 4, 7, 18, 13, 1, 5, 23, 8, 3, 2, 16, 15, 6, 0],
    .xi, .rho (false, 0, 58),
    .perm #[0, 5, 6, 7, 1, 2, 3, 4, 8, 16, 12, 20, 22, 14, 18, 10, 19, 11, 23, 15, 13, 21, 9, 17],
    .xi, .rho (false, 0, 6),
    .perm #[1, 2, 13, 14, 17, 19, 23, 22, 0, 3, 12, 15, 18, 16, 21, 20, 5, 10, 6, 9, 4, 8, 11, 7]]

@[expose] def yIW : List Native.Gen :=
  [.tau, .tau, .rho (false, 1641, 3200), .tau, .rho (true, 1568, 222), .rho (false, 0, 3830),
    .rho (false, 0, 52),
    .perm #[20, 4, 7, 10, 23, 15, 11, 13, 9, 21, 17, 19, 16, 2, 5, 14, 18, 3, 12, 6, 22, 8, 0, 1],
    .xi, .rho (false, 0, 58),
    .perm #[0, 5, 6, 7, 1, 2, 3, 4, 8, 16, 12, 20, 22, 14, 18, 10, 19, 11, 23, 15, 13, 21, 9, 17],
    .xi, .rho (false, 0, 40),
    .perm #[10, 11, 14, 15, 18, 19, 22, 23, 0, 4, 5, 1, 7, 2, 6, 3, 21, 20, 17, 16, 13, 12, 9, 8]]

@[expose] def letterW (l : Fin 2 × Bool) : List Native.Gen :=
  if l.1 = 0 then j1W else if l.2 then yW else yIW

@[expose] def relW (r : List (Fin 2 × Bool)) : List Native.Gen := (r.reverse.map letterW).flatten

@[expose] def l33Pairs : List (List Native.Gen × List Native.Gen) :=
  [(yW ++ yIW, []), (thirteenX ++ yW, yW ++ thirteenX), (thirteenX ++ j1W, j1W ++ thirteenX)] ++
    l33Rels.map fun r => (relW r, [])

@[expose] def l33Check (_ : Unit := ()) : Bool := agreeAll l33Pairs && movesSome j1W

end CFSG.HardMathSupport.Dickson.BMRows.M13L33
