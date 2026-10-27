module

public import CFSG.Quasithin.Background.SmithB45MatIndDefs
public import Certificates.Data.SmithB45MatM22Mod
public import CFSG.Quasithin.Background.HMathieuNormInputs

public section

namespace CFSG.Quasithin.B45Mat.Ind

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.B45Mat.M22 CFSG.Sporadic.Mathieu
  CFSG.QuasithinUnique.Setup.X3E CFSG.Quasithin.H13.A5.M22Hat

@[expose] def amalH1 : ℕ :=
  24604395

@[expose] def amalH2 : ℕ :=
  95251373

@[expose] def amalHP1 : ℕ :=
  882523

@[expose] def amalHP2 : ℕ :=
  8243624663

@[expose] def amalU : ℕ :=
  5489667868

@[expose] def amalGW : List ℕ :=
  [1, 2, 3, 4, 6, 5, 7, 8, 12, 10, 9, 13, 11, 16, 24, 20, 28, 18, 26, 17, 25, 21, 29, 19, 27, 48,
   40, 56, 36, 52, 44, 34, 42, 58]

@[expose] def amalMasks : List ℕ :=
  [3939313485, 10918166038, 3642434010, 6534450433, 9545805046, 10337244935, 8678690456,
   13372305213, 14426360226, 2935195707, 15397354156, 4855027563, 1168359773, 4087934417,
   12918241752, 4249518839, 16813113897, 7706826857, 2208904606, 14934710864, 9021196454,
   5489204478, 106068832, 15006123155, 16668277450, 10093438469, 3787862995, 1128903363,
   16202916265, 15416457876, 3557273565, 10672090844, 15317917818, 8048958489]

@[expose] def amalP1 : List ℕ :=
  [14, 2, 6]

@[expose] def amalP2 : List ℕ :=
  [90, 2, 3, 4, 5, 10, 13, 11, 29, 19, 40, 58]

@[expose] def amalL1 : List ℕ :=
  [12972413776, 9504450443, 11189909599, 16379325298, 0, 817178274, 0, 0, 0, 12568486548,
   12032245206, 12226707384, 13488626694, 0, 0, 0, 0, 12640828042, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0]

@[expose] def amalL2 : List ℕ :=
  [648541896, 16352591043, 16468777873, 3654525353, 15672781318, 12495516575, 868410359,
   15961203807, 928121270, 9959049267, 14138039160, 4222361874, 3086877214, 12832157821,
   7906744236, 5849355162, 6120325916, 4405098893, 1369195831, 2526615040, 2893598759, 0, 0,
   15638803092, 0, 3692913328, 14412281182, 0, 0, 0, 0, 0, 0, 0]

@[expose] def amalRelOK : Bool :=
  let a := psiArr (m22a : Equiv.Perm (Fin 22))
  let b := psiArr (m22b : Equiv.Perm (Fin 22))
  [(amalH1, amalHP1), (amalH2, amalHP2)].all fun p =>
    comp24 m23AArr (wordArr a b (decW p.2)) == comp24 (wordArr a b (decW p.1)) m23AArr

@[expose] def amalMat : (Bool → List ℕ) → ℕ → List ℕ :=
  fun c w => (List.range 34).map fun k => wapp 34 c (decW w) (1 <<< k)

@[expose] def amalCore : List ℕ → List ℕ → Bool :=
  fun ca cb =>
    let c : Bool → List ℕ := fun z => if z then cb else ca
    let A₀ := amalMat c amalHP1
    let A₁ := amalMat c amalHP2
    let B₀ := amalMat c amalH1
    let B₁ := amalMat c amalH2
    homZeroOK 34 (fun z => if z then A₁ else A₀) (fun z => if z then B₁ else B₀) amalU
      (amalGW.map decW) amalMasks (amalP1.map decW) (amalP2.map decW) amalL1 amalL2

@[expose] def amalOK : Bool :=
  amalRelOK && amalCore (packCols (tab34 m22a)) (packCols (tab34 m22b))

end CFSG.Quasithin.B45Mat.Ind
