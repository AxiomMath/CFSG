module

public import Certificates.Data.SuzB0TwistInputs
public import CFSG.Sporadic.SuzRecog.ModelGroupsChecks

public section

namespace CFSG.Sporadic.SuzRecog.B0TwistCheck

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog.LevelTwoData
  CFSG.Sporadic.SuzRecog.ModelGroupsCheck CFSG.Sporadic.SuzRecog.B0TwistData CFSG.CosetTable

@[expose] def twGens : Array (Array Nat) := #[h1Arr, h2Arr, rhoArr, aArr, bArr, tauArr, w0Arr]

@[expose] def twGensT : Array (Array Nat) :=
  #[h1Arr, h2Arr, rhoArr, aArr, bArr, compA 1782 tauArr t1A, w0Arr]

@[expose] def twCodeA (S : Array (Array Nat)) (c : Nat) : Array Nat :=
  if c % 2 = 0 then S[c / 2]! else invCand 1782 S[c / 2]!

@[expose] def twWordA (S : Array (Array Nat)) : List Nat → Array Nat
  | [] => idA 1782
  | c :: w => compA 1782 (twCodeA S c) (twWordA S w)

@[expose] def twRhoPowA : Nat → Array Nat
  | 0 => idA 1782
  | k + 1 => compA 1782 rhoArr (twRhoPowA k)

@[expose] def twEvenAt (x : Array Nat) (k : Nat) : Bool :=
  commA (compA 1782 x (twRhoPowA k)) w0Arr && commA (compA 1782 x (twRhoPowA k)) w1A

@[expose] def twMemOK : Prop :=
  ∀ (G : Type) [Group G] (gen : ℕ → G),
    (∀ x < 14, gen (CFSG.Certificates.CosetEnumeration.invCode x) = (gen x)⁻¹) →
    (∀ r ∈ twRels, CFSG.Certificates.CosetEnumeration.evalWord gen r = 1) →
    gen 12 ∈ Subgroup.closure (gen '' {c | c ∈ [0, 2, 4, 6, 8, 10]})

@[expose] def twPermsOK : Bool :=
  permOK h1Arr && permOK h2Arr && permOK aArr && permOK bArr && permOK tauArr

@[expose] def twMembersOK : Bool :=
  inM h1Arr && inM h2Arr && inM aArr && inM bArr && inM tauArr

@[expose] def twCommOK : Bool :=
  commA h1Arr rhoArr && commA h1Arr t1A && commA h2Arr rhoArr && commA h2Arr t1A &&
    commA aArr rhoArr && commA aArr w0Arr && commA aArr w1A &&
    commA bArr rhoArr && commA bArr w0Arr && commA bArr w1A && commA tauArr t1A

@[expose] def twTauOK : Bool :=
  normR0 tauArr && eqA 1782 (conjA tauArr rhoArr) (invCand 1782 rhoArr) &&
    !twEvenAt tauArr 0 && !twEvenAt tauArr 1 && !twEvenAt tauArr 2

@[expose] def twRelsOK : Bool :=
  (relsC ++ relsN).all (fun w => eqA 1782 (twWordA twGens w) (idA 1782)) &&
    (relsT ++ [relX]).all fun w => eqA 1782 (twWordA twGensT w) (idA 1782)

end CFSG.Sporadic.SuzRecog.B0TwistCheck
