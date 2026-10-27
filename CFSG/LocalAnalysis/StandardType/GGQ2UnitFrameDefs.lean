module

public import CFSG.LocalAnalysis.StandardType.GGQ2UnitRaw
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeBlock
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagProj
public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl

public section

namespace CFSG.StandardType.GGQ2Frame.UnitPlacement

open CFSG CFSG.Assembly CFSG.StandardType Matrix CFSG.ClassicalGroups.UnitaryFlag
open CFSG.SectionRank.OddCover (diagHom)
open CFSG.Open (IsElemAbelian)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

variable {G : Type} [Group G] {H E : Subgroup G} {N : ℕ} {K : Type} [Field K]
  {hEN : E ≤ Subgroup.normalizer (H : Set G)} {ζ : Multiplicative (ZMod 3) →* Kˣ}

@[expose] def diagOf (ζ : Multiplicative (ZMod 3) →* Kˣ) (w : UnitRaw.W N) : GL (Fin N) K :=
  diagHom N (fun i => ζ (Multiplicative.ofAdd (w i)))

@[expose] def blockPSU (S : Finset (Fin N)) : Subgroup (LargeEvenProj (unitarySU 2 1 K N)) :=
  (TableBUE.blockSU (K := K) (n := 1) S).map (LargeEvenProjMk (unitarySU 2 1 K N))

structure UnitFrame (H E : Subgroup G) (hEN : E ≤ Subgroup.normalizer (H : Set G)) (K : Type)
    [Field K] (N : ℕ) (ζ : Multiplicative (ZMod 3) →* Kˣ) : Type where
  π : ↥H →* LargeEvenProj (unitarySU 2 1 K N)
  surj : Function.Surjective π
  ker_le : π.ker ≤ Subgroup.center ↥H
  ι : Additive ↥E →+ UnitRaw.Vfull N
  inj : Function.Injective ι
  intertwine : ∀ (b : ↥E) (w : UnitRaw.W N), (UnitRaw.oneLine N).mkQ w = ι (Additive.ofMul b) →
    ∃ hD : diagOf ζ w ∈ Subgroup.normalizer (unitarySU 2 1 K N : Set (GL (Fin N) K)),
      ∀ h : ↥H, π (H.normalizerMonoidHom ⟨(b : G), hEN b.2⟩ h) =
        TableB.projConj (unitarySU 2 1 K N) ⟨diagOf ζ w, hD⟩ (π h)

@[expose] def UnitFrame.image (fr : UnitFrame H E hEN K N ζ) (X : Subgroup G) :
    Submodule (ZMod 3) (UnitRaw.Vfull N) :=
  AddSubgroup.toZModSubmodule 3 ((X.subgroupOf E).toAddSubgroup.map fr.ι)

@[expose] def UnitFrame.component (fr : UnitFrame H E hEN K N ζ) (S : Finset (Fin N)) :
    Subgroup G :=
  (⁅(blockPSU (K := K) S).comap fr.π, (blockPSU (K := K) S).comap fr.π⁆).map H.subtype

structure UnitCtx (H E : Subgroup G) (hEN : E ≤ Subgroup.normalizer (H : Set G)) (K : Type)
    [Field K] (N : ℕ) (ζ : Multiplicative (ZMod 3) →* Kˣ) : Type where
  fr : UnitFrame H E hEN K N ζ
  hK : Nat.card K = 4
  hζ : Function.Injective ζ
  hHp : commutator H = ⊤
  hEab : IsElemAbelian 3 E
  hC3 : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (H : Set G))
  hN : 5 ≤ N
  innerDiag : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twA, N - 1, 1⟩) 3 E H
  range : fr.ι.range = ⊤ ∨ (3 ∣ N ∧ fr.ι.range = (UnitRaw.heart N).toAddSubgroup)

end

end CFSG.StandardType.GGQ2Frame.UnitPlacement
