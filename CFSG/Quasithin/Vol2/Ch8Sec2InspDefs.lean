module

public import CFSG.Quasithin.Vol2.Ch8Sec2HFactsC
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3Delta5
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasicBase

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native
  CFSG.QuasithinUnique.A5.G3

@[expose] def VzModL34 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] (H : Subgroup (MulAut V)) (z : V),
    BinaryNineTensor H ⊤ ⊥ 1 → z ≠ 1 → IsSylowVec82 H z →
    ∃ (α : ↥(parz82 H z) →* ↥(alternatingGroup (Fin 5)))
      (β : V →* Multiplicative (evenWeight 5)),
      Function.Surjective α ∧ α.ker = (radz82 H z).subgroupOf (parz82 H z) ∧
      Function.Surjective β ∧ β.ker = vz82 H z ∧
      ∀ (p : ↥(parz82 H z)) (v : V) (i : Fin 5),
        ((Multiplicative.toAdd (β ((p : MulAut V) v)) : evenWeight 5) : Fin 5 → ZMod 2) i =
          ((Multiplicative.toAdd (β v) : evenWeight 5) : Fin 5 → ZMod 2)
            (((α p : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5))⁻¹ i)

@[expose] def InspL34 : Prop :=
  ∀ (Y : Type) [Group Y], SQTKHypCat Y → ∀ T : Subgroup Y, IsSylowTwoOf T ⊤ →
    ∀ B ∈ lFamily T, T ≤ Subgroup.normalizer (B : Set Y) → ¬ IsDelta5Group ↥B

@[expose] def InspCode22 : Prop :=
  ∀ (Y : Type) [Group Y], SQTKHypCat Y → ∀ T : Subgroup Y, IsSylowTwoOf T ⊤ →
    ∀ B ∈ lFamily T, Nat.card (ModO2 B) = 360 → Nat.card ↥(CFSG.pCore 2 ↥B) = 2 ^ 5 → False

@[expose] def InspCocode24 : Prop :=
  ∀ (Y : Type) [Group Y], SQTKHypCat Y → ∀ T : Subgroup Y, IsSylowTwoOf T ⊤ →
    ∀ K ∈ cComp (⊤ : Subgroup Y), ∀ B ∈ lFamily T, B ≤ K →
      Nat.card (ModO2 B) = 1080 → IsE2 4 ↥(CFSG.pCore 2 ↥B) →
      CFSG.Open.IsQuasisimple ↥K ∧ Nat.card ↥(Subgroup.center ↥K) = 3 ∧
        IsSporadic .M22 (↥K ⧸ Subgroup.center ↥K)

end CFSG.Quasithin.H13
