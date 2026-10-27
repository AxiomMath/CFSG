module

public import CFSG.RankThree.PartTwo.Sec4.StatementsComponents

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)
open scoped Pointwise

@[expose] def Item4_14_local : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Nonempty (G ≃* Blueprint.NativeSporadic.M12) → ∀ P : Sylow 3 G,
    IsHeisThree (P : Subgroup G) ∧
    IsKleinFour (Subgroup.normalizer ((P : Subgroup G) : Set G) ⧸
      (P : Subgroup G).subgroupOf (Subgroup.normalizer ((P : Subgroup G) : Set G))) ∧
    ∃ (E F A : Subgroup G) (t : G), t ∈ Subgroup.normalizer ((P : Subgroup G) : Set G) ∧
      (∀ z ∈ (P : Subgroup G) ⊓ Subgroup.centralizer ((P : Subgroup G) : Set G),
        t * z * t⁻¹ = z⁻¹) ∧
      {B : Subgroup G | B ≤ P ∧ Nat.card B = 9} = {E, F, A, conjugate A t} ∧
      Nonempty (autIn ⊤ E ≃* GL (Fin 2) (ZMod 3)) ∧
      Nonempty (autIn ⊤ F ≃* GL (Fin 2) (ZMod 3)) ∧
      Nonempty (autIn ⊤ A ≃* Equiv.Perm (Fin 3)) ∧
      ∀ a ∈ A, a ∉ (P : Subgroup G) ⊓ Subgroup.centralizer ((P : Subgroup G) : Set G) →
        Nonempty (Subgroup.normalizer (Subgroup.zpowers a : Set G) ≃*
          Equiv.Perm (Fin 3) × alternatingGroup (Fin 4))

@[expose] def Item4_14_signalizer : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Nonempty (G ≃* Blueprint.NativeSporadic.M12) → ∀ P : Sylow 3 G,
    ∀ B : Subgroup G, B ≤ P → Nat.card B = 9 →
      (Nonempty (autIn ⊤ B ≃* GL (Fin 2) (ZMod 3)) →
        invariantPiSubgroups ⊤ B (piOf 2) = {⊥}) ∧
      (Nonempty (autIn ⊤ B ≃* Equiv.Perm (Fin 3)) → gamma 1 B = ⊤ ∧
        ∀ a ∈ B, a ∉ (P : Subgroup G) ⊓ Subgroup.centralizer ((P : Subgroup G) : Set G) →
          (fun x : G => (conjugate (inSubgroup (CFSG.pCore 2) (Subgroup.centralizer {a})) x).map
              (MulAut.conj : G →* MulAut G)) '' ((P : Subgroup G) : Set G) =
            maxInvariantPiSubgroups ⊤ (B.map (MulAut.conj : G →* MulAut G)) (piOf 2))

@[expose] def Item4_14 : Prop :=
  Item4_14_local ∧ Item4_14_signalizer

@[expose] def Item4_15 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Nonempty (G ≃* Blueprint.NativeSporadic.J2) → ∀ P : Sylow 3 G,
    ∀ Z : Subgroup G, Z = (P : Subgroup G) ⊓ Subgroup.centralizer ((P : Subgroup G) : Set G) →
    ∀ Δ : Set (Subgroup G), Δ = {B : Subgroup G | B ≤ P ∧ Nat.card B = 9} →
      (IsHeisThree (P : Subgroup G) ∧
        Nonempty (Subgroup.normalizer ((P : Subgroup G) : Set G) ⧸
          (P : Subgroup G).subgroupOf (Subgroup.normalizer ((P : Subgroup G) : Set G)) ≃*
            Multiplicative (ZMod 8))) ∧
      (∀ B ∈ Δ, ∀ B' ∈ Δ, ∃ x ∈ Subgroup.normalizer ((P : Subgroup G) : Set G),
        B' = conjugate B x) ∧
      ((∀ g : G, conjugate Z g ≤ P → conjugate Z g = Z) ∧
        IsExtOf (Subgroup.centralizer (Z : Set G)) (alternatingGroup (Fin 6))
          (Multiplicative (ZMod 3)) ∧
        Nonempty (Subgroup.normalizer (Z : Set G) ⧸ Z.subgroupOf (Subgroup.normalizer (Z : Set G))
          ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField 3 2))) ∧
      (∀ A ∈ Δ, ∀ a ∈ A, a ∉ Z →
        Nonempty (autIn ⊤ A ≃* Equiv.Perm (Fin 3)) ∧
        Nonempty (Subgroup.normalizer (Subgroup.zpowers a : Set G) ≃*
          Equiv.Perm (Fin 3) × alternatingGroup (Fin 4)) ∧
        inSubgroup (CFSG.pCore 2) (Subgroup.normalizer
            (inSubgroup (CFSG.pCore 2) (Subgroup.normalizer (Subgroup.zpowers a : Set G)) :
              Set G)) =
          inSubgroup (CFSG.pCore 2) (Subgroup.normalizer (Subgroup.zpowers a : Set G)) ∧
        (inSubgroup (CFSG.pCore 2) (Subgroup.normalizer (Subgroup.zpowers a : Set G))).map
            (MulAut.conj : G →* MulAut G) ∈
          maxInvariantPiSubgroups
            (Subgroup.normalizer (Subgroup.zpowers (MulAut.conj a) : Set (MulAut G)))
            ((Subgroup.normalizer (Subgroup.zpowers a : Set G)).map (MulAut.conj : G →* MulAut G))
            (piOf 2)) ∧
      ∀ A ∈ Δ, ∃ S ∈ maxInvariantPiSubgroups ⊤ A (piOf 2),
        maxInvariantPiSubgroups ⊤ A (piOf 2) = (conjugate S) '' ((P : Subgroup G) : Set G) ∧
        (maxInvariantPiSubgroups ⊤ A (piOf 2)).ncard = 3 ∧
        (∃ T : Sylow 2 (projSL 3 (GaloisField 2 2)),
          Nonempty (S ≃* (T : Subgroup (projSL 3 (GaloisField 2 2))))) ∧
        ∃ a b : G, Subgroup.closure {a, b} = A ∧
          ((S ⊓ Subgroup.centralizer (Z : Set G) : Subgroup G) : Set G) *
              (inSubgroup (CFSG.pCore 2) (Subgroup.centralizer {a}) : Set G) *
              (inSubgroup (CFSG.pCore 2) (Subgroup.centralizer {b}) : Set G) = S

@[expose] def Item4_16 : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (G : Subgroup H), G.Normal → IsQuasisimple G →
    IsExtOf G Blueprint.NativeSporadic.ON (Multiplicative (ZMod 3)) →
    ∀ σ : H, σ ^ 2 = 1 → InducesOuter σ G → G ⊔ Subgroup.zpowers σ = ⊤ →
    ∀ A : Subgroup H, A ≤ G → Late.IsE27 A →
    ∀ a ∈ A, a ∉ (Subgroup.center G).map G.subtype →
    ∀ S ∈ maxInvariantPiSubgroups ⊤ A (piOf 2),
      (∃ P : Sylow 3 G, A ≤ (P : Subgroup G).map G.subtype ∧
        (A.subgroupOf ((P : Subgroup G).map G.subtype)).Normal ∧
        IsExtraspecialPGroup 3 (P : Subgroup G) ∧ Nat.card (P : Subgroup G) = 3 ^ 5 ∧
        Monoid.exponent (P : Subgroup G) = 3) ∧
      ∃ K : Subgroup H, IsExtOf K (alternatingGroup (Fin 6)) (Multiplicative (ZMod 3)) ∧
        G ⊓ Subgroup.centralizer {a} = Subgroup.zpowers a ⊔ K ∧ Subgroup.zpowers a ⊓ K = ⊥ ∧
        IsKleinFour S ∧ S ≤ G ∧ (a ∈ Subgroup.centralizer (S : Set H) → S ≤ K)

end CFSG.RankThree.PartTwo.Sec4
