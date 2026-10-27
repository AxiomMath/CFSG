module

public import CFSG.LocalAnalysis.WeakClosure81.SevenKDefs
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SevenK

open CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

@[expose] def IsUnitaryTransvectionIn (m n : ℕ) {F : Type} [Field F]
    (x : StatedProj (StatedSU m (2 ^ n) F)) : Prop :=
  ∃ g : StatedSU m (2 ^ n) F,
    (QuotientGroup.mk g : StatedProj (StatedSU m (2 ^ n) F)) = x ∧
      Matrix.rank (((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) - 1) = 1

@[expose] def IsUnitaryTransvection (X : Type) [Group X] (m n : ℕ) (x : X) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = (2 ^ n) ^ 2 ∧
    ∃ e : (X ⧸ Subgroup.center X) ≃* StatedProj (StatedSU m (2 ^ n) F),
      IsUnitaryTransvectionIn m n (e (QuotientGroup.mk x))

@[expose] def UnitaryRootCommutatorRank : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K I : Subgroup G) (m n : ℕ), 3 ≤ m →
    IsElemAbelian 2 I → K ≤ Subgroup.normalizer (I : Set G) →
    K ⊓ Subgroup.centralizer (I : Set G) ≤ pCoreOf 2 K →
    ∀ (X : Type) [Group X] (φ : ↥K →* X), IsBarMap K (pCoreOf 2 K) φ →
      IsPSUGp (X ⧸ Subgroup.center X) m n →
      ∀ v : ↥K, (v : G) * (v : G) = 1 → IsUnitaryTransvection X m n (φ v) →
        2 * n ≤ rk ↥⁅I, Subgroup.zpowers (v : G)⁆

end CFSG.LocalAnalysis.WeakClosure81.SevenK

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open SevenK
open scoped commutatorElement

@[expose] def UnitaryRootCommutatorRankAt (m : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K I : Subgroup G) (n : ℕ),
    IsElemAbelian 2 I → K ≤ Subgroup.normalizer (I : Set G) →
    K ⊓ Subgroup.centralizer (I : Set G) ≤ pCoreOf 2 K →
    ∀ (X : Type) [Group X] (φ : ↥K →* X), IsBarMap K (pCoreOf 2 K) φ →
      IsPSUGp (X ⧸ Subgroup.center X) m n →
      ∀ v : ↥K, (v : G) * (v : G) = 1 → IsUnitaryTransvection X m n (φ v) →
        2 * n ≤ rk ↥⁅I, Subgroup.zpowers (v : G)⁆

theorem unitaryRootCommutatorRank_iff_at :
    UnitaryRootCommutatorRank ↔ ∀ m : ℕ, 3 ≤ m → UnitaryRootCommutatorRankAt m := by
  constructor
  · intro h m hm G _ _ K I n hI hK hC X _ φ hφ hX v hv hvt
    exact h G K I m n hm hI hK hC X φ hφ hX v hv hvt
  · intro h G _ _ K I m n hm hI hK hC X _ φ hφ hX v hv hvt
    exact h m hm G K I n hI hK hC X φ hφ hX v hv hvt

end CFSG.LocalAnalysis.WeakClosure81

end
