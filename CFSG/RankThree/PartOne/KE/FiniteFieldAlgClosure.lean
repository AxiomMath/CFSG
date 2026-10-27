module

public import CFSG.RankThree.PartOne.KE.A1SL2

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

theorem exists_finite_field_isAlgClosure (ℓ f : ℕ) [Fact ℓ.Prime] (hf : 1 ≤ f) (K L : Type)
    [Field K] [Finite K] [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ] :
    ∃ (k : Type) (_ : Field k) (_ : Algebra k L), IsAlgClosure k L ∧ Nat.card k = ℓ ^ f := by
  have hL : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨k, hk, hfin, hAlg, hcard⟩ := exists_finite_field_into ℓ f hf L
  have hKc : CharP K ℓ := ⟨fun x => by
    rw [← (algebraMap K L).injective.eq_iff, map_natCast, map_zero]
    exact CharP.cast_eq_zero_iff L ℓ x⟩
  have hkc : CharP k ℓ := ⟨fun x => by
    rw [← (algebraMap k L).injective.eq_iff, map_natCast, map_zero]
    exact CharP.cast_eq_zero_iff L ℓ x⟩
  let _ : Algebra (ZMod ℓ) K := ZMod.algebra K ℓ
  let _ : Algebra (ZMod ℓ) k := ZMod.algebra k ℓ
  let _ : Algebra (ZMod ℓ) L := ZMod.algebra L ℓ
  have : IsScalarTower (ZMod ℓ) K L := IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  have : IsScalarTower (ZMod ℓ) k L := IsScalarTower.of_algebraMap_eq' (RingHom.ext_zmod _ _)
  have : Algebra.IsAlgebraic (ZMod ℓ) K := Algebra.IsAlgebraic.of_finite (ZMod ℓ) K
  have : Algebra.IsAlgebraic K L := IsAlgClosure.isAlgebraic
  have : Algebra.IsAlgebraic (ZMod ℓ) L := Algebra.IsAlgebraic.trans (ZMod ℓ) K L
  have : Algebra.IsAlgebraic k L := Algebra.IsAlgebraic.tower_top (K := ZMod ℓ) (L := k) (A := L)
  exact ⟨k, hk, hAlg, ⟨hL, inferInstance⟩, hcard⟩

end CFSG.RankThree.PartOne.KE
