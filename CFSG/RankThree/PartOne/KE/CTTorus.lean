module

public import CFSG.RankThree.PartOne.KE.CTTorusFixed
public import CFSG.LieType.Chevalley.CLSOddE7RationalEightGroup

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Lattice (orbitLattice)
open scoped Matrix Polynomial

section Twisted

variable {τ : Tag} {L : Type} [Field L]

theorem weylTuple_map_eq_iff (w : WeylGroup τ) (Fr : L →+* L) (a : Fin τ.rank → Lˣ) :
    weylTuple w (fun i => Units.map Fr.toMonoidHom (a i)) = a ↔
      ∀ u, rootChar a (w • u) = Units.map Fr.toMonoidHom (rootChar a u) := by
  constructor
  · intro h u
    have h1 : rootChar a (w • u) =
        rootChar (weylTuple w (fun i => Units.map Fr.toMonoidHom (a i))) (w • u) := by
      rw [h]
    rw [h1, rootChar_weylTuple, inv_smul_smul, ← map_rootChar]
  · intro h
    funext i
    have h1 := h (w⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ))
    rw [smul_inv_smul, CTTorus.rootChar_single] at h1
    change rootChar (fun i => Units.map Fr.toMonoidHom (a i)) (w⁻¹ • Pi.single i 1) = a i
    rw [← map_rootChar, ← h1]

@[expose] def twistedFixedTuples (w : WeylGroup τ) (Fr : L →+* L) :
    Subgroup (Fin τ.rank → Lˣ) where
  carrier := {a | weylTuple w (fun i => Units.map Fr.toMonoidHom (a i)) = a}
  mul_mem' {a b} ha hb := (weylTuple_map_eq_iff w Fr (a * b)).2 fun u => by
    rw [CTTorus.rootChar_mul, CTTorus.rootChar_mul, (weylTuple_map_eq_iff w Fr a).1 ha u,
      (weylTuple_map_eq_iff w Fr b).1 hb u, map_mul]
  one_mem' := (weylTuple_map_eq_iff w Fr 1).2 fun u => by
    rw [CTTorus.rootChar_one, CTTorus.rootChar_one, map_one]
  inv_mem' {a} ha := (weylTuple_map_eq_iff w Fr a⁻¹).2 fun u => by
    rw [rootChar_inv_apply, rootChar_inv_apply, (weylTuple_map_eq_iff w Fr a).1 ha u, map_inv]

theorem mem_twistedFixedTuples_iff {w : WeylGroup τ} {Fr : L →+* L} {a : Fin τ.rank → Lˣ} :
    a ∈ twistedFixedTuples w Fr ↔
      ∀ u, rootChar a (w • u) = Units.map Fr.toMonoidHom (rootChar a u) :=
  weylTuple_map_eq_iff w Fr a

theorem mem_twistedFixedTuples_iff_conj {w : WeylGroup τ} {Fr : L →+* L}
    {a : Fin τ.rank → Lˣ} :
    a ∈ twistedFixedTuples w Fr ↔
      canonicalRep (coxeterSystem τ) L w * Units.map (entrywiseHom Fr) (rootDiagUnit τ a) *
        (canonicalRep (coxeterSystem τ) L w)⁻¹ = rootDiagUnit τ a := by
  rw [show Units.map (entrywiseHom Fr) (rootDiagUnit τ a) =
      rootDiagUnit τ fun i => Units.map Fr.toMonoidHom (a i) from
    Units.ext (entrywise_rootDiag Fr a), canonicalRep_conj_rootDiagUnit,
    (rootDiagUnit_injective (τ := τ) (K := L)).eq_iff]
  exact Iff.rfl

theorem twistedFixedTuples_eq_fixedCharTuples {w : WeylGroup τ}
    {M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} (hw : ∀ u, w • u = M *ᵥ u) (Fr : L →+* L) :
    twistedFixedTuples w Fr = fixedCharTuples M Fr := by
  ext a
  rw [mem_twistedFixedTuples_iff, mem_fixedCharTuples_iff]
  exact forall_congr' fun u => by rw [hw u]

end Twisted

theorem isCyclic_and_card_twistedFixedTuples {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    (w : WeylGroup τ) (M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) (hw : ∀ u, w • u = M *ᵥ u)
    (v : Fin τ.rank → ℤ) (hlin : LinearIndependent ℤ fun j : Fin τ.rank => (M ^ (j : ℕ)) *ᵥ v)
    (hspan : Submodule.span ℤ (Set.range fun j : Fin τ.rank => (M ^ (j : ℕ)) *ᵥ v) = ⊤)
    (Fr : L →+* L) {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) {ℓ : ℕ} [CharP L ℓ] (hℓ : ℓ.Prime)
    (hℓq : ℓ ∣ q) (hdet : M.charpoly.coeff 0 = 1 ∨ M.charpoly.coeff 0 = -1)
    (hne : M.charpoly.eval (q : ℤ) ≠ 0) :
    IsCyclic (twistedFixedTuples w Fr) ∧
      Nat.card (twistedFixedTuples w Fr) = (M.charpoly.eval (q : ℤ)).natAbs := by
  rw [twistedFixedTuples_eq_fixedCharTuples hw Fr]
  exact isCyclic_and_card_fixedCharTuples M v hlin hspan Fr hFr hℓ hℓq hdet hne

theorem rootChar_ne_one_of_mem_twistedFixedTuples {τ : Tag} {L : Type} [Field L]
    (w : WeylGroup τ) (M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) (hw : ∀ u, w • u = M *ᵥ u)
    (Fr : L →+* L) {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) {p : ℕ} (hp : p.Prime)
    {a : Fin τ.rank → Lˣ} (ha : a ∈ twistedFixedTuples w Fr) (hap : ∀ i, a i ^ p = 1)
    (ha1 : a ≠ 1) {α : Fin τ.rank → ℤ} (A : ℤ[X])
    (hA : ∀ β, (Polynomial.aeval M A) *ᵥ β ∈ orbitLattice M α)
    (hpA : ¬ (p : ℤ) ∣ A.eval (q : ℤ)) : rootChar a α ≠ 1 := by
  rw [twistedFixedTuples_eq_fixedCharTuples hw Fr] at ha
  exact rootChar_ne_one_of_mem_fixedCharTuples M Fr hFr hp ha hap ha1 A hA hpA

end CFSG.RankThree.PartOne.KE
