module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.LinearAlgebra.Projectivization.Cardinality
public import Mathlib.GroupTheory.Subgroup.Center

namespace CFSG
end CFSG
open CFSG

/-!
# A small center lemma for `PSL₂`

The projective action of `PSL₂(K)` on the projective line is faithful and
2-transitive.  A central element therefore fixes every projective point: if it
did not fix one point, 2-transitivity would move a pair consisting of that
point and its image to a pair beginning with the image, contradicting
centrality.  This gives a compile-fast, characteristic-free proof that the
center of `PSL₂(K)` is trivial for every finite field `K`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open Matrix
open scoped MatrixGroups LinearAlgebra.Projectivization Pointwise

private theorem center_eq_bot_of_two_pretransitive
    {G X : Type*} [Group G] [MulAction G X] [FaithfulSMul G X]
    (h2 : MulAction.IsMultiplyPretransitive G X 2)
    (hcard : 3 ≤ Nat.card X) :
    Subgroup.center G = ⊥ := by
  apply le_bot_iff.mp
  intro z hz
  apply Subgroup.mem_bot.mpr
  apply (@FaithfulSMul.eq_of_smul_eq_smul G X _
    (inferInstance : FaithfulSMul G X) z (1 : G))
  intro x
  by_contra hzx
  have hpair : ({x, z • x} : Set X).ncard = 2 :=
    Set.ncard_pair (show x ≠ z • x by
      intro h
      apply hzx
      simpa using h.symm)
  have hlt : ({x, z • x} : Set X).ncard < (Set.univ : Set X).ncard := by
    rw [hpair, Set.ncard_univ]
    omega
  obtain ⟨y, hy⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hlt
  have hyx : y ≠ x := by
    intro h
    exact hy.2 (by simp [h])
  obtain ⟨g, hgx, hgy⟩ :=
    (MulAction.is_two_pretransitive_iff.mp h2) hzx hyx
  have hfix : g • (z • x) = z • x := by
    calc
      g • (z • x) = (g * z) • x := by rw [smul_smul]
      _ = (z * g) • x := by rw [Subgroup.mem_center_iff.mp hz g]
      _ = z • (g • x) := by rw [smul_smul]
      _ = z • x := by simpa using congrArg (fun q : X => z • q) hgy
  exact hy.2 (by simp [hgx.symm.trans hfix])

private theorem psl2_two_pretransitive (K : Type*) [Field K] [Finite K] :
    MulAction.IsMultiplyPretransitive (PSL2 K)
      (ℙ K (Fin 2 → K)) 2 := by
  let q : Matrix.SpecialLinearGroup (Fin 2) K →* PSL2 K :=
    QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))
  let f : (ℙ K (Fin 2 → K)) →ₑ[q] (ℙ K (Fin 2 → K)) := {
    toFun := id
    map_smul' := by
      intro g x
      change (q g) • x = g • x
      change g • x = g • x
      rfl }
  let : MulAction.IsPretransitive
      (Matrix.SpecialLinearGroup (Fin 2) K)
      (Fin 2 ↪ ℙ K (Fin 2 → K)) := inferInstance
  exact @MulAction.IsPretransitive.of_embedding _ _ _ _ _ _ _ _ q f (Fin 2)
    Function.surjective_id inferInstance

/-- The center of `PSL₂(K)` is trivial for every finite field `K`. -/
public theorem psl2_center_eq_bot (K : Type*) [Field K] [Finite K] :
    Subgroup.center (PSL2 K) = ⊥ := by
  let : MulAction (PSL2 K) (ℙ K (Fin 2 → K)) := inferInstance
  let : FaithfulSMul (PSL2 K) (ℙ K (Fin 2 → K)) := inferInstance
  have hcard : 3 ≤ Nat.card (ℙ K (Fin 2 → K)) := by
    have hfinrank : Module.finrank K (Fin 2 → K) = 2 := by simp
    rw [Projectivization.card_of_finrank_two K (Fin 2 → K) hfinrank]
    have hK : 2 ≤ Nat.card K := by
      have h := (Finite.one_lt_card : 1 < Nat.card K)
      omega
    omega
  exact center_eq_bot_of_two_pretransitive (psl2_two_pretransitive K) hcard

end CFSG.GorensteinWalter
