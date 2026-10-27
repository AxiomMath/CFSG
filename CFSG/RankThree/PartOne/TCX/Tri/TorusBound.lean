module

public import CFSG.RankThree.PartOne.KE.CTTorusFixed
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartOne.KGD.D4Frame
public import CFSG.RankThree.PartOne.TCX.Tri.Graph

public section

namespace CFSG.RankThree.PartOne.TCX.Tri

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KGD
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix

section Matrices

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem exists_rightInverse_pow_sub_one {U X : Matrix n n ℤ} {d : ℤ} (hU6 : U ^ 6 = 1)
    (hX : (U - 1) * X = d • 1) {k : ℕ} (hk : k % 6 = 1 ∨ k % 6 = 5) :
    ∃ X' : Matrix n n ℤ, (U ^ k - 1) * X' = d • 1 := by
  have hk' : U ^ k = U ^ (k % 6) := by
    conv_lhs => rw [← Nat.div_add_mod k 6, pow_add, pow_mul, hU6, one_pow, one_mul]
  rcases hk with h | h
  · rw [hk', h, pow_one]
    exact ⟨X, hX⟩
  · rw [hk', h]
    refine ⟨-(X * U), ?_⟩
    have h6 : U ^ 5 * U = 1 := by rw [← pow_succ]; exact hU6
    have e1 : U ^ 5 * (U - 1) = -(U ^ 5 - 1) := by
      rw [mul_sub, h6, mul_one, neg_sub]
    have e2 : (U ^ 5 - 1) = -(U ^ 5 * (U - 1)) := by rw [e1, neg_neg]
    calc (U ^ 5 - 1) * -(X * U) = U ^ 5 * ((U - 1) * X) * U := by
          rw [e2]
          simp only [neg_mul, mul_neg, neg_neg, mul_assoc]
      _ = d • 1 := by
          rw [hX, mul_smul_comm, mul_one, smul_mul_assoc, h6]

end Matrices

section Conj

variable {L : Type} [Field L]

@[expose] def ConjTuple (m : ModGL TwistTag.D4.tag L)
    (U : Matrix (Fin TwistTag.D4.tag.rank) (Fin TwistTag.D4.tag.rank) ℤ) : Prop :=
  ∀ a : Fin TwistTag.D4.tag.rank → Lˣ, ∃ a' : Fin TwistTag.D4.tag.rank → Lˣ,
    m * rootDiagUnit TwistTag.D4.tag a * m⁻¹ = rootDiagUnit TwistTag.D4.tag a' ∧
      ∀ v, rootChar a' v = rootChar a (U *ᵥ v)

theorem ConjTuple.pow {m : ModGL TwistTag.D4.tag L}
    {U : Matrix (Fin TwistTag.D4.tag.rank) (Fin TwistTag.D4.tag.rank) ℤ} (h : ConjTuple m U)
    (k : ℕ) : ConjTuple (m ^ k) (U ^ k) := by
  induction k with
  | zero =>
    intro a
    refine ⟨a, ?_, fun v => ?_⟩
    · rw [pow_zero, one_mul, inv_one, mul_one]
    · rw [pow_zero, Matrix.one_mulVec]
  | succ k ih =>
    intro a
    obtain ⟨a', ha'1, ha'2⟩ := ih a
    obtain ⟨a'', ha''1, ha''2⟩ := h a'
    refine ⟨a'', ?_, fun v => ?_⟩
    · have e : m ^ (k + 1) * rootDiagUnit TwistTag.D4.tag a * (m ^ (k + 1))⁻¹ =
          m * (m ^ k * rootDiagUnit TwistTag.D4.tag a * (m ^ k)⁻¹) * m⁻¹ := by
        rw [pow_succ']
        group
      rw [e, ha'1, ha''1]
    · rw [ha''2, ha'2, Matrix.mulVec_mulVec, pow_succ]

theorem triP_conj_rootDiagUnit (b : Fin TwistTag.D4.tag.rank → Lˣ) :
    triP L * rootDiagUnit TwistTag.D4.tag b * (triP L)⁻¹ =
      rootDiagUnit TwistTag.D4.tag (fun i => b (TwistTag.D4.perm.symm i)) := by
  refine Units.ext ?_
  have h := diagramMap_mul_rootDiag (t := TwistTag.D4) (K := L) b
  rw [Units.val_mul, Units.val_mul]
  change (diagramMap TwistTag.D4 L : Module.End L (RootModule TwistTag.D4.tag L)) * rootDiag b *
    ((((diagramMap TwistTag.D4 L)⁻¹ : ModGL TwistTag.D4.tag L)) :
      Module.End L (RootModule TwistTag.D4.tag L)) =
    rootDiag (fun i => b (TwistTag.D4.perm.symm i))
  rw [h, mul_assoc, Units.mul_inv, mul_one]

theorem conjTuple_of_weyl (w : WeylGroup TwistTag.D4.tag)
    {U : Matrix (Fin TwistTag.D4.tag.rank) (Fin TwistTag.D4.tag.rank) ℤ}
    (hU : ∀ v, permLattice TwistTag.D4.perm.symm (w⁻¹ • v) = U *ᵥ v) :
    ConjTuple (canonicalRep (coxeterSystem TwistTag.D4.tag) L w * triP L) U := by
  intro a
  refine ⟨weylTuple w (fun i => a (TwistTag.D4.perm.symm i)), ?_, fun v => ?_⟩
  · have e : (canonicalRep (coxeterSystem TwistTag.D4.tag) L w * triP L) *
        rootDiagUnit TwistTag.D4.tag a *
          (canonicalRep (coxeterSystem TwistTag.D4.tag) L w * triP L)⁻¹ =
        canonicalRep (coxeterSystem TwistTag.D4.tag) L w *
          (triP L * rootDiagUnit TwistTag.D4.tag a * (triP L)⁻¹) *
            (canonicalRep (coxeterSystem TwistTag.D4.tag) L w)⁻¹ := by group
    rw [e, triP_conj_rootDiagUnit, canonicalRep_conj_rootDiagUnit]
  · rw [rootChar_weylTuple, ← hU v]
    exact (rootChar_permLattice a TwistTag.D4.perm.symm (w⁻¹ • v)).symm

end Conj


section Exponent

variable {L : Type} [Field L]

theorem rootChar_pow_self_of_pow {a : Fin TwistTag.D4.tag.rank → Lˣ} {Q : ℕ}
    (haQ : ∀ i, a i ^ Q = a i) (v : Fin TwistTag.D4.tag.rank → ℤ) :
    rootChar a v ^ Q = rootChar a v := by
  simp only [rootChar, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, haQ i]

theorem tri_torus_exponent {m : ModGL TwistTag.D4.tag L}
    {U : Matrix (Fin TwistTag.D4.tag.rank) (Fin TwistTag.D4.tag.rank) ℤ} (hm : ConjTuple m U)
    {Fr : L →+* L} {Q : ℕ} (hFr : ∀ c, Fr c = c ^ Q) {k : ℕ}
    {a : Fin TwistTag.D4.tag.rank → Lˣ}
    (hfix : m ^ k * Units.map (entrywiseHom Fr) (rootDiagUnit TwistTag.D4.tag a) * (m ^ k)⁻¹ =
      rootDiagUnit TwistTag.D4.tag a)
    (haQ : ∀ i, a i ^ Q = a i)
    {X : Matrix (Fin TwistTag.D4.tag.rank) (Fin TwistTag.D4.tag.rank) ℤ} {d : ℕ}
    (hX : (U ^ k - 1) * X = (d : ℤ) • 1) : ∀ i, a i ^ d = 1 := by
  set aF : Fin TwistTag.D4.tag.rank → Lˣ := fun i => Units.map Fr.toMonoidHom (a i) with haF
  have h1 : Units.map (entrywiseHom Fr) (rootDiagUnit TwistTag.D4.tag a) =
      rootDiagUnit TwistTag.D4.tag aF := Units.ext (entrywise_rootDiag Fr a)
  obtain ⟨a', ha'1, ha'2⟩ := (hm.pow k) aF
  rw [h1, ha'1] at hfix
  have hae : a' = a := rootDiagUnit_injective (τ := TwistTag.D4.tag) (K := L) hfix
  have hrel : ∀ v, rootChar a v = rootChar a (U ^ k *ᵥ v) := by
    intro v
    have h2 := ha'2 v
    rw [hae] at h2
    rw [h2, haF, CFSG.RankThree.PartOne.KE.rootChar_map_tuple Fr a,
      CFSG.RankThree.PartOne.KE.CTTorus.map_units_eq_pow hFr]
    exact rootChar_pow_self_of_pow haQ _
  have key : ∀ v, rootChar a v ^ d = 1 := by
    intro v
    have h2 : rootChar a (((U ^ k - 1) * X) *ᵥ v) = 1 := by
      rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, rootChar_sub, ← hrel,
        mul_inv_cancel]
    rw [hX, Matrix.smul_mulVec, Matrix.one_mulVec, CFSG.LieType.Chevalley.rootChar_zsmul,
      zpow_natCast] at h2
    exact h2
  intro i
  have := key (Pi.single i 1)
  rwa [CFSG.RankThree.PartOne.KE.CTTorus.rootChar_single] at this

end Exponent

end CFSG.RankThree.PartOne.TCX.Tri
