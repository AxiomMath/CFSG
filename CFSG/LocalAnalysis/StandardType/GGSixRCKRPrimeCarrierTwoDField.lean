module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTwoDKleinE
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public import CFSG.LieType.Chevalley.SignKernelComponentBruhat
public import CFSG.LieType.Universal.Spin.Chevalley.Odd
public import CFSG.LieType.Universal.Spin.Twisted.Frame

public section

namespace CFSG.StandardType.RCKRP

open CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp.CompsPTwoDKlein
  CFSG.RankThree.PartOne.CTP.SU4Even

theorem rckTwoD_kleinData_fixedField
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {e : ℕ} (he : 0 < e)
    {F : Type} [Field F] (κ : F ≃+* ↥(frobeniusFixedField L 2 e))
    (bb cc : F) (hirr : ∀ s : F, s ^ 2 + bb * s + cc ≠ 0) :
    letI : Algebra F ↥(frobeniusFixedField L 2 (e * 2)) :=
      ((algebraMap ↥(frobeniusFixedField L 2 e) ↥(frobeniusFixedField L 2 (e * 2))).comp
        κ.toRingHom).toAlgebra
    Nonempty (KleinDataEven F ↥(frobeniusFixedField L 2 (e * 2))
      (frobInvol e) bb cc) := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Algebra F ↥(frobeniusFixedField L 2 (e * 2)) :=
    ((algebraMap ↥(frobeniusFixedField L 2 e) ↥(frobeniusFixedField L 2 (e * 2))).comp
      κ.toRingHom).toAlgebra
  let ι : F →+* L := (frobeniusFixedField L 2 e).subtype.comp κ.toRingHom
  let Fr : L →+* L := iterateFrobenius L 2 e
  have hcoef : ∀ r : F, Fr (ι r) = ι r := by
    intro r
    change iterateFrobenius L 2 e (κ r : L) = (κ r : L)
    rw [iterateFrobenius_def]
    exact mem_frobeniusFixedField.1 (κ r).2
  have hsurj : ∀ y : L, y ^ 2 ^ e = y → ∃ r : F, ι r = y := by
    intro y hy
    refine ⟨κ.symm ⟨y, mem_frobeniusFixedField.2 hy⟩, ?_⟩
    change (κ (κ.symm ⟨y, mem_frobeniusFixedField.2 hy⟩) : L) = y
    rw [κ.apply_symm_apply]
  have hσσ : ∀ x : ↥(frobeniusFixedField L 2 (e * 2)),
      frobInvol e (frobInvol e x) = x := fun x => frobHom_frobHom e x
  have hfix : ∀ r : F, frobInvol e
      (algebraMap F ↥(frobeniusFixedField L 2 (e * 2)) r) =
        algebraMap F ↥(frobeniusFixedField L 2 (e * 2)) r := by
    intro r
    apply Subtype.ext
    exact mem_frobeniusFixedField.1 (κ r).2
  have hfix' : ∀ y : ↥(frobeniusFixedField L 2 (e * 2)), frobInvol e y = y →
      ∃ r : F, algebraMap F ↥(frobeniusFixedField L 2 (e * 2)) r = y := by
    intro y hy
    obtain ⟨r, hr⟩ := hsurj y (congrArg Subtype.val hy)
    exact ⟨r, Subtype.ext hr⟩
  let p : Polynomial L := Polynomial.C 1 * Polynomial.X ^ 2 +
    Polynomial.C (ι bb) * Polynomial.X + Polynomial.C (ι cc)
  have hnd : p.natDegree = 2 := Polynomial.natDegree_quadratic one_ne_zero
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root p (by
    intro h
    have h0 : p.natDegree = 0 := Polynomial.natDegree_eq_of_degree_eq_some h
    omega)
  have hαeq : α ^ 2 + ι bb * α + ι cc = 0 := by
    simpa only [p, Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, one_mul] using hα
  have hαeq' : (Fr α) ^ 2 + ι bb * Fr α + ι cc = 0 := by
    simpa only [map_add, map_mul, map_pow, map_zero, hcoef] using congrArg Fr hαeq
  have hne : Fr α ≠ α := by
    intro h
    have hq : α ^ 2 ^ e = α := by simpa only [Fr, iterateFrobenius_def] using h
    obtain ⟨r, hr⟩ := hsurj α hq
    apply hirr r
    apply ι.injective
    simpa only [map_add, map_mul, map_pow, map_zero, hr] using hαeq
  have hmul : (Fr α - α) * (Fr α + α + ι bb) = 0 := by
    linear_combination hαeq' - hαeq
  have hsum : Fr α + α + ι bb = 0 :=
    (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hne)
  have hFrα : Fr α = -ι bb - α := by linear_combination hsum
  have hFr2 : Fr (Fr α) = α := by
    rw [hFrα, map_sub, map_neg, hcoef, hFrα]
    ring
  have hpow : Fr (Fr α) = α ^ 2 ^ (e * 2) := by
    change iterateFrobenius L 2 e (iterateFrobenius L 2 e α) = _
    rw [iterateFrobenius_def, iterateFrobenius_def, ← pow_mul, ← pow_add, Nat.mul_two]
  let ω : ↥(frobeniusFixedField L 2 (e * 2)) :=
    ⟨α, mem_frobeniusFixedField.2 (hpow.symm.trans hFr2)⟩
  have hω : ω ^ 2 + algebraMap F ↥(frobeniusFixedField L 2 (e * 2)) bb * ω +
      algebraMap F ↥(frobeniusFixedField L 2 (e * 2)) cc = 0 := by
    apply Subtype.ext
    exact hαeq
  exact CompsPTwoDKleinE.kleinDataEven_of_root (frobInvol e) hσσ hfix hfix' hirr hω

end CFSG.StandardType.RCKRP
