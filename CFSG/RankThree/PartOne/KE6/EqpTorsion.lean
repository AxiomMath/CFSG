module

public import CFSG.RankThree.PartOne.KE6.EqpTorus
public import CFSG.RankThree.Classical2.TwistedE6Phi3Centralizer

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Lattice
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.Classical2
open CFSG.RankThree.PartOne.KE (twistedTorus mem_twistedTorus)
open scoped Matrix

variable {L : Type} [Field L] {Fr : L →+* L}

theorem eqpMatrix_transpose_mulVec_apply {p : ℕ} (q : ℕ) (z : Fin Tag.E6.rank → ZMod p)
    (i : Fin Tag.E6.rank) :
    (((eqpMatrix q)ᵀ.map (Int.cast : ℤ → ZMod p)) *ᵥ z) i = (q : ZMod p) * z i + z (e6Rho i) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.transpose_apply, eqpMatrix,
    rhoMatrix, Matrix.add_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.of_apply,
    Int.cast_add, add_mul, Finset.sum_add_distrib]
  congr 1
  · simp [apply_ite, Int.cast_natCast, ite_mul, eq_comm]
  · have : ∀ j, (if i = e6Rho.symm j then (1 : ℤ) else 0) = if j = e6Rho i then 1 else 0 := by
      intro j
      by_cases h : j = e6Rho i
      · subst h
        simp
      · have : ¬ i = e6Rho.symm j := fun h' => h (by rw [h']; simp)
        simp [h, this]
    simp [this, ite_mul, apply_ite]

theorem eqp_prime_setup [IsAlgClosed L] {q : ℕ} (hq : (q : L) = 0) {p : ℕ} (hp : p.Prime)
    (hpq : (p : ℤ) ∣ (q : ℤ) + 1) : (p : L) ≠ 0 ∧ ∃ ζ : Lˣ, IsPrimitiveRoot ζ p := by
  have hpL : (p : L) ≠ 0 := fun h => by
    obtain ⟨c, hc⟩ := hpq
    have h1 : (((q : ℤ) + 1 : ℤ) : L) = 0 := by
      rw [hc]
      push_cast
      rw [h, zero_mul]
    push_cast at h1
    rw [hq] at h1
    norm_num at h1
  refine ⟨hpL, ?_⟩
  have : NeZero (p : L) := ⟨hpL⟩
  have := IsSepClosed.hasEnoughRootsOfUnity L p
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L p
  refine ⟨(hζ₀.isUnit hp.ne_zero).unit, IsPrimitiveRoot.coe_units_iff.mp ?_⟩
  rw [IsUnit.unit_spec]
  exact hζ₀

theorem exists_column_of_eqpTorus [IsAlgClosed L] {q p : ℕ} [NeZero p]
    (hFr : ∀ c, Fr c = c ^ q) (hqp : (q : ZMod p) + 1 = 0) {ζ : Lˣ} (hζ : IsPrimitiveRoot ζ p)
    {x : ModGL Tag.E6 L} (hx : x ∈ twistedTorus (eqpN L) Fr) (hxp : x ^ p = 1) :
    ∃ z : Fin Tag.E6.rank → ZMod p,
      x = rootDiagUnit Tag.E6 (fun i => ζ ^ (z i).val) ∧ (∀ i, z (e6Rho i) = z i) ∧
      torusRootKernel x = rootKernel z ∧ (x ≠ 1 → z ≠ 0) := by
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorus.1 hx).1
  have hbker : b ∈ (monomialHom (G := Lˣ) (eqpMatrix q)ᵀ).ker :=
    (mem_twistedTorus_rootDiagUnit_iffQp hFr b).1 (by rw [← hb]; exact hx)
  obtain ⟨z, hz⟩ := exists_eq_rootDiagUnit_zetaPow hζ (mem_twistedTorus.1 hx).1 hxp
  have hbz : b = fun i => ζ ^ (z i).val := rootDiagUnit_injective (hb.symm.trans hz)
  have hzc : ((eqpMatrix q)ᵀ.map (Int.cast : ℤ → ZMod p)) *ᵥ z = 0 := by
    rw [← zetaPow_mem_ker_monomialHom_iff hζ, ← hbz]
    exact hbker
  have hzγ : ∀ i, z (e6Rho i) = z i := fun i => by
    have h := congrFun hzc i
    rw [eqpMatrix_transpose_mulVec_apply] at h
    simp only [Pi.zero_apply] at h
    linear_combination h - z i * hqp
  refine ⟨z, hz, hzγ, ?_, fun hx1 hz0 => hx1 ?_⟩
  · rw [hz, torusRootKernel_rootDiagUnit, rootCharKernel_zetaPow hζ]
  · rw [hz, hz0]
    have : (fun i => ζ ^ ((0 : Fin Tag.E6.rank → ZMod p) i).val) = 1 := by
      funext i
      simp
    rw [this, rootDiagUnit_one]

theorem weylMatrix_e6W0_eq : weylMatrix e6W0 = -rhoMatrix := by
  ext i j
  have h := congrFun (weylMatrix_mulVec e6W0 (Pi.single j 1)) i
  rw [e6W0_smul, permLattice_eq_mulVec] at h
  have h3 : ∀ (M : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ) (i : Fin Tag.E6.rank),
      (M *ᵥ (Pi.single j 1 : Fin Tag.E6.rank → ℤ)) i = M i j := fun M i => by
    rw [Matrix.mulVec_single_one]
    rfl
  rw [h3] at h
  rw [Pi.neg_apply, h3] at h
  rw [h]
  rfl

theorem weylMatrix_e6W0_transpose_mulVec_apply {p : ℕ} (z : Fin Tag.E6.rank → ZMod p)
    (i : Fin Tag.E6.rank) :
    ((((weylMatrix e6W0).map (Int.cast : ℤ → ZMod p))ᵀ) *ᵥ z) i = -z (e6Rho i) := by
  rw [weylMatrix_e6W0_eq]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.transpose_apply, Matrix.neg_apply,
    rhoMatrix, Matrix.of_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib]
  congr 1
  have : ∀ j, (if i = e6Rho.symm j then (1 : ℤ) else 0) = if j = e6Rho i then 1 else 0 := by
    intro j
    by_cases h : j = e6Rho i
    · subst h
      simp
    · have : ¬ i = e6Rho.symm j := fun h' => h (by rw [h']; simp)
      simp [h, this]
  simp [this, ite_mul, apply_ite]

end CFSG.RankThree.PartOne.KE6
