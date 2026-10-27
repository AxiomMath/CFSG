module

public import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneTorusDefs
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameMatrix
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameBlock
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutPSLNonsplitLinear

public section

namespace CFSG.StandardType.SpJoin

open Polynomial Module Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
  CFSG.StandardType.SpNS CFSG.StandardType.OrdPNS

variable {F : Type} [Field F] [Finite F] {p : ℕ}

private theorem nsCore_eq_of_modEq {e s r : ℕ} {C : Matrix (Fin e) (Fin e) F}
    (hCp : C ^ p = 1) {k k' : Fin s → ℕ} (h : ∀ i, k i % p = k' i % p) :
    SLNS.nsCore (r := r) C k = SLNS.nsCore (r := r) C k' := by
  have hpow : ∀ j : ℕ, C ^ j = C ^ (j % p) := fun j => by
    conv_lhs => rw [← Nat.mod_add_div j p, pow_add, pow_mul, hCp, one_pow, mul_one]
  rw [SLNS.nsCore, SLNS.nsCore]
  congr 2
  funext i
  rw [hpow (k i), hpow (k' i), h i]

private theorem exists_card_le_pow_of_frame (hp : p.Prime)
    {n : ℕ} {E : Subgroup (StatedSp n F)}
    {D : Type} [AddCommGroup D] [Module F D] [FiniteDimensional F D] [Nontrivial D]
    {c : D →ₗ[F] D} (hD : SpBlockExists F p D c) (hcp : c ^ p = 1)
    {e : ℕ} (β : Basis (Fin e) F D)
    (mat : E → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
    (hmat : Function.Injective mat)
    (hSc : ∀ x y, Commute (mat x) (mat y))
    (hSp : ∀ x, (mat x) ^ p = 1)
    (hSJ : ∀ x, (mat x)ᵀ * jMat n F * mat x = jMat n F) :
    ∃ s : ℕ, Nat.card E ≤ p ^ s ∧ s * e ≤ 2 * n := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hSc' : ∀ x ∈ Set.range mat, ∀ y ∈ Set.range mat, Commute x y := by
    rintro _ ⟨X, rfl⟩ _ ⟨Y, rfl⟩
    exact hSc X Y
  have hSp' : ∀ x ∈ Set.range mat, x ^ p = 1 := by
    rintro _ ⟨X, rfl⟩
    exact hSp X
  have hSJ' : ∀ x ∈ Set.range mat, xᵀ * jMat n F * x = jMat n F := by
    rintro _ ⟨X, rfl⟩
    exact hSJ X
  obtain ⟨s, r, ε, A₀, hframe, -⟩ :=
    SpNS.exists_spFrame_matrix hD hp.one_lt.le β (Set.range mat) hSc' hSp' hSJ'
  have hCp : (LinearMap.toMatrix β β c) ^ p = 1 := by
    rw [LinearMap.toMatrix_pow, hcp, LinearMap.toMatrix_one]
  let kOf : E → (Fin s → ℕ) := fun X => Classical.choose (hframe (mat X) ⟨X, rfl⟩)
  have hkOf : ∀ X, mat X =
      (A₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
        (SLNS.nsCore (r := r) (LinearMap.toMatrix β β c) (kOf X)).submatrix ε ε *
          ((A₀⁻¹ : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) :=
    fun X => Classical.choose_spec (hframe (mat X) ⟨X, rfl⟩)
  let f : E → (Fin s → ZMod p) := fun X i => (kOf X i : ZMod p)
  have hf : Function.Injective f := by
    intro X Y hXY
    have hmod : ∀ i, kOf X i % p = kOf Y i % p := by
      intro i
      exact (ZMod.natCast_eq_natCast_iff' (kOf X i) (kOf Y i) p).mp (congrFun hXY i)
    have hcore : SLNS.nsCore (r := r) (LinearMap.toMatrix β β c) (kOf X) =
        SLNS.nsCore (r := r) (LinearMap.toMatrix β β c) (kOf Y) :=
      nsCore_eq_of_modEq hCp hmod
    refine hmat ?_
    rw [hkOf X, hkOf Y, hcore]
  have hcardE : Nat.card E ≤ Nat.card (Fin s → ZMod p) :=
    Nat.card_le_card_of_injective f hf
  have hpow : Nat.card (Fin s → ZMod p) = p ^ s := by
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  have hcard : Nat.card E ≤ p ^ s := by
    rw [hpow] at hcardE
    exact hcardE
  have hcardε : Fintype.card (Fin n ⊕ Fin n) = Fintype.card ((Fin e × Fin s) ⊕ Fin r) :=
    Fintype.card_congr ε
  have h2n : 2 * n = e * s + r := by
    rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin, Fintype.card_fin, Fintype.card_fin] at hcardε
    omega
  have hsd : s * e ≤ 2 * n := by
    rw [mul_comm s e]
    omega
  exact ⟨s, hcard, hsd⟩

theorem exists_card_le_pow_of_isElemAbelian (hp : p.Prime) (hp2 : p ≠ 2) (hpF : (p : F) ≠ 0)
    {n : ℕ} (E : Subgroup (StatedSp n F)) (hE : IsElemAbelian p E) :
    ∃ s d : ℕ, 2 ≤ d ∧ ordQ F p ≤ d ∧ Nat.card E ≤ p ^ s ∧ s * d ≤ 2 * n := by
  classical
  have hne : ¬ IsUnit (cyclotomic p F) := by
    rw [Polynomial.isUnit_iff_degree_eq_zero, degree_eq_natDegree (cyclotomic_ne_zero p F),
      natDegree_cyclotomic, Nat.totient_prime hp]
    have := hp.two_le
    norm_cast
    omega
  obtain ⟨g, hgirr, hgd⟩ := WfDvdMonoid.exists_irreducible_factor hne (cyclotomic_ne_zero p F)
  haveI : Fact (Irreducible g) := ⟨hgirr⟩
  have hζ := NSFrame.root_isPrimitiveRoot (g := g) hp hpF hgd
  have hdeg : g.natDegree = ordQ F p := OrdPNS.natDegree_eq_ordQ hp hpF hgirr hgd
  haveI : Module.Finite F (AdjoinRoot g) := (AdjoinRoot.powerBasis hgirr.ne_zero).finite
  let mat : E → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F :=
    fun X => (((X : StatedSp n F) : GL (Fin n ⊕ Fin n) F) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
  have hmat : Function.Injective mat := by
    intro X Y h
    exact Subtype.ext (Subtype.ext (Units.ext h))
  have hSc : ∀ x y, Commute (mat x) (mat y) := by
    intro X Y
    have h1 : (X : StatedSp n F) * (Y : StatedSp n F) =
        (Y : StatedSp n F) * (X : StatedSp n F) := by
      simpa only [Subgroup.coe_mul] using congrArg Subtype.val (hE.1.is_comm.comm X Y)
    have h2 := congrArg (fun Z : StatedSp n F =>
      ((Z : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)) h1
    rw [commute_iff_eq]
    exact h2
  have hSp : ∀ x, (mat x) ^ p = 1 := by
    intro X
    have h1 : (X : StatedSp n F) ^ p = 1 := hE.2 X.1 X.2
    have h2 := congrArg (fun Z : StatedSp n F =>
      ((Z : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)) h1
    simpa only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, Subgroup.coe_one, Units.val_one]
      using h2
  have hSJ : ∀ x, (mat x)ᵀ * jMat n F * mat x = jMat n F := by
    intro X
    exact CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff.mp X.1.2
  have hpowp : ∀ μ : AdjoinRoot g, μ ^ p = 1 → (LinearMap.mulLeft F μ) ^ p = 1 :=
    fun μ hμ => LinearMap.ext fun d => by
      rw [LinearMap.pow_mulLeft, LinearMap.mulLeft_apply, hμ, one_mul, Module.End.one_apply]
  by_cases hA : aeval (AdjoinRoot.root g ^ (p - 1)) g = 0
  · have h2d : 2 ≤ g.natDegree := by
      by_contra h
      rw [not_le] at h
      have hnd : g.natDegree = 1 := by
        have hpos : 0 < g.natDegree :=
          natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hgirr)
        omega
      have hu : g.coeff 1 ≠ 0 := by
        rw [← hnd, Polynomial.coeff_natDegree]
        exact Polynomial.leadingCoeff_ne_zero.mpr hgirr.ne_zero
      have hg_eq : g = Polynomial.C (g.coeff 1) * Polynomial.X + Polynomial.C (g.coeff 0) :=
        Polynomial.eq_X_add_C_of_natDegree_le_one (by omega)
      have hroot : aeval (AdjoinRoot.root g) g = 0 := by
        rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
      have hpoly : aeval (AdjoinRoot.root g)
            (Polynomial.C (g.coeff 1) * Polynomial.X + Polynomial.C (g.coeff 0)) =
          aeval (AdjoinRoot.root g ^ (p - 1))
            (Polynomial.C (g.coeff 1) * Polynomial.X + Polynomial.C (g.coeff 0)) := by
        rw [← hg_eq, hroot, hA]
      simp only [Polynomial.aeval_add, Polynomial.aeval_mul, Polynomial.aeval_C,
        Polynomial.aeval_X] at hpoly
      have hζne : algebraMap F (AdjoinRoot g) (g.coeff 1) ≠ 0 := by
        intro h0
        apply hu
        have h2 : algebraMap F (AdjoinRoot g) (g.coeff 1) = algebraMap F (AdjoinRoot g) 0 := by
          simpa using h0
        exact RingHom.injective (algebraMap F (AdjoinRoot g)) h2
      have heq : AdjoinRoot.root g = AdjoinRoot.root g ^ (p - 1) :=
        mul_left_cancel₀ hζne (add_right_cancel hpoly)
      have hsq : AdjoinRoot.root g ^ 2 = 1 := by
        calc AdjoinRoot.root g ^ 2 = AdjoinRoot.root g * AdjoinRoot.root g := sq _
          _ = AdjoinRoot.root g * AdjoinRoot.root g ^ (p - 1) :=
              congrArg (fun x => AdjoinRoot.root g * x) heq
          _ = AdjoinRoot.root g ^ ((p - 1) + 1) := (pow_succ' _ _).symm
          _ = AdjoinRoot.root g ^ p := by rw [Nat.sub_add_cancel hp.one_lt.le]
          _ = 1 := hζ.pow_eq_one
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
        (hζ.dvd_of_pow_eq_one 2 hsq))
    have hcp : (LinearMap.mulLeft F (AdjoinRoot.root g)) ^ p = 1 :=
      hpowp _ hζ.pow_eq_one
    obtain ⟨s, hcard, hsd⟩ := exists_card_le_pow_of_frame (E := E) hp
      (SpNS.spBlockExists_selfDual hp hp2 hpF hgd hA) hcp
      (AdjoinRoot.powerBasis hgirr.ne_zero).basis mat hmat hSc hSp hSJ
    exact ⟨s, g.natDegree, h2d, le_of_eq hdeg.symm, hcard, hsd⟩
  · have hζp' : (AdjoinRoot.root g ^ (p - 1)) ^ p = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    have h2d : 2 ≤ g.natDegree + g.natDegree := by
      have hpos : 0 < g.natDegree :=
        natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hgirr)
      omega
    have hcp : ((LinearMap.mulLeft F (AdjoinRoot.root g)).prodMap
        (LinearMap.mulLeft F (AdjoinRoot.root g ^ (p - 1)))) ^ p = 1 := by
      rw [OrdPNS.prodMap_pow, hpowp _ hζ.pow_eq_one, hpowp _ hζp', LinearMap.prodMap_one]
    obtain ⟨s, hcard, hsd⟩ := exists_card_le_pow_of_frame (E := E) hp
      (SpNS.spBlockExists_paired hp hpF hgd hA)
      hcp (((AdjoinRoot.powerBasis hgirr.ne_zero).basis.prod
        (AdjoinRoot.powerBasis hgirr.ne_zero).basis).reindex finSumFinEquiv)
      mat hmat hSc hSp hSJ
    refine ⟨s, g.natDegree + g.natDegree, h2d, ?_, hcard, hsd⟩
    rw [← hdeg]
    exact Nat.le_add_right _ _

theorem card_le_pow_of_isElemAbelian (hp : p.Prime) (hp2 : p ≠ 2) (hpF : (p : F) ≠ 0) {n : ℕ}
    (E : Subgroup (StatedSp n F)) (hE : IsElemAbelian p E) : Nat.card E ≤ p ^ n := by
  obtain ⟨s, d, hd2, -, hcard, hsd⟩ := exists_card_le_pow_of_isElemAbelian hp hp2 hpF E hE
  have hsn : s ≤ n := by nlinarith
  exact hcard.trans (Nat.pow_le_pow_right hp.pos hsn)

theorem ordQ_le_two_of_pow_le_card (hp : p.Prime) (hp2 : p ≠ 2) (hpF : (p : F) ≠ 0) {n : ℕ}
    (hn : 1 ≤ n) (E : Subgroup (StatedSp n F)) (hE : IsElemAbelian p E)
    (hcard : p ^ n ≤ Nat.card E) : ordQ F p ≤ 2 := by
  obtain ⟨s, d, hd2, hod, hcard', hsd⟩ := exists_card_le_pow_of_isElemAbelian hp hp2 hpF E hE
  have hns : n ≤ s := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hcard.trans hcard')
  have hd : d ≤ 2 := by nlinarith
  exact hod.trans hd

theorem dvd_card_sub_one_or_add_one_of_pow_le_card (hp : p.Prime) (hp2 : p ≠ 2)
    (hpF : (p : F) ≠ 0) {n : ℕ} (hn : 1 ≤ n) (E : Subgroup (StatedSp n F))
    (hE : IsElemAbelian p E) (hcard : p ^ n ≤ Nat.card E) :
    p ∣ Nat.card F - 1 ∨ p ∣ Nat.card F + 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hle : ordQ F p ≤ 2 := ordQ_le_two_of_pow_le_card hp hp2 hpF hn E hE hcard
  have hpos : 0 < ordQ F p := OrdPNS.ordQ_pos hp hpF
  have hdvdQ : ordQ F p ∣ 2 := by
    have hcases : ordQ F p = 1 ∨ ordQ F p = 2 := by omega
    rcases hcases with h | h <;> rw [h] <;> norm_num
  have hdvd : orderOf ((Nat.card F : ℕ) : ZMod p) ∣ 2 := by
    rw [← OrdPNS.ordQ_def F p]
    exact hdvdQ
  have hsq : ((Nat.card F : ℕ) : ZMod p) ^ 2 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp hdvd
  rcases sq_eq_one_iff.mp hsq with h1 | hneg
  · left
    have hq : ((Nat.card F - 1 : ℕ) : ZMod p) = 0 := by
      have hle1 : 1 ≤ Nat.card F := by
        have := Nat.card_pos (α := F)
        omega
      rw [Nat.cast_sub hle1, h1]
      simp
    exact (ZMod.natCast_eq_zero_iff (Nat.card F - 1) p).mp hq
  · right
    have hq : ((Nat.card F + 1 : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_add, Nat.cast_one, hneg]
      simp
    exact (ZMod.natCast_eq_zero_iff (Nat.card F + 1) p).mp hq

end CFSG.StandardType.SpJoin
