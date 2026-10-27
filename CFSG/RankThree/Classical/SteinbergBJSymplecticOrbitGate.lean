module

public import CFSG.RankThree.Classical.SteinbergBJCharacterSpaces
public import CFSG.RankThree.Classical.SteinbergBJCentralCoprimeLift
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Witt
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticModelOuterTwoPart

public section

namespace CFSG.RankThree.Classical

open Matrix Module CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped IsMulCommutative

variable {r : ℕ} {K : Type} [Field K]

@[expose] noncomputable def liftRep (L : Type*) [Field L] [Algebra K L]
    {Ã : Subgroup (StatedSp r K)} {A : Type*} [Group A] (e : Ã ≃* A) :
    A →* Module.End L (Fin r ⊕ Fin r → L) :=
  (Matrix.toLinAlgEquiv' :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) L ≃ₐ[L] _).toRingEquiv.toMonoidHom.comp
    ((algebraMap K L).mapMatrix.toMonoidHom.comp
      ((mat r K).comp (Ã.subtype.comp e.symm.toMonoidHom)))

theorem liftRep_apply (L : Type*) [Field L] [Algebra K L] {Ã : Subgroup (StatedSp r K)}
    {A : Type*} [Group A] (e : Ã ≃* A) (a : A) (v : Fin r ⊕ Fin r → L) :
    liftRep L e a v = ((mat r K (e.symm a)).map (algebraMap K L)) *ᵥ v :=
  rfl

theorem form_map_mulVec (L : Type) [Field L] [Algebra K L] (x : StatedSp r K)
    (v w : Fin r ⊕ Fin r → L) :
    form ((mat r K x).map (algebraMap K L) *ᵥ v) ((mat r K x).map (algebraMap K L) *ᵥ w) =
      form v w := by
  have hg : (SymplecticPairs.gram K r).map (algebraMap K L) = SymplecticPairs.gram L r := by
    rw [SymplecticPairs.gram, SymplecticPairs.gram, fromBlocks_map, Matrix.map_zero _ (map_zero _),
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_neg _ (map_neg _),
      Matrix.map_one _ (map_zero _) (map_one _)]
  have h : ((mat r K x).map (algebraMap K L))ᵀ * SymplecticPairs.gram L r *
      (mat r K x).map (algebraMap K L) = SymplecticPairs.gram L r := by
    rw [← hg, ← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, mat_transpose_mul_gram_mul]
  unfold form
  rw [Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, ← Matrix.mul_assoc, h]

theorem det_symplecticGram_ne_zero (L : Type) [Field L] : (SymplecticPairs.gram L r).det ≠ 0 :=
  Matrix.det_ne_zero_of_right_inverse (B := -SymplecticPairs.gram L r) (by
    rw [Matrix.mul_neg, gram_mul_gram, neg_neg])

theorem liftRep_injective (L : Type*) [Field L] [Algebra K L] {Ã : Subgroup (StatedSp r K)}
    {A : Type*} [Group A] (e : Ã ≃* A) (a : A) (ha : liftRep L e a = 1) : a = 1 := by
  have h1 : (mat r K (e.symm a)).map (algebraMap K L) = 1 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_one]
    refine LinearMap.ext fun v => ?_
    have := LinearMap.congr_fun ha v
    rw [liftRep_apply, Module.End.one_apply] at this
    rw [Matrix.toLin'_apply, LinearMap.id_apply, this]
  have h2 : mat r K (e.symm a) = 1 :=
    Matrix.map_injective (algebraMap K L).injective
      (h1.trans (Matrix.map_one _ (map_zero _) (map_one _)).symm)
  have h3 : ((e.symm a : Ã) : StatedSp r K) = 1 := mat_injective (by rw [h2, map_one])
  have h4 : e.symm a = 1 := Subtype.ext h3
  rw [← e.apply_symm_apply a, h4, map_one]

theorem charSpace_liftRep_facts {ℓ p f : ℕ} (hℓ : ℓ.Prime) (hp : p.Prime) (hpℓ : p ≠ ℓ)
    [Fintype K] (hcardK : Fintype.card K = ℓ ^ f) [CharP K ℓ] {Ã : Subgroup (StatedSp r K)}
    {A : Type*} [Group A] [IsMulCommutative A] [Fintype A] (e : Ã ≃* A)
    (hexp : ∀ a : A, a ^ p = 1) (hcardA : Fintype.card A = p ^ 2)
    [Fintype (Additive A →+ ZMod p)] (L : Type) [Field L] [Algebra K L] [IsAlgClosed L]
    {ζ : L} (hζ : IsPrimitiveRoot ζ p) :
    iSupIndep (charSpace (liftRep L e) ζ (p := p)) ∧
      ⨆ χ : Additive A →+ ZMod p, charSpace (liftRep L e) ζ χ = ⊤ ∧
      ∑ χ : Additive A →+ ZMod p, finrank L (charSpace (liftRep L e) ζ χ) = 2 * r ∧
      (∀ χ : Additive A →+ ZMod p,
        finrank L (charSpace (liftRep L e) ζ ((ℓ ^ f) • χ)) =
          finrank L (charSpace (liftRep L e) ζ χ)) ∧
      (∀ χ : Additive A →+ ZMod p,
        finrank L (charSpace (liftRep L e) ζ (-χ)) = finrank L (charSpace (liftRep L e) ζ χ)) ∧
      AddSubgroup.closure {χ : Additive A →+ ZMod p |
        χ ≠ 0 ∧ charSpace (liftRep L e) ζ χ ≠ ⊥} = ⊤ := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hpK : (p : K) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff K ℓ] at h
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp h).symm
  have hpL : (p : L) ≠ 0 := by
    rw [← map_natCast (algebraMap K L)]
    exact (map_ne_zero _).mpr hpK
  have hΓL : (Fintype.card A : L) ≠ 0 := by
    rw [hcardA, Nat.cast_pow]
    exact pow_ne_zero 2 hpL
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  let σ : L ≃+* L := iterateFrobeniusEquiv L ℓ f
  have hσ : ∀ x : L, σ x = x ^ ℓ ^ f := fun x => by
    rw [iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  have hσK : ∀ c : K, σ (algebraMap K L c) = algebraMap K L c := fun c => by
    rw [hσ, ← map_pow, ← hcardK, FiniteField.pow_card]
  let Φ : (Fin r ⊕ Fin r → L) ≃+ (Fin r ⊕ Fin r → L) :=
    AddEquiv.piCongrRight fun _ => σ.toAddEquiv
  have hΦ : ∀ (c : L) (v : Fin r ⊕ Fin r → L), Φ (c • v) = σ c • Φ v := fun c v => by
    funext i
    simp [Φ, map_mul]
  have hρ : ∀ (a : A) (v : Fin r ⊕ Fin r → L),
      Φ (liftRep L e a v) = liftRep L e a (Φ v) := by
    intro a v
    funext i
    have hmap : ((mat r K (e.symm a)).map (algebraMap K L)).map σ.toRingHom =
        (mat r K (e.symm a)).map (algebraMap K L) := by
      ext j k
      simp [hσK]
    change σ.toRingHom (((mat r K (e.symm a)).map (algebraMap K L) *ᵥ v) i) =
      ((mat r K (e.symm a)).map (algebraMap K L) *ᵥ fun j => σ.toRingHom (v j)) i
    rw [RingHom.map_mulVec σ.toRingHom, hmap]
    rfl
  have hB : ∀ (a : A) (v w : Fin r ⊕ Fin r → L),
      Matrix.toBilin' (SymplecticPairs.gram L r) (liftRep L e a v) (liftRep L e a w) =
        Matrix.toBilin' (SymplecticPairs.gram L r) v w := by
    intro a v w
    rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply', liftRep_apply, liftRep_apply]
    exact form_map_mulVec L ((e.symm a : Ã) : StatedSp r K) v w
  have hBnd : ∀ v : Fin r ⊕ Fin r → L,
      (∀ w, Matrix.toBilin' (SymplecticPairs.gram L r) v w = 0) → v = 0 := by
    intro v hv
    refine (Matrix.nondegenerate_of_det_ne_zero (det_symplecticGram_ne_zero L)).eq_zero_of_ortho
      fun w => ?_
    rw [← Matrix.toBilin'_apply']
    exact hv w
  refine ⟨iSupIndep_charSpace hζ hΓL, iSup_charSpace_eq_top hp hζ hexp hΓL, ?_,
    fun χ => finrank_charSpace_nsmul hζ.pow_eq_one σ Φ hΦ hρ (ℓ ^ f) (hσ ζ) χ,
    fun χ => finrank_charSpace_neg hp hζ hexp hΓL _ hB hBnd χ,
    closure_support_charSpace_eq_top hp hζ hexp hΓL (liftRep_injective L e)⟩
  rw [sum_finrank_charSpace hp hζ hexp hΓL, Module.finrank_fintype_fun_eq_card, Fintype.card_sum,
    Fintype.card_fin, two_mul]

theorem symplectic_inner_cross_prime_orbit_gate {ℓ p f : ℕ} (hℓ : ℓ.Prime) (hp : p.Prime)
    (hpℓ : p ≠ ℓ) (hp2 : p ≠ 2) (_hf : 1 ≤ f) (hr : 1 ≤ r) (hK : Nat.card K = ℓ ^ f)
    (A : Subgroup (StatedProj (StatedSp r K))) (hA : IsElemAbelian p A)
    (hAc : Nat.card A = p ^ 2) :
    ∃ Ã : Subgroup (StatedSp r K), Ã ≤ A.comap (proj r K) ∧
      (∀ P : Sylow p (A.comap (proj r K)),
        (P : Subgroup (A.comap (proj r K))).map (A.comap (proj r K)).subtype = Ã) ∧
      ∃ e : Ã ≃* A, (∀ x : Ã, (e x : StatedProj (StatedSp r K)) = proj r K x) ∧
      (∀ a ∈ A, ∃! x : StatedSp r K, proj r K x = a ∧ x ^ p = 1) ∧
      (∀ ζ : AlgebraicClosure K, IsPrimitiveRoot ζ p →
        iSupIndep (charSpace (liftRep (AlgebraicClosure K) e) ζ (p := p)) ∧
        ⨆ χ : Additive A →+ ZMod p, charSpace (liftRep (AlgebraicClosure K) e) ζ χ = ⊤ ∧
        ∑ᶠ χ : Additive A →+ ZMod p,
          finrank (AlgebraicClosure K) (charSpace (liftRep (AlgebraicClosure K) e) ζ χ) =
            2 * r ∧
        (∀ χ : Additive A →+ ZMod p,
          finrank (AlgebraicClosure K)
              (charSpace (liftRep (AlgebraicClosure K) e) ζ ((ℓ ^ f) • χ)) =
            finrank (AlgebraicClosure K) (charSpace (liftRep (AlgebraicClosure K) e) ζ χ)) ∧
        (∀ χ : Additive A →+ ZMod p,
          finrank (AlgebraicClosure K) (charSpace (liftRep (AlgebraicClosure K) e) ζ (-χ)) =
            finrank (AlgebraicClosure K) (charSpace (liftRep (AlgebraicClosure K) e) ζ χ)) ∧
        Submodule.span (ZMod p) {χ : Additive A →+ ZMod p |
          χ ≠ 0 ∧ charSpace (liftRep (AlgebraicClosure K) e) ζ χ ≠ ⊥} = ⊤) ∧
      finrank (ZMod p) (Additive A →+ ZMod p) = 2 ∧
      Nat.lcm (orderOf ((ℓ ^ f : ℕ) : ZMod p)) 2 ≤ r ∧
      (r = 2 → p ∣ (ℓ ^ f) ^ 2 - 1) ∧
      (p ∣ ℓ ^ f - 1 → ∃ ζ : K, IsPrimitiveRoot ζ p ∧ ∃ P : StatedSp r K,
        ∃ χ : Fin r → (Additive A →+ ZMod p), ∀ a : A,
          mat r K (P⁻¹ * e.symm a * P) = Matrix.diagonal (Sum.elim
            (fun i => ζ ^ (χ i (Additive.ofMul a)).val)
            fun i => ζ ^ (-χ i (Additive.ofMul a)).val)) := by
  have hq0 : ℓ ^ f ≠ 0 := pow_ne_zero f hℓ.ne_zero
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact hq0)
  have := Fintype.ofFinite K
  have hcardK : Fintype.card K = ℓ ^ f := by rw [Fintype.card_eq_nat_card, hK]
  have hcharK : CharP K ℓ := by
    have : Fact ℓ.Prime := ⟨hℓ⟩
    exact charP_of_card_eq_prime_pow (f := f) hcardK
  have hpK : (p : K) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff K ℓ] at h
    exact hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp h).symm
  have hpq : ¬p ∣ ℓ ^ f := fun h =>
    hpℓ ((Nat.prime_dvd_prime_iff_eq hp hℓ).mp (hp.dvd_of_dvd_pow h))
  have hZc : (proj r K).ker ≤ Subgroup.center (StatedSp r K) := by
    rw [SymplecticHigher.ker_proj]
    exact SymplecticHigher.spScalars_le_center
  have hZp : Nat.Coprime (Nat.card (proj r K).ker) p := by
    rw [SymplecticHigher.ker_proj, card_spScalars_eq_gcd K hr]
    exact Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left 2 _)
      ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  have hAp : IsPGroup p A := fun a => ⟨1, Subtype.ext (by rw [pow_one]; exact hA.2 a a.2)⟩
  obtain ⟨Ã, hÃM, hÃuniq, e, he⟩ := exists_sylow_lift_of_ker_le_center hp (proj r K)
    SymplecticHigher.proj_surjective hZc hZp A hAp
  refine ⟨Ã, hÃM, hÃuniq, e, he, existsUnique_lift_pow_eq_one (proj r K) hZc hZp hA.2 e he, ?_⟩
  have : IsMulCommutative A := hA.1
  have hexp : ∀ a : A, a ^ p = 1 := fun a => Subtype.ext (hA.2 a a.2)
  have : Fintype A := Fintype.ofFinite A
  have hcardA : Fintype.card A = p ^ 2 := by rw [Fintype.card_eq_nat_card, hAc]
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Finite (Additive A →+ ZMod p) := Finite.of_injective _ DFunLike.coe_injective
  have : Fintype (Additive A →+ ZMod p) := Fintype.ofFinite _
  have hDcard : Nat.card (Additive A →+ ZMod p) = p ^ 2 := by rw [natCard_char hp hexp, hAc]
  have hchar := fun (ζ : AlgebraicClosure K) (hζ : IsPrimitiveRoot ζ p) =>
    charSpace_liftRep_facts hℓ hp hpℓ hcardK e hexp hcardA (AlgebraicClosure K) hζ
  have : NeZero (p : K) := ⟨hpK⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) p
  have hlcm : Nat.lcm (orderOf ((ℓ ^ f : ℕ) : ZMod p)) 2 ≤ r := by
    obtain ⟨-, -, hsum, hfrob, hneg, hcl⟩ := hchar ζ₀ hζ₀
    have hS : AddSubgroup.closure {χ : Additive A →+ ZMod p |
        χ ≠ 0 ∧ finrank (AlgebraicClosure K)
          (charSpace (liftRep (AlgebraicClosure K) e) ζ₀ χ) ≠ 0} = ⊤ := by
      have hset : {χ : Additive A →+ ZMod p | χ ≠ 0 ∧ finrank (AlgebraicClosure K)
          (charSpace (liftRep (AlgebraicClosure K) e) ζ₀ χ) ≠ 0} =
          {χ : Additive A →+ ZMod p |
            χ ≠ 0 ∧ charSpace (liftRep (AlgebraicClosure K) e) ζ₀ χ ≠ ⊥} := by
        ext χ
        simp only [Set.mem_ofPred_eq, ne_eq, Submodule.finrank_eq_zero]
      rw [hset]
      exact hcl
    have h := two_mul_lcm_le_sum hp hp2 hDcard hpq
      (fun χ => finrank (AlgebraicClosure K) (charSpace (liftRep (AlgebraicClosure K) e) ζ₀ χ))
      hfrob hneg hS
    omega
  refine ⟨fun ζ hζ => ?_, finrank_zmod_eq_of_natCard hp hDcard, hlcm, ?_, ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hchar ζ hζ
    exact ⟨h1, h2, by rw [finsum_eq_sum_of_fintype]; exact h3, h4, h5,
      span_zmod_eq_top_of_closure_eq_top h6⟩
  ·
    intro hr2
    have hcop : Nat.Coprime (ℓ ^ f) p :=
      Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpq)
    have hpos : 0 < orderOf ((ℓ ^ f : ℕ) : ZMod p) := by
      rw [← ZMod.coe_unitOfCoprime (ℓ ^ f) hcop, orderOf_units]
      exact orderOf_pos _
    have h2 : Nat.lcm (orderOf ((ℓ ^ f : ℕ) : ZMod p)) 2 = 2 :=
      le_antisymm (hr2 ▸ hlcm) (Nat.le_of_dvd (Nat.lcm_pos hpos two_pos) (Nat.dvd_lcm_right _ _))
    have h4 : orderOf ((ℓ ^ f : ℕ) : ZMod p) ∣ 2 := h2 ▸ Nat.dvd_lcm_left _ _
    have h5 : ((ℓ ^ f : ℕ) : ZMod p) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp h4
    have h6 : (((ℓ ^ f) ^ 2 - 1 : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_sub (Nat.one_le_pow _ _ (Nat.pos_of_ne_zero hq0)), Nat.cast_pow, h5,
        Nat.cast_one, sub_self]
    exact (ZMod.natCast_eq_zero_iff _ _).mp h6
  ·
    intro hdvd
    obtain ⟨ζ, hζ⟩ : ∃ ζ : K, IsPrimitiveRoot ζ p := by
      classical
      have : Fact p.Prime := ⟨hp⟩
      have hcardU : p ∣ Fintype.card Kˣ := by
        rw [Fintype.card_units, hcardK]
        exact hdvd
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card p hcardU
      refine ⟨x, IsPrimitiveRoot.coe_units_iff.mpr ?_⟩
      rw [← hx]
      exact IsPrimitiveRoot.orderOf x
    have hΓK : (Fintype.card A : K) ≠ 0 := by
      rw [hcardA, Nat.cast_pow]
      exact pow_ne_zero 2 hpK
    have htop := iSup_charSpace_eq_top (ρ := liftRep K e) hp hζ hexp hΓK
    set BK : LinearMap.BilinForm K (Fin r ⊕ Fin r → K) := Matrix.toBilin' (Matrix.J (Fin r) K)
    have hBK : ∀ (a : A) (v w : Fin r ⊕ Fin r → K),
        BK (liftRep K e a v) (liftRep K e a w) = BK v w := by
      intro a v w
      simp only [BK, toBilin'_J_apply, liftRep_apply]
      rw [form_map_mulVec K ((e.symm a : Ã) : StatedSp r K) v w]
    have horth : ∀ (χ ψ : Additive A →+ ZMod p), ψ ≠ -χ →
        ∀ v ∈ charSpace (liftRep K e) ζ χ, ∀ w ∈ charSpace (liftRep K e) ζ ψ, BK v w = 0 :=
      fun χ ψ h v hv w hw => apply_eq_zero_of_mem_charSpace hζ BK hBK
        (fun h' => h (eq_neg_of_add_eq_zero_right h')) hv hw
    obtain ⟨m, b, hb, hbW⟩ :=
      (isAlt_toBilin'_J (K := K) (n := r)).exists_basis_toMatrix_eq_J_of_iSup_eq_top
        nondegenerate_toBilin'_J (σ := Neg.neg) neg_involutive htop horth
    have hm : m = r := by
      have := Module.finrank_eq_card_basis b
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin, Fintype.card_sum,
        Fintype.card_fin] at this
      omega
    subst hm
    choose χ' hχ' using hbW
    have hBb : ∀ x y, BK (b x) (b y) = Matrix.J (Fin m) K x y := fun x y => by
      rw [← hb, LinearMap.BilinForm.toMatrix_apply]
    have hpair : ∀ i, χ' (Sum.inr i) = -χ' (Sum.inl i) := by
      intro i
      by_contra hne
      have h0 := horth (χ' (Sum.inl i)) (χ' (Sum.inr i)) hne _ (hχ' _) _ (hχ' _)
      rw [hBb] at h0
      simp [Matrix.J] at h0
    have hbform : ∀ x y, form (b x) (b y) = SymplecticPairs.gram K m x y := fun x y => by
      have := hBb x y
      rw [toBilin'_J_apply] at this
      rw [gram_eq_neg_J, Matrix.neg_apply, ← this, neg_neg]
    refine ⟨ζ, hζ, ofSymplecticBasis b hbform, fun i => χ' (Sum.inl i), fun a => ?_⟩
    set X := mat m K (e.symm a)
    set D : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K := Matrix.diagonal (Sum.elim
      (fun i => ζ ^ (χ' (Sum.inl i) (Additive.ofMul a)).val)
      fun i => ζ ^ (-χ' (Sum.inl i) (Additive.ofMul a)).val)
    have hcol : ∀ y, X *ᵥ b y = ζ ^ (χ' y (Additive.ofMul a)).val • b y := by
      intro y
      have := (mem_charSpace.mp (hχ' y)) a
      rwa [liftRep_apply, Algebra.algebraMap_self, RingHom.coe_id, Matrix.map_id] at this
    have hXP : X * basisMat b = basisMat b * D := by
      ext i y
      rw [Matrix.mul_diagonal]
      have h1 : (X * basisMat b) i y = (X *ᵥ b y) i := rfl
      rw [h1, hcol y, Pi.smul_apply, smul_eq_mul, mul_comm]
      congr 1
      rcases y with j | j
      · rfl
      · rw [Sum.elim_inr, hpair j, AddMonoidHom.neg_apply]
    rw [map_mul, map_mul, mat_ofSymplecticBasis, Matrix.mul_assoc, hXP, ← Matrix.mul_assoc,
      ← mat_ofSymplecticBasis b hbform, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mul]

end CFSG.RankThree.Classical
