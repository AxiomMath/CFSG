module

public import CFSG.LieType.Chevalley.ToralCentralizerBruhat
public import CFSG.RankThree.Lattice.SteinbergBIOrbitLattice

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Lattice (orbitLattice)
open scoped Matrix Polynomial

namespace CTTorus

section RootChar

variable {τ : Tag} {K : Type} [Field K]

theorem rootChar_single (a : Fin τ.rank → Kˣ) (i : Fin τ.rank) :
    rootChar a (Pi.single i 1) = a i := by
  simpa using rootChar_nsmul_single a i 1

theorem rootChar_mul (a b : Fin τ.rank → Kˣ) (u : Fin τ.rank → ℤ) :
    rootChar (a * b) u = rootChar a u * rootChar b u := by
  simp only [rootChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

theorem rootChar_one (u : Fin τ.rank → ℤ) : rootChar (1 : Fin τ.rank → Kˣ) u = 1 := by
  simp [rootChar]

theorem rootChar_pow_eq_one {a : Fin τ.rank → Kˣ} {p : ℕ} (ha : ∀ i, a i ^ p = 1)
    (u : Fin τ.rank → ℤ) : rootChar a u ^ p = 1 := by
  rw [rootChar, ← Finset.prod_pow]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha, one_zpow]

theorem eq_one_of_rootChar_eq_one {a : Fin τ.rank → Kˣ} (h : ∀ u, rootChar a u = 1) :
    a = 1 :=
  funext fun i => by rw [← rootChar_single a i, h]; rfl

theorem rootChar_eq_one_of_mem_span {a : Fin τ.rank → Kˣ} {S : Set (Fin τ.rank → ℤ)}
    (hS : ∀ u ∈ S, rootChar a u = 1) {u : Fin τ.rank → ℤ} (hu : u ∈ Submodule.span ℤ S) :
    rootChar a u = 1 := by
  induction hu using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => exact rootChar_zero a
  | add x y _ _ hx hy => rw [rootChar_add, hx, hy, mul_one]
  | smul n x _ hx => rw [rootChar_zsmul, hx, one_zpow]

theorem map_units_eq_pow {Fr : K →+* K} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) (x : Kˣ) :
    Units.map Fr.toMonoidHom x = x ^ q :=
  Units.ext (by simp [hFr])

end RootChar

section Abstract

theorem pow_mulVec_eq_neg_sum {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℤ)
    (v : n → ℤ) {p : ℤ[X]} (hp : p.Monic) {k : ℕ} (hk : p.natDegree = k)
    (h : (Polynomial.aeval M p) *ᵥ v = 0) :
    (M ^ k) *ᵥ v = -∑ i ∈ Finset.range k, p.coeff i • ((M ^ i) *ᵥ v) := by
  have h1 := h
  rw [hp.as_sum, hk, map_add, map_sum] at h1
  simp only [map_pow, Polynomial.aeval_X, Polynomial.aeval_C, map_mul, Matrix.add_mulVec,
    Matrix.sum_mulVec, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, smul_mul_assoc,
    one_mul] at h1
  exact eq_neg_of_add_eq_zero_left h1

theorem eval_monic_eq {p : ℤ[X]} (hp : p.Monic) {k : ℕ} (hk : p.natDegree = k) (q : ℤ) :
    p.eval q = q ^ k + ∑ i ∈ Finset.range k, p.coeff i * q ^ i := by
  rw [Polynomial.eval_eq_sum_range, hk, Finset.sum_range_succ, add_comm, ← hk,
    hp.coeff_natDegree, one_mul]

theorem exists_linearMap_of_charpoly {r : ℕ} {N : Type*} [AddCommGroup N]
    (M : Matrix (Fin r) (Fin r) ℤ) (v : Fin r → ℤ)
    (hlin : LinearIndependent ℤ fun j : Fin r => (M ^ (j : ℕ)) *ᵥ v)
    (hspan : Submodule.span ℤ (Set.range fun j : Fin r => (M ^ (j : ℕ)) *ᵥ v) = ⊤)
    (q : ℤ) (x : N) (hx : (M.charpoly.eval q) • x = 0) :
    ∃ f : (Fin r → ℤ) →ₗ[ℤ] N, f v = x ∧ ∀ u, f (M *ᵥ u) = q • f u := by
  have hmonic := M.charpoly_monic
  have hdeg : M.charpoly.natDegree = r := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  let b : Module.Basis (Fin r) ℤ (Fin r → ℤ) := Module.Basis.mk hlin hspan.ge
  set f := b.constr ℤ (fun j : Fin r => (q ^ (j : ℕ)) • x)
  have hb : ∀ j : Fin r, b j = (M ^ (j : ℕ)) *ᵥ v := fun j => Module.Basis.mk_apply hlin _ j
  have h1 : ∀ m < r, f ((M ^ m) *ᵥ v) = (q ^ m) • x := fun m hm => by
    have := b.constr_basis ℤ (fun j : Fin r => (q ^ (j : ℕ)) • x) ⟨m, hm⟩
    rwa [hb] at this
  have h2 : f ((M ^ r) *ᵥ v) = (q ^ r) • x := by
    have hrel := pow_mulVec_eq_neg_sum M v hmonic hdeg
      (by rw [Matrix.aeval_self_charpoly, Matrix.zero_mulVec])
    have h3 : ∀ i ∈ Finset.range r, f (M.charpoly.coeff i • ((M ^ i) *ᵥ v)) =
        (M.charpoly.coeff i * q ^ i) • x := fun i hi => by
      rw [map_zsmul, h1 i (Finset.mem_range.1 hi), smul_smul]
    have hx' : (q ^ r) • x + (∑ i ∈ Finset.range r, (M.charpoly.coeff i * q ^ i)) • x = 0 := by
      rw [← add_smul, ← eval_monic_eq hmonic hdeg q]
      exact hx
    rw [hrel, map_neg, map_sum, Finset.sum_congr rfl h3, ← Finset.sum_smul]
    exact neg_eq_of_add_eq_zero_left hx'
  have h1' : ∀ m ≤ r, f ((M ^ m) *ᵥ v) = (q ^ m) • x := fun m hm => by
    rcases hm.lt_or_eq with hm | rfl
    · exact h1 m hm
    · exact h2
  have h4 : f ∘ₗ (Matrix.mulVecLin M) = q • f := by
    refine b.ext fun j => ?_
    have e : M *ᵥ (b j) = (M ^ ((j : ℕ) + 1)) *ᵥ v := by
      rw [hb, Matrix.mulVec_mulVec, ← pow_succ']
    have e2 : f (b j) = (q ^ (j : ℕ)) • x := b.constr_basis ℤ _ j
    rw [LinearMap.comp_apply, Matrix.mulVecLin_apply, e, LinearMap.smul_apply, e2, smul_smul,
      ← pow_succ']
    exact h1' _ j.2
  refine ⟨f, ?_, fun u => ?_⟩
  · simpa using h1' 0 (Nat.zero_le _)
  · exact congrArg (fun g : (Fin r → ℤ) →ₗ[ℤ] N => g u) h4

theorem prod_zpow_eq_toMul {G : Type*} [CommGroup G] {r : ℕ}
    (f : (Fin r → ℤ) →ₗ[ℤ] Additive G) (u : Fin r → ℤ) :
    ∏ i, (Additive.toMul (f (Pi.single i 1))) ^ u i = Additive.toMul (f u) := by
  have hu : u = ∑ i, u i • (Pi.single i 1 : Fin r → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hu]
  rw [map_sum, toMul_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_zsmul, toMul_zsmul]

theorem zpow_eq_one_iff_natAbs {G : Type*} [Group G] (c : G) (z : ℤ) :
    c ^ z = 1 ↔ c ^ z.natAbs = 1 := by
  rw [← orderOf_dvd_iff_zpow_eq_one, ← orderOf_dvd_iff_pow_eq_one, Int.natCast_dvd]

end Abstract

end CTTorus

section Fixed

variable {τ : Tag} {L : Type} [Field L]

@[expose] def fixedCharTuples (M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) (Fr : L →+* L) :
    Subgroup (Fin τ.rank → Lˣ) where
  carrier := {a | ∀ u, rootChar a (M *ᵥ u) = Units.map Fr.toMonoidHom (rootChar a u)}
  mul_mem' {a b} ha hb := fun u => by
    rw [CTTorus.rootChar_mul, CTTorus.rootChar_mul, ha u, hb u, map_mul]
  one_mem' := fun u => by
    rw [CTTorus.rootChar_one, CTTorus.rootChar_one, map_one]
  inv_mem' {a} ha := fun u => by
    rw [rootChar_inv_apply, rootChar_inv_apply, ha u, map_inv]

theorem mem_fixedCharTuples_iff {M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} {Fr : L →+* L}
    {a : Fin τ.rank → Lˣ} :
    a ∈ fixedCharTuples M Fr ↔
      ∀ u, rootChar a (M *ᵥ u) = Units.map Fr.toMonoidHom (rootChar a u) :=
  Iff.rfl

end Fixed

section Powers

variable {τ : Tag} {L : Type} [Field L] {M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} {Fr : L →+* L}
  {q : ℕ} {a : Fin τ.rank → Lˣ}

theorem rootChar_pow_mulVec_of_mem_fixedCharTuples (hFr : ∀ c, Fr c = c ^ q)
    (ha : a ∈ fixedCharTuples M Fr) (j : ℕ) (u : Fin τ.rank → ℤ) :
    rootChar a ((M ^ j) *ᵥ u) = rootChar a u ^ (q ^ j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, mem_fixedCharTuples_iff.1 ha,
      CTTorus.map_units_eq_pow hFr, ih, ← pow_mul, pow_succ]

theorem rootChar_aeval_mulVec_of_mem_fixedCharTuples (hFr : ∀ c, Fr c = c ^ q)
    (ha : a ∈ fixedCharTuples M Fr) (A : ℤ[X]) (β : Fin τ.rank → ℤ) :
    rootChar a ((Polynomial.aeval M A) *ᵥ β) = rootChar a β ^ (A.eval (q : ℤ)) := by
  induction A using Polynomial.induction_on' with
  | add p s hp hs =>
    rw [map_add, Matrix.add_mulVec, rootChar_add, hp, hs, Polynomial.eval_add, zpow_add]
  | monomial n c =>
    rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      Matrix.smul_mulVec, rootChar_zsmul, rootChar_pow_mulVec_of_mem_fixedCharTuples hFr ha,
      Polynomial.eval_monomial, ← zpow_natCast, ← zpow_mul]
    push_cast
    rw [mul_comm]

end Powers

section Evaluation

variable {τ : Tag} {L : Type} [Field L]

@[expose] def fixedCharEval (M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) (Fr : L →+* L)
    (v : Fin τ.rank → ℤ) : fixedCharTuples M Fr →* Lˣ where
  toFun a := rootChar (a : Fin τ.rank → Lˣ) v
  map_one' := CTTorus.rootChar_one v
  map_mul' a b := CTTorus.rootChar_mul (a : Fin τ.rank → Lˣ) (b : Fin τ.rank → Lˣ) v

theorem fixedCharEval_injective {M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} {Fr : L →+* L} {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) (v : Fin τ.rank → ℤ)
    (hspan : Submodule.span ℤ (Set.range fun j : Fin τ.rank => (M ^ (j : ℕ)) *ᵥ v) = ⊤) :
    Function.Injective (fixedCharEval M Fr v) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have h1 : ∀ u ∈ Set.range (fun j : Fin τ.rank => (M ^ (j : ℕ)) *ᵥ v),
      rootChar (a : Fin τ.rank → Lˣ) u = 1 := by
    rintro _ ⟨j, rfl⟩
    rw [rootChar_pow_mulVec_of_mem_fixedCharTuples hFr a.2]
    have : rootChar (a : Fin τ.rank → Lˣ) v = 1 := ha
    rw [this, one_pow]
  have h2 : ∀ u, rootChar (a : Fin τ.rank → Lˣ) u = 1 := fun u =>
    CTTorus.rootChar_eq_one_of_mem_span h1 (by rw [hspan]; exact Submodule.mem_top)
  exact Subtype.ext (CTTorus.eq_one_of_rootChar_eq_one h2)

theorem exists_mem_fixedCharTuples_of_zpow_eq_one {M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ}
    {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) (v : Fin τ.rank → ℤ)
    (hlin : LinearIndependent ℤ fun j : Fin τ.rank => (M ^ (j : ℕ)) *ᵥ v)
    (hspan : Submodule.span ℤ (Set.range fun j : Fin τ.rank => (M ^ (j : ℕ)) *ᵥ v) = ⊤)
    (c : Lˣ) (hc : c ^ (M.charpoly.eval (q : ℤ)) = 1) :
    ∃ a ∈ fixedCharTuples M Fr, rootChar a v = c := by
  obtain ⟨f, hfv, hfM⟩ := CTTorus.exists_linearMap_of_charpoly M v hlin hspan (q : ℤ)
    (Additive.ofMul c) (by rw [← ofMul_zpow, hc]; rfl)
  have hχ : ∀ u, rootChar (fun i => Additive.toMul (f (Pi.single i 1))) u =
      Additive.toMul (f u) := fun u => CTTorus.prod_zpow_eq_toMul f u
  refine ⟨fun i => Additive.toMul (f (Pi.single i 1)), fun u => ?_, ?_⟩
  · rw [hχ, hχ, hfM, toMul_zsmul, zpow_natCast, CTTorus.map_units_eq_pow hFr]
  · rw [hχ, hfv]
    rfl

theorem fixedCharEval_range {M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} {Fr : L →+* L} {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) (v : Fin τ.rank → ℤ)
    (hlin : LinearIndependent ℤ fun j : Fin τ.rank => (M ^ (j : ℕ)) *ᵥ v)
    (hspan : Submodule.span ℤ (Set.range fun j : Fin τ.rank => (M ^ (j : ℕ)) *ᵥ v) = ⊤) :
    (fixedCharEval M Fr v).range = rootsOfUnity (M.charpoly.eval (q : ℤ)).natAbs L := by
  ext c
  rw [MonoidHom.mem_range, mem_rootsOfUnity, ← CTTorus.zpow_eq_one_iff_natAbs]
  constructor
  · rintro ⟨a, rfl⟩
    have h := rootChar_aeval_mulVec_of_mem_fixedCharTuples hFr a.2 M.charpoly v
    rw [Matrix.aeval_self_charpoly, Matrix.zero_mulVec, rootChar_zero] at h
    exact h.symm
  · intro hc
    obtain ⟨a, ha, hav⟩ := exists_mem_fixedCharTuples_of_zpow_eq_one hFr v hlin hspan c hc
    exact ⟨⟨a, ha⟩, hav⟩

end Evaluation

theorem isCyclic_and_card_fixedCharTuples {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    (M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ)
    (v : Fin τ.rank → ℤ) (hlin : LinearIndependent ℤ fun j : Fin τ.rank => (M ^ (j : ℕ)) *ᵥ v)
    (hspan : Submodule.span ℤ (Set.range fun j : Fin τ.rank => (M ^ (j : ℕ)) *ᵥ v) = ⊤)
    (Fr : L →+* L) {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) {ℓ : ℕ} [CharP L ℓ] (hℓ : ℓ.Prime)
    (hℓq : ℓ ∣ q) (hdet : M.charpoly.coeff 0 = 1 ∨ M.charpoly.coeff 0 = -1)
    (hne : M.charpoly.eval (q : ℤ) ≠ 0) :
    IsCyclic (fixedCharTuples M Fr) ∧
      Nat.card (fixedCharTuples M Fr) = (M.charpoly.eval (q : ℤ)).natAbs := by
  set N := (M.charpoly.eval (q : ℤ)).natAbs
  have hNℓ : ¬ ℓ ∣ N := by
    intro h
    have h1 : (ℓ : ℤ) ∣ M.charpoly.eval (q : ℤ) := Int.natCast_dvd.2 h
    have h2 : (ℓ : ℤ) ∣ M.charpoly.eval (q : ℤ) - M.charpoly.eval 0 :=
      (Int.natCast_dvd_natCast.2 hℓq).trans
        (by simpa using Polynomial.sub_dvd_eval_sub (q : ℤ) 0 M.charpoly)
    have h3 : (ℓ : ℤ) ∣ M.charpoly.coeff 0 := by
      rw [Polynomial.coeff_zero_eq_eval_zero]
      simpa using dvd_sub h1 h2
    have h4 : ℓ ∣ (M.charpoly.coeff 0).natAbs := Int.natCast_dvd.1 h3
    have h5 : (M.charpoly.coeff 0).natAbs = 1 := by rcases hdet with h | h <;> simp [h]
    rw [h5] at h4
    exact hℓ.one_lt.ne' (Nat.dvd_one.1 h4)
  have : NeZero N := ⟨Int.natAbs_ne_zero.2 hne⟩
  have : NeZero (N : L) := ⟨by rwa [Ne, CharP.cast_eq_zero_iff L ℓ]⟩
  have hinj := fixedCharEval_injective hFr v hspan
  let e : fixedCharTuples M Fr ≃* rootsOfUnity N L :=
    (MonoidHom.ofInjective hinj).trans
      (MulEquiv.subgroupCongr (fixedCharEval_range hFr v hlin hspan))
  have hcyc : IsCyclic (rootsOfUnity N L) := inferInstance
  exact ⟨e.isCyclic.2 hcyc, by
    rw [Nat.card_congr e.toEquiv]
    exact HasEnoughRootsOfUnity.natCard_rootsOfUnity L N⟩

theorem rootChar_ne_one_of_mem_fixedCharTuples {τ : Tag} {L : Type} [Field L]
    (M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ)
    (Fr : L →+* L) {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) {p : ℕ} (hp : p.Prime)
    {a : Fin τ.rank → Lˣ} (ha : a ∈ fixedCharTuples M Fr) (hap : ∀ i, a i ^ p = 1)
    (ha1 : a ≠ 1) {α : Fin τ.rank → ℤ} (A : ℤ[X])
    (hA : ∀ β, (Polynomial.aeval M A) *ᵥ β ∈ orbitLattice M α)
    (hpA : ¬ (p : ℤ) ∣ A.eval (q : ℤ)) : rootChar a α ≠ 1 := by
  intro h1
  apply ha1
  have hspan : ∀ u ∈ orbitLattice M α, rootChar a u = 1 := fun u hu => by
    refine CTTorus.rootChar_eq_one_of_mem_span (S := Set.range fun j : ℕ => (M ^ j) *ᵥ α) ?_ hu
    rintro _ ⟨j, rfl⟩
    rw [rootChar_pow_mulVec_of_mem_fixedCharTuples hFr ha, h1, one_pow]
  refine CTTorus.eq_one_of_rootChar_eq_one fun β => ?_
  have e1 : rootChar a β ^ A.eval (q : ℤ) = 1 := by
    rw [← rootChar_aeval_mulVec_of_mem_fixedCharTuples hFr ha]
    exact hspan _ (hA β)
  have e2 : rootChar a β ^ (p : ℤ) = 1 := by
    rw [zpow_natCast]
    exact CTTorus.rootChar_pow_eq_one hap β
  obtain ⟨s, t, hst⟩ := (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.1 hp)).2 hpA
  calc rootChar a β = (rootChar a β ^ (p : ℤ)) ^ s * (rootChar a β ^ A.eval (q : ℤ)) ^ t := by
        rw [← zpow_mul, ← zpow_mul, ← zpow_add, mul_comm (p : ℤ) s,
          mul_comm (A.eval (q : ℤ)) t, hst, zpow_one]
    _ = 1 := by rw [e1, e2, one_zpow, one_zpow, mul_one]

end CFSG.RankThree.PartOne.KE
