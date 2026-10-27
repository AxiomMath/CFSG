module

public import CFSG.RankThree.PartOne.KE.EDualStabilizer
public import CFSG.RankThree.Lattice.SteinbergBIPrimeKernel
public import CFSG.RankThree.PartOne.KE.CTTorusFixed

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Lattice (pair)
open CFSG.RankThree.E6 (charVal charVal_smul charVal_single)
open scoped Matrix Polynomial

namespace CTBlock

theorem aeval_monic_mulVec {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℤ)
    (v : n → ℤ) {P : ℤ[X]} (hP : P.Monic) {s : ℕ} (hs : P.natDegree = s) :
    (Polynomial.aeval M P) *ᵥ v =
      (M ^ s) *ᵥ v + ∑ i ∈ Finset.range s, P.coeff i • ((M ^ i) *ᵥ v) := by
  conv_lhs => rw [hP.as_sum, hs]
  rw [map_add, map_sum]
  simp only [map_pow, Polynomial.aeval_X, Polynomial.aeval_C, map_mul,
    Matrix.add_mulVec, Matrix.sum_mulVec, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec,
    smul_mul_assoc, one_mul]

theorem exists_linearMap_block {r k : ℕ} {Nm : Type*} [AddCommGroup Nm]
    (M : Matrix (Fin r) (Fin r) ℤ) (c : Fin r → Fin r → ℤ) (hk : k < r) (β : Fin r → ℤ)
    (hlin : LinearIndependent ℤ c) (hspan : Submodule.span ℤ (Set.range c) = ⊤)
    (hβ : ∀ j : Fin r, k ≤ (j : ℕ) → c j = (M ^ ((j : ℕ) - k)) *ᵥ β)
    (hstab : ∀ j : Fin r, (j : ℕ) < k →
      M *ᵥ c j ∈ Submodule.span ℤ (c '' {i : Fin r | (i : ℕ) < k}))
    (P : ℤ[X]) (hP : P.Monic) (hPdeg : P.natDegree = r - k)
    (hrel : (Polynomial.aeval M P) *ᵥ β ∈ Submodule.span ℤ (c '' {i : Fin r | (i : ℕ) < k}))
    (q : ℤ) (x : Nm) (hx : (P.eval q) • x = 0) :
    ∃ f : (Fin r → ℤ) →ₗ[ℤ] Nm, (∀ i : Fin r, (i : ℕ) < k → f (c i) = 0) ∧ f β = x ∧
      ∀ u, f (M *ᵥ u) = q • f u := by
  classical
  let b : Module.Basis (Fin r) ℤ (Fin r → ℤ) := Module.Basis.mk hlin hspan.ge
  have hb : ∀ j : Fin r, b j = c j := fun j => Module.Basis.mk_apply hlin _ j
  let g : Fin r → Nm := fun j => if (j : ℕ) < k then 0 else (q ^ ((j : ℕ) - k)) • x
  set f := b.constr ℤ g with hf
  have hfc : ∀ j : Fin r, f (c j) = g j := fun j => by
    have := b.constr_basis ℤ g j
    rwa [hb] at this
  have hf0 : ∀ i : Fin r, (i : ℕ) < k → f (c i) = 0 := fun i hi => by
    rw [hfc]
    simp [g, hi]
  have hfN : ∀ u ∈ Submodule.span ℤ (c '' {i : Fin r | (i : ℕ) < k}), f u = 0 := by
    have : Submodule.span ℤ (c '' {i : Fin r | (i : ℕ) < k}) ≤ LinearMap.ker f := by
      rw [Submodule.span_le]
      rintro _ ⟨i, hi, rfl⟩
      exact hf0 i hi
    exact fun u hu => LinearMap.mem_ker.1 (this hu)
  have hfq : ∀ m : ℕ, k + m < r → f ((M ^ m) *ᵥ β) = (q ^ m) • x := fun m hm => by
    have h1 := hβ ⟨k + m, hm⟩ (by simp)
    simp only [Nat.add_sub_cancel_left] at h1
    rw [← h1, hfc]
    simp [g]
  have hfβ : f β = x := by
    have := hfq 0 (by omega)
    simpa using this
  have h4 : f ∘ₗ (Matrix.mulVecLin M) = q • f := by
    refine b.ext fun j => ?_
    rw [hb, LinearMap.comp_apply, Matrix.mulVecLin_apply, LinearMap.smul_apply]
    by_cases hj : (j : ℕ) < k
    · rw [hf0 j hj, smul_zero]
      exact hfN _ (hstab j hj)
    · have hjk : k ≤ (j : ℕ) := not_lt.1 hj
      have hcj : f (c j) = (q ^ ((j : ℕ) - k)) • x := by
        rw [hfc]
        simp [g, hj]
      have hMc : M *ᵥ c j = (M ^ ((j : ℕ) - k + 1)) *ᵥ β := by
        rw [hβ j hjk, Matrix.mulVec_mulVec, ← pow_succ']
      rw [hMc, hcj, smul_smul, ← pow_succ']
      by_cases hjr : (j : ℕ) + 1 < r
      · have h5 := hfq ((j : ℕ) - k + 1) (by omega)
        rw [h5]
      ·
        have hs : (j : ℕ) - k + 1 = r - k := by omega
        rw [hs]
        have hrel' := aeval_monic_mulVec M β hP hPdeg
        have h6 : f ((Polynomial.aeval M P) *ᵥ β) = 0 := hfN _ hrel
        rw [hrel', map_add, map_sum] at h6
        have h7 : ∀ i ∈ Finset.range (r - k), f (P.coeff i • ((M ^ i) *ᵥ β)) =
            (P.coeff i * q ^ i) • x := fun i hi => by
          rw [map_zsmul, hfq i (by have := Finset.mem_range.1 hi; omega), smul_smul]
        rw [Finset.sum_congr rfl h7, ← Finset.sum_smul] at h6
        have h8 : (q ^ (r - k)) • x +
            (∑ i ∈ Finset.range (r - k), (P.coeff i * q ^ i)) • x = 0 := by
          rw [← add_smul, ← CTTorus.eval_monic_eq hP hPdeg q]
          exact hx
        exact (eq_neg_of_add_eq_zero_left h6).trans (eq_neg_of_add_eq_zero_left h8).symm
  refine ⟨f, hf0, hfβ, fun u => ?_⟩
  exact congrArg (fun g : (Fin r → ℤ) →ₗ[ℤ] Nm => g u) h4

end CTBlock

section Block

variable {τ : Tag} {L : Type} [Field L]

@[expose] def charTrivialOn (T : Set (Fin τ.rank → ℤ)) : Subgroup (Fin τ.rank → Lˣ) where
  carrier := {a | ∀ u ∈ T, rootChar a u = 1}
  mul_mem' {a b} ha hb := fun u hu => by
    rw [CTTorus.rootChar_mul, ha u hu, hb u hu, mul_one]
  one_mem' := fun u _ => CTTorus.rootChar_one u
  inv_mem' {a} ha := fun u hu => by rw [rootChar_inv_apply, ha u hu, inv_one]

theorem mem_charTrivialOn {T : Set (Fin τ.rank → ℤ)} {a : Fin τ.rank → Lˣ} :
    a ∈ charTrivialOn (L := L) T ↔ ∀ u ∈ T, rootChar a u = 1 :=
  Iff.rfl

@[expose] def fixedBlockTuples (M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) (Fr : L →+* L)
    (T : Set (Fin τ.rank → ℤ)) : Subgroup (Fin τ.rank → Lˣ) :=
  fixedCharTuples M Fr ⊓ charTrivialOn T

theorem mem_fixedBlockTuples {M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} {Fr : L →+* L}
    {T : Set (Fin τ.rank → ℤ)} {a : Fin τ.rank → Lˣ} :
    a ∈ fixedBlockTuples M Fr T ↔ a ∈ fixedCharTuples M Fr ∧ ∀ u ∈ T, rootChar a u = 1 :=
  Iff.rfl

end Block

theorem isCyclic_and_card_fixedBlockTuples {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    (M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) (c : Fin τ.rank → Fin τ.rank → ℤ) {k : ℕ}
    (hk : k < τ.rank) (β : Fin τ.rank → ℤ) (hlin : LinearIndependent ℤ c)
    (hspan : Submodule.span ℤ (Set.range c) = ⊤)
    (hβ : ∀ j : Fin τ.rank, k ≤ (j : ℕ) → c j = (M ^ ((j : ℕ) - k)) *ᵥ β)
    (hstab : ∀ j : Fin τ.rank, (j : ℕ) < k →
      M *ᵥ c j ∈ Submodule.span ℤ (c '' {i : Fin τ.rank | (i : ℕ) < k}))
    (P : ℤ[X]) (hP : P.Monic) (hPdeg : P.natDegree = τ.rank - k)
    (hrel : (Polynomial.aeval M P) *ᵥ β ∈
      Submodule.span ℤ (c '' {i : Fin τ.rank | (i : ℕ) < k}))
    (Fr : L →+* L) {q : ℕ} (hFr : ∀ x, Fr x = x ^ q) {ℓ : ℕ} [CharP L ℓ] (hℓ : ℓ.Prime)
    (hℓq : ℓ ∣ q) (hdet : P.coeff 0 = 1 ∨ P.coeff 0 = -1) (hne : P.eval (q : ℤ) ≠ 0) :
    IsCyclic (fixedBlockTuples M Fr (c '' {i : Fin τ.rank | (i : ℕ) < k})) ∧
      Nat.card (fixedBlockTuples M Fr (c '' {i : Fin τ.rank | (i : ℕ) < k})) =
        (P.eval (q : ℤ)).natAbs := by
  classical
  set T : Set (Fin τ.rank → ℤ) := c '' {i : Fin τ.rank | (i : ℕ) < k} with hT
  set Zb : Subgroup (Fin τ.rank → Lˣ) := fixedBlockTuples M Fr T with hZb
  set N := (P.eval (q : ℤ)).natAbs with hN
  have hNℓ : ¬ ℓ ∣ N := by
    intro h
    have h1 : (ℓ : ℤ) ∣ P.eval (q : ℤ) := Int.natCast_dvd.2 h
    have h2 : (ℓ : ℤ) ∣ P.eval (q : ℤ) - P.eval 0 :=
      (Int.natCast_dvd_natCast.2 hℓq).trans
        (by simpa using Polynomial.sub_dvd_eval_sub (q : ℤ) 0 P)
    have h3 : (ℓ : ℤ) ∣ P.coeff 0 := by
      rw [Polynomial.coeff_zero_eq_eval_zero]
      simpa using dvd_sub h1 h2
    have h4 : ℓ ∣ (P.coeff 0).natAbs := Int.natCast_dvd.1 h3
    have h5 : (P.coeff 0).natAbs = 1 := by rcases hdet with h | h <;> simp [h]
    rw [h5] at h4
    exact hℓ.one_lt.ne' (Nat.dvd_one.1 h4)
  have : NeZero N := ⟨Int.natAbs_ne_zero.2 hne⟩
  have : NeZero (N : L) := ⟨by rwa [Ne, CharP.cast_eq_zero_iff L ℓ]⟩
  have hNspan : ∀ a ∈ Zb, ∀ u ∈ Submodule.span ℤ T, rootChar a u = 1 := fun a ha u hu =>
    CTTorus.rootChar_eq_one_of_mem_span ha.2 hu
  let ev : Zb →* Lˣ :=
    { toFun := fun a => rootChar (a : Fin τ.rank → Lˣ) β
      map_one' := CTTorus.rootChar_one β
      map_mul' := fun a b => CTTorus.rootChar_mul (a : Fin τ.rank → Lˣ) (b : Fin τ.rank → Lˣ) β }
  have hev : ∀ a : Zb, ev a = rootChar (a : Fin τ.rank → Lˣ) β := fun a => rfl
  have hinj : Function.Injective ev := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 : ∀ u ∈ Set.range c, rootChar (a : Fin τ.rank → Lˣ) u = 1 := by
      rintro _ ⟨j, rfl⟩
      by_cases hj : (j : ℕ) < k
      · exact a.2.2 _ ⟨j, hj, rfl⟩
      · rw [hβ j (not_lt.1 hj), rootChar_pow_mulVec_of_mem_fixedCharTuples hFr a.2.1]
        have : rootChar (a : Fin τ.rank → Lˣ) β = 1 := ha
        rw [this, one_pow]
    have h2 : ∀ u, rootChar (a : Fin τ.rank → Lˣ) u = 1 := fun u =>
      CTTorus.rootChar_eq_one_of_mem_span h1 (by rw [hspan]; exact Submodule.mem_top)
    exact Subtype.ext (CTTorus.eq_one_of_rootChar_eq_one h2)
  have hrange : ev.range = rootsOfUnity N L := by
    ext y
    rw [MonoidHom.mem_range, mem_rootsOfUnity, ← CTTorus.zpow_eq_one_iff_natAbs]
    constructor
    · rintro ⟨a, rfl⟩
      have h := rootChar_aeval_mulVec_of_mem_fixedCharTuples hFr a.2.1 P β
      rw [hNspan a a.2 _ hrel] at h
      exact h.symm
    · intro hy
      obtain ⟨f, hf0, hfβ, hfM⟩ := CTBlock.exists_linearMap_block M c hk β hlin hspan hβ hstab P
        hP hPdeg hrel (q : ℤ) (Additive.ofMul y) (by rw [← ofMul_zpow, hy]; rfl)
      have hχ : ∀ u, rootChar (fun i => Additive.toMul (f (Pi.single i 1))) u =
          Additive.toMul (f u) := fun u => CTTorus.prod_zpow_eq_toMul f u
      have hmem : (fun i => Additive.toMul (f (Pi.single i 1))) ∈ Zb := by
        refine ⟨fun u => ?_, fun u hu => ?_⟩
        · rw [hχ, hχ, hfM, toMul_zsmul, zpow_natCast, CTTorus.map_units_eq_pow hFr]
        · obtain ⟨i, hi, rfl⟩ := hu
          rw [hχ, hf0 i hi]
          rfl
      refine ⟨⟨_, hmem⟩, ?_⟩
      rw [hev]
      change rootChar (fun i => Additive.toMul (f (Pi.single i 1))) β = y
      rw [hχ, hfβ]
      rfl
  let e : Zb ≃* rootsOfUnity N L :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  have hcyc : IsCyclic (rootsOfUnity N L) := inferInstance
  exact ⟨e.isCyclic.2 hcyc, by
    rw [Nat.card_congr e.toEquiv]
    exact HasEnoughRootsOfUnity.natCard_rootsOfUnity L N⟩

theorem exists_eigencolumn_of_mem_fixedCharTuples {τ : Tag} {L : Type} [Field L]
    (M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) (Fr : L →+* L) {q : ℕ} (hFr : ∀ x, Fr x = x ^ q)
    {p : ℕ} (hp : p.Prime) {a : Fin τ.rank → Lˣ} (ha : a ∈ fixedCharTuples M Fr)
    (hap : ∀ i, a i ^ p = 1) (ha1 : a ≠ 1) :
    ∃ z : Fin τ.rank → ZMod p, z ≠ 0 ∧
      (M.map (Int.cast : ℤ → ZMod p))ᵀ *ᵥ z = (q : ZMod p) • z ∧
        rootCharKernel a = {α | IsRoot τ α ∧ pair α z = 0} := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨i0, hi0⟩ : ∃ i, a i ≠ 1 := by
    by_contra h
    exact ha1 (funext fun i => not_not.1 fun hi => h ⟨i, hi⟩)
  have hord0 : orderOf (a i0) = p := by
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one (hap i0)) with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hi0
    · exact h
  have hprim : IsPrimitiveRoot ((a i0 : Lˣ) : L) p :=
    IsPrimitiveRoot.coe_units_iff.2 (IsPrimitiveRoot.iff_orderOf.2 hord0)
  have hexp : ∀ i, ∃ n : ℕ, a i = (a i0) ^ n := fun i => by
    have hi : ((a i : Lˣ) : L) ^ p = 1 := by
      rw [← Units.val_pow_eq_pow_val, hap i, Units.val_one]
    obtain ⟨n, -, hn⟩ := hprim.eq_pow_of_pow_eq_one hi
    exact ⟨n, Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hn.symm)⟩
  choose e he using hexp
  have hker : ∀ l l' : Fin τ.rank → ℤ, rootChar a l = rootChar a l' ↔
      charVal (fun i => (e i : ZMod p)) l = charVal (fun i => (e i : ZMod p)) l' :=
    fun l l' => rootChar_eq_rootChar_iff hord0 e a he l l'
  refine ⟨fun i => (e i : ZMod p), ?_, ?_, ?_⟩
  · intro hz
    apply ha1
    funext i
    have h1 : (e i : ZMod p) = 0 := congrFun hz i
    rw [he i]
    have : p ∣ e i := (ZMod.natCast_eq_zero_iff _ _).1 h1
    obtain ⟨m, hm⟩ := this
    rw [hm, pow_mul, ← hord0, pow_orderOf_eq_one, one_pow]
    rfl
  · funext j
    have hcq : rootChar a (M *ᵥ Pi.single j 1) = rootChar a ((q : ℤ) • (Pi.single j 1 :
        Fin τ.rank → ℤ)) := by
      rw [mem_fixedCharTuples_iff.1 ha (Pi.single j 1), CTTorus.map_units_eq_pow hFr,
        rootChar_zsmul, zpow_natCast]
    have h1 := (hker _ _).1 hcq
    rw [charVal_smul, charVal_single] at h1
    have h3 : ∀ i, (M *ᵥ (Pi.single j 1 : Fin τ.rank → ℤ)) i = M i j := fun i => by
      rw [Matrix.mulVec_single_one]
      rfl
    have h2 : charVal (fun i => (e i : ZMod p)) (M *ᵥ Pi.single j 1) =
        ((M.map (Int.cast : ℤ → ZMod p))ᵀ *ᵥ fun i => (e i : ZMod p)) j := by
      simp only [charVal, h3]
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.map_apply]
    rw [h2] at h1
    simpa using h1
  · ext α
    have h1 := hker α 0
    rw [rootChar_zero] at h1
    have h0 : charVal (fun i => (e i : ZMod p)) (0 : Fin τ.rank → ℤ) = 0 := by simp [charVal]
    rw [h0] at h1
    change IsRoot τ α ∧ rootChar a α = 1 ↔ IsRoot τ α ∧ charVal (fun i => (e i : ZMod p)) α = 0
    exact and_congr_right fun _ => h1

theorem transpose_eigen_neg {ι : Type} [Fintype ι] {p : ℕ} (A : Matrix ι ι ℤ) (q : ZMod p)
    (z : ι → ZMod p)
    (h : (((-1 : ℤ) • A).map (Int.cast : ℤ → ZMod p))ᵀ *ᵥ z = q • z) :
    (A.map (Int.cast : ℤ → ZMod p))ᵀ *ᵥ z = (-q) • z := by
  rw [neg_one_smul, Matrix.map_neg (Int.cast : ℤ → ZMod p) (fun a => Int.cast_neg a) A,
    Matrix.transpose_neg, Matrix.neg_mulVec] at h
  rw [neg_smul]
  exact neg_eq_iff_eq_neg.1 h

end CFSG.RankThree.PartOne.KE
