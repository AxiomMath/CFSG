module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Semisimple
import CFSG.GroupTheory.ABGLocalTools.FrobeniusFixedPoints

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix Module

section Diagonalize

variable {L : Type*} [Field L]

theorem exists_basis_common_eigenvectors_of_isAlgClosed [IsAlgClosed L] {V : Type*}
    [AddCommGroup V] [Module L V] [FiniteDimensional L V] {ι : Type*} (f : ι → Module.End L V)
    (hcomm : ∀ i j, Commute (f i) (f j)) (hss : ∀ i, (f i).IsFinitelySemisimple) :
    ∃ (b : Basis (Fin (finrank L V)) L V) (μ : ι → Fin (finrank L V) → L),
      ∀ i j, f i (b j) = μ i j • b j := by
  classical
  obtain ⟨hind, htop⟩ := CFSG.ABGLocalTools.iSupIndep_iInf_eigenspace_and_iSup_eq_top f hcomm hss
  set W : (ι → L) → Submodule L V := fun χ => ⨅ i, Module.End.eigenspace (f i) (χ i) with hWdef
  have hint : DirectSum.IsInternal W :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  let bW := fun χ => Basis.ofVectorSpace L (W χ)
  let b₀ := hint.collectedBasis bW
  have : Finite (Σ χ, Basis.ofVectorSpaceIndex L (W χ)) := Module.Finite.finite_basis b₀
  let e₀ : (Σ χ, Basis.ofVectorSpaceIndex L (W χ)) ≃ Fin (finrank L V) :=
    (Finite.equivFin _).trans (finCongr (Module.finrank_eq_nat_card_basis b₀).symm)
  refine ⟨b₀.reindex e₀, fun i j => (e₀.symm j).1 i, fun i j => ?_⟩
  have hmem : b₀ (e₀.symm j) ∈ W (e₀.symm j).1 := hint.collectedBasis_mem bW (e₀.symm j)
  rw [Basis.reindex_apply]
  exact Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hmem i)

theorem exists_simultaneous_diagonal [IsAlgClosed L] {n : Type*} [Fintype n] [DecidableEq n]
    {ι : Type*} (A : ι → Matrix n n L) (hcomm : ∀ i j, A i * A j = A j * A i)
    (hord : ∀ i, ∃ m : ℕ, (m : L) ≠ 0 ∧ A i ^ m = 1) :
    ∃ P : Matrix n n L, IsUnit P ∧ ∃ d : ι → n → L, ∀ i, A i * P = P * diagonal (d i) := by
  classical
  let f : ι → Module.End L (n → L) := fun i => Matrix.toLin' (A i)
  have hcomm' : ∀ i j, Commute (f i) (f j) := by
    intro i j
    have h := congrArg Matrix.toLin' (hcomm i j)
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul] at h
    exact h
  have hss : ∀ i, (f i).IsFinitelySemisimple := by
    intro i
    obtain ⟨m, hm, hAm⟩ := hord i
    refine CFSG.ABGLocalTools.isFinitelySemisimple_of_pow_eq_one (m := m) ?_ hm
    change Matrix.toLin' (A i) ^ m = 1
    rw [← Matrix.toLin'_pow, hAm, Matrix.toLin'_one]
    rfl
  obtain ⟨b, μ, hb⟩ := exists_basis_common_eigenvectors_of_isAlgClosed f hcomm' hss
  have hcard : finrank L (n → L) = Fintype.card n := Module.finrank_fintype_fun_eq_card L
  let e : Fin (finrank L (n → L)) ≃ n := (finCongr hcard).trans (Fintype.equivFin n).symm
  let b' := b.reindex e
  refine ⟨(Pi.basisFun L n).toMatrix b', ?_, fun i k => μ i (e.symm k), fun i => ?_⟩
  · have := (Pi.basisFun L n).invertibleToMatrix b'
    exact isUnit_of_invertible _
  · ext k j
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    simp only [Basis.toMatrix_apply, Pi.basisFun_repr]
    have h2 : b' j = b (e.symm j) := by simp [b']
    have h3 := congrFun (hb i (e.symm j)) k
    simp only [f, Matrix.toLin'_apply, Pi.smul_apply, smul_eq_mul] at h3
    rw [h2, mul_comm _ (μ i (e.symm j)), ← h3]
    rfl

theorem mem_range_of_mulVec_eq_smul {n : Type*} [Fintype n] [DecidableEq n]
    {A P : Matrix n n L} (hP : IsUnit P) {d : n → L} (hAP : A * P = P * diagonal d)
    {u : n → L} (hu : u ≠ 0) {μ : L} (h : A *ᵥ u = μ • u) : μ ∈ Set.range d := by
  have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  set z := P⁻¹ *ᵥ u with hz
  have hPz : P *ᵥ z = u := by
    rw [hz, mulVec_mulVec, mul_nonsing_inv _ hPdet, one_mulVec]
  have hz0 : z ≠ 0 := by
    intro h0
    apply hu
    rw [← hPz, h0, mulVec_zero]
  have hdz : diagonal d *ᵥ z = μ • z := by
    have hdiag : diagonal d = P⁻¹ * A * P := by
      rw [Matrix.mul_assoc, hAP, ← Matrix.mul_assoc, nonsing_inv_mul _ hPdet, Matrix.one_mul]
    rw [hdiag, ← mulVec_mulVec, hPz, ← mulVec_mulVec, h, mulVec_smul]
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hz0
  refine ⟨j, ?_⟩
  have := congrFun hdz j
  rw [mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at this
  exact mul_right_cancel₀ hj this

theorem pow_eq_one_of_mul_eq_mul_diagonal {n : Type*} [Fintype n] [DecidableEq n]
    {A P : Matrix n n L} (hP : IsUnit P) {d : n → L} (hAP : A * P = P * diagonal d) {m : ℕ}
    (hm : A ^ m = 1) (j : n) : d j ^ m = 1 := by
  have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hdiag : diagonal d = P⁻¹ * A * P := by
    rw [Matrix.mul_assoc, hAP, ← Matrix.mul_assoc, nonsing_inv_mul _ hPdet, Matrix.one_mul]
  have hPP : P * P⁻¹ = 1 := mul_nonsing_inv _ hPdet
  have hpow : ∀ k : ℕ, diagonal d ^ k = P⁻¹ * A ^ k * P := by
    intro k
    induction k with
    | zero => simp [nonsing_inv_mul _ hPdet]
    | succ k ih =>
      rw [pow_succ, ih, hdiag, pow_succ]
      calc P⁻¹ * A ^ k * P * (P⁻¹ * A * P) = P⁻¹ * A ^ k * (P * P⁻¹) * A * P := by
            simp only [Matrix.mul_assoc]
        _ = P⁻¹ * (A ^ k * A) * P := by rw [hPP, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have hpm := hpow m
  rw [hm, Matrix.mul_one, nonsing_inv_mul _ hPdet, diagonal_pow] at hpm
  have := congrFun (congrFun hpm j) j
  simpa using this

end Diagonalize

section GeneralLinear

variable {K : Type*} [Field K]

variable {n : ℕ}

noncomputable abbrev toAlgClosure (M : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin n) (Fin n) (AlgebraicClosure K) :=
  (algebraMap K (AlgebraicClosure K)).mapMatrix M

theorem toAlgClosure_injective :
    Function.Injective (toAlgClosure : Matrix (Fin n) (Fin n) K → _) := fun _ _ h =>
  Matrix.ext fun i j => (algebraMap K (AlgebraicClosure K)).injective (congrFun (congrFun h i) j)

theorem toAlgClosure_det (M : Matrix (Fin n) (Fin n) K) :
    (toAlgClosure M).det = algebraMap K (AlgebraicClosure K) M.det :=
  (RingHom.map_det _ M).symm

theorem toAlgClosure_mul (M N : Matrix (Fin n) (Fin n) K) :
    toAlgClosure (M * N) = toAlgClosure M * toAlgClosure N :=
  map_mul (algebraMap K (AlgebraicClosure K)).mapMatrix M N

theorem toAlgClosure_pow (M : Matrix (Fin n) (Fin n) K) (m : ℕ) :
    toAlgClosure (M ^ m) = toAlgClosure M ^ m :=
  map_pow (algebraMap K (AlgebraicClosure K)).mapMatrix M m

theorem toAlgClosure_one : toAlgClosure (1 : Matrix (Fin n) (Fin n) K) = 1 :=
  map_one (algebraMap K (AlgebraicClosure K)).mapMatrix

theorem card_le_of_isConj_pow {r : ℕ} [Fact r.Prime]
    (hr : (r : K) ≠ 0) {x : GL (Fin n) K} (hxr : x ^ r = 1) (hx1 : x ≠ 1)
    (Q : Finset (ZMod r)) (hQ : ∀ k ∈ Q, IsConj x (x ^ k.val)) :
    Q.card ≤ n := by
  classical
  set f := algebraMap K (AlgebraicClosure K)
  set A := toAlgClosure (x : Matrix (Fin n) (Fin n) K) with hA
  have hAr : A ^ r = 1 := by
    rw [hA, ← toAlgClosure_pow, ← Units.val_pow_eq_pow_val, hxr, Units.val_one, toAlgClosure_one]
  have hrL : (r : AlgebraicClosure K) ≠ 0 := by
    rw [← map_natCast f]
    exact (map_ne_zero f).mpr hr
  obtain ⟨P, hP, d, hd⟩ := exists_simultaneous_diagonal (fun _ : Unit => A) (fun _ _ => rfl)
    (fun _ => ⟨r, hrL, hAr⟩)
  have hAP : A * P = P * diagonal (d ()) := hd ()
  have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  obtain ⟨i, hi⟩ : ∃ i, d () i ≠ 1 := by
    by_contra h
    push Not at h
    apply hx1
    have hd1 : diagonal (d ()) = 1 := by
      rw [← Matrix.diagonal_one]
      exact congrArg diagonal (funext h)
    have hA1 : A = 1 := by
      have := hAP
      rw [hd1, Matrix.mul_one] at this
      calc A = A * P * P⁻¹ := by rw [Matrix.mul_assoc, mul_nonsing_inv _ hPdet, Matrix.mul_one]
        _ = 1 := by rw [this, mul_nonsing_inv _ hPdet]
    apply Units.ext
    apply toAlgClosure_injective
    rw [← hA, hA1, Units.val_one, toAlgClosure_one]
  set l := d () i with hl
  have hlr : l ^ r = 1 := pow_eq_one_of_mul_eq_mul_diagonal hP hAP hAr i
  have hord : orderOf l = r := orderOf_eq_prime hlr hi
  set v := P *ᵥ Pi.single i 1 with hv
  have hv0 : v ≠ 0 := by
    intro h0
    have h := congrArg (fun z => P⁻¹ *ᵥ z) h0
    simp only [hv, mulVec_mulVec, nonsing_inv_mul _ hPdet, one_mulVec, mulVec_zero] at h
    have := congrFun h i
    simp at this
  have hAv : A *ᵥ v = l • v := by
    have hs : Pi.single i (d () i * 1) = l • (Pi.single i 1 : Fin n → AlgebraicClosure K) := by
      ext j
      by_cases h : j = i
      · subst h
        simp [hl]
      · simp [h]
    rw [hv, mulVec_mulVec, hAP, ← mulVec_mulVec, diagonal_mulVec_single, hs, mulVec_smul]
  have hApv : ∀ m : ℕ, A ^ m *ᵥ v = l ^ m • v := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, hAv, smul_smul, ← pow_succ]
  have hmem : ∀ k ∈ Q, l ^ k.val ∈ Set.range (d ()) := by
    intro k hk
    obtain ⟨c, hc⟩ := hQ k hk
    have hcx : (c : GL (Fin n) K) * x = x ^ k.val * c := hc
    set C := toAlgClosure ((c : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    set Ci := toAlgClosure (((c⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K)
    have hCiC : Ci * C = 1 := by
      rw [← toAlgClosure_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, toAlgClosure_one]
    have hCA : C * A = A ^ k.val * C := by
      rw [← toAlgClosure_mul, ← Units.val_mul, hcx, Units.val_mul, toAlgClosure_mul,
        Units.val_pow_eq_pow_val, toAlgClosure_pow]
    have hACi : A * Ci = Ci * A ^ k.val := by
      have hCCi : C * Ci = 1 := by
        rw [← toAlgClosure_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, toAlgClosure_one]
      calc A * Ci = Ci * (C * A) * Ci := by
            rw [← Matrix.mul_assoc, hCiC, Matrix.one_mul]
        _ = Ci * A ^ k.val * (C * Ci) := by rw [hCA]; simp only [Matrix.mul_assoc]
        _ = Ci * A ^ k.val := by rw [hCCi, Matrix.mul_one]
    have hAkv : A ^ k.val *ᵥ v = l ^ k.val • v := hApv k.val
    have hu0 : Ci *ᵥ v ≠ 0 := by
      intro h0
      apply hv0
      have h := congrArg (fun z => C *ᵥ z) h0
      have hCCi : C * Ci = 1 := by
        rw [← toAlgClosure_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, toAlgClosure_one]
      simpa only [mulVec_mulVec, hCCi, one_mulVec, mulVec_zero] using h
    refine mem_range_of_mulVec_eq_smul hP hAP hu0 ?_
    rw [mulVec_mulVec, hACi, ← mulVec_mulVec, hAkv, mulVec_smul]
  have hinj : Set.InjOn (fun k : ZMod r => l ^ k.val) Q := by
    intro a _ b _ hab
    have hab' : l ^ a.val = l ^ b.val := hab
    have hfin : IsOfFinOrder l := orderOf_pos_iff.mp (hord ▸ (Fact.out : r.Prime).pos)
    have h := (IsOfFinOrder.pow_inj_mod hfin).mp hab'
    rw [hord, Nat.mod_eq_of_lt (ZMod.val_lt a), Nat.mod_eq_of_lt (ZMod.val_lt b)] at h
    exact ZMod.val_injective r h
  calc Q.card ≤ (Finset.univ.image (d ())).card := by
        refine Finset.card_le_card_of_injOn _ (fun k hk => ?_) hinj
        obtain ⟨j, hj⟩ := hmem k hk
        exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩
    _ ≤ Finset.univ.card := Finset.card_image_le
    _ = n := by simp

theorem card_le_three_of_isConj_pow [Finite K] {r : ℕ} [Fact r.Prime]
    (hr : (r : K) ≠ 0) {x : GL (Fin 3) K} (hxr : x ^ r = 1) (hx1 : x ≠ 1)
    (Q : Finset (ZMod r)) (hQ : ∀ k ∈ Q, k ≠ 0 ∧ IsConj x (x ^ k.val)) :
    Q.card ≤ 3 :=
  card_le_of_isConj_pow hr hxr hx1 Q fun k hk => (hQ k hk).2

theorem exists_diagonal_of_elementary {r : ℕ} (hr : (r : K) ≠ 0) (E : Subgroup (GL (Fin 3) K))
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hexp : ∀ a ∈ E, a ^ r = 1)
    (hdet : ∀ a ∈ E, (a : Matrix (Fin 3) (Fin 3) K).det = 1) :
    ∃ P : Matrix (Fin 3) (Fin 3) (AlgebraicClosure K), IsUnit P ∧
      ∃ d : E → Fin 3 → AlgebraicClosure K,
        (∀ a : E, toAlgClosure (((a : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) * P =
          P * diagonal (d a)) ∧
        Function.Injective d ∧ (∀ a j, d a j ^ r = 1) ∧ ∀ a, d a 0 * d a 1 * d a 2 = 1 := by
  set f := algebraMap K (AlgebraicClosure K)
  set A : E → Matrix (Fin 3) (Fin 3) (AlgebraicClosure K) :=
    fun a => toAlgClosure (((a : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) with hA
  have hrL : (r : AlgebraicClosure K) ≠ 0 := by
    rw [← map_natCast f]
    exact (map_ne_zero f).mpr hr
  have hAr : ∀ a, A a ^ r = 1 := fun a => by
    rw [hA, ← toAlgClosure_pow, ← Units.val_pow_eq_pow_val, hexp _ a.2, Units.val_one,
      toAlgClosure_one]
  have hAcomm : ∀ a b, A a * A b = A b * A a := fun a b => by
    rw [hA, ← toAlgClosure_mul, ← toAlgClosure_mul, ← Units.val_mul, ← Units.val_mul,
      hcomm _ a.2 _ b.2]
  obtain ⟨P, hP, d, hd⟩ := exists_simultaneous_diagonal A hAcomm (fun a => ⟨r, hrL, hAr a⟩)
  have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  refine ⟨P, hP, d, hd, ?_, fun a j => pow_eq_one_of_mul_eq_mul_diagonal hP (hd a) (hAr a) j,
    fun a => ?_⟩
  · intro a b hab
    have hAab : A a = A b := by
      calc A a = A a * P * P⁻¹ := by
            rw [Matrix.mul_assoc, mul_nonsing_inv _ hPdet, Matrix.mul_one]
        _ = A b * P * P⁻¹ := by rw [hd a, hd b, hab]
        _ = A b := by rw [Matrix.mul_assoc, mul_nonsing_inv _ hPdet, Matrix.mul_one]
    exact Subtype.ext (Units.ext (toAlgClosure_injective hAab))
  · have h := congrArg Matrix.det (hd a)
    rw [det_mul, det_mul, det_diagonal, Fin.prod_univ_three] at h
    have hdetA : (A a).det = 1 := by
      rw [hA, toAlgClosure_det, hdet _ a.2, map_one]
    rw [hdetA, one_mul] at h
    exact (mul_left_cancel₀ hPdet.ne_zero (h.symm.trans (mul_one _).symm) :)

theorem exists_diagonal_pair_injective {r : ℕ} (hr : (r : K) ≠ 0)
    (E : Subgroup (GL (Fin 3) K))
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hexp : ∀ a ∈ E, a ^ r = 1)
    (hdet : ∀ a ∈ E, (a : Matrix (Fin 3) (Fin 3) K).det = 1) :
    ∃ P : Matrix (Fin 3) (Fin 3) (AlgebraicClosure K), IsUnit P ∧
      ∃ d : E → Fin 3 → AlgebraicClosure K,
        (∀ a : E, toAlgClosure (((a : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) * P =
          P * diagonal (d a)) ∧ (∀ a j, d a j ^ r = 1) ∧ (∀ a, d a 0 * d a 1 * d a 2 = 1) ∧
        Function.Injective fun a => (d a 0, d a 1) := by
  obtain ⟨P, hP, d, hd, hinj, hpow, hprod⟩ := exists_diagonal_of_elementary hr E hcomm hexp hdet
  refine ⟨P, hP, d, hd, hpow, hprod, ?_⟩
  intro a b hab
  simp only [Prod.mk.injEq] at hab
  apply hinj
  funext j
  fin_cases j
  · exact hab.1
  · exact hab.2
  · have ha := hprod a
    have hb := hprod b
    rw [hab.1, hab.2] at ha
    have hne : d b 0 * d b 1 ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hb
      exact zero_ne_one hb
    exact mul_left_cancel₀ hne (ha.trans hb.symm)

theorem card_le_sq_of_elementary [Finite K] {r : ℕ} [Fact r.Prime]
    (hr : (r : K) ≠ 0) (E : Subgroup (GL (Fin 3) K))
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hexp : ∀ a ∈ E, a ^ r = 1)
    (hdet : ∀ a ∈ E, (a : Matrix (Fin 3) (Fin 3) K).det = 1) :
    Nat.card E ≤ r ^ 2 := by
  classical
  obtain ⟨-, -, d, -, hpow, -, hinj⟩ := exists_diagonal_pair_injective hr E hcomm hexp hdet
  set R := (Polynomial.nthRoots r (1 : AlgebraicClosure K)).toFinset with hRdef
  have hR : R.card ≤ r := (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots r 1)
  have hmemR : ∀ a j, d a j ∈ R := fun a j => by
    rw [hRdef, Multiset.mem_toFinset, Polynomial.mem_nthRoots (Fact.out : r.Prime).pos]
    exact hpow a j
  let Ψ : E → (R ×ˢ R : Finset (AlgebraicClosure K × AlgebraicClosure K)) :=
    fun a => ⟨(d a 0, d a 1), Finset.mem_product.mpr ⟨hmemR a 0, hmemR a 1⟩⟩
  have hΨ : Function.Injective Ψ := fun a b hab => hinj (congrArg Subtype.val hab)
  calc Nat.card E ≤ Nat.card (R ×ˢ R : Finset (AlgebraicClosure K × AlgebraicClosure K)) :=
        Nat.card_le_card_of_injective Ψ hΨ
    _ = R.card * R.card := by rw [Nat.card_eq_finsetCard, Finset.card_product]
    _ ≤ r ^ 2 := by
        rw [sq]
        exact Nat.mul_le_mul hR hR

theorem exists_scalar_of_card_eq_nine [Finite K] (h3 : (3 : K) ≠ 0)
    (E : Subgroup (GL (Fin 3) K))
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hexp : ∀ a ∈ E, a ^ 3 = 1)
    (hdet : ∀ a ∈ E, (a : Matrix (Fin 3) (Fin 3) K).det = 1) (hcard : Nat.card E = 9) :
    ∃ a ∈ E, a ≠ 1 ∧ ∃ c : K, (a : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) c := by
  classical
  have h3' : ((3 : ℕ) : K) ≠ 0 := by exact_mod_cast h3
  obtain ⟨P, hP, d, hd, hpow, hprod, hinj⟩ := exists_diagonal_pair_injective h3' E hcomm hexp hdet
  set R := (Polynomial.nthRoots 3 (1 : AlgebraicClosure K)).toFinset with hRdef
  have hR : R.card ≤ 3 := (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots 3 1)
  have hmemR : ∀ z : AlgebraicClosure K, z ∈ R ↔ z ^ 3 = 1 := fun z => by
    rw [hRdef, Multiset.mem_toFinset, Polynomial.mem_nthRoots (by norm_num)]
  let Ψ : E → (R ×ˢ R : Finset (AlgebraicClosure K × AlgebraicClosure K)) :=
    fun a => ⟨(d a 0, d a 1),
      Finset.mem_product.mpr ⟨(hmemR _).mpr (hpow a 0), (hmemR _).mpr (hpow a 1)⟩⟩
  have hΨ : Function.Injective Ψ := fun a b hab => hinj (congrArg Subtype.val hab)
  have hRR : Nat.card (R ×ˢ R : Finset (AlgebraicClosure K × AlgebraicClosure K)) =
      R.card * R.card := by
    rw [Nat.card_eq_finsetCard, Finset.card_product]
  have hle := Nat.card_le_card_of_injective Ψ hΨ
  rw [hcard, hRR] at hle
  have hR3 : R.card = 3 := by
    rcases Nat.lt_or_ge R.card 3 with h | h
    · have : R.card * R.card ≤ 2 * 2 := Nat.mul_le_mul (by omega) (by omega)
      omega
    · omega
  have hsurj : Function.Surjective Ψ :=
    (Function.Injective.bijective_of_nat_card_le hΨ (by rw [hcard, hRR, hR3])).2
  obtain ⟨ω, hωR, hω1⟩ := Finset.exists_mem_ne (by omega : 1 < R.card) 1
  have hω3 : ω ^ 3 = 1 := (hmemR ω).mp hωR
  obtain ⟨a, ha⟩ := hsurj ⟨(ω, ω), Finset.mem_product.mpr ⟨hωR, hωR⟩⟩
  have h01 : (d a 0, d a 1) = (ω, ω) := congrArg Subtype.val ha
  simp only [Prod.mk.injEq] at h01
  have hω0 : ω ≠ 0 := by
    intro h0
    rw [h0] at hω3
    norm_num at hω3
  have h2 : d a 2 = ω := by
    have h := hprod a
    rw [h01.1, h01.2] at h
    have hωω : ω * ω ≠ 0 := mul_ne_zero hω0 hω0
    exact mul_left_cancel₀ hωω (h.trans (by rw [← hω3]; ring))
  have hda : d a = fun _ => ω := by
    funext j
    fin_cases j
    · exact h01.1
    · exact h01.2
    · exact h2
  have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hAa : toAlgClosure (((a : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.scalar (Fin 3) ω := by
    have h := hd a
    have hsc : P * diagonal (d a) = Matrix.scalar (Fin 3) ω * P := by
      rw [hda, ← Matrix.scalar_apply, (Matrix.scalar_commute ω (fun _ => mul_comm _ _) P).eq]
    rw [hsc] at h
    calc toAlgClosure (((a : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K)
        = toAlgClosure (((a : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) * P * P⁻¹ := by
          rw [Matrix.mul_assoc, mul_nonsing_inv _ hPdet, Matrix.mul_one]
      _ = Matrix.scalar (Fin 3) ω := by
          rw [h, Matrix.mul_assoc, mul_nonsing_inv _ hPdet, Matrix.mul_one]
  refine ⟨a, a.2, ?_, ((a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0, ?_⟩
  · intro h1
    apply hω1
    have h := congrFun (congrFun hAa 0) 0
    rw [show (a : GL (Fin 3) K) = 1 from h1, Units.val_one, toAlgClosure_one] at h
    simpa using h.symm
  · ext i j
    apply (algebraMap K (AlgebraicClosure K)).injective
    have hij := congrFun (congrFun hAa i) j
    have h00 := congrFun (congrFun hAa 0) 0
    simp only [toAlgClosure, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.scalar_apply,
      Matrix.diagonal_apply] at hij h00 ⊢
    by_cases hij' : i = j
    · subst hij'
      simp only [ite_true] at hij h00 ⊢
      rw [hij, h00]
    · simp only [hij', ite_false] at hij ⊢
      rw [hij, map_zero]

end GeneralLinear

end CFSG.RankThree.SubgroupLists
