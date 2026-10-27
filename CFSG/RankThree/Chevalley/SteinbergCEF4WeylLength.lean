module

public import CFSG.RankThree.Chevalley.EWeylLengthPolynomials
public import CFSG.LieType.Chevalley.LatticeWeylGroup
public import CFSG.Monster.SteinbergBQOddPrimeCongruenceTorsionFree

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Timmesfeld.ExceptionalOrders

namespace F4Weyl

@[expose] def f4J : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ :=
  !![0, 0, 0, 2; 0, 0, 2, 0; 0, 1, 0, 0; 1, 0, 0, 0]

@[expose] def reflT (i : Fin Tag.F4.rank) : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ :=
  Matrix.of fun k l => (if k = l then 1 else 0) - if l = i then Tag.F4.cartan i k else 0

@[expose] def invTranspose (w : (Module.End ℤ (Fin Tag.F4.rank → ℤ))ˣ) :
    Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ :=
  (LinearMap.toMatrix' (↑w⁻¹ : Module.End ℤ (Fin Tag.F4.rank → ℤ))).transpose

@[expose] def charMatrices : Set (Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ) :=
  invTranspose '' (latticeWeylGroup .F4 : Set (Module.End ℤ (Fin Tag.F4.rank → ℤ))ˣ)

theorem invTranspose_one : invTranspose 1 = 1 := by
  rw [invTranspose, inv_one, Units.val_one, LinearMap.toMatrix'_one, Matrix.transpose_one]

theorem invTranspose_mul (a b : (Module.End ℤ (Fin Tag.F4.rank → ℤ))ˣ) :
    invTranspose (a * b) = invTranspose a * invTranspose b := by
  rw [invTranspose, invTranspose, invTranspose, mul_inv_rev, Units.val_mul,
    LinearMap.toMatrix'_mul, Matrix.transpose_mul]

theorem invTranspose_reflectUnit (i : Fin Tag.F4.rank) :
    invTranspose (reflectUnit .F4 i) = reflT i := by
  ext k l
  rw [invTranspose, Matrix.transpose_apply, LinearMap.toMatrix'_apply]
  change reflect .F4 i (Pi.single k 1) l = reflT i k l
  rw [reflect]
  simp only [reflT, Matrix.of_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  by_cases hkl : k = l <;> by_cases hli : l = i <;> simp [hkl, hli, eq_comm]

theorem f4J_mul_f4J :
    f4J * f4J = (2 : ℤ) • (1 : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ) := by
  decide

theorem f4J_mul_reflT (i : Fin Tag.F4.rank) : f4J * reflT i = reflT (Fin.rev i) * f4J := by
  revert i
  decide

theorem mem_charMatrices {u : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ} :
    u ∈ charMatrices ↔ ∃ w : WeylGroup .F4, invTranspose (weylToAut .F4 w) = u := by
  rw [charMatrices, ← range_weylToAut]
  constructor
  · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
    exact ⟨w, rfl⟩
  · rintro ⟨w, rfl⟩
    exact ⟨_, ⟨w, rfl⟩, rfl⟩

theorem invTranspose_weylToAut_mul (w v : WeylGroup .F4) :
    invTranspose (weylToAut .F4 (w * v)) =
      invTranspose (weylToAut .F4 w) * invTranspose (weylToAut .F4 v) := by
  rw [map_mul, invTranspose_mul]

theorem invTranspose_weylToAut_simple (i : Fin Tag.F4.rank) :
    invTranspose (weylToAut .F4 (simple .F4 i)) = reflT i := by
  rw [weylToAut_simple, invTranspose_reflectUnit]

theorem invTranspose_weylToAut_mul_inv (w : WeylGroup .F4) :
    invTranspose (weylToAut .F4 w) * invTranspose (weylToAut .F4 w⁻¹) = 1 := by
  rw [← invTranspose_weylToAut_mul, mul_inv_cancel, map_one, invTranspose_one]

theorem exists_f4J_mul_eq (w : WeylGroup .F4) : ∃ w' : WeylGroup .F4,
    f4J * invTranspose (weylToAut .F4 w) = invTranspose (weylToAut .F4 w') * f4J := by
  induction w using (coxeterSystem .F4).simple_induction_left with
  | one => exact ⟨1, by rw [map_one, invTranspose_one, mul_one, one_mul]⟩
  | mul_simple_left w i ih =>
    obtain ⟨w', hw'⟩ := ih
    refine ⟨simple .F4 (Fin.rev i) * w', ?_⟩
    rw [invTranspose_weylToAut_mul, invTranspose_weylToAut_mul, invTranspose_weylToAut_simple,
      invTranspose_weylToAut_simple, ← mul_assoc, f4J_mul_reflT, mul_assoc, hw', mul_assoc]

theorem exists_f4J_mul_eq' (w' : WeylGroup .F4) : ∃ w : WeylGroup .F4,
    f4J * invTranspose (weylToAut .F4 w) = invTranspose (weylToAut .F4 w') * f4J := by
  induction w' using (coxeterSystem .F4).simple_induction_left with
  | one => exact ⟨1, by rw [map_one, invTranspose_one, mul_one, one_mul]⟩
  | mul_simple_left w' i ih =>
    obtain ⟨w, hw⟩ := ih
    refine ⟨simple .F4 (Fin.rev i) * w, ?_⟩
    rw [invTranspose_weylToAut_mul, invTranspose_weylToAut_mul, invTranspose_weylToAut_simple,
      invTranspose_weylToAut_simple, ← mul_assoc, f4J_mul_reflT, Fin.rev_rev, mul_assoc, hw,
      mul_assoc]

theorem image_f4J_mul_charMatrices :
    (fun u => f4J * u) '' charMatrices = (fun u => u * f4J) '' charMatrices := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨w, rfl⟩ := mem_charMatrices.1 hu
    obtain ⟨w', hw'⟩ := exists_f4J_mul_eq w
    exact ⟨_, mem_charMatrices.2 ⟨w', rfl⟩, hw'.symm⟩
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨w', rfl⟩ := mem_charMatrices.1 hu
    obtain ⟨w, hw⟩ := exists_f4J_mul_eq' w'
    exact ⟨_, mem_charMatrices.2 ⟨w, rfl⟩, hw⟩

@[expose] def longestWord : List (Fin 4) :=
  [0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3]

theorem list_prod_smul (l : List (Fin 4)) (v : Fin Tag.F4.rank → ℤ) :
    (l.map fun i : Fin 4 => simple .F4 ⟨i.1, i.2⟩).prod • v =
      l.foldr (fun i v => reflect .F4 ⟨i.1, i.2⟩ v) v := by
  induction l with
  | nil => simp
  | cons i l ih => rw [List.map_cons, List.prod_cons, mul_smul, ih, simple_smul, List.foldr_cons]

theorem longestWord_single :
    ∀ j : Fin Tag.F4.rank, longestWord.foldr (fun i v => reflect .F4 ⟨i.1, i.2⟩ v)
      (Pi.single j 1) = -Pi.single j 1 := by
  decide

theorem weylToAut_longest :
    weylToAut .F4 (longestWord.map fun i : Fin 4 => simple .F4 ⟨i.1, i.2⟩).prod = -1 := by
  refine Units.ext (LinearMap.pi_ext fun j x => ?_)
  rw [weylToAut_apply, ← mul_one x, ← smul_eq_mul, Pi.single_smul, smul_comm, list_prod_smul,
    longestWord_single, Units.val_neg, Units.val_one, LinearMap.neg_apply, Module.End.one_apply,
    smul_neg]

theorem neg_one_mem_latticeWeylGroup :
    (-1 : (Module.End ℤ (Fin Tag.F4.rank → ℤ))ˣ) ∈ latticeWeylGroup .F4 := by
  rw [← range_weylToAut]
  exact ⟨_, weylToAut_longest⟩

theorem invTranspose_neg_one : invTranspose (-1) = -1 := by
  rw [invTranspose, inv_neg, inv_one, Units.val_neg, Units.val_one, map_neg,
    LinearMap.toMatrix'_one, Matrix.transpose_neg, Matrix.transpose_one]

theorem one_mem_charMatrices : (1 : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ) ∈ charMatrices :=
  ⟨1, one_mem _, invTranspose_one⟩

theorem neg_one_mem_charMatrices :
    (-1 : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ) ∈ charMatrices :=
  ⟨-1, neg_one_mem_latticeWeylGroup, invTranspose_neg_one⟩

theorem mul_reflT_apply (X : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ)
    (i k l : Fin Tag.F4.rank) :
    (X * reflT i) k l = X k l - if l = i then ∑ m, X k m * Tag.F4.cartan i m else 0 := by
  rw [Matrix.mul_apply]
  by_cases hli : l = i
  · subst hli
    simp [reflT, mul_sub, Finset.sum_sub_distrib, Finset.sum_ite_eq']
  · simp [reflT, hli, Finset.sum_ite_eq']

theorem reflT_mul_apply (X : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ)
    (i k l : Fin Tag.F4.rank) :
    (reflT i * X) k l = X k l - Tag.F4.cartan i k * X i l := by
  rw [Matrix.mul_apply]
  simp [reflT, sub_mul, Finset.sum_sub_distrib, ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem eq_scalar_of_commute_reflT {X : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ}
    (h : ∀ i, X * reflT i = reflT i * X) :
    X = Matrix.scalar (Fin Tag.F4.rank) (X ⟨0, by decide⟩ ⟨0, by decide⟩) := by
  have key : ∀ i k l, (if l = i then ∑ m, X k m * Tag.F4.cartan i m else 0) =
      Tag.F4.cartan i k * X i l := by
    intro i k l
    have h1 := congrFun (congrFun (h i) k) l
    rw [mul_reflT_apply, reflT_mul_apply] at h1
    linarith
  have hoff : ∀ i l, l ≠ i → X i l = 0 := by
    intro i l hli
    have h1 := key i i l
    rw [ite_eq_right hli, Tag.cartan_self] at h1
    linarith
  have hrel : ∀ i k, X k k * Tag.F4.cartan i k = Tag.F4.cartan i k * X i i := by
    intro i k
    have h1 := key i k i
    rw [ite_eq_left rfl, Finset.sum_eq_single k (fun m _ hmk => by rw [hoff k m hmk, zero_mul])
      (fun hk => absurd (Finset.mem_univ k) hk)] at h1
    exact h1
  have h01 := hrel ⟨0, by decide⟩ ⟨1, by decide⟩
  have h12 := hrel ⟨1, by decide⟩ ⟨2, by decide⟩
  have h23 := hrel ⟨2, by decide⟩ ⟨3, by decide⟩
  have hc01 : Tag.F4.cartan ⟨0, by decide⟩ ⟨1, by decide⟩ = -1 := by decide
  have hc12 : Tag.F4.cartan ⟨1, by decide⟩ ⟨2, by decide⟩ = -1 := by decide
  have hc23 : Tag.F4.cartan ⟨2, by decide⟩ ⟨3, by decide⟩ = -1 := by decide
  rw [hc01] at h01
  rw [hc12] at h12
  rw [hc23] at h23
  have hcases : ∀ k : Fin Tag.F4.rank, k = ⟨0, by decide⟩ ∨ k = ⟨1, by decide⟩ ∨
      k = ⟨2, by decide⟩ ∨ k = ⟨3, by decide⟩ := by decide
  ext k l
  rw [Matrix.scalar_apply, Matrix.diagonal_apply]
  by_cases hkl : k = l
  · subst hkl
    rw [ite_eq_left rfl]
    rcases hcases k with rfl | rfl | rfl | rfl <;> linarith
  · rw [ite_eq_right hkl]
    exact hoff k l (Ne.symm hkl)

@[expose] def charRep : WeylGroup .F4 →* GL (Fin Tag.F4.rank) ℤ where
  toFun w := ⟨invTranspose (weylToAut .F4 w), invTranspose (weylToAut .F4 w⁻¹),
    invTranspose_weylToAut_mul_inv w, by
      rw [← invTranspose_weylToAut_mul, inv_mul_cancel, map_one, invTranspose_one]⟩
  map_one' := Units.ext (by
    change invTranspose (weylToAut .F4 1) = 1
    rw [map_one, invTranspose_one])
  map_mul' w v := Units.ext (invTranspose_weylToAut_mul w v)

theorem coe_charRep (w : WeylGroup .F4) :
    (charRep w : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ) = invTranspose (weylToAut .F4 w) :=
  rfl

theorem injOn_map_charMatrices {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    Set.InjOn (fun u : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ =>
      u.map (Int.castRingHom (ZMod p))) charMatrices := by
  intro u hu u' hu' heq
  obtain ⟨w, rfl⟩ := mem_charMatrices.1 hu
  obtain ⟨v, rfl⟩ := mem_charMatrices.1 hu'
  simp only at heq
  set ι : ℤ →+* CFSG.Monster.ratLocal p := Int.castRingHom _ with hι
  have hιinj : Function.Injective ι := fun a b hab => by
    have h1 := congrArg (fun x : CFSG.Monster.ratLocal p => (x : ℚ)) hab
    simpa [hι] using h1
  set g := Matrix.GeneralLinearGroup.map ι (charRep (v⁻¹ * w)) with hg
  have hfin : IsOfFinOrder g := (Matrix.GeneralLinearGroup.map ι).isOfFinOrder
    (charRep.isOfFinOrder (isOfFinOrder_of_finite _))
  have hcomp : ∀ a : ℤ, CFSG.Monster.ratLocalRed p (ι a) = Int.castRingHom (ZMod p) a :=
    fun a => by rw [← RingHom.comp_apply, RingHom.ext_int ((CFSG.Monster.ratLocalRed p).comp ι)
      (Int.castRingHom (ZMod p))]
  have hmat : (invTranspose (weylToAut .F4 v⁻¹) * invTranspose (weylToAut .F4 w)).map
      (Int.castRingHom (ZMod p)) = 1 := by
    rw [Matrix.map_mul, heq, ← Matrix.map_mul, ← invTranspose_weylToAut_mul, inv_mul_cancel,
      map_one, invTranspose_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have hred : Matrix.GeneralLinearGroup.map (CFSG.Monster.ratLocalRed p) g = 1 := by
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [Matrix.GeneralLinearGroup.map_apply, hg, Matrix.GeneralLinearGroup.map_apply, hcomp,
      coe_charRep, invTranspose_weylToAut_mul]
    have h1 := congrFun (congrFun hmat i) j
    rw [Matrix.map_apply] at h1
    rw [h1]
    rfl
  have hg1 := (CFSG.Monster.odd_prime_congruence_torsion_free p hp2 (Fin Tag.F4.rank)).1 g hred
    hfin
  have hone : invTranspose (weylToAut .F4 v⁻¹) * invTranspose (weylToAut .F4 w) = 1 := by
    ext i j
    have h1 := congrArg (fun x : GL (Fin Tag.F4.rank) (CFSG.Monster.ratLocal p) =>
      (x : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) (CFSG.Monster.ratLocal p)) i j) hg1
    simp only [hg, Matrix.GeneralLinearGroup.map_apply, coe_charRep,
      invTranspose_weylToAut_mul, Units.val_one] at h1
    apply hιinj
    rw [h1]
    by_cases hij : i = j
    · subst hij
      simp [hι]
    · simp [hι, hij]
  calc invTranspose (weylToAut .F4 w)
      = invTranspose (weylToAut .F4 v) *
          (invTranspose (weylToAut .F4 v⁻¹) * invTranspose (weylToAut .F4 w)) := by
        rw [← mul_assoc, ← invTranspose_weylToAut_mul, mul_inv_cancel, map_one,
          invTranspose_one, one_mul]
    _ = invTranspose (weylToAut .F4 v) := by rw [hone, mul_one]

theorem map_mul_comm_of_eq_scalar {p : ℕ} {A M : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ}
    {c : ZMod p} (hA : A.map (Int.castRingHom (ZMod p)) = Matrix.scalar (Fin Tag.F4.rank) c) :
    (A * M).map (Int.castRingHom (ZMod p)) = (M * A).map (Int.castRingHom (ZMod p)) := by
  rw [Matrix.map_mul, Matrix.map_mul, hA]
  exact (Matrix.scalar_commute c (fun _ => Commute.all _ _) _).eq

theorem eq_one_or_neg_one_of_map_eq_scalar {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {u : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ} (hu : u ∈ charMatrices) {c : ZMod p}
    (hc : u.map (Int.castRingHom (ZMod p)) = Matrix.scalar (Fin Tag.F4.rank) c) :
    u = 1 ∨ u = -1 := by
  obtain ⟨w, rfl⟩ := mem_charMatrices.1 hu
  have hcomm : ∀ i, invTranspose (weylToAut .F4 w) * reflT i =
      reflT i * invTranspose (weylToAut .F4 w) := by
    intro i
    have h1 : invTranspose (weylToAut .F4 w) * reflT i ∈ charMatrices := mem_charMatrices.2
      ⟨w * simple .F4 i, by rw [invTranspose_weylToAut_mul, invTranspose_weylToAut_simple]⟩
    have h2 : reflT i * invTranspose (weylToAut .F4 w) ∈ charMatrices := mem_charMatrices.2
      ⟨simple .F4 i * w, by rw [invTranspose_weylToAut_mul, invTranspose_weylToAut_simple]⟩
    exact injOn_map_charMatrices hp2 h1 h2 (map_mul_comm_of_eq_scalar hc)
  have hX := eq_scalar_of_commute_reflT hcomm
  set d := invTranspose (weylToAut .F4 w) ⟨0, by decide⟩ ⟨0, by decide⟩ with hd
  have hinv := invTranspose_weylToAut_mul_inv w
  rw [hX] at hinv
  have h00 := congrFun (congrFun hinv ⟨0, by decide⟩) ⟨0, by decide⟩
  rw [Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.one_apply_eq] at h00
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' h00 with ⟨hd1, -⟩ | ⟨hd1, -⟩
  · left
    rw [hX, hd1, map_one]
  · right
    rw [hX, hd1, map_neg, map_one]

theorem map_mul_f4J_ne_scalar {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {u : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ} (hu : u ∈ charMatrices) (c : ZMod p) :
    (u * f4J).map (Int.castRingHom (ZMod p)) ≠ Matrix.scalar (Fin Tag.F4.rank) c := by
  intro hc
  obtain ⟨w, rfl⟩ := mem_charMatrices.1 hu
  set f := Int.castRingHom (ZMod p) with hf
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).1 h'
    exact hp2 this
  have hJJ : f4J.map f * f4J.map f = (2 : ZMod p) • 1 := by
    rw [← Matrix.map_mul, f4J_mul_f4J]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp [hf]
  have hcancel : ∀ A B : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ,
      (A * f4J).map f = (B * f4J).map f → A.map f = B.map f := by
    intro A B h
    have h1 := congrArg (· * f4J.map f) h
    simp only [Matrix.map_mul, mul_assoc, hJJ, Matrix.mul_smul, mul_one] at h1
    exact smul_right_injective _ h2 h1
  have hcomm : ∀ i, invTranspose (weylToAut .F4 w) * f4J * reflT i =
      reflT i * (invTranspose (weylToAut .F4 w) * f4J) := by
    intro i
    have e1 : invTranspose (weylToAut .F4 w) * f4J * reflT i =
        invTranspose (weylToAut .F4 (w * simple .F4 (Fin.rev i))) * f4J := by
      rw [mul_assoc, f4J_mul_reflT, ← mul_assoc, invTranspose_weylToAut_mul,
        invTranspose_weylToAut_simple]
    have e2 : reflT i * (invTranspose (weylToAut .F4 w) * f4J) =
        invTranspose (weylToAut .F4 (simple .F4 i * w)) * f4J := by
      rw [← mul_assoc, invTranspose_weylToAut_mul, invTranspose_weylToAut_simple]
    have hred : (invTranspose (weylToAut .F4 (w * simple .F4 (Fin.rev i))) * f4J).map f =
        (invTranspose (weylToAut .F4 (simple .F4 i * w)) * f4J).map f := by
      rw [← e1, ← e2]
      exact map_mul_comm_of_eq_scalar hc
    rw [e1, e2, injOn_map_charMatrices hp2 (mem_charMatrices.2 ⟨_, rfl⟩)
      (mem_charMatrices.2 ⟨_, rfl⟩) (hcancel _ _ hred)]
  have hX := eq_scalar_of_commute_reflT hcomm
  set d := (invTranspose (weylToAut .F4 w) * f4J) ⟨0, by decide⟩ ⟨0, by decide⟩ with hd
  obtain ⟨w', hw'⟩ := exists_f4J_mul_eq w
  have hsq : invTranspose (weylToAut .F4 w) * f4J * (invTranspose (weylToAut .F4 w) * f4J) =
      (2 : ℤ) • invTranspose (weylToAut .F4 (w * w')) := by
    rw [← mul_assoc, mul_assoc _ f4J, hw', ← mul_assoc, mul_assoc _ f4J, f4J_mul_f4J,
      Matrix.mul_smul, mul_one, invTranspose_weylToAut_mul]
  rw [hX, ← map_mul] at hsq
  set y := invTranspose (weylToAut .F4 (w * w')) with hy
  have hentry : ∀ m, (if (⟨0, by decide⟩ : Fin Tag.F4.rank) = m then d * d else 0) =
      2 * y ⟨0, by decide⟩ m := by
    intro m
    have h1 := congrFun (congrFun hsq ⟨0, by decide⟩) m
    rw [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.smul_apply, smul_eq_mul] at h1
    exact h1
  have hy0 : ∀ m, m ≠ (⟨0, by decide⟩ : Fin Tag.F4.rank) → y ⟨0, by decide⟩ m = 0 := by
    intro m hm
    have h1 := hentry m
    rw [ite_eq_right (Ne.symm hm)] at h1
    linarith
  have hdd : d * d = 2 * y ⟨0, by decide⟩ ⟨0, by decide⟩ := by
    have h1 := hentry ⟨0, by decide⟩
    rwa [ite_eq_left rfl] at h1
  have hinv := invTranspose_weylToAut_mul_inv (w * w')
  have h00 := congrFun (congrFun hinv ⟨0, by decide⟩) ⟨0, by decide⟩
  rw [Matrix.mul_apply, Finset.sum_eq_single (⟨0, by decide⟩ : Fin Tag.F4.rank)
    (fun m _ hm => by rw [← hy, hy0 m hm, zero_mul])
    (fun h => absurd (Finset.mem_univ _) h), Matrix.one_apply_eq, ← hy] at h00
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' h00 with ⟨hy1, -⟩ | ⟨hy1, -⟩
  · rw [hy1] at hdd
    have hd1 : d ≤ 1 := by nlinarith
    have hd2 : -1 ≤ d := by nlinarith
    interval_cases d <;> omega
  · rw [hy1] at hdd
    nlinarith [mul_self_nonneg d]

@[expose] def adjB : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ :=
  !![4, 6, 8, 4; 6, 12, 16, 8; 8, 16, 24, 12; 4, 8, 12, 8]

theorem symmetrizedCartan_mul_adjB :
    Tag.F4.symmetrizedCartan * adjB =
      (4 : ℤ) • (1 : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ) := by
  decide

theorem adjB_mul_symmetrizedCartan :
    adjB * Tag.F4.symmetrizedCartan =
      (4 : ℤ) • (1 : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ) := by
  decide

theorem symmetrizedCartan_mul_transpose_f4J :
    Tag.F4.symmetrizedCartan * f4J.transpose = f4J * Tag.F4.symmetrizedCartan := by
  decide

theorem transpose_f4J_mul_inv_mul_f4J :
    (f4J.map (Int.castRingHom ℚ)).transpose *
        (Tag.F4.symmetrizedCartan.map (Int.castRingHom ℚ))⁻¹ * f4J.map (Int.castRingHom ℚ) =
      (2 : ℚ) • (Tag.F4.symmetrizedCartan.map (Int.castRingHom ℚ))⁻¹ := by
  set B := Tag.F4.symmetrizedCartan.map (Int.castRingHom ℚ) with hB
  set Jq := f4J.map (Int.castRingHom ℚ) with hJq
  set C := (1 / 4 : ℚ) • adjB.map (Int.castRingHom ℚ) with hC
  have hBC : B * C = 1 := by
    rw [hC, Matrix.mul_smul, hB, ← Matrix.map_mul, symmetrizedCartan_mul_adjB]
    ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> norm_num
  have hCB : C * B = 1 := by
    rw [hC, Matrix.smul_mul, hB, ← Matrix.map_mul, adjB_mul_symmetrizedCartan]
    ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> norm_num
  have hinv : B⁻¹ = C := Matrix.inv_eq_right_inv hBC
  have hBJ : B * Jq.transpose = Jq * B := by
    rw [hB, hJq, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul,
      symmetrizedCartan_mul_transpose_f4J]
  have hJJ : Jq * Jq = (2 : ℚ) • 1 := by
    rw [hJq, ← Matrix.map_mul, f4J_mul_f4J]
    ext i j
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> norm_num
  rw [hinv]
  calc Jq.transpose * C * Jq = C * B * Jq.transpose * C * Jq := by rw [hCB, one_mul]
    _ = C * (B * Jq.transpose) * C * Jq := by rw [mul_assoc C]
    _ = C * Jq * (B * C) * Jq := by rw [hBJ]; noncomm_ring
    _ = C * (Jq * Jq) := by rw [hBC, mul_one, mul_assoc]
    _ = (2 : ℚ) • C := by rw [hJJ, Matrix.mul_smul, mul_one]

theorem sum_length_eq [Fintype (WeylGroup .F4)] (q : ℕ) :
    ∑ w : WeylGroup .F4, q ^ (coxeterSystem .F4).length w =
      (([2, 6, 8, 12] : List ℕ).map fun d => ∑ i ∈ Finset.range d, q ^ i).prod := by
  rw [sum_length_F4]
  simp only [geomSum, one_mul, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one]
  rw [geom_eq_mul_geom_pow q (show 3 * 2 = 6 from rfl),
    geom_eq_mul_geom_pow q (show 4 * 3 = 12 from rfl)]
  ring

open Polynomial in
theorem weyl_length_polynomial [Fintype (WeylGroup .F4)] :
    ∑ w : WeylGroup .F4, (X : ℤ[X]) ^ (coxeterSystem .F4).length w =
        (([2, 6, 8, 12] : List ℕ).map fun d => ∑ i ∈ Finset.range d, (X : ℤ[X]) ^ i).prod ∧
      Nat.card (WeylGroup .F4) = 1152 := by
  refine ⟨eq_of_forall_natCast_eval_eq fun n => ?_, ?_⟩
  · have h := congrArg (Nat.cast : ℕ → ℤ) (sum_length_eq n)
    simp only [Nat.cast_sum, Nat.cast_pow, Nat.cast_mul, Nat.cast_one, List.map_cons,
      List.map_nil, List.prod_cons, List.prod_nil] at h
    simpa only [eval_finsetSum, eval_pow, eval_X, eval_mul, eval_one, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil] using h
  · have h := sum_length_eq 1
    simp only [one_pow, Finset.sum_const, Finset.card_univ, Finset.card_range, smul_eq_mul,
      mul_one, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil] at h
    rw [Nat.card_eq_fintype_card, h]

end F4Weyl

open F4Weyl

open Polynomial in
theorem F4_weyl_length_polynomial_and_exceptional_scalar_obstruction
    [Fintype (WeylGroup .F4)] :
    Nat.card (WeylGroup .F4) = 1152 ∧ Nat.card (latticeWeylGroup .F4) = 1152 ∧
    (-1 : (Module.End ℤ (Fin Tag.F4.rank → ℤ))ˣ) ∈ latticeWeylGroup .F4 ∧
    ∑ w : WeylGroup .F4, (X : ℤ[X]) ^ (coxeterSystem .F4).length w =
      (([2, 6, 8, 12] : List ℕ).map fun d => ∑ i ∈ Finset.range d, (X : ℤ[X]) ^ i).prod ∧
    f4J * f4J = (2 : ℤ) • (1 : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ) ∧
    (fun u => f4J * u) '' charMatrices = (fun u => u * f4J) '' charMatrices ∧
    (f4J.map (Int.castRingHom ℚ)).transpose *
        (Tag.F4.symmetrizedCartan.map (Int.castRingHom ℚ))⁻¹ * f4J.map (Int.castRingHom ℚ) =
      (2 : ℚ) • (Tag.F4.symmetrizedCartan.map (Int.castRingHom ℚ))⁻¹ ∧
    (1 : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ) ∈ charMatrices ∧
    (-1 : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ) ∈ charMatrices ∧
    ∀ p : ℕ, p.Prime → p ≠ 2 →
      Set.InjOn (fun u : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ =>
        u.map (Int.castRingHom (ZMod p))) charMatrices ∧
      (∀ u ∈ charMatrices, (∃ c : ZMod p, u.map (Int.castRingHom (ZMod p)) =
          Matrix.scalar (Fin Tag.F4.rank) c) ↔ u = 1 ∨ u = -1) ∧
      ∀ u ∈ charMatrices, ∀ c : ZMod p,
        (u * f4J).map (Int.castRingHom (ZMod p)) ≠ Matrix.scalar (Fin Tag.F4.rank) c := by
  obtain ⟨hpoly, hcard⟩ := weyl_length_polynomial
  refine ⟨hcard, by rw [← Nat.card_congr (weylEquivLattice .F4).toEquiv, hcard],
    neg_one_mem_latticeWeylGroup, hpoly, f4J_mul_f4J, image_f4J_mul_charMatrices,
    transpose_f4J_mul_inv_mul_f4J, one_mem_charMatrices, neg_one_mem_charMatrices,
    fun p hp hp2 => ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨injOn_map_charMatrices hp2, fun u hu => ⟨fun ⟨c, hc⟩ =>
    eq_one_or_neg_one_of_map_eq_scalar hp2 hu hc, ?_⟩, fun u hu c =>
    map_mul_f4J_ne_scalar hp2 hu c⟩
  rintro (rfl | rfl)
  · exact ⟨1, by rw [Matrix.map_one _ (map_zero _) (map_one _), map_one]⟩
  · refine ⟨-1, ?_⟩
    ext i j
    simp only [Matrix.map_apply, Matrix.neg_apply, Matrix.one_apply, Matrix.scalar_apply,
      Matrix.diagonal_apply]
    split_ifs
    · rw [map_neg, map_one]
    · rw [neg_zero, map_zero]

end CFSG.RankThree.Chevalley
