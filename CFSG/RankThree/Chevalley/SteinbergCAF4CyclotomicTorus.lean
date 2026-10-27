module

public import CFSG.RankThree.Chevalley.SteinbergCAF4SplitPrimeTorus
public import CFSG.RankThree.Lattice.SteinbergBIF4EightTwelve

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.E6 F4Weyl

@[expose] def f4Col (B : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ) (k : Fin Tag.F4.rank) :
    Fin Tag.F4.rank → ℤ :=
  fun i => B i k

structure F4CyclicBasis (w : WeylGroup .F4) where
  B : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ
  N : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ
  ε : ℤ
  smul_zero : w • f4Col B (f4Index 0) = f4Col B (f4Index 1)
  smul_one : w • f4Col B (f4Index 1) = f4Col B (f4Index 2)
  smul_two : w • f4Col B (f4Index 2) = f4Col B (f4Index 3)
  smul_three : w • f4Col B (f4Index 3) = ε • f4Col B (f4Index 2) - f4Col B (f4Index 0)
  N_mul : N * B = 1
  mul_N : B * N = 1

namespace F4CyclicBasis

variable {w : WeylGroup .F4} (D : F4CyclicBasis w) {L : Type} [Field L]

theorem single_eq_sum (j : Fin Tag.F4.rank) :
    (Pi.single j 1 : Fin Tag.F4.rank → ℤ) = ∑ i, D.N i j • f4Col D.B i := by
  funext t
  have h := congrFun (congrFun D.mul_N t) j
  rw [Matrix.mul_apply, Matrix.one_apply] at h
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul, f4Col]
  rw [Pi.single_apply, ← h]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem eq_of_rootChar_basis {c c' : Fin Tag.F4.rank → Lˣ}
    (h : ∀ k, rootChar c (f4Col D.B k) = rootChar c' (f4Col D.B k)) : c = c' := by
  funext j
  have e : ∀ a : Fin Tag.F4.rank → Lˣ, a j = ∏ i, rootChar a (f4Col D.B i) ^ D.N i j := by
    intro a
    rw [← rootChar_pi_single a j, D.single_eq_sum j, rootChar_sum]
    exact Finset.prod_congr rfl fun i _ => rootChar_zsmul a _ _
  rw [e c, e c']
  exact Finset.prod_congr rfl fun i _ => by rw [h i]

@[expose] def cycTuple (q : ℕ) (ζ : Lˣ) : Fin Tag.F4.rank → Lˣ :=
  fun j => ζ ^ (∑ i : Fin Tag.F4.rank, (q : ℤ) ^ (i : ℕ) * D.N i j)

@[expose] def cycTupleHom (q : ℕ) : Lˣ →* (Fin Tag.F4.rank → Lˣ) where
  toFun := D.cycTuple q
  map_one' := by
    funext j
    simp [cycTuple]
  map_mul' ζ ζ' := by
    funext j
    simp only [cycTuple, Pi.mul_apply, mul_zpow]

theorem cycTupleHom_apply (q : ℕ) (ζ : Lˣ) : D.cycTupleHom q ζ = D.cycTuple q ζ :=
  rfl

theorem rootChar_cycTuple_col (q : ℕ) (ζ : Lˣ) (k : Fin Tag.F4.rank) :
    rootChar (D.cycTuple q ζ) (f4Col D.B k) = ζ ^ ((q : ℤ) ^ (k : ℕ)) := by
  have hNB : ∀ i, ∑ j, D.N i j * D.B j k = if i = k then 1 else 0 := fun i => by
    have h := congrFun (congrFun D.N_mul i) k
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    exact h
  rw [rootChar]
  simp only [cycTuple, f4Col, ← zpow_mul]
  rw [prod_zpow_eq_zpow_sum]
  congr 1
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc, ← Finset.mul_sum, hNB, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

theorem cycTupleHom_injective (q : ℕ) :
    Function.Injective (D.cycTupleHom (L := L) q) := fun ζ ζ' h => by
  have h0 := congrArg (fun c => rootChar c (f4Col D.B (f4Index 0))) h
  simp only [cycTupleHom_apply, rootChar_cycTuple_col] at h0
  rwa [show ((f4Index 0 : Fin Tag.F4.rank) : ℕ) = 0 from rfl, pow_zero, zpow_one, zpow_one] at h0

theorem forall_rootChar_smul_eq_pow_iff (q : ℕ) (c : Fin Tag.F4.rank → Lˣ) :
    (∀ v, rootChar c (w • v) = rootChar c v ^ q) ↔
      ∃ ζ : Lˣ, ζ ^ ((q : ℤ) ^ 4 - D.ε * (q : ℤ) ^ 2 + 1) = 1 ∧ c = D.cycTuple q ζ := by
  constructor
  · intro h
    set ζ := rootChar c (f4Col D.B (f4Index 0)) with hζ
    have h1 : rootChar c (f4Col D.B (f4Index 1)) = ζ ^ ((q : ℤ) ^ (1 : ℕ)) := by
      rw [← D.smul_zero, h, pow_one, zpow_natCast]
    have h2 : rootChar c (f4Col D.B (f4Index 2)) = ζ ^ ((q : ℤ) ^ (2 : ℕ)) := by
      rw [← D.smul_one, h, h1, ← zpow_natCast, ← zpow_mul]
      congr 1
    have h3 : rootChar c (f4Col D.B (f4Index 3)) = ζ ^ ((q : ℤ) ^ (3 : ℕ)) := by
      rw [← D.smul_two, h, h2, ← zpow_natCast, ← zpow_mul]
      congr 1
    have h4 := h (f4Col D.B (f4Index 3))
    rw [D.smul_three, sub_eq_add_neg, rootChar_add, rootChar_neg_eq_inv, rootChar_zsmul, h2, h3,
      ← hζ, ← zpow_natCast, ← zpow_mul, ← zpow_mul] at h4
    refine ⟨ζ, ?_, D.eq_of_rootChar_basis fun k => ?_⟩
    · have e : (q : ℤ) ^ 4 - D.ε * (q : ℤ) ^ 2 + 1 =
          (q : ℤ) ^ 3 * q - (q : ℤ) ^ 2 * D.ε + 1 := by
        ring
      rw [e, zpow_add, zpow_sub, ← h4, zpow_one]
      group
    · rw [rootChar_cycTuple_col]
      fin_cases k
      · show rootChar c (f4Col D.B (f4Index 0)) = ζ ^ ((q : ℤ) ^ (0 : ℕ))
        rw [pow_zero, zpow_one]
      · exact h1
      · exact h2
      · exact h3
  · rintro ⟨ζ, hζ, rfl⟩ v
    have hsmul : ∀ (c : Fin Tag.F4.rank → Lˣ) (x : Fin Tag.F4.rank → ℤ),
        rootChar c (w • x) = rootChar (fun j => rootChar c (w • Pi.single j 1)) x := by
      intro c x
      rw [smul_eq_sum_smul_single w x, rootChar_sum, rootChar]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [rootChar_zsmul]
    have hc : (fun j => rootChar (D.cycTuple q ζ) (w • Pi.single j 1)) =
        D.cycTuple q ζ ^ q := by
      refine D.eq_of_rootChar_basis fun k => ?_
      rw [← hsmul, rootChar_pow_tuple, rootChar_cycTuple_col,
        ← zpow_natCast, ← zpow_mul]
      fin_cases k
      · show rootChar (D.cycTuple q ζ) (w • f4Col D.B (f4Index 0)) = ζ ^ ((q : ℤ) ^ (0 : ℕ) * q)
        rw [D.smul_zero, rootChar_cycTuple_col]
        show ζ ^ ((q : ℤ) ^ (1 : ℕ)) = _
        congr 1
      · show rootChar (D.cycTuple q ζ) (w • f4Col D.B (f4Index 1)) = ζ ^ ((q : ℤ) ^ (1 : ℕ) * q)
        rw [D.smul_one, rootChar_cycTuple_col]
        show ζ ^ ((q : ℤ) ^ (2 : ℕ)) = _
        congr 1
      · show rootChar (D.cycTuple q ζ) (w • f4Col D.B (f4Index 2)) = ζ ^ ((q : ℤ) ^ (2 : ℕ) * q)
        rw [D.smul_two, rootChar_cycTuple_col]
        show ζ ^ ((q : ℤ) ^ (3 : ℕ)) = _
        congr 1
      · show rootChar (D.cycTuple q ζ) (w • f4Col D.B (f4Index 3)) = ζ ^ ((q : ℤ) ^ (3 : ℕ) * q)
        rw [D.smul_three, sub_eq_add_neg, rootChar_add, rootChar_neg_eq_inv, rootChar_zsmul,
          rootChar_cycTuple_col, rootChar_cycTuple_col]
        show (ζ ^ ((q : ℤ) ^ (2 : ℕ))) ^ D.ε * (ζ ^ ((q : ℤ) ^ (0 : ℕ)))⁻¹ = _
        rw [show (q : ℤ) ^ (3 : ℕ) * q = ((q : ℤ) ^ 2 * D.ε + -1) +
            ((q : ℤ) ^ 4 - D.ε * (q : ℤ) ^ 2 + 1) by ring, zpow_add, hζ, mul_one, zpow_add,
          ← zpow_mul, pow_zero, zpow_one, zpow_neg_one]
    rw [hsmul, hc, rootChar_pow_tuple]

@[expose] def torus (L : Type) [Field L] (q d : ℕ) : Subgroup (ModGL .F4 L) :=
  (rootsOfUnity d L).map ((rootDiagUnitHom .F4 L).comp (D.cycTupleHom q))

theorem rootDiagUnit_mem_torus_iff (q d : ℕ) (c : Fin Tag.F4.rank → Lˣ) :
    rootDiagUnit .F4 c ∈ D.torus L q d ↔ ∃ ζ : Lˣ, ζ ^ d = 1 ∧ c = D.cycTuple q ζ := by
  constructor
  · rintro ⟨ζ, hζ, h⟩
    exact ⟨ζ, (mem_rootsOfUnity d ζ).1 hζ, (rootDiagUnit_injective h).symm⟩
  · rintro ⟨ζ, hζ, rfl⟩
    exact ⟨ζ, (mem_rootsOfUnity d ζ).2 hζ, rfl⟩

theorem torus_le_torusGroup (q d : ℕ) : D.torus L q d ≤ torusGroup .F4 L := by
  rintro _ ⟨ζ, -, rfl⟩
  exact F4_rootDiagUnit_mem_torusGroup _

theorem natCard_torus [IsAlgClosed L] (q d : ℕ) [NeZero (d : L)] :
    Nat.card (D.torus L q d) = d := by
  have : NeZero d := ⟨fun h => NeZero.ne (d : L) (by rw [h, Nat.cast_zero])⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.prim (M := L) (n := d)
  rw [torus, Subgroup.card_map_of_injective
    (rootDiagUnit_injective.comp (D.cycTupleHom_injective q)), hζ.card_rootsOfUnity]

theorem isCyclic_torus (q d : ℕ) [NeZero d] : IsCyclic (D.torus L q d) :=
  isCyclic_of_surjective _
    (((rootDiagUnitHom .F4 L).comp (D.cycTupleHom q)).subgroupMap_surjective (rootsOfUnity d L))

theorem conj_frob_eq_iff_mem_torus (F : L →+* L) {q : ℕ} (hF : ∀ c, F c = c ^ q) {d : ℕ}
    (hd : (d : ℤ) = (q : ℤ) ^ 4 - D.ε * (q : ℤ) ^ 2 + 1) {u : ModGL .F4 L}
    (hu : u ∈ torusGroup .F4 L) :
    canonicalRep (coxeterSystem .F4) L w * Units.map (entrywiseHom F) u *
        (canonicalRep (coxeterSystem .F4) L w)⁻¹ = u ↔ u ∈ D.torus L q d := by
  obtain ⟨c, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hu
  rw [conj_frob_rootDiagUnit_eq_iff F hF w c, D.forall_rootChar_smul_eq_pow_iff,
    D.rootDiagUnit_mem_torus_iff, ← hd]
  simp only [zpow_natCast]

end F4CyclicBasis

theorem rootChar_ne_one_of_forall_smul_eq_pow {L : Type} [Field L] {w : WeylGroup .F4}
    {q p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (horb : ∀ α, IsRoot .F4 α → ∃ k : ℕ,
      |(CFSG.RankThree.Lattice.orbitMat (weylMatrix w) α Tag.F4.rank).det| = 2 ^ k)
    {c : Fin Tag.F4.rank → Lˣ} (hfix : ∀ v, rootChar c (w • v) = rootChar c v ^ q)
    (hcp : c ^ p = 1) (hc1 : c ≠ 1) {α : Fin Tag.F4.rank → ℤ} (hα : IsRoot .F4 α) :
    rootChar c α ≠ 1 := by
  intro h1
  have hj : ∀ j : ℕ, rootChar c ((w ^ j) • α) = 1 := by
    intro j
    induction j with
    | zero => rw [pow_zero, one_smul, h1]
    | succ j ih => rw [pow_succ', mul_smul, hfix, ih, one_pow]
  obtain ⟨k, hk⟩ := horb α hα
  set M := CFSG.RankThree.Lattice.orbitMat (weylMatrix w) α Tag.F4.rank with hM
  have hMv : ∀ y : Fin Tag.F4.rank → ℤ, M.mulVec y = ∑ j, y j • ((w ^ (j : ℕ)) • α) := by
    intro y
    funext i
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hM, CFSG.RankThree.Lattice.orbitMat, Matrix.of_apply, ← weylMatrix_pow,
      weylMatrix_mulVec, mul_comm]
  have hall : ∀ v : Fin Tag.F4.rank → ℤ, rootChar c v = 1 := by
    intro v
    have hdet : M.det • v = M.mulVec (M.adjugate.mulVec v) := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]
    have h2 : rootChar c v ^ M.det = 1 := by
      rw [← rootChar_zsmul, hdet, hMv, rootChar_sum]
      exact Finset.prod_eq_one fun j _ => by rw [rootChar_zsmul, hj, one_zpow]
    have h3 : rootChar c v ^ (2 ^ k) = 1 := by
      have e : ((2 ^ k : ℕ) : ℤ) = (2 : ℤ) ^ k := by push_cast; ring
      rcases (abs_eq (by positivity)).1 hk with h | h
      · rwa [h, ← e, zpow_natCast] at h2
      · rwa [h, ← e, zpow_neg, zpow_natCast, inv_eq_one] at h2
    have h4 : rootChar c v ^ p = 1 := rootChar_pow_of_pow_eq_one hcp v
    have hcop : Nat.gcd (2 ^ k) p = 1 :=
      Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
    have h5 := pow_gcd_eq_one.2 ⟨h3, h4⟩
    rwa [hcop, pow_one] at h5
  apply hc1
  funext j
  rw [← rootChar_pi_single c j, hall, Pi.one_apply]

@[expose] def f4W8Elt : WeylGroup .F4 := f4WordProd [0, 1, 2, 1, 2, 3]

theorem weylMatrix_f4W8Elt : weylMatrix f4W8Elt = CFSG.RankThree.Lattice.f4W8 := by
  rw [CFSG.RankThree.Lattice.f4W8_eq, f4W8Elt, weylMatrix_f4WordProd]
  decide

theorem weylMatrix_f4Coxeter_eq_f4W12 : weylMatrix f4Coxeter = CFSG.RankThree.Lattice.f4W12 := by
  rw [weylMatrix_f4Coxeter, CFSG.RankThree.Lattice.f4W12_eq]
  decide

@[expose] def f4W8Basis : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ :=
  !![-1, 0, 0, 0; -1, -1, 0, 0; -1, -1, -1, 1; -1, 0, -1, 0]

@[expose] def f4W8Coord : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ :=
  !![-1, 0, 0, 0; 1, -1, 0, 0; 1, 0, 0, -1; 1, -1, 1, -1]

@[expose] def f4W12Basis : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ :=
  !![-1, 0, -1, 0; -1, -1, -1, -1; -1, -1, -2, -1; -1, 0, -1, -1]

@[expose] def f4W12Coord : Matrix (Fin Tag.F4.rank) (Fin Tag.F4.rank) ℤ :=
  !![-1, -1, 1, 0; 0, -1, 0, 1; 0, 1, -1, 0; 1, 0, 0, -1]

@[expose] def f4W8CyclicBasis : F4CyclicBasis f4W8Elt where
  B := f4W8Basis
  N := f4W8Coord
  ε := 0
  smul_zero := by rw [f4W8Elt, f4WordProd_smul]; decide
  smul_one := by rw [f4W8Elt, f4WordProd_smul]; decide
  smul_two := by rw [f4W8Elt, f4WordProd_smul]; decide
  smul_three := by rw [f4W8Elt, f4WordProd_smul]; decide
  N_mul := by decide
  mul_N := by decide

@[expose] def f4W12CyclicBasis : F4CyclicBasis f4Coxeter where
  B := f4W12Basis
  N := f4W12Coord
  ε := 1
  smul_zero := by rw [f4Coxeter, f4WordProd_smul]; decide
  smul_one := by rw [f4Coxeter, f4WordProd_smul]; decide
  smul_two := by rw [f4Coxeter, f4WordProd_smul]; decide
  smul_three := by rw [f4Coxeter, f4WordProd_smul]; decide
  N_mul := by decide
  mul_N := by decide

theorem orbit_det_f4W8Elt {α : Fin Tag.F4.rank → ℤ} (hα : IsRoot .F4 α) :
    ∃ k : ℕ, |(CFSG.RankThree.Lattice.orbitMat (weylMatrix f4W8Elt) α Tag.F4.rank).det| =
      2 ^ k := by
  rw [weylMatrix_f4W8Elt]
  exact (CFSG.RankThree.Lattice.F4_eight_twelve_Weyl_cyclic_lattice_and_root_orbit_indices
    ).2.2.2.2.2.2.2.1 _ (by simp) α hα |>.2

theorem orbit_det_f4Coxeter {α : Fin Tag.F4.rank → ℤ} (hα : IsRoot .F4 α) :
    ∃ k : ℕ, |(CFSG.RankThree.Lattice.orbitMat (weylMatrix f4Coxeter) α Tag.F4.rank).det| =
      2 ^ k := by
  rw [weylMatrix_f4Coxeter_eq_f4W12]
  exact (CFSG.RankThree.Lattice.F4_eight_twelve_Weyl_cyclic_lattice_and_root_orbit_indices
    ).2.2.2.2.2.2.2.1 _ (by simp) α hα |>.2

end CFSG.RankThree.Chevalley
