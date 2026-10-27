module

public import CFSG.RankThree.E6.CoxeterSquareEisensteinLines
public import CFSG.RankThree.Chevalley.G2CyclotomicTori
public import CFSG.LocalAnalysis.ComponentInitial.LinearMonomial

public noncomputable section

namespace CFSG.RankThree.Classical2

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix

theorem phi3_prime_facts {p q : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ q ^ 2 + q + 1) :
    orderOf (q : ZMod p) = 3 ∧ p % 3 = 1 ∧ 7 ≤ p := by
  have : Fact p.Prime := ⟨hp⟩
  have hq : ((q : ZMod p)) ^ 2 + q + 1 = 0 := by
    have := (ZMod.natCast_eq_zero_iff _ p).mpr hpq
    push_cast at this
    exact this
  have hq3 : ((q : ZMod p)) ^ 3 = 1 := by
    have : ((q : ZMod p)) ^ 3 - 1 = ((q : ZMod p) - 1) * ((q : ZMod p) ^ 2 + q + 1) := by ring
    rw [hq, mul_zero, sub_eq_zero] at this
    exact this
  have hq1 : (q : ZMod p) ≠ 1 := by
    intro h
    rw [h] at hq
    have h3 : ((3 : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination hq
    rw [ZMod.natCast_eq_zero_iff] at h3
    exact absurd (Nat.le_of_dvd (by norm_num) h3) (by omega)
  have hord : orderOf (q : ZMod p) = 3 :=
    orderOf_eq_prime hq3 hq1
  have hq0 : (q : ZMod p) ≠ 0 := by
    intro h
    rw [h] at hq
    norm_num at hq
  have hdvd : 3 ∣ p - 1 := hord ▸ ZMod.orderOf_dvd_card_sub_one hq0
  have hmod : p % 3 = 1 := by omega
  refine ⟨hord, hmod, ?_⟩
  by_contra h
  have h4 : p = 4 := by omega
  rw [h4] at hp
  exact absurd hp (by norm_num)

theorem phi3_residue_facts {p q : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ q ^ 2 + q + 1) :
    ((q : ZMod p)) ^ 2 + q + 1 = 0 ∧ ((q : ZMod p)) ^ 3 = 1 ∧ (q : ZMod p) ≠ 0 ∧
      (q : ZMod p) ≠ 1 ∧ ((q : ZMod p)) ^ 2 ≠ 1 ∧ ((q : ZMod p)) ^ 2 + 1 ≠ 0 ∧
      (2 : ZMod p) ≠ 0 ∧ (3 : ZMod p) ≠ 0 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hord, -, -⟩ := phi3_prime_facts hp hp3 hpq
  have hq : ((q : ZMod p)) ^ 2 + q + 1 = 0 := by
    have := (ZMod.natCast_eq_zero_iff _ p).mpr hpq
    push_cast at this
    exact this
  have hq3 : ((q : ZMod p)) ^ 3 = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one _
  have hq1 : (q : ZMod p) ≠ 1 := fun h => by
    rw [h, orderOf_one] at hord
    exact absurd hord (by norm_num)
  have h2 : (2 : ZMod p) ≠ 0 := by
    have := (ZMod.natCast_eq_zero_iff 2 p).not.mpr (fun h => absurd (Nat.le_of_dvd (by norm_num) h)
      (by omega))
    exact_mod_cast this
  have h3 : (3 : ZMod p) ≠ 0 := by
    have := (ZMod.natCast_eq_zero_iff 3 p).not.mpr (fun h => absurd (Nat.le_of_dvd (by norm_num) h)
      (by omega))
    exact_mod_cast this
  have hq0 : (q : ZMod p) ≠ 0 := fun h => by
    rw [h] at hq
    norm_num at hq
  refine ⟨hq, hq3, hq0, hq1, fun h => hq1 ?_, fun h => hq0 ?_, h2, h3⟩
  · calc (q : ZMod p) = (q : ZMod p) * (q : ZMod p) ^ 2 := by rw [h, mul_one]
      _ = (q : ZMod p) ^ 3 := by ring
      _ = 1 := hq3
  · linear_combination hq - h

theorem padicValNat_twistedE6_order {p q : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ q ^ 2 + q + 1) (hq : 1 ≤ q) :
    padicValNat p (q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
      (q ^ 5 + 1) * (q ^ 2 - 1)) = 2 * padicValNat p (q ^ 2 + q + 1) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hQ, hQ3, hQ0, hQ1, hQ2, hQ21, h2, -⟩ := phi3_residue_facts hp hp3 hpq
  set Q : ZMod p := (q : ZMod p) with hQdef
  have hqq : 2 ≤ q := by
    by_contra h
    obtain rfl : q = 1 := by omega
    apply hQ1
    rw [hQdef, Nat.cast_one]
  have nd : ∀ x : ℕ, (x : ZMod p) ≠ 0 → padicValNat p x = 0 := fun x hx =>
    padicValNat.eq_zero_of_not_dvd fun h => hx ((ZMod.natCast_eq_zero_iff x p).mpr h)
  have hcast : ∀ n : ℕ, 1 ≤ n → (((q ^ n - 1 : ℕ)) : ZMod p) = Q ^ n - 1 := fun n hn => by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega)), Nat.cast_pow, Nat.cast_one]
  have hQ6 : Q ^ 6 = 1 := by rw [show 6 = 3 * 2 by rfl, pow_mul, hQ3, one_pow]
  have hQ9 : Q ^ 9 = 1 := by rw [show 9 = 3 * 3 by rfl, pow_mul, hQ3, one_pow]
  have e12 : q ^ 12 - 1 = (q - 1) * (q ^ 2 + q + 1) * (q ^ 9 + q ^ 6 + q ^ 3 + 1) := by
    zify [Nat.one_le_pow 12 q (by omega), hq]
    ring
  have e6 : q ^ 6 - 1 = (q - 1) * (q ^ 2 + q + 1) * (q ^ 3 + 1) := by
    zify [Nat.one_le_pow 6 q (by omega), hq]
    ring
  rw [e12, e6]
  have ne : ∀ x : ℕ, 1 ≤ x → x ≠ 0 := fun x hx => by omega
  have hq1' : 1 ≤ q - 1 := by omega
  have hpos : ∀ n : ℕ, 1 ≤ n → 1 ≤ q ^ n - 1 := fun n hn => by
    have : 2 ≤ q ^ n := le_trans hqq (Nat.le_self_pow (by omega) q)
    omega
  have hd : 1 ≤ q ^ 2 + q + 1 := by omega
  have v36 : padicValNat p (q ^ 36) = 0 := nd _ (by push_cast; exact pow_ne_zero _ hQ0)
  have vq1 : padicValNat p (q - 1) = 0 := nd _ (by
    rw [Nat.cast_sub hq, Nat.cast_one]
    exact sub_ne_zero.mpr hQ1)
  have vA : padicValNat p (q ^ 9 + q ^ 6 + q ^ 3 + 1) = 0 := nd _ (by
    push_cast
    rw [← hQdef, hQ9, hQ6, hQ3]
    norm_num
    rw [show (4 : ZMod p) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2)
  have v9 : padicValNat p (q ^ 9 + 1) = 0 := nd _ (by
    push_cast
    rw [← hQdef, hQ9]
    norm_num
    exact h2)
  have v8 : padicValNat p (q ^ 8 - 1) = 0 := nd _ (by
    rw [hcast 8 (by norm_num), show Q ^ 8 = Q ^ 6 * Q ^ 2 by ring, hQ6, one_mul]
    exact sub_ne_zero.mpr hQ2)
  have vB : padicValNat p (q ^ 3 + 1) = 0 := nd _ (by
    push_cast
    rw [← hQdef, hQ3]
    norm_num
    exact h2)
  have v5 : padicValNat p (q ^ 5 + 1) = 0 := nd _ (by
    push_cast
    rw [← hQdef, show Q ^ 5 = Q ^ 3 * Q ^ 2 by ring, hQ3, one_mul, add_comm]
    rw [add_comm] at hQ21
    exact hQ21)
  have v2 : padicValNat p (q ^ 2 - 1) = 0 := nd _ (by
    rw [hcast 2 (by norm_num)]
    exact sub_ne_zero.mpr hQ2)
  have hm : ∀ a b : ℕ, 0 < a → 0 < b → padicValNat p (a * b) = padicValNat p a + padicValNat p b :=
    fun a b ha hb => padicValNat.mul ha.ne' hb.ne'
  have p1 : 0 < q ^ 36 := pow_pos (by omega) _
  have p2 : 0 < (q - 1) * (q ^ 2 + q + 1) * (q ^ 9 + q ^ 6 + q ^ 3 + 1) :=
    Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  have p3 : 0 < q ^ 9 + 1 := by omega
  have p4 : 0 < q ^ 8 - 1 := by have := hpos 8 (by norm_num); omega
  have p5 : 0 < (q - 1) * (q ^ 2 + q + 1) * (q ^ 3 + 1) :=
    Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  have p6 : 0 < q ^ 5 + 1 := by omega
  have p7 : 0 < q ^ 2 - 1 := by have := hpos 2 (by norm_num); omega
  rw [hm _ _ (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos p1 p2) p3) p4) p5)
      p6) p7, hm _ _ (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos p1 p2) p3) p4) p5) p6,
    hm _ _ (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos p1 p2) p3) p4) p5,
    hm _ _ (Nat.mul_pos (Nat.mul_pos p1 p2) p3) p4, hm _ _ (Nat.mul_pos p1 p2) p3, hm _ _ p1 p2,
    hm _ _ (Nat.mul_pos (by omega) (by omega)) (by omega), hm _ _ (by omega) (by omega),
    hm _ _ (Nat.mul_pos (by omega) (by omega)) (by omega), hm _ _ (by omega) (by omega),
    v36, vq1, vA, v9, v8, vB, v5, v2]
  ring

theorem padicValNat_phi3_torus_order {p q : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ q ^ 2 + q + 1) :
    padicValNat p ((q ^ 2 + q + 1) ^ 2 * (q ^ 2 - q + 1)) = 2 * padicValNat p (q ^ 2 + q + 1) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hQ, -, hQ0, -, -, -, h2, -⟩ := phi3_residue_facts hp hp3 hpq
  have hle : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  have he : padicValNat p (q ^ 2 - q + 1) = 0 := padicValNat.eq_zero_of_not_dvd fun h => by
    have h1 := (ZMod.natCast_eq_zero_iff _ p).mpr h
    rw [Nat.cast_add, Nat.cast_sub hle, Nat.cast_pow, Nat.cast_one] at h1
    have h3 : (2 : ZMod p) * (q : ZMod p) = 0 := by linear_combination hQ - h1
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact h2 h4
    · exact hQ0 h4
  rw [padicValNat.mul (pow_ne_zero 2 (by omega)) (by omega), padicValNat.pow _ 2, he, add_zero]

@[expose] def phi3VWord : List (Fin 6) :=
  [3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 2, 3, 0, 2, 1, 3, 4, 1, 3, 1]

@[expose] def phi3V : WeylGroup Tag.E6 := (coxeterSystem Tag.E6).wordProd (e6Word phi3VWord)

theorem weylMatrix_phi3V : weylMatrix phi3V = -(coxeterSqMatrix * rhoMatrix) :=
  weylMatrix_wordProd_e6 (by decide +kernel)

theorem phi3V_smul (x : Fin Tag.E6.rank → ℤ) :
    phi3V • x = -(e6CoxeterSq • permLattice e6Rho x) := by
  rw [← weylMatrix_mulVec, weylMatrix_phi3V, permLattice_eq_mulVec, ← weylMatrix_mulVec,
    weylMatrix_e6CoxeterSq, Matrix.mulVec_mulVec, Matrix.neg_mulVec]

theorem e6Rho_symm : e6Rho.symm = e6Rho := by decide

theorem det_scalar_add_coxeterSqMatrix (q : ℤ) :
    (Matrix.scalar (Fin Tag.E6.rank) q + coxeterSqMatrix).det =
      (q ^ 2 + q + 1) ^ 2 * (q ^ 2 - q + 1) := by
  have h := congrArg (Polynomial.eval (-q)) charpoly_coxeterSqMatrix
  rw [Matrix.eval_charpoly] at h
  have e : Matrix.scalar (Fin Tag.E6.rank) (-q) - coxeterSqMatrix =
      -(Matrix.scalar (Fin Tag.E6.rank) q + coxeterSqMatrix) := by
    rw [map_neg, neg_add', sub_eq_add_neg]
  rw [e, Matrix.det_neg, Fintype.card_fin] at h
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_one] at h
  have h6 : ((-1 : ℤ)) ^ Tag.E6.rank = 1 := by decide
  rw [h6, one_mul] at h
  rw [h]
  ring

section Count

variable {Ω : Type*} [Field Ω] {r : ℕ}

@[expose] def latticeChar (t : Fin r → Ωˣ) : (Fin r → ℤ) →+ Additive Ωˣ where
  toFun n := Additive.ofMul (∏ j, t j ^ n j)
  map_zero' := by simp
  map_add' a b := by
    rw [← ofMul_mul]
    congr 1
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => by rw [Pi.add_apply, _root_.zpow_add]

theorem latticeChar_apply (t : Fin r → Ωˣ) (n : Fin r → ℤ) :
    latticeChar t n = Additive.ofMul (∏ j, t j ^ n j) :=
  rfl

theorem latticeChar_single (t : Fin r → Ωˣ) (j : Fin r) (x : ℤ) :
    latticeChar t (Pi.single j x) = Additive.ofMul (t j ^ x) := by
  rw [latticeChar_apply]
  congr 1
  rw [Finset.prod_eq_single j (fun i _ hij => by rw [Pi.single_eq_of_ne hij, zpow_zero])
    (fun h => absurd (Finset.mem_univ j) h), Pi.single_eq_same]

theorem mem_ker_monomialHom_iff (M : Matrix (Fin r) (Fin r) ℤ) (t : Fin r → Ωˣ) :
    t ∈ (monomialHom (G := Ωˣ) M).ker ↔
      (LinearMap.range (Matrix.toLin' Mᵀ)).toAddSubgroup ≤ (latticeChar t).ker := by
  rw [MonoidHom.mem_ker]
  have e : ∀ i j, (Mᵀ.mulVec (Pi.single i 1)) j = M i j := fun i j => by
    simp [Matrix.mulVec_single]
  constructor
  · rintro h _ ⟨n, rfl⟩
    have hbasis : ∀ i, Matrix.toLin' Mᵀ (Pi.single i 1) ∈ (latticeChar t).ker := by
      intro i
      rw [AddMonoidHom.mem_ker, latticeChar_apply, Matrix.toLin'_apply]
      simp only [e]
      have hi := congrFun h i
      rw [monomialHom_apply, Pi.one_apply] at hi
      rw [hi]
      rfl
    have hn : n = ∑ i, n i • Pi.single i (1 : ℤ) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hn, map_sum]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    rw [map_zsmul]
    exact AddSubgroup.zsmul_mem _ (hbasis i) _
  · intro h
    funext i
    have hi := h (show Matrix.toLin' Mᵀ (Pi.single i 1) ∈
      (LinearMap.range (Matrix.toLin' Mᵀ)).toAddSubgroup from ⟨_, rfl⟩)
    rw [AddMonoidHom.mem_ker, latticeChar_apply, Matrix.toLin'_apply] at hi
    rw [monomialHom_apply, Pi.one_apply]
    simp only [e] at hi
    exact hi

theorem natCard_ker_monomialHom [IsAlgClosed Ω] (M : Matrix (Fin r) (Fin r) ℤ)
    (hM : (M.det : Ω) ≠ 0) : Nat.card (monomialHom (G := Ωˣ) M).ker = M.det.natAbs := by
  set N := (LinearMap.range (Matrix.toLin' Mᵀ)).toAddSubgroup with hN
  have hdet0 : M.det ≠ 0 := fun h => hM (by rw [h, Int.cast_zero])
  have hcardA : Nat.card ((Fin r → ℤ) ⧸ N) = M.det.natAbs := by
    change N.index = _
    rw [hN, index_range_toLin'_eq_natAbs_det Mᵀ (by rwa [Matrix.det_transpose]),
      Matrix.det_transpose]
  have : Finite ((Fin r → ℤ) ⧸ N) :=
    Nat.finite_of_card_ne_zero (by rw [hcardA]; exact Int.natAbs_ne_zero.mpr hdet0)
  let Φ : (monomialHom (G := Ωˣ) M).ker → ((Fin r → ℤ) ⧸ N →+ Additive Ωˣ) := fun t =>
    QuotientAddGroup.lift N (latticeChar t.1) ((mem_ker_monomialHom_iff M t.1).mp t.2)
  have hΦ : Function.Bijective Φ := by
    constructor
    · intro t s h
      apply Subtype.ext
      funext j
      have := congrArg (fun g : (Fin r → ℤ) ⧸ N →+ Additive Ωˣ =>
        g (QuotientAddGroup.mk (Pi.single j 1))) h
      simp only [Φ, QuotientAddGroup.lift_mk, latticeChar_single, zpow_one] at this
      exact this
    · intro g
      set t : Fin r → Ωˣ := fun j => Additive.toMul (g (QuotientAddGroup.mk (Pi.single j 1)))
        with ht
      have hcomp : latticeChar t = g.comp (QuotientAddGroup.mk' N) := by
        refine AddMonoidHom.functions_ext _ _ _ fun i x => ?_
        rw [latticeChar_single, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply,
          show (Pi.single i x : Fin r → ℤ) = x • Pi.single i 1 by
            rw [← Pi.single_smul, smul_eq_mul, mul_one],
          QuotientAddGroup.mk_zsmul, map_zsmul, ht]
        rfl
      have hker : t ∈ (monomialHom (G := Ωˣ) M).ker := by
        rw [mem_ker_monomialHom_iff, hcomp]
        intro x hx
        rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply,
          (QuotientAddGroup.eq_zero_iff x).mpr hx, map_zero]
      refine ⟨⟨t, hker⟩, QuotientAddGroup.addMonoidHom_ext N ?_⟩
      rw [← hcomp]
      ext x
      simp only [Φ, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply,
        QuotientAddGroup.lift_mk]
  have hD : ((M.det.natAbs : ℕ) : Ω) ≠ 0 := by
    intro h
    rcases Int.natAbs_eq M.det with e | e
    · rw [e, Int.cast_natCast, h] at hM
      exact hM rfl
    · rw [e, Int.cast_neg, Int.cast_natCast, h, neg_zero] at hM
      exact hM rfl
  have hexp : NeZero ((Monoid.exponent (Multiplicative ((Fin r → ℤ) ⧸ N)) : ℕ) : Ω) := by
    refine ⟨fun h => hD ?_⟩
    obtain ⟨c, hc⟩ := (Group.exponent_dvd_nat_card (G := Multiplicative ((Fin r → ℤ) ⧸ N)))
    change Nat.card ((Fin r → ℤ) ⧸ N) = _ at hc
    rw [← hcardA, hc, Nat.cast_mul, h, zero_mul]
  have := IsSepClosed.hasEnoughRootsOfUnity Ω
    (Monoid.exponent (Multiplicative ((Fin r → ℤ) ⧸ N)))
  calc Nat.card (monomialHom (G := Ωˣ) M).ker =
        Nat.card ((Fin r → ℤ) ⧸ N →+ Additive Ωˣ) := Nat.card_congr (Equiv.ofBijective Φ hΦ)
    _ = Nat.card (Multiplicative ((Fin r → ℤ) ⧸ N) →* Ωˣ) :=
        Nat.card_congr AddMonoidHom.toMultiplicativeLeft
    _ = Nat.card (Multiplicative ((Fin r → ℤ) ⧸ N)) :=
        CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity _ _
    _ = M.det.natAbs := hcardA

end Count

section Torus

variable (Ω : Type) [Field Ω] (Fr : Ω →+* Ω)

@[expose] def twistE6 : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω := twistHom TwistTag.E6 Ω Fr

@[expose] def phi3Theta : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω :=
  (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω phi3V)).toMonoidHom.comp (twistE6 Ω Fr)

@[expose] def phi3FixedGroup : Subgroup (ModGL Tag.E6 Ω) :=
  adjointGroup Tag.E6 Ω ⊓ MonoidHom.eqLocus (phi3Theta Ω Fr) (MonoidHom.id _)

@[expose] def phi3Torus : Subgroup (ModGL Tag.E6 Ω) :=
  torusGroup Tag.E6 Ω ⊓ phi3FixedGroup Ω Fr

variable {Ω Fr}

@[expose] def phi3Matrix (q : ℕ) : Matrix (Fin Tag.E6.rank) (Fin Tag.E6.rank) ℤ :=
  Matrix.scalar (Fin Tag.E6.rank) (q : ℤ) + coxeterSqMatrix

theorem det_phi3Matrix (q : ℕ) :
    (phi3Matrix q).det = ((q : ℤ) ^ 2 + q + 1) ^ 2 * ((q : ℤ) ^ 2 - q + 1) :=
  det_scalar_add_coxeterSqMatrix q

theorem mem_phi3FixedGroup_iff {g : ModGL Tag.E6 Ω} :
    g ∈ phi3FixedGroup Ω Fr ↔ g ∈ adjointGroup Tag.E6 Ω ∧ phi3Theta Ω Fr g = g :=
  Iff.rfl

theorem phi3Theta_apply (g : ModGL Tag.E6 Ω) :
    phi3Theta Ω Fr g = canonicalRep (coxeterSystem Tag.E6) Ω phi3V * twistE6 Ω Fr g *
      (canonicalRep (coxeterSystem Tag.E6) Ω phi3V)⁻¹ :=
  rfl

theorem twistE6_rootDiagUnit (b : Fin Tag.E6.rank → Ωˣ) :
    twistE6 Ω Fr (rootDiagUnit Tag.E6 b) =
      rootDiagUnit Tag.E6 (fun i => Units.map Fr.toMonoidHom (b (e6Rho.symm i))) :=
  twistHom_rootDiagUnit_eq (t := TwistTag.E6) b

theorem rootChar_neg' {τ : Tag} (b : Fin τ.rank → Ωˣ) (x : Fin τ.rank → ℤ) :
    rootChar b (-x) = (rootChar b x)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← rootChar_add, neg_add_cancel, rootChar_zero]

theorem rootChar_phi3Matrix_mulVec (q : ℕ) (b : Fin Tag.E6.rank → Ωˣ)
    (μ : Fin Tag.E6.rank → ℤ) :
    rootChar b (phi3Matrix q *ᵥ μ) = rootChar b (e6CoxeterSq • μ) * rootChar b μ ^ q := by
  rw [phi3Matrix, Matrix.add_mulVec, ← weylMatrix_e6CoxeterSq, weylMatrix_mulVec,
    rootChar_add, mul_comm]
  congr 1
  have : (Matrix.scalar (Fin Tag.E6.rank) (q : ℤ)) *ᵥ μ = (q : ℤ) • μ := by
    ext i
    rw [Matrix.scalar_apply, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  rw [this, rootChar_zsmul, zpow_natCast]

theorem mem_ker_monomialHom_phi3_iff (q : ℕ) (b : Fin Tag.E6.rank → Ωˣ) :
    b ∈ (monomialHom (G := Ωˣ) (phi3Matrix q)ᵀ).ker ↔
      ∀ μ, rootChar b (phi3Matrix q *ᵥ μ) = 1 := by
  have hcol : ∀ j, rootChar b (phi3Matrix q *ᵥ Pi.single j 1) =
      (monomialHom (G := Ωˣ) (phi3Matrix q)ᵀ b) j := fun j => by
    rw [monomialHom_apply, rootChar]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [Matrix.mulVec_single, Matrix.transpose_apply]
  rw [MonoidHom.mem_ker]
  constructor
  · intro h μ
    have hμ : μ = ∑ j, μ j • (Pi.single j 1 : Fin Tag.E6.rank → ℤ) := by
      ext i
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hμ, Matrix.mulVec_sum, rootChar_sum]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [Matrix.mulVec_smul, rootChar_zsmul, hcol, h, Pi.one_apply, one_zpow]
  · intro h
    funext j
    rw [← hcol, h, Pi.one_apply]

theorem phi3Theta_rootDiagUnit_eq_iff {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    (b : Fin Tag.E6.rank → Ωˣ) :
    phi3Theta Ω Fr (rootDiagUnit Tag.E6 b) = rootDiagUnit Tag.E6 b ↔
      b ∈ (monomialHom (G := Ωˣ) (phi3Matrix q)ᵀ).ker := by
  have hb' : (fun i => Units.map Fr.toMonoidHom (b (e6Rho.symm i))) =
      (fun i => b (e6Rho.symm i)) ^ q := by
    funext i
    refine Units.ext ?_
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, hFr]
    rfl
  rw [phi3Theta_apply, twistE6_rootDiagUnit, hb', eq_comm,
    rootDiagUnit_eq_conj_canonicalRep_iff, mem_ker_monomialHom_phi3_iff]
  have hrr : ∀ x : Fin Tag.E6.rank → ℤ, permLattice e6Rho (permLattice e6Rho x) = x := by
    intro x
    funext i
    simp only [permLattice, Function.comp_apply]
    rw [e6Rho_symm, show e6Rho (e6Rho i) = i by revert i; decide]
  have hchar : ∀ v, rootChar ((fun i => b (e6Rho.symm i)) ^ q) v =
      rootChar b (permLattice e6Rho v) ^ q := by
    intro v
    rw [CFSG.RankThree.Chevalley.rootChar_pow_tuple, ← rootChar_permLattice, e6Rho_symm]
  constructor
  · intro h μ
    have h1 := h (permLattice e6Rho μ)
    rw [phi3V_smul, hrr, hchar, hrr, rootChar_neg'] at h1
    rw [rootChar_phi3Matrix_mulVec, ← h1, mul_inv_cancel]
  · intro h v
    rw [phi3V_smul, hchar, rootChar_neg', inv_eq_iff_mul_eq_one]
    have h1 := h (permLattice e6Rho v)
    rw [rootChar_phi3Matrix_mulVec] at h1
    exact h1

theorem torusGroup_le_adjointGroup_E6 : torusGroup Tag.E6 Ω ≤ adjointGroup Tag.E6 Ω := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨⟨i, t⟩, rfl⟩
  exact torusElt_mem_adjointGroup i t

theorem odd_phi3_order (q : ℕ) : Odd ((q ^ 2 + q + 1) ^ 2 * (q ^ 2 - q + 1)) := by
  have h1 : Odd (q ^ 2 + q + 1) := by
    have : q ^ 2 + q = q * (q + 1) := by ring
    rw [this]
    exact (Nat.even_mul_succ_self q).add_one
  have h2 : Odd (q ^ 2 - q + 1) := by
    have : q ^ 2 - q = q * (q - 1) := by rw [sq, Nat.mul_sub_one]
    rw [this]
    exact (Nat.even_mul_pred_self q).add_one
  exact h1.pow.mul h2

@[expose] def phi3TorusEquiv [IsAlgClosed Ω] {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) :
    (monomialHom (G := Ωˣ) (phi3Matrix q)ᵀ).ker ≃ phi3Torus Ω Fr :=
  Equiv.ofBijective
    (fun b => ⟨rootDiagUnit Tag.E6 b.1, rootDiagUnit_mem_torusGroup b.1,
      torusGroup_le_adjointGroup_E6 (rootDiagUnit_mem_torusGroup b.1),
      (phi3Theta_rootDiagUnit_eq_iff hFr b.1).mpr b.2⟩)
    ⟨fun b c h => Subtype.ext (rootDiagUnit_injective (congrArg Subtype.val h)), fun x => by
      obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup x.2.1
      refine ⟨⟨b, (phi3Theta_rootDiagUnit_eq_iff hFr b).mp ?_⟩, Subtype.ext hb.symm⟩
      rw [← hb]
      exact x.2.2.2⟩

theorem coe_phi3TorusEquiv [IsAlgClosed Ω] {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    (b : (monomialHom (G := Ωˣ) (phi3Matrix q)ᵀ).ker) :
    ((phi3TorusEquiv hFr b : phi3Torus Ω Fr) : ModGL Tag.E6 Ω) = rootDiagUnit Tag.E6 b.1 :=
  rfl

theorem natCard_phi3Torus [IsAlgClosed Ω] {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    (hq : (q : Ω) = 0) :
    Nat.card (phi3Torus Ω Fr) = (q ^ 2 + q + 1) ^ 2 * (q ^ 2 - q + 1) ∧
      Odd (Nat.card (phi3Torus Ω Fr)) := by
  have hdet : ((phi3Matrix q)ᵀ).det = ((q ^ 2 + q + 1) ^ 2 * (q ^ 2 - q + 1) : ℕ) := by
    rw [Matrix.det_transpose, det_phi3Matrix]
    have : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
    push_cast [this]
    ring
  have hne : (((phi3Matrix q)ᵀ).det : Ω) ≠ 0 := by
    rw [Matrix.det_transpose, det_phi3Matrix]
    push_cast
    rw [hq]
    norm_num
  have h := natCard_ker_monomialHom (Ω := Ω) (phi3Matrix q)ᵀ hne
  rw [hdet, Int.natAbs_natCast, Nat.card_congr (phi3TorusEquiv hFr)] at h
  exact ⟨h, h ▸ odd_phi3_order q⟩

end Torus

section Lang

variable {Ω : Type} [Field Ω] {Fr : Ω →+* Ω}

variable (Ω Fr) in
@[expose] def phi3Rzero : Subgroup (ModGL Tag.E6 Ω) :=
  CFSG.Blueprint.twistedFixedGroup TwistTag.E6 Ω Fr

theorem mem_phi3Rzero_iff {g : ModGL Tag.E6 Ω} :
    g ∈ phi3Rzero Ω Fr ↔ g ∈ adjointGroup Tag.E6 Ω ∧ twistE6 Ω Fr g = g :=
  Iff.rfl

theorem exists_inv_mul_twistE6_eq [IsAlgClosed Ω] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP Ω ℓ]
    (hf : 1 ≤ f) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {x : ModGL Tag.E6 Ω}
    (hx : x ∈ adjointGroup Tag.E6 Ω) :
    ∃ g ∈ adjointGroup Tag.E6 Ω, g⁻¹ * twistE6 Ω Fr g = x := by
  obtain ⟨-, hlang⟩ :=
    CFSG.LieType.AlgebraicGroups.exceptional_all_characteristic_field_Lang_surjectivity ℓ Ω f hf
  obtain ⟨S, hS, hsurj⟩ := hlang TwistTag.E6 1
  obtain ⟨h, hh⟩ := hsurj ⟨x, hx⟩
  have hFr' : Fr = iterateFrobenius Ω ℓ f := RingHom.ext fun c => by
    rw [hFr, iterateFrobenius_def]
  refine ⟨h.1, h.2, ?_⟩
  have h1 := congrArg Subtype.val hh
  rw [Subgroup.coe_mul, Subgroup.coe_inv, hS, zpow_one] at h1
  subst hFr'
  exact h1.symm

theorem mem_phi3FixedGroup_iff_conj {g : ModGL Tag.E6 Ω} (hg : g ∈ adjointGroup Tag.E6 Ω)
    (hgn : g⁻¹ * twistE6 Ω Fr g = canonicalRep (coxeterSystem Tag.E6) Ω phi3V)
    (x : ModGL Tag.E6 Ω) : x ∈ phi3FixedGroup Ω Fr ↔ g * x * g⁻¹ ∈ phi3Rzero Ω Fr := by
  rw [mem_phi3FixedGroup_iff, mem_phi3Rzero_iff, phi3Theta_apply, ← hgn]
  have hG : x ∈ adjointGroup Tag.E6 Ω ↔ g * x * g⁻¹ ∈ adjointGroup Tag.E6 Ω := by
    constructor
    · intro hx
      exact mul_mem (mul_mem hg hx) (inv_mem hg)
    · intro hx
      have := mul_mem (mul_mem (inv_mem hg) hx) hg
      rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at this
  rw [hG, map_mul, map_mul, map_inv]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h
    calc twistE6 Ω Fr g * twistE6 Ω Fr x * (twistE6 Ω Fr g)⁻¹ =
        g * (g⁻¹ * twistE6 Ω Fr g * twistE6 Ω Fr x * (g⁻¹ * twistE6 Ω Fr g)⁻¹) * g⁻¹ := by
          group
      _ = g * x * g⁻¹ := by rw [h]
  · intro h
    calc g⁻¹ * twistE6 Ω Fr g * twistE6 Ω Fr x * (g⁻¹ * twistE6 Ω Fr g)⁻¹ =
        g⁻¹ * (twistE6 Ω Fr g * twistE6 Ω Fr x * (twistE6 Ω Fr g)⁻¹) * g := by group
      _ = x := by rw [h]; group

theorem phi3FixedGroup_eq_map {g : ModGL Tag.E6 Ω} (hg : g ∈ adjointGroup Tag.E6 Ω)
    (hgn : g⁻¹ * twistE6 Ω Fr g = canonicalRep (coxeterSystem Tag.E6) Ω phi3V) :
    phi3FixedGroup Ω Fr = (phi3Rzero Ω Fr).map (MulAut.conj g⁻¹).toMonoidHom := by
  ext x
  rw [mem_phi3FixedGroup_iff_conj hg hgn]
  constructor
  · intro hx
    refine ⟨g * x * g⁻¹, hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · rintro ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rwa [show g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ = y by group]

end Lang

section Torsion

variable {Ω : Type} [Field Ω] {Fr : Ω →+* Ω}

theorem torusGroup_E6_comm {x y : ModGL Tag.E6 Ω} (hx : x ∈ torusGroup Tag.E6 Ω)
    (hy : y ∈ torusGroup Tag.E6 Ω) : x * y = y * x := by
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hy
  rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]

variable (Ω Fr) in
@[expose] def phi3TorusTorsion (p : ℕ) : Subgroup (ModGL Tag.E6 Ω) where
  carrier := {t | t ∈ phi3Torus Ω Fr ∧ t ^ p = 1}
  mul_mem' {x y} hx hy := ⟨mul_mem hx.1 hy.1, by
    rw [Commute.mul_pow (torusGroup_E6_comm hx.1.1 hy.1.1) p, hx.2, hy.2, one_mul]⟩
  one_mem' := ⟨one_mem _, one_pow p⟩
  inv_mem' {x} hx := ⟨inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩

theorem mem_phi3TorusTorsion {p : ℕ} {t : ModGL Tag.E6 Ω} :
    t ∈ phi3TorusTorsion Ω Fr p ↔ t ∈ phi3Torus Ω Fr ∧ t ^ p = 1 :=
  Iff.rfl

variable {r : ℕ}

theorem zetaPow_mem_ker_monomialHom_iff {p : ℕ} [NeZero p] {ζ : Ωˣ} (hζ : IsPrimitiveRoot ζ p)
    (M : Matrix (Fin r) (Fin r) ℤ) (z : Fin r → ZMod p) :
    (fun i => ζ ^ (z i).val) ∈ (monomialHom (G := Ωˣ) M).ker ↔
      (M.map (Int.cast : ℤ → ZMod p)) *ᵥ z = 0 := by
  rw [MonoidHom.mem_ker, funext_iff, funext_iff]
  refine forall_congr' fun j => ?_
  have hprod : monomialHom (G := Ωˣ) M (fun i => ζ ^ (z i).val) j =
      ζ ^ (∑ i, ((z i).val : ℤ) * M j i) := by
    rw [monomialHom_apply, zpow_finsetSum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_natCast, ← zpow_mul]
  rw [hprod, Pi.one_apply, Pi.zero_apply, hζ.zpow_eq_one_iff_dvd,
    ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  simp only [ZMod.natCast_zmod_val, Matrix.mulVec, dotProduct, Matrix.map_apply]
  rw [Finset.sum_congr rfl fun i _ => mul_comm (z i) ((M j i : ℤ) : ZMod p)]

theorem phi3Matrix_transpose_mulVec_eq_zero_iff {p : ℕ} (q : ℕ) (z : Fin Tag.E6.rank → ZMod p) :
    ((phi3Matrix q)ᵀ.map (Int.cast : ℤ → ZMod p)) *ᵥ z = 0 ↔
      (dualMatrix (ZMod p) e6CoxeterSq) *ᵥ z = (-(q : ZMod p)) • z := by
  have hM : (phi3Matrix q)ᵀ.map (Int.cast : ℤ → ZMod p) =
      Matrix.scalar (Fin Tag.E6.rank) (q : ZMod p) + dualMatrix (ZMod p) e6CoxeterSq := by
    rw [dualMatrix_e6CoxeterSq, phi3Matrix, Matrix.transpose_add, Matrix.map_add _ Int.cast_add,
      Matrix.transpose_map]
    congr 1
    rw [Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_map Int.cast_zero,
      Matrix.diagonal_transpose]
    simp only [Int.cast_natCast]
  rw [hM, Matrix.add_mulVec, neg_smul, eq_neg_iff_add_eq_zero, add_comm]
  have : Matrix.scalar (Fin Tag.E6.rank) (q : ZMod p) *ᵥ z = (q : ZMod p) • z := by
    ext i
    rw [Matrix.scalar_apply, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  rw [this]

@[expose] def eisensteinEquiv {R : Type*} [CommRing R] {r : R} (hr : r ^ 2 - r + 1 = 0) :
    R × R ≃ {z : Fin Tag.E6.rank → R // (dualMatrix R e6CoxeterSq) *ᵥ z = r • z} where
  toFun x := ⟨eisensteinColumn r x.1 x.2, dualMatrix_mulVec_eisensteinColumn hr x.1 x.2⟩
  invFun z := (z.1 (e6Index 4), z.1 (e6Index 5))
  left_inv _ := rfl
  right_inv z := Subtype.ext (eq_eisensteinColumn_of_dualMatrix_mulVec hr z.2).symm

theorem natCard_phi3TorusTorsion [IsAlgClosed Ω] {q p : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    (hq : (q : Ω) = 0) (hp : p.Prime) (hpq : p ∣ q ^ 2 + q + 1) :
    Nat.card (phi3TorusTorsion Ω Fr p) = p ^ 2 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hpΩ : NeZero (p : Ω) := ⟨fun h => by
    obtain ⟨c, hc⟩ := hpq
    have h1 : ((q ^ 2 + q + 1 : ℕ) : Ω) = 0 := by rw [hc, Nat.cast_mul, h, zero_mul]
    push_cast at h1
    rw [hq] at h1
    norm_num at h1⟩
  have := IsSepClosed.hasEnoughRootsOfUnity Ω p
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω p
  set ζ : Ωˣ := (hζ₀.isUnit hp.ne_zero).unit with hζdef
  have hζ : IsPrimitiveRoot ζ p := IsPrimitiveRoot.coe_units_iff.mp (by
    rw [hζdef, IsUnit.unit_spec]
    exact hζ₀)
  set r : ZMod p := -(q : ZMod p) with hrdef
  have hr : r ^ 2 - r + 1 = 0 := by
    have h := (ZMod.natCast_eq_zero_iff _ p).mpr hpq
    push_cast at h
    rw [hrdef]
    linear_combination h
  let ψ : {z : Fin Tag.E6.rank → ZMod p // (dualMatrix (ZMod p) e6CoxeterSq) *ᵥ z = r • z} →
      phi3TorusTorsion Ω Fr p := fun z =>
    ⟨rootDiagUnit Tag.E6 (fun i => ζ ^ (z.1 i).val),
      ⟨⟨rootDiagUnit_mem_torusGroup _,
        torusGroup_le_adjointGroup_E6 (rootDiagUnit_mem_torusGroup _),
        (phi3Theta_rootDiagUnit_eq_iff hFr _).mpr
          ((zetaPow_mem_ker_monomialHom_iff hζ _ z.1).mpr
            ((phi3Matrix_transpose_mulVec_eq_zero_iff q z.1).mpr z.2))⟩, by
        change (rootDiagUnitHom Tag.E6 Ω (fun i => ζ ^ (z.1 i).val)) ^ p = 1
        rw [← map_pow]
        change rootDiagUnit Tag.E6 _ = 1
        rw [show ((fun i => ζ ^ (z.1 i).val) ^ p : Fin Tag.E6.rank → Ωˣ) = 1 by
          funext i
          rw [Pi.pow_apply, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, Pi.one_apply],
          rootDiagUnit_one]⟩⟩
  have hψ : Function.Bijective ψ := by
    constructor
    · intro z w h
      have h1 := rootDiagUnit_injective (congrArg Subtype.val h)
      apply Subtype.ext
      funext i
      have h2 := congrFun h1 i
      exact ZMod.val_injective p (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h2)
    · intro t
      obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup t.2.1.1
      have hbker : b ∈ (monomialHom (G := Ωˣ) (phi3Matrix q)ᵀ).ker :=
        (phi3Theta_rootDiagUnit_eq_iff hFr b).mp (by rw [← hb]; exact t.2.1.2.2)
      have hbp : ∀ i, b i ^ p = 1 := by
        have h1 : rootDiagUnit Tag.E6 (b ^ p) = rootDiagUnit Tag.E6 1 := by
          rw [rootDiagUnit_one]
          change rootDiagUnitHom Tag.E6 Ω (b ^ p) = 1
          rw [map_pow]
          change rootDiagUnit Tag.E6 b ^ p = 1
          rw [← hb]
          exact t.2.2
        intro i
        exact congrFun (rootDiagUnit_injective h1) i
      have hmem : ∀ i, ∃ m : ℤ, ζ ^ m = b i := fun i => by
        have : b i ∈ rootsOfUnity p Ω := (mem_rootsOfUnity p (b i)).mpr (hbp i)
        rw [← hζ.zpowers_eq] at this
        obtain ⟨m, hm⟩ := this
        exact ⟨m, hm⟩
      choose m hm using hmem
      set z : Fin Tag.E6.rank → ZMod p := fun i => (m i : ZMod p) with hz
      have hzb : (fun i => ζ ^ (z i).val) = b := by
        funext i
        have h1 := zpow_mod_orderOf ζ (m i)
        rw [← hζ.eq_orderOf] at h1
        rw [← hm i, ← zpow_natCast, hz, ZMod.val_intCast, h1]
      have hzc : (dualMatrix (ZMod p) e6CoxeterSq) *ᵥ z = r • z := by
        rw [hrdef, ← phi3Matrix_transpose_mulVec_eq_zero_iff q z,
          ← zetaPow_mem_ker_monomialHom_iff hζ, hzb]
        exact hbker
      refine ⟨⟨z, hzc⟩, Subtype.ext ?_⟩
      change rootDiagUnit Tag.E6 (fun i => ζ ^ (z i).val) = t
      rw [hzb, hb]
  rw [← Nat.card_congr (Equiv.ofBijective ψ hψ), ← Nat.card_congr (eisensteinEquiv hr),
    Nat.card_prod, Nat.card_zmod, sq]

end Torsion

section GroupTheory

variable {D : Type*} [Group D]

theorem le_centralizer_of_isSolvable_normal {P V : Subgroup D} [P.Normal] [V.Normal]
    (hP : CFSG.IsQuasisimple P) (hV : Group.IsSolvable V) :
    V ≤ Subgroup.centralizer (P : Set D) := by
  have hperf : Group.IsPerfect P := hP.1
  have : Nontrivial P := by
    obtain ⟨a, b, hab⟩ := hP.2.1.toNontrivial.exists_pair_ne
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    exact hab (by rw [Subsingleton.elim x y])
  have hVP : V.subgroupOf P ≤ Subgroup.center P := by
    rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hP (V.subgroupOf P) with
      h | h
    · exact h
    · exfalso
      have hPV : ∀ x : P, (x : D) ∈ V := fun x => by
        have hx : x ∈ V.subgroupOf P := h ▸ Subgroup.mem_top x
        exact hx
      let f : P →* V :=
        { toFun := fun x => ⟨x, hPV x⟩, map_one' := rfl, map_mul' := fun _ _ => rfl }
      have : Group.IsSolvable P := Group.isSolvable_of_isSolvable_injective (f := f)
        (fun x y hxy => Subtype.ext (congrArg (fun z : V => (z : D)) hxy))
      exact Group.IsPerfect.not_isSolvable P this
  have hcomm : ⁅V, P⁆ ≤ Subgroup.centralizer (P : Set D) := by
    intro x hx
    have hx' := Subgroup.commutator_le_inf V P hx
    have hxc : (⟨x, hx'.2⟩ : P) ∈ Subgroup.center P := hVP hx'.1
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hxc ⟨y, hy⟩)
  have h1 : ⁅⁅V, P⁆, P⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcomm
  have h2 : ⁅⁅P, V⁆, P⁆ = ⊥ := by rw [Subgroup.commutator_comm P V]; exact h1
  have h3 : ⁅⁅P, P⁆, V⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h2 h1
  rw [Subgroup.commutator_eq_self] at h3
  exact Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3)

theorem odd_card_of_isSolvable_normal [Finite D] {P V : Subgroup D} [P.Normal] [V.Normal]
    (hP : CFSG.IsQuasisimple P) (hodd : Odd (Nat.card (Subgroup.centralizer (P : Set D))))
    (hV : Group.IsSolvable V) : Odd (Nat.card V) := by
  have hle := le_centralizer_of_isSolvable_normal hP hV
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hle
  rw [hk] at hodd
  exact (Nat.odd_mul.mp hodd).1

theorem eq_of_isElemAbelian_of_card {p : ℕ} {S E : Subgroup D} [Finite S]
    (hS : ∀ x, x ∈ S ↔ x ^ p = 1) (hSc : Nat.card S = p ^ 2)
    (hE : ∀ x ∈ E, x ^ p = 1) (hEc : Nat.card E = p ^ 2) : E = S :=
  Subgroup.eq_of_le_of_card_ge (fun x hx => (hS x).mpr (hE x hx)) (by rw [hSc, hEc])

end GroupTheory

end CFSG.RankThree.Classical2
