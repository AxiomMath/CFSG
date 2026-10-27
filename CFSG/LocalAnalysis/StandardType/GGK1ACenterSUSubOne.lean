module

public import CFSG.LocalAnalysis.StandardType.GGK1ACenterTorsion
public import CFSG.LocalAnalysis.StandardType.GGK1ACenterInvCount
public import CFSG.LocalAnalysis.StandardType.GGK1AMultUni
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQUni
public import CFSG.LinearAlgebra.MatrixPlanes
public import CFSG.RankThree.PartOne.KC.LinearSplitInner
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.RankThree.PartOne.KCPrimary

section Helpers

variable {p nf N : ℕ} {K : Type} [Field K] [Finite K]

private lemma cenUS2_one_le_nf (hK : Nat.card K = (2 ^ nf) ^ 2) : 1 ≤ nf := by
  rcases Nat.eq_zero_or_pos nf with h0 | hpos
  · exfalso
    rw [h0] at hK
    norm_num at hK
    have := Finite.one_lt_card (α := K)
    omega
  · exact hpos

private lemma cenUS2_charP (hK : Nat.card K = (2 ^ nf) ^ 2) : CharP K 2 := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine charP_of_card_eq_prime_pow (f := 2 * nf) ?_
  rw [← Nat.card_eq_fintype_card, hK, ← pow_mul, mul_comm]

private lemma cenUS2_unitaryData (hK : Nat.card K = (2 ^ nf) ^ 2) :
    CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 nf K :=
  ⟨Nat.prime_two, cenUS2_one_le_nf hK, by rw [hK, ← pow_mul, mul_comm]⟩

private lemma cenUS2_cast_p_ne_zero (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = (2 ^ nf) ^ 2) : (p : K) ≠ 0 := by
  have : CharP K 2 := cenUS2_charP hK
  intro hzero
  have h2 : 2 ∣ p := (CharP.cast_eq_zero_iff K 2 p).mp hzero
  rcases (Nat.dvd_prime hp).mp h2 with h | h
  · exact absurd h (by norm_num)
  · exact hp2 h.symm

omit [Field K] [Finite K] in
private lemma cenUS2_dvd_card_sub_one (hK : Nat.card K = (2 ^ nf) ^ 2)
    (hdvd : p ∣ 2 ^ nf - 1) : p ∣ Nat.card K - 1 := by
  rw [hK]
  have hsq : (2 ^ nf) ^ 2 - 1 = (2 ^ nf + 1) * (2 ^ nf - 1) := by
    simpa using Nat.sq_sub_sq (2 ^ nf) 1
  rw [hsq]
  exact dvd_mul_of_dvd_right hdvd _

private lemma cenUS2_coprime_add_one (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = (2 ^ nf) ^ 2) (hdvd : p ∣ 2 ^ nf - 1) :
    Nat.Coprime p (2 ^ nf + 1) := by
  have h2n : 2 ≤ 2 ^ nf := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ nf := Nat.pow_le_pow_right (by norm_num) (cenUS2_one_le_nf hK)
  rw [Nat.coprime_iff_gcd_eq_one]
  have hg2 : Nat.gcd p (2 ^ nf + 1) ∣ 2 := by
    have h1 : Nat.gcd p (2 ^ nf + 1) ∣ 2 ^ nf - 1 :=
      (Nat.gcd_dvd_left p (2 ^ nf + 1)).trans hdvd
    have h2 : Nat.gcd p (2 ^ nf + 1) ∣ 2 ^ nf + 1 := Nat.gcd_dvd_right p (2 ^ nf + 1)
    have h3 := Nat.dvd_sub h2 h1
    rwa [show 2 ^ nf + 1 - (2 ^ nf - 1) = 2 by omega] at h3
  rcases (Nat.dvd_prime (p := 2) Nat.prime_two).mp hg2 with h | h
  · exact h
  · exfalso
    have h2p : 2 ∣ p := h ▸ Nat.gcd_dvd_left p (2 ^ nf + 1)
    rcases (Nat.dvd_prime hp).mp h2p with h1 | h1
    · exact absurd h1 (by norm_num)
    · exact hp2 h1.symm

omit [Finite K] in
private lemma cenUS2_pow_q_eq_self {mu : K} (hdvd : p ∣ 2 ^ nf - 1)
    (hmu : mu ^ p = 1) : mu ^ 2 ^ nf = mu := by
  obtain ⟨k, hk⟩ := hdvd
  have h1 : 1 ≤ 2 ^ nf := Nat.one_le_two_pow
  rw [show 2 ^ nf = p * k + 1 by omega, pow_add, pow_mul, hmu, one_pow, one_mul, pow_one]

omit [Finite K] in
private lemma cenUS2_transpose_aeval {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (g : K[X]) :
    Matrix.transpose (aeval M g) = aeval (Matrix.transpose M) g := by
  induction g using Polynomial.induction_on' with
  | add q r hq hr => simp [map_add, hq, hr]
  | monomial m c =>
      rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial]
      simp only [Algebra.algebraMap_eq_smul_one, Matrix.transpose_smul, Matrix.transpose_pow,
        Matrix.smul_mul, Matrix.one_mul]

private lemma cenUS2_primaryFactors_linear (hp : p.Prime)
    (hK : Nat.card K = (2 ^ nf) ^ 2) (hdvd : p ∣ 2 ^ nf - 1) {x : GL (Fin N) K}
    (hxp : x ^ p = 1) :
    ∀ a ∈ primaryFactors (ggK1A_glEnd x), ∃ mu : K, mu ^ p = 1 ∧ a = X - C mu := by
  have : CharP K 2 := cenUS2_charP hK
  obtain ⟨ζ, hζ⟩ :=
    CFSG.RankThree.PartOne.exists_primitiveRoot_of_dvd_card_sub_one (k := K) hp
      (cenUS2_dvd_card_sub_one hK hdvd)
  have hfac : (X : K[X]) ^ p - 1 = ∏ z ∈ nthRootsFinset p (1 : K), (X - C z) :=
    Polynomial.X_pow_sub_one_eq_prod hp.pos hζ
  have hmin : minpoly K (ggK1A_glEnd x) ∣ (X : K[X]) ^ p - 1 := by
    refine minpoly.dvd K _ ?_
    have hmat : (x : Matrix (Fin N) (Fin N) K) ^ p = 1 := by
      simpa using congrArg (fun u : GL (Fin N) K => (u : Matrix (Fin N) (Fin N) K)) hxp
    have hpowe : ggK1A_glEnd x ^ p = 1 := by
      rw [ggK1A_glEnd, ← CFSG.RankThree.PartOne.KCLinComm.toLinAlgEquiv'_eq_toLin',
        ← map_pow, hmat, map_one]
    rw [map_sub, map_pow, Polynomial.aeval_X, hpowe, map_one, sub_self]
  intro a ha
  obtain ⟨hirr, hmon, hadivmin⟩ := mem_primaryFactors.mp ha
  have hprime : Prime a := UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr
  have hadiv : a ∣ ∏ z ∈ nthRootsFinset p (1 : K), (X - C z) := by
    rw [← hfac]
    exact hadivmin.trans hmin
  obtain ⟨z, hz, haz⟩ := (Prime.dvd_finsetProd_iff hprime (fun z => X - C z)).mp hadiv
  have hzp : z ^ p = 1 := by
    have h := (Polynomial.mem_nthRootsFinset hp.pos (1 : K)).mp hz
    simpa using h
  exact ⟨z, hzp, Polynomial.eq_of_monic_of_associated hmon (monic_X_sub_C z)
    (hirr.associated_of_dvd (irreducible_X_sub_C z) haz)⟩

omit [Finite K] in
private lemma cenUS2_mem_primaryFactors_of_multiplicity_pos {A : Module.End K (Fin N → K)}
    {b : K[X]} (hirr : Irreducible b) (hmon : b.Monic) (hpos : 0 < primaryMultiplicity A b) :
    b ∈ primaryFactors A := by
  by_contra hmem
  have : Fact (Irreducible b) := ⟨hirr⟩
  have hbot := CFSG.RankThree.Classical.primaryComponent_eq_bot_of_not_mem hirr hmon hmem
  have : Subsingleton ↥(primaryComponent A b) := by rw [hbot]; infer_instance
  have hzero : primaryMultiplicity A b = 0 := Module.finrank_zero_of_subsingleton
  omega

private lemma cenUS2_inv_mem_primaryFactors_iff (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = (2 ^ nf) ^ 2) (hdvd : p ∣ 2 ^ nf - 1) {x : GL (Fin N) K}
    (hx : x ∈ LargeEvenSUGroup (Fin N) K (2 ^ nf)) (hxp : x ^ p = 1) {mu : K}
    (hmu : mu ^ p = 1) :
    ((X - C mu⁻¹ : K[X]) ∈ primaryFactors (ggK1A_glEnd x) ↔
      (X - C mu : K[X]) ∈ primaryFactors (ggK1A_glEnd x)) := by
  have : CharP K 2 := cenUS2_charP hK
  have hsq : Squarefree (minpoly K (ggK1A_glEnd x)) :=
    squarefree_minpoly_ggK1A_glEnd (cenUS2_cast_p_ne_zero hp hp2 hK) hxp
  have hmain : ∀ nu : K, nu ^ p = 1 → (X - C nu : K[X]) ∈ primaryFactors (ggK1A_glEnd x) →
      (X - C nu⁻¹ : K[X]) ∈ primaryFactors (ggK1A_glEnd x) := by
    intro nu hnu hmem
    obtain ⟨ζ, hζ⟩ :=
      CFSG.RankThree.PartOne.exists_primitiveRoot_of_dvd_card_sub_one (k := K) hp
        (cenUS2_dvd_card_sub_one hK hdvd)
    have : NeZero p := ⟨hp.ne_zero⟩
    obtain ⟨j, hj, hζj⟩ := hζ.eq_pow_of_pow_eq_one hnu
    have hmat : (x : Matrix (Fin N) (Fin N) K) ^ p = 1 := by
      simpa using congrArg (fun u : GL (Fin N) K => (u : Matrix (Fin N) (Fin N) K)) hxp
    have hxpow : ggK1A_glEnd ((⟨x, hx⟩ : ↥(LargeEvenSUGroup (Fin N) K (2 ^ nf))) :
        GL (Fin N) K) ^ p = 1 := by
      rw [ggK1A_glEnd, ← CFSG.RankThree.PartOne.KCLinComm.toLinAlgEquiv'_eq_toLin',
        ← map_pow, hmat, map_one]
    have hsymm := ggK1A_uni_primaryMultiplicity_symm (p := p) (nf := nf) (N := N) hp hK hdvd
      (xhat := ⟨x, hx⟩) hxpow hsq hζ hj
    have hnu_inv : nu⁻¹ = ζ ^ ((p - j) % p) := by
      rw [← hζj]
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · simp
      · have hmod : (p - j) % p = p - j := Nat.mod_eq_of_lt (by omega)
        rw [hmod]
        refine inv_eq_of_mul_eq_one_right ?_
        rw [← pow_add, Nat.add_sub_cancel' (le_of_lt hj), hζ.pow_eq_one]
    have hmem' : (X - C (ζ ^ j) : K[X]) ∈ primaryFactors (ggK1A_glEnd x) := by
      rwa [hζj]
    have hpos : 0 < primaryMultiplicity (ggK1A_glEnd x) (X - C (ζ ^ ((p - j) % p))) := by
      rw [hsymm]
      exact CFSG.RankThree.PartOne.KCUnitaryModel.primaryMultiplicity_pos hsq ⟨_, hmem'⟩
    have hgoal : (X - C (ζ ^ ((p - j) % p)) : K[X]) ∈ primaryFactors (ggK1A_glEnd x) :=
      cenUS2_mem_primaryFactors_of_multiplicity_pos (irreducible_X_sub_C _) (monic_X_sub_C _) hpos
    exact hnu_inv ▸ hgoal
  constructor
  · intro h
    have h1 := hmain mu⁻¹ (by rw [inv_pow, hmu, inv_one]) (by simpa using h)
    rwa [inv_inv] at h1
  · exact hmain mu hmu

omit [Finite K] in
private lemma cenUS2_transpose_map_eq_pow_sub_one (hp : p.Prime)
    {M : Matrix (Fin N) (Fin N) K} (hmat : M ^ p = 1)
    (hxU : Matrix.transpose (M.map (fun z => z ^ 2 ^ nf)) * M = 1) :
    Matrix.transpose (M.map (fun z => z ^ 2 ^ nf)) = M ^ (p - 1) := by
  have hxp' : M * M ^ (p - 1) = 1 := by
    rw [← pow_succ', Nat.sub_one_add_one hp.ne_zero, hmat]
  calc Matrix.transpose (M.map (fun z => z ^ 2 ^ nf))
      = Matrix.transpose (M.map (fun z => z ^ 2 ^ nf)) * 1 := (mul_one _).symm
    _ = Matrix.transpose (M.map (fun z => z ^ 2 ^ nf)) * (M * M ^ (p - 1)) := by rw [hxp']
    _ = (Matrix.transpose (M.map (fun z => z ^ 2 ^ nf)) * M) * M ^ (p - 1) :=
      (mul_assoc _ _ _).symm
    _ = M ^ (p - 1) := by rw [hxU, one_mul]

private noncomputable def cenUS2_poly {P : Finset K[X]} (root : P → K) (r : P → Kˣ) : K[X] := by
  classical
  exact Lagrange.interpolate Finset.univ root fun a => (r a : K)

omit [Finite K] in
private lemma cenUS2_poly_eval {P : Finset K[X]} {root : P → K}
    (hroot : Function.Injective root) (r : P → Kˣ) (a : P) :
    (cenUS2_poly root r).eval (root a) = (r a : K) := by
  classical
  simpa [cenUS2_poly] using Lagrange.eval_interpolate_at_node (fun a => (r a : K))
    (fun x _ y _ h => hroot h) (Finset.mem_univ a)

omit [Finite K] in
private lemma cenUS2_dvd_minpoly_of_forall_eval_root {M : Matrix (Fin N) (Fin N) K}
    {P : Finset K[X]} {root : P → K} (hprod : P.prod id = minpoly K M)
    (hcop : ∀ a b : P, a ≠ b → IsCoprime (a : K[X]) (b : K[X]))
    (hlin : ∀ a : P, (a : K[X]) = X - C (root a)) {g : K[X]}
    (hg : ∀ a : P, g.eval (root a) = 0) : minpoly K M ∣ g := by
  have hdvd : P.prod id ∣ g := by
    refine Finset.prod_dvd_of_coprime (s := fun x : K[X] => x) (t := P) (z := g) ?_ ?_
    · exact fun a ha b hb hab => hcop ⟨a, ha⟩ ⟨b, hb⟩ (fun h => hab (congrArg Subtype.val h))
    · intro a ha
      have h1 : (a : K[X]) = X - C (root ⟨a, ha⟩) := hlin ⟨a, ha⟩
      rw [h1, dvd_iff_isRoot]
      exact hg ⟨a, ha⟩
  rwa [hprod] at hdvd

omit [Finite K] in
private lemma cenUS2_aeval_eq_zero_of_forall_eval_root {M : Matrix (Fin N) (Fin N) K}
    {P : Finset K[X]} {root : P → K} (hprod : P.prod id = minpoly K M)
    (hcop : ∀ a b : P, a ≠ b → IsCoprime (a : K[X]) (b : K[X]))
    (hlin : ∀ a : P, (a : K[X]) = X - C (root a)) {g : K[X]}
    (hg : ∀ a : P, g.eval (root a) = 0) : aeval M g = 0 :=
  aeval_eq_zero_of_dvd_aeval_eq_zero (cenUS2_dvd_minpoly_of_forall_eval_root hprod hcop hlin hg)
    (minpoly.aeval K M)

omit [Finite K] in
private lemma cenUS2_aeval_poly_mul {M : Matrix (Fin N) (Fin N) K} {P : Finset K[X]}
    {root : P → K} (hprod : P.prod id = minpoly K M)
    (hcop : ∀ a b : P, a ≠ b → IsCoprime (a : K[X]) (b : K[X]))
    (hlin : ∀ a : P, (a : K[X]) = X - C (root a)) (hroot : Function.Injective root)
    (r s : P → Kˣ) : aeval M (cenUS2_poly root (r * s)) =
      aeval M (cenUS2_poly root r) * aeval M (cenUS2_poly root s) := by
  have h0 : aeval M (cenUS2_poly root (r * s) - cenUS2_poly root r * cenUS2_poly root s) = 0 := by
    refine cenUS2_aeval_eq_zero_of_forall_eval_root hprod hcop hlin ?_
    intro a
    simp only [eval_sub, eval_mul, cenUS2_poly_eval hroot, Pi.mul_apply, Units.val_mul, sub_self]
  rwa [map_sub, map_mul, sub_eq_zero] at h0

omit [Finite K] in
private lemma cenUS2_aeval_poly_one {M : Matrix (Fin N) (Fin N) K} {P : Finset K[X]}
    {root : P → K} (hprod : P.prod id = minpoly K M)
    (hcop : ∀ a b : P, a ≠ b → IsCoprime (a : K[X]) (b : K[X]))
    (hlin : ∀ a : P, (a : K[X]) = X - C (root a)) (hroot : Function.Injective root) :
    aeval M (cenUS2_poly root 1) = 1 := by
  have h0 : aeval M (cenUS2_poly root (1 : P → Kˣ) - 1) = 0 := by
    refine cenUS2_aeval_eq_zero_of_forall_eval_root hprod hcop hlin ?_
    intro a
    simp only [eval_sub, eval_one, cenUS2_poly_eval hroot, Pi.one_apply, Units.val_one, sub_self]
  rwa [map_sub, map_one, sub_eq_zero] at h0

omit [Finite K] in
private lemma cenUS2_aeval_poly_injective {M : Matrix (Fin N) (Fin N) K} {P : Finset K[X]}
    {root : P → K} (hprod : P.prod id = minpoly K M)
    (hlin : ∀ a : P, (a : K[X]) = X - C (root a)) (hroot : Function.Injective root)
    {r s : P → Kˣ} (h : aeval M (cenUS2_poly root r) = aeval M (cenUS2_poly root s)) : r = s := by
  funext a
  have hg : aeval M (cenUS2_poly root r - cenUS2_poly root s) = 0 := by
    rw [map_sub, h, sub_self]
  have hdvd : minpoly K M ∣ cenUS2_poly root r - cenUS2_poly root s := minpoly.dvd K M hg
  have h1 : ((a : P) : K[X]) ∣ minpoly K M := by
    rw [← hprod]
    exact Finset.dvd_prod_of_mem (f := id) a.2
  have h2 : (X - C (root a) : K[X]) ∣ cenUS2_poly root r - cenUS2_poly root s := by
    rw [← hlin a]
    exact h1.trans hdvd
  have h3 := dvd_iff_isRoot.mp h2
  rw [Polynomial.IsRoot.def, eval_sub, cenUS2_poly_eval hroot r a,
    cenUS2_poly_eval hroot s a, sub_eq_zero] at h3
  exact Units.ext h3

omit [Finite K] in
private lemma cenUS2_aeval_poly_pow {M : Matrix (Fin N) (Fin N) K} {P : Finset K[X]}
    {root : P → K} (hprod : P.prod id = minpoly K M)
    (hcop : ∀ a b : P, a ≠ b → IsCoprime (a : K[X]) (b : K[X]))
    (hlin : ∀ a : P, (a : K[X]) = X - C (root a)) (hroot : Function.Injective root)
    {r : P → Kˣ} (hr : ∀ a, (r a : K) ^ p = 1) :
    aeval M (cenUS2_poly root r) ^ p = 1 := by
  have h1 : aeval M (cenUS2_poly root r ^ p - 1) = 0 := by
    refine cenUS2_aeval_eq_zero_of_forall_eval_root hprod hcop hlin ?_
    intro a
    simp only [eval_sub, eval_pow, eval_one, cenUS2_poly_eval hroot, hr a, sub_self]
  rw [← map_pow]
  rwa [map_sub, map_one, sub_eq_zero] at h1

omit [Finite K] in
private lemma cenUS2_transpose_map_aeval_poly
    (hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 nf K)
    (hp : p.Prime) {M : Matrix (Fin N) (Fin N) K} (hmat : M ^ p = 1)
    (hxU : Matrix.transpose (M.map (fun z => z ^ 2 ^ nf)) * M = 1)
    {P : Finset K[X]} {root : P → K} {r : P → Kˣ} :
    Matrix.transpose ((aeval M (cenUS2_poly root r)).map (fun z => z ^ 2 ^ nf)) =
      aeval M (((cenUS2_poly root r).map hU.bar).comp ((X : K[X]) ^ (p - 1))) := by
  have hσ_apply : ∀ c : K, hU.bar c = c ^ 2 ^ nf := fun c => hU.bar_apply c
  have hmapX : hU.bar.mapMatrix M = M.map (fun z => z ^ 2 ^ nf) := by
    ext i j
    simp [RingHom.mapMatrix_apply, hσ_apply]
  have hσXt : Matrix.transpose (hU.bar.mapMatrix M) = M ^ (p - 1) := by
    rw [hmapX]
    exact cenUS2_transpose_map_eq_pow_sub_one hp hmat hxU
  have hσf : hU.bar.mapMatrix (aeval M (cenUS2_poly root r)) =
      aeval (hU.bar.mapMatrix M) ((cenUS2_poly root r).map hU.bar) := by
    refine Polynomial.map_aeval_eq_aeval_map ?_ _ _
    apply RingHom.ext
    intro c
    rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.mapMatrix_apply]
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.algebraMap_eq_diagonal, Matrix.map_apply, hσ_apply]
    · simp [Matrix.algebraMap_eq_diagonal, Matrix.map_apply, hij]
  have htrans : Matrix.transpose (hU.bar.mapMatrix (aeval M (cenUS2_poly root r))) =
      aeval (M ^ (p - 1)) ((cenUS2_poly root r).map hU.bar) := by
    rw [hσf, cenUS2_transpose_aeval, hσXt]
  have hGaeval : aeval (M ^ (p - 1)) ((cenUS2_poly root r).map hU.bar) =
      aeval M (((cenUS2_poly root r).map hU.bar).comp ((X : K[X]) ^ (p - 1))) := by
    have hXp : aeval M ((X : K[X]) ^ (p - 1)) = M ^ (p - 1) := by simp
    rw [← hXp, ← Polynomial.aeval_comp]
  have hmapfin : hU.bar.mapMatrix (aeval M (cenUS2_poly root r)) =
      (aeval M (cenUS2_poly root r)).map (fun z => z ^ 2 ^ nf) := by
    ext i j
    simp [RingHom.mapMatrix_apply, hσ_apply]
  rw [← hmapfin, htrans, hGaeval]

omit [Finite K] in
private lemma cenUS2_aeval_poly_comp_mul_self (hp : p.Prime)
    (hdvd : p ∣ 2 ^ nf - 1)
    (hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 nf K)
    {M : Matrix (Fin N) (Fin N) K}
    {P : Finset K[X]} {root : P → K} {inv : P → P}
    (hprod : P.prod id = minpoly K M)
    (hcop : ∀ a b : P, a ≠ b → IsCoprime (a : K[X]) (b : K[X]))
    (hlin : ∀ a : P, (a : K[X]) = X - C (root a)) (hroot : Function.Injective root)
    (hroot_pow : ∀ a : P, (root a) ^ p = 1)
    (hinv_root : ∀ a : P, root (inv a) = (root a)⁻¹)
    {r : P → Kˣ} (hr : ∀ a, (r a : K) ^ p = 1) (hrinv : ∀ a, r (inv a) * r a = 1) :
    aeval M (((cenUS2_poly root r).map hU.bar).comp ((X : K[X]) ^ (p - 1)) *
      cenUS2_poly root r) = 1 := by
  have hσ_apply : ∀ c : K, hU.bar c = c ^ 2 ^ nf := fun c => hU.bar_apply c
  have hσinv : ∀ c : K, hU.bar (hU.bar c) = c := fun c => hU.bar_bar c
  have hσfix : ∀ a : P, hU.bar ((root a) ^ (p - 1)) = (root a) ^ (p - 1) := by
    intro a
    rw [hσ_apply, ← pow_mul, mul_comm (p - 1) (2 ^ nf), pow_mul,
      cenUS2_pow_q_eq_self hdvd (hroot_pow a)]
  have hinvpow : ∀ a : P, (root a) ^ (p - 1) = (root a)⁻¹ := by
    intro a
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← pow_succ', Nat.sub_one_add_one hp.ne_zero, hroot_pow a]
  have hσr : ∀ a : P, hU.bar ((r a : K)) = (r a : K) := by
    intro a
    rw [hσ_apply]
    exact cenUS2_pow_q_eq_self hdvd (hr a)
  have hdvdmin : minpoly K M ∣
      ((cenUS2_poly root r).map hU.bar).comp ((X : K[X]) ^ (p - 1)) *
        cenUS2_poly root r - 1 := by
    refine cenUS2_dvd_minpoly_of_forall_eval_root hprod hcop hlin ?_
    intro a
    have hval1 : ((cenUS2_poly root r).map hU.bar).eval ((root a) ^ (p - 1)) =
        (r (inv a) : K) := by
      rw [show (root a) ^ (p - 1) = hU.bar (hU.bar ((root a) ^ (p - 1))) from (hσinv _).symm,
        Polynomial.eval_map_apply, hσfix a, hinvpow a, ← hinv_root a, cenUS2_poly_eval hroot]
      exact hσr (inv a)
    have hval2 : (cenUS2_poly root r).eval (root a) = (r a : K) := cenUS2_poly_eval hroot r a
    have hrinv' : (r (inv a) : K) * (r a : K) = 1 := by
      rw [← Units.val_mul, hrinv a, Units.val_one]
    simp only [eval_sub, eval_mul, eval_comp, eval_pow, eval_X, eval_one, hval1, hval2,
      hrinv', sub_self]
  have h := aeval_eq_zero_of_dvd_aeval_eq_zero hdvdmin (minpoly.aeval K M)
  rwa [map_sub, map_one, sub_eq_zero] at h

private lemma cenUS2_map_pow_transpose_mul (hp : p.Prime)
    (hK : Nat.card K = (2 ^ nf) ^ 2) (hdvd : p ∣ 2 ^ nf - 1)
    {M : Matrix (Fin N) (Fin N) K} (hmat : M ^ p = 1)
    (hxU : Matrix.transpose (M.map (fun z => z ^ 2 ^ nf)) * M = 1)
    {P : Finset K[X]} {root : P → K} {inv : P → P}
    (hprod : P.prod id = minpoly K M)
    (hcop : ∀ a b : P, a ≠ b → IsCoprime (a : K[X]) (b : K[X]))
    (hlin : ∀ a : P, (a : K[X]) = X - C (root a)) (hroot : Function.Injective root)
    (hroot_pow : ∀ a : P, (root a) ^ p = 1)
    (hinv_root : ∀ a : P, root (inv a) = (root a)⁻¹)
    {r : P → Kˣ} (hr : ∀ a, (r a : K) ^ p = 1) (hrinv : ∀ a, r (inv a) * r a = 1) :
    Matrix.transpose ((aeval M (cenUS2_poly root r)).map (fun z => z ^ 2 ^ nf)) *
      aeval M (cenUS2_poly root r) = 1 := by
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 nf K := cenUS2_unitaryData hK
  rw [cenUS2_transpose_map_aeval_poly hU hp hmat hxU, ← map_mul]
  exact cenUS2_aeval_poly_comp_mul_self hp hdvd hU hprod hcop hlin hroot hroot_pow hinv_root hr
    hrinv

private lemma cenUS2_det_eq_one (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = (2 ^ nf) ^ 2) (hdvd : p ∣ 2 ^ nf - 1) {u : GL (Fin N) K}
    (hup : u ^ p = 1)
    (huU : Matrix.transpose ((u : Matrix (Fin N) (Fin N) K).map (· ^ 2 ^ nf)) *
      (u : Matrix (Fin N) (Fin N) K) = 1) :
    (u : Matrix (Fin N) (Fin N) K).det = 1 := by
  have : CharP K 2 := cenUS2_charP hK
  have hU := cenUS2_unitaryData hK
  have hcop : Nat.gcd p (2 ^ nf + 1) = 1 := cenUS2_coprime_add_one hp hp2 hK hdvd
  have hmapσ : hU.bar.mapMatrix (u : Matrix (Fin N) (Fin N) K) =
      (u : Matrix (Fin N) (Fin N) K).map (· ^ 2 ^ nf) := by
    ext i j
    simp [RingHom.mapMatrix_apply, hU.bar_apply]
  have hdet2 : ((u : Matrix (Fin N) (Fin N) K).map (· ^ 2 ^ nf)).det =
      ((u : Matrix (Fin N) (Fin N) K).det) ^ 2 ^ nf := by
    have h := RingHom.map_det hU.bar (u : Matrix (Fin N) (Fin N) K)
    rw [hmapσ, hU.bar_apply] at h
    exact h.symm
  have hdet1 : ((u : Matrix (Fin N) (Fin N) K).map (· ^ 2 ^ nf)).det *
      (u : Matrix (Fin N) (Fin N) K).det = 1 := by
    have h := congrArg Matrix.det huU
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  set d : Kˣ := Matrix.GeneralLinearGroup.det u with hd
  have hdval : ((d : K)) = (u : Matrix (Fin N) (Fin N) K).det := rfl
  have hdp : d ^ p = 1 := by
    rw [← map_pow, hup, map_one]
  have hdq : d ^ (2 ^ nf + 1) = 1 := by
    apply Units.ext
    have h2 : ((d : K)) ^ (2 ^ nf + 1) = 1 := by
      rw [pow_succ, hdval, ← hdet2]
      exact hdet1
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact h2
  have hord : orderOf d ∣ 1 := by
    have h := Nat.dvd_gcd (orderOf_dvd_iff_pow_eq_one.mpr hdp)
      (orderOf_dvd_iff_pow_eq_one.mpr hdq)
    rwa [hcop] at h
  have hd1 : d = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hord)
  rw [← hdval, hd1]
  rfl

omit [Finite K] in
private lemma cenUS2_aeval_eq_toLin {A : Module.End K (Fin N → K)}
    {M : Matrix (Fin N) (Fin N) K} (hMA : A = Matrix.toLinAlgEquiv' M) (g : K[X]) :
    aeval A g = Matrix.toLin' (aeval M g) := by
  subst hMA
  rw [Polynomial.aeval_algEquiv]
  exact CFSG.RankThree.PartOne.KCLinComm.toLinAlgEquiv'_eq_toLin' _

omit [Finite K] in
private lemma cenUS2_commute_aeval {A y : Module.End K (Fin N → K)} (h : Commute y A)
    (g : K[X]) : Commute y (aeval A g) := by
  induction g using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact hp.add_right hq
  | monomial n c =>
      rw [Polynomial.aeval_monomial]
      have hc : Commute y (algebraMap K (Module.End K (Fin N → K)) c) :=
        (Algebra.commutes c y).symm
      exact hc.mul_right (h.pow_right n)

omit [Finite K] in
private lemma cenUS2_inv_eq_iff (hp : p.Prime) (hchar : CharP K 2)
    {P : Finset K[X]} {root : P → K} {inv : P → P}
    (hlin : ∀ a : P, (a : K[X]) = X - C (root a))
    (hinv_root : ∀ a : P, root (inv a) = (root a)⁻¹) (hpow : ∀ a : P, (root a) ^ p = 1)
    (hroot : Function.Injective root) (a : P) : inv a = a ↔ (a : K[X]) = X - 1 := by
  have hneg : (-1 : K) = 1 := by
    have h2 : (1 : K) + 1 = 0 := by
      have h3 : ((2 : ℕ) : K) = 0 := (CharP.cast_eq_zero_iff K 2 2).mpr (dvd_refl 2)
      have h4 : ((2 : ℕ) : K) = (1 : K) + 1 := by norm_num
      rw [h4] at h3
      exact h3
    exact (eq_neg_of_add_eq_zero_left h2).symm
  constructor
  · intro h
    have h1 : (root a)⁻¹ = root a := by rw [← hinv_root, h]
    have hz : root a ≠ 0 := by
      intro h0
      have h3 := hpow a
      rw [h0, zero_pow hp.ne_zero] at h3
      exact zero_ne_one h3
    have h2 : root a * root a = 1 := by
      have h3 := mul_inv_cancel₀ hz
      rwa [h1] at h3
    have h3 : root a ^ 2 = 1 := by rw [pow_two]; exact h2
    have h4 : root a = 1 := by
      rcases sq_eq_one_iff.mp h3 with h5 | h5
      · exact h5
      · rw [h5, hneg]
    rw [hlin a, h4, map_one]
  · intro h
    have h1 : root a = 1 := by
      have h2 : (X - C (root a) : K[X]) = X - C (1 : K) := by rw [← hlin a, h, map_one]
      have h3 := congrArg (fun q : K[X] => q.coeff 0) h2
      simp only [coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, neg_inj] at h3
      exact h3
    apply hroot
    rw [hinv_root, h1, inv_one]

open scoped Classical in
omit [Finite K] in
private lemma cenUS2_card_moved (hp : p.Prime) (hchar : CharP K 2) {x : GL (Fin N) K}
    {P : Finset K[X]} {root : P → K} {inv : P → P}
    (hsd : ggK1A_selfDualFactors x = P.filter (fun a : K[X] => a ≠ X - 1))
    (hlin : ∀ a : P, (a : K[X]) = X - C (root a))
    (hinv_root : ∀ a : P, root (inv a) = (root a)⁻¹) (hpow : ∀ a : P, (root a) ^ p = 1)
    (hroot : Function.Injective root) :
    Nat.card {a : P // inv a ≠ a} = (ggK1A_selfDualFactors x).card := by
  classical
  rw [hsd]
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun a =>
    not_congr (cenUS2_inv_eq_iff hp hchar hlin hinv_root hpow hroot a))]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter, Finset.card_filter]
  rw [← Finset.sum_coe_sort (P) (fun a => if (a : K[X]) ≠ X - 1 then 1 else 0)]

private def cenUS2_rOf {Gp : Subgroup Kˣ} {P : Type*} {C : Subgroup (P → ↥Gp)}
    (c : ↥C) (a : P) : Kˣ :=
  ((c.1 a : ↥Gp) : Kˣ)

omit [Finite K] in
private lemma cenUS2_rOf_pow {P : Type*} {C : Subgroup (P → ↥(rootsOfUnity p K))}
    (c : ↥C) (a : P) : ((cenUS2_rOf c a : Kˣ) : K) ^ p = 1 := by
  have h2 : ((c.1 a : ↥(rootsOfUnity p K)) : Kˣ) ^ p = 1 := by
    have h3 := (c.1 a).2
    rwa [mem_rootsOfUnity] at h3
  rw [show cenUS2_rOf c a = ((c.1 a : ↥(rootsOfUnity p K)) : Kˣ) from rfl,
    ← Units.val_pow_eq_pow_val, h2, Units.val_one]

omit [Finite K] in
private lemma cenUS2_rOf_inv {Gp : Subgroup Kˣ} {P : Type*} {C : Subgroup (P → ↥Gp)}
    {inv : P → P} (hC : C = involutiveInvSubgroup ↥Gp inv) (c : ↥C) (a : P) :
    cenUS2_rOf c (inv a) * cenUS2_rOf c a = 1 := by
  have h : c.1 (inv a) * c.1 a = 1 :=
    mem_involutiveInvSubgroup.mp (hC ▸ c.2) a
  have h2 : (((c.1 (inv a) * c.1 a : ↥Gp)) : Kˣ) = 1 := by rw [h, Subgroup.coe_one]
  simpa [cenUS2_rOf] using h2

omit [Finite K] in
private lemma cenUS2_scalar_pow_add_one (hN : 0 < N) {u : Kˣ}
    (huU : Matrix.transpose ((Matrix.scalar (Fin N) (u : K)).map (fun z => z ^ 2 ^ nf)) *
      Matrix.scalar (Fin N) (u : K) = 1) : u ^ (2 ^ nf + 1) = 1 := by
  have hmap : (Matrix.scalar (Fin N) ((u : K))).map (fun z => z ^ 2 ^ nf) =
      Matrix.scalar (Fin N) ((u : K) ^ 2 ^ nf) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  have h00 : (u : K) ^ 2 ^ nf * (u : K) = 1 := by
    have h := huU
    rw [hmap, Matrix.scalar_apply, Matrix.scalar_apply, Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal] at h
    have h2 := congrFun (congrFun h ⟨0, hN⟩) ⟨0, hN⟩
    simpa using h2
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one, pow_succ]
  exact h00

private lemma cenUS2_scalar_eq_one (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = (2 ^ nf) ^ 2) (hdvd : p ∣ 2 ^ nf - 1) {u : Kˣ}
    (hup : u ^ p = 1) (huq1 : u ^ (2 ^ nf + 1) = 1) : u = 1 := by
  have hcop : Nat.gcd p (2 ^ nf + 1) = 1 := cenUS2_coprime_add_one hp hp2 hK hdvd
  have hord : orderOf u ∣ 1 := by
    have h := Nat.dvd_gcd (orderOf_dvd_iff_pow_eq_one.mpr hup)
      (orderOf_dvd_iff_pow_eq_one.mpr huq1)
    rwa [hcop] at h
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hord)

private lemma cenUS2_phi_scalar_eq_one (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = (2 ^ nf) ^ 2) (hdvd : p ∣ 2 ^ nf - 1) (hN : 0 < N)
    {P : Finset K[X]} {Φ : (P → Kˣ) →* GL (Fin N) K} {r : P → Kˣ}
    (hpow : (Φ r) ^ p = 1)
    (huni : Matrix.transpose (((Φ r : GL (Fin N) K) : Matrix (Fin N) (Fin N) K).map
      (· ^ 2 ^ nf)) * ((Φ r : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) = 1)
    (hscal : Φ r ∈ LargeEvenScalars (Fin N) K) : Φ r = 1 := by
  rw [largeEvenScalars_def] at hscal
  obtain ⟨u, hu⟩ := hscal
  have hscalar : ((Φ r : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) =
      Matrix.scalar (Fin N) ((u : K)) := by
    rw [← hu, Matrix.GeneralLinearGroup.coe_scalar]
  have hup : u ^ p = 1 := by
    have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
    apply CFSG.LinearAlgebra.generalLinearGroup_scalar_injective (ι := Fin N)
    rw [map_pow, map_one, hu]
    exact hpow
  have huU : Matrix.transpose ((Matrix.scalar (Fin N) (u : K)).map (fun z => z ^ 2 ^ nf)) *
      Matrix.scalar (Fin N) (u : K) = 1 := by
    rw [← hscalar]
    exact huni
  have hu1 : u = 1 := cenUS2_scalar_eq_one hp hp2 hK hdvd hup
    (cenUS2_scalar_pow_add_one hN huU)
  rw [← hu, hu1, map_one]

open scoped Classical in
private lemma cenUS2_range_inf_scalars_eq_bot_and_card (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = (2 ^ nf) ^ 2) (hdvd : p ∣ 2 ^ nf - 1) (hN : 0 < N)
    {x : GL (Fin N) K} {P : Finset K[X]} {inv : P → P}
    {C : Subgroup (P → ↥(rootsOfUnity p K))}
    (hC : C = involutiveInvSubgroup ↥(rootsOfUnity p K) inv)
    {Φ : (P → Kˣ) →* GL (Fin N) K} {Ψ : ↥C →* GL (Fin N) K}
    (hΨ : ∀ c : ↥C, Ψ c = Φ (cenUS2_rOf c))
    (hΦpow : ∀ r : P → Kˣ, (∀ a, (r a : K) ^ p = 1) → (Φ r) ^ p = 1)
    (huni : ∀ r : P → Kˣ, (∀ a, (r a : K) ^ p = 1) → (∀ a, r (inv a) * r a = 1) →
      Matrix.transpose (((Φ r : GL (Fin N) K) : Matrix (Fin N) (Fin N) K).map (· ^ 2 ^ nf)) *
        ((Φ r : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) = 1)
    (hCcard : Nat.card ↥C = p ^ ((ggK1A_selfDualFactors x).card / 2))
    (hinj : Function.Injective Ψ) :
    Ψ.range ⊓ LargeEvenScalars (Fin N) K = ⊥ ∧
      Nat.card ↥Ψ.range = p ^ ((ggK1A_selfDualFactors x).card / 2) := by
  constructor
  · rw [eq_bot_iff]
    rintro t ⟨htT, htS⟩
    rw [Subgroup.mem_bot]
    obtain ⟨c, hc⟩ := htT
    rw [← hc, hΨ c] at htS ⊢
    exact cenUS2_phi_scalar_eq_one hp hp2 hK hdvd hN (hΦpow _ (cenUS2_rOf_pow c))
      (huni _ (cenUS2_rOf_pow c) (cenUS2_rOf_inv hC c)) htS
  · have hcard : Nat.card ↥Ψ.range = Nat.card ↥C := by
      rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective (K := ⊤) hinj,
        Nat.card_congr Subgroup.topEquiv.toEquiv]
    rw [hcard, hCcard]

open scoped Classical in
private lemma cenUS2_subgroup_of_Phi (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = (2 ^ nf) ^ 2) (hdvd : p ∣ 2 ^ nf - 1) (hN : 0 < N)
    {x : GL (Fin N) K} {P : Finset K[X]} {root : P → K} {inv : P → P}
    (hsd : ggK1A_selfDualFactors x = P.filter (fun a : K[X] => a ≠ X - 1))
    (hlin : ∀ a : P, (a : K[X]) = X - C (root a))
    (hroot : Function.Injective root) (hroot_pow : ∀ a : P, (root a) ^ p = 1)
    (hinv_root : ∀ a : P, root (inv a) = (root a)⁻¹)
    {Φ : (P → Kˣ) →* GL (Fin N) K} (hΦinj : Function.Injective Φ)
    (hΦpow : ∀ r : P → Kˣ, (∀ a, (r a : K) ^ p = 1) → (Φ r) ^ p = 1)
    (hmemTors : ∀ r : P → Kˣ, (∀ a, (r a : K) ^ p = 1) → Φ r ∈ ggK1A_torsGL x p)
    (huni : ∀ r : P → Kˣ, (∀ a, (r a : K) ^ p = 1) → (∀ a, r (inv a) * r a = 1) →
      Matrix.transpose (((Φ r : GL (Fin N) K) : Matrix (Fin N) (Fin N) K).map (· ^ 2 ^ nf)) *
        ((Φ r : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) = 1)
    (hdet : ∀ r : P → Kˣ, (∀ a, (r a : K) ^ p = 1) → (∀ a, r (inv a) * r a = 1) →
      ((Φ r : GL (Fin N) K) : Matrix (Fin N) (Fin N) K).det = 1) :
    ∃ T : Subgroup (GL (Fin N) K), T ≤ LargeEvenSUGroup (Fin N) K (2 ^ nf) ∧
      T ≤ ggK1A_torsGL x p ∧ T ⊓ LargeEvenScalars (Fin N) K = ⊥ ∧
      Nat.card T = p ^ ((ggK1A_selfDualFactors x).card / 2) := by
  classical
  have hchar : CharP K 2 := cenUS2_charP hK
  have hinv_invol : Function.Involutive inv :=
    fun a => hroot (by rw [hinv_root, hinv_root, inv_inv])
  set Gp : Subgroup Kˣ := rootsOfUnity p K with hGp
  have hGp_card : Nat.card ↥Gp = p := by
    rw [hGp, CFSG.RankThree.PartOne.card_rootsOfUnity_finite_field hp.pos]
    exact Nat.gcd_eq_left (cenUS2_dvd_card_sub_one hK hdvd)
  have hGp_odd : Odd (Nat.card ↥Gp) := hGp_card ▸ hp.odd_of_ne_two hp2
  let C : Subgroup (P → ↥Gp) := involutiveInvSubgroup ↥Gp inv
  have hmoved : Nat.card {a : P // inv a ≠ a} = (ggK1A_selfDualFactors x).card :=
    cenUS2_card_moved hp hchar hsd hlin hinv_root hroot_pow hroot
  have hCcard : Nat.card ↥C = p ^ ((ggK1A_selfDualFactors x).card / 2) := by
    rw [card_involutiveInvSubgroup (G := ↥Gp) (σ := inv) hGp_odd hinv_invol, hGp_card, hmoved]
  let Ψ : ↥C →* GL (Fin N) K :=
    { toFun := fun c => Φ (cenUS2_rOf c)
      map_one' := by
        have h1 : cenUS2_rOf (1 : ↥C) = 1 := by funext a; simp [cenUS2_rOf]
        rw [h1, map_one]
      map_mul' := fun c d => by
        have h1 : cenUS2_rOf (c * d) = cenUS2_rOf c * cenUS2_rOf d := by
          funext a; simp [cenUS2_rOf, Subgroup.coe_mul, Pi.mul_apply]
        rw [h1, map_mul] }
  have hinj : Function.Injective Ψ := by
    intro c d hcd
    have h1 : cenUS2_rOf c = cenUS2_rOf d := hΦinj hcd
    refine Subtype.ext ?_
    funext a
    refine Subtype.ext ?_
    have h2 := congrFun h1 a
    simpa [cenUS2_rOf] using h2
  refine ⟨Ψ.range, ?_, ?_, ?_, ?_⟩
  · rintro t ⟨c, rfl⟩
    rw [CFSG.LocalAnalysis.GLTheoremA.FQ.mem_LargeEvenSU_iff]
    exact ⟨hdet (cenUS2_rOf c) (cenUS2_rOf_pow c) (cenUS2_rOf_inv rfl c),
      huni (cenUS2_rOf c) (cenUS2_rOf_pow c) (cenUS2_rOf_inv rfl c)⟩
  · rintro t ⟨c, rfl⟩
    exact hmemTors (cenUS2_rOf c) (cenUS2_rOf_pow c)
  · exact (cenUS2_range_inf_scalars_eq_bot_and_card hp hp2 hK hdvd hN (C := C) (inv := inv)
      (Φ := Φ) (Ψ := Ψ) rfl (fun c => rfl) hΦpow huni hCcard hinj).1
  · exact (cenUS2_range_inf_scalars_eq_bot_and_card hp hp2 hK hdvd hN (C := C) (inv := inv)
      (Φ := Φ) (Ψ := Ψ) rfl (fun c => rfl) hΦpow huni hCcard hinj).2

private lemma cenUS2_exists_linear_roots (hp : p.Prime)
    (hK : Nat.card K = (2 ^ nf) ^ 2) (hdvd : p ∣ 2 ^ nf - 1) {x : GL (Fin N) K}
    (hxp : x ^ p = 1) :
    ∃ root : primaryFactors (ggK1A_glEnd x) → K,
      Function.Injective root ∧ (∀ a, (root a) ^ p = 1) ∧
        (∀ a, ((a : primaryFactors (ggK1A_glEnd x)) : K[X]) = X - C (root a)) := by
  classical
  have : CharP K 2 := cenUS2_charP hK
  have hex : ∀ a : primaryFactors (ggK1A_glEnd x), ∃ mu : K, mu ^ p = 1 ∧
      (a : K[X]) = X - C mu :=
    fun a => cenUS2_primaryFactors_linear hp hK hdvd hxp a a.2
  choose root hroot_pow hlin using hex
  exact ⟨root, fun a b hab => Subtype.ext (by rw [hlin a, hlin b, hab]), hroot_pow, hlin⟩

private lemma cenUS2_exists_inv (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = (2 ^ nf) ^ 2) (hdvd : p ∣ 2 ^ nf - 1) {x : GL (Fin N) K}
    (hx : x ∈ LargeEvenSUGroup (Fin N) K (2 ^ nf)) (hxp : x ^ p = 1)
    {root : primaryFactors (ggK1A_glEnd x) → K}
    (hroot_pow : ∀ a, (root a) ^ p = 1)
    (hlin : ∀ a, ((a : primaryFactors (ggK1A_glEnd x)) : K[X]) = X - C (root a)) :
    ∃ inv : primaryFactors (ggK1A_glEnd x) → primaryFactors (ggK1A_glEnd x),
      ∀ a, root (inv a) = (root a)⁻¹ := by
  classical
  have hinv_mem : ∀ a : primaryFactors (ggK1A_glEnd x),
      (X - C (root a)⁻¹ : K[X]) ∈ primaryFactors (ggK1A_glEnd x) := by
    intro a
    exact (cenUS2_inv_mem_primaryFactors_iff hp hp2 hK hdvd hx hxp (hroot_pow a)).mpr
      (hlin a ▸ a.2)
  let inv : primaryFactors (ggK1A_glEnd x) → primaryFactors (ggK1A_glEnd x) :=
    fun a => ⟨X - C (root a)⁻¹, hinv_mem a⟩
  have hinv_root : ∀ a, root (inv a) = (root a)⁻¹ := by
    intro a
    have h1 : ((inv a : primaryFactors (ggK1A_glEnd x)) : K[X]) = X - C (root (inv a)) :=
      hlin (inv a)
    have h2 : ((inv a : primaryFactors (ggK1A_glEnd x)) : K[X]) = X - C (root a)⁻¹ := rfl
    have h3 : (X - C (root (inv a)) : K[X]) = X - C (root a)⁻¹ := by rw [← h1, h2]
    have h4 := congrArg (fun q : K[X] => q.coeff 0) h3
    simp only [coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, neg_inj] at h4
    exact h4
  exact ⟨inv, hinv_root⟩

omit [Finite K] in
private lemma cenUS2_mem_tors_of_aeval {x u : GL (Fin N) K} {f : K[X]}
    (hpow : u ^ p = 1) (hgl : ggK1A_glEnd u = aeval (ggK1A_glEnd x) f) :
    u ∈ ggK1A_torsGL x p := by
  rw [mem_ggK1A_torsGL_iff]
  exact ⟨hpow, fun y hy => by rw [hgl]; exact cenUS2_commute_aeval hy _⟩

private lemma cenUS2_phi_properties (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = (2 ^ nf) ^ 2) (hdvd : p ∣ 2 ^ nf - 1)
    {x : GL (Fin N) K} {M : Matrix (Fin N) (Fin N) K}
    (hMA : ggK1A_glEnd x = Matrix.toLinAlgEquiv' M) (hmat : M ^ p = 1)
    (hxU : Matrix.transpose (M.map (fun z => z ^ 2 ^ nf)) * M = 1)
    {P : Finset K[X]} {root : P → K} {inv : P → P}
    (hprod : P.prod id = minpoly K M)
    (hcop : ∀ a b : P, a ≠ b → IsCoprime (a : K[X]) (b : K[X]))
    (hlin : ∀ a : P, (a : K[X]) = X - C (root a)) (hroot : Function.Injective root)
    (hroot_pow : ∀ a : P, (root a) ^ p = 1)
    (hinv_root : ∀ a : P, root (inv a) = (root a)⁻¹)
    {Φ : (P → Kˣ) →* GL (Fin N) K}
    (hΦ : ∀ r : P → Kˣ, ((Φ r : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) =
      aeval M (cenUS2_poly root r)) :
    Function.Injective Φ ∧
      (∀ r : P → Kˣ, (∀ a, (r a : K) ^ p = 1) → (Φ r) ^ p = 1) ∧
      (∀ r : P → Kˣ, (∀ a, (r a : K) ^ p = 1) → Φ r ∈ ggK1A_torsGL x p) ∧
      (∀ r : P → Kˣ, (∀ a, (r a : K) ^ p = 1) → (∀ a, r (inv a) * r a = 1) →
        Matrix.transpose (((Φ r : GL (Fin N) K) : Matrix (Fin N) (Fin N) K).map (· ^ 2 ^ nf)) *
          ((Φ r : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) = 1) ∧
      (∀ r : P → Kˣ, (∀ a, (r a : K) ^ p = 1) → (∀ a, r (inv a) * r a = 1) →
        ((Φ r : GL (Fin N) K) : Matrix (Fin N) (Fin N) K).det = 1) := by
  have hΦinj : Function.Injective Φ := fun r s hrs => cenUS2_aeval_poly_injective hprod hlin hroot
    (by simpa [hΦ r, hΦ s] using
      congrArg (fun u : GL (Fin N) K => (u : Matrix (Fin N) (Fin N) K)) hrs)
  have hΦpow : ∀ r : P → Kˣ, (∀ a, (r a : K) ^ p = 1) → (Φ r) ^ p = 1 := by
    intro r hr
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, Units.val_one, hΦ r]
    exact cenUS2_aeval_poly_pow hprod hcop hlin hroot hr
  have hmemTors : ∀ r : P → Kˣ, (∀ a, (r a : K) ^ p = 1) → Φ r ∈ ggK1A_torsGL x p := by
    intro r hr
    refine cenUS2_mem_tors_of_aeval (f := cenUS2_poly root r) (hΦpow r hr) ?_
    rw [cenUS2_aeval_eq_toLin hMA, ggK1A_glEnd, hΦ r]
  have huni : ∀ r : P → Kˣ, (∀ a, (r a : K) ^ p = 1) → (∀ a, r (inv a) * r a = 1) →
      Matrix.transpose (((Φ r : GL (Fin N) K) : Matrix (Fin N) (Fin N) K).map (· ^ 2 ^ nf)) *
        ((Φ r : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) = 1 := by
    intro r hr hrinv
    rw [hΦ r]
    exact cenUS2_map_pow_transpose_mul hp hK hdvd hmat hxU hprod hcop hlin hroot hroot_pow
      hinv_root hr hrinv
  have hdet : ∀ r : P → Kˣ, (∀ a, (r a : K) ^ p = 1) → (∀ a, r (inv a) * r a = 1) →
      ((Φ r : GL (Fin N) K) : Matrix (Fin N) (Fin N) K).det = 1 :=
    fun r hr hrinv => cenUS2_det_eq_one hp hp2 hK hdvd (hΦpow r hr) (huni r hr hrinv)
  exact ⟨hΦinj, hΦpow, hmemTors, huni, hdet⟩

private lemma cenUS2_construction (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = (2 ^ nf) ^ 2) (hdvd : p ∣ 2 ^ nf - 1) (hN : 0 < N)
    {x : GL (Fin N) K} (hx : x ∈ LargeEvenSUGroup (Fin N) K (2 ^ nf)) (hxp : x ^ p = 1) :
    ∃ T : Subgroup (GL (Fin N) K), T ≤ LargeEvenSUGroup (Fin N) K (2 ^ nf) ∧
      T ≤ ggK1A_torsGL x p ∧ T ⊓ LargeEvenScalars (Fin N) K = ⊥ ∧
      Nat.card T = p ^ ((ggK1A_selfDualFactors x).card / 2) := by
  classical
  have hchar : CharP K 2 := cenUS2_charP hK
  let A : Module.End K (Fin N → K) := ggK1A_glEnd x
  let M : Matrix (Fin N) (Fin N) K := (x : Matrix (Fin N) (Fin N) K)
  have hMA : A = Matrix.toLinAlgEquiv' M := by
    change ggK1A_glEnd x = Matrix.toLinAlgEquiv' M
    rw [ggK1A_glEnd, CFSG.RankThree.PartOne.KCLinComm.toLinAlgEquiv'_eq_toLin']
  have hmat : M ^ p = 1 := by
    simpa using congrArg (fun u : GL (Fin N) K => (u : Matrix (Fin N) (Fin N) K)) hxp
  have hxU' : Matrix.transpose (M.map (fun z => z ^ 2 ^ nf)) * M = 1 :=
    ((CFSG.LocalAnalysis.GLTheoremA.FQ.mem_LargeEvenSU_iff (g := nf) x).mp hx).2
  have hsq : Squarefree (minpoly K A) :=
    squarefree_minpoly_ggK1A_glEnd (cenUS2_cast_p_ne_zero hp hp2 hK) hxp
  have hmin : minpoly K M = minpoly K A := by
    rw [hMA]
    exact (minpoly.algEquiv_eq Matrix.toLinAlgEquiv' M).symm
  have hprod : (primaryFactors A).prod id = minpoly K M := by
    simpa using (prod_primaryFactors hsq).trans hmin.symm
  have hcop : ∀ a b : primaryFactors A, a ≠ b → IsCoprime (a : K[X]) (b : K[X]) :=
    fun a b hab => isCoprime_of_mem_primaryFactors a.2 b.2 (fun h => hab (Subtype.ext h))
  obtain ⟨root, hroot, hroot_pow, hlin⟩ := cenUS2_exists_linear_roots hp hK hdvd hxp
  obtain ⟨inv, hinv_root⟩ := cenUS2_exists_inv hp hp2 hK hdvd hx hxp hroot_pow hlin
  let Φ : (primaryFactors A → Kˣ) →* GL (Fin N) K :=
    { toFun := fun r =>
        ⟨aeval M (cenUS2_poly root r), aeval M (cenUS2_poly root r⁻¹),
          by rw [← cenUS2_aeval_poly_mul hprod hcop hlin hroot r r⁻¹, mul_inv_cancel,
            cenUS2_aeval_poly_one hprod hcop hlin hroot],
          by rw [← cenUS2_aeval_poly_mul hprod hcop hlin hroot r⁻¹ r, inv_mul_cancel,
            cenUS2_aeval_poly_one hprod hcop hlin hroot]⟩
      map_one' := Units.ext (cenUS2_aeval_poly_one hprod hcop hlin hroot)
      map_mul' := fun r s => Units.ext (cenUS2_aeval_poly_mul hprod hcop hlin hroot r s) }
  have hΦ : ∀ r : primaryFactors A → Kˣ,
      ((Φ r : GL (Fin N) K) : Matrix (Fin N) (Fin N) K) = aeval M (cenUS2_poly root r) :=
    fun r => rfl
  obtain ⟨hΦinj, hΦpow, hmemTors, huni, hdet⟩ :=
    cenUS2_phi_properties hp hp2 hK hdvd hMA hmat hxU' hprod hcop hlin hroot hroot_pow hinv_root hΦ
  exact cenUS2_subgroup_of_Phi hp hp2 hK hdvd hN rfl hlin hroot hroot_pow hinv_root hΦinj hΦpow
    hmemTors huni hdet

end Helpers

theorem ggK1A_exists_torsion_su_of_dvd_sub_one {p nf N : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (2 ^ nf) ^ 2) (hdvd : p ∣ 2 ^ nf - 1)
    {x : GL (Fin N) K} (hx : x ∈ LargeEvenSUGroup (Fin N) K (2 ^ nf)) (hxp : x ^ p = 1) :
    ∃ T : Subgroup (GL (Fin N) K), T ≤ LargeEvenSUGroup (Fin N) K (2 ^ nf) ∧
      T ≤ ggK1A_torsGL x p ∧ T ⊓ LargeEvenScalars (Fin N) K = ⊥ ∧
      Nat.card T = p ^ ((ggK1A_selfDualFactors x).card / 2) := by
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
    have : Subsingleton (Fin 0 → K) := inferInstance
    have hP : primaryFactors (ggK1A_glEnd x) = ∅ := by
      rw [CFSG.RankThree.PartOne.KCPrimary.primaryFactors,
        minpoly.subsingleton K (ggK1A_glEnd x)]
      simp
    have hsd : ggK1A_selfDualFactors x = ∅ := by
      rw [ggK1A_selfDualFactors, hP]
      simp
    refine ⟨⊥, bot_le, bot_le, by simp, ?_⟩
    rw [hsd]
    simp
  · exact cenUS2_construction hp hp2 hK hdvd hNpos hx hxp

end CFSG.StandardType

end
