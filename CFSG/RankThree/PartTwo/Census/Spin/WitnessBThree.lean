module

public import CFSG.RankThree.PartTwo.Census.Spin.WitnessBShort
public import CFSG.RankThree.PartTwo.Census.Spin.WitnessBTheta
public import CFSG.RankThree.PartTwo.Census.Spin.WitnessTDFive

public section

namespace CFSG.RankThree.PartTwo.Census.Spin

open TauCeti
open scoped commutatorElement

namespace Cliff

open TauCeti CliffordAlgebra

variable {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {P : SpinPolarizationData Q} {ι : Type*}
  {b : Module.Basis ι K P.W} {i k : ι} (hik : i ≠ k)
include hik

theorem chainWeyl_mul_cr_self : chainWeyl b i k * cr b i = -cr b k * chainWeyl b i k := by
  show (1 + cr b i * an b k) * (1 - cr b k * an b i) * (1 + cr b i * an b k) * cr b i =
    -cr b k * ((1 + cr b i * an b k) * (1 - cr b k * an b i) * (1 + cr b i * an b k))
  set E := cr b i * an b k with hEd
  set F := cr b k * an b i with hFd
  have hE : E * E = 0 := chain_E_sq hik
  have hF : F * F = 0 := chain_F_sq hik
  have hik' : an b k * cr b i = -(cr b i * an b k) := an_cr b hik
  have e1 : E * cr b k - cr b k * E = cr b i := by
    calc E * cr b k - cr b k * E
        = cr b i * (an b k * cr b k) - cr b k * cr b i * an b k := by
          rw [hEd]; noncomm_ring
      _ = cr b i * (an b k * cr b k + cr b k * an b k) := by
          rw [cr_cr b k i]; noncomm_ring
      _ = cr b i := by rw [an_cr_self, mul_one]
  have e2 : E * cr b k * E = 0 := by
    have hc := commute_mul_of_anticomm₂ (cr_an b hik) (cr_cr b i k)
    calc E * cr b k * E = cr b i * (an b k * cr b k) * cr b i * an b k := by
          rw [hEd]; noncomm_ring
      _ = an b k * cr b k * (cr b i * cr b i) * an b k := by rw [hc]; noncomm_ring
      _ = 0 := by rw [cr_sq]; noncomm_ring
  have e4 : F * cr b i - cr b i * F = cr b k := by
    calc F * cr b i - cr b i * F
        = cr b k * (an b i * cr b i) - cr b i * cr b k * an b i := by
          rw [hFd]; noncomm_ring
      _ = cr b k * (an b i * cr b i + cr b i * an b i) := by
          rw [cr_cr b i k]; noncomm_ring
      _ = cr b k := by rw [an_cr_self, mul_one]
  have e5 : F * cr b i * F = 0 := by
    have hc := commute_mul_of_anticomm₂ (cr_an b hik.symm) (cr_cr b k i)
    calc F * cr b i * F = cr b k * (an b i * cr b i) * cr b k * an b i := by
          rw [hFd]; noncomm_ring
      _ = an b i * cr b i * (cr b k * cr b k) * an b i := by rw [hc]; noncomm_ring
      _ = 0 := by rw [cr_sq]; noncomm_ring
  have e6 : E * cr b i = 0 := by
    calc E * cr b i = cr b i * (an b k * cr b i) := by rw [hEd]; noncomm_ring
      _ = 0 := by rw [hik', mul_neg, ← mul_assoc, cr_sq, zero_mul, neg_zero]
  have e9 : cr b i * E = 0 := by rw [hEd, ← mul_assoc, cr_sq, zero_mul]
  have s1 : (1 + E) * cr b i = cr b i * (1 + E) := by
    rw [one_add_mul_eq hE, e6, e9, zero_mul, sub_zero, sub_zero, add_zero]
  have s2 : (1 - F) * cr b i = (cr b i - cr b k) * (1 - F) := by
    rw [one_sub_mul_eq hF, e4, e5, sub_zero]
  have s3 : (1 + E) * (cr b i - cr b k) = -cr b k * (1 + E) := by
    rw [one_add_mul_eq hE]
    have hEY : E * (cr b i - cr b k) - (cr b i - cr b k) * E = -cr b i := by
      rw [mul_sub, sub_mul, e6, e9, ← e1]
      noncomm_ring
    have hEYE : E * (cr b i - cr b k) * E = 0 := by
      rw [mul_sub, sub_mul, e6, zero_mul, e2, sub_zero]
    rw [hEY, hEYE, sub_zero]
    noncomm_ring
  calc (1 + E) * (1 - F) * (1 + E) * cr b i = (1 + E) * (1 - F) * ((1 + E) * cr b i) := by
        rw [mul_assoc]
    _ = (1 + E) * ((1 - F) * cr b i) * (1 + E) := by rw [s1]; noncomm_ring
    _ = (1 + E) * (cr b i - cr b k) * (1 - F) * (1 + E) := by rw [s2]; noncomm_ring
    _ = -cr b k * ((1 + E) * (1 - F) * (1 + E)) := by rw [s3]; noncomm_ring

theorem chainWeyl_mul_an_self : chainWeyl b i k * an b i = -an b k * chainWeyl b i k := by
  show (1 + cr b i * an b k) * (1 - cr b k * an b i) * (1 + cr b i * an b k) * an b i =
    -an b k * ((1 + cr b i * an b k) * (1 - cr b k * an b i) * (1 + cr b i * an b k))
  set E := cr b i * an b k with hEd
  set F := cr b k * an b i with hFd
  have hE : E * E = 0 := chain_E_sq hik
  have hF : F * F = 0 := chain_F_sq hik
  have g1 : E * an b k = 0 := by rw [hEd, mul_assoc, an_sq, mul_zero]
  have g2 : an b k * E = 0 := by
    calc an b k * E = an b k * cr b i * an b k := by rw [hEd]; noncomm_ring
      _ = 0 := by
          rw [an_cr b hik, neg_mul, mul_assoc, an_sq, mul_zero, neg_zero]
  have g3 : F * an b k - an b k * F = -an b i := by
    calc F * an b k - an b k * F
        = cr b k * (an b i * an b k) - an b k * cr b k * an b i := by
          rw [hFd]; noncomm_ring
      _ = -((cr b k * an b k + an b k * cr b k) * an b i) := by
          rw [an_an b i k]; noncomm_ring
      _ = -an b i := by rw [cr_an_self, one_mul]
  have g4 : F * an b k * F = 0 := by
    have hc := commute_mul_of_anticomm₂ (an_an b i k) (an_cr b hik.symm)
    calc F * an b k * F = cr b k * (an b i * (an b k * cr b k)) * an b i := by
          rw [hFd]; noncomm_ring
      _ = cr b k * (an b k * cr b k) * (an b i * an b i) := by rw [hc]; noncomm_ring
      _ = 0 := by rw [an_sq]; noncomm_ring
  have g5 : E * an b i - an b i * E = -an b k := by
    calc E * an b i - an b i * E
        = cr b i * (an b k * an b i) - an b i * cr b i * an b k := by
          rw [hEd]; noncomm_ring
      _ = -((cr b i * an b i + an b i * cr b i) * an b k) := by
          rw [an_an b k i]; noncomm_ring
      _ = -an b k := by rw [cr_an_self, one_mul]
  have g6 : E * an b i * E = 0 := by
    have hc := commute_mul_of_anticomm₂ (an_an b k i) (an_cr b hik)
    calc E * an b i * E = cr b i * (an b k * (an b i * cr b i)) * an b k := by
          rw [hEd]; noncomm_ring
      _ = cr b i * (an b i * cr b i) * (an b k * an b k) := by rw [hc]; noncomm_ring
      _ = 0 := by rw [an_sq]; noncomm_ring
  have f1 : F * an b i = 0 := by rw [hFd, mul_assoc, an_sq, mul_zero]
  have f2 : an b i * F = 0 := by
    calc an b i * F = an b i * cr b k * an b i := by rw [hFd]; noncomm_ring
      _ = 0 := by
          rw [an_cr b hik.symm, neg_mul, mul_assoc, an_sq, mul_zero, neg_zero]
  have s1 : (1 + E) * an b i = (an b i - an b k) * (1 + E) := by
    rw [one_add_mul_eq hE, g5, g6, sub_zero, ← sub_eq_add_neg]
  have s2 : (1 - F) * (an b i - an b k) = -an b k * (1 - F) := by
    rw [one_sub_mul_eq hF]
    have hFY : F * (an b i - an b k) - (an b i - an b k) * F = an b i := by
      calc F * (an b i - an b k) - (an b i - an b k) * F
          = F * an b i - an b i * F - (F * an b k - an b k * F) := by noncomm_ring
        _ = an b i := by rw [f1, f2, g3, sub_self, zero_sub, neg_neg]
    have hFYF : F * (an b i - an b k) * F = 0 := by
      rw [mul_sub, sub_mul, f1, zero_mul, g4, sub_zero]
    rw [hFY, hFYF, sub_zero]
    noncomm_ring
  have s3 : (1 + E) * an b k = an b k * (1 + E) := by
    rw [one_add_mul_eq hE, g1, g2, sub_zero, zero_mul, sub_zero, add_zero]
  calc (1 + E) * (1 - F) * (1 + E) * an b i = (1 + E) * (1 - F) * ((1 + E) * an b i) := by
        rw [mul_assoc]
    _ = (1 + E) * ((1 - F) * (an b i - an b k)) * (1 + E) := by rw [s1]; noncomm_ring
    _ = -((1 + E) * an b k) * (1 - F) * (1 + E) := by rw [s2]; noncomm_ring
    _ = -an b k * ((1 + E) * (1 - F) * (1 + E)) := by rw [s3]; noncomm_ring

end Cliff

section Ring

variable {A : Type*} [Ring A]

theorem weyl_anticomm_of {S T z : A} (hSS : S * S = 0) (hST : S * T + T * S = 1)
    (hSz : S * z = -(z * S)) (hTz : T * z = -(z * T)) :
    (1 + S) * (1 - T) * (1 + S) * z = -(z * ((1 + S) * (1 - T) * (1 + S))) := by
  have h1 : (1 + S) * z = z * (1 - S) := by
    rw [add_mul, one_mul, hSz, mul_sub, mul_one, sub_eq_add_neg]
  have h2 : (1 - T) * z = z * (1 + T) := by
    rw [sub_mul, one_mul, hTz, mul_add, mul_one, sub_neg_eq_add]
  have hW : (1 - S) * (1 + T) * (1 - S) = -((1 + S) * (1 - T) * (1 + S)) := by
    have e : (1 - S) * (1 + T) * (1 - S) + (1 + S) * (1 - T) * (1 + S) =
        2 * (1 - (S * T + T * S)) + 2 * (S * S) := by noncomm_ring
    rw [hST, hSS, sub_self, mul_zero, add_zero] at e
    exact eq_neg_of_add_eq_zero_left e
  calc (1 + S) * (1 - T) * (1 + S) * z = (1 + S) * (1 - T) * ((1 + S) * z) := by
        rw [mul_assoc]
    _ = (1 + S) * ((1 - T) * z) * (1 - S) := by rw [h1]; noncomm_ring
    _ = (1 + S) * z * ((1 + T) * (1 - S)) := by rw [h2]; noncomm_ring
    _ = z * ((1 - S) * (1 + T) * (1 - S)) := by rw [h1]; noncomm_ring
    _ = -(z * ((1 + S) * (1 - T) * (1 + S))) := by rw [hW, mul_neg]

end Ring

section Weights

variable {K : Type*} [Field K] {B : Type*} [Ring B] [Algebra K B]

theorem smul_eq_zero_of_weights (h2 : (2 : K) ≠ 0) {A X X' W : B} {c c' : K}
    (hX : A * X - X * A = X) (hX' : A * X' - X' * A = -X') (hW : A * W - W * A = 0)
    (h : c • X + c' • X' + W = 0) : c • X = 0 ∧ c' • X' = 0 := by
  have ad : ∀ (Y Y' Y'' : B) (d d' : K), A * (d • Y + d' • Y' + Y'') - (d • Y + d' • Y' + Y'') * A =
      d • (A * Y - Y * A) + d' • (A * Y' - Y' * A) + (A * Y'' - Y'' * A) := fun Y Y' Y'' d d' => by
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, smul_sub]
    abel
  have e1 : c • X + -(c' • X') = 0 := by
    have e := ad X X' W c c'
    rw [h, mul_zero, zero_mul, sub_zero, hX, hX', hW, add_zero, smul_neg] at e
    exact e.symm
  have e2 : c • X + c' • X' = 0 := by
    have key : A * (c • X + -(c' • X')) - (c • X + -(c' • X')) * A = c • X + c' • X' := by
      have e := ad X X' 0 c (-c')
      simp only [add_zero, mul_zero, zero_mul, sub_zero, neg_smul] at e
      rw [e, hX, hX', smul_neg, neg_neg]
    rw [e1, mul_zero, zero_mul, sub_zero] at key
    exact key.symm
  have h3 : (2 : K) • (c • X) = 0 := by
    rw [two_smul]
    calc c • X + c • X = (c • X + -(c' • X')) + (c • X + c' • X') := by abel
      _ = 0 := by rw [e1, e2, add_zero]
  have hcX : c • X = 0 := (smul_eq_zero.mp h3).resolve_left h2
  refine ⟨hcX, ?_⟩
  rw [hcX, zero_add] at e2
  exact e2

end Weights

namespace RootData

variable {K : Type*} [Field K] {N : Type*} [Fintype N] [DecidableEq N]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {R : RootData K N ι}

theorem witness_of_number {H : Subgroup R.G} {L : Subfield K} {p f m : ℕ} [CharP K p]
    (hcard : Nat.card L = p ^ f) {X : Fin m → Matrix N N K} (hXX : ∀ a b, X a * X b = 0)
    (hind : ∀ c : Fin m → K, ∑ a, c a • X a = 0 → ∀ a, c a = 0)
    (g : Fin m → K → R.G) (hg : ∀ a u, R.mat (g a u) = 1 + u • X a)
    (hgD : ∀ a, ∀ u ∈ L, g a u ∈ ⁅H, H⁆) {Z Y : Matrix N N K} {gZ gY : R.G}
    (hgZ : R.mat gZ = 1 + Z) (hgY : R.mat gY = 1 + Y) (hZD : gZ ∈ ⁅H, H⁆) (hYD : gY ∈ ⁅H, H⁆)
    (hK : ∀ a, Z * Y * X a - X a * (Z * Y) = X a) (t : R.G) (htD : t ∈ ⁅H, H⁆)
    (ht4 : t ^ 4 = 1) (htz : ∃ y ∈ ⁅H, H⁆, t * y ≠ y * t) (ht : ∀ a u, Commute t (g a u)) :
    HasWitness (DerivedCentralQuotient H) p (f * m) := by
  have e2 : ∀ A B : Matrix N N K, A * B = 0 → (1 + A) * (1 + B) = 1 + A + B := fun A B h => by
    rw [show (1 + A) * (1 + B) = 1 + A + B + A * B by noncomm_ring, h, add_zero]
  have hsm : ∀ a b (u v : K), (u • X a) * (v • X b) = 0 := fun a b u v => by
    rw [smul_mul_smul_comm, hXX, smul_zero]
  have hgadd : ∀ a u v, g a (u + v) = g a u * g a v := fun a u v => R.mat_injective (by
    rw [mat_mul, hg, hg, hg, e2 _ _ (hsm a a u v), add_smul, add_assoc])
  have hg0 : ∀ a, g a 0 = 1 := fun a => R.mat_injective (by rw [hg, zero_smul, add_zero, mat_one])
  let ϕ : ∀ _ : Fin m, Multiplicative L →* R.G := fun a =>
    { toFun := fun u => g a ((Multiplicative.toAdd u : L) : K)
      map_one' := by
        show g a ((Multiplicative.toAdd (1 : Multiplicative L) : L) : K) = 1
        rw [toAdd_one, ZeroMemClass.coe_zero, hg0]
      map_mul' := fun u v => by
        show g a ((Multiplicative.toAdd (u * v) : L) : K) = _
        rw [toAdd_mul, AddMemClass.coe_add, hgadd] }
  have hcommg : ∀ a b u v, Commute (g a u) (g b v) := fun a b u v => R.commute_of_mat (by
    show R.mat (g a u) * R.mat (g b v) = R.mat (g b v) * R.mat (g a u)
    rw [hg, hg, e2 _ _ (hsm a b u v), e2 _ _ (hsm b a v u)]
    abel)
  have hcomm : Pairwise fun a b => ∀ u v, Commute (ϕ a u) (ϕ b v) := fun a b _ u v =>
    hcommg a b _ _
  set θ := MonoidHom.noncommPiCoprod ϕ hcomm with hθ
  let Mx : (Fin m → Multiplicative L) → Matrix N N K := fun e =>
    ∑ a, ((Multiplicative.toAdd (e a) : L) : K) • X a
  have hMM : ∀ e e', Mx e * Mx e' = 0 := fun e e' => by
    simp only [Mx, Finset.sum_mul, Finset.mul_sum, hsm, Finset.sum_const_zero]
  have hMmul : ∀ e e', Mx (e * e') = Mx e + Mx e' := fun e e' => by
    simp only [Mx, Pi.mul_apply, toAdd_mul, AddMemClass.coe_add, add_smul,
      Finset.sum_add_distrib]
  have hMsingle : ∀ a (u : Multiplicative L),
      Mx (Pi.mulSingle a u) = ((Multiplicative.toAdd u : L) : K) • X a := fun a u => by
    simp only [Mx]
    rw [Finset.sum_eq_single a]
    · rw [Pi.mulSingle_eq_same]
    · intro b _ hb
      rw [Pi.mulSingle_eq_of_ne hb, toAdd_one, ZeroMemClass.coe_zero, zero_smul]
    · intro h
      exact absurd (Finset.mem_univ a) h
  have hmat : ∀ e, R.mat (θ e) = 1 + Mx e := by
    intro e
    have key := Finset.prod_induction (s := Finset.univ) (fun a => Pi.mulSingle a (e a))
      (fun w => R.mat (θ w) = 1 + Mx w)
      (fun w w' hw hw' => by
        rw [map_mul, mat_mul, hw, hw', e2 _ _ (hMM w w'), hMmul, add_assoc])
      (by
        rw [map_one, mat_one]
        simp [Mx])
      (fun a _ => by
        rw [hθ, MonoidHom.noncommPiCoprod_mulSingle, hMsingle]
        exact hg a _)
    rwa [Finset.univ_prod_mulSingle] at key
  have hzero : ∀ e, Mx e = 0 → e = 1 := fun e he => by
    funext a
    have h := hind (fun a => ((Multiplicative.toAdd (e a) : L) : K)) he a
    have h' : Multiplicative.toAdd (e a) = 0 := Subtype.ext (h.trans (ZeroMemClass.coe_zero L).symm)
    exact Multiplicative.toAdd.injective (h'.trans toAdd_one.symm)
  have hbr : ∀ e, Z * Y * Mx e - Mx e * (Z * Y) = Mx e := fun e => by
    simp only [Mx, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← smul_sub, hK]
  have hθinj : Function.Injective θ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro e he
    rw [MonoidHom.mem_ker] at he
    have h1 := hmat e
    rw [he, mat_one] at h1
    exact (Subgroup.mem_bot).mpr (hzero e (by
      have h2 := congrArg (fun A => A - 1) h1
      simpa using h2.symm))
  have hp : ∀ u : L, p • u = 0 := fun u => Subtype.ext (by
    rw [AddSubmonoidClass.coe_nsmul, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul,
      ZeroMemClass.coe_zero])
  refine exists_quotient_witness (E := θ.range) (P := Subgroup.zpowers t) ⟨⟨fun a b => ?_⟩⟩ ?_ ?_
    ?_ ((Subgroup.zpowers_le).mpr htD) ?_ ?_ ⟨t, Subgroup.mem_zpowers t, htz⟩ ?_
  · obtain ⟨a', ha⟩ := a.2
    obtain ⟨b', hb⟩ := b.2
    apply Subtype.ext
    change (a : R.G) * (b : R.G) = b * a
    rw [← ha, ← hb, ← map_mul, ← map_mul, mul_comm]
  · rintro _ ⟨e, rfl⟩
    rw [← map_pow]
    have : e ^ p = 1 := by
      funext a
      change Multiplicative.ofAdd (p • Multiplicative.toAdd (e a)) = Multiplicative.ofAdd 0
      rw [hp]
    rw [this, map_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hθinj).toEquiv, Nat.card_fun,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative L ≃ L), hcard, Nat.card_eq_fintype_card,
      Fintype.card_fin, ← pow_mul]
  · rw [MonoidHom.noncommPiCoprod_range]
    refine iSup_le fun a => ?_
    rintro _ ⟨u, rfl⟩
    exact hgD a _ (Multiplicative.toAdd u).2
  · have hle : orderOf t ∣ 2 ^ 2 := by
      have h4 := orderOf_dvd_of_pow_eq_one ht4
      norm_num
      exact h4
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hle
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  · rintro _ ⟨e, rfl⟩ hz
    have c1 := hz gZ hZD
    have c2 := hz gY hYD
    have hMZ : Mx e * Z = Z * Mx e := by
      have h := congrArg R.mat c1
      rw [mat_mul, mat_mul, hmat, hgZ] at h
      have e1 : (1 + Mx e) * (1 + Z) - (1 + Z) * (1 + Mx e) = Mx e * Z - Z * Mx e := by
        noncomm_ring
      rw [h, sub_self] at e1
      exact sub_eq_zero.mp e1.symm
    have hMY : Mx e * Y = Y * Mx e := by
      have h := congrArg R.mat c2
      rw [mat_mul, mat_mul, hmat, hgY] at h
      have e1 : (1 + Mx e) * (1 + Y) - (1 + Y) * (1 + Mx e) = Mx e * Y - Y * Mx e := by
        noncomm_ring
      rw [h, sub_self] at e1
      exact sub_eq_zero.mp e1.symm
    have h0 : Z * Y * Mx e - Mx e * (Z * Y) = 0 := by
      rw [mul_assoc, ← hMY, ← mul_assoc, ← hMZ, mul_assoc, sub_self]
    rw [hbr] at h0
    rw [hzero e h0, map_one]
  · rintro _ ⟨e, rfl⟩ x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hc : Commute (θ e) t :=
      (MonoidHom.commute_noncommPiCoprod ϕ (fun a u => ht a _) e).symm
    rw [(hc.zpow_right k).eq, mul_assoc, mul_inv_cancel, mul_one]
    exact Subgroup.zpow_mem_zpowers t k

theorem RootOpIn.add {D : Subgroup R.G} {L : Subfield K} {X X' : Matrix N N K}
    (h : R.RootOpIn D L X) (h' : R.RootOpIn D L X') (hXX' : X * X' = 0) (hX'X : X' * X = 0) :
    R.RootOpIn D L (X + X') where
  sq := by rw [mul_add, add_mul, add_mul, h.sq, h'.sq, hXX', hX'X, add_zero, add_zero]
  mem u := by
    obtain ⟨g, hg⟩ := h.mem u
    obtain ⟨g', hg'⟩ := h'.mem u
    refine ⟨g * g', ?_⟩
    rw [mat_mul, hg, hg', smul_add, add_mul, one_mul, mul_add, mul_one, smul_mul_smul_comm, hXX',
      smul_zero, add_zero]
    abel
  memD u hu := by
    obtain ⟨g, hgD, hg⟩ := h.memD u hu
    obtain ⟨g', hg'D, hg'⟩ := h'.memD u hu
    refine ⟨g * g', D.mul_mem hgD hg'D, ?_⟩
    rw [mat_mul, hg, hg', smul_add, add_mul, one_mul, mul_add, mul_one, smul_mul_smul_comm, hXX',
      smul_zero, add_zero]
    abel

theorem RootOpIn.exists_elt {D : Subgroup R.G} {L : Subfield K} {X : Matrix N N K}
    (h : R.RootOpIn D L X) :
    ∃ g : K → R.G, (∀ u, R.mat (g u) = 1 + u • X) ∧ ∀ u ∈ L, g u ∈ D := by
  choose g hg using h.mem
  refine ⟨g, hg, fun u hu => ?_⟩
  obtain ⟨g', hg'D, hg'⟩ := h.memD u hu
  rw [R.mat_injective ((hg u).trans hg'.symm)]
  exact hg'D

end RootData

namespace CarrierB

open TauCeti TauCeti.TypeBSpinCarrier Cliff RootData

variable (n : ℕ)

theorem weylS_mul_zeta : weylS n * zeta n = -(zeta n * weylS n) := by
  have hSz : crB n (Fin.last n) * zeta n * zeta n =
      -(zeta n * (crB n (Fin.last n) * zeta n)) := by
    rw [mul_assoc, zeta_sq, mul_one, ← mul_assoc, zeta_cr, neg_mul, mul_assoc, zeta_sq,
      mul_one, neg_neg]
  have hTz : zeta n * anB n (Fin.last n) * zeta n =
      -(zeta n * (zeta n * anB n (Fin.last n))) := by
    rw [mul_assoc, an_zeta, mul_neg, ← mul_assoc]
  exact weyl_anticomm_of (ES_sq n) (short_anticomm (Fin.last n)) hSz hTz

section Weyl

variable {n : ℕ} (hn : 2 ≤ n)

noncomputable abbrev tCl : Cl n :=
  weylL (⟨0, by omega⟩ : Fin (n + 1)) ⟨1, by omega⟩ *
    weylL (⟨0, by omega⟩ : Fin (n + 1)) ⟨1, by omega⟩ * weylS n

include hn

theorem tCl_rel :
    tCl hn * crB n ⟨0, by omega⟩ = -crB n ⟨0, by omega⟩ * tCl hn ∧
    tCl hn * crB n ⟨1, by omega⟩ = -crB n ⟨1, by omega⟩ * tCl hn ∧
    tCl hn * anB n ⟨1, by omega⟩ = -anB n ⟨1, by omega⟩ * tCl hn ∧
    tCl hn * crB n (Fin.last n) = -anB n (Fin.last n) * tCl hn ∧
    tCl hn * anB n (Fin.last n) = -crB n (Fin.last n) * tCl hn ∧
    tCl hn * zeta n = -zeta n * tCl hn := by
  set i0 : Fin (n + 1) := ⟨0, by omega⟩ with hi0
  set i1 : Fin (n + 1) := ⟨1, by omega⟩ with hi1
  set l := Fin.last n with hl
  have hv0 : i0.val = 0 := rfl
  have hv1 : i1.val = 1 := rfl
  have hvl : l.val = n := rfl
  have h01 : i0 ≠ i1 := fin_ne_of_val (by omega)
  have h0l : i0 ≠ l := fin_ne_of_val (by omega)
  have h1l : i1 ≠ l := fin_ne_of_val (by omega)
  set w := weylL i0 i1 with hw
  set S := weylS n with hS
  set b := polarizationBasis n
  have w1 : w * crB n i1 = crB n i0 * w := weylL_mul_cr h01
  have w0 : w * crB n i0 = -crB n i1 * w := chainWeyl_mul_cr_self (b := b) h01
  have wa1 : w * anB n i1 = anB n i0 * w := weylL_mul_an h01
  have wa0 : w * anB n i0 = -anB n i1 * w := chainWeyl_mul_an_self (b := b) h01
  have wl : Commute (crB n l) w := commute_weylL (cr_cr b l i0) (cr_an b h0l.symm)
    (cr_cr b l i1) (cr_an b h1l.symm)
  have wal : Commute (anB n l) w := commute_weylL (an_cr b h0l) (an_an b l i0) (an_cr b h1l)
    (an_an b l i1)
  have wz : Commute (zeta n) w := commute_weylL (zeta_cr n i0) (zeta_an n i0) (zeta_cr n i1)
    (zeta_an n i1)
  have s0 : Commute (crB n i0) S := commute_weylS n (cr_cr b i0 l) (cr_an b h0l) (cr_zeta n i0)
  have s1 : Commute (crB n i1) S := commute_weylS n (cr_cr b i1 l) (cr_an b h1l) (cr_zeta n i1)
  have sa1 : Commute (anB n i1) S := commute_weylS n (an_cr b h1l.symm) (an_an b i1 l)
    (an_zeta n i1)
  have sl : S * crB n l = -anB n l * S := weylS_mul_cr n
  have sal : S * anB n l = -crB n l * S := weylS_mul_an n
  have sz : S * zeta n = -(zeta n * S) := weylS_mul_zeta n
  have ww0 : w * w * crB n i0 = -crB n i0 * (w * w) := by
    rw [mul_assoc, w0, neg_mul, mul_neg, ← mul_assoc, w1]
    noncomm_ring
  have ww1 : w * w * crB n i1 = -crB n i1 * (w * w) := by
    rw [mul_assoc, w1, ← mul_assoc, w0]
    noncomm_ring
  have wwa1 : w * w * anB n i1 = -anB n i1 * (w * w) := by
    rw [mul_assoc, wa1, ← mul_assoc, wa0]
    noncomm_ring
  have hwwa : w * w * anB n l = anB n l * (w * w) := by
    rw [mul_assoc, ← wal.eq, ← mul_assoc, ← wal.eq, mul_assoc]
  have hwwc : w * w * crB n l = crB n l * (w * w) := by
    rw [mul_assoc, ← wl.eq, ← mul_assoc, ← wl.eq, mul_assoc]
  have hwwz : w * w * zeta n = zeta n * (w * w) := by
    rw [mul_assoc, ← wz.eq, ← mul_assoc, ← wz.eq, mul_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc w * w * S * crB n i0 = w * w * (S * crB n i0) := by rw [mul_assoc]
      _ = w * w * crB n i0 * S := by rw [← s0.eq]; simp only [mul_assoc]
      _ = -crB n i0 * (w * w * S) := by rw [ww0]; noncomm_ring
  · calc w * w * S * crB n i1 = w * w * (S * crB n i1) := by rw [mul_assoc]
      _ = w * w * crB n i1 * S := by rw [← s1.eq]; simp only [mul_assoc]
      _ = -crB n i1 * (w * w * S) := by rw [ww1]; noncomm_ring
  · calc w * w * S * anB n i1 = w * w * (S * anB n i1) := by rw [mul_assoc]
      _ = w * w * anB n i1 * S := by rw [← sa1.eq]; simp only [mul_assoc]
      _ = -anB n i1 * (w * w * S) := by rw [wwa1]; noncomm_ring
  · calc w * w * S * crB n l = w * w * (S * crB n l) := by rw [mul_assoc]
      _ = -(w * w * anB n l) * S := by rw [sl]; noncomm_ring
      _ = -anB n l * (w * w * S) := by rw [hwwa]; noncomm_ring
  · calc w * w * S * anB n l = w * w * (S * anB n l) := by rw [mul_assoc]
      _ = -(w * w * crB n l) * S := by rw [sal]; noncomm_ring
      _ = -crB n l * (w * w * S) := by rw [hwwc]; noncomm_ring
  · calc w * w * S * zeta n = w * w * (S * zeta n) := by rw [mul_assoc]
      _ = -(w * w * zeta n) * S := by rw [sz]; noncomm_ring
      _ = -zeta n * (w * w * S) := by rw [hwwz]; noncomm_ring

end Weyl

section Three

variable {n : ℕ} {K : Type} [Field K] {σ : K →+* K} {F : (rootData n K).G →* (rootData n K).G}

theorem bthree_ops (hF : (rootData n K).IsFrobenius σ F)
    (hR : (rootData n K).RootsInCommutator σ F) (h2 : (2 : K) ≠ 0) (hn : n = 2) :
    (∃ M : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ,
      IsIntOp n (crB n ⟨0, by omega⟩ * crB n ⟨1, by omega⟩) M ∧
      (rootData n K).RootOpIn ⁅fixedSubgroup F, fixedSubgroup F⁆ (RootData.fixedField σ)
        (intMap K M)) ∧
    (∃ M : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ,
      IsIntOp n (crB n ⟨0, by omega⟩ * crB n (Fin.last n)) M ∧
      (rootData n K).RootOpIn ⁅fixedSubgroup F, fixedSubgroup F⁆ (RootData.fixedField σ)
        (intMap K M)) ∧
    (∃ M : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ,
      IsIntOp n (crB n ⟨0, by omega⟩ * anB n (Fin.last n)) M ∧
      (rootData n K).RootOpIn ⁅fixedSubgroup F, fixedSubgroup F⁆ (RootData.fixedField σ)
        (intMap K M)) := by
  have hDx : ∀ i u, u ∈ RootData.fixedField σ →
      (rootData n K).x i u ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆ := fun i u hu => (hR i u hu).1
  set i0 : Fin (n + 1) := ⟨0, by omega⟩ with hi0
  set i1 : Fin (n + 1) := ⟨1, by omega⟩ with hi1
  set l := Fin.last n with hl
  set b := polarizationBasis n
  have hv0 : i0.val = 0 := rfl
  have hv1 : i1.val = 1 := rfl
  have hvl : l.val = n := rfl
  have h01 : i0 ≠ i1 := fin_ne_of_val (by omega)
  have h0l : i0 ≠ l := fin_ne_of_val (by omega)
  have h1l : i1 ≠ l := fin_ne_of_val (by omega)
  have hl1 : (⟨i1.val + 1, by omega⟩ : Fin (n + 1)) = l := Fin.ext (by simp only; omega)
  have hHn : ∀ (j : Fin (n + 1)), ∀ g ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆,
      nu j * g * (nu j)⁻¹ ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆ := fun j g hg =>
    conj_mem_commutator (nu_mem hF j) g hg
  obtain ⟨Xt, hXt, hXtR⟩ := exists_rootOp_theta (H := fixedSubgroup F)
    (L := RootData.fixedField σ) (by omega) h2 hDx
  have hθR : (rootData n K).RootOpIn ⁅fixedSubgroup F, fixedSubgroup F⁆ (RootData.fixedField σ)
      (intMap K Xt) := ⟨hXtR.sq, hXtR.mem, hXtR.memD⟩
  have hE0 : IsIntOp n (crB n i0 * anB n i1) (rootIntMatrix n (.inl i0)) :=
    isIntOp_E_lt n i0 (by omega)
  have hF0 : IsIntOp n (crB n i1 * anB n i0) (rootIntMatrix n (.inr i0)) :=
    isIntOp_F_lt n i0 (by omega)
  have hE1 : IsIntOp n (crB n i1 * anB n l) (rootIntMatrix n (.inl i1)) := by
    have h := isIntOp_E_lt n i1 (by omega)
    rw [hl1] at h
    exact h
  have hF1 : IsIntOp n (crB n l * anB n i1) (rootIntMatrix n (.inr i1)) := by
    have h := isIntOp_F_lt n i1 (by omega)
    rw [hl1] at h
    exact h
  have hwc1 : weylL i0 i1 * (crB n i1 * anB n l) = crB n i0 * anB n l * weylL i0 i1 := by
    have hc : Commute (anB n l) (weylL i0 i1) :=
      commute_weylL (an_cr b h0l) (an_an b l i0) (an_cr b h1l) (an_an b l i1)
    rw [← mul_assoc, weylL_mul_cr h01, mul_assoc, ← hc.eq, ← mul_assoc]
  obtain ⟨hY', hY'R⟩ := rootOpIn_conj (i := i0) hE0 hF0 (EL_sq h01) (FL_sq h01) hE1 hwc1
    (hHn i0) (RootOpIn.of_x (R := rootData n K) (L := RootData.fixedField σ) i1
      fun u hu => hDx i1 u hu)
  have hwc2 : weylL i1 l * (crB n i0 * crB n i1) = -(crB n i0 * crB n l) * weylL i1 l := by
    have hc : Commute (crB n i0) (weylL i1 l) :=
      commute_weylL (cr_cr b i0 i1) (cr_an b h01) (cr_cr b i0 l) (cr_an b h0l)
    have hw : weylL i1 l * crB n i1 = -crB n l * weylL i1 l := chainWeyl_mul_cr_self (b := b) h1l
    rw [← mul_assoc, ← hc.eq, mul_assoc, hw]
    noncomm_ring
  obtain ⟨hY, hYR⟩ := rootOpIn_conj (i := i1) hE1 hF1 (EL_sq h1l) (FL_sq h1l) hXt hwc2
    (hHn i1) hθR
  have hYR' := hYR.neg
  rw [← intMap_neg'] at hYR'
  exact ⟨⟨Xt, hXt, hθR⟩, ⟨_, hY.neg.congr (neg_neg _), hYR'⟩, ⟨_, hY', hY'R⟩⟩

omit [Field K] in
theorem bracket_intMap {a c d : Cl n} {A C D : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ}
    (ha : IsIntOp n a A) (hc : IsIntOp n c C) (hd : IsIntOp n d D) (h : a * c - c * a = d)
    (K' : Type*) [Field K'] :
    intMap K' A * intMap K' C - intMap K' C * intMap K' A = intMap K' D :=
  intMap_bracket K' (((ha.mul hc).sub (hc.mul ha)).eq (hd.congr h.symm))

omit [Field K] in
theorem conj_intMap {w c c' : Cl n} {W M M' : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ}
    (hw : IsIntOp n w W) (hc : IsIntOp n c M) (hc' : IsIntOp n c' M') (h : w * c = c' * w)
    (K' : Type*) [Field K'] : intMap K' W * intMap K' M = intMap K' M' * intMap K' W := by
  rw [← intMap_mul, ← intMap_mul, (hw.mul hc).eq ((hc'.mul hw).congr h.symm)]

omit [Field K] in
theorem num_zeta (j : Fin (n + 1)) :
    crB n j * anB n j * zeta n - zeta n * (crB n j * anB n j) = 0 := by
  rw [commute_mul_of_anticomm₂ (zeta_cr n j) (zeta_an n j), sub_self]

theorem nu_pow_four (i : Fin (n + 1)) : (nu i : (rootData n K).G) ^ 4 = 1 := by
  have hp := (rootData n K).sqZero i
  have h1 : (rootData n K).mat (nu i) =
      SqZeroPair.φ ((rootData n K).E i) ((rootData n K).F i) 0 1 (-1) 0 := by
    rw [nu, mat_mul, mat_mul, mat_x, mat_y, hp.φ_mul, hp.φ_mul]
    congr 1 <;> ring
  have h2 : (rootData n K).mat (nu i * nu i) =
      SqZeroPair.φ ((rootData n K).E i) ((rootData n K).F i) (-1) 0 0 (-1) := by
    rw [(rootData n K).mat_mul (nu i) (nu i), h1, hp.φ_mul]
    congr 1 <;> ring
  apply (rootData n K).mat_injective
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_two, pow_two,
    (rootData n K).mat_mul (nu i * nu i) (nu i * nu i), h2, hp.φ_mul, mat_one]
  have e : SqZeroPair.φ ((rootData n K).E i) ((rootData n K).F i)
      ((-1) * (-1) + 0 * 0) ((-1) * 0 + 0 * (-1)) (0 * (-1) + (-1) * 0) (0 * 0 + (-1) * (-1)) =
      SqZeroPair.φ ((rootData n K).E i) ((rootData n K).F i) 1 0 0 1 := by
    congr 1 <;> ring
  rw [e, SqZeroPair.φ_one_zero_zero_one]

theorem bthree_T (hR : (rootData n K).RootsInCommutator σ F) (hn : n = 2) :
    ∃ W : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ,
      IsIntOp n (tCl (n := n) (by omega)) W ∧
      (rootData n K).mat (nu ⟨0, by omega⟩ * nu ⟨0, by omega⟩ * nu (Fin.last n)) = intMap K W ∧
      nu ⟨0, by omega⟩ * nu ⟨0, by omega⟩ * nu (Fin.last n) ∈
        ⁅fixedSubgroup F, fixedSubgroup F⁆ ∧
      (nu ⟨0, by omega⟩ * nu ⟨0, by omega⟩ * nu (Fin.last n) : (rootData n K).G) ^ 4 = 1 ∧
      ∃ y ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆,
        nu ⟨0, by omega⟩ * nu ⟨0, by omega⟩ * nu (Fin.last n) * y ≠
          y * (nu ⟨0, by omega⟩ * nu ⟨0, by omega⟩ * nu (Fin.last n)) := by
  set i0 : Fin (n + 1) := ⟨0, by omega⟩ with hi0
  set i1 : Fin (n + 1) := ⟨1, by omega⟩ with hi1
  set l := Fin.last n with hl
  have hv0 : i0.val = 0 := rfl
  have hv1 : i1.val = 1 := rfl
  have hvl : l.val = n := rfl
  have h0l : i0 ≠ l := fin_ne_of_val (by omega)
  have h1L : (1 : K) ∈ RootData.fixedField σ := (RootData.fixedField σ).one_mem
  have hm1L : (-1 : K) ∈ RootData.fixedField σ := (RootData.fixedField σ).neg_mem h1L
  have hnuD : ∀ j, (nu j : (rootData n K).G) ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆ := fun j =>
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (hR j 1 h1L).1 (hR j (-1) hm1L).2) (hR j 1 h1L).1
  have hE0 : IsIntOp n (crB n i0 * anB n i1) (rootIntMatrix n (.inl i0)) :=
    isIntOp_E_lt n i0 (by omega)
  have hF0 : IsIntOp n (crB n i1 * anB n i0) (rootIntMatrix n (.inr i0)) :=
    isIntOp_F_lt n i0 (by omega)
  have hW := ((isIntOp_weyl hE0 hF0).1.mul (isIntOp_weyl hE0 hF0).1).mul
    (isIntOp_weyl (isIntOp_E_last n) (isIntOp_F_last n)).1
  have hmat : (rootData n K).mat (nu i0 * nu i0 * nu l) =
      intMap K (wlMat i0 * wlMat i0 * wlMat l) := by
    rw [mat_mul, mat_mul, mat_nu, mat_nu, intMap_mul, intMap_mul]
  have hcm : (rootData n K).CM i0 l = 0 := by
    rw [rootData_CM, Matrix.transpose_apply]
    exact B_apply_far _ _ _ (by omega) (by omega) (by omega)
  have cxx := (rootData n K).commute_x_x hcm
  have cyy := (rootData n K).commute_y_y hcm
  have cxy := (rootData n K).commute_x_y h0l
  have cyx : ∀ u v, Commute ((rootData n K).y i0 u) ((rootData n K).x l v) := fun u v =>
    ((rootData n K).commute_x_y h0l.symm v u).symm
  have hx0 : ∀ u, Commute ((rootData n K).x i0 u) (nu l) := fun u =>
    ((cxx u 1).mul_right (cxy u (-1))).mul_right (cxx u 1)
  have hy0 : ∀ u, Commute ((rootData n K).y i0 u) (nu l) := fun u =>
    ((cyx u 1).mul_right (cyy u (-1))).mul_right (cyx u 1)
  have h0S : Commute (nu i0 : (rootData n K).G) (nu l) :=
    ((hx0 1).mul_left (hy0 (-1))).mul_left (hx0 1)
  refine ⟨_, hW, hmat, Subgroup.mul_mem _ (Subgroup.mul_mem _ (hnuD i0) (hnuD i0)) (hnuD l), ?_,
    ⟨(rootData n K).x l 1, (hR l 1 h1L).1, fun h => ?_⟩⟩
  · rw [(h0S.mul_left h0S).mul_pow, nu_pow_four (Fin.last n), mul_one, ← pow_two, ← pow_mul,
      show 2 * 4 = 4 * 2 from rfl, pow_mul, nu_pow_four, one_pow]
  ·
    obtain ⟨-, -, -, r4, -, r6⟩ := tCl_rel (n := n) (by omega)
    have hcl : tCl (n := n) (by omega) * (crB n l * zeta n) =
        -(zeta n * anB n l) * tCl (n := n) (by omega) := by
      calc tCl (n := n) (by omega) * (crB n l * zeta n)
          = tCl (n := n) (by omega) * crB n l * zeta n := (mul_assoc _ _ _).symm
        _ = -anB n l * (tCl (n := n) (by omega) * zeta n) := by rw [r4, mul_assoc]
        _ = anB n l * zeta n * tCl (n := n) (by omega) := by
            rw [r6, neg_mul (zeta n), neg_mul_neg, ← mul_assoc]
        _ = -(zeta n * anB n l) * tCl (n := n) (by omega) := by rw [an_zeta]
    have hconj := conj_intMap hW (isIntOp_E_last n) (isIntOp_F_last n).neg hcl K
    rw [intMap_neg', ← hmat] at hconj
    have hm := congrArg (rootData n K).mat h
    rw [(rootData n K).mat_mul (nu i0 * nu i0 * nu l), (rootData n K).mat_mul _
      (nu i0 * nu i0 * nu l), mat_x', one_smul] at hm
    have hE : (rootData n K).E l = intMap K (rootIntMatrix n (.inl l)) := rfl
    have hF : (rootData n K).F l = intMap K (rootIntMatrix n (.inr l)) := rfl
    have hcE : (rootData n K).mat (nu i0 * nu i0 * nu l) * (rootData n K).E l =
        (rootData n K).E l * (rootData n K).mat (nu i0 * nu i0 * nu l) := by
      have e : (rootData n K).mat (nu i0 * nu i0 * nu l) * (1 + (rootData n K).E l) -
          (1 + (rootData n K).E l) * (rootData n K).mat (nu i0 * nu i0 * nu l) =
          (rootData n K).mat (nu i0 * nu i0 * nu l) * (rootData n K).E l -
            (rootData n K).E l * (rootData n K).mat (nu i0 * nu i0 * nu l) := by noncomm_ring
      rw [hm, sub_self] at e
      exact sub_eq_zero.mp e.symm
    have hinv : (rootData n K).mat (nu i0 * nu i0 * nu l) *
        (rootData n K).mat (nu i0 * nu i0 * nu l)⁻¹ = 1 := by
      rw [← mat_mul, mul_inv_cancel, mat_one]
    have hEF : (rootData n K).E l = -(rootData n K).F l := by
      calc (rootData n K).E l = (rootData n K).E l * ((rootData n K).mat (nu i0 * nu i0 * nu l) *
            (rootData n K).mat (nu i0 * nu i0 * nu l)⁻¹) := by rw [hinv, mul_one]
        _ = (rootData n K).mat (nu i0 * nu i0 * nu l) * (rootData n K).E l *
            (rootData n K).mat (nu i0 * nu i0 * nu l)⁻¹ := by rw [hcE]; noncomm_ring
        _ = -((rootData n K).F l * (rootData n K).mat (nu i0 * nu i0 * nu l) *
            (rootData n K).mat (nu i0 * nu i0 * nu l)⁻¹) := by rw [hE, hconj, ← hF]; noncomm_ring
        _ = -(rootData n K).F l := by
            rw [mul_assoc ((rootData n K).F l), hinv, mul_one]
    have hp := (rootData n K).sqZero l
    have h3 : -(rootData n K).F l * (rootData n K).F l * -(rootData n K).F l =
        -(rootData n K).F l := by
      rw [← hEF]
      exact hp.efe
    have h4 : (rootData n K).F l * (rootData n K).F l * (rootData n K).F l =
        -(rootData n K).F l := by
      rw [← h3]
      noncomm_ring
    rw [hp.ff, zero_mul] at h4
    have hF0 : (rootData n K).F l = 0 := neg_eq_zero.mp h4.symm
    exact (rootData n K).E_ne_zero l (by rw [hEF, hF0, neg_zero])

section Ring

variable {A : Type*} [Ring A]

theorem mul_of_neg_conj {t x y : A} (hx : t * x = -x * t) (hy : t * y = -y * t) :
    t * (x * y) = x * y * t := by
  calc t * (x * y) = t * x * y := (mul_assoc _ _ _).symm
    _ = -x * (t * y) := by rw [hx]; noncomm_ring
    _ = x * y * t := by rw [hy]; noncomm_ring

theorem bracket_mul_self_of {N x v : A} (hx : N * x - x * N = x) (hv : N * v - v * N = 0) :
    N * (x * v) - x * v * N = x * v := by
  rw [bracket_mul_of hx hv, mul_zero, add_zero]

end Ring

omit [Field K] in
theorem num_comm {j : Fin (n + 1)} {v : Cl n} (hvc : v * crB n j = -(crB n j * v))
    (hva : v * anB n j = -(anB n j * v)) :
    crB n j * anB n j * v - v * (crB n j * anB n j) = 0 := by
  rw [← commute_mul_of_anticomm₂ hvc hva, sub_self]

omit [Field K] in
theorem bracket_add_of {z x y u v : Cl n} (hx : z * x - x * z = u) (hy : z * y - y * z = v) :
    z * (x + y) - (x + y) * z = u + v := by
  rw [← hx, ← hy]
  noncomm_ring

theorem hasWitness_bthree_gen (hF : (rootData n K).IsFrobenius σ F)
    (hR : (rootData n K).RootsInCommutator σ F) (h2 : (2 : K) ≠ 0) {p f : ℕ} [CharP K p]
    (hcard : Nat.card (RootData.fixedField σ) = p ^ f) {c : Kˣ}
    (hc : ∀ k : ℤ, k ≠ 0 → -4 ≤ k → k ≤ 4 → c ^ k ≠ 1) (hn : n = 2) :
    HasWitness (DerivedCentralQuotient (fixedSubgroup F)) p (f * 4) := by
  have hn2 : 2 ≤ n := by omega
  obtain ⟨⟨Mt, hMt, hMtR⟩, ⟨MY, hMY, hMYR⟩, ⟨MY', hMY', hMY'R⟩⟩ := bthree_ops hF hR h2 hn
  obtain ⟨W, hW, hmatT, hTD, hT4, hTz⟩ := bthree_T (F := F) hR hn
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := tCl_rel hn2
  set i0 : Fin (n + 1) := ⟨0, by omega⟩ with hi0
  set i1 : Fin (n + 1) := ⟨1, by omega⟩ with hi1
  set l := Fin.last n with hl
  have hv0 : i0.val = 0 := rfl
  have hv1 : i1.val = 1 := rfl
  have hvl : l.val = n := rfl
  have h01 : i0 ≠ i1 := fin_ne_of_val (by omega)
  have h0l : i0 ≠ l := fin_ne_of_val (by omega)
  have h1l : i1 ≠ l := fin_ne_of_val (by omega)
  set b := polarizationBasis n
  obtain ⟨MZ, MFZ, hMZ, hMFZ, hMZR, hMFZR⟩ := exists_shortOp hF hc hn2 i0
  obtain ⟨M1, N1, hM1, hN1, -, -⟩ := exists_shortOp hF hc hn2 i1
  have hE0 : IsIntOp n (crB n i0 * anB n i1) (rootIntMatrix n (.inl i0)) :=
    isIntOp_E_lt n i0 (by omega)
  have hEl := isIntOp_E_last n
  have hFl := isIntOp_F_last n
  let v : Fin 4 → Cl n := ![crB n i1, anB n i1, crB n l + anB n l, zeta n]
  let MM : Fin 4 → Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ :=
    ![Mt, rootIntMatrix n (.inl i0), MY + MY', MZ]
  have hMM : ∀ a, IsIntOp n (crB n i0 * v a) (MM a) := by
    intro a
    fin_cases a
    · exact hMt
    · exact hE0
    · exact (hMY.add' hMY').congr (mul_add _ _ _).symm
    · exact hMZ
  have hv : ∀ a, v a * crB n i0 = -(crB n i0 * v a) := by
    intro a
    fin_cases a
    · exact cr_cr b i1 i0
    · exact an_cr b h01
    · show (crB n l + anB n l) * crB n i0 = -(crB n i0 * (crB n l + anB n l))
      rw [add_mul, cr_cr b l i0, an_cr b h0l, mul_add, neg_add]
    · exact zeta_cr n i0
  have hva : ∀ a, v a * anB n i0 = -(anB n i0 * v a) := by
    intro a
    fin_cases a
    · exact cr_an b h01.symm
    · exact an_an b i1 i0
    · show (crB n l + anB n l) * anB n i0 = -(anB n i0 * (crB n l + anB n l))
      rw [add_mul, cr_an b h0l.symm, an_an b l i0, mul_add, neg_add]
    · exact zeta_an n i0
  have hvT : ∀ a, tCl hn2 * v a = -v a * tCl hn2 := by
    intro a
    fin_cases a
    · exact r2
    · exact r3
    · show tCl hn2 * (crB n l + anB n l) = -(crB n l + anB n l) * tCl hn2
      rw [mul_add, r4, r5, neg_add, add_mul, add_comm]
    · exact r6
  have hXX : ∀ a a', intMap K (MM a) * intMap K (MM a') = 0 := fun a a' => by
    rw [← intMap_mul, ((hMM a).mul (hMM a')).eq_zero (crm_mul_crm (hv a)), intMap_zero]
  have hXR : ∀ a, (rootData n K).RootOpIn ⁅fixedSubgroup F, fixedSubgroup F⁆
      (RootData.fixedField σ) (intMap K (MM a)) := by
    intro a
    fin_cases a
    · exact hMtR
    · exact RootOpIn.of_x (R := rootData n K) i0 fun u hu => (hR i0 u hu).1
    · have hYY : intMap K MY * intMap K MY' = 0 := by
        rw [← intMap_mul, (hMY.mul hMY').eq_zero (crm_mul_crm (cr_cr b l i0)), intMap_zero]
      have hY'Y : intMap K MY' * intMap K MY = 0 := by
        rw [← intMap_mul, (hMY'.mul hMY).eq_zero (crm_mul_crm (an_cr b h0l)), intMap_zero]
      show (rootData n K).RootOpIn _ _ (intMap K (MY + MY'))
      rw [intMap_add']
      exact hMYR.add hMY'R hYY hY'Y
    · exact hMZR
  choose g hg hgD using fun a => (hXR a).exists_elt
  obtain ⟨gZ, hgZD, hgZ⟩ := hMZR.memD 1 (RootData.fixedField σ).one_mem
  obtain ⟨gY, hgYD, hgY⟩ := hMFZR.memD 1 (RootData.fixedField σ).one_mem
  rw [one_smul] at hgZ hgY
  have hzz : ∀ j : Fin (n + 1), crB n j * zeta n * (zeta n * anB n j) = crB n j * anB n j :=
    fun j => by rw [mul_assoc, ← mul_assoc (zeta n), zeta_sq, one_mul]
  have hN0 : IsIntOp n (crB n i0 * anB n i0) (MZ * MFZ) := (hMZ.mul hMFZ).congr (hzz i0)
  have hK : ∀ a, intMap K MZ * intMap K MFZ * intMap K (MM a) -
      intMap K (MM a) * (intMap K MZ * intMap K MFZ) = intMap K (MM a) := fun a => by
    rw [← intMap_mul]
    exact bracket_intMap hN0 (hMM a) (hMM a)
      (bracket_mul_self_of (num_cr_self (b := b) i0) (num_comm (hv a) (hva a))) K
  have hTX : ∀ a, (rootData n K).mat (nu i0 * nu i0 * nu l) * intMap K (MM a) =
      intMap K (MM a) * (rootData n K).mat (nu i0 * nu i0 * nu l) := fun a => by
    rw [hmatT]
    exact conj_intMap hW (hMM a) (hMM a) (mul_of_neg_conj r1 (hvT a)) K
  have ht : ∀ a u, Commute (nu i0 * nu i0 * nu l) (g a u) := fun a u =>
    (rootData n K).commute_of_mat (by
      show (rootData n K).mat (nu i0 * nu i0 * nu l) * (rootData n K).mat (g a u) =
        (rootData n K).mat (g a u) * (rootData n K).mat (nu i0 * nu i0 * nu l)
      rw [hg, mul_add, mul_one, add_mul, one_mul, mul_smul_comm, smul_mul_assoc, hTX])
  have hZne : intMap K MZ ≠ 0 := fun h0 => by
    have h : intMap K MZ * intMap K MFZ + intMap K MFZ * intMap K MZ = 1 := by
      rw [← intMap_mul, ← intMap_mul, ← intMap_add',
        ((hMZ.mul hMFZ).add' (hMFZ.mul hMZ)).eq (isIntOp_one.congr (short_anticomm i0).symm),
        intMap_one']
    rw [h0, zero_mul, mul_zero, add_zero] at h
    have h' := congrFun (congrFun h (vac (n := n))) (vac (n := n))
    rw [Matrix.zero_apply, Matrix.one_apply_eq] at h'
    exact zero_ne_one h'
  have hind : ∀ cc : Fin 4 → K, ∑ a, cc a • intMap K (MM a) = 0 → ∀ a, cc a = 0 := by
    intro cc hcc
    rw [Fin.sum_univ_four] at hcc
    have hN1 : IsIntOp n (crB n i1 * anB n i1) (M1 * N1) := (hM1.mul hN1).congr (hzz i1)
    have hNl : IsIntOp n (crB n l * anB n l)
        (rootIntMatrix n (.inl l) * rootIntMatrix n (.inr l)) := (hEl.mul hFl).congr (hzz l)
    have k0 := bracket_intMap hN1 (hMM 0) (hMM 0) ((bracket_mul_of
      (num_cr_ne (b := b) h01.symm) (num_cr_self (b := b) i1)).trans
        (by rw [zero_mul, zero_add]; try rfl)) K
    have k1 := bracket_intMap hN1 (hMM 1) (hMM 1).neg ((bracket_mul_of
      (num_cr_ne (b := b) h01.symm) (num_an_self (b := b) i1)).trans
        (by rw [zero_mul, zero_add, mul_neg]; try rfl)) K
    have k2 := bracket_intMap hN1 (hMM 2) IsIntOp.zero ((bracket_mul_of
      (num_cr_ne (b := b) h01.symm) (bracket_add_of (num_cr_ne (b := b) h1l)
        (num_an_ne (b := b) h1l))).trans (by rw [zero_mul, zero_add, add_zero, mul_zero])) K
    have k3 := bracket_intMap hN1 (hMM 3) IsIntOp.zero ((bracket_mul_of
      (num_cr_ne (b := b) h01.symm) (num_zeta i1)).trans (by rw [zero_mul, zero_add, mul_zero]))
      K
    rw [intMap_neg'] at k1
    rw [intMap_zero] at k2 k3
    have hW1 : intMap K (M1 * N1) * (cc 2 • intMap K (MM 2) + cc 3 • intMap K (MM 3)) -
        (cc 2 • intMap K (MM 2) + cc 3 • intMap K (MM 3)) * intMap K (M1 * N1) = 0 := by
      have e : intMap K (M1 * N1) * (cc 2 • intMap K (MM 2) + cc 3 • intMap K (MM 3)) -
          (cc 2 • intMap K (MM 2) + cc 3 • intMap K (MM 3)) * intMap K (M1 * N1) =
          cc 2 • (intMap K (M1 * N1) * intMap K (MM 2) - intMap K (MM 2) * intMap K (M1 * N1)) +
          cc 3 • (intMap K (M1 * N1) * intMap K (MM 3) - intMap K (MM 3) * intMap K (M1 * N1)) :=
        by simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, smul_sub]; abel
      rw [e, k2, k3, smul_zero, smul_zero, add_zero]
    obtain ⟨hc0, hc1⟩ := smul_eq_zero_of_weights h2 k0 k1 hW1 (by rw [← add_assoc]; exact hcc)
    rw [hc0, hc1, zero_add, zero_add] at hcc
    have m0 := bracket_intMap hNl hMY hMY ((bracket_mul_of
      (num_cr_ne (b := b) h0l.symm) (num_cr_self (b := b) l)).trans
        (by rw [zero_mul, zero_add]; try rfl)) K
    have m1 := bracket_intMap hNl hMY' hMY'.neg ((bracket_mul_of
      (num_cr_ne (b := b) h0l.symm) (num_an_self (b := b) l)).trans
        (by rw [zero_mul, zero_add, mul_neg]; try rfl)) K
    have m3 := bracket_intMap hNl (hMM 3) IsIntOp.zero ((bracket_mul_of
      (num_cr_ne (b := b) h0l.symm) (num_zeta l)).trans (by rw [zero_mul, zero_add, mul_zero])) K
    rw [intMap_neg'] at m1
    rw [intMap_zero] at m3
    have hW2 : intMap K (rootIntMatrix n (.inl l) * rootIntMatrix n (.inr l)) *
        (cc 3 • intMap K (MM 3)) - cc 3 • intMap K (MM 3) *
          intMap K (rootIntMatrix n (.inl l) * rootIntMatrix n (.inr l)) = 0 := by
      rw [mul_smul_comm, smul_mul_assoc, ← smul_sub, m3, smul_zero]
    have hcc' : cc 2 • intMap K MY + cc 2 • intMap K MY' + cc 3 • intMap K (MM 3) = 0 := by
      rw [← smul_add, ← intMap_add']
      exact hcc
    obtain ⟨hc2, hc2'⟩ := smul_eq_zero_of_weights h2 m0 m1 hW2 hcc'
    have hc3 : cc 3 • intMap K (MM 3) = 0 := by
      rw [hc2, hc2', zero_add, zero_add] at hcc'
      exact hcc'
    intro a
    fin_cases a
    · exact (smul_eq_zero.mp hc0).resolve_right (pair_ne_zero (by rw [Fin.lt_def]; omega) hMt)
    · exact (smul_eq_zero.mp hc1).resolve_right ((rootData n K).E_ne_zero i0)
    · exact (smul_eq_zero.mp hc2).resolve_right (pair_ne_zero (by rw [Fin.lt_def]; omega) hMY)
    · exact (smul_eq_zero.mp hc3).resolve_right hZne
  exact witness_of_number hcard hXX hind g hg hgD hgZ hgY hgZD hgYD hK _ hTD hT4 hTz ht

end Three

theorem exists_unit_order_ge_five (v : ValidLieTypeIndex) (hodd : v.characteristic ≠ 2) :
    ∃ c : v.Closureˣ, ∀ k : ℤ, k ≠ 0 → -4 ≤ k → k ≤ 4 → c ^ k ≠ 1 := by
  have hp := v.characteristic_prime
  have h3 : 3 ≤ v.characteristic := by
    have := hp.two_le
    omega
  have hcard : Nat.card (frobeniusFixedSubfield v.Closure v.characteristic 2) =
      v.characteristic ^ 2 := card_frobeniusFixedSubfield _ _ _ (by norm_num)
  have : Finite (frobeniusFixedSubfield v.Closure v.characteristic 2) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.ne_zero)
  obtain ⟨c, -, hc⟩ := exists_unit_orderOf_eq_card
    (frobeniusFixedSubfield v.Closure v.characteristic 2)
  rw [hcard] at hc
  have h8 : 8 ≤ v.characteristic ^ 2 - 1 := by
    have : 9 ≤ v.characteristic ^ 2 := by nlinarith
    omega
  refine ⟨c, fun k hk h1 h2' hck => ?_⟩
  have hdvd := orderOf_dvd_iff_zpow_eq_one.mpr hck
  rw [hc] at hdvd
  obtain ⟨j, hj⟩ := hdvd
  have h8' : (8 : ℤ) ≤ ((v.characteristic ^ 2 - 1 : ℕ) : ℤ) := by exact_mod_cast h8
  rcases lt_trichotomy j 0 with hj0 | hj0 | hj0
  · nlinarith
  · rw [hj0, mul_zero] at hj
    exact hk hj
  · nlinarith

variable (b : TypeBLieIndex)

theorem hasWitness_bthree (hodd : b.1.characteristic ≠ 2) (h3 : b.carrierRank = 2) :
    HasWitness b.Group b.1.characteristic (b.1.fieldExponent * 4) := by
  obtain ⟨c, hc⟩ := exists_unit_order_ge_five b.1 hodd
  exact hasWitness_bthree_gen (isFrobenius b) (rootsInCommutator_odd b hodd (by omega))
    (two_ne_zero_closure b hodd) (card_fixedField_frob b) hc h3

end CarrierB

end CFSG.RankThree.PartTwo.Census.Spin
