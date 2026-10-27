module

public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorusNorm

public section

open Polynomial Module

namespace CFSG.StandardType

namespace SpNS

section Field

variable {K : Type} [Field K] [Finite K] {g : K[X]} [Fact (Irreducible g)] {p : ℕ}

omit [Field K] [Finite K] in
theorem natCast_card_eq_neg_one (hpq : p ∣ Nat.card K + 1) : ((Nat.card K : ℕ) : ZMod p) = -1 := by
  have h : ((Nat.card K + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hpq
  rw [Nat.cast_add, Nat.cast_one] at h
  exact eq_neg_of_add_eq_zero_left h

theorem not_dvd_card_sub_one (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1) :
    ¬ p ∣ Nat.card K - 1 := by
  intro h
  have h1 : 1 ≤ Nat.card K := Nat.one_le_iff_ne_zero.mpr (Nat.card_pos (α := K)).ne'
  have h2 : p ∣ (Nat.card K + 1) - (Nat.card K - 1) := Nat.dvd_sub hpq h
  rw [show Nat.card K + 1 - (Nat.card K - 1) = 2 by omega] at h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)

theorem natDegree_eq_two (hp : p.Prime) (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0)
    (hgd : g ∣ cyclotomic p K) (hpq : p ∣ Nat.card K + 1) : g.natDegree = 2 := by
  have : Fact p.Prime := ⟨hp⟩
  rw [OrdPNS.natDegree_eq_ordQ hp hpK Fact.out hgd, OrdPNS.ordQ, natCast_card_eq_neg_one hpq,
    orderOf_neg_one, ZMod.ringChar_zmod_n]
  split_ifs with h
  · exact absurd h hp2
  · rfl

theorem rootPB_dim_eq_two (hp : p.Prime) (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0)
    (hgd : g ∣ cyclotomic p K) (hpq : p ∣ Nat.card K + 1) : (CoordSL.rootPB g).dim = 2 := by
  rw [CoordSL.rootPB, AdjoinRoot.powerBasis_dim]
  exact natDegree_eq_two hp hp2 hpK hgd hpq

omit [Finite K] in
theorem root_pow_card (hp : p.Prime) (hpK : (p : K) ≠ 0) (hgd : g ∣ cyclotomic p K)
    (hpq : p ∣ Nat.card K + 1) :
    AdjoinRoot.root g ^ Nat.card K = AdjoinRoot.root g ^ (p - 1) := by
  have hζ := NSFrame.root_isPrimitiveRoot (g := g) hp hpK hgd
  rw [pow_eq_pow_mod _ hζ.pow_eq_one, pow_eq_pow_mod (p - 1) hζ.pow_eq_one]
  congr 1
  obtain ⟨m, hm⟩ := hpq
  have hm1 : 1 ≤ m := by
    rcases m with _ | m
    · omega
    · omega
  have h1 : Nat.card K = p * (m - 1) + (p - 1) := by
    have := hp.pos
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    have : p * (m' + 1) = p * m' + p := by ring
    omega
  rw [h1, Nat.mul_add_mod]

theorem aeval_root_pow_pred (hp : p.Prime) (hpK : (p : K) ≠ 0) (hgd : g ∣ cyclotomic p K)
    (hpq : p ∣ Nat.card K + 1) : aeval (AdjoinRoot.root g ^ (p - 1)) g = 0 := by
  have : Fintype K := Fintype.ofFinite K
  have h : AdjoinRoot.root g ^ Fintype.card K =
      FiniteField.frobeniusAlgHom K (AdjoinRoot g) (AdjoinRoot.root g) := rfl
  rw [← root_pow_card hp hpK hgd hpq, Nat.card_eq_fintype_card, h, aeval_algHom_apply,
    AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]

theorem norm_root_eq_one (hp : p.Prime) (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0)
    (hgd : g ∣ cyclotomic p K) (hpq : p ∣ Nat.card K + 1) :
    Algebra.norm K (AdjoinRoot.root g) = 1 := by
  rw [Algebra.norm_eq_matrix_det (CoordSL.rootPB g).basis]
  exact CoordSL.det_rootMat hp (not_dvd_card_sub_one hp hp2 hpq) hpK hgd

theorem eq_root_or_eq_root_pow_pred (hp : p.Prime) (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0)
    (hgd : g ∣ cyclotomic p K) (hpq : p ∣ Nat.card K + 1) {μ : AdjoinRoot g}
    (hμ : aeval μ g = 0) : μ = AdjoinRoot.root g ∨ μ = AdjoinRoot.root g ^ (p - 1) := by
  classical
  have hζ := NSFrame.root_isPrimitiveRoot (g := g) hp hpK hgd
  set ζ := AdjoinRoot.root g with hζdef
  have hne : ζ ≠ ζ ^ (p - 1) := by
    intro h0
    have h2 : ζ ^ 2 = 1 := by
      calc ζ ^ 2 = ζ * ζ := sq _
        _ = ζ * ζ ^ (p - 1) := congrArg (ζ * ·) h0
        _ = 1 := by rw [← pow_succ', Nat.sub_add_cancel hp.one_lt.le, hζ.pow_eq_one]
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hζ.dvd_of_pow_eq_one 2 h2))
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  obtain ⟨P, hP⟩ : ∃ P, P = g.map (algebraMap K (AdjoinRoot g)) := ⟨_, rfl⟩
  have hP0 : P ≠ 0 := hP ▸ Polynomial.map_ne_zero (Fact.out : Irreducible g).ne_zero
  have hroot : ∀ x : AdjoinRoot g, aeval x g = 0 → x ∈ P.roots := fun x hx => by
    rw [Polynomial.mem_roots hP0, IsRoot, hP, eval_map_algebraMap]
    exact hx
  have hζr : ζ ∈ P.roots := hroot ζ (by rw [hζdef, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self])
  have hζ'r : ζ ^ (p - 1) ∈ P.roots := hroot _ (aeval_root_pow_pred hp hpK hgd hpq)
  have hμr : μ ∈ P.roots := hroot μ hμ
  have hnd : (μ ::ₘ ζ ::ₘ {ζ ^ (p - 1)} : Multiset (AdjoinRoot g)).Nodup := by
    simp only [Multiset.nodup_cons, Multiset.mem_cons, Multiset.mem_singleton,
      Multiset.nodup_singleton, not_or, and_true]
    exact ⟨⟨h1, h2⟩, hne⟩
  have hle : (μ ::ₘ ζ ::ₘ {ζ ^ (p - 1)} : Multiset (AdjoinRoot g)) ≤ P.roots := by
    rw [Multiset.le_iff_subset hnd]
    intro x hx
    simp only [Multiset.mem_cons, Multiset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hμr
    · exact hζr
    · exact hζ'r
  have hcard := Multiset.card_le_card hle
  have hdeg : Multiset.card P.roots ≤ 2 := by
    have h3 := Polynomial.card_roots' P
    have h4 : P.natDegree = 2 := by rw [hP, natDegree_map, natDegree_eq_two hp hp2 hpK hgd hpq]
    omega
  simp at hcard
  omega

theorem eq_one_or_eq_neg_one_of_aeval (hp : p.Prime) (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0)
    (hgd : g ∣ cyclotomic p K) (hpq : p ∣ Nat.card K + 1) {a : ZMod p}
    (ha : aeval (AdjoinRoot.root g ^ a.val) g = 0) : a = 1 ∨ a = -1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hζ := NSFrame.root_isPrimitiveRoot (g := g) hp hpK hgd
  have hav : a.val < p := ZMod.val_lt a
  rcases eq_root_or_eq_root_pow_pred hp hp2 hpK hgd hpq ha with h | h
  · left
    have h1 := hζ.pow_inj hav hp.one_lt (h.trans (pow_one _).symm)
    rw [← ZMod.natCast_zmod_val a, h1, Nat.cast_one]
  · right
    have h1 := hζ.pow_inj hav (Nat.sub_lt hp.pos one_pos) h
    rw [← ZMod.natCast_zmod_val a, h1, Nat.cast_sub hp.one_lt.le, ZMod.natCast_self,
      Nat.cast_one, zero_sub]

end Field

section Frob

variable {K : Type} [Field K] [Fintype K] {g : K[X]} [Fact (Irreducible g)] {p : ℕ}

@[expose] noncomputable def frobL (K : Type) [Field K] [Fintype K] (g : K[X])
    [Fact (Irreducible g)] : AdjoinRoot g ≃ₗ[K] AdjoinRoot g :=
  have : Module.Finite K (AdjoinRoot g) := (CoordSL.rootPB g).finite
  (FiniteField.frobeniusAlgEquivOfAlgebraic K (AdjoinRoot g)).toLinearEquiv

theorem frobL_apply (x : AdjoinRoot g) : frobL K g x = x ^ Fintype.card K := by
  simp only [frobL, AlgEquiv.toLinearEquiv_apply]
  rfl

theorem frobL_mul (x y : AdjoinRoot g) : frobL K g (x * y) = frobL K g x * frobL K g y := by
  rw [frobL_apply, frobL_apply, frobL_apply, mul_pow]

theorem frobL_root_mul (hp : p.Prime) (hpK : (p : K) ≠ 0) (hgd : g ∣ cyclotomic p K)
    (hpq : p ∣ Nat.card K + 1) (u : AdjoinRoot g) :
    frobL K g (AdjoinRoot.root g * u) = AdjoinRoot.root g ^ (p - 1) * frobL K g u := by
  rw [frobL_mul, frobL_apply (AdjoinRoot.root g), ← Nat.card_eq_fintype_card,
    root_pow_card hp hpK hgd hpq]

theorem det_frobL [CharP K 2] (hp : p.Prime) (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0)
    (hgd : g ∣ cyclotomic p K) (hpq : p ∣ Nat.card K + 1) :
    LinearMap.det (frobL K g : AdjoinRoot g →ₗ[K] AdjoinRoot g) = 1 := by
  have : Module.Finite K (AdjoinRoot g) := (CoordSL.rootPB g).finite
  have : Finite (AdjoinRoot g) := Module.finite_of_finite K
  have : Fintype (AdjoinRoot g) := Fintype.ofFinite _
  have hcard : Fintype.card (AdjoinRoot g) = Fintype.card K ^ 2 := by
    rw [Module.card_fintype (CoordSL.rootPB g).basis, Fintype.card_fin,
      rootPB_dim_eq_two hp hp2 hpK hgd hpq]
  have hsq : (frobL K g : AdjoinRoot g →ₗ[K] AdjoinRoot g) *
      (frobL K g : AdjoinRoot g →ₗ[K] AdjoinRoot g) = 1 := by
    refine LinearMap.ext fun x => ?_
    rw [Module.End.mul_apply, LinearEquiv.coe_coe, frobL_apply, frobL_apply,
      ← pow_mul, ← sq, ← hcard, FiniteField.pow_card, Module.End.one_apply]
  have h1 : LinearMap.det (frobL K g : AdjoinRoot g →ₗ[K] AdjoinRoot g) ^ 2 = 1 := by
    rw [sq, ← map_mul, hsq, map_one]
  set d := LinearMap.det (frobL K g : AdjoinRoot g →ₗ[K] AdjoinRoot g)
  have h2 : (d - 1) ^ 2 = 0 := by
    have h3 : (d - 1) ^ 2 = d ^ 2 - 2 * d + 1 := by ring
    rw [h3, h1, CharTwo.two_eq_zero, zero_mul, sub_zero, CharTwo.add_self_eq_zero]
  exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h2)

end Frob

end SpNS

end CFSG.StandardType
