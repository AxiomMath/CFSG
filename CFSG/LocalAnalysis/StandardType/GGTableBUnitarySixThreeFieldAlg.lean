module

public import Mathlib
public import CFSG.LocalAnalysis.StandardType.GGPGLToralityCaseB
import CFSG.HardMathSupport.Malle.Coordinator.CoverThreeNoInner.Rank2GLTools
import CFSG.LieType.SeitzGeneration.UnitaryBlocks
import TauCeti.FieldTheory.Finite.FrobeniusFixed
import CFSG.LieType.SeitzGeneration.NonabHeisThreeCore
import CFSG.LieType.SeitzGeneration.NonabHeisThreeUnitary
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeOrbits
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.StandardType

namespace TableBU63

open Polynomial

section Cubic

variable {K : Type*} [Field K]

theorem irreducible_X_pow_three_sub_C {c : K} (hc : ∀ d : K, d ^ 3 ≠ c) :
    Irreducible (X ^ 3 - C c : K[X]) := by
  have hdeg : (X ^ 3 - C c : K[X]).natDegree = 3 := natDegree_X_pow_sub_C
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; simp)
    fun μ hμ => ?_
  rw [IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hμ
  exact hc μ hμ

variable {c : K} {f : K[X]} [Fact (Irreducible f)]

theorem root_pow_three (hf : f = X ^ 3 - C c) :
    (AdjoinRoot.root f) ^ 3 = algebraMap K (AdjoinRoot f) c := by
  have h1 := AdjoinRoot.aeval_eq (f := f) f
  rw [AdjoinRoot.mk_self] at h1
  have h2 : aeval (AdjoinRoot.root f) f = aeval (AdjoinRoot.root f) (X ^ 3 - C c) :=
    congrArg (aeval (AdjoinRoot.root f)) hf
  rw [h2, map_sub, map_pow, aeval_X, aeval_C] at h1
  exact sub_eq_zero.mp h1

@[expose] noncomputable def cubeTwist (hf : f = X ^ 3 - C c) (t : K) (ht : t ^ 3 = 1) :
    AdjoinRoot f →ₐ[K] AdjoinRoot f :=
  AdjoinRoot.liftAlgHom f (Algebra.ofId K _) (algebraMap K _ t * AdjoinRoot.root f) (by
      change f.eval₂ (algebraMap K (AdjoinRoot f)) _ = 0
      rw [← aeval_def]
      have h2 : aeval (algebraMap K (AdjoinRoot f) t * AdjoinRoot.root f) f =
          aeval (algebraMap K (AdjoinRoot f) t * AdjoinRoot.root f) (X ^ 3 - C c) :=
        congrArg (aeval _) hf
      rw [h2, map_sub, map_pow, aeval_X, aeval_C, mul_pow, root_pow_three hf, ← map_pow, ht,
        map_one, one_mul, sub_self])

theorem cubeTwist_root (hf : f = X ^ 3 - C c) (t : K) (ht : t ^ 3 = 1) :
    cubeTwist hf t ht (AdjoinRoot.root f) = algebraMap K _ t * AdjoinRoot.root f :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

theorem cubeTwist_cubeTwist (hf : f = X ^ 3 - C c) (t t' : K) (ht : t ^ 3 = 1)
    (ht' : t' ^ 3 = 1) (x : AdjoinRoot f) :
    cubeTwist hf t ht (cubeTwist hf t' ht' x) =
      cubeTwist hf (t * t') (by rw [mul_pow, ht, ht', one_mul]) x := by
  have e : (cubeTwist hf t ht).comp (cubeTwist hf t' ht') =
      cubeTwist hf (t * t') (by rw [mul_pow, ht, ht', one_mul]) := by
    apply AdjoinRoot.algHom_ext
    rw [AlgHom.comp_apply, cubeTwist_root, map_mul, cubeTwist_root, AlgHom.commutes, cubeTwist_root,
      map_mul]
    ring
  rw [← e, AlgHom.comp_apply]

theorem eq_algebraMap_of_cubeTwist (hf : f = X ^ 3 - C c) {t : K} (ht : t ^ 3 = 1) (ht1 : t ≠ 1)
    {μ : AdjoinRoot f} (hμ : cubeTwist hf t ht μ = μ) :
    ∃ k : K, μ = algebraMap K _ k := by
  classical
  have hf0 : f ≠ 0 := by rw [hf]; exact X_pow_sub_C_ne_zero (by norm_num) c
  set pb := AdjoinRoot.powerBasis hf0 with hpb
  have hdim : pb.dim = 3 := by rw [hpb, AdjoinRoot.powerBasis_dim, hf, natDegree_X_pow_sub_C]
  have ht2 : t ^ 2 ≠ 1 := fun h2 => ht1 (by rw [pow_succ, h2, one_mul] at ht; exact ht)
  have hgen : pb.gen = AdjoinRoot.root f := AdjoinRoot.powerBasis_gen hf0
  have hσb : ∀ i, cubeTwist hf t ht (pb.basis i) = t ^ (i : ℕ) • pb.basis i := by
    intro i
    rw [PowerBasis.coe_basis]
    simp only
    rw [hgen, map_pow, cubeTwist_root, mul_pow, ← map_pow, Algebra.smul_def]
  set r := pb.basis.repr μ with hr
  have hsum : ∑ i, r i • pb.basis i = μ := pb.basis.sum_repr μ
  have hzero : ∑ i, (r i * t ^ (i : ℕ) - r i) • pb.basis i = 0 := by
    have e1 : cubeTwist hf t ht μ = ∑ i, (r i * t ^ (i : ℕ)) • pb.basis i := by
      conv_lhs => rw [← hsum]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, hσb, smul_smul]
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [← e1, hsum, hμ, sub_self]
  have hcoef := Fintype.linearIndependent_iff.mp pb.basis.linearIndependent _ hzero
  set i₀ : Fin pb.dim := ⟨0, by omega⟩ with hi₀
  refine ⟨r i₀, ?_⟩
  rw [← hsum, Finset.sum_eq_single i₀]
  · rw [PowerBasis.coe_basis]
    simp only [hi₀, pow_zero, Algebra.smul_def, mul_one]
  · intro i _ hi
    have hi' : (i : ℕ) = 1 ∨ (i : ℕ) = 2 := by
      have := i.2
      have : (i : ℕ) ≠ 0 := fun h0 => hi (Fin.ext (by rw [h0]))
      omega
    have hti : t ^ (i : ℕ) ≠ 1 := by
      rcases hi' with h1 | h1 <;> rw [h1]
      · simpa using ht1
      · exact ht2
    have h1 := hcoef i
    have h2 : r i * (t ^ (i : ℕ) - 1) = 0 := by rw [mul_sub, mul_one]; exact h1
    rw [(mul_eq_zero.mp h2).resolve_right (sub_ne_zero.mpr hti), zero_smul]
  · intro h
    exact absurd (Finset.mem_univ _) h

omit [Fact (Irreducible f)] in
theorem eq_algebraMap_of_pow_three_eq_one {L : Type*} [Field L] [Algebra K L] {ω : K}
    (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) {y : L} (hy : y ^ 3 = 1) :
    ∃ i : ℕ, y = algebraMap K L (ω ^ i) := by
  have hω0 : ω ≠ 0 := by
    rintro rfl
    norm_num at hω3
  have hq : ω ^ 2 + ω + 1 = 0 := by
    have h1 : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by
      calc (ω - 1) * (ω ^ 2 + ω + 1) = ω ^ 3 - 1 := by ring
        _ = 0 := by rw [hω3, sub_self]
    exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hω1)
  set w := algebraMap K L ω with hw
  have hq' : w ^ 2 + w + 1 = 0 := by
    rw [hw, ← map_pow, ← map_add, ← map_one (algebraMap K L), ← map_add, hq, map_zero]
  have hw3 : w ^ 3 = 1 := by rw [hw, ← map_pow, hω3, map_one]
  have hfac : (y - 1) * (y - w) * (y - w ^ 2) = 0 := by
    have e : (y - 1) * (y - w) * (y - w ^ 2) =
        y ^ 3 - (w ^ 2 + w + 1) * y ^ 2 + (w ^ 2 + w + 1) * w * y - w ^ 3 := by ring
    rw [e, hq', hy, hw3]
    ring
  rcases mul_eq_zero.mp hfac with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact ⟨0, by rw [pow_zero, map_one]; exact sub_eq_zero.mp h⟩
    · exact ⟨1, by rw [pow_one]; exact sub_eq_zero.mp h⟩
  · exact ⟨2, by rw [map_pow]; exact sub_eq_zero.mp h⟩

end Cubic

section Finite

variable {K : Type*} [Field K] [Finite K] {c : K} {f : K[X]} [Fact (Irreducible f)]

theorem exists_eq_mul_root_pow (hf : f = X ^ 3 - C c) (hc : ∀ d : K, d ^ 3 ≠ c)
    (h3 : 3 ∣ Nat.card K - 1) {b : AdjoinRoot f} {k : Kˣ} (hb : b ^ 3 = algebraMap K _ (k : K)) :
    ∃ (d : K) (j : ℕ), b = algebraMap K _ d * AdjoinRoot.root f ^ j := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc0 : c ≠ 0 := fun h0 => hc 0 (by rw [h0]; ring)
  set cu : Kˣ := Units.mk0 c hc0 with hcu
  set q₁ : TypeA.PGLTor.PowQuot K 3 := (QuotientGroup.mk cu : TypeA.PGLTor.PowQuot K 3) with hq₁
  have hq₁1 : q₁ ≠ 1 := by
    intro h1
    obtain ⟨d, hd⟩ := TypeA.PGLTor.powQuot_mk_eq_one_iff.mp h1
    exact hc d (by rw [← Units.val_pow_eq_pow_val, hd, hcu, Units.val_mk0])
  have hq₁3 : q₁ ^ 3 = 1 := by
    rw [hq₁, ← QuotientGroup.mk_pow, TypeA.PGLTor.powQuot_mk_eq_one_iff]
    exact ⟨cu, rfl⟩
  have hord : orderOf q₁ = 3 := orderOf_eq_prime hq₁3 hq₁1
  have htop : Subgroup.zpowers q₁ = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hord]
    have h1 := orderOf_dvd_natCard q₁
    rw [hord] at h1
    have h2 := TypeA.PGLTor.card_powQuot_le (K := K) (p := 3)
    have hpos : 0 < Nat.card (TypeA.PGLTor.PowQuot K 3) := Nat.card_pos
    omega
  have hkmem : (QuotientGroup.mk k : TypeA.PGLTor.PowQuot K 3) ∈ Subgroup.zpowers q₁ :=
    htop ▸ Subgroup.mem_top _
  rw [← mem_powers_iff_mem_zpowers] at hkmem
  obtain ⟨j, hj⟩ := hkmem
  have hj' : (QuotientGroup.mk (cu ^ j) : TypeA.PGLTor.PowQuot K 3) = QuotientGroup.mk k := by
    rw [QuotientGroup.mk_pow]
    exact hj
  rw [QuotientGroup.eq] at hj'
  obtain ⟨d, hd⟩ := hj'
  have hd' : (d : K) ^ 3 * c ^ j = k := by
    have e := congrArg Units.val hd
    simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mul,
      Units.val_inv_eq_inv_val, hcu, Units.val_mk0] at e
    rw [e]
    field_simp
  obtain ⟨ω, hω⟩ := TypeA.PGLTor.exists_isPrimitiveRoot_of_dvd Nat.prime_three h3
  set r := AdjoinRoot.root f with hr
  have hdr : (algebraMap K _ (d : K) * r ^ j) ^ 3 = algebraMap K _ (k : K) := by
    rw [mul_pow, ← map_pow, ← pow_mul, mul_comm j 3, pow_mul, hr, root_pow_three hf, ← map_pow,
      ← map_mul, hd']
  have hk0 : algebraMap K (AdjoinRoot f) (k : K) ≠ 0 :=
    (_root_.map_ne_zero _).mpr k.ne_zero
  have hne : algebraMap K _ (d : K) * r ^ j ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num)] at hdr
    exact hk0 hdr.symm
  set y := b * (algebraMap K _ (d : K) * r ^ j)⁻¹ with hy
  have hy3 : y ^ 3 = 1 := by
    rw [hy, mul_pow, inv_pow, hb, hdr, mul_inv_cancel₀ hk0]
  obtain ⟨i, hi⟩ := eq_algebraMap_of_pow_three_eq_one hω.pow_eq_one
    (hω.ne_one (by norm_num)) hy3
  refine ⟨(d : K) * ω ^ i, j, ?_⟩
  have hb' : b = y * (algebraMap K _ (d : K) * r ^ j) := by
    rw [hy, mul_assoc, inv_mul_cancel₀ hne, mul_one]
  rw [hb', hi, map_mul]
  ring

theorem exists_pow_eq_one_not_mem (hf : f = X ^ 3 - C c) {q : ℕ} (hq : 2 ≤ q)
    (hK : Nat.card K = q ^ 2) :
    ∃ μ : AdjoinRoot f, μ ^ (q ^ 3 + 1) = 1 ∧ ∀ k : K, algebraMap K _ k ≠ μ := by
  have hf0 : f ≠ 0 := by rw [hf]; exact X_pow_sub_C_ne_zero (by norm_num) c
  have : Module.Finite K (AdjoinRoot f) := (AdjoinRoot.powerBasis hf0).finite
  have : Finite (AdjoinRoot f) := Module.finite_of_finite K
  have hfin : Module.finrank K (AdjoinRoot f) = 3 := by
    rw [(AdjoinRoot.powerBasis hf0).finrank, AdjoinRoot.powerBasis_dim, hf, natDegree_X_pow_sub_C]
  have hE : Nat.card (AdjoinRoot f) = q ^ 6 := by
    rw [Module.natCard_eq_pow_finrank (K := K), hK, hfin, ← pow_mul]
  obtain ⟨ξ, hξ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (AdjoinRoot f)ˣ)
  have hEu : Nat.card (AdjoinRoot f)ˣ = q ^ 6 - 1 := by
    rw [Nat.card_units, hE]
  have hq3 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hsplit : q ^ 6 - 1 = (q ^ 3 + 1) * (q ^ 3 - 1) := by
    have h := Nat.mul_self_sub_mul_self_eq (q ^ 3) 1
    rw [mul_one, ← pow_add] at h
    exact h
  have hdvd : q ^ 3 + 1 ∣ orderOf ξ := by
    rw [hξ, hEu, hsplit]
    exact dvd_mul_right _ _
  have hξ0 : orderOf ξ ≠ 0 := by
    rw [hξ, hEu]
    have : 2 ^ 6 ≤ q ^ 6 := Nat.pow_le_pow_left hq 6
    omega
  set μu := ξ ^ (orderOf ξ / (q ^ 3 + 1)) with hμu
  have hμord : orderOf μu = q ^ 3 + 1 := orderOf_pow_orderOf_div hξ0 hdvd
  refine ⟨(μu : AdjoinRoot f), ?_, fun k hk => ?_⟩
  · rw [← Units.val_pow_eq_pow_val, ← hμord, pow_orderOf_eq_one, Units.val_one]
  · have hk0 : k ≠ 0 := by
      rintro rfl
      rw [map_zero] at hk
      exact μu.ne_zero hk.symm
    set ku := Units.mk0 k hk0 with hku
    have hkpow : ku ^ (q ^ 2 - 1) = 1 := by
      rw [← hK, ← Nat.card_units K]
      exact pow_card_eq_one'
    have hμ1 : μu ^ (q ^ 2 - 1) = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, ← hk, ← map_pow, Units.val_one]
      have e := congrArg Units.val hkpow
      rw [Units.val_pow_eq_pow_val, hku, Units.val_mk0, Units.val_one] at e
      rw [e, map_one]
    have h1 := orderOf_dvd_of_pow_eq_one hμ1
    rw [hμord] at h1
    have hpos : 0 < q ^ 2 - 1 := by
      have : 2 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
      omega
    have h2 := Nat.le_of_dvd hpos h1
    have h3 : q ^ 2 ≤ q ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
    omega

end Finite

end TableBU63

end CFSG.StandardType
