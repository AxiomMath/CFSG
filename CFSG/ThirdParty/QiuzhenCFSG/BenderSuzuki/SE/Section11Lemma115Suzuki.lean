module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.Suzuki
public import Mathlib.RingTheory.Trace.Basic
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.theorem_3_3
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.FieldTheory.Perfect
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.LinearAlgebra.Quotient.Card

namespace CFSG
end CFSG
open CFSG

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

/-!
# Section 11, Lemma 11.5: the Suzuki order-five endpoint

This file develops the direct concrete-matrix replacement for the remaining
`[II4; 3.7, 3.8]` source input.  The first ingredient is an elementary
characteristic-two count for the zero set of a quadratic function.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open MatrixGroups

private theorem lemma115_zmodTwo_eq_zero_or_one (z : ZMod 2) :
    z = 0 ∨ z = 1 := by
  have hz : z.val = 0 ∨ z.val = 1 := by
    have := z.val_lt
    omega
  rcases hz with hz | hz
  · left
    apply ZMod.val_injective
    simpa using hz
  · right
    apply ZMod.val_injective
    simpa [ZMod.val_one] using hz

private theorem lemma115_quadratic_zero_cover
    {V : Type*} [AddCommGroup V] [Finite V]
    (Q : V → ZMod 2) (a : V) (hQa : Q a = 1)
    (L : V →+ ZMod 2)
    (htranslate : ∀ x, Q (x + a) = Q x + Q a + L x) :
    Nat.card V ≤ 4 * Nat.card {x : V // Q x = 0} := by
  classical
  by_cases hL : L = 0
  · let cover : {x : V // Q x = 0} × Fin 4 → V := fun z =>
      ![(z.1 : V), (z.1 : V) - a, (z.1 : V), (z.1 : V)] z.2
    have hcover : Function.Surjective cover := by
      intro x
      rcases lemma115_zmodTwo_eq_zero_or_one (Q x) with hx | hx
      · exact ⟨(⟨x, hx⟩, 0), rfl⟩
      · refine ⟨(⟨x + a, ?_⟩, 1), ?_⟩
        · rw [htranslate, hL]
          simpa [hx, hQa] using
            (CharTwo.add_self_eq_zero (1 : ZMod 2))
        · simp [cover]
    have hcard := Nat.card_le_card_of_surjective cover hcover
    simpa [Nat.card_prod, Nat.mul_comm] using hcard
  · obtain ⟨b, hb⟩ : ∃ b, L b = 1 := by
      have hexists : ∃ b, L b ≠ 0 := by
        by_contra h
        push_neg at h
        apply hL
        ext b
        exact h b
      obtain ⟨b, hb⟩ := hexists
      refine ⟨b, ?_⟩
      rcases lemma115_zmodTwo_eq_zero_or_one (L b) with hzero | hone
      · exact (hb hzero).elim
      · exact hone
    let cover : {x : V // Q x = 0} × Fin 4 → V := fun z =>
      ![(z.1 : V), (z.1 : V) - a,
        (z.1 : V) + b, (z.1 : V) - a + b] z.2
    have hcover : Function.Surjective cover := by
      intro x
      rcases lemma115_zmodTwo_eq_zero_or_one (L x) with hLx | hLx
      · rcases lemma115_zmodTwo_eq_zero_or_one (Q x) with hx | hx
        · exact ⟨(⟨x, hx⟩, 0), rfl⟩
        · refine ⟨(⟨x + a, ?_⟩, 1), ?_⟩
          · rw [htranslate, hx, hQa, hLx]
            decide
          · simp [cover]
      · let y := x - b
        have hLy : L y = 0 := by
          simp [y, map_sub, hLx, hb]
        rcases lemma115_zmodTwo_eq_zero_or_one (Q y) with hy | hy
        · refine ⟨(⟨y, hy⟩, 2), ?_⟩
          simp [cover, y]
        · refine ⟨(⟨y + a, ?_⟩, 3), ?_⟩
          · rw [htranslate, hy, hQa, hLy]
            decide
          · simp [cover, y]
    have hcard := Nat.card_le_card_of_surjective cover hcover
    simpa [Nat.card_prod, Nat.mul_comm] using hcard

/-- A quadratic function to `ZMod 2` has at least one quarter of its finite
domain as zeros.  The hypothesis packages the additive polar derivative of
`Q` in each direction. -/
public theorem lemma115_quadratic_trace_zero_count
    {V : Type*} [AddCommGroup V] [Finite V]
    (Q : V → ZMod 2)
    (hpolar : ∀ a : V, ∃ L : V →+ ZMod 2,
      ∀ x, Q (x + a) = Q x + Q a + L x) :
    Nat.card V ≤ 4 * Nat.card {x : V // Q x = 0} := by
  classical
  by_cases hQ : ∀ x, Q x = 0
  · let lift : V → {x : V // Q x = 0} := fun x => ⟨x, hQ x⟩
    have hlift : Function.Injective lift := by
      intro x y hxy
      exact congrArg Subtype.val hxy
    have hcard := Nat.card_le_card_of_injective lift hlift
    omega
  · push_neg at hQ
    obtain ⟨a, ha⟩ := hQ
    have hQa : Q a = 1 :=
      (lemma115_zmodTwo_eq_zero_or_one (Q a)).resolve_left ha
    obtain ⟨L, hL⟩ := hpolar a
    exact lemma115_quadratic_zero_cover Q a hQa L hL

/-- Over an odd-degree binary Galois field, every trace-zero element has
exactly two Artin--Schreier preimages. -/
public theorem lemma115_artinSchreier_fiber_card_two
    (m : ℕ) (c : PFAppendixIII.BinaryGaloisField (2 * m + 1))
    (hc : Algebra.trace (ZMod 2)
      (PFAppendixIII.BinaryGaloisField (2 * m + 1)) c = 0) :
    Nat.card {d : PFAppendixIII.BinaryGaloisField (2 * m + 1) //
      d ^ 2 + d = c} = 2 := by
  classical
  let K := PFAppendixIII.BinaryGaloisField (2 * m + 1)
  let frob : K ≃+* K := iterateFrobeniusEquiv K 2 1
  let frobAlg : K ≃ₐ[ZMod 2] K :=
    AlgEquiv.ofRingEquiv (f := frob) (fun x => by
      have hcomp : frob.toRingHom.comp (algebraMap (ZMod 2) K) =
          algebraMap (ZMod 2) K := Subsingleton.elim _ _
      exact DFunLike.congr_fun hcomp x)
  let AS : K →ₗ[ZMod 2] K := frobAlg.toLinearMap - LinearMap.id
  let tr : K →ₗ[ZMod 2] ZMod 2 := Algebra.trace (ZMod 2) K
  have hfrob (x : K) : frobAlg x = x ^ 2 := by
    exact iterateFrobeniusEquiv_def K 2 1 x
  have hAS (x : K) : AS x = x ^ 2 + x := by
    simp [AS, hfrob, CharTwo.sub_eq_add]
  have hker_mem_iff (x : K) : x ∈ AS.ker ↔ x = 0 ∨ x = 1 := by
    rw [LinearMap.mem_ker, hAS]
    constructor
    · intro hx
      have hfactor : x * (x + 1) = 0 := by
        calc
          x * (x + 1) = x ^ 2 + x := by ring
          _ = 0 := hx
      rcases mul_eq_zero.mp hfactor with hx0 | hx1
      · exact Or.inl hx0
      · right
        calc
          x = -1 := eq_neg_of_add_eq_zero_left hx1
          _ = 1 := CharTwo.neg_eq 1
    · rintro (rfl | rfl)
      · simp
      · simpa using CharTwo.add_self_eq_zero (1 : K)
  let base : ZMod 2 →ₗ[ZMod 2] K := Algebra.linearMap (ZMod 2) K
  let baseKer : ZMod 2 →ₗ[ZMod 2] AS.ker :=
    base.codRestrict AS.ker (fun z => by
      rw [hker_mem_iff]
      rcases lemma115_zmodTwo_eq_zero_or_one z with rfl | rfl
      · exact Or.inl (map_zero (algebraMap (ZMod 2) K))
      · exact Or.inr (map_one (algebraMap (ZMod 2) K)))
  have hbaseKerBij : Function.Bijective baseKer := by
    constructor
    · intro x y hxy
      apply (algebraMap (ZMod 2) K).injective
      exact congrArg Subtype.val hxy
    · intro x
      rcases (hker_mem_iff x).mp x.property with hx | hx
      · refine ⟨0, ?_⟩
        apply Subtype.ext
        simpa [baseKer, base] using hx.symm
      · refine ⟨1, ?_⟩
        apply Subtype.ext
        simpa [baseKer, base] using hx.symm
  let eKer : ZMod 2 ≃ₗ[ZMod 2] AS.ker :=
    LinearEquiv.ofBijective baseKer hbaseKerBij
  have hkerCard : Nat.card AS.ker = 2 := by
    calc
      Nat.card AS.ker = Nat.card (ZMod 2) :=
        Nat.card_congr eKer.symm.toEquiv
      _ = 2 := Nat.card_zmod 2
  have hrange_le : AS.range ≤ tr.ker := by
    rintro y ⟨x, rfl⟩
    rw [LinearMap.mem_ker]
    change tr (frobAlg x - x) = 0
    rw [map_sub, Algebra.trace_eq_of_algEquiv frobAlg x]
    exact sub_self _
  have htr_surj : Function.Surjective tr :=
    Algebra.trace_surjective (ZMod 2) K
  have htr_range : tr.range = ⊤ := LinearMap.range_eq_top.mpr htr_surj
  have hquotAS : Nat.card (K ⧸ AS.ker) = Nat.card AS.range :=
    Nat.card_congr (LinearMap.quotKerEquivRange AS).toEquiv
  have hquotTr : Nat.card (K ⧸ tr.ker) = 2 := by
    calc
      Nat.card (K ⧸ tr.ker) = Nat.card tr.range :=
        Nat.card_congr (LinearMap.quotKerEquivRange tr).toEquiv
      _ = Nat.card (ZMod 2) := by simp [htr_range]
      _ = 2 := Nat.card_zmod 2
  have hcardAS := Submodule.card_eq_card_quotient_mul_card AS.ker
  have hcardTr := Submodule.card_eq_card_quotient_mul_card tr.ker
  have hrangeCard : Nat.card AS.range = Nat.card tr.ker := by
    rw [hkerCard, hquotAS] at hcardAS
    rw [hquotTr] at hcardTr
    omega
  have hrange_eq : AS.range = tr.ker := by
    apply SetLike.coe_injective
    apply Set.Finite.eq_of_subset_of_card_le (Set.toFinite _)
    · exact hrange_le
    · simpa using hrangeCard.symm.le
  have hcKer : c ∈ tr.ker := by
    simpa [tr, K, LinearMap.mem_ker] using hc
  have hcRange : c ∈ AS.range := by
    rw [hrange_eq]
    exact hcKer
  rcases hcRange with ⟨d₀, hd₀⟩
  have hfiber : Nat.card {d : K // AS d = AS d₀} = Nat.card AS.ker := by
    exact Nat.card_congr
      (AddMonoidHom.fiberEquivKer AS.toAddMonoidHom d₀)
  rw [hkerCard] at hfiber
  have hd₀c : AS d₀ = c := hd₀
  rw [← hd₀c]
  simpa [K, hAS] using hfiber

private theorem lemma115_suzuki_trace_zero_count (m : ℕ) :
    let K := PFAppendixIII.BinaryGaloisField (2 * m + 1)
    let theta : K ≃+* K := iterateFrobeniusEquiv K 2 (m + 1)
    let tr := Algebra.trace (ZMod 2) K
    let Q : K → ZMod 2 := fun a => tr (a * theta a + a)
    Nat.card K ≤ 4 * Nat.card {a : K // Q a = 0} := by
  let K := PFAppendixIII.BinaryGaloisField (2 * m + 1)
  let theta : K ≃+* K := iterateFrobeniusEquiv K 2 (m + 1)
  let tr : K →ₗ[ZMod 2] ZMod 2 := Algebra.trace (ZMod 2) K
  let Q : K → ZMod 2 := fun a => tr (a * theta a + a)
  apply lemma115_quadratic_trace_zero_count Q
  intro a
  let L : K →+ ZMod 2 :=
    { toFun := fun x => tr (x * theta a + a * theta x)
      map_zero' := by simp
      map_add' := by
        intro x y
        change tr ((x + y) * theta a + a * theta (x + y)) =
          tr (x * theta a + a * theta x) +
            tr (y * theta a + a * theta y)
        rw [theta.map_add]
        have hinside :
            (x + y) * theta a + a * (theta x + theta y) =
              (x * theta a + a * theta x) +
                (y * theta a + a * theta y) := by ring
        rw [hinside, map_add] }
  refine ⟨L, ?_⟩
  intro x
  change tr ((x + a) * theta (x + a) + (x + a)) =
    tr (x * theta x + x) + tr (a * theta a + a) +
      tr (x * theta a + a * theta x)
  rw [theta.map_add]
  have hinside :
      (x + a) * (theta x + theta a) + (x + a) =
        (x * theta x + x) + (a * theta a + a) +
          (x * theta a + a * theta x) := by ring
  rw [hinside]
  simp only [map_add]

private theorem lemma115_suzuki_artinSchreier_rhs_trace_zero
    (m : ℕ) (a : PFAppendixIII.BinaryGaloisField (2 * m + 1)) :
    Algebra.trace (ZMod 2) (PFAppendixIII.BinaryGaloisField (2 * m + 1))
      (iterateFrobeniusEquiv
          (PFAppendixIII.BinaryGaloisField (2 * m + 1)) 2 (m + 1) a *
        (a ^ 2 + a + 1) + a ^ 2) = 0 := by
  let K := PFAppendixIII.BinaryGaloisField (2 * m + 1)
  let theta : K ≃+* K := iterateFrobeniusEquiv K 2 (m + 1)
  let thetaAlg : K ≃ₐ[ZMod 2] K :=
    AlgEquiv.ofRingEquiv (f := theta) (fun x => by
      have hcomp : theta.toRingHom.comp (algebraMap (ZMod 2) K) =
          algebraMap (ZMod 2) K := Subsingleton.elim _ _
      exact DFunLike.congr_fun hcomp x)
  let tr : K →ₗ[ZMod 2] ZMod 2 := Algebra.trace (ZMod 2) K
  have hthetaSq : ∀ x : K, theta (theta x) = x ^ 2 :=
    External.binaryGaloisField_tits_formula_sq m theta (fun x => rfl)
  have htrace_theta (x : K) : tr (theta x) = tr x := by
    exact Algebra.trace_eq_of_algEquiv thetaAlg x
  have htrace_sq (x : K) : tr (x ^ 2) = tr x := by
    calc
      tr (x ^ 2) = tr (theta (theta x)) := by rw [hthetaSq]
      _ = tr (theta x) := htrace_theta (theta x)
      _ = tr x := htrace_theta x
  change tr (theta a * (a ^ 2 + a + 1) + a ^ 2) = 0
  have htraceProd : tr (theta a * a ^ 2) = tr (a * theta a) := by
    calc
      tr (theta a * a ^ 2) = tr (theta (a * theta a)) := by
        congr 1
        rw [map_mul, hthetaSq]
      _ = tr (a * theta a) := htrace_theta (a * theta a)
  calc
    tr (theta a * (a ^ 2 + a + 1) + a ^ 2) =
        tr (theta a * a ^ 2) + tr (theta a * a) +
          tr (theta a) + tr (a ^ 2) := by
      have hin :
          theta a * (a ^ 2 + a + 1) + a ^ 2 =
            theta a * a ^ 2 + theta a * a + theta a + a ^ 2 := by
        ring
      rw [hin, map_add, map_add, map_add]
    _ = tr (a * theta a) + tr (a * theta a) + tr a + tr a := by
      rw [htraceProd, mul_comm (theta a) a, htrace_theta, htrace_sq]
    _ = 0 := by
      rw [CharTwo.add_self_eq_zero, zero_add, CharTwo.add_self_eq_zero]

private theorem lemma115_suzuki_parameter_unit_ne_zero
    (m : ℕ) (a : PFAppendixIII.BinaryGaloisField (2 * m + 1)) :
    a ^ 2 + a + 1 ≠ 0 := by
  let K := PFAppendixIII.BinaryGaloisField (2 * m + 1)
  let tr : K →ₗ[ZMod 2] ZMod 2 := Algebra.trace (ZMod 2) K
  let frob : K ≃+* K := iterateFrobeniusEquiv K 2 1
  let frobAlg : K ≃ₐ[ZMod 2] K :=
    AlgEquiv.ofRingEquiv (f := frob) (fun x => by
      have hcomp : frob.toRingHom.comp (algebraMap (ZMod 2) K) =
          algebraMap (ZMod 2) K := Subsingleton.elim _ _
      exact DFunLike.congr_fun hcomp x)
  have hfrob (x : K) : frobAlg x = x ^ 2 :=
    iterateFrobeniusEquiv_def K 2 1 x
  have htrace_sq (x : K) : tr (x ^ 2) = tr x := by
    calc
      tr (x ^ 2) = tr (frobAlg x) := by rw [hfrob]
      _ = tr x := Algebra.trace_eq_of_algEquiv frobAlg x
  have hfinrank : Module.finrank (ZMod 2) K = 2 * m + 1 := by
    simpa [K, PFAppendixIII.BinaryGaloisField] using
      GaloisField.finrank 2 (show 2 * m + 1 ≠ 0 by omega)
  have htrace_one : tr (1 : K) = 1 := by
    have h := Algebra.trace_algebraMap
      (R := ZMod 2) (S := K) (1 : ZMod 2)
    change tr (1 : K) = 1
    rw [show tr (1 : K) = (Module.finrank (ZMod 2) K : ZMod 2) by
      simpa using h, hfinrank]
    norm_num [Nat.cast_add, Nat.cast_mul]
    exact Or.inl (CharP.cast_eq_zero (ZMod 2) 2)
  change a ^ 2 + a + 1 ≠ 0
  intro ha
  have h := congrArg tr ha
  rw [map_add, map_add, htrace_sq, htrace_one,
    CharTwo.add_self_eq_zero, zero_add] at h
  rw [map_zero] at h
  exact one_ne_zero h

private theorem lemma115_suzuki_artinSchreier_theta_relation
    (m : ℕ)
    (a d : PFAppendixIII.BinaryGaloisField (2 * m + 1))
    (ha : Algebra.trace (ZMod 2)
      (PFAppendixIII.BinaryGaloisField (2 * m + 1))
      (a * iterateFrobeniusEquiv
        (PFAppendixIII.BinaryGaloisField (2 * m + 1)) 2 (m + 1) a + a) = 0)
    (hd : d ^ 2 + d =
      iterateFrobeniusEquiv
          (PFAppendixIII.BinaryGaloisField (2 * m + 1)) 2 (m + 1) a *
        (a ^ 2 + a + 1) + a ^ 2) :
    iterateFrobeniusEquiv
        (PFAppendixIII.BinaryGaloisField (2 * m + 1)) 2 (m + 1) d + d =
      (a + 1) * iterateFrobeniusEquiv
        (PFAppendixIII.BinaryGaloisField (2 * m + 1)) 2 (m + 1) a := by
  let K := PFAppendixIII.BinaryGaloisField (2 * m + 1)
  let theta : K ≃+* K := iterateFrobeniusEquiv K 2 (m + 1)
  let thetaAlg : K ≃ₐ[ZMod 2] K :=
    AlgEquiv.ofRingEquiv (f := theta) (fun x => by
      have hcomp : theta.toRingHom.comp (algebraMap (ZMod 2) K) =
          algebraMap (ZMod 2) K := Subsingleton.elim _ _
      exact DFunLike.congr_fun hcomp x)
  let tr : K →ₗ[ZMod 2] ZMod 2 := Algebra.trace (ZMod 2) K
  have hthetaSq : ∀ x : K, theta (theta x) = x ^ 2 :=
    External.binaryGaloisField_tits_formula_sq m theta (fun x => rfl)
  have htrace_theta (x : K) : tr (theta x) = tr x :=
    Algebra.trace_eq_of_algEquiv thetaAlg x
  have hfinrank : Module.finrank (ZMod 2) K = 2 * m + 1 := by
    simpa [K, PFAppendixIII.BinaryGaloisField] using
      GaloisField.finrank 2 (show 2 * m + 1 ≠ 0 by omega)
  have htrace_one : tr (1 : K) = 1 := by
    have h := Algebra.trace_algebraMap
      (R := ZMod 2) (S := K) (1 : ZMod 2)
    change tr (1 : K) = 1
    rw [show tr (1 : K) = (Module.finrank (ZMod 2) K : ZMod 2) by
      simpa using h, hfinrank]
    norm_num [Nat.cast_add, Nat.cast_mul]
    exact Or.inl (CharP.cast_eq_zero (ZMod 2) 2)
  change theta d + d = (a + 1) * theta a
  change tr (a * theta a + a) = 0 at ha
  change d ^ 2 + d = theta a * (a ^ 2 + a + 1) + a ^ 2 at hd
  have hdtheta := congrArg theta hd
  simp only [map_add, map_mul, map_pow, map_one] at hdtheta
  rw [hthetaSq a] at hdtheta
  have hpoly :
      (theta d + d) ^ 2 + (theta d + d) =
        ((a + 1) * theta a) ^ 2 + (a + 1) * theta a := by
    calc
      (theta d + d) ^ 2 + (theta d + d) =
          (theta d ^ 2 + theta d) + (d ^ 2 + d) := by
        rw [CharTwo.add_sq]
        ring
      _ =
          (a ^ 2 * (theta a ^ 2 + theta a + 1) + theta a ^ 2) +
            (theta a * (a ^ 2 + a + 1) + a ^ 2) := by
        rw [hdtheta, hd]
      _ = ((a + 1) * theta a) ^ 2 + (a + 1) * theta a := by
        rw [mul_pow, CharTwo.add_sq, one_pow]
        ring_nf
        rw [show (2 : K) = 0 by exact CharP.cast_eq_zero K 2]
        simp
  let z : K := (theta d + d) + (a + 1) * theta a
  have hzpoly : z ^ 2 + z = 0 := by
    dsimp [z]
    rw [CharTwo.add_sq]
    have hreorder :
        (theta d + d) ^ 2 + ((a + 1) * theta a) ^ 2 +
            ((theta d + d) + (a + 1) * theta a) =
          ((theta d + d) ^ 2 + (theta d + d)) +
            (((a + 1) * theta a) ^ 2 + (a + 1) * theta a) := by
      ring
    rw [hreorder, hpoly, CharTwo.add_self_eq_zero]
  have hzCases : z = 0 ∨ z = 1 := by
    have hfactor : z * (z + 1) = 0 := by
      calc
        z * (z + 1) = z ^ 2 + z := by ring
        _ = 0 := hzpoly
    rcases mul_eq_zero.mp hfactor with hz | hz
    · exact Or.inl hz
    · right
      calc
        z = -1 := eq_neg_of_add_eq_zero_left hz
        _ = 1 := CharTwo.neg_eq 1
  rcases hzCases with hz | hz
  · dsimp [z] at hz
    exact eq_neg_of_add_eq_zero_left hz |>.trans (CharTwo.neg_eq _)
  · have htraceZ : tr z = 0 := by
      dsimp [z]
      rw [map_add, map_add, htrace_theta, CharTwo.add_self_eq_zero,
        zero_add]
      have hr : tr ((a + 1) * theta a) = 0 := by
        calc
          tr ((a + 1) * theta a) = tr (a * theta a + theta a) := by
            congr 1
            ring
          _ = tr (a * theta a) + tr a := by
            rw [map_add, htrace_theta]
          _ = tr (a * theta a + a) := by rw [map_add]
          _ = 0 := ha
      exact hr
    rw [hz, htrace_one] at htraceZ
    exact (one_ne_zero htraceZ).elim

private theorem lemma115_suzuki_parameter_card_lower_bound (m : ℕ) :
    let K := PFAppendixIII.BinaryGaloisField (2 * m + 1)
    let theta : K ≃+* K := iterateFrobeniusEquiv K 2 (m + 1)
    let tr := Algebra.trace (ZMod 2) K
    let Z := {a : K // tr (a * theta a + a) = 0}
    let D : Z → Type := fun a =>
      {d : K // d ^ 2 + d =
        theta a * (a ^ 2 + a + 1) + a ^ 2}
    let Param := Σ a : Z, D a
    2 ^ (2 * m) ≤ Nat.card Param := by
  classical
  let K := PFAppendixIII.BinaryGaloisField (2 * m + 1)
  let theta : K ≃+* K := iterateFrobeniusEquiv K 2 (m + 1)
  let tr : K →ₗ[ZMod 2] ZMod 2 := Algebra.trace (ZMod 2) K
  let Z := {a : K // tr (a * theta a + a) = 0}
  let D : Z → Type := fun a =>
    {d : K // d ^ 2 + d =
      theta a * (a ^ 2 + a + 1) + a ^ 2}
  let Param := Σ a : Z, D a
  change 2 ^ (2 * m) ≤ Nat.card Param
  letI : Fintype Z := Fintype.ofFinite Z
  have hDcard (a : Z) : Nat.card (D a) = 2 := by
    exact lemma115_artinSchreier_fiber_card_two m
      (theta a * (a ^ 2 + a + 1) + a ^ 2)
      (lemma115_suzuki_artinSchreier_rhs_trace_zero m a)
  have hParamCard : Nat.card Param = 2 * Nat.card Z := by
    rw [Nat.card_sigma]
    simp_rw [hDcard]
    simp [Nat.card_eq_fintype_card, Nat.mul_comm]
  have hzero : Nat.card K ≤ 4 * Nat.card Z := by
    simpa [K, theta, tr, Z] using lemma115_suzuki_trace_zero_count m
  have hKcard : Nat.card K = 2 ^ (2 * m + 1) := by
    simpa [K, PFAppendixIII.BinaryGaloisField] using
      GaloisField.card 2 (2 * m + 1) (show 2 * m + 1 ≠ 0 by omega)
  have hpow : 2 ^ (2 * m + 1) = 2 * 2 ^ (2 * m) := by
    rw [pow_succ']
  rw [hParamCard]
  rw [hKcard, hpow] at hzero
  omega

set_option maxHeartbeats 1200000 in
private theorem lemma115_suzuki_commuting_matrix
    (m : ℕ)
    (a d : PFAppendixIII.BinaryGaloisField (2 * m + 1))
    (hd : d ^ 2 + d =
      iterateFrobeniusEquiv
          (PFAppendixIII.BinaryGaloisField (2 * m + 1)) 2 (m + 1) a *
        (a ^ 2 + a + 1) + a ^ 2)
    (hrel : iterateFrobeniusEquiv
          (PFAppendixIII.BinaryGaloisField (2 * m + 1)) 2 (m + 1) d + d =
        (a + 1) * iterateFrobeniusEquiv
          (PFAppendixIII.BinaryGaloisField (2 * m + 1)) 2 (m + 1) a)
    (hu : a ^ 2 + a + 1 ≠ 0) :
    Commute
      (MatrixGroups.SuzukiRootGL m a
          (1 + d + a * iterateFrobeniusEquiv
            (PFAppendixIII.BinaryGaloisField (2 * m + 1)) 2 (m + 1) a) *
        MatrixGroups.SuzukiTorusGL m (Units.mk0 (a ^ 2 + a + 1) hu) *
        MatrixGroups.SuzukiWeylGL m * MatrixGroups.SuzukiRootGL m a d)
      (MatrixGroups.SuzukiRootGL m 0 1 *
        MatrixGroups.SuzukiWeylGL m) := by
  let K := PFAppendixIII.BinaryGaloisField (2 * m + 1)
  let theta : K ≃+* K := iterateFrobeniusEquiv K 2 (m + 1)
  let u : K := a ^ 2 + a + 1
  let b : K := 1 + d + a * theta a
  let r : K := u ^ (2 ^ m)
  change Commute
    (SuzukiRootGL m a b * SuzukiTorusGL m (Units.mk0 u hu) *
      SuzukiWeylGL m * SuzukiRootGL m a d)
    (SuzukiRootGL m 0 1 * SuzukiWeylGL m)
  have htheta (x : K) : x ^ (2 ^ (m + 1)) = theta x := by
    exact (iterateFrobeniusEquiv_def K 2 (m + 1) x).symm
  have hthetaSq (x : K) : theta (theta x) = x ^ 2 :=
    External.binaryGaloisField_tits_formula_sq m theta (fun x => rfl) x
  have hrne : r ≠ 0 := pow_ne_zero _ hu
  have hr : u ^ (2 ^ m) = r := rfl
  have houter : u ^ (1 + 2 ^ m) = u * r := by
    rw [pow_add, pow_one, hr]
  have hpowTwoTheta (x : K) :
      x ^ (2 + 2 ^ (m + 1)) = x ^ 2 * theta x := by
    rw [pow_add, htheta]
  have hpowOneTheta (x : K) :
      x ^ (1 + 2 ^ (m + 1)) = x * theta x := by
    rw [pow_add, pow_one, htheta]
  have hrSq : r ^ 2 = theta u := by
    calc
      r ^ 2 = u ^ (2 ^ m * 2) := by simp [r, pow_mul]
      _ = u ^ (2 ^ (m + 1)) := by rw [pow_succ]
      _ = theta u := htheta u
  have hrel' : theta d = (a + 1) * theta a + d := by
    calc
      theta d = (theta d + d) + d := by
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      _ = (a + 1) * theta a + d := by rw [hrel]
  have hdSq : d ^ 2 = theta a * u + a ^ 2 + d := by
    calc
      d ^ 2 = (d ^ 2 + d) + d := by
        rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      _ = (theta a * u + a ^ 2) + d := by rw [hd]
  have hthetaU : theta u = theta a ^ 2 + theta a + 1 := by
    simp [u, map_add, map_pow]
  have hthetaB : theta b = 1 + d ^ 2 + a ^ 2 := by
    simp only [b, map_add, map_mul, map_one]
    rw [hthetaSq]
    rw [hrel']
    have hd' : theta a * u = d ^ 2 + d + a ^ 2 := by
      calc
        theta a * u = (theta a * u + a ^ 2) + a ^ 2 := by
          rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
        _ = (d ^ 2 + d) + a ^ 2 := by rw [← hd]
    calc
      1 + ((a + 1) * theta a + d) + theta a * a ^ 2 =
          1 + d + theta a * u := by simp only [u]; ring
      _ = 1 + d + (d ^ 2 + d + a ^ 2) := by rw [hd']
      _ = 1 + d ^ 2 + a ^ 2 := by
        calc
          1 + d + (d ^ 2 + d + a ^ 2) =
              1 + d ^ 2 + (d + d) + a ^ 2 := by ring
          _ = 1 + d ^ 2 + a ^ 2 := by
            rw [CharTwo.add_self_eq_zero, add_zero]
  have hchar : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hthree : (3 : K) = 1 := by
    simpa using CharP.cast_eq_mod K 2 3
  have hfour : (4 : K) = 0 := by
    simpa using CharP.cast_eq_mod K 2 4
  have hfive : (5 : K) = 1 := by
    simpa using CharP.cast_eq_mod K 2 5
  have hsix : (6 : K) = 0 := by
    simpa using CharP.cast_eq_mod K 2 6
  have hseven : (7 : K) = 1 := by
    simpa using CharP.cast_eq_mod K 2 7
  have height : (8 : K) = 0 := by
    simpa using CharP.cast_eq_mod K 2 8
  have hnine : (9 : K) = 1 := by
    simpa using CharP.cast_eq_mod K 2 9
  have huReorder : 1 + a + a ^ 2 ≠ 0 := by
    intro h
    apply hu
    calc
      a ^ 2 + a + 1 = 1 + a + a ^ 2 := by ring
      _ = 0 := h
  rw [commute_iff_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SuzukiRootGL, SuzukiRootMatrix, SuzukiTorusGL,
      SuzukiTorusMatrix, SuzukiWeylGL, SuzukiWeylMatrix,
      Matrix.mul_apply, Fin.sum_univ_four, htheta, hpowTwoTheta,
      hpowOneTheta, hthetaB, hr, houter] <;>
    simp [hrel', hdSq, b, u, pow_succ] <;>
    field_simp [hu, huReorder, hrne] <;>
    ring_nf <;>
    simp [hchar, hthree, hfour, hfive, hsix, hseven, height, hnine] <;>
    try simp [hdSq, hrSq, hthetaU, u] <;>
    field_simp [huReorder] <;>
    ring_nf <;>
    simp [hchar, hthree, hfour, hfive, hsix, hseven, height]
  all_goals
    field_simp [huReorder]
    ring_nf
    rw [hchar]
    simp

/-- The standard order-five element used to count a Suzuki centralizer. -/
public noncomputable def lemma115_suzukiStandardElement (m : ℕ) :
    SuzukiMatrixGroup m :=
  ⟨SuzukiRootGL m 0 1 * SuzukiWeylGL m,
    (SuzukiMatrixSubgroup m).mul_mem
      (Subgroup.subset_closure (Or.inl ⟨0, 1, rfl⟩))
      (Subgroup.subset_closure (Or.inr (Or.inr rfl)))⟩

set_option maxHeartbeats 1200000 in
/-- The standard Suzuki element `R(0,1)W` has order five. -/
public theorem lemma115_suzuki_standard_order_five (m : ℕ) :
    orderOf (lemma115_suzukiStandardElement m) = 5 := by
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hchar :
      (1 + 1 : PFAppendixIII.BinaryGaloisField (2 * m + 1)) = 0 :=
    CharTwo.add_self_eq_zero 1
  apply orderOf_eq_prime_iff.mpr
  constructor
  · apply Subtype.ext
    change
      (SuzukiRootGL m 0 1 * SuzukiWeylGL m) ^ 5 =
        (1 : GL (Fin 4)
          (PFAppendixIII.BinaryGaloisField (2 * m + 1)))
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [SuzukiRootGL, SuzukiRootMatrix, SuzukiWeylGL,
        SuzukiWeylMatrix, Matrix.mul_apply, Fin.sum_univ_four,
        pow_succ, hchar]
  · intro hone
    have hGL : SuzukiRootGL m 0 1 * SuzukiWeylGL m =
        (1 : GL (Fin 4)
          (PFAppendixIII.BinaryGaloisField (2 * m + 1))) := by
      simpa [lemma115_suzukiStandardElement] using congrArg Subtype.val hone
    have h03 := congrArg
      (fun A : GL (Fin 4)
          (PFAppendixIII.BinaryGaloisField (2 * m + 1)) =>
        ((A : Matrix (Fin 4) (Fin 4)
          (PFAppendixIII.BinaryGaloisField (2 * m + 1))) 0 3)) hGL
    have h10 :
        (1 : PFAppendixIII.BinaryGaloisField (2 * m + 1)) = 0 := by
      simp [SuzukiRootGL, SuzukiRootMatrix, SuzukiWeylGL,
        SuzukiWeylMatrix, Matrix.mul_apply, Fin.sum_univ_four] at h03
    exact one_ne_zero h10

set_option maxHeartbeats 1200000 in
/-- The centralizer of the standard order-five Suzuki element contains an
explicit family of at least `2^(2m)` matrices. -/
public theorem lemma115_suzuki_standard_centralizer_lower_bound (m : ℕ) :
    2 ^ (2 * m) ≤ Nat.card
      (Subgroup.centralizer
        ({lemma115_suzukiStandardElement m} : Set (SuzukiMatrixGroup m))) := by
  classical
  let K := PFAppendixIII.BinaryGaloisField (2 * m + 1)
  let theta : K ≃+* K := iterateFrobeniusEquiv K 2 (m + 1)
  let tr : K →ₗ[ZMod 2] ZMod 2 := Algebra.trace (ZMod 2) K
  let Z := {a : K // tr (a * theta a + a) = 0}
  let D : Z → Type := fun a =>
    {d : K // d ^ 2 + d =
      theta a * (a ^ 2 + a + 1) + a ^ 2}
  let Param := Σ a : Z, D a
  let toG : Param → SuzukiMatrixGroup m := fun z =>
    ⟨SuzukiRootGL m z.1
          (1 + z.2 + z.1 * theta z.1) *
        SuzukiTorusGL m
          (Units.mk0 (z.1 ^ 2 + z.1 + 1)
            (lemma115_suzuki_parameter_unit_ne_zero m z.1)) *
        SuzukiWeylGL m * SuzukiRootGL m z.1 z.2,
      (SuzukiMatrixSubgroup m).mul_mem
        ((SuzukiMatrixSubgroup m).mul_mem
          ((SuzukiMatrixSubgroup m).mul_mem
            (Subgroup.subset_closure
              (Or.inl ⟨z.1, 1 + z.2 + z.1 * theta z.1, rfl⟩))
            (Subgroup.subset_closure
              (Or.inr (Or.inl
                ⟨Units.mk0 (z.1 ^ 2 + z.1 + 1)
                  (lemma115_suzuki_parameter_unit_ne_zero m z.1), rfl⟩))))
          (Subgroup.subset_closure (Or.inr (Or.inr rfl))))
        (Subgroup.subset_closure (Or.inl ⟨z.1, z.2, rfl⟩))⟩
  let toC : Param → Subgroup.centralizer
      ({lemma115_suzukiStandardElement m} : Set (SuzukiMatrixGroup m)) :=
    fun z => ⟨toG z, by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      simpa [toG, lemma115_suzukiStandardElement, K, theta] using
        (lemma115_suzuki_commuting_matrix m z.1 z.2 z.2.property
          (lemma115_suzuki_artinSchreier_theta_relation
            m z.1 z.2 z.1.property z.2.property)
          (lemma115_suzuki_parameter_unit_ne_zero m z.1)).eq⟩
  let scale : Param → K := fun z =>
    ((z.1 ^ 2 + z.1 + 1) ^ (1 + 2 ^ m))⁻¹
  have hscale_ne (z : Param) : scale z ≠ 0 := by
    exact inv_ne_zero (pow_ne_zero _
      (lemma115_suzuki_parameter_unit_ne_zero m z.1))
  have hentry30 (z : Param) :
      (toC z).1.1.val 3 0 = scale z := by
    simp [toC, toG, scale, SuzukiRootGL, SuzukiRootMatrix,
      SuzukiTorusGL, SuzukiTorusMatrix, SuzukiWeylGL,
      SuzukiWeylMatrix, Matrix.mul_apply, Fin.sum_univ_four]
  have hentry31 (z : Param) :
      (toC z).1.1.val 3 1 = scale z * z.1 := by
    simp [toC, toG, scale, SuzukiRootGL, SuzukiRootMatrix,
      SuzukiTorusGL, SuzukiTorusMatrix, SuzukiWeylGL,
      SuzukiWeylMatrix, Matrix.mul_apply, Fin.sum_univ_four]
  have hentry32 (z : Param) :
      (toC z).1.1.val 3 2 = scale z * z.2 := by
    simp [toC, toG, scale, SuzukiRootGL, SuzukiRootMatrix,
      SuzukiTorusGL, SuzukiTorusMatrix, SuzukiWeylGL,
      SuzukiWeylMatrix, Matrix.mul_apply, Fin.sum_univ_four]
  have htoC : Function.Injective toC := by
    rintro ⟨ax, dx⟩ ⟨ay, dy⟩ hxy
    have hs := congrArg (fun z => z.1.1.val 3 0) hxy
    change (toC ⟨ax, dx⟩).1.1.val 3 0 =
      (toC ⟨ay, dy⟩).1.1.val 3 0 at hs
    rw [hentry30 ⟨ax, dx⟩, hentry30 ⟨ay, dy⟩] at hs
    have haMul := congrArg (fun z => z.1.1.val 3 1) hxy
    change (toC ⟨ax, dx⟩).1.1.val 3 1 =
      (toC ⟨ay, dy⟩).1.1.val 3 1 at haMul
    rw [hentry31 ⟨ax, dx⟩, hentry31 ⟨ay, dy⟩, hs] at haMul
    have haVal : (ax : K) = ay := by
      exact mul_left_cancel₀ (hscale_ne ⟨ay, dy⟩) haMul
    have haxy : ax = ay := Subtype.ext haVal
    subst ay
    have hdMulEq := congrArg (fun z => z.1.1.val 3 2) hxy
    change (toC ⟨ax, dx⟩).1.1.val 3 2 =
      (toC ⟨ax, dy⟩).1.1.val 3 2 at hdMulEq
    rw [hentry32 ⟨ax, dx⟩, hentry32 ⟨ax, dy⟩] at hdMulEq
    have hdVal : (dx : K) = dy := by
      exact mul_left_cancel₀ (hscale_ne ⟨ax, dx⟩) hdMulEq
    have hdxy : dx = dy := Subtype.ext hdVal
    subst dy
    rfl
  have hcard := Nat.card_le_card_of_injective toC htoC
  have hParamLower : 2 ^ (2 * m) ≤ Nat.card Param := by
    simpa [K, theta, tr, Z, D, Param] using
      lemma115_suzuki_parameter_card_lower_bound m
  exact hParamLower.trans hcard

end CFSG.BenderSuzuki
