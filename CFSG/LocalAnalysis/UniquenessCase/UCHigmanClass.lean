module

public import CFSG.LocalAnalysis.UniquenessCase.UCHigmanTens
public import CFSG.HardMathSupport.U4FF.ClassChar
public import Mathlib.FieldTheory.IsAlgClosed.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.Higman

open Matrix CFSG.Quasithin.SmithCurtis
open scoped MatrixGroups

section Class

variable {K : Type} [Field K] [CharP K 2] {k : Type} [Field k] [Algebra K k]

theorem splitOver_torus [Finite K] [IsAlgClosed k] :
    SplitOver k (sl2Datum (K := K)).H := by
  intro h hh
  have hfin : IsOfFinOrder h := isOfFinOrder_of_finite h
  refine ⟨orderOf h, pow_orderOf_eq_one h, ?_⟩
  set p : Polynomial k := Polynomial.X ^ orderOf h - 1 with hp
  have hm : p.Monic := by
    have := Polynomial.monic_X_pow_sub_C (1 : k) hfin.orderOf_pos.ne'
    rwa [map_one] at this
  refine ⟨p.roots.toList, ?_⟩
  have key := (IsAlgClosed.splits p).eq_prod_roots_of_monic hm
  have h2 : Multiset.map (fun a => Polynomial.X - Polynomial.C a) p.roots =
      ((p.roots.toList.map fun a => (Polynomial.X - Polynomial.C a : Polynomial k) : List _) :
        Multiset _) := by
    rw [← Multiset.map_coe, Multiset.coe_toList]
  rw [h2, Multiset.prod_coe] at key
  exact key

@[expose] noncomputable def uEquivX (K : Type) [Field K] [CharP K 2] :
    K ≃ ↥((sl2Datum (K := K)).X 0) := uEquiv K

theorem uEquivX_eq_one_iff (a : K) : (uEquivX K a : ↥((sl2Datum (K := K)).X 0)) = 1 ↔ a = 0 := by
  constructor
  · intro h
    have := congrArg (fun g : ↥((sl2Datum (K := K)).X 0) => (g : SL(2, K))) h
    exact (uMat_eq_one_iff a).1 this
  · rintro rfl
    apply Subtype.ext
    exact uMat_zero

open Classical in
theorem d'Scalar_sl2 [Fintype K] (χ : SL(2, K) → k) (e : ℕ)
    (hχ : ∀ r : Kˣ, χ (hMat r) = algebraMap K k (r : K) ^ e) :
    (sl2Datum (K := K)).d'Scalar χ 0 = ∑ r : Kˣ, algebraMap K k (r : K) ^ e := by
  unfold CFSG.Quasithin.SmithCurtis.CurtisDatum.d'Scalar
  letI : DecidableEq SL(2, K) := fun a b => Classical.propDecidable (a = b)
  refine (Finset.sum_bij (fun (r : Kˣ) _ => uEquivX K (r : K)) ?_ ?_ ?_ ?_).symm
  · intro r _
    refine Finset.mem_erase.2 ⟨?_, by simp⟩
    intro h
    exact r.ne_zero ((uEquivX_eq_one_iff (r : K)).1 h)
  · intro r _ r' _ h
    exact Units.ext ((uEquivX K).injective h)
  · intro x hx
    have hx1 := (Finset.mem_erase.1 hx).1
    obtain ⟨a, ha⟩ := (uEquivX K).surjective x
    have ha0 : a ≠ 0 := by
      intro h0
      apply hx1
      rw [← ha, h0]
      exact (uEquivX_eq_one_iff 0).2 rfl
    refine ⟨Units.mk0 a ha0, by simp, ?_⟩
    simpa using ha
  · intro r _
    show algebraMap K k (r : K) ^ e = χ (phiFn (uMat (r : K)))
    rw [phiFn_uMat, hχ r]

theorem simple_iso_TRep [Finite K] [CharP k 2] [IsAlgClosed k] {n : ℕ}
    (hn : Nat.card K = 2 ^ n) {V : Type} [AddCommGroup V] [Module k V]
    (ρ : Representation k SL(2, K) V) (hρ : IsSimpleRep ρ) :
    ∃ S : Finset ℕ, (∀ i ∈ S, i < n) ∧
      ∃ β : V ≃ₗ[k] ((↥S → Fin 2) → k), ∀ (g : SL(2, K)) (v : V), β (ρ g v) = TRep S g (β v) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hn1 : 1 ≤ n := by
    by_contra h
    have : n = 0 := by omega
    rw [this, pow_zero] at hn
    omega
  obtain ⟨y, χ, μ, ht⟩ := (sl2Datum (K := K)).exists_isCurtisType splitOver_torus hρ
  obtain ⟨e, he, hχ⟩ := CFSG.HardMathSupport.U4FF.exists_char_exponent (F := K) (k := k)
    (fun r : Kˣ => χ (hMat r))
    (fun r r' => by rw [← hMat_mul]; exact ht.chi_mul ⟨r, rfl⟩ ⟨r', rfl⟩)
    (by rw [hMat_one]; exact ht.chi_one)
  have hcard : Nat.card Kˣ = 2 ^ n - 1 := by rw [Nat.card_units, hn]
  have hmu := ht.mu_eq 0
  have hd' := d'Scalar_sl2 χ e hχ
  have hsum : ∑ r : Kˣ, algebraMap K k (r : K) ^ e = if e = 0 then 1 else 0 := by
    have h1 := FiniteField.sum_pow_units K e
    have h2 := congrArg (algebraMap K k) h1
    rw [map_sum] at h2
    simp only [map_pow] at h2
    rw [h2]
    have hq : Fintype.card K = 2 ^ n := by rw [← Nat.card_eq_fintype_card, hn]
    by_cases he0 : e = 0
    · subst he0
      rw [if_pos (dvd_zero _), if_pos rfl, map_neg, map_one, CharTwo.neg_eq]
    · have hnd : ¬ (Fintype.card K - 1 ∣ e) := by
        intro hd
        have := Nat.le_of_dvd (Nat.pos_of_ne_zero he0) hd
        omega
      rw [if_neg hnd, if_neg he0, map_zero]
  have hS : ∃ S : Finset ℕ, (∀ i ∈ S, i < n) ∧
      (∀ r : Kˣ, χ (hMat r) = algebraMap K k (r : K) ^ wt S) ∧
      μ 0 = if S = Finset.range n then 1 else 0 := by
    have hrange_ne : (∅ : Finset ℕ) ≠ Finset.range n := fun h => by
      have := congrArg Finset.card h
      simp at this
      omega
    by_cases he0 : e = 0
    · subst he0
      have hd1 : (sl2Datum (K := K)).d'Scalar χ 0 = 1 := by rw [hd', hsum]; simp
      rcases hmu with h0 | h1
      · refine ⟨∅, by simp, fun r => ?_, ?_⟩
        · rw [hχ r]; simp [wt]
        · rw [h0, if_neg hrange_ne]
      · have hw : wt (Finset.range n) = 2 ^ n - 1 :=
          (wt_eq_iff (Finset.range n) (fun i hi => Finset.mem_range.1 hi)).2 rfl
        refine ⟨Finset.range n, fun i hi => Finset.mem_range.1 hi, fun r => ?_, ?_⟩
        · rw [hχ r, pow_zero, hw, ← hcard]
          exact ((CFSG.HardMathSupport.U4FF.units_pow_eq_one_iff (F := K) (k := k)
            (Nat.card Kˣ)).2 dvd_rfl r).symm
        · rw [h1, hd1, if_pos rfl]
    · have hmu0 : μ 0 = 0 := by
        rcases hmu with h0 | h1
        · exact h0
        · rw [h1, hd', hsum, if_neg he0]
      have hwt : wt e.bitIndices.toFinset = e := Finset.sum_toFinset_bitIndices_two_pow e
      have hlt : ∀ i ∈ e.bitIndices.toFinset, i < n := by
        intro i hi
        by_contra hge
        push Not at hge
        have h1 : 2 ^ i ≤ wt e.bitIndices.toFinset := Finset.single_le_sum
          (f := fun i => 2 ^ i) (fun _ _ => Nat.zero_le _) hi
        have h2 : 2 ^ n ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hge
        omega
      refine ⟨e.bitIndices.toFinset, hlt, fun r => ?_, ?_⟩
      · rw [hχ r, hwt]
      · rw [hmu0, if_neg]
        intro h
        have hw : wt (Finset.range n) = 2 ^ n - 1 :=
          (wt_eq_iff (Finset.range n) (fun i hi => Finset.mem_range.1 hi)).2 rfl
        rw [← h, hwt] at hw
        omega
  obtain ⟨S, hSn, hSχ, hSμ⟩ := hS
  have hT := TRep_isCurtisType hn S hSn χ hSχ
  have hμ' : μ = fun _ => (if S = Finset.range n then (1 : k) else 0) := by
    funext s
    rw [Subsingleton.elim s 0, hSμ]
  rw [← hμ'] at hT
  obtain ⟨β, hβ⟩ := (sl2Datum (K := K)).iso_of_isCurtisType hρ (TRep_isSimple hn S hSn) ht hT
  exact ⟨S, hSn, β, hβ⟩

theorem exists_cube_root [IsAlgClosed k] : ∃ ω : k, ω ^ 2 + ω + 1 = 0 := by
  obtain ⟨ω, hω⟩ := IsAlgClosed.exists_root (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial k)
    (by
      have : (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial k).degree = 2 := by
        compute_degree!
      rw [this]; norm_num)
  refine ⟨ω, ?_⟩
  simpa [Polynomial.IsRoot] using hω

theorem simple_natural [Finite K] [CharP k 2] [IsAlgClosed k] {n : ℕ}
    (hn : Nat.card K = 2 ^ n) {V : Type} [AddCommGroup V] [Module k V]
    (ρ : Representation k SL(2, K) V) (hρ : IsSimpleRep ρ) (d : SL(2, K)) (hd3 : d ^ 3 = 1)
    (hd1 : d ≠ 1) (hdV : ∀ v : V, ρ d (ρ d v) + ρ d v + v = 0) :
    ∃ i : ℕ, i < n ∧ ∃ β : V ≃ₗ[k] (Fin 2 → k), ∀ (g : SL(2, K)) (v : V),
      β (ρ g v) = (Amat i g : Matrix (Fin 2) (Fin 2) k) *ᵥ β v := by
  obtain ⟨S, hSn, β, hβ⟩ := simple_iso_TRep hn ρ hρ
  have hdT : ∀ Φ : (↥S → Fin 2) → k, TRep S d (TRep S d Φ) + TRep S d Φ + Φ = 0 := by
    intro Φ
    obtain ⟨v, rfl⟩ := β.surjective Φ
    rw [← hβ, ← hβ, ← map_add, ← map_add, hdV, map_zero]
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have hthree : ∀ Φ : (↥S → Fin 2) → k, Φ + Φ + Φ = Φ := by
    intro Φ
    have : Φ + Φ = 0 := by rw [← two_smul k Φ, h2, zero_smul]
    rw [this, zero_add]
  have hcard : S.card = 1 := by
    by_contra hne
    rcases Nat.lt_or_ge S.card 2 with hlt | hge
    · have h0 : S.card = 0 := by omega
      have hS0 : S = ∅ := Finset.card_eq_zero.1 h0
      subst hS0
      have := hdT (Pi.single (0 : ↥(∅ : Finset ℕ) → Fin 2) (1 : k))
      rw [TRep_empty, TRep_empty, hthree] at this
      exact delta0_ne_zero _ this
    · obtain ⟨ω, hω⟩ := exists_cube_root (k := k)
      obtain ⟨Φ, hΦ0, hΦ⟩ := exists_fixed_vec hω d hd3 hd1 S hge
      have := hdT Φ
      rw [hΦ, hΦ, hthree] at this
      exact hΦ0 this
  obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 hcard
  refine ⟨i, hSn i (Finset.mem_singleton_self i), β.trans (natEquiv k i), fun g v => ?_⟩
  rw [LinearEquiv.trans_apply, hβ, natEquiv_TRep]
  rfl

end Class
end CFSG.LocalAnalysis.UniquenessCase.UCK.Higman
