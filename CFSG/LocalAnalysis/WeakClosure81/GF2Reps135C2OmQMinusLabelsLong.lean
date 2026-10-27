module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusTorus
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusLabel
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusWeights
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusWeightsTorus
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQLabelPow
import CFSG.LieType.Steinberg.CurtisDatum.TorusSums

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin.SmithCurtis CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

private theorem c2slomqmw10_two_mul_inv {M : ℕ} (hM : Odd M) :
    (2 : ZMod M) * (((M + 1) / 2 : ℕ) : ZMod M) = 1 := by
  obtain ⟨j, rfl⟩ := hM
  have h1 : (2 * j + 1 + 1) / 2 = j + 1 := by omega
  rw [h1]
  have h2 : (2 : ZMod (2 * j + 1)) * ((j + 1 : ℕ) : ZMod (2 * j + 1)) =
      (((2 * j + 1 : ℕ) : ZMod (2 * j + 1)) + 1) := by
    push_cast
    ring
  rw [h2, ZMod.natCast_self, zero_add]

theorem omq_omMinus_chi_of_long_trivial {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K]
    [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {k : Type} [Field k]
    [CharP k 2] (ι : K →+* k) (ι' : ShortField b c →+* k)
    (hι' : ∀ x : K, ι' (algebraMap K (ShortField b c) x) = ι x) {V : Type*} [AddCommGroup V]
    [Module k V] {σ : Representation k (spinGroup (quadMinus n K b c)) V} {y : V}
    {χ : spinGroup (quadMinus n K b c) → k} {μ : Fin (n - 1) → k}
    (ht : (SmallO8mCurtis.curtisDatum n hn hirr).IsCurtisType σ y χ μ)
    (hlong : ∀ i : Fin (n - 1), i.val + 1 < n - 1 →
      μ i ≠ (SmallO8mCurtis.curtisDatum n hn hirr).dScalar χ i) :
    ∃ (a : ZMod (Nat.card Kˣ)) (d : ZMod (Nat.card K + 1)),
      ∀ g ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H,
        χ g = omqMinusWt n ι ι' (((fun _ => a : Fin (n - 1) → ZMod (Nat.card Kˣ)), d) :
          OmqMinusLat (n - 1) (Nat.card Kˣ) (Nat.card K + 1)) g := by
  classical
  haveI := fact_shortField hirr
  haveI := finite_shortField (b := b) (c := c)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hχmul : ∀ a ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H,
      ∀ b ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H, χ (a * b) = χ a * χ b :=
    fun a ha b hb => ht.chi_mul ha hb
  have hd' : ∀ i, (SmallO8mCurtis.curtisDatum n hn hirr).d'Scalar χ i =
      (SmallO8mCurtis.curtisDatum n hn hirr).dScalar χ i := fun i =>
    CFSG.LieType.Steinberg.curtisDatumOf_d'Scalar_eq_dScalar
      (minusDatum_isCTGroupDatum n hirr hn) (minusDatum_steinbergExtras n hirr)
      (CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed.bruhatExtras hirr hn) 2
      (fun _ hγ => CFSG.LieType.Steinberg.isPGroup_minusRootGroup hirr hγ) χ i
  have htriv : ∀ (i : Fin (n - 1)), i.val + 1 < n - 1 → ∀ g ∈ minusTorus n hirr i, χ g = 1 := by
    intro i hi g hg
    by_contra hne
    have hne' := hlong i hi
    have hμ0 : μ i = 0 := by
      rcases ht.mu_eq i with h | h
      · exact h
      · exact absurd (h.trans (hd' i)) hne'
    have hdne : (SmallO8mCurtis.curtisDatum n hn hirr).dScalar χ i ≠ 0 := fun h0 =>
      hne' (by rw [hμ0, h0])
    exact hdne (omq_omMinus_dScalar_eq_zero hn hirr χ hχmul i ⟨g, hg, hne⟩)
  let l : Fin (n - 1) := ⟨n - 2, by omega⟩
  have hlmem : ∀ u : (ShortField b c)ˣ, shortTorusHom n hirr l u ∈
      (SmallO8mCurtis.curtisDatum n hn hirr).H := fun u =>
    (omq_omMinus_torus_mem_H hn hirr).2 l u
  let θS : (ShortField b c)ˣ →* k :=
    { toFun := fun u => χ (shortTorusHom n hirr l u)
      map_one' := by
        show χ (shortTorusHom n hirr l 1) = 1
        rw [map_one]
        exact ht.chi_one
      map_mul' := fun u u' => by
        show χ (shortTorusHom n hirr l (u * u')) = χ (shortTorusHom n hirr l u) *
          χ (shortTorusHom n hirr l u')
        rw [map_mul]
        exact ht.chi_mul (hlmem u) (hlmem u') }
  obtain ⟨C, hClt, hC⟩ := omq_exists_pow_of_units_hom ι' θS
  have hcardK : ∃ e : ℕ, 1 ≤ e ∧ Nat.card K = 2 ^ e := by
    haveI : Fintype K := Fintype.ofFinite K
    obtain ⟨e, -, he⟩ := FiniteField.card K 2
    refine ⟨(e : ℕ), e.pos, ?_⟩
    rw [Nat.card_eq_fintype_card]
    exact he
  obtain ⟨e, he1, he⟩ := hcardK
  have hevenq : Even (Nat.card K) := by
    rw [he]
    exact (Nat.even_pow.mpr ⟨even_two, by omega⟩)
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hmodd : Odd (Nat.card Kˣ) := by
    rw [Nat.card_units]
    exact Nat.Even.sub_odd hq1 hevenq odd_one
  have hhodd : Odd (Nat.card K + 1) := hevenq.add_one
  let a : ZMod (Nat.card Kˣ) := (C : ZMod (Nat.card Kˣ)) *
    ((((Nat.card Kˣ + 1) / 2 : ℕ)) : ZMod (Nat.card Kˣ))
  let d : ZMod (Nat.card K + 1) := (C : ZMod (Nat.card K + 1)) *
    ((((Nat.card K + 1 + 1) / 2 : ℕ)) : ZMod (Nat.card K + 1))
  have ha2 : 2 * a = (C : ZMod (Nat.card Kˣ)) := by
    show 2 * ((C : ZMod (Nat.card Kˣ)) * _) = _
    rw [mul_left_comm, c2slomqmw10_two_mul_inv hmodd, mul_one]
  have hd2 : 2 * d = (C : ZMod (Nat.card K + 1)) := by
    show 2 * ((C : ZMod (Nat.card K + 1)) * _) = _
    rw [mul_left_comm, c2slomqmw10_two_mul_inv hhodd, mul_one]
  obtain ⟨C', -, -, hC'm, hC'h, hC'⟩ := omq_omMinus_exists_short_exponent (n := n) hirr rfl rfl
    ι ι' hι' a d
  have hcop : Nat.Coprime (Nat.card Kˣ) (Nat.card K + 1) := by
    have h1 : Nat.card K + 1 = 2 + Nat.card Kˣ := by
      rw [Nat.card_units]
      omega
    rw [h1]
    exact Nat.coprime_add_self_right.mpr (Nat.coprime_two_right.mpr hmodd)
  have hCC' : ∀ u : (ShortField b c)ˣ,
      ι' (u : ShortField b c) ^ C = ι' (u : ShortField b c) ^ C' := by
    intro u
    have h1 : C ≡ C' [MOD Nat.card Kˣ] :=
      ((ZMod.natCast_eq_natCast_iff _ _ _).mp (by rw [hC'm, ha2]))
    have h2 : C ≡ C' [MOD Nat.card K + 1] :=
      ((ZMod.natCast_eq_natCast_iff _ _ _).mp (by rw [hC'h, hd2]))
    have h3 := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h1, h2⟩
    have hcard := omq_omMinus_card_shortField_units hirr
    have hu0 : u ^ (Nat.card Kˣ * (Nat.card K + 1)) = 1 := by
      rw [← hcard]
      exact pow_card_eq_one'
    have hu' : ι' (u : ShortField b c) ^ (Nat.card Kˣ * (Nat.card K + 1)) = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, hu0, Units.val_one, map_one]
    rw [pow_eq_pow_mod C hu', pow_eq_pow_mod C' hu', h3]
  refine ⟨a, d, fun g hg => ?_⟩
  have key : ∃ hgH : g ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H,
      χ g = omqMinusWt n ι ι' (((fun _ => a : Fin (n - 1) → ZMod (Nat.card Kˣ)), d) :
        OmqMinusLat (n - 1) (Nat.card Kˣ) (Nat.card K + 1)) g := by
    change g ∈ ⨆ j, minusTorus n hirr j at hg
    refine Subgroup.iSup_induction (minusTorus n hirr)
      (C := fun g => ∃ hgH : g ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H,
        χ g = omqMinusWt n ι ι' (((fun _ => a : Fin (n - 1) → ZMod (Nat.card Kˣ)), d) :
          OmqMinusLat (n - 1) (Nat.card Kˣ) (Nat.card K + 1)) g) hg ?_ ?_ ?_
    · intro j x hx
      have hxH : x ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H := by
        change x ∈ ⨆ j, minusTorus n hirr j
        exact le_iSup (fun j => minusTorus n hirr j) j hx
      refine ⟨hxH, ?_⟩
      have hx0 := hx
      by_cases hj : j.val + 1 < n - 1
      · rw [minusTorus_of_lt n hirr hj] at hx
        obtain ⟨τ, rfl⟩ := hx
        rw [htriv j hj _ hx0, omq_omMinus_wt_torus_long (n := n) rfl ι ι' _ hj τ]
        simp
      · rw [minusTorus_of_not_lt n hirr hj] at hx
        obtain ⟨a', ha', rfl⟩ := (mem_shortTorus_iff n hirr j).mp hx
        obtain ⟨u, rfl⟩ := exists_fieldCoord_eq (b := b) (c := c) a'
        have hu : u ≠ 0 := fun h0 => ha' (by rw [h0]; ext k; fin_cases k <;> rfl)
        have hjl : j = l := Fin.ext (by have := j.2; show j.val = n - 2; omega)
        have e1 : shortTorusElt n hirr j (fieldCoord u) =
            shortTorusHom n hirr l (Units.mk0 u hu) := by
          rw [shortTorusHom_apply, hjl]
          rfl
        rw [e1, hC' l (Units.mk0 u hu), ← hCC' (Units.mk0 u hu)]
        exact hC (Units.mk0 u hu)
    · refine ⟨one_mem _, ?_⟩
      rw [ht.chi_one, omq_omMinus_wt_eq_of_toral ι ι' _ (OmqMinusToral.one n)]
      simp
    · rintro x y ⟨hxH, hx⟩ ⟨hyH, hy⟩
      refine ⟨mul_mem hxH hyH, ?_⟩
      rw [ht.chi_mul hxH hyH, hx, hy,
        omq_omMinus_wt_mul hn hirr ι ι' _ hxH hyH]
  exact key.2

end CFSG.LocalAnalysis.WeakClosure81
