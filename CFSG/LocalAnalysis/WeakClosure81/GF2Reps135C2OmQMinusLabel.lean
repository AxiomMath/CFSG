module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallO8mCurtis
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQTrivType
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusFinite
import CFSG.LieType.Steinberg.CurtisDatum.TorusSums

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin.SmithCurtis CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

variable {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
  (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {k : Type*} [Field k] [CharP k 2]

private theorem c2slomqml_mul_self_ne_one_of_ne_one {a : k} (ha : a ≠ 1) : a * a ≠ 1 := by
  rw [← pow_two, sq_ne_one_iff]
  exact ⟨ha, by simpa [CharTwo.neg_eq] using ha⟩

private theorem c2slomqml_minusWeyl_inv_conj (i : Fin (n - 1))
    {h : spinGroup (quadMinus n K b c)} (hh : h ∈ minusTorus n hirr i) :
    (minusWeyl n hirr i)⁻¹ * h * minusWeyl n hirr i = h⁻¹ := by
  by_cases hi : i.val + 1 < n - 1
  · rw [minusTorus_of_lt n hirr hi] at hh
    rw [minusWeyl_of_lt n hirr hi]
    rw [MonoidHom.mem_range] at hh
    obtain ⟨τ, rfl⟩ := hh
    have hL2 : ((minusFrame n b c).longWeyl (succ_ne_of_lt n hi) true false) *
        ((minusFrame n b c).longWeyl (succ_ne_of_lt n hi) true false) = 1 := by
      rw [(minusFrame n b c).toHypFrame.longWeyl_mul_self]
      have hneg : (-1 : Kˣ) = 1 := Units.ext (by simp [CharTwo.neg_eq])
      rw [hneg, map_one]
    have hLi : ((minusFrame n b c).longWeyl (succ_ne_of_lt n hi) true false)⁻¹ =
        (minusFrame n b c).longWeyl (succ_ne_of_lt n hi) true false :=
      inv_eq_of_mul_eq_one_right hL2
    have hkey := (minusFrame n b c).toHypFrame.longWeyl_mul_longTorus_mul_inv
      (succ_ne_of_lt n hi) true false τ
    rw [← map_inv]
    rw [hLi] at hkey
    rw [hLi]
    exact hkey
  · rw [minusTorus_of_not_lt n hirr hi] at hh
    have := fact_shortField hirr
    have := finite_shortField (b := b) (c := c)
    obtain ⟨a, ha, rfl⟩ := (mem_shortTorus_iff n hirr i).mp hh
    obtain ⟨t, ht, he⟩ := exists_shortRels_h_eq n hirr i ha
    rw [← he]
    set R := shortRels n hirr i with hR
    have hC : ∀ s t : ShortField b c, s ≠ 0 → t ≠ 0 → R.h (s * t) = R.h s * R.h t :=
      fun s t hs ht => R.h_mul hs ht
    have hw : minusWeyl n hirr i = R.w 1 := by
      rw [minusWeyl_of_not_lt n hirr hi, shortRels_w_one]
    rw [hw]
    have hres := CFSG.LieType.Steinberg.CentralExt.TorusLift.w_conj_h (R := R) (t := -1)
      (u := t) (by norm_num) ht
    rw [← CFSG.LieType.Steinberg.RankOneRels.w_inv (R := R) (t := 1), inv_inv] at hres
    rwa [← R.h_inv hC ht] at hres

include hn hirr in
theorem omq_omMinus_dScalar_eq_one (χ : spinGroup (quadMinus n K b c) → k) (i : Fin (n - 1))
    (hi : ∀ h ∈ minusTorus n hirr i, χ h = 1) :
    (SmallO8mCurtis.curtisDatum n hn hirr).dScalar χ i = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := CFSG.LieType.Steinberg.curtisDatumOf_dScalar_eq_neg_one
    (minusDatum_isCTGroupDatum n hirr hn)
    (minusDatum_steinbergExtras n hirr)
    (CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed.bruhatExtras hirr hn) 2
    (fun _ hγ => CFSG.LieType.Steinberg.isPGroup_minusRootGroup hirr hγ) χ i hi
  rw [CharTwo.neg_eq] at h
  exact h

include hn hirr in
theorem omq_omMinus_dScalar_eq_zero (χ : spinGroup (quadMinus n K b c) → k)
    (hχ : ∀ a ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H,
      ∀ a' ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H, χ (a * a') = χ a * χ a')
    (i : Fin (n - 1)) (hi : ∃ h ∈ minusTorus n hirr i, χ h ≠ 1) :
    (SmallO8mCurtis.curtisDatum n hn hirr).dScalar χ i = 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h₀, hh₀, hχh₀⟩ := hi
  have hmem : h₀ ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H := by
    change h₀ ∈ ⨆ j, minusTorus n hirr j
    exact le_iSup (fun j => minusTorus n hirr j) i hh₀
  have hconj : (minusWeyl n hirr i)⁻¹ * h₀⁻¹ * minusWeyl n hirr i = h₀ := by
    have h := c2slomqml_minusWeyl_inv_conj (n := n) (hirr := hirr) i hh₀
    have e : (minusWeyl n hirr i)⁻¹ * h₀⁻¹ * minusWeyl n hirr i =
        ((minusWeyl n hirr i)⁻¹ * h₀ * minusWeyl n hirr i)⁻¹ := by group
    rw [e, h, inv_inv]
  have hcond : χ h₀ * χ ((minusWeyl n hirr i)⁻¹ * h₀⁻¹ * minusWeyl n hirr i) ≠ 1 := by
    rw [hconj]
    exact c2slomqml_mul_self_ne_one_of_ne_one hχh₀
  exact CFSG.LieType.Steinberg.curtisDatumOf_dScalar_eq_zero_of_conj
    (minusDatum_isCTGroupDatum n hirr hn)
    (minusDatum_steinbergExtras n hirr)
    (CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed.bruhatExtras hirr hn) 2
    (fun _ hγ => CFSG.LieType.Steinberg.isPGroup_minusRootGroup hirr hγ) χ hχ i hmem hcond

include hn hirr in
theorem omq_omMinus_chi_eq_one_of_coroots (χ : spinGroup (quadMinus n K b c) → k)
    (hχ : ∀ a ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H,
      ∀ a' ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H, χ (a * a') = χ a * χ a')
    (hχ1 : χ 1 = 1) (h : ∀ i : Fin (n - 1), ∀ g ∈ minusTorus n hirr i, χ g = 1) :
    ∀ g ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H, χ g = 1 := by
  intro g hg
  change g ∈ ⨆ i, minusTorus n hirr i at hg
  suffices hkey : g ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H ∧ χ g = 1 from hkey.2
  refine Subgroup.iSup_induction (minusTorus n hirr)
    (C := fun g => g ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H ∧ χ g = 1) hg ?_ ?_ ?_
  · intro i x hx
    refine ⟨?_, h i x hx⟩
    change x ∈ ⨆ j, minusTorus n hirr j
    exact le_iSup (fun j => minusTorus n hirr j) i hx
  · exact ⟨one_mem _, hχ1⟩
  · intro x y hx hy
    refine ⟨mul_mem hx.1 hy.1, ?_⟩
    rw [hχ x hx.1 y hy.1, hx.2, hy.2, one_mul]

include hn hirr in
theorem omq_omMinus_exists_separating {V : Type*} [AddCommGroup V] [Module k V]
    {σ : Representation k (spinGroup (quadMinus n K b c)) V} (hσ : IsSimpleRep σ) {y : V}
    {χ : spinGroup (quadMinus n K b c) → k} {μ : Fin (n - 1) → k}
    (ht : (SmallO8mCurtis.curtisDatum n hn hirr).IsCurtisType σ y χ μ)
    {g : spinGroup (quadMinus n K b c)} (hg : σ g ≠ 1) :
    ∃ i : Fin (n - 1), μ i = (SmallO8mCurtis.curtisDatum n hn hirr).dScalar χ i := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra h
  have hne : ∀ i, μ i ≠ (SmallO8mCurtis.curtisDatum n hn hirr).dScalar χ i :=
    fun i hi => h ⟨i, hi⟩
  have hd'S : ∀ i, (SmallO8mCurtis.curtisDatum n hn hirr).d'Scalar χ i =
      (SmallO8mCurtis.curtisDatum n hn hirr).dScalar χ i := fun i =>
    CFSG.LieType.Steinberg.curtisDatumOf_d'Scalar_eq_dScalar
      (minusDatum_isCTGroupDatum n hirr hn) (minusDatum_steinbergExtras n hirr)
      (CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed.bruhatExtras hirr hn) 2
      (fun _ hγ => CFSG.LieType.Steinberg.isPGroup_minusRootGroup hirr hγ) χ i
  have hμ0 : ∀ i, μ i = 0 := by
    intro i
    rcases ht.mu_eq i with h0 | h1
    · exact h0
    · exact absurd (h1.trans (hd'S i)) (hne i)
  have hne0 : ∀ i, (SmallO8mCurtis.curtisDatum n hn hirr).dScalar χ i ≠ 0 := by
    intro i h0
    exact hne i (by rw [hμ0 i, h0])
  have hχmul : ∀ a ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H,
      ∀ b ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H, χ (a * b) = χ a * χ b :=
    fun a ha b hb => ht.chi_mul ha hb
  have hcor : ∀ i : Fin (n - 1), ∀ h ∈ minusTorus n hirr i, χ h = 1 := by
    intro i h hh
    by_contra hh1
    exact hne0 i (omq_omMinus_dScalar_eq_zero hn hirr χ hχmul i ⟨h, hh, hh1⟩)
  have hχH := omq_omMinus_chi_eq_one_of_coroots hn hirr χ hχmul ht.chi_one hcor
  have hμzero : μ = 0 := funext hμ0
  have ht0 : (SmallO8mCurtis.curtisDatum n hn hirr).IsCurtisType σ y χ 0 := by
    rw [hμzero] at ht
    exact ht
  exact hg (omq_rep_eq_one_of_isCurtisType_zero (SmallO8mCurtis.curtisDatum n hn hirr)
    hσ ht0 hχH g)

end CFSG.LocalAnalysis.WeakClosure81
