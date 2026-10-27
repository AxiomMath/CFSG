module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusChars
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusLabel
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQLabelPow
import CFSG.LieType.Steinberg.CurtisDatum.TorusSums

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin.SmithCurtis CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

private theorem c2slomqmw9_entry_zero_generator {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K]
    [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (j : Fin (n - 1))
    {x : spinGroup (quadMinus n K b c)} (hx : x ∈ minusTorus n hirr j) :
    (j.val = 0 ∧ ∃ a : Kˣ, ∃ hj : j.val + 1 < n - 1,
        x = (minusFrame n b c).longTorus (succ_ne_of_lt n hj) true false a ∧
        mat n x (Sum.inl ⟨0, by omega⟩) (Sum.inl ⟨0, by omega⟩) = (a : K)) ∨
      (j.val ≠ 0 ∧ mat n x (Sum.inl ⟨0, by omega⟩) (Sum.inl ⟨0, by omega⟩) = 1) := by
  haveI := fact_shortField hirr
  by_cases hj : j.val + 1 < n - 1
  · rw [minusTorus_of_lt n hirr hj] at hx
    obtain ⟨a, rfl⟩ := hx
    have ht := omq_omMinus_toral_longTorus (b := b) (c := c) hj a
    by_cases h0 : j.val = 0
    · left
      refine ⟨h0, a, hj, rfl, ?_⟩
      have : (⟨0, by omega⟩ : Fin (n - 1)) = j := Fin.ext h0.symm
      rw [ht.mat_inl_inl]
      simp [this]
    · right
      refine ⟨h0, ?_⟩
      have h1 : (⟨0, by omega⟩ : Fin (n - 1)) ≠ j := fun h => h0 (by rw [← h])
      have h2 : (⟨0, by omega⟩ : Fin (n - 1)) ≠ ⟨j.val + 1, hj⟩ := fun h => by
        have := congrArg Fin.val h
        simp at this
      rw [ht.mat_inl_inl]
      simp [h1, h2]
  · rw [minusTorus_of_not_lt n hirr hj] at hx
    obtain ⟨a, ha, rfl⟩ := (mem_shortTorus_iff n hirr j).mp hx
    obtain ⟨u, rfl⟩ := exists_fieldCoord_eq (b := b) (c := c) a
    have hu : u ≠ 0 := fun h0 => ha (by rw [h0]; ext k; fin_cases k <;> rfl)
    have ht := omq_omMinus_toral_shortTorusHom hirr j (Units.mk0 u hu)
    right
    have hj0 : j.val ≠ 0 := by omega
    refine ⟨hj0, ?_⟩
    have h1 : (⟨0, by omega⟩ : Fin (n - 1)) ≠ j := fun h => hj0 (by rw [← h])
    have := ht.mat_inl_inl (⟨0, by omega⟩ : Fin (n - 1))
    simpa [shortTorusHom_apply, h1] using this

theorem omq_omMinus_label_of_single {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K]
    [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {k : Type} [Field k]
    [CharP k 2] (ι : K →+* k) {V : Type*} [AddCommGroup V] [Module k V]
    {σ : Representation k (spinGroup (quadMinus n K b c)) V} {y : V}
    {χ : spinGroup (quadMinus n K b c) → k} {μ : Fin (n - 1) → k}
    (ht : (SmallO8mCurtis.curtisDatum n hn hirr).IsCurtisType σ y χ μ)
    (hJ : ∀ i : Fin (n - 1),
      μ i = (SmallO8mCurtis.curtisDatum n hn hirr).dScalar χ i ↔ i.val = 0) :
    ∃ cc : ℕ, 1 ≤ cc ∧ cc ≤ Nat.card Kˣ ∧
      (∀ g ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H,
        χ g = ι (mat n g (Sum.inl ⟨0, by omega⟩) (Sum.inl ⟨0, by omega⟩)) ^ cc) ∧
      (cc = Nat.card Kˣ → μ ⟨0, by omega⟩ = 1) ∧
      (cc < Nat.card Kˣ → μ ⟨0, by omega⟩ = 0) := by
  classical
  haveI := fact_shortField hirr
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : NeZero (Nat.card Kˣ) := ⟨Nat.card_pos.ne'⟩
  let m0 : Fin (n - 1) := ⟨0, by omega⟩
  have hk0 : m0.val + 1 < n - 1 := by show 0 + 1 < n - 1; omega
  have hχmul : ∀ a ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H,
      ∀ b ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H, χ (a * b) = χ a * χ b :=
    fun a ha b hb => ht.chi_mul ha hb
  have hd' : ∀ i, (SmallO8mCurtis.curtisDatum n hn hirr).d'Scalar χ i =
      (SmallO8mCurtis.curtisDatum n hn hirr).dScalar χ i := fun i =>
    CFSG.LieType.Steinberg.curtisDatumOf_d'Scalar_eq_dScalar
      (minusDatum_isCTGroupDatum n hirr hn) (minusDatum_steinbergExtras n hirr)
      (CFSG.LieType.Steinberg.CentralExt.SpinMinusClosed.bruhatExtras hirr hn) 2
      (fun _ hγ => CFSG.LieType.Steinberg.isPGroup_minusRootGroup hirr hγ) χ i
  have htriv : ∀ (i : Fin (n - 1)), i.val ≠ 0 → ∀ g ∈ minusTorus n hirr i, χ g = 1 := by
    intro i hi g hg
    by_contra hne
    have hne' : μ i ≠ (SmallO8mCurtis.curtisDatum n hn hirr).dScalar χ i :=
      fun h => hi ((hJ i).mp h)
    have hμ0 : μ i = 0 := by
      rcases ht.mu_eq i with h | h
      · exact h
      · exact absurd (h.trans (hd' i)) hne'
    have hdne : (SmallO8mCurtis.curtisDatum n hn hirr).dScalar χ i ≠ 0 := fun h0 =>
      hne' (by rw [hμ0, h0])
    exact hdne (omq_omMinus_dScalar_eq_zero hn hirr χ hχmul i ⟨g, hg, hne⟩)
  let L0 : Kˣ →* spinGroup (quadMinus n K b c) :=
    (minusFrame n b c).longTorus (succ_ne_of_lt n hk0) true false
  have hL0H : ∀ a : Kˣ, L0 a ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H := fun a =>
    (omq_omMinus_torus_mem_H hn hirr).1 m0 hk0 a
  let θ : Kˣ →* k :=
    { toFun := fun a => χ (L0 a)
      map_one' := by
        show χ (L0 1) = 1
        rw [map_one]
        exact ht.chi_one
      map_mul' := fun a a' => by
        show χ (L0 (a * a')) = χ (L0 a) * χ (L0 a')
        rw [map_mul]
        exact ht.chi_mul (hL0H a) (hL0H a') }
  obtain ⟨c₀, hc₀lt, hc₀⟩ := omq_exists_pow_of_units_hom ι θ
  have formula : ∀ cc : ℕ, (∀ a : Kˣ, χ (L0 a) = ι (a : K) ^ cc) →
      ∀ g ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H,
        χ g = ι (mat n g (Sum.inl m0) (Sum.inl m0)) ^ cc := by
    intro cc hcc g hg
    have key : ∃ hgH : g ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H,
        χ g = ι (mat n g (Sum.inl m0) (Sum.inl m0)) ^ cc := by
      change g ∈ ⨆ j, minusTorus n hirr j at hg
      refine Subgroup.iSup_induction (minusTorus n hirr)
        (C := fun g => ∃ hgH : g ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H,
          χ g = ι (mat n g (Sum.inl m0) (Sum.inl m0)) ^ cc) hg ?_ ?_ ?_
      · intro j x hx
        have hxH : x ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H := by
          change x ∈ ⨆ j, minusTorus n hirr j
          exact le_iSup (fun j => minusTorus n hirr j) j hx
        refine ⟨hxH, ?_⟩
        rcases c2slomqmw9_entry_zero_generator hn hirr j hx with ⟨h0, a, hj, rfl, he⟩ | ⟨h0, he⟩
        · have hj0 : j = m0 := Fin.ext h0
          subst hj0
          rw [he]
          exact hcc a
        · rw [he, map_one, one_pow]
          exact htriv j h0 x hx
      · exact ⟨one_mem _, by rw [ht.chi_one, mat_one]; simp⟩
      · rintro x y ⟨hxH, hx⟩ ⟨hyH, hy⟩
        refine ⟨mul_mem hxH hyH, ?_⟩
        have e := (omqMinusEntryHom hn hirr m0).map_mul ⟨x, hxH⟩ ⟨y, hyH⟩
        have e' : mat n (x * y) (Sum.inl m0) (Sum.inl m0) =
            mat n x (Sum.inl m0) (Sum.inl m0) * mat n y (Sum.inl m0) (Sum.inl m0) := by
          have := congrArg (fun u : Kˣ => (u : K)) e
          simpa [omqMinusEntryHom_val] using this
        rw [ht.chi_mul hxH hyH, hx, hy, e', map_mul, mul_pow]
    exact key.2
  have hpow_card : ∀ a : Kˣ, ι (a : K) ^ Nat.card Kˣ = 1 := fun a => by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one', Units.val_one, map_one]
  have hmu0 : μ m0 = (SmallO8mCurtis.curtisDatum n hn hirr).dScalar χ m0 := (hJ m0).mpr rfl
  by_cases hc0 : c₀ = 0
  · refine ⟨Nat.card Kˣ, Nat.card_pos, le_rfl, ?_, ?_, ?_⟩
    · refine formula _ (fun a => ?_)
      rw [hpow_card a]
      have h1 : θ a = ι (a : K) ^ c₀ := hc₀ a
      rw [hc0, pow_zero] at h1
      exact h1
    · intro _
      rw [hmu0]
      refine omq_omMinus_dScalar_eq_one hn hirr χ m0 (fun h hh => ?_)
      rw [minusTorus_of_lt n hirr hk0] at hh
      obtain ⟨a, rfl⟩ := hh
      have h1 : θ a = ι (a : K) ^ c₀ := hc₀ a
      rw [hc0, pow_zero] at h1
      exact h1
    · intro hlt
      exact absurd hlt (lt_irrefl _)
  · have hc0pos : 0 < c₀ := Nat.pos_of_ne_zero hc0
    refine ⟨c₀, hc0pos, hc₀lt.le, ?_, ?_, ?_⟩
    · exact formula c₀ (fun a => hc₀ a)
    · intro hc
      exact absurd hc (ne_of_lt hc₀lt)
    · intro _
      rw [hmu0]
      obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Kˣ)
      have hγord : orderOf γ = Nat.card Kˣ := orderOf_eq_card_of_forall_mem_zpowers hγ
      let f : Kˣ →* kˣ := Units.map ι.toMonoidHom
      have hf : Function.Injective f := fun x y hxy => Units.ext (ι.injective (congrArg
        (fun u : kˣ => (u : k)) hxy))
      have hord : orderOf (f γ) = Nat.card Kˣ := by
        have h1 := orderOf_injective f hf γ
        rw [hγord] at h1
        exact h1
      refine omq_omMinus_dScalar_eq_zero hn hirr χ hχmul m0 ⟨L0 γ, ?_, ?_⟩
      · rw [minusTorus_of_lt n hirr hk0]
        exact ⟨γ, rfl⟩
      · intro h1
        have h2 : χ (L0 γ) = ι (γ : K) ^ c₀ := hc₀ γ
        rw [h2] at h1
        have h3 : (f γ) ^ c₀ = 1 := Units.ext (by simpa [f] using h1)
        have h4 := orderOf_dvd_iff_pow_eq_one.mpr h3
        rw [hord] at h4
        exact Nat.not_dvd_of_pos_of_lt hc0pos hc₀lt h4

end CFSG.LocalAnalysis.WeakClosure81
