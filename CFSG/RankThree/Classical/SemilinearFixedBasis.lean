module

public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism
public import Mathlib.LinearAlgebra.Dual.Lemmas

public section

namespace CFSG.RankThree.Classical

open CFSG.LocalAnalysis.ComponentInitial

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

theorem iterate_smul (σ : k ≃+* k) (a : V ≃+ V) (ha : ∀ (c : k) (v : V), a (c • v) = σ c • a v)
    (j : ℕ) (c : k) (v : V) : (⇑a)^[j] (c • v) = (σ ^ j) c • (⇑a)^[j] v := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, ha, pow_succ']
    rfl

theorem apply_sum_iterate (a : V ≃+ V) {h : ℕ} (hah : ∀ v, (⇑a)^[h] v = v) (x : V) :
    a (∑ j ∈ Finset.range h, (⇑a)^[j] x) = ∑ j ∈ Finset.range h, (⇑a)^[j] x := by
  rw [map_sum]
  have h1 := Finset.sum_range_succ' (fun j => (⇑a)^[j] x) h
  have h2 := Finset.sum_range_succ (fun j => (⇑a)^[j] x) h
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply] at h1 h2
  rw [hah] at h2
  exact add_right_cancel (h1.symm.trans h2)

@[expose] def fixedSet (a : V ≃+ V) : Set V :=
  {v | a v = v}

theorem span_fixed_eq_top (σ : k ≃+* k) {h : ℕ} (hh : 0 < h) (hσ : orderOf σ = h)
    (a : V ≃+ V) (ha : ∀ (c : k) (v : V), a (c • v) = σ c • a v)
    (hah : ∀ v, (⇑a)^[h] v = v) : Submodule.span k (fixedSet a) = ⊤ := by
  by_contra hne
  obtain ⟨v, hv⟩ : ∃ v, v ∉ Submodule.span k (fixedSet a) := by
    by_contra hall
    push Not at hall
    exact hne (eq_top_iff.mpr fun v _ => hall v)
  obtain ⟨f, hfv, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hv inferInstance
  have hf0 : ∀ w ∈ Submodule.span k (fixedSet a), f w = 0 := fun w hw => by
    have : f w ∈ Submodule.map f (Submodule.span k (fixedSet a)) := Submodule.mem_map_of_mem hw
    rwa [hf, Submodule.mem_bot] at this
  let χ : Fin h → (k →* k) := fun j => ((σ ^ (j : ℕ) : k ≃+* k) : k →* k)
  have hχ : Function.Injective χ := by
    intro i j hij
    have h' : (σ ^ (i : ℕ) : k ≃+* k) = σ ^ (j : ℕ) := RingEquiv.ext fun x =>
      DFunLike.congr_fun hij x
    have := pow_injOn_Iio_orderOf (x := σ) (by rw [hσ]; exact i.isLt) (by rw [hσ]; exact j.isLt) h'
    exact Fin.ext this
  have hli : LinearIndependent k fun j => (χ j : k → k) :=
    (linearIndependent_monoidHom k k).comp χ hχ
  have hrel : ∑ j : Fin h, f ((⇑a)^[(j : ℕ)] v) • (χ j : k → k) = 0 := by
    funext b
    have hb : f (∑ j ∈ Finset.range h, (⇑a)^[j] (b • v)) = 0 :=
      hf0 _ (Submodule.subset_span (apply_sum_iterate a hah (b • v)))
    rw [map_sum, ← Fin.sum_univ_eq_sum_range] at hb
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← hb]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [iterate_smul σ a ha, map_smul, smul_eq_mul, mul_comm]
    rfl
  have h0 := Fintype.linearIndependent_iff.mp hli _ hrel ⟨0, hh⟩
  simp only [Function.iterate_zero_apply] at h0
  exact hfv h0

theorem repr_semilinear_apply {ι : Type*} (σ : k ≃+* k) (a : V ≃+ V)
    (ha : ∀ (c : k) (v : V), a (c • v) = σ c • a v) (b : Module.Basis ι k V)
    (hb : ∀ i, a (b i) = b i) (x : V) (i : ι) : b.repr (a x) i = σ (b.repr x i) := by
  have hsl : ∀ y : V, a y = ∑ i ∈ (b.repr y).support, σ (b.repr y i) • b i := by
    intro y
    conv_lhs => rw [← b.linearCombination_repr y, Finsupp.linearCombination_apply, Finsupp.sum]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [ha, hb]
  have hc : a x = Finsupp.linearCombination k b ((b.repr x).mapRange σ (map_zero σ)) := by
    rw [hsl x, Finsupp.linearCombination_apply,
      Finsupp.sum_mapRange_index (fun i => zero_smul k (b i))]
    rfl
  rw [hc, b.repr_linearCombination, Finsupp.mapRange_apply]

theorem semilinear_fixed_basis {ℓ e : ℕ} (hℓ : ℓ.Prime) (he : 1 ≤ e) (hk : Nat.card k = ℓ ^ e)
    (σ : k ≃+* k) {h : ℕ} (hσ : orderOf σ = h) [FiniteDimensional k V] {m : ℕ}
    (hm : Module.finrank k V = m) (a : V ≃+ V) (ha : ∀ (c : k) (v : V), a (c • v) = σ c • a v)
    (hah : ∀ v, (⇑a)^[h] v = v) :
    h ∣ e ∧ ∃ k₀ : Subfield k, (k₀ : Set k) = {c | σ c = c} ∧ Nat.card k₀ = ℓ ^ (e / h) ∧
      ∃ b : Module.Basis (Fin m) k V, (∀ i, a (b i) = b i) ∧
        ∃ C : Submodule k₀ V, (C : Set V) = {v | a v = v} ∧
          (∃ b₀ : Module.Basis (Fin m) k₀ C, ∀ i, (b₀ i : V) = b i) ∧
          Module.finrank k₀ C = m ∧ Nat.card C = ℓ ^ (e * m / h) := by
  obtain ⟨-, -, -, -, hcardAut, hfix⟩ := finite_field_automorphism_fixed_field_cardinality hℓ he hk
  have hfinAut : Finite (k ≃+* k) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  have hh : 0 < h := hσ ▸ orderOf_pos σ
  obtain ⟨hdvd, S, hS, hScard⟩ := hfix (Subgroup.zpowers σ)
  rw [Nat.card_zpowers, hσ] at hdvd hScard
  have hS' : (S : Set k) = {c | σ c = c} := by
    rw [hS]
    ext c
    refine ⟨fun hc => hc σ (Subgroup.mem_zpowers σ), fun hc τ hτ => ?_⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hτ
    have hfixc : ∀ n : ℕ, (σ ^ n) c = c := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [pow_succ']
        change σ ((σ ^ n) c) = c
        rw [ih]
        exact hc
    rcases Int.eq_nat_or_neg n with ⟨n, rfl | rfl⟩
    · rw [zpow_natCast]
      exact hfixc n
    · rw [zpow_neg, zpow_natCast]
      conv_lhs => rw [← hfixc n]
      exact RingEquiv.symm_apply_apply _ _
  refine ⟨hdvd, S, hS', hScard, ?_⟩
  have hmemS : ∀ c : k, σ c = c → c ∈ S := fun c hc => by
    rw [← SetLike.mem_coe, hS']
    exact hc
  obtain ⟨t, htsub, htspan, htli⟩ := exists_linearIndependent k (fixedSet a)
  rw [span_fixed_eq_top σ hh hσ a ha hah] at htspan
  let bt : Module.Basis t k V := Module.Basis.mk htli (by rw [Subtype.range_coe, htspan])
  have : Finite t := Module.Finite.finite_basis bt
  have : Fintype t := Fintype.ofFinite t
  have hcard_t : Fintype.card t = m := by
    rw [← hm, Module.finrank_eq_card_basis bt]
  let b : Module.Basis (Fin m) k V := bt.reindex (Fintype.equivFinOfCardEq hcard_t)
  have hbfix : ∀ i, a (b i) = b i := fun i => by
    rw [Module.Basis.reindex_apply, Module.Basis.mk_apply]
    exact htsub (Subtype.mem _)
  refine ⟨b, hbfix, ?_⟩
  let C : Submodule S V :=
    { carrier := {v | a v = v}
      add_mem' := fun {x y} hx hy => by
        change a (x + y) = x + y
        rw [map_add, hx, hy]
      zero_mem' := by
        change a 0 = 0
        exact map_zero a
      smul_mem' := fun c x hx => by
        change a ((c : k) • x) = (c : k) • x
        rw [ha, hx]
        congr 1
        have hc : (c : k) ∈ S := c.2
        rw [← SetLike.mem_coe, hS'] at hc
        exact hc }
  have hmemC : ∀ v, v ∈ C ↔ a v = v := fun v => Iff.rfl
  refine ⟨C, rfl, ?_⟩
  have hliS : LinearIndependent S (fun i => (⟨b i, hbfix i⟩ : C)) := by
    have hinj : Function.Injective fun r : S => r • (1 : k) := fun r s hrs => by
      simp only [Subfield.smul_def, smul_eq_mul, mul_one] at hrs
      exact Subtype.ext hrs
    have hb' : LinearIndependent S (fun i => (b i : V)) := b.linearIndependent.restrict_scalars hinj
    exact LinearIndependent.of_comp C.subtype hb'
  have hspS : ⊤ ≤ Submodule.span S (Set.range fun i => (⟨b i, hbfix i⟩ : C)) := by
    rintro ⟨x, hx⟩ -
    have hcoef : ∀ i, b.repr x i ∈ S := fun i => by
      apply hmemS
      rw [← repr_semilinear_apply σ a ha b hbfix x i, hx]
    have hx' : (⟨x, hx⟩ : C) = ∑ i, (⟨b.repr x i, hcoef i⟩ : S) • (⟨b i, hbfix i⟩ : C) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul_of_tower, Subfield.smul_def]
      exact (b.sum_repr x).symm
    rw [hx']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let b₀ : Module.Basis (Fin m) S C := Module.Basis.mk hliS hspS
  have hfinC : Module.finrank S C = m := by
    rw [Module.finrank_eq_card_basis b₀, Fintype.card_fin]
  refine ⟨⟨b₀, fun i => by rw [Module.Basis.mk_apply]⟩, hfinC, ?_⟩
  have : Module.Finite S C := Module.Finite.of_basis b₀
  rw [Module.natCard_eq_pow_finrank (K := S) (V := C), hfinC, hScard, ← pow_mul]
  congr 1
  obtain ⟨g, rfl⟩ := hdvd
  rw [Nat.mul_div_cancel_left g hh, mul_assoc, Nat.mul_div_cancel_left (g * m) hh]

end CFSG.RankThree.Classical
