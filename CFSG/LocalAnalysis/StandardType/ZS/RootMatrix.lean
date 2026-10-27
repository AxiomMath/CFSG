module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRootRefl
import CFSG.LocalAnalysis.StandardType.ZS.CommutingRefl

public section

namespace CFSG.StandardType.ZS

@[expose] def IsCartanModel (p : ℕ) {U : Type} [AddCommGroup U] [Module (ZMod p) U] {ι : Type}
    (K : Matrix ι ι ℤ) (A : Subgroup (U ≃ₗ[ZMod p] U)) : Prop :=
  ∃ (u : ι → U) (φ : ι → Module.Dual (ZMod p) U) (hφ : ∀ i, φ i (u i) = 2),
    (∀ i j, φ i (u j) = (K i j : ZMod p)) ∧ Submodule.span (ZMod p) (Set.range u) = ⊤ ∧
      (⨅ i, LinearMap.ker (φ i)) = ⊥ ∧
        A = Subgroup.closure (Set.range fun i => Module.reflection (hφ i))

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U] {ι : Type}

theorem apply_eq_zero_of_orderOf_eq_two (hp : p ≠ 2) {a b : U} {φ ψ : Module.Dual (ZMod p) U}
    (hφ : φ a = 2) (hψ : ψ b = 2)
    (h : orderOf (Module.reflection hφ * Module.reflection hψ) = 2) : φ b = 0 ∧ ψ a = 0 := by
  have hrs2 : (Module.reflection hφ * Module.reflection hψ) *
      (Module.reflection hφ * Module.reflection hψ) = 1 := by
    have := pow_orderOf_eq_one (Module.reflection hφ * Module.reflection hψ)
    rw [h, pow_two] at this
    exact this
  have hne : Module.reflection hφ ≠ Module.reflection hψ := by
    intro heq
    have hrr : Module.reflection hφ * Module.reflection hφ = 1 := by
      simpa [Module.reflection_inv] using mul_inv_cancel (Module.reflection hφ)
    rw [← heq, hrr, orderOf_one] at h
    norm_num at h
  have hcomm : Commute (Module.reflection hφ) (Module.reflection hψ) := by
    show Module.reflection hφ * Module.reflection hψ =
      Module.reflection hψ * Module.reflection hφ
    calc Module.reflection hφ * Module.reflection hψ
        = (Module.reflection hφ * Module.reflection hψ)⁻¹ :=
          eq_inv_of_mul_eq_one_left hrs2
      _ = (Module.reflection hψ)⁻¹ * (Module.reflection hφ)⁻¹ := mul_inv_rev _ _
      _ = Module.reflection hψ * Module.reflection hφ := by
          rw [Module.reflection_inv, Module.reflection_inv]
  exact ⟨apply_eq_zero_of_commute hp hφ hψ hcomm hne,
    apply_eq_zero_of_commute (a := b) (b := a) (φ := ψ) (ψ := φ) hp hψ hφ hcomm.symm
      (fun hc => hne hc.symm)⟩

theorem natCast_eq_zero_of_unipotent {n : ℕ} {r : U ≃ₗ[ZMod p] U} {w : U}
    {χ : Module.Dual (ZMod p) U} (hχw : χ w = 0)
    (hN : ∀ z, r z = z + χ z • w) (hneq : r ≠ 1) (hn : r ^ n = 1) :
    (n : ZMod p) = 0 := by
  have hpow : ∀ k : ℕ, ∀ y : U, (r ^ k) y = y + (k * χ y) • w := by
    intro k
    induction k with
    | zero => intro y; simp
    | succ k ih =>
      intro y
      rw [pow_succ', LinearEquiv.mul_apply, ih, hN]
      simp only [map_add, map_smul, smul_eq_mul, hχw, mul_zero, add_zero]
      rw [add_assoc, ← add_smul]
      congr 1
      push_cast
      ring_nf
  have hex : ∃ z, χ z • w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hneq (LinearEquiv.ext fun z => by
      rw [hN z, hcon z, add_zero, LinearEquiv.coe_one, id_eq])
  obtain ⟨z, hz⟩ := hex
  have hχz : χ z ≠ 0 := fun h0 => hz (by rw [h0, zero_smul])
  have hw : w ≠ 0 := fun h0 => hz (by rw [h0, smul_zero])
  have hz0 : (n * χ z) • w = 0 := by
    have hh := hpow n z
    rw [hn, LinearEquiv.coe_one, id_eq] at hh
    exact (add_left_cancel_iff (a := z)).mp (by simpa using hh)
  have hnw : (n : ZMod p) • w = 0 := by
    rw [mul_comm] at hz0
    rw [mul_smul] at hz0
    exact (smul_eq_zero.mp hz0).resolve_left hχz
  exact (smul_eq_zero.mp hnw).resolve_right hw

private theorem mul_apply_eq_one_of_linearIndependent {a b : U}
    {φ ψ : Module.Dual (ZMod p) U} (hφ : φ a = 2) (hψ : ψ b = 2)
    (hxy : LinearIndependent (ZMod p) ![a, b]) (hfg : LinearIndependent (ZMod p) ![φ, ψ])
    (h3 : (Module.reflection hφ * Module.reflection hψ) ^ 3 = 1) : φ b * ψ a = 1 := by
  have hcrit := (reflection_mul_reflection_pow_eq_one_iff hφ hψ hxy hfg 3).mp h3
  have hA : ggCoxA (ZMod p) ((3 : ℕ) : ℤ) (φ b * ψ a - 2) = (φ b * ψ a - 2) + 1 :=
    SecFiveRootRefl.ggCoxA_three' (ZMod p) (φ b * ψ a - 2)
  have hB : ggCoxB (ZMod p) ((3 : ℕ) : ℤ) (φ b * ψ a - 2) =
      (φ b * ψ a - 2) * ((φ b * ψ a - 2) + 1) := by
    simp only [ggCoxB]
    norm_num
  rw [hA, hB] at hcrit
  have hsq : ((φ b * ψ a - 2) + 1) * ((φ b * ψ a - 2) + 1) = 0 := by
    linear_combination hcrit.1
  have hlin : (φ b * ψ a - 2) + 1 = 0 := mul_self_eq_zero.mp hsq
  linear_combination hlin

private theorem mul_apply_eq_four_of_not_linearIndependent_dual (hp : p ≠ 2) {a b : U}
    {φ ψ : Module.Dual (ZMod p) U} (hφ : φ a = 2) (hψ : ψ b = 2)
    (hfg : ¬ LinearIndependent (ZMod p) ![φ, ψ]) : φ b * ψ a = 4 := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hinj : ¬ Function.Injective (Finsupp.linearCombination (ZMod p) ![φ, ψ]) := hfg
  rw [Function.Injective] at hinj
  push Not at hinj
  obtain ⟨x, y, hxy, hxyeq⟩ := hinj
  have hxeval : ∀ (z : U) (l : Fin 2 →₀ ZMod p),
      Finsupp.linearCombination (ZMod p) ![φ, ψ] l z = l 0 * φ z + l 1 * ψ z := by
    intro z l
    simp [Finsupp.linearCombination_apply, Finsupp.sum_fintype, Fin.sum_univ_two]
  have hb : (x 0 - y 0) * φ b + (x 1 - y 1) * 2 = 0 := by
    have h := congrArg (fun f : Module.Dual (ZMod p) U => f b) hxy
    rw [hxeval b x, hxeval b y, hψ] at h
    linear_combination h
  have ha : (x 0 - y 0) * 2 + (x 1 - y 1) * ψ a = 0 := by
    have h := congrArg (fun f : Module.Dual (ZMod p) U => f a) hxy
    rw [hxeval a x, hxeval a y, hφ] at h
    linear_combination h
  have hne : (x 0 - y 0) ≠ 0 ∨ (x 1 - y 1) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hxyeq
    ext i
    fin_cases i
    · exact sub_eq_zero.mp hcon.1
    · exact sub_eq_zero.mp hcon.2
  have hs0 : x 0 - y 0 ≠ 0 := by
    rintro h0
    have ht : x 1 - y 1 = 0 := by
      have h := hb
      rw [h0, zero_mul, zero_add] at h
      exact (mul_eq_zero.mp h).resolve_right h2
    rcases hne with h | h
    · exact h h0
    · exact h ht
  have ht0 : x 1 - y 1 ≠ 0 := by
    rintro h0
    have hs : x 0 - y 0 = 0 := by
      have h := ha
      rw [h0, zero_mul, add_zero] at h
      exact (mul_eq_zero.mp h).resolve_right h2
    rcases hne with h | h
    · exact h hs
    · exact h h0
  have hprod : (x 0 - y 0) * (x 1 - y 1) * (φ b * ψ a)
      = (x 0 - y 0) * (x 1 - y 1) * 4 := by
    linear_combination ((x 1 - y 1) * ψ a) * hb - (2 * (x 1 - y 1)) * ha
  exact mul_left_cancel₀ (mul_ne_zero hs0 ht0) hprod

private theorem mul_apply_eq_four_of_not_linearIndependent (hp : p ≠ 2) {a b : U}
    {φ ψ : Module.Dual (ZMod p) U} (hφ : φ a = 2) (hψ : ψ b = 2)
    (h : ¬ LinearIndependent (ZMod p) ![a, b] ∨ ¬ LinearIndependent (ZMod p) ![φ, ψ]) :
    φ b * ψ a = 4 := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have ha0 : a ≠ 0 := by rintro rfl; exact h2 (by simpa using hφ.symm)
  rcases h with hxy | hfg
  · obtain ⟨c, hc⟩ := exists_eq_smul_of_not_linearIndependent (K := ZMod p) ha0 hxy
    have hψb : c * ψ a = 2 := by
      have h := hψ; rw [hc, map_smul, smul_eq_mul] at h; exact h
    have hφb : φ b = 2 * c := by
      rw [hc, map_smul, smul_eq_mul, hφ]; ring
    rw [hφb, mul_assoc, hψb]; norm_num
  · exact mul_apply_eq_four_of_not_linearIndependent_dual hp hφ hψ hfg

theorem apply_mul_apply_eq_one_of_orderOf_eq_three (hp : p ≠ 2) {a b : U}
    {φ ψ : Module.Dual (ZMod p) U} (hφ : φ a = 2) (hψ : ψ b = 2)
    (h : orderOf (Module.reflection hφ * Module.reflection hψ) = 3) : φ b * ψ a = 1 := by
  have h3 : (Module.reflection hφ * Module.reflection hψ) ^ 3 = 1 := by
    have := pow_orderOf_eq_one (Module.reflection hφ * Module.reflection hψ)
    rwa [h] at this
  have hneq : Module.reflection hφ * Module.reflection hψ ≠ 1 := by
    intro heq
    rw [heq, orderOf_one] at h
    norm_num at h
  have : NeZero (2 : ZMod p) := ⟨zmod_two_ne_zero hp⟩
  rcases linearIndependent_and_or_exists_transvection (K := ZMod p) hφ hψ with
    ⟨hxy, hfg⟩ | ⟨w, χ, hχw, hN⟩
  · exact mul_apply_eq_one_of_linearIndependent hφ hψ hxy hfg h3
  · have h3zero : (3 : ZMod p) = 0 := natCast_eq_zero_of_unipotent (n := 3) hχw hN hneq h3
    have h41 : (4 : ZMod p) = 1 := by
      rw [show (4 : ZMod p) = 3 + 1 by norm_num, h3zero, zero_add]
    have h4 : φ b * ψ a = 4 := by
      by_cases hxy : LinearIndependent (ZMod p) ![a, b]
      · by_cases hfg : LinearIndependent (ZMod p) ![φ, ψ]
        · rw [mul_apply_eq_one_of_linearIndependent hφ hψ hxy hfg h3, h41]
        · exact mul_apply_eq_four_of_not_linearIndependent hp hφ hψ (Or.inr hfg)
      · exact mul_apply_eq_four_of_not_linearIndependent hp hφ hψ (Or.inl hxy)
    rw [h4, h41]

private theorem mul_apply_eq_two_of_linearIndependent {a b : U}
    {φ ψ : Module.Dual (ZMod p) U} (hp : p ≠ 2) (hφ : φ a = 2) (hψ : ψ b = 2)
    (hxy : LinearIndependent (ZMod p) ![a, b]) (hfg : LinearIndependent (ZMod p) ![φ, ψ])
    (h4 : (Module.reflection hφ * Module.reflection hψ) ^ 4 = 1)
    (hord : orderOf (Module.reflection hφ * Module.reflection hψ) = 4) : φ b * ψ a = 2 := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hcrit := (reflection_mul_reflection_pow_eq_one_iff hφ hψ hxy hfg 4).mp h4
  have hA : ggCoxA (ZMod p) ((4 : ℕ) : ℤ) (φ b * ψ a - 2)
      = (φ b * ψ a - 2) * ((φ b * ψ a - 2) + 1) :=
    SecFiveRootRefl.ggCoxA_four (ZMod p) (φ b * ψ a - 2)
  have hB : ggCoxB (ZMod p) ((4 : ℕ) : ℤ) (φ b * ψ a - 2)
      = (φ b * ψ a - 2) * ((φ b * ψ a - 2) * (φ b * ψ a - 2) - 1 + (φ b * ψ a - 2)) :=
    SecFiveRootRefl.ggCoxB_four (ZMod p) (φ b * ψ a - 2)
  have hcrit' := hcrit
  rw [hA, hB] at hcrit'
  have hpoly : (φ b * ψ a - 2) * (φ b * ψ a - 2) * ((φ b * ψ a - 2) + 2) = 0 := by
    linear_combination hcrit'.1
  rcases mul_eq_zero.mp hpoly with hpoly0 | hpoly0
  · have he0 : φ b * ψ a - 2 = 0 := mul_self_eq_zero.mp hpoly0
    linear_combination he0
  · have he0 : φ b * ψ a - 2 ≠ 0 := by
      intro hh
      rw [hh, zero_add] at hpoly0
      exact h2 hpoly0
    have he1 : (φ b * ψ a - 2) + 1 ≠ 0 := by
      intro hh
      have hone : (1 : ZMod p) = 0 := by linear_combination hpoly0 - hh
      exact one_ne_zero hone
    have hA0 : φ b * ggCoxA (ZMod p) ((4 : ℕ) : ℤ) (φ b * ψ a - 2) = 0 := by
      linear_combination (φ b) * hcrit.1 - hcrit.2.1
    rw [hA] at hA0
    have hφb : φ b = 0 :=
      (mul_eq_zero.mp hA0).resolve_right (mul_ne_zero he0 he1)
    have hA0' : ψ a * ggCoxA (ZMod p) ((4 : ℕ) : ℤ) (φ b * ψ a - 2) = 0 := hcrit.2.2
    rw [hA] at hA0'
    have hψa : ψ a = 0 :=
      (mul_eq_zero.mp hA0').resolve_right (mul_ne_zero he0 he1)
    have h2sq : (Module.reflection hφ * Module.reflection hψ) ^ 2 = 1 :=
      reflection_mul_reflection_pow_two hφ hψ hφb hψa
    have hdvd : orderOf (Module.reflection hφ * Module.reflection hψ) ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr h2sq
    rw [hord] at hdvd
    norm_num at hdvd

theorem apply_mul_apply_eq_two_of_orderOf_eq_four (hp : p ≠ 2) {a b : U}
    {φ ψ : Module.Dual (ZMod p) U} (hφ : φ a = 2) (hψ : ψ b = 2)
    (h : orderOf (Module.reflection hφ * Module.reflection hψ) = 4) : φ b * ψ a = 2 := by
  have h4 : (Module.reflection hφ * Module.reflection hψ) ^ 4 = 1 := by
    have := pow_orderOf_eq_one (Module.reflection hφ * Module.reflection hψ)
    rwa [h] at this
  have hneq : Module.reflection hφ * Module.reflection hψ ≠ 1 := by
    intro heq
    rw [heq, orderOf_one] at h
    norm_num at h
  have : NeZero (2 : ZMod p) := ⟨zmod_two_ne_zero hp⟩
  rcases linearIndependent_and_or_exists_transvection (K := ZMod p) hφ hψ with
    ⟨hxy, hfg⟩ | ⟨w, χ, hχw, hN⟩
  · exact mul_apply_eq_two_of_linearIndependent hp hφ hψ hxy hfg h4 h
  · exfalso
    have h4zero : (4 : ZMod p) = 0 :=
      natCast_eq_zero_of_unipotent (n := 4) hχw hN hneq h4
    have hdvd : p ∣ 4 := (ZMod.natCast_eq_zero_iff 4 p).mp h4zero
    have hpprime : p.Prime := Fact.out
    have hpge : 2 ≤ p := hpprime.two_le
    have hple : p ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases p
    · exact hp rfl
    · norm_num at hdvd
    · norm_num at hpprime

theorem span_range_eq_top_of_invariant [Nonempty ι] (hp : p ≠ 2) {u : ι → U}
    {φ : ι → Module.Dual (ZMod p) U} (hφ : ∀ i, φ i (u i) = 2)
    (hirr : ∀ W : Submodule (ZMod p) U,
      (∀ a ∈ Subgroup.closure (Set.range fun i => Module.reflection (hφ i)), ∀ w ∈ W, a w ∈ W) →
        W = ⊥ ∨ W = ⊤) :
    Submodule.span (ZMod p) (Set.range u) = ⊤ := by
  let W : Submodule (ZMod p) U := Submodule.span (ZMod p) (Set.range u)
  have hgen : ∀ i, (∀ w ∈ W, Module.reflection (hφ i) w ∈ W) ∧
      (∀ w ∈ W, (Module.reflection (hφ i))⁻¹ w ∈ W) := by
    intro i
    have hu : u i ∈ W := Submodule.subset_span ⟨i, rfl⟩
    constructor
    · intro w hw; rw [Module.reflection_apply]; exact sub_mem hw (Submodule.smul_mem W _ hu)
    · rw [Module.reflection_inv]
      intro w hw; rw [Module.reflection_apply]
      exact sub_mem hw (Submodule.smul_mem W _ hu)
  have hW : ∀ a ∈ Subgroup.closure (Set.range fun i => Module.reflection (hφ i)),
      ∀ w ∈ W, a w ∈ W := by
    intro a ha
    have hprop := Subgroup.closure_induction
      (p := fun g _ => (∀ w ∈ W, g w ∈ W) ∧ (∀ w ∈ W, g⁻¹ w ∈ W))
      (fun x hx => by obtain ⟨i, rfl⟩ := hx; exact hgen i)
      ⟨fun w hw => by simpa using hw, fun w hw => by simpa using hw⟩
      (fun x y _ _ px py => ⟨fun w hw => px.1 (y w) (py.1 w hw),
        fun w hw => by
          rw [mul_inv_rev, LinearEquiv.mul_apply]
          exact py.2 (x⁻¹ w) (px.2 w hw)⟩)
      (fun x _ px => ⟨px.2, by simpa using px.1⟩)
      ha
    exact hprop.1
  change W = ⊤
  rcases hirr W hW with h | h
  · exfalso
    let i : ι := Classical.arbitrary ι
    have hui : u i ≠ 0 := by
      intro h0
      have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
      exact h2 (by simpa [h0] using (hφ i).symm)
    have : u i ∈ W := Submodule.subset_span ⟨i, rfl⟩
    rw [h] at this
    exact hui (by simpa using this)
  · exact h

theorem iInf_ker_eq_bot_of_invariant [Nonempty ι] (hp : p ≠ 2) {u : ι → U}
    {φ : ι → Module.Dual (ZMod p) U} (hφ : ∀ i, φ i (u i) = 2)
    (hirr : ∀ W : Submodule (ZMod p) U,
      (∀ a ∈ Subgroup.closure (Set.range fun i => Module.reflection (hφ i)), ∀ w ∈ W, a w ∈ W) →
        W = ⊥ ∨ W = ⊤) :
    (⨅ i, LinearMap.ker (φ i)) = ⊥ := by
  let W : Submodule (ZMod p) U := ⨅ i, LinearMap.ker (φ i)
  have hfix : ∀ i, ∀ w ∈ W, Module.reflection (hφ i) w = w := by
    intro i w hw
    have hker : φ i w = 0 := iInf_le (fun i => LinearMap.ker (φ i)) i hw
    rw [Module.reflection_apply, hker, zero_smul, sub_zero]
  have hW : ∀ a ∈ Subgroup.closure (Set.range fun i => Module.reflection (hφ i)),
      ∀ w ∈ W, a w ∈ W := by
    intro a ha
    have hprop := Subgroup.closure_induction
      (p := fun g _ => ∀ w ∈ W, g w = w)
      (fun x hx => by obtain ⟨i, rfl⟩ := hx; exact hfix i)
      (fun w hw => by simp)
      (fun x y _ _ px py w hw => by rw [LinearEquiv.mul_apply, py w hw, px w hw])
      (fun x _ px w hw => by
        calc x⁻¹ w = x⁻¹ (x w) := by rw [px w hw]
          _ = w := LinearEquiv.symm_apply_apply x w)
      ha
    exact fun w hw => by rw [hprop w hw]; exact hw
  change W = ⊥
  rcases hirr W hW with h | h
  · exact h
  · exfalso
    let i : ι := Classical.arbitrary ι
    have hui : u i ∉ W := by
      intro hmem
      have hzero : φ i (u i) = 0 := iInf_le (fun i => LinearMap.ker (φ i)) i hmem
      have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
      exact h2 (hφ i ▸ hzero)
    refine hui ?_
    rw [h]
    exact Submodule.mem_top

private theorem cartan_gauge_entries (hp : p ≠ 2) {M : CoxeterMatrix ι} {K : Matrix ι ι ℤ}
    (hK : GGIntCartan M K) (hent : ∀ i j, i ≠ j → K i j = 0 ∨ K i j = -1 ∨ K i j = -2)
    {u : ι → U} {φ : ι → Module.Dual (ZMod p) U} (hφ : ∀ i, φ i (u i) = 2)
    (hord : ∀ i j, orderOf (Module.reflection (hφ i) * Module.reflection (hφ j)) = M i j) :
    (∀ i j, i ≠ j → K i j = 0 → φ i (u j) = 0) ∧
      (∀ i j, i ≠ j → K i j ≠ 0 →
        φ i (u j) * φ j (u i) = (K i j : ZMod p) * (K j i : ZMod p)) ∧
      (∀ i j, i ≠ j → K i j ≠ 0 → (K i j : ZMod p) ≠ 0) := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij hCij
    have hM2 : M i j = 2 := by
      rcases hK.entries hij with ⟨hM, h1, -⟩ | ⟨hM, h1, -⟩ | ⟨hM, h1⟩ | ⟨hM, h1⟩
      · exact hM
      · rw [hCij] at h1; norm_num at h1
      · rcases h1 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [hCij] at h1 <;> norm_num at h1
      · rcases h1 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [hCij] at h1 <;> norm_num at h1
    exact (apply_eq_zero_of_orderOf_eq_two hp (hφ i) (hφ j) (by rw [hord i j, hM2])).1
  · intro i j hij hCij
    rcases hK.entries hij with ⟨hM, h1, -⟩ | ⟨hM, h1, h2⟩ | ⟨hM, h1⟩ | ⟨hM, h1⟩
    · exact absurd h1 hCij
    · have h3 : orderOf (Module.reflection (hφ i) * Module.reflection (hφ j)) = 3 := by
        rw [hord i j, hM]
      rw [apply_mul_apply_eq_one_of_orderOf_eq_three hp (hφ i) (hφ j) h3, h1, h2]
      norm_num
    · have h4 : orderOf (Module.reflection (hφ i) * Module.reflection (hφ j)) = 4 := by
        rw [hord i j, hM]
      rw [apply_mul_apply_eq_two_of_orderOf_eq_four hp (hφ i) (hφ j) h4]
      rcases h1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> norm_num
    · rcases h1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rcases hent j i (Ne.symm hij) with h0 | h0 | h0 <;> rw [h2] at h0 <;> norm_num at h0
      · rcases hent i j hij with h0 | h0 | h0 <;> rw [h1] at h0 <;> norm_num at h0
  · intro i j hij hCij
    rcases hent i j hij with h1 | h1 | h1
    · exact absurd h1 hCij
    · rw [h1]; norm_num
    · rw [h1]; push_cast; exact neg_ne_zero.mpr h2

private theorem gauge_root_self {u : ι → U} {φ : ι → Module.Dual (ZMod p) U} {c : ι → ZMod p}
    (hφ : ∀ i, φ i (u i) = 2) (hc0 : ∀ i, c i ≠ 0) :
    ∀ i, ((c i)⁻¹ • φ i) (c i • u i) = 2 := by
  intro i
  rw [LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (hc0 i), one_mul]
  exact hφ i

private theorem gauge_reflection_eq {u : ι → U} {φ : ι → Module.Dual (ZMod p) U}
    {c : ι → ZMod p} (hφ : ∀ i, φ i (u i) = 2) (hc0 : ∀ i, c i ≠ 0)
    (hφ' : ∀ i, ((c i)⁻¹ • φ i) (c i • u i) = 2) :
    ∀ i, Module.reflection (hφ' i) = Module.reflection (hφ i) := by
  intro i
  ext v
  change v - ((c i)⁻¹ • φ i) v • (c i • u i) = v - φ i v • u i
  rw [LinearMap.smul_apply, smul_eq_mul, smul_smul]
  congr 1
  rw [mul_assoc, mul_comm (φ i v) (c i), ← mul_assoc, inv_mul_cancel₀ (hc0 i), one_mul]

private theorem gauge_span {u : ι → U} {c : ι → ZMod p} (hc0 : ∀ i, c i ≠ 0)
    (hspan : Submodule.span (ZMod p) (Set.range u) = ⊤) :
    Submodule.span (ZMod p) (Set.range fun j => c j • u j) = ⊤ := by
  have hle1 : Submodule.span (ZMod p) (Set.range fun j => c j • u j)
      ≤ Submodule.span (ZMod p) (Set.range u) := by
    rw [Submodule.span_le]
    rintro x ⟨j, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hle2 : Submodule.span (ZMod p) (Set.range u)
      ≤ Submodule.span (ZMod p) (Set.range fun j => c j • u j) := by
    rw [Submodule.span_le]
    rintro x ⟨j, rfl⟩
    have h : u j = (c j)⁻¹ • (c j • u j) := by
      rw [smul_smul, inv_mul_cancel₀ (hc0 j), one_smul]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  rw [le_antisymm hle1 hle2, hspan]

private theorem gauge_ker {φ : ι → Module.Dual (ZMod p) U} {c : ι → ZMod p}
    (hc0 : ∀ i, c i ≠ 0) (hker : (⨅ i, LinearMap.ker (φ i)) = ⊥) :
    (⨅ i, LinearMap.ker ((c i)⁻¹ • φ i)) = ⊥ := by
  have hker' : (⨅ i, LinearMap.ker ((c i)⁻¹ • φ i)) = (⨅ i, LinearMap.ker (φ i)) := by
    apply le_antisymm
    · refine le_iInf fun i => ?_
      exact (iInf_le (fun i => LinearMap.ker ((c i)⁻¹ • φ i)) i).trans_eq
        (LinearMap.ker_smul (φ i) ((c i)⁻¹) (inv_ne_zero (hc0 i)))
    · refine le_iInf fun i => ?_
      exact (iInf_le (fun i => LinearMap.ker (φ i)) i).trans_eq
        (LinearMap.ker_smul (φ i) ((c i)⁻¹) (inv_ne_zero (hc0 i))).symm
  rw [hker', hker]

private theorem gauge_pairing {M : CoxeterMatrix ι} {K : Matrix ι ι ℤ}
    {u : ι → U} {φ : ι → Module.Dual (ZMod p) U} {c : ι → ZMod p}
    (hK : GGIntCartan M K) (hφ : ∀ i, φ i (u i) = 2) (hc0 : ∀ i, c i ≠ 0)
    (hc : ∀ i j, i ≠ j → (c i)⁻¹ * c j * φ i (u j) = (K i j : ZMod p)) :
    ∀ i j, ((c i)⁻¹ • φ i) (c j • u j) = (K i j : ZMod p) := by
  intro i j
  by_cases hij : i = j
  · subst hij
    rw [LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ (hc0 i), one_mul, hφ i, hK.1]
    norm_num
  · rw [LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul]
    simpa only [mul_assoc] using hc i j hij

theorem isCartanModel_of_orderOf (hp : p ≠ 2) {M : CoxeterMatrix ι} {K : Matrix ι ι ℤ}
    (hK : GGIntCartan M K) (hent : ∀ i j, i ≠ j → K i j = 0 ∨ K i j = -1 ∨ K i j = -2)
    (hT : SecFiveRootRefl.CartanTree K) {u : ι → U} {φ : ι → Module.Dual (ZMod p) U}
    (hφ : ∀ i, φ i (u i) = 2)
    (hord : ∀ i j, orderOf (Module.reflection (hφ i) * Module.reflection (hφ j)) = M i j)
    (hspan : Submodule.span (ZMod p) (Set.range u) = ⊤)
    (hker : (⨅ i, LinearMap.ker (φ i)) = ⊥) :
    IsCartanModel p K (Subgroup.closure (Set.range fun i => Module.reflection (hφ i))) := by
  classical
  obtain ⟨par, root, depth, hpar, hdepth⟩ := hT
  obtain ⟨hP0, hPP, hAK⟩ := cartan_gauge_entries hp hK hent hφ hord
  obtain ⟨c, hc0, hc⟩ :=
    SecFiveRootRefl.exists_gauge_of_tree (K := ZMod p) (fun i j => K i j) (fun i j => φ i (u j))
      par root depth hP0 hPP hAK hpar hdepth
  have hφ' : ∀ i, ((c i)⁻¹ • φ i) (c i • u i) = 2 := gauge_root_self hφ hc0
  have hrefl : ∀ i, Module.reflection (hφ' i) = Module.reflection (hφ i) :=
    gauge_reflection_eq hφ hc0 hφ'
  unfold IsCartanModel
  refine ⟨fun j => c j • u j, fun i => (c i)⁻¹ • φ i, hφ', ?_, ?_, ?_, ?_⟩
  · exact gauge_pairing hK hφ hc0 hc
  · exact gauge_span hc0 hspan
  · exact gauge_ker hc0 hker
  · rw [show (fun i => Module.reflection (hφ' i)) = (fun i => Module.reflection (hφ i)) from
        funext hrefl]

theorem IsCartanModel.of_reindex {κ : Type} (e : κ ≃ ι) {K : Matrix κ κ ℤ}
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (h : IsCartanModel p (Matrix.reindex e e K) A) :
    IsCartanModel p K A := by
  unfold IsCartanModel at h ⊢
  obtain ⟨u, φ, hφ, hdata, hspan, hker, hA⟩ := h
  refine ⟨fun i => u (e i), fun i => φ (e i), fun i => hφ (e i), ?_, ?_, ?_, ?_⟩
  · intro i j
    rw [hdata (e i) (e j)]
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  · rw [show Set.range (fun i : κ => u (e i)) = Set.range u from
        e.surjective.range_comp u, hspan]
  · rw [show (⨅ i : κ, LinearMap.ker (φ (e i))) = (⨅ j : ι, LinearMap.ker (φ j)) from
        le_antisymm
          (le_iInf fun j => by obtain ⟨i, rfl⟩ := e.surjective j; exact iInf_le _ i)
          (le_iInf fun i => iInf_le _ (e i)), hker]
  · rw [show Set.range (fun i : κ => Module.reflection (hφ (e i)))
          = Set.range (fun j : ι => Module.reflection (hφ j)) from
        e.surjective.range_comp (fun j => Module.reflection (hφ j)), hA]

theorem IsCartanModel.finrank_eq_rank [Fintype ι] {K : Matrix ι ι ℤ}
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (h : IsCartanModel p K A) :
    Module.finrank (ZMod p) U = (K.map (Int.cast : ℤ → ZMod p)).rank := by
  unfold IsCartanModel at h
  obtain ⟨u, φ, hφ, hdata, hspan, hker, hA⟩ := h
  let Φ : U →ₗ[ZMod p] (ι → ZMod p) :=
    { toFun := fun v i => φ i v
      map_add' := fun x y => funext fun i => map_add (φ i) x y
      map_smul' := fun c x => funext fun i => map_smul (φ i) c x }
  have hkerΦ : LinearMap.ker Φ = ⨅ i, LinearMap.ker (φ i) := by
    ext v
    simp [Φ, LinearMap.mem_ker, Submodule.mem_iInf, funext_iff]
  have hkerbot : LinearMap.ker Φ = ⊥ := by rw [hkerΦ, hker]
  have hΦinj : Function.Injective Φ := by
    intro x y hxy
    have hmem : x - y ∈ LinearMap.ker Φ := by
      rw [LinearMap.mem_ker, map_sub, hxy]
      exact sub_self _
    rw [hkerbot] at hmem
    exact sub_eq_zero.mp (by simpa using hmem)
  have hLtop : LinearMap.range (Fintype.linearCombination (ZMod p) u) = ⊤ := by
    rw [Fintype.range_linearCombination, hspan]
  have hcomp : Φ.comp (Fintype.linearCombination (ZMod p) u) =
      (K.map (Int.cast : ℤ → ZMod p)).mulVecLin := by
    ext c i
    change (φ i) (Fintype.linearCombination (ZMod p) u c)
      = ((K.map (Int.cast : ℤ → ZMod p)).mulVecLin c) i
    rw [Fintype.linearCombination_apply, map_sum]
    simp only [map_smul, smul_eq_mul, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
      Matrix.map_apply, hdata]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  calc Module.finrank (ZMod p) U
      = Module.finrank (ZMod p) (LinearMap.range Φ) :=
        (LinearMap.finrank_range_of_inj hΦinj).symm
    _ = Module.finrank (ZMod p)
          (LinearMap.range (Φ.comp (Fintype.linearCombination (ZMod p) u))) := by
        rw [LinearMap.range_comp_of_range_eq_top Φ hLtop]
    _ = Module.finrank (ZMod p)
          (LinearMap.range ((K.map (Int.cast : ℤ → ZMod p)).mulVecLin)) := by
        rw [hcomp]
    _ = (K.map (Int.cast : ℤ → ZMod p)).rank := rfl

theorem IsCartanModel.finrank_le_card_index [Fintype ι] {K : Matrix ι ι ℤ}
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (h : IsCartanModel p K A) :
    Module.finrank (ZMod p) U ≤ Fintype.card ι := by
  unfold IsCartanModel at h
  obtain ⟨u, φ, hφ, -, hspan, -, -⟩ := h
  exact finrank_le_of_span_eq_top hspan

theorem IsCartanModel.finrank_eq_card_of_det [Fintype ι] [DecidableEq ι] {K : Matrix ι ι ℤ}
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (h : IsCartanModel p K A)
    (hdet : ((K.det : ℤ) : ZMod p) ≠ 0) :
    Module.finrank (ZMod p) U = Fintype.card ι := by
  have hdet' : (K.map (Int.cast : ℤ → ZMod p)).det ≠ 0 := by
    have h : (K.map (Int.cast : ℤ → ZMod p)).det = ((K.det : ℤ) : ZMod p) := by
      simpa using (RingHom.map_det (Int.castRingHom (ZMod p)) K).symm
    rw [h]
    exact hdet
  rw [IsCartanModel.finrank_eq_rank h]
  exact Matrix.rank_of_det_ne_zero hdet'

end CFSG.StandardType.ZS

end
