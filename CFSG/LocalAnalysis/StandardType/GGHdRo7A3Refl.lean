module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7A3Basic
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallBridge
import CFSG.LocalAnalysis.StandardType.GGQTwoTransvectionFreeRules
import CFSG.LocalAnalysis.StandardType.GGWAutCommon
import Mathlib.Tactic.Module
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.StandardType.HdRo7A3

open CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU
open CFSG.StandardType.HdRo7SU.Small

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem hdRo7A3ReflAux_two_ne_zero : (2 : ZMod 3) ≠ 0 := by decide

private theorem hdRo7A3ReflAux_three_sum :
    ∀ a b c : ZMod 3, a ≠ b → a ≠ c → b ≠ c → a + b + c = 0 := by
  decide

private theorem hdRo7A3ReflAux_neg_two_mul : ∀ x : ZMod 3, -(2 * x) = x := by decide

private theorem hdRo7A3ReflAux_two_mul_neg : ∀ x : ZMod 3, (2 : ZMod 3) * x = -x := by
  decide

private theorem hdRo7A3ReflAux_third :
    ∀ a b x : ZMod 3, a ≠ b → x ≠ a → x ≠ b → x = -(a + b) := by
  decide

private theorem hdRo7A3ReflAux_neg_two_eq_one : (-2 : ZMod 3) = 1 := by decide

private theorem hdRo7A3ReflAux_zero_ne_one : (0 : ZMod 3) ≠ 1 := by decide

private theorem hdRo7A3ReflAux_zero_ne_two : (0 : ZMod 3) ≠ 2 := by decide

private theorem hdRo7A3ReflAux_one_ne_two : (1 : ZMod 3) ≠ 2 := by decide

private theorem hdRo7A3ReflAux_sum_zmod3 {M : Type} [AddCommMonoid M] (F : ZMod 3 → M) :
    ∑ a : ZMod 3, F a = F 0 + F 1 + F 2 := by
  have hmem : ∀ x : ZMod 3, x ∈ ({0, 1, 2} : Finset (ZMod 3)) := by decide
  have huniv : (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} :=
    (Finset.eq_univ_of_forall hmem).symm
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide)]
  simp only [Finset.sum_singleton]
  abel

private theorem hdRo7A3ReflAux_mem012 (a : ZMod 3) : a = 0 ∨ a = 1 ∨ a = 2 := by
  have hmem : a ∈ ({0, 1, 2} : Finset (ZMod 3)) := by decide +revert
  simpa using hmem

private theorem hdRo7A3ReflAux_fiber {m : ℕ} (ĥ : Fin m → ZMod 3) (G : ZMod 3 → ZMod 3) :
    ∑ i, G (ĥ i) =
      ∑ a : ZMod 3, ((Finset.univ.filter fun i => ĥ i = a).card : ZMod 3) * G a := by
  have h := Finset.sum_fiberwise' (Finset.univ : Finset (Fin m)) ĥ G
  rw [← h]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_const, nsmul_eq_mul]

private theorem hdRo7A3ReflAux_card_fiber {m : ℕ} (ĥ : Fin m → ZMod 3) :
    (Finset.univ.filter fun i => ĥ i = 0).card +
      (Finset.univ.filter fun i => ĥ i = 1).card +
      (Finset.univ.filter fun i => ĥ i = 2).card = m := by
  have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin m))) (f := ĥ)
    (t := (Finset.univ : Finset (ZMod 3))) (fun i _ => Finset.mem_univ _)
  rw [Finset.card_univ, Fintype.card_fin] at h
  rw [hdRo7A3ReflAux_sum_zmod3
    (fun a => (Finset.univ.filter fun i => ĥ i = a).card)] at h
  exact h.symm

private theorem hdRo7A3ReflAux_exists_g {m : ℕ} {ĥ f : Fin m → ZMod 3}
    (hiff : ∀ i j, f i = f j ↔ ĥ i = ĥ j) :
    ∃ g : ZMod 3 → ZMod 3, ∀ i, f i = g (ĥ i) := by
  classical
  refine ⟨fun a => if h : ∃ i, ĥ i = a then f (Classical.choose h) else 0, fun i => ?_⟩
  have hex : ∃ j, ĥ j = ĥ i := ⟨i, rfl⟩
  have hch : ĥ (Classical.choose hex) = ĥ i := Classical.choose_spec hex
  have h1 : (if h : ∃ j, ĥ j = ĥ i then f (Classical.choose h) else 0) =
      f (Classical.choose hex) := by
    rw [dite_eq_left hex]
  show f i = (if h : ∃ j, ĥ j = ĥ i then f (Classical.choose h) else 0)
  rw [h1]
  exact (hiff i (Classical.choose hex)).mpr hch.symm

private theorem hdRo7A3ReflAux_congr {m : ℕ} (hm : 3 ∣ m) {ĥ : Fin m → ZMod 3}
    (hsum : ∑ i, ĥ i = 0) :
    ∀ a : ZMod 3, ((Finset.univ.filter fun i => ĥ i = a).card : ZMod 3) =
      ((Finset.univ.filter fun i => ĥ i = 0).card : ZMod 3) := by
  have hA : ((Finset.univ.filter fun i => ĥ i = 0).card : ZMod 3) +
      ((Finset.univ.filter fun i => ĥ i = 1).card : ZMod 3) +
      ((Finset.univ.filter fun i => ĥ i = 2).card : ZMod 3) = 0 := by
    have hfib := hdRo7A3ReflAux_fiber ĥ (fun _ => (1 : ZMod 3))
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hfib
    rw [hdRo7A3ReflAux_sum_zmod3 (fun a =>
      ((Finset.univ.filter fun i => ĥ i = a).card : ZMod 3) * 1)] at hfib
    have h1 : ((Finset.univ.filter fun i => ĥ i = 0).card : ZMod 3) * 1 +
        ((Finset.univ.filter fun i => ĥ i = 1).card : ZMod 3) * 1 +
        ((Finset.univ.filter fun i => ĥ i = 2).card : ZMod 3) * 1 = (m : ZMod 3) :=
      hfib.symm
    rw [mul_one, mul_one, mul_one] at h1
    rw [h1, ZMod.natCast_eq_zero_iff]
    exact hm
  have hB : ((Finset.univ.filter fun i => ĥ i = 1).card : ZMod 3) +
      2 * ((Finset.univ.filter fun i => ĥ i = 2).card : ZMod 3) = 0 := by
    have hfib := hdRo7A3ReflAux_fiber ĥ (fun a => a)
    rw [hsum] at hfib
    rw [hdRo7A3ReflAux_sum_zmod3 (fun a =>
      ((Finset.univ.filter fun i => ĥ i = a).card : ZMod 3) * a)] at hfib
    linear_combination -hfib
  have hN0 : ((Finset.univ.filter fun i => ĥ i = 0).card : ZMod 3) =
      ((Finset.univ.filter fun i => ĥ i = 2).card : ZMod 3) := by
    linear_combination hA - hB
  have hN1 : ((Finset.univ.filter fun i => ĥ i = 1).card : ZMod 3) =
      ((Finset.univ.filter fun i => ĥ i = 2).card : ZMod 3) := by
    have hB1 : ((Finset.univ.filter fun i => ĥ i = 1).card : ZMod 3) =
        -(2 * ((Finset.univ.filter fun i => ĥ i = 2).card : ZMod 3)) := by
      linear_combination hB
    exact hB1.trans (hdRo7A3ReflAux_neg_two_mul _)
  intro a
  rcases hdRo7A3ReflAux_mem012 a with rfl | rfl | rfl
  · rfl
  · exact hN1.trans hN0.symm
  · exact hN0.symm

private theorem hdRo7A3ReflAux_count {m : ℕ} (hm : 3 ∣ m) {ĥ f : Fin m → ZMod 3}
    (hsum : ∑ i, ĥ i = 0) (hiff : ∀ i j, f i = f j ↔ ĥ i = ĥ j) :
    ∑ i, f i = 0 := by
  classical
  obtain ⟨g, hg⟩ := hdRo7A3ReflAux_exists_g hiff
  have hcongr := hdRo7A3ReflAux_congr hm hsum
  have hfib : ∑ i, f i = ∑ a : ZMod 3,
      ((Finset.univ.filter fun i => ĥ i = a).card : ZMod 3) * g a := by
    rw [show ∑ i, f i = ∑ i, g (ĥ i) from Finset.sum_congr rfl fun i _ => hg i]
    exact hdRo7A3ReflAux_fiber ĥ g
  have hstep : ∑ a : ZMod 3,
      ((Finset.univ.filter fun i => ĥ i = a).card : ZMod 3) * g a =
      ((Finset.univ.filter fun i => ĥ i = 0).card : ZMod 3) * ∑ a : ZMod 3, g a := by
    rw [hdRo7A3ReflAux_sum_zmod3 (fun a =>
        ((Finset.univ.filter fun i => ĥ i = a).card : ZMod 3) * g a),
      hdRo7A3ReflAux_sum_zmod3 g, hcongr 0, hcongr 1, hcongr 2]
    ring
  rw [hfib, hstep]
  by_cases hall : ∀ a : ZMod 3, (Finset.univ.filter fun i => ĥ i = a).card ≠ 0
  · have hinj : Function.Injective g := by
      intro a b hab
      by_contra hne
      have ha : 0 < (Finset.univ.filter fun i => ĥ i = a).card :=
        Nat.pos_of_ne_zero (hall a)
      have hb : 0 < (Finset.univ.filter fun i => ĥ i = b).card :=
        Nat.pos_of_ne_zero (hall b)
      obtain ⟨i, hi⟩ := Finset.card_pos.mp ha
      obtain ⟨j, hj⟩ := Finset.card_pos.mp hb
      rw [Finset.mem_filter] at hi hj
      have hfi : f i = g a := by rw [hg i, hi.2]
      have hfj : f j = g b := by rw [hg j, hj.2]
      have heq : f i = f j := by rw [hfi, hfj, hab]
      have hlev : ĥ i = ĥ j := (hiff i j).mp heq
      rw [hi.2, hj.2] at hlev
      exact hne hlev
    have hsumg : ∑ a : ZMod 3, g a = 0 := by
      rw [hdRo7A3ReflAux_sum_zmod3 g]
      exact hdRo7A3ReflAux_three_sum (g 0) (g 1) (g 2)
        (fun h => absurd (hinj h) (by decide))
        (fun h => absurd (hinj h) (by decide))
        (fun h => absurd (hinj h) (by decide))
    rw [hsumg, mul_zero]
  · push Not at hall
    obtain ⟨a, ha⟩ := hall
    have hzero : ((Finset.univ.filter fun i => ĥ i = 0).card : ZMod 3) = 0 := by
      rw [← hcongr a, ha]
      simp
    rw [hzero, zero_mul]

private theorem hdRo7A3ReflAux_dual_eq_sum {m : ℕ} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {θ : (Fin m → ZMod 3) →ₗ[ZMod 3] V} (φ : Module.Dual (ZMod 3) V)
    (u : Fin m → ZMod 3) : φ (θ u) = ∑ i, φ (θ (Pi.single i 1)) * u i := by
  have h := LinearMap.pi_apply_eq_sum_univ (φ.comp θ) u
  have hsingle : ∀ i : Fin m,
      (fun j => if i = j then (1 : ZMod 3) else 0) = Pi.single i 1 := by
    intro i
    funext j
    by_cases h : i = j
    · subst h; simp
    · have hji : j ≠ i := fun hh => h hh.symm
      rw [Pi.single_eq_of_ne hji]
      simp [h]
  have h2 : ∀ i : Fin m, u i • (φ.comp θ) (fun j => if i = j then 1 else 0) =
      φ (θ (Pi.single i 1)) * u i := by
    intro i
    rw [hsingle i]
    simp [LinearMap.comp_apply, smul_eq_mul, mul_comm]
  calc φ (θ u) = (φ.comp θ) u := rfl
    _ = ∑ i, u i • (φ.comp θ) (fun j => if i = j then 1 else 0) := h
    _ = ∑ i, φ (θ (Pi.single i 1)) * u i := Finset.sum_congr rfl fun i _ => h2 i

private theorem hdRo7A3ReflAux_levels {m : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [Fact (Nat.Prime 3)] {θ : (Fin m → ZMod 3) →ₗ[ZMod 3] V} {z : V}
    {H A : Subgroup (V ≃ₗ[ZMod 3] V)} (hD : A3LinData 3 m V θ z H A)
    (hpm : 3 ∣ m) (hm : 3 ≤ m) {r : V ≃ₗ[ZMod 3] V} (hrH : r ∈ H)
    {c : V} {φ : Module.Dual (ZMod 3) V} (hφc : φ c = 2) (hrf : ∀ v, r v = v - φ v • c)
    {ĥ : Fin m → ZMod 3} (hĥU : ĥ ∈ a3Aug 3 m) (hĥc : θ ĥ = c) :
    ∀ i j, i ≠ j → (φ (θ (Pi.single i 1)) = φ (θ (Pi.single j 1)) ↔ ĥ i = ĥ j) := by
  have hfr := hD.hfr
  have hTF : CFSG.StandardType.QTwoLin.TransvectionFree A := fun g hg hgt =>
    hD.hNoT g hg (c2Transv_of_isTransvectionLin g hgt)
  intro i j hij
  obtain ⟨t, ψ, htU, htz, hψU, _hψz, htf, _htr⟩ :=
    a3_transp (p := 3) rfl hfr hpm hm hij
  have htH : t ∈ H := hD.hPH t ⟨Equiv.swap i j, htU, htz⟩
  have hwij : (Pi.single i 1 - Pi.single j 1 : Fin m → ZMod 3) ∈ a3Aug 3 m :=
    a3_single_sub_mem i j
  have hψw : ψ (θ (Pi.single i 1 - Pi.single j 1)) = 2 := by
    rw [hψU _ hwij]
    have h1 : (Pi.single i 1 - Pi.single j 1 : Fin m → ZMod 3) i = 1 := by
      simp [Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij]
    have h2 : (Pi.single i 1 - Pi.single j 1 : Fin m → ZMod 3) j = -1 := by
      simp [Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij.symm]
    rw [h1, h2]
    norm_num
  have hzp := CFSG.StandardType.QTwoLin.zero_pair_iff_of_transvectionFree (K := ZMod 3) hTF
    (hD.hHA hrH) (hD.hHA htH) hφc hψw hrf htf
  have hψc : ψ c = ĥ i - ĥ j := by rw [← hĥc, hψU ĥ hĥU]
  constructor
  · intro h
    have h0 : φ (θ (Pi.single i 1 - Pi.single j 1)) = 0 := by
      rw [map_sub, map_sub]
      simp [h]
    rw [hzp.mp h0] at hψc
    exact sub_eq_zero.mp hψc.symm
  · intro h
    have h0 : ψ c = 0 := by rw [hψc, h]; simp
    have h1 := hzp.mpr h0
    rw [map_sub, map_sub] at h1
    exact sub_eq_zero.mp h1

private theorem hdRo7A3ReflAux_neg_perm {m : ℕ} {ĥ : Fin m → ZMod 3} {a b : ZMod 3}
    (hab : a ≠ b) (hcard : (Finset.univ.filter fun i => ĥ i = a).card =
      (Finset.univ.filter fun i => ĥ i = b).card) :
    ∃ τ : Equiv.Perm (Fin m), ∀ i, ĥ (τ i) = -ĥ i + (a + b) := by
  classical
  have hcard' : Fintype.card {i : Fin m // ĥ i = a} = Fintype.card {i : Fin m // ĥ i = b} := by
    rw [Fintype.card_subtype, Fintype.card_subtype]
    exact hcard
  let e : {i : Fin m // ĥ i = a} ≃ {i : Fin m // ĥ i = b} := Fintype.equivOfCardEq hcard'
  let τf : Fin m → Fin m := fun i =>
    if h : ĥ i = a then (e ⟨i, h⟩).val
    else if h' : ĥ i = b then (e.symm ⟨i, h'⟩).val
    else i
  have hτa : ∀ i (h : ĥ i = a), τf i = (e ⟨i, h⟩).val := by
    intro i h
    simp only [τf, dite_eq_left h]
  have hτb : ∀ i (h : ĥ i = b), τf i = (e.symm ⟨i, h⟩).val := by
    intro i h
    have h1 : ¬ (ĥ i = a) := by rw [h]; exact hab.symm
    simp only [τf, dite_eq_right h1, dite_eq_left h]
  have hτc : ∀ i, ĥ i ≠ a → ĥ i ≠ b → τf i = i := by
    intro i h h'
    simp only [τf, dite_eq_right h, dite_eq_right h']
  have hval_a : ∀ i (h : ĥ i = a), ĥ (τf i) = b := by
    intro i h
    rw [hτa i h]
    exact (e ⟨i, h⟩).2
  have hval_b : ∀ i (h : ĥ i = b), ĥ (τf i) = a := by
    intro i h
    rw [hτb i h]
    exact (e.symm ⟨i, h⟩).2
  have hinv : ∀ i, τf (τf i) = i := by
    intro i
    by_cases h : ĥ i = a
    · have hb : ĥ (τf i) = b := hval_a i h
      have h2 : τf (τf i) = (e.symm ⟨τf i, hb⟩).val := hτb (τf i) hb
      rw [h2]
      have hsub : (⟨τf i, hb⟩ : {j : Fin m // ĥ j = b}) = e ⟨i, h⟩ :=
        Subtype.ext (hτa i h)
      rw [hsub, Equiv.symm_apply_apply]
    · by_cases h' : ĥ i = b
      · have ha : ĥ (τf i) = a := hval_b i h'
        have h2 : τf (τf i) = (e ⟨τf i, ha⟩).val := hτa (τf i) ha
        rw [h2]
        have hsub : (⟨τf i, ha⟩ : {j : Fin m // ĥ j = a}) = e.symm ⟨i, h'⟩ :=
          Subtype.ext (hτb i h')
        rw [hsub, Equiv.apply_symm_apply]
      · rw [hτc i h h', hτc i h h']
  have hinj : Function.Injective τf := by
    intro x y hxy
    have := congrArg τf hxy
    rwa [hinv x, hinv y] at this
  refine ⟨Equiv.ofBijective τf (Finite.injective_iff_bijective.mp hinj), fun i => ?_⟩
  rw [Equiv.ofBijective_apply]
  by_cases h : ĥ i = a
  · rw [hval_a i h, h]; ring
  · by_cases h' : ĥ i = b
    · rw [hval_b i h', h']; ring
    · rw [hτc i h h']
      have hc : ĥ i = -(a + b) := hdRo7A3ReflAux_third a b (ĥ i) hab h h'
      rw [hc]
      linear_combination -(hdRo7A3ReflAux_two_mul_neg (a + b))

private theorem hdRo7A3ReflAux_dvd_of_distinct {n0 n1 n2 r : ℕ} (h0 : n0 ≤ 9) (h1 : n1 ≤ 9)
    (h2 : n2 ≤ 9) (hs : n0 + n1 + n2 = 9) (hd01 : n0 ≠ n1) (hd02 : n0 ≠ n2)
    (hd12 : n1 ≠ n2) (hr0 : n0 % 3 = r) (hr1 : n1 % 3 = r) (hr2 : n2 % 3 = r) : r = 0 := by
  have e0 : n0 = 3 * (n0 / 3) + r := by
    have := Nat.div_add_mod n0 3
    omega
  have e1 : n1 = 3 * (n1 / 3) + r := by
    have := Nat.div_add_mod n1 3
    omega
  have e2 : n2 = 3 * (n2 / 3) + r := by
    have := Nat.div_add_mod n2 3
    omega
  obtain ⟨q0, hq0⟩ : ∃ q : ℕ, n0 = 3 * q + r := ⟨n0 / 3, e0⟩
  obtain ⟨q1, hq1⟩ : ∃ q : ℕ, n1 = 3 * q + r := ⟨n1 / 3, e1⟩
  obtain ⟨q2, hq2⟩ : ∃ q : ℕ, n2 = 3 * q + r := ⟨n2 / 3, e2⟩
  have hr3 : r < 3 := by
    rw [← hr0]
    exact Nat.mod_lt _ (by norm_num)
  interval_cases r <;> omega

theorem a3_reflU_holds : A3ReflULeaf := by
  intro p hpFact m V instV instM θ z H A hD hU r hrH hrr
  have hp3 : p = 3 := hD.hp
  subst p
  have hpm : 3 ∣ m := hD.h3
  have hm3 : 3 ≤ m := by have := hD.hm; omega
  obtain ⟨c, φ, hφc, hreq⟩ := (CFSG.StandardType.ggLinRefl_iff_isReflLin r).mp hrr
  have hrf : ∀ v, r v = v - φ v • c := fun v => by
    rw [hreq, Module.reflection_apply]
  obtain ⟨u, hu, k, hk⟩ := hD.hfr.2.1 c
  have h1U : (fun _ : Fin m => (1 : ZMod 3)) ∈ a3Aug 3 m := a3_const_mem hpm 1
  let ĥ : Fin m → ZMod 3 := u + k • (fun _ : Fin m => (1 : ZMod 3))
  have hĥU : ĥ ∈ a3Aug 3 m :=
    (a3Aug 3 m).add_mem hu ((a3Aug 3 m).smul_mem k h1U)
  have hĥc : θ ĥ = c := by
    have h1 : θ ĥ = θ u + k • z := by
      rw [map_add, map_smul, hU]
    rw [h1, hk]
  let f : Fin m → ZMod 3 := fun i => φ (θ (Pi.single i 1))
  have hlevel : ∀ i j, i ≠ j → (f i = f j ↔ ĥ i = ĥ j) :=
    hdRo7A3ReflAux_levels hD hpm hm3 hrH hφc hrf hĥU hĥc
  have hiff : ∀ i j, f i = f j ↔ ĥ i = ĥ j := by
    intro i j
    by_cases hij : i = j
    · subst hij; simp
    · exact hlevel i j hij
  have hsumf : ∑ i, f i = 0 := hdRo7A3ReflAux_count hpm hĥU hiff
  have hone : (fun _ : Fin m => (1 : ZMod 3)) = ∑ i, Pi.single i 1 :=
    (Finset.univ_sum_single (fun _ : Fin m => (1 : ZMod 3))).symm
  have hz0 : φ z = 0 := by
    calc φ z = φ (θ (fun _ : Fin m => (1 : ZMod 3))) := by rw [hU]
      _ = φ (θ (∑ i, Pi.single i 1)) := by rw [hone]
      _ = φ (∑ i, θ (Pi.single i 1)) := by rw [map_sum]
      _ = ∑ i, φ (θ (Pi.single i 1)) := by rw [map_sum]
      _ = 0 := hsumf
  rw [hrf z, hz0, zero_smul, sub_zero]

theorem a3_reflM9_holds : A3ReflM9Leaf := by
  intro p hpFact m V instV instM θ z H A hD hM0 hm9 r hrH hrr hspan
  have hp3 : p = 3 := hD.hp
  subst p
  subst m
  have hpm : 3 ∣ 9 := by norm_num
  have hm3 : 3 ≤ 9 := by norm_num
  obtain ⟨c, φ, hφc, hreq⟩ := (CFSG.StandardType.ggLinRefl_iff_isReflLin r).mp hrr
  have hrf : ∀ v, r v = v - φ v • c := fun v => by
    rw [hreq, Module.reflection_apply]
  have hrc : r c = -c := by rw [hrf, hφc]; module
  have hcmove : c ∈ ggLinMove r := by
    refine LinearMap.mem_range.mpr ⟨c, ?_⟩
    rw [LinearMap.sub_apply, LinearEquiv.coe_toLinearMap, hrc, LinearMap.id_apply]
    have h1 : (-c - c : V) = (-2 : ZMod 3) • c := by module
    rw [h1, hdRo7A3ReflAux_neg_two_eq_one, one_smul]
  obtain ⟨ĥ, hĥU, hĥc⟩ := Submodule.mem_map.mp (hspan hcmove)
  let f : Fin 9 → ZMod 3 := fun i => φ (θ (Pi.single i 1))
  have hlevel : ∀ i j, i ≠ j → (f i = f j ↔ ĥ i = ĥ j) :=
    hdRo7A3ReflAux_levels hD hpm hm3 hrH hφc hrf hĥU hĥc
  have hiff : ∀ i j, f i = f j ↔ ĥ i = ĥ j := by
    intro i j
    by_cases hij : i = j
    · subst hij; simp
    · exact hlevel i j hij
  have hsumf : ∑ i, f i = 0 := by
    have h := hdRo7A3ReflAux_dual_eq_sum (θ := θ) φ (fun _ : Fin 9 => (1 : ZMod 3))
    rw [hM0, map_zero] at h
    simpa using h.symm
  have hsumfh : ∑ i, f i * ĥ i = 2 := by
    have h := hdRo7A3ReflAux_dual_eq_sum (θ := θ) φ ĥ
    rw [hĥc, hφc] at h
    exact h.symm
  have hcard9 : (Finset.univ.filter fun i => ĥ i = 0).card +
      (Finset.univ.filter fun i => ĥ i = 1).card +
      (Finset.univ.filter fun i => ĥ i = 2).card = 9 :=
    hdRo7A3ReflAux_card_fiber ĥ
  have hcongr := hdRo7A3ReflAux_congr hpm hĥU
  have hle : ∀ a : ZMod 3, (Finset.univ.filter fun i => ĥ i = a).card ≤ 9 := by
    intro a
    have h := Finset.card_le_card (Finset.filter_subset (fun i => ĥ i = a) Finset.univ)
    simpa using h
  by_cases hcase : ∃ a b : ZMod 3, a ≠ b ∧
      (Finset.univ.filter fun i => ĥ i = a).card =
        (Finset.univ.filter fun i => ĥ i = b).card
  ·
    obtain ⟨a, b, hab, hcab⟩ := hcase
    obtain ⟨τ, hτ⟩ := hdRo7A3ReflAux_neg_perm hab hcab
    obtain ⟨s, hsU, hsz⟩ := a3_exists_perm (p := 3) hD.hfr hpm (Equiv.symm τ)
    have hsH : s ∈ H := hD.hPH s ⟨Equiv.symm τ, hsU, hsz⟩
    have hsh : s c = -c := by
      rw [← hĥc, hsU ĥ hĥU]
      have hfun : (fun i => ĥ (Equiv.symm (Equiv.symm τ) i)) = fun i => -ĥ i + (a + b) := by
        funext i
        exact hτ i
      rw [hfun]
      have hsplit : (fun i => -ĥ i + (a + b)) =
          -ĥ + (a + b) • (fun _ : Fin 9 => (1 : ZMod 3)) := by
        funext i; simp
      rw [hsplit, map_add, map_smul, map_neg, hM0, smul_zero, add_zero, hĥc]
    let ψ' : Module.Dual (ZMod 3) V := φ ∘ₗ (s.symm : V →ₗ[ZMod 3] V)
    have hTF : CFSG.StandardType.QTwoLin.TransvectionFree A := fun g hg hgt =>
      hD.hNoT g hg (c2Transv_of_isTransvectionLin g hgt)
    have hr'mem : s * r * s⁻¹ ∈ H := H.mul_mem (H.mul_mem hsH hrH) (H.inv_mem hsH)
    have hr'form : ∀ v, (s * r * s⁻¹) v = v - ψ' v • (-c) := by
      intro v
      have h1 : (s * r * s⁻¹) v = s (r (s.symm v)) := by
        rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
        rfl
      rw [h1, hrf, map_sub, map_smul, LinearEquiv.apply_symm_apply, hsh]
      rfl
    have hφu1 : (-φ) (-c) = 2 := by
      simp [hφc]
    have hφu2 : ψ' (-c) = 2 := by
      have hsc : s.symm (-c) = c := by
        rw [LinearEquiv.symm_apply_eq]
        exact hsh.symm
      show φ (s.symm (-c)) = 2
      rw [hsc, hφc]
    have hrf_neg : ∀ v, r v = v - (-φ) v • (-c) := by
      intro v
      rw [hrf v]
      simp only [LinearMap.neg_apply, neg_smul, smul_neg, neg_neg]
    have hsame : (-φ) = ψ' :=
      CFSG.StandardType.QTwoLin.eq_form_of_same_root_of_transvectionFree (K := ZMod 3) hTF
        (hD.hHA hrH) (hD.hHA hr'mem) hφu1 hφu2 hrf_neg hr'form
    have hφz : φ z = 0 := by
      have h1 : (-φ) z = φ (s.symm z) := by
        have h2 := congrArg (fun g : Module.Dual (ZMod 3) V => g z) hsame
        simpa [ψ'] using h2
      have hsz' : s.symm z = z := by
        simpa using congrArg s.symm hsz.symm
      rw [hsz'] at h1
      rw [LinearMap.neg_apply] at h1
      have h2 : (2 : ZMod 3) * φ z = 0 := by
        linear_combination -h1
      exact (mul_eq_zero.mp h2).resolve_left hdRo7A3ReflAux_two_ne_zero
    rw [hrf z, hφz, zero_smul, sub_zero]
  ·
    exfalso
    have hne : ∀ a b : ZMod 3, a ≠ b →
        (Finset.univ.filter fun i => ĥ i = a).card ≠
          (Finset.univ.filter fun i => ĥ i = b).card := by
      intro a b hab h
      exact hcase ⟨a, b, hab, h⟩
    have hmod : ∀ a : ZMod 3, (Finset.univ.filter fun i => ĥ i = a).card % 3 =
        (Finset.univ.filter fun i => ĥ i = 0).card % 3 := by
      intro a
      have h := congrArg ZMod.val (hcongr a)
      simpa [ZMod.val_natCast] using h
    have hr0 : (Finset.univ.filter fun i => ĥ i = 0).card % 3 = 0 :=
      hdRo7A3ReflAux_dvd_of_distinct (hle 0) (hle 1) (hle 2) hcard9
        (hne 0 1 hdRo7A3ReflAux_zero_ne_one)
        (hne 0 2 hdRo7A3ReflAux_zero_ne_two)
        (hne 1 2 hdRo7A3ReflAux_one_ne_two)
        (hmod 0) (hmod 1) (hmod 2)
    have hdvd : ∀ a : ZMod 3, 3 ∣ (Finset.univ.filter fun i => ĥ i = a).card := by
      intro a
      exact Nat.dvd_of_mod_eq_zero (by rw [hmod a, hr0])
    have hzero : ∀ a : ZMod 3, ((Finset.univ.filter fun i => ĥ i = a).card : ZMod 3) = 0 := by
      intro a
      rw [ZMod.natCast_eq_zero_iff]
      exact hdvd a
    obtain ⟨g, hg⟩ := hdRo7A3ReflAux_exists_g hiff
    have hfib : ∑ i, f i * ĥ i = ∑ a : ZMod 3,
        ((Finset.univ.filter fun i => ĥ i = a).card : ZMod 3) * (g a * a) := by
      rw [show ∑ i, f i * ĥ i = ∑ i, (fun a => g a * a) (ĥ i) from
        Finset.sum_congr rfl fun i _ => by rw [hg i]]
      exact hdRo7A3ReflAux_fiber ĥ (fun a => g a * a)
    rw [hfib, hdRo7A3ReflAux_sum_zmod3 (fun a =>
      ((Finset.univ.filter fun i => ĥ i = a).card : ZMod 3) * (g a * a)),
      hzero 0, hzero 1, hzero 2] at hsumfh
    simp only [zero_mul, add_zero] at hsumfh
    exact hdRo7A3ReflAux_two_ne_zero hsumfh.symm

end CFSG.StandardType.HdRo7A3
