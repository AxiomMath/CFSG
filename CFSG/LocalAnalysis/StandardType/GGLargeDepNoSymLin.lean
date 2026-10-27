module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleDefs
public import TauCeti.LinearAlgebra.Matrix.Cartan.Classical
import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.StandardType

open CFSG

private lemma l04fLN_two_ne_zero {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h0
  have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h0
  have hp2 : p = 2 := by
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have hge : 2 ≤ p := (Fact.out : p.Prime).two_le
    omega
  exact hp hp2

private lemma l04fLN_move_eq_span {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V]
    (a : V ≃ₗ[ZMod p] V) {c : V} {β : Module.Dual (ZMod p) V} (hβc : β c = 2)
    (hform : ∀ v, a v = v - β v • c) : ggLinMove a = Submodule.span (ZMod p) {c} := by
  have hβ0 : β ≠ 0 := by
    intro hzero
    rw [hzero] at hβc
    exact (l04fLN_two_ne_zero hp2) hβc.symm
  have hL : a.toLinearMap - LinearMap.id = (-β).smulRight c := by
    ext v
    change a v - v = (-β) v • c
    rw [hform v]
    simp only [LinearMap.neg_apply, neg_smul]
    abel
  rw [ggLinMove, hL]
  apply le_antisymm
  · rintro v ⟨w, rfl⟩
    rw [Submodule.mem_span_singleton]
    exact ⟨(-β) w, by rw [LinearMap.smulRight_apply]⟩
  · rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_range]
    have hex : ∃ y, (-β) y ≠ 0 := by
      by_contra h
      apply hβ0
      ext y
      by_contra hy
      exact h ⟨y, neg_ne_zero.mpr hy⟩
    obtain ⟨y, hy⟩ := hex
    refine ⟨((-β) y)⁻¹ • y, ?_⟩
    have h1 : (-β) (((-β) y)⁻¹ • y) = 1 := by
      rw [map_smul, smul_eq_mul]
      exact inv_mul_cancel₀ hy
    rw [LinearMap.smulRight_apply, h1, one_smul]

private lemma l04fLN_map_move {p : ℕ} [Fact p.Prime] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V]
    (s q : V ≃ₗ[ZMod p] V) (h : s * q = q * s) :
    ∀ v ∈ ggLinMove q, s v ∈ ggLinMove q := by
  intro v hv
  rw [ggLinMove] at hv ⊢
  obtain ⟨w, rfl⟩ := LinearMap.mem_range.mp hv
  refine LinearMap.mem_range.mpr ⟨s w, ?_⟩
  rw [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.sub_apply, LinearMap.id_apply, map_sub]
  congr 1
  have hw : s (q w) = q (s w) := by
    have h' : (s * q) w = (q * s) w := by rw [h]
    simpa [LinearEquiv.mul_apply] using h'
  exact hw.symm

private lemma l04fLN_coeff_zero_of_succ {p m : ℕ} [Fact p.Prime] {W : Type}
    [AddCommGroup W] [Module (ZMod p) W] {u : Fin m → W}
    {a : Fin m → Module.Dual (ZMod p) W}
    (hpair : ∀ i j, a i (u j) = (CartanMatrix.A m i j : ZMod p))
    {c : Fin m → ZMod p} (hc : ∑ i, c i • u i = 0)
    {k k' : Fin m} (hk' : (k' : ℕ) = (k : ℕ) + 1)
    (hzero : ∀ j : Fin m, (k : ℕ) + 1 ≤ (j : ℕ) → c j = 0) :
    c k = 0 := by
  have hAadj : ∀ i j : Fin m, (i : ℕ) + 1 = (j : ℕ) →
      (CartanMatrix.A m i j : ZMod p) + 1 = 0 := by
    intro i j hij
    have hne : i ≠ j := by intro h; have := congrArg Fin.val h; omega
    have h : CartanMatrix.A m i j = -1 := by
      simp only [CartanMatrix.A, Matrix.of_apply]
      rw [if_neg hne, if_pos (Or.inl hij)]
    have hz : CartanMatrix.A m i j + 1 = 0 := by rw [h]; norm_num
    have := congrArg (fun z : ℤ => (z : ZMod p)) hz
    simpa using this
  have hAadj' : ∀ i j : Fin m, (j : ℕ) + 1 = (i : ℕ) →
      (CartanMatrix.A m i j : ZMod p) + 1 = 0 := by
    intro i j hij
    have hne : i ≠ j := by intro h; have := congrArg Fin.val h; omega
    have h : CartanMatrix.A m i j = -1 := by
      simp only [CartanMatrix.A, Matrix.of_apply]
      rw [if_neg hne, if_pos (Or.inr hij)]
    have hz : CartanMatrix.A m i j + 1 = 0 := by rw [h]; norm_num
    have := congrArg (fun z : ℤ => (z : ZMod p)) hz
    simpa using this
  have hAzero : ∀ i j : Fin m, i ≠ j →
      ¬ ((i : ℕ) + 1 = (j : ℕ)) → ¬ ((j : ℕ) + 1 = (i : ℕ)) →
      (CartanMatrix.A m i j : ZMod p) = 0 := by
    intro i j hij h1 h2
    have h : CartanMatrix.A m i j = 0 := by
      simp only [CartanMatrix.A, Matrix.of_apply]
      rw [if_neg hij, if_neg (not_or.mpr ⟨h1, h2⟩)]
    simp [h]
  have hsum : (∑ j : Fin m, c j * (CartanMatrix.A m k' j : ZMod p)) = 0 := by
    have h := congrArg (a k') hc
    simpa only [map_zero, map_sum, map_smul, hpair, smul_eq_mul] using h
  have hsingle : (∑ j : Fin m, c j * (CartanMatrix.A m k' j : ZMod p)) =
      c k * (CartanMatrix.A m k' k : ZMod p) := by
    refine Finset.sum_eq_single k ?_ ?_
    · intro j _ hjne
      by_cases hlt : (j : ℕ) < (k : ℕ)
      · have h1 : k' ≠ j := by intro h; have := congrArg Fin.val h; omega
        have h2 : ¬ ((k' : ℕ) + 1 = (j : ℕ)) := by omega
        have h3 : ¬ ((j : ℕ) + 1 = (k' : ℕ)) := by omega
        rw [hAzero k' j h1 h2 h3, mul_zero]
      · have hjge : (k : ℕ) + 1 ≤ (j : ℕ) := by omega
        rw [hzero j hjge, zero_mul]
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  have h1 : c k * (CartanMatrix.A m k' k : ZMod p) + c k = 0 := by
    have hA := hAadj' k' k (by omega)
    have := congrArg (fun z : ZMod p => c k * z) hA
    simpa [mul_add, mul_one] using this
  rw [hsingle] at hsum
  rw [hsum, zero_add] at h1
  exact h1

theorem ggLargeDep_noSym_aug_lin {p m : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {W : Type}
    [AddCommGroup W] [Module (ZMod p) W] {u : Fin m → W} {a : Fin m → Module.Dual (ZMod p) W}
    (hpair : ∀ i j, a i (u j) = (CartanMatrix.A m i j : ZMod p))
    {q : Fin m → (W ≃ₗ[ZMod p] W)} (hq : ∀ i w, q i w = w - a i w • u i)
    {s : W ≃ₗ[ZMod p] W} (hs : GGLinRefl s)
    (hcomm : ∀ i : Fin m, (i : ℕ) + 2 ≤ m → s * q i = q i * s)
    (hne : ∀ i : Fin m, (i : ℕ) + 2 ≤ m → s ≠ q i)
    (hord : ∀ j : Fin m, (j : ℕ) + 1 = m → orderOf (s * q j) = 3) :
    LinearIndependent (ZMod p) u := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  cases m with
  | zero =>
      intro i
      exact Fin.elim0 i
  | succ n =>
      have htwo : (2 : ZMod p) ≠ 0 := l04fLN_two_ne_zero hp2
      have hAii : ∀ i : Fin (n + 1), (CartanMatrix.A (n + 1) i i : ZMod p) = 2 := by
        intro i
        have h : CartanMatrix.A (n + 1) i i = 2 := by
          simp [CartanMatrix.A, Matrix.of_apply]
        rw [h]; norm_num
      have hu_ne : ∀ i : Fin (n + 1), u i ≠ 0 := by
        intro i hi
        have h : a i (u i) = 0 := by rw [hi, map_zero]
        rw [hpair i i, hAii i] at h
        exact htwo h
      have hqi : ∀ i : Fin (n + 1), q i (u i) = -u i := by
        intro i
        rw [hq i (u i), hpair i i, hAii i]
        module
      have hfix : ∀ i : Fin (n + 1), (i : ℕ) + 2 ≤ n + 1 → s (u i) = u i := by
        intro i hi
        have hMove_qi : ggLinMove (q i) = Submodule.span (ZMod p) {u i} :=
          l04fLN_move_eq_span hp2 (q i) (by rw [hpair i i, hAii i]) (fun v => hq i v)
        have hu_mem : u i ∈ ggLinMove (q i) := by
          rw [hMove_qi]
          exact Submodule.mem_span_singleton_self (u i)
        have hsu_mem : s (u i) ∈ ggLinMove (q i) :=
          l04fLN_map_move s (q i) (hcomm i hi) (u i) hu_mem
        obtain ⟨lam, hlam⟩ : ∃ lam : ZMod p, s (u i) = lam • u i := by
          rw [hMove_qi] at hsu_mem
          obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hsu_mem
          exact ⟨a, ha.symm⟩
        have hlam2 : lam ^ 2 = 1 := by
          have hss : s (s (u i)) = u i := by
            have h := congrArg (fun f : W ≃ₗ[ZMod p] W => f (u i)) hs.1
            simpa [LinearEquiv.mul_apply] using h
          have h1 : (lam * lam) • u i = u i := by
            calc (lam * lam) • u i = lam • (lam • u i) := by rw [mul_smul]
              _ = lam • s (u i) := by rw [← hlam]
              _ = s (lam • u i) := by rw [map_smul]
              _ = s (s (u i)) := by rw [← hlam]
              _ = u i := hss
          have hzero : (lam * lam - 1) • u i = 0 := by
            rw [sub_smul, h1, one_smul, sub_self]
          rcases smul_eq_zero.mp hzero with h | h
          · have : lam * lam = 1 := sub_eq_zero.mp h
            rwa [pow_two]
          · exact absurd h (hu_ne i)
        rcases sq_eq_one_iff.mp hlam2 with h1 | h1
        · rw [h1, one_smul] at hlam
          exact hlam
        · exfalso
          have hsui : s (u i) = -u i := by rw [hlam, h1, neg_one_smul]
          have hmem_s : s (u i) - u i ∈ ggLinMove s := by
            rw [ggLinMove, LinearMap.mem_range]
            exact ⟨u i, by rw [LinearMap.sub_apply, LinearMap.id_apply]; rfl⟩
          have hmem_u : u i ∈ ggLinMove s := by
            have h2 : s (u i) - u i = -(2 : ZMod p) • u i := by
              rw [hsui]; module
            have hne2 : (-(2 : ZMod p)) ≠ 0 := neg_ne_zero.mpr htwo
            have hEq : u i = (-(2 : ZMod p))⁻¹ • (s (u i) - u i) := by
              rw [h2, smul_smul, inv_mul_cancel₀ hne2, one_smul]
            rw [hEq]
            exact (ggLinMove s).smul_mem _ hmem_s
          have hMove_s : ggLinMove s = Submodule.span (ZMod p) {u i} := by
            have : FiniteDimensional (ZMod p) ↥(ggLinMove s) :=
              FiniteDimensional.of_finrank_pos (by rw [hs.2]; norm_num)
            exact (Submodule.eq_of_le_of_finrank_eq
              ((Submodule.span_singleton_le_iff_mem (u i) (ggLinMove s)).mpr hmem_u)
              (by rw [finrank_span_singleton (hu_ne i), hs.2])).symm
          have hsw : ∀ w, s w = q i w := by
            intro w
            have hmemw : s w - w ∈ ggLinMove s := by
              rw [ggLinMove, LinearMap.mem_range]
              exact ⟨w, by rw [LinearMap.sub_apply, LinearMap.id_apply]; rfl⟩
            rw [hMove_s, Submodule.mem_span_singleton] at hmemw
            obtain ⟨cc, hcc⟩ := hmemw
            have hsw_eq : s w = w + cc • u i := by
              have h := congrArg (fun z => z + w) hcc.symm
              simpa [add_comm] using h
            have hcomm_w : s (q i w) = q i (s w) := by
              have h := congrArg (fun f : W ≃ₗ[ZMod p] W => f w) (hcomm i hi)
              simpa [LinearEquiv.mul_apply] using h
            have hL : s (q i w) = w + (cc + a i w) • u i := by
              rw [hq i w, map_sub, map_smul, hsui, hsw_eq]
              module
            have hR : q i (s w) = w + (-(a i w) - cc) • u i := by
              rw [hq i (s w), hsw_eq, map_add, map_smul, hpair i i, hAii i, smul_eq_mul]
              module
            have hcoef : (cc + a i w) • u i = (-(a i w) - cc) • u i := by
              exact add_left_cancel ((hL.symm.trans hcomm_w).trans hR)
            have hsum2 : (2 : ZMod p) * (cc + a i w) = 0 := by
              have h0 : ((cc + a i w) - (-(a i w) - cc)) • u i = 0 := by
                rw [sub_smul, hcoef, sub_self]
              have hcoef2 : (cc + a i w) - (-(a i w) - cc) =
                  (2 : ZMod p) * (cc + a i w) := by ring
              rw [hcoef2] at h0
              rcases smul_eq_zero.mp h0 with h | h
              · exact h
              · exact absurd h (hu_ne i)
            have hzz : cc + a i w = 0 := by
              rcases mul_eq_zero.mp hsum2 with h | h
              · exact absurd h htwo
              · exact h
            have hcc' : cc = -a i w := (eq_neg_iff_add_eq_zero).mpr hzz
            rw [hsw_eq, hq i w, hcc']
            module
          exact hne i hi (LinearEquiv.ext hsw)
      have hlast_ne : s (u (Fin.last n)) ≠ u (Fin.last n) := by
        intro hsfix
        have hordlast : orderOf (s * q (Fin.last n)) = 3 :=
          hord (Fin.last n) (by simp [Fin.last])
        set g : W ≃ₗ[ZMod p] W := s * q (Fin.last n) with hgdef
        have hguj : g (u (Fin.last n)) = -u (Fin.last n) := by
          rw [hgdef, LinearEquiv.mul_apply, hqi (Fin.last n), map_neg, hsfix]
        have hg2 : (g ^ 2) (u (Fin.last n)) = u (Fin.last n) := by
          rw [show (2 : ℕ) = 1 + 1 by norm_num, pow_add, pow_one, LinearEquiv.mul_apply,
            hguj, map_neg, hguj, neg_neg]
        have hg3 : (g ^ 3) (u (Fin.last n)) = -u (Fin.last n) := by
          rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_add, pow_one, LinearEquiv.mul_apply,
            hguj, map_neg, hg2]
        have hg3one : g ^ 3 = 1 := by
          have h := pow_orderOf_eq_one g
          rwa [hordlast] at h
        have hconj : -u (Fin.last n) = u (Fin.last n) := by
          have h := congrArg (fun T : W ≃ₗ[ZMod p] W => T (u (Fin.last n))) hg3one
          rw [hg3] at h
          simpa using h
        have h2u : (2 : ZMod p) • u (Fin.last n) = 0 := by
          rw [two_smul]
          exact (neg_eq_iff_add_eq_zero).mp hconj
        rcases smul_eq_zero.mp h2u with h2 | h0
        · exact htwo h2
        · exact hu_ne (Fin.last n) h0
      have hclast : c (Fin.last n) = 0 := by
        have hDsum : (s.toLinearMap - LinearMap.id : W →ₗ[ZMod p] W)
            (∑ i : Fin (n + 1), c i • u i) =
            (s.toLinearMap - LinearMap.id : W →ₗ[ZMod p] W)
              (c (Fin.last n) • u (Fin.last n)) := by
          rw [map_sum]
          refine Finset.sum_eq_single (M := W) (s := Finset.univ) (Fin.last n) ?_ ?_
          · intro i _ hi
            have hival : (i : ℕ) + 2 ≤ n + 1 := by
              have hilt := i.isLt
              have hne : (i : ℕ) ≠ n := by intro h; exact hi (Fin.ext h)
              omega
            rw [LinearMap.sub_apply, LinearMap.id_apply, map_smul]
            change c i • s (u i) - c i • u i = 0
            rw [hfix i hival]
            simp
          · intro h
            exact absurd (Finset.mem_univ (Fin.last n)) h
        have hDlast : (s.toLinearMap - LinearMap.id : W →ₗ[ZMod p] W)
              (c (Fin.last n) • u (Fin.last n)) =
            c (Fin.last n) • (s (u (Fin.last n)) - u (Fin.last n)) := by
          rw [LinearMap.sub_apply, LinearMap.id_apply, map_smul, smul_sub]
          rfl
        have hDzero : (s.toLinearMap - LinearMap.id : W →ₗ[ZMod p] W)
            (∑ i : Fin (n + 1), c i • u i) = 0 := by
          rw [hc, map_zero]
        have hmain : c (Fin.last n) • (s (u (Fin.last n)) - u (Fin.last n)) = 0 := by
          rw [← hDlast, ← hDsum]
          exact hDzero
        have hdiff : s (u (Fin.last n)) - u (Fin.last n) ≠ 0 := by
          intro h
          exact hlast_ne (sub_eq_zero.mp h)
        rcases smul_eq_zero.mp hmain with h0 | h0
        · exact h0
        · exact absurd h0 hdiff
      have hlast_motive : (∀ j : Fin (n + 1), (Fin.last n).val ≤ (j : ℕ) → c j = 0) := by
        intro j hj
        simp only [Fin.val_last] at hj
        have hjval : (j : ℕ) = n := by have := j.isLt; omega
        have hjeq : j = Fin.last n := Fin.ext (by simpa [Fin.last] using hjval)
        rw [hjeq]; exact hclast
      have hcast : ∀ i : Fin n,
          (∀ j : Fin (n + 1), (i.succ : Fin (n + 1)).val ≤ (j : ℕ) → c j = 0) →
          (∀ j : Fin (n + 1), (i.castSucc : Fin (n + 1)).val ≤ (j : ℕ) → c j = 0) := by
        intro i ih j hj
        by_cases hjval : (j : ℕ) = (i : ℕ)
        · have hjeq : j = i.castSucc := Fin.ext (by simpa [Fin.castSucc] using hjval)
          rw [hjeq]
          refine l04fLN_coeff_zero_of_succ (k := i.castSucc) (k' := i.succ) hpair hc ?_ ?_
          · simp [Fin.succ, Fin.castSucc]
          · intro j' hj'
            exact ih j' (by simpa [Fin.succ, Fin.castSucc] using hj')
        · have hj' : (i.succ : Fin (n + 1)).val ≤ (j : ℕ) := by
            simp only [Fin.val_succ, Fin.val_castSucc] at hj ⊢
            omega
          exact ih j hj'
      have hP : ∀ i : Fin (n + 1), ∀ j : Fin (n + 1), (i : ℕ) ≤ (j : ℕ) → c j = 0 :=
        Fin.reverseInduction
          (motive := fun i : Fin (n + 1) => ∀ j : Fin (n + 1), (i : ℕ) ≤ (j : ℕ) → c j = 0)
          hlast_motive hcast
      intro i
      exact hP i i le_rfl

end CFSG.StandardType

end
