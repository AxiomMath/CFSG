module

public import CFSG.LocalAnalysis.StandardType.GGWAutDefs
public import CFSG.ClassicalGroups.Orthogonal.Derived
import CFSG.LocalAnalysis.StandardType.GGWAutMonoNorm
import CFSG.LocalAnalysis.StandardType.GGRCMonomialHom
import CFSG.LocalAnalysis.StandardType.GGLargeDepNoSymPerm

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin
open CFSG.ClassicalGroups.Orthogonal

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V]

private theorem cartanA5_diag (i : Fin 5) : (CartanMatrix.A 5 i i : ZMod 3) = 2 := by
  simp [CartanMatrix.A]

private theorem cartanA5_edge {i j : Fin 5} (hij : i ≠ j)
    (hadj : i.val + 1 = j.val ∨ j.val + 1 = i.val) :
    (CartanMatrix.A 5 i j : ZMod 3) = -1 := by
  have h : CartanMatrix.A 5 i j = -1 := by
    simp only [CartanMatrix.A, Matrix.of_apply]
    rw [if_neg hij, if_pos hadj]
  rw [h]
  norm_num

private theorem cartanA5_nonEdge : (CartanMatrix.A 5 2 0 : ZMod 3) = 0 := by
  have h : CartanMatrix.A 5 2 0 = 0 := by
    simp only [CartanMatrix.A, Matrix.of_apply]
    rw [if_neg (by decide), if_neg (by decide)]
  rw [h]
  norm_num

private theorem zmod3_not_isSquare_two_mul_sq (q : ZMod 3) (hq : q ≠ 0) :
    ¬ IsSquare (2 * q ^ 2) := by
  have hq2 : q ^ 2 = 1 := by
    revert q
    decide
  rintro ⟨r, hr⟩
  rw [hq2, mul_one] at hr
  have hr2 : r * r ≠ 2 := by
    revert r
    decide
  exact hr2 hr.symm

theorem ggQ2TN6_not_imprimitive [Module.Finite (ZMod 3) V]
    (hdim : Module.finrank (ZMod 3) V = 5) (c : Fin 5 → V) (α : Fin 5 → Module.Dual (ZMod 3) V)
    (hpair : ∀ i j, α i (c j) = (CartanMatrix.A 5 i j : ZMod 3))
    (s : Fin 5 → (V ≃ₗ[ZMod 3] V)) (hs : ∀ i v, s i v = v - α i v • c i)
    (R : Subgroup (V ≃ₗ[ZMod 3] V)) (hsR : ∀ i, s i ∈ R) (habs : ZS.AbsIrred 3 R)
    (hgen : R = Subgroup.closure {r | r ∈ R ∧ GGLinRefl r}) :
    ¬ CFSG.Quasithin.SimsG4.IsImprimitiveOnV R := by
  intro himp
  obtain ⟨f, hfmono⟩ := ggWAut_imprim_frame (n := 5) hdim R habs hgen himp
  let W : Subgroup (V ≃ₗ[ZMod 3] V) := Subgroup.closure (Set.range s)
  have hWR : W ≤ R := by
    show Subgroup.closure (Set.range s) ≤ R
    refine (Subgroup.closure_le R).mpr ?_
    rintro _ ⟨i, rfl⟩
    exact hsR i
  have hmon : ∀ a ∈ W, ∃ (σ : Equiv.Perm (Fin 5)) (ε : Fin 5 → ZMod 3),
      (∀ i, ε i ≠ 0) ∧ ∀ i, (a : V ≃ₗ[ZMod 3] V) (f i) = ε i • f (σ i) :=
    fun a ha => hfmono (a : V ≃ₗ[ZMod 3] V) (hWR ha)
  obtain ⟨π, -, -, -, hker⟩ := ggRC_monomial_hom (p := 3) f W hmon
  have hWcard : Nat.card W = 720 := by
    have h : Nat.card W = (5 + 1).factorial :=
      l04fD5_P_card (p := 3) (m := 5) (by decide) (by norm_num) hpair s hs
    rw [h]
    norm_num
  have hcard : Nat.card π.ker * Nat.card π.range = 720 := by
    rw [Subgroup.card_ker_mul_card_range π, hWcard]
  have hrdvd : Nat.card π.range ∣ 120 := by
    have hperm : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
      rw [Nat.card_perm, Nat.card_fin]
      norm_num
    rw [← hperm]
    exact Subgroup.card_subgroup_dvd_card π.range
  have h3 : Nat.Coprime 3 (Nat.card π.ker) :=
    (Nat.prime_three.coprime_iff_not_dvd).mpr hker
  have h9 : Nat.Coprime 9 (Nat.card π.ker) := by
    rw [show (9 : ℕ) = 3 ^ 2 from by norm_num]
    exact (Nat.coprime_pow_left_iff (by norm_num : 0 < 2) 3 _).mpr h3
  have h9range : 9 ∣ Nat.card π.range := by
    have hprod : 9 ∣ Nat.card π.ker * Nat.card π.range := by
      rw [hcard]
      norm_num
    have hprod' : 9 ∣ Nat.card π.range * Nat.card π.ker := by
      rwa [mul_comm]
    exact h9.dvd_of_dvd_mul_right hprod'
  have : 9 ∣ 120 := h9range.trans hrdvd
  norm_num at this

private theorem polar_eq_mul_of_isIsom (Q : QuadraticForm (ZMod 3) V) {u : V}
    {a : Module.Dual (ZMod 3) V} (hau : a u = 2) {g : V ≃ₗ[ZMod 3] V}
    (hg : ∀ v, g v = v - a v • u) (hgQ : ∀ v, Q (g v) = Q v) :
    ∀ v : V, QuadraticMap.polar Q v u = a v * Q u := by
  have htwo : (2 : ZMod 3) * 2 = 1 := by decide
  have hstep : ∀ v : V, a v * (a v * Q u - QuadraticMap.polar Q v u) = 0 := by
    intro v
    have hQv : Q (v - a v • u) = Q v := by
      rw [← hg v]
      exact hgQ v
    have hkey : Q (v - a v • u) =
        Q v + (a v * a v) * Q u - a v * QuadraticMap.polar Q v u := by
      rw [sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg Q,
        QuadraticMap.map_smul Q, QuadraticMap.polar_neg_right, QuadraticMap.polar_smul_right]
      simp only [smul_eq_mul]
      ring
    rw [hkey] at hQv
    linear_combination hQv
  intro v
  by_cases hv : a v = 0
  · have hva : a (v + (2 : ZMod 3) • u) = 1 := by
      rw [map_add, map_smul, hv, hau, smul_eq_mul, htwo, zero_add]
    have h1 : QuadraticMap.polar Q (v + (2 : ZMod 3) • u) u = Q u := by
      have h := hstep (v + (2 : ZMod 3) • u)
      rw [hva, one_mul, one_mul, sub_eq_zero] at h
      exact h.symm
    have hpu : QuadraticMap.polar Q u u = 2 * Q u := by
      rw [QuadraticMap.polar_self, nsmul_eq_mul]
      norm_num
    have hsum : QuadraticMap.polar Q (v + (2 : ZMod 3) • u) u =
        QuadraticMap.polar Q v u + Q u := by
      rw [QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, hpu, smul_eq_mul]
      rw [← mul_assoc, htwo, one_mul]
    rw [hsum] at h1
    have hzero : QuadraticMap.polar Q v u = 0 := by
      have h := congrArg (fun t : ZMod 3 => t - Q u) h1
      simpa using h
    simp [hzero, hv]
  · have hzero : a v * Q u - QuadraticMap.polar Q v u = 0 := by
      rcases mul_eq_zero.mp (hstep v) with h | h
      · exact absurd h hv
      · exact h
    rw [sub_eq_zero] at hzero
    exact hzero.symm

theorem ggQ2TN6_form (Q : QuadraticForm (ZMod 3) V)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (c : Fin 5 → V)
    (α : Fin 5 → Module.Dual (ZMod 3) V)
    (hpair : ∀ i j, α i (c j) = (CartanMatrix.A 5 i j : ZMod 3))
    (s : Fin 5 → (V ≃ₗ[ZMod 3] V)) (hs : ∀ i v, s i v = v - α i v • c i)
    (hsQ : ∀ i, ZS.IsIsom 3 Q (s i)) (x : V) (hxfix : ∀ i, α i x = 0) :
    Q (c 0) ≠ 0 ∧ Q (c 0 + c 2) ≠ 0 ∧ ¬ IsSquare (Q (c 0) * Q (c 0 + c 2)) ∧
      reflect Q (c 0) x = x ∧ reflect Q (c 0 + c 2) x = x := by
  have hαc : ∀ i, α i (c i) = 2 := by
    intro i
    rw [hpair i i, cartanA5_diag i]
  have hpolar : ∀ (i : Fin 5) (v : V),
      QuadraticMap.polar Q v (c i) = α i v * Q (c i) := by
    intro i
    exact polar_eq_mul_of_isIsom Q (hau := hαc i) (hg := hs i) (hgQ := fun v => hsQ i v)
  have hqne : ∀ i, Q (c i) ≠ 0 := by
    intro i hqi
    have hzero : ∀ v, (QuadraticMap.polarBilin Q) (c i) v = 0 := by
      intro v
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm Q (c i) v,
        hpolar i v, hqi, mul_zero]
    have hci : c i = 0 := hQ.1 (c i) hzero
    have hcontra : α i (c i) = 0 := by rw [hci, map_zero]
    rw [hαc i] at hcontra
    exact absurd hcontra (by decide : (2 : ZMod 3) ≠ 0)
  have hq_of_neg : ∀ i j : Fin 5, (CartanMatrix.A 5 i j : ZMod 3) = -1 →
      (CartanMatrix.A 5 j i : ZMod 3) = -1 → Q (c i) = Q (c j) := by
    intro i j hij hji
    have h1 : QuadraticMap.polar Q (c j) (c i) = -Q (c i) := by
      rw [hpolar i (c j), hpair i j, hij]
      ring
    have h2 : QuadraticMap.polar Q (c j) (c i) = -Q (c j) := by
      rw [QuadraticMap.polar_comm Q (c j) (c i), hpolar j (c i), hpair j i, hji]
      ring
    exact neg_injective (h1.symm.trans h2)
  have hq01 : Q (c 0) = Q (c 1) :=
    hq_of_neg 0 1 (cartanA5_edge (by decide) (by decide))
      (cartanA5_edge (by decide) (by decide))
  have hq12 : Q (c 1) = Q (c 2) :=
    hq_of_neg 1 2 (cartanA5_edge (by decide) (by decide))
      (cartanA5_edge (by decide) (by decide))
  have horth : QuadraticMap.polar Q (c 0) (c 2) = 0 := by
    rw [hpolar 2 (c 0), hpair 2 0, cartanA5_nonEdge, zero_mul]
  have h02 : Q (c 0 + c 2) = 2 * Q (c 0) := by
    rw [QuadraticMap.map_add Q, ← hq12, ← hq01, horth]
    ring
  have h02ne : Q (c 0 + c 2) ≠ 0 := by
    intro h0
    have : (2 : ZMod 3) * Q (c 0) = 0 := by
      rw [← h02]
      exact h0
    exact (mul_ne_zero (by decide : (2 : ZMod 3) ≠ 0) (hqne 0)) this
  have hprod : Q (c 0) * Q (c 0 + c 2) = 2 * Q (c 0) ^ 2 := by
    rw [h02]
    ring
  have hnsq : ¬ IsSquare (Q (c 0) * Q (c 0 + c 2)) := by
    rw [hprod]
    exact zmod3_not_isSquare_two_mul_sq (Q (c 0)) (hqne 0)
  have hx0 : QuadraticMap.polar Q (c 0) x = 0 := by
    rw [← QuadraticMap.polar_comm Q x (c 0), hpolar 0 x, hxfix 0, zero_mul]
  have hx02 : QuadraticMap.polar Q (c 0 + c 2) x = 0 := by
    rw [QuadraticMap.polar_add_left, hx0, ← QuadraticMap.polar_comm Q x (c 2),
      hpolar 2 x, hxfix 2, zero_mul, add_zero]
  exact ⟨hqne 0, h02ne, hnsq, reflect_apply_of_polar_eq_zero hx0,
    reflect_apply_of_polar_eq_zero hx02⟩

end CFSG.StandardType

end
