module

public import CFSG.Quasithin.Vol2.Ch12Sec8NonabG112Def

public section

namespace CFSG.Quasithin.H13.C1294

open CFSG.Quasithin

section Basic

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

theorem zmod2_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide

theorem zmod2_mul_self (c : ZMod 2) : c * c = c := by
  rcases zmod2_cases c with rfl | rfl <;> decide

theorem zmod2_add_self (c : ZMod 2) : c + c = 0 := by
  rcases zmod2_cases c with rfl | rfl <;> decide

theorem add_self_eq_zero' (v : W) : v + v = 0 := by
  have h2 : (2 : ZMod 2) = 0 := rfl
  rw [← two_smul (ZMod 2) v, h2, zero_smul]

theorem q_zero (q : W → ZMod 2) (B : LinearMap.BilinForm (ZMod 2) W)
    (hq : ∀ v w, q (v + w) = q v + q w + B v w) : q 0 = 0 := by
  have h := hq 0 0
  rw [add_zero, map_zero] at h
  linear_combination -h

theorem B_self (q : W → ZMod 2) (B : LinearMap.BilinForm (ZMod 2) W)
    (hq : ∀ v w, q (v + w) = q v + q w + B v w) (v : W) : B v v = 0 := by
  have h := hq v v
  rw [add_self_eq_zero', q_zero q B hq] at h
  have h2 : q v + q v = 0 := zmod2_add_self _
  linear_combination -h - h2

theorem B_symm (q : W → ZMod 2) (B : LinearMap.BilinForm (ZMod 2) W)
    (hq : ∀ v w, q (v + w) = q v + q w + B v w) (v w : W) : B v w = B w v := by
  have h1 := hq v w
  have h2 := hq w v
  rw [add_comm w v] at h2
  linear_combination h2 - h1

theorem q_smul (q : W → ZMod 2) (B : LinearMap.BilinForm (ZMod 2) W)
    (hq : ∀ v w, q (v + w) = q v + q w + B v w) (c : ZMod 2) (v : W) :
    q (c • v) = c * c * q v := by
  rcases zmod2_cases c with rfl | rfl
  · simp [q_zero q B hq]
  · simp

theorem exists_B_eq_one (B : LinearMap.BilinForm (ZMod 2) W)
    (hB : ∀ v : W, (∀ w, B v w = 0) → v = 0) (q : W → ZMod 2)
    (hq : ∀ v w, q (v + w) = q v + q w + B v w) {u : W} (hu : u ≠ 0) :
    ∃ x : W, B x u = 1 := by
  by_contra h
  push Not at h
  apply hu
  apply hB u
  intro w
  rw [B_symm q B hq]
  rcases zmod2_cases (B w u) with h0 | h1
  · exact h0
  · exact absurd h1 (h w)

@[expose] def trLin (B : LinearMap.BilinForm (ZMod 2) W) (u : W) : W →ₗ[ZMod 2] W :=
  LinearMap.id + LinearMap.smulRight (LinearMap.flip B u) u

theorem trLin_apply (B : LinearMap.BilinForm (ZMod 2) W) (u x : W) :
    trLin B u x = x + B x u • u := by
  simp [trLin]

theorem trLin_trLin (q : W → ZMod 2) (B : LinearMap.BilinForm (ZMod 2) W)
    (hq : ∀ v w, q (v + w) = q v + q w + B v w) (u : W) (x : W) :
    trLin B u (trLin B u x) = x := by
  have hB' : B (x + B x u • u) u = B x u := by
    simp only [map_add, LinearMap.add_apply, LinearMap.map_smul, LinearMap.smul_apply,
      smul_eq_mul, B_self q B hq u, smul_zero, mul_zero, add_zero]
  rw [trLin_apply B u x, trLin_apply B u (x + B x u • u), hB', add_assoc, ← add_smul,
    zmod2_add_self, zero_smul, add_zero]

@[expose] def trEquiv (q : W → ZMod 2) (B : LinearMap.BilinForm (ZMod 2) W)
    (hq : ∀ v w, q (v + w) = q v + q w + B v w) (u : W) : W ≃ₗ[ZMod 2] W :=
  LinearEquiv.ofInvolutive (trLin B u) (fun x => trLin_trLin q B hq u x)

theorem trEquiv_apply (q : W → ZMod 2) (B : LinearMap.BilinForm (ZMod 2) W)
    (hq : ∀ v w, q (v + w) = q v + q w + B v w) (u x : W) :
    trEquiv q B hq u x = x + B x u • u :=
  trLin_apply B u x

theorem trLin_q (q : W → ZMod 2) (B : LinearMap.BilinForm (ZMod 2) W)
    (hq : ∀ v w, q (v + w) = q v + q w + B v w) {u : W} (hu : q u = 1) (x : W) :
    q (trLin B u x) = q x := by
  rw [trLin_apply, hq, q_smul q B hq, hu, map_smul, smul_eq_mul]
  have h2 : B x u * B x u + B x u * B x u = 0 := by
    rw [zmod2_mul_self, zmod2_add_self]
  linear_combination h2

theorem trEquiv_mem (q : W → ZMod 2) (B : LinearMap.BilinForm (ZMod 2) W)
    (hq : ∀ v w, q (v + w) = q v + q w + B v w) {u : W} (hu : q u = 1) :
    trEquiv q B hq u ∈ orthogonalSubgroupOf q := fun x => by
  rw [trEquiv_apply]
  exact trLin_q q B hq hu x

theorem exists_nonsing_perp [FiniteDimensional (ZMod 2) W]
    (B : LinearMap.BilinForm (ZMod 2) W) (hB : ∀ v : W, (∀ w, B v w = 0) → v = 0)
    (q : W → ZMod 2) (hq : ∀ v w, q (v + w) = q v + q w + B v w)
    (hdim : Module.finrank (ZMod 2) W = 6) {x : W} (hx : x ≠ 0) (hqx : q x = 0) :
    ∃ y : W, B x y = 0 ∧ q y = 1 := by
  by_contra hcon
  push Not at hcon
  have hsing : ∀ y : W, B x y = 0 → q y = 0 := fun y hy => by
    rcases zmod2_cases (q y) with h | h
    · exact h
    · exact absurd h (hcon y hy)
  have hAAb : ∀ y ∈ LinearMap.ker (B x), ∀ y' ∈ LinearMap.ker (B x), B y y' = 0 := by
    intro y hy y' hy'
    have hy1 := hsing y (LinearMap.mem_ker.1 hy)
    have hy2 := hsing y' (LinearMap.mem_ker.1 hy')
    have hy3 := hsing (y + y') (LinearMap.mem_ker.2 (by
      rw [map_add, LinearMap.mem_ker.1 hy, LinearMap.mem_ker.1 hy', add_zero]))
    have h := hq y y'
    rw [hy1, hy2, hy3] at h
    linear_combination -h
  obtain ⟨a, ha⟩ := exists_B_eq_one B hB q hq hx
  have hxa : B x a = 1 := by rw [B_symm q B hq]; exact ha
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hxa
  have hcompl : IsCompl (LinearMap.ker (B x)) (Submodule.span (ZMod 2) {a}) := by
    constructor
    · rw [Submodule.disjoint_def]
      intro w hw hwa
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hwa
      have hc : c = 0 := by
        have h1 := LinearMap.mem_ker.1 hw
        rw [map_smul, smul_eq_mul, hxa, mul_one] at h1
        exact h1
      rw [hc, zero_smul]
    · rw [codisjoint_iff, eq_top_iff]
      intro w _
      have hw : w + B x w • a ∈ LinearMap.ker (B x) := by
        rw [LinearMap.mem_ker, map_add, map_smul, hxa, smul_eq_mul, mul_one]
        exact zmod2_add_self _
      have hmem := Submodule.add_mem_sup hw (Submodule.smul_mem _ (B x w)
        (Submodule.mem_span_singleton_self a))
      have hwe : w + B x w • a + B x w • a = w := by
        rw [add_assoc, ← add_smul, zmod2_add_self, zero_smul, add_zero]
      rw [hwe] at hmem
      exact hmem
  have hAdim : 5 ≤ Module.finrank (ZMod 2) (LinearMap.ker (B x)) := by
    have h := Submodule.finrank_add_eq_of_isCompl hcompl
    rw [finrank_span_singleton ha0, hdim] at h
    omega
  have hnotle : ¬ LinearMap.ker (B x) ≤ Submodule.span (ZMod 2) {x} := by
    intro hle
    have h1 := Submodule.finrank_mono hle
    rw [finrank_span_singleton hx] at h1
    omega
  obtain ⟨y, hyA, hyS⟩ : ∃ y ∈ LinearMap.ker (B x), y ∉ Submodule.span (ZMod 2) {x} := by
    by_contra hc
    push Not at hc
    exact hnotle hc
  have hpoint : ∀ w : W, B y w = B x w * B y a := by
    intro w
    have hw : w + B x w • a ∈ LinearMap.ker (B x) := by
      rw [LinearMap.mem_ker, map_add, map_smul, hxa, smul_eq_mul, mul_one]
      exact zmod2_add_self _
    have h1 := hAAb y hyA _ hw
    have hwe : w + B x w • a + B x w • a = w := by
      rw [add_assoc, ← add_smul, zmod2_add_self, zero_smul, add_zero]
    have hsplit : B y w = B y (w + B x w • a) + B y (B x w • a) := by
      rw [← map_add, hwe]
    have hsm : B y (B x w • a) = B x w * B y a := by
      rw [map_smul, smul_eq_mul]
    rw [hsplit, hsm, h1, zero_add]
  apply hyS
  have hd : y + B y a • x = 0 := by
    refine hB _ (fun w => ?_)
    rw [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hpoint w]
    rw [mul_comm (B y a) (B x w)]
    exact zmod2_add_self _
  have hyc : y = B y a • x := by
    calc y = (y + B y a • x) + B y a • x := by rw [add_assoc, add_self_eq_zero', add_zero]
      _ = B y a • x := by rw [hd, zero_add]
  rw [hyc]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)

end Basic

end CFSG.Quasithin.H13.C1294
