module

public import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Lattice

public section

namespace CFSG.Quasithin.H13

open scoped commutatorElement

structure Ob5PtSetup {G : Type} [Group G] (I P V Vh U A B : Subgroup G) (h : G) : Prop where
  hhI : h ∈ I
  hVI : ∀ v ∈ V, v ∈ I
  hPn : ∀ i ∈ I, ∀ p ∈ P, i * p * i⁻¹ ∈ P
  hVcomm : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v
  hV2 : ∀ v ∈ V, v * v = 1
  hVh : ∀ v ∈ V, h * v * h⁻¹ ∈ Vh
  hVh' : ∀ w ∈ Vh, ∃ v ∈ V, w = h * v * h⁻¹
  hV2h : ∀ w ∈ Vh, w * w = 1
  hU : ∀ x, x ∈ U ↔ x ∈ V ∧ x ∈ Vh
  hUB : ∀ u ∈ U, u ∈ B
  hUc : ∀ u ∈ U, ∀ i ∈ I, i * u * i⁻¹ = u
  hBdef : ∀ x, x ∈ B ↔ x ∈ V ∧ x ∈ P
  hAdef : ∀ x, x ∈ A ↔ x ∈ Vh ∧ x ∈ P
  hPeq : P = A ⊔ B
  hP2 : ∀ p ∈ P, ∀ q ∈ P, ⁅p, q⁆ ∈ U
  hVA : ∀ v ∈ V, ∀ a ∈ A, v * a * v⁻¹ * a⁻¹ ∈ B
  hhB : ∀ b ∈ B, h * b * h⁻¹ ∈ A
  hhA : ∀ a ∈ A, h⁻¹ * a * h ∈ B
  hB5 : ∀ p ∈ P, (∀ v ∈ V, v * p * v⁻¹ * p⁻¹ ∈ U) → p ∈ B
  hA5 : ∀ p ∈ P, (∀ w ∈ Vh, w * p * w⁻¹ * p⁻¹ ∈ U) → p ∈ A

namespace Ob5PtSetup

variable {G : Type} [Group G] {I P V Vh U A B : Subgroup G} {h : G}

theorem B_conj_P (S : Ob5PtSetup I P V Vh U A B h) (p : G) (hp : p ∈ P) (b : G) (hb : b ∈ B) :
    p * b * p⁻¹ ∈ B := by
  have hbP : b ∈ P := ((S.hBdef b).mp hb).2
  have hc : ⁅p, b⁆ ∈ U := S.hP2 p hp b hbP
  have hc' : ⁅p, b⁆ ∈ B := S.hUB _ hc
  have e : p * b * p⁻¹ = ⁅p, b⁆ * b := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact B.mul_mem hc' hb

theorem comm_V_P_mem (S : Ob5PtSetup I P V Vh U A B h) (v : G) (hv : v ∈ V) (p : G) (hp : p ∈ P) :
    v * p * v⁻¹ * p⁻¹ ∈ B := by
  have key : ∀ x ∈ A ⊔ B, x ∈ P ∧ v * x * v⁻¹ * x⁻¹ ∈ B := by
    intro x hx
    rw [Subgroup.sup_eq_closure] at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hxA | hxB
      · refine ⟨by rw [S.hPeq]; exact Subgroup.mem_sup_left hxA, ?_⟩
        exact S.hVA v hv x hxA
      · refine ⟨by rw [S.hPeq]; exact Subgroup.mem_sup_right hxB, ?_⟩
        have hxV : x ∈ V := ((S.hBdef x).mp hxB).1
        have : v * x = x * v := S.hVcomm v hv x hxV
        have e : v * x * v⁻¹ * x⁻¹ = 1 := by
          calc v * x * v⁻¹ * x⁻¹ = x * v * v⁻¹ * x⁻¹ := by rw [this]
            _ = 1 := by group
        rw [e]
        exact B.one_mem
    | one => exact ⟨P.one_mem, by simp⟩
    | mul x y _ _ hx hy =>
      refine ⟨P.mul_mem hx.1 hy.1, ?_⟩
      have e : v * (x * y) * v⁻¹ * (x * y)⁻¹ =
          (v * x * v⁻¹ * x⁻¹) * (x * (v * y * v⁻¹ * y⁻¹) * x⁻¹) := by group
      rw [e]
      exact B.mul_mem hx.2 (by
        have := S.B_conj_P x hx.1 _ hy.2
        exact this)
    | inv x _ hx =>
      refine ⟨P.inv_mem hx.1, ?_⟩
      have e : v * x⁻¹ * v⁻¹ * (x⁻¹)⁻¹ = x⁻¹ * (v * x * v⁻¹ * x⁻¹)⁻¹ * x := by group
      rw [e]
      have := S.B_conj_P x⁻¹ (P.inv_mem hx.1) _ (B.inv_mem hx.2)
      rwa [inv_inv] at this
  rw [← S.hPeq] at key
  exact (key p hp).2

theorem comm_Vh_P_mem (S : Ob5PtSetup I P V Vh U A B h) (w : G) (hw : w ∈ Vh) (p : G) (hp : p ∈ P) :
    w * p * w⁻¹ * p⁻¹ ∈ A := by
  obtain ⟨v, hv, rfl⟩ := S.hVh' w hw
  have hhinv : h⁻¹ ∈ I := I.inv_mem S.hhI
  have hp0 : h⁻¹ * p * h ∈ P := by
    have := S.hPn h⁻¹ hhinv p hp
    simpa [mul_assoc] using this
  have hc := S.comm_V_P_mem v hv _ hp0
  have e : h * v * h⁻¹ * p * (h * v * h⁻¹)⁻¹ * p⁻¹ =
      h * (v * (h⁻¹ * p * h) * v⁻¹ * (h⁻¹ * p * h)⁻¹) * h⁻¹ := by group
  rw [e]
  exact S.hhB _ hc

theorem lemma15 (S : Ob5PtSetup I P V Vh U A B h) (y : G) (hy : y ∈ I) (v : G) (hv : v ∈ V)
    (j : ℕ) (q : G) (hq : q ∈ P) (hg : v * (h * v * h⁻¹) = y ^ j * q)
    (hcover : ∀ w ∈ V, w ∈ B ∨ ∃ b ∈ B, w = v * b)
    (hcoverh : ∀ w ∈ Vh, w ∈ A ∨ ∃ a ∈ A, w = (h * v * h⁻¹) * a)
    (p : G) (hp : p ∈ P) (hyp : y * p * y⁻¹ * p⁻¹ ∈ U) : p ∈ U := by
  have hUcen : ∀ u ∈ U, ∀ i ∈ I, i * u * i⁻¹ = u := S.hUc
  have hpow : ∀ n : ℕ, (y ^ n) * p * (y ^ n)⁻¹ * p⁻¹ ∈ U := by
    intro n
    induction n with
    | zero => simp [U.one_mem]
    | succ n ih =>
      set u := (y ^ n) * p * (y ^ n)⁻¹ * p⁻¹ with hu
      have hyn : y ^ n ∈ I := I.pow_mem hy n
      have e : y ^ (n + 1) * p * (y ^ (n + 1))⁻¹ * p⁻¹ =
          (y ^ n * (y * p * y⁻¹ * p⁻¹) * (y ^ n)⁻¹) * u := by
        rw [hu]
        group
      rw [e]
      have hc : y ^ n * (y * p * y⁻¹ * p⁻¹) * (y ^ n)⁻¹ ∈ U := by
        rw [hUcen _ hyp _ hyn]
        exact hyp
      exact U.mul_mem hc ih
  have hUV : ∀ u ∈ U, ∀ x ∈ V, x * u * x⁻¹ = u := by
    intro u hu x hx
    have hu' := ((S.hU u).mp hu).1
    have := S.hVcomm x hx u hu'
    rw [this]
    group
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right (S.hV2 v hv)
  set w0 := h * v * h⁻¹ with hw0def
  have hw0Vh : w0 ∈ Vh := S.hVh v hv
  have hw0I : w0 ∈ I := I.mul_mem (I.mul_mem S.hhI (S.hVI v hv)) (I.inv_mem S.hhI)
  have hw0 : w0 = v * (y ^ j * q) := by
    rw [← hg, ← mul_assoc, S.hV2 v hv, one_mul]
  have hyj : y ^ j ∈ I := I.pow_mem hy j
  set c0 := v * p * v⁻¹ * p⁻¹ with hc0def
  set a0 := ⁅q, p⁆ * (y ^ j * p * (y ^ j)⁻¹ * p⁻¹) with ha0def
  have ha0U : a0 ∈ U := U.mul_mem (S.hP2 q hq p hp) (hpow j)
  have hA1 : y ^ j * (q * p * q⁻¹) * (y ^ j)⁻¹ = a0 * p := by
    have hqc : q * p * q⁻¹ = ⁅q, p⁆ * p := by
      simp only [commutatorElement_def]
      group
    have hcc := hUcen _ (S.hP2 q hq p hp) (y ^ j) hyj
    rw [hqc, ha0def]
    calc y ^ j * (⁅q, p⁆ * p) * (y ^ j)⁻¹
        = (y ^ j * ⁅q, p⁆ * (y ^ j)⁻¹) * (y ^ j * p * (y ^ j)⁻¹) := by group
      _ = ⁅q, p⁆ * (y ^ j * p * (y ^ j)⁻¹ * p⁻¹ * p) := by rw [hcc]; group
      _ = ⁅q, p⁆ * (y ^ j * p * (y ^ j)⁻¹ * p⁻¹) * p := by group
  have hw0conj : w0 * p * w0⁻¹ = a0 * (v * p * v⁻¹) := by
    rw [hw0]
    calc v * (y ^ j * q) * p * (v * (y ^ j * q))⁻¹
        = v * (y ^ j * (q * p * q⁻¹) * (y ^ j)⁻¹) * v⁻¹ := by group
      _ = v * (a0 * p) * v⁻¹ := by rw [hA1]
      _ = (v * a0 * v⁻¹) * (v * p * v⁻¹) := by group
      _ = a0 * (v * p * v⁻¹) := by rw [hUV a0 ha0U v hv]
  have hc0B : c0 ∈ B := S.comm_V_P_mem v hv p hp
  have hc0'A : w0 * p * w0⁻¹ * p⁻¹ ∈ A := S.comm_Vh_P_mem w0 hw0Vh p hp
  have hc0'eq : w0 * p * w0⁻¹ * p⁻¹ = a0 * c0 := by
    rw [hw0conj, hc0def]
    group
  have hc0U : c0 ∈ U := by
    have hsB : a0 * c0 ∈ B := B.mul_mem (S.hUB _ ha0U) hc0B
    have hsA : a0 * c0 ∈ A := hc0'eq ▸ hc0'A
    have hsU : a0 * c0 ∈ U := (S.hU _).mpr ⟨((S.hBdef _).mp hsB).1, ((S.hAdef _).mp hsA).1⟩
    have e : c0 = a0⁻¹ * (a0 * c0) := by group
    rw [e]
    exact U.mul_mem (U.inv_mem ha0U) hsU
  have hw0p : w0 * p * w0⁻¹ * p⁻¹ ∈ U := by
    rw [hc0'eq]
    exact U.mul_mem ha0U hc0U
  have hwV : ∀ w ∈ V, w * p * w⁻¹ * p⁻¹ ∈ U := by
    intro w hw
    rcases hcover w hw with hwB | ⟨b, hb, rfl⟩
    · exact S.hP2 w ((S.hBdef w).mp hwB).2 p hp
    · have hbP : b ∈ P := ((S.hBdef b).mp hb).2
      have hbp := S.hP2 b hbP p hp
      have e : v * b * p * (v * b)⁻¹ * p⁻¹ = (v * ⁅b, p⁆ * v⁻¹) * c0 := by
        simp only [commutatorElement_def, hc0def]
        group
      rw [e]
      refine U.mul_mem ?_ hc0U
      rw [hUV _ hbp v hv]
      exact hbp
  have hpB : p ∈ B := S.hB5 p hp hwV
  have hwVh : ∀ w ∈ Vh, w * p * w⁻¹ * p⁻¹ ∈ U := by
    intro w hw
    rcases hcoverh w hw with hwA | ⟨a, ha, rfl⟩
    · exact S.hP2 w ((S.hAdef w).mp hwA).2 p hp
    · have hap := S.hP2 a ((S.hAdef a).mp ha).2 p hp
      have e : w0 * a * p * (w0 * a)⁻¹ * p⁻¹ = (w0 * ⁅a, p⁆ * w0⁻¹) * (w0 * p * w0⁻¹ * p⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      refine U.mul_mem ?_ hw0p
      rw [hUcen _ hap w0 hw0I]
      exact hap
  have hpA : p ∈ A := S.hA5 p hp hwVh
  exact (S.hU p).mpr ⟨((S.hBdef p).mp hpB).1, ((S.hAdef p).mp hpA).1⟩

end Ob5PtSetup

end CFSG.Quasithin.H13
