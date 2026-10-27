module

public import CFSG.Quasithin.Background.RonanF95Lin1
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Quasithin.RonanF95

open Module

namespace TwoInv

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Finite E] (S : TwoInv E)

theorem add_self_E (y : E) : y + y = 0 := by
  calc y + y = (2 : ZMod 2) • y := (two_smul (ZMod 2) y).symm
    _ = 0 := by rw [show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem add_self_End (f : Module.End (ZMod 2) E) : f + f = 0 := by
  rw [← two_mul, TwoInv.char_two, zero_mul]

theorem eq_of_add_eq_zero_E {u v : E} (h : u + v = 0) : u = v := by
  calc u = u + (v + v) := by rw [add_self_E v, add_zero]
    _ = (u + v) + v := by rw [add_assoc]
    _ = v := by rw [h, zero_add]

theorem eq_of_add_eq_zero_End {u v : Module.End (ZMod 2) E} (h : u + v = 0) : u = v := by
  calc u = u + (v + v) := by rw [add_self_End v, add_zero]
    _ = (u + v) + v := by rw [add_assoc]
    _ = v := by rw [h, zero_add]

theorem ni_apply (x : E) : S.ni x = S.i x + x := by
  simp only [ni, LinearMap.add_apply, Module.End.one_apply]

theorem D_apply (x : E) : S.D x = S.v (S.i x) + S.i (S.v x) := by
  simp only [D, LinearMap.add_apply, Module.End.mul_apply]

theorem D_sq_apply (x : E) : (S.D ^ 2) x = S.D (S.D x) := by
  rw [sq, Module.End.mul_apply]

theorem D_ni_apply (c : E) : S.D (S.ni c) = S.ni (S.D c) := by
  have h := congrArg (fun f : Module.End (ZMod 2) E => f c) S.D_comm_ni
  simpa only [Module.End.mul_apply] using h

theorem sigma_D_shift (a c : E) : S.b (S.D a) (S.ni c) = S.b a (S.ni (S.D c)) := by
  rw [S.D_selfAdj a (S.ni c), S.D_ni_apply c]

theorem sigma_pow_shift (l : ℕ) (a c : E) :
    S.b a (S.ni ((S.D ^ l) c)) = S.b ((S.D ^ l) a) (S.ni c) := by
  induction l generalizing a c with
  | zero => simp
  | succ l ih =>
    have h1 : (S.D ^ (l + 1)) c = S.D ((S.D ^ l) c) := by
      rw [pow_succ', Module.End.mul_apply]
    have h2 : (S.D ^ (l + 1)) a = (S.D ^ l) (S.D a) := by
      rw [pow_succ, Module.End.mul_apply]
    rw [h1, ← S.sigma_D_shift a ((S.D ^ l) c), ih (S.D a) c, h2]

theorem D_pow_mem_X (z : E) (hz : z ∈ S.X) (k : ℕ) : (S.D ^ k) z ∈ S.X := by
  induction k with
  | zero => simpa using hz
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact S.D_mem_X _ ih

theorem D1_sq : (S.D + 1) ^ 2 = S.D ^ 2 + 1 := by
  have e : (S.D + 1) * (S.D + 1) = S.D * S.D + (S.D + S.D) + 1 := by noncomm_ring
  rw [sq, sq, e, add_self_End, add_zero]

theorem P1_apply (x : E) : ((S.D + 1) ^ 2 : Module.End (ZMod 2) E) x = S.D (S.D x) + x := by
  rw [S.D1_sq, LinearMap.add_apply, Module.End.one_apply, S.D_sq_apply]

theorem P2_apply (x : E) :
    (S.D ^ 2 + S.D + 1 : Module.End (ZMod 2) E) x = S.D (S.D x) + S.D x + x := by
  rw [LinearMap.add_apply, LinearMap.add_apply, Module.End.one_apply, S.D_sq_apply]

theorem finrank_map_ni (Z : Submodule (ZMod 2) E) (hZ : Z ≤ S.X) :
    finrank (ZMod 2) (Z.map S.ni) = finrank (ZMod 2) Z := by
  have hinj : Function.Injective (S.ni ∘ₗ Z.subtype) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    exact Subtype.ext (S.ni_inj_X a (hZ a.2) ha)
  have hrange : LinearMap.range (S.ni ∘ₗ Z.subtype) = Z.map S.ni := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  rw [← hrange]
  exact LinearMap.finrank_range_of_inj hinj

theorem iso_span (A : Set E) (hA : ∀ a ∈ A, ∀ a' ∈ A, S.b a (S.ni a') = 0) :
    ∀ z ∈ Submodule.span (ZMod 2) A, ∀ z' ∈ Submodule.span (ZMod 2) A,
      S.b z (S.ni z') = 0 := by
  have h1 : ∀ z ∈ Submodule.span (ZMod 2) A, ∀ a ∈ A, S.b z (S.ni a) = 0 := by
    intro z hz a ha
    induction hz using Submodule.span_induction with
    | mem x hx => exact hA x hx a ha
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul c x _ hx => simp [hx]
  intro z hz z' hz'
  induction hz' using Submodule.span_induction with
  | mem a ha => exact h1 z hz a ha
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

theorem tot_iso_dim (W : Submodule (ZMod 2) E)
    (hW : ∀ w ∈ W, ∀ w' ∈ W, S.b w w' = 0) : 2 * finrank (ZMod 2) W ≤ finrank (ZMod 2) E := by
  have hsl : LinearMap.SeparatingLeft S.b := fun x hx => S.hbnd x hx
  have hsr : LinearMap.SeparatingRight S.b := fun y hy =>
    S.hbnd y (fun x => by rw [S.b_symm]; exact hy x)
  have hnd : LinearMap.Nondegenerate S.b := ⟨hsl, hsr⟩
  have hle : W ≤ LinearMap.BilinForm.orthogonal S.b W := by
    intro w hw
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    exact hW n hn w hw
  have h1 := LinearMap.BilinForm.finrank_orthogonal hnd W
  have h2 := Submodule.finrank_mono hle
  omega

theorem sigma_alt (x : E) (hx : x ∈ S.X) : S.b x (S.ni x) = 0 := by
  have hq1 : S.q (S.ni x) = 0 := S.hqY _ (S.ni_mem_Y x)
  have hq2 : S.q (S.i x) = 0 := by rw [S.hqi, S.hqX x hx]
  have hexp := S.hq (S.i x) x
  rw [← S.ni_apply x, hq1, hq2, S.hqX x hx] at hexp
  have hbix : S.b (S.i x) x = 0 := by simpa using hexp.symm
  have hbxi : S.b x (S.i x) = 0 := (S.b_symm x (S.i x)).trans hbix
  rw [S.ni_apply x, map_add, hbxi, S.hbalt x, add_zero]

theorem tau_alt (x : E) (hx : x ∈ S.X) : S.b (S.D x) (S.ni x) = 0 := by
  have hyY : S.ni x ∈ S.Y := S.ni_mem_Y x
  have hvx : S.v x = x := (S.hXv x).mp hx
  have hDx : S.D x = S.v (S.ni x) + S.ni x := by
    calc S.D x = S.v (S.i x) + S.i x := by rw [S.D_apply x, hvx]
      _ = S.v (S.i x) + S.i x + (x + x) := by rw [add_self_E, add_zero]
      _ = S.v (S.i x) + x + (S.i x + x) := by abel
      _ = S.v (S.i x + x) + (S.i x + x) := by rw [map_add, hvx]
      _ = S.v (S.ni x) + S.ni x := by rw [S.ni_apply x]
  have hvy : S.v (S.ni x) + S.ni x ∈ S.X := S.hvX _
  have hq0 : S.q (S.v (S.ni x) + S.ni x) = 0 := S.hqX _ hvy
  have hq1 : S.q (S.ni x) = 0 := S.hqY _ hyY
  have hq2 : S.q (S.v (S.ni x)) = 0 := by rw [S.hqv, hq1]
  have hexp := S.hq (S.v (S.ni x)) (S.ni x)
  rw [hq0, hq2, hq1] at hexp
  simp only [zero_add] at hexp
  simp only [hDx, map_add, LinearMap.add_apply, S.hbalt, add_zero]
  exact hexp.symm

theorem cyc_gen (z : E) (hz : z ∈ S.X) (m : ℕ) : S.b ((S.D ^ m) z) (S.ni z) = 0 := by
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' m
  · have hw : (S.D ^ k) z ∈ S.X := S.D_pow_mem_X z hz k
    have h1 := S.sigma_alt _ hw
    have h2 := S.sigma_pow_shift k ((S.D ^ k) z) z
    have h3 : (S.D ^ k) ((S.D ^ k) z) = (S.D ^ (2 * k)) z := by
      rw [two_mul, pow_add, Module.End.mul_apply]
    rw [h3] at h2
    rw [h2] at h1
    exact h1
  · have hw : (S.D ^ k) z ∈ S.X := S.D_pow_mem_X z hz k
    have h1 := S.tau_alt _ hw
    have h2 := S.sigma_pow_shift k ((S.D ^ (k + 1)) z) z
    have h3 : (S.D ^ (k + 1)) z = S.D ((S.D ^ k) z) := by
      rw [pow_succ', Module.End.mul_apply]
    have h4 : (S.D ^ k) ((S.D ^ (k + 1)) z) = (S.D ^ (2 * k + 1)) z := by
      rw [← Module.End.mul_apply, ← pow_add, show k + (k + 1) = 2 * k + 1 by omega]
    calc S.b ((S.D ^ (2 * k + 1)) z) (S.ni z)
          = S.b ((S.D ^ k) ((S.D ^ (k + 1)) z)) (S.ni z) := by rw [h4]
      _ = S.b ((S.D ^ (k + 1)) z) (S.ni ((S.D ^ k) z)) := h2.symm
      _ = S.b (S.D ((S.D ^ k) z)) (S.ni ((S.D ^ k) z)) := by rw [h3]
      _ = 0 := h1

theorem cyc (z : E) (hz : z ∈ S.X) (k l : ℕ) :
    S.b ((S.D ^ k) z) (S.ni ((S.D ^ l) z)) = 0 := by
  rw [S.sigma_pow_shift l ((S.D ^ k) z) z]
  have h : (S.D ^ l) ((S.D ^ k) z) = (S.D ^ (l + k)) z := by
    rw [pow_add, Module.End.mul_apply]
  rw [h]
  exact S.cyc_gen z hz (l + k)

theorem isotropic_bound (Z : Submodule (ZMod 2) E) (hZ : Z ≤ S.X)
    (hiso : ∀ z ∈ Z, ∀ z' ∈ Z, S.b z (S.ni z') = 0) :
    2 * finrank (ZMod 2) Z ≤ finrank (ZMod 2) S.X := by
  have hZ'Y : Z.map S.ni ≤ S.Y := by
    rintro _ ⟨z, _, rfl⟩
    exact S.ni_mem_Y z
  have hdisj : Disjoint Z (Z.map S.ni) := Disjoint.mono hZ hZ'Y S.hXY.disjoint
  have hcard : finrank (ZMod 2) (Z.map S.ni) = finrank (ZMod 2) Z := S.finrank_map_ni Z hZ
  have hWfin : finrank (ZMod 2) ↥(Z ⊔ Z.map S.ni)
      = finrank (ZMod 2) Z + finrank (ZMod 2) (Z.map S.ni) := by
    have := Submodule.finrank_sup_add_finrank_inf_eq Z (Z.map S.ni)
    rw [hdisj.eq_bot, finrank_bot, add_zero] at this
    exact this
  have hW : ∀ w ∈ Z ⊔ Z.map S.ni, ∀ w' ∈ Z ⊔ Z.map S.ni, S.b w w' = 0 := by
    intro w hw w' hw'
    obtain ⟨z₁, hz₁, u₁, hu₁, rfl⟩ := Submodule.mem_sup.mp hw
    obtain ⟨z₂, hz₂, u₂, hu₂, rfl⟩ := Submodule.mem_sup.mp hw'
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hu₁
    obtain ⟨c, hc, rfl⟩ := Submodule.mem_map.mp hu₂
    have e1 : S.b z₁ z₂ = 0 := S.b_X z₁ z₂ (hZ hz₁) (hZ hz₂)
    have e2 : S.b z₁ (S.ni c) = 0 := hiso z₁ hz₁ c hc
    have e3 : S.b (S.ni a) z₂ = 0 := by
      rw [S.b_symm]
      exact hiso z₂ hz₂ a ha
    have e4 : S.b (S.ni a) (S.ni c) = 0 := S.b_Y _ _ (S.ni_mem_Y a) (S.ni_mem_Y c)
    simp only [map_add, LinearMap.add_apply, e1, e2, e3, e4, add_zero]
  have hWle := S.tot_iso_dim (Z ⊔ Z.map S.ni) hW
  rw [hWfin, hcard, S.finrank_E] at hWle
  omega

theorem D_one_of_finrank_two (h : finrank (ZMod 2) S.X = 2) : ∀ x ∈ S.X, S.D x = x := by
  intro x hx
  by_cases hx0 : x = 0
  · simp [hx0]
  have hDx : S.D x ∈ S.X := S.D_mem_X x hx
  have hA : ∀ a ∈ ({x, S.D x} : Set E), ∀ a' ∈ ({x, S.D x} : Set E),
      S.b a (S.ni a') = 0 := by
    have c00 := S.cyc x hx 0 0
    have c01 := S.cyc x hx 0 1
    have c10 := S.cyc x hx 1 0
    have c11 := S.cyc x hx 1 1
    simp only [pow_zero, pow_one, Module.End.one_apply] at c00 c01 c10 c11
    intro a ha a' ha'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha ha'
    rcases ha with h1 | h1 <;> rcases ha' with h2 | h2 <;> rw [h1, h2] <;> assumption
  have hZX : Submodule.span (ZMod 2) ({x, S.D x} : Set E) ≤ S.X := by
    rw [Submodule.span_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact hx
    · exact hDx
  have hiso := S.iso_span ({x, S.D x} : Set E) hA
  have hb := S.isotropic_bound (Submodule.span (ZMod 2) ({x, S.D x} : Set E)) hZX hiso
  rw [h] at hb
  have hDxZ : S.D x ∈ Submodule.span (ZMod 2) ({x, S.D x} : Set E) :=
    Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hWZ : Submodule.span (ZMod 2) ({x} : Set E)
      ≤ Submodule.span (ZMod 2) ({x, S.D x} : Set E) :=
    Submodule.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
  have hW1 : finrank (ZMod 2) (Submodule.span (ZMod 2) ({x} : Set E)) = 1 :=
    finrank_span_singleton hx0
  have hle := Submodule.finrank_mono hWZ
  have heq : Submodule.span (ZMod 2) ({x} : Set E)
      = Submodule.span (ZMod 2) ({x, S.D x} : Set E) :=
    Submodule.eq_of_le_of_finrank_eq hWZ (by omega)
  rw [← heq] at hDxZ
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hDxZ
  have hc01 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases hc01 c with rfl | rfl
  · exfalso
    apply hx0
    apply S.D_inj_X x hx
    rw [← hc, zero_smul]
  · rw [one_smul] at hc
    exact hc.symm

theorem three_dep (h : finrank (ZMod 2) S.X = 4) (x : E) (hx : x ∈ S.X) :
    ∃ a₀ a₁ a₂ : ZMod 2, a₀ • x + a₁ • S.D x + a₂ • S.D (S.D x) = 0 ∧
      (a₀ ≠ 0 ∨ a₁ ≠ 0 ∨ a₂ ≠ 0) := by
  by_contra hcon
  have hli : LinearIndependent (ZMod 2) (fun k : Fin 3 => (S.D ^ (k : ℕ)) x) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg' : g 0 • x + g 1 • S.D x + g 2 • S.D (S.D x) = 0 := by
      simpa [Fin.sum_univ_three, D_sq_apply] using hg
    have key : g 0 = 0 ∧ g 1 = 0 ∧ g 2 = 0 := by
      by_contra hne
      exact hcon ⟨g 0, g 1, g 2, hg', by tauto⟩
    intro i
    fin_cases i
    · exact key.1
    · exact key.2.1
    · exact key.2.2
  have hfin := finrank_span_eq_card hli
  have hsub : Submodule.span (ZMod 2) (Set.range (fun k : Fin 3 => (S.D ^ (k : ℕ)) x)) ≤ S.X := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact S.D_pow_mem_X x hx k
  have hiso := S.iso_span (Set.range (fun k : Fin 3 => (S.D ^ (k : ℕ)) x)) (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact S.cyc x hx i j)
  have hb := S.isotropic_bound _ hsub hiso
  rw [hfin, Fintype.card_fin, h] at hb
  omega

theorem poly_pt (h : finrank (ZMod 2) S.X = 4) (x : E) (hx : x ∈ S.X) :
    ((S.D + 1) ^ 2 : Module.End (ZMod 2) E) x = 0 ∨
      (S.D ^ 2 + S.D + 1 : Module.End (ZMod 2) E) x = 0 := by
  rw [S.P1_apply, S.P2_apply]
  have hy : S.D x ∈ S.X := S.D_mem_X x hx
  have hw : S.D (S.D x) ∈ S.X := S.D_mem_X _ hy
  obtain ⟨a₀, a₁, a₂, hrel, hne⟩ := S.three_dep h x hx
  have hz : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rcases hz a₀ with rfl | rfl
  · rcases hz a₁ with rfl | rfl
    · rcases hz a₂ with rfl | rfl
      · simp at hne
      · simp only [zero_smul, one_smul, zero_add, add_zero] at hrel
        have h1 : S.D x = 0 := S.D_inj_X (S.D x) hy hrel
        have h2 : x = 0 := S.D_inj_X x hx h1
        left
        rw [h2]
        simp
    · rcases hz a₂ with rfl | rfl
      · simp only [zero_smul, one_smul, zero_add, add_zero] at hrel
        have h2 : x = 0 := S.D_inj_X x hx hrel
        left
        rw [h2]
        simp
      · simp only [zero_smul, one_smul, zero_add, add_zero] at hrel
        have h0 : S.D (x + S.D x) = 0 := by
          rw [map_add]
          exact hrel
        have hxy : x + S.D x = 0 := S.D_inj_X (x + S.D x) (S.X.add_mem hx hy) h0
        have hDx : S.D x = x := (eq_of_add_eq_zero_E hxy).symm
        left
        rw [hDx, hDx]
        exact add_self_E x
  · rcases hz a₁ with rfl | rfl
    · rcases hz a₂ with rfl | rfl
      · simp only [zero_smul, one_smul, zero_add, add_zero] at hrel
        left
        rw [hrel]
        simp
      · simp only [zero_smul, one_smul, zero_add, add_zero] at hrel
        left
        rw [add_comm]
        exact hrel
    · rcases hz a₂ with rfl | rfl
      · simp only [zero_smul, one_smul, zero_add, add_zero] at hrel
        have hDx : S.D x = x := (eq_of_add_eq_zero_E hrel).symm
        left
        rw [hDx, hDx]
        exact add_self_E x
      · simp only [zero_smul, one_smul, zero_add, add_zero] at hrel
        right
        calc S.D (S.D x) + S.D x + x = x + S.D x + S.D (S.D x) := by abel
          _ = 0 := hrel

theorem rel_of_finrank_four (h : finrank (ZMod 2) S.X = 4) :
    (∀ x ∈ S.X, (((S.D + 1) ^ 2 : Module.End (ZMod 2) E)) x = 0) ∨
      (∀ x ∈ S.X, ((S.D ^ 2 + S.D + 1 : Module.End (ZMod 2) E)) x = 0) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hx, hx1⟩ := hcon.1
  obtain ⟨w, hw, hw2⟩ := hcon.2
  have hx2 := (S.poly_pt h x hx).resolve_left hx1
  have hw1 := (S.poly_pt h w hw).resolve_right hw2
  have hxw : x + w ∈ S.X := S.X.add_mem hx hw
  rcases S.poly_pt h (x + w) hxw with h1 | h2
  · apply hx1
    have e : ((S.D + 1) ^ 2 : Module.End (ZMod 2) E) (x + w)
        = ((S.D + 1) ^ 2 : Module.End (ZMod 2) E) x + ((S.D + 1) ^ 2 : Module.End (ZMod 2) E) w :=
      map_add _ _ _
    rw [e, hw1, add_zero] at h1
    exact h1
  · apply hw2
    have e : (S.D ^ 2 + S.D + 1 : Module.End (ZMod 2) E) (x + w)
        = (S.D ^ 2 + S.D + 1 : Module.End (ZMod 2) E) x
          + (S.D ^ 2 + S.D + 1 : Module.End (ZMod 2) E) w :=
      map_add _ _ _
    rw [e, hx2, zero_add] at h2
    exact h2

theorem kills_E (f : Module.End (ZMod 2) E) (hfi : f * S.i = S.i * f)
    (hf : ∀ x ∈ S.X, f x = 0) : f = 0 := by
  have hmap : S.X.map S.ni = S.Y := by
    have hle : S.X.map S.ni ≤ S.Y := by
      rintro _ ⟨x, _, rfl⟩
      exact S.ni_mem_Y x
    exact Submodule.eq_of_le_of_finrank_eq hle
      (by rw [S.finrank_map_ni S.X le_rfl, S.finrank_Y])
  have hfni : ∀ x ∈ S.X, f (S.ni x) = 0 := by
    intro x hx
    have h1 : f (S.i x) = 0 := by
      have h := congrArg (fun g : Module.End (ZMod 2) E => g x) hfi
      simp only [Module.End.mul_apply] at h
      rw [hf x hx, map_zero] at h
      exact h
    rw [S.ni_apply x, map_add, h1, hf x hx, add_zero]
  have hfY : ∀ y ∈ S.Y, f y = 0 := by
    intro y hy
    rw [← hmap] at hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    exact hfni x hx
  apply LinearMap.ext
  intro e
  have hsup : e ∈ S.X ⊔ S.Y := by
    rw [S.hXY.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hsup
  rw [LinearMap.zero_apply, map_add, hf x hx, hfY y hy, add_zero]

theorem t_sq_ne_one (hX : S.X ≠ ⊥) : S.t ^ 2 ≠ 1 := by
  intro hsq
  have h1 : S.t * S.t = 1 := by
    rw [← sq]
    exact hsq
  rw [S.t_sq] at h1
  have hDt : S.D * S.t = 0 := by simpa using h1
  have hinv : S.t * (S.i * S.v) = 1 := by
    simp only [t, mul_assoc]
    rw [← mul_assoc S.i S.i S.v, S.hi, one_mul, S.hv]
  have hD0 : S.D = 0 := by
    calc S.D = S.D * (S.t * (S.i * S.v)) := by rw [hinv, mul_one]
      _ = (S.D * S.t) * (S.i * S.v) := by rw [mul_assoc]
      _ = 0 := by rw [hDt, zero_mul]
  obtain ⟨x, hxX, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hX
  exact hx0 (S.D_inj_X x hxX (by simp [hD0]))

theorem t_pow_three_gen : S.t ^ 3 = S.D ^ 2 * S.t + S.D + S.t := by
  calc S.t ^ 3 = S.t * (S.t * S.t) := pow_three S.t
    _ = S.t * (S.D * S.t + 1) := by rw [S.t_sq]
    _ = S.t * S.D * S.t + S.t := by noncomm_ring
    _ = S.D * S.t * S.t + S.t := by rw [← S.D_comm_t]
    _ = S.D * (S.t * S.t) + S.t := by rw [mul_assoc]
    _ = S.D * (S.D * S.t + 1) + S.t := by rw [S.t_sq]
    _ = S.D * S.D * S.t + S.D + S.t := by noncomm_ring
    _ = S.D ^ 2 * S.t + S.D + S.t := by rw [sq]

theorem t4B_of (hD2 : S.D ^ 2 = S.D + 1) (t3B : S.t ^ 3 = S.D * S.t + S.D) :
    S.t ^ 4 = S.t + S.D := by
  calc S.t ^ 4 = S.t * S.t ^ 3 := pow_succ' S.t 3
    _ = S.t * (S.D * S.t + S.D) := by rw [t3B]
    _ = S.t * S.D * S.t + S.t * S.D := by noncomm_ring
    _ = S.D * S.t * S.t + S.D * S.t := by rw [← S.D_comm_t]
    _ = S.D * (S.t * S.t) + S.D * S.t := by rw [mul_assoc]
    _ = S.D * (S.D * S.t + 1) + S.D * S.t := by rw [S.t_sq]
    _ = S.D * S.D * S.t + S.D + S.D * S.t := by noncomm_ring
    _ = S.D ^ 2 * S.t + S.D + S.D * S.t := by rw [sq]
    _ = (S.D + 1) * S.t + S.D + S.D * S.t := by rw [hD2]
    _ = S.D * S.t + S.t + S.D + S.D * S.t := by noncomm_ring
    _ = (S.D * S.t + S.D * S.t) + (S.t + S.D) := by abel
    _ = S.t + S.D := by rw [add_self_End, zero_add]

theorem t5B_of (t4 : S.t ^ 4 = S.t + S.D) : S.t ^ 5 = 1 := by
  calc S.t ^ 5 = S.t * S.t ^ 4 := pow_succ' S.t 4
    _ = S.t * (S.t + S.D) := by rw [t4]
    _ = S.t * S.t + S.t * S.D := by rw [mul_add]
    _ = S.D * S.t + 1 + S.t * S.D := by rw [S.t_sq]
    _ = S.D * S.t + 1 + S.D * S.t := by rw [← S.D_comm_t]
    _ = 1 + (S.D * S.t + S.D * S.t) := by abel
    _ = 1 := by rw [add_self_End, add_zero]

theorem t_pow_three_of_finrank_two (h : finrank (ZMod 2) S.X = 2) : S.t ^ 3 = 1 := by
  have hD1 := S.D_one_of_finrank_two h
  have hc : Commute S.D S.i := S.D_comm_i
  have hfi : (S.D + 1) * S.i = S.i * (S.D + 1) := (hc.add_left (Commute.one_left S.i)).eq
  have hf : ∀ x ∈ S.X, (S.D + 1) x = 0 := by
    intro x hx
    rw [LinearMap.add_apply, Module.End.one_apply, hD1 x hx, add_self_E]
  have hkill : S.D + 1 = 0 := S.kills_E (S.D + 1) hfi hf
  have h11 : (1 : Module.End (ZMod 2) E) + 1 = 0 := by
    rw [one_add_one_eq_two, TwoInv.char_two]
  have hD : S.D = 1 := by
    calc S.D = S.D + (1 + 1) := by rw [h11, add_zero]
      _ = (S.D + 1) + 1 := by rw [add_assoc]
      _ = 1 := by rw [hkill, zero_add]
  have ht2 : S.t * S.t = S.t + 1 := by rw [S.t_sq, hD, one_mul]
  calc S.t ^ 3 = S.t * (S.t * S.t) := pow_three S.t
    _ = S.t * (S.t + 1) := by rw [ht2]
    _ = S.t * S.t + S.t := by rw [mul_add, mul_one]
    _ = S.t + 1 + S.t := by rw [ht2]
    _ = 1 + (S.t + S.t) := by abel
    _ = 1 := by rw [add_self_End, add_zero]

theorem t_pow_of_finrank_four (h : finrank (ZMod 2) S.X = 4) :
    S.t ^ 3 = 1 ∨ S.t ^ 5 = 1 ∨ S.t ^ 6 = 1 := by
  have hc : Commute S.D S.i := S.D_comm_i
  rcases S.rel_of_finrank_four h with h1 | h2
  · have hfi : (S.D + 1) ^ 2 * S.i = S.i * (S.D + 1) ^ 2 :=
      ((hc.add_left (Commute.one_left S.i)).pow_left 2).eq
    have hf : (S.D + 1) ^ 2 = 0 := S.kills_E ((S.D + 1) ^ 2) hfi h1
    have hD2 : S.D ^ 2 = 1 := by
      have h' : S.D ^ 2 + 1 = 0 := by
        rw [← S.D1_sq]
        exact hf
      exact eq_of_add_eq_zero_End h'
    have ht3 : S.t ^ 3 = S.D := by
      rw [S.t_pow_three_gen, hD2, one_mul, add_right_comm, add_self_End, zero_add]
    right
    right
    have h6 : S.t ^ 6 = S.t ^ 3 * S.t ^ 3 := pow_add S.t 3 3
    rw [h6, ht3, ← sq, hD2]
  · have hfi : (S.D ^ 2 + S.D + 1) * S.i = S.i * (S.D ^ 2 + S.D + 1) :=
      (((hc.pow_left 2).add_left hc).add_left (Commute.one_left S.i)).eq
    have hf : S.D ^ 2 + S.D + 1 = 0 := S.kills_E (S.D ^ 2 + S.D + 1) hfi h2
    have hD2 : S.D ^ 2 = S.D + 1 := by
      have h' : S.D ^ 2 + (S.D + 1) = 0 := by
        rw [← add_assoc]
        exact hf
      exact eq_of_add_eq_zero_End h'
    have t3B : S.t ^ 3 = S.D * S.t + S.D := by
      rw [S.t_pow_three_gen, hD2, add_mul, one_mul]
      calc S.D * S.t + S.t + S.D + S.t = S.D * S.t + S.D + (S.t + S.t) := by abel
        _ = S.D * S.t + S.D := by rw [add_self_End, add_zero]
    have t4 : S.t ^ 4 = S.t + S.D := S.t4B_of hD2 t3B
    right
    left
    exact S.t5B_of t4

theorem order_t (h : finrank (ZMod 2) S.X = 2 ∨ finrank (ZMod 2) S.X = 4) :
    S.t ^ 2 ≠ 1 ∧ (S.t ^ 3 = 1 ∨
      (finrank (ZMod 2) S.X = 4 ∧ (S.t ^ 5 = 1 ∨ S.t ^ 6 = 1))) := by
  have hX : S.X ≠ ⊥ := by
    intro hbot
    have h0 : finrank (ZMod 2) S.X = 0 := by
      rw [hbot]
      exact finrank_bot _ _
    rcases h with h | h <;> omega
  refine ⟨S.t_sq_ne_one hX, ?_⟩
  rcases h with h2 | h4
  · exact Or.inl (S.t_pow_three_of_finrank_two h2)
  · rcases S.t_pow_of_finrank_four h4 with h3 | h5 | h6
    · exact Or.inl h3
    · exact Or.inr ⟨h4, Or.inl h5⟩
    · exact Or.inr ⟨h4, Or.inr h6⟩

end TwoInv

end CFSG.Quasithin.RonanF95
