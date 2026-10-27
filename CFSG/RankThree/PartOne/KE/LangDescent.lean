module

public import CFSG.GroupTheory.LangNormOneDescent
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.GroupTheory.Subgroup.Center

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG.GroupTheory

theorem conj_mul_pow_aut {C : Type*} [Group C] (x : C) (T : MulAut C) (n : ℕ) :
    (MulAut.conj x * T) ^ n =
      MulAut.conj (((List.range n).map fun i => (T ^ i) x).prod) * T ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hT : T ^ n * MulAut.conj x = MulAut.conj ((T ^ n) x) * T ^ n := by
      ext u
      simp [MulAut.conj_apply, map_mul, map_inv]
    rw [pow_succ, ih, List.range_succ, List.map_append, List.prod_append, List.map_singleton,
      List.prod_singleton, map_mul, mul_assoc, ← mul_assoc (T ^ n), hT, pow_succ]
    simp only [mul_assoc]

theorem exists_inner_conj_eq_of_lang {Γ M : Type*} [Group Γ] [Group M]
    (hZ : Subgroup.center Γ = ⊥) (F₀ : MulAut Γ) {p : ℕ} (hp : 1 ≤ p) (hF₀p : F₀ ^ p = 1)
    (S₀ : MulAut M) (hLang : ∀ m : M, ∃ h, m = h⁻¹ * S₀ h) (e : Γ →* M)
    (he : Function.Injective e) (heF₀ : ∀ g, e (F₀ g) = S₀ (e g))
    (hmem : ∀ h : M, (S₀ ^ p) h = h → h ∈ e.range) (x : Γ)
    (hβ : (MulAut.conj x * F₀) ^ p = 1) :
    ∃ g : Γ, MulAut.conj g * (MulAut.conj x * F₀) * (MulAut.conj g)⁻¹ = F₀ := by
  classical
  have hβ' := hβ
  rw [conj_mul_pow_aut, hF₀p, mul_one] at hβ'
  generalize hNdef : ((List.range p).map fun i => (F₀ ^ i) x).prod = N at hβ'
  have hN1 : N = 1 := by
    have hc : N ∈ Subgroup.center Γ := by
      refine Subgroup.mem_center_iff.2 fun g => ?_
      have h1 : N * g * N⁻¹ = g := by
        have := congrArg (fun φ : MulAut Γ => φ g) hβ'
        simpa only [MulAut.conj_apply, MulAut.one_apply] using this
      calc g * N = N * g * N⁻¹ * N := by rw [h1]
        _ = N * g := by group
    rw [hZ] at hc
    exact Subgroup.mem_bot.1 hc
  have hS₀iter : ∀ (i : ℕ) (g : Γ), (⇑S₀.toMonoidHom)^[i] (e g) = e ((F₀ ^ i) g) := by
    intro i
    induction i with
    | zero => intro g; rfl
    | succ i ih =>
      intro g
      rw [Function.iterate_succ_apply', ih, MulEquiv.coe_toMonoidHom, ← heF₀,
        ← MulAut.mul_apply, ← pow_succ']
  have hnormx : ((List.range p).map fun i => (⇑S₀.toMonoidHom)^[i] (e x)).prod = 1 := by
    have h1 : ((List.range p).map fun i => (⇑S₀.toMonoidHom)^[i] (e x)) =
        ((List.range p).map fun i => (F₀ ^ i) x).map e := by
      rw [List.map_map]
      exact List.map_congr_left fun i _ => hS₀iter i x
    rw [h1, ← map_list_prod, hNdef, hN1, map_one]
  obtain ⟨h, hR, hxh, -⟩ :=
    exceptional_Lang_norm_one_descent S₀.toMonoidHom hp hLang (e x) hnormx
  have hS₀iterate : ∀ (n : ℕ) (y : M), (⇑S₀.toMonoidHom)^[n] y = (S₀ ^ n) y := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih =>
      intro y
      rw [Function.iterate_succ_apply', ih, pow_succ', MulAut.mul_apply]
      rfl
  have hhS : (S₀ ^ p) h = h := by
    rw [← hS₀iterate]
    exact mem_iterateFixedSubgroup.1 hR
  obtain ⟨g, rfl⟩ := hmem h hhS
  have hxh' : e x = (e g)⁻¹ * S₀ (e g) := hxh
  have hinvapp : ∀ u : Γ, ((MulAut.conj g : MulAut Γ)⁻¹) u = g⁻¹ * u * g := fun u => by
    rw [← map_inv, MulAut.conj_apply, inv_inv]
  refine ⟨g, MulEquiv.ext fun u => he ?_⟩
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, hinvapp u]
  simp only [MulAut.conj_apply, map_mul, map_inv, heF₀]
  rw [hxh']
  group

end CFSG.RankThree.PartOne.KE
