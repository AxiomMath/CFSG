module

public import CFSG.Quasithin.Background.C124YLS2Alg
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.TotallySplit

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124.YL.S2

open Matrix
open scoped MatrixGroups

variable {F : Type*} [Field F]

theorem card_fix_sq_le [Finite F] {ω τω : F} (hne : τω ≠ ω) (g : (Fin 2 → F) →+ (Fin 2 → F))
    (hg : ∀ q, g (ω • q) = τω • g q) (L : AddSubgroup (Fin 2 → F)) (hL : ∀ x ∈ L, ω • x ∈ L) :
    Nat.card ↥(L ⊓ (g - AddMonoidHom.id _).ker) ^ 2 ≤ Nat.card L := by
  set X := L ⊓ (g - AddMonoidHom.id (Fin 2 → F)).ker with hX
  have hmem : ∀ x, x ∈ X ↔ x ∈ L ∧ g x = x := fun x => by
    simp [hX, AddSubgroup.mem_inf, AddMonoidHom.mem_ker, sub_eq_zero]
  let f : X × X → L := fun p => ⟨(p.1 : Fin 2 → F) + ω • (p.2 : Fin 2 → F),
    L.add_mem ((hmem _).1 p.1.2).1 (hL _ ((hmem _).1 p.2.2).1)⟩
  have hf : Function.Injective f := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ h
    have h1 : (x : Fin 2 → F) + ω • (y : Fin 2 → F) = (x' : Fin 2 → F) + ω • (y' : Fin 2 → F) :=
      congrArg Subtype.val h
    have hx := ((hmem _).1 x.2).2
    have hy := ((hmem _).1 y.2).2
    have hx' := ((hmem _).1 x'.2).2
    have hy' := ((hmem _).1 y'.2).2
    have e : (x : Fin 2 → F) - x' = ω • ((y' : Fin 2 → F) - y) := by
      calc (x : Fin 2 → F) - x' = (x + ω • (y : Fin 2 → F)) - x' - ω • (y : Fin 2 → F) := by abel
        _ = (x' + ω • (y' : Fin 2 → F)) - x' - ω • (y : Fin 2 → F) := by rw [h1]
        _ = ω • ((y' : Fin 2 → F) - y) := by rw [smul_sub]; abel
    have gx : g ((x : Fin 2 → F) - x') = (x : Fin 2 → F) - x' := by rw [map_sub, hx, hx']
    have gy : g ((y' : Fin 2 → F) - y) = (y' : Fin 2 → F) - y := by rw [map_sub, hy', hy]
    rw [e, hg, gy] at gx
    have h3 : (τω - ω) • ((y' : Fin 2 → F) - y) = 0 := by rw [sub_smul, gx, sub_self]
    have hb : (y' : Fin 2 → F) - y = 0 := by
      rcases smul_eq_zero.1 h3 with h | h
      · exact absurd (sub_eq_zero.1 h) hne
      · exact h
    have hyy : (y : Fin 2 → F) = y' := (sub_eq_zero.1 hb).symm
    have hxx : (x : Fin 2 → F) = x' := by
      rw [hyy] at h1
      exact add_right_cancel h1
    exact Prod.ext (Subtype.ext hxx) (Subtype.ext hyy)
  have := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod] at this
  simpa [sq] using this

theorem no_semilin_commute {ω : F} (τ : F → F) (hτ1 : τ 1 = 1) (hne : τ ω ≠ ω)
    (g : (Fin 2 → F) →+ (Fin 2 → F)) (hg : ∀ a q, g (a • q) = τ a • g q)
    (hinj : Function.Injective g)
    (hu1 : ∀ q, g (((uSL (1 : F) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ q) =
      ((uSL (1 : F) : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ g q)
    (huω : ∀ q, g (((uSL ω : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ q) =
      ((uSL ω : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ g q) : False := by
  have key : ∀ b : F, (∀ q, g (((uSL b : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ q) =
      ((uSL b : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ g q) →
      τ b * (g ![1, 0]) 1 = 0 ∧ τ b * (g ![1, 0]) 0 = b * (g ![0, 1]) 1 := by
    intro b hb
    have h := hb ![0, 1]
    have e : (![b, 1] : Fin 2 → F) = ![0, 1] + b • ![1, 0] := by
      ext i
      fin_cases i <;> simp
    rw [uSL_mulVec, uSL_mulVec] at h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zero_add, mul_one] at h
    rw [e, map_add, hg] at h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one] at h0 h1
    exact ⟨by linear_combination h1, by linear_combination h0⟩
  obtain ⟨a1, a2⟩ := key 1 hu1
  obtain ⟨b1, b2⟩ := key ω huω
  rw [hτ1] at a1 a2
  have hv0 : (g ![1, 0]) 0 = 0 := by
    have h3 : (τ ω - ω) * (g ![1, 0]) 0 = 0 := by
      rw [sub_mul, b2]
      linear_combination (-ω) * a2
    rcases mul_eq_zero.1 h3 with h | h
    · exact absurd (sub_eq_zero.1 h) hne
    · exact h
  have hv1 : (g ![1, 0]) 1 = 0 := by simpa using a1
  have hv : g ![1, 0] = 0 := by
    ext i
    fin_cases i
    · exact hv0
    · exact hv1
  have := hinj (hv.trans (map_zero g).symm)
  have h0 := congrFun this 0
  simp at h0

theorem exists_SL_of_linear [Finite F] (hF : Nat.card F = 4) (g : (Fin 2 → F) →+ (Fin 2 → F))
    (hlin : ∀ (a : F) q, g (a • q) = a • g q) {k : ℕ} (hk : ∀ q, g^[2 ^ k] q = q) :
    ∃ s : SL(2, F), ∀ q, g q = ((s : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *ᵥ q := by
  let gl : (Fin 2 → F) →ₗ[F] (Fin 2 → F) :=
    { toFun := g, map_add' := map_add g, map_smul' := fun a q => hlin a q }
  have hgl : gl ^ 2 ^ k = 1 := by
    refine LinearMap.ext fun q => ?_
    rw [Module.End.pow_apply, Module.End.one_apply]
    exact hk q
  have hdet : (LinearMap.toMatrix' gl).det = 1 := by
    have h1 : LinearMap.det gl ^ 2 ^ k = 1 := by
      rw [← map_pow, hgl, map_one]
    have h2 : LinearMap.det gl = (LinearMap.toMatrix' gl).det := by
      conv_lhs => rw [← Matrix.toLin'_toMatrix' gl]
      exact LinearMap.det_toLin' _
    rw [← h2]
    have h0 : LinearMap.det gl ≠ 0 := by
      intro h
      rw [h, zero_pow (by positivity)] at h1
      exact zero_ne_one h1
    have : Fintype F := Fintype.ofFinite F
    have h3 : LinearMap.det gl ^ 3 = 1 := by
      have := FiniteField.pow_card_sub_one_eq_one (LinearMap.det gl) h0
      rwa [show Fintype.card F = 4 by rw [← Nat.card_eq_fintype_card, hF]] at this
    have h4 := (pow_gcd_eq_one (a := LinearMap.det gl) (m := 2 ^ k) (n := 3)).2 ⟨h1, h3⟩
    have hc : Nat.gcd (2 ^ k) 3 = 1 := by
      apply Nat.Coprime.pow_left
      norm_num
    rwa [hc, pow_one] at h4
  refine ⟨⟨LinearMap.toMatrix' gl, hdet⟩, fun q => ?_⟩
  have := congrArg (fun f : (Fin 2 → F) →ₗ[F] (Fin 2 → F) => f q) (Matrix.toLin'_toMatrix' gl)
  simp only [Matrix.toLin'_apply] at this
  exact this.symm

end CFSG.Quasithin.C124.YL.S2
