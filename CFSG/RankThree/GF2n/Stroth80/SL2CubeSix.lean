module

public import CFSG.RankThree.GF2n.Stroth80.SL2KDescent
public import CFSG.RankThree.GF2n.Smith81.TiD2Alg

public section

namespace CFSG.RankThree.GF2n.Stroth80.SL2Descent

open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.RankThree.GF2n.Smith81
open scoped MatrixGroups

section Six

variable {K F : Type} [Field K] [Fintype K] [CharP K 2] [Field F] [Fintype F] [Algebra K F]

theorem exists_frobTensor_single_eq [CharP F 2] (a : ℕ) {u u' : ((↥({a} : Finset ℕ)) → Fin 2) → F}
    (hu : u ≠ 0) (hu' : u' ≠ 0) :
    ∃ g : SL(2, F), frobTensor F F {a} g u = u' := by
  classical
  let a₀ : ↥({a} : Finset ℕ) := ⟨a, Finset.mem_singleton_self a⟩
  haveI : Unique ↥({a} : Finset ℕ) :=
    ⟨⟨a₀⟩, fun i => Subtype.ext (Finset.mem_singleton.mp i.2)⟩
  let e : (↥({a} : Finset ℕ) → Fin 2) ≃ Fin 2 := Equiv.funUnique _ _
  let col : ((↥({a} : Finset ℕ) → Fin 2) → F) → (Fin 2 → F) := fun w s => w (e.symm s)
  have key : ∀ (g : SL(2, F)) (w : (↥({a} : Finset ℕ) → Fin 2) → F),
      col (frobTensor F F {a} g w) = (twistMat F a g).mulVec (col w) := by
    intro g w
    funext s
    simp only [col, frobTensor, tensorRep_apply, tmatE, Matrix.mulVec, dotProduct]
    rw [← Fintype.sum_equiv e.symm (fun t => twistMat F a g s t * w (e.symm t))]
    intro x
    have hd : ((default : ↥({a} : Finset ℕ)) : ℕ) = a :=
      Finset.mem_singleton.mp (default : ↥({a} : Finset ℕ)).2
    rw [Fintype.prod_unique, hd]
    simp [e]
  have hcol : Function.Injective col := fun w w' h => by
    funext x
    have h1 := congrFun h (e x)
    simpa [col] using h1
  have hc : col u ≠ 0 := fun h => hu (hcol (h.trans (by funext s; rfl)))
  have hc' : col u' ≠ 0 := fun h => hu' (hcol (h.trans (by funext s; rfl)))
  obtain ⟨g', hg'⟩ := D2.exists_sl_mulVec_eq hc hc'
  haveI : ExpChar F 2 := ExpChar.prime Nat.prime_two
  let σ : F ≃+* F := iterateFrobeniusEquiv F 2 a
  have hσ : ∀ x, σ x = x ^ 2 ^ a := fun x => iterateFrobeniusEquiv_def F 2 a x
  refine ⟨D2.slMap σ.symm g', hcol ?_⟩
  rw [key]
  have h2 : twistMat F a (D2.slMap σ.symm g') = (g' : Mat2 F) := by
    ext i j
    rw [twistMat_apply, D2.coe_slMap, Algebra.algebraMap_self, RingHom.id_apply, ← hσ,
      σ.apply_symm_apply]
  rw [h2, hg']


theorem six_dim_vanish [CharP F 2] {k : ℕ} (hk : Fintype.card K = 2 ^ k) (hk1 : 1 ≤ k)
    (hK4 : 4 ≤ Nat.card K) (hF : Fintype.card F = 2 ^ (k * 3)) {X : Type} [AddCommGroup X]
    [Module K X] [Module.Finite K X] (hdim : Module.finrank K X = 6)
    (ρ : Representation K SL(2, F) X) [Fact ρ.IsIrreducible] (hnt : ∃ g, ρ g ≠ 1) (Q : X → K)
    (hQsmul : ∀ (a : K) x, Q (a • x) = a ^ 2 * Q x) (hQρ : ∀ g x, Q (ρ g x) = Q x) :
    ∀ x, Q x = 0 := by
  classical
  haveI : Finite X := Module.finite_of_finite K
  have hn : 1 ≤ k * 3 := by omega
  obtain ⟨f, hf1, hDk, hb⟩ := exists_descent_gen (ρ := ρ) hk hn hF hnt
  haveI : Finite (EndRing ρ) := finite_endRing ρ
  haveI : Module.Finite (EndRing ρ) X := Module.Finite.of_finite
  let b := Module.finBasis (EndRing ρ) X
  obtain ⟨E₀, _, _, _, _, ιD₀, J₀, -, -, ⟨Φ₀⟩, -, -⟩ := hb b
  obtain ⟨ν, -⟩ := exists_ringHom_endRing b (algebraMap K F) ιD₀ Φ₀
  have hf3 : f ∣ 3 := Nat.dvd_of_mul_dvd_mul_left (by omega) (dvd_of_ringHom ν hDk hF)
  obtain ⟨J, hJne, hJn, ⟨Φ⟩, -, hdimJ⟩ := descent_core_alg (F := F) (E := F) hn hF ρ hnt hDk b ν
  have hfin := finrank_eq_mul_finrank (ρ := ρ) hk hk1 hDk
  rw [hdim, hdimJ] at hfin
  have hJ1 : J.card = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hf3 with h1 | h3
    · exfalso
      subst h1
      rcases Nat.lt_or_ge J.card 3 with h | h
      · interval_cases J.card <;> omega
      · have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) h
        omega
    · subst h3
      have h2 : 2 ^ J.card = 2 ^ 1 := by omega
      exact Nat.pow_right_injective le_rfl h2
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hJ1
  let θ₀ : X → (Fin (Module.finrank (EndRing ρ) X) → F) := fun x i => ν (b.repr x i)
  have hθ₀inj : Function.Injective θ₀ := coords_injective b ν
  have hθ₀rep : ∀ g x, θ₀ (ρ g x) = matRepE b ν g (θ₀ x) := fun g x => by
    rw [matRepE_apply]
    exact coords_rep b ν g x
  have hθ₀zero : θ₀ 0 = 0 := by
    funext i
    show ν (b.repr 0 i) = 0
    rw [map_zero, Finsupp.zero_apply]
    exact ν.map_zero
  have htrans : ∀ x y : X, x ≠ 0 → y ≠ 0 → ∃ g : SL(2, F), ρ g x = y := by
    intro x y hx hy
    have hu : Φ.toLinearEquiv (θ₀ x) ≠ 0 := fun h =>
      hx (hθ₀inj ((Φ.toLinearEquiv.map_eq_zero_iff.mp h).trans hθ₀zero.symm))
    have hu' : Φ.toLinearEquiv (θ₀ y) ≠ 0 := fun h =>
      hy (hθ₀inj ((Φ.toLinearEquiv.map_eq_zero_iff.mp h).trans hθ₀zero.symm))
    obtain ⟨g, hg⟩ := exists_frobTensor_single_eq a hu hu'
    refine ⟨g, hθ₀inj ?_⟩
    apply Φ.toLinearEquiv.injective
    rw [hθ₀rep]
    exact (equiv_apply Φ g (θ₀ x)).trans hg
  obtain ⟨c, hc0, hc1⟩ := D2.exists_ne_zero_sq_ne_one (K := K) hK4
  intro x
  by_cases hx : x = 0
  · subst hx
    have h1 := hQsmul 0 0
    simpa using h1
  · have hcx : c • x ≠ 0 := smul_ne_zero hc0 hx
    obtain ⟨g, hg⟩ := htrans x (c • x) hx hcx
    have h1 : Q (c • x) = Q x := by rw [← hg, hQρ]
    rw [hQsmul] at h1
    have h2 : (c ^ 2 - 1) * Q x = 0 := by linear_combination h1
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hc1)

end Six

end CFSG.RankThree.GF2n.Stroth80.SL2Descent
