module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterFaithfulRadical
public import CFSG.LocalAnalysis.StandardType.GGCartanATypeArith
import CFSG.LocalAnalysis.StandardType.GGRCWeylCard

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem ta_cast_eq {Λ : Type} {n : ℕ} (e : Fin n ≃ Λ) {C : Matrix Λ Λ ℤ}
    (hC : GGIntCartan ((CoxeterMatrix.A n).reindex e) C) (p : ℕ) (i j : Λ) :
    (C i j : ZMod p) = ggCartanAMod n p (e.symm i) (e.symm j) := by
  have hsymm : ∀ a b : Fin n, CartanMatrix.A n a b = CartanMatrix.A n b a := fun a b => by
    simp only [CartanMatrix.A, Matrix.of_apply, Fin.ext_iff]
    split_ifs <;> omega
  rcases hC.eq_or_eq_transpose ((ggIntCartan_A n).reindex e)
      ((ggAtMostOneMultipleEdge_A n).reindex e) with h | h
  · rw [h]
    simp [ggCartanAMod, Matrix.reindex_apply]
  · rw [h]
    simp [ggCartanAMod, Matrix.reindex_apply, hsymm]

private theorem ta_independent {Λ : Type} [Fintype Λ] [DecidableEq Λ] {n : ℕ} (e : Fin n ≃ Λ)
    {C : Matrix Λ Λ ℤ} (hC : GGIntCartan ((CoxeterMatrix.A n).reindex e) C) {p : ℕ}
    [Fact p.Prime] (hpn : ¬ p ∣ n + 1) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V) (hP : ∀ i j, α i (h j) = (C i j : ZMod p)) :
    LinearIndependent (ZMod p) h := by
  refine linearIndependent_of_det_ne_zero h α ?_
  have hmap : (Matrix.of fun i j => α i (h j)) =
      Matrix.reindex e e ((CartanMatrix.A n).map fun x : ℤ => (x : ZMod p)) := by
    ext i j
    simp [Matrix.reindex_apply, hP, ta_cast_eq e hC p i j, ggCartanAMod]
  rw [hmap, Matrix.det_reindex_self, ← Int.cast_det (CartanMatrix.A n), CartanMatrix.A_det]
  intro h0
  apply hpn
  have h1 : (p : ℤ) ∣ (n : ℤ) + 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd ((n : ℤ) + 1) p).mp h0
  exact_mod_cast h1

private theorem ta_four_le {n p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (hn : 3 ≤ n) (hpn : p ∣ n + 1) :
    4 ≤ n := by
  by_contra hlt
  obtain rfl : n = 3 := by omega
  have h2 : p ∣ 2 * 2 := hpn
  rcases (Nat.Prime.dvd_mul Fact.out).mp h2 with h | h <;>
    exact hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h)

theorem ggCoxeterIso_of_typeA_odd {Λ : Type} {M : CoxeterMatrix Λ} {n : ℕ} (e : Fin n ≃ Λ)
    (hM : M = (CoxeterMatrix.A n).reindex e) (hn : 3 ≤ n) {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V) (hP : ∀ i j, α i (h j) = (C i j : ZMod p))
    (s : Λ → V ≃ₗ[ZMod p] V) (hs : ∀ i v, s i v = v - α i v • h i) :
    ∃ f : M.Group ≃* ↥(Subgroup.closure (Set.range s)),
      ∀ i, (f (M.simple i) : V ≃ₗ[ZMod p] V) = s i := by
  subst hM
  classical
  let _ : Fintype Λ := Fintype.ofEquiv (Fin n) e
  have hα : ∀ i, α i (h i) = 2 := fun i => by rw [hP, hC.1 i]; norm_num
  have hMW : GGIsWeylMatrixFixed ((CoxeterMatrix.A n).reindex e) :=
    Or.inl ⟨n, e, by omega, Or.inl rfl⟩
  refine ggCoxeterIso_of_injective_lift hC h α hα hP ?_ s hs
  by_cases hpn : p ∣ n + 1
  · have hn4 := ta_four_le hp hn hpn
    have hn1 : 1 ≤ n := by omega
    have hCz := ta_cast_eq e hC p
    refine ggCoxeterFaithful_of_radical (k := n - 1) hC hMW hp
      (fun i => ggCartanARad n p (e.symm i)) (e ⟨0, hn1⟩) ?_ ?_ ?_ ?_ (fun a => e ⟨a, by omega⟩)
      ?_ ?_ h α hα hP
    · simp [ggCartanARad]
    · intro i
      calc ∑ j, (C i j : ZMod p) * ggCartanARad n p (e.symm j)
          = ∑ j, ggCartanAMod n p (e.symm i) (e.symm j) * ggCartanARad n p (e.symm j) :=
            Finset.sum_congr rfl fun j _ => by rw [hCz]
        _ = ∑ j', ggCartanAMod n p (e.symm i) j' * ggCartanARad n p j' :=
            Equiv.sum_comp e.symm fun j' => ggCartanAMod n p (e.symm i) j' * ggCartanARad n p j'
        _ = 0 := ggCartanAMod_rad n p hpn _
    · intro x hx
      have hx' : ∀ i' : Fin n, ∑ j', ggCartanAMod n p i' j' * x (e j') = 0 := fun i' => by
        have h1 := hx (e i')
        rw [← Equiv.sum_comp e (fun j => (C (e i') j : ZMod p) * x j)] at h1
        simpa [hCz] using h1
      have h2 := ggCartanAMod_ker n p hn1 (fun j' => x (e j')) hx'
      funext j
      have h3 := congrFun h2 (e.symm j)
      simpa using h3
    · intro i j
      have h1 : Relation.ReflTransGen (fun a b => (C a b : ZMod p) ≠ 0) (e (e.symm i))
          (e (e.symm j)) :=
        Relation.ReflTransGen.lift (p := fun a b => (C a b : ZMod p) ≠ 0) e
          (fun a b hab => by
            show (C (e a) (e b) : ZMod p) ≠ 0
            rw [hCz]
            simpa using hab) _ _ (ggCartanAMod_conn n p (e.symm i) (e.symm j))
      simpa using h1
    · intro c hc
      refine ggCartanAMod_rows_indep n p c fun j' => ?_
      simpa [hCz] using hc (e j')
    · rw [Nat.card_congr ((CoxeterMatrix.A n).reindexGroupEquiv e).toEquiv, l05nK3a_card_coxeterA]
      exact ggNotDvd_factorial_of_typeA n p hp hpn hn4
  · exact ggCartanFaithfulInputFixed_holds p Fact.out hp Λ _ C hMW hC V h α hα hP
      (ta_independent e hC hpn h α hP)

end CFSG.StandardType

end
