module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitOrthEdge
import CFSG.LocalAnalysis.StandardType.GGWeylCartan

public section

namespace CFSG.StandardType

theorem ggSimplePair_conj_pivot {ι : Type} {M : CoxeterMatrix ι} {a b c : ι}
    (hab : M.M a b = 2) (hac : M.M a c = 2) (hbc : M.M b c = 3) :
    ∃ w : M.Group, w * M.simple a * w⁻¹ = M.simple a ∧ w * M.simple b * w⁻¹ = M.simple c := by
  refine ⟨M.simple b * M.simple c, mul_inv_eq_of_eq_mul ?_, mul_inv_eq_of_eq_mul ?_⟩
  · rw [mul_assoc, ← ggSimplyLaced_simple_comm hac, ← mul_assoc,
      ← ggSimplyLaced_simple_comm hab, mul_assoc]
  · rw [ggSimplyLaced_braid hbc, mul_assoc]

theorem ggSimplePair_conj_swap {ι : Type} {M : CoxeterMatrix ι} {a b x : ι}
    (hab : M.M a b = 2) (hax : M.M a x = 3) (hbx : M.M b x = 3) :
    ∃ w : M.Group, w * M.simple a * w⁻¹ = M.simple b ∧ w * M.simple b * w⁻¹ = M.simple a := by
  have r1 : ∀ r, M.simple a * (M.simple b * r) = M.simple b * (M.simple a * r) := fun r => by
    rw [← mul_assoc, ggSimplyLaced_simple_comm hab, mul_assoc]
  have r2 : ∀ r, M.simple a * (M.simple x * (M.simple a * r)) =
      M.simple x * (M.simple a * (M.simple x * r)) := fun r => by
    simp only [← mul_assoc, ggSimplyLaced_braid hax]
  have r3 : ∀ r, M.simple b * (M.simple x * (M.simple b * r)) =
      M.simple x * (M.simple b * (M.simple x * r)) := fun r => by
    simp only [← mul_assoc, ggSimplyLaced_braid hbx]
  refine ⟨M.simple x * M.simple a * M.simple b * M.simple x, mul_inv_eq_of_eq_mul ?_,
    mul_inv_eq_of_eq_mul ?_⟩
  · have h : ∀ r, M.simple x * (M.simple a * (M.simple b * (M.simple x * (M.simple a * r)))) =
        M.simple b * (M.simple x * (M.simple a * (M.simple b * (M.simple x * r)))) := fun r => by
      rw [r1, r2, ← r3, ← r1]
    simpa only [mul_one, mul_assoc] using h 1
  · have h : ∀ r, M.simple x * (M.simple a * (M.simple b * (M.simple x * (M.simple b * r)))) =
        M.simple a * (M.simple x * (M.simple a * (M.simple b * (M.simple x * r)))) := fun r => by
      rw [r3, ← r2]
    simpa only [mul_one, mul_assoc] using h 1

theorem ggSimplePair_conj_of_table {ι : Type} {M : CoxeterMatrix ι} {n : ℕ} (e : Fin n ≃ ι)
    (f : Fin n → Fin n → ℕ) (hf : ∀ x y, M.M (e x) (e y) = f x y) (a₀ b₀ : Fin n)
    (p q : Fin n → Fin n → Fin n) (rk : Fin n → Fin n → ℕ)
    (htab : ∀ a b, f a b = 2 → (a = a₀ ∧ b = b₀) ∨
      (f (p a b) (q a b) = 2 ∧ rk (p a b) (q a b) < rk a b ∧
        ((p a b = a ∧ f (q a b) b = 3) ∨ (q a b = b ∧ f (p a b) a = 3) ∨
          (p a b = b ∧ q a b = a ∧ ∃ x, f a x = 3 ∧ f b x = 3))))
    {a b : Fin n} (hab : f a b = 2) :
    ∃ w : M.Group, w * M.simple (e a₀) * w⁻¹ = M.simple (e a) ∧
      w * M.simple (e b₀) * w⁻¹ = M.simple (e b) := by
  suffices H : ∀ N a b, rk a b < N → f a b = 2 → ∃ w : M.Group,
      w * M.simple (e a₀) * w⁻¹ = M.simple (e a) ∧ w * M.simple (e b₀) * w⁻¹ = M.simple (e b) from
    H _ a b (Nat.lt_succ_self _) hab
  intro N
  induction N with
  | zero => exact fun a b h => absurd h (Nat.not_lt_zero _)
  | succ N ih =>
    intro a b hN hab
    rcases htab a b hab with ⟨rfl, rfl⟩ | ⟨h2, hlt, hmv⟩
    · exact ⟨1, by group, by group⟩
    · obtain ⟨w, hw₁, hw₂⟩ := ih _ _ (by omega) h2
      obtain ⟨v, hv₁, hv₂⟩ : ∃ v : M.Group, v * M.simple (e (p a b)) * v⁻¹ = M.simple (e a) ∧
          v * M.simple (e (q a b)) * v⁻¹ = M.simple (e b) := by
        rcases hmv with ⟨hp, h3⟩ | ⟨hq, h3⟩ | ⟨hp, hq, x, hax, hbx⟩
        · rw [hp] at h2 ⊢
          exact ggSimplePair_conj_pivot (by rw [hf, h2]) (by rw [hf, hab]) (by rw [hf, h3])
        · rw [hq] at h2 ⊢
          obtain ⟨v, hv₁, hv₂⟩ := ggSimplePair_conj_pivot (M := M) (a := e b) (b := e (p a b))
            (c := e a) (by rw [M.symmetric, hf, h2]) (by rw [M.symmetric, hf, hab])
            (by rw [hf, h3])
          exact ⟨v, hv₂, hv₁⟩
        · rw [hp, hq]
          exact ggSimplePair_conj_swap (x := e x) (by rw [M.symmetric, hf, hab])
            (by rw [hf, hbx]) (by rw [hf, hax])
      refine ⟨v * w, ?_, ?_⟩
      · rw [← hv₁, ← hw₁]
        group
      · rw [← hv₂, ← hw₂]
        group

theorem ggOrth_conj_of_simplePair {ι : Type} {M : CoxeterMatrix ι} (hW : GGIsWeylMatrix M)
    (h3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {a₀ b₀ : ι}
    (hconn : ∀ a b : ι, M.M a b = 2 → ∃ w : M.Group,
      w * M.simple a₀ * w⁻¹ = M.simple a ∧ w * M.simple b₀ * w⁻¹ = M.simple b)
    {t t' : M.Group} (ht : ∃ (w : M.Group) (i : ι), t = w * M.simple i * w⁻¹)
    (ht' : ∃ (w : M.Group) (i : ι), t' = w * M.simple i * w⁻¹) (hne : t ≠ t')
    (hcomm : t * t' = t' * t) {i j : ι} (h2 : M.M i j = 2) :
    ∃ w : M.Group, w * M.simple i * w⁻¹ = t ∧ w * M.simple j * w⁻¹ = t' := by
  haveI : Finite ι := ggIsWeylMatrix_finite hW
  haveI : Fintype ι := Fintype.ofFinite ι
  classical
  obtain ⟨C, hC, -, rfl⟩ := ggWeylCartan hW h3
  obtain ⟨a, b, w, hab, hwa, hwb⟩ :=
    ggOrth_edge hC (ggSimplyLacedConnected_of_weyl hW h3).1 ht ht' hne hcomm
  obtain ⟨u, hua, hub⟩ := hconn a b hab
  obtain ⟨v, hvi, hvj⟩ := hconn i j h2
  refine ⟨w * u * v⁻¹, ?_, ?_⟩
  · rw [← hwa, ← hua, ← hvi]
    group
  · rw [← hwb, ← hub, ← hvj]
    group

end CFSG.StandardType

end
