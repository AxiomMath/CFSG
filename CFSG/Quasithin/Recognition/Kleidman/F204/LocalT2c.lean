module

public import CFSG.Quasithin.EmptyFaithful.SzF53BasA
public import CFSG.Quasithin.Recognition.GoldschmidtF112FA5Transv

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.FA5 CFSG.Quasithin.F53 CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

omit [Finite G] in
theorem exists_geodesic {H M : Subgroup G} :
    ∀ (b : ℕ) (α α' : Geo H M), dist α α' = b →
      ∃ p : ℕ → Geo H M, p 0 = α ∧ p b = α' ∧ (∀ k, k < b → (graph _ H M).Adj (p k) (p (k + 1))) ∧
        ∀ k, k ≤ b → dist α (p k) = k := by
  intro b
  induction b with
  | zero =>
    intro α α' h
    have : α = α' := (CosetGeom.dist_eq_zero_iff rfl).mp h
    refine ⟨fun _ => α, rfl, this, fun k hk => absurd hk (by omega), fun k hk => ?_⟩
    have : k = 0 := by omega
    subst this; exact CosetGeom.dist_self α
  | succ b ih =>
    intro α α' h
    obtain ⟨β, hβ, hβd⟩ := exists_adj_dist_eq rfl (α := α) (δ := α') (d := b) h
    obtain ⟨p, hp0, hpb, hpadj, hpd⟩ := ih α β hβd
    refine ⟨fun k => if k ≤ b then p k else α', by simpa using hp0, by simp, fun k hk => ?_, fun k hk => ?_⟩
    · by_cases hk' : k < b
      · simp only [ite_eq_left hk'.le, ite_eq_left (Nat.succ_le_of_lt hk')]
        exact hpadj k hk'
      · have : k = b := by omega
        subst this
        simp only [le_refl, ite_true, show ¬ (k + 1 ≤ k) by omega, ite_false]
        rw [hpb]; exact hβ.symm
    · by_cases hk' : k ≤ b
      · simp only [ite_eq_left hk']; exact hpd k hk'
      · have : k = b + 1 := by omega
        subst this
        simp only [show ¬ (b + 1 ≤ b) by omega, ite_false]; exact h

omit [Finite G] in
theorem vtype_path {H M : Subgroup G} (p : ℕ → Geo H M) {b : ℕ} (hp0 : vtype (p 0) = false)
    (hadj : ∀ k, k < b → (graph _ H M).Adj (p k) (p (k + 1))) :
    ∀ k, k ≤ b → (vtype (p k) = true ↔ k % 2 = 1) := by
  intro k
  induction k with
  | zero => intro _; rw [hp0]; simp
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    have h2 := vtype_ne_of_adj (hadj k (by omega))
    cases hv : vtype (p (k + 1)) <;> cases hv' : vtype (p k) <;> simp_all <;> omega

end CFSG.Quasithin.Kleidman.F204
