module

public import CFSG.Quasithin.Background.GoldschmidtD35CoreSemi
public import CFSG.Quasithin.Background.GoldschmidtD35CoreCoord

public section

namespace CFSG.Quasithin.D35Core

variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V]

@[expose] def Generic (b : Module.Basis (Fin 3) F V) (w : V) : Prop :=
  b.repr w 0 ≠ 0 ∧ b.repr w 1 ≠ 0 ∧ b.repr w 2 ≠ 0 ∧ b.repr w 0 ≠ b.repr w 1 ∧
    b.repr w 0 ≠ b.repr w 2 ∧ b.repr w 1 ≠ b.repr w 2

theorem generic_of_indep (b : Module.Basis (Fin 3) F V) {w : V}
    (h01 : LinearIndependent F ![b 0, b 1, w]) (h02 : LinearIndependent F ![b 0, b 2, w])
    (h12 : LinearIndependent F ![b 1, b 2, w])
    (h0 : LinearIndependent F ![b 0, b 0 + b 1 + b 2, w])
    (h1 : LinearIndependent F ![b 1, b 0 + b 1 + b 2, w])
    (h2 : LinearIndependent F ![b 2, b 0 + b 1 + b 2, w]) : Generic b w := by
  obtain ⟨a, b', c⟩ := coord_ne_zero b h01 h02 h12
  obtain ⟨d, e, f⟩ := coord_ne_of_unit b h0 h1 h2
  exact ⟨a, b', c, d, e, f⟩

theorem exists_smul_semiPerm_of_generic [Finite F] (hF : Nat.card F = 4)
    (b : Module.Basis (Fin 3) F V) {σ : F ≃+* F} (hσ : ∀ x, σ x = x ^ 2) {w w' : V}
    (hw : Generic b w) (hw' : Generic b w') (hne : ∀ c : F, w' ≠ c • w) :
    ∃ c : F, c ≠ 0 ∧ semiPerm b σ w = c • w' := by
  obtain ⟨hw0, hw1, hw2, hw01, hw02, hw12⟩ := hw
  obtain ⟨hv0, hv1, hv2, hv01, hv02, hv12⟩ := hw'
  have e2 := sq_ratio hF hw0 hw1 hw2 hw01 hw02 hw12
  have e2' := sq_ratio hF hv0 hv1 hv2 hv01 hv02 hv12
  set a0 := b.repr w 0 with ha0
  set a1 := b.repr w 1 with ha1
  set a2 := b.repr w 2 with ha2
  set c0 := b.repr w' 0 with hc0
  set c1 := b.repr w' 1 with hc1
  set c2 := b.repr w' 2 with hc2
  set s := a1 / a0 with hs
  set s' := c1 / c0 with hs'
  have hs1 : s ≠ 1 := fun h => hw01 (by rw [hs, div_eq_one_iff_eq hw0] at h; exact h.symm)
  have hs'1 : s' ≠ 1 := fun h => hv01 (by rw [hs', div_eq_one_iff_eq hv0] at h; exact h.symm)
  have eq1 : a1 = a0 * s := by rw [hs]; field_simp
  have eq1' : c1 = c0 * s' := by rw [hs']; field_simp
  have hss' : s' ≠ s := by
    intro h
    apply hne (c0 / a0)
    apply b.repr.injective
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, map_smul, Finsupp.smul_apply, smul_eq_mul, ← ha0, ← hc0]
      field_simp
    · simp only [Fin.mk_one, map_smul, Finsupp.smul_apply, smul_eq_mul, ← ha1, ← hc1]
      rw [eq1', h, eq1]
      field_simp
    · simp only [Fin.reduceFinMk, map_smul, Finsupp.smul_apply, smul_eq_mul, ← ha2, ← hc2]
      rw [e2', h, e2]
      field_simp
  have hs's : s' = s ^ 2 :=
    (eq_or_eq_sq hF (div_ne_zero hw1 hw0) hs1 (div_ne_zero hv1 hv0) hs'1).resolve_left hss'
  refine ⟨a0 ^ 2 / c0, div_ne_zero (pow_ne_zero 2 hw0) hv0, ?_⟩
  apply b.repr.injective
  ext i
  fin_cases i
  · simp only [Fin.zero_eta, repr_semiPerm, hσ, map_smul, Finsupp.smul_apply, smul_eq_mul, ← ha0,
      ← hc0]
    field_simp
  · simp only [Fin.mk_one, repr_semiPerm, hσ, map_smul, Finsupp.smul_apply, smul_eq_mul, ← ha1,
      ← hc1]
    rw [eq1', hs's, eq1]
    field_simp
  · simp only [Fin.reduceFinMk, repr_semiPerm, hσ, map_smul, Finsupp.smul_apply, smul_eq_mul,
      ← ha2, ← hc2]
    rw [e2', hs's, e2]
    field_simp

end CFSG.Quasithin.D35Core
