module

public import CFSG.Quasithin.Recognition.CertG2TwoOuter

public section

namespace CFSG.Quasithin

open CFSG.Sporadic.Bridge

namespace F6

namespace G22Perm

variable {k : Type} [Field k] (h2 : (2 : k) = 0) (hk2 : ∀ c : k, c = 0 ∨ c = 1)

@[expose] noncomputable def rhoPow
    (ε : Bool) : G2Group k := if ε then g2RhoC h2 else 1

@[expose] def piPow (ε : Bool) : Equiv.Perm (Fin 28) := if ε then u33Pi else 1

include hk2 in
theorem exists_rep
    (g : G2Group k) : ∃ (x : U33G) (ε : Bool), g = g2HomC h2 x * rhoPow h2 ε := by
  have D := g2IndexTwoData h2 hk2
  rcases D.cover g with ⟨x, hx⟩ | ⟨x, hx⟩
  · exact ⟨x, false, by rw [hx]; simp [rhoPow]⟩
  · refine ⟨x, true, ?_⟩
    simp only [rhoPow, ite_true]
    rw [hx, mul_assoc, D.sq, mul_one]

include hk2 in
theorem rep_unique
    {x y : U33G} {ε δ : Bool}
    (h : g2HomC h2 x * rhoPow h2 ε = g2HomC h2 y * rhoPow h2 δ) : x = y ∧ ε = δ := by
  have D := g2IndexTwoData h2 hk2
  have hρ : g2RhoC h2 ∉ (g2HomC h2).range := D.rho_not_mem
  cases ε <;> cases δ <;> simp only [rhoPow, Bool.false_eq_true, ite_false, ite_true,
    mul_one] at h
  · exact ⟨D.inj h, rfl⟩
  · exfalso
    apply hρ
    refine ⟨y⁻¹ * x, ?_⟩
    rw [map_mul, map_inv, h]
    group
  · exfalso
    apply hρ
    refine ⟨x⁻¹ * y, ?_⟩
    rw [map_mul, map_inv, ← h]
    group
  · exact ⟨D.inj (mul_right_cancel h), rfl⟩

@[expose] noncomputable def part
    (g : G2Group k) : U33G := (exists_rep h2 hk2 g).choose

@[expose] noncomputable def expo
    (g : G2Group k) : Bool := (exists_rep h2 hk2 g).choose_spec.choose

theorem part_spec
    (g : G2Group k) : g = g2HomC h2 (part h2 hk2 g) * rhoPow h2 (expo h2 hk2 g) :=
  (exists_rep h2 hk2 g).choose_spec.choose_spec

theorem part_rep
    (x : U33G) (ε : Bool) :
    part h2 hk2 (g2HomC h2 x * rhoPow h2 ε) = x ∧ expo h2 hk2 (g2HomC h2 x * rhoPow h2 ε) = ε := by
  have := rep_unique h2 hk2 (part_spec h2 hk2 (g2HomC h2 x * rhoPow h2 ε)).symm
  exact this

include hk2 in
theorem rho_mul
    (y : U33G) : g2RhoC h2 * g2HomC h2 y = g2HomC h2 (u33Phi' y) * g2RhoC h2 := by
  have C := (g2IndexTwoData h2 hk2).toIndexTwoCore
  rw [← C.conj y, mul_assoc, inv_mul_cancel, mul_one]

include hk2 in
theorem rep_mul
    (x y : U33G) (ε δ : Bool) :
    g2HomC h2 x * rhoPow h2 ε * (g2HomC h2 y * rhoPow h2 δ) =
      g2HomC h2 (x * (if ε then u33Phi' y else y)) * rhoPow h2 (xor ε δ) := by
  have D := g2IndexTwoData h2 hk2
  have hr := rho_mul h2 hk2 y
  cases ε <;> cases δ <;> simp only [rhoPow, Bool.false_eq_true, ite_false, ite_true, mul_one,
    Bool.xor_false, Bool.false_xor, Bool.xor_self, map_mul]
  · group
  · calc g2HomC h2 x * g2RhoC h2 * g2HomC h2 y = g2HomC h2 x * (g2RhoC h2 * g2HomC h2 y) := by
          group
      _ = g2HomC h2 x * g2HomC h2 (u33Phi' y) * g2RhoC h2 := by rw [hr]; group
  · calc g2HomC h2 x * g2RhoC h2 * (g2HomC h2 y * g2RhoC h2) =
          g2HomC h2 x * (g2RhoC h2 * g2HomC h2 y) * g2RhoC h2 := by group
      _ = g2HomC h2 x * g2HomC h2 (u33Phi' y) * (g2RhoC h2 * g2RhoC h2) := by rw [hr]; group
      _ = g2HomC h2 x * g2HomC h2 (u33Phi' y) := by rw [D.sq, mul_one]

@[expose] noncomputable def psiFun
    (g : G2Group k) : Equiv.Perm (Fin 28) :=
  u33PresHom (part h2 hk2 g) * piPow (expo h2 hk2 g)

theorem psiFun_rep
    (x : U33G) (ε : Bool) :
    psiFun h2 hk2 (g2HomC h2 x * rhoPow h2 ε) = u33PresHom x * piPow ε := by
  obtain ⟨h1, h2'⟩ := part_rep h2 hk2 x ε
  rw [psiFun, h1, h2']

@[expose] noncomputable def psi
    : G2Group k →* Equiv.Perm (Fin 28) where
  toFun := psiFun h2 hk2
  map_one' := by
    have h1 : (1 : G2Group k) = g2HomC h2 1 * rhoPow h2 false := by simp [rhoPow]
    rw [h1, psiFun_rep]
    simp [piPow]
  map_mul' g h := by
    rw [part_spec h2 hk2 g, part_spec h2 hk2 h, rep_mul h2 hk2, psiFun_rep, psiFun_rep,
      psiFun_rep]
    set x := part h2 hk2 g
    set y := part h2 hk2 h
    cases expo h2 hk2 g <;> cases expo h2 hk2 h <;>
      simp only [piPow, Bool.false_eq_true, ite_false, ite_true, mul_one, Bool.xor_false,
        Bool.false_xor, Bool.xor_self, map_mul, u33PresHom_phi']
    all_goals simp only [mul_assoc, u33Pi_sq, mul_one]

theorem psi_rep
    (x : U33G) (ε : Bool) :
    psi h2 hk2 (g2HomC h2 x * rhoPow h2 ε) = u33PresHom x * piPow ε :=
  psiFun_rep h2 hk2 x ε

theorem psi_f
    (x : U33G) : psi h2 hk2 (g2HomC h2 x) = u33PresHom x := by
  have := psi_rep h2 hk2 x false
  simpa [rhoPow, piPow] using this

theorem psi_rho
    : psi h2 hk2 (g2RhoC h2) = u33Pi := by
  have := psi_rep h2 hk2 1 true
  simpa [rhoPow, piPow] using this

theorem psi_injective
    : Function.Injective (psi h2 hk2) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker, part_spec h2 hk2 g, psi_rep] at hg
  rw [Subgroup.mem_bot, part_spec h2 hk2 g]
  cases hε : expo h2 hk2 g
  · rw [hε] at hg
    simp only [piPow, Bool.false_eq_true, ite_false, mul_one] at hg
    have := u33PresHom_injective (hg.trans (map_one _).symm)
    simp [this, rhoPow]
  · rw [hε] at hg
    simp only [piPow, ite_true] at hg
    exfalso
    apply u33Pi_not_mem
    change u33Pi ∈ Subgroup.closure _
    rw [← range_u33PresHom]
    refine ⟨(part h2 hk2 g)⁻¹, ?_⟩
    rw [map_inv]
    exact (eq_inv_of_mul_eq_one_right hg).symm

@[expose] noncomputable def sEl
    (i : ℕ) : G2Group k :=
  if i < 32 then g2HomC h2 (u33Tel u33GenPG i) else g2RhoC h2 * g2HomC h2 (u33Tel u33GenPG (i - 32))

theorem repL_psi_sEl
    (i : ℕ) (hi : i < 64) : RepL (u33XL i) (psi h2 hk2 (sEl h2 i)) := by
  have h1 := u33X_rep i hi
  have h3 : psi h2 hk2 (sEl h2 i) = u33XE i := by
    rw [sEl, u33XE]
    split_ifs
    · rw [psi_f, u33Tel_hom]
    · rw [map_mul, psi_rho, psi_f, u33Tel_hom]
  rw [h3]
  exact h1

end G22Perm

end F6

end CFSG.Quasithin
