module

public import CFSG.Quasithin.Vol2.Ch11SecB414ML
public import CFSG.Quasithin.Vol2.Ch11SecB414MM

public section

namespace CFSG.Quasithin.H13.Ch4.B414.M

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Quasithin CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
open CFSG.Assembly.LowTwoRank (StatedSL)
open Matrix

variable {F : Type} [Field F] [Finite F] [CharP F 2] {G : Type} [Group G]
  {Γ V Z L X : Subgroup G} {k : ℕ} {α : ↥Γ →* PGL3 F} (m : Model Γ V Z F k α)

theorem Model.min_scalar_diag (hF : Nat.card F = 4) {W W' : AddSubgroup (Matrix (Fin 3) (Fin 3) F)}
    {d : Fin 3 → F} (hdec : ∀ M ∈ W', ∃ t : F, M - t • diagonal d ∈ W)
    (hWdg : ∀ c : Fˣ, ∀ M ∈ W, twAdj k (dgHom c) M ∈ W) {γx : ↥Γ} {c : Fˣ}
    (hγx : α γx = ProjGenLinGroup.mk (dgHom c)) (hck : (c : F) ^ k ≠ 1) {J : Subgroup G}
    (h1 : m.pre W ≤ J) (h2 : J ≤ m.pre W') (hyJ : (γx : G) ∈ Subgroup.normalizer (J : Set G)) :
    J = m.pre W ∨ J = m.pre W' := by
  have hyV : ∀ s ∈ V, (γx : G) * s * (γx : G)⁻¹ ∈ V := fun s hs =>
    (Subgroup.mem_normalizer_iff.mp (m.normV γx.2) s).mp hs
  refine m.eq_or_eq_of_scalar hF hdec hyV (pow_ne_zero _ c.ne_zero) hck
    (fun s hs _ t hst => ?_) h1 h2 hyJ
  rw [m.act γx ⟨s, hs⟩ ⟨_, hyV s hs⟩ rfl (dgHom c) hγx.symm]
  have e : twAdj k (dgHom c) (Multiplicative.toAdd (m.β ⟨s, hs⟩)) - ((c : F) ^ k * t) • diagonal d =
      twAdj k (dgHom c) (Multiplicative.toAdd (m.β ⟨s, hs⟩) - t • diagonal d) := by
    rw [twAdj_sub, twAdj_smul, twAdj_dg_diagonal, smul_smul, mul_comm t]
  rw [e]
  exact hWdg c _ hst

omit [Finite F] [CharP F 2] in
theorem pow_ne_one_of_lt_three {c : F} (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) {k : ℕ} (hk3 : k < 3)
    (hk0 : k ≠ 0) : c ^ k ≠ 1 := by
  interval_cases k
  · exact absurd rfl hk0
  · rwa [pow_one]
  · intro h
    apply hc1
    calc c = c ^ 3 * (c ^ 2)⁻¹ := by
          rw [h, inv_one, mul_one, pow_succ, h, one_mul]
      _ = 1 := by rw [hc3, h, inv_one, mul_one]

end CFSG.Quasithin.H13.Ch4.B414.M
