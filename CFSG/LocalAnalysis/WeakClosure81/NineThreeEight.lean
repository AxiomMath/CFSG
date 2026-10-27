module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreePRank

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}

@[expose] def weylD4 : Subgroup (Equiv.Perm (Fin 4 × Bool)) :=
  Subgroup.closure {σ | ∃ (i j : Fin 4) (b : Bool), i ≠ j ∧
    σ = Equiv.swap (i, false) (j, b) * Equiv.swap (i, true) (j, !b)}

@[expose] def nineDeltaPerm (V S : Subgroup G) :
    ↥(nineDeltaStab V S) →* Equiv.Perm ↥(nineDelta V S) where
  toFun l :=
    { toFun := fun B => ⟨conjSubgroup B.1 (l : G)⁻¹,
        (mem_nineDeltaStab.mp ((nineDeltaStab V S).inv_mem l.2) B.1).mp B.2⟩
      invFun := fun B => ⟨conjSubgroup B.1 (l : G), (mem_nineDeltaStab.mp l.2 B.1).mp B.2⟩
      left_inv := fun B => Subtype.ext (by
        show conjSubgroup (conjSubgroup B.1 (l : G)⁻¹) (l : G) = B.1
        rw [CFSG.Quasithin.conjSubgroup_conjSubgroup, inv_mul_cancel,
          CFSG.Quasithin.conjSubgroup_one])
      right_inv := fun B => Subtype.ext (by
        show conjSubgroup (conjSubgroup B.1 (l : G)) (l : G)⁻¹ = B.1
        rw [CFSG.Quasithin.conjSubgroup_conjSubgroup, mul_inv_cancel,
          CFSG.Quasithin.conjSubgroup_one]) }
  map_one' := Equiv.ext fun B => Subtype.ext (by
    show conjSubgroup B.1 ((1 : ↥(nineDeltaStab V S)) : G)⁻¹ = B.1
    rw [Subgroup.coe_one, inv_one, CFSG.Quasithin.conjSubgroup_one])
  map_mul' := fun l₁ l₂ => Equiv.ext fun B => Subtype.ext (by
    show conjSubgroup B.1 ((l₁ * l₂ : ↥(nineDeltaStab V S)) : G)⁻¹ =
      conjSubgroup (conjSubgroup B.1 (l₂ : G)⁻¹) (l₁ : G)⁻¹
    rw [CFSG.Quasithin.conjSubgroup_conjSubgroup, Subgroup.coe_mul, mul_inv_rev])

@[expose] def Nine3NGeOne (V S : Subgroup G) : Prop :=
  3 ≤ Nat.card ↥(nineDelta V S)

@[expose] def Nine3IW (V K S : Subgroup G) (g : G) : Prop :=
  nineI V K ⊓ nineW V S = nineI V K ⊓ nineW0 V K S g

namespace Nine3Choice

theorem card_nineDelta_eq_three_or_five (hc : Nine3Choice V T A K S X p g x)
    (hI : Nine3IFacts V K S) (h3 : 3 ≤ Nat.card ↥(nineDelta V S)) :
    Nat.card ↥(nineDelta V S) = 3 ∨ Nat.card ↥(nineDelta V S) = 5 := by
  have h5 := hc.card_nineDelta_le_five hI
  obtain ⟨n, -, hΔ⟩ := hc.core.card_nineOmegaIn
  rw [hΔ] at h3 h5 ⊢
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at h3
  have hn2 : n ≤ 2 := by
    by_contra hn
    push Not at hn
    have h8 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  interval_cases n <;> simp_all

theorem conjSubgroup_V_of_mem_nineD (hc : Nine3Choice V T A K S X p g x) {d : G}
    (hd : d ∈ nineD K A x) : conjSubgroup V d = V :=
  conjSubgroup_eq_iff_mem_normalizer.mpr
    (Subgroup.centralizer_le_normalizer _ (hc.core.nineD_le_centralizer hc.x_mem hd))

theorem nineD_transitive_delta (hc : Nine3Choice V T A K S X p g x) {B B' : Subgroup G}
    (hB : B ∈ nineDelta V S) (hB' : B' ∈ nineDelta V S) (hBV : B ≠ V) (hB'V : B' ≠ V) :
    ∃ d ∈ nineD K A x, conjSubgroup B d = B' := by
  obtain ⟨d, hd, hdB⟩ := hc.core.nineD_transitive hc.x_mem hc.x_ne_one
    ((hc.core.mem_nineDelta_iff.mp hB).resolve_left hBV)
    ((hc.core.mem_nineDelta_iff.mp hB').resolve_left hB'V)
  exact ⟨d, hd, hdB.symm⟩

end Nine3Choice

end CFSG.LocalAnalysis.WeakClosure81
