module

public import CFSG.RankThree.PartTwo.Sec21.FF81S59D8
public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.S59

open CFSG.RankThree.PartTwo.Sec21.FF79

section Mod

variable {G : Type} [Group G] [Finite G] {T : Subgroup G} {γ : G}

theorem card_sq_fixed_modEq (hγ7 : γ ^ 7 = 1) (hγT : γ ∈ Nor T) :
    Nat.card {u : G // u ∈ T ∧ u ^ 2 = 1} ≡
      Nat.card {v : G // v ∈ T ⊓ Cen γ ∧ v ^ 2 = 1} [MOD 7] := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : Fintype G := Fintype.ofFinite G
  have hγinv : γ⁻¹ ∈ Nor T := Subgroup.inv_mem _ hγT
  have hmem : ∀ {g : G}, g ∈ Nor T → ∀ u : {u : G // u ∈ T ∧ u ^ 2 = 1},
      g * (u : G) * g⁻¹ ∈ T ∧ (g * (u : G) * g⁻¹) ^ 2 = 1 := by
    intro g hg u
    refine ⟨(Subgroup.mem_normalizer_iff.mp hg u).mp u.2.1, ?_⟩
    rw [conj_pow, u.2.2, mul_one, mul_inv_cancel]
  let σ : Equiv.Perm {u : G // u ∈ T ∧ u ^ 2 = 1} :=
    { toFun := fun u => ⟨γ * (u : G) * γ⁻¹, hmem hγT u⟩
      invFun := fun u => ⟨γ⁻¹ * (u : G) * γ⁻¹⁻¹, by simpa using hmem hγinv u⟩
      left_inv := fun u => Subtype.ext (by simp [mul_assoc])
      right_inv := fun u => Subtype.ext (by simp [mul_assoc]) }
  have hσn : ∀ (n : ℕ) (u : {u : G // u ∈ T ∧ u ^ 2 = 1}),
      ((σ ^ n) u : G) = γ ^ n * (u : G) * (γ ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro u; simp
    | succ n ih =>
      intro u
      rw [pow_succ, Equiv.Perm.mul_apply, ih]
      show γ ^ n * (γ * (u : G) * γ⁻¹) * (γ ^ n)⁻¹ = γ ^ (n + 1) * (u : G) * (γ ^ (n + 1))⁻¹
      rw [pow_succ', mul_inv_rev]
      group
  have hσ : σ ^ 7 = 1 := by
    ext u
    rw [hσn, hγ7]
    simp
  have hcm := Equiv.Perm.card_compl_support_modEq (p := 7) (n := 1) (σ := σ) (by simpa using hσ)
  have hsup : σ.supportᶜ.card = Nat.card {v : G // v ∈ T ⊓ Cen γ ∧ v ^ 2 = 1} := by
    have hcard : Nat.card {v : G // v ∈ T ⊓ Cen γ ∧ v ^ 2 = 1} =
        Nat.card {u : {u : G // u ∈ T ∧ u ^ 2 = 1} // σ u = u} :=
      Nat.card_congr
        { toFun := fun v => ⟨⟨v.1, v.2.1.1, v.2.2⟩, Subtype.ext (by
            have h1 := Subgroup.mem_centralizer_singleton_iff.mp v.2.1.2
            show γ * (v : G) * γ⁻¹ = v
            rw [mul_inv_eq_iff_eq_mul]
            exact h1.symm)⟩
          invFun := fun u => ⟨(u.1 : G), ⟨u.1.2.1, Subgroup.mem_centralizer_singleton_iff.mpr (by
            have h1 : γ * (u.1 : G) * γ⁻¹ = u.1 := congrArg Subtype.val u.2
            rw [mul_inv_eq_iff_eq_mul] at h1
            exact h1.symm)⟩, u.1.2.2⟩
          left_inv := fun v => rfl
          right_inv := fun u => rfl }
    rw [hcard, Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext u
    simp [Equiv.Perm.mem_support]
  rw [hsup, ← Nat.card_eq_fintype_card] at hcm
  exact hcm.symm

theorem nonempty_mulEquiv_D8 (hγ7 : γ ^ 7 = 1) (hγT : γ ∈ Nor T)
    (hN : Nat.card {u : G // u ∈ T ∧ u ^ 2 = 1} = 17408) (hV : Nat.card ↥(T ⊓ Cen γ) = 8) :
    Nonempty (↥(T ⊓ Cen γ) ≃* DihedralGroup 4) := by
  have hmod := card_sq_fixed_modEq hγ7 hγT
  rw [hN] at hmod
  have hequiv : {v : G // v ∈ T ⊓ Cen γ ∧ v ^ 2 = 1} ≃ {v : ↥(T ⊓ Cen γ) // v ^ 2 = 1} :=
    { toFun := fun v => ⟨⟨v.1, v.2.1⟩, Subtype.ext (by simpa using v.2.2)⟩
      invFun := fun v => ⟨v.1.1, v.1.2, by simpa using congrArg Subtype.val v.2⟩
      left_inv := fun v => rfl
      right_inv := fun v => rfl }
  have hle : Nat.card {v : ↥(T ⊓ Cen γ) // v ^ 2 = 1} ≤ 8 := by
    rw [← hV]
    exact Nat.card_le_card_of_injective _ Subtype.val_injective
  have hpos : 0 < Nat.card {v : ↥(T ⊓ Cen γ) // v ^ 2 = 1} := by
    haveI : Nonempty {v : ↥(T ⊓ Cen γ) // v ^ 2 = 1} := ⟨⟨1, one_pow 2⟩⟩
    exact Nat.card_pos
  rw [Nat.card_congr hequiv] at hmod
  have h6 : Nat.card {v : ↥(T ⊓ Cen γ) // v ^ 2 = 1} = 6 := by
    unfold Nat.ModEq at hmod
    omega
  exact nonempty_mulEquiv_dihedral_four hV h6

end Mod

end CFSG.RankThree.PartTwo.Sec21.FF81.S59
