module

public import CFSG.Quasithin.H13.GoldschmidtU43EMat4

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

namespace JWSetup

variable [Finite G] {z : G} (S : JWSetup z) (r : S.Rho)

theorem fixed_of_comm (n : ↥S.Ng) (m : ↥S.Mg) (hm : (n : G) * m = m * (n : G)) :
    (S.chiN r n).mulVec ((Equiv.ofBijective _ (evC_basis_bijective r)).symm m) =
      (Equiv.ofBijective _ (evC_basis_bijective r)).symm m := by
  set e := Equiv.ofBijective _ (evC_basis_bijective r) with he
  have h1 := S.chiN_rep r n (e.symm m)
  have h2 : S.conjM n n.2 (evC (basis r) (e.symm m)) = m := by
    have : evC (basis r) (e.symm m) = m := e.apply_symm_apply m
    rw [this]
    apply Subtype.ext
    show (n : G) * m * (n : G)⁻¹ = m
    rw [mul_inv_eq_iff_eq_mul]
    exact hm
  apply e.injective
  show evC (basis r) _ = evC (basis r) _
  rw [← h1, h2]
  exact (e.apply_symm_apply m).symm

theorem card_centralizer_le (n : ↥S.Ng) {k : ℕ}
    (h : Nat.card {v : Fin 4 → ZMod 3 // (S.chiN r n).mulVec v = v} ≤ k) :
    Nat.card {m : ↥S.Mg // (n : G) * m = m * (n : G)} ≤ k := by
  refine le_trans (Nat.card_le_card_of_injective
    (fun m => ⟨(Equiv.ofBijective _ (evC_basis_bijective r)).symm m.1,
      S.fixed_of_comm r n m.1 m.2⟩) ?_) h
  intro a b hab
  exact Subtype.ext ((Equiv.ofBijective _ (evC_basis_bijective r)).symm.injective
    (congrArg Subtype.val hab))

theorem card_centralizer2_le (n₁ n₂ : ↥S.Ng) {k : ℕ}
    (h : Nat.card {v : Fin 4 → ZMod 3 //
      (S.chiN r n₁).mulVec v = v ∧ (S.chiN r n₂).mulVec v = v} ≤ k) :
    Nat.card {m : ↥S.Mg // (n₁ : G) * m = m * (n₁ : G) ∧ (n₂ : G) * m = m * (n₂ : G)} ≤ k := by
  refine le_trans (Nat.card_le_card_of_injective
    (fun m => ⟨(Equiv.ofBijective _ (evC_basis_bijective r)).symm m.1,
      S.fixed_of_comm r n₁ m.1 m.2.1, S.fixed_of_comm r n₂ m.1 m.2.2⟩) ?_) h
  intro a b hab
  exact Subtype.ext ((Equiv.ofBijective _ (evC_basis_bijective r)).symm.injective
    (congrArg Subtype.val hab))

end JWSetup

end CFSG.Quasithin.H13.U43
