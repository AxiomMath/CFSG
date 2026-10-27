module

public import CFSG.Quasithin.H13.A6Statements
public import CFSG.Quasithin.H13.ModelsSymplectic
public import CFSG.Quasithin.Recognition.ProductDisconnectedFusion

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

theorem isSimpleGroup_of_lieModel_psp {X : Type} [Group X] {n p f : ℕ} (hn : n ≠ 0)
    (h : LieModel X .PSp n p f) : IsSimpleGroup X := by
  rcases h with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp X n p f h
  all_goals exact absurd h hn

theorem exists_ne_mul_comm_of_isSimpleGroup {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hX : ¬ (Nat.card X).Prime) : ∃ a b : X, a * b ≠ b * a := by
  by_contra hcomm
  have hc : ∀ a b : X, a * b = b * a := fun a b => by
    by_contra h
    exact hcomm ⟨a, b, h⟩
  let _ : CommGroup X := { (inferInstance : Group X) with mul_comm := hc }
  exact hX (IsSimpleGroup.prime_card (α := X))

theorem card_of_lieModel_sp62 {X : Type} [Group X] (h : LieModel X .PSp 3 2 1) :
    Nat.card X = 1451520 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_symplecticGroup_of_lieModel h
  rw [Nat.card_congr e.toEquiv, card_symplecticGroup_three_two]

theorem lieModel_psp_of_c3System
    (hI51 : StmtI_5_1) {G : Type} [Group G] [Finite G]
    (hs : IsSimpleGroup G) (hna : ∃ a b : G, a * b ≠ b * a) (Es : Fin 3 → Subgroup G)
    (hD : IsDSystem .C3 fun i => (Es i).subgroupOf (Es 0 ⊔ Es 1 ⊔ Es 2)) {d : G}
    (hd : orderOf d = 2) (hCd : Subgroup.centralizer ({d} : Set G) ≤ Es 0 ⊔ Es 1 ⊔ Es 2)
    (hfus : ∀ a ∈ Es 0 ⊔ Es 1 ⊔ Es 2, ∀ b ∈ Es 0 ⊔ Es 1 ⊔ Es 2, orderOf a = 2 → IsConj a b →
      ∃ e ∈ Es 0 ⊔ Es 1 ⊔ Es 2, e * a * e⁻¹ = b)
    (hprod : ∀ e : G, IsConj d e → d * e = e * d → e ≠ d →
      Subgroup.centralizer ({d * e} : Set G) ≤ Es 0 ⊔ Es 1 ⊔ Es 2) :
    LieModel G .PSp 3 2 1 := by
  have hLE : LieModel ↥(Es 0 ⊔ Es 1 ⊔ Es 2) .PSp 3 2 1 := (hI51 _ .C3 _ hD).2 rfl
  have hEs : IsSimpleGroup ↥(Es 0 ⊔ Es 1 ⊔ Es 2) := isSimpleGroup_of_lieModel_psp (by norm_num) hLE
  have hEna : ∃ a b : ↥(Es 0 ⊔ Es 1 ⊔ Es 2), a * b ≠ b * a :=
    exists_ne_mul_comm_of_isSimpleGroup (by rw [card_of_lieModel_sp62 hLE]; norm_num)
  have htop := CFSG.Quasithin.Recognition.eq_top_of_fusion hs hna hEs hEna hd hCd hfus hprod
  obtain ⟨φ⟩ := nonempty_mulEquiv_symplecticGroup_of_lieModel hLE
  exact lieModel_of_mulEquiv_symplecticGroup
    ((Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm)).trans φ)

end CFSG.Quasithin.H13.A6
