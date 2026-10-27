module

public import CFSG.Quasithin.Background.AutOnBasics

public section

namespace CFSG.Quasithin.AutOn

open CFSG.Open

variable {G : Type*} [Group G]

theorem card_autOn_mul {K V : Subgroup G} (hK : K ≤ Subgroup.normalizer (V : Set G)) :
    Nat.card (autOn K V) * Nat.card ↥(K ⊓ Subgroup.centralizer (V : Set G)) = Nat.card K := by
  set N := Subgroup.normalizer (V : Set G)
  have h1 : Nat.card (autOn K V) * Nat.card ↥((conjAct V).ker ⊓ K.subgroupOf N) =
      Nat.card (K.subgroupOf N) := by
    unfold autOn
    rw [← Subgroup.relIndex_ker, Subgroup.relIndex_mul_card]
  have h2 : Nat.card (K.subgroupOf N) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv
  have h3 : Nat.card ↥((conjAct V).ker ⊓ K.subgroupOf N) =
      Nat.card ↥(K ⊓ Subgroup.centralizer (V : Set G)) :=
    Nat.card_congr
      { toFun := fun x =>
          ⟨x.1.1, x.2.2, (conjAct_eq_one_iff (V := V) x.1).1 (MonoidHom.mem_ker.1 x.2.1)⟩
        invFun := fun y =>
          ⟨⟨(y : G), hK y.2.1⟩,
            MonoidHom.mem_ker.2 ((conjAct_eq_one_iff (V := V) ⟨(y : G), hK y.2.1⟩).2 y.2.2),
            y.2.1⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [h3, h2] at h1
  exact h1

end CFSG.Quasithin.AutOn
