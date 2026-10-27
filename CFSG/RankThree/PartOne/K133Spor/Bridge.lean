module

public import CFSG.RankThree.PartOne.K133.InnerRed
public import CFSG.RankThree.PartOne.KS.Basic
public import CFSG.Walter.ReeOrder.JT.AuxGroup

public section

namespace CFSG.RankThree.PartOne.K133

open CFSG CFSG.ComponentClassification.OuterAutomorphisms

theorem goodRes_of_not_sq_dvd {p : ℕ} {X : Type} [Group X]
    (h : ¬ p ^ 2 ∣ Nat.card (MulAut X)) : GoodRes p X := by
  intro Ē hE hc _
  exfalso
  apply h
  have hd := Subgroup.card_subgroup_dvd_card Ē
  rw [hc] at hd
  exact (pow_dvd_pow p (by norm_num : 2 ≤ 3)).trans hd

theorem noConfig_of_centralizer_not_four_dvd {p : ℕ} {X : Type} [Group X] [Finite X]
    (h4 : ∀ D : Subgroup X, (∀ g ∈ D, g ^ p = 1) → Nat.card D = p ^ 2 →
      ¬ 4 ∣ Nat.card (Subgroup.centralizer (D : Set X)))
    (C : Subgroup X) (hC : IsElementaryAbelian p C) (hCc : Nat.card C = p ^ 2)
    (Kb : Subgroup X) (hKs : IsSimpleGroup Kb) (hKn : ∃ a b : Kb, a * b ≠ b * a) :
    ¬ ∀ c ∈ C, ∀ k ∈ Kb, c * k = k * c := by
  intro hcomm
  have hKle : Kb ≤ Subgroup.centralizer (C : Set X) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact hcomm d hd k hk
  have hsolC : Group.IsSolvable (Subgroup.centralizer (C : Set X)) :=
    CFSG.Walter.JT.isSolvable_of_not_four_dvd
      (h4 C (fun g hg => elemPow_eq_one_of_isElementaryAbelian g hg) hCc)
  have hsolK : Group.IsSolvable Kb :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKle)
  obtain ⟨a, b, hab⟩ := hKn
  exact hab ((IsSimpleGroup.comm_iff_isSolvable).2 hsolK a b)

theorem goodRes_of_centralizer_not_four_dvd {p : ℕ} (hp : p.Prime) {X : Type} [Group X] [Finite X]
    [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a) (hOut : ¬ p ∣ Nat.card (Outer X))
    (h4 : ∀ D : Subgroup X, (∀ g ∈ D, g ^ p = 1) → Nat.card D = p ^ 2 →
      ¬ 4 ∣ Nat.card (Subgroup.centralizer (D : Set X))) : GoodRes p X :=
  goodRes_of_inner_noConfig hp (CFSG.RankThree.PartOne.center_eq_bot_of_simple hnab)
    (fun _ hE => le_inner_of_isPGroup_of_not_dvd_outer hp hOut hE)
    (fun C hC hCc Kb hKs hKn _ => noConfig_of_centralizer_not_four_dvd h4 C hC hCc Kb hKs hKn)

end CFSG.RankThree.PartOne.K133
