module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80U3Par
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80U3Cen
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80Levi

public section

namespace CFSG.Quasithin.E2P.Asc80

open CFSG.Quasithin.A312U3 CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

variable {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [Finite F]

theorem inf_M_eq_of_u3 (hirr : SU3OddIrr) (hp2 : p ≠ 2) (hF : Nat.card F = p ^ 2)
    (h3 : p = 3 → ∀ {Y : Subgroup (SU3F p F)}, leviU hF ≤ Y → Odd Y.index →
      IsIrrIn (StatedSU 3 (p ^ 1) F) Y → ¬ Group.IsSolvable ↥Y)
    {X : Type} [Group X] [Finite X] {K T M : Subgroup X} (hX : ASHyp K T M)
    (e : ↥K ≃* PSU3F p F) :
    M ⊓ K = K ⊓ Subgroup.centralizer (zOf (T ⊓ K) : Set X) := by
  obtain ⟨U, c, d, hU, hUB, hQ, hc, hd⟩ := exists_special_sylow_u hp2 hF
  have hB := centralizer_zOf_eq_leviCU hp2 hF hU hUB
  refine hX.inf_M_eq_of_levi e hU ?_ ?_
  · rw [hB]
    exact leviCU_ne_top hp2 hF
  · intro Y hBY hY
    rw [hB] at hBY ⊢
    exact le_leviCU_of_ne_top hirr hp2 hF h3 hBY hY

end CFSG.Quasithin.E2P.Asc80
