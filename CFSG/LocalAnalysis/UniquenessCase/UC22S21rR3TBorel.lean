module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3TBorelLie
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3TBorelA9

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22r3t_commutator_mem_T (D : Data G) (hB : ListBNonabelian) (h1930 : H1930 D)
    (hK3 : PartTwo.Inputs1719.K_BorelTorusAbelian) {K₁ : Subgroup G}
    (hK₁ : K₁ ∈ calL D.T D.M) {x y : G} (hx : x ∈ K₁) (hy : y ∈ K₁)
    (hxT : x ∈ normalizer (D.T : Set G)) (hyT : y ∈ normalizer (D.T : Set G)) {r : ℕ}
    (hr : r.Prime) (hr7 : 7 < r) {k : ℕ} (hyo : orderOf y = r ^ k) :
    x * y * x⁻¹ * y⁻¹ ∈ D.T := by
  obtain ⟨K, hK, hLK⟩ := hK₁.2.2.2
  have hlie : ∀ {t : CFSG.Open.StatedLieTag} {m n : ℕ},
      CFSG.Blueprint.LieModel (Bar2 K ⧸ Subgroup.center (Bar2 K)) t m 2 n →
        x * y * x⁻¹ * y⁻¹ ∈ D.T := fun hm =>
    uc22r3t_commutator_mem_T_of_isMulCommutative D hK₁
      (uc22r3t_isMulCommutative_of_lie D hK3 hK₁ hK hLK hm) hx hy hxT hyT
  rcases uc22p20p_S_on_listB D hB h1930 hK₁ hK hLK with
    ⟨t, m, n, -, hm⟩ | hm | hm | hm | hm | hm | hA
  all_goals first
    | exact hlie hm
    | exact uc22r3t_commutator_mem_T_of_mem_center D hK₁ hx hy
        (uc22r3t_mk_mem_center_of_alt9 D hK₁ hK hLK hA hy hr hr7 hyo)

end CFSG.LocalAnalysis.UniquenessCase.UC22
