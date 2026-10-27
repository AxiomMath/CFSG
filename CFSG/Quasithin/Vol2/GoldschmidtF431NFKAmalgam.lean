module

public import CFSG.Quasithin.Vol2.GoldschmidtF431NFKDef
public import CFSG.Quasithin.Recognition.F4Local

public section

namespace CFSG.Quasithin.H13.F431.NF

open CFSG.Quasithin CFSG.QuasithinUnique

theorem NFK.not_isConj_amalgam {Mb : Type*} [Group Mb] {G : Type*} [Group G] [Finite G]
    {T Q Z X Y M1 M2 : Subgroup Mb} {z v nr na : Mb} {q n : ℕ} {b1 : ↥M1 →* G}
    {b2 : ↥M2 →* G} (C : F431Comp M1 M2 b1 b2) (D : NFK T Q Z X Y M1 M2 z v nr na q n)
    (hsyl : IsSylowTwoOf ((T.subgroupOf M1).map b1) ⊤)
    (hcent : ∀ x ∈ (Z.subgroupOf M1).map b1, x ≠ 1 →
      Subgroup.centralizer ({x} : Set G) ≤ b1.range) :
    ¬ IsConj (amalgamMap b1 b2 z) (amalgamMap b1 b2 v) := by
  rw [amalgamMap_of_mem₁ b1 b2 D.z_mem₁, amalgamMap_of_mem₁ b1 b2 D.v_mem₁]
  exact D.not_isConj_img C.inj₁ C.agree hsyl hcent

end CFSG.Quasithin.H13.F431.NF
