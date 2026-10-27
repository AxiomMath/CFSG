module

public import CFSG.Quasithin.EmptyFaithful.S146P19
public import CFSG.Quasithin.EmptyFaithful.Der6AGen
public import CFSG.Quasithin.EmptyFaithful.SBc13ACComp
public import CFSG.Quasithin.Background.F9Comp

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Quasithin.F7

namespace SBc13

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {H₁ H₂ K₁ K₂ : Subgroup G} {s : G}

theorem gap3Pair_of_shapeOne (hset : Setup14615 T M H H₁ H₂ K₁ K₂ s)
    (hc₁ : K₁ ∈ cComp (mcOf T)) (hc₂ : K₂ ∈ cComp (mcOf T)) : Gap3Pair T K₁ K₂ := by
  intro x hx
  have hKz : mcOf T ≤ Subgroup.normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) := by
    rw [← hset.kz]
    exact le_normalizer_conjClosure _ _
  have hC : conjSub x K₂ ∈ cComp (mcOf T) := conjSub_mem_cComp_of_mem hc₂ hx
  have hle : conjSub x K₂ ≤ K₁ ⊔ K₂ :=
    calc conjSub x K₂ ≤ conjSub x (K₁ ⊔ K₂) := conjSub_mono x le_sup_right
      _ = K₁ ⊔ K₂ := conjSub_eq_of_mem_normalizer (hKz hx)
  rcases eq_or_eq_of_mem_cComp_of_le_sup hc₁ hc₂ hC hle with h | h
  · exact Or.inr h
  · exact Or.inl h

theorem gap3Theta_of_shapeOne (S : Setting146 G T M) (hset : Setup14615 T M H H₁ H₂ K₁ K₂ s)
    (hG : mcOf T = conjClosure (oTwoUpper H) (mcOf T) ⊔ T) : Gap3Theta T K₁ K₂ := by
  intro x hx hx5
  have hKzG : conjClosure (oTwoUpper H) (mcOf T) ≤ mcOf T := le_sup_left.trans hG.ge
  have hTG : T ≤ mcOf T := le_sup_right.trans hG.ge
  have hKzN : ((conjClosure (oTwoUpper H) (mcOf T)).subgroupOf (mcOf T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKzG).mpr (le_normalizer_conjClosure _ _)
  have hO : oTwoUpper (mcOf T) ≤ conjClosure (oTwoUpper H) (mcOf T) :=
    Der6A.oTwoUpper_le_of_normal_sup hKzG hKzN S.hyp.sylow.1 hTG hG.le
  rw [← hset.kz]
  exact hO (mem_oTwoUpper_of_odd hx (by rw [hx5]; decide))

end SBc13

end CFSG.Quasithin
