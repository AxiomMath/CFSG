module

public import CFSG.RankThree.GF2n.Stroth80.Sec311Conj

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.conj_LB_eq_of_img_eq (hc : Ctx M Q Z B) {K : Type} [Field K] {γ : G → K}
    {M₀ : Tim79.QuadModel Q Z K γ} {m₁ m₂ : G} (hm₁ : m₁ ∈ M) (hm₂ : m₂ ∈ M)
    (hline : ∀ v, v ∈ M₀.img (conjSubgroup m₁ B) ↔ v ∈ M₀.img (conjSubgroup m₂ B)) :
    conjSubgroup m₁ (LB M Q B) = conjSubgroup m₂ (LB M Q B) := by
  have hle : ∀ {m₁ m₂ : G}, m₁ ∈ M → m₂ ∈ M →
      (∀ v, v ∈ M₀.img (conjSubgroup m₁ B) → v ∈ M₀.img (conjSubgroup m₂ B)) →
      conjSubgroup m₁ B ⊔ Z ≤ conjSubgroup m₂ B ⊔ Z := by
    intro m₁ m₂ hm₁ hm₂ hsub
    refine sup_le (fun x hx => ?_) le_sup_right
    have hxQ : x ∈ Q := (hc.conj_of_mem hm₁).le hx
    exact (M₀.mem_img_iff (le_sup_right : Z ≤ conjSubgroup m₂ B ⊔ Z) hxQ).mp
      (M₀.img_mono le_sup_left (hsub _ (M₀.pi_mem_img hx hxQ)))
  exact hc.conj_LB_eq_of_conj_BZ hm₁ hm₂ (le_antisymm
    (hle hm₁ hm₂ fun v hv => (hline v).mp hv) (hle hm₂ hm₁ fun v hv => (hline v).mpr hv))

end CFSG.RankThree.GF2n.Stroth80
