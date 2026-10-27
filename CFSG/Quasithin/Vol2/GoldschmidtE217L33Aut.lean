module

public import CFSG.GH74.AS16.E2.OuterL33
public import CFSG.GH74.E2.K0Simple

public section

namespace CFSG.Quasithin

namespace E217R4

theorem eq_of_centralizes_sylow_L33
    {K : Type} [Group K] (hK : CFSG.GH74.E2.ShapeL33 K)
    (Q : Subgroup K) (hQ : IsPGroup 2 Q) (hQi : ¬ 2 ∣ Q.index) :
    ∃ s ∈ Q, orderOf s = 2 ∧ (∀ q ∈ Q, q * s = s * q) ∧
      ∀ α : MulAut K, α ^ 2 = 1 → α ≠ 1 → (∀ q ∈ Q, α q = q) → α = MulAut.conj s := by
  have hfacts := CFSG.GH74.E2.ShapeL33.facts hK
  have hcen : Subgroup.center K = ⊥ := by
    have := hfacts.1
    exact CFSG.GH74.E2.center_eq_bot_of_simple_of_not_prime hfacts.2.2
  obtain ⟨s, hsQ, hs1, hs2, hsc, hs4, hs5, -⟩ :=
    (CFSG.GH74.AS16.E2.outerSylowTable_L33 hK Q hQ hQi).exists_s
  refine ⟨s, hsQ, orderOf_eq_prime hs2 hs1, hsc, fun α hα2 hα1 hfix => ?_⟩
  obtain ⟨a, haQ, hac, hαa⟩ := hs5 α hfix
  have ha2 : a ^ 2 = 1 := by
    have h1 : (MulAut.conj (a ^ 2) : MulAut K) = 1 := by
      rw [map_pow, ← hαa]
      exact hα2
    have h2 : a ^ 2 ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun φ : MulAut K => φ g) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      calc g * a ^ 2 = (a ^ 2 * g * (a ^ 2)⁻¹) * a ^ 2 := by rw [this]
        _ = a ^ 2 * g := by group
    rwa [hcen, Subgroup.mem_bot] at h2
  rcases hs4 a haQ hac ha2 with rfl | rfl
  · exact absurd (hαa.trans (map_one _)) hα1
  · exact hαa

end E217R4

end CFSG.Quasithin
