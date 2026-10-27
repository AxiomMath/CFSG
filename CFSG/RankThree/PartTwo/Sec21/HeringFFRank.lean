module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.RankThreeEvenClassification.Helpers

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG.Open (IsElemAbelian IsTwoLocal evenRank)

theorem ff_card_le_of_normalizes {G : Type} [Group G] [Finite G] {V E : Subgroup G}
    (hV : V ≠ ⊥) (hV2 : IsPGroup 2 V) (hE : IsElemAbelian 3 E)
    (hEV : E ≤ Subgroup.normalizer (V : Set G)) : Nat.card E ≤ 3 ^ evenRank G := by
  have hEp : IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩
  obtain ⟨k, hk⟩ := hEp.exists_card_eq
  have hloc : IsTwoLocal (Subgroup.normalizer (V : Set G)) := ⟨V, hV, hV2, rfl⟩
  have h1 : k ≤ CFSG.Open.pRank 3 (Subgroup.normalizer (V : Set G)) :=
    le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three _)
      ⟨E, hEV, hE, hk⟩
  have h2 := CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank 3 Nat.prime_three
    (by norm_num) _ hloc
  rw [hk]
  exact Nat.pow_le_pow_right (by norm_num) (h1.trans h2)

theorem ff_false_of_two_nines {G : Type} [Group G] [Finite G] (hG : evenRank G = 3)
    {V E E' : Subgroup G} (hV : V ≠ ⊥) (hV2 : IsPGroup 2 V) (hE : IsElemAbelian 3 E)
    (hE9 : Nat.card E = 9) (hE' : IsElemAbelian 3 E') (hE'9 : Nat.card E' = 9)
    (hEV : E ≤ Subgroup.normalizer (V : Set G)) (hE'V : E' ≤ Subgroup.centralizer (V : Set G))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E', x * y = y * x) (hdisj : ∀ x ∈ E, x ∈ E' → x = 1) : False := by
  set φ : E × E' →* G := E.subtype.noncommCoprod E'.subtype (fun x y => hcomm x x.2 y y.2)
    with hφ
  have hφapp : ∀ p : E × E', φ p = (p.1 : G) * (p.2 : G) := fun p => rfl
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨x, y⟩ hxy
    rw [MonoidHom.mem_ker, hφapp] at hxy
    have hx : (x : G) = ((y : G))⁻¹ := eq_inv_of_mul_eq_one_left hxy
    have hx1 : (x : G) = 1 := hdisj x x.2 (by rw [hx]; exact E'.inv_mem y.2)
    have hy1 : (y : G) = 1 := by rw [hx1, one_mul] at hxy; exact hxy
    exact Subgroup.mem_bot.mpr (Prod.ext (Subtype.ext hx1) (Subtype.ext hy1))
  have hcard : Nat.card φ.range = 81 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod, hE9, hE'9]
  have hRab : IsElemAbelian 3 φ.range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun r hr => ?_⟩
    · obtain ⟨a, ha⟩ := a
      obtain ⟨b, hb⟩ := b
      obtain ⟨⟨x₁, y₁⟩, rfl⟩ := ha
      obtain ⟨⟨x₂, y₂⟩, rfl⟩ := hb
      apply Subtype.ext
      simp only [Subgroup.coe_mul, hφapp]
      have h1 : (x₁ : G) * x₂ = x₂ * x₁ := hE.1.is_comm.comm x₁ x₂ |> congrArg Subtype.val
      have h2 : (y₁ : G) * y₂ = y₂ * y₁ := hE'.1.is_comm.comm y₁ y₂ |> congrArg Subtype.val
      calc (x₁ : G) * y₁ * (x₂ * y₂) = x₁ * (y₁ * x₂) * y₂ := by simp only [mul_assoc]
        _ = x₁ * (x₂ * y₁) * y₂ := by rw [← hcomm x₂ x₂.2 y₁ y₁.2]
        _ = (x₁ * x₂) * (y₁ * y₂) := by simp only [mul_assoc]
        _ = (x₂ * x₁) * (y₂ * y₁) := by rw [h1, h2]
        _ = x₂ * (x₁ * y₂) * y₁ := by simp only [mul_assoc]
        _ = x₂ * (y₂ * x₁) * y₁ := by rw [hcomm x₁ x₁.2 y₂ y₂.2]
        _ = x₂ * y₂ * (x₁ * y₁) := by simp only [mul_assoc]
    · obtain ⟨⟨x, y⟩, rfl⟩ := hr
      rw [hφapp]
      have hxy : Commute (x : G) (y : G) := hcomm x x.2 y y.2
      rw [hxy.mul_pow, hE.2 x x.2, hE'.2 y y.2, one_mul]
  have hRN : φ.range ≤ Subgroup.normalizer (V : Set G) := by
    rintro _ ⟨⟨x, y⟩, rfl⟩
    rw [hφapp]
    exact Subgroup.mul_mem _ (hEV x.2) (Subgroup.centralizer_le_normalizer (V : Set G) (hE'V y.2))
  have h4 : 4 ≤ CFSG.Open.pRank 3 (Subgroup.normalizer (V : Set G)) :=
    le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three _)
      ⟨φ.range, hRN, hRab, by rw [hcard]; norm_num⟩
  have hloc : IsTwoLocal (Subgroup.normalizer (V : Set G)) := ⟨V, hV, hV2, rfl⟩
  have h5 := CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank 3 Nat.prime_three
    (by norm_num) _ hloc
  omega

end CFSG.RankThree.PartTwo.Sec21
