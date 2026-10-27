module

public import CFSG.Monster.B.E6.FieldInvF4Star
public import CFSG.Monster.B.E6.StandardSimple
public import CFSG.LieType.Chevalley.E6GraphInnerCosetExhaustion

public noncomputable section

namespace CFSG.Monster.B.E6.FieldInvF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Overlap CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open CFSG.Monster.B.E6.StdF4 CFSG.Monster.B.E6.StdF4Radical

theorem inl_mul_betaStarElt
    (a : stdGroup) :
    (SemidirectProduct.inl a * betaStarElt : GStar) = ⟨a, betaElt'⟩ :=
  SemidirectProduct.ext (by simp) (by simp)

theorem sq_inl_mul_betaStarElt
    (a : stdGroup) :
    (SemidirectProduct.inl a * betaStarElt : GStar) ^ 2 = SemidirectProduct.inl (a * betaG a) := by
  rw [pow_two, inl_mul_betaStarElt]
  exact SemidirectProduct.ext (by simp) (by simp [betaElt'_mul_self])

theorem sq_mul_diagE6GL
    (a : stdGroup) :
    ((a : ModGL Tag.E6 K) * diagE6GL) ^ 2 = (a : ModGL Tag.E6 K) * betaGL (a : ModGL Tag.E6 K) := by
  rw [← diagE6GL_conj_eq_betaGL a.2, pow_two]
  calc (a : ModGL Tag.E6 K) * diagE6GL * ((a : ModGL Tag.E6 K) * diagE6GL) =
        (a : ModGL Tag.E6 K) * (diagE6GL * a * diagE6GL⁻¹) * (diagE6GL * diagE6GL) := by group
    _ = _ := by rw [diagE6GL_mul_self, mul_one]

theorem sq_eq_one_iff
    (a : stdGroup) :
    (SemidirectProduct.inl a * betaStarElt : GStar) ^ 2 = 1 ↔
      ((a : ModGL Tag.E6 K) * diagE6GL) ^ 2 = 1 := by
  rw [sq_inl_mul_betaStarElt, sq_mul_diagE6GL,
    map_eq_one_iff _ (SemidirectProduct.inl_injective (φ := betaGroup.subtype)), ← coe_betaG_apply,
    ← Subgroup.coe_mul, OneMemClass.coe_eq_one]

theorem conj_inl_mul_betaStarElt
    (g a : stdGroup) :
    SemidirectProduct.inl g * (SemidirectProduct.inl a * betaStarElt) *
        (SemidirectProduct.inl g)⁻¹ =
      (SemidirectProduct.inl (g * a * (betaG g)⁻¹) * betaStarElt : GStar) := by
  rw [inl_mul_betaStarElt, inl_mul_betaStarElt]
  exact SemidirectProduct.ext (by simp [mul_assoc]) (by simp)

theorem conj_mul_diagE6GL
    (g a : stdGroup) :
    (g : ModGL Tag.E6 K) * ((a : ModGL Tag.E6 K) * diagE6GL) * (g : ModGL Tag.E6 K)⁻¹ =
      ((g * a * (betaG g)⁻¹ : stdGroup) : ModGL Tag.E6 K) * diagE6GL := by
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_betaG_apply,
    ← diagE6GL_conj_eq_betaGL g.2]
  group

theorem exists_conj_of_sq_eq_one
    {a : stdGroup}
    (ha : (SemidirectProduct.inl a * betaStarElt : GStar) ^ 2 = 1) :
    (∃ g : stdGroup, SemidirectProduct.inl g * (SemidirectProduct.inl a * betaStarElt) *
        (SemidirectProduct.inl g)⁻¹ = betaStarElt) ∨
      ∃ g : stdGroup, SemidirectProduct.inl g * (SemidirectProduct.inl a * betaStarElt) *
        (SemidirectProduct.inl g)⁻¹ = tStar := by
  obtain ⟨-, -, -, -, hex, -⟩ := (even_E6_graph_inner_coset_exhaustion 1 le_rfl (ZMod 2) K
    (by simp) CFSG.Monster.B.E6.card_K barHom CFSG.Monster.B.E6.barHom_eq_pow).2
  rcases hex (a : ModGL Tag.E6 K) a.2 ((sq_eq_one_iff a).mp ha) with ⟨g, hg, he⟩ | ⟨g, hg, he⟩
  · refine Or.inl ⟨⟨g, hg⟩, ?_⟩
    have h1 : ((⟨g, hg⟩ * a * (betaG ⟨g, hg⟩)⁻¹ : stdGroup) : ModGL Tag.E6 K) * diagE6GL =
        1 * diagE6GL := ((conj_mul_diagE6GL ⟨g, hg⟩ a).symm.trans he).trans (one_mul _).symm
    have h2 : (⟨g, hg⟩ * a * (betaG ⟨g, hg⟩)⁻¹ : stdGroup) = 1 :=
      Subtype.ext (mul_right_cancel h1)
    rw [conj_inl_mul_betaStarElt, h2, map_one, one_mul]
  · refine Or.inr ⟨⟨g, hg⟩, ?_⟩
    have h1 : ((⟨g, hg⟩ * a * (betaG ⟨g, hg⟩)⁻¹ : stdGroup) : ModGL Tag.E6 K) * diagE6GL =
        rootInvM * diagE6GL := (conj_mul_diagE6GL ⟨g, hg⟩ a).symm.trans he
    have h2 : (⟨g, hg⟩ * a * (betaG ⟨g, hg⟩)⁻¹ : stdGroup) = rootInv :=
      Subtype.ext (mul_right_cancel h1)
    rw [conj_inl_mul_betaStarElt, h2]
    rfl

end CFSG.Monster.B.E6.FieldInvF4
