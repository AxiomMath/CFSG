module

public import CFSG.RankThree.GF2n.Smith81.S81BA5Uni
public import CFSG.LinearAlgebra.SchurElemAbelianTwo
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKLift
import CFSG.CGT.Timmesfeld75.ListWCLinPSL
public import CFSG.RankThree.GF2n.Smith81.OrthSetup
public import CFSG.RankThree.GF2n.Smith81.S81BNF

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.Open CFSG.CGT.Timmesfeld75 CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
  CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom CFSG.RankThree.GF2n.Smith81.A5Cube

variable {G : Type} [Group G]

theorem card_le_pow_nine_of_isElemAbelian_statedProj {K : Type} [Field K] [Finite K] [CharP K 2]
    {E : Subgroup (StatedProj (StatedSL 6 K))} (hE : IsElemAbelian 2 E) :
    Nat.card E ≤ Nat.card K ^ 9 := by
  obtain ⟨E₁, hE₁, hcard⟩ := CFSG.QuasithinUnique.Lin2.exists_isElemAbelian_lift
    ((StatedScalars (Fin 6) K).subgroupOf (StatedSL 6 K))
    (CFSG.CGT.Timmesfeld75.odd_card_statedScalars (by norm_num)) hE
  have hE₂ : IsElemAbelian 2 (E₁.map (StatedSL 6 K).subtype) := hE₁.map _
  have h := CFSG.LinearAlgebra.SchurElemAbelianTwo.card_le_pow_of_isElemAbelian_two hE₂
  rw [Subgroup.card_map_of_injective (StatedSL 6 K).subtype_injective, hcard] at h
  simpa using h

theorem elemBoundE3L_of_uniform
    (hFE1 : Smith24E3LUniformStatement) : ElemBoundE3LStatement := by
  intro G _ _ M Q Z B IH hc h3L _ n hw A hAS hAel
  have hw10 : Width Q Z 10 := by
    obtain ⟨t, -, h⟩ := h3L
    exact h.1
  have hn : n = 10 := width_unique hc.ctx.hyp hw hw10
  subst hn
  obtain ⟨K, _, _, _, γ, M₀, hg⟩ := stroth_globalModelData hc.ctx.hyp
  obtain ⟨ψ, φ, d⟩ := hFE1 G M Q Z B IH hc.toRemCfg h3L K γ M₀ hg
  have hLM : Lgen M (LB M Q B) ≤ M := iSup₂_le fun m hm => by
    calc conjSubgroup m (LB M Q B) ≤ conjSubgroup m M := Subgroup.map_mono hc.ctx.LB_le_M
      _ = M := hc.ctx.conj_M_eq hm
  set θ : ↥(Lgen M (LB M Q B)) →* ↥M ⧸ Q.subgroupOf M :=
    (QuotientGroup.mk' (Q.subgroupOf M)).comp (Subgroup.inclusion hLM) with hθ
  have hker : θ.ker = φ.ker := by
    ext s
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, d.ker s, hθ, MonoidHom.comp_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rfl
  have hAθ : A ≤ θ.range := by
    intro a ha
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp (hAS ha)
    exact ⟨⟨m, Subgroup.mem_subgroupOf.mp hm⟩, rfl⟩
  let e : θ.range ≃* φ.range := (QuotientGroup.quotientKerEquivRange θ).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans (QuotientGroup.quotientKerEquivRange φ))
  set A₁ : Subgroup θ.range := A.subgroupOf θ.range with hA₁
  set A₂ : Subgroup (Cube K ≃ₗ[K] Cube K) :=
    (A₁.map e.toMonoidHom).map φ.range.subtype with hA₂
  have hA₂le : A₂ ≤ (cubeHom K).range := by
    rw [cubeHom_range, ← d.range]
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  set E := A₂.comap (cubeHom K) with hE
  have hA₁el : IsElemAbelian 2 A₁ := hAel.comap θ.range.subtype_injective
  have hA₂el : IsElemAbelian 2 A₂ := (hA₁el.map _).map _
  have hEel : IsElemAbelian 2 E := hA₂el.comap cubeHom_injective
  have hcardE : Nat.card E = Nat.card A := by
    have h1 : Nat.card E = Nat.card A₂ := by
      rw [← Subgroup.card_map_of_injective (f := cubeHom K) cubeHom_injective,
        Subgroup.map_comap_eq_self hA₂le]
    have h2 : Nat.card A₂ = Nat.card A₁ := by
      rw [hA₂, Subgroup.card_map_of_injective φ.range.subtype_injective,
        Subgroup.card_map_of_injective e.injective]
    have h3 : Nat.card A₁ = Nat.card A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAθ).toEquiv
    rw [h1, h2, h3]
  have hbound := card_le_pow_nine_of_isElemAbelian_statedProj hEel
  rw [hcardE, hg.card] at hbound
  simpa using hbound

end CFSG.RankThree.GF2n.Smith81
