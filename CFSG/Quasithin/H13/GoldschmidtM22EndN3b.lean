module

public import CFSG.Quasithin.H13.GoldschmidtM22EndN2b
public import CFSG.Quasithin.H13.GoldschmidtM22EndN2c
public import CFSG.Quasithin.H13.GoldschmidtM22EndN2d

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

namespace PsiData

variable {n : ℕ} (P : PsiData T L V n) (h : Hyp6Sec2 G T M L V)

include P h in
theorem hyp626_of_noncomm (hZ : Nat.card (quasithinOmegaOneCenter T) = 2) (h621 : Stmt6_2_1)
    (h6210 : Stmt6_2_10) (h6211 : Stmt6_2_11) (a g : ↥(HH T)) (haV : (a : G) ∈ V)
    (haC : (a : G) ∉ CHU T L V)
    (hnc₁ : ¬ Commute (P.ψ (g⁻¹ * a * g)) (P.ψ a))
    (hnc₂ : ¬ Commute (P.ψ (g * a * g⁻¹)) (P.ψ a)) :
    (conjSubgroup V (g : G) ⊓ Subgroup.normalizer (V : Set G)).relIndex
        (conjSubgroup V (g : G)) = 2 ∧
      (V ⊓ Subgroup.normalizer ((conjSubgroup V (g : G) : Subgroup G) : Set G)).relIndex V = 2 := by
  obtain ⟨hτ, hNa⟩ := P.swap_norm a haV haC
  have hgH : (g : G) ∈ HH T := g.2
  have hU : (V ⊓ Subgroup.normalizer ((conjSubgroup V (g : G) : Subgroup G) : Set G)).relIndex V
      = 2 := by
    refine relIndex_eq_two_of_lt (A := V ⊓ CHU T L V)
      (inf_le_inf_left _ (CHU_le_normalizer_conj_V h hZ h621 hgH)) inf_le_left
      (relIndex_V_CHU h h6211) fun hle => ?_
    have haN := (Subgroup.mem_inf.mp (hle haV)).2
    rw [← CFSG.QuasithinUnique.C5.conjSubgroup_normalizer] at haN
    exact hnc₂ ((hNa (g * a * g⁻¹)).mp (mem_conjSubgroup_iff.mp haN))
  have hc₁V : ((g⁻¹ * a * g : ↥(HH T)) : G) ∈ conjSubgroup V (g : G) := by
    refine mem_conjSubgroup_iff.mpr ?_
    have e : (g : G) * ((g : G)⁻¹ * (a : G) * (g : G)) * (g : G)⁻¹ = (a : G) := by group
    exact e ▸ haV
  have hA : (conjSubgroup V (g : G) ⊓ Subgroup.normalizer (V : Set G)).relIndex
      (conjSubgroup V (g : G)) = 2 := by
    have hrel : (conjSubgroup V (g : G) ⊓ CHU T L V).relIndex (conjSubgroup V (g : G)) = 2 := by
      have := CFSG.QuasithinUnique.C5.relIndex_conjSubgroup (V ⊓ CHU T L V) V (g : G)
      rw [CFSG.QuasithinUnique.C5.conjSubgroup_inf,
        CFSG.Quasithin.conjSubgroup_eq_iff_mem_normalizer.mpr
          (HH_le_normalizer_CHU h hZ hgH)] at this
      rw [this]
      exact relIndex_V_CHU h h6211
    refine relIndex_eq_two_of_lt (A := conjSubgroup V (g : G) ⊓ CHU T L V)
      (inf_le_inf_left _ (CHU_le_normalizer_V h h6210)) inf_le_left hrel fun hle => ?_
    have hN := (Subgroup.mem_inf.mp (hle hc₁V)).2
    exact hnc₁ ((hNa (g⁻¹ * a * g)).mp hN)
  exact ⟨hA, hU⟩

end PsiData

end CFSG.Quasithin.H13.GM22
