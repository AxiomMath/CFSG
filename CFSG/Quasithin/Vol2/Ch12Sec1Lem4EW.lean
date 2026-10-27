module

public import CFSG.Quasithin.Vol2.Ch12Sec1Lem4Z1W
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem4X

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin.E3 CFSG.LieType.BorelTits
  CFSG.Assembly.LowTwoRank EmptyFaithfulMultiple
open scoped IsMulCommutative

namespace Sec1214

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V V₁ V₂ T₀ : Subgroup G} {v : G}
  (c : Setting T L V V₁ V₂ v T₀)
include c

theorem not_le_normalizer_XW (hFF : LemH9FF4) (hA21 : AsA21SQTKSection) (h51 : AsB51)
    (h134 : C134L32CorrM) {X : Subgroup G} (hX : IsXSub T L V V₁ X) :
    ¬ T₀ ⊔ X ⊔ T ≤ Subgroup.normalizer (X : Set G) := by
  intro hH
  set T₁ := T ⊓ Subgroup.normalizer (V₁ : Set G) with hT₁
  set C := omegaOneCenterOf T₁ ⊓ Subgroup.centralizer (L : Set G) with hC
  have hCX : C = omegaOneCenterOf T₁ ⊓ Subgroup.centralizer (X : Set G) := by
    refine le_antisymm (fun z hz => ⟨hz.1, Subgroup.centralizer_le
      (by exact_mod_cast hX.le_L) hz.2⟩) (fun z hz => ⟨hz.1, ?_⟩)
    exact c.mem_centralizer_of_isXSub hFF hA21 h51 hX hz.1 hz.2
  obtain ⟨z, hzZ, hz1, hzL⟩ := c.exists_mem_omegaOneCenterOfW h134
  have hC1 : C ≠ ⊥ := fun hb => hz1 (by
    have : z ∈ C := ⟨hzZ, hzL⟩
    rwa [hb, Subgroup.mem_bot] at this)
  have hC2 : IsPGroup 2 ↥C :=
    c.T₁_two.to_le (inf_le_left.trans (A4.omegaOneCenterOf_le T₁))
  have hLT : L ⊔ T ≤ Subgroup.normalizer (C : Set G) := by
    refine sup_le (fun l hl => Sec121Swap.mem_normalizer_of_conj_mem fun w hw => ?_)
      (fun t ht => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨A4.normalizer_le_normalizer_omegaOneCenterOf T₁ (c.T_le_normalizer_T₁ ht),
          B6.le_normalizer_centralizer c.S.ctx.hTL ht⟩)
    have h1 : l * w = w * l := Subgroup.mem_centralizer_iff.mp hw.2 l hl
    rw [h1, mul_inv_cancel_right]
    exact hw
  have hT₀C : T₀ ≤ Subgroup.normalizer (C : Set G) := by
    intro t ht
    rw [hCX]
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨A4.normalizer_le_normalizer_omegaOneCenterOf T₁ (c.hT₀N ht),
        B6.le_normalizer_centralizer (le_sup_left.trans (le_sup_left.trans hH)) ht⟩
  exact c.hT₀M (hT₀C.trans (c.normalizer_le hC1 hC2 hLT))

end Setting

end Sec1214

end CFSG.Quasithin.H13
