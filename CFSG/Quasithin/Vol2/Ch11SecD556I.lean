module

public import CFSG.Quasithin.Vol2.Ch11SecDK

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem le_pCoreOf_Y (hTI : PointsTIFact) (h1102 : Stmt11_0_2) (h1141 : Stmt11_4_1)
    (h1143 : Stmt11_4_3) (h : Hyp11 G T L I n) {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) :
    V₁ ≤ pCoreOf 2 (Subgroup.centralizer (V₁ : Set G) ⊓
      sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV₁T : V₁ ≤ T := (SecA.IsVi.le_fsuV hV₁).trans (SecA.fsuV_le_T h)
  have hKC := kOf_le_centralizer hTI h1102 h1141 h1143 h hV₁
  have hTK : T ≤ Subgroup.normalizer (KOf L V₁ V₁ : Set G) :=
    (SecA.IsVi.le_normalizer hV₁).trans (normalizer_le_normalizer_kOf L V₁ V₁)
  have hab : ∀ a ∈ V₁, ∀ b ∈ V₁, a * b = b * a := fun a ha b hb => by
    have hV := SecA.isElemAbelian_fsuV h
    have := hV.1
    have hc := congrArg Subtype.val (mul_comm (⟨a, SecA.IsVi.le_fsuV hV₁ ha⟩ : ↥(fsuV T I))
      ⟨b, SecA.IsVi.le_fsuV hV₁ hb⟩)
    simpa using hc
  have hVY : V₁ ≤ Subgroup.centralizer (V₁ : Set G) ⊓
      sectionCentralizer (KOf L V₁ V₁) (pCoreOf 2 (KOf L V₁ V₁)) := fun v hv => by
    refine ⟨Subgroup.mem_centralizer_iff.mpr fun w hw => hab w hw v hv,
      hTK (hV₁T hv), CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ (hTK (hV₁T hv)),
      fun k hk => ?_⟩
    have hvk : v * k = k * v := (Subgroup.mem_centralizer_iff.mp (hKC hk) v hv)
    rw [hvk, mul_inv_cancel_right, mul_inv_cancel]
    exact Subgroup.one_mem _
  refine CFSG.LieType.BorelTits.le_pCoreOf 2 hVY
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hVY).mpr
      (inf_le_left.trans (Subgroup.centralizer_le_normalizer _)))
    (h.fsu.sylow.1.to_le hV₁T)

end CFSG.Quasithin.Vol2.Ch11.SecD
