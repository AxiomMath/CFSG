module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qNFqElem
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieD4Facts
import CFSG.LieType.Chevalley.GraphFixedParabolicNormalizer
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qNFqCard

public section

namespace CFSG.Quasithin.H13.F431.D4q.NFq

open CFSG.ComponentClassification.RankTwoExceptional.D4 CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.Quasithin.H13.F431.D4q.Struct


set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)
  (hσ : ∀ c, σ (σ (σ c)) = c)

theorem Pst0_conj_Qg {p : Cm σ} (hp : p ∈ Pst0 σ) {x : ModGL TwistTag.D4.tag K}
    (hx : x ∈ d4Vr K σ) : (p : ModGL TwistTag.D4.tag K) * x * (p : ModGL TwistTag.D4.tag K)⁻¹ ∈
      d4Vr K σ := by
  have hrad : graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom
      {(⟨0, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)} = d4Vr K σ :=
    CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4.radical_eq_simpleComplement σ.toRingHom
      ⟨0, by decide⟩ CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4.supp_fa0
  have h := diagram_fixed_parabolic_root_radical_normalizers TwistTag.D4 K σ
    {(⟨0, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)}
  have hpN : (p : ModGL TwistTag.D4.tag K) ∈ Subgroup.normalizer (d4Vr K σ : Set _) := by
    have : (p : ModGL TwistTag.D4.tag K) ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom ⊓
        Subgroup.normalizer (graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom
          {(⟨0, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)} : Set (ModGL TwistTag.D4.tag K)) := by
      rw [h]
      exact Subgroup.mem_subgroupOf.mp hp
    rw [hrad] at this
    exact (Subgroup.mem_inf.mp this).2
  exact (Subgroup.mem_normalizer_iff.mp hpN _).mp hx

include hσ in
theorem Zg_iff_center {x : ModGL TwistTag.D4.tag K} :
    (x ∈ d4Vr K σ ∧ ∀ y ∈ d4Vr K σ, x * y = y * x) ↔ x ∈ d4Zz K σ := by
  constructor
  · rintro ⟨hx, hc⟩
    obtain ⟨a, f, rfl⟩ := exists_vmk σ hσ hx
    have h0 : a = 0 := by
      refine isoBil_sep_left σ hσ fun b => Subtype.ext ?_
      exact isoForm_eq_zero_of_commute σ hσ (hc (vmk σ b 0) (vmk_mem σ hσ b 0))
    rw [h0]
    exact (mem_Zg_iff σ hσ).2 ⟨f, rfl⟩
  · intro hz
    exact ⟨Zg_le_Qg σ hσ hz, fun y hy => (Zg_central_Qg σ hσ hy hz).symm⟩

include hσ in
theorem Pst0_conj_Zg {p : Cm σ} (hp : p ∈ Pst0 σ) {z : ModGL TwistTag.D4.tag K}
    (hz : z ∈ d4Zz K σ) : (p : ModGL TwistTag.D4.tag K) * z * (p : ModGL TwistTag.D4.tag K)⁻¹ ∈
      d4Zz K σ := by
  have hzQ : z ∈ d4Vr K σ := Zg_le_Qg σ hσ hz
  have hc : ∀ y ∈ d4Vr K σ, (z : ModGL TwistTag.D4.tag K) * y = y * z :=
    fun y hy => (Zg_central_Qg σ hσ hy hz).symm
  refine (Zg_iff_center σ hσ).1 ⟨Pst0_conj_Qg σ hp hzQ, fun y hy => ?_⟩
  have hy' := Pst0_conj_Qg σ (inv_mem hp) hy
  have h1 := hc _ hy'
  simp only [Subgroup.coe_inv, inv_inv] at hy'
  calc (p : ModGL TwistTag.D4.tag K) * z * (p : ModGL TwistTag.D4.tag K)⁻¹ * y
      = (p : ModGL TwistTag.D4.tag K) * (z * ((p : ModGL TwistTag.D4.tag K)⁻¹ * y *
          (p : ModGL TwistTag.D4.tag K))) * (p : ModGL TwistTag.D4.tag K)⁻¹ := by group
    _ = (p : ModGL TwistTag.D4.tag K) * (((p : ModGL TwistTag.D4.tag K)⁻¹ * y *
          (p : ModGL TwistTag.D4.tag K)) * z) * (p : ModGL TwistTag.D4.tag K)⁻¹ := by
        rw [hc _ (by simpa using Pst0_conj_Qg σ (inv_mem hp) hy)]
    _ = y * ((p : ModGL TwistTag.D4.tag K) * z * (p : ModGL TwistTag.D4.tag K)⁻¹) := by group

end CFSG.Quasithin.H13.F431.D4q.NFq
