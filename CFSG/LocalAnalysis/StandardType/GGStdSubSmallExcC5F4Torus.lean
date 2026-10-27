module

public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoInputsParabolic
public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoInputsSylow
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType.SmallExc.F4Two

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction.F4Pilot
  CFSG.LieType.Ree CFSG.StandardType.TableBF4TwoInputs
open CFSG.Open (IsElemAbelian)

theorem eq_zero_of_shift_iterate_mulSingle : ∀ m < 3,
    shift^[m] (Pi.mulSingle (0 : Fin 3) (Multiplicative.ofAdd (1 : ZMod 3))) =
      (Pi.mulSingle (0 : Fin 3) (Multiplicative.ofAdd (1 : ZMod 3)) :
        Fin 3 → Multiplicative (ZMod 3)) → m = 0 := by
  decide +kernel

variable
  {K : Type} [Field K] [CharP K 2]

theorem mem_range_torus3_of_commute {t : adjointGroup .F4 K} (ht : t ∈ sylT K)
    (hc : t * TableBF4Two.torusGen K 0 = TableBF4Two.torusGen K 0 * t) :
    t ∈ (TableBF4Two.torus3 K).range := by
  obtain ⟨f, k, rfl⟩ := sylT_normal_form ht
  rw [cElt_pow_mod] at hc ⊢
  have h2 : TableBF4Two.torus3 K f * cElt K ^ (k % 3) * TableBF4Two.torusGen K 0 *
      (TableBF4Two.torus3 K f * cElt K ^ (k % 3))⁻¹ =
        TableBF4Two.torus3 K
          (shift^[k % 3] (Pi.mulSingle 0 (Multiplicative.ofAdd (1 : ZMod 3)))) := by
    rw [torusGen_eq_torus3]
    calc _ = TableBF4Two.torus3 K f * (cElt K ^ (k % 3) *
          TableBF4Two.torus3 K (Pi.mulSingle 0 (Multiplicative.ofAdd 1)) *
            (cElt K ^ (k % 3))⁻¹) * (TableBF4Two.torus3 K f)⁻¹ := by group
      _ = _ := by
        rw [cElt_pow_conj_torus3, ← map_inv, ← map_mul, ← map_mul, mul_comm f, mul_assoc,
          mul_inv_cancel, mul_one]
  have h1 : TableBF4Two.torus3 K f * cElt K ^ (k % 3) * TableBF4Two.torusGen K 0 *
      (TableBF4Two.torus3 K f * cElt K ^ (k % 3))⁻¹ =
        TableBF4Two.torus3 K (Pi.mulSingle 0 (Multiplicative.ofAdd (1 : ZMod 3))) := by
    rw [hc, mul_inv_cancel_right, torusGen_eq_torus3]
  have hfix := TableBF4Two.torus3_injective (h2.symm.trans h1)
  rw [eq_zero_of_shift_iterate_mulSingle (k % 3) (Nat.mod_lt _ (by norm_num)) hfix, pow_zero,
    mul_one]
  exact ⟨f, rfl⟩

theorem le_range_torus3_of_le_sylT [Finite K] (hK : Nat.card K = 2)
    {B : Subgroup (adjointGroup .F4 K)} (hBT : B ≤ sylT K)
    (hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hB : 3 ^ 3 ≤ Nat.card B) :
    B ≤ (TableBF4Two.torus3 K).range := fun b hb =>
  mem_range_torus3_of_commute (hBT hb) (hBc _ hb _ (torusGen_zero_mem_of_le_sylT hK hBT hBc hB))

theorem exists_mulEquiv_le_range_torus3 [Finite K] (hK : Nat.card K = 2)
    {A : Subgroup (adjointGroup .F4 K)} (hA : IsElemAbelian 3 A) (h27 : 3 ^ 3 ≤ Nat.card A)
    (hα : ∃ U : Subgroup (adjointGroup .F4 K), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      A ≤ Subgroup.normalizer (U : Set (adjointGroup .F4 K))) :
    ∃ β : adjointGroup .F4 K ≃* adjointGroup .F4 K,
      ∀ a ∈ A, β a ∈ (TableBF4Two.torus3 K).range := by
  have : CharP K ReeTag.F4.prime := ‹CharP K 2›
  obtain ⟨V, hV, hV2, hAV⟩ := hα
  have hAp : IsPGroup 3 A := fun x =>
    ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]; exact hA.2 _ x.2)⟩
  obtain ⟨g, hg⟩ := exists_conj_le_C3Levi_or_B3Levi hK hV hV2 hAV hAp h27
  have hγ : ∃ γ : adjointGroup .F4 K ≃* adjointGroup .F4 K, ∀ a ∈ A, γ a ∈ C3Levi K := by
    rcases hg with hC | hB
    · exact ⟨MulAut.conj g, fun a ha => hC ⟨a, ha, rfl⟩⟩
    · refine ⟨(MulAut.conj g).trans (graphAutF4 K).symm, fun a ha => ?_⟩
      have h1 := hB ⟨a, ha, rfl⟩
      rw [← map_graphAutF4_C3Levi] at h1
      obtain ⟨d, hd, hde⟩ := h1
      have e : ((MulAut.conj g).trans (graphAutF4 K).symm) a = d := by
        show (graphAutF4 K).symm (MulAut.conj g a) = d
        rw [show MulAut.conj g a = graphAutF4 K d from hde.symm]
        exact (graphAutF4 K).symm_apply_apply d
      rw [e]
      exact hd
  obtain ⟨γ, hγA⟩ := hγ
  have hA'D : A.map γ.toMonoidHom ≤ C3Levi K := by
    rintro _ ⟨a, ha, rfl⟩
    exact hγA a ha
  obtain ⟨d, -, hd⟩ := exists_conj_le_sylT hK hA'D (hAp.map _)
  set B := (A.map γ.toMonoidHom).map (MulAut.conj d⁻¹).toMonoidHom with hB
  have hBT : B ≤ sylT K := by
    rintro _ ⟨a, ha, rfl⟩
    simpa [MulAut.conj_apply] using hd a ha
  have hBe : IsElemAbelian 3 B := (hA.map _).map _
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hBe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hBcard : 3 ^ 3 ≤ Nat.card B := by
    rw [hB, Subgroup.card_map_of_injective (MulAut.conj d⁻¹).injective,
      Subgroup.card_map_of_injective γ.injective]
    exact h27
  exact ⟨γ.trans (MulAut.conj d⁻¹), fun a ha =>
    le_range_torus3_of_le_sylT hK hBT hBc hBcard ⟨γ a, ⟨a, ha, rfl⟩, rfl⟩⟩

end CFSG.StandardType.SmallExc.F4Two

end
