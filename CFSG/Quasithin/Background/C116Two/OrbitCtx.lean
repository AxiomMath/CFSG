module

public import CFSG.Quasithin.Background.C116Two.Ctx
public import CFSG.Quasithin.Background.C116Two.OrbitConj
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238FourConj

public section

namespace CFSG.Quasithin.C116Two

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem Ctx.conj {H T V L : Subgroup G} (h : Ctx H T V L) {a : G} (ha : a ∈ T) :
    Ctx H T V (conjByElt a L) := by
  have haH : a ∈ H := h.sylow.1 ha
  refine ⟨h.charTwo, h.red, h.sylow, ⟨IsBlock2.conjByElt_of_mem h.chi.1 haH, ?_⟩, ?_⟩
  · rcases h.chi.2 with ⟨n, hn, hlin⟩ | ⟨m, hm, hm3, halt⟩
    · exact Or.inl ⟨n, hn, Lin2.IsLin2Type.map_equiv hlin (MulAut.conj a)⟩
    · exact Or.inr ⟨m, hm, hm3, L238.IsAltType.map_equiv halt (MulAut.conj a)⟩
  · intro hle
    apply h.notCent
    intro l hl
    have hmem : a * l * a⁻¹ ∈ conjByElt a L := ⟨l, hl, by simp [MulAut.conj_apply]⟩
    have h1 := hle hmem
    have hN : a⁻¹ ∈ Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G) :=
      CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_centralizer V
        (h.red.2.1 (H.inv_mem haH))
    have := (Subgroup.mem_normalizer_iff.mp hN (a * l * a⁻¹)).mp h1
    simpa [mul_assoc] using this

theorem orbitW_le_V {H T V L A : Subgroup G} (h : Ctx H T V L) (hAT : A ≤ T) :
    orbitW A L ≤ V :=
  iSup₂_le fun _ ha => (h.conj (hAT ha)).blockU_le_V

theorem orbitW_elemAbelian_le {H T V L A : Subgroup G} (h : Ctx H T V L) (hAT : A ≤ T) :
    IsElemAbelian 2 (orbitW A L) ∧ orbitW A L ≤ T :=
  ⟨B2F.isElemAbelian_mono (orbitW_le_V h hAT) h.red.2.2.1, (orbitW_le_V h hAT).trans h.V_le_T⟩

@[expose] def fixModZ {L : Subgroup G} (hL : IsShort2 L) (B : Subgroup G) : Subgroup G where
  carrier := {u | u ∈ blockU L ∧ ∀ b ∈ B, ⁅u, b⁆ ∈ blockZ L}
  one_mem' := ⟨(blockU L).one_mem, fun b _ => by simp [(blockZ L).one_mem]⟩
  mul_mem' := by
    rintro u v ⟨hu, hu'⟩ ⟨hv, hv'⟩
    refine ⟨(blockU L).mul_mem hu hv, fun b hb => ?_⟩
    have hcomm : ∀ x ∈ blockU L, ∀ y ∈ blockU L, x * y = y * x := (C1.elemAb2_blockU hL).1
    have hZU : blockZ L ≤ blockU L := inf_le_left
    have e : ⁅u * v, b⁆ = (u * ⁅v, b⁆ * u⁻¹) * ⁅u, b⁆ := by
      simp only [commutatorElement_def]; group
    have h1 : u * ⁅v, b⁆ * u⁻¹ = ⁅v, b⁆ := by
      have := hcomm u hu _ (hZU (hv' b hb))
      rw [this]; group
    rw [e, h1]
    exact (blockZ L).mul_mem (hv' b hb) (hu' b hb)
  inv_mem' := by
    rintro u ⟨hu, hu'⟩
    refine ⟨(blockU L).inv_mem hu, fun b hb => ?_⟩
    have hcomm : ∀ x ∈ blockU L, ∀ y ∈ blockU L, x * y = y * x := (C1.elemAb2_blockU hL).1
    have hZU : blockZ L ≤ blockU L := inf_le_left
    have e : ⁅u⁻¹, b⁆ = u⁻¹ * (⁅u, b⁆)⁻¹ * u := by
      simp only [commutatorElement_def]; group
    have h1 : u⁻¹ * (⁅u, b⁆)⁻¹ * u = (⁅u, b⁆)⁻¹ := by
      have := hcomm u⁻¹ ((blockU L).inv_mem hu) _ ((blockU L).inv_mem (hZU (hu' b hb)))
      rw [this]; group
    rw [e, h1]
    exact (blockZ L).inv_mem (hu' b hb)

end CFSG.Quasithin.C116Two
