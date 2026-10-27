module

public import CFSG.Quasithin.Background.C116Two.Orbit
public import CFSG.Quasithin.Background.C116Two.FixModLift
public import CFSG.Quasithin.Background.C116Two.FixModVec

public section

namespace CFSG.Quasithin.C116Two

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem Ctx.thompsonJ_le_normalizer {H T V L : Subgroup G} (h : Ctx H T V L) :
    thompsonJ T ≤ Subgroup.normalizer (L : Set G) :=
  iSup₂_le fun _ hA => h.normalizer_of_isMaxElemAbelian hA

theorem Ctx.exists_fixed_vector {H T V L : Subgroup G} (h : Ctx H T V L) :
    ∃ w ∈ blockU L, (∀ j ∈ thompsonJ T, j * w = w * j) ∧ ∃ l ∈ L, l * w ≠ w * l := by
  have hJN := h.thompsonJ_le_normalizer
  have hJ2 : IsPGroup 2 (thompsonJ T) := h.sylow.2.1.to_le (C1GN.thompsonJ_le T)
  obtain ⟨u, huU, huZ, hu⟩ := exists_fixMod_ne h.chi hJ2 hJN
  have hUV : blockU L ≤ V := h.blockU_le_V
  have hUe : IsElemAbelian 2 (blockU L) := B2F.isElemAbelian_mono hUV h.red.2.2.1
  have hUT : blockU L ≤ T := hUV.trans h.V_le_T
  refine ⟨u, huU, ?_, ?_⟩
  ·
    have hle : thompsonJ T ≤ Subgroup.centralizer ({u} : Set G) := by
      refine iSup₂_le fun A hA => ?_
      have hAJ : A ≤ thompsonJ T := le_iSup₂_of_le A hA le_rfl
      have hoff := card_le_relIndex_mul_card hUe hUT hA
      have := fixMod_le_centralizer h.chi hA.2.1 (h.normalizer_of_isMaxElemAbelian hA) hoff u huU
        (fun a ha => hu a (hAJ ha))
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact this a ha
    intro j hj
    have := Subgroup.mem_centralizer_iff.mp (hle hj) u rfl
    exact this.symm
  · by_contra hcon
    push_neg at hcon
    apply huZ
    refine ⟨huU, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro l hl
    exact hcon l hl

theorem Ctx.baum_le_normalizer {H T V L : Subgroup G} (h : Ctx H T V L) :
    baum T ≤ Subgroup.normalizer (L : Set G) := by
  obtain ⟨w, hwU, hJ, l₀, hl₀, hl₀w⟩ := h.exists_fixed_vector
  have hVe : IsElemAbelian 2 V := h.red.2.2.1
  have hVN : H ≤ Subgroup.normalizer (V : Set G) := h.red.2.1
  have hLH : L ≤ H := h.chi.1.2.1
  have hwV : w ∈ V := by
    have hle : blockU L ≤ V := by
      rw [← h.commutator_V_eq_blockU, Subgroup.commutator_le]
      intro v hv l hl
      have h1 : l * v⁻¹ * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hVN (hLH hl)) v⁻¹).mp
        (V.inv_mem hv)
      have : ⁅v, l⁆ = v * (l * v⁻¹ * l⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [this]
      exact V.mul_mem hv h1
    exact hle hwU
  have hwΩ := mem_omegaOneCenter_of_centralizes hVe h.V_le_T hwV hJ
  intro b hb
  by_contra hbN
  have hbH : b ∈ H := h.sylow.1 hb.1
  have hLb : IsBlock2 H (conjByElt b L) := IsBlock2.conjByElt_of_mem h.chi.1 hbH
  have hne : L ≠ conjByElt b L := fun hEq =>
    hbN (mem_normalizer_of_conj_eq (by unfold conjByElt at hEq; exact hEq.symm))
  have hcomm : ⁅L, conjByElt b L⁆ = ⊥ :=
    distinctBlocksCommuteStatement H L (conjByElt b L) h.charTwo h.chi.1 hLb hne
  have hwL : w ∈ L := by
    have hle : blockU L ≤ L := by
      unfold blockU
      rw [Subgroup.commutator_le]
      intro q hq l hl
      have hqL : q ∈ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L hq
      simp only [commutatorElement_def]
      exact L.mul_mem (L.mul_mem (L.mul_mem hqL hl) (L.inv_mem hqL)) (L.inv_mem hl)
    exact hle hwU
  have hbw : w * b = b * w := by
    have := Subgroup.mem_centralizer_iff.mp hb.2 w hwΩ
    exact this
  have hbw'' : b * w * b⁻¹ = w := by
    rw [← hbw]; group
  apply hl₀w
  have hx : b * l₀ * b⁻¹ ∈ conjByElt b L := ⟨l₀, hl₀, by simp [MulAut.conj_apply]⟩
  have hc := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm)
  have hcw : (b * l₀ * b⁻¹) * w = w * (b * l₀ * b⁻¹) :=
    Subgroup.mem_centralizer_iff.mp (hc hwL) (b * l₀ * b⁻¹) hx
  calc l₀ * w = b⁻¹ * ((b * l₀ * b⁻¹) * (b * w * b⁻¹)) * b := by group
    _ = b⁻¹ * ((b * l₀ * b⁻¹) * w) * b := by rw [hbw'']
    _ = b⁻¹ * (w * (b * l₀ * b⁻¹)) * b := by rw [hcw]
    _ = b⁻¹ * ((b * w * b⁻¹) * (b * l₀ * b⁻¹)) * b := by rw [hbw'']
    _ = w * l₀ := by group

theorem theoremC116Two : TheoremC116Two := by
  intro G _ _ H T V L hH hV hT hL hJ
  have hLH : L ≤ H := hL.1.2.1
  have hnc : ¬ L ≤ Subgroup.centralizer (V : Set G) := by
    intro hLC
    apply hJ
    rw [Subgroup.commutator_le]
    intro l hl j hj
    have hjH : j ∈ H := hT.1 (C1GN.thompsonJ_le T hj)
    have hjC : j * l⁻¹ * j⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
      have hjN := CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_centralizer V
        (hV.2.1 hjH)
      exact (Subgroup.mem_normalizer_iff.mp hjN l⁻¹).mp ((Subgroup.centralizer (V : Set G)).inv_mem (hLC hl)) |> fun h => by simpa using h
    have e : ⁅l, j⁆ = l * (j * l⁻¹ * j⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.centralizer (V : Set G)).mul_mem (hLC hl) hjC
  exact (Ctx.baum_le_normalizer ⟨hH, hV, hT, hL, hnc⟩)

end CFSG.Quasithin.C116Two
