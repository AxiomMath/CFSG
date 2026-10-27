module

public import CFSG.Quasithin.Vol2.Ch10SecC8J

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem acts_as_inner_fsuUL (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (h3 : Case10_1_1Three T L I) {s : G} (hs : s ∈ T1 T L) :
    ∃ x₀ ∈ L, (∀ x ∈ L, s * x * s⁻¹ * (x₀ * x * x₀⁻¹)⁻¹ ∈ pCoreOf 2 L) ∧
      ∀ v ∈ fsuUL T L I, s * v * s⁻¹ = x₀ * v * x₀⁻¹ := by
  obtain ⟨x₀, hx₀L, hA, hB⟩ := SecB.inner_of_case3 hyp h3 hs
  refine ⟨x₀, hx₀L, hA, ?_⟩
  have hO := pCoreOf_L_le_centralizer hyp h1011
  have hV1V : fsuUL T L I ≤ fsuVM T L I :=
    commutator_le_left_of_le_normalizer
      ((SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I))
  set g := x₀⁻¹ * s with hg
  have hgen : ⁅fsuUL T L I, L⁆ ≤ Subgroup.centralizer ({g} : Set G) := by
    rw [Subgroup.commutator_le]
    intro v hv l hl
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    set c := s * v * s⁻¹ * (x₀ * v * x₀⁻¹)⁻¹
    set o := x₀⁻¹ * (s * l * s⁻¹ * (x₀ * l * x₀⁻¹)⁻¹) * x₀
    have hc : c ∈ fsuCVM T L I := hB v hv
    have ho : o ∈ pCoreOf 2 L := by
      have h1 := hA l hl
      have hn := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L (L.inv_mem hx₀L)
      have h2 := (Subgroup.mem_normalizer_iff.mp hn _).mp h1
      simpa [o, mul_assoc] using h2
    have hW : ⁅v, l⁆ ∈ fsuVM T L I :=
      hV1V ((commutator_fsuUL_eq hyp) ▸ Subgroup.commutator_mem_commutator hv hl)
    have hcx : Commute c x₀ :=
      (Subgroup.mem_centralizer_iff.mp hc.2 x₀ (SecA.le_fsuL0 T L hx₀L)).symm
    have hgv : g * v * g⁻¹ = c * v := by
      have : g * v * g⁻¹ = x₀⁻¹ * (c * (x₀ * v * x₀⁻¹)) * x₀ := by
        simp only [hg, c]
        group
      rw [this]
      have e : x₀⁻¹ * c = c * x₀⁻¹ := (hcx.inv_right).eq.symm
      calc x₀⁻¹ * (c * (x₀ * v * x₀⁻¹)) * x₀ = (x₀⁻¹ * c) * x₀ * v * (x₀⁻¹ * x₀) := by group
        _ = (c * x₀⁻¹) * x₀ * v * (x₀⁻¹ * x₀) := by rw [e]
        _ = c * v := by group
    have hgl : g * l * g⁻¹ = o * l := by
      simp only [hg, o]
      group
    have hcomm := conj_commutatorElement_eq (s := g) (v := v) (l := l) (c := c) (o := o)
      hgv hgl
      (Subgroup.mem_centralizer_iff.mp hc.2 l (SecA.le_fsuL0 T L hl)).symm
      (Subgroup.mem_centralizer_iff.mp (hO ho) c hc.1)
      (congrArg Subtype.val ((SecA.isElemAbelian_fsuVM hyp).1.is_comm.comm ⟨c, hc.1⟩
        ⟨v, hV1V hv⟩))
      (Subgroup.mem_centralizer_iff.mp (hO ho) v (hV1V hv)).symm
      (Subgroup.mem_centralizer_iff.mp (hO ho) _ hW).symm
    calc g * ⁅v, l⁆ = g * ⁅v, l⁆ * g⁻¹ * g := by group
      _ = ⁅v, l⁆ * g := by rw [hcomm]
  intro v hv
  have hv' : v ∈ ⁅fsuUL T L I, L⁆ := by rw [commutator_fsuUL_eq hyp]; exact hv
  have h := (Subgroup.mem_centralizer_iff.mp (hgen hv') g rfl)
  have e : s = x₀ * g := by simp only [hg]; group
  rw [e]
  calc x₀ * g * v * (x₀ * g)⁻¹ = x₀ * (g * v) * g⁻¹ * x₀⁻¹ := by group
    _ = x₀ * (v * g) * g⁻¹ * x₀⁻¹ := by rw [h]
    _ = x₀ * v * x₀⁻¹ := by group

end CFSG.Quasithin.Vol2.Ch10.SecC
