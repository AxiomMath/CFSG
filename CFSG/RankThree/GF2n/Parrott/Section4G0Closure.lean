module

public import CFSG.GroupTheory.WeaklyClosedFusion
public import CFSG.RankThree.GF2n.Parrott.Section1Fusion
public import CFSG.RankThree.GF2n.Parrott.Section4EInv
public import CFSG.RankThree.GF2n.Parrott.Section4G0Nonfusion
public import CFSG.GF2Type.Aschbacher1976
public import CFSG.GroupTheory.Fitting.MulEquiv
public import CFSG.GroupTheory.PCore.Transport
public import CFSG.Holt.PSL2Natural.Defs
public import CFSG.Holt.PermFacts
public import CFSG.Holt.ThreePoint
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalBender
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatSuzuki
public import CFSG.LocalAnalysis.UniquenessCase.UC6Basic
public import CFSG.Quasithin.Background.E2NParamStar
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS3
public import CFSG.Quasithin.Vol2.E2TenEight
public import CFSG.RankThree.Holt.Basic
public import CFSG.RankThree.PartTwo.Sec21.HoltCatalog

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

theorem exists_outer_involution_nonfusion_of_sylow {E : Subgroup G} (hE : IsParrottE z E)
    (hJN : J z ≤ ⁅H z, H z⁆ ⊔ centerIn (J z))
    (hweak : ∀ T : Subgroup G, IsSylowOf 2 T (H z) → E ≤ T →
      ∀ g : G, CFSG.conjugate E g ≤ T → CFSG.conjugate E g = E)
    (hEinv : ∀ y ∈ ⁅H z, H z⁆ ⊔ centerIn (J z), orderOf y = 2 → ∃ c ∈ H z, c * y * c⁻¹ ∈ E)
    (hS : ∃ x ∈ H z, orderOf x = 2 ∧ x ∉ ⁅H z, H z⁆ ⊔ centerIn (J z) ∧
      ∃ Y : Subgroup G, IsSylowOf 2 Y (H z ⊓ centralizer ({x} : Set G)) ∧
        IsSylowOf 2 Y (centralizer ({x} : Set G))) :
    ∃ x ∈ H z, orderOf x = 2 ∧ x ∉ ⁅H z, H z⁆ ⊔ centerIn (J z) ∧
      ∀ g : G, g⁻¹ * x * g ∉ ⁅H z, H z⁆ ⊔ centerIn (J z) := by
  obtain ⟨hEH, hEHJ, -, hEab, -⟩ := hE
  obtain ⟨x, hxH, hx2, hxN, Y, hYH, hYG⟩ := hS
  have hEN : E ≤ ⁅H z, H z⁆ ⊔ centerIn (J z) := hEHJ.trans (sup_le le_sup_left hJN)
  have hNnorm : ∀ c ∈ H z, ∀ y ∈ ⁅H z, H z⁆ ⊔ centerIn (J z),
      c * y * c⁻¹ ∈ ⁅H z, H z⁆ ⊔ centerIn (J z) := by
    intro c hc y hy
    have h1 : c * y * c⁻¹ * y⁻¹ ∈ ⁅H z, H z⁆ :=
      Subgroup.commutator_mem_commutator hc (commutator_sup_centerIn_le_H hy)
    have h2 : c * y * c⁻¹ = (c * y * c⁻¹ * y⁻¹) * y := by group
    rw [h2]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1) hy
  have hweak' : ∀ T : Subgroup G, IsSylowOf 2 T (H z) → E ≤ T → ∀ m : G,
      (∀ a ∈ E, m⁻¹ * a * m ∈ T) → ∀ y : G, m * y * m⁻¹ ∈ E → y ∈ E := by
    intro T hT hET m hm y hy
    have hle : CFSG.conjugate E m ≤ T := by
      intro w hw
      have hw' : m * w * m⁻¹ ∈ E := mem_conjugate_iff.mp hw
      have h1 := hm _ hw'
      have e : m⁻¹ * (m * w * m⁻¹) * m = w := by group
      rwa [e] at h1
    have heq := hweak T hT hET m hle
    have h2 : y ∈ CFSG.conjugate E m := mem_conjugate_iff.mpr hy
    rwa [heq] at h2
  refine ⟨x, hxH, hx2, hxN, fun g hg => ?_⟩
  have hy2 : orderOf (g⁻¹ * x * g) = 2 := by
    rw [← hx2]
    exact (SemiconjBy.orderOf_eq g⁻¹ (show g⁻¹ * x = (g⁻¹ * x * g) * g⁻¹ by group)).symm
  obtain ⟨c, hcH, hcE⟩ := hEinv _ hg hy2
  have hxE : (c * g⁻¹) * x * (c * g⁻¹)⁻¹ ∈ E := by
    have h1 : (c * g⁻¹) * x * (c * g⁻¹)⁻¹ = c * (g⁻¹ * x * g) * c⁻¹ := by group
    rw [h1]
    exact hcE
  obtain ⟨c', hc'H, hc'E⟩ :=
    CFSG.GroupTheory.exists_mem_conj_mem_of_weaklyClosed_of_isSylowOf_centralizer (p := 2) hYG
      (hYH.le.trans inf_le_left) hEH hEab.isPGroup
      (fun a ha b hb => congrArg Subtype.val (hEab.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)) hweak' hxE
  apply hxN
  have h3 := hNnorm c'⁻¹ (inv_mem hc'H) _ (hEN hc'E)
  have e : c'⁻¹ * (c' * x * c'⁻¹) * c'⁻¹⁻¹ = x := by group
  rwa [e] at h3

theorem exists_index_two_not_le_H_of_sylow_centralizer (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) = centerIn (H z))
    (hH' : (⁅H z, H z⁆ ⊔ centerIn (J z)).relIndex (H z) = 2) {E : Subgroup G}
    (hE : IsParrottE z E) (hJN : J z ≤ ⁅H z, H z⁆ ⊔ centerIn (J z))
    (hweak : ∀ T : Subgroup G, IsSylowOf 2 T (H z) → E ≤ T →
      ∀ g : G, CFSG.conjugate E g ≤ T → CFSG.conjugate E g = E)
    (hEinv : ∀ y ∈ ⁅H z, H z⁆ ⊔ centerIn (J z), orderOf y = 2 → ∃ c ∈ H z, c * y * c⁻¹ ∈ E)
    (hS : ∃ x ∈ H z, orderOf x = 2 ∧ x ∉ ⁅H z, H z⁆ ⊔ centerIn (J z) ∧
      ∃ Y : Subgroup G, IsSylowOf 2 Y (H z ⊓ centralizer ({x} : Set G)) ∧
        IsSylowOf 2 Y (centralizer ({x} : Set G))) :
    ∃ G₀ : Subgroup G, G₀.Normal ∧ G₀.index = 2 ∧ ¬ H z ≤ G₀ :=
  exists_index_two_not_le_H_of_nonfusion h hZ hH'
    (exists_outer_involution_nonfusion_of_sylow hE hJN hweak hEinv hS)

end CFSG.RankThree.GF2n.Parrott
