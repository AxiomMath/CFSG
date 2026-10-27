module

public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeSympLinAux2
public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeGlue
public import CFSG.LocalAnalysis.StandardType.GGNbrCenterPCyclic
public import CFSG.LocalAnalysis.StandardType.GGResNonsingularBase
import CFSG.LocalAnalysis.StandardType.GGPZWeylB

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

variable {G : Type} [Group G] [Finite G]

theorem ggWeylOfType_B_nbr_of_linearNs (hcyc : GGLabelCenterPCyclicInput) {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {S : ℕ → LargeEvenLabel → Prop} (hcfg : GGConfig p B Bs x L D J)
    (hNoTr : GGNoTransvection p Bs) (hnb : GGNbr p B x D J y K)
    (hS : ∀ lab, S p lab → lab.tag = .A ∧ p ∣ 2 ^ lab.n + 1)
    (hK : GGInnerDiagOnLabel S p Bs K) :
    ∃ (k : ℕ) (lab : LargeEvenLabel), 3 ≤ k ∧
      GGWeylOfType p (CoxeterMatrix.B k) (ggAutomizer K Bs) ∧ LargeEvenInLambda2 lab ∧ S p lab ∧
      lab.rank + 1 < (p - 1) * (k + 1) ∧ GGHasLabel lab (↥K ⧸ Subgroup.center ↥K) := by
  have hp : p.Prime := Fact.out
  have hInnK : GGInnerDiagOn Bs K :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hP.2.1, hP.2.2⟩) hK
  have hZ := ggNbr_card_center_le_of_centerPCyclic hcyc hcfg hInnK
  obtain ⟨hperf, lab, hlab, hraw⟩ := hK
  obtain ⟨R₀, _instR₀, I₀, F₀, hQ₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, -, hS₀, -⟩ := hQ₀
  have hhas : GGHasLabel lab (↥K ⧸ Subgroup.center ↥K) := by
    unfold GGHasLabel
    refine largeEvenRawDatum_mono ?_ hraw
    rintro R _ I F ⟨-, -, θ, -⟩
    exact ⟨θ⟩
  obtain ⟨R, _instR, I, F, ⟨-, -, θ, -, hN, hind⟩, r, hlift, hT⟩ :=
    largeEvenRawDatum_exists
      (ggWTB2_largeEvenLabelAll_weylTypeB_linearNs hp hlab (hS lab hS₀) _ hraw)
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈ I := by
    intro b hb
    obtain ⟨φ, hφI, hindφ⟩ := hind b⁻¹ (Bs.inv_mem hb)
    have hφeq : φ = ggLAut K θ ⟨b⁻¹⁻¹,
        (Subgroup.normalizer (K : Set G)).inv_mem (hN (Bs.inv_mem hb))⟩ :=
      eq_ggLAut_of_induces K θ (hN (Bs.inv_mem hb)) hindφ
    have hb_eq : (⟨b⁻¹⁻¹, (Subgroup.normalizer (K : Set G)).inv_mem
        (hN (Bs.inv_mem hb))⟩ : Subgroup.normalizer (K : Set G)) = ⟨b, hN hb⟩ :=
      Subtype.ext (inv_inv b)
    rw [hφeq, hb_eq] at hφI
    exact hφI
  obtain ⟨k, hk, hkd, f, hf⟩ := hT K (ggQuotHom θ) (ggGamma K hN).range
    (ggTorusTBGroup_of_nbr hcfg hnb hperf θ hN hBsI hlift)
  exact ⟨k, lab, hk, ggWeylOfType_of_ggTorusReflSet hcfg hNoTr hN f hf hZ, hlab, hS₀, hkd, hhas⟩

theorem card_ggAutomizer_nbr_of_linearNs (hcyc : GGLabelCenterPCyclicInput) {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {S : ℕ → LargeEvenLabel → Prop} (hcfg : GGConfig p B Bs x L D J)
    (hNoTr : GGNoTransvection p Bs) (hnb : GGNbr p B x D J y K)
    (hS : ∀ lab, S p lab → lab.tag = .A ∧ p ∣ 2 ^ lab.n + 1)
    (hK : GGInnerDiagOnLabel S p Bs K) :
    ∃ k : ℕ, 3 ≤ k ∧ Nat.card ↥(ggAutomizer K Bs) = 2 ^ k * k.factorial := by
  obtain ⟨k, _, hk, ⟨e, -⟩, -⟩ := ggWeylOfType_B_nbr_of_linearNs hcyc hcfg hNoTr hnb hS hK
  exact ⟨k, hk, (Nat.card_congr e.toEquiv).symm.trans (ggCoxeterB_card k (by omega))⟩

theorem not_ggSingularWeylOrder_two_pow_mul_factorial {p k : ℕ} (hk : 2 ≤ k) :
    ¬ ggSingularWeylOrder p (2 ^ k * k.factorial) := by
  rintro (⟨m, -, -, hm⟩ | ⟨-, hm⟩)
  · exact factorial_succ_ne_two_pow_mul_factorial hk hm.symm
  · exact two_pow_mul_factorial_ne_E6 hk hm

theorem GGResHyp.not_ggSingularWeylOrder_K_of_linearNs (hcyc : GGLabelCenterPCyclicInput)
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {S : ℕ → LargeEvenLabel → Prop} (hH : GGResHyp p B Bs x L D J y K)
    (hS : ∀ lab, S p lab → lab.tag = .A ∧ p ∣ 2 ^ lab.n + 1)
    (hK : GGInnerDiagOnLabel S p Bs K) :
    ¬ ggSingularWeylOrder p (Nat.card ↥(ggAutomizer K Bs)) := by
  obtain ⟨k, hk, hc⟩ :=
    card_ggAutomizer_nbr_of_linearNs hcyc hH.1 hH.2.2.2.1 hH.2.2.2.2.1 hS hK
  rw [hc]
  exact not_ggSingularWeylOrder_two_pow_mul_factorial (by omega)

end CFSG.StandardType

end
