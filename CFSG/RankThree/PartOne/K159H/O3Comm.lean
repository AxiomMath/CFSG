module

public import CFSG.RankThree.PartOne.K159H.O3Wpart
public import CFSG.RankThree.PartOne.K159H.O3Reduce
public import CFSG.RankThree.PartOne.K159H.O3Norm

public noncomputable section

namespace CFSG.RankThree.PartOne.K159H

open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Universal.Spin
  CFSG.RankThree.OrthogonalInvolutions Module

variable {K : Type} [Field K] {A : Type} [AddCommGroup A] [Module K A] {r : ℕ} {qA : QuadraticForm K A}
  {S : Subgroup (Fin r → Kˣ)} [Finite K] [CharP K 2] [FiniteDimensional K A]

theorem Csub_le_sup (hreg : (polarBilin qA).Nondegenerate) (hani : qA.Anisotropic) (hdim : finrank K A = 2)
    (hr : r = 3) (hnt : ∃ j, ¬ TrivOn S j) :
    Csub qA S ≤ Rts qA S ⊔ (Tor K A r ⊔ Rot qA r) := by
  have hr3 : 3 ≤ r := by omega
  intro g hg
  obtain ⟨hgΩ, hgC⟩ := mem_Csub.1 hg
  obtain ⟨h, hh, g', hg', hgeq, hfix⟩ := reduce (S := S) (qA := qA) _ g hgC rfl
  have hhΩ : h ∈ Om qA r := (sup_le (Rts_le_Om hreg hr3 S) (Tor_le_Om hreg hr3)) hh
  have hg'Ω : g' ∈ Om qA r := by
    have : g' = h⁻¹ * g := by rw [hgeq]; group
    rw [this]
    exact mul_mem (inv_mem hhΩ) hgΩ
  rw [hgeq]
  have hle : Rts qA S ⊔ Tor K A r ≤ Rts qA S ⊔ (Tor K A r ⊔ Rot qA r) := sup_le_sup_left le_sup_left _
  refine mul_mem (hle hh) ?_
  by_cases htr : ∃ j, TrivOn S j
  · exact Subgroup.mem_sup_left (mem_Rts_of_fix_nontriv hreg hani hdim hr hnt htr hg'Ω hfix)
  · push Not at htr
    exact Subgroup.mem_sup_right (Subgroup.mem_sup_right (⟨hg'Ω, fun j => hfix j (htr j)⟩ : g' ∈ Rot qA r))

theorem derived_Csub_le (hreg : (polarBilin qA).Nondegenerate) (hani : qA.Anisotropic)
    (hdim : finrank K A = 2) (hr : r = 3) (hnt : ∃ j, ¬ TrivOn S j) :
    ⁅Csub qA S, Csub qA S⁆ ≤ Rts qA S := by
  have hr3 : 3 ≤ r := by omega
  have h1 := Subgroup.commutator_mono (Csub_le_sup hreg hani hdim hr hnt) (Csub_le_sup hreg hani hdim hr hnt)
  refine h1.trans (commutator_sup_le (sup_le Tor_le_normalizer_Rts Rot_le_normalizer_Rts) ?_)
  exact A_comm hreg hr3 hdim

end CFSG.RankThree.PartOne.K159H
