module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_4.A5Irr
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_4.A5Types
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_4.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise Matrix

private lemma exists_fixed_map {W : Type*} [CommGroup W] {L : Subgroup (MulAut W)}
    {I : Subgroup W} {g : MulAut W} (hnorm : ∀ z ∈ L, g * z * g⁻¹ ∈ L) {z : MulAut W}
    (hz : z ∈ L) (hz3 : orderOf z = 3) {u : W} (hu : u ∈ I) (hu1 : u ≠ 1) (hzu : z u = u) :
    ∃ z' ∈ L, orderOf z' = 3 ∧
      ∃ u' ∈ I.map g.toMonoidHom, u' ≠ 1 ∧ z' u' = u' := by
  refine ⟨g * z * g⁻¹, hnorm z hz, ?_, g u, Subgroup.mem_map.mpr ⟨u, hu, rfl⟩, ?_, ?_⟩
  · rw [show g * z * g⁻¹ = MulAut.conj g z from (MulAut.conj_apply g z).symm,
      MulEquiv.orderOf_eq, hz3]
  · intro h
    exact hu1 ((MulEquiv.map_eq_one_iff g).mp h)
  · show (g * z * g⁻¹) (g u) = g u
    simp [MulAut.mul_apply, hzu]

private lemma exists_fixed_of_secIsoOn {W : Type*} [CommGroup W] {L : Subgroup (MulAut W)}
    {A B : Subgroup W} {z : MulAut W} {u : W} (hsec : SecIsoOn L A ⊥ B ⊥) (hz : z ∈ L)
    (hu : u ∈ A) (hu1 : u ≠ 1) (hzu : z u = u) :
    ∃ v ∈ B, v ≠ 1 ∧ z v = v := by
  obtain ⟨-, -, -, -, -, -, β, hβB, hβbot, -, heq⟩ := hsec
  refine ⟨β ⟨u, hu⟩, hβB _, ?_, ?_⟩
  · intro h
    have hbot : ((⟨u, hu⟩ : ↥A) : W) ∈ (⊥ : Subgroup W) :=
      (hβbot ⟨u, hu⟩).mp (Subgroup.mem_bot.mpr h)
    exact hu1 (Subgroup.mem_bot.mp hbot)
  · have hmem : β ⟨u, hu⟩ * (z (β ⟨u, hu⟩))⁻¹ ∈ (⊥ : Subgroup W) :=
      heq z hz ⟨u, hu⟩ ⟨u, hu⟩ hzu.symm
    exact (mul_inv_eq_one.mp (Subgroup.mem_bot.mp hmem)).symm

theorem kA5Homog_holds : KA5Homog := by
  classical
  intro W _ _ hW Y L hLY hLn hL hfix hspan
  obtain ⟨-, htr⟩ := hspan
  let P : Subgroup W → Prop :=
    fun I => ∃ z ∈ L, orderOf z = 3 ∧ ∃ u ∈ I, u ≠ 1 ∧ z u = u
  have hclass : ∀ I ∈ irrSet L,
      BinaryNaturalSL L I ⊥ 2 2 ∨ AlternatingNatural L I ⊥ 5 := by
    intro I hI
    obtain ⟨hIrr, hmv⟩ := isIrrOn_of_mem_irrSet hfix hI
    exact (a5_irr_classification hW hL hIrr hmv).2
  have hNP : ∀ I ∈ irrSet L, BinaryNaturalSL L I ⊥ 2 2 → ¬ P I := by
    rintro I _ hI ⟨z, hz, hz3, u, hu, hu1, hzu⟩
    exact hu1 (eq_one_of_fixed_of_binaryNaturalSL hI hz hz3 hu hzu)
  have hOP : ∀ I ∈ irrSet L, AlternatingNatural L I ⊥ 5 → P I := by
    intro I _ hI
    exact exists_fixed_of_alternatingNatural hI
  have hnorm : ∀ g ∈ Y, ∀ z ∈ L, g * z * g⁻¹ ∈ L := by
    intro g hg z hz
    exact Subgroup.mem_subgroupOf.mp
      (hLn.conj_mem (⟨z, hLY hz⟩ : ↥Y) (Subgroup.mem_subgroupOf.mpr hz) ⟨g, hg⟩)
  have htrans : ∀ I ∈ irrSet L, ∀ J ∈ irrSet L, P I → P J := by
    rintro I hI J hJ ⟨z, hz, hz3, u, hu, hu1, hzu⟩
    obtain ⟨g, hgY, hsec⟩ := htr I hI J hJ
    rw [hfix, sup_bot_eq, sup_bot_eq] at hsec
    obtain ⟨z', hz'L, hz'3, u', hu'g, hu'1, hz'u'⟩ :=
      exists_fixed_map (hnorm g hgY) hz hz3 hu hu1 hzu
    exact ⟨z', hz'L, hz'3, exists_fixed_of_secIsoOn hsec hz'L hu'g hu'1 hz'u'⟩
  by_cases hO : ∃ I ∈ irrSet L, AlternatingNatural L I ⊥ 5
  · right
    intro I hI
    obtain ⟨J, hJ, hJO⟩ := hO
    have hPI : P I := htrans J hJ I hI (hOP J hJ hJO)
    rcases hclass I hI with hN | hO'
    · exact absurd hPI (hNP I hI hN)
    · exact hO'
  · left
    intro I hI
    rcases hclass I hI with hN | hO'
    · exact hN
    · exact absurd ⟨I, hI, hO'⟩ hO

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
