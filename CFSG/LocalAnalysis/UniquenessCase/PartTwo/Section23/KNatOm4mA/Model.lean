module

public import CFSG.Quasithin.Vol2.Ch6H11Main
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatOm4mA.Basic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatOm4mA.Inner
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatOm4mA.Outer
import CFSG.Quasithin.Background.RonanE42Small

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NatOm4mA

open CFSG.Quasithin
open CFSG.Quasithin.H13.H11M (VH NH LH UH SigInv exists_conj_stdH)

variable {F : Type} [Field F] [CharP F 2] {a : ℕ} (hσ : SigInv a F)

theorem not_mem_aSet_of_le_normalizer [Fintype F] (ha : 1 ≤ a)
    (hF : Fintype.card F = 2 ^ (2 * a)) {X : Subgroup (MulAut (VH a F))} (hX : X ≤ NH hσ)
    (A : Subgroup (MulAut (VH a F))) : A ∉ E3.aSet (a + 1) X := by
  intro hA
  obtain ⟨g, hgL, hstd⟩ := exists_conj_stdH hσ ha hF hA.2.2.1
  have hgN : g ∈ NH hσ := Subgroup.le_normalizer hgL
  have hA' := conj_mem_aSet hA g
  have hX' : X.map (MulAut.conj g).toMonoidHom ≤ NH hσ := by
    rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (NH hσ).mul_mem ((NH hσ).mul_mem hgN (hX hx)) ((NH hσ).inv_mem hgN)
  have hA'N : A.map (MulAut.conj g).toMonoidHom ≤ NH hσ := hA'.1.trans hX'
  by_cases hAL : A.map (MulAut.conj g).toMonoidHom ≤ LH hσ
  · have hAU : A.map (MulAut.conj g).toMonoidHom ≤ UH hσ := fun x hx => hstd ⟨hx, hAL hx⟩
    obtain ⟨B, hB, hm, hfix⟩ := exists_witness_inner hσ ha hF hAU hA'.2.1
    exact not_mem_aSet_succ_of_witness ⟨B, hB, hm, hfix⟩ hA'
  · obtain ⟨B, hB, hm, hfix⟩ := exists_witness_outer hσ ha hF hA'N hA'.2.2.1 hstd hAL
    exact not_mem_aSet_succ_of_witness ⟨B, hB, hm, hfix⟩ hA'

theorem aParam_le_of_le_normalizer [Fintype F] (ha : 1 ≤ a)
    (hF : Fintype.card F = 2 ^ (2 * a)) {X : Subgroup (MulAut (VH a F))} (hX : X ≤ NH hσ) :
    E3.aParam X ≤ a :=
  CFSG.Quasithin.RonanE42.aParam_le_of_aSet_empty X a
    (fun A => not_mem_aSet_of_le_normalizer hσ ha hF hX A)

end CFSG.LocalAnalysis.UniquenessCase.UC22.NatOm4mA
