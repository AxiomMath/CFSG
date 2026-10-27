module

public import CFSG.GroupTheory.IsSylowOfMapOfKerPrimeNotDvd
public import CFSG.LocalAnalysis.UniquenessCase.UC6S19
public import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPL
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WS6
public import CFSG.LocalAnalysis.UniquenessCase.UC6End
public import CFSG.LocalAnalysis.UniquenessCase.UC6S35

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG
open scoped commutatorElement
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor)
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
variable {G : Type} [Group G] [Finite G] {D : Data G}

theorem normalizer_le_M_of_weaklyClosed {Z P U : Subgroup G} {M : Subgroup G}
    (hWC : IsWeaklyClosedIn Z P)
    (hNZ : Subgroup.normalizer (Z : Set G) ≤ M)
    (hZU : Z ≤ U) (hUP : U ≤ P) :
    Subgroup.normalizer (U : Set G) ≤ M := by
  intro g hg
  apply hNZ
  rw [Subgroup.mem_normalizer_iff]
  have hconj_le : CFSG.conjugate Z g ≤ P := by
    have h1 : CFSG.conjugate Z g ≤ CFSG.conjugate U g := by
      simpa [CFSG.conjugate] using Subgroup.map_mono (f := ((MulAut.conj g)⁻¹).toMonoidHom) hZU
    have h2 : CFSG.conjugate U g = U := by
      ext x
      rw [CFSG.mem_conjugate_iff]
      exact (Subgroup.mem_normalizer_iff.mp hg x).symm
    rw [h2] at h1
    exact h1.trans hUP
  have hZeq : CFSG.conjugate Z g = Z := hWC g hconj_le
  intro z
  constructor
  · intro hz
    have hmem : z ∈ CFSG.conjugate Z g := by rw [hZeq]; exact hz
    exact (CFSG.mem_conjugate_iff Z g z).mp hmem
  · intro hz
    have hmem : z ∈ CFSG.conjugate Z g := (CFSG.mem_conjugate_iff Z g z).mpr hz
    rwa [hZeq] at hmem

theorem twoCoreCen_normal_in_cen_inf_M {M : Subgroup G} {e : G}
    (hQ : M ≤ Subgroup.normalizer ((CFSG.Open.pCoreOf 2 M : Subgroup G) : Set G)) :
    ((Subgroup.centralizer ({e} : Set G) ⊓ CFSG.Open.pCoreOf 2 M).subgroupOf
      (Subgroup.centralizer ({e} : Set G) ⊓ M)).Normal := by
  classical
  let C : Subgroup G := Subgroup.centralizer ({e} : Set G)
  let Q : Subgroup G := CFSG.Open.pCoreOf 2 M
  let W : Subgroup G := C ⊓ Q
  let K : Subgroup G := C ⊓ M
  have hWleK : W ≤ K := fun w hw => ⟨hw.1, Subgroup.map_subtype_le _ hw.2⟩
  refine ⟨fun w hw k => ?_⟩
  have hwW : w.1 ∈ W := Subgroup.mem_subgroupOf.mp hw
  have hkC : k.1 ∈ C := k.2.1
  have hkM : k.1 ∈ M := k.2.2
  refine Subgroup.mem_subgroupOf.mpr ⟨?_, ?_⟩
  · exact C.mul_mem (C.mul_mem hkC hwW.1) (C.inv_mem hkC)
  · exact (Subgroup.mem_normalizer_iff.mp (hQ hkM) w.1).1 hwW.2

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
