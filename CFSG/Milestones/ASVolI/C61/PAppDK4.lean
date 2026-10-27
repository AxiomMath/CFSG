module

public import CFSG.Milestones.ASVolI.C61.PAppDK3

public section

namespace CFSG.QuasithinUnique.burnsideC56_P.AppD

open CFSG.QuasithinUnique.AppD

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.QuasithinUnique.burnsideC56_P.DoubleA3
open CFSG.QuasithinUnique.DoubleA3 hiding A3A3 A3A3.V_isPGroup A3A3.blockU0_eq A3A3.center_L0
  A3A3.comm_elem A3A3.conjJoin_ne A3A3.conj_cases A3A3.inf_Ls A3A3.inf_S_L0 A3A3.isA4 A3A3.isA4s
  A3A3.isShort A3A3.isSylowTwoOf_V A3A3.le_normalizer_V A3A3.normalizer_conjR exists_A3A3
open CFSG.QuasithinUnique.A5.Delta5 Equiv

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {s : G}

namespace A3x
open CFSG.QuasithinUnique.AppD.A3x

variable {h : A3A3 T M H S L s} (sp : Spec h)

include sp in
theorem piS_im_B : (piS sp).im (baum S) = Estd := by
  apply le_antisymm
  · intro σ hσ
    obtain ⟨y, hy, rfl⟩ := (PiS.mem_im _).1 hσ
    exact (mem_Estd _).2 (piS_B_mem sp hy)
  · intro σ hσ
    have hσ' : σ ∈ Eset := (mem_Estd σ).1 hσ
    obtain ⟨⟨b₁, hb₁, hb₁1, hb₁2⟩, ⟨b₂, hb₂, hb₂1, hb₂2⟩⟩ := exists_swap_elements sp
    have m1 : Equiv.swap 0 1 ∈ (piS sp).im (baum S) := by
      have := (piS sp).pi_mem_im (K := baum S) (y := ⟨b₁, baum_le_S' S hb₁⟩) hb₁
      rwa [piS_swap01 sp hb₁ hb₁1 hb₁2] at this
    have m2 : Equiv.swap 2 3 ∈ (piS sp).im (baum S) := by
      have := (piS sp).pi_mem_im (K := baum S) (y := ⟨b₂, baum_le_S' S hb₂⟩) hb₂
      rwa [piS_swap23 sp hb₂ hb₂1 hb₂2] at this
    simp only [Eset, Finset.mem_insert, Finset.mem_singleton] at hσ'
    rcases hσ' with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact m1
    · exact m2
    · exact mul_mem m1 m2

include sp in
theorem piS_im_S : (piS sp).im S = Dstd := by
  apply le_antisymm
  · intro σ hσ
    obtain ⟨y, -, rfl⟩ := (PiS.mem_im _).1 hσ
    exact (mem_Dstd _).2 (piS_mem_Dset sp y)
  · intro τ hτ
    have hτ' : τ ∈ Dset := (mem_Dstd τ).1 hτ
    have hB : ∀ e ∈ Eset, e ∈ (piS sp).im S := fun e he =>
      (piS sp).im_mono (baum_le_S' S) ((piS_im_B sp).symm ▸ (mem_Estd e).2 he)
    have hσ₀ : (piS sp).π ⟨s, h.s_mem⟩ ∈ (piS sp).im S :=
      (piS sp).pi_mem_im (K := S) h.s_mem
    rcases Dset_cosets _ (piS_mem_Dset sp ⟨s, h.s_mem⟩) (piS_s_not_mem sp) τ hτ' with h1 | h1
    · exact hB τ h1
    · have := mul_mem (hB _ h1) hσ₀
      rwa [inv_mul_cancel_right] at this

end A3x

end CFSG.QuasithinUnique.burnsideC56_P.AppD
