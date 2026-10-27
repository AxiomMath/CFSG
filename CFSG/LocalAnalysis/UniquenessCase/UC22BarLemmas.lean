module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
public import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem barImage_mono {M K L : Subgroup G} (h : K ≤ L) :
    barImage M K ≤ barImage M L := by
  intro q hq
  obtain ⟨m, hm, rfl⟩ := uc22p21c_mem_barImage.1 hq
  exact uc22p21c_mem_barImage.2 ⟨m, h hm, rfl⟩

theorem barImage_barPreimage (M : Subgroup G) (Y : Subgroup (Bar2 M)) :
    barImage M (barPreimage M Y) = Y := by
  refine le_antisymm ?_ ?_
  · intro q hq
    obtain ⟨m, hm, rfl⟩ := uc22p21c_mem_barImage.1 hq
    simpa using (uc22p21c_mem_barPreimage.1 hm).2
  · intro q hq
    obtain ⟨m, rfl⟩ := uc22p21c_pi_surjective M q
    exact uc22p21c_mem_barImage.2
      ⟨m, uc22p21c_mem_barPreimage.2 ⟨m.2, hq⟩, rfl⟩

theorem barPreimage_mono {M : Subgroup G} {Y Y' : Subgroup (Bar2 M)} (h : Y ≤ Y') :
    barPreimage M Y ≤ barPreimage M Y' :=
  Subgroup.map_mono (Subgroup.comap_mono h)

theorem pCoreOf_le_barPreimage (M : Subgroup G) (Y : Subgroup (Bar2 M)) :
    CFSG.Open.pCoreOf 2 M ≤ barPreimage M Y := by
  intro x hx
  obtain ⟨y, hy, hyx⟩ := hx
  have hxM : x ∈ M := by rw [← hyx]; exact y.2
  refine uc22p21c_mem_barPreimage.2 ⟨hxM, ?_⟩
  have h1 : uc22p21cPi M y = 1 := (QuotientGroup.eq_one_iff y).2 hy
  have hx1 : uc22p21cPi M ⟨x, hxM⟩ = 1 := by
    rw [show (⟨x, hxM⟩ : ↥M) = y from Subtype.ext hyx.symm, h1]
  rw [hx1]
  exact Subgroup.one_mem _

theorem closure_le_barPreimage {M S : Subgroup G} {b : G}
    (hSM : S ≤ M) (hbM : b ∈ M) {C : Subgroup (Bar2 M)} (hC : C.Normal)
    (hbC : uc22p21cPi M ⟨b, hbM⟩ ∈ C) :
    Subgroup.closure {x : G | ∃ s ∈ S, x = ⁅s, b⁆} ≤ barPreimage M C := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨s, hs, rfl⟩
  have hsM : s ∈ M := hSM hs
  have hxM : ⁅s, b⁆ ∈ M := by
    rw [commutatorElement_def]
    exact M.mul_mem (M.mul_mem (M.mul_mem hsM hbM) (M.inv_mem hsM)) (M.inv_mem hbM)
  refine uc22p21c_mem_barPreimage.2 ⟨hxM, ?_⟩
  have hconj : uc22p21cPi M ⟨s, hsM⟩ * uc22p21cPi M ⟨b, hbM⟩ *
      (uc22p21cPi M ⟨s, hsM⟩)⁻¹ ∈ C := hC.conj_mem _ hbC _
  have hx : uc22p21cPi M ⟨s, hsM⟩ * uc22p21cPi M ⟨b, hbM⟩ *
      (uc22p21cPi M ⟨s, hsM⟩)⁻¹ * (uc22p21cPi M ⟨b, hbM⟩)⁻¹ ∈ C :=
    C.mul_mem hconj (C.inv_mem hbC)
  have hmap : uc22p21cPi M ⟨⁅s, b⁆, hxM⟩ =
      ⁅uc22p21cPi M ⟨s, hsM⟩, uc22p21cPi M ⟨b, hbM⟩⁆ := by
    rw [← map_commutatorElement (uc22p21cPi M) (⟨s, hsM⟩ : ↥M) (⟨b, hbM⟩ : ↥M)]
    congr 1
  rw [hmap, commutatorElement_def]
  exact hx

theorem le_pCoreOf_of_barImage_eq_bot {M R : Subgroup G} (hRM : R ≤ M)
    (h : barImage M R = ⊥) : R ≤ CFSG.Open.pCoreOf 2 M := by
  intro x hx
  have hxM : x ∈ M := hRM hx
  have hxbar : uc22p21cPi M ⟨x, hxM⟩ ∈ barImage M R :=
    uc22p21c_mem_barImage.2 ⟨⟨x, hxM⟩, hx, rfl⟩
  rw [h] at hxbar
  have hxbar1 : uc22p21cPi M ⟨x, hxM⟩ = 1 := by simpa using hxbar
  exact (CFSG.mem_openPCoreOf_iff ⟨x, hxM⟩).2 ((QuotientGroup.eq_one_iff _).1 hxbar1)

end CFSG.LocalAnalysis.UniquenessCase.UC22
