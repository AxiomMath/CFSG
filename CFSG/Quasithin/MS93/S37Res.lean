module

public import CFSG.Quasithin.MS93.S37Ex

public section

namespace CFSG.Quasithin.MS93.S37

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.MSP
open CFSG.QuasithinUnique CFSG.Quasithin.MS93.S36 CFSG.Quasithin.Vol2
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

variable {G : Type} [Group G]

section Restr

variable {T S : Subgroup G}

theorem mem_of_tImage_eq {θ : MulAut ↥T} (hS : S ≤ T) (h : tImage θ S = S) {s : G}
    (hs : s ∈ S) : ((θ ⟨s, hS hs⟩ : ↥T) : G) ∈ S := by
  have : ((θ ⟨s, hS hs⟩ : ↥T) : G) ∈ tImage θ S := mem_tImage.2 ⟨s, hS hs, hs, rfl⟩
  rwa [h] at this

theorem tImage_inv_eq {θ : MulAut ↥T} (hS : S ≤ T) (h : tImage θ S = S) : tImage θ⁻¹ S = S := by
  have := tImage_inv_tImage' θ hS
  rwa [h] at this

@[expose] noncomputable def restr (θ : MulAut ↥T) (hS : S ≤ T) (h : tImage θ S = S) :
    MulAut ↥S where
  toFun s := ⟨θ ⟨s, hS s.2⟩, mem_of_tImage_eq hS h s.2⟩
  invFun s := ⟨θ⁻¹ ⟨s, hS s.2⟩, mem_of_tImage_eq hS (tImage_inv_eq hS h) s.2⟩
  left_inv s := Subtype.ext (by simp)
  right_inv s := Subtype.ext (by simp)
  map_mul' s t := Subtype.ext (by
    show ((θ ⟨(s : G) * t, hS (s * t).2⟩ : ↥T) : G) =
      ((θ ⟨s, hS s.2⟩ : ↥T) : G) * ((θ ⟨t, hS t.2⟩ : ↥T) : G)
    rw [show (⟨(s : G) * t, hS (s * t).2⟩ : ↥T) = ⟨s, hS s.2⟩ * ⟨t, hS t.2⟩ from rfl, map_mul]
    rfl)

theorem tImage_restr (θ : MulAut ↥T) (hS : S ≤ T) (h : tImage θ S = S) {K : Subgroup G}
    (hK : K ≤ S) : tImage (restr θ hS h) K = tImage θ K := by
  ext x
  rw [mem_tImage, mem_tImage]
  constructor
  · rintro ⟨y, hyS, hyK, rfl⟩
    exact ⟨y, hS hyS, hyK, rfl⟩
  · rintro ⟨y, hyT, hyK, rfl⟩
    exact ⟨y, hK hyK, hyK, rfl⟩

theorem tImage_restr_inv (θ : MulAut ↥T) (hS : S ≤ T) (h : tImage θ S = S) {K : Subgroup G}
    (hK : K ≤ S) : tImage (restr θ hS h)⁻¹ K = tImage θ⁻¹ K := by
  ext x
  rw [mem_tImage, mem_tImage]
  constructor
  · rintro ⟨y, hyS, hyK, rfl⟩
    exact ⟨y, hS hyS, hyK, rfl⟩
  · rintro ⟨y, hyT, hyK, rfl⟩
    exact ⟨y, hK hyK, hyK, rfl⟩

end Restr

variable [Finite G]

namespace Cfg

variable {M T L : Subgroup G} {F : Type} [Field F] [Fintype F] (C : Cfg M T L F)
include C

theorem partner_relIndex_eq (θ : MulAut ↥(T1 M T L)) (hcrit : ¬ Uq M T L ≤ Qt M θ) :
    (pCoreOf 2 M).relIndex (Ut M T L θ⁻¹) = (pCoreOf 2 M).relIndex (Ut M T L θ) := by
  have hU : Ut M T L θ ≤ T1 M T L := tImage_le θ _
  have hU' : Ut M T L θ⁻¹ ≤ T1 M T L := tImage_le θ⁻¹ _
  rcases le_total ((pCoreOf 2 M).relIndex (Ut M T L θ⁻¹)) ((pCoreOf 2 M).relIndex (Ut M T L θ))
    with hle | hle
  · exact (C.relIndex_inv_eq C.pCore_le_T1 T1_le_T θ hcrit hU hU' hle).1
  · have hcrit' := C.crit_inv C.pCore_le_T1 T1_le_T θ hcrit
    have h := C.relIndex_inv_eq C.pCore_le_T1 T1_le_T θ⁻¹ hcrit' hU'
      (by rw [inv_inv]; exact hU) (by rw [inv_inv]; exact hle)
    rw [inv_inv] at h
    exact h.1.symm

theorem partner_cases (θ : MulAut ↥(T1 M T L)) (hcrit : ¬ Uq M T L ≤ Qt M θ) :
    (∃ p : Submodule F (V4 F), IsPoint p ∧ C.rhoIm (Ut M T L θ) = xPoint p) ∨
      (IsLine (fixSp (C.rhoIm (Ut M T L θ))) ∧
        C.rhoIm (Ut M T L θ) ≤ qLine (fixSp (C.rhoIm (Ut M T L θ)))) :=
  C.case_I_or_II C.pCore_le_T1 T1_le_T θ hcrit (tImage_le θ _)
    (C.partner_relIndex_eq θ hcrit).le

end Cfg

end CFSG.Quasithin.MS93.S37
