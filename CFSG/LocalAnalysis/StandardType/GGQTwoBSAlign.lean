module

public import CFSG.ClassicalInvolution.Phan.Defs
import CFSG.LocalAnalysis.StandardType.GGQTwoSixAlign
import CFSG.LocalAnalysis.StandardType.GGQTwoSixExt
import CFSG.LocalAnalysis.StandardType.GGQTwoSixGensWindows

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private theorem bsa_winEmb_univ_zero :
    (Finset.univ : Finset (Fin 2)).map
        (SixPoint.qTwoSixWinEmb (by norm_num : 0 + 2 ≤ 3)) =
      ({0, 1} : Finset (Fin 3)) := by
  ext a
  rw [Finset.mem_map]
  constructor
  · rintro ⟨b, -, rfl⟩
    fin_cases b <;> decide
  · intro ha
    rw [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact ⟨0, Finset.mem_univ _, by decide⟩
    · exact ⟨1, Finset.mem_univ _, by decide⟩

private theorem bsa_winEmb_univ_one :
    (Finset.univ : Finset (Fin 2)).map
        (SixPoint.qTwoSixWinEmb (by norm_num : 1 + 2 ≤ 3)) =
      ({1, 2} : Finset (Fin 3)) := by
  ext a
  rw [Finset.mem_map]
  constructor
  · rintro ⟨b, -, rfl⟩
    fin_cases b <;> decide
  · intro ha
    rw [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact ⟨0, Finset.mem_univ _, by decide⟩
    · exact ⟨1, Finset.mem_univ _, by decide⟩

private theorem bsa_range_blockEmb_zero :
    (blockEmb K 2 1 3 2 0 (by norm_num)).range =
      coordBlockSU K 2 1 ({0, 1} : Finset (Fin 3)) := by
  rw [SixPoint.qTwoSixWin_range (m := 3) (k := 2) (i := 0) (by norm_num),
    bsa_winEmb_univ_zero]

private theorem bsa_range_blockEmb_one :
    (blockEmb K 2 1 3 2 1 (by norm_num)).range =
      coordBlockSU K 2 1 ({1, 2} : Finset (Fin 3)) := by
  rw [SixPoint.qTwoSixWin_range (m := 3) (k := 2) (i := 1) (by norm_num),
    bsa_winEmb_univ_one]

private theorem bsa_map_range_of_comp_range {G : Type} [Group G]
    {A₁ A₂ : Su K 2 1 3 →* G} (hA₂ : Function.Injective A₂)
    {α : Su K 2 1 3 ≃* Su K 2 1 3} (hα : ∀ u, A₂ (α u) = A₁ u)
    {b : Su K 2 1 2 →* Su K 2 1 3}
    (hb : (A₁.comp b).range = (A₂.comp b).range) :
    b.range.map α.toMonoidHom = b.range := by
  apply Subgroup.map_injective hA₂
  rw [Subgroup.map_map]
  have he : A₂.comp α.toMonoidHom = A₁ := MonoidHom.ext fun u => hα u
  rw [he]
  rw [MonoidHom.range_comp, MonoidHom.range_comp] at hb
  exact hb

private theorem bsa_exists_three_align {G : Type} [Group G] {φ φ' : Su K 2 1 4 →* G}
    (hφ : Function.Injective (φ.comp (blockEmb K 2 1 4 3 1 (by norm_num))))
    (hφ' : Function.Injective (φ'.comp (blockEmb K 2 1 4 3 0 (by norm_num))))
    (h3 : (φ.comp (blockEmb K 2 1 4 3 1 (by norm_num))).range =
      (φ'.comp (blockEmb K 2 1 4 3 0 (by norm_num))).range)
    (h21 : (φ.comp (blockEmb K 2 1 4 2 1 (by norm_num))).range =
      (φ'.comp (blockEmb K 2 1 4 2 0 (by norm_num))).range)
    (h22 : (φ.comp (blockEmb K 2 1 4 2 2 (by norm_num))).range =
      (φ'.comp (blockEmb K 2 1 4 2 1 (by norm_num))).range) :
    ∃ α : Su K 2 1 3 ≃* Su K 2 1 3,
      (∀ u, (φ'.comp (blockEmb K 2 1 4 3 0 (by norm_num))) (α u) =
        (φ.comp (blockEmb K 2 1 4 3 1 (by norm_num))) u) ∧
      (coordBlockSU K 2 1 ({0, 1} : Finset (Fin 3))).map α.toMonoidHom =
        coordBlockSU K 2 1 ({0, 1} : Finset (Fin 3)) ∧
      (coordBlockSU K 2 1 ({1, 2} : Finset (Fin 3))).map α.toMonoidHom =
        coordBlockSU K 2 1 ({1, 2} : Finset (Fin 3)) := by
  let e₁ : Su K 2 1 3 →* Su K 2 1 4 := blockEmb K 2 1 4 3 1 (by norm_num)
  let e₂ : Su K 2 1 3 →* Su K 2 1 4 := blockEmb K 2 1 4 3 0 (by norm_num)
  let A₁ : Su K 2 1 3 →* G := φ.comp e₁
  let A₂ : Su K 2 1 3 →* G := φ'.comp e₂
  let b0 : Su K 2 1 2 →* Su K 2 1 3 := blockEmb K 2 1 3 2 0 (by norm_num)
  let b1 : Su K 2 1 2 →* Su K 2 1 3 := blockEmb K 2 1 3 2 1 (by norm_num)
  obtain ⟨α, hα⟩ := exists_mulEquiv_comp_eq hφ hφ' h3
  have hcomp01 : (blockEmb K 2 1 4 2 1 (by norm_num) : Su K 2 1 2 →* Su K 2 1 4) =
      e₁.comp b0 := by rw [blockEmb_comp]
  have hcomp00 : (blockEmb K 2 1 4 2 0 (by norm_num) : Su K 2 1 2 →* Su K 2 1 4) =
      e₂.comp b0 := by rw [blockEmb_comp]
  have hcomp11 : (blockEmb K 2 1 4 2 2 (by norm_num) : Su K 2 1 2 →* Su K 2 1 4) =
      e₁.comp b1 := by rw [blockEmb_comp]
  have hcomp10 : (blockEmb K 2 1 4 2 1 (by norm_num) : Su K 2 1 2 →* Su K 2 1 4) =
      e₂.comp b1 := by rw [blockEmb_comp]
  have hb0 : (A₁.comp b0).range = (A₂.comp b0).range := by
    have h := h21
    rw [hcomp01, hcomp00] at h
    simpa only [A₁, A₂, MonoidHom.comp_assoc] using h
  have hb1 : (A₁.comp b1).range = (A₂.comp b1).range := by
    have h := h22
    rw [hcomp11, hcomp10] at h
    simpa only [A₁, A₂, MonoidHom.comp_assoc] using h
  refine ⟨α, hα, ?_, ?_⟩
  · rw [← bsa_range_blockEmb_zero]
    exact bsa_map_range_of_comp_range hφ' hα hb0
  · rw [← bsa_range_blockEmb_one]
    exact bsa_map_range_of_comp_range hφ' hα hb1

theorem exists_mulEquiv_comp_blockEmb_eq (hK : Nat.card K = 4) {G : Type} [Group G]
    {φ φ' : Su K 2 1 4 →* G}
    (hφ : Function.Injective (φ.comp (blockEmb K 2 1 4 3 1 (by norm_num))))
    (hφ' : Function.Injective (φ'.comp (blockEmb K 2 1 4 3 0 (by norm_num))))
    (h3 : (φ.comp (blockEmb K 2 1 4 3 1 (by norm_num))).range =
      (φ'.comp (blockEmb K 2 1 4 3 0 (by norm_num))).range)
    (h21 : (φ.comp (blockEmb K 2 1 4 2 1 (by norm_num))).range =
      (φ'.comp (blockEmb K 2 1 4 2 0 (by norm_num))).range)
    (h22 : (φ.comp (blockEmb K 2 1 4 2 2 (by norm_num))).range =
      (φ'.comp (blockEmb K 2 1 4 2 1 (by norm_num))).range) :
    ∃ β : Su K 2 1 4 ≃* Su K 2 1 4,
      (∀ (k i : ℕ) (h : i + k ≤ 4),
        (blockEmb K 2 1 4 k i h).range.map β.toMonoidHom = (blockEmb K 2 1 4 k i h).range) ∧
      φ.comp (blockEmb K 2 1 4 3 1 (by norm_num)) =
        (φ'.comp β.toMonoidHom).comp (blockEmb K 2 1 4 3 0 (by norm_num)) := by
  classical
  obtain ⟨α, hα, h01, h12⟩ := bsa_exists_three_align hφ hφ' h3 h21 h22
  obtain ⟨d, σ, hd⟩ := SixPoint.qTwoSix_lem62 hK α h01 h12
  obtain ⟨β, hβblocks, hβrestrict⟩ := SixPoint.qTwoSix_ext hK d σ
  refine ⟨β, ?_, ?_⟩
  · intro k i h
    rw [SixPoint.qTwoSixWin_range (m := 4) (k := k) (i := i) h, hβblocks]
  · ext u
    have he : β (blockEmb K 2 1 4 3 0 (by norm_num) u) =
        blockEmb K 2 1 4 3 0 (by norm_num) (α u) := by
      apply Subtype.ext
      apply Units.ext
      rw [hβrestrict, coe_coe_blockEmb, hd u]
    change (φ.comp (blockEmb K 2 1 4 3 1 (by norm_num))) u =
      φ' (β (blockEmb K 2 1 4 3 0 (by norm_num) u))
    rw [he]
    exact (hα u).symm

end CFSG.StandardType.QTwo

end
