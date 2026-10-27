module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3e7Tc
public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3e7Link

public section

namespace CFSG.StandardType.LevTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem levTwoS3e7_patSetFin_eq (m : ℕ) : levTwoS3e7_patSetFin m = levTwoS3e7_patSet m := by
  have hlen : levTwoS3e7_rootVecs.length = 126 := by
    simp [levTwoS3e7_rootVecs, levTwoS3e7_roots_length]
  have hget : ∀ i : Fin levTwoS3e7_rootVecs.length, levTwoS3e7_rootVecs.get i =
      levTwoS3e7_vec (Tag.rank Tag.E7) (levTwoS3e7_roots.getD i.val []) := by
    intro i
    rw [← List.getD_eq_get levTwoS3e7_rootVecs 0 i]
    exact levTwoS3u_getD_map (Tag.rank Tag.E7) levTwoS3e7_roots i.val
  ext β
  simp only [levTwoS3e7_patSetFin, levTwoS3e7_patSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨i, rfl, hb⟩
    exact ⟨i.val, by rw [← hlen]; exact i.2, (hget i).symm, hb⟩
  · rintro ⟨i, hi, rfl, hb⟩
    exact ⟨⟨i, by rw [hlen]; exact hi⟩, hget ⟨i, by rw [hlen]; exact hi⟩, hb⟩

theorem levTwoS3e7_excFinite :
    ExcFinite Tag.E7 kacE7 := by
  intro D l hD hirr hrank
  obtain ⟨hm, rfl, hpart⟩ := levTwoS3e7_mask_cases D l hD hirr hrank
  rw [hpart, ← levTwoS3e7_patSetFin_eq]
  have hm' : levTwoS3e7_maskOf D = 63 ∨ levTwoS3e7_maskOf D = 123 ∨ levTwoS3e7_maskOf D = 126 ∨
      levTwoS3e7_maskOf D = 127 ∨ levTwoS3e7_maskOf D = 250 ∨ levTwoS3e7_maskOf D = 251 ∨
      levTwoS3e7_maskOf D = 252 ∨ levTwoS3e7_maskOf D = 254 := by
    simpa [levTwoS3e7_survivors] using hm
  rcases hm' with h | h | h | h | h | h | h | h <;> rw [h]
  · exact levTwoS3e7_tcRoot_63
  · exact levTwoS3e7_tcRoot_123
  · exact levTwoS3e7_tcRoot_126
  · exact levTwoS3e7_tcRoot_127
  · exact levTwoS3e7_tcRoot_250
  · exact levTwoS3e7_tcRoot_251
  · exact levTwoS3e7_tcRoot_252
  · exact levTwoS3e7_tcRoot_254

end CFSG.StandardType.LevTwo
