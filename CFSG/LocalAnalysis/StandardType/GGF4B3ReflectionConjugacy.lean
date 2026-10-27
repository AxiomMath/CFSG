module

public import CFSG.LocalAnalysis.StandardType.GGF4OrigRep

public section

namespace CFSG.StandardType.F4Model

variable {W : Type} [Group W]

theorem F4Rep.exists_conj_of_b3 (R : F4Rep W) (b : Fin 3 → W)
    (hb : ∀ j, R.IsRefl (b j))
    (o01 : orderOf (b 0 * b 1) = 3)
    (o12 : orderOf (b 1 * b 2) = 4)
    (o02 : orderOf (b 0 * b 2) = 2)
    {t : W} (ht : R.IsRefl t) :
    ∃ (j : Fin 3) (g : W), g * b j * g⁻¹ = t := by
  obtain ⟨gB, hB⟩ := R.classify (hb 0) (hb 1) (hb 2) o01 o12 o02
  obtain ⟨gT, T, hT, hTarget⟩ := R.stage1_conj ht
  have key {z : W} (hz : gB * z * gB⁻¹ = gT * t * gT⁻¹) :
      (gT⁻¹ * gB) * z * (gT⁻¹ * gB)⁻¹ = t := by
    calc
      _ = gT⁻¹ * (gB * z * gB⁻¹) * gT := by group
      _ = gT⁻¹ * (gT * t * gT⁻¹) * gT := by rw [hz]
      _ = t := by group
  rcases hT with rfl | rfl
  · rcases hB with hB | hB
    · exact ⟨1, gT⁻¹ * gB, key (hB.2.1.trans hTarget.symm)⟩
    · exact ⟨2, gT⁻¹ * gB, key (hB.2.2.trans hTarget.symm)⟩
  · rcases hB with hB | hB
    · exact ⟨2, gT⁻¹ * gB, key (hB.2.2.trans hTarget.symm)⟩
    · exact ⟨1, gT⁻¹ * gB, key (hB.2.1.trans hTarget.symm)⟩

theorem exists_conj_b3_reflection (cs : CoxeterSystem CoxeterMatrix.F₄ W)
    (b : Fin 3 → W) (hb : ∀ j, cs.IsReflection (b j))
    (o01 : orderOf (b 0 * b 1) = 3)
    (o12 : orderOf (b 1 * b 2) = 4)
    (o02 : orderOf (b 0 * b 2) = 2)
    {t : W} (ht : cs.IsReflection t) :
    ∃ (j : Fin 3) (g : W), g * b j * g⁻¹ = t := by
  obtain ⟨R, hRs⟩ := exists_f4Rep cs
  exact R.exists_conj_of_b3 b (fun j => (F4Rep.isRefl_iff hRs).2 (hb j))
    o01 o12 o02 ((F4Rep.isRefl_iff hRs).2 ht)

end CFSG.StandardType.F4Model

end
