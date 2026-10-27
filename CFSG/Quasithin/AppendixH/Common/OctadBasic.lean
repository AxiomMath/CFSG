module

public import CFSG.Milestones.ASVolI.H13
public import CFSG.Monster.B.Cbar.Octads

public section

open scoped Pointwise

namespace CFSG.ASVolI.AppH

open CFSG.ASVolI.ChH CFSG.Monster.Code CFSG.Quasithin.H.Mathieu

@[expose] def octStab (O : Finset (Fin 24)) : Subgroup S24 :=
  M24g ⊓ MulAction.stabilizer S24 O

theorem mem_octStab_iff {O : Finset (Fin 24)} {g : S24} :
    g ∈ octStab O ↔ g ∈ M24g ∧ g • O = O :=
  Iff.rfl

theorem isOctad_smul {σ : S24} (hσ : σ ∈ M24g) {O : Finset (Fin 24)} (h : IsOctad O) :
    IsOctad (σ • O) :=
  ⟨by rw [Finset.card_smul_finset]; exact h.1, by
    rw [smul_finset_eq_map, ← permAct_eY]
    exact (preserves_cocode hσ).2 _ h.2⟩

theorem octStab_smul {σ : S24} (hσ : σ ∈ M24g) (O : Finset (Fin 24)) :
    octStab (σ • O) = (octStab O).map (MulAut.conj σ).toMonoidHom := by
  ext g
  rw [mem_octStab_iff, Subgroup.mem_map]
  constructor
  · rintro ⟨hgM, hgO⟩
    refine ⟨σ⁻¹ * g * σ, ?_, ?_⟩
    · rw [mem_octStab_iff]
      refine ⟨M24g.mul_mem (M24g.mul_mem (M24g.inv_mem hσ) hgM) hσ, ?_⟩
      rw [mul_smul, mul_smul, hgO]
      simp
    · show MulAut.conj σ (σ⁻¹ * g * σ) = g
      rw [MulAut.conj_apply]
      group
  · rintro ⟨h, ⟨hhM, hhO⟩, hgh⟩
    rw [← hgh]
    refine ⟨?_, ?_⟩
    · show MulAut.conj σ h ∈ M24g
      rw [MulAut.conj_apply]
      exact M24g.mul_mem (M24g.mul_mem hσ hhM) (M24g.inv_mem hσ)
    · show MulAut.conj σ h • (σ • O) = σ • O
      rw [MulAut.conj_apply, mul_smul, mul_smul, inv_smul_smul, hhO]

theorem isOctad_iff_mem_octads {O : Finset (Fin 24)} : IsOctad O ↔ O ∈ octads := by
  constructor
  · intro hO
    have hsupp : suppFin (Multiplicative.toAdd (eY O)) = O := by
      ext i
      rw [mem_suppFin, toAdd_eY]
      by_cases hi : i ∈ O <;> simp [hi]
    refine mem_octads.2 ⟨Multiplicative.toAdd (eY O), (mem_golayC_iff' _).1 hO.2, ?_, hsupp⟩
    rw [← card_suppFin, hsupp, hO.1]
  · intro hO
    obtain ⟨x, hxC, hxwt, hxsupp⟩ := mem_octads.1 hO
    refine ⟨?_, ?_⟩
    · rw [← hxsupp, card_suppFin, hxwt]
    · have heq : Multiplicative.toAdd (eY O) = x := by
        funext i
        rw [toAdd_eY]
        rcases h13_zmod2_cases (x i) with h0 | h1
        · have hi : i ∉ O := by
            rw [← hxsupp, mem_suppFin]
            simp [h0]
          simp [hi, h0]
        · have hi : i ∈ O := by
            rw [← hxsupp, mem_suppFin]
            simp [h1]
          simp [hi, h1]
      rw [mem_golayC_iff', heq]
      exact hxC

@[expose] def octadB0 : Finset (Fin 24) := Finset.univ.filter fun i => B 0 i ≠ 0

theorem isOctad_octadB0 : IsOctad octadB0 := by
  rw [isOctad_iff_mem_octads]
  exact mem_octads.2 ⟨B 0, B_mem_C 0, wt_B 0, rfl⟩

end CFSG.ASVolI.AppH
