module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aAmE
public import CFSG.Quasithin.Vol2.Ch11SecQ9aCartE

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {Q : Type} [Group Q]

theorem exists_fpf_of_isPSL [Finite Q] (hQ : IsPSL 3 2 2 Q) {S P : Subgroup Q}
    (hS : QuasithinUnique.IsSylowTwoOf S ⊤) (hP1 : P ≠ ⊥) (hPt : P ≠ ⊤) (hPp : ⁅P, P⁆ = P)
    (hSP : S ≤ Subgroup.normalizer (P : Set Q)) :
    pCoreOf 2 P ≠ ⊥ ∧ ∃ y ∈ P, orderOf y = 3 ∧ ∀ b ∈ pCoreOf 2 P, y * b * y⁻¹ = b → b = 1 := by
  obtain ⟨K, _, _, _, φ, hK, hφS, -, -⟩ :=
    CFSG.QuasithinUnique.Setup.X7a.even_rank_two_residual_linear hQ hS
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  have hPm1 : P.map φ.toMonoidHom ≠ ⊥ := fun h =>
    hP1 ((Subgroup.map_eq_bot_iff_of_injective _ φ.injective).mp h)
  have hPmp : ⁅P.map φ.toMonoidHom, P.map φ.toMonoidHom⁆ = P.map φ.toMonoidHom := by
    rw [← Subgroup.map_commutator, hPp]
  have hSPm : projUnitriangular 3 K ≤
      Subgroup.normalizer ((P.map φ.toMonoidHom : Subgroup _) : Set (projectiveSL 3 K)) := by
    rw [← hφS, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hSP
  have hPmt : P.map φ.toMonoidHom ≠ ⊤ := fun h => hPt (by
    apply Subgroup.map_injective (f := φ.toMonoidHom) φ.injective
    rw [h, Subgroup.map_top_of_surjective _ φ.surjective])
  obtain ⟨j, hj⟩ : ∃ j, P.map φ.toMonoidHom = C11P9A.parab34 K j := by
    rcases C11P9A.classify_std hK4 _ hPm1 hPmp hSPm with h | h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact absurd h hPmt
  obtain ⟨y₀, hy₀, hy₀3, hfree⟩ := exists_fpf_parab34 hK4 j
  have hO : pCoreOf 2 (P.map φ.toMonoidHom) = (pCoreOf 2 P).map φ.toMonoidHom :=
    C11P9A.pCoreOf_map_of_injective φ.toMonoidHom φ.injective 2 P
  refine ⟨fun hb => ?_, φ.symm y₀, ?_, ?_, fun b hb hyb => ?_⟩
  · have h0 : pCoreOf 2 (C11P9A.parab34 K j) = ⊥ := by rw [← hj, hO, hb, Subgroup.map_bot]
    have h16 := (C11P9A.parab34_structure hK4 j).2.1
    rw [C11P9A.dInf_parab34 hK4 j] at h16
    have hc : Nat.card ↥(pCoreOf 2 (C11P9A.parab34 K j)) = 16 := by
      rw [pCoreOf, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), h16]
    rw [h0, Subgroup.card_bot] at hc
    omega
  · have h1 : y₀ ∈ P.map φ.toMonoidHom := hj ▸ hy₀
    exact Subgroup.mem_map_equiv.mp h1
  · exact (orderOf_injective φ.symm.toMonoidHom φ.symm.injective y₀).trans hy₀3
  · have hb' : φ b ∈ pCoreOf 2 (C11P9A.parab34 K j) := by
      rw [← hj, hO]
      exact ⟨b, hb, rfl⟩
    have h2 := hfree (φ b) hb' (by simpa using congrArg φ hyb)
    exact (map_eq_one_iff φ φ.injective).mp h2

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS
