module

public import CFSG.RankThree.PartTwo.Sec10.KS1012AutHyp.SL364C2
public import CFSG.RankThree.PartTwo.Sec10.KS1012AutHyp.SL364C3
public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofL364Sylow

public section

namespace CFSG.RankThree.PartTwo.Sec10.KS1012AutHyp

open CFSG.RankThree.PartTwo.Sec4.Res6L364
  (K64 σ4 F4 ι glι glι_injective GLσ mapσ range_glι σ4_ι coe_glι ι_injective)

theorem card_F4_eq : Nat.card F4 = 4 := by
  rw [Nat.card_eq_fintype_card]
  exact CFSG.RankThree.PartTwo.Sec4.Res6L364.card_F4

theorem det_glι (A : GL (Fin 3) F4) :
    ((glι A : GL (Fin 3) K64) : Matrix (Fin 3) (Fin 3) K64).det =
      ι ((A : Matrix (Fin 3) (Fin 3) F4).det) := by
  rw [coe_glι, ← RingHom.mapMatrix_apply, ← RingHom.map_det]

theorem exists_mulEquiv_fixedSub :
    Nonempty (CFSG.Open.StatedSL 3 F4 ≃* ↥(fixedSub (slFieldSL K64 σ4))) := by
  have hmemSL : ∀ A : CFSG.Open.StatedSL 3 F4,
      glι (A : GL (Fin 3) F4) ∈ CFSG.Open.StatedSL 3 K64 := by
    intro A
    rw [CFSG.Open.StatedAPI.mem_statedSL_iff, det_glι,
      CFSG.Open.StatedAPI.det_of_mem_statedSL A.2, map_one]
  let g1 : CFSG.Open.StatedSL 3 F4 →* CFSG.Open.StatedSL 3 K64 :=
    (glι.comp (CFSG.Open.StatedSL 3 F4).subtype).codRestrict (CFSG.Open.StatedSL 3 K64) hmemSL
  have hg1 : ∀ A : CFSG.Open.StatedSL 3 F4, ((g1 A : CFSG.Open.StatedSL 3 K64) : GL (Fin 3) K64) =
      glι (A : GL (Fin 3) F4) := fun A => rfl
  have hfix : ∀ A : CFSG.Open.StatedSL 3 F4, g1 A ∈ fixedSub (slFieldSL K64 σ4) := by
    intro A
    rw [mem_fixedSub]
    apply Subtype.ext
    apply Units.ext
    ext i j
    rw [coe_slFieldSL, hg1]
    exact σ4_ι _
  let g2 : CFSG.Open.StatedSL 3 F4 →* ↥(fixedSub (slFieldSL K64 σ4)) :=
    g1.codRestrict (fixedSub (slFieldSL K64 σ4)) hfix
  have hg2 : ∀ A : CFSG.Open.StatedSL 3 F4,
      (((g2 A : ↥(fixedSub (slFieldSL K64 σ4))) : CFSG.Open.StatedSL 3 K64) : GL (Fin 3) K64) =
        glι (A : GL (Fin 3) F4) := fun A => rfl
  refine ⟨MulEquiv.ofBijective g2 ⟨?_, ?_⟩⟩
  · intro A B h
    apply Subtype.ext
    apply glι_injective
    rw [← hg2, ← hg2, h]
  · rintro ⟨x, hx⟩
    have hxσ : mapσ (x : GL (Fin 3) K64) = x := by
      apply Units.ext
      ext i j
      have h1 := coe_slFieldSL K64 σ4 x i j
      rw [mem_fixedSub.mp hx] at h1
      exact h1.symm
    obtain ⟨A, hA⟩ : (x : GL (Fin 3) K64) ∈ glι.range := by
      rw [range_glι]; exact hxσ
    have hdet : (A : Matrix (Fin 3) (Fin 3) F4).det = 1 := by
      apply ι_injective
      rw [← det_glι, hA, map_one]
      exact CFSG.Open.StatedAPI.det_of_mem_statedSL x.2
    refine ⟨⟨A, CFSG.Open.StatedAPI.mem_statedSL_of_det hdet⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hA

end CFSG.RankThree.PartTwo.Sec10.KS1012AutHyp

end
