module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8R95B0D
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3.Transitive
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8R95B0L3b
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3.Main
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3.GL2Max
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddQ7L3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3
open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

theorem r95_eq_top_of_section_SL3 {F : Type} [Field F] [Finite F]
    (hq : Nat.card F % 3 = 2) {W E : Subgroup (SL3 F)}
    (hNW : Subgroup.normalizer ((A0 : Subgroup (SL3 F)) : Set (SL3 F)) ≤ W) (hEW : E ≤ W)
    (hE : HasL32Quot E) : W = ⊤ := by
  have hroot :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.L3Leaves.sq_add_self_add_one_ne_zero hq
  have hcube := exists_cube hq
  have hlev : ∀ X : GL (Fin 2) F,
      (X : Matrix (Fin 2) (Fin 2) F) * cMat = cMat * (X : Matrix (Fin 2) (Fin 2) F) →
        lev X ∈ W := fun X hX => hNW (lev_mem_normalizer_A0 (mem_Nt_of_comm hX))
  rcases le_P1_or_le_P2_or_transitive hroot hcube hlev with h | h | htr
  ·
    exfalso
    exact r95_false_of_embed_P1 hq (Subgroup.inclusion (hEW.trans h))
      (Subgroup.inclusion_injective (hEW.trans h)) hE
  ·
    exfalso
    refine r95_false_of_embed_P1 hq ?_ ?_ hE
    · exact (dualAut.toMonoidHom.comp E.subtype).codRestrict (P1 : Subgroup (SL3 F))
        (fun y => dualAut_mem_P1 ((hEW.trans h) y.2))
    · intro x y hxy
      have := congrArg Subtype.val hxy
      exact Subtype.ext (dualAut.injective this)
  ·
    rcases inf_Q1_eq_bot_or_le hroot hcube (Y := W ⊓ P1)
        (fun X hX => ⟨hlev X hX, lev_mem_P1 X⟩) with hb | hle
    · exfalso
      by_cases hF : 2 ∣ Nat.card F
      ·
        exact r95_false_of_transitive_even hF hEW htr hb hE
      ·
        have h5 : 5 ≤ Nat.card F := by
          have h1 : 1 < Nat.card F := Finite.one_lt_card
          omega
        obtain ⟨μ, hμ0, hμ6⟩ := exists_pow_six_ne_one hq h5
        have hμ3 : μ ^ 3 ≠ 1 := fun h3 =>
          hμ6 (by rw [show 6 = 3 * 2 by norm_num, pow_mul, h3, one_pow])
        have hNtY : (Nt : Subgroup (GL (Fin 2) F)) ≤
            ((W ⊓ P1).subgroupOf P1).map rho1 :=
          fun X hX => ⟨⟨lev X, lev_mem_P1 X⟩,
            Subgroup.mem_subgroupOf.mpr ⟨hNW (lev_mem_normalizer_A0 hX), lev_mem_P1 X⟩,
            rho1_lev X⟩
        rcases gl2NonsplitMax hq h5 _ hNtY with h | h
        · exact false_of_map_rho1_le_Nt hroot hμ0 hμ6 hlev htr h.le
        · exact CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.false_of_transitive_of_sl2_le
            hμ0 hμ3 (hlev _ (scalGL_comm μ hμ0)) htr hb h
    · exact eq_top_of_Q1_le_of_transitive htr (hle.trans inf_le_left)

theorem r95_gB_L3 {Q : Type} [Group Q] [Finite Q] {p f : ℕ}
    (hpf : p ^ f % 3 = 2) (hQ : LieModel Q .PSL 3 p f)
    (hcyc : ∀ P : Subgroup Q, IsPGroup 3 P → IsCyclic P) {E : Subgroup Q} (hE : HasL32Quot E)
    {W : Subgroup Q} (hEW : E ≤ W)
    (hNW : ∀ D : Subgroup Q, D ≤ E → Nat.card D = 3 → normalizer (D : Set Q) ≤ W) :
    W = ⊤ := by
  obtain ⟨-, K, _, _, hK, ⟨eK⟩⟩ := hQ.statedClassicalModel (by decide)
  have hqK : Nat.card K % 3 = 2 := by rw [hK]; exact hpf
  let e : Q ≃* SL3 K := (eK.trans
    (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm).trans
    (pslEquivSL3 hqK)
  have hcycS : ∀ P : Subgroup (SL3 K), IsPGroup 3 P → IsCyclic P := by
    intro P hP
    have := hcyc _ (hP.map e.symm.toMonoidHom)
    exact isCyclic_of_surjective
      (P.equivMapOfInjective e.symm.toMonoidHom e.symm.injective).symm.toMonoidHom
      (MulEquiv.surjective _)
  obtain ⟨A, hAE, hA3⟩ := r95_exists_order_three_of_hasL32Quot hE
  have hA3' : Nat.card (A.map e.toMonoidHom) = 3 := by
    rw [Subgroup.card_map_of_injective e.injective, hA3]
  obtain ⟨g, hg⟩ :=
    CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.L3Leaves.exists_conj_eq_of_card_eq_three hcycS
      hA3' card_A0
  let φ : Q ≃* SL3 K := e.trans (MulAut.conj g)
  have hmap : ∀ R : Subgroup Q,
      R.map φ.toMonoidHom = (R.map e.toMonoidHom).map (MulAut.conj g).toMonoidHom := fun R => by
    rw [Subgroup.map_map]
    rfl
  have hA : (A0 : Subgroup (SL3 K)) = A.map φ.toMonoidHom := by rw [hmap]; exact hg
  have hNW' : Subgroup.normalizer ((A0 : Subgroup (SL3 K)) : Set (SL3 K)) ≤
      W.map φ.toMonoidHom := by
    rw [hA, ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono (hNW A hAE hA3)
  have hE' : HasL32Quot (E.map φ.toMonoidHom) := r95_hasL32Quot_map φ hE
  have htop := r95_eq_top_of_section_SL3 hqK hNW' (Subgroup.map_mono hEW) hE'
  rw [eq_top_iff]
  intro x _
  obtain ⟨w, hw, hwx⟩ : φ x ∈ W.map φ.toMonoidHom := htop ▸ Subgroup.mem_top _
  rwa [φ.injective hwx] at hw

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
