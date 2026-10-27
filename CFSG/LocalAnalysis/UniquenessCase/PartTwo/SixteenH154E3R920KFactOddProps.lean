module

public import CFSG.Blueprint.Catalog
import CFSG.GH74.Filter.Small.RankThree
import CFSG.RankThree.PartTwo.Sec4.T444.DiagL34OddSL3
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.GL83LieDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.GorensteinWalter

private theorem r920kop_statedSL_map_mk_eq_range_toPGL {K : Type} [Field K] :
    (StatedSL 3 K).map (Matrix.ProjGenLinGroup.mk :
        GL (Fin 3) K →* Matrix.ProjGenLinGroup (Fin 3) K) =
      (Matrix.SpecialLinearGroup.toPGL :
        Matrix.SpecialLinearGroup (Fin 3) K →*
          Matrix.ProjGenLinGroup (Fin 3) K).range := by
  rw [StatedAPI.statedSL_eq_ker_det, ← Matrix.SpecialLinearGroup.range_toGL_eq_ker_det,
    MonoidHom.range_comp]

private theorem r920kop_range_subtype_comp {Q X : Type*} [Group Q] [Group X]
    (S : Subgroup X) (e : Q ≃* S) : (S.subtype.comp e.toMonoidHom).range = S := by
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 e.surjective, Subgroup.map_top,
    Subgroup.range_subtype]

private theorem r920kop_exists_abelian_relIndex_two_of_le_range_toPGL {K : Type} [Field K]
    [Finite K] (hK : IsOddPrimePower (Nat.card K))
    (R : Subgroup (Matrix.ProjGenLinGroup (Fin 3) K)) (hR : IsPGroup 2 R)
    (hRrange : R ≤ (Matrix.SpecialLinearGroup.toPGL :
      Matrix.SpecialLinearGroup (Fin 3) K →* Matrix.ProjGenLinGroup (Fin 3) K).range) :
    ∃ B : Subgroup (Matrix.ProjGenLinGroup (Fin 3) K),
      B ≤ R ∧ (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧ B.relIndex R ≤ 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS, hSm⟩ :=
    CFSG.RankThree.PartTwo.Sec4.L34Odd.exists_isPGroup_map_eq 2
      (Matrix.SpecialLinearGroup.toPGL :
        Matrix.SpecialLinearGroup (Fin 3) K →* Matrix.ProjGenLinGroup (Fin 3) K) R hR hRrange
  obtain ⟨B, hBc, hBi, -⟩ :=
    CFSG.RankThree.PartTwo.Sec4.L34Odd.gl2Type_of_injective_sl3 hK hS S.subtype
      S.subtype_injective
  let π : S →* Matrix.ProjGenLinGroup (Fin 3) K :=
    (Matrix.SpecialLinearGroup.toPGL :
      Matrix.SpecialLinearGroup (Fin 3) K →* Matrix.ProjGenLinGroup (Fin 3) K).comp S.subtype
  have hπrange : π.range = R := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact hSm
  refine ⟨B.map π, ?_, ?_, ?_⟩
  · exact (Subgroup.map_le_range (f := π) B).trans_eq hπrange
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg π (hBc a ha b hb)
  · have h := Subgroup.relIndex_map_map π B ⊤
    rw [Subgroup.map_top π, hπrange, top_sup_eq, Subgroup.relIndex_top_right] at h
    rw [h]
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite))
      (Subgroup.index_dvd_of_le (le_sup_left : B ≤ B ⊔ π.ker))).trans hBi

private theorem r920kop_abelian_of_statedProj {K : Type} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) {Q : Type*} [Group Q] [Finite Q]
    (H : Subgroup (GL (Fin 3) K))
    (hH : H.map (Matrix.ProjGenLinGroup.mk :
        GL (Fin 3) K →* Matrix.ProjGenLinGroup (Fin 3) K) ≤
      (Matrix.SpecialLinearGroup.toPGL :
        Matrix.SpecialLinearGroup (Fin 3) K →*
          Matrix.ProjGenLinGroup (Fin 3) K).range)
    (e : Q ≃* StatedProj H) (R : Subgroup Q) (hR : IsPGroup 2 ↥R) :
    ∃ B : Subgroup Q, B ≤ R ∧ (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧ B.relIndex R ≤ 2 := by
  classical
  let e' : Q ≃* ↥(H.map (Matrix.ProjGenLinGroup.mk :
      GL (Fin 3) K →* Matrix.ProjGenLinGroup (Fin 3) K)) :=
    e.trans (StatedAPI.mapMkEquivStatedProj H).symm
  let φ : Q →* Matrix.ProjGenLinGroup (Fin 3) K :=
    (H.map (Matrix.ProjGenLinGroup.mk :
      GL (Fin 3) K →* Matrix.ProjGenLinGroup (Fin 3) K)).subtype.comp e'.toMonoidHom
  have hφrange : φ.range = H.map (Matrix.ProjGenLinGroup.mk :
      GL (Fin 3) K →* Matrix.ProjGenLinGroup (Fin 3) K) :=
    r920kop_range_subtype_comp _ e'
  have hRrange : R.map φ ≤ (Matrix.SpecialLinearGroup.toPGL :
      Matrix.SpecialLinearGroup (Fin 3) K →*
        Matrix.ProjGenLinGroup (Fin 3) K).range :=
    (Subgroup.map_le_range (f := φ) R).trans (hφrange.le.trans hH)
  obtain ⟨B', hB'le, hB'c, hB'i⟩ :=
    r920kop_exists_abelian_relIndex_two_of_le_range_toPGL hK (R.map φ) (hR.map φ) hRrange
  have hφinj : Function.Injective φ :=
    (H.map (Matrix.ProjGenLinGroup.mk :
      GL (Fin 3) K →* Matrix.ProjGenLinGroup (Fin 3) K)).subtype_injective.comp e'.injective
  refine ⟨B'.comap φ, ?_, ?_, ?_⟩
  · exact (Subgroup.comap_mono hB'le).trans
      (le_of_eq (Subgroup.comap_map_eq_self_of_injective hφinj R))
  · intro a ha b hb
    apply hφinj
    rw [map_mul, map_mul]
    exact hB'c (φ a) ha (φ b) hb
  · rw [Subgroup.relIndex_comap]
    exact hB'i

theorem exists_abelian_index_two_of_isPGroup_two_L3U3 {Q : Type} [Group Q] [Finite Q] {p f : ℕ}
    (hp : p ≠ 2) (hQ : LieModel Q .PSL 3 p f ∨ LieModel Q .PSU 3 p f) (R : Subgroup Q)
    (hR : IsPGroup 2 ↥R) :
    ∃ B : Subgroup Q, B ≤ R ∧ (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧ B.relIndex R ≤ 2 := by
  rcases hQ with hPSL | hPSU
  · obtain ⟨⟨hpp, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ :=
      hPSL.statedClassicalModel (by decide : StatedLieTag.PSL ∈ CFSG.Blueprint.classicalTags)
    have hoddK : IsOddPrimePower (Nat.card K) :=
      ⟨p, f, hpp, hpp.odd_of_ne_two hp, hf, hK⟩
    exact r920kop_abelian_of_statedProj hoddK (StatedSL 3 K)
      (le_of_eq r920kop_statedSL_map_mk_eq_range_toPGL) e R hR
  · obtain ⟨⟨hpp, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ :=
      hPSU.statedClassicalModel (by decide : StatedLieTag.PSU ∈ CFSG.Blueprint.classicalTags)
    have hoddK : IsOddPrimePower (Nat.card K) :=
      ⟨p, f * 2, hpp, hpp.odd_of_ne_two hp, by omega, by rw [hK, pow_mul]⟩
    exact r920kop_abelian_of_statedProj hoddK (StatedSU 3 (p ^ f) K)
      ((Subgroup.map_mono (StatedAPI.statedSU_le_statedSL 3 (p ^ f) K)).trans
        (le_of_eq r920kop_statedSL_map_mk_eq_range_toPGL)) e R hR

theorem pRank_two_le_two_L3U3 {Q : Type} [Group Q] [Finite Q] {p f : ℕ} (hp : p ≠ 2)
    (hQ : LieModel Q .PSL 3 p f ∨ LieModel Q .PSU 3 p f) :
    CFSG.Open.pRank 2 (⊤ : Subgroup Q) ≤ 2 := by
  rcases hQ with hPSL | hPSU
  · exact CFSG.GH74.Filter.t_PSL_three_odd Q p f hp
      (hPSL.statedClassicalModel (by decide : StatedLieTag.PSL ∈ CFSG.Blueprint.classicalTags))
  · exact CFSG.GH74.Filter.t_PSU_three_odd Q p f hp
      (hPSU.statedClassicalModel (by decide : StatedLieTag.PSU ∈ CFSG.Blueprint.classicalTags))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
