module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.GH74.Uniqueness.SU.SU5Q8D8
public import CFSG.Quasithin.Background.A3StructureDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsNineB23Lines
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC6U4OverAux1
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KOdd2Fin
import CFSG.RankThree.PartOne.SRC.ModelL3
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoFacts
import CFSG.GH74.KGroups.PSL2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.HardMathSupport.Solomon.UniquenessMaximal.Odd2
open scoped MatrixGroups
open CFSG.Blueprint (LieModel)

theorem false_of_odd_quot {Q : Type} [Group Q] [Finite Q] {n : ℕ} (hn : 1 < n)
    (hL2 : IsL2 (Q ⧸ CFSG.pCore 2 Q) (2 * n)) (N : Subgroup Q) [N.Normal]
    (hN3 : ¬ 3 ∣ Nat.card N)
    (hcases : (∃ (F : Type) (_ : Field F) (_ : Finite F), Odd (Nat.card F) ∧
          Nonempty (Q ⧸ N ≃* SL(2, F))) ∨
        (∃ m : ℕ, Odd m ∧ LieModel (Q ⧸ N) .PSL 2 2 m) ∨
        CFSG.Quasithin.IsExt (Q ⧸ N)
          (fun V _ => CFSG.GH74.Uniqueness.SU.SU5.IsQ8D8 (⊤ : Subgroup V))
          (fun Y _ => CFSG.Quasithin.IsAlt 5 Y)) : False := by
  classical
  let P : Subgroup Q := CFSG.pCore 2 Q
  let S := Q ⧸ P
  haveI hPnormal : P.Normal := CFSG.pCore_normal (p := 2) (G := Q)
  have hSsimple : IsSimpleGroup S := isSimpleGroup_of_isL2 hL2
  have hScm : CFSG.Open.StatedClassicalModel S .PSL 2 2 (2 * n) :=
    (CFSG.Blueprint.LieModel.classical_iff (t := .PSL) (by decide)).mp hL2
  have hScard : Nat.card S = 2 ^ (2 * n) * ((2 ^ (2 * n)) ^ 2 - 1) :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_two hScm
  have hSthree : 3 ∣ Nat.card S :=
    CFSG.Open.StatedAPI.three_dvd_card_of_statedClassicalModel_psl_two_two hScm
  have hNbarBot : N ≤ P := by
    let Nbar : Subgroup S := N.map (QuotientGroup.mk' P)
    have hNbarNormal : Nbar.Normal :=
      Subgroup.Normal.map (inferInstance : N.Normal) (QuotientGroup.mk' P)
        (QuotientGroup.mk'_surjective P)
    have hNbarThree : ¬ 3 ∣ Nat.card Nbar := fun h3 =>
      hN3 (h3.trans (Subgroup.card_map_dvd (H := N) (f := QuotientGroup.mk' P)))
    have hNbar : Nbar = ⊥ ∨ Nbar = ⊤ :=
      IsSimpleGroup.eq_bot_or_eq_top_of_normal Nbar
    rcases hNbar with hbot | htop
    · rw [← QuotientGroup.ker_mk' (N := P)]
      exact (Subgroup.map_eq_bot_iff (H := N) (f := QuotientGroup.mk' P)).mp hbot
    · exact absurd (by rw [htop, Subgroup.card_top]; exact hSthree) hNbarThree
  let π : Q ⧸ N →* S :=
    QuotientGroup.map N P (MonoidHom.id Q) (by simpa using hNbarBot)
  have hπ : Function.Surjective π := by
    refine QuotientGroup.map_surjective_of_surjective (N := N) (M := P)
      (f := MonoidHom.id Q) ?_ (by simpa using hNbarBot)
    intro y
    exact QuotientGroup.mk'_surjective P y
  rcases hcases with ⟨F, hFfield, hFfinite, hFodd, ⟨eF⟩⟩ | ⟨m, hmOdd, hmL2⟩ | hExt
  · letI : Field F := hFfield
    letI : Finite F := hFfinite
    have hFodd' : Nat.card F % 2 = 1 := Nat.odd_iff.mp hFodd
    have hSecSL2 : Sec8 (Matrix.SpecialLinearGroup (Fin 2) F) := by
      let φ : Matrix.SpecialLinearGroup (Fin 2) F →*
          Matrix.GeneralLinearGroup (Fin 3) F :=
        Matrix.SpecialLinearGroup.toGL.comp
          (CFSG.RankThree.PartOne.SRC.blockHom (F := F))
      have hφ : Function.Injective φ :=
        Matrix.SpecialLinearGroup.toGL_injective.comp
          (CFSG.RankThree.PartOne.SRC.blockHom_injective (F := F))
      let H : Subgroup (Matrix.GeneralLinearGroup (Fin 3) F) := φ.range
      have hdet : ∀ g ∈ H,
          ((g : Matrix.GeneralLinearGroup (Fin 3) F) :
            Matrix (Fin 3) (Fin 3) F).det = 1 := by
        rintro g ⟨A, rfl⟩
        change (CFSG.RankThree.PartOne.SRC.blockMat A).det = 1
        exact CFSG.RankThree.PartOne.SRC.det_blockMat A
      have hSecH : Sec8 ↥H :=
        CFSG.HardMathSupport.Solomon.UniquenessMaximal.Odd2.sec8_of_det_one hFodd' H hdet
      exact Sec8.of_injective (MonoidHom.ofInjective hφ).toMonoidHom
        (MonoidHom.ofInjective hφ).injective hSecH
    have hSecQN : Sec8 (Q ⧸ N) := Sec8.of_injective eF.toMonoidHom eF.injective hSecSL2
    have hSecS : Sec8 S := Sec8.of_surjective π hπ hSecQN
    have h2npos : 0 < 2 * n := by omega
    have h2n1 : 1 ≤ 2 * n := by omega
    have hGF : Nat.card (GaloisField 2 (2 * n)) = 2 ^ (2 * n) :=
      GaloisField.card 2 (2 * n) (by omega)
    obtain ⟨eS⟩ := CFSG.GH74.KGroups.PSL2.psl2_equiv_of_lieModel
      (F := GaloisField 2 (2 * n)) 2 (2 * n) h2npos hGF hL2
    let U : Sylow 2 (CFSG.AGLEmbedding.PSL2GF 2 (2 * n)) := default
    have hU := CFSG.AGLEmbedding.psl2GF_sylow 2 (2 * n) h2n1 U
    let E : Subgroup S := U.map eS.symm.toMonoidHom
    have hEcard : Nat.card E = 2 ^ (2 * n) := by
      dsimp only [E]
      rw [Subgroup.card_map_of_injective (f := eS.symm.toMonoidHom) eS.symm.injective, hU.2]
    have hEtwo : ∀ x ∈ E, x * x = 1 := by
      intro x hx
      dsimp only [E] at hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      have hy2 : y ^ 2 = 1 := hU.1.2 y hy
      have := congrArg (fun z => eS.symm z) hy2
      simpa [pow_two] using this
    have hle8 : Nat.card E ≤ 8 :=
      hSecS E E E.subtype (MonoidHom.id E) E.subtype_injective
        (fun x => ⟨x, rfl⟩) (fun x => by
          show (x : ↥E) * x = 1
          exact Subtype.ext (by simpa using hEtwo x x.2))
    have hge16 : 16 ≤ Nat.card E := by
      rw [hEcard]
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · haveI : IsSimpleGroup (Q ⧸ N) := isSimpleGroup_of_isL2 hmL2
    have hker : π.ker = ⊥ ∨ π.ker = ⊤ :=
      IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker
    rcases hker with hbot | htop
    · have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).mp hbot
      let eπ : Q ⧸ N ≃* S := MulEquiv.ofBijective π ⟨hinj, hπ⟩
      have hmL2' : IsL2 S m := CFSG.Blueprint.LieModel.of_mulEquiv eπ hmL2
      have hmEq : m = 2 * n := s16c6_isL2_param_unique hmL2' hL2
      obtain ⟨k, hk⟩ := hmOdd
      omega
    · have htriv : ∀ x : Q ⧸ N, π x = 1 := by
        intro x
        have hx : x ∈ π.ker := by rw [htop]; exact Subgroup.mem_top x
        simpa using hx
      have hsub : Subsingleton S := ⟨fun a b => by
        obtain ⟨x, rfl⟩ := hπ a
        obtain ⟨y, rfl⟩ := hπ b
        rw [htriv x, htriv y]⟩
      obtain ⟨a, b, hab⟩ := (inferInstance : Nontrivial S).exists_pair_ne
      exact hab (Subsingleton.elim a b)
  · obtain ⟨V, hVnormal, hQ8, hA5⟩ := hExt
    haveI : V.Normal := hVnormal
    have hVcard : Nat.card V = 32 := by
      have h := (CFSG.GH74.Uniqueness.SU.SU5.IsQ8D8.facts hQ8).1
      simpa using h
    obtain ⟨eA5⟩ := hA5
    have hA5card : Nat.card ((Q ⧸ N) ⧸ V) = 60 := by
      rw [Nat.card_congr eA5.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      norm_num
    have hQNcard : Nat.card (Q ⧸ N) = 1920 := by
      have h := Subgroup.card_mul_index (H := V)
      rw [hVcard, Subgroup.index_eq_card, hA5card] at h
      norm_num at h
      exact h.symm
    have hdvd : Nat.card S ∣ 1920 := by
      rw [← hQNcard]
      exact Subgroup.card_dvd_of_surjective hπ
    have hge : 4080 ≤ Nat.card S := by
      rw [hScard]
      have h1 : 16 ≤ 2 ^ (2 * n) := by
        calc 16 = 2 ^ 4 := by norm_num
          _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : 255 ≤ (2 ^ (2 * n)) ^ 2 - 1 := by
        have h3 : 16 ^ 2 ≤ (2 ^ (2 * n)) ^ 2 := Nat.pow_le_pow_left h1 2
        norm_num at h3
        omega
      calc 4080 = 16 * 255 := by norm_num
        _ ≤ 2 ^ (2 * n) * ((2 ^ (2 * n)) ^ 2 - 1) := Nat.mul_le_mul h1 h2
    have hle : Nat.card S ≤ 1920 := Nat.le_of_dvd (by norm_num) hdvd
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
