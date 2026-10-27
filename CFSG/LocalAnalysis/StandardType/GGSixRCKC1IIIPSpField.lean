module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIUnitaryRecognition
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIINativeSp
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeF1PSp
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.FEPSp
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelSelfDualPSp
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelSelfDualTwoPSp
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelDualPairPSp

public section

namespace CFSG.StandardType.RCKC1

open Matrix CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.StandardType
  CFSG.StandardType.RCKRP CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieAdmissible StatedLieTag StatedSp)


theorem field_eq_one_of_row_III_of_native_PSp
    {X : Type} [Group X] [Finite X] {p n f : ℕ} {K J : Subgroup X} {d : X}
    (hp : p.Prime) (hp2 : p ≠ 2) (hdp : d ^ p = 1) (hf : 1 ≤ f)
    (φ : (ggU .PSp n f).K →* X) (hφr : φ.range = K)
    (hφk : φ.ker ≤ Subgroup.center (ggU .PSp n f).K)
    (hdN : d ∈ Subgroup.normalizer (K : Set X))
    (hdID : GGPsiInnerDiag (ggU .PSp n f).D φ d)
    (hJ : IsComponentOf J (K ⊓ Subgroup.centralizer {d}))
    (hrow : GGSixRCKJRow .III J) (hNoA6 : IsEmpty (↥J ≃* alternatingGroup (Fin 6))) :
    f = 1 := by
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
  let f : ℕ := g + 1
  by_contra hf1
  have hf2 : 2 ≤ f := by omega
  have hq4 : 4 ≤ 2 ^ f := by
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hf2
    simpa using this
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨s, hsSp, -, hsodd, ε, hε, ⟨e, he, heε, hsplit⟩, J', hJe, hJmap⟩ :=
    rckF1_PSp hp hp2 hdp hf φ hφr hφk hdN hdID hJ
  have hrow' : GGSixRCKJRow .III (J'.map φ) := by rw [hJmap]; exact hrow
  let S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)) := {s}
  have hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b := by
    intro a ha b hb
    have ha' : a = s := ha
    have hb' : b = s := hb
    rw [ha', hb']
  have hSp : ∀ a ∈ S, a ∈ StatedSp n (GaloisField 2 f) := by
    intro a ha
    have ha' : a = s := ha
    simpa only [ha'] using hsSp
  have hodd : ∀ a ∈ S, Odd (orderOf a) := by
    intro a ha
    have ha' : a = s := ha
    simpa only [ha'] using hsodd
  have hFE := not_fieldExtCase_of_row_III (t := .PSp) hrow' hf
  have hcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  rcases hsplit with heq | ⟨hne, hpair, hsum⟩
  · have hadj : formAdj (RingHom.id (GaloisField 2 f))
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
          (GaloisField 2 f)) e = e := by
      rw [heq]
      exact hε.2.2.2.1
    have hJe' : IsComponentOf J' ⁅glBlockCentralizer (StatedSp n (GaloisField 2 f)).subtype S e,
        glBlockCentralizer (StatedSp n (GaloisField 2 f)).subtype S e⁆ := by
      rw [heq]
      exact hJe
    have hdeg4 : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4 := by
      by_contra hd
      exact hFE (ggSixLSevenFieldExtCase_PSp n f (GaloisField 2 f) hcard φ hφk
        S hSp hS hodd hε hJe he heε (Or.inl ⟨heq, by omega⟩))
    by_cases hdeg1 : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 2
    · have hφinj : Function.Injective φ := by
        apply (MonoidHom.ker_eq_bot_iff φ).mp
        apply le_antisymm ?_ bot_le
        have hbot : Subgroup.center (ggU .PSp n f).K = ⊥ := by
          change Subgroup.center (StatedSp n (GaloisField 2 f)) = ⊥
          exact CFSG.SeitzReduction.SymplecticPilot.center_statedSp_eq_bot n
        exact hφk.trans hbot.le
      have hNoA6' : IsEmpty (↥J' ≃* alternatingGroup (Fin 6)) := by
        refine ⟨fun η => ?_⟩
        have ηJ : ↥(J'.map φ) ≃* alternatingGroup (Fin 6) :=
          (Subgroup.equivMapOfInjective J' φ hφinj).symm.trans η
        rw [hJmap] at ηJ
        exact hNoA6.false ηJ
      obtain ⟨m, ι, -, -, -, -, hιinj, hιrange, -⟩ :=
        exists_linearBlockModel_selfDual_PSp n f S hS he hadj hdeg1 hJe' hNoA6'
      let ιA : (ggU .PSp m f).K →* (ggU .PSp n f).K := ι
      let ν : (ggU .PSp m f).K →* X := φ.comp ιA
      have hνr : ν.range = J'.map φ := by
        dsimp only [ν]
        rw [MonoidHom.range_comp φ ιA, show ιA.range = J' from hιrange]
      have hνk : ν.ker ≤ Subgroup.center (ggU .PSp m f).K := by
        intro y hy
        have hcy := hφk hy
        rw [Subgroup.mem_center_iff] at hcy ⊢
        intro z
        apply hιinj
        rw [map_mul, map_mul]
        exact hcy (ι z)
      let j : (ggU .PSp m f).K →* GL (Fin (m + m)) (GaloisField 2 f) :=
        (Equiv.reindexGL finSumFinEquiv (GaloisField 2 f)).toMonoidHom.comp
          (StatedSp m (GaloisField 2 f)).subtype
      have hj : Function.Injective j :=
        (Equiv.reindexGL finSumFinEquiv (GaloisField 2 f)).injective.comp
          (Subgroup.subtype_injective _)
      have : Finite (ggU .PSp m f).K :=
        inferInstanceAs (Finite (StatedSp m (GaloisField 2 f)))
      have hm3 := three_le_of_row_III_of_matrix_range j hj ν (by rw [hνr]) hrow'
      have hadm : StatedLieAdmissible .PSp m 2 f := by
        refine ⟨Nat.prime_two, hf, by omega, ?_⟩
        intro hbad
        have := (Prod.mk.inj hbad).2
        omega
      have hmodel := irg_lieModel_quot (ht := Or.inr (Or.inr (Or.inl rfl))) hadm ν hνr hνk
      exact hf1 (lieModel_parameters_of_row_III hrow' hmodel).1
    · have hex := exists_blockModel_selfDualTwo_PSp_explicit n f S hSp hS hodd he hadj
        (by omega) hdeg4 hJe'
      rw [max_eq_left hf] at hex
      obtain ⟨m, ι, -, -, -, hcent, hιrange, -⟩ := hex
      let ιA : (ggU .PSU m f).K →* (ggU .PSp n f).K := ι
      let ν : (ggU .PSU m f).K →* X := φ.comp ιA
      have hνr : ν.range = J'.map φ := by
        dsimp only [ν]
        rw [MonoidHom.range_comp φ ιA, show ιA.range = J' from hιrange]
      have hνk : ν.ker ≤ Subgroup.center (ggU .PSU m f).K := by
        intro y hy
        exact hcent y (hφk hy)
      let j : (ggU .PSU m f).K →* GL (Fin m) (GaloisField 2 (2 * f)) :=
        (SU (CFSG.LieType.BorelTits.unitaryInvolution
          (GaloisField 2 (2 * f)) 2 f) m).subtype
      have hj : Function.Injective j := Subgroup.subtype_injective _
      have : Finite (ggU .PSU m f).K :=
        inferInstanceAs (Finite ↥(SU (CFSG.LieType.BorelTits.unitaryInvolution
          (GaloisField 2 (2 * f)) 2 f) m))
      have hm3 := three_le_of_row_III_of_matrix_range j hj ν (by rw [hνr]) hrow'
      have hadm : StatedLieAdmissible .PSU m 2 f := by
        refine ⟨Nat.prime_two, hf, hm3, ?_⟩
        intro hbad
        have := (Prod.mk.inj hbad).2
        omega
      have hmodel := irg_lieModel_quot (ht := Or.inr (Or.inl rfl)) hadm ν hνr hνk
      exact hf1 (lieModel_parameters_of_row_III hrow' hmodel).1
  · have hdeg1 : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 2 := by
      by_contra hd
      exact hFE (ggSixLSevenFieldExtCase_PSp n f (GaloisField 2 f) hcard φ hφk
        S hSp hS hodd hε hJe he heε (Or.inr ⟨hne, by omega⟩))
    have hJe' : IsComponentOf J'
        ⁅glBlockCentralizer (StatedSp n (GaloisField 2 f)).subtype S
            (e + formAdj (RingHom.id (GaloisField 2 f))
              (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
                (GaloisField 2 f)) e),
          glBlockCentralizer (StatedSp n (GaloisField 2 f)).subtype S
            (e + formAdj (RingHom.id (GaloisField 2 f))
              (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n)
                (GaloisField 2 f)) e)⁆ := by
      rw [← hsum]
      exact hJe
    obtain ⟨k, ι, -, -, -, hcent, hιrange, -⟩ :=
      exists_blockModel_dualPair_PSp_explicit n f S hSp hS he hpair hdeg1 hJe'
    let ιA : (ggU .PSL (k + 1) f).K →* (ggU .PSp n f).K := ι
    let ν : (ggU .PSL (k + 1) f).K →* X := φ.comp ιA
    have hνr : ν.range = J'.map φ := by
      dsimp only [ν]
      rw [MonoidHom.range_comp φ ιA, show ιA.range = J' from hιrange]
    have hνk : ν.ker ≤ Subgroup.center (ggU .PSL (k + 1) f).K := by
      intro y hy
      exact hcent y (hφk hy)
    let j : (ggU .PSL (k + 1) f).K →* GL (Fin (k + 1)) (GaloisField 2 f) :=
      SpecialLinearGroup.toGL
    have hj : Function.Injective j := by
      intro x y hxy
      exact Subtype.ext (congrArg (fun a : GL (Fin (k + 1)) (GaloisField 2 f) =>
        (a : Matrix (Fin (k + 1)) (Fin (k + 1)) (GaloisField 2 f))) hxy)
    have : Finite (ggU .PSL (k + 1) f).K :=
      inferInstanceAs (Finite (SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 f)))
    have hk3 := three_le_of_row_III_of_matrix_range j hj ν (by rw [hνr]) hrow'
    have hadm : StatedLieAdmissible .PSL (k + 1) 2 f := by
      refine ⟨Nat.prime_two, hf, by omega, ?_, ?_⟩
      all_goals intro hbad; have := (Prod.mk.inj hbad).1; omega
    have hmodel := irg_lieModel_quot (ht := Or.inl rfl) hadm ν hνr hνk
    exact hf1 (lieModel_parameters_of_row_III hrow' hmodel).1

theorem native_PSp_two_of_modelID_of_row_III
    {X : Type} [Group X] [Finite X] {p : ℕ} {K J B : Subgroup X} {d : X}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpow : ∀ b ∈ B, b ^ p = 1)
    (hBK : B ≤ Subgroup.normalizer (K : Set X)) (hdB : d ∈ B)
    (hmodel : RCKClassicalModelIDAt .PSp K B)
    (hJ : IsComponentOf J (K ⊓ Subgroup.centralizer {d}))
    (hrow : GGSixRCKJRow .III J) (hNoA6 : IsEmpty (↥J ≃* alternatingGroup (Fin 6))) :
    ∃ (n : ℕ) (φ : (ggU .PSp n 1).K →* X), φ.range = K ∧
      φ.ker ≤ Subgroup.center (ggU .PSp n 1).K ∧
      ∀ b ∈ B, GGPsiInnerDiag (ggU .PSp n 1).D φ b := by
  obtain ⟨n, f, φ, hf, hφr, hφk, hdiag⟩ := hmodel
  have hf1 := field_eq_one_of_row_III_of_native_PSp hp hp2 (hpow d hdB) hf
    φ hφr hφk (hBK hdB) (hdiag d hdB) hJ hrow hNoA6
  subst f
  exact ⟨n, φ, hφr, hφk, hdiag⟩

theorem ne_PSp_of_row_III_of_modelID
    {X : Type} [Group X] [Finite X] {p : ℕ} {K J B : Subgroup X} {t : StatedLieTag}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpow : ∀ b ∈ B, b ^ p = 1)
    (hBK : B ≤ Subgroup.normalizer (K : Set X))
    (hJd : ∃ d ∈ B, IsComponentOf J (K ⊓ Subgroup.centralizer {d}))
    (hrow : GGSixRCKJRow .III J) (hNoA6 : IsEmpty (↥J ≃* alternatingGroup (Fin 6)))
    (hNotBlock : ¬ FixedSpBlockAt K J) (hmodel : RCKClassicalModelIDAt t K B) : t ≠ .PSp := by
  rintro rfl
  obtain ⟨d, hdB, hJ⟩ := hJd
  obtain ⟨n, φ, hφr, hφk, hdiag⟩ := native_PSp_two_of_modelID_of_row_III
    hp hp2 hpow hBK hdB hmodel hJ hrow hNoA6
  exact hNotBlock (fixedSpBlockAt_of_native_PSp_two_of_jRow_III hp hp2 (hpow d hdB)
    φ hφr hφk (hBK hdB) (hdiag d hdB) hJ hrow)

end CFSG.StandardType.RCKC1
