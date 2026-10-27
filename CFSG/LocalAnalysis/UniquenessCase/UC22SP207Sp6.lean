module

public import CFSG.LocalAnalysis.UniquenessCase.UC22SP207Defs
import CFSG.LocalAnalysis.StandardType.GGSpJoinWeylRank
import CFSG.LocalAnalysis.UniquenessCase.UC22SP207Coxeter
import CFSG.LocalAnalysis.UniquenessCase.UC22SP207Datum
import CFSG.LocalAnalysis.UniquenessCase.UC22SP207Transfer
import CFSG.Milestones.ASVolI.I2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.ASVolI.ChIJK CFSG.GH74.BNPair CFSG.GroupActions CFSG.LieType.Universal
  CFSG.LieType.Steinberg CFSG.LieType.RootSystem CFSG.LieType.CurtisTits CFSG.GH74.GLS.SP
  CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras
open CFSG.Blueprint (LieModel)

theorem uc22sp207_hasCentralLongest_Sp6 {X : Type} [Group X] {n : ℕ}
    (h : LieModel X .PSp 3 2 n) : HasCentralLongest X := by
  obtain ⟨⟨hp, hf, -, -⟩, F, hFf, hFfin, hcard, ⟨e⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)
  have : Fact (Nat.Prime 2) := ⟨hp⟩
  have : CharP F 2 := burnsideI2BN_charP_of_card hp hf hcard
  have hct := Symplectic.isCTGroupDatum 3 F
  have hext := Symplectic.steinbergExtras 3 F
  have hN := cartan_normal_of_datum hct hext
  have : Finite (coxeterMatrix (isFiniteType_cartanC 3)).Group :=
    Finite.of_equiv _ (weylEquiv hct hext).toEquiv
  have hB : coxeterMatrix (isFiniteType_cartanC 3) = CoxeterMatrix.B 3 :=
    CFSG.StandardType.coxeterMatrix_cartanC_eq_B 3
  have hSp : HasCentralLongest ↥(CFSG.Open.StatedSp 3 F) :=
    uc22sp207_hasCentralLongest_of_datum (D := Symplectic.rootDatum 3 F)
      (n := Symplectic.weylRep 3 F) (H := Symplectic.torus 3 F) hct hext
      CFSG.StandardType.GGRootSp.bruhatExtras (by
        rintro ⟨x, hx⟩
        have hidb := idBelow_of_mem_iSup (F := F) 1
          {γ | γ ∈ roots (isFiniteType_cartanC 3) ∅ ∧ 0 < ht γ}
          (fun γ hγ => ⟨hγ.1, by have := hγ.2; omega⟩) hx
        obtain ⟨k, hk⟩ := burnsideI2BN_pow_eq_one_of_triangular (p := 2)
          (fun a => (1 : ℤ) * lvl a) (M := mat 3 F x) hidb
        refine ⟨k, Subtype.ext (mat_injective (n := 3) (F := F) ?_)⟩
        simpa [map_pow] using hk) (by
        have hT : ∀ x ∈ (⨆ i, Symplectic.torus 3 F i : Subgroup (CFSG.Open.StatedSp 3 F)),
            x ^ (Nat.card F - 1) = 1 := by
          intro x hx
          obtain ⟨t, rfl⟩ := exists_diagonal_of_mem_iSup_torus hx
          have ht : t ^ (Nat.card F - 1) = 1 := by
            funext i
            rw [Pi.pow_apply, Pi.one_apply]
            exact burnsideI2BN_units_pow_card_sub_one (t i)
          rw [← map_pow, ← map_pow, ht, map_one, map_one]
        exact burnsideI2BN_not_dvd_card_of_pow_eq_one hT
          (burnsideI2BN_not_dvd_card_sub_one hp
            (hcard ▸ dvd_pow_self 2 (by omega : n ≠ 0))))
      (uc22sp207_exists_central_longest_B3 (coxeterMatrix (isFiniteType_cartanC 3)).toCoxeterSystem
        (p := (0 : Fin 3)) (l := 1) (π := 2) (by decide) (by decide) (by decide) (by decide)
        (by rw [hB]; decide) (by rw [hB]; decide) (by rw [hB]; decide))
  exact (hSp.statedProj).of_mulEquiv e.symm

end CFSG.LocalAnalysis.UniquenessCase.UC22
