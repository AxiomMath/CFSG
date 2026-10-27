module

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_3.FixTSzTensor
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_3.FixTSzDescent
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_3.FixTSzSteinberg
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_3.FixTSzSetup
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_3.FixTSzBorel
import CFSG.Sporadic.Schreier.TitsComponent
import CFSG.Quasithin.Background.SmithB45SzDesc

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.QuasithinUnique.Setup.SL2Modules CFSG.Quasithin.JonesParshall
open CFSG.LieType.Ree
open CFSG.Blueprint (LieModel)
open scoped MatrixGroups

theorem exists_borelMoves_of_isSz {W : Type} [CommGroup W]
    [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)} {n : ℕ} (hL : IsSz ↥L n)
    {J : Subgroup W} (hJ : J ∈ irrSet L) (hJC : J ⊓ fixV L ≠ ⊥) :
    ∃ S₀ : Subgroup (MulAut W), IsSylowIn 2 S₀ L ∧ BorelMoves L S₀ := by
  classical
  obtain ⟨a, K, hKfield, hKfin, hKchar, hK, π, M, hMadd, hMmod, hMfin, ρ, β,
    hirr, hnt, hβs, hβk, hβe, c, hc, hnc⟩ := exists_szSection_data hW hL hJ hJC
  letI : Field K := hKfield
  letI : Fintype K := hKfin
  letI : CharP K 2 := hKchar
  letI : AddCommGroup M := hMadd
  letI : Module (ZMod 2) M := hMmod
  letI : Finite M := hMfin
  haveI : Fact ρ.IsIrreducible := ⟨hirr⟩
  have hJinv : ∀ h : ↥L, ∀ u ∈ J, (h : MulAut W) u ∈ J :=
    fun h u hu => hJ.2.2.1 h h.2 u hu
  obtain ⟨d, -, -, hdesc⟩ := B45Sz.sz_descent hK hnt
  have : Module.Finite (EndRing ρ) M := Module.Finite.of_finite
  let b := Module.finBasis (EndRing ρ) M
  obtain ⟨E, hEfield, hEfin, hEchar, ιK, ιD, A, hAne, hAΩ, hΦ, -, -⟩ := hdesc b
  letI : Field E := hEfield
  letI : Finite E := hEfin
  letI : CharP E 2 := hEchar
  letI : Algebra K E := ιK.toAlgebra
  obtain ⟨Φ⟩ := hΦ
  by_cases hΩ : A = B45Sz.szOmega a
  · subst hΩ
    exfalso
    obtain ⟨φE, hφE⟩ := szT_higman hK E
    obtain ⟨ψ, hψ⟩ := exists_higman_of_equiv b ιD (B45Sz.szT E hK (B45Sz.szOmega a)) Φ
      (suzukiU a K) φE hφE
    exact hnc (mem_B1_dual_of_higman ρ (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp
      (CFSG.Sporadic.Schreier.Tits.suzukiU_isSylow hK).2)) ψ hψ hc)
  · obtain ⟨l, χ, hχ, hl⟩ := exists_szT_suzukiDElt_eTopS_ne hK E hAΩ hAne hΩ
    obtain ⟨m, hm, hmD⟩ := exists_norm_vector_of_equiv b ιD (B45Sz.szT E hK A) Φ
      (eTopS_ne_zero E A) (fun s => ∃ u v : K, u ≠ 0 ∧ s = suzukiSElt a K u v)
      (by
        rintro s ⟨u, v, hu, rfl⟩
        exact szT_norm_eTopS hK E hAne hu v) hχ hl
    obtain ⟨x, hxU, hxD⟩ := exists_fixed_suzukiU_of_norm hK π.toMonoidHom hJinv inf_le_right
      ρ β hβs hβk hβe (fun u v hu => hm _ ⟨u, v, hu, rfl⟩) ⟨l, hmD⟩
    exact borelMoves_of_surjective_sz hW hK π ⟨x, hxU, hxD⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3
