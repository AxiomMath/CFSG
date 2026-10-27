module

public import CFSG.Quasithin.Vol2.Ch3E213MOLB2
public import CFSG.Quasithin.Vol2.Ch3E213MOLB9

public section

namespace CFSG.Quasithin.Ch3E213M.OLB

open CFSG.Open CFSG.ClassicalInvolution
open scoped MatrixGroups


theorem kFactL33NoQuadFour_holds : OL.KFactL33NoQuadFour := by
  intro X _ _ K hKn hL hC S
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ι⟩ := exists_equiv_sl3 hL
  obtain ⟨g, hg⟩ := exists_zOf_sl3 ι S
  set z₀ := Models.rootInv (GaloisField 3 1) (n := 3) (by norm_num) with hz₀
  set ι' : SL(3, GaloisField 3 1) ≃* K := (MulAut.conj g).trans ι with hι'
  have hι'z : ι' z₀ = ι (g * z₀ * g⁻¹) := rfl
  have hcl := Models.isClassicalSL2_rootSL2 (K := GaloisField 3 1) two_ne_zero_gf3
    (by norm_num : 2 ≤ 3)
  refine ⟨ι' z₀, ?_, by rw [hι'z]; exact hg, ?_⟩
  · rw [MulEquiv.orderOf_eq]
    exact hcl.orderOf_eq_two
  intro V hVe hV4 hVP W _ _ hcomm hexp ρ hnt
  by_contra hcon
  push Not at hcon
  have hKs : IsSimpleGroup K := by
    obtain ⟨-, F, _, _, -, ⟨e⟩⟩ := hL
    obtain ⟨-, hs, -⟩ := CFSG.LinearGroups.linear_projective_simple (K := F) (n := 3)
      (by norm_num) (Or.inl le_rfl)
    have h1 :=
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 F).symm.isSimpleGroup
    exact e.isSimpleGroup
  set P := pCoreOf 2 (Subgroup.centralizer ({((ι' z₀ : K) : X)} : Set X)) with hPdef
  have hP : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hPz : P ≤ Subgroup.centralizer ({((ι' z₀ : K) : X)} : Set X) :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hPn : Subgroup.centralizer ({((ι' z₀ : K) : X)} : Set X) ≤
      Subgroup.normalizer (P : Set X) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  obtain ⟨k, hk, hk1⟩ := hnt
  exact hk1 (trivial_of_quadratic ι' hC hKs hP hPz hPn hVe hV4 hVP hcomm hexp ρ hcon k hk)

end CFSG.Quasithin.Ch3E213M.OLB
