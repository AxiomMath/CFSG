module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSevenDiag
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.U3IndexNormal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
  CFSG.LocalAnalysis.WeakClosure81
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

theorem inFSq_top_of_normal_mulEquiv_isL2 (hKc : Inputs1719.K_L2SzAutRank)
    {Q : Type} [Group Q] [Finite Q] {J : Subgroup Q} {m : ℕ} (hperf : ⁅J, J⁆ = J)
    (hL2 : IsL2 (Bar2 J) m) (E : Type) [Group E] [Finite E] (J_E : Subgroup E) [J_E.Normal]
    (e : Nonempty (↥J_E ≃* ↥J)) (h2 : IsPGroup 2 (E ⧸ J_E)) :
    InFSq m (⊤ : Subgroup E) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ := Sylow.nonempty (p := 2) (G := E)
  have hS : IsSylowIn 2 (S : Subgroup E) ⊤ := isSylowIn_top S
  have hsup : J_E ⊔ (S : Subgroup E) = ⊤ :=
    CFSG.OrderReductions.PrimeQuotientFrattini.kernel_sup_sylow_eq_top 2 J_E h2 S
  have hperf' : ⁅J_E, J_E⁆ = J_E := by
    obtain ⟨e⟩ := e
    haveI : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.mpr hperf
    exact Subgroup.isPerfect_iff.mp
      (Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective)
  have hL2' : IsL2 (Bar2 J_E) m := by
    obtain ⟨e⟩ := e
    exact LieModel.of_mulEquiv (QuotientGroup.congr (CFSG.pCore 2 ↥J_E)
      (CFSG.pCore 2 ↥J) e (CFSG.pCore_map_iso 2 e)).symm hL2
  exact inFSq_of_isL2_of_normal_sup (H := ⊤) (K := J_E) (T := (S : Subgroup E)) le_top
    (by infer_instance) hS hsup hperf' hL2' hKc

theorem inFSq_top_of_normal_mulEquiv_isU3 (hKidx : Inputs1719.K_U3IndexNormal)
    {Q : Type} [Group Q] [Finite Q] {J : Subgroup Q} {m : ℕ} (hperf : ⁅J, J⁆ = J)
    (hq : CFSG.Open.IsQuasisimple (Bar2 J)) (hU3 : IsU3 (Bar2 J) m)
    (E : Type) [Group E] [Finite E] (J_E : Subgroup E) [J_E.Normal]
    (e : Nonempty (↥J_E ≃* ↥J)) (h2 : IsPGroup 2 (E ⧸ J_E)) :
    InFSq m (⊤ : Subgroup E) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ := Sylow.nonempty (p := 2) (G := E)
  have hS : IsSylowIn 2 (S : Subgroup E) ⊤ := isSylowIn_top S
  have hsup : J_E ⊔ (S : Subgroup E) = ⊤ :=
    CFSG.OrderReductions.PrimeQuotientFrattini.kernel_sup_sylow_eq_top 2 J_E h2 S
  have hperf' : ⁅J_E, J_E⁆ = J_E := by
    obtain ⟨e⟩ := e
    haveI : Group.IsPerfect ↥J := Subgroup.isPerfect_iff.mpr hperf
    exact Subgroup.isPerfect_iff.mp
      (Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective)
  have hU3' : IsU3 (Bar2 J_E) m := by
    obtain ⟨e⟩ := e
    exact LieModel.of_mulEquiv (QuotientGroup.congr (CFSG.pCore 2 ↥J_E)
      (CFSG.pCore 2 ↥J) e (CFSG.pCore_map_iso 2 e)).symm hU3
  have hq' : CFSG.Open.IsQuasisimple (Bar2 J_E) := by
    obtain ⟨e⟩ := e
    exact hq.of_mulEquiv (QuotientGroup.congr (CFSG.pCore 2 ↥J_E)
      (CFSG.pCore 2 ↥J) e (CFSG.pCore_map_iso 2 e))
  have hSU3 : IsSU3 (Bar2 J_E) m := uc22p22d_isSU3_of_isU3 hq' hU3'
  exact hKidx E J_E S ⊤ m le_top ((inferInstance : J_E.Normal).subgroupOf ⊤)
    hperf' hq' hSU3 hS hsup

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
