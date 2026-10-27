module

public import CFSG.Quasithin.Vol2.Ch3E213MP4C6
public import CFSG.Quasithin.Vol2.Ch3E213MSL2PairE
public import CFSG.Permutation.UnitaryThreeRecognition.ModelTransport

public section

namespace CFSG.Quasithin.Ch3E213M

open CFSG.Open CFSG.QuasithinUnique B6
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)
open CFSG.QuasithinUnique.Setup (oddResidualPreimage)

namespace P4C

theorem nonempty_equiv_star_of_case2 {G : Type} [Group G] [Finite G] {H T M V K : Subgroup G}
    (hS : Setting H T M V K) (h2 : Case2 H T M K) :
    Nonempty (↥((oddResidualPreimage H).map (QuotientGroup.mk' (kerIn (M.subgroupOf H) ⊤))) ≃*
      ↥(E2.star M H K)) := by
  rw [map_oddResidualPreimage_eq_of_case2 hS h2]
  exact nonempty_mulEquiv_star hS.hyp.minParabolic.maximal.1.le K

theorem pair_of_u3
    {G : Type} [Group G] [Finite G]
    {H T M V K : Subgroup G} (hS : Setting H T M V K) (h2 : Case2 H T M K) {n : ℕ} (hn : 2 ≤ n)
    (hU : IsPSU 3 2 n ↥(E2.star M H K)) :
    ∃ T' : Sylow 2 ↥H, (T' : Subgroup H) = T.subgroupOf H ∧
      SL2Pair.Pair T' (M.subgroupOf H) (V.subgroupOf H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVH : V ≤ H := hS.hyp.le_H
  obtain ⟨T', hT', hcharH, hTn, hTM', hMH', hmax', hel, hVT', hTV', hVM', -⟩ :=
    qrcHyp_of_hyp28 hS.hyp hS.charTwo
  have := hel
  have hVQ' : 4 ≤ (V.subgroupOf H ⊓ CFSG.pCore 2 H).relIndex (V.subgroupOf H) := by
    rw [relIndex_subgroupOf_inf_pCore hVH]
    exact hS.four_le
  obtain ⟨eK⟩ := nonempty_equiv_star_of_case2 hS h2
  obtain ⟨-, k, _, _, hk, ⟨e⟩⟩ := hU
  obtain ⟨J, hJ, -, hfix⟩ :=
    CFSG.UnitaryThreeRecognition.Model.exists_standardHermitianForm (K := k) 2 n hk
  obtain ⟨e'⟩ := CFSG.UnitaryThreeRecognition.Model.nonempty_psu_equiv_statedProj J (2 ^ n) hk hfix
  exact ⟨T', hT', qrc_unitary_pair hS.not_solvable hcharH T' hTn hTM' hMH' hmax' hVT' hTV' hVM'
    hVQ' hn J hk hfix hJ ((eK.trans e).trans e'.symm)⟩

end P4C

theorem pkgBenderU3 :
    ∀ (G : Type) [Group G] [Finite G] (H T M V K : Subgroup G), Setting H T M V K →
      Case2 H T M K → ∀ n : ℕ, 2 ≤ n → IsPSU 3 2 n ↥(E2.star M H K) →
      E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K)) → E213Concl H T M V := by
  intro G _ _ H T M V K hS h2 n hn hU _
  obtain ⟨T', hT', hP⟩ := P4C.pair_of_u3 hS h2 hn hU
  exact SL2Pair.e213Concl_of_pair hS hT' hP

end CFSG.Quasithin.Ch3E213M
