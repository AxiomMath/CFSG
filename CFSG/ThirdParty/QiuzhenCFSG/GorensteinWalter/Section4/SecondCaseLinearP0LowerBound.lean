module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearPostNineData
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearP0Odd
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearPNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearOmegaTrichotomy
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearOmegaInversionEndpoint
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearNoNormalInvertedException
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalizerSubgroupCyclic
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The lower bound on the line-normalizer parameter

The relative index `p₀ = |N_U(A):N_U(P)|` is odd.  It is not one: in the
three omega alternatives, either the normalizer condition in the characteristic
`p`-subgroup supplies an element normalizing `A` but not `P`, or the inversion
alternative supplies such an element from `F(U)`; in the equality alternative,
`A` is normal in `U`, and `p₀ = 1` would force `U ≤ M`, contradicting
`H ⊄ M` after `S ≤ E ≤ M`.  Oddness then gives `3 ≤ p₀`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The source lower bound `3 ≤ p₀` for the linear equation-(11) parameter. -/
public theorem secondCase_linear_p0_ge_three
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (post : SecondCaseLinearPostNineData c w d K) :
    3 ≤ post.indices.p0 := by
  classical
  let : Fact post.od.p.Prime := ⟨post.od.hp_prime⟩
  let QG : Subgroup G := post.od.Q.map c.U.subtype
  have hQnormalU : IsNormalIn QG c.U := by
    change IsNormalIn (post.od.Q.map c.U.subtype) c.U
    exact map_characteristic_isNormalIn_of_isNormalIn post.od.Q
      post.od.Q_characteristic
      ⟨le_rfl, by
        intro u hu x hx
        exact c.U.mul_mem (c.U.mul_mem hu hx) (c.U.inv_mem hu)⟩
  have hQGp : IsPGroup post.od.p QG := by
    intro x
    refine ⟨1, ?_⟩
    let eQ : post.od.Q ≃* QG :=
      Subgroup.equivMapOfInjective post.od.Q c.U.subtype
        c.U.subtype_injective
    have hQexp : Monoid.exponent QG = post.od.p :=
      (Monoid.exponent_eq_of_mulEquiv eQ).symm.trans post.od.Q_exponent
    have hx : x ^ post.od.p = 1 :=
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (by rw [hQexp]) x)
    simpa using hx
  have hQGleU : QG ≤ c.U := by
    intro z hz
    rcases Subgroup.mem_map.mp hz with ⟨z0, hz0, hzEq⟩
    rw [← hzEq]
    exact z0.2
  have hSleM : (c.S : Subgroup G) ≤ w.M :=
    post.hSleE.trans d.E_component.1
  have hUnotM : ¬ c.U ≤ w.M := by
    intro hU
    apply secondCase_H_not_le_M hmin c w
    rw [← fact_2_preamble_H_eq_SU_proved hmin c]
    exact sup_le hSleM hU
  have hNP : Subgroup.normalizer (post.od.P : Set G) = w.M :=
    secondCase_linear_P_normalizer_eq_M c w d post.od
  have hNUPleNA : normalizerIn c.U post.od.P ≤
      normalizerIn c.U post.od.A :=
    secondCase_linear_omega_NU_P_le_NU_A c w d post.od
  have hrelne :
      (normalizerIn c.U post.od.P).relIndex
        (normalizerIn c.U post.od.A) ≠ 1 := by
    intro hone
    have hNAleNP : normalizerIn c.U post.od.A ≤
        normalizerIn c.U post.od.P :=
      (Subgroup.relIndex_eq_one.mp hone)
    have htri := secondCase_linear_omega_trichotomy c w d post.od
    dsimp at htri
    rcases htri with heq | hstrict | hinv
    · have hAnormalU : IsNormalIn post.od.A c.U := by
        rw [heq]
        exact hQnormalU
      have hNUAeq : normalizerIn c.U post.od.A = c.U := by
        apply le_antisymm inf_le_left
        intro u hu
        exact ⟨hu, le_normalizer_of_isNormalIn hAnormalU hu⟩
      have hUleNUP : c.U ≤ normalizerIn c.U post.od.P := by
        intro u hu
        have huNA : u ∈ normalizerIn c.U post.od.A := by
          rw [hNUAeq]
          exact hu
        exact hNAleNP huNA
      have hUleM : c.U ≤ w.M := by
        have hUleN : c.U ≤ Subgroup.normalizer (post.od.P : Set G) := by
          intro u hu
          exact (hUleNUP hu).2
        rw [hNP] at hUleN
        exact hUleN
      exact hUnotM hUleM
    · have hAleQ : post.od.A ≤ QG := hstrict.2.1.le
      have hAQproper : post.od.A.subgroupOf QG < (⊤ : Subgroup QG) := by
        apply lt_top_iff_ne_top.mpr
        intro htop
        exact (not_le_of_gt hstrict.2.1)
          (Subgroup.subgroupOf_eq_top.mp htop)
      let : Group.IsNilpotent QG := hQGp.isNilpotent
      have hnorm : post.od.A.subgroupOf QG <
          Subgroup.normalizer ((post.od.A.subgroupOf QG : Subgroup QG) : Set QG) :=
        Group.normalizerCondition_of_isNilpotent _ hAQproper
      have hnotle : ¬ Subgroup.normalizer
          ((post.od.A.subgroupOf QG : Subgroup QG) : Set QG) ≤
            post.od.A.subgroupOf QG := not_le_of_gt hnorm
      rcases Set.not_subset.mp hnotle with ⟨z, hzN, hznotA⟩
      have hzN' : (z : G) ∈ Subgroup.normalizer (post.od.A : Set G) := by
        have hzInf : (z : QG) ∈
            (QG ⊓ Subgroup.normalizer (post.od.A : Set G)).subgroupOf QG := by
          rw [← normalizer_subgroupOf_eq_subgroupOf_inf_normalizer QG post.od.A hAleQ]
          exact hzN
        exact (Subgroup.mem_subgroupOf.mp hzInf).2
      have hzNA : (z : G) ∈ normalizerIn c.U post.od.A :=
        ⟨hQGleU z.2, hzN'⟩
      have hznotNP : (z : G) ∉ Subgroup.normalizer (post.od.P : Set G) := by
        intro hzP
        have hzAmem : (z : G) ∈ post.od.A := by
          exact (secondCase_linear_omega_conjugation_control c w d post.od).1
            ⟨hzP, z.2⟩
        have hzAQ : z ∈ post.od.A.subgroupOf QG :=
          Subgroup.mem_subgroupOf.mpr hzAmem
        exact hznotA hzAQ
      exact hznotNP ((hNAleNP hzNA).2)
    · have hFfull : post.od.F = centralizerIn c.FU (post.od.s : G) := by
        have hfull := full_fixed_subgroups_of_nilpotent_normalizer_eq
          c.U c.FU w.M post.od.F post.od.B (post.od.s : G)
          (_root_.CFSG.fittingSubgroupOf_isNilpotent c.U)
          (fittingSubgroupOf_isNormalIn c.U)
          post.od.F_fixed post.od.B_fixed post.od.F_normalizer
        exact hfull.1
      have hno := secondCase_linear_no_normal_inverted_exception
        hmin c post.S0_centralizes_U (post.od.s : G)
        post.hsS post.hsS0
      have hend := secondCase_linear_omega_inversion_endpoint
        hmin c w d post.od hFfull hinv
      have hAnormalFU : IsNormalIn post.od.A c.FU :=
        hend.2 hno |>.2
      obtain ⟨I, hIdef, hIeq, hInormalU, hIleFU⟩ :=
        secondCase_linear_omega_invertedElements_le_fitting
          c w d post.od hFfull hinv
      have hUodd : Odd (Nat.card c.U) := by
        change Odd (Nat.card (oddCoreOf c.H))
        exact odd_card_oddCoreOf c.H
      have hsU : ∀ x : G, x ∈ c.U →
          (post.od.s : G) * x * (post.od.s : G)⁻¹ ∈ c.U :=
        (centralizerSetup_U_isNormalIn_H c).2
          (post.od.s : G) post.od.s_mem_H
      have hcopU : Nat.Coprime 2 (Nat.card c.U) :=
        Nat.coprime_two_left.mpr hUodd
      have hUeq : c.U = post.od.B ⊔ c.FU := by
        apply le_antisymm
        · intro x hx
          rcases fact_1_5_ii_decomposition post.od.s_involution hcopU hsU x hx with
            ⟨b, hb, i, hi, hxi⟩
          have hNFfull : Subgroup.normalizer
              (centralizerIn c.FU (post.od.s : G) : Set G) = w.M := by
            rw [← hFfull]
            exact post.od.F_normalizer
          have hCU : centralizerIn c.U (post.od.s : G) = post.od.B :=
            secondCase_psl2_uniform_reflection_fixed
              hmin c w d post.od.s post.od.B post.od.B_fixed
              post.hsS post.hsS0 post.hSleE post.S0_centralizes_U hNFfull
              (post.od.s : G) post.hsS post.hsS0
          have hbB : b ∈ post.od.B := by
            rw [← hCU]
            exact hb
          have hiFU : i ∈ c.FU := by
            have hiI : i ∈ (I : Set G) := by
              rw [hIeq]
              exact hi
            exact hIleFU hiI
          rw [hxi]
          exact (post.od.B ⊔ c.FU).mul_mem
            (Subgroup.mem_sup_left hbB) (Subgroup.mem_sup_right hiFU)
        · exact sup_le
            (by
              rw [post.od.B_fixed]
              change (c.U ⊓ w.M) ⊓ Subgroup.centralizer
                ({(post.od.s : G)} : Set G) ≤ c.U
              exact inf_le_left.trans inf_le_left)
            (fittingSubgroupOf_le c.U)
      have hBleM : post.od.B ≤ w.M := by
        intro b hb
        have hbUM : b ∈ c.U ⊓ w.M := by
          rw [← post.od.U_inter_M_eq]
          exact Subgroup.mem_sup_right hb
        exact hbUM.2
      have hFUnotM : ¬ c.FU ≤ w.M := by
        intro hFU
        apply hUnotM
        rw [hUeq]
        exact sup_le hBleM hFU
      rcases Set.not_subset.mp hFUnotM with ⟨f, hfFU, hfnotM⟩
      have hfNA : f ∈ normalizerIn c.U post.od.A := by
        refine ⟨fittingSubgroupOf_le c.U hfFU, ?_⟩
        exact le_normalizer_of_isNormalIn hAnormalFU hfFU
      have hfnotNP : f ∉ Subgroup.normalizer (post.od.P : Set G) := by
        intro hfP
        apply hfnotM
        rw [← hNP]
        exact hfP
      exact hfnotNP ((hNAleNP hfNA).2)
  have hp0ne : post.indices.p0 ≠ 1 := by
    intro h
    apply hrelne
    rw [← post.indices.p0_def]
    exact h
  have hp0odd : Odd post.indices.p0 :=
    secondCase_linear_p0_odd c w d post.od post.indices.p0 post.indices.p0_def
  rcases hp0odd with ⟨k, hk⟩
  omega

end CFSG.GorensteinWalter
