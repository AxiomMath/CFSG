module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearPostNineData
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2UniformReflectionFixed
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationElevenData
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralCore
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourCentralizerTransport
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Klein-four centralizers in the aligned linear branch

Every Klein four subgroup of the component can be conjugated inside the
component into the fixed dihedral Sylow subgroup.  It then contains the
central involution `t` and a reflection.  The decomposition `H = U S` and
the uniform reflection fixed subgroup identify its centralizer with elements
whose `U` and `S` coordinates both lie in `M`.
-/

noncomputable section
open scoped Pointwise
namespace CFSG.GorensteinWalter
universe u

/-- The centralizer of every Klein four subgroup of the selected component
is contained in the second-case maximal subgroup. -/
public theorem secondCase_linear_kleinFour_centralizer_le_M
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (post : SecondCaseLinearPostNineData c w d K)
    (V : Subgroup G) (hVleE : V ≤ d.E) (hVK : IsKleinFour V) :
    Subgroup.centralizer (V : Set G) ≤ w.M := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSleM : (c.S : Subgroup G) ≤ w.M :=
    post.hSleE.trans d.E_component.1
  let VE : Subgroup d.E := V.subgroupOf d.E
  have hVE2 : IsPGroup 2 VE := by
    apply IsPGroup.of_equiv (G := V)
      (IsPGroup.of_card (n := 2) (by simpa using hVK.card_four))
      (Subgroup.subgroupOfEquivOfLe hVleE).symm
  have hSE2 : IsPGroup 2 ((c.S : Subgroup G).subgroupOf d.E) :=
    c.S.isPGroup'.comap_subtype
  have hSEidx : ¬ 2 ∣ ((c.S : Subgroup G).subgroupOf d.E).index := by
    have hdvd : ((c.S : Subgroup G).subgroupOf d.E).index ∣
        (c.S : Subgroup G).index := by
      simpa [Subgroup.relIndex] using
        (Subgroup.relIndex_dvd_index_of_le post.hSleE)
    intro htwo
    exact c.S.not_dvd_index (htwo.trans hdvd)
  let SE : Sylow 2 d.E := hSE2.toSylow hSEidx
  obtain ⟨Q, hVEQ⟩ := hVE2.exists_le_sylow
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq d.E Q SE
  have hVEa : VE.map (MulAut.conj a).toMonoidHom ≤ (SE : Subgroup d.E) := by
    rw [← ha]
    exact Subgroup.map_mono hVEQ
  let V' : Subgroup G := conjugateSubgroup V (a : G)
  have hV'leS : V' ≤ (c.S : Subgroup G) := by
    intro z hz
    rcases Subgroup.mem_map.mp hz with ⟨v, hv, rfl⟩
    let vE : d.E := ⟨v, hVleE hv⟩
    have hvmap : (MulAut.conj a).toMonoidHom vE ∈
        VE.map (MulAut.conj a).toMonoidHom := by
      apply Subgroup.mem_map.mpr
      exact ⟨vE, Subgroup.mem_subgroupOf.mpr hv, rfl⟩
    have hvSE : (MulAut.conj a).toMonoidHom vE ∈ (SE : Subgroup d.E) :=
      hVEa hvmap
    change (a : G) * v * (a : G)⁻¹ ∈ (c.S : Subgroup G)
    exact hvSE
  have hV'K : IsKleinFour V' := by
    change IsKleinFour (V.map (MulAut.conj (a : G)).toMonoidHom)
    exact isKleinFour_map_mulEquiv V hVK (MulAut.conj (a : G))
  let VS : Subgroup c.S := V'.subgroupOf (c.S : Subgroup G)
  have hVSK : IsKleinFour VS := by
    let eVS : VS ≃* V' := Subgroup.subgroupOfEquivOfLe hV'leS
    exact {
      card_four := (Nat.card_congr eVS.toEquiv).trans hV'K.card_four
      exponent_two := (Monoid.exponent_eq_of_mulEquiv eVS).trans hV'K.exponent_two
    }
  let tS : c.S := ⟨c.t, c.S0_le_S c.t_mem_S0⟩
  have htCenter : tS ∈ Subgroup.center c.S := by
    apply Subgroup.mem_center_iff.mpr
    intro y
    apply Subtype.ext
    have hyH : (y : G) ∈ c.H := centralizerSetup_S_le_H c y.2
    rw [c.H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff] at hyH
    change (y : G) * c.t = c.t * (y : G)
    exact hyH
  have htVS : tS ∈ VS :=
    center_mem_kleinFour_of_dihedral_mulEquiv c.one_le_m
      c.dihedralEquiv.some VS hVSK htCenter
  have htV' : c.t ∈ V' := Subgroup.mem_subgroupOf.mp htVS
  let : Fintype V' := Fintype.ofFinite V'
  have hthree : 3 ≤ ENat.card V' := by
    rw [ENat.card_eq_coe_fintype_card, ← Nat.card_eq_fintype_card,
      hV'K.card_four]
    norm_num
  let tV : V' := ⟨c.t, htV'⟩
  obtain ⟨sV, hs1, hst⟩ :=
    ENat.exists_ne_ne_of_three_le hthree (1 : V') tV
  let s : G := sV
  have hsV' : s ∈ V' := sV.2
  have hsS : s ∈ (c.S : Subgroup G) := hV'leS hsV'
  have hsne : s ≠ 1 := by
    intro hs
    apply hs1
    apply Subtype.ext
    exact hs
  have hstG : s ≠ c.t := by
    intro hs
    apply hst
    apply Subtype.ext
    exact hs
  have hssq : s ^ 2 = 1 := by
    have hs := congrArg Subtype.val (hV'K.mul_self sV)
    simpa [pow_two, s] using hs
  have hsS0 : s ∉ c.S0 := by
    intro hs0
    let Zs : Subgroup G := Subgroup.zpowers s
    let Zt : Subgroup G := Subgroup.zpowers c.t
    have hZsle : Zs ≤ c.S0 := Subgroup.zpowers_le.mpr hs0
    have hZtle : Zt ≤ c.S0 := Subgroup.zpowers_le.mpr c.t_mem_S0
    have hsord : orderOf s = 2 := orderOf_eq_prime hssq hsne
    have htord : orderOf c.t = 2 := orderOf_eq_prime c.t_involution.2 c.t_involution.1
    have hZscard : Nat.card Zs = 2 := by rw [Nat.card_zpowers, hsord]
    have hZtcard : Nat.card Zt = 2 := by rw [Nat.card_zpowers, htord]
    have htwoS0 : 2 ∣ Nat.card c.S0 := by
      rw [← hZtcard]
      exact Subgroup.card_dvd_of_le hZtle
    obtain ⟨H0, hH0, huniq⟩ :=
      secondCase_unique_order_p_subgroup_of_cyclic
        (G := G) (T := c.S0) c.S0_cyclic rfl htwoS0
    have hZseq : Zs = H0 := huniq Zs ⟨hZsle, hZscard⟩
    have hZteq : Zt = H0 := huniq Zt ⟨hZtle, hZtcard⟩
    have hsZt : s ∈ Zt := by
      rw [hZteq, ← hZseq]
      exact Subgroup.mem_zpowers s
    let sZ : Zt := ⟨s, hsZt⟩
    let tZ : Zt := ⟨c.t, Subgroup.mem_zpowers c.t⟩
    obtain ⟨z, hz1, hzuniq⟩ := (Nat.card_eq_two_iff' (1 : Zt)).mp hZtcard
    have htZne : tZ ≠ 1 := by
      intro ht
      exact c.t_involution.1 (congrArg Subtype.val ht)
    have hsZne : sZ ≠ 1 := by
      intro hs
      exact hsne (congrArg Subtype.val hs)
    have htzeq : tZ = z := hzuniq tZ htZne
    have hszeq : sZ = z := hzuniq sZ hsZne
    exact hstG (congrArg Subtype.val (hszeq.trans htzeq.symm))
  have hBfull : post.od.F = centralizerIn c.FU (post.od.s : G) := by
    exact (full_fixed_subgroups_of_nilpotent_normalizer_eq
      c.U c.FU w.M post.od.F post.od.B (post.od.s : G)
      (fittingSubgroupOf_isNilpotent c.U)
      (fittingSubgroupOf_isNormalIn c.U)
      post.od.F_fixed post.od.B_fixed post.od.F_normalizer).1
  have hNFfull : Subgroup.normalizer
      (centralizerIn c.FU (post.od.s : G) : Set G) = w.M := by
    rw [← hBfull]
    exact post.od.F_normalizer
  have hCU : centralizerIn c.U s = post.od.B :=
    secondCase_psl2_uniform_reflection_fixed hmin c w d post.od.s post.od.B
      post.od.B_fixed post.hsS post.hsS0 post.hSleE
      post.S0_centralizes_U hNFfull s hsS hsS0
  have hBleM : post.od.B ≤ w.M := by
    rw [post.od.B_fixed]
    exact inf_le_left.trans inf_le_right
  have hUnormal : IsNormalIn c.U c.H := centralizerSetup_U_isNormalIn_H c
  have hUinfS : c.U ⊓ (c.S : Subgroup G) = ⊥ := by
    have hUodd : Odd (Nat.card c.U) := by
      change Odd (Nat.card (oddCoreOf c.H))
      exact odd_card_oddCoreOf c.H
    rcases c.S.isPGroup'.exists_card_eq with ⟨n, hn⟩
    have hcop : Nat.Coprime (Nat.card c.U) (Nat.card c.S) := by
      rw [hn]
      exact hUodd.coprime_two_right.pow_right n
    exact (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  have hSNormU : (c.S : Subgroup G) ≤ Subgroup.normalizer (c.U : Set G) :=
    (centralizerSetup_S_le_H c).trans
      (le_normalizer_of_isNormalIn hUnormal)
  have hHprod : (c.H : Set G) = (c.U : Set G) * ((c.S : Subgroup G) : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left c.U (c.S : Subgroup G) hSNormU]
    rw [sup_comm, fact_2_preamble_H_eq_SU_proved hmin c]
  have hCentV' : Subgroup.centralizer (V' : Set G) ≤ w.M := by
    intro z hz
    have hzt : z * c.t = c.t * z :=
      ((Subgroup.mem_centralizer_iff.mp hz) c.t htV').symm
    have hzH : z ∈ c.H := by
      rw [c.H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
      exact hzt
    have hzprod : z ∈ (c.U : Set G) * ((c.S : Subgroup G) : Set G) := by
      rw [← hHprod]
      exact hzH
    rcases hzprod with ⟨u, hu, sigma, hsigma, huz⟩
    change u * sigma = z at huz
    have hzcomm : z * s = s * z :=
      ((Subgroup.mem_centralizer_iff.mp hz) s hsV').symm
    have h1 : u * (sigma * s) = s * u * sigma := by
      calc
        u * (sigma * s) = (u * sigma) * s := by group
        _ = z * s := by rw [huz]
        _ = s * z := hzcomm
        _ = s * (u * sigma) := by rw [huz]
        _ = s * u * sigma := by group
    let b : G := sigma * s * sigma⁻¹
    have hbS : b ∈ (c.S : Subgroup G) := by
      exact c.S.mul_mem (c.S.mul_mem hsigma hsS) (c.S.inv_mem hsigma)
    have h2 : u * b * u⁻¹ = s := by
      dsimp [b]
      calc
        u * (sigma * s * sigma⁻¹) * u⁻¹ =
            (u * (sigma * s) * sigma⁻¹) * u⁻¹ := by group
        _ = ((s * u * sigma) * sigma⁻¹) * u⁻¹ := by rw [h1]
        _ = s := by group
    have hcommU : u * b * u⁻¹ * b⁻¹ ∈ c.U := by
      have hbHu : b * u⁻¹ * b⁻¹ ∈ c.U :=
        hUnormal.2 b (centralizerSetup_S_le_H c hbS) u⁻¹ (c.U.inv_mem hu)
      simpa [mul_assoc] using c.U.mul_mem hu hbHu
    have hsbS : s * b⁻¹ ∈ (c.S : Subgroup G) :=
      c.S.mul_mem hsS (c.S.inv_mem hbS)
    have hsbU : s * b⁻¹ ∈ c.U := by
      rw [← h2]
      exact hcommU
    have hsb1 : s * b⁻¹ = 1 := by
      have hmem : s * b⁻¹ ∈ c.U ⊓ (c.S : Subgroup G) := ⟨hsbU, hsbS⟩
      rw [hUinfS] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hbeq : b = s := by
      have hinv : b⁻¹ = s⁻¹ := by
        calc
          b⁻¹ = s⁻¹ * (s * b⁻¹) := by group
          _ = s⁻¹ := by rw [hsb1]; simp
      exact inv_injective hinv
    have hsigcomm : sigma * s = s * sigma := by
      calc
        sigma * s = sigma * s * sigma⁻¹ * sigma := by group
        _ = b * sigma := by rfl
        _ = s * sigma := by rw [hbeq]
    have hucomm : u * s = s * u := by
      calc
        u * s = u * s * sigma * sigma⁻¹ := by group
        _ = u * (s * sigma) * sigma⁻¹ := by group
        _ = u * (sigma * s) * sigma⁻¹ := by rw [hsigcomm]
        _ = (s * u * sigma) * sigma⁻¹ := by rw [h1]
        _ = s * u := by group
    have huB : u ∈ post.od.B := by
      rw [← hCU]
      change u ∈ c.U ∧ u ∈ Subgroup.centralizer ({s} : Set G)
      refine ⟨hu, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro y hy
      simp only [Set.mem_singleton_iff] at hy
      subst y
      exact hucomm.symm
    have huM : u ∈ w.M := hBleM huB
    have hsigmaM : sigma ∈ w.M := hSleM hsigma
    rw [← huz]
    exact w.M.mul_mem huM hsigmaM
  intro z hz
  have hza : (a : G) * z * (a : G)⁻¹ ∈
      Subgroup.centralizer (V' : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨v, hv, hvy⟩
    have hzv : z * v = v * z :=
      ((Subgroup.mem_centralizer_iff.mp hz) v hv).symm
    change (a : G) * v * (a : G)⁻¹ = y at hvy
    rw [← hvy]
    change ((a : G) * v * (a : G)⁻¹) *
        ((a : G) * z * (a : G)⁻¹) =
      ((a : G) * z * (a : G)⁻¹) *
        ((a : G) * v * (a : G)⁻¹)
    calc
      ((a : G) * v * (a : G)⁻¹) * ((a : G) * z * (a : G)⁻¹) =
          (a : G) * (v * z) * (a : G)⁻¹ := by group
      _ = (a : G) * (z * v) * (a : G)⁻¹ := by rw [hzv]
      _ = ((a : G) * z * (a : G)⁻¹) *
          ((a : G) * v * (a : G)⁻¹) := by group
  have hzaM := hCentV' hza
  have haM : (a : G) ∈ w.M := d.E_component.1 a.2
  have hzexpr : z = (a : G)⁻¹ * ((a : G) * z * (a : G)⁻¹) * (a : G) := by
    group
  rw [hzexpr]
  exact w.M.mul_mem (w.M.mul_mem (w.M.inv_mem haM) hzaM) haM

end CFSG.GorensteinWalter
