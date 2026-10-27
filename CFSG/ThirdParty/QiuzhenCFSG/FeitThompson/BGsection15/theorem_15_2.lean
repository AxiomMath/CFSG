module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection15.lemma_15_1
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.CentralizerControl
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Conjugacy
import Mathlib.Algebra.Group.Subgroup.Order
import Mathlib.GroupTheory.Schreier

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise commutatorElement

/-! # Theorem 15 2 from BG Section 15 -/

section Section15

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]
omit [IsMinCE G] in
public theorem CFSG.section15_sylow_le_normal_hall_of_mem
    {H : Type*} [Group H] [Finite H] {π : Set Nat.Primes} {S : Subgroup H}
    [S.Normal] (hSHall : IsHallSubgroup π S) {p : Nat.Primes} (hpπ : p ∈ π)
    (P : Sylow p.val H) :
    (P : Subgroup H) ≤ S := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  let PS : Sylow p.val S := Classical.choice (Sylow.nonempty (p := p.val) (G := S))
  let Psub : Subgroup H := (PS : Subgroup S).map S.subtype
  have hPsub_p : IsPGroup p.val Psub :=
    IsPGroup.map (p := p.val) (H := (PS : Subgroup S)) PS.isPGroup' S.subtype
  have hp_not_S_index : ¬ p.val ∣ S.index := by
    intro hp_dvd
    exact (hSHall.p_in_pi_of_p_dvd_index p hp_dvd) hpπ
  have hp_not_Psub_index : ¬ p.val ∣ Psub.index := by
    intro hp_dvd
    have hidx : Psub.index = (PS : Subgroup S).index * S.index := by
      simpa [Psub] using
        (Subgroup.index_map_subtype (H := S) (K := (PS : Subgroup S)))
    have hp_prod : p.val ∣ (PS : Subgroup S).index * S.index := by
      simpa [hidx] using hp_dvd
    rcases p.property.dvd_or_dvd hp_prod with hp_PS | hp_S
    · exact PS.not_dvd_index hp_PS
    · exact hp_not_S_index hp_S
  let Q : Sylow p.val H := hPsub_p.toSylow hp_not_Psub_index
  have hQ_le_S : (Q : Subgroup H) ≤ S := by
    intro x hx
    have hxPsub : x ∈ Psub := by
      simpa [Q] using hx
    rcases Subgroup.mem_map.mp hxPsub with ⟨y, _hy, rfl⟩
    exact y.property
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H Q P
  have hgQ_le_S : ((g • Q : Sylow p.val H) : Subgroup H) ≤ S := by
    intro x hx
    rw [Sylow.coe_subgroup_smul] at hx
    have hx' : g⁻¹ * x * g ∈ (Q : Subgroup H) := by
      simpa [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
        MulAut.conj_apply, mul_assoc] using hx
    have hxS' : g⁻¹ * x * g ∈ S := hQ_le_S hx'
    simpa [mul_assoc] using ((inferInstance : S.Normal).conj_mem (g⁻¹ * x * g) hxS' g)
  simpa [hg] using hgQ_le_S

public theorem CFSG.section15_prime_mem_sigma_of_nilpotentNormalHallIn
    {M H : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hH : section15NilpotentNormalHallIn H M)
    {p : Nat.Primes} (hpH : p ∈ subgroupPrimeSet H) :
    p ∈ section10SigmaPrimes M := by
  classical
  rcases hH with ⟨hHM, hHnormM, hHnil, hHHall⟩
  haveI : Fact p.val.Prime := ⟨p.property⟩
  let P : Sylow p.val M := Classical.choice (Sylow.nonempty (p := p.val) (G := M))
  have hpM : p ∈ subgroupPrimeSet M :=
    section8_subgroupPrimeSet_mono hHM hpH
  have hP_le_Hsub : (P : Subgroup M) ≤ H.subgroupOf M := by
    haveI : (H.subgroupOf M).Normal := hHnormM
    exact section15_sylow_le_normal_hall_of_mem hHHall hpH P
  let S : Subgroup M := H.subgroupOf M
  let PS : Sylow p.val S := P.subtype (by simpa [S] using hP_le_Hsub)
  have hS_nil : Group.IsNilpotent S := by
    let e : S ≃* H := Subgroup.subgroupOfEquivOfLe (H := H) (K := M) hHM
    exact Group.nilpotent_of_mulEquiv (G := H) (G' := S) (_h := hHnil) e.symm
  have hPS_normal : (PS : Subgroup S).Normal :=
    Group.IsNilpotent.sylow_normal hS_nil p.val PS
  haveI : (PS : Subgroup S).Characteristic :=
    Sylow.characteristic_of_normal PS hPS_normal
  haveI : S.Normal := by
    simpa [S] using hHnormM
  have hPS_map_normal : ((PS : Subgroup S).map S.subtype).Normal := by
    infer_instance
  have hPS_map_eq : (PS : Subgroup S).map S.subtype = (P : Subgroup M) := by
    change Subgroup.map S.subtype ((P : Subgroup M).subgroupOf S) = (P : Subgroup M)
    exact Subgroup.map_subgroupOf_eq_of_le (by simpa [S] using hP_le_Hsub)
  have hP_normal_M : (P : Subgroup M).Normal := by
    simpa [hPS_map_eq] using hPS_map_normal
  let PG : Subgroup G := section10AmbientSylowSubgroup M P
  have hPG_le_M : PG ≤ M := by
    intro x hx
    have hxmap : x ∈ (P : Subgroup M).map M.subtype := by
      simpa [PG, section10AmbientSylowSubgroup] using hx
    rcases Subgroup.mem_map.mp hxmap with ⟨y, _hy, rfl⟩
    exact y.property
  have hp_dvd_P : p.val ∣ Nat.card (P : Subgroup M) :=
    Sylow.dvd_card_of_dvd_card P (by simpa [subgroupPrimeSet] using hpM)
  have hP_ne_bot : (P : Subgroup M) ≠ ⊥ := by
    intro hPbot
    have hcard : Nat.card (P : Subgroup M) = 1 := by
      simp [hPbot]
    exact p.property.not_dvd_one (by simpa [hcard] using hp_dvd_P)
  have hPG_ne_bot : PG ≠ ⊥ := by
    intro hPGbot
    have hPbot : (P : Subgroup M) = ⊥ := by
      have hmapbot : (P : Subgroup M).map M.subtype = ⊥ := by
        simpa [PG, section10AmbientSylowSubgroup] using hPGbot
      exact
        (Subgroup.map_eq_bot_iff_of_injective
          (H := (P : Subgroup M)) (f := M.subtype) M.subtype_injective).1 hmapbot
    exact hP_ne_bot hPbot
  have hPG_subgroupOf_normal : (PG.subgroupOf M).Normal := by
    have hsub_eq : PG.subgroupOf M = (P : Subgroup M) := by
      simpa [PG, section10AmbientSylowSubgroup] using
        (subgroupOf_map_subtype_eq (K := M) (P : Subgroup M))
    simpa [hsub_eq] using hP_normal_M
  have hnorm_eq : Subgroup.normalizer (PG : Set G) = M :=
    section8_normalizer_eq_of_nontrivial_normal_in_maximal
      hM hPG_le_M hPG_ne_bot hPG_subgroupOf_normal
  refine ⟨hpM, P, ?_⟩
  exact (le_of_eq hnorm_eq : Subgroup.normalizer (PG : Set G) ≤ M)

/-- Theorem 15.2 L001-S0010: the Section 15 construction of `M_F` places it
inside `M_σ`.  This is the Lean interface for the source preamble sentence that
`M_F` is the product of the normal Sylow subgroups of `M` and lies in
`M_σ`. -/
public theorem CFSG.section15_MF_le_msigma
    {M MF : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF) :
    MF ≤ section10Msigma M := by
  classical
  rcases hMF.1 with ⟨hMFM, hMFnormM, hMFnil, hMFHall⟩
  have hMFπ : IsPiSubgroup (G := G) (section10SigmaPrimes M) MF := by
    intro p hpMF
    exact section15_prime_mem_sigma_of_nilpotentNormalHallIn
      hM ⟨hMFM, hMFnormM, hMFnil, hMFHall⟩ hpMF
  have hcore : MF ≤ piCoreIn (section10SigmaPrimes M) M :=
    section8_le_piCoreIn_of_normal_isPiSubgroup hMFM hMFnormM hMFπ
  simpa [section10Msigma, section10MsigmaSubgroup, piCoreIn] using hcore

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_hallSubgroupIn_map_subtype
    {π : Set Nat.Primes} {H : Subgroup G} {K : Subgroup H}
    (hK : IsHallSubgroup π K) :
    section12HallSubgroupIn π (K.map H.subtype) H := by
  have hKH : K.map H.subtype ≤ H := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  refine ⟨hKH, ?_⟩
  have hsub_eq : (K.map H.subtype).subgroupOf H = K := by
    ext x
    constructor
    · intro hx
      change ((x : H) : G) ∈ K.map H.subtype at hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, hyx⟩
      have hy_eq : y = x := Subtype.ext hyx
      simpa [hy_eq] using hy
    · intro hx
      change ((x : H) : G) ∈ K.map H.subtype
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  simpa [hsub_eq] using hK

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_coprime_card_of_hall_disjoint_primes
    {H : Type*} [Group H] [Finite H]
    {π ρ : Set Nat.Primes} {A B : Subgroup H}
    (hA : IsHallSubgroup π A) (hB : IsHallSubgroup ρ B)
    (hπρ : Disjoint π ρ) :
    Nat.Coprime (Nat.card A) (Nat.card B) := by
  refine Nat.coprime_of_dvd ?_
  intro q hqprime hqA hqB
  let q' : Nat.Primes := ⟨q, hqprime⟩
  have hqπ : q' ∈ π := hA.p_in_pi_of_p_dvd_card q' hqA
  have hqρ : q' ∈ ρ := hB.p_in_pi_of_p_dvd_card q' hqB
  exact (Set.disjoint_left.mp hπρ hqπ) hqρ

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_disjoint_of_hall_disjoint_primes
    {H : Type*} [Group H] [Finite H]
    {π ρ : Set Nat.Primes} {A B : Subgroup H}
    (hA : IsHallSubgroup π A) (hB : IsHallSubgroup ρ B)
    (hπρ : Disjoint π ρ) :
    Disjoint A B := by
  rw [Subgroup.disjoint_def]
  intro x hxA hxB
  have hcop : Nat.Coprime (Nat.card A) (Nat.card B) := by
    exact section15_coprime_card_of_hall_disjoint_primes hA hB hπρ
  have hcop_order : Nat.Coprime (orderOf x) (Nat.card B) :=
    Nat.Coprime.of_dvd_left (Subgroup.orderOf_dvd_natCard A hxA) hcop
  have hx_order_one : orderOf x = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop_order dvd_rfl
      (Subgroup.orderOf_dvd_natCard B hxB)
  exact orderOf_eq_one_iff.mp hx_order_one

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_centralizer_singleton_le_centralizer_zpowers
    {a : G} :
    Subgroup.centralizer ({a} : Set G) ≤
      Subgroup.centralizer (Subgroup.zpowers a : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro y hy
  rcases Subgroup.mem_zpowers_iff.mp hy with ⟨n, rfl⟩
  have hcomm : Commute a x :=
    (Subgroup.mem_centralizer_singleton_iff.mp hx).symm
  simpa using (hcomm.zpow_left n).eq


omit [IsMinCE G] in
public theorem CFSG.section15_exists_primeOrder_zpowers_in
    {B : Subgroup G} {x : G} (hxB : x ∈ B) (hxne : x ≠ 1) :
    ∃ q : Nat.Primes, ∃ z : G,
      z ∈ Subgroup.zpowers x ∧ z ∈ B ∧ z ≠ 1 ∧
        Subgroup.zpowers z ∈ section10PrimeOrderSubgroupsIn q B := by
  classical
  have hcard_ne_one : Nat.card (Subgroup.zpowers x) ≠ 1 := by
    intro hcard
    have hzbot : Subgroup.zpowers x = ⊥ :=
      (Subgroup.card_eq_one (H := Subgroup.zpowers x)).1 hcard
    have hxbot : x ∈ (⊥ : Subgroup G) := by
      simpa [hzbot] using (Subgroup.mem_zpowers x)
    exact hxne (by simpa using hxbot)
  rcases Nat.exists_prime_and_dvd hcard_ne_one with ⟨q, hqprime, hqdiv⟩
  let q' : Nat.Primes := ⟨q, hqprime⟩
  haveI : Fact q.Prime := ⟨hqprime⟩
  obtain ⟨z₀, hz₀_order⟩ :=
    exists_prime_orderOf_dvd_card' (G := Subgroup.zpowers x) q hqdiv
  let z : G := z₀
  have hz_zpowx : z ∈ Subgroup.zpowers x := z₀.property
  have hzB : z ∈ B := (Subgroup.zpowers_le.2 hxB) hz_zpowx
  have hz_order : orderOf z = q := by
    simpa [z, Subgroup.orderOf_coe] using hz₀_order
  have hz_ne : z ≠ 1 := by
    intro hz1
    have hq_one : q = 1 := by
      rw [← hz_order, hz1, orderOf_one]
    exact hqprime.ne_one hq_one
  have hX_card : Nat.card (Subgroup.zpowers z) = q'.val := by
    rw [Nat.card_zpowers]
    exact hz_order
  exact ⟨q', z, hz_zpowx, hzB, hz_ne,
    by simpa [section10PrimeOrderSubgroupsIn, Nat.card_zpowers] using
      ⟨hzB, hz_order⟩⟩

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_elementCentralizerIn_subgroupOf_eq
    (S H : Subgroup G) (x : G) (hx : x ∈ S) :
    elementCentralizerIn (H.subgroupOf S) (⟨x, hx⟩ : S) =
      (elementCentralizerIn H x).subgroupOf S := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨hyH, hyC⟩
    change (y : G) ∈ H ∧ (y : G) ∈ Subgroup.centralizer ({x} : Set G)
    refine ⟨hyH, ?_⟩
    change y ∈ Subgroup.centralizer ({(⟨x, hx⟩ : S)} : Set S) at hyC
    rw [Subgroup.mem_centralizer_iff] at hyC ⊢
    intro z hz
    have hyx : (⟨x, hx⟩ : S) * y = y * (⟨x, hx⟩ : S) :=
      (Subgroup.mem_centralizer_iff.mp hyC) (⟨x, hx⟩) (by simp)
    have hz_eq : z = x := by simpa using hz
    simpa [hz_eq] using congrArg Subtype.val hyx
  · intro hy
    change (y : G) ∈ H ∧ (y : G) ∈ Subgroup.centralizer ({x} : Set G) at hy
    rcases hy with ⟨hyH, hyC⟩
    refine ⟨hyH, ?_⟩
    change y ∈ Subgroup.centralizer ({(⟨x, hx⟩ : S)} : Set S)
    rw [Subgroup.mem_centralizer_iff] at hyC ⊢
    intro z hz
    have hyx : (x : G) * (y : G) = (y : G) * x := hyC x (by simp)
    have hz_eq : z = (⟨x, hx⟩ : S) := by simpa using hz
    apply Subtype.ext
    simpa [hz_eq] using hyx

public theorem CFSG.section15_exists_kappa_hallSubgroupIn
    {M : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G) :
    ∃ K : Subgroup G,
      section12HallSubgroupIn (section14KappaPrimes M) K M := by
  classical
  letI : MulDistribMulAction Unit M := {
    smul := fun _ x => x
    one_smul := fun _ => rfl
    mul_smul := fun _ _ _ => rfl
    smul_mul := fun _ _ _ => rfl
    smul_one := fun _ => rfl }
  have hsolvM : Group.IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.2 hM.1)
  have hcopM : Nat.Coprime (Nat.card Unit) (Nat.card M) := by simp
  rcases exists_isHallSubgroup_isInvariant
      (G := M) (A := Unit) hsolvM hcopM (section14KappaPrimes M) with
    ⟨Kloc, hKlocHall, _hKlocInv⟩
  exact ⟨Kloc.map M.subtype,
    section15_hallSubgroupIn_map_subtype hKlocHall⟩

public theorem CFSG.section15_exists_kappa_hallSubgroupIn_le_sigma_complement
    {M N : Subgroup G}
    (hN : N ∈ section9MaximalSubgroups G)
    (hcomp : section12ComplementIn N (section10Msigma N) (M ⊓ N)) :
    ∃ K : Subgroup G,
      section12HallSubgroupIn (section14KappaPrimes N) K N ∧ K ≤ M ⊓ N := by
  classical
  let D : Subgroup G := M ⊓ N
  have hcompTo : section12ComplementToMsigma N D := by
    simpa [D, section12ComplementToMsigma] using hcomp
  have hDN : D ≤ N := by
    simp [D]
  have hDproper : D ≠ ⊤ := by
    intro hDtop
    have htop_le_N : (⊤ : Subgroup G) ≤ N := by
      simpa [hDtop] using hDN
    exact hN.1 (top_le_iff.mp htop_le_N)
  have hsolvD : Group.IsSolvable D :=
    IsMinCE.proper_subgroups_solvable D (lt_top_iff_ne_top.2 hDproper)
  letI : MulDistribMulAction Unit D := {
    smul := fun _ x => x
    one_smul := fun _ => rfl
    mul_smul := fun _ _ _ => rfl
    smul_mul := fun _ _ _ => rfl
    smul_one := fun _ => rfl }
  have hcopD : Nat.Coprime (Nat.card Unit) (Nat.card D) := by simp
  rcases exists_isHallSubgroup_isInvariant
      (G := D) (A := Unit) hsolvD hcopD (section14KappaPrimes N) with
    ⟨Kloc, hKlocHall, _hKlocInv⟩
  let K : Subgroup G := Kloc.map D.subtype
  have hKHallD : section12HallSubgroupIn (section14KappaPrimes N) K D :=
    section15_hallSubgroupIn_map_subtype hKlocHall
  have hKD : K ≤ D := hKHallD.1
  have hDHall :
      IsHallSubgroup (section10SigmaPrimes N)ᶜ (D.subgroupOf N) :=
    section12_msigma_complement_isHall_sigma_compl
      (G := G) (M := N) (E := D) hN hcompTo
  have hKHallN :
      section12HallSubgroupIn (section14KappaPrimes N) K N := by
    refine ⟨hKD.trans hDN, ?_⟩
    refine isHallSubgroup_of
      (G := N) (π := section14KappaPrimes N) (H := K.subgroupOf N) ?_ ?_
    · intro p hp
      have hcardKN : Nat.card (K.subgroupOf N) = Nat.card K :=
        Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe (H := K) (K := N) (hKD.trans hDN)).toEquiv
      have hcardKD : Nat.card (K.subgroupOf D) = Nat.card K :=
        Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe (H := K) (K := D) hKD).toEquiv
      exact hKHallD.2.p_in_pi_of_p_dvd_card p
        (by simpa [hcardKN, hcardKD] using hp)
    · intro p hpκ hpidx
      change p.val ∣ K.relIndex N at hpidx
      have hmul :
          K.relIndex D * D.relIndex N = K.relIndex N :=
        Subgroup.relIndex_mul_relIndex K D N hKD hDN
      have hpProd : p.val ∣ K.relIndex D * D.relIndex N := by
        simpa [hmul] using hpidx
      rcases p.2.dvd_mul.mp hpProd with hpKD | hpDN
      · exact (hKHallD.2.p_in_pi_of_p_dvd_index p
          (by simpa [Subgroup.relIndex] using hpKD)) hpκ
      · have hpσc : p ∈ (section10SigmaPrimes N)ᶜ :=
          (section15_kappa_subset_primeSet_diff_sigma
            (G := G) (M := N) hpκ).2
        exact (hDHall.p_in_pi_of_p_dvd_index p
          (by simpa [Subgroup.relIndex] using hpDN)) hpσc
  exact ⟨K, hKHallN, by simpa [D] using hKD⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_nontrivial_of_prime_card_subgroup
    {K MF : Subgroup G} {q : Nat.Primes}
    (hq : q.val = Nat.card K)
    (hKMF : K ≤ MF) :
    (⊥ : Subgroup G) < MF := by
  have hq_dvd_K : q.val ∣ Nat.card K := by
    rw [← hq]
  have hcard_sub :
      Nat.card (K.subgroupOf MF) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKMF).toEquiv
  have hq_dvd_sub : q.val ∣ Nat.card (K.subgroupOf MF) := by
    simpa [hcard_sub] using hq_dvd_K
  have hq_dvd_MF : q.val ∣ Nat.card MF :=
    hq_dvd_sub.trans (Subgroup.card_subgroup_dvd_card (K.subgroupOf MF))
  have hMF_ne_bot : MF ≠ ⊥ := by
    intro hMFbot
    have hcard : Nat.card MF = 1 := by
      simp [hMFbot]
    exact q.property.not_dvd_one (by simpa [hcard] using hq_dvd_MF)
  exact lt_of_le_of_ne bot_le hMF_ne_bot.symm

/-- Theorem 15.2 L001-S0030: the derived subgroup of a Section 15 maximal
subgroup is proper. -/
private theorem CFSG.section15_ambientDerived_lt_maximal
    {M : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G) :
    ambientDerivedSubgroup M < M := by
  classical
  have hM_ne_bot : M ≠ ⊥ := by
    intro hMbot
    have hMsigma_le_M : section10Msigma M ≤ M := section15_msigma_le
    have hMsigma_bot : section10Msigma M = ⊥ := by
      exact le_bot_iff.mp (by simpa [hMbot] using hMsigma_le_M)
    exact (theorem_10_2_e (M := M) hM) hMsigma_bot
  haveI : Nontrivial M := (Subgroup.nontrivial_iff_ne_bot (H := M)).2 hM_ne_bot
  have hsolvM : Group.IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.2 hM.1)
  let : Group.IsSolvable M := hsolvM
  have hcomm_lt : commutator M < (⊤ : Subgroup M) :=
    Group.IsSolvable.commutator_lt_top_of_nontrivial (G := M)
  refine lt_of_le_of_ne section15_ambientDerived_le ?_
  intro hEq
  have hDtop : derivedSubgroup M = (⊤ : Subgroup M) := by
    have hsubtop : (ambientDerivedSubgroup M).subgroupOf M = ⊤ := by
      rw [hEq]
      exact Subgroup.subgroupOf_eq_top.2 le_rfl
    simpa [section15_ambientDerived_subgroupOf_eq] using hsubtop
  have hcomm_top : commutator M = (⊤ : Subgroup M) := by
    change derivedSeries M 1 = ⊤ at hDtop
    rw [derivedSeries_one] at hDtop
    exact hDtop
  exact hcomm_lt.ne hcomm_top

/-- If `M_σ` is nilpotent, then it is one of the nilpotent normal Hall
subgroups controlled by the maximality clause in `M_F`. -/
public theorem CFSG.section15_msigma_nilpotentNormalHallIn_of_nilpotent
    {M : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hNil : Group.IsNilpotent (section10Msigma M)) :
    section15NilpotentNormalHallIn (section10Msigma M) M := by
  classical
  refine ⟨section15_msigma_le, (section15_msigma_normalIn (M := M)).2, hNil, ?_⟩
  have hHallLocal :
      IsHallSubgroup (section10SigmaPrimes M)
        ((section10Msigma M).subgroupOf M) := by
    simpa [section15_msigma_subgroupOf_eq] using
      (theorem_10_2_b (G := G) hM).2
  refine isHallSubgroup_of
    (G := M) (π := subgroupPrimeSet (section10Msigma M))
    (H := (section10Msigma M).subgroupOf M) ?_ ?_
  · intro p hp_dvd
    have hcard_eq :
        Nat.card ((section10Msigma M).subgroupOf M) =
          Nat.card (section10Msigma M) :=
      natCard_subgroupOf_eq (section10Msigma M) M section15_msigma_le
    have hp_ambient : p.val ∣ Nat.card (section10Msigma M) := by
      simpa [hcard_eq] using hp_dvd
    simpa [subgroupPrimeSet] using hp_ambient
  · intro p hp_support hp_dvd_index
    have hcard_eq :
        Nat.card ((section10Msigma M).subgroupOf M) =
          Nat.card (section10Msigma M) :=
      natCard_subgroupOf_eq (section10Msigma M) M section15_msigma_le
    have hp_ambient : p.val ∣ Nat.card (section10Msigma M) := by
      simpa [subgroupPrimeSet] using hp_support
    have hp_local : p.val ∣ Nat.card ((section10Msigma M).subgroupOf M) := by
      simpa [hcard_eq] using hp_ambient
    exact (hHallLocal.p_in_pi_of_p_dvd_index p hp_dvd_index)
      (hHallLocal.p_in_pi_of_p_dvd_card p hp_local)

public theorem CFSG.section15_msigma_MFSubgroup_of_nilpotent
    {M : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hNil : Group.IsNilpotent (section10Msigma M)) :
    section15MFSubgroup M (section10Msigma M) := by
  classical
  refine ⟨section15_msigma_nilpotentNormalHallIn_of_nilpotent hM hNil, ?_⟩
  intro H hH
  rcases hH with ⟨hHM, hHnormM, hHnil, hHHall⟩
  have hHπ : IsPiSubgroup (G := G) (section10SigmaPrimes M) H := by
    intro p hpH
    exact section15_prime_mem_sigma_of_nilpotentNormalHallIn
      hM ⟨hHM, hHnormM, hHnil, hHHall⟩ hpH
  have hcore : H ≤ piCoreIn (section10SigmaPrimes M) M :=
    section8_le_piCoreIn_of_normal_isPiSubgroup hHM hHnormM hHπ
  simpa [section10Msigma, section10MsigmaSubgroup, piCoreIn] using hcore

/-- Theorem 15.2 L002-S0020: if `M_F` is properly smaller than `M_σ`, then
`M_σ` cannot be nilpotent. -/
private theorem CFSG.section15_MF_ne_msigma_not_nilpotent
    {M MF : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hMFne : MF ≠ section10Msigma M) :
    ¬ Group.IsNilpotent (section10Msigma M) := by
  intro hNil
  have hMsigmaHall : section15NilpotentNormalHallIn (section10Msigma M) M :=
    section15_msigma_nilpotentNormalHallIn_of_nilpotent hM hNil
  have hMsigma_le_MF : section10Msigma M ≤ MF :=
    hMF.2 (section10Msigma M) hMsigmaHall
  have hMF_le_msigma : MF ≤ section10Msigma M :=
    section15_MF_le_msigma hM hMF
  exact hMFne (le_antisymm hMF_le_msigma hMsigma_le_MF)

/-- Theorem 15.2 L002: if `M_F` is properly smaller than `M_σ`, then the
source Lemma 14.1 branch puts `M` in type `𝓟₁` and identifies the fixed Hall
`κ(M)` subgroup as a complement to `M_σ`. -/
private theorem CFSG.section15_MF_ne_msigma_implies_P1
    {M MF K : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMFne : MF ≠ section10Msigma M) :
    M ∈ section14MFamilyP1 G ∧ M = K ⊔ section10Msigma M := by
  have hnotNil : ¬ Group.IsNilpotent (section10Msigma M) :=
    section15_MF_ne_msigma_not_nilpotent hM hMF hMFne
  have hP1 : M ∈ section14MFamilyP1 G :=
    section15_lemma_14_1_nonnilpotent_msigma_mem_familyP1 hM hnotNil
  exact ⟨hP1, section15_familyP1_hall_kappa_sup_msigma_eq hM hP1 hK⟩

/-- Theorem 15.2 L003-S0020: the proper-containment branch gives the
prime-action hypothesis for `K` on `M_σ`. -/
private theorem CFSG.section15_prime_action_of_MF_ne_msigma
    {M MF K : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMFne : MF ≠ section10Msigma M) :
    section14ActsInPrimeManner K (section10Msigma M) := by
  have hP1 : M ∈ section14MFamilyP1 G :=
    (section15_MF_ne_msigma_implies_P1 hM hMF hK hMFne).1
  have hMP : M ∈ section14MFamilyP G := hP1.1
  rcases proposition_14_2_a hMP hK with ⟨U, hU⟩
  exact hU.1

/-- Theorem 15.2 L003-S0030: Lemma 6.3(a) turns the proper-branch
prime-action context into `M_σ = [M_σ,K]`. -/
private theorem CFSG.section15_msigma_commutator_eq_of_prime_action
    {M MF K : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMFne : MF ≠ section10Msigma M)
    (hprime : section14ActsInPrimeManner K (section10Msigma M)) :
    ⁅section10Msigma M, K⁆ = section10Msigma M := by
  classical
  let _ := hprime
  let Hloc : Subgroup M := section10MsigmaSubgroup M
  let Kloc : Subgroup M := K.subgroupOf M
  have hP1prod := section15_MF_ne_msigma_implies_P1 hM hMF hK hMFne
  have hP1 : M ∈ section14MFamilyP1 G := hP1prod.1
  have hprod : M = K ⊔ section10Msigma M := hP1prod.2
  have hHallH : IsHallSubgroup (section10SigmaPrimes M) Hloc := by
    simpa [Hloc] using (theorem_10_2_b (G := G) hM).2
  have hHallK : IsHallSubgroup (section14KappaPrimes M) Kloc := by
    simpa [Kloc] using hK.2
  have hπdisj :
      Disjoint (section10SigmaPrimes M) (section14KappaPrimes M) := by
    rw [hP1.2]
    rw [Set.disjoint_left]
    intro p hpσ hpκ
    exact hpκ.2 hpσ
  have hdisj : Disjoint Hloc Kloc :=
    section15_disjoint_of_hall_disjoint_primes hHallH hHallK hπdisj
  have hsup_local : Hloc ⊔ Kloc = ⊤ := by
    calc
      Hloc ⊔ Kloc =
          (section10Msigma M).subgroupOf M ⊔ K.subgroupOf M := by
        simp [Hloc, Kloc, section15_msigma_subgroupOf_eq]
      _ = (section10Msigma M ⊔ K).subgroupOf M := by
        symm
        exact Subgroup.subgroupOf_sup
          (A := section10Msigma M) (A' := K) (B := M)
          section15_msigma_le hK.1
      _ = ⊤ := by
        rw [sup_comm, ← hprod]
        exact Subgroup.subgroupOf_eq_top.2 le_rfl
  have hCompl : IsCompl Hloc Kloc :=
    IsCompl.of_eq hdisj.eq_bot hsup_local
  have : Group.IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.2 hM.1)
  have hld : Hloc ≤ derivedSubgroup M := by
    simpa [Hloc] using (theorem_10_2_c (G := G) hM).2
  have hcomm_local : Hloc = ⁅Hloc, Kloc⁆ :=
    lemma_6_3_a_1
      (G := M) (H := Hloc) (K := Kloc)
      ⟨section10SigmaPrimes M, hHallH⟩ hCompl hld
  have hKloc_map : Kloc.map M.subtype = K := by
    simpa [Kloc] using
      (Subgroup.map_subgroupOf_eq_of_le (G := G) (H := K) (K := M) hK.1)
  calc
    ⁅section10Msigma M, K⁆ =
        ⁅Hloc.map M.subtype, Kloc.map M.subtype⁆ := by
      simp [Hloc, Kloc, hKloc_map, section10Msigma]
    _ = (⁅Hloc, Kloc⁆).map M.subtype := by
      simpa using
        (Subgroup.map_commutator (H₁ := Hloc) (H₂ := Kloc) M.subtype).symm
    _ = Hloc.map M.subtype := by
      rw [← hcomm_local]
    _ = section10Msigma M := by
      simp [Hloc, section10Msigma]

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_primeOrderSubgroups_of_primeOrderSubgroupsIn
    {p : Nat.Primes} {A X : Subgroup G}
    (hX : X ∈ section10PrimeOrderSubgroupsIn p A) :
    X ∈ section12PrimeOrderSubgroups A := by
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hX) with
    ⟨hXA, hXcard⟩
  exact ⟨hXA, ⟨p, hXcard⟩⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_kstar_le_centralizer_of_le
    {M K X : Subgroup G}
    (hXK : X ≤ K) :
    section14KStar M K ≤ subgroupCentralizerIn (section10Msigma M) X := by
  intro y hy
  refine ⟨hy.1, ?_⟩
  change y ∈ Subgroup.centralizer (X : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro x hxX
  exact Subgroup.mem_centralizer_iff.mp hy.2 x (hXK hxX)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_centralizer_eq_kstar_of_prime_manner
    {M K X : Subgroup G}
    (hprime : section14ActsInPrimeManner K (section10Msigma M))
    (hX : X ∈ section12PrimeOrderSubgroups K) :
    subgroupCentralizerIn (section10Msigma M) X = section14KStar M K := by
  apply le_antisymm
  · exact hprime.2 X hX
  · exact section15_kstar_le_centralizer_of_le (M := M) (K := K) (X := X) hX.1

omit [IsMinCE G] in
public theorem CFSG.section15_elementCentralizerIn_eq_kstar_of_prime_manner
    {M K : Subgroup G}
    (hprime : section14ActsInPrimeManner K (section10Msigma M))
    {x : G} (hxK : x ∈ K) (hxne : x ≠ 1) :
    elementCentralizerIn (section10Msigma M) x = section14KStar M K := by
  classical
  rcases section15_exists_primeOrder_zpowers_in (B := K) hxK hxne with
    ⟨q, z, hzpowx, _hzK, _hzne, hzprimeK⟩
  have hZprime : Subgroup.zpowers z ∈ section12PrimeOrderSubgroups K :=
    section15_primeOrderSubgroups_of_primeOrderSubgroupsIn hzprimeK
  have hCentZ :
      subgroupCentralizerIn (section10Msigma M) (Subgroup.zpowers z) =
        section14KStar M K :=
    section15_centralizer_eq_kstar_of_prime_manner
      (M := M) (K := K) hprime hZprime
  apply le_antisymm
  · intro y hy
    have hyCentZ :
        y ∈ subgroupCentralizerIn (section10Msigma M) (Subgroup.zpowers z) := by
      refine ⟨hy.1, ?_⟩
      have hyCentXpow :
          y ∈ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) :=
        section15_centralizer_singleton_le_centralizer_zpowers hy.2
      change y ∈ Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G)
      rw [Subgroup.mem_centralizer_iff] at hyCentXpow ⊢
      intro t ht
      exact hyCentXpow t ((Subgroup.zpowers_le.2 hzpowx) ht)
    simpa [hCentZ] using hyCentZ
  · intro y hy
    have hy' : y ∈ subgroupCentralizerIn (section10Msigma M) K := by
      simpa [section14KStar] using hy
    refine ⟨hy'.1, ?_⟩
    change y ∈ Subgroup.centralizer ({x} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have ht_eq : t = x := by simpa using ht
    have hcomm : x * y = y * x :=
      Subgroup.mem_centralizer_iff.mp hy'.2 x hxK
    simpa [ht_eq] using hcomm

omit [IsMinCE G] in
private theorem CFSG.section15_map_fittingSubgroupOf_subgroupOf_le_fitting
    {L B : Subgroup G} (hLB : L ≤ B) :
    (fittingSubgroupOf (G := B) (L.subgroupOf B)).map B.subtype ≤
      fittingSubgroupOf (G := G) L := by
  classical
  let Lsub : Subgroup B := L.subgroupOf B
  let Fsub : Subgroup B := fittingSubgroupOf (G := B) Lsub
  let e : Lsub ≃* L :=
    Subgroup.subgroupOfEquivOfLe (G := G) (H := L) (K := B) hLB
  let F1 : Subgroup L := (fittingSubgroup Lsub).map e.toMonoidHom
  have hF1_normal : F1.Normal := by
    exact Subgroup.Normal.map (H := fittingSubgroup Lsub)
      (inferInstance : (fittingSubgroup Lsub).Normal) e.toMonoidHom e.surjective
  have hF1_nil : Group.IsNilpotent F1 := by
    let ψ : fittingSubgroup Lsub →* F1 :=
      { toFun := fun x => ⟨e x, ⟨x, x.2, rfl⟩⟩
        map_one' := rfl
        map_mul' := by intro a b; rfl }
    have hψ_surj : Function.Surjective ψ := by
      rintro ⟨x, hx⟩
      rcases hx with ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
    exact Group.nilpotent_of_surjective (G := fittingSubgroup Lsub) (G' := F1) ψ hψ_surj
  have hF1_le_fit : F1 ≤ fittingSubgroup L := le_sSup ⟨hF1_normal, hF1_nil⟩
  have hcomp :
      L.subtype.comp e.toMonoidHom = B.subtype.comp Lsub.subtype := by
    ext x
    rfl
  have hmap_eq : Fsub.map B.subtype = F1.map L.subtype := by
    calc
      Fsub.map B.subtype
          = ((fittingSubgroup Lsub).map Lsub.subtype).map B.subtype := by
              simp [Fsub, fittingSubgroupOf]
      _ = (fittingSubgroup Lsub).map (B.subtype.comp Lsub.subtype) := by
            rw [Subgroup.map_map]
      _ = (fittingSubgroup Lsub).map (L.subtype.comp e.toMonoidHom) := by
            rw [hcomp.symm]
      _ = ((fittingSubgroup Lsub).map e.toMonoidHom).map L.subtype := by
            rw [Subgroup.map_map]
      _ = F1.map L.subtype := rfl
  calc
    (fittingSubgroupOf (G := B) (L.subgroupOf B)).map B.subtype = F1.map L.subtype :=
      hmap_eq
    _ ≤ (fittingSubgroup L).map L.subtype := Subgroup.map_mono hF1_le_fit
    _ = fittingSubgroupOf (G := G) L := rfl

/-- Theorem 15.2 L003-S0040 core interface: this is the explicit local
Theorem 3.8 application hidden in the source proof.  If the fixed-point
subgroup `K* = C_{M_σ}(K)` does not meet `F(M)`, then the split coprime action
of `K` on `M_σ` forces the commutator `[M_σ,K]` into `F(M_σ)`. -/
private theorem CFSG.section15_commutator_le_fitting_msigma_of_kstar_disjoint_fitting
    {M MF K : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMFne : MF ≠ section10Msigma M)
    (hprime : section14ActsInPrimeManner K (section10Msigma M))
    (hdisj : section14KStar M K ⊓ section8FittingSubgroup M = ⊥) :
    ⁅section10Msigma M, K⁆ ≤ section8FittingSubgroup (section10Msigma M) := by
  classical
  -- This is the formal version of the odd-order proof's application of
  -- Theorem 3.8 to the local semidirect product `M = K M_σ`.
  let Hloc : Subgroup M := section10MsigmaSubgroup M
  let Kloc : Subgroup M := K.subgroupOf M
  have hP1prod := section15_MF_ne_msigma_implies_P1 hM hMF hK hMFne
  have hP1 : M ∈ section14MFamilyP1 G := hP1prod.1
  have hprod : M = K ⊔ section10Msigma M := hP1prod.2
  have hHallH : IsHallSubgroup (section10SigmaPrimes M) Hloc := by
    simpa [Hloc] using (theorem_10_2_b (G := G) hM).2
  have hHallK : IsHallSubgroup (section14KappaPrimes M) Kloc := by
    simpa [Kloc] using hK.2
  have hπdisj :
      Disjoint (section10SigmaPrimes M) (section14KappaPrimes M) := by
    rw [hP1.2]
    rw [Set.disjoint_left]
    intro p hpσ hpκ
    exact hpκ.2 hpσ
  have hsup_local : Hloc ⊔ Kloc = ⊤ := by
    calc
      Hloc ⊔ Kloc =
          (section10Msigma M).subgroupOf M ⊔ K.subgroupOf M := by
        simp [Hloc, Kloc, section15_msigma_subgroupOf_eq]
      _ = (section10Msigma M ⊔ K).subgroupOf M := by
        symm
        exact Subgroup.subgroupOf_sup
          (A := section10Msigma M) (A' := K) (B := M)
          section15_msigma_le hK.1
      _ = ⊤ := by
        rw [sup_comm, ← hprod]
        exact Subgroup.subgroupOf_eq_top.2 le_rfl
  have hcop_local : Nat.Coprime (Nat.card Kloc) (Nat.card Hloc) :=
    section15_coprime_card_of_hall_disjoint_primes hHallK hHallH hπdisj.symm
  have hsolvM : Group.IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.2 hM.1)
  have hoddM : Odd (Nat.card M) :=
    odd_of_card_dvd IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card M)
  have hHloc_normal : Hloc.Normal := by
    simpa [Hloc, section15_msigma_subgroupOf_eq] using
      (section15_msigma_normalIn (M := M)).2
  let Floc : Subgroup M := fittingSubgroupOf (G := M) Hloc
  have hfit_fix : subgroupCentralizerIn Floc Kloc = ⊥ := by
    apply bot_unique
    intro y hy
    have hFloc_map_le_fitM : Floc.map M.subtype ≤ section8FittingSubgroup M := by
      have hFloc_le_fitMloc : Floc ≤ fittingSubgroup M := by
        simpa [Floc] using
          fittingSubgroupOf_le_fittingSubgroup (G := M) Hloc hHloc_normal
      have hmap :
          Floc.map M.subtype ≤ (fittingSubgroup M).map M.subtype :=
        Subgroup.map_mono hFloc_le_fitMloc
      simpa [section8FittingSubgroup, fittingSubgroupOf] using hmap
    have hyHloc : y ∈ Hloc :=
      fittingSubgroupOf_le (G := M) Hloc hy.1
    have hySamb : (y : G) ∈ section10Msigma M := by
      have hyMap : (y : G) ∈ Hloc.map M.subtype :=
        Subgroup.mem_map.mpr ⟨y, hyHloc, rfl⟩
      simpa [Hloc, section10Msigma] using hyMap
    have hyCentKamb : (y : G) ∈ Subgroup.centralizer (K : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hkK
      let kM : M := ⟨k, hK.1 hkK⟩
      have hkKloc : kM ∈ Kloc := by
        simpa [Kloc, Subgroup.mem_subgroupOf] using hkK
      have hcommM : kM * y = y * kM :=
        (Subgroup.mem_centralizer_iff.mp hy.2) kM hkKloc
      simpa [kM] using congrArg Subtype.val hcommM
    have hyKstar : (y : G) ∈ section14KStar M K := by
      simpa [section14KStar] using
        (show (y : G) ∈ subgroupCentralizerIn (section10Msigma M) K from
          ⟨hySamb, hyCentKamb⟩)
    have hyFitAmb : (y : G) ∈ section8FittingSubgroup M :=
      hFloc_map_le_fitM (Subgroup.mem_map.mpr ⟨y, hy.1, rfl⟩)
    have hyBotG : (y : G) ∈ (⊥ : Subgroup G) := by
      have hyInf :
          (y : G) ∈ section14KStar M K ⊓ section8FittingSubgroup M :=
        ⟨hyKstar, hyFitAmb⟩
      simpa [hdisj] using hyInf
    have hyG_one : (y : G) = 1 := Subgroup.mem_bot.mp hyBotG
    simpa using (Subtype.ext hyG_one : y = 1)
  have hcentralizer :
      ∀ x : Kloc, x ≠ 1 →
        elementCentralizerIn Hloc (x : M) = subgroupCentralizerIn Hloc Kloc := by
    intro x hxne
    have hxG_ne : (x : G) ≠ 1 := by
      intro hxG
      apply hxne
      exact Subtype.ext (Subtype.ext hxG)
    have hcent_amb :
        elementCentralizerIn (section10Msigma M) (x : G) = section14KStar M K :=
      section15_elementCentralizerIn_eq_kstar_of_prime_manner
        (M := M) (K := K) hprime x.property hxG_ne
    calc
      elementCentralizerIn Hloc (x : M)
          = elementCentralizerIn ((section10Msigma M).subgroupOf M) (x : M) := by
              simp [Hloc, section15_msigma_subgroupOf_eq]
      _ = (elementCentralizerIn (section10Msigma M) (x : G)).subgroupOf M := by
              simpa using
                section15_elementCentralizerIn_subgroupOf_eq
                  (S := M) (H := section10Msigma M) (x := ((x : M) : G))
                  (hx := (x : M).2)
      _ = (section14KStar M K).subgroupOf M := by
              rw [hcent_amb]
      _ = (subgroupCentralizerIn (section10Msigma M) K).subgroupOf M := by
              simp [section14KStar]
      _ = subgroupCentralizerIn ((section10Msigma M).subgroupOf M) (K.subgroupOf M) := by
              rw [← subgroupCentralizerIn_subgroupOf_eq M (section10Msigma M) K hK.1]
      _ = subgroupCentralizerIn Hloc Kloc := by
              simp [Hloc, Kloc, section15_msigma_subgroupOf_eq]
  have hcomm_local_le :
      ⁅Hloc, Kloc⁆ ≤ fittingSubgroupOf (G := M) Hloc :=
    theorem_3_8 (G := M) Hloc Kloc hsolvM hoddM hHloc_normal hsup_local
      hcop_local hcentralizer (by simpa [Floc] using hfit_fix)
  have hFloc_map_le_fitS :
      (fittingSubgroupOf (G := M) Hloc).map M.subtype ≤
        section8FittingSubgroup (section10Msigma M) := by
    simpa [Hloc, section8FittingSubgroup, section15_msigma_subgroupOf_eq] using
      (section15_map_fittingSubgroupOf_subgroupOf_le_fitting
        (G := G) (L := section10Msigma M) (B := M)
        (section15_msigma_le (M := M)))
  have hKloc_map : Kloc.map M.subtype = K := by
    simpa [Kloc] using
      (Subgroup.map_subgroupOf_eq_of_le (G := G) (H := K) (K := M) hK.1)
  have hcomm_map :
      ⁅section10Msigma M, K⁆ = (⁅Hloc, Kloc⁆).map M.subtype := by
    calc
      ⁅section10Msigma M, K⁆ =
          ⁅Hloc.map M.subtype, Kloc.map M.subtype⁆ := by
        simp [Hloc, Kloc, hKloc_map, section10Msigma]
      _ = (⁅Hloc, Kloc⁆).map M.subtype := by
        simpa using
          (Subgroup.map_commutator (H₁ := Hloc) (H₂ := Kloc) M.subtype).symm
  rw [hcomm_map]
  exact (Subgroup.map_mono hcomm_local_le).trans hFloc_map_le_fitS

/-- Theorem 15.2 L003-S0040: Theorem 3.8 gives a nontrivial intersection
between `K*` and the Fitting subgroup once `[M_σ,K]` is not contained in
`F(M_σ)`. -/
private theorem CFSG.section15_kstar_meets_fitting_of_MF_ne_msigma
    {M MF K : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMFne : MF ≠ section10Msigma M)
    (hcomm : ⁅section10Msigma M, K⁆ = section10Msigma M) :
    section14KStar M K ⊓ section8FittingSubgroup M ≠ ⊥ := by
  classical
  intro hmeet
  have hdisj : section14KStar M K ⊓ section8FittingSubgroup M = ⊥ :=
    hmeet
  have hprime : section14ActsInPrimeManner K (section10Msigma M) :=
    section15_prime_action_of_MF_ne_msigma hM hMF hK hMFne
  have hcomm_le_fit :
      ⁅section10Msigma M, K⁆ ≤ section8FittingSubgroup (section10Msigma M) :=
    section15_commutator_le_fitting_msigma_of_kstar_disjoint_fitting
      hM hMF hK hMFne hprime hdisj
  have hMsigma_le_fit :
      section10Msigma M ≤ section8FittingSubgroup (section10Msigma M) := by
    simpa [hcomm] using hcomm_le_fit
  have hfit_eq :
      section8FittingSubgroup (section10Msigma M) = section10Msigma M :=
    le_antisymm (section8FittingSubgroup_le (section10Msigma M)) hMsigma_le_fit
  have hNil : Group.IsNilpotent (section10Msigma M) := by
    let e :
        section8FittingSubgroup (section10Msigma M) ≃*
          section10Msigma M :=
      MulEquiv.subgroupCongr hfit_eq
    exact Group.nilpotent_of_mulEquiv
      (G := section8FittingSubgroup (section10Msigma M))
      (G' := section10Msigma M)
      (_h := section8FittingSubgroup_isNilpotent (section10Msigma M)) e
  exact (section15_MF_ne_msigma_not_nilpotent hM hMF hMFne) hNil

omit [IsMinCE G] in
public theorem CFSG.section15_le_of_prime_card_inf_ne_bot
    {A B : Subgroup G} {q : Nat.Primes}
    (hcard : q.val = Nat.card A) (hne : A ⊓ B ≠ ⊥) :
    A ≤ B := by
  classical
  have hdiv : Nat.card ↥(A ⊓ B) ∣ q.val := by
    rw [hcard]
    exact Subgroup.card_dvd_of_le (inf_le_left : A ⊓ B ≤ A)
  rcases (Nat.dvd_prime q.property).1 hdiv with hcard_one | hcard_prime
  · exact False.elim
      (hne ((Subgroup.card_eq_one (H := A ⊓ B)).1 hcard_one))
  · have hEq : A ⊓ B = A := by
      apply Subgroup.eq_of_le_of_card_ge (inf_le_left : A ⊓ B ≤ A)
      exact le_of_eq (hcard.symm.trans hcard_prime.symm)
    intro x hxA
    have hxInf : x ∈ A ⊓ B := by
      simpa [hEq] using hxA
    exact hxInf.2

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_isPGroup_of_prime_card
    {A : Subgroup G} {q : Nat.Primes}
    (hcard : q.val = Nat.card A) :
    IsPGroup q.val A := by
  refine IsPGroup.of_card (p := q.val) (G := A) (n := 1) ?_
  simpa [pow_one] using hcard.symm

omit [IsMinCE G] in
private theorem CFSG.section15_kstar_le_pCoreIn_of_meets_fitting
    {M K : Subgroup G} {q : Nat.Primes}
    (_hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hq : q.val = Nat.card (section14KStar M K))
    (hmeet : section14KStar M K ⊓ section8FittingSubgroup M ≠ ⊥) :
    section14KStar M K ≤ section15PCoreIn q M := by
  classical
  let F : Subgroup G := section8FittingSubgroup M
  have hKstar_le_F : section14KStar M K ≤ F :=
    section15_le_of_prime_card_inf_ne_bot (A := section14KStar M K)
      (B := F) hq (by simpa [F] using hmeet)
  have hKstar_q : IsPGroup q.val (section14KStar M K) :=
    section15_isPGroup_of_prime_card (A := section14KStar M K) hq
  haveI : Group.IsNilpotent F := by
    simpa [F] using section8FittingSubgroup_isNilpotent M
  have hKstar_le_coreF :
      section14KStar M K ≤ piCoreIn ({q} : Set Nat.Primes) F :=
    section8_isPGroup_le_piCoreIn_singleton_of_le_nilpotent
      (G := G) (H := section14KStar M K) (K := F)
      hKstar_le_F q hKstar_q
  have hcoreF_le_coreM :
      piCoreIn ({q} : Set Nat.Primes) F ≤ piCoreIn ({q} : Set Nat.Primes) M :=
    section8_piCoreIn_singleton_le_of_le_normalizer
      (G := G) (Y := F) (H := M)
      (by simpa [F] using section8FittingSubgroup_le M)
      (by simpa [F] using section10_le_normalizer_fitting (G := G) M) q
  calc
    section14KStar M K ≤ piCoreIn ({q} : Set Nat.Primes) F :=
      hKstar_le_coreF
    _ ≤ piCoreIn ({q} : Set Nat.Primes) M := hcoreF_le_coreM
    _ = section15PCoreIn q M := by
      simp [section15PCoreIn, section8_piCoreIn_singleton_eq_pCore_map]

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_pCoreIn_le
    (q : Nat.Primes) (M : Subgroup G) :
    section15PCoreIn q M ≤ M := by
  classical
  intro x hx
  have hxmap : x ∈ (pCore q.val M).map M.subtype := by
    simpa [section15PCoreIn] using hx
  rcases Subgroup.mem_map.mp hxmap with ⟨y, _hy, rfl⟩
  exact y.property

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_pCoreIn_isPGroup
    (q : Nat.Primes) (M : Subgroup G) :
    IsPGroup q.val (section15PCoreIn q M) := by
  classical
  change IsPGroup q.val ((pCore q.val M).map M.subtype)
  exact IsPGroup.map (p := q.val) (H := pCore q.val M)
    (pCore_isPGroup (G := M) (p := q.val)) M.subtype

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_pCoreIn_subgroupOf_eq
    (q : Nat.Primes) (M : Subgroup G) :
    (section15PCoreIn q M).subgroupOf M = pCore q.val M := by
  classical
  simpa [section15PCoreIn] using
    (subgroupOf_map_subtype_eq (K := M) (pCore q.val M))

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_pCoreIn_normalIn
    (q : Nat.Primes) (M : Subgroup G) :
    section10NormalIn (section15PCoreIn q M) M := by
  classical
  have hQM : section15PCoreIn q M ≤ M := section15_pCoreIn_le q M
  refine ⟨hQM, ?_⟩
  simpa [section15_pCoreIn_subgroupOf_eq q M] using
    (pCore_normal (p := q.val) (G := M))

omit [IsMinCE G] in
public theorem CFSG.section15_pCoreIn_le_msigma_of_mem_sigma
    {M : Subgroup G} {q : Nat.Primes}
    (hqσ : q ∈ section10SigmaPrimes M) :
    section15PCoreIn q M ≤ section10Msigma M := by
  classical
  have hQπ : IsPiSubgroup (G := G) (section10SigmaPrimes M)
      (section15PCoreIn q M) := by
    intro r hrQ
    have hQ_single :
        IsPiSubgroup (G := G) ({q} : Set Nat.Primes) (section15PCoreIn q M) :=
      section8_isPiSubgroup_singleton_of_isPGroup
        (section15_pCoreIn_isPGroup q M)
    have hrq : r ∈ ({q} : Set Nat.Primes) := hQ_single r hrQ
    simpa using (Set.mem_singleton_iff.mp hrq ▸ hqσ)
  exact section8_le_piCoreIn_of_normal_isPiSubgroup
    (G := G) (π := section10SigmaPrimes M)
    (K := section15PCoreIn q M) (H := M)
    (section15_pCoreIn_le q M)
    (section15_pCoreIn_normalIn q M).2 hQπ

omit [IsMinCE G] in
public theorem CFSG.section15_pCore_le_sylow
    {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (P : Sylow p H) :
    pCore p H ≤ (P : Subgroup H) := by
  have hsup_p : IsPGroup p (((P : Subgroup H) ⊔ pCore p H : Subgroup H)) :=
    IsPGroup.to_sup_of_normal_right (p := p) (H := (P : Subgroup H))
      (K := pCore p H) P.isPGroup' (pCore_isPGroup (G := H) (p := p))
  have hEq : (((P : Subgroup H) ⊔ pCore p H : Subgroup H)) = (P : Subgroup H) :=
    P.is_maximal' hsup_p le_sup_left
  exact sup_eq_left.mp hEq

omit [IsMinCE G] in
private theorem CFSG.section15_normal_sylowSubgroupIn_subgroupOf_eq_pCore
    {M Q : Subgroup G} {q : Nat.Primes}
    (hQ : section12SylowSubgroupIn q Q M)
    (hQnormal : section10NormalIn Q M) :
    Q.subgroupOf M = pCore q.val M := by
  classical
  haveI : Fact q.val.Prime := ⟨q.property⟩
  rcases hQ with ⟨P, hPamb⟩
  have hQsub_eq : Q.subgroupOf M = (P : Subgroup M) := by
    rw [← hPamb]
    simpa [section10AmbientSylowSubgroup] using
      (subgroupOf_map_subtype_eq (K := M) (P : Subgroup M))
  have hQloc_normal : (Q.subgroupOf M).Normal := hQnormal.2
  have hPnormal : (P : Subgroup M).Normal := by
    simpa [hQsub_eq] using hQloc_normal
  have hP_le_core : (P : Subgroup M) ≤ pCore q.val M :=
    le_sSup (show (P : Subgroup M) ∈
      {K : Subgroup M | K.Normal ∧ IsPGroup q.val K} from
        ⟨hPnormal, P.isPGroup'⟩)
  have hcore_le_P : pCore q.val M ≤ (P : Subgroup M) :=
    section15_pCore_le_sylow P
  rw [hQsub_eq]
  exact le_antisymm hP_le_core hcore_le_P

omit [IsMinCE G] in
private theorem CFSG.section15_kstar_le_normal_sylow_of_prime_card
    {M K Q : Subgroup G} {q : Nat.Primes}
    (hq : q.val = Nat.card (section14KStar M K))
    (hQ : section12SylowSubgroupIn q Q M)
    (hQnormal : section10NormalIn Q M) :
    section14KStar M K ≤ Q := by
  classical
  haveI : Fact q.val.Prime := ⟨q.property⟩
  rcases hQ with ⟨P, hPamb⟩
  have hQsub_eq : Q.subgroupOf M = (P : Subgroup M) := by
    rw [← hPamb]
    simpa [section10AmbientSylowSubgroup] using
      (subgroupOf_map_subtype_eq (K := M) (P : Subgroup M))
  have hQloc_normal : (Q.subgroupOf M).Normal := hQnormal.2
  have hPnormal : (P : Subgroup M).Normal := by
    simpa [hQsub_eq] using hQloc_normal
  haveI : Unique (Sylow q.val M) := Sylow.unique_of_normal P hPnormal
  have hKstar_le_M : section14KStar M K ≤ M :=
    (show section14KStar M K ≤ section10Msigma M from inf_le_left).trans
      (section15_msigma_le (M := M))
  let A : Subgroup M := (section14KStar M K).subgroupOf M
  have hKstar_p : IsPGroup q.val (section14KStar M K) :=
    section15_isPGroup_of_prime_card (A := section14KStar M K) hq
  have hA_p : IsPGroup q.val A := by
    exact hKstar_p.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := section14KStar M K) (K := M)
        hKstar_le_M).symm
  obtain ⟨T, hA_le_T⟩ := IsPGroup.exists_le_sylow (G := M) (p := q.val) hA_p
  have hT_eq_P : (T : Subgroup M) = (P : Subgroup M) := by
    have hTP : T = P := Subsingleton.elim T P
    simp [hTP]
  intro x hx
  let xM : M := ⟨x, hKstar_le_M hx⟩
  have hxA : xM ∈ A := by
    simpa [A, xM, Subgroup.mem_subgroupOf] using hx
  have hxT : xM ∈ (T : Subgroup M) := hA_le_T hxA
  have hxP : xM ∈ (P : Subgroup M) := by
    simpa [hT_eq_P] using hxT
  have hxQsub : xM ∈ Q.subgroupOf M := by
    simpa [hQsub_eq] using hxP
  simpa [xM, Subgroup.mem_subgroupOf] using hxQsub

private theorem CFSG.section15_prime_mem_sigma_of_kstar_prime_card
    {M K : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hq : q.val = Nat.card (section14KStar M K)) :
    q ∈ section10SigmaPrimes M := by
  have hqKstar : q.val ∣ Nat.card (section14KStar M K) := by
    rw [← hq]
  have hqMsigma : q.val ∣ Nat.card (section10Msigma M) :=
    hqKstar.trans
      (Subgroup.card_dvd_of_le
        (show section14KStar M K ≤ section10Msigma M from inf_le_left))
  have hcard_sub :
      Nat.card (section10MsigmaSubgroup M) = Nat.card (section10Msigma M) := by
    simpa [section15_msigma_subgroupOf_eq] using
      (natCard_subgroupOf_eq (section10Msigma M) M
        (section15_msigma_le (M := M)))
  have hqSub : q.val ∣ Nat.card (section10MsigmaSubgroup M) := by
    simpa [hcard_sub] using hqMsigma
  exact ((theorem_10_2_b (G := G) hM).2).p_in_pi_of_p_dvd_card q hqSub

private theorem CFSG.section15_pCoreIn_le_msigma_of_kstar_prime_card
    {M K : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hq : q.val = Nat.card (section14KStar M K)) :
    section15PCoreIn q M ≤ section10Msigma M := by
  classical
  have hqσ : q ∈ section10SigmaPrimes M :=
    section15_prime_mem_sigma_of_kstar_prime_card hM hq
  have hQπ : IsPiSubgroup (G := G) (section10SigmaPrimes M)
      (section15PCoreIn q M) := by
    intro r hrQ
    have hQ_single :
        IsPiSubgroup (G := G) ({q} : Set Nat.Primes) (section15PCoreIn q M) :=
      section8_isPiSubgroup_singleton_of_isPGroup
        (section15_pCoreIn_isPGroup q M)
    have hrq : r ∈ ({q} : Set Nat.Primes) := hQ_single r hrQ
    simpa using (Set.mem_singleton_iff.mp hrq ▸ hqσ)
  exact section8_le_piCoreIn_of_normal_isPiSubgroup
    (G := G) (π := section10SigmaPrimes M)
    (K := section15PCoreIn q M) (H := M)
    (section15_pCoreIn_le q M)
    (section15_pCoreIn_normalIn q M).2 hQπ

private theorem CFSG.section15_msigmaSubgroup_disjoint_kappaHall_of_MF_ne
    {M MF K : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMFne : MF ≠ section10Msigma M) :
    Disjoint (section10MsigmaSubgroup M) (K.subgroupOf M) := by
  classical
  let Hloc : Subgroup M := section10MsigmaSubgroup M
  let Kloc : Subgroup M := K.subgroupOf M
  have hP1prod := section15_MF_ne_msigma_implies_P1 hM hMF hK hMFne
  have hP1 : M ∈ section14MFamilyP1 G := hP1prod.1
  have hHallH : IsHallSubgroup (section10SigmaPrimes M) Hloc := by
    simpa [Hloc] using (theorem_10_2_b (G := G) hM).2
  have hHallK : IsHallSubgroup (section14KappaPrimes M) Kloc := by
    simpa [Kloc] using hK.2
  have hπdisj :
      Disjoint (section10SigmaPrimes M) (section14KappaPrimes M) := by
    rw [hP1.2]
    rw [Set.disjoint_left]
    intro p hpσ hpκ
    exact hpκ.2 hpσ
  exact section15_disjoint_of_hall_disjoint_primes hHallH hHallK hπdisj

omit [IsMinCE G] in
public theorem CFSG.section15_hall_kappa_ne_bot
    {M K : Subgroup G}
    (hM : M ∈ section14MFamilyP G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    K ≠ ⊥ := by
  classical
  intro hbot
  rcases hM.2 with ⟨p, hpκ⟩
  rcases hK with ⟨hKM, hHallK⟩
  have hpM : p ∈ subgroupPrimeSet M := by
    rcases hpκ.2 with ⟨P, hPprime, _hCP⟩
    rcases hPprime with ⟨hPM, hPcard⟩
    have hpP : p.val ∣ Nat.card P := by rw [hPcard]
    exact hpP.trans (Subgroup.card_dvd_of_le hPM)
  have hHallBot :
      IsHallSubgroup (section14KappaPrimes M) ((⊥ : Subgroup G).subgroupOf M) := by
    simpa [hbot] using hHallK
  have hpindex : p.val ∣ ((⊥ : Subgroup G).subgroupOf M).index := by
    simpa [subgroupPrimeSet, Subgroup.bot_subgroupOf, Subgroup.index_bot] using hpM
  exact (hHallBot.p_in_pi_of_p_dvd_index p hpindex) hpκ

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_disjoint_map_mk'_of_le_left_and_disjoint
    {H R N : Subgroup G} [N.Normal]
    (hN_le_H : N ≤ H) (hdisj : Disjoint H R) :
    Disjoint (H.map (QuotientGroup.mk' N)) (R.map (QuotientGroup.mk' N)) := by
  classical
  let qG : G →* G ⧸ N := QuotientGroup.mk' N
  rw [Subgroup.disjoint_def]
  intro x hxH hxR
  rw [Subgroup.mem_map] at hxH hxR
  rcases hxH with ⟨h, hhH, hhx⟩
  rcases hxR with ⟨r, hrR, hrx⟩
  have hrhN : r⁻¹ * h ∈ N := QuotientGroup.eq.mp (hrx.trans hhx.symm)
  have hrhH : r⁻¹ * h ∈ H := hN_le_H hrhN
  have hr_inv_H : r⁻¹ ∈ H := by
    have hmul : (r⁻¹ * h) * h⁻¹ ∈ H := H.mul_mem hrhH (H.inv_mem hhH)
    simpa [mul_assoc] using hmul
  have hrH : r ∈ H := by
    simpa using H.inv_mem hr_inv_H
  have hr_one : r = 1 := Subgroup.disjoint_def.mp hdisj hrH hrR
  calc
    x = qG r := hrx.symm
    _ = 1 := by simp [qG, hr_one]

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_natCard_map_mk'_eq_of_le_left_and_disjoint
    {H R N : Subgroup G} [N.Normal]
    (hN_le_H : N ≤ H) (hdisj : Disjoint H R) :
    Nat.card (R.map (QuotientGroup.mk' N)) = Nat.card R := by
  classical
  let qG : G →* G ⧸ N := QuotientGroup.mk' N
  have hq_inj : Function.Injective (qG ∘ R.subtype) := by
    intro a b hab
    apply Subtype.ext
    change qG (a : G) = qG (b : G) at hab
    have habN : (a : G)⁻¹ * (b : G) ∈ N := QuotientGroup.eq.mp hab
    have habH : (a : G)⁻¹ * (b : G) ∈ H := hN_le_H habN
    have habR : (a : G)⁻¹ * (b : G) ∈ R :=
      R.mul_mem (R.inv_mem a.property) b.property
    have hab_one : (a : G)⁻¹ * (b : G) = 1 :=
      Subgroup.disjoint_def.mp hdisj habH habR
    have := congrArg (fun t : G => (a : G) * t) hab_one
    have hb_eq_a : (b : G) = a := by simpa [mul_assoc] using this
    exact hb_eq_a.symm
  let f : R → R.map qG := fun r => ⟨qG r, ⟨r, r.property, rfl⟩⟩
  have hf_inj : Function.Injective f := by
    intro a b hab
    exact hq_inj (by simpa [f] using congrArg Subtype.val hab)
  have hf_surj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    rcases hx with ⟨r, hrR, rfl⟩
    exact ⟨⟨r, hrR⟩, rfl⟩
  exact Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩).symm

/-- Theorem 15.2 L003-S0050 core: after `K* ≤ O_q(M)`, Proposition 1.5(d)
and Theorem 3.7 force the quotient `M_σ/O_q(M)` to be nilpotent. -/
private theorem CFSG.section15_msigma_quotient_pCore_nilpotent_of_kstar_le
    {M MF K : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMFne : MF ≠ section10Msigma M)
    (hq : q.val = Nat.card (section14KStar M K))
    (hKstarQ : section14KStar M K ≤ section15PCoreIn q M) :
    let S : Subgroup M := section10MsigmaSubgroup M
    let Qloc : Subgroup M := pCore q.val M
    Group.IsNilpotent (S.map (QuotientGroup.mk' Qloc)) := by
  classical
  let S : Subgroup M := section10MsigmaSubgroup M
  let Qloc : Subgroup M := pCore q.val M
  let qM : M →* M ⧸ Qloc := QuotientGroup.mk' Qloc
  let Sbar : Subgroup (M ⧸ Qloc) := S.map qM
  have hP1prod := section15_MF_ne_msigma_implies_P1 hM hMF hK hMFne
  have hP1 : M ∈ section14MFamilyP1 G := hP1prod.1
  have hprime : section14ActsInPrimeManner K (section10Msigma M) :=
    section15_prime_action_of_MF_ne_msigma hM hMF hK hMFne
  have hKne : K ≠ ⊥ := section15_hall_kappa_ne_bot hP1.1 hK
  haveI : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot (H := K)).2 hKne
  obtain ⟨x, hxK, hxne⟩ := Subgroup.exists_ne_one_of_nontrivial K
  rcases section15_exists_primeOrder_zpowers_in (B := K) hxK hxne with
    ⟨r, z, _hzpowx, hzK, _hzne, hRprimeInK⟩
  let R : Subgroup G := Subgroup.zpowers z
  let Kloc : Subgroup M := K.subgroupOf M
  let Rloc : Subgroup M := R.subgroupOf M
  let Rbar : Subgroup (M ⧸ Qloc) := Rloc.map qM
  let T : Subgroup (M ⧸ Qloc) := Sbar ⊔ Rbar
  have hQloc_le_S : Qloc ≤ S := by
    intro x hxQ
    let xG : G := x
    have hxQamb : xG ∈ section15PCoreIn q M := by
      have hxSub : x ∈ (section15PCoreIn q M).subgroupOf M := by
        simpa [Qloc, section15_pCoreIn_subgroupOf_eq q M] using hxQ
      simpa [xG, Subgroup.mem_subgroupOf] using hxSub
    have hxSamb : xG ∈ section10Msigma M :=
      section15_pCoreIn_le_msigma_of_kstar_prime_card hM hq hxQamb
    have hxSsub : x ∈ (section10Msigma M).subgroupOf M := by
      simpa [xG, Subgroup.mem_subgroupOf] using hxSamb
    simpa [S, section15_msigma_subgroupOf_eq] using hxSsub
  have hR_le_K : R ≤ K := Subgroup.zpowers_le.2 hzK
  have hR_le_M : R ≤ M := hR_le_K.trans hK.1
  have hRloc_le_Kloc : Rloc ≤ Kloc := by
    intro y hy
    have hyR : (y : G) ∈ R := by
      simpa [Rloc, Subgroup.mem_subgroupOf] using hy
    have hyK : (y : G) ∈ K := hR_le_K hyR
    simpa [Kloc, Subgroup.mem_subgroupOf] using hyK
  have hS_K_disj : Disjoint S Kloc := by
    simpa [S, Kloc] using
      section15_msigmaSubgroup_disjoint_kappaHall_of_MF_ne hM hMF hK hMFne
  have hS_R_disj : Disjoint S Rloc :=
    hS_K_disj.mono_right hRloc_le_Kloc
  have hS_normal : S.Normal := by
    simpa [S, section15_msigma_subgroupOf_eq] using
      (section15_msigma_normalIn (M := M)).2
  haveI : S.Normal := hS_normal
  have hSbar_normal : Sbar.Normal := by
    exact Subgroup.Normal.map
      (H := S) (inferInstance : S.Normal) qM (QuotientGroup.mk'_surjective Qloc)
  haveI : Sbar.Normal := hSbar_normal
  have hSbar_Rbar_disj : Disjoint Sbar Rbar := by
    simpa [Sbar, Rbar, qM] using
      section15_disjoint_map_mk'_of_le_left_and_disjoint
        (H := S) (R := Rloc) (N := Qloc) hQloc_le_S hS_R_disj
  have hSbarT_normal : (Sbar.subgroupOf T).Normal := by
    exact Subgroup.Normal.subgroupOf (H := Sbar) (K := T) hSbar_normal
  have hSbar_Rbar_comp :
      (Sbar.subgroupOf T).IsComplement' (Rbar.subgroupOf T) := by
    simpa [T] using
      isComplement'_subgroupOf_sup_of_disjoint Sbar Rbar hSbar_Rbar_disj
  have hRprime_card : Nat.Prime (Nat.card R) := by
    rcases (by simpa [R, section10PrimeOrderSubgroupsIn] using hRprimeInK) with
      ⟨_hRK, hRcard⟩
    simpa [R, hRcard] using r.property
  have hRloc_card : Nat.card Rloc = Nat.card R := by
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := R) (K := M) hR_le_M).toEquiv
  have hRloc_prime : Nat.Prime (Nat.card Rloc) := by
    simpa [hRloc_card] using hRprime_card
  have hRbar_card : Nat.card Rbar = Nat.card Rloc := by
    simpa [Rbar, qM] using
      section15_natCard_map_mk'_eq_of_le_left_and_disjoint
        (H := S) (R := Rloc) (N := Qloc) hQloc_le_S hS_R_disj
  have hRbar_prime : Nat.Prime (Nat.card Rbar) := by
    simpa [hRbar_card] using hRloc_prime
  have hRbarT_prime : Nat.Prime (Nat.card (Rbar.subgroupOf T)) := by
    have hcard : Nat.card (Rbar.subgroupOf T) = Nat.card Rbar := by
      exact Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := Rbar) (K := T) le_sup_right).toEquiv
    simpa [hcard] using hRbar_prime
  have hsolvM : Group.IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.2 hM.1)
  have hsolvS : Group.IsSolvable S := by
    letI : Group.IsSolvable M := hsolvM
    infer_instance
  have hsolvQ : Group.IsSolvable (M ⧸ Qloc) := by
    letI : Group.IsSolvable M := hsolvM
    infer_instance
  have hsolvT : Group.IsSolvable T := by
    letI : Group.IsSolvable (M ⧸ Qloc) := hsolvQ
    infer_instance
  have hoddM : Odd (Nat.card M) :=
    odd_of_card_dvd IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card M)
  have hoddQ : Odd (Nat.card (M ⧸ Qloc)) :=
    odd_of_card_dvd hoddM (Subgroup.card_quotient_dvd_card (s := Qloc))
  have hoddT : Odd (Nat.card T) :=
    odd_of_card_dvd hoddQ (Subgroup.card_subgroup_dvd_card T)
  have hHallS : IsHallSubgroup (section10SigmaPrimes M) S := by
    simpa [S] using (theorem_10_2_b (G := G) hM).2
  have hHallKloc : IsHallSubgroup (section14KappaPrimes M) Kloc := by
    simpa [Kloc] using hK.2
  have hπdisj :
      Disjoint (section10SigmaPrimes M) (section14KappaPrimes M) := by
    rw [hP1.2]
    rw [Set.disjoint_left]
    intro p hpσ hpκ
    exact hpκ.2 hpσ
  have hcop_SKloc : Nat.Coprime (Nat.card S) (Nat.card Kloc) :=
    section15_coprime_card_of_hall_disjoint_primes hHallS hHallKloc hπdisj
  have hcop_SRloc : Nat.Coprime (Nat.card S) (Nat.card Rloc) :=
    hcop_SKloc.of_dvd_right (Subgroup.card_dvd_of_le hRloc_le_Kloc)
  have hRloc_norm_S : Rloc ≤ Subgroup.normalizer (S : Set M) :=
    le_top.trans (Subgroup.le_normalizer_of_normal (H := S))
  have hQloc_inv :
      ∀ r : Rloc, ∀ x ∈ Qloc, (r : M) * x * (r : M)⁻¹ ∈ Qloc := by
    intro r x hx
    exact (inferInstance : Qloc.Normal).conj_mem x hx r
  have hRprime_section : R ∈ section12PrimeOrderSubgroups K :=
    section15_primeOrderSubgroups_of_primeOrderSubgroupsIn (A := K) hRprimeInK
  have hcent_local_eq :
      subgroupCentralizerIn S Rloc = (section14KStar M K).subgroupOf M := by
    calc
      subgroupCentralizerIn S Rloc =
          subgroupCentralizerIn ((section10Msigma M).subgroupOf M) (R.subgroupOf M) := by
            simp [S, Rloc, section15_msigma_subgroupOf_eq]
      _ = (subgroupCentralizerIn (section10Msigma M) R).subgroupOf M := by
            rw [subgroupCentralizerIn_subgroupOf_eq M (section10Msigma M) R hR_le_M]
      _ = (section14KStar M K).subgroupOf M := by
            rw [section15_centralizer_eq_kstar_of_prime_manner
              (M := M) (K := K) hprime hRprime_section]
  have hcent_local_le_Q : subgroupCentralizerIn S Rloc ≤ Qloc := by
    intro y hy
    have hyKstar_sub : y ∈ (section14KStar M K).subgroupOf M := by
      simpa [hcent_local_eq] using hy
    have hyKstar : (y : G) ∈ section14KStar M K := by
      simpa [Subgroup.mem_subgroupOf] using hyKstar_sub
    have hyQamb : (y : G) ∈ section15PCoreIn q M := hKstarQ hyKstar
    have hyQsub : y ∈ (section15PCoreIn q M).subgroupOf M := by
      simpa [Subgroup.mem_subgroupOf] using hyQamb
    simpa [Qloc, section15_pCoreIn_subgroupOf_eq q M] using hyQsub
  have hcent_local_map_bot :
      (subgroupCentralizerIn S Rloc).map qM = ⊥ := by
    apply bot_unique
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨x, hxC, rfl⟩
    have hxQ : x ∈ Qloc := hcent_local_le_Q hxC
    simpa [qM, QuotientGroup.eq_one_iff] using hxQ
  have hcent_quot :
      subgroupCentralizerIn Sbar Rbar = ⊥ := by
    have hmap :=
      subgroupCentralizerIn_map_mk'_eq_map_of_solvable_coprime
        (H := S) (R := Rloc) (X := Qloc)
        hRloc_norm_S hsolvS hcop_SRloc hQloc_inv
    calc
      subgroupCentralizerIn Sbar Rbar =
          (subgroupCentralizerIn S Rloc).map qM := by
            simpa [Sbar, Rbar, qM] using hmap
      _ = ⊥ := hcent_local_map_bot
  have hfixT :
      subgroupCentralizerIn (Sbar.subgroupOf T) (Rbar.subgroupOf T) = ⊥ := by
    rw [subgroupCentralizerIn_subgroupOf_eq T Sbar Rbar le_sup_right]
    simp [hcent_quot]
  have hnilSbarT : Group.IsNilpotent (Sbar.subgroupOf T) :=
    theorem_3_7 (G := T) (Sbar.subgroupOf T) (Rbar.subgroupOf T)
      hsolvT hoddT hSbarT_normal hSbar_Rbar_comp hRbarT_prime hfixT
  let e : Sbar.subgroupOf T ≃* Sbar :=
    Subgroup.subgroupOfEquivOfLe (H := Sbar) (K := T) le_sup_left
  exact (by
    simpa [Sbar] using
      (Group.nilpotent_of_mulEquiv
        (G := Sbar.subgroupOf T) (G' := Sbar) (_h := hnilSbarT) e))

omit [Group G] [Finite G] [IsMinCE G] in
private theorem CFSG.section15_pCore_quotient_pCore_eq_bot
    {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime] :
    pCore p (H ⧸ pCore p H) = ⊥ := by
  let qH : H →* H ⧸ pCore p H := QuotientGroup.mk' (pCore p H)
  have hmap :
      (pCore p H).map qH = pCore p (H ⧸ pCore p H) := by
    exact pCore_map_mk'_eq_of_normal_isPGroup (G := H) (p := p) (pCore p H)
      (pCore_isPGroup (G := H) (p := p))
  calc
    pCore p (H ⧸ pCore p H) = (pCore p H).map qH := hmap.symm
    _ = ⊥ := by
      change (pCore p H).map (QuotientGroup.mk' (pCore p H)) = ⊥
      exact QuotientGroup.map_mk'_self (N := pCore p H)

omit [Group G] [Finite G] [IsMinCE G] in
private theorem CFSG.section15_sylow_map_le_pCore_of_nilpotent_normal
    {H : Type*} [Group H] [Finite H]
    {N : Subgroup H} (hN : N.Normal) (hnil : Group.IsNilpotent N)
    (p : ℕ) [Fact p.Prime] (P : Sylow p N) :
    (P : Subgroup N).map N.subtype ≤ pCore p H := by
  have hP_normal : (P : Subgroup N).Normal :=
    Group.IsNilpotent.sylow_normal hnil p P
  have hP_char : (P : Subgroup N).Characteristic :=
    Sylow.characteristic_of_normal P hP_normal
  have hmap_normal : ((P : Subgroup N).map N.subtype).Normal := by
    infer_instance
  have hmap_p : IsPGroup p ((P : Subgroup N).map N.subtype) := by
    exact IsPGroup.map (p := p) (H := (P : Subgroup N)) P.isPGroup' N.subtype
  exact le_sSup
    (show (P : Subgroup N).map N.subtype ∈
        {K : Subgroup H | K.Normal ∧ IsPGroup p K} from
      ⟨hmap_normal, hmap_p⟩)

omit [Group G] [Finite G] [IsMinCE G] in
private theorem CFSG.section15_not_dvd_card_normal_nilpotent_subgroup_quotient_pCore
    {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (N : Subgroup (H ⧸ pCore p H)) [N.Normal]
    (hNnil : Group.IsNilpotent N) :
    ¬ p ∣ Nat.card N := by
  classical
  intro hpN
  let P : Sylow p N := Classical.choice (Sylow.nonempty (p := p) (G := N))
  have hPne : (P : Subgroup N) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card (G := N) (p := p) P hpN
  have hPmap_le :
      (P : Subgroup N).map N.subtype ≤ pCore p (H ⧸ pCore p H) :=
    section15_sylow_map_le_pCore_of_nilpotent_normal
      (N := N) (hN := inferInstance) hNnil p P
  have hcorebot :
      pCore p (H ⧸ pCore p H) = ⊥ :=
    section15_pCore_quotient_pCore_eq_bot (H := H) (p := p)
  have hPmap_bot : (P : Subgroup N).map N.subtype = ⊥ :=
    le_bot_iff.mp (hPmap_le.trans (le_of_eq hcorebot))
  exact hPne
    ((Subgroup.map_eq_bot_iff_of_injective
      (H := (P : Subgroup N)) (f := N.subtype) N.subtype_injective).1 hPmap_bot)

omit [IsMinCE G] in
private theorem CFSG.section15_nilpotentNormalHallIn_of_normal_sylow
    {M Q : Subgroup G} {q : Nat.Primes}
    (hQ : section12SylowSubgroupIn q Q M)
    (hQnormal : section10NormalIn Q M) :
    section15NilpotentNormalHallIn Q M := by
  classical
  rcases hQ with ⟨P, hPamb⟩
  have hQM : Q ≤ M := hQnormal.1
  have hQsub_eq : Q.subgroupOf M = (P : Subgroup M) := by
    rw [← hPamb]
    simpa [section10AmbientSylowSubgroup] using
      (subgroupOf_map_subtype_eq (K := M) (P : Subgroup M))
  have hQp : IsPGroup q.val Q := by
    rw [← hPamb]
    change IsPGroup q.val ((P : Subgroup M).map M.subtype)
    exact IsPGroup.map (p := q.val) (H := (P : Subgroup M))
      P.isPGroup' M.subtype
  have hQnil : Group.IsNilpotent Q := by
    haveI : Fact q.val.Prime := ⟨q.property⟩
    exact IsPGroup.isNilpotent (p := q.val) (G := Q) hQp
  haveI : Fact q.val.Prime := ⟨q.property⟩
  have hQHall :
      IsHallSubgroup (subgroupPrimeSet Q) (Q.subgroupOf M) := by
    refine isHallSubgroup_of
      (G := M) (π := subgroupPrimeSet Q) (H := Q.subgroupOf M) ?_ ?_
    · intro r hr
      have hcard : Nat.card (Q.subgroupOf M) = Nat.card Q := by
        exact Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe (H := Q) (K := M) hQM).toEquiv
      simpa [subgroupPrimeSet, hcard] using hr
    · intro r hrQ hrIndex
      have hQ_single : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) Q :=
        section8_isPiSubgroup_singleton_of_isPGroup hQp
      have hrq : r = q := Set.mem_singleton_iff.mp (hQ_single r hrQ)
      have hnot : ¬ q.val ∣ (Q.subgroupOf M).index := by
        simpa [hQsub_eq] using P.not_dvd_index
      exact hnot (by simpa [hrq] using hrIndex)
  exact ⟨hQM, hQnormal.2, hQnil, hQHall⟩

/-- Theorem 15.2 L003-S0050/L003-S0060: once `K*` meets `F(M)`, the
`q`-core is a normal Sylow `q`-subgroup contained in `M_F`. -/
private theorem CFSG.section15_normal_sylow_q_in_MF_of_kstar_meets_fitting
    {M MF K : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMFne : MF ≠ section10Msigma M)
    (hq : q.val = Nat.card (section14KStar M K))
    (hmeet : section14KStar M K ⊓ section8FittingSubgroup M ≠ ⊥) :
    ∃ Q : Subgroup G,
      section12SylowSubgroupIn q Q M ∧ section10NormalIn Q M ∧
        section14KStar M K ≤ Q ∧ Q ≤ MF := by
  classical
  let Q : Subgroup G := section15PCoreIn q M
  have hKstarQ : section14KStar M K ≤ Q := by
    simpa [Q] using
      section15_kstar_le_pCoreIn_of_meets_fitting
        (M := M) (K := K) hK hq hmeet
  have hQnormal : section10NormalIn Q M := by
    simpa [Q] using section15_pCoreIn_normalIn q M
  have hQsylow : section12SylowSubgroupIn q Q M := by
    let S : Subgroup M := section10MsigmaSubgroup M
    let Qloc : Subgroup M := pCore q.val M
    let qM : M →* M ⧸ Qloc := QuotientGroup.mk' Qloc
    let Sbar : Subgroup (M ⧸ Qloc) := S.map qM
    haveI : Fact q.val.Prime := ⟨q.property⟩
    have hQloc_le_S : Qloc ≤ S := by
      intro x hxQ
      have hxM : (x : G) ∈ M := x.property
      let xG : G := x
      have hxQamb : xG ∈ section15PCoreIn q M := by
        have hxSub : x ∈ (section15PCoreIn q M).subgroupOf M := by
          simpa [section15_pCoreIn_subgroupOf_eq q M] using hxQ
        simpa [xG, Subgroup.mem_subgroupOf] using hxSub
      have hxSamb : xG ∈ section10Msigma M :=
        section15_pCoreIn_le_msigma_of_kstar_prime_card hM hq hxQamb
      have hxSsub : x ∈ (section10Msigma M).subgroupOf M := by
        simpa [xG, Subgroup.mem_subgroupOf] using hxSamb
      simpa [S, section15_msigma_subgroupOf_eq] using hxSsub
    have hSbar_nil : Group.IsNilpotent Sbar := by
      simpa [Sbar, S, Qloc, qM] using
        section15_msigma_quotient_pCore_nilpotent_of_kstar_le
          hM hMF hK hMFne hq hKstarQ
    have hSbar_normal : Sbar.Normal := by
      exact Subgroup.Normal.map
        (H := S) (inferInstance : S.Normal) qM (QuotientGroup.mk'_surjective Qloc)
    haveI : Sbar.Normal := hSbar_normal
    have hnot_card_Sbar : ¬ q.val ∣ Nat.card Sbar :=
      section15_not_dvd_card_normal_nilpotent_subgroup_quotient_pCore
        (H := M) (p := q.val) Sbar hSbar_nil
    have hSbar_card :
        Nat.card Sbar = (Qloc.subgroupOf S).index := by
      calc
        Nat.card Sbar = Nat.card (S ⧸ Qloc.subgroupOf S) := by
          simpa [Sbar, qM] using natCard_map_mk'_eq S Qloc
        _ = (Qloc.subgroupOf S).index := by
          simp [Subgroup.index_eq_card]
    have hnot_QlocS_index : ¬ q.val ∣ (Qloc.subgroupOf S).index := by
      intro hdiv
      exact hnot_card_Sbar (by simpa [hSbar_card] using hdiv)
    have hqσ : q ∈ section10SigmaPrimes M :=
      section15_prime_mem_sigma_of_kstar_prime_card hM hq
    have hnot_S_index : ¬ q.val ∣ S.index := by
      intro hdiv
      exact (((theorem_10_2_b (G := G) hM).2).p_in_pi_of_p_dvd_index q
        (by simpa [S] using hdiv)) hqσ
    have hQloc_index_eq : Qloc.index = (Qloc.subgroupOf S).index * S.index := by
      have hrel := Subgroup.relIndex_mul_index (H := Qloc) (K := S) hQloc_le_S
      change Qloc.index = Qloc.relIndex S * S.index
      exact hrel.symm
    have hnot_Qloc_index : ¬ q.val ∣ Qloc.index := by
      intro hdiv
      have hprod :
          q.val ∣ (Qloc.subgroupOf S).index * S.index := by
        simpa [hQloc_index_eq] using hdiv
      rcases q.property.dvd_or_dvd hprod with hleft | hright
      · exact hnot_QlocS_index hleft
      · exact hnot_S_index hright
    let P : Sylow q.val M :=
      (pCore_isPGroup (G := M) (p := q.val)).toSylow hnot_Qloc_index
    refine ⟨P, ?_⟩
    simp [Q, Qloc, P, section15PCoreIn, section10AmbientSylowSubgroup,
      IsPGroup.toSylow_coe]
  have hQMF : Q ≤ MF :=
    hMF.2 Q (section15_nilpotentNormalHallIn_of_normal_sylow hQsylow hQnormal)
  exact ⟨Q, hQsylow, hQnormal, hKstarQ, hQMF⟩

/-- Theorem 15.2 L003: in the proper-containment branch,
`q = |K*|` is prime and there is a normal Sylow `q`-subgroup `Q ≤ M_F`. -/
public theorem CFSG.section15_kstar_prime_and_normal_sylow
    {M MF K : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMFne : MF ≠ section10Msigma M) :
    ∃ q : Nat.Primes, q.val = Nat.card (section14KStar M K) ∧
      ∃ Q : Subgroup G,
        section12SylowSubgroupIn q Q M ∧ section10NormalIn Q M ∧
          section14KStar M K ≤ Q ∧ Q ≤ MF := by
  have hP1 : M ∈ section14MFamilyP1 G :=
    (section15_MF_ne_msigma_implies_P1 hM hMF hK hMFne).1
  rcases section15_familyP1_kstar_card_prime hM hP1 hK with ⟨q, hq⟩
  have hprime : section14ActsInPrimeManner K (section10Msigma M) :=
    section15_prime_action_of_MF_ne_msigma hM hMF hK hMFne
  have hcomm : ⁅section10Msigma M, K⁆ = section10Msigma M :=
    section15_msigma_commutator_eq_of_prime_action hM hMF hK hMFne hprime
  have hmeet : section14KStar M K ⊓ section8FittingSubgroup M ≠ ⊥ :=
    section15_kstar_meets_fitting_of_MF_ne_msigma hM hMF hK hMFne hcomm
  rcases section15_normal_sylow_q_in_MF_of_kstar_meets_fitting
      hM hMF hK hMFne hq hmeet with ⟨Q, hQ⟩
  exact ⟨q, hq, Q, hQ⟩

/-- Theorem 15.2 L001-S0040: `M_F` is nontrivial.  The source proof derives
this by entering the proper-containment branch and producing a nontrivial
normal Sylow subgroup contained in `M_F`; it is isolated as a core helper so
the public chain theorem does not hide that argument. -/
private theorem CFSG.section15_MF_nontrivial
    {M MF : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF) :
    (⊥ : Subgroup G) < MF := by
  classical
  have hMF_ne_bot : MF ≠ ⊥ := by
    intro hMFbot
    have hMsigma_ne_bot : section10Msigma M ≠ ⊥ :=
      theorem_10_2_e (G := G) hM
    have hMFne : MF ≠ section10Msigma M := by
      intro hEq
      exact hMsigma_ne_bot (by simpa [← hEq] using hMFbot)
    rcases section15_exists_kappa_hallSubgroupIn hM with ⟨K, hK⟩
    rcases section15_kstar_prime_and_normal_sylow hM hMF hK hMFne with
      ⟨q, hq, Q, _hQ, _hQnormal, hKstarQ, hQMF⟩
    have hKstarMF : section14KStar M K ≤ MF := hKstarQ.trans hQMF
    exact (ne_of_gt
      (section15_nontrivial_of_prime_card_subgroup hq hKstarMF)) hMFbot
  exact lt_of_le_of_ne bot_le hMF_ne_bot.symm

/-- Theorem 15.2 L004 setup: in the proper-containment branch,
`M_σ = M'`. -/
private theorem CFSG.section15_msigma_eq_ambientDerived_of_MF_ne
    {M MF K : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMFne : MF ≠ section10Msigma M) :
    section10Msigma M = ambientDerivedSubgroup M := by
  classical
  let S : Subgroup G := section10Msigma M
  let Kloc : Subgroup M := K.subgroupOf M
  let Sloc : Subgroup M := S.subgroupOf M
  have hP1prod := section15_MF_ne_msigma_implies_P1 hM hMF hK hMFne
  have hP1 : M ∈ section14MFamilyP1 G := hP1prod.1
  have hprod : M = K ⊔ S := by
    simpa [S] using hP1prod.2
  have hSleM : S ≤ M := by
    simpa [S] using (section15_msigma_le (M := M))
  have hSnormM : section10NormalIn S M := by
    simpa [S] using (section15_msigma_normalIn (M := M))
  have hHallK : IsHallSubgroup (section14KappaPrimes M) Kloc := by
    simpa [Kloc] using hK.2
  have hHallS : IsHallSubgroup (section10SigmaPrimes M) Sloc := by
    simpa [S, Sloc, section15_msigma_subgroupOf_eq] using
      (theorem_10_2_b (G := G) hM).2
  have hκσdisj : Disjoint (section14KappaPrimes M) (section10SigmaPrimes M) := by
    rw [hP1.2]
    rw [Set.disjoint_left]
    intro p hpκ hpσ
    exact hpκ.2 hpσ
  have hloc_disj : Disjoint Kloc Sloc :=
    section15_disjoint_of_hall_disjoint_primes hHallK hHallS hκσdisj
  have hdisjKS : Disjoint K S := by
    rw [Subgroup.disjoint_def]
    intro x hxK hxS
    have hxM : x ∈ M := hK.1 hxK
    let xM : M := ⟨x, hxM⟩
    have hxKloc : xM ∈ Kloc := by
      simpa [xM, Kloc, Subgroup.mem_subgroupOf] using hxK
    have hxSloc : xM ∈ Sloc := by
      simpa [xM, S, Sloc, Subgroup.mem_subgroupOf] using hxS
    have hxbot : xM ∈ (⊥ : Subgroup M) :=
      Subgroup.disjoint_def.mp hloc_disj hxKloc hxSloc
    change (xM : G) = (1 : G)
    exact congrArg Subtype.val (by simpa using hxbot)
  have hcomp : section12ComplementIn M K S := by
    refine ⟨hK.1, hSleM, ?_, hdisjKS⟩
    simpa [S] using hprod
  have hcomp' : Kloc.IsComplement' Sloc := by
    simpa [Kloc, Sloc] using
      section15_normal_complementIn_isComplement'
        (M := M) (K := K) (N := S) hcomp hSnormM
  have hKcyc : IsCyclic K := by
    have hMP : M ∈ section14MFamilyP G := hP1.1
    have hZcyc : IsCyclic (section14Z M K) :=
      (theorem_14_7_d (G := G) (M := M) (K := K) hMP hK).2.1
    letI : IsCyclic (section14Z M K) := hZcyc
    exact Subgroup.isCyclic_of_le (show K ≤ section14Z M K by
      change K ≤ K ⊔ section14KStar M K
      exact le_sup_left)
  have hKcomm : IsMulCommutative K := by
    letI : IsCyclic K := hKcyc
    infer_instance
  have hKloc_comm : IsMulCommutative Kloc := by
    refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
    apply Subtype.ext
    exact setLike_mul_comm
      (s := K) x.property y.property
  haveI : Sloc.Normal := by
    simpa [S, Sloc] using hSnormM.2
  let eQ : M ⧸ Sloc ≃* Kloc := hcomp'.QuotientMulEquiv
  have hquot_comm : IsMulCommutative (M ⧸ Sloc) := by
    letI : IsMulCommutative Kloc := hKloc_comm
    letI : CommGroup Kloc := IsMulCommutative.instCommGroup
    refine ⟨⟨fun x y => ?_⟩⟩
    apply eQ.injective
    simpa [map_mul] using (mul_comm (eQ x) (eQ y))
  have hder_le_Sloc : derivedSubgroup M ≤ Sloc :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le
      (N := Sloc)).1 hquot_comm
  have hDleS : ambientDerivedSubgroup M ≤ S := by
    intro x hxD
    have hxM : x ∈ M := section15_ambientDerived_le hxD
    let xM : M := ⟨x, hxM⟩
    have hxDer : xM ∈ derivedSubgroup M := by
      have hxSub : xM ∈ (ambientDerivedSubgroup M).subgroupOf M := by
        simpa [xM, Subgroup.mem_subgroupOf] using hxD
      simpa [section15_ambientDerived_subgroupOf_eq] using hxSub
    have hxS : xM ∈ Sloc := hder_le_Sloc hxDer
    simpa [xM, S, Sloc, Subgroup.mem_subgroupOf] using hxS
  exact le_antisymm
    (by simpa [S] using section15_msigma_le_ambientDerived hM)
    (by simpa [S] using hDleS)

/-- Theorem 15.2 L004-S0010/L004-S0020: Proposition 1.5(d) and Theorem 3.7
produce a complement to the normal Sylow `q`-subgroup inside `M_σ`. -/
private theorem CFSG.section15_exists_complement_to_normal_sylow_in_msigma
    {M MF K Q : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMFne : MF ≠ section10Msigma M)
    (_hq : q.val = Nat.card (section14KStar M K))
    (hQ : section12SylowSubgroupIn q Q M)
    (hQnormal : section10NormalIn Q M)
    (hQMF : Q ≤ MF) :
    ∃ D : Subgroup G,
      section12ComplementIn (section10Msigma M) Q D ∧
        K ≤ Subgroup.normalizer (D : Set G) := by
  classical
  let S : Subgroup G := section10Msigma M
  have hSleM : S ≤ M := by
    simpa [S] using (section15_msigma_le (M := M))
  have hQleS : Q ≤ S :=
    hQMF.trans (by simpa [S] using section15_MF_le_msigma (M := M) (MF := MF) hM hMF)
  have hQleM : Q ≤ M := hQleS.trans hSleM
  rcases hQ with ⟨P, hPamb⟩
  let Qloc : Subgroup S := Q.subgroupOf S
  have hQsubM_eq : Q.subgroupOf M = (P : Subgroup M) := by
    rw [← hPamb]
    simpa [section10AmbientSylowSubgroup] using
      (subgroupOf_map_subtype_eq (K := M) (P : Subgroup M))
  have hQloc_card :
      Nat.card Qloc = Nat.card (P : Subgroup M) := by
    calc
      Nat.card Qloc = Nat.card Q := by
        exact Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe (H := Q) (K := S) hQleS).toEquiv
      _ = Nat.card (Q.subgroupOf M) := by
        exact (Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe (H := Q) (K := M) hQleM).toEquiv).symm
      _ = Nat.card (P : Subgroup M) := by
        rw [hQsubM_eq]
  have hQloc_index_dvd :
      Qloc.index ∣ (P : Subgroup M).index := by
    have hrel :
        Q.relIndex S * S.relIndex M = Q.relIndex M :=
      Subgroup.relIndex_mul_relIndex (H := Q) (K := S) (L := M) hQleS hSleM
    have hQrel_dvd :
        Q.relIndex S ∣ Q.relIndex M := ⟨S.relIndex M, hrel.symm⟩
    have hQrelM_eq : Q.relIndex M = (P : Subgroup M).index := by
      change (Q.subgroupOf M).index = (P : Subgroup M).index
      rw [hQsubM_eq]
    change (Q.subgroupOf S).index ∣ (P : Subgroup M).index
    rwa [← hQrelM_eq]
  have hQloc_coprime : Nat.Coprime (Nat.card Qloc) Qloc.index := by
    haveI : Fact q.val.Prime := ⟨q.property⟩
    exact Nat.Coprime.of_dvd_right hQloc_index_dvd
      (by simpa [hQloc_card] using (P.card_coprime_index))
  have hQloc_norm : Qloc.Normal := by
    rcases hQnormal with ⟨_hQM, hQnormM⟩
    refine ⟨fun x hx y => ?_⟩
    have hxQ : ((x : S) : G) ∈ Q := by
      simpa [Qloc, Subgroup.mem_subgroupOf] using hx
    let xM : M := ⟨((x : S) : G), hQleM hxQ⟩
    let yM : M := ⟨((y : S) : G), hSleM y.property⟩
    have hxQM : xM ∈ Q.subgroupOf M := by
      simpa [xM, Subgroup.mem_subgroupOf] using hxQ
    have hconjM : yM * xM * yM⁻¹ ∈ Q.subgroupOf M :=
      Subgroup.Normal.conj_mem hQnormM xM hxQM yM
    have hconjQ : (((y * x * y⁻¹ : S) : G)) ∈ Q := by
      simpa [xM, yM, Subgroup.mem_subgroupOf] using hconjM
    simpa [Qloc, Subgroup.mem_subgroupOf] using hconjQ
  haveI : Qloc.Normal := hQloc_norm
  have hSnormM : section10NormalIn S M := by
    simpa [S] using (section15_msigma_normalIn (M := M))
  have hM_norm_S : M ≤ Subgroup.normalizer (S : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSnormM.1).1 hSnormM.2
  have hK_norm_S : K ≤ Subgroup.normalizer (S : Set G) :=
    hK.1.trans hM_norm_S
  haveI : Subgroup.Normalizes K S := ⟨hK_norm_S⟩
  have hsolvM : Group.IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.2 hM.1)
  have hsolvS : Group.IsSolvable S := by
    let Sloc : Subgroup M := S.subgroupOf M
    have hSloc_solv : Group.IsSolvable Sloc := by
      letI : Group.IsSolvable M := hsolvM
      infer_instance
    let eS : Sloc ≃* S :=
      Subgroup.subgroupOfEquivOfLe (H := S) (K := M) hSleM
    exact Group.isSolvable_of_surjective (f := eS.toMonoidHom) eS.surjective
  have hK_S_coprime : Nat.Coprime (Nat.card K) (Nat.card S) := by
    have hP1 : M ∈ section14MFamilyP1 G :=
      (section15_MF_ne_msigma_implies_P1 hM hMF hK hMFne).1
    have hκσdisj : Disjoint (section14KappaPrimes M) (section10SigmaPrimes M) := by
      rw [hP1.2]
      rw [Set.disjoint_left]
      intro p hpκ hpσ
      exact hpκ.2 hpσ
    let KlocM : Subgroup M := K.subgroupOf M
    let SlocM : Subgroup M := S.subgroupOf M
    have hHallK : IsHallSubgroup (section14KappaPrimes M) KlocM := by
      simpa [KlocM] using hK.2
    have hHallS : IsHallSubgroup (section10SigmaPrimes M) SlocM := by
      simpa [S, SlocM, section15_msigma_subgroupOf_eq] using
        (theorem_10_2_b (G := G) hM).2
    have hcopLoc : Nat.Coprime (Nat.card KlocM) (Nat.card SlocM) :=
      section15_coprime_card_of_hall_disjoint_primes hHallK hHallS hκσdisj
    have hKloc_card : Nat.card (K.subgroupOf M) = Nat.card K :=
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := K) (K := M) hK.1).toEquiv
    have hSloc_card : Nat.card (S.subgroupOf M) = Nat.card S :=
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := S) (K := M) hSleM).toEquiv
    simpa [KlocM, SlocM, hKloc_card, hSloc_card] using hcopLoc
  have hQloc_p : IsPGroup q.val Qloc := by
    haveI : Fact q.val.Prime := ⟨q.property⟩
    rcases IsPGroup.iff_card.mp P.isPGroup' with ⟨n, hn⟩
    exact IsPGroup.iff_card.mpr ⟨n, by simp [hQloc_card, hn]⟩
  have hQloc_not_dvd_index : ¬ q.val ∣ Qloc.index := by
    haveI : Fact q.val.Prime := ⟨q.property⟩
    intro hqidx
    exact P.not_dvd_index (hqidx.trans hQloc_index_dvd)
  have hQlocHall : IsHallSubgroup ({q} : Set Nat.Primes) Qloc := by
    refine isHallSubgroup_of (G := S) (π := ({q} : Set Nat.Primes)) (H := Qloc) ?_ ?_
    · exact section8_isPiSubgroup_singleton_of_isPGroup hQloc_p
    · intro r hr hidx
      have hrq : r = q := by simpa using hr
      exact hQloc_not_dvd_index (by simpa [hrq] using hidx)
  let πD : Set Nat.Primes := ({q} : Set Nat.Primes)ᶜ
  rcases exists_isHallSubgroup_isInvariant
      (G := S) (A := K) hsolvS hK_S_coprime πD with
    ⟨Dloc, hDlocHall, hDloc_inv⟩
  have hcompl : Qloc.IsComplement' Dloc := by
    simpa [πD] using
      section11_isComplement_of_isHall_compl
        (G := S) (π := ({q} : Set Nat.Primes))
        (N := Qloc) (E := Dloc) hQlocHall hDlocHall
  let D : Subgroup G := section8SubgroupInAmbient Dloc
  have hKnormD : K ≤ Subgroup.normalizer (D : Set G) := by
    intro k hkK
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hxD
      rcases Subgroup.mem_map.mp hxD with ⟨xS, hxDloc, rfl⟩
      have hxDsmul : (⟨k, hkK⟩ : K) • xS ∈ Dloc :=
        (IsInvariant.invariant (A := K) (G := S) (H := Dloc)
          (⟨k, hkK⟩ : K) xS).1 hxDloc
      exact Subgroup.mem_map.mpr ⟨(⟨k, hkK⟩ : K) • xS, hxDsmul, by
        simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]⟩
    · intro hxD
      rcases Subgroup.mem_map.mp hxD with ⟨xS, hxDloc, hxS_eq⟩
      have hxDsmul : ((⟨k, hkK⟩ : K)⁻¹) • xS ∈ Dloc :=
        (IsInvariant.invariant (A := K) (G := S) (H := Dloc)
          ((⟨k, hkK⟩ : K)⁻¹) xS).1 hxDloc
      exact Subgroup.mem_map.mpr
        ⟨((⟨k, hkK⟩ : K)⁻¹) • xS, hxDsmul, by
          simp [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
          change k⁻¹ * S.subtype xS * k = x
          rw [hxS_eq]
          simp [mul_assoc]⟩
  refine ⟨D, ?_, hKnormD⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [S] using hQleS
  · intro x hxD
    rcases Subgroup.mem_map.mp hxD with ⟨y, _hy, rfl⟩
    exact (y : S).property
  · apply le_antisymm
    · intro x hxS
      let xS : S := ⟨x, by simpa [S] using hxS⟩
      have hxTop : xS ∈ (⊤ : Subgroup S) := by simp
      have hxSup : xS ∈ Qloc ⊔ Dloc := by
        simp [hcompl.sup_eq_top]
      have hDleS : D ≤ S := by
        intro x hxD
        rcases Subgroup.mem_map.mp hxD with ⟨y, _hy, rfl⟩
        exact (y : S).property
      have hxSupAmb : x ∈ Q ⊔ D := by
        have hxSub : xS ∈ (Q ⊔ D).subgroupOf S := by
          have hsub_eq :
              (Q ⊔ D).subgroupOf S = Qloc ⊔ Dloc := by
            calc
              (Q ⊔ D).subgroupOf S =
                  Q.subgroupOf S ⊔ D.subgroupOf S := by
                exact Subgroup.subgroupOf_sup (A := Q) (A' := D) (B := S)
                  hQleS hDleS
              _ = Qloc ⊔ Dloc := by
                rw [section8SubgroupInAmbient_subgroupOf_eq]
          simpa [hsub_eq] using hxSup
        simpa [xS, Subgroup.mem_subgroupOf] using hxSub
      simpa [S] using hxSupAmb
    · exact sup_le hQleS (by
        intro x hxD
        rcases Subgroup.mem_map.mp hxD with ⟨y, _hy, rfl⟩
        exact (y : S).property)
  · rw [Subgroup.disjoint_def]
    intro x hxQ hxD
    let xS : S := ⟨x, hQleS hxQ⟩
    have hxQloc : xS ∈ Qloc := by
      simpa [xS, Qloc, Subgroup.mem_subgroupOf] using hxQ
    have hxDloc : xS ∈ Dloc := by
      have hxDsub : xS ∈ D.subgroupOf S := by
        simpa [xS, Subgroup.mem_subgroupOf] using hxD
      simpa [D, section8SubgroupInAmbient_subgroupOf_eq] using hxDsub
    have hxbot : xS ∈ (⊥ : Subgroup S) :=
      Subgroup.disjoint_def.mp hcompl.disjoint hxQloc hxDloc
    change (xS : G) = (1 : G)
    exact congrArg Subtype.val (by simpa using hxbot)

/-- Theorem 15.2 L004-S0030: the complement `D` is nilpotent because it maps
isomorphically to the nilpotent quotient `M_σ / Q`. -/
private theorem CFSG.section15_complement_to_Q_nilpotent
    {M MF K Q D : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMFne : MF ≠ section10Msigma M)
    (hq : q.val = Nat.card (section14KStar M K))
    (hQ : section12SylowSubgroupIn q Q M)
    (hQnormal : section10NormalIn Q M)
    (_hQMF : Q ≤ MF)
    (hDcompl : section12ComplementIn (section10Msigma M) Q D) :
    Group.IsNilpotent D := by
  classical
  haveI : Fact q.val.Prime := ⟨q.property⟩
  let S : Subgroup G := section10Msigma M
  let Sloc : Subgroup M := section10MsigmaSubgroup M
  let Dloc : Subgroup M := D.subgroupOf M
  have hQleS : Q ≤ S := by
    simpa [S] using hDcompl.1
  have hDleS : D ≤ S := by
    simpa [S] using hDcompl.2.1
  have hSleM : S ≤ M := by
    simpa [S] using (section15_msigma_le (M := M))
  have hQleM : Q ≤ M := hQleS.trans hSleM
  have hDleM : D ≤ M := hDleS.trans hSleM
  let Qloc : Subgroup M := pCore q.val M
  have hQsub_eq_pcore : Q.subgroupOf M = Qloc := by
    simpa [Qloc] using
      section15_normal_sylowSubgroupIn_subgroupOf_eq_pCore
        (M := M) (Q := Q) (q := q) hQ hQnormal
  have hQloc_normal : Qloc.Normal := by
    simpa [Qloc] using (pCore_normal (p := q.val) (G := M))
  haveI : Qloc.Normal := hQloc_normal
  let qM : M →* M ⧸ Qloc := QuotientGroup.mk' Qloc
  have hKstar_le_Q : section14KStar M K ≤ Q :=
    section15_kstar_le_normal_sylow_of_prime_card
      (M := M) (K := K) (Q := Q) (q := q) hq hQ hQnormal
  have hKstar_le_core : section14KStar M K ≤ section15PCoreIn q M := by
    intro x hx
    have hxQ : x ∈ Q := hKstar_le_Q hx
    let xM : M := ⟨x, hQleM hxQ⟩
    have hxQsub : xM ∈ Q.subgroupOf M := by
      simpa [xM, Subgroup.mem_subgroupOf] using hxQ
    have hxCore : xM ∈ pCore q.val M := by
      simpa [hQsub_eq_pcore, Qloc] using hxQsub
    change x ∈ (pCore q.val M).map M.subtype
    exact Subgroup.mem_map.mpr ⟨xM, hxCore, rfl⟩
  have hSbar_nil : Group.IsNilpotent (Sloc.map qM) := by
    have hnil :=
      section15_msigma_quotient_pCore_nilpotent_of_kstar_le
        (M := M) (MF := MF) (K := K) (q := q)
        hM hMF hK hMFne hq hKstar_le_core
    simpa [Sloc, Qloc, qM] using hnil
  have hDloc_le_Sloc : Dloc ≤ Sloc := by
    intro x hxDloc
    have hxD : (x : G) ∈ D := by
      simpa [Dloc, Subgroup.mem_subgroupOf] using hxDloc
    have hxS : (x : G) ∈ S := hDleS hxD
    have hxSsub : x ∈ S.subgroupOf M := by
      simpa [S, Subgroup.mem_subgroupOf] using hxS
    simpa [Sloc, S, section15_msigma_subgroupOf_eq] using hxSsub
  have hDmap_le_Sbar : Dloc.map qM ≤ Sloc.map qM :=
    Subgroup.map_mono hDloc_le_Sloc
  have hDmap_sub_nil :
      Group.IsNilpotent ((Dloc.map qM).subgroupOf (Sloc.map qM)) := by
    letI : Group.IsNilpotent (Sloc.map qM) := hSbar_nil
    exact Subgroup.isNilpotent ((Dloc.map qM).subgroupOf (Sloc.map qM))
  have hDmap_nil : Group.IsNilpotent (Dloc.map qM) := by
    let e : (Dloc.map qM).subgroupOf (Sloc.map qM) ≃* Dloc.map qM :=
      Subgroup.subgroupOfEquivOfLe (H := Dloc.map qM) (K := Sloc.map qM)
        hDmap_le_Sbar
    exact Group.nilpotent_of_mulEquiv
      (G := (Dloc.map qM).subgroupOf (Sloc.map qM)) (G' := Dloc.map qM)
      (_h := hDmap_sub_nil) e
  have hQlocDloc_bot : Qloc.subgroupOf Dloc = ⊥ := by
    ext x
    constructor
    · intro hx
      have hxQloc : ((x : Dloc) : M) ∈ Qloc := by
        simpa [Subgroup.mem_subgroupOf] using hx
      have hxQsub : ((x : Dloc) : M) ∈ Q.subgroupOf M := by
        simpa [hQsub_eq_pcore] using hxQloc
      have hxQ : ((x : Dloc) : G) ∈ Q := by
        simpa [Subgroup.mem_subgroupOf] using hxQsub
      have hxD : ((x : Dloc) : G) ∈ D := by
        exact x.property
      have hxoneG : ((x : Dloc) : G) = 1 :=
        Subgroup.disjoint_def.mp hDcompl.2.2.2 hxQ hxD
      have hxone : x = 1 := by
        apply Subtype.ext
        exact Subtype.ext hxoneG
      simp [hxone]
    · intro hx
      rw [hx]
      exact Subgroup.one_mem (Qloc.subgroupOf Dloc)
  have hDquot_nil : Group.IsNilpotent (Dloc ⧸ Qloc.subgroupOf Dloc) := by
    let e : Dloc ⧸ Qloc.subgroupOf Dloc ≃* Dloc.map qM :=
      quotientSubgroupRangeEquiv Dloc Qloc
    exact Group.nilpotent_of_mulEquiv
      (G := Dloc.map qM) (G' := Dloc ⧸ Qloc.subgroupOf Dloc)
      (_h := hDmap_nil) e.symm
  have hDloc_nil : Group.IsNilpotent Dloc := by
    let e : Dloc ⧸ Qloc.subgroupOf Dloc ≃* Dloc :=
      (QuotientGroup.quotientMulEquivOfEq hQlocDloc_bot).trans QuotientGroup.quotientBot
    exact Group.nilpotent_of_mulEquiv
      (G := Dloc ⧸ Qloc.subgroupOf Dloc) (G' := Dloc)
      (_h := hDquot_nil) e
  let eD : Dloc ≃* D :=
    Subgroup.subgroupOfEquivOfLe (H := D) (K := M) hDleM
  exact Group.nilpotent_of_mulEquiv (G := Dloc) (G' := D) (_h := hDloc_nil) eD

/-- Theorem 15.2 L004: package the nilpotent complement data. -/
private theorem CFSG.section15_theorem15_2_nilpotent_complement
    {M MF K Q : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMFne : MF ≠ section10Msigma M)
    (hq : q.val = Nat.card (section14KStar M K))
    (hQ : section12SylowSubgroupIn q Q M)
    (hQnormal : section10NormalIn Q M)
    (hQMF : Q ≤ MF) :
    ∃ D : Subgroup G,
      section15Theorem15_2ComplementData M K Q D := by
  rcases section15_exists_complement_to_normal_sylow_in_msigma
      hM hMF hK hMFne hq hQ hQnormal hQMF with ⟨D, hDcompl, hDkinv⟩
  refine ⟨D, ?_, hDcompl, ?_, hDkinv⟩
  · exact section15_msigma_eq_ambientDerived_of_MF_ne hM hMF hK hMFne
  · exact section15_complement_to_Q_nilpotent
      hM hMF hK hMFne hq hQ hQnormal hQMF hDcompl

omit [Finite G] [IsMinCE G] in
/-- Theorem 15.2 L005-S0010: the complement `D` may be chosen `K`-invariant
by Proposition 1.5(a). -/
private theorem CFSG.section15_complement_D_K_invariant
    {M MF K Q D : Subgroup G} {q : Nat.Primes}
    (_hM : M ∈ section9MaximalSubgroups G)
    (_hMF : section15MFSubgroup M MF)
    (_hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (_hMFne : MF ≠ section10Msigma M)
    (_hq : q.val = Nat.card (section14KStar M K))
    (_hQ : section12SylowSubgroupIn q Q M)
    (_hQnormal : section10NormalIn Q M)
    (_hQMF : Q ≤ MF)
    (hD : section15Theorem15_2ComplementData M K Q D) :
    K ≤ Subgroup.normalizer (D : Set G) := by
  exact hD.2.2.2

omit [Finite G] [IsMinCE G] in
/-- Theorem 15.2 L005-S0020: a `K`-invariant complement makes
`Q₀ = C_Q(D)` invariant under `KD`. -/
private theorem CFSG.section15_Q0_KD_invariant_of_K_invariant_complement
    {M MF K Q D : Subgroup G} {q : Nat.Primes}
    (_hM : M ∈ section9MaximalSubgroups G)
    (_hMF : section15MFSubgroup M MF)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (_hMFne : MF ≠ section10Msigma M)
    (_hq : q.val = Nat.card (section14KStar M K))
    (_hQ : section12SylowSubgroupIn q Q M)
    (hQnormal : section10NormalIn Q M)
    (_hQMF : Q ≤ MF)
    (hD : section15Theorem15_2ComplementData M K Q D)
    (hDkinv : K ≤ Subgroup.normalizer (D : Set G)) :
    K ⊔ D ≤ Subgroup.normalizer (subgroupCentralizerIn Q D : Set G) := by
  classical
  let Q₀ : Subgroup G := subgroupCentralizerIn Q D
  have hDcomp : section12ComplementIn (section10Msigma M) Q D := hD.2.1
  have hMleNormQ : M ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQnormal.1).1 hQnormal.2
  have hKnormQ : K ≤ Subgroup.normalizer (Q : Set G) :=
    hK.1.trans hMleNormQ
  have hKnormQ₀ : K ≤ Subgroup.normalizer (Q₀ : Set G) := by
    simpa [Q₀] using
      section15_le_normalizer_subgroupCentralizerIn
        (N := K) (E := Q) (A := D) hKnormQ hDkinv
  have hDnormQ : D ≤ Subgroup.normalizer (Q : Set G) :=
    hDcomp.2.1.trans (section15_msigma_le.trans hMleNormQ)
  have hDnormQ₀ : D ≤ Subgroup.normalizer (Q₀ : Set G) := by
    simpa [Q₀] using
      section15_le_normalizer_subgroupCentralizerIn
        (N := D) (E := Q) (A := D) hDnormQ Subgroup.le_normalizer
  simpa [Q₀] using sup_le hKnormQ₀ hDnormQ₀

/-- The minimal-normal part of the quotient assertion in Theorem 15.2(f). -/
private def CFSG.section15QuotientMinimalNormal
    (M Q Q₀ : Subgroup G) : Prop :=
  ∃ _hQ₀M : Q₀ ≤ M, ∃ _hQM : Q ≤ M, ∃ _hQ₀Q : Q₀ ≤ Q,
    ∃ _hNorm : (Q₀.subgroupOf M).Normal,
      let Qbar : Subgroup (M ⧸ Q₀.subgroupOf M) :=
        (Q.subgroupOf M).map (QuotientGroup.mk' (Q₀.subgroupOf M))
      Qbar ≠ ⊥ ∧ Qbar.Normal ∧
        ∀ N : Subgroup (M ⧸ Q₀.subgroupOf M),
          N.Normal → N ≤ Qbar → N = ⊥ ∨ N = Qbar

/-- The elementary-abelian cardinality part of Theorem 15.2(f). -/
private def CFSG.section15QuotientElementaryCard
    (M Q Q₀ : Subgroup G) (p q : Nat.Primes) : Prop :=
  ∃ _hQ₀M : Q₀ ≤ M, ∃ _hQM : Q ≤ M, ∃ _hQ₀Q : Q₀ ≤ Q,
    ∃ _hNorm : (Q₀.subgroupOf M).Normal,
      let Qbar : Subgroup (M ⧸ Q₀.subgroupOf M) :=
        (Q.subgroupOf M).map (QuotientGroup.mk' (Q₀.subgroupOf M))
      IsElementaryAbelian q.val Qbar ∧ Nat.card Qbar = q.val ^ p.val

omit [IsMinCE G] in
private theorem CFSG.section15_sylowSubgroupIn_nilpotent
    {M Q : Subgroup G} {q : Nat.Primes}
    (hQ : section12SylowSubgroupIn q Q M) :
    Group.IsNilpotent Q := by
  classical
  rcases hQ with ⟨P, hP⟩
  have hQp : IsPGroup q.val Q := by
    rw [← hP]
    change IsPGroup q.val ((P : Subgroup M).map M.subtype)
    exact IsPGroup.map (p := q.val) (H := (P : Subgroup M))
      P.isPGroup' M.subtype
  haveI : Fact q.val.Prime := ⟨q.property⟩
  exact IsPGroup.isNilpotent (p := q.val) (G := Q) hQp

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_nilpotent_of_central_complement
    {S Q D : Subgroup G}
    (hcomp : section12ComplementIn S Q D)
    (hQnorm : section10NormalIn Q S)
    (hQnil : Group.IsNilpotent Q)
    (hDnil : Group.IsNilpotent D)
    (hQcentD : Q ≤ Subgroup.centralizer (D : Set G)) :
    Group.IsNilpotent S := by
  classical
  let Qloc : Subgroup S := Q.subgroupOf S
  let Dloc : Subgroup S := D.subgroupOf S
  haveI : Qloc.Normal := by
    simpa [Qloc] using hQnorm.2
  have hsup : Qloc ⊔ Dloc = ⊤ := by
    calc
      Qloc ⊔ Dloc = (Q ⊔ D).subgroupOf S := by
        symm
        exact Subgroup.subgroupOf_sup (A := Q) (A' := D) (B := S)
          hcomp.1 hcomp.2.1
      _ = ⊤ := by
        rw [← hcomp.2.2.1]
        simp
  have hcomp' : Qloc.IsComplement' Dloc := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [Subgroup.disjoint_def]
      intro x hxQ hxD
      apply Subtype.ext
      apply Subgroup.disjoint_def.mp hcomp.2.2.2
      · simpa [Qloc, Subgroup.mem_subgroupOf] using hxQ
      · simpa [Dloc, Subgroup.mem_subgroupOf] using hxD
    · ext x
      constructor
      · intro _hx
        simp
      · intro _hx
        have hxSup : x ∈ Qloc ⊔ Dloc := by
          simp [hsup]
        rcases (Subgroup.mem_sup_of_normal_left (s := Qloc) (t := Dloc) (x := x)).1
            hxSup with
          ⟨q, hq, d, hd, hqd⟩
        exact ⟨q, hq, d, hd, hqd⟩
  let hDleNormQ : Dloc ≤ Subgroup.normalizer (Qloc : Set S) :=
    Qloc.normalizer_eq_top ▸ le_top
  let eSD :
      Qloc ⋊[(Qloc.normalizerMonoidHom).comp
        (Subgroup.inclusion hDleNormQ)] Dloc ≃* S :=
    SemidirectProduct.mulEquivSubgroup hcomp'
  have hphi_eq :
      (Qloc.normalizerMonoidHom.comp (Subgroup.inclusion hDleNormQ)) = 1 := by
    ext d q
    simp [Subgroup.normalizerMonoidHom]
    have hqQ : ((q : S) : G) ∈ Q := q.property
    have hdD : ((d : S) : G) ∈ D := d.property
    have hcomm :
        ((d : S) : G) * ((q : S) : G) =
          ((q : S) : G) * ((d : S) : G) :=
      (Subgroup.mem_centralizer_iff.mp (hQcentD hqQ)) ((d : S) : G) hdD
    calc
      ((d : S) : G) * ((q : S) : G) * ((d : S) : G)⁻¹ =
          ((q : S) : G) * ((d : S) : G) * ((d : S) : G)⁻¹ := by
        rw [hcomm]
      _ = ((q : S) : G) := by
        simp [mul_assoc]
  let eprod :
      Qloc ⋊[(Qloc.normalizerMonoidHom).comp
        (Subgroup.inclusion hDleNormQ)] Dloc ≃* Qloc × Dloc := by
    rw [hphi_eq]
    exact SemidirectProduct.mulEquivProd
  have hQloc_nil : Group.IsNilpotent Qloc := by
    let e : Qloc ≃* Q := Subgroup.subgroupOfEquivOfLe hcomp.1
    exact Group.nilpotent_of_mulEquiv (G := Q) (G' := Qloc) (_h := hQnil) e.symm
  have hDloc_nil : Group.IsNilpotent Dloc := by
    let e : Dloc ≃* D := Subgroup.subgroupOfEquivOfLe hcomp.2.1
    exact Group.nilpotent_of_mulEquiv (G := D) (G' := Dloc) (_h := hDnil) e.symm
  have hprod_nil : Group.IsNilpotent (Qloc × Dloc) := by
    letI : Group.IsNilpotent Qloc := hQloc_nil
    letI : Group.IsNilpotent Dloc := hDloc_nil
    infer_instance
  exact Group.nilpotent_of_mulEquiv
    (G := Qloc × Dloc) (G' := S) (_h := hprod_nil) (eprod.symm.trans eSD)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_lt_inf_normalizer_of_lt_of_nilpotent
    {Q C : Subgroup G}
    (hC_lt_Q : C < Q) (hQnil : Group.IsNilpotent Q) :
    C < Q ⊓ Subgroup.normalizer (C : Set G) := by
  classical
  let Cq : Subgroup Q := C.subgroupOf Q
  have hC_le_Q : C ≤ Q := hC_lt_Q.le
  rcases SetLike.exists_of_lt hC_lt_Q with ⟨x, hxQ, hxC⟩
  have hCq_lt_top : Cq < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    have hxCq : (⟨x, hxQ⟩ : Q) ∈ Cq := by
      simp [htop]
    exact hxC (by simpa [Cq, Subgroup.mem_subgroupOf] using hxCq)
  letI : Group.IsNilpotent Q := hQnil
  have hnc : NormalizerCondition Q := Group.normalizerCondition_of_isNilpotent (G := Q)
  have hCq_lt_norm : Cq < Subgroup.normalizer (Cq : Set Q) :=
    hnc Cq hCq_lt_top
  refine lt_of_le_of_ne ?_ ?_
  · intro y hyC
    exact ⟨hC_le_Q hyC, Subgroup.le_normalizer hyC⟩
  · intro hEq
    rcases SetLike.exists_of_lt hCq_lt_norm with ⟨y, hyNorm, hyCq⟩
    have hyNormAmbient : (y : G) ∈ Subgroup.normalizer (C : Set G) := by
      rw [Subgroup.mem_normalizer_iff] at hyNorm ⊢
      intro z
      constructor
      · intro hzC
        let zq : Q := ⟨z, hC_le_Q hzC⟩
        have hzCq : zq ∈ Cq := by
          simpa [Cq, zq, Subgroup.mem_subgroupOf] using hzC
        have hconj : y * zq * y⁻¹ ∈ Cq := (hyNorm zq).1 hzCq
        simpa [Cq, zq, Subgroup.mem_subgroupOf] using hconj
      · intro hzC
        have hzQ : z ∈ Q := by
          have hzConjQ : (y : G) * z * (y : G)⁻¹ ∈ Q := hC_le_Q hzC
          have hzQ' : (y : G)⁻¹ * ((y : G) * z * (y : G)⁻¹) * (y : G) ∈ Q :=
            Q.mul_mem (Q.mul_mem (Q.inv_mem y.property) hzConjQ) y.property
          simpa [mul_assoc] using hzQ'
        let zq : Q := ⟨z, hzQ⟩
        have hzConjCq : y * zq * y⁻¹ ∈ Cq := by
          simpa [Cq, zq, Subgroup.mem_subgroupOf] using hzC
        have hzCq : zq ∈ Cq := (hyNorm zq).2 hzConjCq
        simpa [Cq, zq, Subgroup.mem_subgroupOf] using hzCq
    have hyInf : (y : G) ∈ Q ⊓ Subgroup.normalizer (C : Set G) :=
      ⟨y.property, hyNormAmbient⟩
    have hyC : (y : G) ∈ C := by
      rw [hEq]
      exact hyInf
    exact hyCq (by simpa [Cq, Subgroup.mem_subgroupOf] using hyC)

/-- Theorem 15.2 L005-S0030: `Q₀=C_Q(D)` is proper in `Q`. -/
private theorem CFSG.section15_Q0_lt_Q
    {M MF K Q D : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (_hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMFne : MF ≠ section10Msigma M)
    (_hq : q.val = Nat.card (section14KStar M K))
    (hQ : section12SylowSubgroupIn q Q M)
    (hQnormal : section10NormalIn Q M)
    (_hQMF : Q ≤ MF)
    (hD : section15Theorem15_2ComplementData M K Q D) :
    subgroupCentralizerIn Q D < Q := by
  classical
  refine lt_of_le_of_ne inf_le_left ?_
  intro hQ₀eq
  let S : Subgroup G := section10Msigma M
  have hDcomp : section12ComplementIn S Q D := by
    simpa [S] using hD.2.1
  have hQcentD : Q ≤ Subgroup.centralizer (D : Set G) := by
    intro x hxQ
    have hxQ₀ : x ∈ subgroupCentralizerIn Q D := by
      simpa [hQ₀eq] using hxQ
    exact hxQ₀.2
  have hSleM : S ≤ M := by
    simpa [S] using (section15_msigma_le (M := M))
  have hQnormS : section10NormalIn Q S := by
    refine ⟨hDcomp.1, ?_⟩
    have hMleNormQ : M ≤ Subgroup.normalizer (Q : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQnormal.1).1 hQnormal.2
    have hSleNormQ : S ≤ Subgroup.normalizer (Q : Set G) :=
      hSleM.trans hMleNormQ
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hDcomp.1).2 hSleNormQ
  have hQnil : Group.IsNilpotent Q :=
    section15_sylowSubgroupIn_nilpotent hQ
  have hSnil : Group.IsNilpotent S :=
    section15_nilpotent_of_central_complement hDcomp hQnormS hQnil hD.2.2.1 hQcentD
  exact (section15_MF_ne_msigma_not_nilpotent hM hMF hMFne) (by
    simpa [S] using hSnil)


omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_normalIn_inf_normalizer
    {M C : Subgroup G} (hCM : C ≤ M) :
    section10NormalIn C (M ⊓ Subgroup.normalizer (C : Set G)) := by
  have hC_le_N : C ≤ M ⊓ Subgroup.normalizer (C : Set G) := by
    intro x hx
    exact ⟨hCM hx, Subgroup.le_normalizer hx⟩
  refine ⟨hC_le_N, ?_⟩
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hC_le_N).2 inf_le_right

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_inf_normalizer_normalIn_inf_normalizer_of_normalIn
    {M Q C : Subgroup G} (hQnormal : section10NormalIn Q M) :
    section10NormalIn (Q ⊓ Subgroup.normalizer (C : Set G))
      (M ⊓ Subgroup.normalizer (C : Set G)) := by
  classical
  let QN : Subgroup G := Q ⊓ Subgroup.normalizer (C : Set G)
  let N : Subgroup G := M ⊓ Subgroup.normalizer (C : Set G)
  have hQN_le_N : QN ≤ N := by
    intro x hx
    exact ⟨hQnormal.1 hx.1, hx.2⟩
  refine ⟨hQN_le_N, ?_⟩
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hQN_le_N).2 ?_
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hnQ : n ∈ Subgroup.normalizer (Q : Set G) :=
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hQnormal.1).1 hQnormal.2) hn.1
    have hxQ : x ∈ Q := hx.1
    have hxCnorm : x ∈ Subgroup.normalizer (C : Set G) := hx.2
    refine ⟨(Subgroup.mem_normalizer_iff.mp hnQ x).1 hxQ, ?_⟩
    exact (Subgroup.normalizer (C : Set G)).mul_mem
      ((Subgroup.normalizer (C : Set G)).mul_mem hn.2 hxCnorm)
      ((Subgroup.normalizer (C : Set G)).inv_mem hn.2)
  · intro hx
    have hnQ : n ∈ Subgroup.normalizer (Q : Set G) :=
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hQnormal.1).1 hQnormal.2) hn.1
    have hnInvQ : n⁻¹ ∈ Subgroup.normalizer (Q : Set G) :=
      (Subgroup.normalizer (Q : Set G)).inv_mem hnQ
    have hnInvC : n⁻¹ ∈ Subgroup.normalizer (C : Set G) :=
      (Subgroup.normalizer (C : Set G)).inv_mem hn.2
    have hxQ : n⁻¹ * (n * x * n⁻¹) * (n⁻¹)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp hnInvQ (n * x * n⁻¹)).1 hx.1
    have hxCnorm : n⁻¹ * (n * x * n⁻¹) * (n⁻¹)⁻¹ ∈
        Subgroup.normalizer (C : Set G) :=
      (Subgroup.normalizer (C : Set G)).mul_mem
        ((Subgroup.normalizer (C : Set G)).mul_mem hnInvC hx.2)
        ((Subgroup.normalizer (C : Set G)).inv_mem hnInvC)
    constructor
    · simpa [mul_assoc] using hxQ
    · simpa [mul_assoc] using hxCnorm

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_subgroupOf_map_mk'_ne_bot_of_lt
    {N A B : Subgroup G}
    (hB_le_N : B ≤ N)
    (hA_lt_B : A < B)
    (hAnorm : (A.subgroupOf N).Normal) :
    (B.subgroupOf N).map (QuotientGroup.mk' (A.subgroupOf N)) ≠ ⊥ := by
  classical
  haveI : (A.subgroupOf N).Normal := hAnorm
  intro hmap
  have hB_le_A : B ≤ A := by
    intro x hxB
    have hxBN : (⟨x, hB_le_N hxB⟩ : N) ∈ B.subgroupOf N := by
      simpa [Subgroup.mem_subgroupOf] using hxB
    have hxKer :
        (⟨x, hB_le_N hxB⟩ : N) ∈
          (QuotientGroup.mk' (A.subgroupOf N)).ker :=
      (Subgroup.map_eq_bot_iff (H := B.subgroupOf N)
        (f := QuotientGroup.mk' (A.subgroupOf N))).1 hmap hxBN
    simpa [QuotientGroup.ker_mk', Subgroup.mem_subgroupOf] using hxKer
  exact hA_lt_B.ne (le_antisymm hA_lt_B.le hB_le_A)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_le_normalizer_map_subtype_of_normal
    {N : Subgroup G} {L : Subgroup N} (hLnorm : L.Normal) :
    N ≤ Subgroup.normalizer ((L.map N.subtype : Subgroup G) : Set G) := by
  classical
  intro n hn
  let nN : N := ⟨n, hn⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨l, hl, hlx⟩
    exact Subgroup.mem_map.mpr
      ⟨nN * l * nN⁻¹, hLnorm.conj_mem l hl nN, by
        simpa [nN, hlx, mul_assoc]⟩
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨l, hl, hlx⟩
    have hx' : nN⁻¹ * l * (nN⁻¹)⁻¹ ∈ L :=
      hLnorm.conj_mem l hl nN⁻¹
    have hcoerce : ((nN⁻¹ * l * (nN⁻¹)⁻¹ : N) : G) = x := by
      have hlx' : (l : G) = n * x * n⁻¹ := hlx
      calc
        ((nN⁻¹ * l * (nN⁻¹)⁻¹ : N) : G) =
            n⁻¹ * (l : G) * n := by
          simp [nN, mul_assoc]
        _ = n⁻¹ * (n * x * n⁻¹) * n := by
          rw [hlx']
        _ = x := by
          simp [mul_assoc]
    exact Subgroup.mem_map.mpr
      ⟨nN⁻¹ * l * (nN⁻¹)⁻¹, hx', hcoerce⟩


/-- The same normalizer-quotient choice, pulled back to a subgroup `Q₁` of
`N_M(Q₀)`.  This is the formal version of choosing `Q₁/Q₀`. -/
private def CFSG.section15NormalizerQuotientLiftData
    (M Q Q₀ : Subgroup G) : Prop :=
  let N : Subgroup G := M ⊓ Subgroup.normalizer (Q₀ : Set G)
  let QN : Subgroup G := Q ⊓ Subgroup.normalizer (Q₀ : Set G)
  ∃ _hQ₀N : Q₀ ≤ N, ∃ _hQNN : QN ≤ N,
    ∃ _hQ₀Norm : (Q₀.subgroupOf N).Normal,
      ∃ Q₁ : Subgroup N,
        Q₀.subgroupOf N < Q₁ ∧ Q₁ ≤ QN.subgroupOf N ∧ Q₁.Normal ∧
          let Q₁bar : Subgroup (N ⧸ Q₀.subgroupOf N) :=
            Q₁.map (QuotientGroup.mk' (Q₀.subgroupOf N))
          Q₁bar.Normal ∧ Q₁bar ≠ ⊥ ∧
            (∀ R : Subgroup (N ⧸ Q₀.subgroupOf N),
              R.Normal → R ≤ Q₁bar → R = ⊥ ∨ R = Q₁bar)

omit [IsMinCE G] in
/-- Generic normalizer-quotient selection used twice in the source proof:
if `A<Q`, then `N_M(A)/A` has a nontrivial minimal normal subgroup
coming from `N_Q(A)`. -/
private theorem CFSG.section15_exists_normalizer_quotient_lift_of_lt
    {M Q A : Subgroup G}
    (hQnormal : section10NormalIn Q M)
    (hQnil : Group.IsNilpotent Q)
    (hA_lt_Q : A < Q) :
    section15NormalizerQuotientLiftData M Q A := by
  classical
  let N : Subgroup G := M ⊓ Subgroup.normalizer (A : Set G)
  let QN : Subgroup G := Q ⊓ Subgroup.normalizer (A : Set G)
  have hA_M : A ≤ M := hA_lt_Q.le.trans hQnormal.1
  have hAN : A ≤ N := by
    intro x hx
    exact ⟨hA_M hx, Subgroup.le_normalizer hx⟩
  have hQNN : QN ≤ N := by
    intro x hx
    exact ⟨hQnormal.1 hx.1, hx.2⟩
  have hANormData : section10NormalIn A N := by
    simpa [N] using section15_normalIn_inf_normalizer (M := M) (C := A) hA_M
  have hANorm : (A.subgroupOf N).Normal := hANormData.2
  have hQNNormData : section10NormalIn QN N := by
    simpa [QN, N] using
      section15_inf_normalizer_normalIn_inf_normalizer_of_normalIn
        (M := M) (Q := Q) (C := A) hQnormal
  have hQNNorm : (QN.subgroupOf N).Normal := hQNNormData.2
  haveI : (A.subgroupOf N).Normal := hANorm
  haveI : (QN.subgroupOf N).Normal := hQNNorm
  let qN : N →* N ⧸ A.subgroupOf N := QuotientGroup.mk' (A.subgroupOf N)
  let QNbar : Subgroup (N ⧸ A.subgroupOf N) :=
    (QN.subgroupOf N).map qN
  have hA_lt_QN : A < QN := by
    simpa [QN] using
      section15_lt_inf_normalizer_of_lt_of_nilpotent hA_lt_Q hQnil
  have hQNbar_ne : QNbar ≠ ⊥ := by
    simpa [QNbar, qN] using
      section15_subgroupOf_map_mk'_ne_bot_of_lt
        (N := N) (A := A) (B := QN) hQNN hA_lt_QN hANorm
  have hQNbar_norm : QNbar.Normal := by
    simpa [QNbar, qN] using
      Subgroup.Normal.map hQNNorm qN
        (QuotientGroup.mk'_surjective (N := A.subgroupOf N))
  rcases exists_minimal_normal_le (G := N ⧸ A.subgroupOf N)
      QNbar hQNbar_norm hQNbar_ne with
    ⟨Qbar, hQbar_norm, hQbar_le, hQbar_ne, hQbar_min⟩
  let Q₁ : Subgroup N := Qbar.comap qN
  have hQ₁_map : Q₁.map qN = Qbar := by
    simpa [Q₁, qN] using
      (Subgroup.map_comap_eq_self_of_surjective
        (f := qN) (QuotientGroup.mk'_surjective (N := A.subgroupOf N)) Qbar)
  have hA_le_Q₁ : A.subgroupOf N ≤ Q₁ := by
    intro x hx
    change qN x ∈ Qbar
    have hxker : qN x = 1 := by
      simpa [qN, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] using hx
    simp [hxker]
  have hQ₁_ne_A : Q₁ ≠ A.subgroupOf N := by
    intro hEq
    have hQbar_bot : Qbar = ⊥ := by
      rw [← hQ₁_map, hEq]
      exact QuotientGroup.map_mk'_self (N := A.subgroupOf N)
    exact hQbar_ne hQbar_bot
  have hA_lt_Q₁ : A.subgroupOf N < Q₁ :=
    lt_of_le_of_ne hA_le_Q₁ (Ne.symm hQ₁_ne_A)
  have hA_le_QN : A ≤ QN := by
    intro x hx
    exact ⟨hA_lt_Q.le hx, Subgroup.le_normalizer hx⟩
  have hker_le_QN : qN.ker ≤ QN.subgroupOf N := by
    intro x hx
    have hxA : (x : G) ∈ A := by
      simpa [qN, QuotientGroup.ker_mk', Subgroup.mem_subgroupOf] using hx
    simpa [Subgroup.mem_subgroupOf] using hA_le_QN hxA
  have hQ₁_le_QN : Q₁ ≤ QN.subgroupOf N := by
    have hcomap_le :
        Q₁ ≤ ((QN.subgroupOf N).map qN).comap qN := by
      simpa [Q₁, QNbar] using (Subgroup.comap_mono (f := qN) hQbar_le)
    have hcomap_QN :
        ((QN.subgroupOf N).map qN).comap qN = QN.subgroupOf N := by
      exact Subgroup.comap_map_eq_self hker_le_QN
    simpa [hcomap_QN] using hcomap_le
  have hQ₁_norm : Q₁.Normal := hQbar_norm.comap qN
  refine ⟨hAN, hQNN, hANorm, Q₁, hA_lt_Q₁, hQ₁_le_QN,
    hQ₁_norm, ?_, ?_, ?_⟩
  · change (Q₁.map qN).Normal
    simpa [hQ₁_map] using hQbar_norm
  · change Q₁.map qN ≠ ⊥
    simpa [hQ₁_map] using hQbar_ne
  · change ∀ R : Subgroup (N ⧸ A.subgroupOf N),
        R.Normal → R ≤ Q₁.map qN → R = ⊥ ∨ R = Q₁.map qN
    intro R hRnorm hRle
    by_cases hRbot : R = ⊥
    · exact Or.inl hRbot
    · exact Or.inr (by
        have hRle' : R ≤ Qbar := by
          simpa [hQ₁_map] using hRle
        simpa [hQ₁_map] using hQbar_min R hRnorm hRle' hRbot)

/-- Ambient form of the selected `Q₁`: it lies in `Q`, properly contains
`Q₀`, and is normalized by `KD`. -/
private def CFSG.section15AmbientQ1Data
    (M K Q D Q₀ Q₁ : Subgroup G) : Prop :=
  let N : Subgroup G := M ⊓ Subgroup.normalizer (Q₀ : Set G)
  Q₀ < Q₁ ∧ Q₁ ≤ Q ∧ Q₁ ≤ N ∧
    (Q₁.subgroupOf N).Normal ∧
      K ⊔ D ≤ Subgroup.normalizer (Q₁ : Set G)

/-- Ambient form of the selected `Q₁` together with the minimality of
`Q₁/Q₀` in the source normalizer quotient. -/
private def CFSG.section15AmbientQ1MinimalData
    (M K Q D Q₀ Q₁ : Subgroup G) : Prop :=
  let N : Subgroup G := M ⊓ Subgroup.normalizer (Q₀ : Set G)
  ∃ _hQ₀N : Q₀ ≤ N, ∃ _hQ₀Norm : (Q₀.subgroupOf N).Normal,
    section15AmbientQ1Data M K Q D Q₀ Q₁ ∧
        let Q₁bar : Subgroup (N ⧸ Q₀.subgroupOf N) :=
          (Q₁.subgroupOf N).map (QuotientGroup.mk' (Q₀.subgroupOf N))
        Q₁bar.Normal ∧ Q₁bar ≠ ⊥ ∧
          ∀ R : Subgroup (N ⧸ Q₀.subgroupOf N),
            R.Normal → R ≤ Q₁bar → R = ⊥ ∨ R = Q₁bar

/-- Ambient form of the generic normalizer-quotient lift. -/
private def CFSG.section15AmbientNormalizerLiftData
    (M K Q D A B : Subgroup G) : Prop :=
  let N : Subgroup G := M ⊓ Subgroup.normalizer (A : Set G)
  A < B ∧ B ≤ Q ∧ B ≤ N ∧
    (B.subgroupOf N).Normal ∧
      K ⊔ D ≤ Subgroup.normalizer (B : Set G)

omit [IsMinCE G] in
/-- Generic ambient lift: from a `KD`-invariant proper subgroup `A<Q`, choose
`B` with `A<B≤Q` which is normal in `N_M(A)` and remains `KD`-invariant. -/
private theorem CFSG.section15_exists_ambient_lift_in_normalizer_quotient_of_lt
    {M K Q D A : Subgroup G}
    (hQnormal : section10NormalIn Q M)
    (hQnil : Group.IsNilpotent Q)
    (hKleM : K ≤ M)
    (hDleM : D ≤ M)
    (hA_lt_Q : A < Q)
    (hAKD : K ⊔ D ≤ Subgroup.normalizer (A : Set G)) :
    ∃ B : Subgroup G, section15AmbientNormalizerLiftData M K Q D A B := by
  classical
  let N : Subgroup G := M ⊓ Subgroup.normalizer (A : Set G)
  let QN : Subgroup G := Q ⊓ Subgroup.normalizer (A : Set G)
  rcases section15_exists_normalizer_quotient_lift_of_lt
      (M := M) (Q := Q) (A := A) hQnormal hQnil hA_lt_Q with
    ⟨hAN, _hQNN, _hANorm, BN, hA_lt_BN, hBN_le_QN, hBN_norm,
      _hBbar_norm, _hBbar_ne, _hBbar_min⟩
  let B : Subgroup G := BN.map N.subtype
  have hAmap : (A.subgroupOf N).map N.subtype = A := by
    ext x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      simpa [Subgroup.mem_subgroupOf] using hy
    · intro hx
      exact Subgroup.mem_map.mpr ⟨⟨x, hAN hx⟩, by
        simpa [Subgroup.mem_subgroupOf] using hx, rfl⟩
  have hA_le_B : A ≤ B := by
    intro x hx
    rw [← hAmap] at hx
    exact Subgroup.mem_map.mpr
      (by
        rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
        exact ⟨y, hA_lt_BN.le hy, rfl⟩)
  have hB_ne_A : B ≠ A := by
    intro hEq
    have hBN_eq : BN = A.subgroupOf N := by
      have hcomap_B :
          (BN.map N.subtype).comap N.subtype = BN :=
        Subgroup.comap_map_eq_self_of_injective
          (H := BN) (f := N.subtype) N.subtype_injective
      have hcomap_A :
          A.comap N.subtype = A.subgroupOf N := by
        rfl
      calc
        BN = (BN.map N.subtype).comap N.subtype := hcomap_B.symm
        _ = B.comap N.subtype := by rfl
        _ = A.comap N.subtype := by rw [hEq]
        _ = A.subgroupOf N := hcomap_A
    exact hA_lt_BN.ne hBN_eq.symm
  have hA_lt_B : A < B :=
    lt_of_le_of_ne hA_le_B (Ne.symm hB_ne_A)
  have hB_le_Q : B ≤ Q := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    have hyQN : (y : G) ∈ QN := by
      simpa [QN, Subgroup.mem_subgroupOf] using hBN_le_QN hy
    exact hyQN.1
  have hB_le_N : B ≤ N := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hB_subgroupOf_eq : B.subgroupOf N = BN := by
    ext x
    constructor
    · intro hx
      have hxB : (x : G) ∈ B := by
        simpa [Subgroup.mem_subgroupOf] using hx
      rcases Subgroup.mem_map.mp hxB with ⟨y, hy, hyx⟩
      have hy_eq : y = x := Subtype.ext hyx
      simpa [hy_eq] using hy
    · intro hx
      have hxB : (x : G) ∈ B :=
        Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      simpa [Subgroup.mem_subgroupOf] using hxB
  have hB_norm_N : (B.subgroupOf N).Normal := by
    simpa [hB_subgroupOf_eq] using hBN_norm
  have hK_le_N : K ≤ N := by
    intro x hx
    exact ⟨hKleM hx, hAKD ((le_sup_left : K ≤ K ⊔ D) hx)⟩
  have hD_le_N : D ≤ N := by
    intro x hx
    exact ⟨hDleM hx, hAKD ((le_sup_right : D ≤ K ⊔ D) hx)⟩
  have hN_norm_B : N ≤ Subgroup.normalizer (B : Set G) := by
    simpa [B] using
      section15_le_normalizer_map_subtype_of_normal
        (N := N) (L := BN) hBN_norm
  have hKD_norm_B : K ⊔ D ≤ Subgroup.normalizer (B : Set G) :=
    sup_le (hK_le_N.trans hN_norm_B) (hD_le_N.trans hN_norm_B)
  exact ⟨B, hA_lt_B, hB_le_Q, hB_le_N, hB_norm_N, hKD_norm_B⟩

omit [IsMinCE G] in
private theorem CFSG.section15_kstar_inf_le_of_le_or_not_le
    {M K A B : Subgroup G} {q : Nat.Primes}
    (hq : q.val = Nat.card (section14KStar M K))
    (_hA_le_B : A ≤ B)
    (hpos : section14KStar M K ≤ A ∨ ¬ section14KStar M K ≤ B) :
    section14KStar M K ⊓ B ≤ A := by
  classical
  rcases hpos with hKstarA | hKstar_not_B
  · exact inf_le_left.trans hKstarA
  · have hInf_bot : section14KStar M K ⊓ B = ⊥ := by
      by_contra hInf_ne
      exact hKstar_not_B
        (section15_le_of_prime_card_inf_ne_bot
          (A := section14KStar M K) (B := B) hq hInf_ne)
    intro x hx
    have hxbot : x ∈ (⊥ : Subgroup G) := by
      simpa [hInf_bot] using hx
    have hxone : x = 1 := by
      simpa using hxbot
    simp [hxone]

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_kstar_inf_sup_le_of_complement
    {M K Q D B : Subgroup G}
    (hDcomp : section12ComplementIn (section10Msigma M) Q D)
    (hKstarQ : section14KStar M K ≤ Q)
    (hB_le_Q : B ≤ Q)
    (hDnormB : D ≤ Subgroup.normalizer (B : Set G)) :
    section14KStar M K ⊓ (B ⊔ D) ≤ B := by
  classical
  intro x hx
  have hxKstar : x ∈ section14KStar M K := hx.1
  have hxQ : x ∈ Q := hKstarQ hxKstar
  have hxSup : x ∈ (B ⊔ D : Subgroup G) := hx.2
  change x ∈ ((B ⊔ D : Subgroup G) : Set G) at hxSup
  rw [Subgroup.coe_mul_of_right_le_normalizer_left (N := B) (H := D) hDnormB,
    Set.mem_mul] at hxSup
  rcases hxSup with ⟨b, hbB, d, hdD, hbd⟩
  have hbQ : b ∈ Q := hB_le_Q hbB
  have hdQ : d ∈ Q := by
    have hd_eq : d = b⁻¹ * x := by
      calc
        d = (1 : G) * d := by simp
        _ = (b⁻¹ * b) * d := by simp
        _ = b⁻¹ * (b * d) := by simp
        _ = b⁻¹ * x := by rw [hbd]
    rw [hd_eq]
    exact Q.mul_mem (Q.inv_mem hbQ) hxQ
  have hd_one : d = 1 :=
    Subgroup.disjoint_def.mp hDcomp.2.2.2 hdQ hdD
  have hx_eq_b : x = b := by
    calc
      x = b * d := hbd.symm
      _ = b := by simp [hd_one]
  simpa [hx_eq_b] using hbB

omit [IsMinCE G] in
private theorem CFSG.section15_kstar_inf_sup_le_of_position
    {M K Q D A B : Subgroup G} {q : Nat.Primes}
    (hq : q.val = Nat.card (section14KStar M K))
    (hDcomp : section12ComplementIn (section10Msigma M) Q D)
    (hKstarQ : section14KStar M K ≤ Q)
    (hA_le_B : A ≤ B)
    (hB_le_Q : B ≤ Q)
    (hDnormB : D ≤ Subgroup.normalizer (B : Set G))
    (hpos : section14KStar M K ≤ A ∨ ¬ section14KStar M K ≤ B) :
    section14KStar M K ⊓ (B ⊔ D) ≤ A := by
  intro x hx
  have hxB : x ∈ B :=
    section15_kstar_inf_sup_le_of_complement
      (M := M) (K := K) (Q := Q) (D := D) (B := B)
      hDcomp hKstarQ hB_le_Q hDnormB hx
  exact
    section15_kstar_inf_le_of_le_or_not_le
      (M := M) (K := K) (A := A) (B := B) hq hA_le_B hpos
      ⟨hx.1, hxB⟩

omit [IsMinCE G] in
private theorem CFSG.section15_subgroupCentralizerIn_sup_le_of_kstar_position
    {M K Q D A B R : Subgroup G} {q : Nat.Primes}
    (hq : q.val = Nat.card (section14KStar M K))
    (hDcomp : section12ComplementIn (section10Msigma M) Q D)
    (hKstarQ : section14KStar M K ≤ Q)
    (hA_le_B : A ≤ B)
    (hB_le_Q : B ≤ Q)
    (hDnormB : D ≤ Subgroup.normalizer (B : Set G))
    (hcent : subgroupCentralizerIn (section10Msigma M) R = section14KStar M K)
    (hpos : section14KStar M K ≤ A ∨ ¬ section14KStar M K ≤ B) :
    subgroupCentralizerIn (B ⊔ D) R ≤ A := by
  classical
  have hBD_le_msigma : B ⊔ D ≤ section10Msigma M :=
    sup_le (hB_le_Q.trans hDcomp.1) hDcomp.2.1
  intro x hx
  have hxKstar : x ∈ section14KStar M K := by
    have hxcent_msigma :
        x ∈ subgroupCentralizerIn (section10Msigma M) R :=
      ⟨hBD_le_msigma hx.1, hx.2⟩
    simpa [hcent] using hxcent_msigma
  exact
    section15_kstar_inf_sup_le_of_position
      (M := M) (K := K) (Q := Q) (D := D) (A := A) (B := B)
      hq hDcomp hKstarQ hA_le_B hB_le_Q hDnormB hpos
      ⟨hxKstar, hx.1⟩

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_isPiSubgroup_map
    {R S : Type*} [Group R] [Group S] {π : Set Nat.Primes}
    {H : Subgroup R} (hH : IsPiSubgroup (G := R) π H) (f : R →* S) :
    IsPiSubgroup (G := S) π (H.map f) := by
  intro p hp
  exact hH p (hp.trans (Subgroup.card_map_dvd (H := H) f))

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_isPiSubgroup_subgroupOf
    {π : Set Nat.Primes} {H K : Subgroup G}
    (hKπ : IsPiSubgroup (G := G) π K) (hKH : K ≤ H) :
    IsPiSubgroup (G := H) π (K.subgroupOf H) := by
  intro p hp
  have hcard : Nat.card (K.subgroupOf H) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv
  exact hKπ p (by rwa [hcard] at hp)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_isPiSubgroup_sup_of_normal_right
    {R : Type*} [Group R] {π : Set Nat.Primes}
    {H K : Subgroup R} (hH : IsPiSubgroup (G := R) π H)
    (hK : IsPiSubgroup (G := R) π K) [K.Normal] :
    IsPiSubgroup (G := R) π (H ⊔ K) := by
  intro p hpSup
  have hmul : (↑(H ⊔ K) : Set R) = (H : Set R) * (K : Set R) := by
    simpa using (Subgroup.mul_normal H K)
  have hcard_sup_set :
      Nat.card (↑(H ⊔ K) : Set R) = Nat.card ((H : Set R) * (K : Set R) : Set R) :=
    Nat.card_congr (Set.equivOfEq hmul)
  have hcard_sup :
      Nat.card (↥(H ⊔ K)) = Nat.card ((H : Set R) * (K : Set R) : Set R) := by
    simpa using hcard_sup_set
  have hcard_mul :
      Nat.card ((H : Set R) * (K : Set R) : Set R) =
        Nat.card K * Nat.card ((H : Set R).image (↑) : Set (R ⧸ K)) := by
    simpa using
      (Subgroup.card_mul_eq_card_subgroup_mul_card_quotient (s := K) (t := (H : Set R)))
  have hset_image :
      ((H : Set R).image (↑) : Set (R ⧸ K)) =
        (H.map (QuotientGroup.mk' K) : Set (R ⧸ K)) := by
    simp [Subgroup.coe_map]
  have hcard_image_set :
      Nat.card ((H : Set R).image (↑) : Set (R ⧸ K)) =
        Nat.card (H.map (QuotientGroup.mk' K) : Set (R ⧸ K)) :=
    Nat.card_congr (Set.equivOfEq hset_image)
  have hcard_image_subgroup :
      Nat.card ((H : Set R).image (↑) : Set (R ⧸ K)) =
        Nat.card (H.map (QuotientGroup.mk' K)) := by
    exact hcard_image_set
  have hp_mul :
      p.val ∣ Nat.card K * Nat.card ((H : Set R).image (↑) : Set (R ⧸ K)) := by
    rw [← hcard_mul, ← hcard_sup]
    exact hpSup
  rcases p.2.dvd_mul.mp hp_mul with hpK | hpImg
  · exact hK p hpK
  · have hpMap : p.val ∣ Nat.card (H.map (QuotientGroup.mk' K)) := by
      rwa [hcard_image_subgroup] at hpImg
    exact (_root_.CFSG.section12_isPiSubgroup_map hH (QuotientGroup.mk' K)) p hpMap

omit [IsMinCE G] in
private theorem CFSG.section15_nilpotentNormalHallIn_sup
    {M A B : Subgroup G}
    (hA : section15NilpotentNormalHallIn A M)
    (hB : section15NilpotentNormalHallIn B M) :
    section15NilpotentNormalHallIn (A ⊔ B) M := by
  classical
  rcases hA with ⟨hAM, hAnormM, hAnil, hAHall⟩
  rcases hB with ⟨hBM, hBnormM, hBnil, hBHall⟩
  have hSupM : A ⊔ B ≤ M := sup_le hAM hBM
  refine ⟨hSupM, ?_, ?_, ?_⟩
  · have hsub_eq :
        (A ⊔ B).subgroupOf M = A.subgroupOf M ⊔ B.subgroupOf M := by
      exact Subgroup.subgroupOf_sup (A := A) (A' := B) (B := M) hAM hBM
    haveI : (A.subgroupOf M).Normal := hAnormM
    haveI : (B.subgroupOf M).Normal := hBnormM
    rw [hsub_eq]
    exact Subgroup.sup_normal (A.subgroupOf M) (B.subgroupOf M)
  · let F : Subgroup G := section8FittingSubgroup M
    have hAleF : A ≤ F := by
      simpa [F] using
        section12_le_fittingSubgroupOf_of_normalIn_nilpotent hAM hAnormM hAnil
    have hBleF : B ≤ F := by
      simpa [F] using
        section12_le_fittingSubgroupOf_of_normalIn_nilpotent hBM hBnormM hBnil
    have hSupF : A ⊔ B ≤ F := sup_le hAleF hBleF
    have hFnil : Group.IsNilpotent F := by
      simpa [F] using section8FittingSubgroup_isNilpotent M
    haveI : Group.IsNilpotent F := hFnil
    have hSupSubNil :
        Group.IsNilpotent (((A ⊔ B : Subgroup G).subgroupOf F)) := by
      infer_instance
    let e : (A ⊔ B : Subgroup G).subgroupOf F ≃* (A ⊔ B : Subgroup G) :=
      Subgroup.subgroupOfEquivOfLe (H := (A ⊔ B : Subgroup G)) (K := F) hSupF
    exact Group.nilpotent_of_mulEquiv
      (G := (A ⊔ B : Subgroup G).subgroupOf F)
      (G' := (A ⊔ B : Subgroup G)) (_h := hSupSubNil) e
  · have hsub_eq :
        (A ⊔ B).subgroupOf M = A.subgroupOf M ⊔ B.subgroupOf M := by
      exact Subgroup.subgroupOf_sup (A := A) (A' := B) (B := M) hAM hBM
    have hA_le_sup_sub :
        A.subgroupOf M ≤ (A ⊔ B).subgroupOf M := by
      rw [hsub_eq]
      exact le_sup_left
    have hB_le_sup_sub :
        B.subgroupOf M ≤ (A ⊔ B).subgroupOf M := by
      rw [hsub_eq]
      exact le_sup_right
    refine isHallSubgroup_of
      (G := M) (π := subgroupPrimeSet (A ⊔ B))
      (H := (A ⊔ B).subgroupOf M) ?_ ?_
    · intro p hp
      have hcard :
          Nat.card ((A ⊔ B : Subgroup G).subgroupOf M) =
            Nat.card (A ⊔ B : Subgroup G) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe
          (H := (A ⊔ B : Subgroup G)) (K := M) hSupM).toEquiv
      simpa [subgroupPrimeSet, hcard] using hp
    · intro p hpSup hpIndex
      have hAπ :
          IsPiSubgroup (G := M) (subgroupPrimeSet A ∪ subgroupPrimeSet B)
            (A.subgroupOf M) := by
        intro q hq
        exact Or.inl (hAHall.p_in_pi_of_p_dvd_card q hq)
      have hBπ :
          IsPiSubgroup (G := M) (subgroupPrimeSet A ∪ subgroupPrimeSet B)
            (B.subgroupOf M) := by
        intro q hq
        exact Or.inr (hBHall.p_in_pi_of_p_dvd_card q hq)
      haveI : (B.subgroupOf M).Normal := hBnormM
      have hSupπ :
          IsPiSubgroup (G := M) (subgroupPrimeSet A ∪ subgroupPrimeSet B)
            (A.subgroupOf M ⊔ B.subgroupOf M) :=
        section15_isPiSubgroup_sup_of_normal_right hAπ hBπ
      have hpSupCard :
          p.val ∣ Nat.card ((A ⊔ B : Subgroup G).subgroupOf M) := by
        have hcard :
            Nat.card ((A ⊔ B : Subgroup G).subgroupOf M) =
              Nat.card (A ⊔ B : Subgroup G) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe
            (H := (A ⊔ B : Subgroup G)) (K := M) hSupM).toEquiv
        simpa [subgroupPrimeSet, hcard] using hpSup
      have hpUnion : p ∈ subgroupPrimeSet A ∪ subgroupPrimeSet B := by
        exact hSupπ p (by simpa [hsub_eq] using hpSupCard)
      rcases hpUnion with hpA | hpB
      · have hidxA : p.val ∣ (A.subgroupOf M).index :=
          hpIndex.trans (Subgroup.index_dvd_of_le hA_le_sup_sub)
        exact (hAHall.p_in_pi_of_p_dvd_index p hidxA) hpA
      · have hidxB : p.val ∣ (B.subgroupOf M).index :=
          hpIndex.trans (Subgroup.index_dvd_of_le hB_le_sup_sub)
        exact (hBHall.p_in_pi_of_p_dvd_index p hidxB) hpB

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_bot_nilpotentNormalHallIn
    (M : Subgroup G) :
    section15NilpotentNormalHallIn (⊥ : Subgroup G) M := by
  classical
  refine ⟨bot_le, ?_, ?_, ?_⟩
  · have hbot_subgroupOf :
        ((⊥ : Subgroup G).subgroupOf M) = (⊥ : Subgroup M) := by
      ext x
      simp
    rw [hbot_subgroupOf]
    infer_instance
  · infer_instance
  · have hbot_subgroupOf :
        ((⊥ : Subgroup G).subgroupOf M) = (⊥ : Subgroup M) := by
      ext x
      simp
    rw [hbot_subgroupOf]
    refine isHallSubgroup_of
      (G := M) (π := subgroupPrimeSet (⊥ : Subgroup G))
      (H := (⊥ : Subgroup M)) ?_ ?_
    · intro p hp
      exact False.elim (p.property.not_dvd_one (by simpa using hp))
    · intro p hp _hpIndex
      exact False.elim (p.property.not_dvd_one (by simpa [subgroupPrimeSet] using hp))

omit [IsMinCE G] in
public theorem CFSG.section15_exists_MFSubgroup
    (M : Subgroup G) :
    ∃ MF : Subgroup G, section15MFSubgroup M MF := by
  classical
  let S : Set (Subgroup G) := {H | section15NilpotentNormalHallIn H M}
  have hSfinite : S.Finite := Set.toFinite S
  have hSne : S.Nonempty := by
    refine ⟨⊥, ?_⟩
    simpa [S] using section15_bot_nilpotentNormalHallIn (G := G) M
  obtain ⟨MF, hMFmax⟩ :=
    hSfinite.exists_maximalFor (fun H : Subgroup G => Nat.card H) S hSne
  have hMF : section15NilpotentNormalHallIn MF M := by
    simpa [S] using hMFmax.1
  refine ⟨MF, hMF, ?_⟩
  intro H hH
  have hSup : section15NilpotentNormalHallIn (MF ⊔ H) M :=
    section15_nilpotentNormalHallIn_sup hMF hH
  have hcardSup_le : Nat.card (MF ⊔ H : Subgroup G) ≤ Nat.card MF := by
    exact hMFmax.le (j := (MF ⊔ H : Subgroup G)) (by simpa [S] using hSup)
  have hMF_eq_sup : MF = MF ⊔ H :=
    Subgroup.eq_of_le_of_card_ge le_sup_left hcardSup_le
  intro x hx
  have hsup_le_MF : MF ⊔ H ≤ MF := by
    rw [← hMF_eq_sup]
  exact hsup_le_MF ((show H ≤ MF ⊔ H from le_sup_right) hx)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_coprime_card_of_disjoint_piSubgroups
    {π ρ : Set Nat.Primes} {A B : Subgroup G}
    (hπρ : Disjoint π ρ)
    (hAπ : IsPiSubgroup (G := G) π A)
    (hBρ : IsPiSubgroup (G := G) ρ B) :
    Nat.Coprime (Nat.card A) (Nat.card B) := by
  classical
  by_contra hcop
  rcases (Nat.Prime.not_coprime_iff_dvd).1 hcop with
    ⟨p, hpprime, hpA, hpB⟩
  let p' : Nat.Primes := ⟨p, hpprime⟩
  have hpπ : p' ∈ π := hAπ p' hpA
  have hpρ : p' ∈ ρ := hBρ p' hpB
  rw [Set.disjoint_left] at hπρ
  exact hπρ hpπ hpρ

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_coprime_natCard_of_disjoint_piGroups
    {R S : Type*} [Group R] [Finite R] [Group S] [Finite S]
    {π ρ : Set Nat.Primes}
    (hπρ : Disjoint π ρ)
    (hRπ : IsPiSubgroup (G := R) π (⊤ : Subgroup R))
    (hSρ : IsPiSubgroup (G := S) ρ (⊤ : Subgroup S)) :
    Nat.Coprime (Nat.card R) (Nat.card S) := by
  classical
  by_contra hcop
  rcases (Nat.Prime.not_coprime_iff_dvd).1 hcop with
    ⟨p, hpprime, hpR, hpS⟩
  let p' : Nat.Primes := ⟨p, hpprime⟩
  have hpπ : p' ∈ π := hRπ p' (by simpa using hpR)
  have hpρ : p' ∈ ρ := hSρ p' (by simpa using hpS)
  rw [Set.disjoint_left] at hπρ
  exact hπρ hpπ hpρ

omit [IsMinCE G] in
public theorem CFSG.section15_sylowSubgroupIn_isPiSubgroup_singleton
    {M Q : Subgroup G} {q : Nat.Primes}
    (hQ : section12SylowSubgroupIn q Q M) :
    IsPiSubgroup (G := G) ({q} : Set Nat.Primes) Q := by
  classical
  rcases hQ with ⟨P, hP⟩
  have hQp : IsPGroup q.val Q := by
    rw [← hP]
    change IsPGroup q.val ((P : Subgroup M).map M.subtype)
    exact IsPGroup.map (p := q.val) (H := (P : Subgroup M))
      P.isPGroup' M.subtype
  exact section8_isPiSubgroup_singleton_of_isPGroup hQp

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_le_of_subgroupOf_map_mk'_eq_bot
    {S A B : Subgroup G} (_hAS : A ≤ S) (hBS : B ≤ S)
    (hAnorm : (A.subgroupOf S).Normal)
    (hmap :
      letI : (A.subgroupOf S).Normal := hAnorm
      (B.subgroupOf S).map (QuotientGroup.mk' (A.subgroupOf S)) = ⊥) :
    B ≤ A := by
  classical
  letI : (A.subgroupOf S).Normal := hAnorm
  let qS : S →* S ⧸ A.subgroupOf S := QuotientGroup.mk' (A.subgroupOf S)
  intro x hxB
  let xS : S := ⟨x, hBS hxB⟩
  have hxmap : qS xS ∈ (B.subgroupOf S).map qS :=
    Subgroup.mem_map_of_mem qS (by
      simpa [xS, Subgroup.mem_subgroupOf] using hxB)
  have hxbot : qS xS ∈ (⊥ : Subgroup (S ⧸ A.subgroupOf S)) := by
    simpa [qS, hmap] using hxmap
  have hxker : xS ∈ A.subgroupOf S := by
    have hxone : qS xS = 1 := by simpa using hxbot
    simpa [qS, QuotientGroup.eq_one_iff] using hxone
  simpa [xS, Subgroup.mem_subgroupOf] using hxker

omit [IsMinCE G] in
private theorem CFSG.section15_q_subgroup_le_normal_sylow
    {M Q A : Subgroup G} {q : Nat.Primes}
    (hQ : section12SylowSubgroupIn q Q M)
    (hQnormal : section10NormalIn Q M)
    (hAM : A ≤ M) (hAq : IsPGroup q.val A) :
    A ≤ Q := by
  classical
  haveI : Fact q.val.Prime := ⟨q.property⟩
  rcases hQ with ⟨P, hPamb⟩
  have hQsub_eq : Q.subgroupOf M = (P : Subgroup M) := by
    rw [← hPamb]
    simpa [section10AmbientSylowSubgroup] using
      (subgroupOf_map_subtype_eq (K := M) (P : Subgroup M))
  have hQloc_normal : (Q.subgroupOf M).Normal := hQnormal.2
  have hPnormal : (P : Subgroup M).Normal := by
    simpa [hQsub_eq] using hQloc_normal
  haveI : Unique (Sylow q.val M) := Sylow.unique_of_normal P hPnormal
  let Aloc : Subgroup M := A.subgroupOf M
  have hAloc_q : IsPGroup q.val Aloc := by
    exact hAq.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := A) (K := M) hAM).symm
  obtain ⟨T, hAloc_le_T⟩ := IsPGroup.exists_le_sylow (G := M) (p := q.val) hAloc_q
  have hT_eq_P : (T : Subgroup M) = (P : Subgroup M) := by
    have hTP : T = P := Subsingleton.elim T P
    simp [hTP]
  intro x hxA
  let xM : M := ⟨x, hAM hxA⟩
  have hxAloc : xM ∈ Aloc := by
    simpa [Aloc, xM, Subgroup.mem_subgroupOf] using hxA
  have hxP : xM ∈ (P : Subgroup M) := by
    have hxT : xM ∈ (T : Subgroup M) := hAloc_le_T hxAloc
    simpa [hT_eq_P] using hxT
  have hxQsub : xM ∈ Q.subgroupOf M := by
    simpa [hQsub_eq] using hxP
  simpa [xM, Subgroup.mem_subgroupOf] using hxQsub

omit [IsMinCE G] in
private theorem CFSG.section15_complement_to_normal_sylow_isPiSubgroup_compl
    {M Q D : Subgroup G} {q : Nat.Primes}
    (hQ : section12SylowSubgroupIn q Q M)
    (hQnormal : section10NormalIn Q M)
    (hDleM : D ≤ M) (hQDdisj : Disjoint Q D) :
    IsPiSubgroup (G := G) ({q} : Set Nat.Primes)ᶜ D := by
  classical
  intro p hpD
  by_cases hpq : p = q
  · have hpDq : q.val ∣ Nat.card D := by
      simpa [hpq] using hpD
    haveI : Fact q.val.Prime := ⟨q.property⟩
    let P : Sylow q.val D := Classical.choice (Sylow.nonempty (p := q.val) (G := D))
    have hPne : (P : Subgroup D) ≠ ⊥ :=
      Sylow.ne_bot_of_dvd_card (G := D) (p := q.val) P hpDq
    let PG : Subgroup G := (P : Subgroup D).map D.subtype
    have hPG_le_D : PG ≤ D := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
      exact y.property
    have hPG_le_M : PG ≤ M := hPG_le_D.trans hDleM
    have hPG_q : IsPGroup q.val PG :=
      IsPGroup.map (p := q.val) (H := (P : Subgroup D)) P.isPGroup' D.subtype
    have hPG_le_Q : PG ≤ Q :=
      section15_q_subgroup_le_normal_sylow
        (M := M) (Q := Q) (A := PG) (q := q) hQ hQnormal hPG_le_M hPG_q
    have hPG_bot : PG = ⊥ := by
      apply le_bot_iff.mp
      intro x hxPG
      exact Subgroup.disjoint_def.mp hQDdisj (hPG_le_Q hxPG) (hPG_le_D hxPG)
    have hPbot : (P : Subgroup D) = ⊥ := by
      exact (Subgroup.map_eq_bot_iff_of_injective
        (H := (P : Subgroup D)) (f := D.subtype) D.subtype_injective).1 hPG_bot
    exact (hPne hPbot).elim
  · simp [Set.mem_compl_iff, hpq]

omit [IsMinCE G] in
private theorem CFSG.section15_complement_D_isPiSubgroup_q_compl
    {M Q D : Subgroup G} {q : Nat.Primes}
    (hQ : section12SylowSubgroupIn q Q M)
    (hQnormal : section10NormalIn Q M)
    (hDcomp : section12ComplementIn (section10Msigma M) Q D) :
    IsPiSubgroup (G := G) ({q} : Set Nat.Primes)ᶜ D := by
  have hDleM : D ≤ M := hDcomp.2.1.trans (section15_msigma_le (M := M))
  exact
    section15_complement_to_normal_sylow_isPiSubgroup_compl
      (M := M) (Q := Q) (D := D) (q := q)
      hQ hQnormal hDleM hDcomp.2.2.2

private theorem CFSG.section15_hall_kappa_isPiSubgroup_q_compl
    {M K : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hq : q.val = Nat.card (section14KStar M K)) :
    IsPiSubgroup (G := G) ({q} : Set Nat.Primes)ᶜ K := by
  classical
  intro p hpK
  have hpKloc :
      p.val ∣ Nat.card (K.subgroupOf M) := by
    have hcard : Nat.card (K.subgroupOf M) = Nat.card K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK.1).toEquiv
    simpa [hcard] using hpK
  have hpκ : p ∈ section14KappaPrimes M :=
    hK.2.p_in_pi_of_p_dvd_card p hpKloc
  have hp_not_sigma : p ∉ section10SigmaPrimes M :=
    (section15_kappa_subset_primeSet_diff_sigma (G := G) (M := M) hpκ).2
  have hq_sigma : q ∈ section10SigmaPrimes M :=
    section15_prime_mem_sigma_of_kstar_prime_card hM hq
  have hp_ne_q : p ≠ q := by
    intro hpq
    exact hp_not_sigma (by simpa [hpq] using hq_sigma)
  simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hp_ne_q

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_le_centralizer_of_le_centralizer
    {A S : Subgroup G} (hSC : S ≤ Subgroup.centralizer (A : Set G)) :
    A ≤ Subgroup.centralizer (S : Set G) := by
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  exact (Subgroup.mem_centralizer_iff.mp (hSC hs) a ha).symm

omit [IsMinCE G] in
private theorem CFSG.section15_pSubgroup_le_centralizer_piSubgroup_of_nilpotent_overgroup
    {π : Set Nat.Primes} {L P X : Subgroup G} {p : Nat.Primes}
    (hpπ : p ∉ π) (hLnil : Group.IsNilpotent L) (hPL : P ≤ L) (hXL : X ≤ L)
    (hPp : IsPGroup p.val P) (hXπ : IsPiSubgroup (G := G) π X) :
    P ≤ Subgroup.centralizer (X : Set G) := by
  classical
  have hXnil : Group.IsNilpotent X := by
    letI : Group.IsNilpotent L := hLnil
    let Xsub : Subgroup L := X.subgroupOf L
    have hXsub_nil : Group.IsNilpotent Xsub := by infer_instance
    let e : Xsub ≃* X := Subgroup.subgroupOfEquivOfLe (H := X) (K := L) hXL
    letI : Group.IsNilpotent Xsub := hXsub_nil
    exact Group.nilpotent_of_mulEquiv (G := Xsub) (G' := X) e
  letI : Group.IsNilpotent X := hXnil
  have htop_nil : Group.IsNilpotent (⊤ : Subgroup X) := by
    let e : X ≃* (⊤ : Subgroup X) :=
      (Subgroup.topEquiv : (⊤ : Subgroup X) ≃* X).symm
    exact Group.nilpotent_of_mulEquiv (G := X) (G' := (⊤ : Subgroup X)) e
  have htop_le_sup :
      (⊤ : Subgroup X) ≤
        ⨆ q : (Nat.card X).primeFactors.attach, pCore q.1.1 X :=
    normal_nilpotent_le_sup_pCore
      (G := X) (N := (⊤ : Subgroup X)) (hN := inferInstance) htop_nil
  have hsup_le_cent :
      (⨆ q : (Nat.card X).primeFactors.attach, pCore q.1.1 X) ≤
        (Subgroup.centralizer (P : Set G)).comap X.subtype := by
    refine iSup_le ?_
    intro q0
    let q : Nat.Primes := ⟨q0.1.1, Nat.prime_of_mem_primeFactors q0.1.2⟩
    haveI : Fact q.val.Prime := ⟨q.2⟩
    have hqX : q.val ∣ Nat.card X := Nat.dvd_of_mem_primeFactors q0.1.2
    have hqπ : q ∈ π := hXπ q hqX
    have hpq : p ≠ q := by
      intro hpq
      exact hpπ (by simpa [hpq] using hqπ)
    let Q : Subgroup G := (pCore q.val X).map X.subtype
    have hQq : IsPGroup q.val Q := by
      exact IsPGroup.map (p := q.val) (H := pCore q.val X)
        (pCore_isPGroup (G := X) (p := q.val)) X.subtype
    have hQL : Q ≤ L := by
      intro y hy
      rcases Subgroup.mem_map.mp hy with ⟨yX, _hyQ, rfl⟩
      exact hXL yX.2
    have hPcentQ : P ≤ Subgroup.centralizer (Q : Set G) :=
      section10_pSubgroup_le_centralizer_of_nilpotent_overgroup
        (G := G) hpq hLnil hPL hQL hPp hQq
    have hQcentP : Q ≤ Subgroup.centralizer (P : Set G) :=
      section15_le_centralizer_of_le_centralizer (G := G) hPcentQ
    intro x hx
    change ((x : X) : G) ∈ Subgroup.centralizer (P : Set G)
    exact hQcentP (Subgroup.mem_map_of_mem X.subtype (by simpa [q] using hx))
  have hXcentP : X ≤ Subgroup.centralizer (P : Set G) := by
    intro x hx
    let xX : X := ⟨x, hx⟩
    have hxC : xX ∈ (Subgroup.centralizer (P : Set G)).comap X.subtype :=
      hsup_le_cent (htop_le_sup (Subgroup.mem_top xX))
    change x ∈ Subgroup.centralizer (P : Set G) at hxC
    exact hxC
  exact section15_le_centralizer_of_le_centralizer (G := G) hXcentP

omit [IsMinCE G] in
private theorem CFSG.section15_isPiSubgroup_le_centralizer_of_nilpotent_disjoint
    {π ρ : Set Nat.Primes} {L A B : Subgroup G}
    (hπρ : Disjoint π ρ) (hLnil : Group.IsNilpotent L) (hAL : A ≤ L) (hBL : B ≤ L)
    (hAπ : IsPiSubgroup (G := G) π A) (hBρ : IsPiSubgroup (G := G) ρ B) :
    A ≤ Subgroup.centralizer (B : Set G) := by
  classical
  have hAnil : Group.IsNilpotent A := by
    letI : Group.IsNilpotent L := hLnil
    let Asub : Subgroup L := A.subgroupOf L
    have hAsub_nil : Group.IsNilpotent Asub := by infer_instance
    let e : Asub ≃* A := Subgroup.subgroupOfEquivOfLe (H := A) (K := L) hAL
    letI : Group.IsNilpotent Asub := hAsub_nil
    exact Group.nilpotent_of_mulEquiv (G := Asub) (G' := A) e
  letI : Group.IsNilpotent A := hAnil
  have htop_nil : Group.IsNilpotent (⊤ : Subgroup A) := by
    let e : A ≃* (⊤ : Subgroup A) :=
      (Subgroup.topEquiv : (⊤ : Subgroup A) ≃* A).symm
    exact Group.nilpotent_of_mulEquiv (G := A) (G' := (⊤ : Subgroup A)) e
  have htop_le_sup :
      (⊤ : Subgroup A) ≤
        ⨆ q : (Nat.card A).primeFactors.attach, pCore q.1.1 A :=
    normal_nilpotent_le_sup_pCore
      (G := A) (N := (⊤ : Subgroup A)) (hN := inferInstance) htop_nil
  have hsup_le_cent :
      (⨆ q : (Nat.card A).primeFactors.attach, pCore q.1.1 A) ≤
        (Subgroup.centralizer (B : Set G)).comap A.subtype := by
    refine iSup_le ?_
    intro q0
    let q : Nat.Primes := ⟨q0.1.1, Nat.prime_of_mem_primeFactors q0.1.2⟩
    haveI : Fact q.val.Prime := ⟨q.2⟩
    have hqA : q.val ∣ Nat.card A := Nat.dvd_of_mem_primeFactors q0.1.2
    have hqπ : q ∈ π := hAπ q hqA
    have hqρ : q ∉ ρ := by
      rw [Set.disjoint_left] at hπρ
      exact hπρ hqπ
    let Q : Subgroup G := (pCore q.val A).map A.subtype
    have hQq : IsPGroup q.val Q := by
      exact IsPGroup.map (p := q.val) (H := pCore q.val A)
        (pCore_isPGroup (G := A) (p := q.val)) A.subtype
    have hQL : Q ≤ L := by
      intro y hy
      rcases Subgroup.mem_map.mp hy with ⟨yA, _hyQ, rfl⟩
      exact hAL yA.2
    have hQcentB : Q ≤ Subgroup.centralizer (B : Set G) :=
      section15_pSubgroup_le_centralizer_piSubgroup_of_nilpotent_overgroup
        (G := G) hqρ hLnil hQL hBL hQq hBρ
    intro x hx
    change ((x : A) : G) ∈ Subgroup.centralizer (B : Set G)
    exact hQcentB (Subgroup.mem_map_of_mem A.subtype (by simpa [q] using hx))
  intro a ha
  let aA : A := ⟨a, ha⟩
  have haC : aA ∈ (Subgroup.centralizer (B : Set G)).comap A.subtype :=
    hsup_le_cent (htop_le_sup (Subgroup.mem_top aA))
  change a ∈ Subgroup.centralizer (B : Set G) at haC
  exact haC

private theorem CFSG.section15_le_of_nilpotent_sup_quotient
    {M K Q D A B : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hQ : section12SylowSubgroupIn q Q M)
    (hQnormal : section10NormalIn Q M)
    (hD : section15Theorem15_2ComplementData M K Q D)
    (hQ₀_le_A : subgroupCentralizerIn Q D ≤ A)
    (hA_le_B : A ≤ B)
    (hB_le_Q : B ≤ Q)
    (_hB_norm_A : B ≤ Subgroup.normalizer (A : Set G))
    (hD_norm_A : D ≤ Subgroup.normalizer (A : Set G))
    (hD_norm_B : D ≤ Subgroup.normalizer (B : Set G))
    (hAnormS : (A.subgroupOf (B ⊔ D)).Normal)
    (hnil :
      letI : (A.subgroupOf (B ⊔ D)).Normal := hAnormS
      Group.IsNilpotent (↥(B ⊔ D) ⧸ A.subgroupOf (B ⊔ D))) :
    B ≤ A := by
  classical
  let S : Subgroup G := B ⊔ D
  have hAS : A ≤ S := hA_le_B.trans le_sup_left
  have hBS : B ≤ S := le_sup_left
  have hDS : D ≤ S := le_sup_right
  let Asub : Subgroup S := A.subgroupOf S
  let Bsub : Subgroup S := B.subgroupOf S
  let Dsub : Subgroup S := D.subgroupOf S
  letI : Asub.Normal := by
    simpa [Asub, S] using hAnormS
  let qS : S →* S ⧸ Asub := QuotientGroup.mk' Asub
  let Bbar : Subgroup (S ⧸ Asub) := Bsub.map qS
  let Dbar : Subgroup (S ⧸ Asub) := Dsub.map qS
  have hquot_nil : Group.IsNilpotent (S ⧸ Asub) := by
    simpa [S, Asub] using hnil
  have htop_nil : Group.IsNilpotent (⊤ : Subgroup (S ⧸ Asub)) := by
    let e : (S ⧸ Asub) ≃* (⊤ : Subgroup (S ⧸ Asub)) :=
      (Subgroup.topEquiv : (⊤ : Subgroup (S ⧸ Asub)) ≃* (S ⧸ Asub)).symm
    exact Group.nilpotent_of_mulEquiv
      (G := S ⧸ Asub) (G' := (⊤ : Subgroup (S ⧸ Asub)))
      (_h := hquot_nil) e
  have hQπ : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) Q :=
    section15_sylowSubgroupIn_isPiSubgroup_singleton hQ
  have hBπ : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) B :=
    IsPiSubgroup.of_le hB_le_Q hQπ
  have hDπ : IsPiSubgroup (G := G) ({q} : Set Nat.Primes)ᶜ D :=
    section15_complement_D_isPiSubgroup_q_compl hQ hQnormal hD.2.1
  have hBsubπ : IsPiSubgroup (G := S) ({q} : Set Nat.Primes) Bsub := by
    simpa [Bsub] using section15_isPiSubgroup_subgroupOf hBπ hBS
  have hDsubπ : IsPiSubgroup (G := S) ({q} : Set Nat.Primes)ᶜ Dsub := by
    simpa [Dsub] using section15_isPiSubgroup_subgroupOf hDπ hDS
  have hBbarπ : IsPiSubgroup (G := S ⧸ Asub) ({q} : Set Nat.Primes) Bbar := by
    simpa [Bbar, qS] using section15_isPiSubgroup_map hBsubπ qS
  have hDbarπ : IsPiSubgroup (G := S ⧸ Asub) ({q} : Set Nat.Primes)ᶜ Dbar := by
    simpa [Dbar, qS] using section15_isPiSubgroup_map hDsubπ qS
  have hπdisj : Disjoint ({q} : Set Nat.Primes) ({q} : Set Nat.Primes)ᶜ := by
    rw [Set.disjoint_left]
    intro p hp hpcompl
    exact hpcompl hp
  have hBbar_centDbar : Bbar ≤ Subgroup.centralizer (Dbar : Set (S ⧸ Asub)) :=
    section15_isPiSubgroup_le_centralizer_of_nilpotent_disjoint
      (G := S ⧸ Asub) (π := ({q} : Set Nat.Primes))
      (ρ := ({q} : Set Nat.Primes)ᶜ) (L := ⊤)
      (A := Bbar) (B := Dbar) hπdisj htop_nil le_top le_top
      hBbarπ hDbarπ
  have hBbar_eq_cent : subgroupCentralizerIn Bbar Dbar = Bbar := by
    ext y
    constructor
    · intro hy
      exact hy.1
    · intro hy
      exact ⟨hy, hBbar_centDbar hy⟩
  have hDsub_norm_Bsub : Dsub ≤ Subgroup.normalizer (Bsub : Set S) := by
    intro d hd
    have hdNorm : (d : G) ∈ Subgroup.normalizer (B : Set G) := by
      exact hD_norm_B (by simpa [Dsub, Subgroup.mem_subgroupOf] using hd)
    have hdNormSub :
        d ∈ (Subgroup.normalizer (B : Set G)).subgroupOf S := by
      simpa [Subgroup.mem_subgroupOf] using hdNorm
    have hnorm_eq :
        (Subgroup.normalizer (B : Set G)).subgroupOf S =
          Subgroup.normalizer (Bsub : Set S) := by
      simpa [Bsub] using
        (Subgroup.subgroupOf_normalizer_eq (H := B) (N := S) hBS)
    simpa [hnorm_eq] using hdNormSub
  have hDsub_norm_Asub : Dsub ≤ Subgroup.normalizer (Asub : Set S) := by
    intro d hd
    have hdNorm : (d : G) ∈ Subgroup.normalizer (A : Set G) := by
      exact hD_norm_A (by simpa [Dsub, Subgroup.mem_subgroupOf] using hd)
    have hdNormSub :
        d ∈ (Subgroup.normalizer (A : Set G)).subgroupOf S := by
      simpa [Subgroup.mem_subgroupOf] using hdNorm
    have hnorm_eq :
        (Subgroup.normalizer (A : Set G)).subgroupOf S =
          Subgroup.normalizer (Asub : Set S) := by
      simpa [Asub] using
        (Subgroup.subgroupOf_normalizer_eq (H := A) (N := S) hAS)
    simpa [hnorm_eq] using hdNormSub
  have hAinvDsub :
      ∀ r : Dsub, ∀ x ∈ Asub, (r : S) * x * (r : S)⁻¹ ∈ Asub := by
    intro r x hxA
    exact (Subgroup.mem_normalizer_iff.mp (hDsub_norm_Asub r.property) x).1 hxA
  have hBM : B ≤ M := hB_le_Q.trans hQnormal.1
  have hsolvM : Group.IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.2 hM.1)
  have hsolvB : Group.IsSolvable B := by
    let BlocM : Subgroup M := B.subgroupOf M
    have hBlocM_solv : Group.IsSolvable BlocM := by
      letI : Group.IsSolvable M := hsolvM
      infer_instance
    let eB : BlocM ≃* B :=
      Subgroup.subgroupOfEquivOfLe (H := B) (K := M) hBM
    exact Group.isSolvable_of_surjective (f := eB.toMonoidHom) eB.surjective
  have hsolvBsub : Group.IsSolvable Bsub := by
    let eB : Bsub ≃* B :=
      Subgroup.subgroupOfEquivOfLe (H := B) (K := S) hBS
    exact Group.isSolvable_of_surjective (f := eB.symm.toMonoidHom) eB.symm.surjective
  have hcopBD : Nat.Coprime (Nat.card Bsub) (Nat.card Dsub) :=
    section15_coprime_card_of_disjoint_piSubgroups
      (G := S) hπdisj hBsubπ hDsubπ
  have hcent_eq :
      subgroupCentralizerIn Bbar Dbar =
        (subgroupCentralizerIn Bsub Dsub).map qS := by
    simpa [Bbar, Dbar, qS] using
      subgroupCentralizerIn_map_mk'_eq_map_of_solvable_coprime
        (H := Bsub) (R := Dsub) (X := Asub)
        hDsub_norm_Bsub hsolvBsub hcopBD hAinvDsub
  have hcentBD_le_A : subgroupCentralizerIn B D ≤ A := by
    intro x hx
    exact hQ₀_le_A ⟨hB_le_Q hx.1, hx.2⟩
  have hcent_map_bot : (subgroupCentralizerIn Bsub Dsub).map qS = ⊥ := by
    apply bot_unique
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨x, hxC, rfl⟩
    have hlocal_eq :
        subgroupCentralizerIn Bsub Dsub =
          (subgroupCentralizerIn B D).subgroupOf S := by
      simpa [Bsub, Dsub] using
        subgroupCentralizerIn_subgroupOf_eq S B D hDS
    have hxCamb_sub :
        x ∈ (subgroupCentralizerIn B D).subgroupOf S := by
      simpa [hlocal_eq] using hxC
    have hxA : (x : G) ∈ A := hcentBD_le_A (by
      simpa [Subgroup.mem_subgroupOf] using hxCamb_sub)
    have hxAsub : x ∈ Asub := by
      simpa [Asub, Subgroup.mem_subgroupOf] using hxA
    simpa [qS, QuotientGroup.eq_one_iff] using hxAsub
  have hBbar_bot : Bbar = ⊥ := by
    calc
      Bbar = subgroupCentralizerIn Bbar Dbar := hBbar_eq_cent.symm
      _ = (subgroupCentralizerIn Bsub Dsub).map qS := hcent_eq
      _ = ⊥ := hcent_map_bot
  exact
    section15_le_of_subgroupOf_map_mk'_eq_bot
      (S := S) (A := A) (B := B) hAS hBS (by simpa [S] using hAnormS)
      (by simpa [S, Asub, Bsub, qS, Bbar] using hBbar_bot)


/-- Theorem 15.2 L005-S0040, pulled-back form: choose `Q₁` with
`Q₀ < Q₁ ≤ N_Q(Q₀)` and `Q₁/Q₀` minimal normal in `N_M(Q₀)/Q₀`. -/
private theorem CFSG.section15_exists_Q1_lift_in_normalizer_quotient
    {M MF K Q D : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMFne : MF ≠ section10Msigma M)
    (hq : q.val = Nat.card (section14KStar M K))
    (hQ : section12SylowSubgroupIn q Q M)
    (hQnormal : section10NormalIn Q M)
    (hQMF : Q ≤ MF)
    (hD : section15Theorem15_2ComplementData M K Q D) :
    section15NormalizerQuotientLiftData M Q (subgroupCentralizerIn Q D) := by
  let Q₀ : Subgroup G := subgroupCentralizerIn Q D
  simpa [Q₀] using
    section15_exists_normalizer_quotient_lift_of_lt
      (M := M) (Q := Q) (A := Q₀)
      hQnormal (section15_sylowSubgroupIn_nilpotent hQ)
      (section15_Q0_lt_Q hM hMF hK hMFne hq hQ hQnormal hQMF hD)


/-- The same ambient `Q₁` choice, retaining the normalizer-quotient
minimality data needed for the final package. -/
private theorem CFSG.section15_exists_ambient_Q1_minimal_lift_in_normalizer_quotient
    {M MF K Q D : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMFne : MF ≠ section10Msigma M)
    (hq : q.val = Nat.card (section14KStar M K))
    (hQ : section12SylowSubgroupIn q Q M)
    (hQnormal : section10NormalIn Q M)
    (hQMF : Q ≤ MF)
    (hD : section15Theorem15_2ComplementData M K Q D) :
    ∃ Q₁ : Subgroup G,
      section15AmbientQ1MinimalData M K Q D (subgroupCentralizerIn Q D) Q₁ := by
  classical
  let Q₀ : Subgroup G := subgroupCentralizerIn Q D
  let N : Subgroup G := M ⊓ Subgroup.normalizer (Q₀ : Set G)
  let QN : Subgroup G := Q ⊓ Subgroup.normalizer (Q₀ : Set G)
  rcases section15_exists_Q1_lift_in_normalizer_quotient
      hM hMF hK hMFne hq hQ hQnormal hQMF hD with
    ⟨hQ₀N, _hQNN, hQ₀Norm, Q₁N, hQ₀_lt_Q₁N, hQ₁N_le_QN, hQ₁N_norm,
      hQ₁bar_norm, hQ₁bar_ne, hQ₁bar_min⟩
  let Q₁ : Subgroup G := Q₁N.map N.subtype
  have hQ₀map : (Q₀.subgroupOf N).map N.subtype = Q₀ := by
    ext x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      simpa [Subgroup.mem_subgroupOf] using hy
    · intro hx
      exact Subgroup.mem_map.mpr ⟨⟨x, hQ₀N hx⟩, by
        simpa [Subgroup.mem_subgroupOf] using hx, rfl⟩
  have hQ₀_le_Q₁ : Q₀ ≤ Q₁ := by
    intro x hx
    rw [← hQ₀map] at hx
    exact Subgroup.mem_map.mpr
      (by
        rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
        exact ⟨y, hQ₀_lt_Q₁N.le hy, rfl⟩)
  have hQ₁_ne_Q₀ : Q₁ ≠ Q₀ := by
    intro hEq
    have hQ₁N_eq : Q₁N = Q₀.subgroupOf N := by
      have hcomap_Q₁ :
          (Q₁N.map N.subtype).comap N.subtype = Q₁N :=
        Subgroup.comap_map_eq_self_of_injective
          (H := Q₁N) (f := N.subtype) N.subtype_injective
      have hcomap_Q₀ :
          Q₀.comap N.subtype = Q₀.subgroupOf N := by
        rfl
      calc
        Q₁N = (Q₁N.map N.subtype).comap N.subtype := hcomap_Q₁.symm
        _ = Q₁.comap N.subtype := by rfl
        _ = Q₀.comap N.subtype := by rw [hEq]
        _ = Q₀.subgroupOf N := hcomap_Q₀
    exact hQ₀_lt_Q₁N.ne hQ₁N_eq.symm
  have hQ₀_lt_Q₁ : Q₀ < Q₁ :=
    lt_of_le_of_ne hQ₀_le_Q₁ (Ne.symm hQ₁_ne_Q₀)
  have hQ₁_le_Q : Q₁ ≤ Q := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    have hyQN : (y : G) ∈ QN := by
      simpa [QN, Subgroup.mem_subgroupOf] using hQ₁N_le_QN hy
    exact hyQN.1
  have hQ₁_le_N : Q₁ ≤ N := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hQ₁_subgroupOf_eq : Q₁.subgroupOf N = Q₁N := by
    ext x
    constructor
    · intro hx
      have hxQ₁ : (x : G) ∈ Q₁ := by
        simpa [Subgroup.mem_subgroupOf] using hx
      rcases Subgroup.mem_map.mp hxQ₁ with ⟨y, hy, hyx⟩
      have hy_eq : y = x := Subtype.ext hyx
      simpa [hy_eq] using hy
    · intro hx
      have hxQ₁ : (x : G) ∈ Q₁ :=
        Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      simpa [Subgroup.mem_subgroupOf] using hxQ₁
  have hQ₁_norm_N : (Q₁.subgroupOf N).Normal := by
    simpa [hQ₁_subgroupOf_eq] using hQ₁N_norm
  have hDcomp : section12ComplementIn (section10Msigma M) Q D := hD.2.1
  have hD_le_M : D ≤ M := hDcomp.2.1.trans section15_msigma_le
  have hDkinv : K ≤ Subgroup.normalizer (D : Set G) :=
    section15_complement_D_K_invariant
      hM hMF hK hMFne hq hQ hQnormal hQMF hD
  have hQ₀KD :
      K ⊔ D ≤ Subgroup.normalizer (Q₀ : Set G) := by
    simpa [Q₀] using
      section15_Q0_KD_invariant_of_K_invariant_complement
        hM hMF hK hMFne hq hQ hQnormal hQMF hD hDkinv
  have hK_le_N : K ≤ N := by
    intro x hx
    exact ⟨hK.1 hx, hQ₀KD ((le_sup_left : K ≤ K ⊔ D) hx)⟩
  have hD_le_N : D ≤ N := by
    intro x hx
    exact ⟨hD_le_M hx, hQ₀KD ((le_sup_right : D ≤ K ⊔ D) hx)⟩
  have hN_norm_Q₁ : N ≤ Subgroup.normalizer (Q₁ : Set G) := by
    simpa [Q₁] using
      section15_le_normalizer_map_subtype_of_normal
        (N := N) (L := Q₁N) hQ₁N_norm
  have hKD_norm_Q₁ : K ⊔ D ≤ Subgroup.normalizer (Q₁ : Set G) :=
    sup_le (hK_le_N.trans hN_norm_Q₁) (hD_le_N.trans hN_norm_Q₁)
  refine ⟨Q₁, hQ₀N, hQ₀Norm,
    ⟨hQ₀_lt_Q₁, hQ₁_le_Q, hQ₁_le_N, hQ₁_norm_N, hKD_norm_Q₁⟩, ?_, ?_, ?_⟩
  · change ((Q₁.subgroupOf N).map
        (QuotientGroup.mk' (Q₀.subgroupOf N))).Normal
    rw [hQ₁_subgroupOf_eq]
    exact hQ₁bar_norm
  · change (Q₁.subgroupOf N).map
        (QuotientGroup.mk' (Q₀.subgroupOf N)) ≠ ⊥
    rw [hQ₁_subgroupOf_eq]
    exact hQ₁bar_ne
  · intro R hRnorm hRle
    have hRle' := hRle
    rw [hQ₁_subgroupOf_eq] at hRle'
    rcases hQ₁bar_min R hRnorm hRle' with hRbot | hReq
    · exact Or.inl hRbot
    · exact Or.inr (by
        rw [hReq, hQ₁_subgroupOf_eq])

/-- Core regular-action contradiction used twice in L005.  If the source
alternatives put `K*` either below `A` or not below `B`, then the
Theorem 3.7/Proposition 1.5 argument forces `B ≤ A`. -/
private theorem CFSG.section15_le_of_kstar_position
    {M MF K Q D A B : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMFne : MF ≠ section10Msigma M)
    (hq : q.val = Nat.card (section14KStar M K))
    (hQ : section12SylowSubgroupIn q Q M)
    (hQnormal : section10NormalIn Q M)
    (hD : section15Theorem15_2ComplementData M K Q D)
    (hQ₀_le_A : subgroupCentralizerIn Q D ≤ A)
    (hA_lt_B : A < B)
    (hB_le_Q : B ≤ Q)
    (hB_le_N : B ≤ M ⊓ Subgroup.normalizer (A : Set G))
    (hAKD : K ⊔ D ≤ Subgroup.normalizer (A : Set G))
    (hBKD : K ⊔ D ≤ Subgroup.normalizer (B : Set G))
    (hpos : section14KStar M K ≤ A ∨ ¬ section14KStar M K ≤ B) :
    B ≤ A := by
  classical
  have hA_le_B : A ≤ B := hA_lt_B.le
  have hB_norm_A : B ≤ Subgroup.normalizer (A : Set G) := by
    intro x hx
    exact (hB_le_N hx).2
  have hD_norm_A : D ≤ Subgroup.normalizer (A : Set G) :=
    le_sup_right.trans hAKD
  have hD_norm_B : D ≤ Subgroup.normalizer (B : Set G) :=
    le_sup_right.trans hBKD
  have hAS : A ≤ B ⊔ D := hA_le_B.trans le_sup_left
  have hS_norm_A : B ⊔ D ≤ Subgroup.normalizer (A : Set G) :=
    sup_le hB_norm_A hD_norm_A
  have hAnormS : (A.subgroupOf (B ⊔ D)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAS).2 hS_norm_A
  have hnil :
      letI : (A.subgroupOf (B ⊔ D)).Normal := hAnormS
      Group.IsNilpotent (↥(B ⊔ D) ⧸ A.subgroupOf (B ⊔ D)) := by
    classical
    let S : Subgroup G := B ⊔ D
    have hDcomp : section12ComplementIn (section10Msigma M) Q D := hD.2.1
    have hS_le_msigma : S ≤ section10Msigma M := by
      simpa [S] using sup_le (hB_le_Q.trans hDcomp.1) hDcomp.2.1
    have hS_le_M : S ≤ M := hS_le_msigma.trans (section15_msigma_le (M := M))
    have hKstarQ : section14KStar M K ≤ Q :=
      section15_kstar_le_normal_sylow_of_prime_card
        (M := M) (K := K) (Q := Q) (q := q) hq hQ hQnormal
    have hP1prod := section15_MF_ne_msigma_implies_P1 hM hMF hK hMFne
    have hP1 : M ∈ section14MFamilyP1 G := hP1prod.1
    have hprime : section14ActsInPrimeManner K (section10Msigma M) :=
      section15_prime_action_of_MF_ne_msigma hM hMF hK hMFne
    have hKne : K ≠ ⊥ := section15_hall_kappa_ne_bot hP1.1 hK
    haveI : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot (H := K)).2 hKne
    obtain ⟨x, hxK, hxne⟩ := Subgroup.exists_ne_one_of_nontrivial K
    rcases section15_exists_primeOrder_zpowers_in (B := K) hxK hxne with
      ⟨r, z, _hzpowx, hzK, _hzne, hRprimeInK⟩
    let R : Subgroup G := Subgroup.zpowers z
    have hR_le_K : R ≤ K := Subgroup.zpowers_le.2 hzK
    have hR_le_M : R ≤ M := hR_le_K.trans hK.1
    have hR_norm_A : R ≤ Subgroup.normalizer (A : Set G) :=
      hR_le_K.trans (le_sup_left.trans hAKD)
    have hR_norm_B : R ≤ Subgroup.normalizer (B : Set G) :=
      hR_le_K.trans (le_sup_left.trans hBKD)
    have hR_norm_D : R ≤ Subgroup.normalizer (D : Set G) :=
      hR_le_K.trans hD.2.2.2
    have hR_norm_S : R ≤ Subgroup.normalizer (S : Set G) := by
      simpa [S] using
        section15_le_normalizer_sup_of_le_normalizers
          (N := R) (A := B) (B := D) hR_norm_B hR_norm_D
    let H : Subgroup G := S ⊔ R
    have hS_le_H : S ≤ H := by
      simp [H]
    have hR_le_H : R ≤ H := by
      simp [H]
    have hA_le_S : A ≤ S := by
      simpa [S] using hAS
    have hA_le_H : A ≤ H := hA_le_S.trans hS_le_H
    have hH_norm_A : H ≤ Subgroup.normalizer (A : Set G) := by
      simpa [H, S] using sup_le hS_norm_A hR_norm_A
    have hAnormH : (A.subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hA_le_H).2 hH_norm_A
    let AsubH : Subgroup H := A.subgroupOf H
    let Ssub : Subgroup H := S.subgroupOf H
    let Rsub : Subgroup H := R.subgroupOf H
    have hH_norm_S : H ≤ Subgroup.normalizer (S : Set G) := by
      simpa [H] using sup_le Subgroup.le_normalizer hR_norm_S
    have hSnormalH : Ssub.Normal := by
      simpa [Ssub] using
        (Subgroup.normal_subgroupOf_iff_le_normalizer hS_le_H).2 hH_norm_S
    haveI : AsubH.Normal := by
      simpa [AsubH] using hAnormH
    haveI : Ssub.Normal := hSnormalH
    let qH : H →* H ⧸ AsubH := QuotientGroup.mk' AsubH
    let Sbar : Subgroup (H ⧸ AsubH) := Ssub.map qH
    let Rbar : Subgroup (H ⧸ AsubH) := Rsub.map qH
    let T : Subgroup (H ⧸ AsubH) := Sbar ⊔ Rbar
    have hS_K_disj : Disjoint (section10MsigmaSubgroup M) (K.subgroupOf M) := by
      simpa using
        section15_msigmaSubgroup_disjoint_kappaHall_of_MF_ne hM hMF hK hMFne
    have hS_R_disj : Disjoint S R := by
      rw [Subgroup.disjoint_def]
      intro y hyS hyR
      let yM : M := ⟨y, hS_le_M hyS⟩
      have hySigmaSub : yM ∈ section10MsigmaSubgroup M := by
        have hySigma : y ∈ section10Msigma M := hS_le_msigma hyS
        rw [← section15_msigma_subgroupOf_eq]
        change (yM : G) ∈ section10Msigma M
        exact hySigma
      have hyKsub : yM ∈ K.subgroupOf M := by
        have hyK : y ∈ K := hR_le_K hyR
        simpa [yM, Subgroup.mem_subgroupOf] using hyK
      have hybotM : yM ∈ (⊥ : Subgroup M) :=
        Subgroup.disjoint_def.mp hS_K_disj hySigmaSub hyKsub
      have hyone : y = 1 := by
        have hyMone : yM = 1 := by
          simpa using hybotM
        exact congrArg Subtype.val hyMone
      simp [hyone]
    have hSsub_Rsub_disj : Disjoint Ssub Rsub := by
      rw [Subgroup.disjoint_def]
      intro y hyS hyR
      have hySG : ((y : H) : G) ∈ S := by
        simpa [Ssub, Subgroup.mem_subgroupOf] using hyS
      have hyRG : ((y : H) : G) ∈ R := by
        simpa [Rsub, Subgroup.mem_subgroupOf] using hyR
      have hyoneG : ((y : H) : G) = 1 := by
        have hybot : ((y : H) : G) ∈ (⊥ : Subgroup G) :=
          Subgroup.disjoint_def.mp hS_R_disj hySG hyRG
        simpa using hybot
      have hyoneH : y = 1 := by
        apply Subtype.ext
        exact hyoneG
      simp [hyoneH]
    have hAsubH_le_Ssub : AsubH ≤ Ssub := by
      intro y hyA
      have hyAG : ((y : H) : G) ∈ A := by
        simpa [AsubH, Subgroup.mem_subgroupOf] using hyA
      have hyS : ((y : H) : G) ∈ S := hA_le_S hyAG
      simpa [Ssub, Subgroup.mem_subgroupOf] using hyS
    have hSbar_normal : Sbar.Normal := by
      exact Subgroup.Normal.map
        (H := Ssub) (inferInstance : Ssub.Normal) qH
        (QuotientGroup.mk'_surjective AsubH)
    haveI : Sbar.Normal := hSbar_normal
    have hSbar_Rbar_disj : Disjoint Sbar Rbar := by
      simpa [Sbar, Rbar, qH] using
        section15_disjoint_map_mk'_of_le_left_and_disjoint
          (G := H) (H := Ssub) (R := Rsub) (N := AsubH)
          hAsubH_le_Ssub hSsub_Rsub_disj
    have hSbarT_normal : (Sbar.subgroupOf T).Normal := by
      exact Subgroup.Normal.subgroupOf (H := Sbar) (K := T) hSbar_normal
    have hSbar_Rbar_comp :
        (Sbar.subgroupOf T).IsComplement' (Rbar.subgroupOf T) := by
      simpa [T] using
        isComplement'_subgroupOf_sup_of_disjoint Sbar Rbar hSbar_Rbar_disj
    have hRprime_card : Nat.Prime (Nat.card R) := by
      rcases (by simpa [R, section10PrimeOrderSubgroupsIn] using hRprimeInK) with
        ⟨_hRK, hRcard⟩
      simpa [R, hRcard] using r.property
    have hRsub_card : Nat.card Rsub = Nat.card R := by
      exact Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := R) (K := H) hR_le_H).toEquiv
    have hRbar_card : Nat.card Rbar = Nat.card Rsub := by
      simpa [Rbar, qH] using
        section15_natCard_map_mk'_eq_of_le_left_and_disjoint
          (G := H) (H := Ssub) (R := Rsub) (N := AsubH)
          hAsubH_le_Ssub hSsub_Rsub_disj
    have hRbar_prime : Nat.Prime (Nat.card Rbar) := by
      simpa [hRbar_card, hRsub_card] using hRprime_card
    have hRbarT_prime : Nat.Prime (Nat.card (Rbar.subgroupOf T)) := by
      have hcard : Nat.card (Rbar.subgroupOf T) = Nat.card Rbar := by
        exact Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe (H := Rbar) (K := T) le_sup_right).toEquiv
      simpa [hcard] using hRbar_prime
    have hsolvM : Group.IsSolvable M :=
      IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.2 hM.1)
    have hH_le_M : H ≤ M := by
      simpa [H] using sup_le hS_le_M hR_le_M
    have hsolvH : Group.IsSolvable H := by
      let Hloc : Subgroup M := H.subgroupOf M
      have hHloc_solv : Group.IsSolvable Hloc := by
        letI : Group.IsSolvable M := hsolvM
        infer_instance
      let eH : Hloc ≃* H :=
        Subgroup.subgroupOfEquivOfLe (H := H) (K := M) hH_le_M
      exact Group.isSolvable_of_surjective (f := eH.toMonoidHom) eH.surjective
    have hsolvSsub : Group.IsSolvable Ssub := by
      letI : Group.IsSolvable H := hsolvH
      infer_instance
    have hsolvQ : Group.IsSolvable (H ⧸ AsubH) := by
      letI : Group.IsSolvable H := hsolvH
      infer_instance
    have hsolvT : Group.IsSolvable T := by
      letI : Group.IsSolvable (H ⧸ AsubH) := hsolvQ
      infer_instance
    have hoddM : Odd (Nat.card M) :=
      odd_of_card_dvd IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card M)
    have hoddH : Odd (Nat.card H) :=
      odd_of_card_dvd hoddM (Subgroup.card_dvd_of_le hH_le_M)
    have hoddQ : Odd (Nat.card (H ⧸ AsubH)) :=
      odd_of_card_dvd hoddH (Subgroup.card_quotient_dvd_card (s := AsubH))
    have hoddT : Odd (Nat.card T) :=
      odd_of_card_dvd hoddQ (Subgroup.card_subgroup_dvd_card T)
    let Sloc : Subgroup M := S.subgroupOf M
    let Rloc : Subgroup M := R.subgroupOf M
    let Kloc : Subgroup M := K.subgroupOf M
    have hSloc_le_sigma : Sloc ≤ section10MsigmaSubgroup M := by
      intro y hy
      have hyS : (y : G) ∈ S := by
        simpa [Sloc, Subgroup.mem_subgroupOf] using hy
      have hySigma : (y : G) ∈ section10Msigma M := hS_le_msigma hyS
      rw [← section15_msigma_subgroupOf_eq]
      change (y : G) ∈ section10Msigma M
      exact hySigma
    have hRloc_le_Kloc : Rloc ≤ Kloc := by
      intro y hy
      have hyR : (y : G) ∈ R := by
        simpa [Rloc, Subgroup.mem_subgroupOf] using hy
      have hyK : (y : G) ∈ K := hR_le_K hyR
      simpa [Kloc, Subgroup.mem_subgroupOf] using hyK
    have hHallS : IsHallSubgroup (section10SigmaPrimes M) (section10MsigmaSubgroup M) := by
      simpa using (theorem_10_2_b (G := G) hM).2
    have hHallKloc : IsHallSubgroup (section14KappaPrimes M) Kloc := by
      simpa [Kloc] using hK.2
    have hπdisj :
        Disjoint (section10SigmaPrimes M) (section14KappaPrimes M) := by
      rw [hP1.2]
      rw [Set.disjoint_left]
      intro p hpσ hpκ
      exact hpκ.2 hpσ
    have hcop_sigma_Kloc :
        Nat.Coprime (Nat.card (section10MsigmaSubgroup M)) (Nat.card Kloc) :=
      section15_coprime_card_of_hall_disjoint_primes hHallS hHallKloc hπdisj
    have hcop_Sloc_Kloc : Nat.Coprime (Nat.card Sloc) (Nat.card Kloc) :=
      hcop_sigma_Kloc.of_dvd_left (Subgroup.card_dvd_of_le hSloc_le_sigma)
    have hcop_Sloc_Rloc : Nat.Coprime (Nat.card Sloc) (Nat.card Rloc) :=
      hcop_Sloc_Kloc.of_dvd_right (Subgroup.card_dvd_of_le hRloc_le_Kloc)
    have hcardSloc : Nat.card Sloc = Nat.card S := by
      exact Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := S) (K := M) hS_le_M).toEquiv
    have hcardRloc : Nat.card Rloc = Nat.card R := by
      exact Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := R) (K := M) hR_le_M).toEquiv
    have hcardSsub : Nat.card Ssub = Nat.card S := by
      exact Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := S) (K := H) hS_le_H).toEquiv
    have hcardRsub : Nat.card Rsub = Nat.card R := hRsub_card
    have hcop_Ssub_Rsub : Nat.Coprime (Nat.card Ssub) (Nat.card Rsub) := by
      rw [hcardSsub, hcardRsub, ← hcardSloc, ← hcardRloc]
      exact hcop_Sloc_Rloc
    have hRsub_norm_Ssub : Rsub ≤ Subgroup.normalizer (Ssub : Set H) :=
      le_top.trans (Subgroup.le_normalizer_of_normal (H := Ssub))
    have hAsub_inv :
        ∀ r : Rsub, ∀ x ∈ AsubH, (r : H) * x * (r : H)⁻¹ ∈ AsubH := by
      intro r x hx
      exact (inferInstance : AsubH.Normal).conj_mem x hx r
    have hRprime_section : R ∈ section12PrimeOrderSubgroups K :=
      section15_primeOrderSubgroups_of_primeOrderSubgroupsIn (A := K) hRprimeInK
    have hcent_msigma_eq :
        subgroupCentralizerIn (section10Msigma M) R = section14KStar M K :=
      section15_centralizer_eq_kstar_of_prime_manner
        (M := M) (K := K) (X := R) hprime hRprime_section
    have hcentS_le_A : subgroupCentralizerIn S R ≤ A := by
      simpa [S] using
        section15_subgroupCentralizerIn_sup_le_of_kstar_position
          (M := M) (K := K) (Q := Q) (D := D) (A := A) (B := B)
          (R := R) (q := q)
          hq hDcomp hKstarQ hA_le_B hB_le_Q hD_norm_B
          hcent_msigma_eq hpos
    have hcent_local_le_A : subgroupCentralizerIn Ssub Rsub ≤ AsubH := by
      intro y hy
      have hlocal_eq :
          subgroupCentralizerIn Ssub Rsub =
            (subgroupCentralizerIn S R).subgroupOf H := by
        simpa [Ssub, Rsub] using
          subgroupCentralizerIn_subgroupOf_eq H S R hR_le_H
      have hyamb_sub : y ∈ (subgroupCentralizerIn S R).subgroupOf H := by
        simpa [hlocal_eq] using hy
      have hyA : ((y : H) : G) ∈ A := by
        exact hcentS_le_A (by
          simpa [Subgroup.mem_subgroupOf] using hyamb_sub)
      simpa [AsubH, Subgroup.mem_subgroupOf] using hyA
    have hcent_local_map_bot :
        (subgroupCentralizerIn Ssub Rsub).map qH = ⊥ := by
      apply bot_unique
      intro y hy
      rcases Subgroup.mem_map.mp hy with ⟨x, hxC, rfl⟩
      have hxA : x ∈ AsubH := hcent_local_le_A hxC
      simpa [qH, QuotientGroup.eq_one_iff] using hxA
    have hcent_quot :
        subgroupCentralizerIn Sbar Rbar = ⊥ := by
      have hmap :=
        subgroupCentralizerIn_map_mk'_eq_map_of_solvable_coprime
          (H := Ssub) (R := Rsub) (X := AsubH)
          hRsub_norm_Ssub hsolvSsub hcop_Ssub_Rsub hAsub_inv
      calc
        subgroupCentralizerIn Sbar Rbar =
            (subgroupCentralizerIn Ssub Rsub).map qH := by
              simpa [Sbar, Rbar, qH] using hmap
        _ = ⊥ := hcent_local_map_bot
    have hfixT :
        subgroupCentralizerIn (Sbar.subgroupOf T) (Rbar.subgroupOf T) = ⊥ := by
      rw [subgroupCentralizerIn_subgroupOf_eq T Sbar Rbar le_sup_right]
      simp [hcent_quot]
    have hnilSbarT : Group.IsNilpotent (Sbar.subgroupOf T) :=
      theorem_3_7 (G := T) (Sbar.subgroupOf T) (Rbar.subgroupOf T)
        hsolvT hoddT hSbarT_normal hSbar_Rbar_comp hRbarT_prime hfixT
    have hnilSbar : Group.IsNilpotent Sbar := by
      let e : Sbar.subgroupOf T ≃* Sbar :=
        Subgroup.subgroupOfEquivOfLe (H := Sbar) (K := T) le_sup_left
      exact Group.nilpotent_of_mulEquiv
        (G := Sbar.subgroupOf T) (G' := Sbar) (_h := hnilSbarT) e
    let AsubS : Subgroup S := A.subgroupOf S
    have hAnormSlocal : AsubS.Normal := by
      simpa [AsubS, S] using hAnormS
    haveI : AsubS.Normal := hAnormSlocal
    have hAsubHsub_normal : (AsubH.subgroupOf Ssub).Normal := by
      exact Subgroup.Normal.subgroupOf (H := AsubH) (K := Ssub)
        (show AsubH.Normal from inferInstance)
    haveI : (AsubH.subgroupOf Ssub).Normal := hAsubHsub_normal
    let eS : S ≃* Ssub :=
      (Subgroup.subgroupOfEquivOfLe (H := S) (K := H) hS_le_H).symm
    have hAsub_map : AsubS.map eS.toMonoidHom = AsubH.subgroupOf Ssub := by
      ext y
      constructor
      · rintro ⟨a, haA, rfl⟩
        have haG : (a : G) ∈ A := by
          simpa [AsubS, Subgroup.mem_subgroupOf] using haA
        simpa [eS, AsubH, Ssub, Subgroup.mem_subgroupOf] using haG
      · intro hy
        let a : S := ⟨((y : H) : G), by
          exact Subgroup.mem_subgroupOf.mp y.property⟩
        have haA : a ∈ AsubS := by
          have hyA : ((y : H) : G) ∈ A := by
            simpa [AsubH, Subgroup.mem_subgroupOf] using hy
          simpa [a, AsubS, Subgroup.mem_subgroupOf] using hyA
        refine ⟨a, haA, ?_⟩
        ext
        rfl
    let eQuot : S ⧸ AsubS ≃* Ssub ⧸ AsubH.subgroupOf Ssub :=
      QuotientGroup.congr AsubS (AsubH.subgroupOf Ssub) eS hAsub_map
    let eRange : Ssub ⧸ AsubH.subgroupOf Ssub ≃* Sbar :=
      quotientSubgroupRangeEquiv Ssub AsubH
    let e : S ⧸ AsubS ≃* Sbar := eQuot.trans eRange
    have hnilSquot : Group.IsNilpotent (S ⧸ AsubS) :=
      Group.nilpotent_of_mulEquiv (G := Sbar) (G' := S ⧸ AsubS)
        (_h := hnilSbar) e.symm
    simpa [S, AsubS] using hnilSquot
  exact
    section15_le_of_nilpotent_sup_quotient
      (M := M) (K := K) (Q := Q) (D := D) (A := A) (B := B) (q := q)
      hM hQ hQnormal hD hQ₀_le_A hA_le_B hB_le_Q hB_norm_A
      hD_norm_A hD_norm_B hAnormS hnil

omit [Finite G] [IsMinCE G] in
/-- Once the selected normalizer-quotient subgroup is all of `Q`, its
minimality data packages as the desired `M/Q₀` minimal-normal quotient. -/
private theorem CFSG.section15_quotient_minimal_normal_of_Q1_eq_Q
    {M K Q D Q₀ Q₁ : Subgroup G}
    (hM_norm_Q₀ : M ≤ Subgroup.normalizer (Q₀ : Set G))
    (hQ₁min : section15AmbientQ1MinimalData M K Q D Q₀ Q₁)
    (hQ₁eq : Q₁ = Q) :
    section15QuotientMinimalNormal M Q Q₀ := by
  classical
  let N : Subgroup G := M ⊓ Subgroup.normalizer (Q₀ : Set G)
  rcases hQ₁min with
    ⟨hQ₀N, hQ₀NormN, hQ₁data, hQ₁bar_norm, hQ₁bar_ne, hQ₁bar_min⟩
  rcases hQ₁data with
    ⟨hQ₀_lt_Q₁, _hQ₁_le_Q, hQ₁_le_N, _hQ₁_norm_N, _hQ₁KD⟩
  have hN_eq_M : N = M := by
    apply le_antisymm
    · exact inf_le_left
    · intro x hxM
      exact ⟨hxM, hM_norm_Q₀ hxM⟩
  have hQ₀M : Q₀ ≤ M := by
    intro x hx
    exact (hQ₀N hx).1
  have hQN : Q ≤ N := by
    intro x hxQ
    have hxQ₁ : x ∈ Q₁ := by
      simpa [hQ₁eq] using hxQ
    exact hQ₁_le_N hxQ₁
  have hQM : Q ≤ M := by
    intro x hxQ
    exact (hQN hxQ).1
  have hQ₀Q : Q₀ ≤ Q := by
    intro x hx
    have hxQ₁ : x ∈ Q₁ := hQ₀_lt_Q₁.le hx
    simpa [hQ₁eq] using hxQ₁
  have hQ₀NormM : (Q₀.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ₀M).2 hM_norm_Q₀
  letI : (Q₀.subgroupOf N).Normal := hQ₀NormN
  letI : (Q₀.subgroupOf M).Normal := hQ₀NormM
  let QbarN : Subgroup (N ⧸ Q₀.subgroupOf N) :=
    (Q.subgroupOf N).map (QuotientGroup.mk' (Q₀.subgroupOf N))
  let QbarM : Subgroup (M ⧸ Q₀.subgroupOf M) :=
    (Q.subgroupOf M).map (QuotientGroup.mk' (Q₀.subgroupOf M))
  have hQbarN_norm : QbarN.Normal := by
    simpa [QbarN, hQ₁eq] using hQ₁bar_norm
  have hQbarN_ne : QbarN ≠ ⊥ := by
    simpa [QbarN, hQ₁eq] using hQ₁bar_ne
  have hQbarN_min :
      ∀ R : Subgroup (N ⧸ Q₀.subgroupOf N),
        R.Normal → R ≤ QbarN → R = ⊥ ∨ R = QbarN := by
    intro R hRnorm hRle
    have hRle' :
        R ≤ (Q₁.subgroupOf N).map (QuotientGroup.mk' (Q₀.subgroupOf N)) := by
      simpa [QbarN, hQ₁eq] using hRle
    rcases hQ₁bar_min R hRnorm hRle' with hRbot | hReq
    · exact Or.inl hRbot
    · exact Or.inr (by
        simpa [QbarN, hQ₁eq] using hReq)
  let eNM : N ≃* M := MulEquiv.subgroupCongr hN_eq_M
  have hQ₀_map :
      (Q₀.subgroupOf N).map eNM.toMonoidHom = Q₀.subgroupOf M := by
    ext x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      simpa [eNM, Subgroup.mem_subgroupOf] using hy
    · intro hx
      let y : N := ⟨x, hQ₀N (by
        simpa [Subgroup.mem_subgroupOf] using hx)⟩
      refine Subgroup.mem_map.mpr ⟨y, ?_, ?_⟩
      · simpa [y, Subgroup.mem_subgroupOf] using hx
      · ext
        simp [eNM, y]
  let eQ : N ⧸ Q₀.subgroupOf N ≃* M ⧸ Q₀.subgroupOf M :=
    QuotientGroup.congr (Q₀.subgroupOf N) (Q₀.subgroupOf M) eNM hQ₀_map
  have hQbar_map : QbarN.map eQ.toMonoidHom = QbarM := by
    ext z
    constructor
    · intro hz
      rcases Subgroup.mem_map.mp hz with ⟨y, hy, rfl⟩
      rcases Subgroup.mem_map.mp hy with ⟨x, hxQ, rfl⟩
      refine Subgroup.mem_map.mpr ⟨eNM x, ?_, ?_⟩
      · simpa [eNM, Subgroup.mem_subgroupOf] using hxQ
      · change
          (QuotientGroup.mk' (Q₀.subgroupOf M)) (eNM x) =
            (QuotientGroup.congr (Q₀.subgroupOf N) (Q₀.subgroupOf M)
              eNM hQ₀_map) (QuotientGroup.mk' (Q₀.subgroupOf N) x)
        exact (QuotientGroup.congr_mk' (Q₀.subgroupOf N) (Q₀.subgroupOf M)
          eNM hQ₀_map x).symm
    · intro hz
      rcases Subgroup.mem_map.mp hz with ⟨x, hxQ, rfl⟩
      let xN : N := ⟨x, hQN (by
        simpa [Subgroup.mem_subgroupOf] using hxQ)⟩
      refine Subgroup.mem_map.mpr
        ⟨QuotientGroup.mk' (Q₀.subgroupOf N) xN, ?_, ?_⟩
      · exact Subgroup.mem_map_of_mem (QuotientGroup.mk' (Q₀.subgroupOf N))
          (by simpa [xN, Subgroup.mem_subgroupOf] using hxQ)
      · have hxNM : eNM xN = x := by
          ext
          simp [eNM, xN]
        change
          (QuotientGroup.congr (Q₀.subgroupOf N) (Q₀.subgroupOf M)
            eNM hQ₀_map) (QuotientGroup.mk' (Q₀.subgroupOf N) xN) =
            (QuotientGroup.mk' (Q₀.subgroupOf M)) x
        simpa only [hxNM] using
          (QuotientGroup.congr_mk' (Q₀.subgroupOf N) (Q₀.subgroupOf M)
            eNM hQ₀_map xN)
  refine ⟨hQ₀M, hQM, hQ₀Q, hQ₀NormM, ?_, ?_, ?_⟩
  · change (Q.subgroupOf M).map
        (QuotientGroup.mk' (Q₀.subgroupOf M)) ≠ ⊥
    intro hbot
    have hmap_bot : QbarN.map eQ.toMonoidHom = ⊥ := by
      simpa [QbarM, hbot] using hQbar_map
    have hQbarN_bot : QbarN = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective
        (H := QbarN) (f := eQ.toMonoidHom) eQ.injective).1 hmap_bot
    exact hQbarN_ne hQbarN_bot
  · change ((Q.subgroupOf M).map
        (QuotientGroup.mk' (Q₀.subgroupOf M))).Normal
    have hnorm : (QbarN.map eQ.toMonoidHom).Normal :=
      (Subgroup.Normal.map hQbarN_norm eQ.toMonoidHom eQ.surjective)
    rw [hQbar_map] at hnorm
    simpa [QbarM] using hnorm
  · change ∀ R : Subgroup (M ⧸ Q₀.subgroupOf M),
        R.Normal →
          R ≤ (Q.subgroupOf M).map (QuotientGroup.mk' (Q₀.subgroupOf M)) →
            R = ⊥ ∨ R = (Q.subgroupOf M).map
              (QuotientGroup.mk' (Q₀.subgroupOf M))
    intro R hRnorm hRle
    let R' : Subgroup (N ⧸ Q₀.subgroupOf N) := R.map eQ.symm.toMonoidHom
    have hR'norm : R'.Normal := by
      simpa [R'] using
        (Subgroup.Normal.map hRnorm eQ.symm.toMonoidHom eQ.symm.surjective)
    have hQbar_map_symm : QbarM.map eQ.symm.toMonoidHom = QbarN := by
      ext x
      constructor
      · intro hx
        rcases Subgroup.mem_map.mp hx with ⟨y, hy, hyx⟩
        have hy' : y ∈ QbarN.map eQ.toMonoidHom := by
          rw [hQbar_map]
          exact hy
        rcases Subgroup.mem_map.mp hy' with ⟨z, hz, hzy⟩
        have hxz : x = z := by
          rw [← hyx, ← hzy]
          simp
        simpa [hxz] using hz
      · intro hx
        refine Subgroup.mem_map.mpr ⟨eQ x, ?_, ?_⟩
        · rw [← hQbar_map]
          exact Subgroup.mem_map_of_mem eQ.toMonoidHom hx
        · simp
    have hR'le : R' ≤ QbarN := by
      intro x hx
      have hx' : x ∈ QbarM.map eQ.symm.toMonoidHom :=
        Subgroup.map_mono (by
          simpa [QbarM] using hRle) hx
      rw [hQbar_map_symm] at hx'
      exact hx'
    rcases hQbarN_min R' hR'norm hR'le with hR'bot | hR'eq
    · left
      have hmap := congrArg (fun S : Subgroup (N ⧸ Q₀.subgroupOf N) =>
        S.map eQ.toMonoidHom) hR'bot
      simpa [R', Subgroup.map_map] using hmap
    · right
      have hmap := congrArg (fun S : Subgroup (N ⧸ Q₀.subgroupOf N) =>
        S.map eQ.toMonoidHom) hR'eq
      have hR_eq : R = QbarM := by
        have hR_eq' : R = QbarN.map eQ.toMonoidHom := by
          simpa [R', Subgroup.map_map] using hmap
        exact hR_eq'.trans hQbar_map
      simpa [QbarM] using hR_eq

/-- Theorem 15.2 L005-S0040--S0070: the regular-action contradiction forces
`Q/Q₀` to be minimal normal in `M/Q₀`. -/
private theorem CFSG.section15_Q0_quotient_minimal_normal
    {M MF K Q D : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMFne : MF ≠ section10Msigma M)
    (hq : q.val = Nat.card (section14KStar M K))
    (hQ : section12SylowSubgroupIn q Q M)
    (hQnormal : section10NormalIn Q M)
    (hQMF : Q ≤ MF)
    (hD : section15Theorem15_2ComplementData M K Q D) :
    section15QuotientMinimalNormal M Q (subgroupCentralizerIn Q D) := by
  classical
  let Q₀ : Subgroup G := subgroupCentralizerIn Q D
  have hDcomp : section12ComplementIn (section10Msigma M) Q D := hD.2.1
  have hD_le_M : D ≤ M := hDcomp.2.1.trans section15_msigma_le
  have hDkinv : K ≤ Subgroup.normalizer (D : Set G) :=
    section15_complement_D_K_invariant
      hM hMF hK hMFne hq hQ hQnormal hQMF hD
  have hQ₀KD :
      K ⊔ D ≤ Subgroup.normalizer (Q₀ : Set G) := by
    simpa [Q₀] using
      section15_Q0_KD_invariant_of_K_invariant_complement
        hM hMF hK hMFne hq hQ hQnormal hQMF hD hDkinv
  rcases section15_exists_ambient_Q1_minimal_lift_in_normalizer_quotient
      hM hMF hK hMFne hq hQ hQnormal hQMF hD with
    ⟨Q₁, hQ₁min⟩
  have hQ₁min_saved := hQ₁min
  rcases hQ₁min with
    ⟨_hQ₀N, _hQ₀Norm, hQ₁data, _hQ₁bar_norm, _hQ₁bar_ne, _hQ₁bar_min⟩
  rcases hQ₁data with
    ⟨hQ₀_lt_Q₁, hQ₁_le_Q, hQ₁_le_N, _hQ₁_norm_N, hQ₁KD⟩
  have hnot_pos :
      ¬ (section14KStar M K ≤ Q₀ ∨ ¬ section14KStar M K ≤ Q₁) := by
    intro hpos
    have hQ₁_le_Q₀ : Q₁ ≤ Q₀ :=
      section15_le_of_kstar_position
        (M := M) (MF := MF) (K := K) (Q := Q) (D := D) (A := Q₀) (B := Q₁)
        hM hMF hK hMFne hq hQ hQnormal hD le_rfl hQ₀_lt_Q₁ hQ₁_le_Q
        hQ₁_le_N hQ₀KD hQ₁KD hpos
    exact (not_le_of_gt hQ₀_lt_Q₁) hQ₁_le_Q₀
  have hKstar_not_Q₀ : ¬ section14KStar M K ≤ Q₀ := by
    intro hKstarQ₀
    exact hnot_pos (Or.inl hKstarQ₀)
  have hKstar_le_Q₁ : section14KStar M K ≤ Q₁ := by
    by_contra hKstar_not_Q₁
    exact hnot_pos (Or.inr hKstar_not_Q₁)
  have hQ₁_eq_Q : Q₁ = Q := by
    by_contra hQ₁_ne_Q
    have hQ₁_lt_Q : Q₁ < Q := lt_of_le_of_ne hQ₁_le_Q hQ₁_ne_Q
    rcases section15_exists_ambient_lift_in_normalizer_quotient_of_lt
        (M := M) (K := K) (Q := Q) (D := D) (A := Q₁)
        hQnormal (section15_sylowSubgroupIn_nilpotent hQ) hK.1 hD_le_M
        hQ₁_lt_Q hQ₁KD with
      ⟨B, hBdata⟩
    rcases hBdata with
      ⟨hQ₁_lt_B, hB_le_Q, hB_le_N, _hB_norm_N, hBKD⟩
    have hB_le_Q₁ : B ≤ Q₁ :=
      section15_le_of_kstar_position
        (M := M) (MF := MF) (K := K) (Q := Q) (D := D) (A := Q₁) (B := B)
        hM hMF hK hMFne hq hQ hQnormal hD hQ₀_lt_Q₁.le hQ₁_lt_B hB_le_Q
        hB_le_N hQ₁KD hBKD (Or.inl hKstar_le_Q₁)
    exact (not_le_of_gt hQ₁_lt_B) hB_le_Q₁
  have hM_norm_Q₀ : M ≤ Subgroup.normalizer (Q₀ : Set G) := by
    have hQ_norm_Q₀ : Q ≤ Subgroup.normalizer (Q₀ : Set G) := by
      intro x hxQ
      have hxQ₁ : x ∈ Q₁ := by
        simpa [hQ₁_eq_Q] using hxQ
      exact (hQ₁_le_N hxQ₁).2
    have hD_norm_Q₀ : D ≤ Subgroup.normalizer (Q₀ : Set G) :=
      le_sup_right.trans hQ₀KD
    have hMsigma_norm_Q₀ : section10Msigma M ≤ Subgroup.normalizer (Q₀ : Set G) := by
      rw [hDcomp.2.2.1]
      exact sup_le hQ_norm_Q₀ hD_norm_Q₀
    have hK_norm_Q₀ : K ≤ Subgroup.normalizer (Q₀ : Set G) :=
      le_sup_left.trans hQ₀KD
    have hMprod : M = K ⊔ section10Msigma M :=
      (section15_MF_ne_msigma_implies_P1 hM hMF hK hMFne).2
    rw [hMprod]
    exact sup_le hK_norm_Q₀ hMsigma_norm_Q₀
  simpa [Q₀] using
    section15_quotient_minimal_normal_of_Q1_eq_Q
      (M := M) (K := K) (Q := Q) (D := D) (Q₀ := Q₀) (Q₁ := Q₁)
      hM_norm_Q₀ hQ₁min_saved hQ₁_eq_Q


/-- The L005 regular-action branch also proves that `K*` is not contained in
`Q₀ = C_Q(D)`.  This is the exact source fact needed later to see that the
quotient map is injective on `K*`. -/
private theorem CFSG.section15_kstar_not_le_Q0_of_theorem15_2_context
    {M MF K Q D : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMFne : MF ≠ section10Msigma M)
    (hq : q.val = Nat.card (section14KStar M K))
    (hQ : section12SylowSubgroupIn q Q M)
    (hQnormal : section10NormalIn Q M)
    (hQMF : Q ≤ MF)
    (hD : section15Theorem15_2ComplementData M K Q D) :
    ¬ section14KStar M K ≤ subgroupCentralizerIn Q D := by
  classical
  let Q₀ : Subgroup G := subgroupCentralizerIn Q D
  have hDkinv : K ≤ Subgroup.normalizer (D : Set G) :=
    section15_complement_D_K_invariant
      hM hMF hK hMFne hq hQ hQnormal hQMF hD
  have hQ₀KD :
      K ⊔ D ≤ Subgroup.normalizer (Q₀ : Set G) := by
    simpa [Q₀] using
      section15_Q0_KD_invariant_of_K_invariant_complement
        hM hMF hK hMFne hq hQ hQnormal hQMF hD hDkinv
  rcases section15_exists_ambient_Q1_minimal_lift_in_normalizer_quotient
      hM hMF hK hMFne hq hQ hQnormal hQMF hD with
    ⟨Q₁, hQ₁min⟩
  rcases hQ₁min with
    ⟨_hQ₀N, _hQ₀Norm, hQ₁data, _hQ₁bar_norm, _hQ₁bar_ne, _hQ₁bar_min⟩
  rcases hQ₁data with
    ⟨hQ₀_lt_Q₁, hQ₁_le_Q, hQ₁_le_N, _hQ₁_norm_N, hQ₁KD⟩
  have hnot_pos :
      ¬ (section14KStar M K ≤ Q₀ ∨ ¬ section14KStar M K ≤ Q₁) := by
    intro hpos
    have hQ₁_le_Q₀ : Q₁ ≤ Q₀ :=
      section15_le_of_kstar_position
        (M := M) (MF := MF) (K := K) (Q := Q) (D := D) (A := Q₀) (B := Q₁)
        hM hMF hK hMFne hq hQ hQnormal hD le_rfl hQ₀_lt_Q₁ hQ₁_le_Q
        hQ₁_le_N hQ₀KD hQ₁KD hpos
    exact (not_le_of_gt hQ₀_lt_Q₁) hQ₁_le_Q₀
  intro hKstarQ₀
  exact hnot_pos (Or.inl (by simpa [Q₀] using hKstarQ₀))

/-- Theorem 15.2 L006-S0030 setup: `KD` is a Frobenius group with kernel
`D` and complement `K`. -/
private theorem CFSG.section15_KD_frobenius_with_kernel_D
    {M MF K Q D : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMFne : MF ≠ section10Msigma M)
    (hq : q.val = Nat.card (section14KStar M K))
    (hQ : section12SylowSubgroupIn q Q M)
    (hQnormal : section10NormalIn Q M)
    (hD : section15Theorem15_2ComplementData M K Q D) :
    IsFrobeniusGroupWithKernelComplement
      (D.subgroupOf (D ⊔ K)) (K.subgroupOf (D ⊔ K)) := by
  classical
  let S : Subgroup G := D ⊔ K
  let Dsub : Subgroup S := D.subgroupOf S
  let Ksub : Subgroup S := K.subgroupOf S
  have hK_le_S : K ≤ S := by
    exact le_sup_right
  have hDcomp : section12ComplementIn (section10Msigma M) Q D := hD.2.1
  have hD_le_sigma : D ≤ section10Msigma M := hDcomp.2.1
  have hD_le_M : D ≤ M := hD_le_sigma.trans section15_msigma_le
  have hK_norm_D : K ≤ Subgroup.normalizer (D : Set G) := hD.2.2.2
  have hS_norm_D : S ≤ Subgroup.normalizer (D : Set G) := by
    simpa [S] using sup_le Subgroup.le_normalizer hK_norm_D
  have hDnormalS : Dsub.Normal := by
    simpa [Dsub, S] using
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (show D ≤ S by simp [S])).2 hS_norm_D
  have hP1 : M ∈ section14MFamilyP1 G :=
    (section15_MF_ne_msigma_implies_P1 hM hMF hK hMFne).1
  have hKne : K ≠ ⊥ := section15_hall_kappa_ne_bot hP1.1 hK
  have hDne : D ≠ ⊥ := by
    intro hDbot
    have hSigma_eq_Q : section10Msigma M = Q := by
      rw [hDcomp.2.2.1, hDbot, sup_bot_eq]
    have hQnil : Group.IsNilpotent Q := section15_sylowSubgroupIn_nilpotent hQ
    have hSigmanil : Group.IsNilpotent (section10Msigma M) := by
      rw [hSigma_eq_Q]
      exact hQnil
    exact (section15_MF_ne_msigma_not_nilpotent hM hMF hMFne) hSigmanil
  have hSigma_K_disj :
      Disjoint (section10MsigmaSubgroup M) (K.subgroupOf M) := by
    simpa using
      section15_msigmaSubgroup_disjoint_kappaHall_of_MF_ne hM hMF hK hMFne
  have hD_K_disj : Disjoint D K := by
    rw [Subgroup.disjoint_def]
    intro y hyD hyK
    let yM : M := ⟨y, hD_le_M hyD⟩
    have hySigma : yM ∈ section10MsigmaSubgroup M := by
      have hySigmaG : y ∈ section10Msigma M := hD_le_sigma hyD
      rw [← section15_msigma_subgroupOf_eq]
      change (yM : G) ∈ section10Msigma M
      exact hySigmaG
    have hyKsub : yM ∈ K.subgroupOf M := by
      simpa [yM, Subgroup.mem_subgroupOf] using hyK
    have hybot : yM ∈ (⊥ : Subgroup M) :=
      Subgroup.disjoint_def.mp hSigma_K_disj hySigma hyKsub
    have hyoneM : yM = 1 := by simpa using hybot
    exact congrArg Subtype.val hyoneM
  have hcompl : Dsub.IsComplement' Ksub := by
    have hsup_local : Dsub ⊔ Ksub = ⊤ := by
      calc
        Dsub ⊔ Ksub = (D ⊔ K).subgroupOf S := by
          symm
          exact Subgroup.subgroupOf_sup (A := D) (A' := K) (B := S)
            (by simp [S])
            (by simp [S])
        _ = ⊤ := by simp [S]
    letI : Dsub.Normal := hDnormalS
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [Subgroup.disjoint_def]
      intro x hxD hxK
      apply Subtype.ext
      exact Subgroup.disjoint_def.mp hD_K_disj
        (by simpa [Dsub, Subgroup.mem_subgroupOf] using hxD)
        (by simpa [Ksub, Subgroup.mem_subgroupOf] using hxK)
    · simpa [hsup_local] using (Subgroup.normal_mul Dsub Ksub).symm
  refine
    (lemma_3_1 (G := S) (K := Dsub) (R := Ksub)
      (by
        intro hbot
        apply hDne
        rw [Subgroup.eq_bot_iff_forall]
        intro d hdD
        have hdSub : (⟨d, by simpa [S] using (le_sup_left : D ≤ D ⊔ K) hdD⟩ : S) ∈ Dsub := by
          simpa [Dsub, Subgroup.mem_subgroupOf] using hdD
        have hdBot : (⟨d, by simpa [S] using (le_sup_left : D ≤ D ⊔ K) hdD⟩ : S) ∈
            (⊥ : Subgroup S) := by
          simpa [hbot] using hdSub
        have hdOne : (⟨d, by simpa [S] using (le_sup_left : D ≤ D ⊔ K) hdD⟩ : S) = 1 := by
          simpa using hdBot
        exact congrArg Subtype.val hdOne)
      (by
        intro hbot
        apply hKne
        rw [Subgroup.eq_bot_iff_forall]
        intro k hkK
        have hkSub : (⟨k, by simpa [S] using (le_sup_right : K ≤ D ⊔ K) hkK⟩ : S) ∈ Ksub := by
          simpa [Ksub, Subgroup.mem_subgroupOf] using hkK
        have hkBot : (⟨k, by simpa [S] using (le_sup_right : K ≤ D ⊔ K) hkK⟩ : S) ∈
            (⊥ : Subgroup S) := by
          simpa [hbot] using hkSub
        have hkOne : (⟨k, by simpa [S] using (le_sup_right : K ≤ D ⊔ K) hkK⟩ : S) = 1 := by
          simpa using hkBot
        exact congrArg Subtype.val hkOne)
      hDnormalS hcompl).2 ?_
  intro x hxne
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  have hprime : section14ActsInPrimeManner K (section10Msigma M) :=
    section15_prime_action_of_MF_ne_msigma hM hMF hK hMFne
  let xG : G := ((x : S) : G)
  have hxK : xG ∈ K := by
    simpa [xG] using (Subgroup.mem_subgroupOf.mp x.property)
  have hxneG : xG ≠ 1 := by
    intro hxG
    apply hxne
    apply Subtype.ext
    apply Subtype.ext
    exact hxG
  have hyD : ((y : S) : G) ∈ D := by
    simpa [Dsub, Subgroup.mem_subgroupOf] using hy.1
  have hyComm : ((y : S) : G) * xG = xG * ((y : S) : G) := by
    have hcommS : y * (x : S) = (x : S) * y :=
      Subgroup.mem_centralizer_singleton_iff.mp hy.2
    exact congrArg Subtype.val hcommS
  have hyCentSigma : ((y : S) : G) ∈ elementCentralizerIn (section10Msigma M) xG := by
    exact ⟨hD_le_sigma hyD, Subgroup.mem_centralizer_singleton_iff.mpr hyComm⟩
  have hCent_eq :
      elementCentralizerIn (section10Msigma M) xG = section14KStar M K :=
    section15_elementCentralizerIn_eq_kstar_of_prime_manner
      (M := M) (K := K) hprime hxK hxneG
  have hyKstar : ((y : S) : G) ∈ section14KStar M K := by
    simpa [hCent_eq] using hyCentSigma
  have hKstarQ : section14KStar M K ≤ Q :=
    section15_kstar_le_normal_sylow_of_prime_card
      (M := M) (K := K) (Q := Q) (q := q) hq hQ hQnormal
  have hyQ : ((y : S) : G) ∈ Q := hKstarQ hyKstar
  have hyoneG : ((y : S) : G) = 1 :=
    Subgroup.disjoint_def.mp hDcomp.2.2.2 hyQ hyD
  have hyoneS : y = 1 := by
    apply Subtype.ext
    exact hyoneG
  simp [hyoneS]


omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_subgroupCentralizerIn_eq_kstar_of_between
    {M K Q : Subgroup G}
    (hQ_le_sigma : Q ≤ section10Msigma M)
    (hKstarQ : section14KStar M K ≤ Q) :
    subgroupCentralizerIn Q K = section14KStar M K := by
  apply le_antisymm
  · intro x hx
    exact ⟨hQ_le_sigma hx.1, hx.2⟩
  · intro x hx
    exact ⟨hKstarQ hx, hx.2⟩

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_mem_centralizer_of_mem_kstar
    {M K : Subgroup G} {x : G}
    (hx : x ∈ section14KStar M K) :
    x ∈ Subgroup.centralizer (K : Set G) := by
  change x ∈ subgroupCentralizerIn (section10Msigma M) K at hx
  exact hx.2

omit [IsMinCE G] in
private theorem CFSG.section15_zpowers_centralizer_eq_kstar_of_prime_manner
    {M K Q : Subgroup G} {x : G}
    (hQ_le_sigma : Q ≤ section10Msigma M)
    (hprime : section14ActsInPrimeManner K (section10Msigma M))
    (hxK : x ∈ K) (hxne : x ≠ 1)
    (hKstarQ : section14KStar M K ≤ Q) :
    subgroupCentralizerIn Q (Subgroup.zpowers x) = section14KStar M K := by
  have hElem_eq :
      elementCentralizerIn (section10Msigma M) x = section14KStar M K :=
    section15_elementCentralizerIn_eq_kstar_of_prime_manner
      (M := M) (K := K) hprime hxK hxne
  apply le_antisymm
  · intro y hy
    have hySigma : y ∈ section10Msigma M := hQ_le_sigma hy.1
    have hyCentX : y ∈ Subgroup.centralizer ({x} : Set G) := by
      have hxy : x * y = y * x :=
        Subgroup.mem_centralizer_iff.mp hy.2 x (Subgroup.mem_zpowers x)
      exact Subgroup.mem_centralizer_singleton_iff.mpr hxy.symm
    have hyElem : y ∈ elementCentralizerIn (section10Msigma M) x :=
      ⟨hySigma, hyCentX⟩
    rw [← hElem_eq]
    exact hyElem
  · intro y hy
    have hyQ : y ∈ Q := hKstarQ hy
    have hyCentK : y ∈ Subgroup.centralizer (K : Set G) :=
      section15_mem_centralizer_of_mem_kstar hy
    refine ⟨hyQ, ?_⟩
    exact (Subgroup.centralizer_le
      (show (Subgroup.zpowers x : Set G) ⊆ (K : Set G) from
        fun z hz => (Subgroup.zpowers_le.2 hxK) hz)) hyCentK

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_subgroupCentralizerIn_subgroupOf_eq_of_ambient
    {M A B C : Subgroup G} (hB_le_M : B ≤ M)
    (hC : subgroupCentralizerIn A B = C) :
    subgroupCentralizerIn (A.subgroupOf M) (B.subgroupOf M) = C.subgroupOf M := by
  calc
    subgroupCentralizerIn (A.subgroupOf M) (B.subgroupOf M) =
        (subgroupCentralizerIn A B).subgroupOf M := by
      exact subgroupCentralizerIn_subgroupOf_eq M A B hB_le_M
    _ = C.subgroupOf M := by rw [hC]

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_subgroupCentralizerIn_subgroupOf_eq_kstar_of_between
    {M K Q : Subgroup G} (hK_le_M : K ≤ M)
    (hQ_le_sigma : Q ≤ section10Msigma M)
    (hKstarQ : section14KStar M K ≤ Q) :
    subgroupCentralizerIn (Q.subgroupOf M) (K.subgroupOf M) =
      (section14KStar M K).subgroupOf M :=
  section15_subgroupCentralizerIn_subgroupOf_eq_of_ambient hK_le_M
    (section15_subgroupCentralizerIn_eq_kstar_of_between hQ_le_sigma hKstarQ)

omit [IsMinCE G] in
private theorem CFSG.section15_zpowers_centralizer_subgroupOf_eq_kstar_of_prime_manner
    {M K Q : Subgroup G} {x : G}
    (hzpow_le_M : Subgroup.zpowers x ≤ M)
    (hQ_le_sigma : Q ≤ section10Msigma M)
    (hprime : section14ActsInPrimeManner K (section10Msigma M))
    (hxK : x ∈ K) (hxne : x ≠ 1)
    (hKstarQ : section14KStar M K ≤ Q) :
    subgroupCentralizerIn (Q.subgroupOf M) ((Subgroup.zpowers x).subgroupOf M) =
      (section14KStar M K).subgroupOf M :=
  section15_subgroupCentralizerIn_subgroupOf_eq_of_ambient hzpow_le_M
    (section15_zpowers_centralizer_eq_kstar_of_prime_manner
      hQ_le_sigma hprime hxK hxne hKstarQ)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_subgroupOf_le_normalizer_of_normalIn
    {M Q R : Subgroup G} (hQnormal : section10NormalIn Q M) :
    R.subgroupOf M ≤ Subgroup.normalizer ((Q.subgroupOf M : Subgroup M) : Set M) := by
  letI : (Q.subgroupOf M).Normal := hQnormal.2
  exact le_top.trans (Subgroup.le_normalizer_of_normal (H := Q.subgroupOf M))

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_subgroupOf_solvable_of_solvable
    {M Q : Subgroup G} (hsolvM : Group.IsSolvable M) :
    Group.IsSolvable (Q.subgroupOf M) := by
  letI : Group.IsSolvable M := hsolvM
  infer_instance

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_zpowers_subgroupOf_eq
    {M : Subgroup G} {x : G} (hxM : x ∈ M) :
    (Subgroup.zpowers x).subgroupOf M = Subgroup.zpowers (⟨x, hxM⟩ : M) := by
  let xM : M := ⟨x, hxM⟩
  ext y
  constructor
  · intro hy
    have hyG : ((y : M) : G) ∈ Subgroup.zpowers x := by
      simpa [Subgroup.mem_subgroupOf] using hy
    rcases hyG with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    apply Subtype.ext
    simpa [xM] using hn
  · intro hy
    rcases hy with ⟨n, hn⟩
    change ((y : M) : G) ∈ Subgroup.zpowers x
    refine ⟨n, ?_⟩
    simpa [xM] using congrArg (fun z : M => (z : G)) hn

private theorem CFSG.section15_coprime_card_Q_K_subgroupOf
    {M K Q : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hq : q.val = Nat.card (section14KStar M K))
    (hQ : section12SylowSubgroupIn q Q M) (hQM : Q ≤ M) :
    Nat.Coprime (Nat.card (Q.subgroupOf M)) (Nat.card (K.subgroupOf M)) := by
  have hQπ := section15_sylowSubgroupIn_isPiSubgroup_singleton hQ
  have hKπ := section15_hall_kappa_isPiSubgroup_q_compl hM hK hq
  have hQlocπ :
      IsPiSubgroup (G := M) ({q} : Set Nat.Primes) (Q.subgroupOf M) :=
    section15_isPiSubgroup_subgroupOf hQπ hQM
  have hKlocπ :
      IsPiSubgroup (G := M) ({q} : Set Nat.Primes)ᶜ (K.subgroupOf M) :=
    section15_isPiSubgroup_subgroupOf hKπ hK.1
  have hπdisj : Disjoint ({q} : Set Nat.Primes) (({q} : Set Nat.Primes)ᶜ) := by
    rw [Set.disjoint_left]
    intro p hpsing hpcompl
    exact hpcompl hpsing
  exact section15_coprime_card_of_disjoint_piSubgroups
    (G := M) hπdisj hQlocπ hKlocπ

private theorem CFSG.section15_coprime_card_Q_zpowers_subgroupOf
    {M K Q : Subgroup G} {q : Nat.Primes} {x : G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hq : q.val = Nat.card (section14KStar M K))
    (hQ : section12SylowSubgroupIn q Q M) (hQM : Q ≤ M)
    (hxK : x ∈ K) :
    Nat.Coprime (Nat.card (Q.subgroupOf M))
      (Nat.card ((Subgroup.zpowers x).subgroupOf M)) := by
  have hQπ := section15_sylowSubgroupIn_isPiSubgroup_singleton hQ
  have hKπ := section15_hall_kappa_isPiSubgroup_q_compl hM hK hq
  have hQlocπ :
      IsPiSubgroup (G := M) ({q} : Set Nat.Primes) (Q.subgroupOf M) :=
    section15_isPiSubgroup_subgroupOf hQπ hQM
  have hKlocπ :
      IsPiSubgroup (G := M) ({q} : Set Nat.Primes)ᶜ (K.subgroupOf M) :=
    section15_isPiSubgroup_subgroupOf hKπ hK.1
  have hRloc_le_Kloc :
      (Subgroup.zpowers x).subgroupOf M ≤ K.subgroupOf M := by
    intro y hy
    have hyR : (y : G) ∈ Subgroup.zpowers x := by
      simpa [Subgroup.mem_subgroupOf] using hy
    have hyK : (y : G) ∈ K := (Subgroup.zpowers_le.2 hxK) hyR
    simpa [Subgroup.mem_subgroupOf] using hyK
  have hRlocπ :
      IsPiSubgroup (G := M) ({q} : Set Nat.Primes)ᶜ
        ((Subgroup.zpowers x).subgroupOf M) :=
    IsPiSubgroup.of_le hRloc_le_Kloc hKlocπ
  have hπdisj : Disjoint ({q} : Set Nat.Primes) (({q} : Set Nat.Primes)ᶜ) := by
    rw [Set.disjoint_left]
    intro p hpsing hpcompl
    exact hpcompl hpsing
  exact section15_coprime_card_of_disjoint_piSubgroups
    (G := M) hπdisj hQlocπ hRlocπ

/-- Theorem 15.2 L006-S0030: Theorem 3.10 gives `p=|K|` prime in the
proper-containment branch. -/
private theorem CFSG.section15_p_card_prime_of_theorem15_2_context
    {M MF K Q D : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMFne : MF ≠ section10Msigma M)
    (hq : q.val = Nat.card (section14KStar M K))
    (hQ : section12SylowSubgroupIn q Q M)
    (hQnormal : section10NormalIn Q M)
    (hQMF : Q ≤ MF)
    (hD : section15Theorem15_2ComplementData M K Q D) :
    ∃ p : Nat.Primes, p.val = Nat.card K := by
  classical
  let Q₀ : Subgroup G := subgroupCentralizerIn Q D
  rcases section15_Q0_quotient_minimal_normal
      hM hMF hK hMFne hq hQ hQnormal hQMF hD with
    ⟨hQ₀M, hQM, hQ₀Q, hQ₀norm, hQbar_ne, hQbar_norm, _hQbar_min⟩
  let Q0M : Subgroup M := Q₀.subgroupOf M
  let qM : M →* M ⧸ Q0M := QuotientGroup.mk' Q0M
  let Qbar : Subgroup (M ⧸ Q0M) := (Q.subgroupOf M).map qM
  haveI : Q0M.Normal := by
    simpa [Q0M] using hQ₀norm
  haveI : Qbar.Normal := by
    simpa [Qbar] using hQbar_norm
  haveI : Nontrivial Qbar := by
    exact Qbar.nontrivial_iff_ne_bot.mpr (by simpa [Qbar] using hQbar_ne)
  let S : Subgroup G := D ⊔ K
  let Dsub : Subgroup S := D.subgroupOf S
  let Ksub : Subgroup S := K.subgroupOf S
  have hK_le_S : K ≤ S := by
    exact le_sup_right
  have hK_le_M : K ≤ M := hK.1
  have hDcomp : section12ComplementIn (section10Msigma M) Q D := hD.2.1
  have hD_le_M : D ≤ M := hDcomp.2.1.trans section15_msigma_le
  have hMF_le_sigma : MF ≤ section10Msigma M := section15_MF_le_msigma hM hMF
  have hQ_le_sigma : Q ≤ section10Msigma M := hQMF.trans hMF_le_sigma
  have hS_le_M : S ≤ M := by
    simpa [S] using sup_le hD_le_M hK_le_M
  let toQ : S →* M ⧸ Q0M :=
    (QuotientGroup.mk' Q0M).comp (Subgroup.inclusion hS_le_M)
  let toTop : (M ⧸ Q0M) →* (⊤ : Subgroup (M ⧸ Q0M)) :=
    { toFun := fun x => ⟨x, by simp⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp }
  letI : MulDistribMulAction (M ⧸ Q0M) Qbar :=
    MulDistribMulAction.compHom Qbar toTop
  letI : MulDistribMulAction S Qbar :=
    MulDistribMulAction.compHom Qbar toQ
  have hfrob :
      IsFrobeniusGroupWithKernelComplement Dsub Ksub := by
    simpa [Dsub, Ksub, S] using
      section15_KD_frobenius_with_kernel_D
        hM hMF hK hMFne hq hQ hQnormal hD
  have hsolvM : Group.IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.2 hM.1)
  have hsolvS : Group.IsSolvable S := by
    let Sloc : Subgroup M := S.subgroupOf M
    have hSloc_solv : Group.IsSolvable Sloc := by
      letI : Group.IsSolvable M := hsolvM
      infer_instance
    let eS : Sloc ≃* S :=
      Subgroup.subgroupOfEquivOfLe (H := S) (K := M) hS_le_M
    exact Group.isSolvable_of_surjective (f := eS.toMonoidHom) eS.surjective
  have hQbar_p : IsPGroup q.val Qbar := by
    haveI : Fact q.val.Prime := ⟨q.property⟩
    rcases hQ with ⟨P, hP⟩
    have hQp : IsPGroup q.val Q := by
      rw [← hP]
      change IsPGroup q.val ((P : Subgroup M).map M.subtype)
      exact IsPGroup.map (p := q.val) (H := (P : Subgroup M))
        P.isPGroup' M.subtype
    have hQloc_p : IsPGroup q.val (Q.subgroupOf M) := by
      have hcard : Nat.card (Q.subgroupOf M) = Nat.card Q := by
        exact Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe (H := Q) (K := M) hQM).toEquiv
      rcases IsPGroup.iff_card.mp hQp with ⟨n, hn⟩
      exact IsPGroup.iff_card.mpr ⟨n, by simp [hcard, hn]⟩
    simpa [Qbar, qM] using IsPGroup.map (p := q.val) (H := Q.subgroupOf M) hQloc_p qM
  have hnilQbar : Group.IsNilpotent Qbar := by
    haveI : Fact q.val.Prime := ⟨q.property⟩
    exact IsPGroup.isNilpotent (p := q.val) (G := Qbar) hQbar_p
  have hcop : Nat.Coprime (Nat.card S) (Nat.card Qbar) := by
    have hDπ : IsPiSubgroup (G := G) ({q} : Set Nat.Primes)ᶜ D :=
      section15_complement_D_isPiSubgroup_q_compl hQ hQnormal hDcomp
    have hKπ : IsPiSubgroup (G := G) ({q} : Set Nat.Primes)ᶜ K :=
      section15_hall_kappa_isPiSubgroup_q_compl hM hK hq
    have hDsubπ : IsPiSubgroup (G := S) ({q} : Set Nat.Primes)ᶜ Dsub := by
      simpa [Dsub] using
        section15_isPiSubgroup_subgroupOf
          (G := G) (H := S) (K := D) hDπ (by simp [S])
    have hKsubπ : IsPiSubgroup (G := S) ({q} : Set Nat.Primes)ᶜ Ksub := by
      simpa [Ksub] using
        section15_isPiSubgroup_subgroupOf
          (G := G) (H := S) (K := K) hKπ (by simp [S])
    have hStopπ :
        IsPiSubgroup (G := S) ({q} : Set Nat.Primes)ᶜ (⊤ : Subgroup S) := by
      have hDsub_normal : Dsub.Normal := hfrob.normal
      letI : Dsub.Normal := hDsub_normal
      have hsupπ :
          IsPiSubgroup (G := S) ({q} : Set Nat.Primes)ᶜ (Ksub ⊔ Dsub) :=
        section15_isPiSubgroup_sup_of_normal_right hKsubπ hDsubπ
      have hcompl : Dsub.IsComplement' Ksub := hfrob.isComplement'
      have hsup_top : Ksub ⊔ Dsub = ⊤ := by
        simpa [sup_comm] using hcompl.sup_eq_top
      simpa [hsup_top] using hsupπ
    have hQbartop_p : IsPGroup q.val (⊤ : Subgroup Qbar) :=
      hQbar_p.of_equiv
        (Subgroup.topEquiv : (⊤ : Subgroup Qbar) ≃* Qbar).symm
    have hQbartopπ :
        IsPiSubgroup (G := Qbar) ({q} : Set Nat.Primes) (⊤ : Subgroup Qbar) :=
      section8_isPiSubgroup_singleton_of_isPGroup hQbartop_p
    have hπdisj : Disjoint (({q} : Set Nat.Primes)ᶜ) ({q} : Set Nat.Primes) := by
      rw [Set.disjoint_left]
      intro p hpcompl hpsing
      exact hpcompl hpsing
    exact
      section15_coprime_natCard_of_disjoint_piGroups
        (R := S) (S := Qbar) hπdisj hStopπ hQbartopπ
  let Qloc : Subgroup M := Q.subgroupOf M
  let Kloc : Subgroup M := K.subgroupOf M
  have hsolvQloc' : Group.IsSolvable Qloc := by
    simpa [Qloc] using
      section15_subgroupOf_solvable_of_solvable (G := G) (M := M) (Q := Q) hsolvM
  have hcop_QKloc : Nat.Coprime (Nat.card Qloc) (Nat.card Kloc) := by
    simpa [Qloc, Kloc] using
      section15_coprime_card_Q_K_subgroupOf
        (G := G) (M := M) (K := K) (Q := Q) (q := q) hM hK hq hQ hQM
  have hprime : section14ActsInPrimeManner K (section10Msigma M) :=
    section15_prime_action_of_MF_ne_msigma hM hMF hK hMFne
  have hKstarQ : section14KStar M K ≤ Q :=
    section15_kstar_le_normal_sylow_of_prime_card
      (M := M) (K := K) (Q := Q) (q := q) hq hQ hQnormal
  have hcent_K_local_eq :
      subgroupCentralizerIn Qloc Kloc =
        (section14KStar M K).subgroupOf M := by
    exact section15_subgroupCentralizerIn_subgroupOf_eq_kstar_of_between
      (M := M) (K := K) (Q := Q) hK.1 hQ_le_sigma hKstarQ
  have hmap_subgroupOf (A : Subgroup G) (hAS : A ≤ S) (hAM : A ≤ M) :
      (A.subgroupOf S).map toQ = (A.subgroupOf M).map qM := by
    ext z
    constructor
    · intro hz
      rcases Subgroup.mem_map.mp hz with ⟨aS, haA, rfl⟩
      have haAamb : (aS : G) ∈ A := by
        simpa [Subgroup.mem_subgroupOf] using haA
      let aM : M := ⟨(aS : G), hAM haAamb⟩
      have haM : aM ∈ A.subgroupOf M := by
        simpa [aM, Subgroup.mem_subgroupOf] using haAamb
      refine Subgroup.mem_map.mpr ⟨aM, haM, ?_⟩
      have ha_eq : aM = Subgroup.inclusion hS_le_M aS := by
        apply Subtype.ext
        rfl
      simpa [toQ, qM, aM] using congrArg qM ha_eq
    · intro hz
      rcases Subgroup.mem_map.mp hz with ⟨aM, haA, rfl⟩
      have haAamb : (aM : G) ∈ A := by
        simpa [Subgroup.mem_subgroupOf] using haA
      let aS : S := ⟨(aM : G), hAS haAamb⟩
      have haS : aS ∈ A.subgroupOf S := by
        simpa [aS, Subgroup.mem_subgroupOf] using haAamb
      refine Subgroup.mem_map.mpr ⟨aS, haS, ?_⟩
      have ha_eq : Subgroup.inclusion hS_le_M aS = aM := by
        apply Subtype.ext
        rfl
      simpa [toQ, qM, aS] using congrArg qM ha_eq
  have hKbar_eq :
      Ksub.map toQ = Kloc.map qM := by
    simpa [Ksub, Kloc] using hmap_subgroupOf K hK_le_S hK_le_M
  have hcent_K_map :
      subgroupCentralizerIn (Qloc.map qM) (Kloc.map qM) =
        (subgroupCentralizerIn Qloc Kloc).map qM := by
    have hKnormH : Kloc ≤ Subgroup.normalizer (Qloc : Set M) := by
      simpa [Qloc, Kloc] using
        section15_subgroupOf_le_normalizer_of_normalIn
          (M := M) (Q := Q) (R := K) hQnormal
    have hQ0inv : ∀ r : Kloc, ∀ y ∈ Q0M, (r : M) * y * (r : M)⁻¹ ∈ Q0M := by
      intro r y hy
      exact (inferInstance : Q0M.Normal).conj_mem y hy r
    exact
      subgroupCentralizerIn_map_mk'_eq_map_of_solvable_coprime
        (G := M) Qloc Kloc Q0M hKnormH
        hsolvQloc' hcop_QKloc hQ0inv
  have hfix_toQ_eq (A : Subgroup S) :
      fixedPointSubgroup (↥A) Qbar =
        (subgroupCentralizerIn Qbar (A.map toQ)).subgroupOf Qbar := by
    ext y
    constructor
    · intro hy
      refine ⟨y.2, ?_⟩
      change (y : M ⧸ Q0M) ∈
        Subgroup.centralizer (A.map toQ : Set (M ⧸ Q0M))
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rcases Subgroup.mem_map.mp hz with ⟨a, haA, rfl⟩
      have hyfix : (⟨a, haA⟩ : A) • y = y := by
        rw [fixedPointSubgroup, FixedPoints.mem_subgroup] at hy
        exact hy ⟨a, haA⟩
      have hconj :
          toQ a * (y : M ⧸ Q0M) * (toQ a)⁻¹ = y := by
        have hval := congrArg Subtype.val hyfix
        change toQ a * (y : M ⧸ Q0M) * (toQ a)⁻¹ = (y : M ⧸ Q0M) at hval
        exact hval
      exact mul_inv_eq_iff_eq_mul.mp hconj
    · intro hy
      rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
      intro a
      have hcomm :
          toQ (a : S) * (y : M ⧸ Q0M) =
            (y : M ⧸ Q0M) * toQ (a : S) := by
        have hyc :
            (y : M ⧸ Q0M) ∈
              Subgroup.centralizer (A.map toQ : Set (M ⧸ Q0M)) := hy.2
        exact Subgroup.mem_centralizer_iff.mp hyc (toQ (a : S))
          (Subgroup.mem_map.mpr ⟨(a : S), a.property, rfl⟩)
      have hconj :
          toQ (a : S) * (y : M ⧸ Q0M) * (toQ (a : S))⁻¹ = y := by
        exact mul_inv_eq_iff_eq_mul.mpr hcomm
      apply Subtype.ext
      change toQ (a : S) * (y : M ⧸ Q0M) * (toQ (a : S))⁻¹ =
        (y : M ⧸ Q0M)
      exact hconj
  have hfixD : fixedPointSubgroup (↥Dsub) Qbar = ⊥ := by
    let Qloc : Subgroup M := Q.subgroupOf M
    let Dloc : Subgroup M := D.subgroupOf M
    let Dbar : Subgroup (M ⧸ Q0M) := Dloc.map qM
    have hDbar_eq : Dsub.map toQ = Dbar := by
      simpa [Dsub, Dloc, Dbar] using
        hmap_subgroupOf D (by simp [S]) hD_le_M
    have hfix_eq :
        fixedPointSubgroup (↥Dsub) Qbar =
          (subgroupCentralizerIn Qbar Dbar).subgroupOf Qbar := by
      calc
        fixedPointSubgroup (↥Dsub) Qbar =
            (subgroupCentralizerIn Qbar (Dsub.map toQ)).subgroupOf Qbar :=
          hfix_toQ_eq Dsub
        _ = (subgroupCentralizerIn Qbar Dbar).subgroupOf Qbar := by
          rw [hDbar_eq]
    have hQloc_norm : Qloc.Normal := by
      simpa [Qloc] using hQnormal.2
    have hDloc_norm_Qloc : Dloc ≤ Subgroup.normalizer (Qloc : Set M) :=
      le_top.trans (Subgroup.le_normalizer_of_normal (H := Qloc))
    have hsolvQloc' :=
      section15_subgroupOf_solvable_of_solvable (G := G) (M := M) (Q := Q) hsolvM
    have hQπ : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) Q :=
      section15_sylowSubgroupIn_isPiSubgroup_singleton hQ
    have hDπ : IsPiSubgroup (G := G) ({q} : Set Nat.Primes)ᶜ D :=
      section15_complement_D_isPiSubgroup_q_compl hQ hQnormal hDcomp
    have hQlocπ :
        IsPiSubgroup (G := M) ({q} : Set Nat.Primes) Qloc := by
      simpa [Qloc] using
        section15_isPiSubgroup_subgroupOf
          (G := G) (H := M) (K := Q) hQπ hQM
    have hDlocπ :
        IsPiSubgroup (G := M) ({q} : Set Nat.Primes)ᶜ Dloc := by
      simpa [Dloc] using
        section15_isPiSubgroup_subgroupOf
          (G := G) (H := M) (K := D) hDπ hD_le_M
    have hπdisj : Disjoint ({q} : Set Nat.Primes) (({q} : Set Nat.Primes)ᶜ) := by
      rw [Set.disjoint_left]
      intro p hpsing hpcompl
      exact hpcompl hpsing
    have hcopQDloc : Nat.Coprime (Nat.card Qloc) (Nat.card Dloc) :=
      section15_coprime_card_of_disjoint_piSubgroups
        (G := M) hπdisj hQlocπ hDlocπ
    have hQ0invDloc :
        ∀ r : Dloc, ∀ x ∈ Q0M, (r : M) * x * (r : M)⁻¹ ∈ Q0M := by
      intro r x hx
      exact (inferInstance : Q0M.Normal).conj_mem x hx r
    have hcent_map :
        subgroupCentralizerIn Qbar Dbar =
          (subgroupCentralizerIn Qloc Dloc).map qM := by
      simpa [Qbar, Dbar, Qloc, Dloc, qM] using
        subgroupCentralizerIn_map_mk'_eq_map_of_solvable_coprime
          (H := Qloc) (R := Dloc) (X := Q0M)
          hDloc_norm_Qloc hsolvQloc' hcopQDloc hQ0invDloc
    have hcent_local_eq :
        subgroupCentralizerIn Qloc Dloc = Q0M := by
      simpa [Qloc, Dloc, Q0M] using
        subgroupCentralizerIn_subgroupOf_eq M Q D hD_le_M
    have hQ0_map_bot : Q0M.map qM = ⊥ := by
      apply bot_unique
      intro y hy
      rcases Subgroup.mem_map.mp hy with ⟨x, hxQ0, rfl⟩
      simpa [qM, QuotientGroup.eq_one_iff] using hxQ0
    have hcent_bot : subgroupCentralizerIn Qbar Dbar = ⊥ := by
      calc
        subgroupCentralizerIn Qbar Dbar =
            (subgroupCentralizerIn Qloc Dloc).map qM := hcent_map
        _ = Q0M.map qM := by rw [hcent_local_eq]
        _ = ⊥ := hQ0_map_bot
    simp [hfix_eq, hcent_bot]
  have hfixK :
      ∀ x : Ksub, x ≠ 1 →
        fixedPointSubgroup (↥(Subgroup.zpowers (x : S))) Qbar =
          fixedPointSubgroup (↥Ksub) Qbar := by
    clear hfixD _hQbar_min
    intro x hxne
    let xG : G := ((x : S) : G)
    let R : Subgroup G := Subgroup.zpowers xG
    let Rloc : Subgroup M := (Subgroup.zpowers xG).subgroupOf M
    have hxK : xG ∈ K := by
      simpa [xG] using (Subgroup.mem_subgroupOf.mp x.property)
    have hxneG : xG ≠ 1 := by
      intro hx1
      apply hxne
      apply Subtype.ext
      apply Subtype.ext
      exact hx1
    have hR_le_K : R ≤ K := by
      simpa [R, xG] using (Subgroup.zpowers_le.2 hxK)
    have hR_le_M : R ≤ M := hR_le_K.trans hK.1
    have hzpow_le_M : Subgroup.zpowers xG ≤ M :=
      Subgroup.zpowers_le.2 (hK.1 hxK)
    have hR_le_S : R ≤ S := by
      simpa [S] using hR_le_K.trans (le_sup_right : K ≤ D ⊔ K)
    have hRloc_le_Kloc : Rloc ≤ Kloc := by
      intro y hy
      have hyR : (y : G) ∈ R := by
        simpa [Rloc, R, Subgroup.mem_subgroupOf] using hy
      have hyK : (y : G) ∈ K := hR_le_K hyR
      simpa [Kloc, Subgroup.mem_subgroupOf] using hyK
    have hcop_QRloc : Nat.Coprime (Nat.card Qloc) (Nat.card Rloc) := by
      simpa [Qloc, Rloc] using
        section15_coprime_card_Q_zpowers_subgroupOf
          (G := G) (M := M) (K := K) (Q := Q) (q := q) (x := xG)
          hM hK hq hQ hQM hxK
    have hcent_R_map :
        subgroupCentralizerIn (Qloc.map qM) (Rloc.map qM) =
          (subgroupCentralizerIn Qloc Rloc).map qM := by
      have hRnormH : Rloc ≤ Subgroup.normalizer (Qloc : Set M) := by
        simpa [Qloc, Rloc] using
          section15_subgroupOf_le_normalizer_of_normalIn
            (M := M) (Q := Q) (R := Subgroup.zpowers xG) hQnormal
      have hQ0inv : ∀ r : Rloc, ∀ y ∈ Q0M, (r : M) * y * (r : M)⁻¹ ∈ Q0M := by
        intro r y hy
        exact (inferInstance : Q0M.Normal).conj_mem y hy r
      exact
        subgroupCentralizerIn_map_mk'_eq_map_of_solvable_coprime
          (G := M) Qloc Rloc Q0M hRnormH
          hsolvQloc' hcop_QRloc hQ0inv
    have hRsubS_eq : R.subgroupOf S = Subgroup.zpowers (x : S) := by
      have hxS : xG ∈ S := hR_le_S (Subgroup.mem_zpowers xG)
      have hxS_eq : (⟨xG, hxS⟩ : S) = (x : S) := by
        apply Subtype.ext
        rfl
      simpa only [R, hxS_eq] using
        section15_zpowers_subgroupOf_eq (M := S) (x := xG) hxS
    have hRbar_eq :
        (Subgroup.zpowers (x : S)).map toQ =
          Rloc.map qM := by
      rw [← hRsubS_eq]
      exact hmap_subgroupOf R hR_le_S hR_le_M
    have hcent_R_local_eq :
        subgroupCentralizerIn (Q.subgroupOf M) ((Subgroup.zpowers xG).subgroupOf M) =
          (section14KStar M K).subgroupOf M := by
      exact section15_zpowers_centralizer_subgroupOf_eq_kstar_of_prime_manner
        (M := M) (K := K) (Q := Q) (x := xG)
        hzpow_le_M hQ_le_sigma hprime hxK hxneG hKstarQ
    letI : (Q.subgroupOf M).Normal := hQnormal.2
    have hQbar_def : Qbar = (Q.subgroupOf M).map qM := by
      rfl
    have hqM_def : qM = QuotientGroup.mk' Q0M := by
      rfl
    have hcent_quot_eq :
        subgroupCentralizerIn Qbar ((Subgroup.zpowers (x : S)).map toQ) =
          subgroupCentralizerIn Qbar (Ksub.map toQ) := by
      change
        subgroupCentralizerIn (Qloc.map qM)
            ((Subgroup.zpowers (x : S)).map toQ) =
          subgroupCentralizerIn (Qloc.map qM)
            (Ksub.map toQ)
      calc
        subgroupCentralizerIn (Qloc.map qM)
            ((Subgroup.zpowers (x : S)).map toQ) =
            subgroupCentralizerIn (Qloc.map qM) (Rloc.map qM) := by
              exact congrArg
                (fun A : Subgroup (M ⧸ Q0M) => subgroupCentralizerIn (Qloc.map qM) A)
                hRbar_eq
        _ = (subgroupCentralizerIn Qloc Rloc).map qM := by
              simpa [qM] using hcent_R_map
        _ = ((section14KStar M K).subgroupOf M).map qM := by
              simpa [Qloc, Rloc] using congrArg
                (fun A : Subgroup M => A.map qM) hcent_R_local_eq
        _ = (subgroupCentralizerIn Qloc Kloc).map qM := by
              simpa [Qloc, Kloc] using congrArg
                (fun A : Subgroup M => A.map qM) hcent_K_local_eq.symm
        _ = subgroupCentralizerIn (Qloc.map qM) (Kloc.map qM) := by
              simpa [qM] using hcent_K_map.symm
        _ = subgroupCentralizerIn (Qloc.map qM) (Ksub.map toQ) := by
              exact congrArg
                (fun A : Subgroup (M ⧸ Q0M) => subgroupCentralizerIn (Qloc.map qM) A)
                hKbar_eq.symm
    calc
      fixedPointSubgroup (↥(Subgroup.zpowers (x : S))) Qbar =
          (subgroupCentralizerIn Qbar ((Subgroup.zpowers (x : S)).map toQ)).subgroupOf Qbar :=
            hfix_toQ_eq (Subgroup.zpowers (x : S))
      _ = (subgroupCentralizerIn Qbar (Ksub.map toQ)).subgroupOf Qbar := by
            rw [hcent_quot_eq]
      _ = fixedPointSubgroup (↥Ksub) Qbar := (hfix_toQ_eq Ksub).symm
  have hmain :=
    theorem_3_10_a (G := S) (K := Dsub) (R := Ksub) (M := Qbar)
      hfrob hsolvS hnilQbar hcop hfixD hfixK
  have hKsub_card : Nat.card Ksub = Nat.card K := by
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe
        (H := K) (K := S) (by simp [S])).toEquiv
  exact ⟨⟨Nat.card K, by simpa [hKsub_card] using hmain.2⟩, rfl⟩

omit [IsMinCE G] in
private theorem CFSG.section15_elementary_prime_eq_of_nontrivial_pgroup
    {H : Type*} [Group H] [Finite H] {p r : ℕ}
    (hp : p.Prime) (hr : r.Prime) [Nontrivial H]
    (hHp : IsPGroup p H) (hElem : IsElementaryAbelian r H) :
    r = p := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨x, hx_ne⟩ := exists_ne (1 : H)
  have hxpow : x ^ r = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p r H) x
  have horder_eq_r : orderOf x = r := orderOf_eq_prime hxpow hx_ne
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf (p := p) (G := H)).1 hHp x
  have hn0 : n ≠ 0 := by
    intro hn0
    apply hx_ne
    exact orderOf_eq_one_iff.mp (by simpa [hn0] using hn)
  have hp_dvd_r : p ∣ r := by
    rw [← horder_eq_r, hn]
    exact dvd_pow_self p hn0
  simpa [eq_comm] using (hr.dvd_iff_eq hp.ne_one).1 hp_dvd_r

/-- Theorem 15.2 L006-S0030: `Q/Q₀` is elementary abelian of order `q^p`. -/
private theorem CFSG.section15_Qbar_elementary_card
    {M MF K Q D : Subgroup G} {p q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMFne : MF ≠ section10Msigma M)
    (hp : p.val = Nat.card K)
    (hq : q.val = Nat.card (section14KStar M K))
    (hQ : section12SylowSubgroupIn q Q M)
    (hQnormal : section10NormalIn Q M)
    (hQMF : Q ≤ MF)
    (hD : section15Theorem15_2ComplementData M K Q D) :
    section15QuotientElementaryCard M Q (subgroupCentralizerIn Q D) p q := by
  classical
  let Q₀ : Subgroup G := subgroupCentralizerIn Q D
  rcases section15_Q0_quotient_minimal_normal
      hM hMF hK hMFne hq hQ hQnormal hQMF hD with
    ⟨hQ₀M, hQM, hQ₀Q, hQ₀norm, hQbar_ne, hQbar_norm, hQbar_min⟩
  refine ⟨hQ₀M, hQM, hQ₀Q, hQ₀norm, ?_⟩
  let Q0M : Subgroup M := Q₀.subgroupOf M
  let qM : M →* M ⧸ Q0M := QuotientGroup.mk' Q0M
  let Qbar : Subgroup (M ⧸ Q0M) := (Q.subgroupOf M).map qM
  haveI : Q0M.Normal := by
    simpa [Q0M] using hQ₀norm
  haveI : Qbar.Normal := by
    simpa [Qbar] using hQbar_norm
  haveI : Nontrivial Qbar := by
    exact Qbar.nontrivial_iff_ne_bot.mpr (by simpa [Qbar] using hQbar_ne)
  have hQbar_min' :
      ∀ N : Subgroup (M ⧸ Q0M), N.Normal → N ≤ Qbar → N = ⊥ ∨ N = Qbar := by
    simpa [Qbar, Q0M, Q₀, qM] using hQbar_min
  let S : Subgroup G := D ⊔ K
  let Dsub : Subgroup S := D.subgroupOf S
  let Ksub : Subgroup S := K.subgroupOf S
  have hK_le_S : K ≤ S := by
    exact le_sup_right
  have hK_le_M : K ≤ M := hK.1
  have hDcomp : section12ComplementIn (section10Msigma M) Q D := hD.2.1
  have hD_le_M : D ≤ M := hDcomp.2.1.trans section15_msigma_le
  have hMF_le_sigma : MF ≤ section10Msigma M := section15_MF_le_msigma hM hMF
  have hQ_le_sigma : Q ≤ section10Msigma M := hQMF.trans hMF_le_sigma
  have hS_le_M : S ≤ M := by
    simpa [S] using sup_le hD_le_M hK_le_M
  let toQ : S →* M ⧸ Q0M :=
    (QuotientGroup.mk' Q0M).comp (Subgroup.inclusion hS_le_M)
  let toTop : (M ⧸ Q0M) →* (⊤ : Subgroup (M ⧸ Q0M)) :=
    { toFun := fun x => ⟨x, by simp⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp }
  letI : MulDistribMulAction (M ⧸ Q0M) Qbar :=
    MulDistribMulAction.compHom Qbar toTop
  letI : MulDistribMulAction S Qbar :=
    MulDistribMulAction.compHom Qbar toQ
  have hfrob :
      IsFrobeniusGroupWithKernelComplement Dsub Ksub := by
    simpa [Dsub, Ksub, S] using
      section15_KD_frobenius_with_kernel_D
        hM hMF hK hMFne hq hQ hQnormal hD
  have hsolvM : Group.IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.2 hM.1)
  have hsolvS : Group.IsSolvable S := by
    let Sloc : Subgroup M := S.subgroupOf M
    have hSloc_solv : Group.IsSolvable Sloc := by
      letI : Group.IsSolvable M := hsolvM
      infer_instance
    let eS : Sloc ≃* S :=
      Subgroup.subgroupOfEquivOfLe (H := S) (K := M) hS_le_M
    exact Group.isSolvable_of_surjective (f := eS.toMonoidHom) eS.surjective
  have hQbar_p : IsPGroup q.val Qbar := by
    haveI : Fact q.val.Prime := ⟨q.property⟩
    rcases hQ with ⟨P, hP⟩
    have hQp : IsPGroup q.val Q := by
      rw [← hP]
      change IsPGroup q.val ((P : Subgroup M).map M.subtype)
      exact IsPGroup.map (p := q.val) (H := (P : Subgroup M))
        P.isPGroup' M.subtype
    have hQloc_p : IsPGroup q.val (Q.subgroupOf M) := by
      have hcard : Nat.card (Q.subgroupOf M) = Nat.card Q := by
        exact Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe (H := Q) (K := M) hQM).toEquiv
      rcases IsPGroup.iff_card.mp hQp with ⟨n, hn⟩
      exact IsPGroup.iff_card.mpr ⟨n, by simp [hcard, hn]⟩
    simpa [Qbar, qM] using IsPGroup.map (p := q.val) (H := Q.subgroupOf M) hQloc_p qM
  have hQbar_elem : IsElementaryAbelian q.val Qbar := by
    haveI : IsMinimalNormal Qbar := {
      minimal := by
        intro N hNnorm hNle
        exact hQbar_min' N hNnorm hNle
    }
    haveI : Group.IsSolvable Qbar := by
      haveI : Fact q.val.Prime := ⟨q.property⟩
      haveI : Group.IsNilpotent Qbar :=
        IsPGroup.isNilpotent (p := q.val) (G := Qbar) hQbar_p
      infer_instance
    rcases minimalNormal_solvable_exists_isElementaryAbelian
        (G := M ⧸ Q0M) (M := Qbar) with
      ⟨r, hrprime, hElem_r⟩
    have hr_eq_q :
        r = q.val :=
      section15_elementary_prime_eq_of_nontrivial_pgroup
        (H := Qbar) q.property hrprime hQbar_p hElem_r
    simpa [hr_eq_q] using hElem_r
  have hnilQbar : Group.IsNilpotent Qbar := by
    haveI : Fact q.val.Prime := ⟨q.property⟩
    exact IsPGroup.isNilpotent (p := q.val) (G := Qbar) hQbar_p
  have hcop : Nat.Coprime (Nat.card S) (Nat.card Qbar) := by
    have hDπ : IsPiSubgroup (G := G) ({q} : Set Nat.Primes)ᶜ D :=
      section15_complement_D_isPiSubgroup_q_compl hQ hQnormal hDcomp
    have hKπ : IsPiSubgroup (G := G) ({q} : Set Nat.Primes)ᶜ K :=
      section15_hall_kappa_isPiSubgroup_q_compl hM hK hq
    have hDsubπ : IsPiSubgroup (G := S) ({q} : Set Nat.Primes)ᶜ Dsub := by
      simpa [Dsub] using
        section15_isPiSubgroup_subgroupOf
          (G := G) (H := S) (K := D) hDπ (by simp [S])
    have hKsubπ : IsPiSubgroup (G := S) ({q} : Set Nat.Primes)ᶜ Ksub := by
      simpa [Ksub] using
        section15_isPiSubgroup_subgroupOf
          (G := G) (H := S) (K := K) hKπ (by simp [S])
    have hStopπ :
        IsPiSubgroup (G := S) ({q} : Set Nat.Primes)ᶜ (⊤ : Subgroup S) := by
      have hDsub_normal : Dsub.Normal := hfrob.normal
      letI : Dsub.Normal := hDsub_normal
      have hsupπ :
          IsPiSubgroup (G := S) ({q} : Set Nat.Primes)ᶜ (Ksub ⊔ Dsub) :=
        section15_isPiSubgroup_sup_of_normal_right hKsubπ hDsubπ
      have hcompl : Dsub.IsComplement' Ksub := hfrob.isComplement'
      have hsup_top : Ksub ⊔ Dsub = ⊤ := by
        simpa [sup_comm] using hcompl.sup_eq_top
      simpa [hsup_top] using hsupπ
    have hQbartop_p : IsPGroup q.val (⊤ : Subgroup Qbar) :=
      hQbar_p.of_equiv
        (Subgroup.topEquiv : (⊤ : Subgroup Qbar) ≃* Qbar).symm
    have hQbartopπ :
        IsPiSubgroup (G := Qbar) ({q} : Set Nat.Primes) (⊤ : Subgroup Qbar) :=
      section8_isPiSubgroup_singleton_of_isPGroup hQbartop_p
    have hπdisj : Disjoint (({q} : Set Nat.Primes)ᶜ) ({q} : Set Nat.Primes) := by
      rw [Set.disjoint_left]
      intro p hpcompl hpsing
      exact hpcompl hpsing
    exact
      section15_coprime_natCard_of_disjoint_piGroups
        (R := S) (S := Qbar) hπdisj hStopπ hQbartopπ
  let Qloc : Subgroup M := Q.subgroupOf M
  let Kloc : Subgroup M := K.subgroupOf M
  have hsolvQloc' : Group.IsSolvable Qloc := by
    simpa [Qloc] using
      section15_subgroupOf_solvable_of_solvable (G := G) (M := M) (Q := Q) hsolvM
  have hcop_QKloc : Nat.Coprime (Nat.card Qloc) (Nat.card Kloc) := by
    simpa [Qloc, Kloc] using
      section15_coprime_card_Q_K_subgroupOf
        (G := G) (M := M) (K := K) (Q := Q) (q := q) hM hK hq hQ hQM
  have hprime : section14ActsInPrimeManner K (section10Msigma M) :=
    section15_prime_action_of_MF_ne_msigma hM hMF hK hMFne
  have hKstarQ : section14KStar M K ≤ Q :=
    section15_kstar_le_normal_sylow_of_prime_card
      (M := M) (K := K) (Q := Q) (q := q) hq hQ hQnormal
  have hcent_K_local_eq :
      subgroupCentralizerIn Qloc Kloc =
        (section14KStar M K).subgroupOf M := by
    exact section15_subgroupCentralizerIn_subgroupOf_eq_kstar_of_between
      (M := M) (K := K) (Q := Q) hK.1 hQ_le_sigma hKstarQ
  have hmap_subgroupOf (A : Subgroup G) (hAS : A ≤ S) (hAM : A ≤ M) :
      (A.subgroupOf S).map toQ = (A.subgroupOf M).map qM := by
    ext z
    constructor
    · intro hz
      rcases Subgroup.mem_map.mp hz with ⟨aS, haA, rfl⟩
      have haAamb : (aS : G) ∈ A := by
        simpa [Subgroup.mem_subgroupOf] using haA
      let aM : M := ⟨(aS : G), hAM haAamb⟩
      have haM : aM ∈ A.subgroupOf M := by
        simpa [aM, Subgroup.mem_subgroupOf] using haAamb
      refine Subgroup.mem_map.mpr ⟨aM, haM, ?_⟩
      have ha_eq : aM = Subgroup.inclusion hS_le_M aS := by
        apply Subtype.ext
        rfl
      simpa [toQ, qM, aM] using congrArg qM ha_eq
    · intro hz
      rcases Subgroup.mem_map.mp hz with ⟨aM, haA, rfl⟩
      have haAamb : (aM : G) ∈ A := by
        simpa [Subgroup.mem_subgroupOf] using haA
      let aS : S := ⟨(aM : G), hAS haAamb⟩
      have haS : aS ∈ A.subgroupOf S := by
        simpa [aS, Subgroup.mem_subgroupOf] using haAamb
      refine Subgroup.mem_map.mpr ⟨aS, haS, ?_⟩
      have ha_eq : Subgroup.inclusion hS_le_M aS = aM := by
        apply Subtype.ext
        rfl
      simpa [toQ, qM, aS] using congrArg qM ha_eq
  have hKbar_eq :
      Ksub.map toQ = Kloc.map qM := by
    simpa [Ksub, Kloc] using hmap_subgroupOf K hK_le_S hK_le_M
  have hcent_K_map :
      subgroupCentralizerIn (Qloc.map qM) (Kloc.map qM) =
        (subgroupCentralizerIn Qloc Kloc).map qM := by
    have hKnormH : Kloc ≤ Subgroup.normalizer (Qloc : Set M) := by
      simpa [Qloc, Kloc] using
        section15_subgroupOf_le_normalizer_of_normalIn
          (M := M) (Q := Q) (R := K) hQnormal
    have hQ0inv : ∀ r : Kloc, ∀ y ∈ Q0M, (r : M) * y * (r : M)⁻¹ ∈ Q0M := by
      intro r y hy
      exact (inferInstance : Q0M.Normal).conj_mem y hy r
    exact
      subgroupCentralizerIn_map_mk'_eq_map_of_solvable_coprime
        (G := M) Qloc Kloc Q0M hKnormH
        hsolvQloc' hcop_QKloc hQ0inv
  have hfix_toQ_eq (A : Subgroup S) :
      fixedPointSubgroup (↥A) Qbar =
        (subgroupCentralizerIn Qbar (A.map toQ)).subgroupOf Qbar := by
    ext y
    constructor
    · intro hy
      refine ⟨y.2, ?_⟩
      change (y : M ⧸ Q0M) ∈
        Subgroup.centralizer (A.map toQ : Set (M ⧸ Q0M))
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rcases Subgroup.mem_map.mp hz with ⟨a, haA, rfl⟩
      have hyfix : (⟨a, haA⟩ : A) • y = y := by
        rw [fixedPointSubgroup, FixedPoints.mem_subgroup] at hy
        exact hy ⟨a, haA⟩
      have hconj :
          toQ a * (y : M ⧸ Q0M) * (toQ a)⁻¹ = y := by
        have hval := congrArg Subtype.val hyfix
        change toQ a * (y : M ⧸ Q0M) * (toQ a)⁻¹ = (y : M ⧸ Q0M) at hval
        exact hval
      exact mul_inv_eq_iff_eq_mul.mp hconj
    · intro hy
      rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
      intro a
      have hcomm :
          toQ (a : S) * (y : M ⧸ Q0M) =
            (y : M ⧸ Q0M) * toQ (a : S) := by
        have hyc :
            (y : M ⧸ Q0M) ∈
              Subgroup.centralizer (A.map toQ : Set (M ⧸ Q0M)) := hy.2
        exact Subgroup.mem_centralizer_iff.mp hyc (toQ (a : S))
          (Subgroup.mem_map.mpr ⟨(a : S), a.property, rfl⟩)
      have hconj :
          toQ (a : S) * (y : M ⧸ Q0M) * (toQ (a : S))⁻¹ = y := by
        exact mul_inv_eq_iff_eq_mul.mpr hcomm
      apply Subtype.ext
      change toQ (a : S) * (y : M ⧸ Q0M) * (toQ (a : S))⁻¹ =
        (y : M ⧸ Q0M)
      exact hconj
  have hfixD : fixedPointSubgroup (↥Dsub) Qbar = ⊥ := by
    let Qloc : Subgroup M := Q.subgroupOf M
    let Dloc : Subgroup M := D.subgroupOf M
    let Dbar : Subgroup (M ⧸ Q0M) := Dloc.map qM
    have hDbar_eq : Dsub.map toQ = Dbar := by
      simpa [Dsub, Dloc, Dbar] using
        hmap_subgroupOf D (by simp [S]) hD_le_M
    have hfix_eq :
        fixedPointSubgroup (↥Dsub) Qbar =
          (subgroupCentralizerIn Qbar Dbar).subgroupOf Qbar := by
      calc
        fixedPointSubgroup (↥Dsub) Qbar =
            (subgroupCentralizerIn Qbar (Dsub.map toQ)).subgroupOf Qbar :=
          hfix_toQ_eq Dsub
        _ = (subgroupCentralizerIn Qbar Dbar).subgroupOf Qbar := by
          rw [hDbar_eq]
    have hQloc_norm : Qloc.Normal := by
      simpa [Qloc] using hQnormal.2
    have hDloc_norm_Qloc : Dloc ≤ Subgroup.normalizer (Qloc : Set M) :=
      le_top.trans (Subgroup.le_normalizer_of_normal (H := Qloc))
    have hsolvQloc' :=
      section15_subgroupOf_solvable_of_solvable (G := G) (M := M) (Q := Q) hsolvM
    have hQπ : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) Q :=
      section15_sylowSubgroupIn_isPiSubgroup_singleton hQ
    have hDπ : IsPiSubgroup (G := G) ({q} : Set Nat.Primes)ᶜ D :=
      section15_complement_D_isPiSubgroup_q_compl hQ hQnormal hDcomp
    have hQlocπ :
        IsPiSubgroup (G := M) ({q} : Set Nat.Primes) Qloc := by
      simpa [Qloc] using
        section15_isPiSubgroup_subgroupOf
          (G := G) (H := M) (K := Q) hQπ hQM
    have hDlocπ :
        IsPiSubgroup (G := M) ({q} : Set Nat.Primes)ᶜ Dloc := by
      simpa [Dloc] using
        section15_isPiSubgroup_subgroupOf
          (G := G) (H := M) (K := D) hDπ hD_le_M
    have hπdisj : Disjoint ({q} : Set Nat.Primes) (({q} : Set Nat.Primes)ᶜ) := by
      rw [Set.disjoint_left]
      intro p hpsing hpcompl
      exact hpcompl hpsing
    have hcopQDloc : Nat.Coprime (Nat.card Qloc) (Nat.card Dloc) :=
      section15_coprime_card_of_disjoint_piSubgroups
        (G := M) hπdisj hQlocπ hDlocπ
    have hQ0invDloc :
        ∀ r : Dloc, ∀ x ∈ Q0M, (r : M) * x * (r : M)⁻¹ ∈ Q0M := by
      intro r x hx
      exact (inferInstance : Q0M.Normal).conj_mem x hx r
    have hcent_map :
        subgroupCentralizerIn Qbar Dbar =
          (subgroupCentralizerIn Qloc Dloc).map qM := by
      simpa [Qbar, Dbar, Qloc, Dloc, qM] using
        subgroupCentralizerIn_map_mk'_eq_map_of_solvable_coprime
          (H := Qloc) (R := Dloc) (X := Q0M)
          hDloc_norm_Qloc hsolvQloc' hcopQDloc hQ0invDloc
    have hcent_local_eq :
        subgroupCentralizerIn Qloc Dloc = Q0M := by
      simpa [Qloc, Dloc, Q0M] using
        subgroupCentralizerIn_subgroupOf_eq M Q D hD_le_M
    have hQ0_map_bot : Q0M.map qM = ⊥ := by
      apply bot_unique
      intro y hy
      rcases Subgroup.mem_map.mp hy with ⟨x, hxQ0, rfl⟩
      simpa [qM, QuotientGroup.eq_one_iff] using hxQ0
    have hcent_bot : subgroupCentralizerIn Qbar Dbar = ⊥ := by
      calc
        subgroupCentralizerIn Qbar Dbar =
            (subgroupCentralizerIn Qloc Dloc).map qM := hcent_map
        _ = Q0M.map qM := by rw [hcent_local_eq]
        _ = ⊥ := hQ0_map_bot
    simp [hfix_eq, hcent_bot]
  have hfixK :
      ∀ x : Ksub, x ≠ 1 →
        fixedPointSubgroup (↥(Subgroup.zpowers (x : S))) Qbar =
          fixedPointSubgroup (↥Ksub) Qbar := by
    clear hfixD hQbar_min
    intro x hxne
    let xG : G := ((x : S) : G)
    let R : Subgroup G := Subgroup.zpowers xG
    let Rloc : Subgroup M := (Subgroup.zpowers xG).subgroupOf M
    have hxK : xG ∈ K := by
      simpa [xG] using (Subgroup.mem_subgroupOf.mp x.property)
    have hxneG : xG ≠ 1 := by
      intro hx1
      apply hxne
      apply Subtype.ext
      apply Subtype.ext
      exact hx1
    have hR_le_K : R ≤ K := by
      simpa [R, xG] using (Subgroup.zpowers_le.2 hxK)
    have hR_le_M : R ≤ M := hR_le_K.trans hK.1
    have hzpow_le_M : Subgroup.zpowers xG ≤ M :=
      Subgroup.zpowers_le.2 (hK.1 hxK)
    have hR_le_S : R ≤ S := by
      simpa [S] using hR_le_K.trans (le_sup_right : K ≤ D ⊔ K)
    have hRloc_le_Kloc : Rloc ≤ Kloc := by
      intro y hy
      have hyR : (y : G) ∈ R := by
        simpa [Rloc, R, Subgroup.mem_subgroupOf] using hy
      have hyK : (y : G) ∈ K := hR_le_K hyR
      simpa [Kloc, Subgroup.mem_subgroupOf] using hyK
    have hcop_QRloc : Nat.Coprime (Nat.card Qloc) (Nat.card Rloc) := by
      simpa [Qloc, Rloc] using
        section15_coprime_card_Q_zpowers_subgroupOf
          (G := G) (M := M) (K := K) (Q := Q) (q := q) (x := xG)
          hM hK hq hQ hQM hxK
    have hcent_R_map :
        subgroupCentralizerIn (Qloc.map qM) (Rloc.map qM) =
          (subgroupCentralizerIn Qloc Rloc).map qM := by
      have hRnormH : Rloc ≤ Subgroup.normalizer (Qloc : Set M) := by
        simpa [Qloc, Rloc] using
          section15_subgroupOf_le_normalizer_of_normalIn
            (M := M) (Q := Q) (R := Subgroup.zpowers xG) hQnormal
      have hQ0inv : ∀ r : Rloc, ∀ y ∈ Q0M, (r : M) * y * (r : M)⁻¹ ∈ Q0M := by
        intro r y hy
        exact (inferInstance : Q0M.Normal).conj_mem y hy r
      exact
        subgroupCentralizerIn_map_mk'_eq_map_of_solvable_coprime
          (G := M) Qloc Rloc Q0M hRnormH
          hsolvQloc' hcop_QRloc hQ0inv
    have hRsubS_eq : R.subgroupOf S = Subgroup.zpowers (x : S) := by
      have hxS : xG ∈ S := hR_le_S (Subgroup.mem_zpowers xG)
      have hxS_eq : (⟨xG, hxS⟩ : S) = (x : S) := by
        apply Subtype.ext
        rfl
      simpa only [R, hxS_eq] using
        section15_zpowers_subgroupOf_eq (M := S) (x := xG) hxS
    have hRbar_eq :
        (Subgroup.zpowers (x : S)).map toQ =
          Rloc.map qM := by
      rw [← hRsubS_eq]
      exact hmap_subgroupOf R hR_le_S hR_le_M
    have hcent_R_local_eq :
        subgroupCentralizerIn (Q.subgroupOf M) ((Subgroup.zpowers xG).subgroupOf M) =
          (section14KStar M K).subgroupOf M := by
      exact section15_zpowers_centralizer_subgroupOf_eq_kstar_of_prime_manner
        (M := M) (K := K) (Q := Q) (x := xG)
        hzpow_le_M hQ_le_sigma hprime hxK hxneG hKstarQ
    letI : (Q.subgroupOf M).Normal := hQnormal.2
    have hcent_quot_eq :
        subgroupCentralizerIn Qbar ((Subgroup.zpowers (x : S)).map toQ) =
          subgroupCentralizerIn Qbar (Ksub.map toQ) := by
      change
        subgroupCentralizerIn (Qloc.map qM)
            ((Subgroup.zpowers (x : S)).map toQ) =
          subgroupCentralizerIn (Qloc.map qM)
            (Ksub.map toQ)
      calc
        subgroupCentralizerIn (Qloc.map qM)
            ((Subgroup.zpowers (x : S)).map toQ) =
            subgroupCentralizerIn (Qloc.map qM) (Rloc.map qM) := by
              exact congrArg
                (fun A : Subgroup (M ⧸ Q0M) => subgroupCentralizerIn (Qloc.map qM) A)
                hRbar_eq
        _ = (subgroupCentralizerIn Qloc Rloc).map qM := by
              simpa [qM] using hcent_R_map
        _ = ((section14KStar M K).subgroupOf M).map qM := by
              simpa [Qloc, Rloc] using congrArg
                (fun A : Subgroup M => A.map qM) hcent_R_local_eq
        _ = (subgroupCentralizerIn Qloc Kloc).map qM := by
              simpa [Qloc, Kloc] using congrArg
                (fun A : Subgroup M => A.map qM) hcent_K_local_eq.symm
        _ = subgroupCentralizerIn (Qloc.map qM) (Kloc.map qM) := by
              simpa [qM] using hcent_K_map.symm
        _ = subgroupCentralizerIn (Qloc.map qM) (Ksub.map toQ) := by
              exact congrArg
                (fun A : Subgroup (M ⧸ Q0M) => subgroupCentralizerIn (Qloc.map qM) A)
                hKbar_eq.symm
    calc
      fixedPointSubgroup (↥(Subgroup.zpowers (x : S))) Qbar =
          (subgroupCentralizerIn Qbar ((Subgroup.zpowers (x : S)).map toQ)).subgroupOf Qbar :=
            hfix_toQ_eq (Subgroup.zpowers (x : S))
      _ = (subgroupCentralizerIn Qbar (Ksub.map toQ)).subgroupOf Qbar := by
            rw [hcent_quot_eq]
      _ = fixedPointSubgroup (↥Ksub) Qbar := (hfix_toQ_eq Ksub).symm
  have hcent_K_quot_eq :
      subgroupCentralizerIn Qbar (Ksub.map toQ) =
        ((section14KStar M K).subgroupOf M).map qM := by
    change
      subgroupCentralizerIn (Qloc.map qM) (Ksub.map toQ) =
        ((section14KStar M K).subgroupOf M).map qM
    calc
      subgroupCentralizerIn (Qloc.map qM) (Ksub.map toQ) =
          subgroupCentralizerIn (Qloc.map qM) (Kloc.map qM) := by
            rw [hKbar_eq]
      _ = (subgroupCentralizerIn Qloc Kloc).map qM := hcent_K_map
      _ = ((section14KStar M K).subgroupOf M).map qM := by
            simpa [Qloc, Kloc] using congrArg
              (fun A : Subgroup M => A.map qM) hcent_K_local_eq
  have hfixK_eq :
      fixedPointSubgroup (↥Ksub) Qbar =
        (((section14KStar M K).subgroupOf M).map qM).subgroupOf Qbar := by
    calc
      fixedPointSubgroup (↥Ksub) Qbar =
          (subgroupCentralizerIn Qbar (Ksub.map toQ)).subgroupOf Qbar :=
            hfix_toQ_eq Ksub
      _ = (((section14KStar M K).subgroupOf M).map qM).subgroupOf Qbar := by
            rw [hcent_K_quot_eq]
  have hKstar_not_Q₀ :
      ¬ section14KStar M K ≤ Q₀ := by
    simpa [Q₀] using
      section15_kstar_not_le_Q0_of_theorem15_2_context
        hM hMF hK hMFne hq hQ hQnormal hQMF hD
  have hQ₀_Kstar_disj : Disjoint Q₀ (section14KStar M K) := by
    rw [Subgroup.disjoint_def]
    intro x hxQ₀ hxKstar
    by_contra hxne
    have hne_inf : section14KStar M K ⊓ Q₀ ≠ ⊥ := by
      intro hbot
      have hxbot : x ∈ (⊥ : Subgroup G) := by
        simpa [hbot] using
          (show x ∈ section14KStar M K ⊓ Q₀ from ⟨hxKstar, hxQ₀⟩)
      exact hxne (Subgroup.mem_bot.mp hxbot)
    have hle : section14KStar M K ≤ Q₀ :=
      section15_le_of_prime_card_inf_ne_bot
        (A := section14KStar M K) (B := Q₀) hq hne_inf
    exact hKstar_not_Q₀ hle
  have hKstar_le_M : section14KStar M K ≤ M := by
    intro x hx
    exact section15_msigma_le hx.1
  have hQ0M_KstarM_disj :
      Disjoint Q0M ((section14KStar M K).subgroupOf M) := by
    rw [Subgroup.disjoint_def]
    intro x hxQ0 hxKstar
    apply Subtype.ext
    exact Subgroup.disjoint_def.mp hQ₀_Kstar_disj
      (by simpa [Q0M, Subgroup.mem_subgroupOf] using hxQ0)
      (by simpa [Subgroup.mem_subgroupOf] using hxKstar)
  have hKstarM_le_Qloc :
      (section14KStar M K).subgroupOf M ≤ Qloc := by
    intro x hx
    have hxKstar : (x : G) ∈ section14KStar M K := by
      simpa [Subgroup.mem_subgroupOf] using hx
    have hxQ : (x : G) ∈ Q := hKstarQ hxKstar
    simpa [Qloc, Subgroup.mem_subgroupOf] using hxQ
  have hKstarM_map_le_Qbar :
      ((section14KStar M K).subgroupOf M).map qM ≤ Qbar := by
    simpa [Qbar, Qloc] using Subgroup.map_mono hKstarM_le_Qloc
  have hKstarM_card :
      Nat.card ((section14KStar M K).subgroupOf M) =
        Nat.card (section14KStar M K) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKstar_le_M).toEquiv
  have hKstarM_map_card :
      Nat.card (((section14KStar M K).subgroupOf M).map qM) =
        Nat.card ((section14KStar M K).subgroupOf M) := by
    simpa [Q0M, qM] using
      section15_natCard_map_mk'_eq_of_le_left_and_disjoint
        (G := M) (H := Q0M) (R := (section14KStar M K).subgroupOf M)
        (N := Q0M) le_rfl hQ0M_KstarM_disj
  have hfixK_card :
      Nat.card (fixedPointSubgroup (↥Ksub) Qbar) = q.val := by
    calc
      Nat.card (fixedPointSubgroup (↥Ksub) Qbar) =
          Nat.card ((((section14KStar M K).subgroupOf M).map qM).subgroupOf Qbar) := by
            rw [hfixK_eq]
      _ = Nat.card (((section14KStar M K).subgroupOf M).map qM) :=
            Nat.card_congr
              (Subgroup.subgroupOfEquivOfLe hKstarM_map_le_Qbar).toEquiv
      _ = Nat.card ((section14KStar M K).subgroupOf M) := hKstarM_map_card
      _ = Nat.card (section14KStar M K) := hKstarM_card
      _ = q.val := hq.symm
  have hmain_card :=
    theorem_3_10_b (G := S) (K := Dsub) (R := Ksub) (M := Qbar)
      hfrob hsolvS hnilQbar hcop hfixD hfixK
  have hKsub_card : Nat.card Ksub = Nat.card K := by
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe
        (H := K) (K := S) (by simp [S])).toEquiv
  have hQbar_card : Nat.card Qbar = q.val ^ p.val := by
    calc
      Nat.card Qbar =
          Nat.card (fixedPointSubgroup (↥Ksub) Qbar) ^ Nat.card Ksub := hmain_card
      _ = q.val ^ Nat.card K := by rw [hfixK_card, hKsub_card]
      _ = q.val ^ p.val := by rw [← hp]
  exact ⟨hQbar_elem, hQbar_card⟩


omit [IsMinCE G] in
public theorem CFSG.section15_local_fitting_le_pCore_sup_pPrimeCore
    {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime] :
    fittingSubgroup H ≤ pCore p H ⊔ pPrimeCore p H := by
  classical
  have hnilF : Group.IsNilpotent (fittingSubgroup H) := by infer_instance
  have hF_le_iSup :
      fittingSubgroup H ≤ ⨆ q : (Nat.card H).primeFactors.attach, pCore q.1 H :=
    normal_nilpotent_le_sup_pCore
      (G := H) (N := fittingSubgroup H) (hN := inferInstance) hnilF
  refine hF_le_iSup.trans ?_
  refine iSup_le ?_
  intro q
  by_cases hqp : q.1 = p
  · subst hqp
    exact le_sup_left
  · have hqprime : Nat.Prime q.1 := Nat.prime_of_mem_primeFactors q.1.2
    letI : Fact (Nat.Prime q.1) := ⟨hqprime⟩
    obtain ⟨n, hn⟩ := (pCore_isPGroup (G := H) (p := q.1)).exists_card_eq
    have hcop : Nat.Coprime p (Nat.card (pCore q.1 H)) := by
      rw [hn]
      have hpq : p ≠ q.1 := by
        intro hpq'
        exact hqp hpq'.symm
      exact ((Nat.coprime_primes (Fact.out : Nat.Prime p) hqprime).2 hpq).pow_right n
    exact
      (le_sSup (show pCore q.1 H ∈ {K : Subgroup H | K.Normal ∧ Nat.Coprime p (Nat.card K)} from
        ⟨inferInstance, hcop⟩)).trans le_sup_right


omit [IsMinCE G] in
private theorem CFSG.section15_fitting_le_pCore_sup_pPrimeCore_map
    (M : Subgroup G) (q : Nat.Primes) :
    section8FittingSubgroup M ≤
      section15PCoreIn q M ⊔ (pPrimeCore q.val M).map M.subtype := by
  classical
  letI : Fact q.val.Prime := ⟨q.property⟩
  have hlocal :
      fittingSubgroup M ≤ pCore q.val M ⊔ pPrimeCore q.val M :=
    section15_local_fitting_le_pCore_sup_pPrimeCore (H := M) (p := q.val)
  have hmap :
      (fittingSubgroup M).map M.subtype ≤
        ((pCore q.val M ⊔ pPrimeCore q.val M : Subgroup M).map M.subtype) :=
    Subgroup.map_mono hlocal
  have htarget :
      ((pCore q.val M ⊔ pPrimeCore q.val M : Subgroup M).map M.subtype) ≤
        section15PCoreIn q M ⊔ (pPrimeCore q.val M).map M.subtype := by
    rw [Subgroup.map_sup]
    exact sup_le
      (by
        simp [section15PCoreIn])
      le_sup_right
  simpa [section8FittingSubgroup, fittingSubgroupOf] using hmap.trans htarget

omit [IsMinCE G] in
private theorem CFSG.section15_fitting_le_Q_sup_centralizer_Q_of_pcore
    {M Q : Subgroup G} (q : Nat.Primes)
    (hQ_eq_pcore : Q = section15PCoreIn q M) :
    section8FittingSubgroup M ≤ Q ⊔ subgroupCentralizerIn M Q := by
  classical
  letI : Fact q.val.Prime := ⟨q.property⟩
  have hfit :
      section8FittingSubgroup M ≤
        section15PCoreIn q M ⊔ (pPrimeCore q.val M).map M.subtype :=
    section15_fitting_le_pCore_sup_pPrimeCore_map M q
  have hpprime_le_cent :
      (pPrimeCore q.val M).map M.subtype ≤ Subgroup.centralizer (Q : Set G) := by
    have hcent :
        (pPrimeCore q.val M).map M.subtype ≤
          Subgroup.centralizer ((section15PCoreIn q M) : Set G) := by
      simpa [section15PCoreIn] using
        (pPrimeCore_map_le_centralizer_pCore_map (G := G) (p := q.val) M)
    simpa [hQ_eq_pcore] using hcent
  have hpprime_le_M : (pPrimeCore q.val M).map M.subtype ≤ M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hpprime_le_C :
      (pPrimeCore q.val M).map M.subtype ≤ subgroupCentralizerIn M Q := by
    intro x hx
    exact ⟨hpprime_le_M hx, hpprime_le_cent hx⟩
  refine hfit.trans (sup_le ?_ ?_)
  · rw [← hQ_eq_pcore]
    exact le_sup_left
  · exact hpprime_le_C.trans le_sup_right

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_Q_sup_centralizer_Q_le_quotient_centralizer
    {M Q N : Subgroup G}
    (_hNM : N ≤ M) (hQM : Q ≤ M) (_hNQ : N ≤ Q)
    (hNnorm : (N.subgroupOf M).Normal)
    (hQbar_comm :
      IsMulCommutative
        ((Q.subgroupOf M).map (QuotientGroup.mk' (N.subgroupOf M)))) :
    Q ⊔ subgroupCentralizerIn M Q ≤
      ((Subgroup.centralizer
        (((Q.subgroupOf M).map (QuotientGroup.mk' (N.subgroupOf M))) :
          Set (M ⧸ N.subgroupOf M))).comap
            (QuotientGroup.mk' (N.subgroupOf M))).map M.subtype := by
  classical
  let Nloc : Subgroup M := N.subgroupOf M
  let qM : M →* M ⧸ Nloc := QuotientGroup.mk' Nloc
  let Qbar : Subgroup (M ⧸ Nloc) := (Q.subgroupOf M).map qM
  haveI : Nloc.Normal := by
    simpa [Nloc] using hNnorm
  haveI : IsMulCommutative Qbar := by
    simpa [Qbar, Nloc, qM] using hQbar_comm
  refine sup_le ?_ ?_
  · intro x hxQ
    let xM : M := ⟨x, hQM hxQ⟩
    refine Subgroup.mem_map.mpr ⟨xM, ?_, rfl⟩
    change qM xM ∈ Subgroup.centralizer (Qbar : Set (M ⧸ Nloc))
    rw [Subgroup.mem_centralizer_iff]
    intro y hyQbar
    have hxQbar : qM xM ∈ Qbar := by
      refine Subgroup.mem_map.mpr ⟨xM, ?_, rfl⟩
      simpa [xM, Subgroup.mem_subgroupOf] using hxQ
    exact
      (setLike_mul_comm
        (s := Qbar) hyQbar hxQbar)
  · intro x hxC
    let xM : M := ⟨x, hxC.1⟩
    refine Subgroup.mem_map.mpr ⟨xM, ?_, rfl⟩
    change qM xM ∈ Subgroup.centralizer (Qbar : Set (M ⧸ Nloc))
    rw [Subgroup.mem_centralizer_iff]
    intro y hyQbar
    rcases Subgroup.mem_map.mp hyQbar with ⟨yM, hyQsub, rfl⟩
    have hyQ : (yM : G) ∈ Q := by
      simpa [Subgroup.mem_subgroupOf] using hyQsub
    have hcommG : (yM : G) * x = x * (yM : G) :=
      Subgroup.mem_centralizer_iff.mp hxC.2 (yM : G) hyQ
    have hcommM : yM * xM = xM * yM := Subtype.ext hcommG
    simpa [qM, map_mul] using congrArg qM hcommM

private theorem CFSG.section15_Qbar_D_centralizer_eq_bot_of_theorem15_2_context
    {M MF K Q D : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMFne : MF ≠ section10Msigma M)
    (hq : q.val = Nat.card (section14KStar M K))
    (hQ : section12SylowSubgroupIn q Q M)
    (hQnormal : section10NormalIn Q M)
    (hQMF : Q ≤ MF)
    (hD : section15Theorem15_2ComplementData M K Q D)
    (hQ₀norm_arg : ((subgroupCentralizerIn Q D).subgroupOf M).Normal) :
    let Q₀ : Subgroup G := subgroupCentralizerIn Q D
    let Q0M : Subgroup M := Q₀.subgroupOf M
    letI : Q0M.Normal := hQ₀norm_arg
    let qM : M →* M ⧸ Q0M := QuotientGroup.mk' Q0M
    let Qbar : Subgroup (M ⧸ Q0M) := (Q.subgroupOf M).map qM
    let Dbar : Subgroup (M ⧸ Q0M) := (D.subgroupOf M).map qM
    subgroupCentralizerIn Qbar Dbar = ⊥ := by
  classical
  let Q₀ : Subgroup G := subgroupCentralizerIn Q D
  rcases section15_Q0_quotient_minimal_normal
      hM hMF hK hMFne hq hQ hQnormal hQMF hD with
    ⟨_hQ₀M, hQM, _hQ₀Q, hQ₀norm, _hQbar_ne, _hQbar_norm, _hQbar_min⟩
  let Q0M : Subgroup M := Q₀.subgroupOf M
  haveI : Q0M.Normal := by
    simpa [Q0M, Q₀] using hQ₀norm_arg
  let qM : M →* M ⧸ Q0M := QuotientGroup.mk' Q0M
  let Qloc : Subgroup M := Q.subgroupOf M
  let Dloc : Subgroup M := D.subgroupOf M
  let Qbar : Subgroup (M ⧸ Q0M) := Qloc.map qM
  let Dbar : Subgroup (M ⧸ Q0M) := Dloc.map qM
  have hDcomp : section12ComplementIn (section10Msigma M) Q D := hD.2.1
  have hD_le_M : D ≤ M := hDcomp.2.1.trans section15_msigma_le
  have hQloc_norm : Qloc.Normal := by
    simpa [Qloc] using hQnormal.2
  have hDloc_norm_Qloc : Dloc ≤ Subgroup.normalizer (Qloc : Set M) :=
    le_top.trans (Subgroup.le_normalizer_of_normal (H := Qloc))
  have hsolvM : Group.IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.2 hM.1)
  have hsolvQloc' :=
    section15_subgroupOf_solvable_of_solvable (G := G) (M := M) (Q := Q) hsolvM
  have hQπ : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) Q :=
    section15_sylowSubgroupIn_isPiSubgroup_singleton hQ
  have hDπ : IsPiSubgroup (G := G) ({q} : Set Nat.Primes)ᶜ D :=
    section15_complement_D_isPiSubgroup_q_compl hQ hQnormal hDcomp
  have hQlocπ :
      IsPiSubgroup (G := M) ({q} : Set Nat.Primes) Qloc := by
    simpa [Qloc] using
      section15_isPiSubgroup_subgroupOf
        (G := G) (H := M) (K := Q) hQπ hQM
  have hDlocπ :
      IsPiSubgroup (G := M) ({q} : Set Nat.Primes)ᶜ Dloc := by
    simpa [Dloc] using
      section15_isPiSubgroup_subgroupOf
        (G := G) (H := M) (K := D) hDπ hD_le_M
  have hπdisj : Disjoint ({q} : Set Nat.Primes) (({q} : Set Nat.Primes)ᶜ) := by
    rw [Set.disjoint_left]
    intro p hpsing hpcompl
    exact hpcompl hpsing
  have hcopQDloc : Nat.Coprime (Nat.card Qloc) (Nat.card Dloc) :=
    section15_coprime_card_of_disjoint_piSubgroups
      (G := M) hπdisj hQlocπ hDlocπ
  have hQ0invDloc :
      ∀ r : Dloc, ∀ x ∈ Q0M, (r : M) * x * (r : M)⁻¹ ∈ Q0M := by
    intro r x hx
    exact (inferInstance : Q0M.Normal).conj_mem x hx r
  have hcent_map :
      subgroupCentralizerIn Qbar Dbar =
        (subgroupCentralizerIn Qloc Dloc).map qM := by
    simpa [Qbar, Dbar, Qloc, Dloc, qM] using
      subgroupCentralizerIn_map_mk'_eq_map_of_solvable_coprime
        (H := Qloc) (R := Dloc) (X := Q0M)
        hDloc_norm_Qloc hsolvQloc' hcopQDloc hQ0invDloc
  have hcent_local_eq :
      subgroupCentralizerIn Qloc Dloc = Q0M := by
    simpa [Qloc, Dloc, Q0M, Q₀] using
      subgroupCentralizerIn_subgroupOf_eq M Q D hD_le_M
  have hQ0_map_bot : Q0M.map qM = ⊥ := by
    apply bot_unique
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨x, hxQ0, rfl⟩
    simpa [qM, QuotientGroup.eq_one_iff] using hxQ0
  calc
    subgroupCentralizerIn Qbar Dbar =
        (subgroupCentralizerIn Qloc Dloc).map qM := hcent_map
    _ = Q0M.map qM := by rw [hcent_local_eq]
    _ = ⊥ := hQ0_map_bot

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_quotient_centralizer_normalIn
    {M Q N : Subgroup G}
    (_hNM : N ≤ M) (_hQM : Q ≤ M)
    (hNnorm : (N.subgroupOf M).Normal)
    (hQbar_norm :
      ((Q.subgroupOf M).map (QuotientGroup.mk' (N.subgroupOf M))).Normal) :
    section10NormalIn
      (((Subgroup.centralizer
        (((Q.subgroupOf M).map (QuotientGroup.mk' (N.subgroupOf M))) :
          Set (M ⧸ N.subgroupOf M))).comap
            (QuotientGroup.mk' (N.subgroupOf M))).map M.subtype)
      M := by
  classical
  let Nloc : Subgroup M := N.subgroupOf M
  haveI : Nloc.Normal := by
    simpa [Nloc] using hNnorm
  let qM : M →* M ⧸ Nloc := QuotientGroup.mk' Nloc
  let Qbar : Subgroup (M ⧸ Nloc) := (Q.subgroupOf M).map qM
  let Cloc : Subgroup M := (Subgroup.centralizer (Qbar : Set (M ⧸ Nloc))).comap qM
  let Cbar : Subgroup G := Cloc.map M.subtype
  haveI : Qbar.Normal := by
    simpa [Qbar, Nloc, qM] using hQbar_norm
  have hCloc_norm : Cloc.Normal := by
    simpa [Cloc] using
      (Subgroup.normal_centralizer (H := Qbar)).comap qM
  have hCbarM : Cbar ≤ M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hsub_eq : Cbar.subgroupOf M = Cloc := by
    ext x
    constructor
    · intro hx
      have hxmap : (x : G) ∈ Cbar := by
        simpa [Subgroup.mem_subgroupOf] using hx
      rcases Subgroup.mem_map.mp hxmap with ⟨y, hy, hyx⟩
      have hy_eq_x : y = x := by
        apply Subtype.ext
        exact hyx
      simpa [hy_eq_x] using hy
    · intro hx
      have hxmap : (x : G) ∈ Cbar := by
        exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      simpa [Subgroup.mem_subgroupOf] using hxmap
  have hsub_norm : (Cbar.subgroupOf M).Normal := by
    rw [hsub_eq]
    exact hCloc_norm
  refine ⟨?_, ?_⟩
  · simpa [Cbar, Cloc, Qbar, Nloc, qM] using hCbarM
  · simpa [Cbar, Cloc, Qbar, Nloc, qM] using hsub_norm

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_le_normalizer_quotient_centralizer
    {H N A R : Subgroup G}
    (_hNH : N ≤ H) (hAH : A ≤ H)
    (hNnorm : (N.subgroupOf H).Normal)
    (hRH : R ≤ Subgroup.normalizer (H : Set G))
    (hRN : R ≤ Subgroup.normalizer (N : Set G))
    (hRA : R ≤ Subgroup.normalizer (A : Set G)) :
    R ≤
      Subgroup.normalizer
        ((((Subgroup.centralizer
          (((A.subgroupOf H).map (QuotientGroup.mk' (N.subgroupOf H))) :
            Set (H ⧸ N.subgroupOf H))).comap
              (QuotientGroup.mk' (N.subgroupOf H))).map H.subtype) : Set G) := by
  classical
  let Nloc : Subgroup H := N.subgroupOf H
  haveI : Nloc.Normal := by
    simpa [Nloc] using hNnorm
  let qH : H →* H ⧸ Nloc := QuotientGroup.mk' Nloc
  let Abar : Subgroup (H ⧸ Nloc) := (A.subgroupOf H).map qH
  let C : Subgroup G :=
    ((Subgroup.centralizer (Abar : Set (H ⧸ Nloc))).comap qH).map H.subtype
  have hconj_mem :
      ∀ r ∈ R, ∀ x ∈ C, r * x * r⁻¹ ∈ C := by
    intro r hr x hxC
    have hrH : r ∈ Subgroup.normalizer (H : Set G) := hRH hr
    have hrN : r ∈ Subgroup.normalizer (N : Set G) := hRN hr
    have hrA : r ∈ Subgroup.normalizer (A : Set G) := hRA hr
    rcases Subgroup.mem_map.mp hxC with ⟨xH, hxcent, hx⟩
    have hxH_eq : (xH : G) = x := hx
    have hconjH : r * x * r⁻¹ ∈ H := by
      have hxH : x ∈ H := by
        rw [← hxH_eq]
        exact xH.property
      exact (Subgroup.mem_normalizer_iff.mp hrH x).1 hxH
    let rxH : H := ⟨r * x * r⁻¹, hconjH⟩
    refine Subgroup.mem_map.mpr ⟨rxH, ?_, rfl⟩
    change qH rxH ∈ Subgroup.centralizer (Abar : Set (H ⧸ Nloc))
    rw [Subgroup.mem_centralizer_iff]
    intro y hyAbar
    rcases Subgroup.mem_map.mp hyAbar with ⟨aH, haA, rfl⟩
    have haG : (aH : G) ∈ A := by
      simpa [Subgroup.mem_subgroupOf] using haA
    have hrinvA : r⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
      (Subgroup.normalizer (A : Set G)).inv_mem hrA
    have ha_conj_A : r⁻¹ * (aH : G) * r ∈ A := by
      simpa [mul_assoc] using
        (Subgroup.mem_normalizer_iff.mp hrinvA (aH : G)).1 haG
    let a' : H := ⟨r⁻¹ * (aH : G) * r, hAH ha_conj_A⟩
    have ha'bar : qH a' ∈ Abar := by
      exact Subgroup.mem_map.mpr
        ⟨a', by simpa [a', Subgroup.mem_subgroupOf] using ha_conj_A, rfl⟩
    have hcomm :
        qH a' * qH xH = qH xH * qH a' :=
      Subgroup.mem_centralizer_iff.mp hxcent (qH a') ha'bar
    rw [← map_mul, ← map_mul]
    apply (QuotientGroup.eq_iff_div_mem (N := Nloc)).2
    have hdelta : a' * xH / (xH * a') ∈ Nloc := by
      apply (QuotientGroup.eq_iff_div_mem (N := Nloc)).1
      change qH (a' * xH) = qH (xH * a')
      simpa only [map_mul] using hcomm
    have hdeltaG : (((a' * xH / (xH * a') : H) : G)) ∈ N := by
      simpa [Nloc, Subgroup.mem_subgroupOf] using hdelta
    have hconjN :
        r * (((a' * xH / (xH * a') : H) : G)) * r⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp hrN
        (((a' * xH / (xH * a') : H) : G))).1 hdeltaG
    have htarget_eq :
        (((aH * rxH / (rxH * aH) : H) : G)) =
          r * (((a' * xH / (xH * a') : H) : G)) * r⁻¹ := by
      dsimp [a', rxH]
      rw [hxH_eq]
      simp [div_eq_mul_inv, mul_assoc]
    have htargetG : (((aH * rxH / (rxH * aH) : H) : G)) ∈ N := by
      rw [htarget_eq]
      exact hconjN
    simpa [Nloc, Subgroup.mem_subgroupOf] using htargetG
  intro r hr
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    simpa [C, Abar, Nloc, qH] using hconj_mem r hr x (by simpa [C, Abar, Nloc, qH] using hx)
  · intro hx
    have hback :
        r⁻¹ * (r * x * r⁻¹) * (r⁻¹)⁻¹ ∈ C :=
      hconj_mem r⁻¹ ((R : Subgroup G).inv_mem hr) (r * x * r⁻¹)
        (by simpa [C, Abar, Nloc, qH] using hx)
    have hsimp : r⁻¹ * (r * x * r⁻¹) * (r⁻¹)⁻¹ = x := by
      group
    rw [hsimp] at hback
    simpa [C, Abar, Nloc, qH] using hback

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_quotient_centralizer_le_of_minimal_normal
    {M Q N A C : Subgroup G}
    (_hNM : N ≤ M) (_hQM : Q ≤ M) (_hAM : A ≤ M) (hCM : C ≤ M)
    (hAQ : A ≤ Q)
    (hNnorm : (N.subgroupOf M).Normal)
    (hQbar_norm :
      ((Q.subgroupOf M).map (QuotientGroup.mk' (N.subgroupOf M))).Normal)
    (hQbar_min :
      ∀ R : Subgroup (M ⧸ N.subgroupOf M),
        R.Normal →
          R ≤ (Q.subgroupOf M).map (QuotientGroup.mk' (N.subgroupOf M)) →
            R = ⊥ ∨ R = (Q.subgroupOf M).map (QuotientGroup.mk' (N.subgroupOf M)))
    (hAbar_ne :
      (A.subgroupOf M).map (QuotientGroup.mk' (N.subgroupOf M)) ≠ ⊥)
    (hCnorm : (C.subgroupOf M).Normal)
    (hC_le_CbarA :
      C ≤
        ((Subgroup.centralizer
          (((A.subgroupOf M).map (QuotientGroup.mk' (N.subgroupOf M))) :
            Set (M ⧸ N.subgroupOf M))).comap
              (QuotientGroup.mk' (N.subgroupOf M))).map M.subtype) :
    C ≤
      ((Subgroup.centralizer
        (((Q.subgroupOf M).map (QuotientGroup.mk' (N.subgroupOf M))) :
          Set (M ⧸ N.subgroupOf M))).comap
            (QuotientGroup.mk' (N.subgroupOf M))).map M.subtype := by
  classical
  let Nloc : Subgroup M := N.subgroupOf M
  haveI : Nloc.Normal := by
    simpa [Nloc] using hNnorm
  let qM : M →* M ⧸ Nloc := QuotientGroup.mk' Nloc
  let Qbar : Subgroup (M ⧸ Nloc) := (Q.subgroupOf M).map qM
  let Abar : Subgroup (M ⧸ Nloc) := (A.subgroupOf M).map qM
  let Cbar : Subgroup (M ⧸ Nloc) := (C.subgroupOf M).map qM
  let Qfix : Subgroup (M ⧸ Nloc) := subgroupCentralizerIn Qbar Cbar
  haveI : Qbar.Normal := by
    simpa [Qbar, Nloc, qM] using hQbar_norm
  haveI : Cbar.Normal := by
    simpa [Cbar, Nloc, qM] using
      Subgroup.Normal.map hCnorm qM (QuotientGroup.mk'_surjective (N := Nloc))
  have hQfix_norm : Qfix.Normal := by
    haveI : (Subgroup.centralizer (Cbar : Set (M ⧸ Nloc))).Normal :=
      Subgroup.normal_centralizer (H := Cbar)
    change (Qbar ⊓ Subgroup.centralizer (Cbar : Set (M ⧸ Nloc))).Normal
    infer_instance
  have hAbar_le_Qbar : Abar ≤ Qbar := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨aM, haA, rfl⟩
    have haQ : (aM : G) ∈ Q := by
      exact hAQ (by simpa [Subgroup.mem_subgroupOf] using haA)
    exact Subgroup.mem_map.mpr
      ⟨aM, by simpa [Subgroup.mem_subgroupOf] using haQ, rfl⟩
  have hAbar_le_centCbar :
      Abar ≤ Subgroup.centralizer (Cbar : Set (M ⧸ Nloc)) := by
    intro y hyA
    rw [Subgroup.mem_centralizer_iff]
    intro z hzC
    rcases Subgroup.mem_map.mp hzC with ⟨cM, hcC, rfl⟩
    have hcG : (cM : G) ∈ C := by
      simpa [Subgroup.mem_subgroupOf] using hcC
    have hcA :
        (cM : G) ∈
          ((Subgroup.centralizer (Abar : Set (M ⧸ Nloc))).comap qM).map M.subtype := by
      simpa [Abar, Nloc, qM] using hC_le_CbarA hcG
    rcases Subgroup.mem_map.mp hcA with ⟨dM, hdcent, hdc⟩
    have hd_eq : dM = cM := by
      apply Subtype.ext
      exact hdc
    have hc_cent : qM cM ∈ Subgroup.centralizer (Abar : Set (M ⧸ Nloc)) := by
      simpa [hd_eq] using hdcent
    exact (Subgroup.mem_centralizer_iff.mp hc_cent y hyA).symm
  have hAbar_le_Qfix : Abar ≤ Qfix := by
    intro y hy
    exact ⟨hAbar_le_Qbar hy, hAbar_le_centCbar hy⟩
  have hQfix_ne : Qfix ≠ ⊥ := by
    intro hbot
    apply hAbar_ne
    apply bot_unique
    intro y hyA
    have hyQfix : y ∈ Qfix := hAbar_le_Qfix hyA
    simpa [hbot] using hyQfix
  have hQfix_eq : Qfix = Qbar := by
    have hmin := hQbar_min Qfix hQfix_norm (by
      intro y hy
      exact hy.1)
    rcases hmin with hbot | htop
    · exact False.elim (hQfix_ne hbot)
    · exact htop
  intro x hxC
  have hxM : x ∈ M := hCM hxC
  let xM : M := ⟨x, hxM⟩
  refine Subgroup.mem_map.mpr ⟨xM, ?_, rfl⟩
  change qM xM ∈ Subgroup.centralizer (Qbar : Set (M ⧸ Nloc))
  rw [Subgroup.mem_centralizer_iff]
  intro y hyQ
  have hyFix : y ∈ Qfix := by
    rw [hQfix_eq]
    exact hyQ
  have hyCent : y ∈ Subgroup.centralizer (Cbar : Set (M ⧸ Nloc)) := hyFix.2
  have hxCbar : qM xM ∈ Cbar := by
    exact Subgroup.mem_map.mpr
      ⟨xM, by simpa [xM, Subgroup.mem_subgroupOf] using hxC, rfl⟩
  exact (Subgroup.mem_centralizer_iff.mp hyCent (qM xM) hxCbar).symm

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_Q_sup_D_centralizer_Q_nilpotent
    {M Q D : Subgroup G}
    (hDcomp : section12ComplementIn (section10Msigma M) Q D)
    (hQnormal : section10NormalIn Q M)
    (hQnil : Group.IsNilpotent Q)
    (hDnil : Group.IsNilpotent D) :
    Group.IsNilpotent (↥(Q ⊔ subgroupCentralizerIn D Q)) := by
  classical
  let E : Subgroup G := subgroupCentralizerIn D Q
  let S : Subgroup G := Q ⊔ E
  have hE_le_D : E ≤ D := by
    intro x hx
    exact hx.1
  have hE_le_sigma : E ≤ section10Msigma M := hE_le_D.trans hDcomp.2.1
  have hS_le_M : S ≤ M := by
    exact sup_le hQnormal.1 (hE_le_sigma.trans section15_msigma_le)
  have hcomp : section12ComplementIn S Q E := by
    refine ⟨le_sup_left, le_sup_right, rfl, ?_⟩
    rw [Subgroup.disjoint_def]
    intro x hxQ hxE
    exact Subgroup.disjoint_def.mp hDcomp.2.2.2 hxQ (hE_le_D hxE)
  have hQnormS : section10NormalIn Q S := by
    have hM_norm_Q : M ≤ Subgroup.normalizer (Q : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQnormal.1).1 hQnormal.2
    have hS_norm_Q : S ≤ Subgroup.normalizer (Q : Set G) :=
      hS_le_M.trans hM_norm_Q
    refine ⟨le_sup_left, ?_⟩
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (show Q ≤ S by exact le_sup_left)).2
      hS_norm_Q
  have hEnil : Group.IsNilpotent E := by
    let Eloc : Subgroup D := E.subgroupOf D
    have hEloc_nil : Group.IsNilpotent Eloc := by
      letI : Group.IsNilpotent D := hDnil
      infer_instance
    let e : Eloc ≃* E := Subgroup.subgroupOfEquivOfLe (H := E) (K := D) hE_le_D
    exact Group.nilpotent_of_mulEquiv (G := Eloc) (G' := E) (_h := hEloc_nil) e
  have hQcentE : Q ≤ Subgroup.centralizer (E : Set G) := by
    intro x hxQ
    rw [Subgroup.mem_centralizer_iff]
    intro y hyE
    exact (Subgroup.mem_centralizer_iff.mp hyE.2 x hxQ).symm
  simpa [S, E] using
    section15_nilpotent_of_central_complement hcomp hQnormS hQnil hEnil hQcentE

private theorem CFSG.section15_quotient_centralizer_le_fitting_of_theorem15_2_context
    {M MF K Q D : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMFne : MF ≠ section10Msigma M)
    (hq : q.val = Nat.card (section14KStar M K))
    (hQ : section12SylowSubgroupIn q Q M)
    (hQnormal : section10NormalIn Q M)
    (hQMF : Q ≤ MF)
    (hD : section15Theorem15_2ComplementData M K Q D)
    (hQ₀norm : ((subgroupCentralizerIn Q D).subgroupOf M).Normal) :
    let Q₀ : Subgroup G := subgroupCentralizerIn Q D
    letI : (Q₀.subgroupOf M).Normal := hQ₀norm
    ((Subgroup.centralizer
      (((Q.subgroupOf M).map (QuotientGroup.mk' (Q₀.subgroupOf M))) :
        Set (M ⧸ Q₀.subgroupOf M))).comap
          (QuotientGroup.mk' (Q₀.subgroupOf M))).map M.subtype
      ≤ section8FittingSubgroup M ∧
    ((Subgroup.centralizer
      (((Q.subgroupOf M).map (QuotientGroup.mk' (Q₀.subgroupOf M))) :
        Set (M ⧸ Q₀.subgroupOf M))).comap
          (QuotientGroup.mk' (Q₀.subgroupOf M))).map M.subtype
      ≤ section10Msigma M := by
  classical
  let Q₀ : Subgroup G := subgroupCentralizerIn Q D
  let Q0M : Subgroup M := Q₀.subgroupOf M
  haveI : Q0M.Normal := by
    simpa [Q0M, Q₀] using hQ₀norm
  let qM : M →* M ⧸ Q0M := QuotientGroup.mk' Q0M
  let Qbar : Subgroup (M ⧸ Q0M) := (Q.subgroupOf M).map qM
  let Cbar : Subgroup G :=
    ((Subgroup.centralizer (Qbar : Set (M ⧸ Q0M))).comap qM).map M.subtype
  rcases section15_Q0_quotient_minimal_normal
      hM hMF hK hMFne hq hQ hQnormal hQMF hD with
    ⟨hQ₀M, hQM, hQ₀Q, _hQ₀norm', hQbar_ne, hQbar_norm, _hQbar_min⟩
  have hCbar_norm : section10NormalIn Cbar M := by
    simpa [Cbar, Qbar, Q0M, qM, Q₀] using
      section15_quotient_centralizer_normalIn
        (M := M) (Q := Q) (N := Q₀) hQ₀M hQM hQ₀norm hQbar_norm
  rcases section15_p_card_prime_of_theorem15_2_context
      hM hMF hK hMFne hq hQ hQnormal hQMF hD with
    ⟨p, hp⟩
  rcases section15_Qbar_elementary_card
      hM hMF hK hMFne hp hq hQ hQnormal hQMF hD with
    ⟨_hQ₀M', _hQM', _hQ₀Q', _hQ₀norm'', hQbar_elem, _hQbar_card⟩
  have hQbar_comm : IsMulCommutative Qbar := by
    letI : IsElementaryAbelian q.val Qbar := by
      simpa [Qbar, Q0M, qM, Q₀] using hQbar_elem
    infer_instance
  have hCbar_le_QE :
      Cbar ≤ Q ⊔ subgroupCentralizerIn D Q := by
    have hCbar_le_sigma_direct : Cbar ≤ section10Msigma M := by
      let S : Subgroup G := D ⊔ K
      let Dsub : Subgroup S := D.subgroupOf S
      let Ksub : Subgroup S := K.subgroupOf S
      haveI : Qbar.Normal := by
        simpa [Qbar, Q0M, qM, Q₀] using hQbar_norm
      haveI : Nontrivial Qbar := by
        exact Qbar.nontrivial_iff_ne_bot.mpr (by simpa [Qbar] using hQbar_ne)
      have hDcomp : section12ComplementIn (section10Msigma M) Q D := hD.2.1
      have hD_le_M : D ≤ M := hDcomp.2.1.trans section15_msigma_le
      have hMF_le_sigma : MF ≤ section10Msigma M := section15_MF_le_msigma hM hMF
      have hQ_le_sigma : Q ≤ section10Msigma M := hQMF.trans hMF_le_sigma
      have hS_le_M : S ≤ M := by
        simpa [S] using sup_le hD_le_M hK.1
      let toQ : S →* M ⧸ Q0M :=
        (QuotientGroup.mk' Q0M).comp (Subgroup.inclusion hS_le_M)
      let toTop : (M ⧸ Q0M) →* (⊤ : Subgroup (M ⧸ Q0M)) :=
        { toFun := fun x => ⟨x, by simp⟩
          map_one' := by ext; simp
          map_mul' := by intro x y; ext; simp }
      letI : MulDistribMulAction (M ⧸ Q0M) Qbar :=
        MulDistribMulAction.compHom Qbar toTop
      letI : MulDistribMulAction S Qbar :=
        MulDistribMulAction.compHom Qbar toQ
      have hfrob :
          IsFrobeniusGroupWithKernelComplement Dsub Ksub := by
        simpa [Dsub, Ksub, S] using
          section15_KD_frobenius_with_kernel_D
            hM hMF hK hMFne hq hQ hQnormal hD
      have hDsub_solv : Group.IsSolvable Dsub := by
        have hDsolv : Group.IsSolvable D := by
          letI : Group.IsNilpotent D := hD.2.2.1
          infer_instance
        let e : Dsub ≃* D :=
          Subgroup.subgroupOfEquivOfLe
            (H := D) (K := S) (by simp [S])
        exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
      let Qloc : Subgroup M := Q.subgroupOf M
      let Dloc : Subgroup M := D.subgroupOf M
      let Dbar : Subgroup (M ⧸ Q0M) := Dloc.map qM
      have hmap_subgroupOf (A : Subgroup G) (hAS : A ≤ S) (hAM : A ≤ M) :
          (A.subgroupOf S).map toQ = (A.subgroupOf M).map qM := by
        ext z
        constructor
        · intro hz
          rcases Subgroup.mem_map.mp hz with ⟨aS, haA, rfl⟩
          have haAamb : (aS : G) ∈ A := by
            simpa [Subgroup.mem_subgroupOf] using haA
          let aM : M := ⟨(aS : G), hAM haAamb⟩
          have haM : aM ∈ A.subgroupOf M := by
            simpa [aM, Subgroup.mem_subgroupOf] using haAamb
          refine Subgroup.mem_map.mpr ⟨aM, haM, ?_⟩
          have ha_eq : aM = Subgroup.inclusion hS_le_M aS := by
            apply Subtype.ext
            rfl
          simpa [toQ, qM, aM] using congrArg qM ha_eq
        · intro hz
          rcases Subgroup.mem_map.mp hz with ⟨aM, haA, rfl⟩
          have haAamb : (aM : G) ∈ A := by
            simpa [Subgroup.mem_subgroupOf] using haA
          let aS : S := ⟨(aM : G), hAS haAamb⟩
          have haS : aS ∈ A.subgroupOf S := by
            simpa [aS, Subgroup.mem_subgroupOf] using haAamb
          refine Subgroup.mem_map.mpr ⟨aS, haS, ?_⟩
          have ha_eq : Subgroup.inclusion hS_le_M aS = aM := by
            apply Subtype.ext
            rfl
          simpa [toQ, qM, aS] using congrArg qM ha_eq
      have hfix_toQ_eq (A : Subgroup S) :
          fixedPointSubgroup (↥A) Qbar =
            (subgroupCentralizerIn Qbar (A.map toQ)).subgroupOf Qbar := by
        ext y
        constructor
        · intro hy
          refine ⟨y.2, ?_⟩
          change (y : M ⧸ Q0M) ∈
            Subgroup.centralizer (A.map toQ : Set (M ⧸ Q0M))
          rw [Subgroup.mem_centralizer_iff]
          intro z hz
          rcases Subgroup.mem_map.mp hz with ⟨a, haA, rfl⟩
          have hyfix : (⟨a, haA⟩ : A) • y = y := by
            rw [fixedPointSubgroup, FixedPoints.mem_subgroup] at hy
            exact hy ⟨a, haA⟩
          have hconj :
              toQ a * (y : M ⧸ Q0M) * (toQ a)⁻¹ = y := by
            have hval := congrArg Subtype.val hyfix
            change toQ a * (y : M ⧸ Q0M) * (toQ a)⁻¹ = (y : M ⧸ Q0M) at hval
            exact hval
          exact mul_inv_eq_iff_eq_mul.mp hconj
        · intro hy
          rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
          intro a
          have hcomm :
              toQ (a : S) * (y : M ⧸ Q0M) =
                (y : M ⧸ Q0M) * toQ (a : S) := by
            have hyc :
                (y : M ⧸ Q0M) ∈
                  Subgroup.centralizer (A.map toQ : Set (M ⧸ Q0M)) := hy.2
            exact Subgroup.mem_centralizer_iff.mp hyc (toQ (a : S))
              (Subgroup.mem_map.mpr ⟨(a : S), a.property, rfl⟩)
          have hconj :
              toQ (a : S) * (y : M ⧸ Q0M) * (toQ (a : S))⁻¹ = y := by
            exact mul_inv_eq_iff_eq_mul.mpr hcomm
          apply Subtype.ext
          change toQ (a : S) * (y : M ⧸ Q0M) * (toQ (a : S))⁻¹ =
            (y : M ⧸ Q0M)
          exact hconj
      have hDbar_eq : Dsub.map toQ = Dbar := by
        simpa [Dsub, Dloc, Dbar] using
          hmap_subgroupOf D (by simp [S]) hD_le_M
      have hcent_D_bot : subgroupCentralizerIn Qbar Dbar = ⊥ := by
        simpa [Qbar, Dbar, Qloc, Dloc, Q0M, qM, Q₀] using
          section15_Qbar_D_centralizer_eq_bot_of_theorem15_2_context
            hM hMF hK hMFne hq hQ hQnormal hQMF hD hQ₀norm
      have hfixD : fixedPointSubgroup (↥Dsub) Qbar = ⊥ := by
        have hfix_eq :
            fixedPointSubgroup (↥Dsub) Qbar =
              (subgroupCentralizerIn Qbar Dbar).subgroupOf Qbar := by
          calc
            fixedPointSubgroup (↥Dsub) Qbar =
                (subgroupCentralizerIn Qbar (Dsub.map toQ)).subgroupOf Qbar :=
              hfix_toQ_eq Dsub
            _ = (subgroupCentralizerIn Qbar Dbar).subgroupOf Qbar := by
              rw [hDbar_eq]
        simp [hfix_eq, hcent_D_bot]
      let N : Subgroup S := (MulDistribMulAction.toMulAut S Qbar).ker
      haveI : N.Normal := by
        dsimp [N]
        infer_instance
      have hD_not_le_N : ¬ Dsub ≤ N := by
        intro hDleN
        have hfix_top : fixedPointSubgroup (↥Dsub) Qbar = ⊤ := by
          apply le_antisymm le_top
          intro y _hy
          rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
          intro d
          have hdN : (d : S) ∈ N := hDleN d.property
          have hdker : MulDistribMulAction.toMulAut S Qbar (d : S) = 1 := by
            exact MonoidHom.mem_ker.mp (by simpa [N] using hdN)
          have hact := congrArg (fun f : MulAut Qbar => f y) hdker
          change (d : S) • y = y
          exact hact
        have htop_bot : (⊤ : Subgroup Qbar) = ⊥ := hfix_top.symm.trans hfixD
        exact (top_ne_bot : (⊤ : Subgroup Qbar) ≠ (⊥ : Subgroup Qbar)) htop_bot
      have hker_le_D : N ≤ Dsub :=
        lemma_3_2_a (G := S) (K := Dsub) (R := Ksub) (N := N)
          hfrob hDsub_solv hD_not_le_N
      intro x hxCbar
      have hxM : x ∈ M := hCbar_norm.1 hxCbar
      let xM : M := ⟨x, hxM⟩
      have hxcent : qM xM ∈ Subgroup.centralizer (Qbar : Set (M ⧸ Q0M)) := by
        rcases Subgroup.mem_map.mp hxCbar with ⟨yM, hycent, hyx⟩
        have hy_eq : yM = xM := by
          apply Subtype.ext
          exact hyx
        simpa [Cbar, xM, hy_eq] using hycent
      have hM_eq_Ksigma : M = K ⊔ section10Msigma M :=
        (section15_MF_ne_msigma_implies_P1 hM hMF hK hMFne).2
      let KlocM : Subgroup M := K.subgroupOf M
      let SiglocM : Subgroup M := (section10Msigma M).subgroupOf M
      haveI : SiglocM.Normal := by
        simpa [SiglocM] using (section15_msigma_normalIn (M := M)).2
      have hKsigma_top : KlocM ⊔ SiglocM = ⊤ := by
        calc
          KlocM ⊔ SiglocM = (K ⊔ section10Msigma M).subgroupOf M := by
            symm
            exact Subgroup.subgroupOf_sup (A := K) (A' := section10Msigma M)
              (B := M) hK.1 section15_msigma_le
          _ = ⊤ := by
            rw [← hM_eq_Ksigma]
            simp
      have hxSigmaKloc : xM ∈ SiglocM ⊔ KlocM := by
        rw [sup_comm, hKsigma_top]
        simp
      rcases (Subgroup.mem_sup_of_normal_left (s := SiglocM) (t := KlocM)
          (x := xM)).1 hxSigmaKloc with
        ⟨sgM, hsgSigmaLoc, kgM, hkgKloc, hsgkgM⟩
      let sg : G := sgM
      let kg : G := kgM
      have hsgSigma : sg ∈ section10Msigma M := by
        simpa [sg, SiglocM, Subgroup.mem_subgroupOf] using hsgSigmaLoc
      have hkgK : kg ∈ K := by
        simpa [kg, KlocM, Subgroup.mem_subgroupOf] using hkgKloc
      have hsgkg : sg * kg = x := by
        simpa [sg, kg, xM] using congrArg (fun y : M => (y : G)) hsgkgM
      let DlocM : Subgroup M := D.subgroupOf M
      haveI : Qloc.Normal := by
        simpa [Qloc] using hQnormal.2
      have hQD_local : Qloc ⊔ DlocM = (Q ⊔ D).subgroupOf M := by
        symm
        exact Subgroup.subgroupOf_sup (A := Q) (A' := D) (B := M) hQM hD_le_M
      have hsgQDloc : sgM ∈ Qloc ⊔ DlocM := by
        have hsgQDamb : sg ∈ Q ⊔ D := by
          rw [← hDcomp.2.2.1]
          exact hsgSigma
        have hsgSub : sgM ∈ (Q ⊔ D).subgroupOf M := by
          simpa [sg, Subgroup.mem_subgroupOf] using hsgQDamb
        simpa [hQD_local] using hsgSub
      rcases (Subgroup.mem_sup_of_normal_left (s := Qloc) (t := DlocM)
          (x := sgM)).1 hsgQDloc with
        ⟨qgM', hqgQloc, dgM', hdgDloc, hqgdM⟩
      let qg : G := qgM'
      let dg : G := dgM'
      have hqgQ : qg ∈ Q := by
        simpa [qg, Qloc, Subgroup.mem_subgroupOf] using hqgQloc
      have hdgD : dg ∈ D := by
        simpa [dg, DlocM, Subgroup.mem_subgroupOf] using hdgDloc
      have hqgd : qg * dg = sg := by
        simpa [qg, dg, sg] using congrArg (fun y : M => (y : G)) hqgdM
      have hx_eq_qs : qg * (dg * kg) = x := by
        calc
          qg * (dg * kg) = (qg * dg) * kg := by rw [mul_assoc]
          _ = sg * kg := by rw [hqgd]
          _ = x := hsgkg
      let qgM : M := ⟨qg, hQM hqgQ⟩
      let sS : S := ⟨dg * kg,
        (S.mul_mem
          (by simpa [S] using (Subgroup.mem_sup_left hdgD : dg ∈ D ⊔ K))
          (by simpa [S] using (Subgroup.mem_sup_right hkgK : kg ∈ D ⊔ K)))⟩
      let sM : M := ⟨dg * kg, M.mul_mem (hD_le_M hdgD) (hK.1 hkgK)⟩
      have hqgsM : qgM * sM = xM := by
        apply Subtype.ext
        simpa [qgM, sM, xM] using hx_eq_qs
      have hqgQbar : qM qgM ∈ Qbar := by
        refine Subgroup.mem_map.mpr ⟨qgM, ?_, rfl⟩
        simpa [qgM, Qloc, Subgroup.mem_subgroupOf] using hqgQ
      have hqg_cent : qM qgM ∈ Subgroup.centralizer (Qbar : Set (M ⧸ Q0M)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hyQbar
        exact setLike_mul_comm
          (s := Qbar) hyQbar hqgQbar
      let Cq : Subgroup (M ⧸ Q0M) := Subgroup.centralizer (Qbar : Set (M ⧸ Q0M))
      have hsbar_cent : qM sM ∈ Cq := by
        have hprod : qM qgM * qM sM ∈ Cq := by
          have hprod_eq : qM qgM * qM sM = qM xM := by
            rw [← map_mul, hqgsM]
          simpa [Cq, hprod_eq] using hxcent
        have hmem : (qM qgM)⁻¹ * (qM qgM * qM sM) ∈ Cq :=
          Cq.mul_mem (Cq.inv_mem (by simpa [Cq] using hqg_cent)) hprod
        simpa [Cq, mul_assoc] using hmem
      have hs_toQ : toQ sS = qM sM := by
        have hsM_eq : Subgroup.inclusion hS_le_M sS = sM := by
          apply Subtype.ext
          rfl
        change qM (Subgroup.inclusion hS_le_M sS) = qM sM
        exact congrArg qM hsM_eq
      have hs_cent : toQ sS ∈ Subgroup.centralizer (Qbar : Set (M ⧸ Q0M)) := by
        simpa [hs_toQ] using (by simpa [Cq] using hsbar_cent)
      have hsN : sS ∈ N := by
        change sS ∈ (MulDistribMulAction.toMulAut S Qbar).ker
        rw [MonoidHom.mem_ker]
        ext y
        change toQ sS * (y : M ⧸ Q0M) * (toQ sS)⁻¹ = (y : M ⧸ Q0M)
        have hcomm_y :
            (y : M ⧸ Q0M) * toQ sS = toQ sS * (y : M ⧸ Q0M) :=
          Subgroup.mem_centralizer_iff.mp hs_cent (y : M ⧸ Q0M) y.property
        exact mul_inv_eq_iff_eq_mul.mpr hcomm_y.symm
      have hsDsub : sS ∈ Dsub := hker_le_D hsN
      have hsD : (sS : G) ∈ D := by
        simpa [Dsub, Subgroup.mem_subgroupOf] using hsDsub
      have hx_eq_qsS : qg * (sS : G) = x := by
        simpa [sS] using hx_eq_qs
      have hxQD : x ∈ Q ⊔ D := by
        rw [← hx_eq_qsS]
        exact (Q ⊔ D).mul_mem (Subgroup.mem_sup_left hqgQ)
          (Subgroup.mem_sup_right hsD)
      simpa [hDcomp.2.2.1] using hxQD
    have hDcomp : section12ComplementIn (section10Msigma M) Q D := hD.2.1
    have hD_le_M : D ≤ M := hDcomp.2.1.trans section15_msigma_le
    have hsolvM : Group.IsSolvable M :=
      IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.2 hM.1)
    let Qloc : Subgroup M := Q.subgroupOf M
    have hsolvQloc : Group.IsSolvable Qloc := by
      simpa [Qloc] using
        section15_subgroupOf_solvable_of_solvable (G := G) (M := M) (Q := Q) hsolvM
    have hQπ : IsPiSubgroup (G := G) ({q} : Set Nat.Primes) Q :=
      section15_sylowSubgroupIn_isPiSubgroup_singleton hQ
    have hDπ : IsPiSubgroup (G := G) ({q} : Set Nat.Primes)ᶜ D :=
      section15_complement_D_isPiSubgroup_q_compl hQ hQnormal hDcomp
    have hQlocπ :
        IsPiSubgroup (G := M) ({q} : Set Nat.Primes) Qloc := by
      simpa [Qloc] using
        section15_isPiSubgroup_subgroupOf
          (G := G) (H := M) (K := Q) hQπ hQM
    have hDlocπ :
        IsPiSubgroup (G := M) ({q} : Set Nat.Primes)ᶜ (D.subgroupOf M) := by
      simpa using
        section15_isPiSubgroup_subgroupOf
          (G := G) (H := M) (K := D) hDπ hD_le_M
    have hπdisj : Disjoint ({q} : Set Nat.Primes) (({q} : Set Nat.Primes)ᶜ) := by
      rw [Set.disjoint_left]
      intro r hrsing hrcompl
      exact hrcompl hrsing
    intro x hxCbar
    have hxSigma : x ∈ section10Msigma M := hCbar_le_sigma_direct hxCbar
    have hxM : x ∈ M := section15_msigma_le hxSigma
    let xM : M := ⟨x, hxM⟩
    let Dloc : Subgroup M := D.subgroupOf M
    haveI : Qloc.Normal := by
      simpa [Qloc] using hQnormal.2
    have hQD_local : Qloc ⊔ Dloc = (Q ⊔ D).subgroupOf M := by
      symm
      exact Subgroup.subgroupOf_sup (A := Q) (A' := D) (B := M) hQM hD_le_M
    have hxQDloc : xM ∈ Qloc ⊔ Dloc := by
      have hxQDamb : x ∈ Q ⊔ D := by
        rw [← hDcomp.2.2.1]
        exact hxSigma
      have hxSub : xM ∈ (Q ⊔ D).subgroupOf M := by
        simpa [xM, Subgroup.mem_subgroupOf] using hxQDamb
      simpa [hQD_local] using hxSub
    rcases (Subgroup.mem_sup_of_normal_left (s := Qloc) (t := Dloc)
        (x := xM)).1 hxQDloc with
      ⟨qgM0, hqgQloc, dgM0, hdgDloc, hqdM0⟩
    let qg : G := qgM0
    let dg : G := dgM0
    have hqgQ : qg ∈ Q := by
      simpa [qg, Qloc, Subgroup.mem_subgroupOf] using hqgQloc
    have hdgD : dg ∈ D := by
      simpa [dg, Dloc, Subgroup.mem_subgroupOf] using hdgDloc
    have hqd : qg * dg = x := by
      simpa [qg, dg, xM] using congrArg (fun y : M => (y : G)) hqdM0
    have hxcent : qM xM ∈ Subgroup.centralizer (Qbar : Set (M ⧸ Q0M)) := by
      rcases Subgroup.mem_map.mp hxCbar with ⟨yM, hycent, hyx⟩
      have hy_eq : yM = xM := by
        apply Subtype.ext
        exact hyx
      simpa [Cbar, xM, hy_eq] using hycent
    let qgM : M := ⟨qg, hQM hqgQ⟩
    let dgM : M := ⟨dg, hD_le_M hdgD⟩
    have hqdM : qgM * dgM = xM := by
      apply Subtype.ext
      simpa [qgM, dgM, xM] using hqd
    have hqgQbar : qM qgM ∈ Qbar := by
      refine Subgroup.mem_map.mpr ⟨qgM, ?_, rfl⟩
      simpa [qgM, Subgroup.mem_subgroupOf] using hqgQ
    have hqg_cent : qM qgM ∈ Subgroup.centralizer (Qbar : Set (M ⧸ Q0M)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hyQbar
      exact setLike_mul_comm
        (s := Qbar) hyQbar hqgQbar
    let Cq : Subgroup (M ⧸ Q0M) := Subgroup.centralizer (Qbar : Set (M ⧸ Q0M))
    have hdgbar_cent : qM dgM ∈ Cq := by
      have hprod : qM qgM * qM dgM ∈ Cq := by
        have hprod_eq : qM qgM * qM dgM = qM xM := by
          rw [← map_mul, hqdM]
        simpa [Cq, hprod_eq] using hxcent
      have hmem : (qM qgM)⁻¹ * (qM qgM * qM dgM) ∈ Cq :=
        Cq.mul_mem (Cq.inv_mem (by simpa [Cq] using hqg_cent)) hprod
      simpa [Cq, mul_assoc] using hmem
    let Rloc : Subgroup M := Subgroup.zpowers dgM
    have hdgDloc : dgM ∈ D.subgroupOf M := by
      simpa [dgM, Subgroup.mem_subgroupOf] using hdgD
    have hRloc_le_Dloc : Rloc ≤ D.subgroupOf M :=
      Subgroup.zpowers_le.2 hdgDloc
    have hRlocπ :
        IsPiSubgroup (G := M) ({q} : Set Nat.Primes)ᶜ Rloc :=
      IsPiSubgroup.of_le hRloc_le_Dloc hDlocπ
    have hcopQRloc : Nat.Coprime (Nat.card Qloc) (Nat.card Rloc) :=
      section15_coprime_card_of_disjoint_piSubgroups
        (G := M) hπdisj hQlocπ hRlocπ
    have hRnormQloc : Rloc ≤ Subgroup.normalizer (Qloc : Set M) :=
      le_top.trans (Subgroup.le_normalizer_of_normal (H := Qloc))
    have hQ0invRloc :
        ∀ r : Rloc, ∀ y ∈ Q0M, (r : M) * y * (r : M)⁻¹ ∈ Q0M := by
      intro r y hy
      exact (inferInstance : Q0M.Normal).conj_mem y hy r
    have hcent_map :
        subgroupCentralizerIn (Qloc.map qM) (Rloc.map qM) =
          (subgroupCentralizerIn Qloc Rloc).map qM := by
      simpa [Qloc, Rloc, qM] using
        subgroupCentralizerIn_map_mk'_eq_map_of_solvable_coprime
          (H := Qloc) (R := Rloc) (X := Q0M)
          hRnormQloc hsolvQloc hcopQRloc hQ0invRloc
    have hRloc_map :
        Rloc.map qM = Subgroup.zpowers (qM dgM) := by
      simp [Rloc]
    have hcent_quot_top :
        subgroupCentralizerIn (Qloc.map qM) (Rloc.map qM) = Qloc.map qM := by
      apply le_antisymm
      · intro y hy
        exact hy.1
      · intro y hyQ
        refine ⟨hyQ, ?_⟩
        rw [hRloc_map]
        change y ∈ Subgroup.centralizer (Subgroup.zpowers (qM dgM) : Set (M ⧸ Q0M))
        apply section15_centralizer_singleton_le_centralizer_zpowers
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hyQbar : y ∈ Qbar := by
          simpa [Qbar, Qloc] using hyQ
        exact Subgroup.mem_centralizer_iff.mp
          (by simpa [Cq] using hdgbar_cent) y hyQbar
    have hcent_local_map :
        (subgroupCentralizerIn Qloc Rloc).map qM = Qloc.map qM := by
      calc
        (subgroupCentralizerIn Qloc Rloc).map qM =
            subgroupCentralizerIn (Qloc.map qM) (Rloc.map qM) := hcent_map.symm
        _ = Qloc.map qM := hcent_quot_top
    have hQ0M_le_Qloc : Q0M ≤ Qloc := by
      intro y hyQ0
      have hyQ0G : (y : G) ∈ Q₀ := by
        simpa [Q0M, Q₀, Subgroup.mem_subgroupOf] using hyQ0
      have hyQG : (y : G) ∈ Q := hQ₀Q hyQ0G
      simpa [Qloc, Subgroup.mem_subgroupOf] using hyQG
    have hQ0M_le_cent : Q0M ≤ subgroupCentralizerIn Qloc Rloc := by
      intro y hyQ0
      refine ⟨hQ0M_le_Qloc hyQ0, ?_⟩
      change y ∈ Subgroup.centralizer (Rloc : Set M)
      rw [Subgroup.mem_centralizer_iff]
      intro r hrR
      have hyQ0G : (y : G) ∈ Q₀ := by
        simpa [Q0M, Q₀, Subgroup.mem_subgroupOf] using hyQ0
      have hrDloc : r ∈ D.subgroupOf M := hRloc_le_Dloc hrR
      have hrD : (r : G) ∈ D := by
        simpa [Subgroup.mem_subgroupOf] using hrDloc
      have hcommG : (r : G) * (y : G) = (y : G) * (r : G) :=
        Subgroup.mem_centralizer_iff.mp hyQ0G.2 (r : G) hrD
      exact Subtype.ext hcommG
    have hcent_local_eq : subgroupCentralizerIn Qloc Rloc = Qloc := by
      apply le_antisymm
      · intro y hy
        exact hy.1
      · intro y hyQloc
        have hy_map : qM y ∈ (subgroupCentralizerIn Qloc Rloc).map qM := by
          rw [hcent_local_map]
          exact Subgroup.mem_map.mpr ⟨y, hyQloc, rfl⟩
        rcases Subgroup.mem_map.mp hy_map with ⟨z, hzcent, hzy⟩
        have hyzQ0 : y * z⁻¹ ∈ Q0M := by
          have hdiv : y / z ∈ Q0M :=
            (QuotientGroup.eq_iff_div_mem (N := Q0M)).1 hzy.symm
          simpa [div_eq_mul_inv] using hdiv
        have hyzcent : y * z⁻¹ ∈ subgroupCentralizerIn Qloc Rloc :=
          hQ0M_le_cent hyzQ0
        have hycent : (y * z⁻¹) * z ∈ subgroupCentralizerIn Qloc Rloc :=
          (subgroupCentralizerIn Qloc Rloc).mul_mem hyzcent hzcent
        simpa [mul_assoc] using hycent
    have hdg_centQ : dg ∈ Subgroup.centralizer (Q : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hyQ
      let yM : M := ⟨y, hQM hyQ⟩
      have hyQloc : yM ∈ Qloc := by
        simpa [Qloc, yM, Subgroup.mem_subgroupOf] using hyQ
      have hycent : yM ∈ subgroupCentralizerIn Qloc Rloc := by
        simpa [hcent_local_eq] using hyQloc
      have hdgR : dgM ∈ Rloc := Subgroup.mem_zpowers dgM
      have hcommM : dgM * yM = yM * dgM :=
        Subgroup.mem_centralizer_iff.mp hycent.2 dgM hdgR
      exact (congrArg (fun z : M => (z : G)) hcommM).symm
    rw [← hqd]
    exact (Q ⊔ subgroupCentralizerIn D Q).mul_mem
      (Subgroup.mem_sup_left hqgQ)
      (Subgroup.mem_sup_right ⟨hdgD, hdg_centQ⟩)
  have hDcomp : section12ComplementIn (section10Msigma M) Q D := hD.2.1
  have hCbar_le_sigma : Cbar ≤ section10Msigma M := by
    refine hCbar_le_QE.trans ?_
    exact sup_le hDcomp.1 (by
      intro x hx
      exact hDcomp.2.1 hx.1)
  have hQnil : Group.IsNilpotent Q :=
    section15_sylowSubgroupIn_nilpotent hQ
  have hQE_nil : Group.IsNilpotent (↥(Q ⊔ subgroupCentralizerIn D Q)) :=
    section15_Q_sup_D_centralizer_Q_nilpotent hDcomp hQnormal hQnil hD.2.2.1
  have hCbar_nil : Group.IsNilpotent Cbar := by
    let Csub : Subgroup (↥(Q ⊔ subgroupCentralizerIn D Q)) :=
      Cbar.subgroupOf (Q ⊔ subgroupCentralizerIn D Q)
    have hCsub_nil : Group.IsNilpotent Csub := by
      letI : Group.IsNilpotent (↥(Q ⊔ subgroupCentralizerIn D Q)) := hQE_nil
      infer_instance
    let e : Csub ≃* Cbar :=
      Subgroup.subgroupOfEquivOfLe (H := Cbar)
        (K := Q ⊔ subgroupCentralizerIn D Q) hCbar_le_QE
    exact Group.nilpotent_of_mulEquiv (G := Csub) (G' := Cbar) (_h := hCsub_nil) e
  have hCbar_le_F : Cbar ≤ section8FittingSubgroup M := by
    simpa [section8FittingSubgroup] using
      section12_le_fittingSubgroupOf_of_normalIn_nilpotent
        (G := G) (H := M) (N := Cbar) hCbar_norm.1 hCbar_norm.2 hCbar_nil
  exact ⟨by simpa [Cbar, Qbar, Q0M, qM, Q₀] using hCbar_le_F,
    by simpa [Cbar, Qbar, Q0M, qM, Q₀] using hCbar_le_sigma⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_derived_le_sup_commutator_of_normal_sup_top
    {Q D : Subgroup G} [Q.Normal] (hQD : Q ⊔ D = ⊤) :
    derivedSubgroup G ≤ Q ⊔ ⁅D, D⁆ := by
  change ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ ≤ Q ⊔ ⁅D, D⁆
  rw [Subgroup.commutator_le]
  intro p hp q hq
  have hp_sup : p ∈ Q ⊔ D := by simp [hQD]
  rcases (Subgroup.mem_sup_of_normal_left (s := Q) (t := D) (x := p)).1 hp_sup with
    ⟨q₁, hq₁Q, d₁, hd₁D, hq₁d₁⟩
  have hq_sup : q ∈ Q ⊔ D := by simp [hQD]
  rcases (Subgroup.mem_sup_of_normal_left (s := Q) (t := D) (x := q)).1 hq_sup with
    ⟨q₂, hq₂Q, d₂, hd₂D, hq₂d₂⟩
  let c : G := ⁅d₁, d₂⁆
  have hcDD : c ∈ ⁅D, D⁆ :=
    Subgroup.commutator_mem_commutator (H₁ := D) (H₂ := D) hd₁D hd₂D
  have hq₁eq : (((q₁ * d₁ : G) : G) : G ⧸ Q) = (d₁ : G ⧸ Q) := by
    rw [QuotientGroup.eq_iff_div_mem]
    simpa [div_eq_mul_inv, mul_assoc] using hq₁Q
  have hq₂eq : (((q₂ * d₂ : G) : G) : G ⧸ Q) = (d₂ : G ⧸ Q) := by
    rw [QuotientGroup.eq_iff_div_mem]
    simpa [div_eq_mul_inv, mul_assoc] using hq₂Q
  have hmap_eq : QuotientGroup.mk' Q ⁅p, q⁆ = QuotientGroup.mk' Q c := by
    calc
      QuotientGroup.mk' Q ⁅p, q⁆ =
          ⁅((p : G) : G ⧸ Q), ((q : G) : G ⧸ Q)⁆ := by
        simp
      _ = ⁅(((q₁ * d₁ : G) : G) : G ⧸ Q), (((q₂ * d₂ : G) : G) : G ⧸ Q)⁆ := by
        rw [← hq₁d₁, ← hq₂d₂]
      _ = ⁅(d₁ : G ⧸ Q), (d₂ : G ⧸ Q)⁆ := by
        rw [hq₁eq, hq₂eq]
      _ = QuotientGroup.mk' Q c := by
        simp [c]
  have hq₀Q : ⁅p, q⁆ * c⁻¹ ∈ Q := by
    apply (QuotientGroup.eq_one_iff (N := Q) (x := ⁅p, q⁆ * c⁻¹)).mp
    calc
      QuotientGroup.mk' Q (⁅p, q⁆ * c⁻¹) =
          QuotientGroup.mk' Q ⁅p, q⁆ * (QuotientGroup.mk' Q c)⁻¹ := by
        rw [map_mul, map_inv]
      _ = QuotientGroup.mk' Q c * (QuotientGroup.mk' Q c)⁻¹ := by
        rw [hmap_eq]
      _ = 1 := by simp
  let q₀ : G := ⁅p, q⁆ * c⁻¹
  have hrepr : ⁅p, q⁆ = q₀ * c := by
    dsimp [q₀]
    simp [mul_assoc]
  rw [hrepr]
  exact (Q ⊔ ⁅D, D⁆).mul_mem (Subgroup.mem_sup_left hq₀Q)
    (Subgroup.mem_sup_right hcDD)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_ambientDerived_le_sup_commutator_of_complement
    {S Q D : Subgroup G}
    (hcomp : section12ComplementIn S Q D)
    (hQnorm : section10NormalIn Q S) :
    ambientDerivedSubgroup S ≤ Q ⊔ ⁅D, D⁆ := by
  classical
  let Qloc : Subgroup S := Q.subgroupOf S
  let Dloc : Subgroup S := D.subgroupOf S
  haveI : Qloc.Normal := by
    simpa [Qloc] using hQnorm.2
  have hloc_sup_top : Qloc ⊔ Dloc = ⊤ := by
    calc
      Qloc ⊔ Dloc = (Q ⊔ D).subgroupOf S := by
        symm
        exact Subgroup.subgroupOf_sup (A := Q) (A' := D) (B := S)
          hcomp.1 hcomp.2.1
      _ = ⊤ := by
        rw [← hcomp.2.2.1]
        simp
  have hder_loc : derivedSubgroup S ≤ Qloc ⊔ ⁅Dloc, Dloc⁆ :=
    section15_derived_le_sup_commutator_of_normal_sup_top
      (G := S) (Q := Qloc) (D := Dloc) hloc_sup_top
  intro x hx
  have hxS_mem : x ∈ S := section15_ambientDerived_le hx
  let xS : S := ⟨x, hxS_mem⟩
  have hxS_der : xS ∈ derivedSubgroup S := by
    have hxSub : xS ∈ (ambientDerivedSubgroup S).subgroupOf S := by
      simpa [xS, Subgroup.mem_subgroupOf] using hx
    simpa [section15_ambientDerived_subgroupOf_eq] using hxSub
  have hxS_sup : xS ∈ Qloc ⊔ ⁅Dloc, Dloc⁆ := hder_loc hxS_der
  rcases (Subgroup.mem_sup_of_normal_left (s := Qloc) (t := ⁅Dloc, Dloc⁆)
      (x := xS)).1 hxS_sup with
    ⟨qS, hqS, dS, hdS, hqd⟩
  have hqG : (qS : G) ∈ Q := by
    simpa [Qloc, Subgroup.mem_subgroupOf] using hqS
  have hdG : (dS : G) ∈ ⁅D, D⁆ := by
    have hdmap : (dS : G) ∈ (⁅Dloc, Dloc⁆).map S.subtype :=
      Subgroup.mem_map.mpr ⟨dS, hdS, rfl⟩
    have hmap_eq : (⁅Dloc, Dloc⁆).map S.subtype = ⁅D, D⁆ := by
      simpa [Dloc] using
        (commutator_subgroupOf_map_eq
          (S := S) (H := D) (R := D) hcomp.2.1 hcomp.2.1)
    simpa [hmap_eq] using hdmap
  have hx_eq : (qS : G) * (dS : G) = x := by
    simpa [xS] using congrArg (fun y : S => (y : G)) hqd
  rw [← hx_eq]
  exact (Q ⊔ ⁅D, D⁆).mul_mem (Subgroup.mem_sup_left hqG)
    (Subgroup.mem_sup_right hdG)

/-- Theorem 15.2 L006-S0010: the source Proposition 1.5(d)-style
Fitting/centralizer formula `F(M)=QC_M(Q)=C_M(Q/Q₀)<M_σ`. -/
private theorem CFSG.section15_fitting_eq_Q_sup_centralizer_Q_of_theorem15_2_context
    {M MF K Q D : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMFne : MF ≠ section10Msigma M)
    (hq : q.val = Nat.card (section14KStar M K))
    (hQ : section12SylowSubgroupIn q Q M)
    (hQnormal : section10NormalIn Q M)
    (hQMF : Q ≤ MF)
    (hD : section15Theorem15_2ComplementData M K Q D)
    (_hQ_le_F : Q ≤ section8FittingSubgroup M)
    (hQ_eq_pcore : Q = section15PCoreIn q M) :
    section8FittingSubgroup M = Q ⊔ subgroupCentralizerIn M Q ∧
      section15QuotientCentralizerEquals
        (section8FittingSubgroup M) M Q (subgroupCentralizerIn Q D) ∧
        section8FittingSubgroup M < section10Msigma M := by
  classical
  let Q₀ : Subgroup G := subgroupCentralizerIn Q D
  rcases section15_Q0_quotient_minimal_normal
      hM hMF hK hMFne hq hQ hQnormal hQMF hD with
    ⟨hQ₀M, hQM, hQ₀Q, hQ₀norm, _hQbar_ne, _hQbar_norm, _hQbar_min⟩
  rcases section15_p_card_prime_of_theorem15_2_context
      hM hMF hK hMFne hq hQ hQnormal hQMF hD with
    ⟨p, hp⟩
  rcases section15_Qbar_elementary_card
      hM hMF hK hMFne hp hq hQ hQnormal hQMF hD with
    ⟨_hQ₀M', _hQM', _hQ₀Q', _hQ₀norm', hQbar_elem, _hQbar_card⟩
  let Cbar : Subgroup G :=
    ((Subgroup.centralizer
      (((Q.subgroupOf M).map (QuotientGroup.mk' (Q₀.subgroupOf M))) :
        Set (M ⧸ Q₀.subgroupOf M))).comap
          (QuotientGroup.mk' (Q₀.subgroupOf M))).map M.subtype
  have hQbar_comm :
      IsMulCommutative
        ((Q.subgroupOf M).map (QuotientGroup.mk' (Q₀.subgroupOf M))) := by
    letI : IsElementaryAbelian q.val
        ((Q.subgroupOf M).map (QuotientGroup.mk' (Q₀.subgroupOf M))) := by
      simpa [Q₀] using hQbar_elem
    infer_instance
  have hF_le_QC :
      section8FittingSubgroup M ≤ Q ⊔ subgroupCentralizerIn M Q :=
    section15_fitting_le_Q_sup_centralizer_Q_of_pcore q hQ_eq_pcore
  have hQC_le_Cbar :
      Q ⊔ subgroupCentralizerIn M Q ≤ Cbar := by
    simpa [Cbar, Q₀] using
      section15_Q_sup_centralizer_Q_le_quotient_centralizer
        (M := M) (Q := Q) (N := Q₀)
        hQ₀M hQM hQ₀Q hQ₀norm hQbar_comm
  rcases section15_quotient_centralizer_le_fitting_of_theorem15_2_context
      hM hMF hK hMFne hq hQ hQnormal hQMF hD hQ₀norm with
    ⟨hCbar_le_F, hCbar_le_sigma⟩
  have hQC_le_F :
      Q ⊔ subgroupCentralizerIn M Q ≤ section8FittingSubgroup M :=
    hQC_le_Cbar.trans (by simpa [Cbar] using hCbar_le_F)
  have hF_eq_QC :
      section8FittingSubgroup M = Q ⊔ subgroupCentralizerIn M Q :=
    le_antisymm hF_le_QC hQC_le_F
  have hF_eq_Cbar : section8FittingSubgroup M = Cbar := by
    exact le_antisymm (hF_le_QC.trans hQC_le_Cbar)
      (by simpa [Cbar] using hCbar_le_F)
  have hquot_M :
      section15QuotientCentralizerEquals
        (section8FittingSubgroup M) M Q Q₀ := by
    exact ⟨hQ₀M, hQM, hQ₀norm, by simpa [Cbar] using hF_eq_Cbar⟩
  have hF_le_sigma : section8FittingSubgroup M ≤ section10Msigma M := by
    rw [hF_eq_Cbar]
    simpa [Cbar] using hCbar_le_sigma
  have hF_ne_sigma : section8FittingSubgroup M ≠ section10Msigma M := by
    intro hEq
    have hnil : Group.IsNilpotent (section10Msigma M) := by
      rw [← hEq]
      exact section8FittingSubgroup_isNilpotent M
    exact (section15_MF_ne_msigma_not_nilpotent hM hMF hMFne) hnil
  exact ⟨hF_eq_QC, by simpa [Q₀] using hquot_M,
    lt_of_le_of_ne hF_le_sigma hF_ne_sigma⟩

/-- Theorem 15.2 L006-S0040: Theorem 3.10(c) gives
`M_σ'≤Q D'≤C_{M_σ}(Q/Q₀)≤F(M)`. -/
private theorem CFSG.section15_msigma_derived_le_quotient_centralizer_of_theorem15_2_context
    {M MF K Q D : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMFne : MF ≠ section10Msigma M)
    (hq : q.val = Nat.card (section14KStar M K))
    (hQ : section12SylowSubgroupIn q Q M)
    (hQnormal : section10NormalIn Q M)
    (hQMF : Q ≤ MF)
    (hD : section15Theorem15_2ComplementData M K Q D)
    (hQ₀norm : ((subgroupCentralizerIn Q D).subgroupOf M).Normal) :
    let Q₀ : Subgroup G := subgroupCentralizerIn Q D
    letI : (Q₀.subgroupOf M).Normal := hQ₀norm
    ambientDerivedSubgroup (section10Msigma M) ≤
      ((Subgroup.centralizer
        (((Q.subgroupOf M).map (QuotientGroup.mk' (Q₀.subgroupOf M))) :
          Set (M ⧸ Q₀.subgroupOf M))).comap
            (QuotientGroup.mk' (Q₀.subgroupOf M))).map M.subtype := by
  classical
  let Q₀ : Subgroup G := subgroupCentralizerIn Q D
  let Q0M : Subgroup M := Q₀.subgroupOf M
  haveI : Q0M.Normal := by
    simpa [Q0M, Q₀] using hQ₀norm
  let qM : M →* M ⧸ Q0M := QuotientGroup.mk' Q0M
  let Qloc : Subgroup M := Q.subgroupOf M
  let Qbar : Subgroup (M ⧸ Q0M) := Qloc.map qM
  let Cbar : Subgroup G :=
    ((Subgroup.centralizer (Qbar : Set (M ⧸ Q0M))).comap qM).map M.subtype
  rcases section15_Q0_quotient_minimal_normal
      hM hMF hK hMFne hq hQ hQnormal hQMF hD with
    ⟨hQ₀M, hQM, hQ₀Q, _hQ₀norm', hQbar_ne, hQbar_norm, _hQbar_min⟩
  rcases section15_p_card_prime_of_theorem15_2_context
      hM hMF hK hMFne hq hQ hQnormal hQMF hD with
    ⟨p, hp⟩
  rcases section15_Qbar_elementary_card
      hM hMF hK hMFne hp hq hQ hQnormal hQMF hD with
    ⟨_hQ₀M', _hQM', _hQ₀Q', _hQ₀norm'', hQbar_elem, hQbar_card⟩
  letI : Fact q.val.Prime := ⟨q.property⟩
  haveI : Qbar.Normal := by
    simpa [Qbar, Qloc, Q0M, qM, Q₀] using hQbar_norm
  haveI : Nontrivial Qbar := by
    exact Qbar.nontrivial_iff_ne_bot.mpr (by simpa [Qbar, Qloc, Q0M, qM, Q₀] using hQbar_ne)
  have hQbar_comm : IsMulCommutative Qbar := by
    letI : IsElementaryAbelian q.val Qbar := by
      simpa [Qbar, Qloc, Q0M, qM, Q₀] using hQbar_elem
    infer_instance
  have hQbar_p : IsPGroup q.val Qbar := by
    letI : IsElementaryAbelian q.val Qbar := by
      simpa [Qbar, Qloc, Q0M, qM, Q₀] using hQbar_elem
    exact IsElementaryAbelian.isPGroup q.val Qbar
  have hnilQbar : Group.IsNilpotent Qbar :=
    IsPGroup.isNilpotent (p := q.val) (G := Qbar) hQbar_p
  have hDcomp : section12ComplementIn (section10Msigma M) Q D := hD.2.1
  have hMF_le_sigma : MF ≤ section10Msigma M := section15_MF_le_msigma hM hMF
  have hQ_le_sigma : Q ≤ section10Msigma M := hQMF.trans hMF_le_sigma
  have hQnorm_sigma : section10NormalIn Q (section10Msigma M) := by
    refine ⟨hQ_le_sigma, ?_⟩
    have hM_norm_Q : M ≤ Subgroup.normalizer (Q : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQnormal.1).1 hQnormal.2
    have hsigma_norm_Q : section10Msigma M ≤ Subgroup.normalizer (Q : Set G) :=
      section15_msigma_le.trans hM_norm_Q
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hQ_le_sigma).2 hsigma_norm_Q
  have hder_le_QDcomm :
      ambientDerivedSubgroup (section10Msigma M) ≤ Q ⊔ ⁅D, D⁆ :=
    section15_ambientDerived_le_sup_commutator_of_complement
      (S := section10Msigma M) (Q := Q) (D := D) hDcomp hQnorm_sigma
  have hQ_le_Cbar : Q ≤ Cbar := by
    have hQ_CQ_le_Cbar : Q ⊔ subgroupCentralizerIn M Q ≤ Cbar := by
      simpa [Cbar, Qbar, Qloc, Q0M, qM, Q₀] using
        section15_Q_sup_centralizer_Q_le_quotient_centralizer
          (M := M) (Q := Q) (N := Q₀)
          hQ₀M hQM hQ₀Q hQ₀norm hQbar_comm
    exact le_sup_left.trans hQ_CQ_le_Cbar
  let S : Subgroup G := D ⊔ K
  let Dsub : Subgroup S := D.subgroupOf S
  let Ksub : Subgroup S := K.subgroupOf S
  have hD_le_M : D ≤ M := hDcomp.2.1.trans section15_msigma_le
  have hS_le_M : S ≤ M := by
    simpa [S] using sup_le hD_le_M hK.1
  let toQ : S →* M ⧸ Q0M :=
    (QuotientGroup.mk' Q0M).comp (Subgroup.inclusion hS_le_M)
  let toTop : (M ⧸ Q0M) →* (⊤ : Subgroup (M ⧸ Q0M)) :=
    { toFun := fun x => ⟨x, by simp⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp }
  letI : MulDistribMulAction (M ⧸ Q0M) Qbar :=
    MulDistribMulAction.compHom Qbar toTop
  letI : MulDistribMulAction S Qbar :=
    MulDistribMulAction.compHom Qbar toQ
  have hfrob :
      IsFrobeniusGroupWithKernelComplement Dsub Ksub := by
    simpa [Dsub, Ksub, S] using
      section15_KD_frobenius_with_kernel_D
        hM hMF hK hMFne hq hQ hQnormal hD
  have hsolvM : Group.IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.2 hM.1)
  have hsolvS : Group.IsSolvable S := by
    let Sloc : Subgroup M := S.subgroupOf M
    have hSloc_solv : Group.IsSolvable Sloc := by
      letI : Group.IsSolvable M := hsolvM
      infer_instance
    let eS : Sloc ≃* S :=
      Subgroup.subgroupOfEquivOfLe (H := S) (K := M) hS_le_M
    exact Group.isSolvable_of_surjective (f := eS.toMonoidHom) eS.surjective
  have hcop : Nat.Coprime (Nat.card S) (Nat.card Qbar) := by
    have hDπ : IsPiSubgroup (G := G) ({q} : Set Nat.Primes)ᶜ D :=
      section15_complement_D_isPiSubgroup_q_compl hQ hQnormal hDcomp
    have hKπ : IsPiSubgroup (G := G) ({q} : Set Nat.Primes)ᶜ K :=
      section15_hall_kappa_isPiSubgroup_q_compl hM hK hq
    have hDsubπ : IsPiSubgroup (G := S) ({q} : Set Nat.Primes)ᶜ Dsub := by
      simpa [Dsub] using
        section15_isPiSubgroup_subgroupOf
          (G := G) (H := S) (K := D) hDπ
          (by simp [S])
    have hKsubπ : IsPiSubgroup (G := S) ({q} : Set Nat.Primes)ᶜ Ksub := by
      simpa [Ksub] using
        section15_isPiSubgroup_subgroupOf
          (G := G) (H := S) (K := K) hKπ
          (by simp [S])
    have hStopπ :
        IsPiSubgroup (G := S) ({q} : Set Nat.Primes)ᶜ (⊤ : Subgroup S) := by
      have hDsub_normal : Dsub.Normal := hfrob.normal
      letI : Dsub.Normal := hDsub_normal
      have hsupπ :
          IsPiSubgroup (G := S) ({q} : Set Nat.Primes)ᶜ (Ksub ⊔ Dsub) :=
        section15_isPiSubgroup_sup_of_normal_right hKsubπ hDsubπ
      have hcompl : Dsub.IsComplement' Ksub := hfrob.isComplement'
      have hsup_top : Ksub ⊔ Dsub = ⊤ := by
        simpa [sup_comm] using hcompl.sup_eq_top
      simpa [hsup_top] using hsupπ
    have hQbartop_p : IsPGroup q.val (⊤ : Subgroup Qbar) :=
      hQbar_p.of_equiv
        (Subgroup.topEquiv : (⊤ : Subgroup Qbar) ≃* Qbar).symm
    have hQbartopπ :
        IsPiSubgroup (G := Qbar) ({q} : Set Nat.Primes) (⊤ : Subgroup Qbar) :=
      section8_isPiSubgroup_singleton_of_isPGroup hQbartop_p
    have hπdisj : Disjoint (({q} : Set Nat.Primes)ᶜ) ({q} : Set Nat.Primes) := by
      rw [Set.disjoint_left]
      intro r hrcompl hrsing
      exact hrcompl hrsing
    exact
      section15_coprime_natCard_of_disjoint_piGroups
        (R := S) (S := Qbar) hπdisj hStopπ hQbartopπ
  have hmap_subgroupOf (A : Subgroup G) (hAS : A ≤ S) (hAM : A ≤ M) :
      (A.subgroupOf S).map toQ = (A.subgroupOf M).map qM := by
    ext z
    constructor
    · intro hz
      rcases Subgroup.mem_map.mp hz with ⟨aS, haA, rfl⟩
      have haAamb : (aS : G) ∈ A := by
        simpa [Subgroup.mem_subgroupOf] using haA
      let aM : M := ⟨(aS : G), hAM haAamb⟩
      have haM : aM ∈ A.subgroupOf M := by
        simpa [aM, Subgroup.mem_subgroupOf] using haAamb
      refine Subgroup.mem_map.mpr ⟨aM, haM, ?_⟩
      have ha_eq : aM = Subgroup.inclusion hS_le_M aS := by
        apply Subtype.ext
        rfl
      simpa [toQ, qM, aM] using congrArg qM ha_eq
    · intro hz
      rcases Subgroup.mem_map.mp hz with ⟨aM, haA, rfl⟩
      have haAamb : (aM : G) ∈ A := by
        simpa [Subgroup.mem_subgroupOf] using haA
      let aS : S := ⟨(aM : G), hAS haAamb⟩
      have haS : aS ∈ A.subgroupOf S := by
        simpa [aS, Subgroup.mem_subgroupOf] using haAamb
      refine Subgroup.mem_map.mpr ⟨aS, haS, ?_⟩
      have ha_eq : Subgroup.inclusion hS_le_M aS = aM := by
        apply Subtype.ext
        rfl
      simpa [toQ, qM, aS] using congrArg qM ha_eq
  have hfix_toQ_eq (A : Subgroup S) :
      fixedPointSubgroup (↥A) Qbar =
        (subgroupCentralizerIn Qbar (A.map toQ)).subgroupOf Qbar := by
    ext y
    constructor
    · intro hy
      refine ⟨y.2, ?_⟩
      change (y : M ⧸ Q0M) ∈
        Subgroup.centralizer (A.map toQ : Set (M ⧸ Q0M))
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rcases Subgroup.mem_map.mp hz with ⟨a, haA, rfl⟩
      have hyfix : (⟨a, haA⟩ : A) • y = y := by
        rw [fixedPointSubgroup, FixedPoints.mem_subgroup] at hy
        exact hy ⟨a, haA⟩
      have hconj :
          toQ a * (y : M ⧸ Q0M) * (toQ a)⁻¹ = y := by
        have hval := congrArg Subtype.val hyfix
        change toQ a * (y : M ⧸ Q0M) * (toQ a)⁻¹ =
          (y : M ⧸ Q0M) at hval
        exact hval
      exact mul_inv_eq_iff_eq_mul.mp hconj
    · intro hy
      rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
      intro a
      have hcomm :
          toQ (a : S) * (y : M ⧸ Q0M) =
            (y : M ⧸ Q0M) * toQ (a : S) := by
        have hyc :
            (y : M ⧸ Q0M) ∈
              Subgroup.centralizer (A.map toQ : Set (M ⧸ Q0M)) := hy.2
        exact Subgroup.mem_centralizer_iff.mp hyc (toQ (a : S))
          (Subgroup.mem_map.mpr ⟨(a : S), a.property, rfl⟩)
      have hconj :
          toQ (a : S) * (y : M ⧸ Q0M) * (toQ (a : S))⁻¹ = y := by
        exact mul_inv_eq_iff_eq_mul.mpr hcomm
      apply Subtype.ext
      change toQ (a : S) * (y : M ⧸ Q0M) * (toQ (a : S))⁻¹ =
        (y : M ⧸ Q0M)
      exact hconj
  have hfixD : fixedPointSubgroup (↥Dsub) Qbar = ⊥ := by
    let Dloc : Subgroup M := D.subgroupOf M
    let Dbar : Subgroup (M ⧸ Q0M) := Dloc.map qM
    have hDbar_eq : Dsub.map toQ = Dbar := by
      simpa [Dsub, Dloc, Dbar] using
        hmap_subgroupOf D (by simp [S]) hD_le_M
    have hcent_D_bot : subgroupCentralizerIn Qbar Dbar = ⊥ := by
      simpa [Qbar, Dbar, Qloc, Dloc, Q0M, qM, Q₀] using
        section15_Qbar_D_centralizer_eq_bot_of_theorem15_2_context
          hM hMF hK hMFne hq hQ hQnormal hQMF hD hQ₀norm
    have hfix_eq :
        fixedPointSubgroup (↥Dsub) Qbar =
          (subgroupCentralizerIn Qbar Dbar).subgroupOf Qbar := by
      calc
        fixedPointSubgroup (↥Dsub) Qbar =
            (subgroupCentralizerIn Qbar (Dsub.map toQ)).subgroupOf Qbar :=
          hfix_toQ_eq Dsub
        _ = (subgroupCentralizerIn Qbar Dbar).subgroupOf Qbar := by
          rw [hDbar_eq]
    simp [hfix_eq, hcent_D_bot]
  have hKsub_card : Nat.card Ksub = Nat.card K := by
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe
        (H := K) (K := S) (by simp [S])).toEquiv
  have hKsub_card_p : Nat.card Ksub = p.val := by
    calc
      Nat.card Ksub = Nat.card K := hKsub_card
      _ = p.val := hp.symm
  have hKsub_prime : Nat.Prime (Nat.card Ksub) := by
    simpa [hKsub_card_p] using p.property
  have hfixK :
      ∀ x : Ksub, x ≠ 1 →
        fixedPointSubgroup (↥(Subgroup.zpowers (x : S))) Qbar =
          fixedPointSubgroup (↥Ksub) Qbar := by
    intro x hx
    have hx_top : Subgroup.zpowers x = (⊤ : Subgroup Ksub) :=
      zpowers_eq_top_of_prime_card_of_ne_one hKsub_prime hx
    have hmap_zpow :
        (Subgroup.zpowers x).map Ksub.subtype = Subgroup.zpowers (x : S) := by
      simp
    have htop_map : (⊤ : Subgroup Ksub).map Ksub.subtype = Ksub := by
      ext y
      constructor
      · intro hy
        rcases Subgroup.mem_map.mp hy with ⟨z, _hz, rfl⟩
        exact z.property
      · intro hy
        exact Subgroup.mem_map.mpr ⟨⟨y, hy⟩, by simp, rfl⟩
    have hzpow_eq : Subgroup.zpowers (x : S) = Ksub := by
      calc
        Subgroup.zpowers (x : S) = (Subgroup.zpowers x).map Ksub.subtype :=
          hmap_zpow.symm
        _ = (⊤ : Subgroup Ksub).map Ksub.subtype := by rw [hx_top]
        _ = Ksub := htop_map
    rw [hzpow_eq]
  have hmain_card :
      Nat.card Qbar = Nat.card (fixedPointSubgroup (↥Ksub) Qbar) ^ Nat.card Ksub :=
    theorem_3_10_b (G := S) (K := Dsub) (R := Ksub) (M := Qbar)
      hfrob hsolvS hnilQbar hcop hfixD hfixK
  have hfixK_card :
      Nat.card (fixedPointSubgroup (↥Ksub) Qbar) = q.val := by
    have hpow_eq :
        Nat.card (fixedPointSubgroup (↥Ksub) Qbar) ^ p.val = q.val ^ p.val := by
      calc
        Nat.card (fixedPointSubgroup (↥Ksub) Qbar) ^ p.val =
            Nat.card (fixedPointSubgroup (↥Ksub) Qbar) ^ Nat.card Ksub := by
          rw [hKsub_card_p]
        _ = Nat.card Qbar := hmain_card.symm
        _ = q.val ^ p.val := by
          simpa [Qbar, Qloc, Q0M, qM, Q₀] using hQbar_card
    exact Nat.pow_left_injective (Nat.Prime.ne_zero p.property) hpow_eq
  have hfixK_cyclic : IsCyclic (fixedPointSubgroup (↥Ksub) Qbar) := by
    exact isCyclic_of_prime_card hfixK_card
  have hDcomm_action :
      ⁅Dsub, Dsub⁆ ≤ actionCentralizerIn (A := S) (G := Qbar) Dsub :=
    theorem_3_10_c (G := S) (K := Dsub) (R := Ksub) (M := Qbar)
      hfrob hsolvS hnilQbar hcop hfixD hfixK hfixK_cyclic
  have hDcomm_le_Cbar : ⁅D, D⁆ ≤ Cbar := by
    intro x hxComm
    have hxD : x ∈ D := (Subgroup.commutator_le_self D) hxComm
    let xM : M := ⟨x, hD_le_M hxD⟩
    refine Subgroup.mem_map.mpr ⟨xM, ?_, rfl⟩
    change qM xM ∈ Subgroup.centralizer (Qbar : Set (M ⧸ Q0M))
    have hDcomm_map : (⁅Dsub, Dsub⁆).map S.subtype = ⁅D, D⁆ := by
      simpa [Dsub] using
        (commutator_subgroupOf_map_eq
          (S := S) (H := D) (R := D)
          (by simp [S])
          (by simp [S]))
    have hxMap : x ∈ (⁅Dsub, Dsub⁆).map S.subtype := by
      simpa [hDcomm_map] using hxComm
    rcases Subgroup.mem_map.mp hxMap with ⟨xS, hxSComm, hxSx⟩
    have hxS_action : xS ∈ actionCentralizerIn (A := S) (G := Qbar) Dsub :=
      hDcomm_action hxSComm
    have hxS_fix : xS ∈ fixingSubgroupOf S Qbar (Set.univ : Set Qbar) := by
      simpa [actionCentralizerIn] using hxS_action.2
    have hxS_cent :
        toQ xS ∈ Subgroup.centralizer (Qbar : Set (M ⧸ Q0M)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hyQbar
      let yQ : Qbar := ⟨y, hyQbar⟩
      have hxSker : MulDistribMulAction.toMulAut S Qbar xS = 1 := by
        have hfix' := hxS_fix
        rw [fixingSubgroupOf_univ_eq_ker_toMulAut] at hfix'
        exact MonoidHom.mem_ker.mp hfix'
      have hyfix : (xS : S) • yQ = yQ := by
        have hact := congrArg (fun f : MulAut Qbar => f yQ) hxSker
        simpa using hact
      have hconj :
          toQ xS * y * (toQ xS)⁻¹ = y := by
        have hval := congrArg Subtype.val hyfix
        change toQ xS * (y : M ⧸ Q0M) * (toQ xS)⁻¹ =
          (y : M ⧸ Q0M) at hval
        exact hval
      exact (mul_inv_eq_iff_eq_mul.mp hconj).symm
    have hxM_eq : Subgroup.inclusion hS_le_M xS = xM := by
      apply Subtype.ext
      exact hxSx
    have hx_toQ : qM xM = toQ xS := by
      change qM xM = qM (Subgroup.inclusion hS_le_M xS)
      exact (congrArg qM hxM_eq).symm
    simpa [hx_toQ] using hxS_cent
  exact hder_le_QDcomm.trans (by
    simpa [Cbar, Qbar, Qloc, Q0M, qM, Q₀] using
      (sup_le hQ_le_Cbar hDcomm_le_Cbar))

private theorem CFSG.section15_msigma_derived_le_fitting_of_theorem15_2_context
    {M MF K Q D : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMFne : MF ≠ section10Msigma M)
    (hq : q.val = Nat.card (section14KStar M K))
    (hQ : section12SylowSubgroupIn q Q M)
    (hQnormal : section10NormalIn Q M)
    (hQMF : Q ≤ MF)
    (hD : section15Theorem15_2ComplementData M K Q D)
    (hquot_M :
      section15QuotientCentralizerEquals
        (section8FittingSubgroup M) M Q (subgroupCentralizerIn Q D)) :
    ambientDerivedSubgroup (section10Msigma M) ≤ section8FittingSubgroup M := by
  classical
  let Q₀ : Subgroup G := subgroupCentralizerIn Q D
  rcases hquot_M with ⟨hQ₀M, hQM, hQ₀norm, hF_eq_Cbar⟩
  have hder_le_Cbar :
      ambientDerivedSubgroup (section10Msigma M) ≤
        ((Subgroup.centralizer
          (((Q.subgroupOf M).map (QuotientGroup.mk' (Q₀.subgroupOf M))) :
            Set (M ⧸ Q₀.subgroupOf M))).comap
              (QuotientGroup.mk' (Q₀.subgroupOf M))).map M.subtype := by
    simpa [Q₀] using
      section15_msigma_derived_le_quotient_centralizer_of_theorem15_2_context
        hM hMF hK hMFne hq hQ hQnormal hQMF hD hQ₀norm
  rw [hF_eq_Cbar]
  exact hder_le_Cbar

/-- Theorem 15.2 L006-S0040: minimality of `Q/Q₀` identifies
`C_{M_σ}(\overline{K*})` with `F(M)`. -/
private theorem CFSG.section15_kstar_quotient_centralizer_eq_fitting_of_theorem15_2_context
    {M MF K Q D : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMFne : MF ≠ section10Msigma M)
    (hq : q.val = Nat.card (section14KStar M K))
    (hQ : section12SylowSubgroupIn q Q M)
    (hQnormal : section10NormalIn Q M)
    (hQMF : Q ≤ MF)
    (hD : section15Theorem15_2ComplementData M K Q D)
    (hF_le_sigma : section8FittingSubgroup M ≤ section10Msigma M)
    (hder_le_F :
      ambientDerivedSubgroup (section10Msigma M) ≤ section8FittingSubgroup M)
    (hquot_M :
      section15QuotientCentralizerEquals
        (section8FittingSubgroup M) M Q (subgroupCentralizerIn Q D)) :
    section15QuotientCentralizerEquals
      (section8FittingSubgroup M) (section10Msigma M)
        (section14KStar M K) (subgroupCentralizerIn Q D) := by
  classical
  let Q₀ : Subgroup G := subgroupCentralizerIn Q D
  let σ : Subgroup G := section10Msigma M
  rcases hquot_M with ⟨hQ₀M, hQM, hQ₀normM, hF_eq_CbarM⟩
  rcases section15_Q0_quotient_minimal_normal
      hM hMF hK hMFne hq hQ hQnormal hQMF hD with
    ⟨_hQ₀M', _hQM', hQ₀Q, _hQ₀norm', hQbar_ne, hQbar_norm, hQbar_min⟩
  have hMF_le_sigma : MF ≤ σ := by
    simpa [σ] using section15_MF_le_msigma hM hMF
  have hQ_le_sigma : Q ≤ σ := hQMF.trans hMF_le_sigma
  have hQ₀_sigma : Q₀ ≤ σ := by
    intro x hx
    exact hQ_le_sigma (hQ₀Q (by simpa [Q₀] using hx))
  have hKstar_sigma : section14KStar M K ≤ σ := by
    intro x hx
    exact hx.1
  have hKstarQ : section14KStar M K ≤ Q :=
    section15_kstar_le_normal_sylow_of_prime_card
      (M := M) (K := K) (Q := Q) (q := q) hq hQ hQnormal
  have hQ₀norm_sigma : (Q₀.subgroupOf σ).Normal := by
    have hM_norm_Q₀ : M ≤ Subgroup.normalizer (Q₀ : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQ₀M).1 hQ₀normM
    have hσ_norm_Q₀ : σ ≤ Subgroup.normalizer (Q₀ : Set G) := by
      simpa [σ] using section15_msigma_le.trans hM_norm_Q₀
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hQ₀_sigma).2 hσ_norm_Q₀
  refine ⟨hQ₀_sigma, hKstar_sigma, hQ₀norm_sigma, ?_⟩
  let qM : M →* M ⧸ Q₀.subgroupOf M := QuotientGroup.mk' (Q₀.subgroupOf M)
  let qσ : σ →* σ ⧸ Q₀.subgroupOf σ := QuotientGroup.mk' (Q₀.subgroupOf σ)
  let QbarM : Subgroup (M ⧸ Q₀.subgroupOf M) := (Q.subgroupOf M).map qM
  let Kbarσ : Subgroup (σ ⧸ Q₀.subgroupOf σ) :=
    ((section14KStar M K).subgroupOf σ).map qσ
  let CbarM : Subgroup G :=
    ((Subgroup.centralizer (QbarM : Set (M ⧸ Q₀.subgroupOf M))).comap qM).map M.subtype
  let CbarσK : Subgroup G :=
    ((Subgroup.centralizer (Kbarσ : Set (σ ⧸ Q₀.subgroupOf σ))).comap qσ).map σ.subtype
  have hF_eq_CbarM' : section8FittingSubgroup M = CbarM := by
    simpa [CbarM, QbarM, qM, Q₀] using hF_eq_CbarM
  have hF_le_CbarσK : section8FittingSubgroup M ≤ CbarσK := by
    intro x hxF
    have hxσ : x ∈ σ := hF_le_sigma hxF
    let xσ : σ := ⟨x, hxσ⟩
    let xM : M := ⟨x, section15_msigma_le (by simpa [σ] using hxσ)⟩
    have hxMcent : qM xM ∈ Subgroup.centralizer (QbarM : Set (M ⧸ Q₀.subgroupOf M)) := by
      have hxCbarM : x ∈ CbarM := by
        rw [← hF_eq_CbarM']
        exact hxF
      rcases Subgroup.mem_map.mp hxCbarM with ⟨yM, hycent, hyx⟩
      have hy_eq : yM = xM := by
        apply Subtype.ext
        exact hyx
      simpa [CbarM, xM, hy_eq] using hycent
    refine Subgroup.mem_map.mpr ⟨xσ, ?_, rfl⟩
    change qσ xσ ∈ Subgroup.centralizer (Kbarσ : Set (σ ⧸ Q₀.subgroupOf σ))
    rw [Subgroup.mem_centralizer_iff]
    intro y hyKbar
    rcases Subgroup.mem_map.mp hyKbar with ⟨kσ, hkKstar, rfl⟩
    let kM : M := ⟨(kσ : G), section15_msigma_le (by exact kσ.property)⟩
    have hkKstarG : (kσ : G) ∈ section14KStar M K := by
      simpa [Subgroup.mem_subgroupOf] using hkKstar
    have hkQloc : kM ∈ Q.subgroupOf M := by
      have hkQ : (kσ : G) ∈ Q := hKstarQ hkKstarG
      simpa [kM, Subgroup.mem_subgroupOf] using hkQ
    have hkQbar : qM kM ∈ QbarM := by
      refine Subgroup.mem_map.mpr ⟨kM, hkQloc, rfl⟩
    have hcommM :
        qM kM * qM xM = qM xM * qM kM :=
      Subgroup.mem_centralizer_iff.mp hxMcent (qM kM) hkQbar
    rw [← map_mul, ← map_mul]
    apply (QuotientGroup.eq_iff_div_mem (N := Q₀.subgroupOf σ)).2
    have hdivM : kM * xM / (xM * kM) ∈ Q₀.subgroupOf M := by
      apply (QuotientGroup.eq_iff_div_mem (N := Q₀.subgroupOf M)).1
      change qM (kM * xM) = qM (xM * kM)
      simpa only [map_mul] using hcommM
    have hdivG : ((kσ * xσ / (xσ * kσ) : σ) : G) ∈ Q₀ := by
      have hdivG_M : ((kM * xM / (xM * kM) : M) : G) ∈ Q₀ := by
        simpa [Subgroup.mem_subgroupOf] using hdivM
      simpa [kM, xM, xσ, div_eq_mul_inv, mul_assoc] using hdivG_M
    simpa [Subgroup.mem_subgroupOf] using hdivG
  have hCbarσK_le_F : CbarσK ≤ section8FittingSubgroup M := by
    have hCbarσK_le_sigma : CbarσK ≤ σ := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨xσ, _hx, rfl⟩
      exact xσ.property
    have hCbarσK_le_M : CbarσK ≤ M := by
      intro x hx
      exact section15_msigma_le (by simpa [σ] using hCbarσK_le_sigma hx)
    have hKstarM : section14KStar M K ≤ M := by
      intro x hx
      exact section15_msigma_le (by exact hx.1)
    have hKbarM_ne :
        ((section14KStar M K).subgroupOf M).map qM ≠ ⊥ := by
      have hKstar_not_Q₀ :
          ¬ section14KStar M K ≤ Q₀ := by
        simpa [Q₀] using
          section15_kstar_not_le_Q0_of_theorem15_2_context
            hM hMF hK hMFne hq hQ hQnormal hQMF hD
      intro hbot
      apply hKstar_not_Q₀
      intro x hxKstar
      have hxM : x ∈ M := hKstarM hxKstar
      let xM : M := ⟨x, hxM⟩
      have hxsub : xM ∈ (section14KStar M K).subgroupOf M := by
        simpa [xM, Subgroup.mem_subgroupOf] using hxKstar
      have hxker :
          xM ∈ (QuotientGroup.mk' (Q₀.subgroupOf M)).ker :=
        (Subgroup.map_eq_bot_iff
          (H := (section14KStar M K).subgroupOf M)
          (f := QuotientGroup.mk' (Q₀.subgroupOf M))).1 hbot hxsub
      simpa [QuotientGroup.ker_mk', Q₀, xM, Subgroup.mem_subgroupOf] using hxker
    have hCbarσK_le_CbarK_M :
        CbarσK ≤
          ((Subgroup.centralizer
            ((((section14KStar M K).subgroupOf M).map qM) :
              Set (M ⧸ Q₀.subgroupOf M))).comap qM).map M.subtype := by
      intro x hxC
      rcases Subgroup.mem_map.mp hxC with ⟨xσ, hxσcent, hx⟩
      let xM : M := ⟨x, hCbarσK_le_M hxC⟩
      have hxσ_eq : (xσ : G) = x := hx
      refine Subgroup.mem_map.mpr ⟨xM, ?_, rfl⟩
      change qM xM ∈
        Subgroup.centralizer
          ((((section14KStar M K).subgroupOf M).map qM) :
            Set (M ⧸ Q₀.subgroupOf M))
      rw [Subgroup.mem_centralizer_iff]
      intro y hyKbarM
      rcases Subgroup.mem_map.mp hyKbarM with ⟨kM, hkKstarM, rfl⟩
      have hkKstarG : (kM : G) ∈ section14KStar M K := by
        simpa [Subgroup.mem_subgroupOf] using hkKstarM
      let kσ : σ := ⟨(kM : G), hKstar_sigma hkKstarG⟩
      have hkKstarσ : kσ ∈ (section14KStar M K).subgroupOf σ := by
        simpa [kσ, Subgroup.mem_subgroupOf] using hkKstarG
      have hkKbarσ : qσ kσ ∈ Kbarσ := by
        exact Subgroup.mem_map.mpr ⟨kσ, hkKstarσ, rfl⟩
      have hcommσ :
          qσ kσ * qσ xσ = qσ xσ * qσ kσ :=
        Subgroup.mem_centralizer_iff.mp hxσcent (qσ kσ) hkKbarσ
      rw [← map_mul, ← map_mul]
      apply (QuotientGroup.eq_iff_div_mem (N := Q₀.subgroupOf M)).2
      have hdivσ : kσ * xσ / (xσ * kσ) ∈ Q₀.subgroupOf σ := by
        apply (QuotientGroup.eq_iff_div_mem (N := Q₀.subgroupOf σ)).1
        change qσ (kσ * xσ) = qσ (xσ * kσ)
        simpa only [map_mul] using hcommσ
      have hdivG : ((kM * xM / (xM * kM) : M) : G) ∈ Q₀ := by
        have hdivGσ : ((kσ * xσ / (xσ * kσ) : σ) : G) ∈ Q₀ := by
          simpa [Subgroup.mem_subgroupOf] using hdivσ
        simpa [kσ, xM, hxσ_eq, div_eq_mul_inv, mul_assoc] using hdivGσ
      simpa [Subgroup.mem_subgroupOf] using hdivG
    have hCbarσK_normM : (CbarσK.subgroupOf M).Normal := by
      have hder_le_CbarσK :
          ambientDerivedSubgroup σ ≤ CbarσK := by
        intro x hx
        exact hF_le_CbarσK (hder_le_F (by simpa [σ] using hx))
      have hCbarσK_normσ : (CbarσK.subgroupOf σ).Normal := by
        refine section15_normal_of_derivedSubgroup_le
          (R := σ) (N := CbarσK.subgroupOf σ) ?_
        intro x hx
        have hx_amb : (x : G) ∈ ambientDerivedSubgroup σ := by
          have hx_sub :
              x ∈ (ambientDerivedSubgroup σ).subgroupOf σ := by
            simpa [section15_ambientDerived_subgroupOf_eq] using hx
          simpa [Subgroup.mem_subgroupOf] using hx_sub
        have hxC : (x : G) ∈ CbarσK := hder_le_CbarσK hx_amb
        simpa [Subgroup.mem_subgroupOf] using hxC
      have hσ_norm_CbarσK :
          σ ≤ Subgroup.normalizer (CbarσK : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hCbarσK_le_sigma).1
          hCbarσK_normσ
      have hK_norm_σ : K ≤ Subgroup.normalizer (σ : Set G) := by
        simpa [σ] using hK.1.trans (section15_msigma_le_normalizer (M := M))
      have hDkinv : K ≤ Subgroup.normalizer (D : Set G) :=
        section15_complement_D_K_invariant
          hM hMF hK hMFne hq hQ hQnormal hQMF hD
      have hKD_norm_Q₀ : K ⊔ D ≤ Subgroup.normalizer (Q₀ : Set G) := by
        simpa [Q₀] using
          section15_Q0_KD_invariant_of_K_invariant_complement
            hM hMF hK hMFne hq hQ hQnormal hQMF hD hDkinv
      have hK_norm_Q₀ : K ≤ Subgroup.normalizer (Q₀ : Set G) :=
        le_sup_left.trans hKD_norm_Q₀
      have hK_norm_Kstar :
          K ≤ Subgroup.normalizer (section14KStar M K : Set G) := by
        simpa [section14KStar, σ] using
          section15_le_normalizer_subgroupCentralizerIn
            (N := K) (E := σ) (A := K) hK_norm_σ
            (Subgroup.le_normalizer (H := K))
      have hK_norm_CbarσK :
          K ≤ Subgroup.normalizer (CbarσK : Set G) := by
        simpa [CbarσK, Kbarσ, qσ, Q₀, σ] using
          section15_le_normalizer_quotient_centralizer
            (H := σ) (N := Q₀) (A := section14KStar M K) (R := K)
            hQ₀_sigma hKstar_sigma hQ₀norm_sigma
            hK_norm_σ hK_norm_Q₀ hK_norm_Kstar
      have hM_eq_Kσ : M = K ⊔ σ := by
        simpa [σ] using
          (section15_MF_ne_msigma_implies_P1 hM hMF hK hMFne).2
      have hM_norm_CbarσK :
          M ≤ Subgroup.normalizer (CbarσK : Set G) := by
        rw [hM_eq_Kσ]
        exact sup_le hK_norm_CbarσK hσ_norm_CbarσK
      exact
        (Subgroup.normal_subgroupOf_iff_le_normalizer hCbarσK_le_M).2
          hM_norm_CbarσK
    have hCbarσK_le_CbarM : CbarσK ≤ CbarM := by
      simpa [CbarM, QbarM, qM, Q₀] using
        section15_quotient_centralizer_le_of_minimal_normal
          (M := M) (Q := Q) (N := Q₀) (A := section14KStar M K)
          (C := CbarσK) hQ₀M hQM hKstarM hCbarσK_le_M hKstarQ
          hQ₀normM hQbar_norm hQbar_min hKbarM_ne hCbarσK_normM
          hCbarσK_le_CbarK_M
    intro x hx
    rw [hF_eq_CbarM']
    exact hCbarσK_le_CbarM hx
  exact le_antisymm hF_le_CbarσK hCbarσK_le_F

/-- Theorem 15.2 L006-S0040: the displayed Fitting and centralizer chain. -/
private theorem CFSG.section15_fitting_quotient_centralizer_chain_of_theorem15_2_context
    {M MF K Q D : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMFne : MF ≠ section10Msigma M)
    (hq : q.val = Nat.card (section14KStar M K))
    (hQ : section12SylowSubgroupIn q Q M)
    (hQnormal : section10NormalIn Q M)
    (hQMF : Q ≤ MF)
    (hD : section15Theorem15_2ComplementData M K Q D) :
    ambientDerivedSubgroup (section10Msigma M) ≤ section8FittingSubgroup M ∧
      section8FittingSubgroup M = Q ⊔ subgroupCentralizerIn M Q ∧
        section15QuotientCentralizerEquals
          (section8FittingSubgroup M) M Q (subgroupCentralizerIn Q D) ∧
          section15QuotientCentralizerEquals
            (section8FittingSubgroup M) (section10Msigma M)
              (section14KStar M K) (subgroupCentralizerIn Q D) ∧
            section8FittingSubgroup M < section10Msigma M := by
  classical
  let Q₀ : Subgroup G := subgroupCentralizerIn Q D
  rcases section15_Q0_quotient_minimal_normal
      hM hMF hK hMFne hq hQ hQnormal hQMF hD with
    ⟨hQ₀M, hQM, hQ₀Q, hQ₀norm, hQbar_ne, hQbar_norm, hQbar_min⟩
  have hQ_le_F : Q ≤ section8FittingSubgroup M := by
    exact section12_le_fittingSubgroupOf_of_normalIn_nilpotent
      (G := G) hQnormal.1 hQnormal.2 (section15_sylowSubgroupIn_nilpotent hQ)
  have hQ_eq_pcore : Q = section15PCoreIn q M := by
    apply le_antisymm
    · intro x hxQ
      have hxM : x ∈ M := hQnormal.1 hxQ
      let xM : M := ⟨x, hxM⟩
      have hxQsub : xM ∈ Q.subgroupOf M := by
        simpa [xM, Subgroup.mem_subgroupOf] using hxQ
      have hxpcore : xM ∈ pCore q.val M := by
        simpa [section15_normal_sylowSubgroupIn_subgroupOf_eq_pCore hQ hQnormal]
          using hxQsub
      change x ∈ (pCore q.val M).map M.subtype
      exact Subgroup.mem_map.mpr ⟨xM, hxpcore, rfl⟩
    · rw [section15PCoreIn]
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      have hyQsub : y ∈ Q.subgroupOf M := by
        simpa [section15_normal_sylowSubgroupIn_subgroupOf_eq_pCore hQ hQnormal]
          using hy
      simpa [Subgroup.mem_subgroupOf] using hyQsub
  rcases section15_fitting_eq_Q_sup_centralizer_Q_of_theorem15_2_context
      hM hMF hK hMFne hq hQ hQnormal hQMF hD hQ_le_F hQ_eq_pcore with
    ⟨hF_eq, hquot_M, hF_lt_sigma⟩
  have hder_le_F :
      ambientDerivedSubgroup (section10Msigma M) ≤ section8FittingSubgroup M :=
    section15_msigma_derived_le_fitting_of_theorem15_2_context
      hM hMF hK hMFne hq hQ hQnormal hQMF hD hquot_M
  have hquot_sigma :
      section15QuotientCentralizerEquals
        (section8FittingSubgroup M) (section10Msigma M)
          (section14KStar M K) (subgroupCentralizerIn Q D) :=
    section15_kstar_quotient_centralizer_eq_fitting_of_theorem15_2_context
      hM hMF hK hMFne hq hQ hQnormal hQMF hD hF_lt_sigma.1 hder_le_F hquot_M
  exact ⟨hder_le_F, hF_eq, hquot_M, hquot_sigma, hF_lt_sigma⟩

private theorem CFSG.section15_g_conclusions_of_theorem15_2_context
    {M MF K Q D : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMFne : MF ≠ section10Msigma M)
    (hq : q.val = Nat.card (section14KStar M K))
    (hQ : section12SylowSubgroupIn q Q M)
    (hQnormal : section10NormalIn Q M)
    (hQMF : Q ≤ MF)
    (hD : section15Theorem15_2ComplementData M K Q D) :
    section15Theorem15_2GConclusions M K Q D := by
  classical
  rcases section15_fitting_quotient_centralizer_chain_of_theorem15_2_context
      hM hMF hK hMFne hq hQ hQnormal hQMF hD with
    ⟨hder_le_F, hF_eq, hquot_M, hquot_sigma, hF_lt_sigma⟩
  have hσD : section10Msigma M = ambientDerivedSubgroup M := hD.1
  have hsecond_eq :
      section15SecondDerivedSubgroup M =
        ambientDerivedSubgroup (section10Msigma M) :=
    section15_secondDerived_eq_ambientDerived_msigma_of_msigma_eq_derived hσD
  refine ⟨hsecond_eq, ?_, hF_eq, hquot_M, hquot_sigma, hF_lt_sigma, hσD⟩
  rw [hsecond_eq]
  exact hder_le_F

omit [IsMinCE G] in
private theorem CFSG.section15_le_centralizer_of_sylow_images
    {K X : Subgroup G}
    (hSylowCent : ∀ p : Nat.Primes, p ∈ subgroupPrimeSet X →
      ∀ S : Sylow p.val X,
        (S : Subgroup X).map X.subtype ≤ Subgroup.centralizer (K : Set G)) :
    X ≤ Subgroup.centralizer (K : Set G) := by
  classical
  haveI : Finite X := Subtype.finite
  let C : Subgroup X := (Subgroup.centralizer (K : Set G)).comap X.subtype
  have htop_le_C : (⊤ : Subgroup X) ≤ C := by
    rw [← Sylow.iSup_sylow_eq_top (G := X)]
    refine iSup_le ?_
    intro r
    refine iSup_le ?_
    intro hr
    have hrprime : Nat.Prime r := Nat.prime_of_mem_primeFactors hr
    let p : Nat.Primes := ⟨r, hrprime⟩
    haveI : Fact p.val.Prime := ⟨p.property⟩
    let S : Sylow p.val X := default
    change (S : Subgroup X) ≤ C
    intro y hyS
    change ((y : X) : G) ∈ Subgroup.centralizer (K : Set G)
    have hy_map : ((y : X) : G) ∈ ((S : Subgroup X).map X.subtype : Subgroup G) :=
      Subgroup.mem_map_of_mem X.subtype hyS
    have hpX : p ∈ subgroupPrimeSet X := by
      change p.val ∣ Nat.card X
      exact Nat.dvd_of_mem_primeFactors hr
    exact hSylowCent p hpX S hy_map
  intro x hxX
  let xX : X := ⟨x, hxX⟩
  have hxC : xX ∈ C := htop_le_C (show xX ∈ (⊤ : Subgroup X) by simp)
  change x ∈ Subgroup.centralizer (K : Set G) at hxC
  exact hxC

private theorem CFSG.section15_D_le_centralizer_Q_of_not_mem_beta
    {M MF K Q D : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (_hMF : section15MFSubgroup M MF)
    (_hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (_hMFne : MF ≠ section10Msigma M)
    (_hq : q.val = Nat.card (section14KStar M K))
    (hQ : section12SylowSubgroupIn q Q M)
    (hQnormal : section10NormalIn Q M)
    (_hQMF : Q ≤ MF)
    (hD : section15Theorem15_2ComplementData M K Q D)
    (hqβ : q ∉ section10BetaPrimes M) :
    D ≤ Subgroup.centralizer (Q : Set G) := by
  classical
  have hQq : IsPGroup q.val Q := by
    rcases hQ with ⟨P, hP⟩
    rw [← hP]
    change IsPGroup q.val ((P : Subgroup M).map M.subtype)
    exact IsPGroup.map (p := q.val) (H := (P : Subgroup M))
      P.isPGroup' M.subtype
  have hQnarrow : IsNarrowPGroup q.val Q := by
    rcases hQ with ⟨P, hP⟩
    have hPnarrow :
        IsNarrowPGroup q.val (P : Subgroup M) :=
      section10_sylow_narrow_of_not_mem_beta
        (G := G) hM hqβ P
    have hAmbNarrow :
        IsNarrowPGroup q.val (section10AmbientSylowSubgroup M P) :=
      section10_isNarrowPGroup_of_equiv
        (e := (Subgroup.equivMapOfInjective
          (f := M.subtype) (P : Subgroup M) M.subtype_injective).symm)
        hPnarrow
    exact
      section10_isNarrowPGroup_of_equiv
        (e := (MulEquiv.subgroupCongr hP).symm) hAmbNarrow
  have hM_norm_Q : M ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQnormal.1).1 hQnormal.2
  have hD_le_Mder : D ≤ ambientDerivedSubgroup M := by
    have hD_le_sigma : D ≤ section10Msigma M := hD.2.1.2.1
    intro x hxD
    have hxσ : x ∈ section10Msigma M := hD_le_sigma hxD
    simpa [hD.1] using hxσ
  have hD_le_der_normQ :
      D ≤ ambientDerivedSubgroup (Subgroup.normalizer (Q : Set G)) :=
    hD_le_Mder.trans (section12_ambientDerivedSubgroup_mono hM_norm_Q)
  have hDπ : IsPiSubgroup (G := G) ({q} : Set Nat.Primes)ᶜ D :=
    section15_complement_D_isPiSubgroup_q_compl hQ hQnormal hD.2.1
  apply section15_le_centralizer_of_sylow_images (K := Q) (X := D)
  intro p hpD S
  let P : Subgroup G := (S : Subgroup D).map D.subtype
  have hPp : IsPGroup p.val P := by
    simpa [P] using
      (IsPGroup.map (p := p.val) (H := (S : Subgroup D))
        S.isPGroup' D.subtype)
  have hP_le_D : P ≤ D := by
    intro x hxP
    rcases Subgroup.mem_map.mp hxP with ⟨y, _hy, rfl⟩
    exact y.property
  have hPder : P ≤ ambientDerivedSubgroup (Subgroup.normalizer (Q : Set G)) :=
    hP_le_D.trans hD_le_der_normQ
  have hpq : p ≠ q := by
    have hp_not_q : p ∈ ({q} : Set Nat.Primes)ᶜ := hDπ p hpD
    simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hp_not_q
  exact
    section10_le_centralizer_of_le_derived_normalizer_of_narrow
      (G := G) hpq hPp hPder hQq hQnarrow

/-- Theorem 15.2 L006-S0050: the prime `q=|K*|` lies in `β(M)`. -/
private theorem CFSG.section15_q_mem_beta_of_theorem15_2_context
    {M MF K Q D : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMFne : MF ≠ section10Msigma M)
    (hq : q.val = Nat.card (section14KStar M K))
    (hQ : section12SylowSubgroupIn q Q M)
    (hQnormal : section10NormalIn Q M)
    (hQMF : Q ≤ MF)
    (hD : section15Theorem15_2ComplementData M K Q D) :
    q ∈ section10BetaPrimes M := by
  classical
  by_contra hqβ
  have hDcentQ : D ≤ Subgroup.centralizer (Q : Set G) :=
    section15_D_le_centralizer_Q_of_not_mem_beta
      hM hMF hK hMFne hq hQ hQnormal hQMF hD hqβ
  have hQcentD : Q ≤ Subgroup.centralizer (D : Set G) := by
    intro x hxQ
    rw [Subgroup.mem_centralizer_iff]
    intro y hyD
    exact (Subgroup.mem_centralizer_iff.mp (hDcentQ hyD) x hxQ).symm
  let S : Subgroup G := section10Msigma M
  have hDcomp : section12ComplementIn S Q D := by
    simpa [S] using hD.2.1
  have hSleM : S ≤ M := by
    simpa [S] using section15_msigma_le
  have hQnormS : section10NormalIn Q S := by
    refine ⟨hDcomp.1, ?_⟩
    have hMleNormQ : M ≤ Subgroup.normalizer (Q : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQnormal.1).1 hQnormal.2
    exact
      (Subgroup.normal_subgroupOf_iff_le_normalizer hDcomp.1).2
        (hSleM.trans hMleNormQ)
  have hQnil : Group.IsNilpotent Q := section15_sylowSubgroupIn_nilpotent hQ
  have hSnil : Group.IsNilpotent S :=
    section15_nilpotent_of_central_complement
      hDcomp hQnormS hQnil hD.2.2.1 hQcentD
  exact (section15_MF_ne_msigma_not_nilpotent hM hMF hMFne) (by
    simpa [S] using hSnil)

omit [Finite G] [IsMinCE G] in
/-- Theorem 15.2(b), `q ∈ π(M_F)` part, extracted from `Q ≤ M_F`. -/
private theorem CFSG.section15_q_mem_MF_primeSet_of_normal_sylow
    {M MF K Q : Subgroup G} {q : Nat.Primes}
    (hq : q.val = Nat.card (section14KStar M K))
    (hKstarQ : section14KStar M K ≤ Q)
    (hQMF : Q ≤ MF) :
    q ∈ subgroupPrimeSet MF := by
  have hKstarMF : section14KStar M K ≤ MF := le_trans hKstarQ hQMF
  have hq_dvd_kstar : q.val ∣ Nat.card (section14KStar M K) := by
    rw [← hq]
  have hcard :
      Nat.card ((section14KStar M K).subgroupOf MF) =
        Nat.card (section14KStar M K) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKstarMF).toEquiv
  have hq_dvd_sub : q.val ∣ Nat.card ((section14KStar M K).subgroupOf MF) := by
    simpa [hcard] using hq_dvd_kstar
  exact hq_dvd_sub.trans
    (Subgroup.card_subgroup_dvd_card ((section14KStar M K).subgroupOf MF))

/-- Theorem 15.2 L001: package the initial chain from the exposed source
subclaims. -/
private theorem CFSG.section15_theorem15_2_basic_chain
    {M MF : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF) :
    ⊥ < MF ∧ MF ≤ section10Msigma M ∧
      section10Msigma M ≤ ambientDerivedSubgroup M ∧
        ambientDerivedSubgroup M < M := by
  exact ⟨section15_MF_nontrivial hM hMF,
    section15_MF_le_msigma hM hMF,
    section15_msigma_le_ambientDerived hM,
    section15_ambientDerived_lt_maximal hM⟩

/-- Theorem 15.2, initial chain: for every maximal subgroup,
`1 < M_F ≤ M_σ ≤ M' < M`. -/
public theorem CFSG.theorem_15_2_chain
    {M MF : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF) :
    ⊥ < MF ∧ MF ≤ section10Msigma M ∧
      section10Msigma M ≤ ambientDerivedSubgroup M ∧
        ambientDerivedSubgroup M < M := by
  exact section15_theorem15_2_basic_chain hM hMF

/-- Theorem 15.2(a): if `M_F ≠ M_σ`, then `M` has type `𝓟₁`, i.e.
`M = K M_σ`. -/
public theorem CFSG.theorem_15_2_a
    {M MF K : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMFne : MF ≠ section10Msigma M) :
    M ∈ section14MFamilyP1 G ∧ M = K ⊔ section10Msigma M := by
  exact section15_MF_ne_msigma_implies_P1 hM hMF hK hMFne

/-- Theorem 15.2(b): with `p = |K|`, `K* = C_{M_σ}(K)`, and
`q = |K*|`, `p` and `q` are primes and `q ∈ π(M_F) ∩ β(M)`. -/
public theorem CFSG.theorem_15_2_b
    {M MF K : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMFne : MF ≠ section10Msigma M) :
    ∃ p q : Nat.Primes,
      p.val = Nat.card K ∧ q.val = Nat.card (section14KStar M K) ∧
        q ∈ subgroupPrimeSet MF ∩ section10BetaPrimes M := by
  rcases section15_kstar_prime_and_normal_sylow hM hMF hK hMFne with
    ⟨q, hq, Q, hQ, hQnormal, hKstarQ, hQMF⟩
  rcases section15_theorem15_2_nilpotent_complement
      hM hMF hK hMFne hq hQ hQnormal hQMF with ⟨D, hD⟩
  rcases section15_p_card_prime_of_theorem15_2_context
      hM hMF hK hMFne hq hQ hQnormal hQMF hD with ⟨p, hp⟩
  have hqMF : q ∈ subgroupPrimeSet MF :=
    section15_q_mem_MF_primeSet_of_normal_sylow hq hKstarQ hQMF
  have hqBeta : q ∈ section10BetaPrimes M :=
    section15_q_mem_beta_of_theorem15_2_context
      hM hMF hK hMFne hq hQ hQnormal hQMF hD
  exact ⟨p, q, hp, hq, ⟨hqMF, hqBeta⟩⟩

/-- Theorem 15.2(c): `M` has a normal Sylow `q`-subgroup `Q` contained
in `M_F`, where `q = |K*|`. -/
public theorem CFSG.theorem_15_2_c
    {M MF K : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMFne : MF ≠ section10Msigma M) :
    ∃ q : Nat.Primes, q.val = Nat.card (section14KStar M K) ∧
      ∃ Q : Subgroup G,
        section12SylowSubgroupIn q Q M ∧ section10NormalIn Q M ∧ Q ≤ MF := by
  rcases section15_kstar_prime_and_normal_sylow hM hMF hK hMFne with
    ⟨q, hq, Q, hQ, hQnormal, _hKstarQ, hQMF⟩
  exact ⟨q, hq, Q, hQ, hQnormal, hQMF⟩

/-- Theorem 15.2(d): a complement `D` of the normal Sylow `q`-subgroup
`Q` in `M_σ = M'` is nilpotent. -/
public theorem CFSG.theorem_15_2_d
    {M MF K Q : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMFne : MF ≠ section10Msigma M)
    (hq : q.val = Nat.card (section14KStar M K))
    (hQ : section12SylowSubgroupIn q Q M)
    (hQnormal : section10NormalIn Q M)
    (hQMF : Q ≤ MF) :
    ∃ D : Subgroup G,
      section15Theorem15_2ComplementData M K Q D := by
  exact section15_theorem15_2_nilpotent_complement
    hM hMF hK hMFne hq hQ hQnormal hQMF


/-- Theorem 15.2(g): the displayed chain
`M'' = M_σ' ≤ F(M) = QC_M(Q) = C_M(Q̄) = C_{M_σ}(K* bar) < M_σ`,
and `M_σ = M'`. -/
public theorem CFSG.theorem_15_2_g
    {M MF K Q D : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section15MFSubgroup M MF)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M)
    (hMFne : MF ≠ section10Msigma M)
    (hq : q.val = Nat.card (section14KStar M K))
    (hQ : section12SylowSubgroupIn q Q M)
    (hQnormal : section10NormalIn Q M)
    (hQMF : Q ≤ MF)
    (hD : section15Theorem15_2ComplementData M K Q D) :
    section15Theorem15_2GConclusions M K Q D := by
  exact section15_g_conclusions_of_theorem15_2_context
    hM hMF hK hMFne hq hQ hQnormal hQMF hD

end Section15
