module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.proposition_12_15_c

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# proposition_12_15_d
-/

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_ambient_sylow_le
    {M : Subgroup G} {p : Nat.Primes} (P : Sylow p.val M) :
    section10AmbientSylowSubgroup M P ≤ M := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
  exact y.property

omit [IsMinCE G] in
private theorem CFSG.section12_normalizer_inf_sylow_le_right_of_sigma
    {M Mstar : Subgroup G} {q : Nat.Primes}
    {S : Sylow q.val (M ⊓ Mstar : Subgroup G)}
    (hMstar : Mstar ∈ section9MaximalSubgroups G)
    (hqσstar : q ∈ section10SigmaPrimes Mstar)
    (hSylowStar :
      section12SylowSubgroupIn q (section10AmbientSylowSubgroup (M ⊓ Mstar) S)
        Mstar) :
    Subgroup.normalizer
        ((section10AmbientSylowSubgroup (M ⊓ Mstar) S : Subgroup G) : Set G) ≤
      Mstar := by
  classical
  rcases hSylowStar with ⟨Pstar, hPstar⟩
  intro g hg
  refine theorem_10_1_d (G := G) (M := Mstar) (p := q) hMstar hqσstar Pstar ?_
  rw [hPstar, section12_conjBy_eq_of_mem_normalizer hg, ← hPstar]
  exact (section12_ambient_sylow_le (M := Mstar) (p := q) Pstar)

omit [IsMinCE G] in
private theorem CFSG.section12_global_sylow_of_inf_sylow_normalizer_le
    {M Mstar : Subgroup G} {q : Nat.Primes}
    {S : Sylow q.val (M ⊓ Mstar : Subgroup G)}
    (hnormM :
      Subgroup.normalizer
          ((section10AmbientSylowSubgroup (M ⊓ Mstar) S : Subgroup G) : Set G) ≤
        M)
    (hnormMstar :
      Subgroup.normalizer
          ((section10AmbientSylowSubgroup (M ⊓ Mstar) S : Subgroup G) : Set G) ≤
        Mstar) :
    ∃ Sg : Sylow q.val G,
      (Sg : Subgroup G) = section10AmbientSylowSubgroup (M ⊓ Mstar) S := by
  classical
  have : Fact q.val.Prime := ⟨q.property⟩
  have hnormInf :
      Subgroup.normalizer
          (section8SubgroupInAmbient (S : Subgroup (M ⊓ Mstar : Subgroup G)) : Set G) ≤
        M ⊓ Mstar := by
    intro g hg
    have hg' :
        g ∈ Subgroup.normalizer
          ((section10AmbientSylowSubgroup (M ⊓ Mstar) S : Subgroup G) : Set G) := by
      simpa [section10AmbientSylowSubgroup, section8SubgroupInAmbient] using hg
    exact ⟨hnormM hg', hnormMstar hg'⟩
  rcases section8SubgroupInAmbient_sylow_of_normalizer_le
      (G := G) (p := q.val) (M := M ⊓ Mstar) S hnormInf with ⟨Sg, hSg⟩
  refine ⟨Sg, ?_⟩
  simpa [section10AmbientSylowSubgroup, section8SubgroupInAmbient] using hSg

omit [IsMinCE G] in
private theorem CFSG.section12_Mbeta_eq_Malpha_of_alphaPrimes_eq_betaPrimes
    {M : Subgroup G} (hαβ : section10AlphaPrimes M = section10BetaPrimes M) :
    section10Mbeta M = section10Malpha M := by
  simp [section10Mbeta, section10Malpha, section10MbetaSubgroup,
    section10MalphaSubgroup, hαβ]

omit [IsMinCE G] in
private theorem CFSG.section12_Mbeta_ne_bot_of_inf_sup_mbeta_eq
    {M Mstar : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMstar : Mstar ∈ section9MaximalSubgroups G)
    (hMstar_ne : Mstar ≠ M)
    (hjoin : M ⊓ Mstar ⊔ section10Mbeta Mstar = Mstar) :
    section10Mbeta Mstar ≠ ⊥ := by
  intro hβbot
  have hMstar_le_M : Mstar ≤ M := by
    intro x hx
    have hxjoin : x ∈ M ⊓ Mstar ⊔ section10Mbeta Mstar := by
      rw [hjoin]
      exact hx
    have hxinf : x ∈ M ⊓ Mstar := by
      simpa [hβbot] using hxjoin
    exact hxinf.1
  have hM_eq_Mstar : M = Mstar := (hMstar.le_iff_eq hM.1).mp hMstar_le_M
  exact hMstar_ne hM_eq_Mstar.symm

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_Msigma_le (M : Subgroup G) :
    section10Msigma M ≤ M := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
  exact y.property

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_Malpha_le (M : Subgroup G) :
    section10Malpha M ≤ M := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
  exact y.property

omit [IsMinCE G] in
public theorem CFSG.section12_Mbeta_le (M : Subgroup G) :
    section10Mbeta M ≤ M := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
  exact y.property

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_complementIn_inf_of_complementToMsigma_le_of_inf_bot
    {M N E : Subgroup G}
    (hcomp : section12ComplementToMsigma N E)
    (hE_le_M : E ≤ M)
    (hσ_inf_M : section10Msigma N ⊓ M = ⊥) :
    section12ComplementIn N (section10Msigma N) (M ⊓ N) := by
  classical
  rcases hcomp with ⟨hσN, hEN, hNsup, _hdisj⟩
  refine ⟨hσN, inf_le_right, ?_, ?_⟩
  · apply le_antisymm
    · intro x hxN
      have hxSup : x ∈ section10Msigma N ⊔ E := by
        rw [← hNsup]
        exact hxN
      have hE_norm_σ : E ≤ Subgroup.normalizer (section10Msigma N : Set G) :=
        hEN.trans section12_le_normalizer_msigma
      change x ∈ ((section10Msigma N ⊔ E : Subgroup G) : Set G) at hxSup
      rw [Subgroup.coe_mul_of_right_le_normalizer_left
          (N := section10Msigma N) (H := E) hE_norm_σ, Set.mem_mul] at hxSup
      rcases hxSup with ⟨s, hsσ, e, heE, hse⟩
      have hsSup : s ∈ section10Msigma N ⊔ (M ⊓ N) :=
        (le_sup_left : section10Msigma N ≤ section10Msigma N ⊔ (M ⊓ N)) hsσ
      have heInf : e ∈ M ⊓ N := ⟨hE_le_M heE, hEN heE⟩
      have heSup : e ∈ section10Msigma N ⊔ (M ⊓ N) :=
        (le_sup_right : M ⊓ N ≤ section10Msigma N ⊔ (M ⊓ N)) heInf
      have hs_mul_e : s * e ∈ section10Msigma N ⊔ (M ⊓ N) :=
        Subgroup.mul_mem (section10Msigma N ⊔ (M ⊓ N)) hsSup heSup
      simpa [hse] using hs_mul_e
    · exact sup_le hσN inf_le_right
  · rw [Subgroup.disjoint_def]
    intro x hxσ hxMN
    have hxbot : x ∈ (⊥ : Subgroup G) := by
      simpa [hσ_inf_M] using (show x ∈ section10Msigma N ⊓ M from ⟨hxσ, hxMN.1⟩)
    simpa using hxbot

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12Malpha_subgroupOf_eq {M : Subgroup G} :
    (section10Malpha M).subgroupOf M = section10MalphaSubgroup M := by
  change (piCoreIn (section10AlphaPrimes M) M).subgroupOf M =
    piCore (section10AlphaPrimes M) M
  exact piCore_map_subtype_subgroupOf (G := G) (section10AlphaPrimes M) M

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_local_sup_malpha_eq_top
    {L N : Subgroup G} (hLN : L ≤ N)
    (hjoin : L ⊔ section10Malpha N = N) :
    section10MalphaSubgroup N ⊔ L.subgroupOf N = ⊤ := by
  calc
    section10MalphaSubgroup N ⊔ L.subgroupOf N =
        (section10Malpha N).subgroupOf N ⊔ L.subgroupOf N := by
      rw [section12Malpha_subgroupOf_eq]
    _ = (section10Malpha N ⊔ L).subgroupOf N := by
      symm
      exact Subgroup.subgroupOf_sup (A := section10Malpha N) (A' := L) (B := N)
        (section12_Malpha_le N) hLN
    _ = ⊤ := by
      rw [sup_comm, hjoin]
      simp


omit [IsMinCE G] in
public theorem CFSG.section12_prime_dvd_card_of_primeRank_pos
    {R : Type*} [Group R] [Finite R] {p : Nat.Primes}
    (hpos : 0 < primeRank p.val R) :
    p.val ∣ Nat.card R := by
  classical
  let T : Set ℕ :=
    {n : ℕ | ∃ A : Subgroup R, IsPGroup p.val A ∧ IsMulCommutative A ∧
      n ≤ generatorRank A}
  have hTbdd : BddAbove T := by
    refine ⟨Nat.card R, ?_⟩
    intro n hn
    rcases hn with ⟨A, _hAp, _hAcomm, hnA⟩
    exact hnA.trans <|
      (section8_generatorRank_le_natCard A).trans (Subgroup.card_le_card_group A)
  have hTnonempty : T.Nonempty :=
    ⟨0, ⊥, IsPGroup.of_bot (p := p.val) (G := R), inferInstance, Nat.zero_le _⟩
  have hSup_mem : sSup T ∈ T := Nat.sSup_mem hTnonempty hTbdd
  rcases hSup_mem with ⟨A, hAp, _hAcomm, hAgen⟩
  have hAgen_pos : 0 < generatorRank A := by
    have hSup_pos : 0 < sSup T := by
      simpa [primeRank, T] using hpos
    exact lt_of_lt_of_le hSup_pos hAgen
  have hAnontrivial : Nontrivial A := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    have : Subsingleton A := hsub
    have hgen0 : generatorRank A = 0 := by
      rw [generatorRank_eq_group_rank]
      have : Group.FG A := inferInstance
      apply le_antisymm ?_ (Nat.zero_le _)
      refine Group.rank_le (G := A) (S := ∅) ?_
      rw [Finset.coe_empty, Subgroup.closure_empty]
      exact (Subsingleton.elim (⊤ : Subgroup A) ⊥).symm
    omega
  have : Fact p.val.Prime := ⟨p.property⟩
  have hpA : p.val ∣ Nat.card A := by
    rcases (IsPGroup.nontrivial_iff_card (p := p.val) (G := A) (hG := hAp)).1
        hAnontrivial with
      ⟨n, hn_pos, hcard⟩
    rw [hcard]
    exact dvd_pow_self p.val hn_pos.ne'
  exact hpA.trans (Subgroup.card_subgroup_dvd_card A)

omit [IsMinCE G] in
private theorem CFSG.section12_sylow_inf_derived_eq_bot_of_not_mem_derived
    {H : Type*} [Group H] [Finite H] {p : Nat.Primes}
    (S : Sylow p.val H) (hpD : p ∉ subgroupPrimeSet (derivedSubgroup H)) :
    (S : Subgroup H) ⊓ derivedSubgroup H = ⊥ := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  by_contra hne
  let C : Subgroup H := (S : Subgroup H) ⊓ derivedSubgroup H
  have hC_ne : C ≠ ⊥ := by
    simpa [C] using hne
  have hC_le_D : C ≤ derivedSubgroup H := by
    intro x hx
    exact hx.2
  have hC_le_S : C ≤ (S : Subgroup H) := by
    intro x hx
    exact hx.1
  let CD : Subgroup (derivedSubgroup H) := C.subgroupOf (derivedSubgroup H)
  let CS : Subgroup (S : Subgroup H) := C.subgroupOf (S : Subgroup H)
  have hCSp : IsPGroup p.val CS :=
    S.isPGroup'.to_subgroup CS
  have hCp : IsPGroup p.val C :=
    hCSp.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := C) (K := (S : Subgroup H)) hC_le_S)
  have hCDp : IsPGroup p.val CD :=
    hCp.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := C) (K := derivedSubgroup H) hC_le_D).symm
  have hCDne : CD ≠ ⊥ := by
    intro hbot
    exact hC_ne ((Subgroup.subgroupOf_eq_bot.mp hbot).eq_bot_of_le hC_le_D)
  exact hpD
    (section8_prime_mem_subgroupPrimeSet_of_nontrivial_pSubgroup
      (A := derivedSubgroup H) (B := CD) hCDp hCDne)

omit [IsMinCE G] in
public theorem CFSG.section12_prime_not_dvd_index_of_sup_hall
    {H : Type*} [Group H] [Finite H] {π : Set Nat.Primes}
    {K U : Subgroup H} [K.Normal] {p : Nat.Primes}
    (hKHall : IsHallSubgroup π K) (hpπ : p ∉ π)
    (hKU : K ⊔ U = ⊤) :
    ¬ p.val ∣ U.index := by
  intro hpU
  have hrel_eq :
      U.relIndex (U ⊔ K) = (U ⊓ K).relIndex K := by
    have hK_rel :
        K.relIndex (U ⊔ K) = (U ⊓ K).relIndex U := by
      calc
        K.relIndex (U ⊔ K) = K.relIndex U := by
          simp
        _ = (U ⊓ K).relIndex U := by
          symm
          simpa [inf_comm] using (Subgroup.inf_relIndex_left (H := U) (K := K))
    have hmul :
        (U ⊓ K).relIndex U * U.relIndex (U ⊔ K) =
          (U ⊓ K).relIndex K * (U ⊓ K).relIndex U := by
      calc
        (U ⊓ K).relIndex U * U.relIndex (U ⊔ K) =
            (U ⊓ K).relIndex (U ⊔ K) := by
          exact
            Subgroup.relIndex_mul_relIndex (H := U ⊓ K) (K := U) (L := U ⊔ K)
              inf_le_left le_sup_left
        _ = (U ⊓ K).relIndex K * K.relIndex (U ⊔ K) := by
          symm
          exact
            Subgroup.relIndex_mul_relIndex (H := U ⊓ K) (K := K) (L := U ⊔ K)
              inf_le_right le_sup_right
        _ = (U ⊓ K).relIndex K * (U ⊓ K).relIndex U := by
          rw [hK_rel]
    have hrel_pos : 0 < (U ⊓ K).relIndex U := by
      have hrel_ne_zero : (U ⊓ K).relIndex U ≠ 0 := by
        dsimp [Subgroup.relIndex]
        exact Subgroup.index_ne_zero_of_finite (H := (U ⊓ K).subgroupOf U)
      exact Nat.pos_of_ne_zero hrel_ne_zero
    have hmul' :
        (U ⊓ K).relIndex U * U.relIndex (U ⊔ K) =
          (U ⊓ K).relIndex U * (U ⊓ K).relIndex K := by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
    exact Nat.eq_of_mul_eq_mul_left hrel_pos hmul'
  have hidx_eq : U.relIndex (U ⊔ K) = U.index := by
    rw [show U ⊔ K = ⊤ by simpa [sup_comm] using hKU]
    exact Subgroup.relIndex_top_right (H := U)
  have hrel_dvd_cardK : U.relIndex (U ⊔ K) ∣ Nat.card K := by
    rw [hrel_eq]
    exact Subgroup.relIndex_dvd_card (H := U ⊓ K) (K := K)
  have hidx_dvd_cardK : U.index ∣ Nat.card K := by
    simpa [hidx_eq] using hrel_dvd_cardK
  exact hpπ (hKHall.p_in_pi_of_p_dvd_card p (hpU.trans hidx_dvd_cardK))

omit [IsMinCE G] in
public theorem CFSG.section12_sylow_map_subtype_of_sup_hall
    {H : Type*} [Group H] [Finite H] {π : Set Nat.Primes}
    {K U : Subgroup H} [K.Normal] {p : Nat.Primes}
    (hKHall : IsHallSubgroup π K) (hpπ : p ∉ π)
    (hKU : K ⊔ U = ⊤) (S : Sylow p.val U) :
    ∃ T : Sylow p.val H, (T : Subgroup H) = (S : Subgroup U).map U.subtype := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  let SG : Subgroup H := (S : Subgroup U).map U.subtype
  have hSGp : IsPGroup p.val SG := by
    simpa [SG] using
      IsPGroup.map (p := p.val) (H := (S : Subgroup U)) S.isPGroup' U.subtype
  have hU_not_index : ¬ p.val ∣ U.index :=
    section12_prime_not_dvd_index_of_sup_hall hKHall hpπ hKU
  have hSG_not_index : ¬ p.val ∣ SG.index := by
    intro hpidx
    have hidx : SG.index = (S : Subgroup U).index * U.index := by
      simpa [SG] using Subgroup.index_map_subtype (H := U) (S : Subgroup U)
    have hp_prod : p.val ∣ (S : Subgroup U).index * U.index := by
      simpa [hidx] using hpidx
    rcases p.property.dvd_or_dvd hp_prod with hpS | hpU
    · exact S.not_dvd_index hpS
    · exact hU_not_index hpU
  let T : Sylow p.val H := hSGp.toSylow hSG_not_index
  exact ⟨T, IsPGroup.toSylow_coe hSGp hSG_not_index⟩

private theorem CFSG.section12_tau1_transfer_of_malpha_products
    {M Mstar : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMstar : Mstar ∈ section9MaximalSubgroups G)
    (hjoinM : M ⊓ Mstar ⊔ section10Malpha M = M)
    (hjoinStar : M ⊓ Mstar ⊔ section10Malpha Mstar = Mstar)
    {r : Nat.Primes}
    (hrτstar : r ∈ section12Tau1Primes Mstar)
    (hrαM : r ∉ section10AlphaPrimes M) :
    r ∈ section12Tau1Primes M := by
  classical
  have : Fact r.val.Prime := ⟨r.property⟩
  rcases (by simpa [section12Tau1Primes] using hrτstar) with
    ⟨hrσstar, hrDstar, hrankStar⟩
  have hrαstar : r ∉ section10AlphaPrimes Mstar := by
    intro hrα
    exact hrσstar (section12_sigmaPrimes_mem_of_alphaPrimes_mem hMstar hrα)
  let U : Subgroup G := M ⊓ Mstar
  let UM : Subgroup M := U.subgroupOf M
  let Ustar : Subgroup Mstar := U.subgroupOf Mstar
  have hUM_top : section10MalphaSubgroup M ⊔ UM = ⊤ := by
    simpa [U, UM] using
      section12_local_sup_malpha_eq_top
        (L := M ⊓ Mstar) (N := M) inf_le_left hjoinM
  have hUstar_top : section10MalphaSubgroup Mstar ⊔ Ustar = ⊤ := by
    simpa [U, Ustar] using
      section12_local_sup_malpha_eq_top
        (L := M ⊓ Mstar) (N := Mstar) inf_le_right hjoinStar
  have hHallαM : IsHallSubgroup (section10AlphaPrimes M) (section10MalphaSubgroup M) :=
    (theorem_10_2_a (G := G) hM).2
  have hHallαStar :
      IsHallSubgroup (section10AlphaPrimes Mstar) (section10MalphaSubgroup Mstar) :=
    (theorem_10_2_a (G := G) hMstar).2
  have hrankStar_pos : 0 < primeRank r.val Mstar := by
    omega
  have hrMstar_card : r.val ∣ Nat.card Mstar :=
    section12_prime_dvd_card_of_primeRank_pos (R := Mstar) hrankStar_pos
  have hUstar_not_index : ¬ r.val ∣ Ustar.index :=
    section12_prime_not_dvd_index_of_sup_hall
      (H := Mstar) (π := section10AlphaPrimes Mstar)
      hHallαStar hrαstar hUstar_top
  have hrUstar_card : r.val ∣ Nat.card Ustar := by
    have hmul : Ustar.index * Nat.card Ustar = Nat.card Mstar :=
      Subgroup.index_mul_card (H := Ustar)
    have hprod : r.val ∣ Ustar.index * Nat.card Ustar := by
      simpa [hmul] using hrMstar_card
    rcases r.property.dvd_or_dvd hprod with hidx | hcard
    · exact False.elim (hUstar_not_index hidx)
    · exact hcard
  let eUM : UM ≃* U :=
    Subgroup.subgroupOfEquivOfLe (H := U) (K := M) (by
      intro x hx
      exact hx.1)
  let eUstar : Ustar ≃* U :=
    Subgroup.subgroupOfEquivOfLe (H := U) (K := Mstar) (by
      intro x hx
      exact hx.2)
  let eU : UM ≃* Ustar := eUM.trans eUstar.symm
  have hUM_card_eq : Nat.card UM = Nat.card Ustar :=
    Nat.card_congr eU.toEquiv
  have hrUM_card : r.val ∣ Nat.card UM := by
    simpa [hUM_card_eq] using hrUstar_card
  have hrM_card : r ∈ subgroupPrimeSet M :=
    hrUM_card.trans (Subgroup.card_subgroup_dvd_card UM)
  let SU : Sylow r.val UM := Classical.choice (Sylow.nonempty (p := r.val) (G := UM))
  rcases section12_sylow_map_subtype_of_sup_hall
      (H := M) (π := section10AlphaPrimes M)
      (K := section10MalphaSubgroup M) (U := UM)
      hHallαM hrαM hUM_top SU with
    ⟨SM, hSM_eq⟩
  let SUstar : Sylow r.val Ustar :=
    SU.mapSurjective (f := eU.toMonoidHom) eU.surjective
  rcases section12_sylow_map_subtype_of_sup_hall
      (H := Mstar) (π := section10AlphaPrimes Mstar)
      (K := section10MalphaSubgroup Mstar) (U := Ustar)
      hHallαStar hrαstar hUstar_top SUstar with
    ⟨SMstar, hSMstar_eq⟩
  have hrG_card : r.val ∣ Nat.card G :=
    hrMstar_card.trans (Subgroup.card_subgroup_dvd_card Mstar)
  have hrodd : r.val ≠ 2 :=
    Odd.ne_two_of_dvd_nat IsMinCE.odd_order hrG_card
  have hSMstar_cyc : IsCyclic (SMstar : Subgroup Mstar) :=
    section12_sylow_cyclic_of_primeRank_le_one hrodd (by omega) SMstar
  have hSUstar_cyc : IsCyclic (SUstar : Subgroup Ustar) := by
    have hmap_cyc : IsCyclic ((SUstar : Subgroup Ustar).map Ustar.subtype) := by
      exact (MulEquiv.subgroupCongr hSMstar_eq).isCyclic.mp hSMstar_cyc
    let eS : (SUstar : Subgroup Ustar) ≃*
        ((SUstar : Subgroup Ustar).map Ustar.subtype) :=
      Subgroup.equivMapOfInjective
        (f := Ustar.subtype) (SUstar : Subgroup Ustar) Ustar.subtype_injective
    exact eS.isCyclic.mpr hmap_cyc
  have hSU_cyc : IsCyclic (SU : Subgroup UM) := by
    let SUmap : Subgroup Ustar := (SU : Subgroup UM).map eU.toMonoidHom
    have hSUstar_eq : (SUstar : Subgroup Ustar) = SUmap := by
      simp [SUstar, SUmap]
    have hSUmap_cyc : IsCyclic SUmap := by
      exact (MulEquiv.subgroupCongr hSUstar_eq).isCyclic.mp hSUstar_cyc
    let eS : (SU : Subgroup UM) ≃* SUmap :=
      Subgroup.equivMapOfInjective
        (f := eU.toMonoidHom) (SU : Subgroup UM) eU.injective
    exact eS.isCyclic.mpr hSUmap_cyc
  have hSM_cyc : IsCyclic (SM : Subgroup M) := by
    have hmap_cyc : IsCyclic ((SU : Subgroup UM).map UM.subtype) := by
      let eS : (SU : Subgroup UM) ≃* ((SU : Subgroup UM).map UM.subtype) :=
        Subgroup.equivMapOfInjective
          (f := UM.subtype) (SU : Subgroup UM) UM.subtype_injective
      exact eS.isCyclic.mp hSU_cyc
    exact (MulEquiv.subgroupCongr hSM_eq).isCyclic.mpr hmap_cyc
  have hrankM_le : primeRank r.val M ≤ 1 :=
    section12_primeRank_le_one_of_cyclic_sylow (R := M) SM hSM_cyc
  have hrankM_pos : 1 ≤ primeRank r.val M :=
    section12_primeRank_pos_of_mem_subgroupPrimeSet (R := M) hrM_card
  have hrankM : primeRank r.val M = 1 := le_antisymm hrankM_le hrankM_pos
  have hSM_le_UM : (SM : Subgroup M) ≤ UM := by
    intro x hx
    have hxmap : x ∈ (SU : Subgroup UM).map UM.subtype := by
      simpa [hSM_eq] using hx
    rcases Subgroup.mem_map.mp hxmap with ⟨y, _hy, rfl⟩
    exact y.property
  have hKpiM : IsPiSubgroup (G := M) ({r} : Set Nat.Primes)ᶜ
      (section10MalphaSubgroup M) := by
    intro s hs
    rw [Set.mem_compl_iff]
    intro hsr
    have hsα : s ∈ section10AlphaPrimes M :=
      hHallαM.p_in_pi_of_p_dvd_card s hs
    have hsr_eq : s = r := Set.mem_singleton_iff.mp hsr
    exact hrαM (by simpa [hsr_eq] using hsα)
  have hcopM :
      Nat.Coprime (Nat.card (SM : Subgroup M))
        (Nat.card (section10MalphaSubgroup M)) :=
    section8_coprime_card_of_isPGroup_of_isPiSubgroup_compl
      (G := M) (π := ({r} : Set Nat.Primes)) (r := r)
      (by simp) SM.isPGroup' hKpiM
  have : Group.IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.2 hM.1)
  have hSM_infM_eq :
      (SM : Subgroup M) ⊓ derivedSubgroup M =
        (SM : Subgroup M) ⊓ ⁅UM, UM⁆ := by
    simpa using
      lemma_6_5_a (G := M) (K := section10MalphaSubgroup M) (U := UM)
        (H := (SM : Subgroup M)) hUM_top hSM_le_UM hcopM
  have hSMstar_infD_bot :
      (SMstar : Subgroup Mstar) ⊓ derivedSubgroup Mstar = ⊥ :=
    section12_sylow_inf_derived_eq_bot_of_not_mem_derived SMstar hrDstar
  have hSM_infD_bot : (SM : Subgroup M) ⊓ derivedSubgroup M = ⊥ := by
    rw [hSM_infM_eq]
    apply le_bot_iff.mp
    intro x hx
    have hxSM : x ∈ (SM : Subgroup M) := hx.1
    have hxCommM : x ∈ ⁅UM, UM⁆ := hx.2
    have hxUM : x ∈ UM := hSM_le_UM hxSM
    let xU : UM := ⟨x, hxUM⟩
    have hxSU : xU ∈ (SU : Subgroup UM) := by
      have hxmap : x ∈ (SU : Subgroup UM).map UM.subtype := by
        simpa [hSM_eq] using hxSM
      rcases Subgroup.mem_map.mp hxmap with ⟨y, hySU, hyx⟩
      have hy_eq : y = xU := Subtype.ext hyx
      simpa [← hy_eq] using hySU
    have hxCommG : (x : G) ∈ ⁅U, U⁆ := by
      have hUMmap : UM.map M.subtype = U := by
        ext z
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact hy
        · intro hz
          exact ⟨⟨z, hz.1⟩, hz, rfl⟩
      have hcomm_map : (⁅UM, UM⁆).map M.subtype = ⁅U, U⁆ := by
        calc
          (⁅UM, UM⁆).map M.subtype =
              ⁅UM.map M.subtype, UM.map M.subtype⁆ := by
            simpa using (Subgroup.map_commutator (H₁ := UM) (H₂ := UM) M.subtype)
          _ = ⁅U, U⁆ := by rw [hUMmap]
      have hx_map : (x : G) ∈ (⁅UM, UM⁆).map M.subtype :=
        ⟨x, hxCommM, rfl⟩
      simpa [hcomm_map] using hx_map
    have hxMstar : (x : G) ∈ Mstar := hxUM.2
    let xStar : Mstar := ⟨(x : G), hxMstar⟩
    have hxDstar : xStar ∈ derivedSubgroup Mstar := by
      have hxCommStarG : (x : G) ∈ ⁅Mstar, Mstar⁆ :=
        (Subgroup.commutator_mono (H₁ := U) (H₂ := U)
          (by intro z hz; exact hz.2) (by intro z hz; exact hz.2)) hxCommG
      have hxmap : (x : G) ∈ (_root_.commutator Mstar).map Mstar.subtype := by
        simpa [Subgroup.map_subtype_commutator] using hxCommStarG
      rcases Subgroup.mem_map.mp hxmap with ⟨z, hz, hzx⟩
      have hz_eq : z = xStar := Subtype.ext hzx
      simpa [xStar, hz_eq, derivedSubgroup, derivedSeries_one, commutator] using hz
    have hxSMstar : xStar ∈ (SMstar : Subgroup Mstar) := by
      let ystar : Ustar := eU xU
      have hystar_SU : ystar ∈ (SUstar : Subgroup Ustar) := by
        change eU xU ∈ (SU : Subgroup UM).map eU.toMonoidHom
        exact ⟨xU, hxSU, rfl⟩
      have hystar_val : ((ystar : Ustar) : G) = (x : G) := by
        rfl
      have hxmap : xStar ∈ (SUstar : Subgroup Ustar).map Ustar.subtype := by
        refine ⟨ystar, hystar_SU, ?_⟩
        apply Subtype.ext
        exact hystar_val
      simpa [hSMstar_eq] using hxmap
    have hxInfStar : xStar ∈ (SMstar : Subgroup Mstar) ⊓ derivedSubgroup Mstar :=
      ⟨hxSMstar, hxDstar⟩
    have hxG_one : (x : G) = 1 := by
      have hxStar_one : xStar = 1 := by
        have hxbotStar : xStar ∈ (⊥ : Subgroup Mstar) := by
          rw [← hSMstar_infD_bot]
          exact hxInfStar
        simpa using hxbotStar
      exact congrArg Subtype.val hxStar_one
    exact Subtype.ext hxG_one
  have hrD : r ∉ subgroupPrimeSet (derivedSubgroup M) := by
    intro hrD
    exact section12_sylow_inf_normal_ne_bot_of_prime_dvd_normal
      (R := M) (D := derivedSubgroup M) SM hrD hSM_infD_bot
  have hrσ : r ∉ section10SigmaPrimes M := by
    intro hrσM
    have hSM_le_D : (SM : Subgroup M) ≤ derivedSubgroup M :=
      section10_sigma_sylow_le_derivedSubgroup (G := G) hM hrσM SM
    have hSM_bot : (SM : Subgroup M) = ⊥ := by
      apply le_bot_iff.mp
      intro x hx
      have hxinf : x ∈ (SM : Subgroup M) ⊓ derivedSubgroup M :=
        ⟨hx, hSM_le_D hx⟩
      have hxbot : x ∈ (⊥ : Subgroup M) := by
        rw [← hSM_infD_bot]
        exact hxinf
      simpa using hxbot
    have hSM_ne : (SM : Subgroup M) ≠ ⊥ :=
      Sylow.ne_bot_of_dvd_card (G := M) SM hrM_card
    exact hSM_ne hSM_bot
  simpa [section12Tau1Primes] using ⟨hrσ, hrD, hrankM⟩

private theorem CFSG.section12_tau1_subset_tau1_union_alpha_of_sigma_transfer
    {M Mstar X : Subgroup G} {q : Nat.Primes}
    {S : Sylow q.val (M ⊓ Mstar : Subgroup G)}
    (hM : M ∈ section9MaximalSubgroups G)
    (hq : q ∈ section10SigmaPrimes M)
    (hX : X ≤ M) (hXne : X ≠ ⊥) (hXq : IsPGroup q.val X)
    (hMstar : Mstar ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (X : Set G)))
    (hMstar_ne : Mstar ≠ M)
    (hXS : X ≤ section10AmbientSylowSubgroup (M ⊓ Mstar) S)
    (hqσstar : q ∈ section10SigmaPrimes Mstar) :
    section12Tau1Primes Mstar ⊆ section12Tau1Primes M ∪ section10AlphaPrimes M := by
  classical
  have hnormM :
      Subgroup.normalizer
          ((section10AmbientSylowSubgroup (M ⊓ Mstar) S : Subgroup G) : Set G) ≤
        M :=
    proposition_12_15_b (G := G) (M := M) (Mstar := Mstar) (X := X) (q := q)
      (S := S) hM hq hX hXne hXq hMstar hMstar_ne hXS
  have hSylowStar :
      section12SylowSubgroupIn q (section10AmbientSylowSubgroup (M ⊓ Mstar) S)
        Mstar :=
    proposition_12_15_c (G := G) (M := M) (Mstar := Mstar) (X := X) (q := q)
      (S := S) hM hq hX hXne hXq hMstar hMstar_ne hXS
  have hnormMstar :
      Subgroup.normalizer
          ((section10AmbientSylowSubgroup (M ⊓ Mstar) S : Subgroup G) : Set G) ≤
        Mstar :=
    section12_normalizer_inf_sylow_le_right_of_sigma
      (M := M) (Mstar := Mstar) (q := q) (S := S) hMstar.1 hqσstar hSylowStar
  rcases section12_global_sylow_of_inf_sylow_normalizer_le
      (M := M) (Mstar := Mstar) (q := q) (S := S) hnormM hnormMstar with
    ⟨Sg, hSg⟩
  have hSexists :
      ∃ p : Nat.Primes, ∃ S : Sylow p.val G,
        Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ M ⊓ Mstar := by
    refine ⟨q, Sg, ?_⟩
    intro g hg
    have hg' :
        g ∈ Subgroup.normalizer
          ((section10AmbientSylowSubgroup (M ⊓ Mstar) S : Subgroup G) : Set G) := by
      simpa [hSg] using hg
    exact ⟨hnormM hg', hnormMstar hg'⟩
  have hSexists_swap :
      ∃ p : Nat.Primes, ∃ S : Sylow p.val G,
        Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ Mstar ⊓ M := by
    refine ⟨q, Sg, ?_⟩
    intro g hg
    have hg' :
        g ∈ Subgroup.normalizer
          ((section10AmbientSylowSubgroup (M ⊓ Mstar) S : Subgroup G) : Set G) := by
      simpa [hSg] using hg
    exact ⟨hnormMstar hg', hnormM hg'⟩
  rcases corollary_10_9_b (G := G) (M := M) (H := Mstar)
      hM hMstar.1 hMstar_ne hSexists_swap with
    ⟨hjoinMβ, hαβM⟩
  rcases corollary_10_9_b (G := G) (M := Mstar) (H := M)
      hMstar.1 hM hMstar_ne.symm hSexists with
    ⟨hjoinStarβ, hαβStar⟩
  have hjoinM : M ⊓ Mstar ⊔ section10Malpha M = M := by
    simpa [inf_comm, section12_Mbeta_eq_Malpha_of_alphaPrimes_eq_betaPrimes hαβM]
      using hjoinMβ
  have hjoinStar : M ⊓ Mstar ⊔ section10Malpha Mstar = Mstar := by
    simpa [section12_Mbeta_eq_Malpha_of_alphaPrimes_eq_betaPrimes hαβStar]
      using hjoinStarβ
  intro r hrτstar
  by_cases hrαM : r ∈ section10AlphaPrimes M
  · exact Or.inr hrαM
  · exact Or.inl
      (section12_tau1_transfer_of_malpha_products
        (G := G) (M := M) (Mstar := Mstar) hM hMstar.1 hjoinM hjoinStar
        hrτstar hrαM)

/-- Proposition 12.15(d). -/
public theorem CFSG.proposition_12_15_d
    {M Mstar X : Subgroup G} {q : Nat.Primes}
    {S : Sylow q.val (M ⊓ Mstar : Subgroup G)}
    (hM : M ∈ section9MaximalSubgroups G)
    (hq : q ∈ section10SigmaPrimes M)
    (hX : X ≤ M) (hXne : X ≠ ⊥) (hXq : IsPGroup q.val X)
    (hMstar : Mstar ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (X : Set G)))
    (hMstar_ne : Mstar ≠ M)
    (hXS : X ≤ section10AmbientSylowSubgroup (M ⊓ Mstar) S)
    (hqσstar : q ∈ section10SigmaPrimes Mstar) :
    Mstar = (M ⊓ Mstar) ⊔ section10Mbeta Mstar ∧
      section12Tau1Primes Mstar ⊆ section12Tau1Primes M ∪ section10AlphaPrimes M ∧
        section10Mbeta Mstar = section10Malpha Mstar ∧
          section10Mbeta Mstar ≠ ⊥ := by
  classical
  have hnormM :
      Subgroup.normalizer
          ((section10AmbientSylowSubgroup (M ⊓ Mstar) S : Subgroup G) : Set G) ≤
        M :=
    proposition_12_15_b (G := G) (M := M) (Mstar := Mstar) (X := X) (q := q)
      (S := S) hM hq hX hXne hXq hMstar hMstar_ne hXS
  have hSylowStar :
      section12SylowSubgroupIn q (section10AmbientSylowSubgroup (M ⊓ Mstar) S)
        Mstar :=
    proposition_12_15_c (G := G) (M := M) (Mstar := Mstar) (X := X) (q := q)
      (S := S) hM hq hX hXne hXq hMstar hMstar_ne hXS
  have hnormMstar :
      Subgroup.normalizer
          ((section10AmbientSylowSubgroup (M ⊓ Mstar) S : Subgroup G) : Set G) ≤
        Mstar :=
    section12_normalizer_inf_sylow_le_right_of_sigma
      (M := M) (Mstar := Mstar) (q := q) (S := S) hMstar.1 hqσstar hSylowStar
  rcases section12_global_sylow_of_inf_sylow_normalizer_le
      (M := M) (Mstar := Mstar) (q := q) (S := S) hnormM hnormMstar with
    ⟨Sg, hSg⟩
  have hSexists :
      ∃ p : Nat.Primes, ∃ S : Sylow p.val G,
        Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ M ⊓ Mstar := by
    refine ⟨q, Sg, ?_⟩
    intro g hg
    have hg' :
        g ∈ Subgroup.normalizer
          ((section10AmbientSylowSubgroup (M ⊓ Mstar) S : Subgroup G) : Set G) := by
      simpa [hSg] using hg
    exact ⟨hnormM hg', hnormMstar hg'⟩
  rcases corollary_10_9_b (G := G) (M := Mstar) (H := M)
      hMstar.1 hM hMstar_ne.symm hSexists with
    ⟨hjoin, hαβ⟩
  refine ⟨hjoin.symm, ?_,
    section12_Mbeta_eq_Malpha_of_alphaPrimes_eq_betaPrimes hαβ,
    section12_Mbeta_ne_bot_of_inf_sup_mbeta_eq (G := G) hM hMstar.1 hMstar_ne hjoin⟩
  exact section12_tau1_subset_tau1_union_alpha_of_sigma_transfer
    (G := G) (M := M) (Mstar := Mstar) (X := X) (q := q) (S := S)
    hM hq hX hXne hXq hMstar hMstar_ne hXS hqσstar

end Section12
