module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ReflectedCyclicKleinFourCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2LowTorus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2OuterInvolutionFusion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2InnerInvolutionFusion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2TorusInvolutionDerived
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourExceptionTransport
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearThreeEquiv
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Klein-four centralizers in odd PGL₂

Every involution of odd `PGL₂(K)` is fused either to the distinguished outer
involution of the low torus or to the involution of the opposite high torus.
Both standard involutions have a reflected cyclic centralizer.  Consequently
no Klein four can centralize a nontrivial odd cyclic subgroup.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open Matrix
open scoped MatrixGroups

universe u

private theorem pgl2_no_kleinFour_of_conjugate_torus_centralizer
    {K : Type u} [Field K] [Finite K]
    (A V : Subgroup (PGL2 K))
    (hAcyc : IsCyclic A) (hAne : A ≠ ⊥) (hAodd : Odd (Nat.card A))
    (hVK : IsKleinFour V)
    (hVcent : V ≤ Subgroup.centralizer (A : Set (PGL2 K)))
    {t : PGL2 K} (htV : t ∈ V)
    (U : Subgroup (PGL2 K)) {s w : PGL2 K}
    (hUcyc : IsCyclic U) (hwU : w ∉ U) (hwsq : w * w = 1)
    (hwinv : ∀ x : PGL2 K, x ∈ U → w * x * w⁻¹ = x⁻¹)
    (hcent : Subgroup.centralizer ({s} : Set (PGL2 K)) =
      U ⊔ Subgroup.zpowers w)
    (hts : IsConj t s) :
    False := by
  classical
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  obtain ⟨g, hg⟩ := isConj_iff.mp hts
  let e : PGL2 K ≃* PGL2 K := MulAut.conj g
  let A0 : Subgroup (PGL2 K) := A.map e.toMonoidHom
  let V0 : Subgroup (PGL2 K) := V.map e.toMonoidHom
  let eA : A ≃* A0 :=
    Subgroup.equivMapOfInjective A e.toMonoidHom e.injective
  have hA0cyc : IsCyclic A0 := eA.isCyclic.mp hAcyc
  have hA0ne : A0 ≠ ⊥ := by
    intro hbot
    apply hAne
    exact (Subgroup.map_eq_bot_iff_of_injective
      (H := A) (f := e.toMonoidHom) e.injective).mp hbot
  have hA0odd : Odd (Nat.card A0) := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact hAodd
  have hV0K : IsKleinFour V0 :=
    isKleinFour_map_mulEquiv V hVK e
  have hV0cent : V0 ≤ Subgroup.centralizer (A0 : Set (PGL2 K)) :=
    centralizer_map_le_of_mulEquiv e A V hVcent
  have hsV0 : s ∈ V0 :=
    Subgroup.mem_map.mpr ⟨t, htV, hg⟩
  have hA0leC : A0 ≤ Subgroup.centralizer ({s} : Set (PGL2 K)) := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (hV0cent hsV0)) a ha
  have hV0leC : V0 ≤ Subgroup.centralizer ({s} : Set (PGL2 K)) := by
    let : IsKleinFour V0 := hV0K
    let : IsMulCommutative V0 := IsKleinFour.isMulCommutative
    intro v hv
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val
      ((IsKleinFour.isMulCommutative (G := V0)).is_comm.comm
        ⟨v, hv⟩ ⟨s, hsV0⟩)
  have hA0leD : A0 ≤ U ⊔ Subgroup.zpowers w := by
    rw [← hcent]
    exact hA0leC
  have hV0leD : V0 ≤ U ⊔ Subgroup.zpowers w := by
    rw [← hcent]
    exact hV0leC
  exact no_kleinFour_centralizes_odd_subgroup_of_reflected_cyclic_join
    U A0 V0 w hUcyc hwU hwsq hwinv hA0leD hV0leD hA0ne hA0odd
      hV0K hV0cent

/-- No Klein four in odd `PGL₂(K)` centralizes a nontrivial odd cyclic
subgroup. -/
public theorem pgl2_no_kleinFour_centralizes_odd_cyclic
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (A V : Subgroup (PGL2 K))
    (hAcyc : IsCyclic A) (hAne : A ≠ ⊥) (hAodd : Odd (Nat.card A))
    (hVK : IsKleinFour V)
    (hVcent : V ≤ Subgroup.centralizer (A : Set (PGL2 K))) :
    False := by
  classical
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  have hqge : 3 ≤ Nat.card K := by
    rcases hK with ⟨p, n, hp, hpodd, hn, hcard⟩
    have hpne2 : p ≠ 2 := by
      intro hp2
      subst p
      exact hpodd.not_two_dvd_nat (by simp)
    have hpge : 3 ≤ p := by
      have hp2 := hp.two_le
      omega
    rw [hcard]
    exact hpge.trans (by
      calc
        p = p ^ 1 := by simp
        _ ≤ p ^ n := Nat.pow_le_pow_right (by omega) hn)
  by_cases hq3 : Nat.card K = 3
  · let : Fintype K := Fintype.ofFinite K
    have hFcard : Fintype.card K = 3 := by
      simpa [Nat.card_eq_fintype_card] using hq3
    let eK : ZMod 3 ≃+* K :=
      ZMod.ringEquivOfPrime K Nat.prime_three hFcard
    let e : PGL2 K ≃* Equiv.Perm (Fin 4) :=
      (pgl2RingEquiv eK).symm.trans pgl2_three_equiv_perm
    exact no_kleinFour_centralizes_odd_cyclic_of_mulEquiv_perm_four
      e A V hAcyc hAne hAodd hVK hVcent
  · have hcard : 3 < Nat.card K := by omega
    have hqOdd : Odd (Nat.card K) := by
      rcases hK with ⟨p, n, hp, hpodd, hn, hKcard⟩
      rw [hKcard]
      exact hpodd.pow
    let J : Subgroup (PGL2 K) := commutator (PGL2 K)
    have hJindex : J.index = 2 := by
      dsimp [J]
      rw [pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hcard]
      exact pgl2_psl2Range_index_eq_two K hK
    obtain ⟨Ulow, sout, tin, wlow, hUlowcyc, hUlowhalf,
      hUlowcard, hsoutU, hsoutJ, hsoutne, hsoutsq, htinJ, htinU,
      htinsq, htinInv, htinRel, hwlowU, hwlowsq, hwlowInv, hcentlow⟩ :=
      pgl2_low_two_part_torus_reflection_data K hK hcard
    by_cases hVJ : V ≤ J
    · let : Fintype V := Fintype.ofFinite V
      have hlt : 1 < Fintype.card V := by
        rw [← Nat.card_eq_fintype_card, hVK.card_four]
        norm_num
      obtain ⟨tv, htvne⟩ := Fintype.exists_ne_of_one_lt_card hlt (1 : V)
      let t : PGL2 K := (tv : V)
      have htV : t ∈ V := tv.2
      have htne : t ≠ 1 := by
        intro h
        apply htvne
        exact Subtype.ext h
      have htsq : t * t = 1 :=
        congrArg Subtype.val (hVK.mul_self tv)
      have htI : IsInvolution t :=
        ⟨htne, by simpa [pow_two] using htsq⟩
      have htJ : t ∈ J := hVJ htV
      by_cases hUminus : Nat.card Ulow = Nat.card K - 1
      · obtain ⟨U0, s0, w0, hU0cyc, hU0card, hs0U, hs0sq, hs0ne,
          hw0U, hw0sq, hw0inv, hcent0, hU0cross⟩ :=
          pgl2_nonsplit_torus_centralizer_data K hqOdd
        have hU0crossJ : ¬ U0 ≤ J := by
          intro hle
          apply hU0cross hqOdd
          simpa [J, pgl2_commutator_eq_psl2_range_of_card_gt_three
            K hK hcard] using hle
        let m : ℕ := (Nat.card K + 1) / 2
        have hU0two : Nat.card U0 = 2 * m := by
          dsimp [m]
          rw [hU0card]
          rcases hqOdd with ⟨a, ha⟩
          omega
        have hmeven : Even m := by
          have hminusOdd : Odd ((Nat.card K - 1) / 2) := by
            simpa [hUminus] using hUlowhalf
          have hplus : (Nat.card K - 1) / 2 + 1 = (Nat.card K + 1) / 2 := by
            rcases hqOdd with ⟨a, ha⟩
            omega
          dsimp [m]
          rw [← hplus]
          rcases hminusOdd with ⟨a, ha⟩
          exact ⟨a + 1, by omega⟩
        have hs0J : s0 ∈ J :=
          pgl2_torus_involution_mem_commutator hJindex U0 hU0cyc
            hs0U hs0sq hs0ne hU0two hmeven hU0crossJ
        have hs0I : IsInvolution s0 :=
          ⟨hs0ne, by simpa [pow_two] using hs0sq⟩
        obtain ⟨g, hgJ, hg⟩ :=
          pgl2_inner_involutions_conjugate hK hcard htJ htI hs0J hs0I
        exact pgl2_no_kleinFour_of_conjugate_torus_centralizer
          A V hAcyc hAne hAodd hVK hVcent htV U0 hU0cyc hw0U
            hw0sq hw0inv hcent0 (isConj_iff.mpr ⟨g, hg⟩)
      · have hUplus : Nat.card Ulow = Nat.card K + 1 :=
          hUlowcard.resolve_left hUminus
        obtain ⟨U0, s0, w0, hU0cyc, hU0card, hs0U, hs0sq, hs0ne,
          hw0U, hw0sq, hw0inv, hcent0, hU0cross⟩ :=
          pgl2_split_torus_centralizer_data K hqOdd
        have hU0crossJ : ¬ U0 ≤ J := by
          intro hle
          apply hU0cross hqOdd
          simpa [J, pgl2_commutator_eq_psl2_range_of_card_gt_three
            K hK hcard] using hle
        let m : ℕ := (Nat.card K - 1) / 2
        have hU0two : Nat.card U0 = 2 * m := by
          dsimp [m]
          rw [hU0card]
          rcases hqOdd with ⟨a, ha⟩
          omega
        have hmeven : Even m := by
          have hplusOdd : Odd ((Nat.card K + 1) / 2) := by
            simpa [hUplus] using hUlowhalf
          have hminus : (Nat.card K + 1) / 2 - 1 = (Nat.card K - 1) / 2 := by
            rcases hqOdd with ⟨a, ha⟩
            omega
          dsimp [m]
          rw [← hminus]
          rcases hplusOdd with ⟨a, ha⟩
          exact ⟨a, by omega⟩
        have hs0J : s0 ∈ J :=
          pgl2_torus_involution_mem_commutator hJindex U0 hU0cyc
            hs0U hs0sq hs0ne hU0two hmeven hU0crossJ
        have hs0I : IsInvolution s0 :=
          ⟨hs0ne, by simpa [pow_two] using hs0sq⟩
        obtain ⟨g, hgJ, hg⟩ :=
          pgl2_inner_involutions_conjugate hK hcard htJ htI hs0J hs0I
        exact pgl2_no_kleinFour_of_conjugate_torus_centralizer
          A V hAcyc hAne hAodd hVK hVcent htV U0 hU0cyc hw0U
            hw0sq hw0inv hcent0 (isConj_iff.mpr ⟨g, hg⟩)
    · obtain ⟨t, htV, htJ⟩ := SetLike.not_le_iff_exists.mp hVJ
      have htne : t ≠ 1 := by
        intro htone
        apply htJ
        simpa [htone] using J.one_mem
      let : IsKleinFour V := hVK
      have htsq : t * t = 1 :=
        congrArg Subtype.val (IsKleinFour.mul_self (⟨t, htV⟩ : V))
      have htI : IsInvolution t :=
        ⟨htne, by simpa [pow_two] using htsq⟩
      have hsoutI : IsInvolution sout :=
        ⟨hsoutne, by simpa [pow_two] using hsoutsq⟩
      have hconj : IsConj t sout :=
        pgl2_outer_involutions_conjugate K hK hcard htI hsoutI htJ hsoutJ
      exact pgl2_no_kleinFour_of_conjugate_torus_centralizer
        A V hAcyc hAne hAodd hVK hVcent htV Ulow hUlowcyc hwlowU
          hwlowsq hwlowInv hcentlow hconj

end CFSG.GorensteinWalter
