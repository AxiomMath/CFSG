module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection15.Defs
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.CentralizerControl
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Conjugacy
import Mathlib.Algebra.Group.Subgroup.Order
import Mathlib.GroupTheory.Schreier

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise commutatorElement

/-! # Lemma 15 1 from BG Section 15 -/

section Section15

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]
omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_not_unique_of_le_two_distinct_maximal
    {L M N : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G) (hN : N ∈ section9MaximalSubgroups G)
    (hLM : L ≤ M) (hLN : L ≤ N) (hNM : N ≠ M) :
    L ∉ section9UniqueSubgroups G := by
  classical
  intro hL
  rcases hL with ⟨_hLproper, U, hUuniq⟩
  have hMcont : M ∈ section9MaximalSubgroupsContaining L := ⟨hM, hLM⟩
  have hNcont : N ∈ section9MaximalSubgroupsContaining L := ⟨hN, hLN⟩
  have hMU : M = U := by
    have hsingle : M ∈ ({U} : Set (Subgroup G)) := by
      simpa [hUuniq] using hMcont
    simpa using hsingle
  have hNU : N = U := by
    have hsingle : N ∈ ({U} : Set (Subgroup G)) := by
      simpa [hUuniq] using hNcont
    simpa using hsingle
  exact hNM (hNU.trans hMU.symm)

omit [IsMinCE G] in
public theorem CFSG.section15_kappa_subset_primeSet_diff_sigma
    {M : Subgroup G} :
    section14KappaPrimes M ⊆ subgroupPrimeSet M \ section10SigmaPrimes M := by
  intro p hp
  have hp' :
      (p ∈ section12Tau1Primes M ∧
        ∃ P : Subgroup G, P ∈ section10PrimeOrderSubgroupsIn p M ∧
          subgroupCentralizerIn (section10Msigma M) P ≠ ⊥) ∨
        (p ∈ section12Tau3Primes M ∧
          ∃ P : Subgroup G, P ∈ section10PrimeOrderSubgroupsIn p M ∧
            subgroupCentralizerIn (section10Msigma M) P ≠ ⊥) := by
    simpa [section14KappaPrimes] using hp
  rcases hp' with ⟨hpτ1, P, hPprime, _hcent⟩ | ⟨hpτ3, P, hPprime, _hcent⟩
  · constructor
    · have hpP : p.val ∣ Nat.card P := by
        rw [hPprime.2]
      exact (section8_subgroupPrimeSet_mono hPprime.1) hpP
    · exact hpτ1.1
  · constructor
    · have hpP : p.val ∣ Nat.card P := by
        rw [hPprime.2]
      exact (section8_subgroupPrimeSet_mono hPprime.1) hpP
    · exact hpτ3.1

private theorem CFSG.section15_primeSet_diff_sigma_nonempty
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) :
    (subgroupPrimeSet M \ section10SigmaPrimes M).Nonempty := by
  classical
  by_contra hnone
  have hpi_subset : subgroupPrimeSet M ⊆ section10SigmaPrimes M := by
    intro p hpM
    by_contra hpσ
    exact hnone ⟨p, hpM, hpσ⟩
  have hσtop : section10MsigmaSubgroup M = ⊤ := by
    apply Subgroup.index_eq_one.mp
    rw [Nat.eq_one_iff_not_exists_prime_dvd]
    intro q hqprime hqidx
    let p : Nat.Primes := ⟨q, hqprime⟩
    have hpidx : p.val ∣ (section10MsigmaSubgroup M).index := by
      simpa [p] using hqidx
    have hp_not_σ : p ∉ section10SigmaPrimes M :=
      ((theorem_10_2_b (G := G) hM).2).p_in_pi_of_p_dvd_index p hpidx
    have hpM : p ∈ subgroupPrimeSet M := by
      have hmul :
          (section10MsigmaSubgroup M).index * Nat.card (section10MsigmaSubgroup M) =
            Nat.card M :=
        Subgroup.index_mul_card (H := section10MsigmaSubgroup M)
      have hp_mul :
          p.val ∣
            (section10MsigmaSubgroup M).index * Nat.card (section10MsigmaSubgroup M) :=
        dvd_mul_of_dvd_left hpidx _
      simpa [subgroupPrimeSet, hmul] using hp_mul
    exact hp_not_σ (hpi_subset hpM)
  have hDtop : derivedSubgroup M = ⊤ := by
    apply top_le_iff.mp
    rw [← hσtop]
    exact (theorem_10_2_c (G := G) hM).2
  have hM_ne_bot : M ≠ ⊥ := by
    intro hMbot
    have hMsigma_bot : section10Msigma M = ⊥ := by
      apply le_bot_iff.mp
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
      simpa [hMbot] using y.property
    exact (theorem_10_2_e (G := G) hM) hMsigma_bot
  haveI : Nontrivial M := (Subgroup.nontrivial_iff_ne_bot (H := M)).2 hM_ne_bot
  have hsolvM : Group.IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.2 hM.1)
  have hcomm_lt : commutator M < (⊤ : Subgroup M) :=
    Group.IsSolvable.commutator_lt_top_of_nontrivial (G := M)
  have hcomm_top : commutator M = (⊤ : Subgroup M) := by
    change derivedSeries M 1 = ⊤ at hDtop
    rw [derivedSeries_one] at hDtop
    exact hDtop
  exact hcomm_lt.ne hcomm_top

private theorem CFSG.section15_exists_prime_outside_sigma_kappa_of_not_P1
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    (hMnotP1 : M ∉ section14MFamilyP1 G) :
    (subgroupPrimeSet M \
      (section10SigmaPrimes M ∪ section14KappaPrimes M)).Nonempty := by
  classical
  by_contra hnone
  have hκsubset :
      section14KappaPrimes M ⊆ subgroupPrimeSet M \ section10SigmaPrimes M :=
    section15_kappa_subset_primeSet_diff_sigma
  have hκeq : section14KappaPrimes M = subgroupPrimeSet M \ section10SigmaPrimes M := by
    apply le_antisymm hκsubset
    intro p hp
    by_contra hpκ
    exact hnone ⟨p, hp.1, by
      intro hpσκ
      exact hpσκ.elim hp.2 hpκ⟩
  have hκnonempty : (section14KappaPrimes M).Nonempty := by
    rcases section15_primeSet_diff_sigma_nonempty (G := G) hM with ⟨p, hp⟩
    exact ⟨p, by simpa [hκeq] using hp⟩
  exact hMnotP1 (by
    simpa [section14MFamilyP1, section14MFamilyP] using
      (show M ∈ section14MFamilyP G ∧
          section14KappaPrimes M = subgroupPrimeSet M \ section10SigmaPrimes M from
        ⟨⟨hM, hκnonempty⟩, hκeq⟩))

/-- Section 15 local interface for Lemma 14.1, contrapositive form: a
maximal subgroup with nonnilpotent `M_σ` is of type `𝓟₁`.  This is kept local
to Section 15 so Section 14 is not enlarged by downstream proof debt. -/
public theorem CFSG.section15_lemma_14_1_nonnilpotent_msigma_mem_familyP1
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    (hnotNil : ¬ Group.IsNilpotent (section10Msigma M)) :
    M ∈ section14MFamilyP1 G := by
  classical
  by_contra hMnotP1
  rcases section15_exists_prime_outside_sigma_kappa_of_not_P1
      (G := G) hM hMnotP1 with ⟨p, hp⟩
  let S : Sylow p.val M := Classical.choice (Sylow.nonempty (p := p.val) (G := M))
  exact hnotNil ((lemma_14_1 (G := G) hM hMnotP1 hp S).2.2)

/-- Section 15 local interface: in type `𝓟₁`, a Hall `κ(M)`-subgroup
complements `M_σ` in `M`. -/
public theorem CFSG.section15_familyP1_hall_kappa_sup_msigma_eq
    {M K : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hP1 : M ∈ section14MFamilyP1 G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    M = K ⊔ section10Msigma M := by
  classical
  let Kloc : Subgroup M := K.subgroupOf M
  let Sloc : Subgroup M := section10MsigmaSubgroup M
  let Hloc : Subgroup M := Kloc ⊔ Sloc
  have hKHall : IsHallSubgroup (section14KappaPrimes M) Kloc := by
    simpa [Kloc] using hK.2
  have hSHall : IsHallSubgroup (section10SigmaPrimes M) Sloc := by
    simpa [Sloc] using (theorem_10_2_b (G := G) hM).2
  have hHlocHall :
      IsHallSubgroup (section14KappaPrimes M ∪ section10SigmaPrimes M) Hloc := by
    refine isHallSubgroup_of
      (G := M) (section14KappaPrimes M ∪ section10SigmaPrimes M) Hloc ?_ ?_
    · intro p hpH
      have hpM : p ∈ subgroupPrimeSet M := by
        have hpMdiv : p.val ∣ Nat.card M :=
          hpH.trans (Subgroup.card_subgroup_dvd_card Hloc)
        simpa [subgroupPrimeSet] using hpMdiv
      by_cases hpσ : p ∈ section10SigmaPrimes M
      · exact Or.inr hpσ
      · exact Or.inl (by
          rw [hP1.2]
          exact ⟨hpM, hpσ⟩)
    · intro p hpUnion hpidx
      rcases hpUnion with hpκ | hpσ
      · have hidx : Hloc.index ∣ Kloc.index :=
          Subgroup.index_dvd_of_le (show Kloc ≤ Hloc by exact le_sup_left)
        exact (hKHall.p_in_pi_of_p_dvd_index p (hpidx.trans hidx)) hpκ
      · have hidx : Hloc.index ∣ Sloc.index :=
          Subgroup.index_dvd_of_le (show Sloc ≤ Hloc by exact le_sup_right)
        exact (hSHall.p_in_pi_of_p_dvd_index p (hpidx.trans hidx)) hpσ
  have hTopHall :
      IsHallSubgroup (section14KappaPrimes M ∪ section10SigmaPrimes M)
        (⊤ : Subgroup M) := by
    refine isHallSubgroup_of
      (G := M) (section14KappaPrimes M ∪ section10SigmaPrimes M)
      (⊤ : Subgroup M) ?_ ?_
    · intro p hpTop
      have hpM : p ∈ subgroupPrimeSet M := by
        simpa [subgroupPrimeSet] using hpTop
      by_cases hpσ : p ∈ section10SigmaPrimes M
      · exact Or.inr hpσ
      · exact Or.inl (by
          rw [hP1.2]
          exact ⟨hpM, hpσ⟩)
    · intro p _ hpidx
      exact p.property.not_dvd_one (by simpa using hpidx)
  have hHtop : Hloc = ⊤ :=
    hHlocHall.eq_of_le hTopHall le_top
  have hσM : section10Msigma M ≤ M := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact (y : M).property
  have hσsub_eq :
      (section10Msigma M).subgroupOf M = section10MsigmaSubgroup M := by
    change (piCoreIn (section10SigmaPrimes M) M).subgroupOf M =
      piCore (section10SigmaPrimes M) M
    exact piCore_map_subtype_subgroupOf (section10SigmaPrimes M) M
  have hsup_subgroupOf_top :
      (K ⊔ section10Msigma M).subgroupOf M = ⊤ := by
    calc
      (K ⊔ section10Msigma M).subgroupOf M =
          K.subgroupOf M ⊔ (section10Msigma M).subgroupOf M := by
        exact Subgroup.subgroupOf_sup (A := K) (A' := section10Msigma M)
          (B := M) hK.1 hσM
      _ = Kloc ⊔ Sloc := by
        simp [Kloc, Sloc, hσsub_eq]
      _ = ⊤ := hHtop
  apply le_antisymm
  · intro x hxM
    have hxloc : (⟨x, hxM⟩ : M) ∈ (K ⊔ section10Msigma M).subgroupOf M := by
      simp [hsup_subgroupOf_top]
    simpa [Subgroup.mem_subgroupOf] using hxloc
  · exact sup_le hK.1 hσM

/-- Section 15 local interface: in the `𝓟₁` branch used in Theorem 15.2,
`|K*|` is prime. -/
public theorem CFSG.section15_familyP1_kstar_card_prime
    {M K : Subgroup G}
    (_hM : M ∈ section9MaximalSubgroups G)
    (hP1 : M ∈ section14MFamilyP1 G)
    (hK : section12HallSubgroupIn (section14KappaPrimes M) K M) :
    ∃ q : Nat.Primes, q.val = Nat.card (section14KStar M K) := by
  rcases (by simpa [section14MFamilyP1] using hP1) with ⟨hMP, hκeq⟩
  rcases theorem_14_7_f (G := G) (M := M) (K := K) hMP hK with hfirst | hsecond
  · rcases (by simpa [section14MFamilyP2] using hfirst.1) with ⟨_hMP2, hκne⟩
    exact False.elim (hκne hκeq)
  · exact ⟨⟨Nat.card (section14KStar M K), hsecond.2⟩, rfl⟩

omit [Finite G] [IsMinCE G] in
/-- Section 15 local fixed-complement context: the fixed subgroup `U M_σ` is
normal in `M`. -/
private theorem CFSG.section15_kappa_compl_context_um_sigma_normal
    {M K U : Subgroup G}
    (_hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U) :
    section10NormalIn (U ⊔ section10Msigma M) M := by
  exact hKU.2.2.2.2.2.1

omit [Finite G] [IsMinCE G] in
/-- Section 15 local fixed-complement context: the fixed `U` is a Hall
`(κ(M) ∪ σ(M))'` subgroup of `M`. -/
public theorem CFSG.section15_kappa_compl_context_U_hall
    {M K U : Subgroup G}
    (hKU : section15KUData M K U) :
    section12HallSubgroupIn
      ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ) U M := by
  exact hKU.2.2.2.1

omit [Finite G] [IsMinCE G] in
/-- Section 15 local fixed-complement context: the fixed `U` is a
`(κ(M) ∪ σ(M))'`-subgroup of `M`. -/
private theorem CFSG.section15_kappa_compl_context_U_sigma_kappa_compl
    {M K U : Subgroup G}
    (_hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U) :
    IsPiSubgroup (G := G) ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ) U := by
  let hHallU := section15_kappa_compl_context_U_hall hKU
  rcases hHallU with ⟨hUM, hUHall⟩
  intro p hpU
  have hcard : Nat.card (U.subgroupOf M) = Nat.card U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := U) (K := M) hUM).toEquiv
  exact hUHall.p_in_pi_of_p_dvd_card p (by simpa [hcard] using hpU)

omit [Finite G] [IsMinCE G] in
/-- Section 15 local fixed-complement context: inside the fixed complement
`K ⊔ U` to `M_σ`, the subgroup `U` is normal. -/
public theorem CFSG.section15_kappa_compl_context_U_normal_in_KU
    {M K U : Subgroup G}
    (_hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U) :
    section10NormalIn U (K ⊔ U) := by
  exact hKU.2.2.2.2.2.2

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_isElementaryAbelian_map
    {p : ℕ} [Fact p.Prime] {R S : Type*} [Group R] [Group S]
    {A : Subgroup R} [IsElementaryAbelian p A] (f : R →* S) :
    IsElementaryAbelian p (A.map f) := by
  refine
    { toIsMulCommutative := by
        simpa using (Subgroup.map_isMulCommutative (f := f) (H := A))
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro x
  apply Subtype.ext
  rcases Subgroup.mem_map.mp x.2 with ⟨y, hyA, hyx⟩
  let yA : A := ⟨y, hyA⟩
  have hypow : yA ^ p = 1 := by
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p A) yA
  have hx_eq : (x : S) = f y := by simpa using hyx.symm
  calc
    (x : S) ^ p = (f y) ^ p := by simp [hx_eq]
    _ = f (y ^ p) := by simp
    _ = 1 := by simpa using congrArg f (congrArg Subtype.val hypow)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_isElementaryAbelian_subgroupOf_of_le
    {p : ℕ} [Fact p.Prime] {A S : Subgroup G}
    [IsElementaryAbelian p A] (_hAS : A ≤ S) :
    IsElementaryAbelian p (A.subgroupOf S) := by
  refine
    { toIsMulCommutative := by
        exact
          { is_comm := ⟨fun x y =>
              Subtype.ext <| Subtype.ext <|
                setLike_mul_comm (s := A)
                  (Subgroup.mem_subgroupOf.mp x.2) (Subgroup.mem_subgroupOf.mp y.2)⟩ }
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro x
  apply Subtype.ext
  apply Subtype.ext
  let xA : A := ⟨((x : A.subgroupOf S) : S), Subgroup.mem_subgroupOf.mp x.2⟩
  have hxpow : xA ^ p = 1 := by
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p A) xA
  simpa [xA] using congrArg (fun y : A => ((y : A) : G)) hxpow

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_rankTwoMaximal_subgroupOf_of_le
    {p : Nat.Primes} {A S : Subgroup G} (hAS : A ≤ S)
    (hArankTwo : A ∈ elementaryAbelianSubgroupsOfRank p.val 2 G)
    (hAmax : A ∈ maximalElementaryAbelianSubgroups p.val G) :
    A.subgroupOf S ∈ section10RankTwoMaximalElementaryAbelianSubgroups p S := by
  haveI : Fact p.val.Prime := ⟨p.property⟩
  rcases hArankTwo with ⟨hAcard, hAelem⟩
  rcases hAmax with ⟨_hAelem', hAmax'⟩
  haveI : IsElementaryAbelian p.val A := hAelem
  have hAsub_card : Nat.card (A.subgroupOf S) = p.val ^ 2 := by
    simpa [hAcard] using
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := A) (K := S) hAS).toEquiv
  have hAsub_elem : IsElementaryAbelian p.val (A.subgroupOf S) :=
    section15_isElementaryAbelian_subgroupOf_of_le (G := G) (p := p.val) hAS
  have hAsub_max : A.subgroupOf S ∈ maximalElementaryAbelianSubgroups p.val S := by
    refine ⟨hAsub_elem, ?_⟩
    intro B hAB hBelem
    let Bmap : Subgroup G := B.map S.subtype
    have hA_le_Bmap : A ≤ Bmap := by
      intro a ha
      let aS : A.subgroupOf S := ⟨⟨a, hAS ha⟩, ha⟩
      exact Subgroup.mem_map.mpr ⟨aS, hAB aS.2, rfl⟩
    have hBmap_elem : IsElementaryAbelian p.val Bmap := by
      letI : IsElementaryAbelian p.val B := hBelem
      simpa [Bmap] using
        section15_isElementaryAbelian_map (p := p.val) (A := B) S.subtype
    have hEq : A = Bmap := hAmax' Bmap hA_le_Bmap hBmap_elem
    apply Subgroup.ext
    intro x
    constructor
    · intro hx
      have hxA : ((x : S) : G) ∈ A := hx
      rw [hEq] at hxA
      rcases Subgroup.mem_map.mp hxA with ⟨y, hyB, hyx⟩
      have : y = x := Subtype.ext hyx
      simpa [this] using hyB
    · intro hx
      have hxMap : ((x : S) : G) ∈ Bmap := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      rw [← hEq] at hxMap
      exact hxMap
  exact ⟨⟨hAsub_card, hAsub_elem⟩, hAsub_max⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_omega1Z_isElementaryAbelian
    {p : ℕ} [Fact p.Prime] (R : Type*) [Group R] :
    IsElementaryAbelian p (Ω₁Z p R) := by
  let Ωc : Subgroup (Subgroup.center R) := omega₁ (G := Subgroup.center R) (p := p)
  have hΩcelem : IsElementaryAbelian p Ωc := by
    letI : IsMulCommutative (Subgroup.center R) := inferInstance
    simpa [Ωc] using
      section12_omega1_isElementaryAbelian_of_commutative
        (p := p) (Subgroup.center R)
  letI : IsElementaryAbelian p Ωc := hΩcelem
  change IsElementaryAbelian p (Ωc.map (Subgroup.center R).subtype)
  exact section15_isElementaryAbelian_map (p := p) (A := Ωc) (Subgroup.center R).subtype

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_omega1Z_le_center
    (p : ℕ) (R : Type*) [Group R] :
    Ω₁Z p R ≤ Subgroup.center R := by
  intro z hz
  rcases Subgroup.mem_map.mp hz with ⟨y, _hy, rfl⟩
  exact y.property

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_omegaOneCenter_isElementaryAbelian
    {p : Nat.Primes} (P : Subgroup G) :
    IsElementaryAbelian p.val (section10OmegaOneCenter p P) := by
  haveI : Fact p.val.Prime := ⟨p.property⟩
  have hΩelem : IsElementaryAbelian p.val (Ω₁Z p.val P) :=
    section15_omega1Z_isElementaryAbelian (p := p.val) P
  letI : IsElementaryAbelian p.val (Ω₁Z p.val P) := hΩelem
  change IsElementaryAbelian p.val ((Ω₁Z p.val P).map P.subtype)
  exact section15_isElementaryAbelian_map (p := p.val) (A := Ω₁Z p.val P) P.subtype

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_isElementaryAbelian_of_prime_card_isCyclic
    {p : ℕ} [Fact p.Prime]
    {H : Type*} [Group H] [Finite H] [IsCyclic H]
    (hcard : Nat.card H = p) :
    IsElementaryAbelian p H := by
  letI : CommGroup H := IsCyclic.commGroup
  refine
    { toIsMulCommutative := { is_comm := ⟨mul_comm⟩ }
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro x
  exact orderOf_dvd_iff_pow_eq_one.mp <| by
    simpa [hcard] using (orderOf_dvd_natCard x)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_isElementaryAbelian_sup_of_le_centralizer
    {p : ℕ} [Fact p.Prime] {E D : Subgroup G}
    [IsElementaryAbelian p E] [IsElementaryAbelian p D]
    (hDE : D ≤ Subgroup.centralizer (E : Set G)) :
    IsElementaryAbelian p ↥(E ⊔ D) := by
  classical
  let s : Set G := (E : Set G) ∪ (D : Set G)
  have hcomm_s : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x := by
    intro x hx y hy
    rcases hx with hxE | hxD
    · rcases hy with hyE | hyD
      · simpa using congrArg Subtype.val
          ((IsMulCommutative.is_comm (M := E)).comm ⟨x, hxE⟩ ⟨y, hyE⟩)
      · exact (Subgroup.mem_centralizer_iff.mp (hDE hyD)) x hxE
    · rcases hy with hyE | hyD
      · exact ((Subgroup.mem_centralizer_iff.mp (hDE hxD)) y hyE).symm
      · simpa using congrArg Subtype.val
          ((IsMulCommutative.is_comm (M := D)).comm ⟨x, hxD⟩ ⟨y, hyD⟩)
  have hsup : E ⊔ D = Subgroup.closure s := by
    simpa [s] using (Subgroup.sup_eq_closure E D)
  refine
    { toIsMulCommutative := by
        rw [hsup]
        exact Subgroup.isMulCommutative_closure fun x hx y hy _ => hcomm_s x hx y hy
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro x
  apply Subtype.ext
  have hxcl : (x : G) ∈ Subgroup.closure s := by
    simpa [hsup] using x.property
  exact
    Subgroup.closure_induction (k := s)
      (p := fun z _hz => z ^ p = 1) (x := (x : G)) (by
        intro y hy
        rcases hy with hyE | hyD
        · have hypow : (⟨y, hyE⟩ : E) ^ p = 1 :=
            Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
              (IsElementaryAbelian.exponent_dvd_p p E) ⟨y, hyE⟩
          simpa using congrArg Subtype.val hypow
        · have hypow : (⟨y, hyD⟩ : D) ^ p = 1 :=
            Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
              (IsElementaryAbelian.exponent_dvd_p p D) ⟨y, hyD⟩
          simpa using congrArg Subtype.val hypow) (by simp) (by
        intro y z hy hz hypow hzpow
        have hyz_comm : Commute y z := by
          letI : IsMulCommutative (Subgroup.closure s) :=
            Subgroup.isMulCommutative_closure fun x hx y hy _ => hcomm_s x hx y hy
          letI : CommGroup (Subgroup.closure s) := IsMulCommutative.instCommGroup
          show y * z = z * y
          simpa using congrArg Subtype.val
            (mul_comm (⟨y, hy⟩ : Subgroup.closure s) (⟨z, hz⟩ : Subgroup.closure s))
        calc
          (y * z) ^ p = y ^ p * z ^ p := by simpa using hyz_comm.mul_pow p
          _ = 1 := by simp [hypow, hzpow]) (by
        intro y _hy hypow
        simpa [inv_pow] using congrArg Inv.inv hypow) hxcl

omit [IsMinCE G] in
omit [Finite G] in
public theorem CFSG.section15_map_subtype_ne_bot_of_ne_bot
    {M : Subgroup G} {K : Subgroup M} (hK : K ≠ ⊥) :
    K.map M.subtype ≠ (⊥ : Subgroup G) := by
  intro hmap
  have hmap_bot : K.map M.subtype = (⊥ : Subgroup M).map M.subtype := by
    simpa using hmap
  exact hK ((Subgroup.map_injective M.subtype_injective) hmap_bot)

omit [IsMinCE G] in
public theorem CFSG.section15_omegaOneCenter_ne_bot_of_nontrivial_pSubgroup
    {p : Nat.Primes} {P : Subgroup G}
    (hPp : IsPGroup p.val P) [Nontrivial P] :
    section10OmegaOneCenter p P ≠ ⊥ := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  have hZ_nontrivial : Nontrivial (Subgroup.center P) := hPp.center_nontrivial
  have hpdvd_center : p.val ∣ Nat.card (Subgroup.center P) := by
    have hcenter_p : IsPGroup p.val (Subgroup.center P) :=
      hPp.to_subgroup (Subgroup.center P)
    rcases (IsPGroup.nontrivial_iff_card
        (p := p.val) (G := Subgroup.center P) (hG := hcenter_p)).1 hZ_nontrivial with
      ⟨n, hn, hcard⟩
    rw [hcard]
    exact dvd_pow_self p.val (Nat.ne_of_gt hn)
  have hΩlocal_ne_bot : Ω₁Z p.val P ≠ ⊥ := by
    simpa [Ω₁Z] using
      omega₁_map_subtype_ne_bot (M := Subgroup.center P) (p := p.val) hpdvd_center
  simpa [section10OmegaOneCenter] using
    section15_map_subtype_ne_bot_of_ne_bot (G := G) (M := P) hΩlocal_ne_bot

public theorem CFSG.section15_exists_rankTwo_in_noncyclic_pSubgroup
    {P : Subgroup G} {p : Nat.Primes}
    (hPp : IsPGroup p.val P) (hPnoncyc : ¬ IsCyclic P) :
    ∃ A : Subgroup G, A ∈ section12RankTwoElementaryAbelianIn p P := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  have hp_dvd_P : p.val ∣ Nat.card P := by
    rcases hPp.exists_card_eq with ⟨n, hn⟩
    cases n with
    | zero =>
        have hcard_one : Nat.card P = 1 := by
          simpa using hn
        exact False.elim <| hPnoncyc <| by
          letI : Subsingleton P := (Nat.card_eq_one_iff_unique.mp hcard_one).1
          exact isCyclic_of_subsingleton (α := P)
    | succ n =>
        rw [hn]
        exact dvd_pow_self p.val (Nat.succ_ne_zero n)
  have hp_dvd_G : p.val ∣ Nat.card G :=
    hp_dvd_P.trans (Subgroup.card_subgroup_dvd_card P)
  have hpodd : p.val ≠ 2 := Odd.ne_two_of_dvd_nat IsMinCE.odd_order hp_dvd_G
  haveI : Fact (IsPGroup p.val P) := ⟨hPp⟩
  obtain ⟨A₀, _hA₀norm, hA₀card, hA₀elem⟩ :=
    lemma_4_5_a (R := P) (p := p.val) hpodd hPnoncyc
  haveI : IsElementaryAbelian p.val A₀ := hA₀elem
  let A : Subgroup G := A₀.map P.subtype
  have hA_le_P : A ≤ P := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨a, _ha, rfl⟩
    exact a.2
  have hAcard : Nat.card A = p.val ^ 2 := by
    have hcard : Nat.card A = Nat.card A₀ := by
      simpa [A] using
        Subgroup.card_map_of_injective (K := A₀) (f := P.subtype) P.subtype_injective
    rw [hcard, hA₀card]
  have hAelem : IsElementaryAbelian p.val A := by
    simpa [A] using
      section15_isElementaryAbelian_map (p := p.val) (A := A₀) P.subtype
  exact ⟨A, ⟨hA_le_P, hAcard, hAelem⟩⟩

omit [IsMinCE G] in
public theorem CFSG.section15_groupRank_at_least_two_of_rankTwo_elementary_le
    {K A : Subgroup G} {p : Nat.Primes}
    (hAK : A ≤ K) (hA : A ∈ elementaryAbelianSubgroupsOfRank p.val 2 G) :
    2 ≤ groupRank K := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  rcases hA with ⟨hAcard, hAelem⟩
  letI : IsElementaryAbelian p.val A := hAelem
  have hAgen : 2 ≤ generatorRank A :=
    section12_generatorRank_at_least_two_of_elementaryAbelian_card_p_sq
      (p := p.val) (A := A) hAcard
  let A' : Subgroup K := A.subgroupOf K
  have hA'p : IsPGroup p.val A' :=
    (IsElementaryAbelian.isPGroup p.val A).of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := A) (K := K) hAK).symm
  have hA'comm : IsMulCommutative A' := by
    letI : IsMulCommutative A := hAelem.toIsMulCommutative
    exact Subgroup.subgroupOf_isMulCommutative (H := A) (K := K)
  have hgen_eq : generatorRank A' = generatorRank A := by
    rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
    exact Group.rank_congr
      (Subgroup.subgroupOfEquivOfLe (H := A) (K := K) hAK)
  have hA'gen : 2 ≤ generatorRank A' := by
    simpa [hgen_eq] using hAgen
  have hprimeRank : 2 ≤ primeRank p.val K :=
    hA'gen.trans
      (section12_generatorRank_le_primeRank_of_subgroup
        (R := K) (q := p.val) (A := A') hA'p hA'comm)
  let S : Sylow p.val K := Classical.choice (Sylow.nonempty (p := p.val) (G := K))
  exact hprimeRank.trans
    ((section10_primeRank_le_groupRank_sylow (G := K) S).trans
      (section8_groupRank_le_of_subgroup (G := K) (S : Subgroup K)))

omit [IsMinCE G] in
public theorem CFSG.section15_primeRank_at_least_two_of_rankTwo
    {M A : Subgroup G} {p : Nat.Primes}
    (hA : A ∈ section12RankTwoElementaryAbelianIn p M) :
    2 ≤ primeRank p.val M := by
  classical
  haveI : Fact p.val.Prime := ⟨p.2⟩
  have hAM : A ≤ M := section12_rankTwo_le hA
  rcases section12_rankTwo_elementary hA with ⟨hcard, hElem⟩
  haveI : IsElementaryAbelian p.val A := hElem
  have hAcomm : IsMulCommutative A := inferInstance
  let A' : Subgroup M := A.subgroupOf M
  have hA'p : IsPGroup p.val A' :=
    (IsElementaryAbelian.isPGroup p.val A).of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := A) (K := M) hAM).symm
  have hA'comm : IsMulCommutative A' := by
    exact Subgroup.subgroupOf_isMulCommutative (H := A) (K := M)
  have hgenA : 2 ≤ generatorRank A :=
    section12_generatorRank_at_least_two_of_elementaryAbelian_card_p_sq
      (p := p.val) hcard
  have hgen_eq : generatorRank A' = generatorRank A := by
    rw [generatorRank_eq_group_rank, generatorRank_eq_group_rank]
    exact Group.rank_congr
      (Subgroup.subgroupOfEquivOfLe (H := A) (K := M) hAM)
  have hgenA' : 2 ≤ generatorRank A' := by
    simpa [hgen_eq] using hgenA
  exact hgenA'.trans
    (section12_generatorRank_le_primeRank_of_subgroup
      (R := M) (q := p.val) (A := A') hA'p hA'comm)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_exists_noncyclic_sylow_of_noncyclic_nilpotent
    {X : Type*} [Group X] [Finite X] [Group.IsNilpotent X]
    (hXnoncyc : ¬ IsCyclic X) :
    ∃ p : Nat.Primes, ∃ P : Sylow p.val X, ¬ IsCyclic P := by
  classical
  by_contra hnone
  have hZ : IsZGroup X := ⟨fun p hp P => by
    by_contra hP
    exact hnone ⟨⟨p, hp⟩, P, hP⟩⟩
  letI : IsZGroup X := hZ
  exact hXnoncyc (inferInstance : IsCyclic X)

public theorem CFSG.section15_groupRank_at_least_two_of_not_isCyclic
    (R : Subgroup G) [Group.IsNilpotent R] (hR : ¬ IsCyclic R) :
    2 ≤ groupRank R := by
  classical
  have hRodd : Odd (Nat.card R) :=
    odd_of_card_dvd IsMinCE.odd_order (Subgroup.card_subgroup_dvd_card R)
  rcases section15_exists_noncyclic_sylow_of_noncyclic_nilpotent
      (X := R) hR with ⟨p, P, hPnoncyc⟩
  haveI : Fact p.val.Prime := ⟨p.property⟩
  rcases P.isPGroup'.exists_card_eq with ⟨n, hn⟩
  cases n with
  | zero =>
      have hcard : Nat.card P = 1 := by simp [hn]
      haveI : Subsingleton P := (Nat.card_eq_one_iff_unique.mp hcard).1
      exact False.elim (hPnoncyc (by infer_instance))
  | succ n =>
      have hp_dvd_P : p.val ∣ Nat.card P := by
        rw [hn, Nat.pow_succ']
        exact dvd_mul_of_dvd_left (dvd_refl p.val) _
      have hpodd : p.val ≠ 2 := by
        have hp_dvd_R : p.val ∣ Nat.card R := hp_dvd_P.trans P.card_subgroup_dvd_card
        exact Odd.ne_two_of_dvd_nat hRodd hp_dvd_R
      have hPrank : 2 ≤ groupRank (P : Subgroup R) := by
        haveI : Fact (IsPGroup p.val P) := ⟨P.isPGroup'⟩
        obtain ⟨A₀, _hA₀norm, hA₀card, hA₀elem⟩ :=
          lemma_4_5_a (R := P) (p := p.val) hpodd hPnoncyc
        haveI : IsElementaryAbelian p.val A₀ := hA₀elem
        let A : Subgroup R := A₀.map (P : Subgroup R).subtype
        have hA_le_P : A ≤ (P : Subgroup R) := by
          intro x hx
          rcases Subgroup.mem_map.mp hx with ⟨a, _ha, rfl⟩
          exact a.2
        have hAcard : Nat.card A = p.val ^ 2 := by
          have hcard : Nat.card A = Nat.card A₀ := by
            simpa [A] using
              Subgroup.card_map_of_injective
                (K := A₀) (f := (P : Subgroup R).subtype) (P : Subgroup R).subtype_injective
          rw [hcard, hA₀card]
        have hAelem : IsElementaryAbelian p.val A := by
          simpa [A] using
            section15_isElementaryAbelian_map
              (R := P) (S := R) (p := p.val) (A := A₀) (P : Subgroup R).subtype
        exact
          section15_groupRank_at_least_two_of_rankTwo_elementary_le
            (G := R) (K := (P : Subgroup R)) (A := A) (p := p)
            hA_le_P ⟨hAcard, hAelem⟩
      exact hPrank.trans (section8_groupRank_le_of_subgroup (G := R) (S := (P : Subgroup R)))

omit [IsMinCE G] in
public theorem CFSG.section15_pPrimeCore_le
    {p : Nat.Primes} (H : Subgroup G) :
    section10PPrimeCore p H ≤ H := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  have hcore_eq :
      section10PPrimeCore p H = (pPrimeCore p.val H).map H.subtype := by
    have hp_eq : (⟨p.val, Fact.out⟩ : Nat.Primes) = p := Subtype.ext rfl
    simpa [section10PPrimeCore, section10PPrimeSet, hp_eq] using
      section8_piCoreIn_singleton_compl_eq_pPrimeCore_map
        (G := G) (p := p.val) H
  intro x hx
  rw [hcore_eq] at hx
  rcases Subgroup.mem_map.mp hx with ⟨xH, _hx, rfl⟩
  exact xH.property

omit [IsMinCE G] in
public theorem CFSG.section15_pPrimeCore_le_centralizer_pCoreIn
    {p : Nat.Primes} (H : Subgroup G) :
    section10PPrimeCore p H ≤
      Subgroup.centralizer (section15PCoreIn p H : Set G) := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  have hcore_eq :
      section10PPrimeCore p H = (pPrimeCore p.val H).map H.subtype := by
    have hp_eq : (⟨p.val, Fact.out⟩ : Nat.Primes) = p := Subtype.ext rfl
    simpa [section10PPrimeCore, section10PPrimeSet, hp_eq] using
      section8_piCoreIn_singleton_compl_eq_pPrimeCore_map
        (G := G) (p := p.val) H
  have hcentH :
      pPrimeCore p.val H ≤ Subgroup.centralizer (pCore p.val H : Set H) :=
    pPrimeCore_le_centralizer_of_normal_pgroup
      (G := H) (p := p.val) (R := pCore p.val H)
      (pCore_isPGroup (G := H) (p := p.val))
  intro x hx
  rw [hcore_eq] at hx
  rcases Subgroup.mem_map.mp hx with ⟨xH, hxH, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro y hyP
  have hyP' : y ∈ (pCore p.val H).map H.subtype := by
    simpa [section15PCoreIn] using hyP
  rcases Subgroup.mem_map.mp hyP' with ⟨yH, hyH, rfl⟩
  exact congrArg Subtype.val
    (Subgroup.mem_centralizer_iff.mp (hcentH hxH) yH hyH)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_E2_hall_in_E
    {M E E₁₂ E₂ : Subgroup G}
    (hE12 : section12HallSubgroupIn
      (section12Tau1Primes M ∪ section12Tau2Primes M) E₁₂ E)
    (hE2 : section12HallSubgroupIn (section12Tau2Primes M) E₂ E₁₂) :
    section12HallSubgroupIn (section12Tau2Primes M) E₂ E := by
  classical
  rcases hE12 with ⟨hE12E, hHallE12⟩
  rcases hE2 with ⟨hE2E12, hHallE2⟩
  refine ⟨hE2E12.trans hE12E, ?_⟩
  refine isHallSubgroup_of (G := E) (section12Tau2Primes M) (E₂.subgroupOf E) ?_ ?_
  · intro p hp
    have hcardE : Nat.card (E₂.subgroupOf E) = Nat.card E₂ :=
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := E₂) (K := E)
          (hE2E12.trans hE12E)).toEquiv
    have hcardE12 : Nat.card (E₂.subgroupOf E₁₂) = Nat.card E₂ :=
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := E₂) (K := E₁₂) hE2E12).toEquiv
    exact hHallE2.p_in_pi_of_p_dvd_card p (by simpa [hcardE, hcardE12] using hp)
  · intro p hpτ2 hpidx
    change p.val ∣ E₂.relIndex E at hpidx
    have hmul :
        E₂.relIndex E₁₂ * E₁₂.relIndex E = E₂.relIndex E :=
      Subgroup.relIndex_mul_relIndex E₂ E₁₂ E hE2E12 hE12E
    have hprod : p.val ∣ E₂.relIndex E₁₂ * E₁₂.relIndex E := by
      simpa [hmul] using hpidx
    rcases p.2.dvd_mul.mp hprod with hpidx2 | hpidx12
    · exact (hHallE2.p_in_pi_of_p_dvd_index p
        (by simpa [Subgroup.relIndex] using hpidx2)) hpτ2
    · exact (hHallE12.p_in_pi_of_p_dvd_index p
        (by simpa [Subgroup.relIndex] using hpidx12)) (Or.inr hpτ2)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_hallSubgroupIn_of_le_overgroup
    {M E U : Subgroup G} {π : Set Nat.Primes}
    (hU : section12HallSubgroupIn π U M)
    (hUE : U ≤ E) (hEM : E ≤ M) :
    section12HallSubgroupIn π U E := by
  classical
  rcases hU with ⟨hUM, hHallU⟩
  refine ⟨hUE, ?_⟩
  refine isHallSubgroup_of (G := E) π (U.subgroupOf E) ?_ ?_
  · intro p hp
    have hcardE : Nat.card (U.subgroupOf E) = Nat.card U :=
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := U) (K := E) hUE).toEquiv
    have hcardM : Nat.card (U.subgroupOf M) = Nat.card U :=
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := U) (K := M) hUM).toEquiv
    exact hHallU.p_in_pi_of_p_dvd_card p (by simpa [hcardE, hcardM] using hp)
  · intro p hpπ hpidx
    change p.val ∣ U.relIndex E at hpidx
    have hmul :
        U.relIndex E * E.relIndex M = U.relIndex M :=
      Subgroup.relIndex_mul_relIndex U E M hUE hEM
    have hpidxM : p.val ∣ U.relIndex M := by
      exact hmul ▸ dvd_mul_of_dvd_left hpidx (E.relIndex M)
    exact (hHallU.p_in_pi_of_p_dvd_index p
      (by simpa [Subgroup.relIndex] using hpidxM)) hpπ

private theorem CFSG.section15_tau2_piSubgroup_commutative
    {M E E₁₂ E₁ E₂ E₃ X : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hXE : X ≤ E)
    (hXπ : IsPiSubgroup (G := G) (section12Tau2Primes M) X) :
    IsMulCommutative X := by
  classical
  let Xsub : Subgroup E := X.subgroupOf E
  have hXsubπ : IsPiSubgroup (G := E) (section12Tau2Primes M) Xsub := by
    intro q hq
    have hcard : Nat.card Xsub = Nat.card X :=
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := X) (K := E) hXE).toEquiv
    exact hXπ q (by simpa [Xsub, hcard] using hq)
  have hEproper : E ≠ ⊤ := by
    intro hEtop
    have htop_le_M : (⊤ : Subgroup G) ≤ M := by
      simpa [hEtop] using hE.1.2.1
    exact hM.1 (top_le_iff.mp htop_le_M)
  have hEsolv : IsSolvable E :=
    IsMinCE.proper_subgroups_solvable E (lt_top_iff_ne_top.2 hEproper)
  letI : MulDistribMulAction Unit E := {
    smul := fun _ x => x
    one_smul := fun x => rfl
    mul_smul := fun _ _ x => rfl
    smul_mul := fun _ x y => rfl
    smul_one := fun _ => rfl }
  have hXsubInv : IsInvariant Unit E Xsub := by
    refine ⟨?_⟩
    intro a x
    simp
  rcases exists_isHallSubgroup_isInvariant_of_isPiSubgroup
      (G := E) (A := Unit) hEsolv (by simp)
      (section12Tau2Primes M) Xsub hXsubπ hXsubInv with
    ⟨H, hHHall, _hHinv, hXH⟩
  have hE2Hall :
      IsHallSubgroup (section12Tau2Primes M) (E₂.subgroupOf E) :=
    (section15_E2_hall_in_E hE.2.1 hE.2.2.2.1).2
  rcases exists_conj_eq_of_isHallSubgroup_of_solvable
      (G := E) hEsolv hE2Hall hHHall with ⟨g, hHg⟩
  have hE2comm : IsMulCommutative E₂ :=
    (corollary_12_10_b (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE).1
  have hE2sub_comm : IsMulCommutative (E₂.subgroupOf E) := by
    letI : IsMulCommutative E₂ := hE2comm
    refine ⟨⟨fun x y => ?_⟩⟩
    apply Subtype.ext
    apply Subtype.ext
    have hxE2 : ((x : E) : G) ∈ E₂ := by
      exact Subgroup.mem_subgroupOf.mp x.property
    have hyE2 : ((y : E) : G) ∈ E₂ := by
      exact Subgroup.mem_subgroupOf.mp y.property
    exact setLike_mul_comm (s := E₂) hxE2 hyE2
  have hHcomm : IsMulCommutative H := by
    have hmapcomm :
        IsMulCommutative ((E₂.subgroupOf E).map (MulAut.conj g).toMonoidHom) := by
      letI : IsMulCommutative (E₂.subgroupOf E) := hE2sub_comm
      exact Subgroup.map_isMulCommutative
        (f := (MulAut.conj g).toMonoidHom) (H := E₂.subgroupOf E)
    rw [hHg]
    exact hmapcomm
  letI : IsMulCommutative H := hHcomm
  refine ⟨⟨fun x y => ?_⟩⟩
  let xE : E := ⟨x, hXE x.property⟩
  let yE : E := ⟨y, hXE y.property⟩
  have hxXsub : xE ∈ Xsub := by
    simp [Xsub, xE, Subgroup.mem_subgroupOf]
  have hyXsub : yE ∈ Xsub := by
    simp [Xsub, yE, Subgroup.mem_subgroupOf]
  have hxH : xE ∈ H := hXH hxXsub
  have hyH : yE ∈ H := hXH hyXsub
  have hcommE : xE * yE = yE * xE :=
    setLike_mul_comm (s := H) hxH hyH
  apply Subtype.ext
  exact congrArg (fun z : E => (z : G)) hcommE

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_exists_noncyclic_sylow_of_noncyclic_commutative
    {X : Type*} [Group X] [Finite X]
    (hXcomm : IsMulCommutative X) (hXnoncyc : ¬ IsCyclic X) :
    ∃ p : Nat.Primes, ∃ P : Sylow p.val X, ¬ IsCyclic P := by
  classical
  by_contra hnone
  have hZ : IsZGroup X := by
    refine ⟨?_⟩
    intro p hp P
    by_contra hP
    exact hnone ⟨⟨p, hp⟩, P, hP⟩
  haveI : IsZGroup X := hZ
  letI : IsMulCommutative X := hXcomm
  letI : CommGroup X := IsMulCommutative.instCommGroup
  haveI : Group.IsNilpotent X := inferInstance
  exact hXnoncyc (inferInstance : IsCyclic X)

/-- Section 15 local copy of the Section 12 rank-two extraction used in
Lemma 15.1(c).
Section 12. -/
private theorem CFSG.section15_exists_rankTwo_in_noncyclic_tau2_piSubgroup
    {M E E₁₂ E₁ E₂ E₃ X : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hXE : X ≤ E)
    (hXπ : IsPiSubgroup (G := G) (section12Tau2Primes M) X)
    (hXnoncyc : ¬ IsCyclic X) :
    ∃ p : Nat.Primes, p ∈ section12Tau2Primes M ∧
      ∃ A : Subgroup G, A ≤ X ∧ A ∈ section12RankTwoElementaryAbelianIn p M := by
  classical
  have hXcomm : IsMulCommutative X :=
    section15_tau2_piSubgroup_commutative
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂)
      (E₃ := E₃) (X := X) hM hE hXE hXπ
  rcases section15_exists_noncyclic_sylow_of_noncyclic_commutative
      (X := X) hXcomm hXnoncyc with ⟨p, P, hPnoncyc⟩
  haveI : Fact p.val.Prime := ⟨p.property⟩
  let Pamb : Subgroup G := (P : Subgroup X).map X.subtype
  have hPamb_p : IsPGroup p.val Pamb := by
    simpa [Pamb] using
      (IsPGroup.map (p := p.val) (H := (P : Subgroup X)) P.isPGroup' X.subtype)
  have hPnoncyc_sub : ¬ IsCyclic (P : Subgroup X) := by
    simpa using hPnoncyc
  have hPamb_noncyc : ¬ IsCyclic Pamb := by
    intro hPamb_cyc
    let e : (P : Subgroup X) ≃* Pamb :=
      Subgroup.equivMapOfInjective (f := X.subtype) (P : Subgroup X) X.subtype_injective
    exact hPnoncyc_sub (e.isCyclic.2 hPamb_cyc)
  obtain ⟨A, hA_Pamb⟩ :=
    section15_exists_rankTwo_in_noncyclic_pSubgroup
      (G := G) (P := Pamb) (p := p) hPamb_p hPamb_noncyc
  rcases (by simpa [section12RankTwoElementaryAbelianIn] using hA_Pamb) with
    ⟨hA_le_Pamb, hAelem⟩
  have hPamb_le_X : Pamb ≤ X := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hA_le_X : A ≤ X := hA_le_Pamb.trans hPamb_le_X
  have hp_dvd_X : p.val ∣ Nat.card X := by
    rcases P.isPGroup'.exists_card_eq with ⟨n, hn⟩
    have hp_dvd_P : p.val ∣ Nat.card (P : Subgroup X) := by
      cases n with
      | zero =>
          have hcard_one : Nat.card (P : Subgroup X) = 1 := by
            simpa using hn
          exact False.elim <| hPnoncyc_sub <| by
            letI : Subsingleton (P : Subgroup X) :=
              (Nat.card_eq_one_iff_unique.mp hcard_one).1
            exact isCyclic_of_subsingleton (α := (P : Subgroup X))
      | succ n =>
          rw [hn]
          exact dvd_pow_self p.val (Nat.succ_ne_zero n)
    exact hp_dvd_P.trans (Subgroup.card_subgroup_dvd_card (P : Subgroup X))
  have hpτ2 : p ∈ section12Tau2Primes M := hXπ p hp_dvd_X
  have hA_le_M : A ≤ M := hA_le_X.trans (hXE.trans hE.1.2.1)
  have hA_M : A ∈ section12RankTwoElementaryAbelianIn p M := by
    exact ⟨hA_le_M, hAelem⟩
  exact ⟨p, hpτ2, A, hA_le_X, hA_M⟩

/-- Section 15 local fixed-complement version of the Section 12 data
construction: a chosen complement `E` to `M_σ` can be refined to full
`section12EData`. -/
public theorem CFSG.section15_exists_EData_for_fixed_sigma_complement
    {M E : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hEcomp : section12ComplementToMsigma M E) :
    ∃ E₁₂ E₁ E₂ E₃ : Subgroup G,
      section12EData M E E₁₂ E₁ E₂ E₃ := by
  classical
  have hEM : E ≤ M := hEcomp.2.1
  have hEHall :
      IsHallSubgroup (section10SigmaPrimes M)ᶜ (E.subgroupOf M) :=
    section12_msigma_complement_isHall_sigma_compl hM hEcomp
  have hEπ : IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ E := by
    intro q hqE
    have hcard : Nat.card (E.subgroupOf M) = Nat.card E :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := E) (K := M) hEM).toEquiv
    exact hEHall.p_in_pi_of_p_dvd_card q (by simpa [hcard] using hqE)
  rcases section13_exists_EData_containing_sigma_compl_piSubgroup
      (G := G) (M := M) (A := E) hM hEM hEπ with
    ⟨E', E₁₂, E₁, E₂, E₃, hE'data, hEE'⟩
  have hE'M : E' ≤ M := hE'data.1.2.1
  have hE'Hall :
      IsHallSubgroup (section10SigmaPrimes M)ᶜ (E'.subgroupOf M) :=
    section12_msigma_complement_isHall_sigma_compl hM hE'data.1
  have hsub_le : E.subgroupOf M ≤ E'.subgroupOf M := by
    intro x hx
    exact hEE' hx
  have hsub_eq : E.subgroupOf M = E'.subgroupOf M :=
    hEHall.eq_of_le hE'Hall hsub_le
  have hE'_le_E : E' ≤ E := by
    intro x hx
    have hxsub : (⟨x, hE'M hx⟩ : M) ∈ E'.subgroupOf M := by
      simpa [Subgroup.mem_subgroupOf] using hx
    have hxsubE : (⟨x, hE'M hx⟩ : M) ∈ E.subgroupOf M := by
      simpa [hsub_eq] using hxsub
    simpa [Subgroup.mem_subgroupOf] using hxsubE
  have hEeq : E' = E := le_antisymm hE'_le_E hEE'
  refine ⟨E₁₂, E₁, E₂, E₃, ?_⟩
  simpa [hEeq] using hE'data

public theorem CFSG.section15_tau2_mem_subgroupPrimeSet_of_complement
    {M E : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hEcomp : section12ComplementToMsigma M E)
    (hpτ2 : p ∈ section12Tau2Primes M) :
    p ∈ subgroupPrimeSet M := by
  classical
  rcases section15_exists_EData_for_fixed_sigma_complement
      (G := G) (M := M) (E := E) hM hEcomp with
    ⟨E₁₂, E₁, E₂, E₃, hEdata⟩
  rcases section12_exists_rankTwo_in_E_of_tau2
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hEdata hpτ2 with
    ⟨A, hA⟩
  exact section12_rankTwo_prime_mem
    (G := G) (M := M) (A := A) (p := p)
    (section12_rankTwo_of_EData hEdata hA)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_subgroupPrimeSet_of_hallSubgroupIn
    {π : Set Nat.Primes} {K H : Subgroup G} {p : Nat.Primes}
    (hK : section12HallSubgroupIn π K H)
    (hpπ : p ∈ π)
    (hpH : p ∈ subgroupPrimeSet H) :
    p ∈ subgroupPrimeSet K := by
  classical
  rcases hK with ⟨hKH, hHallK⟩
  have hcardK :
      Nat.card (K.subgroupOf H) = Nat.card K :=
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := K) (K := H) hKH).toEquiv
  have hHcard :
      (K.subgroupOf H).index * Nat.card (K.subgroupOf H) = Nat.card H :=
    Subgroup.index_mul_card (H := K.subgroupOf H)
  have hpdiv :
      p.val ∣ (K.subgroupOf H).index * Nat.card (K.subgroupOf H) := by
    simpa [hHcard, subgroupPrimeSet] using hpH
  rcases p.2.dvd_mul.mp hpdiv with hpidx | hpcard
  · exact False.elim ((hHallK.p_in_pi_of_p_dvd_index p hpidx) hpπ)
  · simpa [subgroupPrimeSet, hcardK] using hpcard

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_msigma_le_normalizer
    {M : Subgroup G} :
    M ≤ Subgroup.normalizer (section10Msigma M : Set G) := by
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨xM, hxσ, hx_eq⟩
    let mM : M := ⟨m, hm⟩
    have hconj : mM * xM * mM⁻¹ ∈ section10MsigmaSubgroup M :=
      (show (section10MsigmaSubgroup M).Normal from inferInstance).conj_mem xM hxσ mM
    refine Subgroup.mem_map.mpr ⟨mM * xM * mM⁻¹, hconj, ?_⟩
    have hx_eq' : (xM : G) = x := by simpa using hx_eq
    calc
      ((mM * xM * mM⁻¹ : M) : G) = m * (xM : G) * m⁻¹ := by
        simp [mM]
      _ = m * x * m⁻¹ := by rw [hx_eq']
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨xM, hxσ, hx_eq⟩
    let mM : M := ⟨m, hm⟩
    have hconj : mM⁻¹ * xM * (mM⁻¹)⁻¹ ∈ section10MsigmaSubgroup M :=
      (show (section10MsigmaSubgroup M).Normal from inferInstance).conj_mem xM hxσ mM⁻¹
    refine Subgroup.mem_map.mpr ⟨mM⁻¹ * xM * (mM⁻¹)⁻¹, hconj, ?_⟩
    have hx_eq' : (xM : G) = m * x * m⁻¹ := by simpa using hx_eq
    calc
      ((mM⁻¹ * xM * (mM⁻¹)⁻¹ : M) : G) = m⁻¹ * (xM : G) * (m⁻¹)⁻¹ := by
        simp [mM]
      _ = m⁻¹ * (m * x * m⁻¹) * (m⁻¹)⁻¹ := by rw [hx_eq']
      _ = x := by group

private theorem CFSG.section15_frobeniusJoinWithKernel_of_regular_subgroup
    {M R : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hRM : R ≤ M)
    (hdisj : Disjoint (section10Msigma M) R)
    (hRne : R ≠ ⊥)
    (hreg : ∀ r : G, r ∈ R → r ≠ 1 →
      elementCentralizerIn (section10Msigma M) r = ⊥) :
    section12FrobeniusJoinWithKernel (section10Msigma M) R := by
  classical
  let K : Subgroup G := section10Msigma M
  let S : Subgroup G := K ⊔ R
  let Ksub : Subgroup S := K.subgroupOf S
  let Rsub : Subgroup S := R.subgroupOf S
  have hR_norm_K : R ≤ Subgroup.normalizer (K : Set G) := by
    intro r hr
    exact section15_msigma_le_normalizer (M := M) (hRM hr)
  haveI : Ksub.Normal := by
    have hS_le_normK : S ≤ Subgroup.normalizer (K : Set G) := by
      exact sup_le Subgroup.le_normalizer hR_norm_K
    simpa [Ksub, S] using
      (Subgroup.normal_subgroupOf_iff_le_normalizer (H := K) (K := S) le_sup_left).2
        hS_le_normK
  have hKsub_ne : Ksub ≠ ⊥ := by
    intro hbot
    have hKbot : K = ⊥ := by
      apply le_bot_iff.mp
      intro x hxK
      let xS : S := ⟨x, Subgroup.mem_sup_left hxK⟩
      have hxKsub : xS ∈ Ksub := by
        simpa [Ksub, xS, Subgroup.mem_subgroupOf] using hxK
      have hxbot : xS ∈ (⊥ : Subgroup S) := by simpa [hbot] using hxKsub
      have hxS_one : xS = 1 := Subgroup.mem_bot.mp hxbot
      change x = 1
      exact congrArg Subtype.val hxS_one
    exact (theorem_10_2_e (G := G) hM) (by simpa [K] using hKbot)
  have hRsub_ne : Rsub ≠ ⊥ := by
    intro hbot
    apply hRne
    apply le_bot_iff.mp
    intro x hxR
    let xS : S := ⟨x, Subgroup.mem_sup_right hxR⟩
    have hxRsub : xS ∈ Rsub := by
      simpa [Rsub, xS, Subgroup.mem_subgroupOf] using hxR
    have hxbot : xS ∈ (⊥ : Subgroup S) := by simpa [hbot] using hxRsub
    have hxS_one : xS = 1 := Subgroup.mem_bot.mp hxbot
    change x = 1
    exact congrArg Subtype.val hxS_one
  have hcomp : Ksub.IsComplement' Rsub := by
    have hsup_local : Ksub ⊔ Rsub = ⊤ := by
      calc
        Ksub ⊔ Rsub = (K ⊔ R).subgroupOf S := by
          symm
          exact Subgroup.subgroupOf_sup (A := K) (A' := R) (B := S)
            le_sup_left le_sup_right
        _ = ⊤ := by simp [S]
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [Subgroup.disjoint_def]
      intro x hxK hxR
      apply Subtype.ext
      exact Subgroup.disjoint_def.mp hdisj
        (by simpa [Ksub, K, Subgroup.mem_subgroupOf] using hxK)
        (by simpa [Rsub, Subgroup.mem_subgroupOf] using hxR)
    · simpa [hsup_local] using (Subgroup.normal_mul Ksub Rsub).symm
  have hcent : ∀ x : Rsub, x ≠ 1 → elementCentralizerIn Ksub (x : S) = ⊥ := by
    intro x hxne
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    rcases hy with ⟨hyK, hyC⟩
    have hxR : ((x : S) : G) ∈ R := by
      exact Subgroup.mem_subgroupOf.mp x.property
    have hxGne : ((x : S) : G) ≠ 1 := by
      intro hxG
      apply hxne
      apply Subtype.ext
      simpa using hxG
    have hyKamb : ((y : S) : G) ∈ K := by
      simpa [Ksub, K, Subgroup.mem_subgroupOf] using hyK
    have hyCentAmb : ((y : S) : G) ∈ Subgroup.centralizer ({((x : S) : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      have hcommS : (y : S) * x = x * (y : S) :=
        Subgroup.mem_centralizer_singleton_iff.mp hyC
      exact (congrArg Subtype.val hcommS).symm
    have hyAmb : ((y : S) : G) ∈ elementCentralizerIn K ((x : S) : G) :=
      ⟨hyKamb, hyCentAmb⟩
    have hybot : ((y : S) : G) ∈ (⊥ : Subgroup G) := by
      rw [hreg ((x : S) : G) hxR hxGne] at hyAmb
      simpa [K] using hyAmb
    apply Subtype.ext
    simpa using hybot
  simpa [section12FrobeniusJoinWithKernel, K, S, Ksub, Rsub] using
    (lemma_3_1 (G := S) (K := Ksub) (R := Rsub) hKsub_ne hRsub_ne
      (by infer_instance) hcomp).2 hcent

private theorem CFSG.section15_same_exponent_frobenius_of_regular_abelian
    {M V : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hVM : V ≤ M)
    (hVcomm : IsMulCommutative V)
    (hVne : V ≠ ⊥)
    (hdisj : Disjoint (section10Msigma M) V)
    (hreg : ∀ v : G, v ∈ V → v ≠ 1 →
      elementCentralizerIn (section10Msigma M) v = ⊥) :
    ∃ V₀ : Subgroup G, V₀ ≤ V ∧ Monoid.exponent V₀ = Monoid.exponent V ∧
      section12FrobeniusJoinWithKernel (section10Msigma M) V₀ := by
  classical
  letI : IsMulCommutative V := hVcomm
  letI : CommGroup V := IsMulCommutative.instCommGroup
  obtain ⟨v, hvexp⟩ :=
    Monoid.exists_orderOf_eq_exponent (G := V)
      (Monoid.ExponentExists.of_finite (G := V))
  let vG : G := v
  let V₀ : Subgroup G := Subgroup.zpowers vG
  have hvG_mem : vG ∈ V := v.property
  have hV₀V : V₀ ≤ V := Subgroup.zpowers_le.2 hvG_mem
  have hvG_order : orderOf vG = Monoid.exponent V := by
    simpa [vG, Subgroup.orderOf_coe] using hvexp
  have hV₀_exp : Monoid.exponent V₀ = Monoid.exponent V := by
    haveI : IsCyclic V₀ := by
      dsimp [V₀]
      infer_instance
    calc
      Monoid.exponent V₀ = Nat.card V₀ := IsCyclic.exponent_eq_card
      _ = orderOf vG := Nat.card_zpowers vG
      _ = Monoid.exponent V := hvG_order
  have hvG_ne : vG ≠ 1 := by
    intro hvG_one
    have hv_one : v = 1 := Subtype.ext hvG_one
    have hExp_one : Monoid.exponent V = 1 := by
      simpa [hv_one] using hvexp.symm
    have hsub : Subsingleton V := Monoid.exp_eq_one_iff.mp hExp_one
    exact hVne (le_bot_iff.mp (by
      intro x hx
      have hx_one : (⟨x, hx⟩ : V) = 1 := Subsingleton.elim _ _
      simpa using congrArg Subtype.val hx_one))
  have hV₀_ne : V₀ ≠ ⊥ := by
    simpa [V₀] using (Subgroup.zpowers_ne_bot.mpr hvG_ne)
  have hdisj₀ : Disjoint (section10Msigma M) V₀ := by
    rw [Subgroup.disjoint_def] at hdisj ⊢
    intro x hxσ hxV₀
    exact hdisj hxσ (hV₀V hxV₀)
  have hreg₀ : ∀ v : G, v ∈ V₀ → v ≠ 1 →
      elementCentralizerIn (section10Msigma M) v = ⊥ := by
    intro v hvV₀ hvne
    exact hreg v (hV₀V hvV₀) hvne
  exact ⟨V₀, hV₀V, hV₀_exp,
    section15_frobeniusJoinWithKernel_of_regular_subgroup
      (M := M) (R := V₀) hM (hV₀V.trans hVM) hdisj₀ hV₀_ne hreg₀⟩


omit [IsMinCE G] in
private theorem CFSG.section15_default_ambient_sylow_of_prime_dvd
    {V : Subgroup G} {p : Nat.Primes}
    (hVcomm : IsMulCommutative V)
    (hpV : p.val ∣ Nat.card V) :
    let P : Sylow p.val V := default
    let PG : Subgroup G := section10AmbientSylowSubgroup V P
    PG ≤ V ∧ PG ≠ ⊥ ∧ IsPGroup p.val PG ∧ IsMulCommutative PG ∧
      section10NormalIn PG V := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  let P : Sylow p.val V := default
  let PG : Subgroup G := section10AmbientSylowSubgroup V P
  have hPGV : PG ≤ V := by
    intro x hx
    have hxmap : x ∈ (P : Subgroup V).map V.subtype := by
      simpa [PG, section10AmbientSylowSubgroup] using hx
    rcases Subgroup.mem_map.mp hxmap with
      ⟨y, _hyP, rfl⟩
    exact y.property
  have hPGne : PG ≠ ⊥ := by
    have hP_ne : (P : Subgroup V) ≠ ⊥ :=
      Sylow.ne_bot_of_dvd_card (G := V) (p := p.val) P hpV
    intro hPGbot
    have hcard_map : Nat.card PG = Nat.card (P : Subgroup V) := by
      simpa [PG, section10AmbientSylowSubgroup] using
        (Subgroup.card_map_of_injective
          (K := (P : Subgroup V)) (f := V.subtype) V.subtype_injective)
    have hP_card : Nat.card (P : Subgroup V) = 1 := by
      rw [← hcard_map]
      simp [hPGbot]
    exact hP_ne ((Subgroup.card_eq_one (H := (P : Subgroup V))).1 hP_card)
  have hPGp : IsPGroup p.val PG := by
    change IsPGroup p.val ((P : Subgroup V).map V.subtype)
    exact IsPGroup.map (p := p.val) (H := (P : Subgroup V)) P.isPGroup' V.subtype
  have hPGcomm : IsMulCommutative PG := by
    refine ⟨⟨fun x y => ?_⟩⟩
    apply Subtype.ext
    exact setLike_mul_comm (s := V)
      (hPGV x.property) (hPGV y.property)
  have hPGnorm : section10NormalIn PG V := by
    refine ⟨hPGV, ?_⟩
    letI : IsMulCommutative V := hVcomm
    infer_instance
  exact ⟨hPGV, hPGne, hPGp, hPGcomm, hPGnorm⟩

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_pSubgroup_le_normal_hall_of_prime_mem
    {R : Type*} [Group R] [Finite R] {π : Set Nat.Primes}
    {H A : Subgroup R} [H.Normal] {p : Nat.Primes}
    (hHall : IsHallSubgroup π H) (hpπ : p ∈ π)
    (hAp : IsPGroup p.val A) :
    A ≤ H := by
  classical
  letI : Fact p.val.Prime := ⟨p.property⟩
  rw [← QuotientGroup.ker_mk' H]
  rw [← Subgroup.map_eq_bot_iff (f := QuotientGroup.mk' H) (H := A)]
  by_contra hmap_ne_bot
  have hAmap_p : IsPGroup p.val (A.map (QuotientGroup.mk' H)) :=
    IsPGroup.map hAp (QuotientGroup.mk' H)
  obtain ⟨n, hn⟩ := hAmap_p.exists_card_eq
  have hp_dvd_map : p.val ∣ Nat.card (A.map (QuotientGroup.mk' H)) := by
    rw [hn]
    cases n with
    | zero =>
        have hcard_one : Nat.card (A.map (QuotientGroup.mk' H)) = 1 := by
          simpa [hn]
        exact False.elim
          (hmap_ne_bot
            ((Subgroup.card_eq_one (H := A.map (QuotientGroup.mk' H))).1 hcard_one))
    | succ n =>
        exact dvd_pow_self p.val (Nat.succ_ne_zero n)
  have hcard_map_dvd_quot :
      Nat.card (A.map (QuotientGroup.mk' H)) ∣ Nat.card (R ⧸ H) :=
    Subgroup.card_subgroup_dvd_card (A.map (QuotientGroup.mk' H))
  have hp_dvd_quot : p.val ∣ Nat.card (R ⧸ H) :=
    hp_dvd_map.trans hcard_map_dvd_quot
  have hp_dvd_index : p.val ∣ H.index := by
    simpa [Subgroup.index_eq_card] using hp_dvd_quot
  exact (hHall.p_in_pi_of_p_dvd_index p hp_dvd_index) hpπ

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_rankTwo_le
    {M A : Subgroup G} {p : Nat.Primes}
    (hA : A ∈ section12RankTwoElementaryAbelianIn p M) :
    A ≤ M := by
  rcases (by simpa [section12RankTwoElementaryAbelianIn] using hA) with ⟨hAM, _hA⟩
  exact hAM

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_rankTwo_elementary
    {M A : Subgroup G} {p : Nat.Primes}
    (hA : A ∈ section12RankTwoElementaryAbelianIn p M) :
    A ∈ elementaryAbelianSubgroupsOfRank p.val 2 G := by
  rcases (by simpa [section12RankTwoElementaryAbelianIn] using hA) with ⟨_hAM, hA⟩
  exact hA

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_not_isCyclic_of_two_le_generatorRank
    {H : Type*} [Group H] (hHrank : 2 ≤ generatorRank H) :
    ¬ IsCyclic H := by
  intro hcyc
  have hle : generatorRank H ≤ 1 := generatorRank_le_one_of_isCyclic (G := H) hcyc
  have hlt : 1 < generatorRank H := lt_of_lt_of_le (by decide : 1 < 2) hHrank
  exact (not_lt_of_ge hle) hlt

omit [IsMinCE G] in
public theorem CFSG.section15_rankTwo_not_isCyclic
    {M A : Subgroup G} {p : Nat.Primes}
    (hA : A ∈ section12RankTwoElementaryAbelianIn p M) :
    ¬ IsCyclic A := by
  haveI : Fact p.val.Prime := ⟨p.2⟩
  rcases section15_rankTwo_elementary hA with ⟨hcard, _hElem⟩
  exact section15_not_isCyclic_of_two_le_generatorRank
    (section12_generatorRank_at_least_two_of_elementaryAbelian_card_p_sq
      (p := p.val) hcard)

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_rankTwo_subgroupOf_isPGroup
    {M A : Subgroup G} {p : Nat.Primes}
    (hA : A ∈ section12RankTwoElementaryAbelianIn p M) :
    IsPGroup p.val (A.subgroupOf M) := by
  have hAM : A ≤ M := section15_rankTwo_le hA
  rcases section15_rankTwo_elementary hA with ⟨_hcard, hElem⟩
  let e : A.subgroupOf M ≃* A := Subgroup.subgroupOfEquivOfLe hAM
  have hAp : IsPGroup p.val A := by
    haveI : IsElementaryAbelian p.val A := hElem
    exact IsElementaryAbelian.isPGroup p.val A
  exact hAp.of_equiv e.symm

omit [IsMinCE G] in
private theorem CFSG.section15_rankTwo_le_normal_hall_of_prime_dvd
    {E V A : Subgroup G} {p : Nat.Primes}
    (hVnorm : section10NormalIn V E)
    (hVHall : ∃ π : Set Nat.Primes, section12HallSubgroupIn π V E)
    (hpV : p.val ∣ Nat.card V)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E) :
    A ≤ V := by
  classical
  rcases hVHall with ⟨π, hVHallπ⟩
  rcases hVHallπ with ⟨hVE, hHallV⟩
  have hpπ : p ∈ π := by
    have hcard_sub : Nat.card (V.subgroupOf E) = Nat.card V :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := V) (K := E) hVE).toEquiv
    exact hHallV.p_in_pi_of_p_dvd_card p (by simpa [hcard_sub] using hpV)
  have hAE : A ≤ E := section15_rankTwo_le hA
  have hAsub_p : IsPGroup p.val (A.subgroupOf E) :=
    section15_rankTwo_subgroupOf_isPGroup hA
  haveI : (V.subgroupOf E).Normal := hVnorm.2
  have hAsub_le_Vsub : A.subgroupOf E ≤ V.subgroupOf E :=
    section15_pSubgroup_le_normal_hall_of_prime_mem
      (R := E) (π := π) (H := V.subgroupOf E) (A := A.subgroupOf E)
      hHallV hpπ hAsub_p
  intro x hxA
  let xE : E := ⟨x, hAE hxA⟩
  have hxsub : xE ∈ A.subgroupOf E := by
    simpa [xE, Subgroup.mem_subgroupOf] using hxA
  have hxVsub : xE ∈ V.subgroupOf E := hAsub_le_Vsub hxsub
  simpa [xE, Subgroup.mem_subgroupOf] using hxVsub


omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_subgroupCentralizerIn_zpowers_eq_elementCentralizerIn_early
    {Q : Subgroup G} (a : G) :
    subgroupCentralizerIn Q (Subgroup.zpowers a) = elementCentralizerIn Q a := by
  ext x
  constructor
  · intro hx
    refine ⟨hx.1, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr <| by
      have hxcent : x ∈ Subgroup.centralizer ((Subgroup.zpowers a) : Set G) := hx.2
      have hcomm : a * x = x * a :=
        Subgroup.mem_centralizer_iff.mp hxcent a (Subgroup.mem_zpowers a)
      exact hcomm.symm
  · intro hx
    refine ⟨hx.1, ?_⟩
    change x ∈ Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases Subgroup.mem_zpowers_iff.mp hy with ⟨n, rfl⟩
    have hcomm : Commute a x :=
      (Subgroup.mem_centralizer_singleton_iff.mp hx.2).symm
    simpa using (hcomm.zpow_left n).eq


omit [IsMinCE G] in
private noncomputable def CFSG.section15_mulEquiv_iSup_of_pairwise_coprime_order
    {ι : Type*} [Fintype ι] [DecidableEq ι] (H : ι → Subgroup G)
    (hcomm : Pairwise fun i j => ∀ x y, x ∈ H i → y ∈ H j → Commute x y)
    (hcoprime : Pairwise fun i j => Nat.Coprime (Nat.card (H i)) (Nat.card (H j))) :
    (∀ i, H i) ≃* ↥(⨆ i, H i) := by
  classical
  letI : ∀ i, Fintype ↥(H i) := fun i => Fintype.ofFinite ↥(H i)
  have hcoprime' : Pairwise fun i j => Nat.Coprime (Fintype.card (H i)) (Fintype.card (H j)) := by
    intro i j hij
    simpa [Nat.card_eq_fintype_card] using hcoprime hij
  have hind : iSupIndep H :=
    Subgroup.independent_of_coprime_order hcomm hcoprime'
  let ϕ := Subgroup.noncommPiCoprod (H := H) (hcomm := hcomm)
  have h_range : ϕ.range = ⨆ i, H i :=
    Subgroup.noncommPiCoprod_range (H := H) (hcomm := hcomm)
  have hinj : Function.Injective ϕ :=
    Subgroup.injective_noncommPiCoprod_of_iSupIndep (H := H) (hcomm := hcomm) hind
  let hcod : ∀ a, ϕ a ∈ ⨆ i, H i := by
    intro a
    rw [← h_range]
    exact ⟨a, rfl⟩
  let ϕ' : (∀ i, H i) →* ↥(⨆ i, H i) := ϕ.codRestrict (⨆ i, H i) hcod
  have hinj' : Function.Injective ϕ' :=
    (ϕ.injective_codRestrict (⨆ i, H i) hcod).mpr hinj
  have hsurj' : Function.Surjective ϕ' := by
    intro x
    have hx : x.1 ∈ ϕ.range := by
      rw [h_range]
      exact x.2
    rcases hx with ⟨a, ha⟩
    exact ⟨a, Subtype.ext ha⟩
  exact MulEquiv.ofBijective ϕ' ⟨hinj', hsurj'⟩

omit [IsMinCE G] in
private theorem CFSG.section15_exponent_eq_iSup_of_pairwise_coprime_order
    {ι : Type*} [Fintype ι] [DecidableEq ι] (H : ι → Subgroup G)
    (hcomm : Pairwise fun i j => ∀ x y, x ∈ H i → y ∈ H j → Commute x y)
    (hcoprime : Pairwise fun i j => Nat.Coprime (Nat.card (H i)) (Nat.card (H j))) :
    Monoid.exponent ↥(⨆ i, H i) = Finset.lcm Finset.univ (fun i => Monoid.exponent (H i)) := by
  classical
  letI : ∀ i, Fintype (H i) := fun i => Fintype.ofFinite (H i)
  let e := section15_mulEquiv_iSup_of_pairwise_coprime_order (G := G) H hcomm hcoprime
  calc
    Monoid.exponent ↥(⨆ i, H i) = Monoid.exponent (∀ i, H i) := by
      simpa using (Monoid.exponent_eq_of_mulEquiv e).symm
    _ = Finset.lcm Finset.univ (fun i => Monoid.exponent (H i)) := by
      simpa using (Monoid.exponent_pi (M := fun i => H i))

omit [IsMinCE G] in
private theorem CFSG.section15_isCyclic_pi_of_pairwise_coprime_cyclic
    {ι : Type*} [Fintype ι] [DecidableEq ι] (H : ι → Subgroup G)
    (hcyc : ∀ i, IsCyclic (H i))
    (hcoprime : Pairwise fun i j => Nat.Coprime (Nat.card (H i)) (Nat.card (H j))) :
    IsCyclic (∀ i, H i) := by
  classical
  letI : ∀ i, Fintype (H i) := fun i => Fintype.ofFinite (H i)
  letI : ∀ i, CommGroup (H i) := fun i => IsMulCommutative.instCommGroup
  have hexp_coprime :
      Set.Pairwise (↑(Finset.univ : Finset ι)) (Nat.Coprime.onFun fun i => Monoid.exponent (H i)) := by
    intro i hi j hj hij
    change Nat.Coprime (Monoid.exponent (H i)) (Monoid.exponent (H j))
    rw [show Monoid.exponent (H i) = Fintype.card (H i) by
          rw [(hcyc i).exponent_eq_card, Nat.card_eq_fintype_card]]
    rw [show Monoid.exponent (H j) = Fintype.card (H j) by
          rw [(hcyc j).exponent_eq_card, Nat.card_eq_fintype_card]]
    simpa [Nat.card_eq_fintype_card] using hcoprime hij
  rw [IsCyclic.iff_exponent_eq_card]
  rw [Monoid.exponent_pi]
  rw [Nat.card_eq_fintype_card, Fintype.card_pi]
  rw [Finset.lcm_eq_prod hexp_coprime]
  congr with i
  rw [← Nat.card_eq_fintype_card, (hcyc i).exponent_eq_card]

omit [IsMinCE G] in
private theorem CFSG.section15_isCyclic_iSup_of_pairwise_coprime_cyclic
    {ι : Type*} [Fintype ι] [DecidableEq ι] (H : ι → Subgroup G)
    (hcyc : ∀ i, IsCyclic (H i))
    (hcomm : Pairwise fun i j => ∀ x y, x ∈ H i → y ∈ H j → Commute x y)
    (hcoprime : Pairwise fun i j => Nat.Coprime (Nat.card (H i)) (Nat.card (H j))) :
    IsCyclic ↥(⨆ i, H i) := by
  let e := section15_mulEquiv_iSup_of_pairwise_coprime_order (G := G) H hcomm hcoprime
  exact e.isCyclic.mp
    (section15_isCyclic_pi_of_pairwise_coprime_cyclic (G := G) H hcyc hcoprime)

omit [IsMinCE G] in
private lemma CFSG.section15_unique_subgroup_of_prime_order_in_cyclic
    {H : Type*} [Group H] [Finite H] [IsCyclic H]
    {p : ℕ} [Fact p.Prime] (A B : Subgroup H)
    (hA : Nat.card A = p) (hB : Nat.card B = p) : A = B := by
  have hp_prime : Nat.Prime p := Fact.out
  have hp_pos : 0 < p := Nat.Prime.pos hp_prime
  have hp_dvd_cardH : p ∣ Nat.card H := by
    rw [← hA]
    exact Subgroup.card_subgroup_dvd_card A
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := H)
  have hg_order : orderOf g = Nat.card H := by
    apply orderOf_eq_card_of_forall_mem_zpowers
    intro x
    have hx := hg x
    rcases (Submonoid.mem_powers_iff _ _).mp hx with ⟨k, hk⟩
    rw [← hk]
    exact ⟨(k : ℤ), by simp⟩
  set d := Nat.card H / p with hd_def
  have hd_mul : d * p = Nat.card H := Nat.div_mul_cancel hp_dvd_cardH
  have hd_dvd : d ∣ Nat.card H := by
    rw [← hd_mul]
    exact ⟨p, rfl⟩
  have hd_pos : 0 < d := by
    by_contra hd0
    have hd0' : d = 0 := Nat.eq_zero_of_not_pos hd0
    rw [hd0', zero_mul] at hd_mul
    have hcard_pos : 0 < Nat.card H := Nat.card_pos_iff.mpr ⟨⟨1⟩, inferInstance⟩
    omega
  set g0 := g ^ d with hg0_def
  have hg0_order : orderOf g0 = p := by
    rw [hg0_def, orderOf_pow, hg_order]
    have h_gcd : Nat.gcd (Nat.card H) d = d := Nat.gcd_eq_right hd_dvd
    rw [h_gcd]
    exact Nat.div_eq_of_eq_mul_right hd_pos hd_mul.symm
  let H0 : Subgroup H := Subgroup.zpowers g0
  have hH0_card : Nat.card H0 = p := by
    rw [Nat.card_zpowers, hg0_order]
  have h_eq_H0 (L : Subgroup H) (hL : Nat.card L = p) : L = H0 := by
    have hL_ne_bot : L ≠ ⊥ := by
      intro hbot
      have hcard1 : Nat.card L = 1 := by
        simp [hbot]
      rw [hL] at hcard1; exact hp_prime.ne_one hcard1
    haveI : Nontrivial L := (Subgroup.nontrivial_iff_ne_bot L).mpr hL_ne_bot
    obtain ⟨h, hh⟩ := IsCyclic.exists_monoid_generator (α := L)
    have hh_order_L : orderOf (h : L) = p := by
      have h_eq : orderOf (h : L) = Nat.card L :=
        orderOf_eq_card_of_forall_mem_zpowers (by
          intro x; have hx := hh x
          rcases ((Submonoid.mem_powers_iff _ _).mp hx) with ⟨n, hn⟩
          rw [← hn]; exact ⟨(n : ℤ), by simp⟩)
      rw [hL] at h_eq; exact h_eq
    have hh_order_H : orderOf (h : H) = p := by
      rw [Subgroup.orderOf_coe (h : L), hh_order_L]
    have hh_mem : (h : H) ∈ Submonoid.powers g := hg (h : H)
    rcases ((Submonoid.mem_powers_iff _ _).mp hh_mem) with ⟨k, hk⟩
    rw [← hk] at hh_order_H; rw [orderOf_pow, hg_order] at hh_order_H
    set gk := Nat.gcd (Nat.card H) k with hgk_def
    have hgk_dvd_N : gk ∣ Nat.card H := Nat.gcd_dvd_left _ _
    have hN_eq_gk_mul_p : Nat.card H = gk * p := by
      calc
        Nat.card H = gk * (Nat.card H / gk) := (Nat.mul_div_cancel' hgk_dvd_N).symm
        _ = gk * p := by rw [hh_order_H]
    have hgk_eq_d : gk = d := by
      have h_eq : gk * p = d * p := by rw [← hN_eq_gk_mul_p, hd_mul]
      apply Nat.eq_of_mul_eq_mul_right hp_pos
      simpa [mul_comm, mul_left_comm, mul_assoc] using h_eq
    have hd_dvd_k : d ∣ k := by rw [← hgk_eq_d]; exact Nat.gcd_dvd_right _ _
    rcases hd_dvd_k with ⟨m, hm⟩
    have h_mem_H0 : (h : H) ∈ H0 := by
      rw [← hk, hm, pow_mul, ← hg0_def]
      exact Subgroup.mem_zpowers_iff.mpr ⟨(m : ℤ), by simp⟩
    have hL_le_H0 : L ≤ H0 := by
      intro x hx
      have hx_mem : (⟨x, hx⟩ : L) ∈ Submonoid.powers (h : L) := hh ⟨x, hx⟩
      rcases ((Submonoid.mem_powers_iff _ _).mp hx_mem) with ⟨n, hn⟩
      have hx_eq : x = (h : H) ^ n := by simpa using congrArg Subtype.val hn.symm
      rw [hx_eq]; exact Subgroup.pow_mem H0 h_mem_H0 n
    apply Subgroup.eq_of_le_of_card_ge hL_le_H0
    rw [hH0_card, hL]
  exact (h_eq_H0 A hA).trans (h_eq_H0 B hB).symm

omit [IsMinCE G] in
private theorem CFSG.section15_exists_cyclic_full_exponent_subgroup_of_abelian_pgroup
    {P : Subgroup G} {p : Nat.Primes}
    (hPcomm : IsMulCommutative P)
    (hPp : IsPGroup p.val P)
    (hPne : P ≠ ⊥) :
    ∃ Z : Subgroup G, Z ≤ P ∧ IsCyclic Z ∧ IsPGroup p.val Z ∧
      Monoid.exponent Z = Monoid.exponent P ∧ Z ≠ ⊥ := by
  classical
  letI : IsMulCommutative P := hPcomm
  letI : CommGroup P := IsMulCommutative.instCommGroup
  obtain ⟨t, htord⟩ :=
    Monoid.exists_orderOf_eq_exponent (G := P)
      (Monoid.ExponentExists.of_finite (G := P))
  let tG : G := t
  let Z : Subgroup G := Subgroup.zpowers tG
  have htG_mem : tG ∈ P := t.property
  have hZleP : Z ≤ P := Subgroup.zpowers_le.2 htG_mem
  have hZcyc : IsCyclic Z := by
    dsimp [Z]
    infer_instance
  have hZp : IsPGroup p.val Z := by
    have hZsub_p : IsPGroup p.val (Z.subgroupOf P) :=
      hPp.to_subgroup (Z.subgroupOf P)
    exact hZsub_p.of_equiv (Subgroup.subgroupOfEquivOfLe hZleP)
  have htG_order : orderOf tG = Monoid.exponent P := by
    simpa [tG, Subgroup.orderOf_coe] using htord
  have hZexp : Monoid.exponent Z = Monoid.exponent P := by
    calc
      Monoid.exponent Z = Nat.card Z := hZcyc.exponent_eq_card
      _ = orderOf tG := Nat.card_zpowers tG
      _ = Monoid.exponent P := htG_order
  have htG_ne : tG ≠ 1 := by
    intro htG_one
    have ht_one : t = 1 := Subtype.ext htG_one
    have hExp_one : Monoid.exponent P = 1 := by
      simpa [ht_one] using htord.symm
    have hsub : Subsingleton P := Monoid.exp_eq_one_iff.mp hExp_one
    exact hPne (le_bot_iff.mp (by
      intro x hx
      have hx_one : (⟨x, hx⟩ : P) = 1 := Subsingleton.elim _ _
      simpa using congrArg Subtype.val hx_one))
  have hZne : Z ≠ ⊥ := by
    simpa [Z] using (Subgroup.zpowers_ne_bot.mpr htG_ne)
  exact ⟨Z, hZleP, hZcyc, hZp, hZexp, hZne⟩

omit [IsMinCE G] in
public theorem CFSG.section15_exists_primeOrder_zpowers_of_prime_dvd_card
    {B : Subgroup G} {q : Nat.Primes} (hqB : q.val ∣ Nat.card B) :
    ∃ z : G, z ∈ B ∧ z ≠ 1 ∧
      Subgroup.zpowers z ∈ section10PrimeOrderSubgroupsIn q B := by
  classical
  haveI : Fact q.val.Prime := ⟨q.property⟩
  obtain ⟨z₀, hz₀_order⟩ := exists_prime_orderOf_dvd_card' (G := B) q.val hqB
  let z : G := z₀
  have hzB : z ∈ B := z₀.property
  have hz_order : orderOf z = q.val := by
    simpa [z, Subgroup.orderOf_coe] using hz₀_order
  have hz_ne : z ≠ 1 := by
    intro hz1
    have hq_one : q.val = 1 := by
      rw [← hz_order, hz1, orderOf_one]
    exact q.property.ne_one hq_one
  have hX_card : Nat.card (Subgroup.zpowers z) = q.val := by
    rw [Nat.card_zpowers]
    exact hz_order
  exact ⟨z, hzB, hz_ne,
    by
      simpa [section10PrimeOrderSubgroupsIn] using
        (⟨Subgroup.zpowers_le.2 hzB, hX_card⟩ :
          Subgroup.zpowers z ≤ B ∧ Nat.card (Subgroup.zpowers z) = q.val)⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_mem_omegaOneSubgroup_of_mem_pow_eq_one
    {H : Subgroup G} {p : Nat.Primes} {x : G}
    (hxH : x ∈ H) (hxp : x ^ p.val = 1) :
    x ∈ section12OmegaOneSubgroup p H := by
  let xH : H := ⟨x, hxH⟩
  have hxΩ : xH ∈ omega₁ (G := H) (p := p.val) := by
    rw [omega₁, omega]
    exact Subgroup.subset_closure (by simpa [xH] using hxp)
  exact Subgroup.mem_map.mpr ⟨xH, hxΩ, rfl⟩

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_primeOrder_le_omegaOneSubgroup_of_le
    {H X : Subgroup G} {p : Nat.Primes}
    (hX : X ∈ section10PrimeOrderSubgroupsIn p H) :
    X ≤ section12OmegaOneSubgroup p H := by
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hX) with ⟨hXH, hXcard⟩
  intro x hxX
  have hxpowX : (⟨x, hxX⟩ : X) ^ Nat.card X = 1 := pow_card_eq_one'
  have hxpow : x ^ p.val = 1 := by
    simpa [hXcard] using congrArg Subtype.val hxpowX
  exact section15_mem_omegaOneSubgroup_of_mem_pow_eq_one (p := p) (hXH hxX) hxpow

omit [IsMinCE G] in
public theorem CFSG.section15_natCard_omegaOne_cyclic_pGroup_eq_prime
    {H : Type*} [Group H] [Finite H] {p : Nat.Primes}
    [Fact (IsPGroup p.val H)] (hcyc : IsCyclic H) [Nontrivial H] :
    Nat.card (omega₁ (G := H) (p := p.val)) = p.val := by
  classical
  haveI : Fact p.val.Prime := ⟨p.2⟩
  letI : IsCyclic H := hcyc
  letI : CommGroup H := hcyc.commGroup
  have hOmega_eq_ker : omega₁ (G := H) (p := p.val) =
      (powMonoidHom p.val : H →* H).ker := by
    apply le_antisymm
    · rw [omega₁, omega]
      refine (Subgroup.closure_le (K := (powMonoidHom p.val : H →* H).ker)).2 ?_
      intro x hx
      change x ^ (p.val ^ 1) = 1 at hx
      simpa [powMonoidHom_apply, pow_one, MonoidHom.mem_ker] using hx
    · intro x hx
      change x ∈ Subgroup.closure {y : H | y ^ (p.val ^ 1) = 1}
      refine Subgroup.subset_closure ?_
      simpa [powMonoidHom_apply, pow_one, MonoidHom.mem_ker] using hx
  obtain ⟨n, hn_pos, hcardH⟩ :=
    (IsPGroup.nontrivial_iff_card (p := p.val) (G := H) (hG := Fact.out)).mp
      inferInstance
  calc
    Nat.card (omega₁ (G := H) (p := p.val))
        = Nat.card ((powMonoidHom p.val : H →* H).ker) := by rw [hOmega_eq_ker]
    _ = (Nat.card H).gcd p.val := IsCyclic.card_powMonoidHom_ker (G := H) p.val
    _ = p.val := by
      rw [hcardH]
      exact Nat.gcd_eq_right_iff_dvd.mpr
        (dvd_pow_self p.val (Nat.pos_iff_ne_zero.mp hn_pos))

omit [IsMinCE G] in
public theorem CFSG.section15_omegaOneSubgroup_card_eq_prime_of_cyclic_pSubgroup
    {H : Subgroup G} {p : Nat.Primes}
    (hHp : IsPGroup p.val H) (hHcyc : IsCyclic H) (hHne : H ≠ ⊥) :
    Nat.card (section12OmegaOneSubgroup p H) = p.val := by
  classical
  haveI : Fact (IsPGroup p.val H) := ⟨hHp⟩
  haveI : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).2 hHne
  have hcard :
      Nat.card (section12OmegaOneSubgroup p H) =
        Nat.card (omega₁ (G := H) (p := p.val)) := by
    simpa [section12OmegaOneSubgroup] using
      (Subgroup.card_map_of_injective
        (K := omega₁ (G := H) (p := p.val)) (f := H.subtype) H.subtype_injective)
  exact hcard.trans
    (section15_natCard_omegaOne_cyclic_pGroup_eq_prime (H := H) (p := p) hHcyc)

private theorem CFSG.section15_normalizer_ne_top_of_ne_bot_ne_top
    {Q : Subgroup G} (hQ_ne_bot : Q ≠ ⊥) (hQ_ne_top : Q ≠ ⊤) :
    Subgroup.normalizer (Q : Set G) ≠ ⊤ := by
  intro hNtop
  have hQnormal : Q.Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
  letI : IsSimpleGroup G := IsMinCE.simple
  rcases hQnormal.eq_bot_or_eq_top with hQbot | hQtop
  · exact hQ_ne_bot hQbot
  · exact hQ_ne_top hQtop

private theorem CFSG.section15_primeOrder_ne_top
    {A X : Subgroup G} {p : Nat.Primes}
    (hX : X ∈ section10PrimeOrderSubgroupsIn p A) :
    X ≠ ⊤ := by
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hX) with ⟨_hXA, hXcard⟩
  intro htop
  have hGcard : Nat.card G = p.val := by
    simpa [htop] using hXcard
  haveI : Fact p.val.Prime := ⟨p.2⟩
  haveI : IsCyclic G := by
    exact isCyclic_of_prime_card (α := G) (p := p.val) hGcard
  have hsolv : Group.IsSolvable G := by infer_instance
  exact IsMinCE.not_solvable (G := G) hsolv

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_powMonoidHom_range_characteristic
    {H : Type*} [CommGroup H] (d : Nat) :
    ((powMonoidHom d : H →* H).range).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro e
  ext x
  constructor
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    rcases MonoidHom.mem_range.mp hy with ⟨z, rfl⟩
    exact MonoidHom.mem_range.mpr ⟨e z, by simp [powMonoidHom_apply]⟩
  · intro hx
    rcases MonoidHom.mem_range.mp hx with ⟨y, rfl⟩
    refine Subgroup.mem_map.mpr ⟨(e.symm y) ^ d, ?_, ?_⟩
    · exact MonoidHom.mem_range.mpr ⟨e.symm y, rfl⟩
    · simp [powMonoidHom_apply]

omit [IsMinCE G] in
private theorem CFSG.section15_primeOrderSubgroupIn_of_ne_bot_ne_self_of_rankTwo
    {A X : Subgroup G} {p : Nat.Primes}
    (hAcard : Nat.card A = p.val ^ 2)
    (hXA : X ≤ A) (hXne : X ≠ ⊥) (hXproper : X ≠ A) :
    X ∈ section10PrimeOrderSubgroupsIn p A := by
  have hXdvd : Nat.card X ∣ p.val ^ 2 := by
    exact (Subgroup.card_dvd_of_le hXA).trans (dvd_rfl.trans (by rw [hAcard]))
  rcases (Nat.dvd_prime_pow p.2).1 hXdvd with ⟨k, hk_le, hk_card⟩
  have hk_ne_zero : k ≠ 0 := by
    intro hk0
    apply hXne
    apply (Subgroup.card_eq_one (H := X)).mp
    simp [hk_card, hk0]
  have hk_ne_two : k ≠ 2 := by
    intro hk2
    have hXsub_card : Nat.card (X.subgroupOf A) = Nat.card A := by
      rw [section12_card_subgroupOf_eq hXA, hAcard, hk_card, hk2]
    have hXsub_top : X.subgroupOf A = ⊤ :=
      Subgroup.eq_top_of_card_eq (H := X.subgroupOf A) hXsub_card
    have hXeqA : X = A := by
      apply le_antisymm hXA
      intro a ha
      have haSub : (⟨a, ha⟩ : A) ∈ X.subgroupOf A := by
        simp [hXsub_top]
      simpa [Subgroup.mem_subgroupOf] using haSub
    exact hXproper hXeqA
  have hk_eq_one : k = 1 := by
    omega
  exact ⟨hXA, by simp [hk_card, hk_eq_one]⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_zpowers_mem_primeOrderSubgroupsIn_of_pow_eq_one
    {B : Subgroup G} {p : Nat.Primes} {x : G}
    (hxB : x ∈ B) (hxpow : x ^ p.val = 1) (hxne : x ≠ 1) :
    Subgroup.zpowers x ∈ section10PrimeOrderSubgroupsIn p B := by
  haveI : Fact p.val.Prime := ⟨p.2⟩
  have hcard : Nat.card (Subgroup.zpowers x) = p.val := by
    rw [Nat.card_zpowers, orderOf_eq_prime hxpow hxne]
  exact ⟨Subgroup.zpowers_le.2 hxB, hcard⟩

omit [IsMinCE G] in
public theorem CFSG.section15_eq_of_le_primeOrderSubgroupsIn
    {A X Y : Subgroup G} {p : Nat.Primes}
    (hX : X ∈ section10PrimeOrderSubgroupsIn p A)
    (hY : Y ∈ section10PrimeOrderSubgroupsIn p A)
    (hXY : X ≤ Y) :
    X = Y := by
  have hXsub_card : Nat.card (X.subgroupOf Y) = Nat.card Y := by
    rcases (by simpa [section10PrimeOrderSubgroupsIn] using hX) with ⟨_hXA, hXcard⟩
    rcases (by simpa [section10PrimeOrderSubgroupsIn] using hY) with ⟨_hYA, hYcard⟩
    rw [section12_card_subgroupOf_eq hXY, hXcard, hYcard]
  have hXsub_top : X.subgroupOf Y = ⊤ :=
    Subgroup.eq_top_of_card_eq (H := X.subgroupOf Y) hXsub_card
  apply le_antisymm hXY
  intro y hy
  have hySub : (⟨y, hy⟩ : Y) ∈ X.subgroupOf Y := by
    simp [hXsub_top]
  simpa [Subgroup.mem_subgroupOf] using hySub

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_omegaOneSubgroup_le
    {H : Subgroup G} {p : Nat.Primes} :
    section12OmegaOneSubgroup p H ≤ H := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
  exact y.property

omit [IsMinCE G] in
public theorem CFSG.section15_omegaOneSubgroup_le_of_nontrivial_subgroup_of_cyclic_pSubgroup
    {H K : Subgroup G} {p : Nat.Primes}
    (hHp : IsPGroup p.val H) (hHcyc : IsCyclic H) (hHne : H ≠ ⊥)
    (hKH : K ≤ H) (hKne : K ≠ ⊥) :
    section12OmegaOneSubgroup p H ≤ K := by
  have hKsubp : IsPGroup p.val (K.subgroupOf H) := hHp.to_subgroup (K.subgroupOf H)
  have hKp : IsPGroup p.val K :=
    hKsubp.of_equiv (Subgroup.subgroupOfEquivOfLe (H := K) (K := H) hKH)
  letI : IsCyclic H := hHcyc
  have hKsubcyc : IsCyclic (K.subgroupOf H) := by infer_instance
  have hKcyc : IsCyclic K :=
    (Subgroup.subgroupOfEquivOfLe (H := K) (K := H) hKH).isCyclic.mp hKsubcyc
  have hOmegaH_card :
      Nat.card (section12OmegaOneSubgroup p H) = p.val :=
    section15_omegaOneSubgroup_card_eq_prime_of_cyclic_pSubgroup
      (G := G) (H := H) (p := p) hHp hHcyc hHne
  have hOmegaK_card :
      Nat.card (section12OmegaOneSubgroup p K) = p.val :=
    section15_omegaOneSubgroup_card_eq_prime_of_cyclic_pSubgroup
      (G := G) (H := K) (p := p) hKp hKcyc hKne
  have hOmegaK_primeH :
      section12OmegaOneSubgroup p K ∈ section10PrimeOrderSubgroupsIn p H := by
    exact ⟨(show section12OmegaOneSubgroup p K ≤ K from section15_omegaOneSubgroup_le).trans hKH,
      hOmegaK_card⟩
  have hOmegaH_primeH :
      section12OmegaOneSubgroup p H ∈ section10PrimeOrderSubgroupsIn p H :=
    ⟨section15_omegaOneSubgroup_le, hOmegaH_card⟩
  have hOmegaK_le_OmegaH :
      section12OmegaOneSubgroup p K ≤ section12OmegaOneSubgroup p H :=
    section15_primeOrder_le_omegaOneSubgroup_of_le
      (G := G) (H := H) (X := section12OmegaOneSubgroup p K) hOmegaK_primeH
  have hOmegaK_eq_OmegaH :
      section12OmegaOneSubgroup p K = section12OmegaOneSubgroup p H := by
    exact
      Subgroup.eq_of_le_of_card_ge hOmegaK_le_OmegaH (by
        rw [hOmegaK_card, hOmegaH_card])
  intro x hx
  rw [← hOmegaK_eq_OmegaH] at hx
  exact section15_omegaOneSubgroup_le hx

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_isMulCommutative_ambientSylowSubgroup
    {M : Subgroup G} {p : Nat.Primes} (P : Sylow p.val M)
    (hPcomm : IsMulCommutative (P : Subgroup M)) :
    IsMulCommutative (section10AmbientSylowSubgroup M P) := by
  letI : IsMulCommutative (P : Subgroup M) := hPcomm
  change IsMulCommutative ((P : Subgroup M).map M.subtype)
  exact Subgroup.map_isMulCommutative (f := M.subtype) (H := (P : Subgroup M))

private theorem CFSG.section15_exists_tau2_cyclic_factor_of_abelian_m_sylow
    {M E E₁₂ E₁ E₂ E₃ A Ssub : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hA_M : A ∈ section12RankTwoElementaryAbelianIn p M)
    (hScomm : IsMulCommutative Ssub)
    (hSp : IsPGroup p.val Ssub)
    (hOmegaS : section12OmegaOneSubgroup p Ssub = A)
    (hNormS_not : ¬ Subgroup.normalizer (Ssub : Set G) ≤ M) :
    ∃ Z : Subgroup G, Z ≤ Ssub ∧ IsCyclic Z ∧ IsPGroup p.val Z ∧
      Z ≠ ⊥ ∧ Monoid.exponent Z = Monoid.exponent Ssub ∧
      subgroupCentralizerIn (section10Msigma M) (section12OmegaOneSubgroup p Z) = ⊥ := by
  classical
  have hAne : A ≠ ⊥ := section12_rankTwo_ne_bot hA
  have hSne : Ssub ≠ ⊥ := by
    intro hSbot
    have hOmegaBot : section12OmegaOneSubgroup p Ssub = ⊥ := by
      rw [hSbot]
      apply le_antisymm
      · intro x hx
        exact section15_omegaOneSubgroup_le hx
      · exact bot_le
    have hAbot : A = ⊥ := hOmegaS.symm.trans hOmegaBot
    exact hAne hAbot
  haveI : Nontrivial Ssub := (Subgroup.nontrivial_iff_ne_bot (H := Ssub)).2 hSne
  haveI : Fact p.val.Prime := ⟨p.2⟩
  letI : CommGroup Ssub := IsMulCommutative.instCommGroup
  rcases (IsPGroup.nontrivial_iff_card (p := p.val) (G := Ssub) (hG := hSp)).mp inferInstance with
    ⟨n, hn_pos, hcardS⟩
  have hexp_dvd_card : Monoid.exponent Ssub ∣ p.val ^ n := by
    simpa [hcardS] using (Group.exponent_dvd_nat_card (G := Ssub))
  rcases (Nat.dvd_prime_pow p.2).1 hexp_dvd_card with ⟨k, hk_le, hExpS⟩
  have hExpS_ne_one : Monoid.exponent Ssub ≠ 1 := by
    intro hExp1
    have hsub : Subsingleton Ssub := (Monoid.exp_eq_one_iff).1 hExp1
    letI : Subsingleton Ssub := hsub
    have hcard1 : Nat.card Ssub = 1 := by simp
    exact hSne ((Subgroup.eq_bot_iff_card (H := Ssub)).2 hcard1)
  have hk_pos : 0 < k := by
    cases k with
    | zero =>
        exfalso
        exact hExpS_ne_one (by simp [hExpS])
    | succ k =>
        exact Nat.succ_pos _
  let d : Nat := p.val ^ (k - 1)
  let Isub : Subgroup Ssub := (powMonoidHom d : Ssub →* Ssub).range
  let I : Subgroup G := Isub.map Ssub.subtype
  have hI_le_A : I ≤ A := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hyI, rfl⟩
    rcases MonoidHom.mem_range.mp hyI with ⟨z, rfl⟩
    have hzpow : ((z : Ssub) ^ d : G) ^ p.val = 1 := by
      have hpow : (z : Ssub) ^ (d * p.val) = 1 := by
        have hExp_dvd : Monoid.exponent Ssub ∣ d * p.val := by
          change Monoid.exponent Ssub ∣ p.val ^ (k - 1) * p.val
          refine ⟨1, ?_⟩
          rw [hExpS]
          cases k with
          | zero =>
              cases (Nat.not_lt_zero _ hk_pos)
          | succ k =>
              simp [pow_succ', Nat.mul_comm]
        exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hExp_dvd z
      simpa [d, pow_mul] using congrArg Subtype.val hpow
    have hxOmega : ((z : Ssub) ^ d : G) ∈ section12OmegaOneSubgroup p Ssub :=
      section15_mem_omegaOneSubgroup_of_mem_pow_eq_one
        (G := G) (H := Ssub) (p := p) (x := ((z : Ssub) ^ d : G))
        (by exact ((z : Ssub) ^ d).property) hzpow
    simpa [I, Isub, powMonoidHom_apply, hOmegaS] using hxOmega
  obtain ⟨t, htord⟩ :=
    Monoid.exists_orderOf_eq_exponent (G := Ssub) Monoid.ExponentExists.of_finite
  have htpow_ne : (t : Ssub) ^ d ≠ 1 := by
    have hd_lt : d < orderOf t := by
      change p.val ^ (k - 1) < orderOf t
      rw [htord, hExpS]
      cases k with
      | zero =>
          cases (Nat.not_lt_zero _ hk_pos)
      | succ k =>
          simpa using Nat.pow_lt_pow_right p.2.one_lt (Nat.pred_lt (Nat.succ_ne_zero k))
    exact pow_ne_one_of_lt_orderOf (pow_ne_zero (k - 1) p.2.ne_zero) hd_lt
  have hIne : I ≠ ⊥ := by
    intro hIbot
    have htbot : Ssub.subtype ((t : Ssub) ^ d) ∈ (⊥ : Subgroup G) := by
      have htI : Ssub.subtype ((t : Ssub) ^ d) ∈ I := by
        refine Subgroup.mem_map.mpr ?_
        refine ⟨(powMonoidHom d) t, ?_, rfl⟩
        exact MonoidHom.mem_range.mpr ⟨t, rfl⟩
      simpa [hIbot] using htI
    exact htpow_ne (by
      apply Subtype.ext
      simpa using htbot)
  have htdpow : (((t : Ssub) ^ d : Ssub) : G) ^ p.val = 1 := by
    have hpow : (t : Ssub) ^ (d * p.val) = 1 := by
      have hExp_dvd : Monoid.exponent Ssub ∣ d * p.val := by
        change Monoid.exponent Ssub ∣ p.val ^ (k - 1) * p.val
        refine ⟨1, ?_⟩
        rw [hExpS]
        cases k with
        | zero =>
            cases (Nat.not_lt_zero _ hk_pos)
        | succ k =>
            simp [pow_succ', Nat.mul_comm]
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hExp_dvd t
    simpa [d, pow_mul] using congrArg Subtype.val hpow
  have htI : (((t : Ssub) ^ d : Ssub) : G) ∈ I := by
    refine Subgroup.mem_map.mpr ?_
    refine ⟨(powMonoidHom d) t, ?_, rfl⟩
    exact MonoidHom.mem_range.mpr ⟨t, rfl⟩
  rcases section15_rankTwo_elementary hA with ⟨hAcard, _hAelem⟩
  by_cases hIA : I = A
  · obtain ⟨A₁, hA₁prime, hCA₁⟩ :=
      theorem_12_5_f (G := G) (M := M) (A := A) (p := p) hM hp hA_M
    rcases hA₁prime with ⟨hA₁A, hA₁card⟩
    have hA₁prime' : A₁ ∈ section10PrimeOrderSubgroupsIn p A := ⟨hA₁A, hA₁card⟩
    have hA₁ne : A₁ ≠ ⊥ := section12_primeOrder_ne_bot (G := G) hA₁prime'
    rcases Subgroup.ne_bot_iff_exists_ne_one.mp hA₁ne with ⟨aA₁, haA₁ne⟩
    let a : G := aA₁
    have haA₁ : a ∈ A₁ := aA₁.property
    have hane : a ≠ 1 := by
      intro ha1
      exact haA₁ne (Subtype.ext ha1)
    have haI : a ∈ I := by
      simpa [hIA] using hA₁A haA₁
    rcases Subgroup.mem_map.mp haI with ⟨y, hyIsub, hya⟩
    rcases MonoidHom.mem_range.mp hyIsub with ⟨u, hu_pow⟩
    have huda : (((u : Ssub) ^ d : Ssub) : G) = a := by
      calc
        (((u : Ssub) ^ d : Ssub) : G) = (y : G) := by
          simpa [powMonoidHom_apply] using congrArg Subtype.val hu_pow
        _ = a := hya
    let Z : Subgroup G := Subgroup.zpowers (u : G)
    have hZleS : Z ≤ Ssub := Subgroup.zpowers_le.2 u.property
    have hZcyc : IsCyclic Z := by
      dsimp [Z]
      infer_instance
    have huord_dvd : orderOf u ∣ Monoid.exponent Ssub := by
      exact (Monoid.exponent_dvd.mp (dvd_rfl : Monoid.exponent Ssub ∣ Monoid.exponent Ssub)) u
    rcases (Nat.dvd_prime_pow p.2).1 (hExpS ▸ huord_dvd) with ⟨m, hm_le, huord⟩
    have hk_le_m : k ≤ m := by
      by_contra hkm
      have hm_lt_k : m < k := Nat.lt_of_not_ge hkm
      have hudvd : orderOf u ∣ d := by
        rw [huord]
        change p.val ^ m ∣ p.val ^ (k - 1)
        exact Nat.pow_dvd_pow p.val (Nat.le_pred_of_lt hm_lt_k)
      have hu_pow_d_one : (u : Ssub) ^ d = 1 :=
        (orderOf_dvd_iff_pow_eq_one).mp hudvd
      have haone : a = 1 := by
        calc
          a = (((u : Ssub) ^ d : Ssub) : G) := huda.symm
          _ = 1 := by simpa using congrArg Subtype.val hu_pow_d_one
      exact hane haone
    have hm_eq_k : m = k := le_antisymm hm_le hk_le_m
    have huord_eq_exp : orderOf u = Monoid.exponent Ssub := by
      simp [hExpS, huord, hm_eq_k]
    have hZexp : Monoid.exponent Z = Monoid.exponent Ssub := by
      calc
        Monoid.exponent Z = Nat.card Z := hZcyc.exponent_eq_card
        _ = orderOf (u : G) := by
          dsimp [Z]
          rw [Nat.card_zpowers]
        _ = orderOf u := by simp
        _ = Monoid.exponent Ssub := huord_eq_exp
    have hu_ne : (u : G) ≠ 1 := by
      intro hu1
      apply hExpS_ne_one
      rw [← huord_eq_exp, ← Subgroup.orderOf_coe, hu1, orderOf_one]
    have hZne : Z ≠ ⊥ := by
      intro hZbot
      have hu_bot : (u : G) ∈ (⊥ : Subgroup G) := by
        simpa [hZbot, Z] using (Subgroup.mem_zpowers (u : G))
      exact hu_ne (by simpa using hu_bot)
    have hZp : IsPGroup p.val Z := by
      have hZsub_p : IsPGroup p.val (Z.subgroupOf Ssub) := hSp.to_subgroup (Z.subgroupOf Ssub)
      exact hZsub_p.of_equiv (Subgroup.subgroupOfEquivOfLe hZleS)
    have hOmegaZ_card : Nat.card (section12OmegaOneSubgroup p Z) = p.val :=
      section15_omegaOneSubgroup_card_eq_prime_of_cyclic_pSubgroup
        (G := G) (H := Z) (p := p) hZp hZcyc hZne
    have haZ : a ∈ Z := by
      rw [← huda]
      dsimp [Z]
      exact Subgroup.mem_zpowers_iff.mpr ⟨d, by simp⟩
    have hapow : a ^ p.val = 1 := by
      have haPowA₁ : (⟨a, haA₁⟩ : A₁) ^ Nat.card A₁ = 1 := pow_card_eq_one'
      simpa [hA₁card] using congrArg Subtype.val haPowA₁
    have haOmegaZ : a ∈ section12OmegaOneSubgroup p Z :=
      section15_mem_omegaOneSubgroup_of_mem_pow_eq_one
        (G := G) (H := Z) (p := p) (x := a) haZ hapow
    have hzaPrime : Subgroup.zpowers a ∈ section10PrimeOrderSubgroupsIn p A₁ :=
      section15_zpowers_mem_primeOrderSubgroupsIn_of_pow_eq_one
        (G := G) (B := A₁) (p := p) haA₁ hapow hane
    have hA₁self : A₁ ∈ section10PrimeOrderSubgroupsIn p A₁ := ⟨le_rfl, hA₁card⟩
    have hza_eq_A₁ : Subgroup.zpowers a = A₁ :=
      section15_eq_of_le_primeOrderSubgroupsIn
        (G := G) (A := A₁) (X := Subgroup.zpowers a) (Y := A₁) (p := p)
        hzaPrime hA₁self (Subgroup.zpowers_le.2 haA₁)
    have hA₁_le_OmegaZ : A₁ ≤ section12OmegaOneSubgroup p Z := by
      rw [← hza_eq_A₁]
      exact Subgroup.zpowers_le.2 haOmegaZ
    have hOmegaZ_le_S : section12OmegaOneSubgroup p Z ≤ Ssub :=
      (section15_omegaOneSubgroup_le (G := G) (H := Z) (p := p)).trans hZleS
    have hOmegaZ_primeS : section12OmegaOneSubgroup p Z ∈ section10PrimeOrderSubgroupsIn p Ssub :=
      ⟨hOmegaZ_le_S, hOmegaZ_card⟩
    have hOmegaZ_le_A : section12OmegaOneSubgroup p Z ≤ A := by
      have hOmegaZ_le_OmegaS :
          section12OmegaOneSubgroup p Z ≤ section12OmegaOneSubgroup p Ssub :=
        section15_primeOrder_le_omegaOneSubgroup_of_le
          (G := G) (H := Ssub) (X := section12OmegaOneSubgroup p Z) hOmegaZ_primeS
      intro x hx
      have hxOmegaS : x ∈ section12OmegaOneSubgroup p Ssub := hOmegaZ_le_OmegaS hx
      rwa [hOmegaS] at hxOmegaS
    have hOmegaZ_primeA : section12OmegaOneSubgroup p Z ∈ section10PrimeOrderSubgroupsIn p A :=
      ⟨hOmegaZ_le_A, hOmegaZ_card⟩
    have hOmegaZ_eq_A₁ : section12OmegaOneSubgroup p Z = A₁ := by
      symm
      exact
        section15_eq_of_le_primeOrderSubgroupsIn
          (G := G) (A := A) (X := A₁) (Y := section12OmegaOneSubgroup p Z) (p := p)
          hA₁prime' hOmegaZ_primeA hA₁_le_OmegaZ
    refine ⟨Z, hZleS, hZcyc, hZp, hZne, hZexp, ?_⟩
    simpa [hOmegaZ_eq_A₁] using hCA₁
  · have hIprime : I ∈ section10PrimeOrderSubgroupsIn p A :=
      section15_primeOrderSubgroupIn_of_ne_bot_ne_self_of_rankTwo
        (G := G) (A := A) (X := I) (p := p) hAcard hI_le_A hIne hIA
    have hCI : subgroupCentralizerIn (section10Msigma M) I = ⊥ := by
      by_contra hCIne
      have huniq :
          section9MaximalSubgroupsContaining (Subgroup.centralizer (I : Set G)) = {M} :=
        corollary_12_6_c (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
          (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
          hM hE hp hA I hIprime hCIne
      have hNormS_le_NI :
          Subgroup.normalizer (Ssub : Set G) ≤ Subgroup.normalizer (I : Set G) := by
        haveI : Isub.Characteristic :=
          section15_powMonoidHom_range_characteristic (H := Ssub) d
        simpa [I] using
          (section8_normalizer_map_subtype_le_of_characteristic
            (H := Ssub) (K := Isub))
      have hNI_ne_top : Subgroup.normalizer (I : Set G) ≠ ⊤ :=
        section15_normalizer_ne_top_of_ne_bot_ne_top
          (G := G) (Q := I) hIne (section15_primeOrder_ne_top (G := G) hIprime)
      rcases eq_top_or_exists_le_coatom (Subgroup.normalizer (I : Set G)) with
        htop | ⟨N, hNcoatom, hNle⟩
      · exact hNI_ne_top htop
      have hNmax : N ∈ section9MaximalSubgroups G := hNcoatom
      have hNcont :
          N ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer (I : Set G)) := by
        refine ⟨hNmax, ?_⟩
        exact (centralizer_le_normalizer I).trans hNle
      have hN_eq_M : N = M := by
        have hsingle : N ∈ ({M} : Set (Subgroup G)) := by
          simpa [huniq] using hNcont
        simpa using hsingle
      have hNI_le_M : Subgroup.normalizer (I : Set G) ≤ M := by
        simpa [hN_eq_M] using hNle
      exact hNormS_not (hNormS_le_NI.trans hNI_le_M)
    let Z : Subgroup G := Subgroup.zpowers (t : G)
    let T : Subgroup G := Subgroup.zpowers (((t : Ssub) ^ d : Ssub) : G)
    have hZleS : Z ≤ Ssub := Subgroup.zpowers_le.2 t.property
    have hZcyc : IsCyclic Z := by
      dsimp [Z]
      infer_instance
    have hZexp : Monoid.exponent Z = Monoid.exponent Ssub := by
      calc
        Monoid.exponent Z = Nat.card Z := hZcyc.exponent_eq_card
        _ = orderOf (t : G) := by
          dsimp [Z]
          rw [Nat.card_zpowers]
        _ = orderOf t := by simp
        _ = Monoid.exponent Ssub := htord
    have hZne : Z ≠ ⊥ := by
      have htne : (t : G) ≠ 1 := by
        intro ht1
        apply hExpS_ne_one
        rw [← htord, ← Subgroup.orderOf_coe, ht1, orderOf_one]
      intro hZbot
      have htbot : (t : G) ∈ (⊥ : Subgroup G) := by
        simpa [hZbot, Z] using (Subgroup.mem_zpowers (t : G))
      exact htne (by simpa using htbot)
    have hZp : IsPGroup p.val Z := by
      have hZsub_p : IsPGroup p.val (Z.subgroupOf Ssub) := hSp.to_subgroup (Z.subgroupOf Ssub)
      exact hZsub_p.of_equiv (Subgroup.subgroupOfEquivOfLe hZleS)
    have hOmegaZ_card : Nat.card (section12OmegaOneSubgroup p Z) = p.val :=
      section15_omegaOneSubgroup_card_eq_prime_of_cyclic_pSubgroup
        (G := G) (H := Z) (p := p) hZp hZcyc hZne
    have hTprimeI : T ∈ section10PrimeOrderSubgroupsIn p I := by
      have htpow_neG : (((t : Ssub) ^ d : Ssub) : G) ≠ 1 := by
        intro h1
        exact htpow_ne (Subtype.ext h1)
      exact section15_zpowers_mem_primeOrderSubgroupsIn_of_pow_eq_one
        (G := G) (B := I) (p := p) htI htdpow htpow_neG
    have hTZleZ : T ≤ Z := by
      intro x hx
      rcases Subgroup.mem_zpowers_iff.mp hx with ⟨m, rfl⟩
      dsimp [Z]
      refine Subgroup.mem_zpowers_iff.mpr ?_
      refine ⟨m * d, by simpa using (zpow_mul' (t : G) m d)⟩
    have hTprimeZ : T ∈ section10PrimeOrderSubgroupsIn p Z := by
      rcases hTprimeI with ⟨_hTI, hTcard⟩
      exact ⟨hTZleZ, hTcard⟩
    have hTprimeOmegaZ : T ∈ section10PrimeOrderSubgroupsIn p (section12OmegaOneSubgroup p Z) := by
      rcases hTprimeZ with ⟨hTZ, hTcard⟩
      exact ⟨section15_primeOrder_le_omegaOneSubgroup_of_le (G := G) (H := Z) (X := T)
          ⟨hTZ, hTcard⟩,
        hTcard⟩
    have hTI : T = I :=
      section15_eq_of_le_primeOrderSubgroupsIn (G := G) (A := A) (X := T) (Y := I) (p := p)
        (by
          rcases hTprimeI with ⟨hTI, hTcard⟩
          exact ⟨hTI.trans hI_le_A, hTcard⟩)
        hIprime
        (by
          rcases hTprimeI with ⟨hTI, _hTcard⟩
          exact hTI)
    have hTOmegaZ : T = section12OmegaOneSubgroup p Z :=
      section15_eq_of_le_primeOrderSubgroupsIn (G := G) (A := Z)
        (X := T) (Y := section12OmegaOneSubgroup p Z) (p := p)
        (by
          rcases hTprimeI with ⟨_hTI, hTcard⟩
          exact ⟨hTZleZ, hTcard⟩)
        (by
          exact ⟨section15_omegaOneSubgroup_le, hOmegaZ_card⟩)
        (by
          rcases hTprimeOmegaZ with ⟨hTΩ, _hTcard⟩
          exact hTΩ)
    refine ⟨Z, hZleS, hZcyc, hZp, hZne, hZexp, ?_⟩
    simpa [← hTOmegaZ, hTI] using hCI

omit [IsMinCE G] in
private theorem CFSG.section15_tau13_regular_cyclic_factor_of_prime_dvd
    {M V : Subgroup G} {q : Nat.Primes}
    (hVcomm : IsMulCommutative V)
    (hqτ13 : q ∈ section12Tau1Primes M ∪ section12Tau3Primes M)
    (hqV : q.val ∣ Nat.card V)
    (hcent :
      ∀ e : G, e ∈ V → e ≠ 1 →
        subgroupPrimeSet (Subgroup.zpowers e) ⊆
          section12Tau1Primes M ∪ section12Tau3Primes M →
            elementCentralizerIn (section10Msigma M) e = ⊥) :
    ∃ Z O : Subgroup G,
      Z ≤ V ∧ IsCyclic Z ∧ IsPGroup q.val Z ∧
        Monoid.exponent Z =
          Monoid.exponent
            ((((default : Sylow q.val V) : Subgroup V).map V.subtype) : Subgroup G) ∧
        O ≤ Z ∧ Nat.card O = q.val ∧
          subgroupCentralizerIn (section10Msigma M) O = ⊥ := by
  classical
  haveI : Fact q.val.Prime := ⟨q.property⟩
  let P : Sylow q.val V := default
  let PG : Subgroup G := section10AmbientSylowSubgroup V P
  rcases section15_default_ambient_sylow_of_prime_dvd
      (V := V) (p := q) hVcomm hqV with
    ⟨hPGV, hPGne, hPGp, hPGcomm, _hPGnorm⟩
  obtain ⟨Z, hZlePG, hZcyc, hZp, hZexpPG, hZne⟩ :=
    section15_exists_cyclic_full_exponent_subgroup_of_abelian_pgroup
      (P := PG) (p := q) hPGcomm hPGp hPGne
  have hZleV : Z ≤ V := hZlePG.trans hPGV
  have hqZ : q.val ∣ Nat.card Z := by
    haveI : Nontrivial Z := (Subgroup.nontrivial_iff_ne_bot Z).2 hZne
    rcases (IsPGroup.nontrivial_iff_card (p := q.val) (G := Z) (hG := hZp)).mp inferInstance with
      ⟨n, hn_pos, hcardZ⟩
    rw [hcardZ]
    cases n with
    | zero =>
        exact False.elim ((Nat.not_lt_zero 0) hn_pos)
    | succ n =>
        exact dvd_pow_self q.val (Nat.succ_ne_zero n)
  obtain ⟨z, hzZ, hzne, hOprimeZ⟩ :=
    section15_exists_primeOrder_zpowers_of_prime_dvd_card
      (G := G) (B := Z) (q := q) hqZ
  let O : Subgroup G := Subgroup.zpowers z
  have hOleZ : O ≤ Z := by
    exact Subgroup.zpowers_le.2 hzZ
  have hOcard : Nat.card O = q.val := by
    rcases (by simpa [section10PrimeOrderSubgroupsIn] using hOprimeZ) with
      ⟨_hOZ, hOcard⟩
    simpa [O] using hOcard
  have hOτ13 :
      subgroupPrimeSet (Subgroup.zpowers z) ⊆
        section12Tau1Primes M ∪ section12Tau3Primes M := by
    intro r hr
    have hr_dvd_q : r.val ∣ q.val := by
      simpa [O, subgroupPrimeSet, hOcard] using hr
    have hr_eq_q_val : r.val = q.val :=
      (Nat.prime_dvd_prime_iff_eq r.2 q.2).mp hr_dvd_q
    have hr_eq_q : r = q := Subtype.ext hr_eq_q_val
    simpa [hr_eq_q] using hqτ13
  have hzV : z ∈ V := hZleV hzZ
  have hOcent : subgroupCentralizerIn (section10Msigma M) O = ⊥ := by
    have hzcent := hcent z hzV hzne hOτ13
    simpa [O, section15_subgroupCentralizerIn_zpowers_eq_elementCentralizerIn_early] using hzcent
  refine ⟨Z, O, hZleV, hZcyc, hZp, ?_, hOleZ, hOcard, hOcent⟩
  change Monoid.exponent Z = Monoid.exponent PG
  exact hZexpPG

private theorem CFSG.section15_tau2_regular_cyclic_factor_of_prime_dvd
    {M E E₁₂ E₁ E₂ E₃ V : Subgroup G} {q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hVnorm : section10NormalIn V E)
    (hVHall : ∃ π : Set Nat.Primes, section12HallSubgroupIn π V E)
    (hVcomm : IsMulCommutative V)
    (hqτ2 : q ∈ section12Tau2Primes M)
    (hqV : q.val ∣ Nat.card V) :
    ∃ Z O : Subgroup G,
      Z ≤ V ∧ IsCyclic Z ∧ IsPGroup q.val Z ∧
        Monoid.exponent Z =
          Monoid.exponent
            ((((default : Sylow q.val V) : Subgroup V).map V.subtype) : Subgroup G) ∧
        O ≤ Z ∧ Nat.card O = q.val ∧
          subgroupCentralizerIn (section10Msigma M) O = ⊥ := by
  classical
  have hVE : V ≤ E := hVnorm.1
  have hVM : V ≤ M := hVE.trans hE.1.2.1
  haveI : Fact q.val.Prime := ⟨q.2⟩
  obtain ⟨A, hA_E⟩ :=
    section12_exists_rankTwo_in_E_of_tau2
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE hqτ2
  have hA_le_V : A ≤ V :=
    section15_rankTwo_le_normal_hall_of_prime_dvd
      (E := E) (V := V) (A := A) (p := q) hVnorm hVHall hqV hA_E
  have hA_M : A ∈ section12RankTwoElementaryAbelianIn q M :=
    section12_rankTwo_of_EData hE hA_E
  have hA_V : A ∈ section12RankTwoElementaryAbelianIn q V := by
    exact ⟨hA_le_V, section15_rankTwo_elementary hA_E⟩
  letI : CommGroup V := IsMulCommutative.instCommGroup
  let AVsub : Subgroup V := A.subgroupOf V
  let QVsub : Subgroup V := ((default : Sylow q.val V) : Subgroup V)
  let Jsub : Subgroup V := AVsub ⊔ QVsub
  have hAVp : IsPGroup q.val AVsub :=
    section15_rankTwo_subgroupOf_isPGroup hA_V
  have hQVp : IsPGroup q.val QVsub :=
    (default : Sylow q.val V).isPGroup'
  have hJp : IsPGroup q.val Jsub := by
    dsimp [Jsub]
    exact IsPGroup.to_sup_of_normal_right hAVp hQVp
  let JG : Subgroup G := Jsub.map V.subtype
  have hJG_le_V : JG ≤ V := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hJG_le_M : JG ≤ M := hJG_le_V.trans hVM
  have hJGp : IsPGroup q.val JG := by
    simpa [JG] using IsPGroup.map hJp V.subtype
  let JM : Subgroup M := JG.subgroupOf M
  have hJMp : IsPGroup q.val JM :=
    hJGp.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := JG) (K := M) hJG_le_M).symm
  obtain ⟨P, hJM_le_P⟩ :=
    IsPGroup.exists_le_sylow (G := M) (p := q.val) hJMp
  let Ssub : Subgroup G := section10AmbientSylowSubgroup M P
  have hJG_le_Ssub : JG ≤ Ssub := by
    intro x hx
    exact Subgroup.mem_map.mpr
      ⟨⟨x, hJG_le_M hx⟩,
        hJM_le_P (by simpa [JM, Subgroup.mem_subgroupOf] using hx), rfl⟩
  have hA_le_Ssub : A ≤ Ssub := by
    intro x hxA
    have hxJ : (⟨x, hA_le_V hxA⟩ : V) ∈ Jsub := by
      exact (show AVsub ≤ Jsub from le_sup_left)
        (by simpa [AVsub, Subgroup.mem_subgroupOf] using hxA)
    have hxJG : x ∈ JG :=
      Subgroup.mem_map.mpr ⟨⟨x, hA_le_V hxA⟩, hxJ, rfl⟩
    exact hJG_le_Ssub hxJG
  have hQV_le_SsubV :
      QVsub ≤ Ssub.subgroupOf V := by
    intro y hy
    have hyJ : y ∈ Jsub := (show QVsub ≤ Jsub from le_sup_right) hy
    have hyJG : (y : G) ∈ JG :=
      Subgroup.mem_map.mpr ⟨y, hyJ, rfl⟩
    have hyS : (y : G) ∈ Ssub := hJG_le_Ssub hyJG
    simpa [Subgroup.mem_subgroupOf] using hyS
  have hScomm : IsMulCommutative Ssub := by
    have hPcomm : IsMulCommutative (P : Subgroup M) :=
      (theorem_12_5_b (G := G) (M := M) (A := A) (p := q) hM hqτ2 hA_M).1 P
    simpa [Ssub] using
      section15_isMulCommutative_ambientSylowSubgroup (G := G) (M := M) (p := q) P hPcomm
  have hSp : IsPGroup q.val Ssub := by
    change IsPGroup q.val ((P : Subgroup M).map M.subtype)
    exact IsPGroup.map P.isPGroup' M.subtype
  have hOmegaS :
      section12OmegaOneSubgroup q Ssub = A := by
    have hdata :=
      (theorem_12_5_b (G := G) (M := M) (A := A) (p := q) hM hqτ2 hA_M).2
        P (by simpa [Ssub] using hA_le_Ssub)
    simpa [Ssub] using hdata.1
  have hNormS_not : ¬ Subgroup.normalizer (Ssub : Set G) ≤ M := by
    have hdata :=
      (theorem_12_5_b (G := G) (M := M) (A := A) (p := q) hM hqτ2 hA_M).2
        P (by simpa [Ssub] using hA_le_Ssub)
    simpa [Ssub] using hdata.2
  have hC_le_E : Subgroup.centralizer (A : Set G) ≤ E := by
    have h6 :=
      corollary_12_6_b (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := q)
        hM hE hqτ2 hA_E
    intro x hx
    simpa [h6.2.1] using h6.1 hx
  have hSleE : Ssub ≤ E := by
    intro s hs
    exact hC_le_E (by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact (setLike_mul_comm
        (s := Ssub) hs (hA_le_Ssub ha)).symm)
  rcases hVHall with ⟨π, hVHallπ⟩
  rcases hVHallπ with ⟨hVE', hHallV⟩
  have hqπ : q ∈ π := by
    have hcard_sub : Nat.card (V.subgroupOf E) = Nat.card V :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := V) (K := E) hVE').toEquiv
    exact hHallV.p_in_pi_of_p_dvd_card q (by simpa [hcard_sub] using hqV)
  have hSsubE_p : IsPGroup q.val (Ssub.subgroupOf E) :=
    hSp.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := Ssub) (K := E) hSleE).symm
  haveI : (V.subgroupOf E).Normal := hVnorm.2
  have hSsubE_le_VE : Ssub.subgroupOf E ≤ V.subgroupOf E :=
    section15_pSubgroup_le_normal_hall_of_prime_mem
      (R := E) (π := π) (H := V.subgroupOf E) (A := Ssub.subgroupOf E)
      hHallV hqπ hSsubE_p
  have hSleV : Ssub ≤ V := by
    intro x hxS
    let xE : E := ⟨x, hSleE hxS⟩
    have hxSsubE : xE ∈ Ssub.subgroupOf E := by
      simpa [xE, Subgroup.mem_subgroupOf] using hxS
    have hxVE : xE ∈ V.subgroupOf E := hSsubE_le_VE hxSsubE
    simpa [xE, Subgroup.mem_subgroupOf] using hxVE
  have hSsubV_p : IsPGroup q.val (Ssub.subgroupOf V) :=
    hSp.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := Ssub) (K := V) hSleV).symm
  have hSsubV_eq_QV : Ssub.subgroupOf V = QVsub :=
    (default : Sylow q.val V).is_maximal' hSsubV_p hQV_le_SsubV
  rcases section15_exists_tau2_cyclic_factor_of_abelian_m_sylow
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (A := A) (Ssub := Ssub) (p := q)
      hM hE hqτ2 hA_E hA_M hScomm hSp hOmegaS hNormS_not with
    ⟨Z, hZleS, hZcyc, hZp, hZne, hZexpS, hOcent⟩
  let O : Subgroup G := section12OmegaOneSubgroup q Z
  have hZleV : Z ≤ V := hZleS.trans hSleV
  have hO_le_Z : O ≤ Z := by
    simpa [O] using (section15_omegaOneSubgroup_le (G := G) (H := Z) (p := q))
  have hOcard : Nat.card O = q.val := by
    simpa [O] using
      section15_omegaOneSubgroup_card_eq_prime_of_cyclic_pSubgroup
        (G := G) (H := Z) (p := q) hZp hZcyc hZne
  have hSexp_QVsub :
      Monoid.exponent Ssub = Monoid.exponent QVsub := by
    calc
      Monoid.exponent Ssub = Monoid.exponent (Ssub.subgroupOf V) := by
        symm
        simpa using
          (Monoid.exponent_eq_of_mulEquiv
            (Subgroup.subgroupOfEquivOfLe (H := Ssub) (K := V) hSleV))
      _ = Monoid.exponent QVsub := by rw [hSsubV_eq_QV]
  have hQVsub_exp_amb :
      Monoid.exponent QVsub =
        Monoid.exponent
          ((((default : Sylow q.val V) : Subgroup V).map V.subtype) : Subgroup G) := by
    simpa [QVsub] using
      (Monoid.exponent_eq_of_mulEquiv
        (Subgroup.equivMapOfInjective
          (f := V.subtype)
          ((default : Sylow q.val V) : Subgroup V)
          V.subtype_injective))
  refine ⟨Z, O, hZleV, hZcyc, hZp, ?_, hO_le_Z, hOcard, ?_⟩
  · exact hZexpS.trans (hSexp_QVsub.trans hQVsub_exp_amb)
  · simpa [O] using hOcent

private theorem CFSG.section15_exists_regular_full_exponent_subgroup_of_abelian_normal
    {M E E₁₂ E₁ E₂ E₃ V : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hVnorm : section10NormalIn V E)
    (hVHall : ∃ π : Set Nat.Primes, section12HallSubgroupIn π V E)
    (hVcomm : IsMulCommutative V)
    (hVne : V ≠ ⊥)
    (hcent :
      ∀ e : G, e ∈ V → e ≠ 1 →
        subgroupPrimeSet (Subgroup.zpowers e) ⊆
          section12Tau1Primes M ∪ section12Tau3Primes M →
            elementCentralizerIn (section10Msigma M) e = ⊥) :
    ∃ V₀ : Subgroup G, V₀ ≤ V ∧ V₀ ≠ ⊥ ∧
      Monoid.exponent V₀ = Monoid.exponent V ∧
        ∀ r : G, r ∈ V₀ → r ≠ 1 →
          elementCentralizerIn (section10Msigma M) r = ⊥ := by
  classical
  have hVE : V ≤ E := hVnorm.1
  let ι : Type := (Nat.card V).primeFactors
  let qOf : ι → Nat.Primes := fun i => ⟨i.1, Nat.prime_of_mem_primeFactors i.2⟩
  have hZfac_exists :
      ∀ i : ι, ∃ Z O : Subgroup G,
        Z ≤ V ∧ IsCyclic Z ∧ IsPGroup (qOf i).val Z ∧
          Monoid.exponent Z =
            Monoid.exponent
              ((((default : Sylow (qOf i).val V) : Subgroup V).map V.subtype) :
                Subgroup G) ∧
          O ≤ Z ∧ Nat.card O = (qOf i).val ∧
            subgroupCentralizerIn (section10Msigma M) O = ⊥ := by
    intro i
    let q : Nat.Primes := qOf i
    have hq_dvd_V : q.val ∣ Nat.card V :=
      Nat.dvd_of_mem_primeFactors i.2
    have hqE : q ∈ subgroupPrimeSet E := by
      simpa [subgroupPrimeSet] using
        hq_dvd_V.trans (Subgroup.card_dvd_of_le hVE)
    have hqτ :
        q ∈ section12Tau1Primes M ∪ section12Tau2Primes M ∪
          section12Tau3Primes M :=
      section12_prime_mem_tau_union_of_mem_E hM hE.1 hqE
    rcases hqτ with hqτ12 | hqτ3
    · rcases hqτ12 with hqτ1 | hqτ2
      · exact
          section15_tau13_regular_cyclic_factor_of_prime_dvd
            (M := M) (V := V) (q := q) hVcomm (Or.inl hqτ1) hq_dvd_V hcent
      · exact
          section15_tau2_regular_cyclic_factor_of_prime_dvd
            (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
            (E₂ := E₂) (E₃ := E₃) (V := V) (q := q)
            hM hE hVnorm hVHall hVcomm hqτ2 hq_dvd_V
    · exact
        section15_tau13_regular_cyclic_factor_of_prime_dvd
          (M := M) (V := V) (q := q) hVcomm (Or.inr hqτ3) hq_dvd_V hcent
  let Zfac : ι → Subgroup G := fun i => Classical.choose (hZfac_exists i)
  let Ofac : ι → Subgroup G := fun i => Classical.choose (Classical.choose_spec (hZfac_exists i))
  have hZfac_le : ∀ i : ι, Zfac i ≤ V := by
    intro i
    exact (Classical.choose_spec (Classical.choose_spec (hZfac_exists i))).1
  have hZfac_cyc : ∀ i : ι, IsCyclic (Zfac i) := by
    intro i
    exact (Classical.choose_spec (Classical.choose_spec (hZfac_exists i))).2.1
  have hZfac_p : ∀ i : ι, IsPGroup (qOf i).val (Zfac i) := by
    intro i
    exact (Classical.choose_spec (Classical.choose_spec (hZfac_exists i))).2.2.1
  have hZfac_exp :
      ∀ i : ι,
        Monoid.exponent (Zfac i) =
          Monoid.exponent
            ((((default : Sylow (qOf i).val V) : Subgroup V).map V.subtype) :
              Subgroup G) := by
    intro i
    exact (Classical.choose_spec (Classical.choose_spec (hZfac_exists i))).2.2.2.1
  have hOfac_le_Z : ∀ i : ι, Ofac i ≤ Zfac i := by
    intro i
    exact (Classical.choose_spec (Classical.choose_spec (hZfac_exists i))).2.2.2.2.1
  have hOfac_card : ∀ i : ι, Nat.card (Ofac i) = (qOf i).val := by
    intro i
    exact (Classical.choose_spec (Classical.choose_spec (hZfac_exists i))).2.2.2.2.2.1
  have hOfac_cent :
      ∀ i : ι, subgroupCentralizerIn (section10Msigma M) (Ofac i) = ⊥ := by
    intro i
    exact (Classical.choose_spec (Classical.choose_spec (hZfac_exists i))).2.2.2.2.2.2
  let Qfac : ι → Subgroup G := fun i =>
    ((((default : Sylow (qOf i).val V) : Subgroup V).map V.subtype) : Subgroup G)
  have hQfac_sup : (⨆ i, Qfac i) = V := by
    have hsup_top :
        (⨆ i : ι, ((default : Sylow (qOf i).val V) : Subgroup V)) = ⊤ := by
      simpa [ι, qOf, iSup_subtype] using (Sylow.iSup_sylow_eq_top (G := V))
    calc
      (⨆ i, Qfac i) =
          ((⨆ i : ι, ((default : Sylow (qOf i).val V) : Subgroup V)).map V.subtype) := by
        simp [Qfac, Subgroup.map_iSup]
      _ = ((⊤ : Subgroup V).map V.subtype) := by
        rw [hsup_top]
      _ = V.subtype.range := by rw [MonoidHom.range_eq_map]
      _ = V := by simp
  have hZfac_comm :
      Pairwise fun i j => ∀ x y, x ∈ Zfac i → y ∈ Zfac j → Commute x y := by
    intro i j _hij x y hx hy
    exact setLike_mul_comm
      (s := V) (hZfac_le i hx) (hZfac_le j hy)
  have hQfac_comm :
      Pairwise fun i j => ∀ x y, x ∈ Qfac i → y ∈ Qfac j → Commute x y := by
    intro i j _hij x y hx hy
    have hxV : x ∈ V := by
      rcases Subgroup.mem_map.mp hx with ⟨x', _hx', rfl⟩
      exact x'.property
    have hyV : y ∈ V := by
      rcases Subgroup.mem_map.mp hy with ⟨y', _hy', rfl⟩
      exact y'.property
    exact setLike_mul_comm (s := V) hxV hyV
  have hZfac_coprime :
      Pairwise fun i j => Nat.Coprime (Nat.card (Zfac i)) (Nat.card (Zfac j)) := by
    intro i j hij
    haveI : Fact (qOf i).val.Prime := ⟨(qOf i).2⟩
    haveI : Fact (qOf j).val.Prime := ⟨(qOf j).2⟩
    have hq_ne : (qOf i).val ≠ (qOf j).val := by
      intro hq
      apply hij
      exact Subtype.ext hq
    exact IsPGroup.coprime_card_of_ne
      (qOf i).val (qOf j).val hq_ne (Zfac i) (Zfac j) (hZfac_p i) (hZfac_p j)
  have hQfac_p : ∀ i : ι, IsPGroup (qOf i).val (Qfac i) := by
    intro i
    haveI : Fact (qOf i).val.Prime := ⟨(qOf i).2⟩
    simpa [Qfac] using
      IsPGroup.map
        (show IsPGroup (qOf i).val ((default : Sylow (qOf i).val V) : Subgroup V) from
          (default : Sylow (qOf i).val V).isPGroup') V.subtype
  have hQfac_coprime :
      Pairwise fun i j => Nat.Coprime (Nat.card (Qfac i)) (Nat.card (Qfac j)) := by
    intro i j hij
    haveI : Fact (qOf i).val.Prime := ⟨(qOf i).2⟩
    haveI : Fact (qOf j).val.Prime := ⟨(qOf j).2⟩
    have hq_ne : (qOf i).val ≠ (qOf j).val := by
      intro hq
      apply hij
      exact Subtype.ext hq
    exact IsPGroup.coprime_card_of_ne
      (qOf i).val (qOf j).val hq_ne (Qfac i) (Qfac j) (hQfac_p i) (hQfac_p j)
  let V₀ : Subgroup G := ⨆ i, Zfac i
  have hV₀_le_V : V₀ ≤ V := by
    simpa [V₀] using iSup_le hZfac_le
  have hV₀cyc : IsCyclic V₀ :=
    section15_isCyclic_iSup_of_pairwise_coprime_cyclic
      (G := G) Zfac hZfac_cyc hZfac_comm hZfac_coprime
  have hV₀exp :
      Monoid.exponent V₀ =
        Finset.lcm Finset.univ (fun i : ι => Monoid.exponent (Zfac i)) := by
    simpa [V₀] using
      section15_exponent_eq_iSup_of_pairwise_coprime_order
        (G := G) Zfac hZfac_comm hZfac_coprime
  have hVexp :
      Monoid.exponent V =
        Finset.lcm Finset.univ (fun i : ι => Monoid.exponent (Qfac i)) := by
    calc
      Monoid.exponent V = Monoid.exponent (↥(⨆ i, Qfac i)) := by
        rw [hQfac_sup.symm]
      _ = Finset.lcm Finset.univ (fun i : ι => Monoid.exponent (Qfac i)) := by
        simpa [Qfac] using
          section15_exponent_eq_iSup_of_pairwise_coprime_order
            (G := G) Qfac hQfac_comm hQfac_coprime
  have hV₀expV : Monoid.exponent V₀ = Monoid.exponent V := by
    rw [hV₀exp, hVexp]
    congr with i
    exact hZfac_exp i
  have hV_card_ne_one : Nat.card V ≠ 1 := by
    intro hcard
    exact hVne ((Subgroup.card_eq_one (H := V)).mp hcard)
  obtain ⟨p0, hp0prime, hp0div⟩ := Nat.exists_prime_and_dvd hV_card_ne_one
  have hp0_mem : p0 ∈ (Nat.card V).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp0prime, hp0div, Nat.card_pos.ne'⟩
  let i0 : ι := ⟨p0, hp0_mem⟩
  have hOfac_i0_le_V₀ : Ofac i0 ≤ V₀ :=
    (hOfac_le_Z i0).trans (le_iSup Zfac i0)
  have hV₀ne : V₀ ≠ ⊥ := by
    intro hV₀bot
    have hOfac_bot : Ofac i0 = ⊥ := by
      apply le_bot_iff.mp
      intro x hx
      have hxV₀ : x ∈ V₀ := hOfac_i0_le_V₀ hx
      simpa [hV₀bot] using hxV₀
    have hcard_bot : Nat.card (Ofac i0) = 1 := by
      simp [hOfac_bot]
    rw [hOfac_card i0] at hcard_bot
    exact (qOf i0).2.ne_one hcard_bot
  have hV₀reg :
      ∀ r : G, r ∈ V₀ → r ≠ 1 →
        elementCentralizerIn (section10Msigma M) r = ⊥ := by
    have hMsigma_ne : section10Msigma M ≠ ⊥ := theorem_10_2_e (M := M) hM
    intro r hrV₀ hrne
    apply le_bot_iff.mp
    intro x hx
    by_contra hxne
    let R : Subgroup G := Subgroup.zpowers r
    have hR_le_V₀ : R ≤ V₀ := Subgroup.zpowers_le.2 hrV₀
    have hR_ne : R ≠ ⊥ := by
      intro hRbot
      have hrbot : r ∈ (⊥ : Subgroup G) := by
        simpa [R, hRbot] using (Subgroup.mem_zpowers r)
      exact hrne (by simpa using hrbot)
    have hR_card_ne_one : Nat.card R ≠ 1 := by
      intro hcard
      exact hR_ne ((Subgroup.card_eq_one (H := R)).mp hcard)
    obtain ⟨q0, hq0prime, hq0div⟩ := Nat.exists_prime_and_dvd hR_card_ne_one
    let q : Nat.Primes := ⟨q0, hq0prime⟩
    haveI : Fact q.val.Prime := ⟨q.2⟩
    obtain ⟨z, hzR, hzne, hXprimeR⟩ :=
      section15_exists_primeOrder_zpowers_of_prime_dvd_card
        (G := G) (B := R) (q := q) hq0div
    let X : Subgroup G := Subgroup.zpowers z
    have hX_le_R : X ≤ R := by
      simpa [X] using hXprimeR.1
    have hX_card : Nat.card X = q.val := by
      simpa [X] using hXprimeR.2
    have hq_dvd_V : q.val ∣ Nat.card V :=
      hq0div.trans (Subgroup.card_dvd_of_le (hR_le_V₀.trans hV₀_le_V))
    have hq_mem_V : q.val ∈ (Nat.card V).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨q.2, hq_dvd_V, Nat.card_pos.ne'⟩
    let i : ι := ⟨q.val, hq_mem_V⟩
    have hqOf_i : qOf i = q := by
      apply Subtype.ext
      rfl
    have hO_bot : subgroupCentralizerIn (section10Msigma M) (Ofac i) = ⊥ :=
      hOfac_cent i
    have hO_card : Nat.card (Ofac i) = q.val := by
      simpa [hqOf_i] using hOfac_card i
    have hO_le_V₀ : Ofac i ≤ V₀ :=
      (hOfac_le_Z i).trans (le_iSup Zfac i)
    have hX_le_V₀ : X ≤ V₀ := hX_le_R.trans hR_le_V₀
    letI : IsCyclic V₀ := hV₀cyc
    have hXsub_eq_OSub :
        X.subgroupOf V₀ = (Ofac i).subgroupOf V₀ :=
      section15_unique_subgroup_of_prime_order_in_cyclic
        (p := q.val) (A := X.subgroupOf V₀) (B := (Ofac i).subgroupOf V₀)
        (by simpa [section12_card_subgroupOf_eq hX_le_V₀] using hX_card)
        (by simpa [section12_card_subgroupOf_eq hO_le_V₀] using hO_card)
    have hO_le_X : Ofac i ≤ X := by
      intro a ha
      have haSub : (⟨a, hO_le_V₀ ha⟩ : V₀) ∈ (Ofac i).subgroupOf V₀ := by
        simpa [Subgroup.mem_subgroupOf] using ha
      have haXSub : (⟨a, hO_le_V₀ ha⟩ : V₀) ∈ X.subgroupOf V₀ := by
        rwa [← hXsub_eq_OSub] at haSub
      simpa [Subgroup.mem_subgroupOf] using haXSub
    have hxr : Commute x r := by
      exact show x * r = r * x from
        ((Subgroup.mem_centralizer_iff.mp hx.2) r (by simp)).symm
    have hxz : Commute x z := by
      rcases Subgroup.mem_zpowers_iff.mp hzR with ⟨n, rfl⟩
      exact hxr.zpow_right n
    have hxCX : x ∈ subgroupCentralizerIn (section10Msigma M) X := by
      refine ⟨hx.1, ?_⟩
      change x ∈ Subgroup.centralizer (X : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      rcases Subgroup.mem_zpowers_iff.mp ha with ⟨n, rfl⟩
      exact (hxz.zpow_right n).eq.symm
    have hxCO : x ∈ subgroupCentralizerIn (section10Msigma M) (Ofac i) := by
      refine ⟨hx.1, ?_⟩
      change x ∈ Subgroup.centralizer (Ofac i : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact (Subgroup.mem_centralizer_iff.mp hxCX.2) a (hO_le_X ha)
    have hxbot : x ∈ (⊥ : Subgroup G) := by
      simpa [hO_bot] using hxCO
    exact hxne (by simpa using hxbot)
  exact ⟨V₀, hV₀_le_V, hV₀ne, hV₀expV, hV₀reg⟩

/-- Section 15 local copy of the abelian-normal-subgroup form of the short
`C_E(S)=E` branch in Theorem 12.12(b). -/
public theorem CFSG.section15_theorem_12_12_b_abelian_normal_subgroup
    {M E E₁₂ E₁ E₂ E₃ V : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hVnorm : section10NormalIn V E)
    (hVHall : ∃ π : Set Nat.Primes, section12HallSubgroupIn π V E)
    (hVcomm : IsMulCommutative V)
    (hVne : V ≠ ⊥)
    (hcent :
      ∀ e : G, e ∈ V → e ≠ 1 →
        subgroupPrimeSet (Subgroup.zpowers e) ⊆
          section12Tau1Primes M ∪ section12Tau3Primes M →
            elementCentralizerIn (section10Msigma M) e = ⊥) :
    ∃ V₀ : Subgroup G, V₀ ≤ V ∧ Monoid.exponent V₀ = Monoid.exponent V ∧
      section12FrobeniusJoinWithKernel (section10Msigma M) V₀ := by
  classical
  have hVE : V ≤ E := hVnorm.1
  rcases section15_exists_regular_full_exponent_subgroup_of_abelian_normal
      (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂)
      (E₃ := E₃) (V := V) hM hE hVnorm hVHall hVcomm hVne hcent with
    ⟨V₁, hV₁V, hV₁ne, hV₁exp, hV₁reg⟩
  have hV₁M : V₁ ≤ M := hV₁V.trans (hVE.trans hE.1.2.1)
  have hV₁comm : IsMulCommutative V₁ := by
    refine ⟨⟨fun x y => ?_⟩⟩
    apply Subtype.ext
    exact setLike_mul_comm
      (s := V) (hV₁V x.property) (hV₁V y.property)
  have hdisj : Disjoint (section10Msigma M) V₁ := by
    rw [Subgroup.disjoint_def]
    intro x hxσ hxV₁
    exact (Subgroup.disjoint_def.mp hE.1.2.2.2) hxσ (hVE (hV₁V hxV₁))
  rcases section15_same_exponent_frobenius_of_regular_abelian
      (M := M) (V := V₁) hM hV₁M hV₁comm hV₁ne hdisj hV₁reg with
    ⟨V₀, hV₀V₁, hV₀expV₁, hV₀Frob⟩
  exact ⟨V₀, hV₀V₁.trans hV₁V, hV₀expV₁.trans hV₁exp, hV₀Frob⟩

public theorem CFSG.section15_msigma_le_ambientDerived
    {M : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G) :
    section10Msigma M ≤ ambientDerivedSubgroup M := by
  simpa [section10Msigma, ambientDerivedSubgroup] using
    (Subgroup.map_mono (f := M.subtype) (theorem_10_2_c hM).2)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_product_eq
    {M K U : Subgroup G}
    (hKU : section15KUData M K U) :
    M = K ⊔ U ⊔ section10Msigma M := by
  have hprod : M = section10Msigma M ⊔ (K ⊔ U) := hKU.2.2.1.2.2.1
  simpa [sup_assoc, sup_comm, sup_left_comm] using hprod

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_msigma_subgroupOf_eq
    {M : Subgroup G} :
    (section10Msigma M).subgroupOf M = section10MsigmaSubgroup M := by
  change (piCoreIn (section10SigmaPrimes M) M).subgroupOf M =
    piCore (section10SigmaPrimes M) M
  exact piCore_map_subtype_subgroupOf (section10SigmaPrimes M) M

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_msigma_le
    {M : Subgroup G} :
    section10Msigma M ≤ M := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
  exact (y : M).property

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_msigma_normalIn
    {M : Subgroup G} :
    section10NormalIn (section10Msigma M) M := by
  refine ⟨section15_msigma_le, ?_⟩
  rw [section15_msigma_subgroupOf_eq]
  infer_instance

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_ambientDerived_le
    {M : Subgroup G} :
    ambientDerivedSubgroup M ≤ M := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
  exact (y : M).property

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_ambientDerived_subgroupOf_eq
    {M : Subgroup G} :
    (ambientDerivedSubgroup M).subgroupOf M = derivedSubgroup M := by
  ext x
  constructor
  · intro hx
    change (x : G) ∈ ambientDerivedSubgroup M at hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, hyx⟩
    have hy_eq : y = x := by
      apply Subtype.ext
      simpa using hyx
    simpa [hy_eq] using hy
  · intro hx
    change (x : G) ∈ ambientDerivedSubgroup M
    exact Subgroup.mem_map_of_mem M.subtype hx

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_ambientDerived_normalIn
    {M : Subgroup G} :
    section10NormalIn (ambientDerivedSubgroup M) M := by
  refine ⟨section15_ambientDerived_le, ?_⟩
  rw [section15_ambientDerived_subgroupOf_eq]
  infer_instance

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_normal_of_derivedSubgroup_le
    {R : Type*} [Group R] (N : Subgroup R) (hder : derivedSubgroup R ≤ N) :
    N.Normal := by
  refine Subgroup.Normal.mk ?_
  intro n hn g
  have hcomm : ⁅g, n⁆ ∈ derivedSubgroup R := by
    change ⁅g, n⁆ ∈ ⁅(⊤ : Subgroup R), (⊤ : Subgroup R)⁆
    exact Subgroup.commutator_mem_commutator (by simp) (by simp)
  have hconj_eq : g * n * g⁻¹ = ⁅g, n⁆ * n := by
    rw [commutatorElement_def]
    group
  rw [hconj_eq]
  exact N.mul_mem (hder hcomm) hn

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_secondDerived_eq_ambientDerived_msigma_of_msigma_eq_derived
    {M : Subgroup G}
    (hσD : section10Msigma M = ambientDerivedSubgroup M) :
    section15SecondDerivedSubgroup M =
      ambientDerivedSubgroup (section10Msigma M) := by
  rw [section15SecondDerivedSubgroup, ← hσD]


omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_le_normalizer_subgroupCentralizerIn
    {N E A : Subgroup G}
    (hNE : N ≤ Subgroup.normalizer (E : Set G))
    (hNA : N ≤ Subgroup.normalizer (A : Set G)) :
    N ≤ Subgroup.normalizer (subgroupCentralizerIn E A : Set G) := by
  classical
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rcases hx with ⟨hxE, hxC⟩
    have hnE : n ∈ Subgroup.normalizer (E : Set G) := hNE hn
    have hnA : n ∈ Subgroup.normalizer (A : Set G) := hNA hn
    refine ⟨(Subgroup.mem_normalizer_iff.mp hnE x).1 hxE, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro a haA
    have hnA_inv : n⁻¹ ∈ Subgroup.normalizer (A : Set G) := by
      exact inv_mem hnA
    have hninvaA : n⁻¹ * a * n ∈ A := by
      simpa [mul_assoc] using
        (Subgroup.mem_normalizer_iff.mp hnA_inv a).1 haA
    have hxC' : x ∈ Subgroup.centralizer (A : Set G) := hxC
    have hcomm :=
      Subgroup.mem_centralizer_iff.mp hxC' (n⁻¹ * a * n) hninvaA
    have hconj := congrArg (fun t : G => n * t * n⁻¹) hcomm
    simpa [mul_assoc] using hconj
  · intro hx
    rcases hx with ⟨hxE, hxC⟩
    have hnE : n ∈ Subgroup.normalizer (E : Set G) := hNE hn
    have hnA : n ∈ Subgroup.normalizer (A : Set G) := hNA hn
    refine ⟨(Subgroup.mem_normalizer_iff.mp hnE x).2 hxE, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro a haA
    have hnaA : n * a * n⁻¹ ∈ A := by
      simpa [mul_assoc] using
        (Subgroup.mem_normalizer_iff.mp hnA a).1 haA
    have hxC' : n * x * n⁻¹ ∈ Subgroup.centralizer (A : Set G) := hxC
    have hcomm :=
      Subgroup.mem_centralizer_iff.mp hxC' (n * a * n⁻¹) hnaA
    have hconj := congrArg (fun t : G => n⁻¹ * t * n) hcomm
    simpa [mul_assoc] using hconj

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_le_normalizer_sup_of_le_normalizers
    {N A B : Subgroup G}
    (hNA : N ≤ Subgroup.normalizer (A : Set G))
    (hNB : N ≤ Subgroup.normalizer (B : Set G)) :
    N ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  classical
  intro n hn
  have hnA : n ∈ Subgroup.normalizer (A : Set G) := hNA hn
  have hnB : n ∈ Subgroup.normalizer (B : Set G) := hNB hn
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hAmap : A.map (MulAut.conj n).toMonoidHom = A := by
      ext y
      constructor
      · rintro ⟨a, haA, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp hnA a).1 haA
      · intro hyA
        refine ⟨n⁻¹ * y * n, ?_, ?_⟩
        · have hninvA : n⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
            (Subgroup.normalizer (A : Set G)).inv_mem hnA
          simpa [mul_assoc] using
            (Subgroup.mem_normalizer_iff.mp hninvA y).1 hyA
        · simp [mul_assoc]
    have hBmap : B.map (MulAut.conj n).toMonoidHom = B := by
      ext y
      constructor
      · rintro ⟨b, hbB, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp hnB b).1 hbB
      · intro hyB
        refine ⟨n⁻¹ * y * n, ?_, ?_⟩
        · have hninvB : n⁻¹ ∈ Subgroup.normalizer (B : Set G) :=
            (Subgroup.normalizer (B : Set G)).inv_mem hnB
          simpa [mul_assoc] using
            (Subgroup.mem_normalizer_iff.mp hninvB y).1 hyB
        · simp [mul_assoc]
    have hsupmap :
        (A ⊔ B).map (MulAut.conj n).toMonoidHom = A ⊔ B := by
      rw [Subgroup.map_sup, hAmap, hBmap]
    have hy :
        MulAut.conj n x ∈ (A ⊔ B).map (MulAut.conj n).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    have hy' : MulAut.conj n x ∈ A ⊔ B := by
      simpa only [hsupmap] using hy
    simpa [MulAut.conj_apply] using hy'
  · intro hx
    have hninvA : n⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
      (Subgroup.normalizer (A : Set G)).inv_mem hnA
    have hninvB : n⁻¹ ∈ Subgroup.normalizer (B : Set G) :=
      (Subgroup.normalizer (B : Set G)).inv_mem hnB
    have hAmap : A.map (MulAut.conj n⁻¹).toMonoidHom = A := by
      ext y
      constructor
      · rintro ⟨a, haA, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp hninvA a).1 haA
      · intro hyA
        refine ⟨n * y * n⁻¹, ?_, ?_⟩
        · simpa [mul_assoc] using
            (Subgroup.mem_normalizer_iff.mp hnA y).1 hyA
        · simp [mul_assoc]
    have hBmap : B.map (MulAut.conj n⁻¹).toMonoidHom = B := by
      ext y
      constructor
      · rintro ⟨b, hbB, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp hninvB b).1 hbB
      · intro hyB
        refine ⟨n * y * n⁻¹, ?_, ?_⟩
        · simpa [mul_assoc] using
            (Subgroup.mem_normalizer_iff.mp hnB y).1 hyB
        · simp [mul_assoc]
    have hsupmap :
        (A ⊔ B).map (MulAut.conj n⁻¹).toMonoidHom = A ⊔ B := by
      rw [Subgroup.map_sup, hAmap, hBmap]
    have hy :
        MulAut.conj n⁻¹ (n * x * n⁻¹) ∈
          (A ⊔ B).map (MulAut.conj n⁻¹).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨n * x * n⁻¹, hx, rfl⟩
    have hy' : MulAut.conj n⁻¹ (n * x * n⁻¹) ∈ A ⊔ B := by
      simpa only [hsupmap] using hy
    simpa [MulAut.conj_apply, mul_assoc] using hy'

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_ambientDerived_le_centralizer_of_cyclic_normal
    {M Z : Subgroup G} (hZleM : Z ≤ M)
    (hZnormM : (Z.subgroupOf M).Normal) (hZcyc : IsCyclic Z) :
    ambientDerivedSubgroup M ≤ Subgroup.centralizer (Z : Set G) := by
  classical
  let ZM : Subgroup M := Z.subgroupOf M
  haveI : ZM.Normal := hZnormM
  have hZMcyc : IsCyclic ZM :=
    (Subgroup.subgroupOfEquivOfLe (H := Z) (K := M) hZleM).isCyclic.2 hZcyc
  letI : IsCyclic ZM := hZMcyc
  let eAut : MulAut ZM ≃* (ZMod (Nat.card ZM))ˣ :=
    IsCyclic.mulAutMulEquiv (G := ZM)
  letI : CommGroup (MulAut ZM) :=
    MonoidHom.commGroupOfInjective eAut.toMonoidHom eAut.injective
  let φ : M →* MulAut ZM := MulAut.conjNormal (H := ZM)
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rcases Subgroup.mem_map.mp hx with ⟨d, hd, rfl⟩
  let zM : M := ⟨z, hZleM hz⟩
  let zZM : ZM := ⟨zM, by
    change z ∈ Z
    exact hz⟩
  have hd_comm : (d : M) ∈ _root_.commutator M := by
    change (d : M) ∈ derivedSubgroup M
    exact hd
  have hd_ker : (d : M) ∈ φ.ker :=
    Abelianization.commutator_subset_ker φ hd_comm
  have hφd : φ d = 1 := by
    simpa [MonoidHom.mem_ker] using hd_ker
  have hfix : φ d zZM = zZM := by
    simp [hφd]
  have hconj : ((d : M) : G) * z * ((d : M) : G)⁻¹ = z := by
    have hval := congrArg (fun z : ZM => ((z : M) : G)) hfix
    simpa [φ, zZM, zM, ZM, MulAut.conjNormal_apply, MulAut.conj_apply,
      mul_assoc] using hval
  have hmul := congrArg (fun t : G => t * ((d : M) : G)) hconj
  simpa [mul_assoc] using hmul.symm

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_ambientDerived_eq_bot_of_isMulCommutative
    {M : Subgroup G} (hMcomm : IsMulCommutative M) :
    ambientDerivedSubgroup M = ⊥ := by
  classical
  letI : IsMulCommutative M := hMcomm
  letI : CommGroup M := IsMulCommutative.instCommGroup
  have htop_le_cent :
      (⊤ : Subgroup M) ≤ Subgroup.centralizer (((⊤ : Subgroup M) : Set M)) := by
    intro x _hx
    rw [Subgroup.mem_centralizer_iff]
    intro y _hy
    exact mul_comm y x
  have htop_comm_bot : ⁅(⊤ : Subgroup M), (⊤ : Subgroup M)⁆ = ⊥ :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).2 htop_le_cent
  have hcomm_bot : _root_.commutator M = ⊥ := by
    simpa [_root_.commutator_def] using htop_comm_bot
  apply bot_unique
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
  have hybot : y ∈ (⊥ : Subgroup M) := by
    simpa [derivedSubgroup, derivedSeries_one, _root_.commutator_def,
      htop_comm_bot, hcomm_bot] using hy
  have hyone : y = 1 := by
    simpa using hybot
  simp [hyone]

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_normal_complementIn_isComplement'
    {M K N : Subgroup G}
    (hcomp : section12ComplementIn M K N)
    (hNnorm : section10NormalIn N M) :
    (K.subgroupOf M).IsComplement' (N.subgroupOf M) := by
  classical
  rcases hcomp with ⟨hKM, hNM, hM, hdisj⟩
  haveI : (N.subgroupOf M).Normal := hNnorm.2
  have hsup_local : K.subgroupOf M ⊔ N.subgroupOf M = ⊤ := by
    calc
      K.subgroupOf M ⊔ N.subgroupOf M = (K ⊔ N).subgroupOf M := by
        symm
        exact Subgroup.subgroupOf_sup (A := K) (A' := N) (B := M) hKM hNM
      _ = ⊤ := by
        rw [← hM]
        simp
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [Subgroup.disjoint_def]
    intro x hxK hxN
    apply Subtype.ext
    apply Subgroup.disjoint_def.mp hdisj
    · simpa [Subgroup.mem_subgroupOf] using hxK
    · simpa [Subgroup.mem_subgroupOf] using hxN
  · simpa [hsup_local] using
      (Subgroup.mul_normal (K.subgroupOf M) (N.subgroupOf M)).symm

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_card_eq_of_normal_complements
    {M K A B : Subgroup G}
    (hA : section12ComplementIn M K A)
    (hAnorm : section10NormalIn A M)
    (hB : section12ComplementIn M K B)
    (hBnorm : section10NormalIn B M) :
    Nat.card A = Nat.card B := by
  classical
  have hAcomp :
      (K.subgroupOf M).IsComplement' (A.subgroupOf M) :=
    section15_normal_complementIn_isComplement' hA hAnorm
  have hBcomp :
      (K.subgroupOf M).IsComplement' (B.subgroupOf M) :=
    section15_normal_complementIn_isComplement' hB hBnorm
  calc
    Nat.card A = Nat.card (A.subgroupOf M) := by
      exact (natCard_subgroupOf_eq A M hA.2.1).symm
    _ = (K.subgroupOf M).index := by
      exact hAcomp.symm.index_eq_card.symm
    _ = Nat.card (B.subgroupOf M) := by
      exact hBcomp.symm.index_eq_card
    _ = Nat.card B := by
      exact natCard_subgroupOf_eq B M hB.2.1

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_fixed_um_sigma_complement
    {M K U : Subgroup G}
    (hKU : section15KUData M K U) :
    section12ComplementIn M K (U ⊔ section10Msigma M) := by
  exact hKU.2.1

omit [IsMinCE G] in
/-- Nontrivial Hall `κ(M)` data puts `M` in the Section 14 `𝓜_P` family.
This is a real proof obligation used to access Theorem 14.7. -/
private theorem CFSG.section15_familyP_of_nontrivial_K
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U)
    (hKne : K ≠ ⊥) :
    M ∈ section14MFamilyP G := by
  classical
  rcases hKU.1 with ⟨hKM, hKHall⟩
  have hK_card_ne_one : Nat.card K ≠ 1 := by
    intro hcard
    exact hKne ((Subgroup.card_eq_one (H := K)).1 hcard)
  obtain ⟨q0, hq0prime, hq0dvd⟩ := Nat.exists_prime_and_dvd hK_card_ne_one
  let q : Nat.Primes := ⟨q0, hq0prime⟩
  have hcard_sub : Nat.card (K.subgroupOf M) = Nat.card K := by
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := K) (K := M) hKM).toEquiv
  have hq_sub : q.val ∣ Nat.card (K.subgroupOf M) := by
    simpa [q, hcard_sub] using hq0dvd
  have hqκ : q ∈ section14KappaPrimes M :=
    hKHall.p_in_pi_of_p_dvd_card q hq_sub
  exact ⟨hM, ⟨q, hqκ⟩⟩

private theorem CFSG.section15_K_cyclic
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U) :
    IsCyclic K := by
  by_cases hKbot : K = ⊥
  · subst K
    exact isCyclic_of_subsingleton (α := (⊥ : Subgroup G))
  · have hMP : M ∈ section14MFamilyP G :=
      section15_familyP_of_nontrivial_K hM hKU hKbot
    have hZcyc : IsCyclic (section14Z M K) := (theorem_14_7_d hMP hKU.1).2.1
    letI : IsCyclic (section14Z M K) := hZcyc
    exact Subgroup.isCyclic_of_le (show K ≤ section14Z M K by
      exact le_sup_left)

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_U_sigma_kappa_compl
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U) :
    IsPiSubgroup (G := G) ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ) U := by
  exact section15_kappa_compl_context_U_sigma_kappa_compl hM hKU

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_elementPrimeSupport_le_sigma_kappa_compl_of_mem_U
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U)
    {y : G} (hyU : y ∈ U) :
    section14ElementPrimeSupport y ⊆
      ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ) := by
  intro q hq
  have hUπ := section15_U_sigma_kappa_compl (M := M) (K := K) (U := U) hM hKU
  have hcyc_le_U : Subgroup.zpowers y ≤ U := Subgroup.zpowers_le.2 hyU
  have hqU : q.val ∣ Nat.card U := by
    exact hq.trans (Subgroup.card_dvd_of_le hcyc_le_U)
  exact hUπ q hqU

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_not_kappa_support_of_nontrivial_mem_U
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U)
    {y : G} (hyU : y ∈ U) (hyne : y ≠ 1) :
    ¬ section14ElementPrimeSupport y ⊆ section14KappaPrimes M := by
  classical
  intro hyκ
  have hyσ' :
      section14ElementPrimeSupport y ⊆
        ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ) :=
    section15_elementPrimeSupport_le_sigma_kappa_compl_of_mem_U
      (M := M) (K := K) (U := U) hM hKU hyU
  have hzp_ne_bot : Subgroup.zpowers y ≠ (⊥ : Subgroup G) := by
    intro hbot
    have hybot : y ∈ (⊥ : Subgroup G) := by
      simpa [hbot] using (Subgroup.mem_zpowers y)
    exact hyne (by simpa using hybot)
  have hcard_ne_one : Nat.card (Subgroup.zpowers y) ≠ 1 := by
    intro hcard
    exact hzp_ne_bot ((Subgroup.eq_bot_iff_card (H := Subgroup.zpowers y)).2 hcard)
  rcases Nat.exists_prime_and_dvd hcard_ne_one with ⟨p, hpprime, hpdvd⟩
  let q : Nat.Primes := ⟨p, hpprime⟩
  have hq_support : q ∈ section14ElementPrimeSupport y := by
    change p ∣ Nat.card (Subgroup.zpowers y)
    exact hpdvd
  exact hyσ' hq_support (Or.inl (hyκ hq_support))

private theorem CFSG.section15_tau_branch_of_nontrivial_mem_U_centralizing_msigma
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U)
    {x y : G}
    (hxMs : x ∈ section10Msigma M) (hxne : x ≠ 1)
    (hyU : y ∈ U) (hyne : y ≠ 1)
    (hycent : y ∈ elementCentralizerIn M x) :
    section14ElementPrimeSupport y ⊆ section12Tau2Primes M ∧
      section14SigmaLength y = 1 ∧
        section9MaximalSubgroupsContaining
          (Subgroup.centralizer ({y} : Set G)) = {M} := by
  have hyσ' : section14IsPiElement (section10SigmaPrimes M)ᶜ y := by
    intro q hq
    have hq_not_union :
        q ∈ ((section14KappaPrimes M ∪ section10SigmaPrimes M)ᶜ) :=
      section15_elementPrimeSupport_le_sigma_kappa_compl_of_mem_U
        (M := M) (K := K) (U := U) hM hKU hyU hq
    intro hqσ
    exact hq_not_union (Or.inr hqσ)
  rcases corollary_14_3 (M := M) hM hxMs hxne hyne hycent hyσ' with hκ | htau
  · exact False.elim
      (section15_not_kappa_support_of_nontrivial_mem_U
        (M := M) (K := K) (U := U) hM hKU hyU hyne hκ.1)
  · exact htau

private theorem CFSG.section15_tau_branch_of_nontrivial_X_element
    {M K U X : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U)
    (hXU : X ≤ U)
    (hcent : subgroupCentralizerIn (section10Msigma M) X ≠ ⊥)
    {y : G} (hyX : y ∈ X) (hyne : y ≠ 1) :
    section14ElementPrimeSupport y ⊆ section12Tau2Primes M ∧
      section14SigmaLength y = 1 ∧
        section9MaximalSubgroupsContaining
          (Subgroup.centralizer ({y} : Set G)) = {M} := by
  classical
  rcases Subgroup.ne_bot_iff_exists_ne_one.mp hcent with ⟨xC, hxCne⟩
  let x : G := xC
  have hxCmem : x ∈ subgroupCentralizerIn (section10Msigma M) X := xC.property
  have hxMs : x ∈ section10Msigma M := hxCmem.1
  have hxcentX : x ∈ Subgroup.centralizer (X : Set G) := hxCmem.2
  have hxne : x ≠ 1 := by
    intro hx
    apply hxCne
    ext
    exact hx
  have hyU : y ∈ U := hXU hyX
  have hyM : y ∈ M := (section15_kappa_compl_context_U_hall hKU).1 hyU
  have hxy : x * y = y * x := by
    have hyx : y * x = x * y := by
      simpa [Subgroup.mem_centralizer_iff] using hxcentX y hyX
    exact hyx.symm
  have hycent_singleton : y ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hz_eq : z = x := by simpa using hz
    subst z
    exact hxy
  have hycent : y ∈ elementCentralizerIn M x := ⟨hyM, hycent_singleton⟩
  exact section15_tau_branch_of_nontrivial_mem_U_centralizing_msigma
    (M := M) (K := K) (U := U) hM hKU hxMs hxne hyU hyne hycent

private theorem CFSG.section15_centralizer_subgroups_tau2_pi
    {M K U X : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U)
    (hXU : X ≤ U) (_hXne : X ≠ ⊥)
    (hcent : subgroupCentralizerIn (section10Msigma M) X ≠ ⊥) :
    IsPiSubgroup (G := G) (section12Tau2Primes M) X := by
  classical
  intro q hqX
  haveI : Fact q.val.Prime := ⟨q.property⟩
  obtain ⟨a, ha_order⟩ := exists_prime_orderOf_dvd_card' (G := X) q.val hqX
  let y : G := (a : X)
  have hyX : y ∈ X := a.property
  have hy_order : orderOf y = q.val := by
    simpa [y, Subgroup.orderOf_coe] using ha_order
  have hyne : y ≠ 1 := by
    intro hy
    have hone : (1 : ℕ) = q.val := by
      simpa [y, hy] using hy_order
    exact q.property.ne_one hone.symm
  have hq_support : q ∈ section14ElementPrimeSupport y := by
    simp [section14ElementPrimeSupport, subgroupPrimeSet, Nat.card_zpowers, hy_order]
  exact (section15_tau_branch_of_nontrivial_X_element
    (M := M) (K := K) (U := U) (X := X) hM hKU hXU hcent hyX hyne).1
    hq_support

private theorem CFSG.section15_centralizer_subgroups_cyclic
    {M K U X : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U)
    (hXU : X ≤ U) (hXne : X ≠ ⊥)
    (hcent : subgroupCentralizerIn (section10Msigma M) X ≠ ⊥) :
    IsCyclic X := by
  classical
  by_contra hXnoncyc
  let C : Subgroup G := K ⊔ U
  have hCcomp : section12ComplementToMsigma M C := by
    change section12ComplementIn M (section10Msigma M) C
    simpa [C] using hKU.2.2.1
  have hChall :
      IsHallSubgroup (section10SigmaPrimes M)ᶜ (C.subgroupOf M) :=
    section12_msigma_complement_isHall_sigma_compl hM hCcomp
  have hCπ : IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ C := by
    intro q hqC
    have hcard :
        Nat.card (C.subgroupOf M) = Nat.card C :=
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := C) (K := M) hCcomp.2.1).toEquiv
    exact hChall.p_in_pi_of_p_dvd_card q (by simpa [hcard] using hqC)
  rcases section13_exists_EData_containing_sigma_compl_piSubgroup
      (G := G) (M := M) (A := C) hM hCcomp.2.1 hCπ with
    ⟨E, E₁₂, E₁, E₂, E₃, hE, hC_le_E⟩
  have hXE : X ≤ E := by
    intro y hyX
    exact hC_le_E (Subgroup.mem_sup_right (hXU hyX))
  have hXπ : IsPiSubgroup (G := G) (section12Tau2Primes M) X :=
    section15_centralizer_subgroups_tau2_pi hM hKU hXU hXne hcent
  rcases section15_exists_rankTwo_in_noncyclic_tau2_piSubgroup
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (X := X) hM hE hXE hXπ hXnoncyc with
    ⟨p, hpτ2, A, hAX, hA_M⟩
  rcases Subgroup.ne_bot_iff_exists_ne_one.mp hcent with ⟨xC, hxCne⟩
  let x : G := xC
  have hxCmem : x ∈ subgroupCentralizerIn (section10Msigma M) X := xC.property
  have hxMs : x ∈ section10Msigma M := hxCmem.1
  have hxcentX : x ∈ Subgroup.centralizer (X : Set G) := hxCmem.2
  have hxA : x ∈ subgroupCentralizerIn (section10Msigma M) A := by
    refine ⟨hxMs, ?_⟩
    change x ∈ Subgroup.centralizer (A : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro a haA
    exact (Subgroup.mem_centralizer_iff.mp hxcentX) a (hAX haA)
  have hAcent_bot :
      subgroupCentralizerIn (section10Msigma M) A = ⊥ :=
    theorem_12_5_d hM hpτ2 hA_M
  have hxbot : x ∈ (⊥ : Subgroup G) := by
    simpa [hAcent_bot] using hxA
  exact hxCne (by
    ext
    simpa [x] using hxbot)

private theorem CFSG.section15_centralizer_subgroups_maximal_overgroup
    {M K U X : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U)
    (hXU : X ≤ U) (hXne : X ≠ ⊥)
    (hcent : subgroupCentralizerIn (section10Msigma M) X ≠ ⊥)
    (hXcyc : IsCyclic X) :
    section9MaximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M} := by
  classical
  obtain ⟨xX, hxX_gen⟩ := (isCyclic_iff_exists_zpowers_eq_top (α := X)).1 hXcyc
  let y : G := xX
  have hyX : y ∈ X := xX.property
  have hyne : y ≠ 1 := by
    intro hy
    have hxX_one : xX = 1 := Subtype.ext hy
    have hXbot : X = ⊥ := le_bot_iff.mp (by
      intro z hzX
      let zX : X := ⟨z, hzX⟩
      have hzpow : zX ∈ Subgroup.zpowers xX := by
        simp [hxX_gen]
      rcases Subgroup.mem_zpowers_iff.mp hzpow with ⟨n, hn⟩
      have hzX_one : zX = 1 := by
        simpa [hxX_one] using hn.symm
      have hz_one : z = 1 := by
        simpa [zX] using congrArg Subtype.val hzX_one
      simpa [Subgroup.mem_bot] using hz_one)
    exact hXne hXbot
  have hbranch :=
    section15_tau_branch_of_nontrivial_X_element
      (M := M) (K := K) (U := U) (X := X) hM hKU hXU hcent hyX hyne
  have hcent_eq :
      Subgroup.centralizer (X : Set G) =
        Subgroup.centralizer ({y} : Set G) := by
    apply le_antisymm
    · intro g hg
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hz_eq : z = y := by simpa using hz
      subst z
      exact (Subgroup.mem_centralizer_iff.mp hg) y hyX
    · intro g hg
      rw [Subgroup.mem_centralizer_iff]
      intro z hzX
      let zX : X := ⟨z, hzX⟩
      have hzpow : zX ∈ Subgroup.zpowers xX := by
        simp [hxX_gen]
      rcases Subgroup.mem_zpowers_iff.mp hzpow with ⟨n, hn⟩
      have hz_eq : z = y ^ n := by
        simpa [y, zX] using (congrArg Subtype.val hn).symm
      rw [hz_eq]
      have hcomm : Commute y g :=
        (Subgroup.mem_centralizer_singleton_iff.mp hg).symm
      exact (hcomm.zpow_left n).eq
  simpa [hcent_eq] using hbranch.2.2

omit [Finite G] [IsMinCE G] in
/-- L005-S0030: in the nontrivial-`K` branch the fixed `UM_σ` is normal in
`M`.  This should come from the fixed semidirect-product decomposition
`M = (UM_σ) ⋊ K`, not from replacing `U` by Proposition 14.2(a)'s existential
complement. -/
private theorem CFSG.section15_um_sigma_normal_of_nontrivial_K
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U)
    (_hKne : K ≠ ⊥) :
    section10NormalIn (U ⊔ section10Msigma M) M := by
  exact section15_kappa_compl_context_um_sigma_normal hM hKU

/-- L005-S0050: since `M/(UM_σ) ≃ K` and `K` is cyclic, `M' ≤ UM_σ`. -/
private theorem CFSG.section15_derived_le_um_sigma_of_nontrivial_K
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U)
    (hKne : K ≠ ⊥) :
    ambientDerivedSubgroup M ≤ U ⊔ section10Msigma M := by
  let N : Subgroup G := U ⊔ section10Msigma M
  have hNnorm : section10NormalIn N M := by
    simpa [N] using section15_um_sigma_normal_of_nontrivial_K hM hKU hKne
  haveI : (N.subgroupOf M).Normal := hNnorm.2
  have hcomp :
      (K.subgroupOf M).IsComplement' (N.subgroupOf M) := by
    exact section15_normal_complementIn_isComplement'
      (section15_fixed_um_sigma_complement (M := M) (K := K) (U := U) hKU)
      hNnorm
  have hKsub_cyclic : IsCyclic (K.subgroupOf M) := by
    have hKcyc : IsCyclic K := section15_K_cyclic hM hKU
    let eK : K.subgroupOf M ≃* K :=
      Subgroup.subgroupOfEquivOfLe (H := K) (K := M) hKU.1.1
    letI : IsCyclic K := hKcyc
    exact isCyclic_of_surjective eK.symm.toMonoidHom eK.symm.surjective
  have hquot_cyclic : IsCyclic (M ⧸ N.subgroupOf M) := by
    let eQ : M ⧸ N.subgroupOf M ≃* K.subgroupOf M :=
      hcomp.QuotientMulEquiv
    letI : IsCyclic (K.subgroupOf M) := hKsub_cyclic
    exact isCyclic_of_surjective eQ.symm.toMonoidHom eQ.symm.surjective
  have hquot_comm :
      IsMulCommutative (M ⧸ N.subgroupOf M) := by
    letI : IsCyclic (M ⧸ N.subgroupOf M) := hquot_cyclic
    exact IsCyclic.isMulCommutative
  have hcomm_le : _root_.commutator M ≤ N.subgroupOf M :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le
      (N := N.subgroupOf M)).1 hquot_comm
  intro x hx
  have hxM : x ∈ M := section15_ambientDerived_le hx
  have hxsub :
      (⟨x, hxM⟩ : M) ∈ derivedSubgroup M := by
    have hxsub' :
        (⟨x, hxM⟩ : M) ∈ (ambientDerivedSubgroup M).subgroupOf M := by
      simpa [Subgroup.mem_subgroupOf] using hx
    simpa [section15_ambientDerived_subgroupOf_eq] using hxsub'
  have hxcomm : (⟨x, hxM⟩ : M) ∈ _root_.commutator M := by
    simpa [derivedSubgroup, derivedSeries_one, _root_.commutator_def] using hxsub
  have hxNsub : (⟨x, hxM⟩ : M) ∈ N.subgroupOf M :=
    hcomm_le hxcomm
  simpa [N, Subgroup.mem_subgroupOf] using hxNsub

/-- L005-S0060: `M'` and the fixed `UM_σ` are both complements to `K` in
`M`, hence have the same order. -/
private theorem CFSG.section15_derived_card_eq_um_sigma_of_nontrivial_K
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U)
    (hKne : K ≠ ⊥) :
    Nat.card (ambientDerivedSubgroup M) =
      Nat.card ((U ⊔ section10Msigma M : Subgroup G)) := by
  have hMP : M ∈ section14MFamilyP G :=
    section15_familyP_of_nontrivial_K hM hKU hKne
  exact section15_card_eq_of_normal_complements
    (theorem_14_7_h hMP hKU.1)
    section15_ambientDerived_normalIn
    (section15_fixed_um_sigma_complement (M := M) (K := K) (U := U) hKU)
    (section15_um_sigma_normal_of_nontrivial_K hM hKU hKne)

private theorem CFSG.section15_derived_eq_um_sigma_of_nontrivial_K
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U)
    (hKne : K ≠ ⊥) :
    ambientDerivedSubgroup M = U ⊔ section10Msigma M := by
  have hle : ambientDerivedSubgroup M ≤ U ⊔ section10Msigma M :=
    section15_derived_le_um_sigma_of_nontrivial_K hM hKU hKne
  have hcard : Nat.card (ambientDerivedSubgroup M) =
      Nat.card ((U ⊔ section10Msigma M : Subgroup G)) :=
    section15_derived_card_eq_um_sigma_of_nontrivial_K hM hKU hKne
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [← hcard])

private theorem CFSG.section15_fixed_complement_ambientDerived_commutative
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U) :
    IsMulCommutative (ambientDerivedSubgroup (K ⊔ U)) := by
  classical
  let A : Subgroup G := K ⊔ U
  have hAcomp : section12ComplementToMsigma M A := by
    change section12ComplementIn M (section10Msigma M) A
    simpa [A] using hKU.2.2.1
  have hAhall :
      IsHallSubgroup (section10SigmaPrimes M)ᶜ (A.subgroupOf M) :=
    section12_msigma_complement_isHall_sigma_compl hM hAcomp
  have hAπ : IsPiSubgroup (G := G) (section10SigmaPrimes M)ᶜ A := by
    intro q hqA
    have hcard :
        Nat.card (A.subgroupOf M) = Nat.card A :=
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := A) (K := M) hAcomp.2.1).toEquiv
    exact hAhall.p_in_pi_of_p_dvd_card q (by simpa [hcard] using hqA)
  rcases section13_exists_EData_containing_sigma_compl_piSubgroup
      (G := G) (M := M) (A := A) hM hAcomp.2.1 hAπ with
    ⟨E, E₁₂, E₁, E₂, E₃, hE, hA_le_E⟩
  have hAder_le_Eder :
      ambientDerivedSubgroup A ≤ ambientDerivedSubgroup E :=
    section12_ambientDerivedSubgroup_mono hA_le_E
  have hEder_comm : IsMulCommutative (ambientDerivedSubgroup E) :=
    (corollary_12_10_b (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE).2
  refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
  exact setLike_mul_comm
    (s := ambientDerivedSubgroup E) (hAder_le_Eder x.property)
    (hAder_le_Eder y.property)

private theorem CFSG.section15_quotient_abelian_fixed_complement
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U) :
    section15QuotientAbelian (ambientDerivedSubgroup M) (section10Msigma M) := by
  classical
  let S : Subgroup G := section10Msigma M
  let D : Subgroup G := ambientDerivedSubgroup M
  let A : Subgroup G := K ⊔ U
  let C : Subgroup G := ambientDerivedSubgroup A
  have hSleD : S ≤ D := by
    simpa [S, D] using section15_msigma_le_ambientDerived hM
  have hDleM : D ≤ M := by
    simpa [D] using (section15_ambientDerived_le (M := M))
  have hAcomp : section12ComplementToMsigma M A := by
    change section12ComplementIn M (section10Msigma M) A
    simpa [A] using hKU.2.2.1
  have hCeq : A ⊓ D = C := by
    simpa [A, D, C] using
      (section12_complement_inter_ambientDerived_eq (G := G) (M := M)
        (E := A) hAcomp)
  have hCleA : C ≤ A := by
    simpa [C, A] using (section15_ambientDerived_le (M := A))
  have hCleD : C ≤ D := by
    rw [← hCeq]
    exact inf_le_right
  have hSNormD : section10NormalIn S D := by
    refine ⟨hSleD, ?_⟩
    have hSNormM : section10NormalIn S M := by
      simpa [S] using (section15_msigma_normalIn (M := M))
    have hM_norm_S : M ≤ Subgroup.normalizer (S : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hSNormM.1).1 hSNormM.2
    have hD_norm_S : D ≤ Subgroup.normalizer (S : Set G) := hDleM.trans hM_norm_S
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hSleD).2 hD_norm_S
  have hD_le_SC : D ≤ S ⊔ C := by
    intro x hxD
    have hxM : x ∈ M := hDleM hxD
    let xM : M := ⟨x, hxM⟩
    have hsup_local :
        S.subgroupOf M ⊔ A.subgroupOf M = ⊤ := by
      calc
        S.subgroupOf M ⊔ A.subgroupOf M = (S ⊔ A).subgroupOf M := by
          symm
          exact Subgroup.subgroupOf_sup (A := S) (A' := A) (B := M)
            hAcomp.1 hAcomp.2.1
        _ = ⊤ := by
          rw [← hAcomp.2.2.1]
          simp
    have hxlocal : xM ∈ S.subgroupOf M ⊔ A.subgroupOf M := by
      rw [hsup_local]
      exact trivial
    have hSNormM : section10NormalIn S M := by
      simpa [S] using (section15_msigma_normalIn (M := M))
    haveI : (S.subgroupOf M).Normal := hSNormM.2
    rcases (Subgroup.mem_sup_of_normal_left
        (s := S.subgroupOf M) (t := A.subgroupOf M) (x := xM)).1 hxlocal with
      ⟨sM, hsS, aM, haA, hsaM⟩
    let s : G := sM
    let a : G := aM
    have hsS' : s ∈ S := by
      simpa [s, Subgroup.mem_subgroupOf] using hsS
    have haA' : a ∈ A := by
      simpa [a, Subgroup.mem_subgroupOf] using haA
    have hsaG : s * a = x := by
      simpa [s, a, xM] using congrArg Subtype.val hsaM
    have hsD : s ∈ D := hSleD hsS'
    have haD : a ∈ D := by
      have ha_eq : a = s⁻¹ * x := by
        rw [← hsaG]
        simp
      rw [ha_eq]
      exact D.mul_mem (D.inv_mem hsD) hxD
    have haC : a ∈ C := by
      have haInf : a ∈ A ⊓ D := ⟨haA', haD⟩
      simpa [hCeq] using haInf
    rw [← hsaG]
    exact Subgroup.mul_mem_sup hsS' haC
  have hD_eq : D = S ⊔ C :=
    le_antisymm hD_le_SC (sup_le hSleD hCleD)
  have hcompDC : section12ComplementIn D C S := by
    refine ⟨hCleD, hSleD, ?_, ?_⟩
    · simp [hD_eq, sup_comm]
    · rw [Subgroup.disjoint_def]
      intro x hxC hxS
      exact Subgroup.disjoint_def.mp hAcomp.2.2.2 hxS (hCleA hxC)
  have hcomp' :
      (C.subgroupOf D).IsComplement' (S.subgroupOf D) :=
    section15_normal_complementIn_isComplement' hcompDC hSNormD
  have hCcomm : IsMulCommutative C := by
    simpa [C, A] using
      section15_fixed_complement_ambientDerived_commutative
        (M := M) (K := K) (U := U) hM hKU
  have hCsub_comm : IsMulCommutative (C.subgroupOf D) := by
    refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
    apply Subtype.ext
    have hxC : ((x : D) : G) ∈ C :=
      (Subgroup.mem_subgroupOf.mp x.property)
    have hyC : ((y : D) : G) ∈ C :=
      (Subgroup.mem_subgroupOf.mp y.property)
    exact setLike_mul_comm
      (s := C) hxC hyC
  letI : (S.subgroupOf D).Normal := hSNormD.2
  let eQ : D ⧸ S.subgroupOf D ≃* C.subgroupOf D := hcomp'.QuotientMulEquiv
  have hquot_comm : IsMulCommutative (D ⧸ S.subgroupOf D) := by
    letI : IsMulCommutative (C.subgroupOf D) := hCsub_comm
    letI : CommGroup (C.subgroupOf D) := IsMulCommutative.instCommGroup
    refine ⟨⟨fun x y => ?_⟩⟩
    apply eQ.injective
    simpa [map_mul] using (mul_comm (eQ x) (eQ y))
  exact ⟨hSleD, hSNormD.2, hquot_comm⟩

/-- L005-S0080: after `M'=UM_σ`, the subgroup `U` embeds in the abelian
quotient `M'/M_σ`, so `U` is abelian. -/
private theorem CFSG.section15_U_commutative_of_nontrivial_K
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U)
    (hKne : K ≠ ⊥) :
    IsMulCommutative U := by
  classical
  let D : Subgroup G := ambientDerivedSubgroup M
  let S : Subgroup G := section10Msigma M
  have hD_eq : D = U ⊔ S := by
    simpa [D, S] using section15_derived_eq_um_sigma_of_nontrivial_K hM hKU hKne
  rcases section15_quotient_abelian_fixed_complement
      (M := M) (K := K) (U := U) hM hKU with
    ⟨hSD, hSNorm, hquot_comm⟩
  letI : (S.subgroupOf D).Normal := hSNorm
  letI : IsMulCommutative (D ⧸ S.subgroupOf D) := hquot_comm
  letI : CommGroup (D ⧸ S.subgroupOf D) := IsMulCommutative.instCommGroup
  refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
  have hxD : (x : G) ∈ D := by
    rw [hD_eq]
    exact Subgroup.mem_sup_left x.property
  have hyD : (y : G) ∈ D := by
    rw [hD_eq]
    exact Subgroup.mem_sup_left y.property
  let xD : D := ⟨x, hxD⟩
  let yD : D := ⟨y, hyD⟩
  let q : D →* D ⧸ S.subgroupOf D := QuotientGroup.mk' (S.subgroupOf D)
  have hq_comm : q xD * q yD = q yD * q xD := mul_comm (q xD) (q yD)
  have hcomm_q_one : q ⁅xD, yD⁆ = 1 := by
    simpa [q, map_commutatorElement] using
      (commutatorElement_eq_one_iff_mul_comm).2 hq_comm
  have hcomm_S : ⁅(x : G), (y : G)⁆ ∈ S := by
    have hcomm_sub :
        ⁅xD, yD⁆ ∈ S.subgroupOf D :=
      (QuotientGroup.eq_one_iff (N := S.subgroupOf D) (x := ⁅xD, yD⁆)).1 hcomm_q_one
    simpa [S, xD, yD, Subgroup.mem_subgroupOf, commutatorElement_def] using hcomm_sub
  have hcomm_U : ⁅(x : G), (y : G)⁆ ∈ U := by
    simpa [commutatorElement_def] using
      U.mul_mem (U.mul_mem (U.mul_mem x.property y.property) (U.inv_mem x.property))
        (U.inv_mem y.property)
  have hcomm_one : ⁅(x : G), (y : G)⁆ = 1 := by
    have hdisj : Disjoint S (K ⊔ U) := by
      simpa [S] using hKU.2.2.1.2.2.2
    have hcomm_bot : ⁅(x : G), (y : G)⁆ ∈ (⊥ : Subgroup G) := by
      have hinf : ⁅(x : G), (y : G)⁆ ∈ S ⊓ (K ⊔ U) :=
        ⟨hcomm_S, Subgroup.mem_sup_right hcomm_U⟩
      simpa [hdisj.eq_bot] using hinf
    simpa using hcomm_bot
  exact (commutatorElement_eq_one_iff_mul_comm).1 hcomm_one

/-- Fixed-`U` bridge for Lemma 15.1(b), assembled from the L005 core
subclaims. -/
private theorem CFSG.section15_nontrivial_K_fixed_U_bridge
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U)
    (hKne : K ≠ ⊥) :
    section10NormalIn (U ⊔ section10Msigma M) M ∧
      ambientDerivedSubgroup M = U ⊔ section10Msigma M ∧
        IsMulCommutative U := by
  exact ⟨section15_um_sigma_normal_of_nontrivial_K hM hKU hKne,
    section15_derived_eq_um_sigma_of_nontrivial_K hM hKU hKne,
    section15_U_commutative_of_nontrivial_K hM hKU hKne⟩

private theorem CFSG.section15_fixed_um_sigma_normal
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U) :
    section10NormalIn (U ⊔ section10Msigma M) M := by
  by_cases hK : K = ⊥
  · have hUM : U ⊔ section10Msigma M = M := by
      have hprod := section15_product_eq (M := M) (K := K) (U := U) hKU
      simpa [hK, sup_assoc] using hprod.symm
    rw [hUM]
    refine ⟨le_rfl, ?_⟩
    rw [Subgroup.subgroupOf_self]
    infer_instance
  · exact (section15_nontrivial_K_fixed_U_bridge hM hKU hK).1

/-- Lemma 15.1(a): under the fixed `M,K,U` notation, `UM_σ` is normal in
`M = KUM_σ`, `K` is cyclic, `M_σ ≤ M'`, and `M'/M_σ` is abelian. -/
public theorem CFSG.lemma_15_1_a
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U) :
    section10NormalIn (U ⊔ section10Msigma M) M ∧
      M = K ⊔ U ⊔ section10Msigma M ∧
        IsCyclic K ∧
          section10Msigma M ≤ ambientDerivedSubgroup M ∧
            section15QuotientAbelian (ambientDerivedSubgroup M) (section10Msigma M) := by
  exact ⟨section15_fixed_um_sigma_normal hM hKU,
    section15_product_eq hKU,
    section15_K_cyclic hM hKU,
    section15_msigma_le_ambientDerived hM,
    section15_quotient_abelian_fixed_complement hM hKU⟩

/-- Lemma 15.1(b): if `K ≠ 1`, then `M' = UM_σ` and `U` is abelian. -/
public theorem CFSG.lemma_15_1_b
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U)
    (hKne : K ≠ ⊥) :
    ambientDerivedSubgroup M = U ⊔ section10Msigma M ∧
      IsMulCommutative U := by
  exact (section15_nontrivial_K_fixed_U_bridge hM hKU hKne).2

/-- Lemma 15.1(c): a nonidentity subgroup `X ≤ U` with
`C_{M_σ}(X) ≠ 1` has unique maximal centralizer overgroup `M` and is a
cyclic `τ₂(M)`-subgroup. -/
public theorem CFSG.lemma_15_1_c
    {M K U X : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U)
    (hXU : X ≤ U) (hXne : X ≠ ⊥)
    (hcent : subgroupCentralizerIn (section10Msigma M) X ≠ ⊥) :
    section9MaximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M} ∧
      IsCyclic X ∧ IsPiSubgroup (G := G) (section12Tau2Primes M) X := by
  have hXcyc : IsCyclic X :=
    section15_centralizer_subgroups_cyclic hM hKU hXU hXne hcent
  exact ⟨section15_centralizer_subgroups_maximal_overgroup
      hM hKU hXU hXne hcent hXcyc,
    hXcyc,
    section15_centralizer_subgroups_tau2_pi hM hKU hXU hXne hcent⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section15_generated_msigma_centralizers_le_U
    (M U : Subgroup G) :
    section15GeneratedMsigmaCentralizers M U ≤ U := by
  classical
  refine (Subgroup.closure_le (K := U)).2 ?_
  intro u hu
  rcases hu with ⟨x, _hxMsigma, _hxne, huCent⟩
  exact huCent.1

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_trivial_K_U_complementToMsigma
    {M K U : Subgroup G}
    (hKU : section15KUData M K U)
    (hK : K = ⊥) :
    section12ComplementToMsigma M U := by
  subst K
  change section12ComplementIn M (section10Msigma M) U
  simpa using hKU.2.2.1

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section15_tau2_disjoint_tau1_tau3
    {M : Subgroup G} {q : Nat.Primes}
    (hq2 : q ∈ section12Tau2Primes M) :
    q ∉ section12Tau1Primes M ∪ section12Tau3Primes M := by
  intro hq13
  rcases hq13 with hq1 | hq3
  · have h2 : primeRank q.val M = 2 := hq2.2
    have h1 : primeRank q.val M = 1 := hq1.2.2
    have hbad : (2 : ℕ) = 1 := h2.symm.trans h1
    norm_num at hbad
  · have h2 : primeRank q.val M = 2 := hq2.2
    have h1 : primeRank q.val M = 1 := hq3.2.2
    have hbad : (2 : ℕ) = 1 := h2.symm.trans h1
    norm_num at hbad

/-- The centralizer-vanishing hypothesis needed to apply the Theorem 12.12
construction to the fixed Section 15 subgroup `U`.  If a nonidentity
`τ₁(M)∪τ₃(M)` element of `U` centralized a nonidentity element of `M_σ`,
Lemma 15.1(c) would force the cyclic subgroup it generates to be a
`τ₂(M)`-subgroup, contradicting the disjoint definitions of `τ₁,τ₂,τ₃`. -/
public theorem CFSG.section15_theorem12_12_hcent_of_U
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U) :
    ∀ e : G, e ∈ U → e ≠ 1 →
      subgroupPrimeSet (Subgroup.zpowers e) ⊆
        section12Tau1Primes M ∪ section12Tau3Primes M →
          elementCentralizerIn (section10Msigma M) e = ⊥ := by
  classical
  intro e heU hene hsupport
  apply le_antisymm ?_ bot_le
  intro y hy
  by_contra hyne
  have hXU : Subgroup.zpowers e ≤ U := Subgroup.zpowers_le.2 heU
  have hXne : Subgroup.zpowers e ≠ (⊥ : Subgroup G) := by
    intro hbot
    have he_bot : e ∈ (⊥ : Subgroup G) := by
      simpa [hbot] using (Subgroup.mem_zpowers e)
    exact hene (by simpa using he_bot)
  have hsubcent_ne :
      subgroupCentralizerIn (section10Msigma M) (Subgroup.zpowers e) ≠ ⊥ := by
    have hySub :
        y ∈ subgroupCentralizerIn (section10Msigma M) (Subgroup.zpowers e) := by
      refine ⟨hy.1, ?_⟩
      change y ∈ Subgroup.centralizer ((Subgroup.zpowers e : Subgroup G) : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, hn⟩
      have hz_eq : z = e ^ n := hn.symm
      rw [hz_eq]
      have hcomm : Commute y e :=
        Subgroup.mem_centralizer_singleton_iff.mp hy.2
      exact (hcomm.zpow_right n).eq.symm
    let yC : subgroupCentralizerIn (section10Msigma M) (Subgroup.zpowers e) :=
      ⟨y, hySub⟩
    refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨yC, ?_⟩
    intro hyC_one
    exact hyne (by simpa [yC] using congrArg Subtype.val hyC_one)
  have hXπ : IsPiSubgroup (G := G) (section12Tau2Primes M) (Subgroup.zpowers e) :=
    (lemma_15_1_c (M := M) (K := K) (U := U) (X := Subgroup.zpowers e)
      hM hKU hXU hXne hsubcent_ne).2.2
  have hcard_ne_one : Nat.card (Subgroup.zpowers e) ≠ 1 := by
    intro hcard
    exact hXne ((Subgroup.eq_bot_iff_card (H := Subgroup.zpowers e)).2 hcard)
  rcases Nat.exists_prime_and_dvd hcard_ne_one with ⟨p, hpprime, hpdvd⟩
  let q : Nat.Primes := ⟨p, hpprime⟩
  have hq_support : q ∈ subgroupPrimeSet (Subgroup.zpowers e) := by
    change p ∣ Nat.card (Subgroup.zpowers e)
    exact hpdvd
  exact (section15_tau2_disjoint_tau1_tau3
    (M := M) (q := q) (hXπ q (by simpa [q] using hpdvd)))
    (hsupport hq_support)

/-- The `K=1` branch of Lemma 15.1(d), supplied by Theorem 12.12(a) for the
fixed Section 12 complement attached to the Section 15 choice of `U`. -/
private theorem CFSG.section15_generated_centralizers_of_trivial_K
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U)
    (hK : K = ⊥) :
    IsMulCommutative (section15GeneratedMsigmaCentralizers M U) := by
  classical
  have hUcomp : section12ComplementToMsigma M U :=
    section15_trivial_K_U_complementToMsigma hKU hK
  rcases section15_exists_EData_for_fixed_sigma_complement
      (G := G) (M := M) (E := U) hM hUcomp with
    ⟨E₁₂, E₁, E₂, E₃, hE⟩
  rcases theorem_12_12_a
      (G := G) (M := M) (E := U) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) hM hE
      (section15_theorem12_12_hcent_of_U hM hKU) with
    ⟨A₀, _hA₀U, hA₀comm, _hA₀norm, hcentral_le⟩
  have hG_le_A₀ : section15GeneratedMsigmaCentralizers M U ≤ A₀ := by
    refine (Subgroup.closure_le (K := A₀)).2 ?_
    intro u hu
    rcases hu with ⟨x, hxMsigma, hxne, huCent⟩
    exact hcentral_le x hxMsigma hxne huCent
  refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
  exact setLike_mul_comm
    (s := A₀) (hG_le_A₀ x.property) (hG_le_A₀ y.property)

private theorem CFSG.section15_generated_centralizers_of_nontrivial_K
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U)
    (hKne : K ≠ ⊥) :
    IsMulCommutative (section15GeneratedMsigmaCentralizers M U) := by
  classical
  have hUcomm : IsMulCommutative U :=
    (lemma_15_1_b hM hKU hKne).2
  have hGU : section15GeneratedMsigmaCentralizers M U ≤ U :=
    section15_generated_msigma_centralizers_le_U M U
  refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
  exact setLike_mul_comm
    (s := U) (hGU x.property) (hGU y.property)


/-- Lemma 15.1(d): the subgroup generated by the centralizers `C_U(x)` for
`x ∈ M_σ#` is abelian. -/
public theorem CFSG.lemma_15_1_d
    {M K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hKU : section15KUData M K U) :
    IsMulCommutative (section15GeneratedMsigmaCentralizers M U) := by
  by_cases hK : K = ⊥
  · exact section15_generated_centralizers_of_trivial_K hM hKU hK
  · exact section15_generated_centralizers_of_nontrivial_K hM hKU hK


end Section15
