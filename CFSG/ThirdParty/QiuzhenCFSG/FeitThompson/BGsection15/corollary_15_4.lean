module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection15.corollary_15_3
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.CentralizerControl
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Conjugacy
import Mathlib.Algebra.Group.Subgroup.Order
import Mathlib.GroupTheory.Schreier

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-! # Corollary 15 4 from BG Section 15 -/

section Section15

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]
omit [IsMinCE G] in
/-- Corollary 15.4: every nonidentity nilpotent Hall subgroup of `G` is
contained in `M_σ` for a suitable maximal subgroup `M`. -/
private theorem CFSG.section15_corollary15_4_exists_nontrivial_sylow
    {H : Subgroup G}
    (hHne : H ≠ ⊥)
    (_hHall : section15HallSubgroupOf H (⊤ : Subgroup G))
    (_hNil : Group.IsNilpotent H) :
    ∃ p : Nat.Primes, ∃ S : Subgroup G,
      S ≤ H ∧ S ≠ ⊥ ∧ IsPGroup p.val S ∧ section15HallSubgroupOf S H := by
  classical
  have hcard_ne_one : Nat.card H ≠ 1 := by
    intro hcard
    exact hHne ((Subgroup.card_eq_one (H := H)).1 hcard)
  obtain ⟨p, hpPrime, hpDvd⟩ := Nat.exists_prime_and_dvd hcard_ne_one
  let p' : Nat.Primes := ⟨p, hpPrime⟩
  haveI : Fact p'.val.Prime := ⟨p'.property⟩
  let P : Sylow p'.val H := Classical.choice (Sylow.nonempty (p := p'.val) (G := H))
  let S : Subgroup G := section10AmbientSylowSubgroup H P
  have hSleH : S ≤ H := by
    intro x hx
    have hxmap : x ∈ (P : Subgroup H).map H.subtype := by
      simpa [S, section10AmbientSylowSubgroup] using hx
    rcases Subgroup.mem_map.mp hxmap with ⟨y, _hy, rfl⟩
    exact y.property
  have hPne : (P : Subgroup H) ≠ ⊥ := by
    exact Sylow.ne_bot_of_dvd_card (G := H) (p := p'.val) P (by simpa [p'] using hpDvd)
  have hSne : S ≠ ⊥ := by
    intro hSbot
    have hmapbot : (P : Subgroup H).map H.subtype = ⊥ := by
      simpa [S, section10AmbientSylowSubgroup] using hSbot
    exact hPne
      ((Subgroup.map_eq_bot_iff_of_injective
        (H := (P : Subgroup H)) (f := H.subtype) H.subtype_injective).1 hmapbot)
  have hSp : IsPGroup p'.val S := by
    change IsPGroup p'.val ((P : Subgroup H).map H.subtype)
    exact IsPGroup.map (p := p'.val) (H := (P : Subgroup H)) P.isPGroup' H.subtype
  have hSsub_eq : S.subgroupOf H = (P : Subgroup H) := by
    simpa [S, section10AmbientSylowSubgroup] using
      (subgroupOf_map_subtype_eq (K := H) (P : Subgroup H))
  have hSprimeSet : subgroupPrimeSet S = ({p'} : Set Nat.Primes) := by
    simpa using
      (section8_subgroupPrimeSet_eq_singleton_of_isPGroup_ne_bot
        (G := G) (p := p'.val) (H := S) hSp hSne)
  have hPprimeSet : subgroupPrimeSet (P : Subgroup H) = ({p'} : Set Nat.Primes) := by
    simpa using
      (section8_subgroupPrimeSet_eq_singleton_of_isPGroup_ne_bot
        (G := H) (p := p'.val) (H := (P : Subgroup H)) P.isPGroup' hPne)
  have hSHall : section15HallSubgroupOf S H := by
    refine ⟨hSleH, ?_⟩
    rw [hSsub_eq, hSprimeSet]
    refine isHallSubgroup_of (G := H) ({p'} : Set Nat.Primes) (P : Subgroup H) ?_ ?_
    · intro q hqcard
      have hqP : q ∈ subgroupPrimeSet (P : Subgroup H) := by
        simpa [subgroupPrimeSet] using hqcard
      simpa [hPprimeSet] using hqP
    · intro q hq hpidx
      have hqeq : q = p' := by simpa using hq
      subst q
      exact P.not_dvd_index hpidx
  exact ⟨p', S, hSleH, hSne, hSp, hSHall⟩

private theorem CFSG.section15_normalizer_ne_top_of_nontrivial_pSubgroup
    {S : Subgroup G} {p : Nat.Primes}
    (hSne : S ≠ ⊥) (hSp : IsPGroup p.val S) :
    Subgroup.normalizer (S : Set G) ≠ ⊤ := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  intro hnorm_top
  have hSnormal : S.Normal := Subgroup.normalizer_eq_top_iff.mp hnorm_top
  let : IsSimpleGroup G := IsMinCE.simple
  rcases (haveI := hSnormal; IsSimpleGroup.eq_bot_or_eq_top_of_normal S) with hSbot | hStop
  · exact hSne hSbot
  · have htop_p : IsPGroup p.val (⊤ : Subgroup G) :=
      hSp.of_equiv (MulEquiv.subgroupCongr hStop)
    have hGp : IsPGroup p.val G :=
      htop_p.of_equiv (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G)
    have : Group.IsNilpotent G := IsPGroup.isNilpotent (p := p.val) (G := G)
      (h := hGp)
    exact IsMinCE.not_solvable (G := G) (inferInstance : Group.IsSolvable G)

/-- Corollary 15.4 setup: for a chosen nonidentity Sylow subgroup `S` of
`H`, choose `M ∈ 𝓜(N_G(S))`; the Section 10 sigma-normalizer step gives
`S ≤ M_σ` and lets `S` be used as a Hall subgroup of `M_σ`. -/
private theorem CFSG.section15_corollary15_4_exists_maximal_for_sylow
    {H S : Subgroup G} {p : Nat.Primes}
    (hHall : section15HallSubgroupOf H (⊤ : Subgroup G))
    (hSleH : S ≤ H)
    (hSne : S ≠ ⊥)
    (hSp : IsPGroup p.val S)
    (hSHall : section15HallSubgroupOf S H) :
    ∃ M : Subgroup G,
      M ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (S : Set G)) ∧
        S ≤ section10Msigma M ∧
          section15HallSubgroupOf S (section10Msigma M) := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  rcases hHall with ⟨_hHtop, hHHall⟩
  rcases hSHall with ⟨_hSleH', hSHallH⟩
  have hSprimeSet : subgroupPrimeSet S = ({p} : Set Nat.Primes) := by
    have hp_eq : (⟨p.val, Fact.out⟩ : Nat.Primes) = p := Subtype.ext rfl
    simpa [hp_eq] using
      (section8_subgroupPrimeSet_eq_singleton_of_isPGroup_ne_bot
        (G := G) (p := p.val) (H := S) hSp hSne)
  have hpS : p ∈ subgroupPrimeSet S := by
    simp [hSprimeSet]
  have hpH : p ∈ subgroupPrimeSet H :=
    hpS.trans (Subgroup.card_dvd_of_le hSleH)
  have hp_not_SsubH_index : ¬ p.val ∣ (S.subgroupOf H).index := by
    intro hpidx
    exact (hSHallH.p_in_pi_of_p_dvd_index p hpidx) hpS
  have hp_not_H_index : ¬ p.val ∣ H.index := by
    intro hpidx
    have hHtop_map :
        (H.subgroupOf (⊤ : Subgroup G)).map (⊤ : Subgroup G).subtype = H := by
      exact Subgroup.map_subgroupOf_eq_of_le (G := G) (H := H) (K := ⊤) le_top
    have hH_index_top :
        H.index = (H.subgroupOf (⊤ : Subgroup G)).index * (⊤ : Subgroup G).index := by
      simpa [hHtop_map] using
        (Subgroup.index_map_subtype
          (H := (⊤ : Subgroup G)) (K := H.subgroupOf (⊤ : Subgroup G)))
    have hpidx_top : p.val ∣ (H.subgroupOf (⊤ : Subgroup G)).index := by
      have hp_prod :
          p.val ∣ (H.subgroupOf (⊤ : Subgroup G)).index *
            (⊤ : Subgroup G).index := by
        simpa [hH_index_top] using hpidx
      simpa using hp_prod
    exact (hHHall.p_in_pi_of_p_dvd_index p hpidx_top) hpH
  have hSsubH_map : (S.subgroupOf H).map H.subtype = S := by
    exact Subgroup.map_subgroupOf_eq_of_le (G := G) (H := S) (K := H) hSleH
  have hS_index :
      S.index = (S.subgroupOf H).index * H.index := by
    simpa [hSsubH_map] using
      (Subgroup.index_map_subtype (H := H) (K := S.subgroupOf H))
  have hp_not_S_index : ¬ p.val ∣ S.index := by
    intro hpidx
    have hp_prod : p.val ∣ (S.subgroupOf H).index * H.index := by
      simpa [hS_index] using hpidx
    rcases p.property.dvd_or_dvd hp_prod with hpSidx | hpHidx
    · exact hp_not_SsubH_index hpSidx
    · exact hp_not_H_index hpHidx
  let P : Sylow p.val G := hSp.toSylow hp_not_S_index
  have hP_eq_S : (P : Subgroup G) = S := by
    simp [P, IsPGroup.toSylow_coe]
  have hnorm_proper : Subgroup.normalizer (S : Set G) ≠ ⊤ :=
    section15_normalizer_ne_top_of_nontrivial_pSubgroup
      (G := G) (S := S) (p := p) hSne hSp
  rcases section9_exists_maximalSubgroupsContaining_of_ne_top
      (G := G) hnorm_proper with ⟨M, hMcont⟩
  have hM : M ∈ section9MaximalSubgroups G := hMcont.1
  have hNormSleM : Subgroup.normalizer (S : Set G) ≤ M := hMcont.2
  have hSleM : S ≤ M :=
    Subgroup.le_normalizer.trans hNormSleM
  have hPleM : (P : Subgroup G) ≤ M := by
    simpa [hP_eq_S] using hSleM
  let PM : Sylow p.val M := P.subtype hPleM
  have hPM_map : (PM : Subgroup M).map M.subtype = (P : Subgroup G) := by
    calc
      (PM : Subgroup M).map M.subtype =
          ((P : Subgroup G).subgroupOf M).map M.subtype := by
        simp [PM, Sylow.coe_subtype]
      _ = (P : Subgroup G) ⊓ M := by
        exact Subgroup.subgroupOf_map_subtype (P : Subgroup G) M
      _ = (P : Subgroup G) := inf_eq_left.mpr hPleM
  have hAmbient_PM : section10AmbientSylowSubgroup M PM = S := by
    simpa [section10AmbientSylowSubgroup, hP_eq_S] using hPM_map
  have hpM : p ∈ subgroupPrimeSet M :=
    hpS.trans (Subgroup.card_dvd_of_le hSleM)
  have hpσ : p ∈ section10SigmaPrimes M := by
    refine ⟨hpM, PM, ?_⟩
    simpa [hAmbient_PM] using hNormSleM
  have hSsubM_p : IsPGroup p.val (S.subgroupOf M) := by
    let e : S.subgroupOf M ≃* S :=
      Subgroup.subgroupOfEquivOfLe (H := S) (K := M) hSleM
    exact hSp.of_equiv e.symm
  have hSsubM_le_sigma :
      S.subgroupOf M ≤ section10MsigmaSubgroup M :=
    section15_pSubgroup_le_normal_hall_of_prime_mem
      (R := M) (π := section10SigmaPrimes M)
      (H := section10MsigmaSubgroup M) (A := S.subgroupOf M) (p := p)
      ((theorem_10_2_b (G := G) hM).2) hpσ hSsubM_p
  have hSsigma : S ≤ section10Msigma M := by
    intro x hxS
    have hxM : x ∈ M := hSleM hxS
    let xM : M := ⟨x, hxM⟩
    have hxSsub : xM ∈ S.subgroupOf M := by
      simpa [xM, Subgroup.mem_subgroupOf] using hxS
    exact Subgroup.mem_map.mpr ⟨xM, hSsubM_le_sigma hxSsub, rfl⟩
  have hSHallSigma : section15HallSubgroupOf S (section10Msigma M) := by
    refine ⟨hSsigma, ?_⟩
    refine isHallSubgroup_of
      (G := section10Msigma M) (π := subgroupPrimeSet S)
      (H := S.subgroupOf (section10Msigma M)) ?_ ?_
    · intro q hqcard
      have hcard :
          Nat.card (S.subgroupOf (section10Msigma M)) = Nat.card S :=
        Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe
            (H := S) (K := section10Msigma M) hSsigma).toEquiv
      simpa [subgroupPrimeSet, hcard] using hqcard
    · intro q hqS hqidx
      have hq_eq : q = p := by
        have hq_single : q ∈ ({p} : Set Nat.Primes) := by
          simpa [hSprimeSet] using hqS
        simpa using hq_single
      subst q
      have hSsubSigma_map :
          (S.subgroupOf (section10Msigma M)).map
              (section10Msigma M).subtype = S := by
        exact Subgroup.map_subgroupOf_eq_of_le
          (G := G) (H := S) (K := section10Msigma M) hSsigma
      have hS_index_sigma :
          S.index =
            (S.subgroupOf (section10Msigma M)).index *
              (section10Msigma M).index := by
        simpa [hSsubSigma_map] using
          (Subgroup.index_map_subtype
            (H := section10Msigma M) (K := S.subgroupOf (section10Msigma M)))
      exact hp_not_S_index (by
        rw [hS_index_sigma]
        exact dvd_mul_of_dvd_left hqidx (section10Msigma M).index)
  exact ⟨M, hMcont, hSsigma, hSHallSigma⟩

omit [IsMinCE G] in
/-- In a nilpotent subgroup, a nontrivial Hall `p`-subgroup is normal
inside the ambient local group. -/
private theorem CFSG.section15_hall_pSubgroup_subgroupOf_normal_of_nilpotent
    {H S : Subgroup G} {p : Nat.Primes}
    (hNil : Group.IsNilpotent H)
    (hSleH : S ≤ H)
    (hSne : S ≠ ⊥)
    (hSp : IsPGroup p.val S)
    (hSHall : section15HallSubgroupOf S H) :
    (S.subgroupOf H).Normal := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  rcases hSHall with ⟨_hSleH', hHallS⟩
  let Ssub : Subgroup H := S.subgroupOf H
  have hSprimeSet : subgroupPrimeSet S = ({p} : Set Nat.Primes) := by
    have hp_eq : (⟨p.val, Fact.out⟩ : Nat.Primes) = p := Subtype.ext rfl
    simpa [hp_eq] using
      (section8_subgroupPrimeSet_eq_singleton_of_isPGroup_ne_bot
        (G := G) (p := p.val) (H := S) hSp hSne)
  have hpS : p ∈ subgroupPrimeSet S := by
    simp [hSprimeSet]
  have hSsub_p : IsPGroup p.val Ssub := by
    exact hSp.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := S) (K := H) hSleH).symm
  have hp_not_Ssub_index : ¬ p.val ∣ Ssub.index := by
    intro hpidx
    exact (hHallS.p_in_pi_of_p_dvd_index p hpidx) hpS
  let P : Sylow p.val H := hSsub_p.toSylow hp_not_Ssub_index
  have hPnormal : (P : Subgroup H).Normal :=
    Group.IsNilpotent.sylow_normal hNil p.val P
  simpa [P, Ssub, IsPGroup.toSylow_coe] using hPnormal

omit [IsMinCE G] in
/-- In the Corollary 15.4 setup, a nontrivial Hall `q`-subgroup `T` of the
ambient Hall subgroup `H`, once known to lie in `M`, is a Sylow `q`-subgroup
of `M`. -/
private theorem CFSG.section15_corollary15_4_exists_sylow_M_for_hall_subgroup
    {H T M : Subgroup G} {q : Nat.Primes}
    (hHall : section15HallSubgroupOf H (⊤ : Subgroup G))
    (hTleH : T ≤ H)
    (hTleM : T ≤ M)
    (hTne : T ≠ ⊥)
    (hTp : IsPGroup q.val T)
    (hTHall : section15HallSubgroupOf T H) :
    ∃ P : Sylow q.val M, section10AmbientSylowSubgroup M P = T := by
  classical
  haveI : Fact q.val.Prime := ⟨q.property⟩
  let TsubM : Subgroup M := T.subgroupOf M
  have hTsubM_p : IsPGroup q.val TsubM := by
    exact hTp.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := T) (K := M) hTleM).symm
  have hTprimeSet : subgroupPrimeSet T = ({q} : Set Nat.Primes) := by
    have hq_eq : (⟨q.val, Fact.out⟩ : Nat.Primes) = q := Subtype.ext rfl
    simpa [hq_eq] using
      (section8_subgroupPrimeSet_eq_singleton_of_isPGroup_ne_bot
        (G := G) (p := q.val) (H := T) hTp hTne)
  have hqT : q ∈ subgroupPrimeSet T := by
    simp [hTprimeSet]
  rcases hHall with ⟨_hHtop, hHHall⟩
  rcases hTHall with ⟨_hTH, hTHallH⟩
  have hqH : q ∈ subgroupPrimeSet H := by
    have hq_dvd_T : q.val ∣ Nat.card T := by
      simpa [subgroupPrimeSet] using hqT
    exact hq_dvd_T.trans (Subgroup.card_dvd_of_le hTleH)
  have hTsubH_not_idx : ¬ q.val ∣ (T.subgroupOf H).index := by
    intro hqidx
    exact (hTHallH.p_in_pi_of_p_dvd_index q hqidx) hqT
  have hHsubTop_index_eq :
      (H.subgroupOf (⊤ : Subgroup G)).index = H.index := by
    have hmap :
        (H.subgroupOf (⊤ : Subgroup G)).map (⊤ : Subgroup G).subtype = H := by
      ext x
      constructor
      · intro hx
        rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
        simpa [Subgroup.mem_subgroupOf] using hy
      · intro hx
        refine Subgroup.mem_map.mpr ⟨⟨x, by simp⟩, ?_, rfl⟩
        simpa [Subgroup.mem_subgroupOf] using hx
    have hidx :=
      Subgroup.index_map_subtype
        (H := (⊤ : Subgroup G)) (K := H.subgroupOf (⊤ : Subgroup G))
    simpa [hmap] using hidx.symm
  have hH_not_idx : ¬ q.val ∣ H.index := by
    intro hqidx
    exact (hHHall.p_in_pi_of_p_dvd_index q (by
      simpa [hHsubTop_index_eq] using hqidx)) hqH
  have hTsubH_map : (T.subgroupOf H).map H.subtype = T := by
    ext x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      simpa [Subgroup.mem_subgroupOf] using hy
    · intro hx
      refine Subgroup.mem_map.mpr ⟨⟨x, hTleH hx⟩, ?_, rfl⟩
      simpa [Subgroup.mem_subgroupOf] using hx
  have hT_index_eq_H : T.index = (T.subgroupOf H).index * H.index := by
    have hidx := Subgroup.index_map_subtype (H := H) (K := T.subgroupOf H)
    simpa [hTsubH_map] using hidx
  have hTsubM_map : TsubM.map M.subtype = T := by
    ext x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      simpa [TsubM, Subgroup.mem_subgroupOf] using hy
    · intro hx
      refine Subgroup.mem_map.mpr ⟨⟨x, hTleM hx⟩, ?_, rfl⟩
      simpa [TsubM, Subgroup.mem_subgroupOf] using hx
  have hT_index_eq_M : T.index = TsubM.index * M.index := by
    have hidx := Subgroup.index_map_subtype (H := M) (K := TsubM)
    simpa [hTsubM_map] using hidx
  have hTsubM_not_idx : ¬ q.val ∣ TsubM.index := by
    intro hqidxM
    have hqidxT : q.val ∣ T.index := by
      rw [hT_index_eq_M]
      exact dvd_mul_of_dvd_left hqidxM M.index
    have hqidx_prod : q.val ∣ (T.subgroupOf H).index * H.index := by
      simpa [hT_index_eq_H] using hqidxT
    rcases q.property.dvd_or_dvd hqidx_prod with hqTsubH | hqHidx
    · exact hTsubH_not_idx hqTsubH
    · exact hH_not_idx hqHidx
  let P : Sylow q.val M := hTsubM_p.toSylow hTsubM_not_idx
  refine ⟨P, ?_⟩
  calc
    section10AmbientSylowSubgroup M P = TsubM.map M.subtype := by
      simp [P, section10AmbientSylowSubgroup]
    _ = T := hTsubM_map

/-- Corollary 15.4 source core: after reducing to a Sylow subgroup of the
nilpotent Hall subgroup lying in `C_M(S)`, Corollary 15.3(a)'s cyclic
`τ₂(M)` factor forces that Sylow subgroup back into `M_σ`. -/
private theorem CFSG.section15_corollary15_4_centralizer_hall_le_msigma
    {H S T M : Subgroup G} {q : Nat.Primes}
    (hHall : section15HallSubgroupOf H (⊤ : Subgroup G))
    (hM : M ∈ section9MaximalSubgroups G)
    (_hSsigma : S ≤ section10Msigma M)
    (hSne : S ≠ ⊥)
    (hSHallSigma : section15HallSubgroupOf S (section10Msigma M))
    (hTleH : T ≤ H)
    (hTp : IsPGroup q.val T)
    (hTHall : section15HallSubgroupOf T H)
    (hTcent : T ≤ subgroupCentralizerIn M S) :
    T ≤ section10Msigma M := by
  classical
  by_cases hTbot : T = ⊥
  · simp [hTbot]
  have hTleM : T ≤ M := fun x hx => (hTcent hx).1
  rcases section15_corollary15_4_exists_sylow_M_for_hall_subgroup
      (H := H) (T := T) (M := M) (q := q)
      hHall hTleH hTleM hTbot hTp hTHall with
    ⟨P, hPamb⟩
  let C : Subgroup G := subgroupCentralizerIn M S
  let Cσ : Subgroup G := subgroupCentralizerIn (section10Msigma M) S
  have hTleC : T ≤ C := by
    simpa [C] using hTcent
  have hCleM : C ≤ M := fun _ hx => hx.1
  have hCσleC : Cσ ≤ C := by
    intro x hx
    exact ⟨section15_msigma_le hx.1, hx.2⟩
  let Cσloc : Subgroup C := Cσ.subgroupOf C
  rcases section15_corollary15_3_a_hall_factor
      (M := M) (H := S) hM hSne hSHallSigma with
    ⟨X, hXleC, hXcyc, hXτ2, hXHallσc_raw, _hfactor⟩
  let Xsub : Subgroup C := X.subgroupOf C
  have hXHallσc :
      IsHallSubgroup (section10SigmaPrimes M)ᶜ Xsub := by
    simpa [C, Xsub] using hXHallσc_raw
  have hCσ_eq_inf : Cσ = section10Msigma M ⊓ C := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1, ⟨section15_msigma_le hx.1, hx.2⟩⟩
    · intro hx
      exact ⟨hx.1, hx.2.2⟩
  have hC_norm_sigma : C ≤ Subgroup.normalizer (section10Msigma M : Set G) := by
    intro x hx
    exact section15_msigma_le_normalizer (M := M) hx.1
  have hCσHallSigma : IsHallSubgroup (section10SigmaPrimes M) Cσloc := by
    have hInfHall :
        IsHallSubgroup (section10SigmaPrimes M)
          (((section10Msigma M) ⊓ C).subgroupOf C) :=
      section15_isHallSubgroup_inf_subgroupOf_right
        (G := G) (π := section10SigmaPrimes M)
        (H := section10Msigma M) (K := C) hC_norm_sigma
        (theorem_10_2_b (G := G) hM).1
    simpa [Cσloc, hCσ_eq_inf] using hInfHall
  have hC_norm_Cσ : C ≤ Subgroup.normalizer (Cσ : Set G) := by
    have hC_norm_S : C ≤ Subgroup.normalizer (S : Set G) := by
      intro x hx
      exact centralizer_le_normalizer S hx.2
    simpa [Cσ] using
      section15_le_normalizer_subgroupCentralizerIn
        (G := G) (N := C) (E := section10Msigma M) (A := S)
        hC_norm_sigma hC_norm_S
  haveI : Cσloc.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCσleC).2 hC_norm_Cσ
  have hXsubτ2 : IsPiSubgroup (G := C) (section12Tau2Primes M) Xsub := by
    intro r hrX
    have hcard : Nat.card Xsub = Nat.card X :=
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (G := G) (H := X) (K := C) hXleC).toEquiv
    exact hXτ2 r (by simpa [Xsub, hcard] using hrX)
  have hXHallτ2 : IsHallSubgroup (section12Tau2Primes M) Xsub := by
    refine isHallSubgroup_of (G := C) (π := section12Tau2Primes M) (H := Xsub)
      hXsubτ2 ?_
    intro r hrτ2 hridx
    have hr_not_sigma : r ∉ section10SigmaPrimes M := by
      have hrτ2' : r ∉ section10SigmaPrimes M ∧ primeRank r.val M = 2 := by
        simpa [section12Tau2Primes] using hrτ2
      exact hrτ2'.1
    exact (hXHallσc.p_in_pi_of_p_dvd_index r hridx)
      (by simpa [Set.mem_compl_iff] using hr_not_sigma)
  have hcomp : Cσloc.IsComplement' Xsub :=
    section11_isComplement_of_isHall_compl hCσHallSigma hXHallσc
  have hCσHallτ2c : IsHallSubgroup (section12Tau2Primes M)ᶜ Cσloc :=
    section15_isHall_compl_of_isHall_complement hXHallτ2 hcomp.symm
  have hTsubC_p : IsPGroup q.val (T.subgroupOf C) := by
    exact hTp.of_equiv
      (Subgroup.subgroupOfEquivOfLe (G := G) (H := T) (K := C) hTleC).symm
  by_cases hqτ2 : q ∈ section12Tau2Primes M
  · have hTsubCπ : IsPiSubgroup (G := C) (section12Tau2Primes M) (T.subgroupOf C) :=
      section15_isPiSubgroup_of_isPGroup_of_mem hTsubC_p hqτ2
    have hCne_top : C ≠ ⊤ := by
      intro hCtop
      have htop_le_M : (⊤ : Subgroup G) ≤ M := by
        intro x hx
        have hxC : x ∈ C := by
          simp [hCtop]
        exact hCleM hxC
      exact hM.1 (top_le_iff.mp htop_le_M)
    have hCsolv : IsSolvable C :=
      IsMinCE.proper_subgroups_solvable C (lt_top_iff_ne_top.mpr hCne_top)
    letI : MulDistribMulAction Unit C := {
      smul := fun _ x => x
      one_smul := fun _ => rfl
      mul_smul := fun _ _ _ => rfl
      smul_mul := fun _ _ _ => rfl
      smul_one := fun _ => rfl }
    have hTsubCInv : IsInvariant Unit C (T.subgroupOf C) := by
      refine ⟨?_⟩
      intro _ x
      simp [Subgroup.mem_subgroupOf]
    obtain ⟨L, hLHall, _hLInv, hTsubC_le_L⟩ :=
      exists_isHallSubgroup_isInvariant_of_isPiSubgroup
        (G := C) (A := Unit) hCsolv (by simp) (section12Tau2Primes M)
        (T.subgroupOf C) hTsubCπ hTsubCInv
    obtain ⟨c, hc⟩ :=
      exists_conj_eq_of_isHallSubgroup_of_solvable
        (G := C) hCsolv hXHallτ2 hLHall
    have hXsub_cyc : IsCyclic Xsub := by
      exact
        (Subgroup.subgroupOfEquivOfLe (G := G) (H := X) (K := C) hXleC).isCyclic.2
          hXcyc
    have hXconj_cyc :
        IsCyclic (Xsub.map (MulAut.conj c).toMonoidHom) := by
      let e : Xsub ≃* Xsub.map (MulAut.conj c).toMonoidHom :=
        Subgroup.equivMapOfInjective
          (f := (MulAut.conj c).toMonoidHom) Xsub
          (EquivLike.injective (MulAut.conj c))
      exact e.isCyclic.1 hXsub_cyc
    have hTsubC_cyc : IsCyclic (T.subgroupOf C) := by
      have hTsubC_le_conj :
          T.subgroupOf C ≤ Xsub.map (MulAut.conj c).toMonoidHom := by
        simpa [hc] using hTsubC_le_L
      exact Subgroup.isCyclic_of_le hTsubC_le_conj
    have hTsubM_cyc : IsCyclic (T.subgroupOf M) := by
      let eC : T.subgroupOf C ≃* T :=
        Subgroup.subgroupOfEquivOfLe (G := G) (H := T) (K := C) hTleC
      let eM : T.subgroupOf M ≃* T :=
        Subgroup.subgroupOfEquivOfLe (G := G) (H := T) (K := M) hTleM
      exact eM.isCyclic.2 (eC.isCyclic.1 hTsubC_cyc)
    have hP_eq_TsubM : (P : Subgroup M) = T.subgroupOf M := by
      ext y
      constructor
      · intro hyP
        have hyAmb : ((y : M) : G) ∈ section10AmbientSylowSubgroup M P :=
          Subgroup.mem_map_of_mem M.subtype hyP
        have hyT : ((y : M) : G) ∈ T := by
          simpa [hPamb] using hyAmb
        simpa [Subgroup.mem_subgroupOf] using hyT
      · intro hyTsub
        have hyT : ((y : M) : G) ∈ T := by
          simpa [Subgroup.mem_subgroupOf] using hyTsub
        have hyAmb : ((y : M) : G) ∈ section10AmbientSylowSubgroup M P := by
          simpa [hPamb] using hyT
        rcases Subgroup.mem_map.mp hyAmb with ⟨z, hzP, hz_eq⟩
        have hzy : z = y := Subtype.ext (by simpa using hz_eq)
        simpa [hzy] using hzP
    have hPcyc : IsCyclic (P : Subgroup M) := by
      rw [hP_eq_TsubM]
      exact hTsubM_cyc
    have hqRank_le_one : primeRank q.val M ≤ 1 :=
      (section10_primeRank_le_groupRank_sylow (G := M) P).trans
        (groupRank_le_one_of_isCyclic (P : Subgroup M))
    have hqτ2' : q ∉ section10SigmaPrimes M ∧ primeRank q.val M = 2 := by
      simpa [section12Tau2Primes] using hqτ2
    have htwo_le_one : (2 : ℕ) ≤ 1 := by
      rw [hqτ2'.2] at hqRank_le_one
      exact hqRank_le_one
    omega
  · have hqτ2c : q ∈ (section12Tau2Primes M)ᶜ := by
      simpa [Set.mem_compl_iff] using hqτ2
    have hTsubC_le_Cσ : T.subgroupOf C ≤ Cσloc :=
      section15_pSubgroup_le_normal_hall_of_prime_mem
        (R := C) (π := (section12Tau2Primes M)ᶜ) (H := Cσloc)
        (A := T.subgroupOf C) hCσHallτ2c hqτ2c hTsubC_p
    intro x hxT
    have hxC : x ∈ C := hTleC hxT
    let xC : C := ⟨x, hxC⟩
    have hxTsub : xC ∈ T.subgroupOf C := by
      simpa [xC, Subgroup.mem_subgroupOf] using hxT
    have hxCσloc : xC ∈ Cσloc := hTsubC_le_Cσ hxTsub
    exact hxCσloc.1

/-- Corollary 15.4 centralizer step: a Sylow subgroup of the nilpotent Hall
subgroup `H` centralizes the chosen `S`; Corollary 15.3(a) then forces it
into `M_σ`. -/
private theorem CFSG.section15_corollary15_4_centralizing_sylow_le_msigma
    {H S T M : Subgroup G} {p q : Nat.Primes}
    (hHall : section15HallSubgroupOf H (⊤ : Subgroup G))
    (hNil : Group.IsNilpotent H)
    (hSleH : S ≤ H)
    (hSne : S ≠ ⊥)
    (hSp : IsPGroup p.val S)
    (hSHall : section15HallSubgroupOf S H)
    (hM : M ∈ section9MaximalSubgroups G)
    (hNormSleM : Subgroup.normalizer (S : Set G) ≤ M)
    (hSsigma : S ≤ section10Msigma M)
    (hSHallSigma : section15HallSubgroupOf S (section10Msigma M))
    (hTleH : T ≤ H)
    (hTp : IsPGroup q.val T)
    (hTHall : section15HallSubgroupOf T H) :
    T ≤ section10Msigma M := by
  classical
  haveI : Fact p.val.Prime := ⟨p.property⟩
  haveI : Fact q.val.Prime := ⟨q.property⟩
  have hSnormalH : (S.subgroupOf H).Normal :=
    section15_hall_pSubgroup_subgroupOf_normal_of_nilpotent
      (H := H) (S := S) (p := p) hNil hSleH hSne hSp hSHall
  by_cases hqp : q = p
  · subst q
    rcases hSHall with ⟨_hSleH', hSHallH⟩
    have hpS : p ∈ subgroupPrimeSet S := by
      have hSprimeSet : subgroupPrimeSet S = ({p} : Set Nat.Primes) := by
        have hp_eq : (⟨p.val, Fact.out⟩ : Nat.Primes) = p := Subtype.ext rfl
        simpa [hp_eq] using
          (section8_subgroupPrimeSet_eq_singleton_of_isPGroup_ne_bot
            (G := G) (p := p.val) (H := S) hSp hSne)
      simp [hSprimeSet]
    have hTsub_p : IsPGroup p.val (T.subgroupOf H) := by
      exact hTp.of_equiv
        (Subgroup.subgroupOfEquivOfLe (H := T) (K := H) hTleH).symm
    haveI : (S.subgroupOf H).Normal := hSnormalH
    have hTsub_le_Ssub : T.subgroupOf H ≤ S.subgroupOf H :=
      section15_pSubgroup_le_normal_hall_of_prime_mem
        (R := H) (π := subgroupPrimeSet S) (H := S.subgroupOf H)
        (A := T.subgroupOf H) hSHallH hpS hTsub_p
    exact fun x hxT => hSsigma (by
      have hxH : x ∈ H := hTleH hxT
      let xH : H := ⟨x, hxH⟩
      have hxTsub : xH ∈ T.subgroupOf H := by
        simpa [xH, Subgroup.mem_subgroupOf] using hxT
      have hxSsub : xH ∈ S.subgroupOf H := hTsub_le_Ssub hxTsub
      simpa [xH, Subgroup.mem_subgroupOf] using hxSsub)
  · by_cases hTbot : T = ⊥
    · subst T
      exact bot_le
    · have hTHall_saved : section15HallSubgroupOf T H := hTHall
      rcases hTHall with ⟨_hTleH', hTHallH⟩
      have hTnormalH : (T.subgroupOf H).Normal :=
        section15_hall_pSubgroup_subgroupOf_normal_of_nilpotent
          (H := H) (S := T) (p := q) hNil hTleH hTbot hTp hTHall_saved
      have hHleNormS : H ≤ Subgroup.normalizer (S : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hSleH).1 hSnormalH
      have hTleM : T ≤ M := hTleH.trans (hHleNormS.trans hNormSleM)
      have hTsub_q : IsPGroup q.val (T.subgroupOf H) := by
        exact hTp.of_equiv
          (Subgroup.subgroupOfEquivOfLe (H := T) (K := H) hTleH).symm
      have hSsub_p : IsPGroup p.val (S.subgroupOf H) := by
        exact hSp.of_equiv
          (Subgroup.subgroupOfEquivOfLe (H := S) (K := H) hSleH).symm
      have hdisj : Disjoint (S.subgroupOf H) (T.subgroupOf H) :=
        IsPGroup.disjoint_of_ne p.val q.val
          (by
            intro hpq
            exact hqp (Subtype.ext hpq.symm))
          (S.subgroupOf H) (T.subgroupOf H) hSsub_p hTsub_q
      have hTcent : T ≤ subgroupCentralizerIn M S := by
        intro x hxT
        refine ⟨hTleM hxT, ?_⟩
        change x ∈ Subgroup.centralizer (S : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro s hsS
        let sH : H := ⟨s, hSleH hsS⟩
        let xH : H := ⟨x, hTleH hxT⟩
        have hsSsub : sH ∈ S.subgroupOf H := by
          simpa [sH, Subgroup.mem_subgroupOf] using hsS
        have hxTsub : xH ∈ T.subgroupOf H := by
          simpa [xH, Subgroup.mem_subgroupOf] using hxT
        have hcomm :=
          Subgroup.commute_of_normal_of_disjoint
            (S.subgroupOf H) (T.subgroupOf H)
            hSnormalH hTnormalH hdisj sH xH hsSsub hxTsub
        exact congrArg Subtype.val hcomm.eq
      exact section15_corollary15_4_centralizer_hall_le_msigma
        hHall hM hSsigma hSne hSHallSigma hTleH hTp hTHall_saved hTcent

/-- Corollary 15.4 final nilpotent-generation step: once every Sylow subgroup
of `H` is in `M_σ`, nilpotence gives `H ≤ M_σ`. -/
private theorem CFSG.section15_corollary15_4_nilpotent_hall_le_msigma_of_chosen_sylow
    {H S M : Subgroup G} {p : Nat.Primes}
    (_hHne : H ≠ ⊥)
    (hHall : section15HallSubgroupOf H (⊤ : Subgroup G))
    (hNil : Group.IsNilpotent H)
    (hSleH : S ≤ H)
    (hSne : S ≠ ⊥)
    (hSp : IsPGroup p.val S)
    (hSHall : section15HallSubgroupOf S H)
    (hM : M ∈ section9MaximalSubgroups G)
    (hNormSleM : Subgroup.normalizer (S : Set G) ≤ M)
    (hSsigma : S ≤ section10Msigma M)
    (hSHallSigma : section15HallSubgroupOf S (section10Msigma M)) :
    H ≤ section10Msigma M := by
  classical
  let C : Subgroup H := (section10Msigma M).comap H.subtype
  have htop_le_C : (⊤ : Subgroup H) ≤ C := by
    rw [← Sylow.iSup_sylow_eq_top (G := H)]
    refine iSup_le ?_
    intro r
    refine iSup_le ?_
    intro hr
    have hrprime : Nat.Prime r := Nat.prime_of_mem_primeFactors hr
    let q : Nat.Primes := ⟨r, hrprime⟩
    haveI : Fact q.val.Prime := ⟨q.property⟩
    let P : Sylow q.val H := default
    let T : Subgroup G := section10AmbientSylowSubgroup H P
    have hTleH : T ≤ H := by
      intro x hx
      have hxmap : x ∈ (P : Subgroup H).map H.subtype := by
        simpa [T, section10AmbientSylowSubgroup] using hx
      rcases Subgroup.mem_map.mp hxmap with ⟨y, _hy, rfl⟩
      exact y.property
    have hTp : IsPGroup q.val T := by
      change IsPGroup q.val ((P : Subgroup H).map H.subtype)
      exact IsPGroup.map (p := q.val) (H := (P : Subgroup H)) P.isPGroup' H.subtype
    have hTsub_eq : T.subgroupOf H = (P : Subgroup H) := by
      simpa [T, section10AmbientSylowSubgroup] using
        (subgroupOf_map_subtype_eq (K := H) (P : Subgroup H))
    have hTprimeSet : subgroupPrimeSet T ⊆ ({q} : Set Nat.Primes) := by
      intro s hsT
      have hs_dvd_P : s.val ∣ Nat.card (P : Subgroup H) := by
        have hcard : Nat.card (T.subgroupOf H) = Nat.card T :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTleH).toEquiv
        have hs_dvd_sub : s.val ∣ Nat.card (T.subgroupOf H) := by
          simpa [subgroupPrimeSet, hcard] using hsT
        simpa [hTsub_eq] using hs_dvd_sub
      rcases P.isPGroup'.exists_card_eq with ⟨n, hn⟩
      have hs_dvd_pow : s.val ∣ q.val ^ n := by simpa [hn] using hs_dvd_P
      have hs_dvd_q : s.val ∣ q.val := s.property.dvd_of_dvd_pow hs_dvd_pow
      have hs_eq_q : s = q :=
        Subtype.ext ((Nat.prime_dvd_prime_iff_eq s.property q.property).mp hs_dvd_q)
      simp [hs_eq_q]
    have hPprimeSet_subset : subgroupPrimeSet (P : Subgroup H) ⊆ ({q} : Set Nat.Primes) := by
      intro s hsP
      rcases P.isPGroup'.exists_card_eq with ⟨n, hn⟩
      have hs_dvd_pow : s.val ∣ q.val ^ n := by simpa [subgroupPrimeSet, hn] using hsP
      have hs_dvd_q : s.val ∣ q.val := s.property.dvd_of_dvd_pow hs_dvd_pow
      have hs_eq_q : s = q :=
        Subtype.ext ((Nat.prime_dvd_prime_iff_eq s.property q.property).mp hs_dvd_q)
      simp [hs_eq_q]
    have hTHall : section15HallSubgroupOf T H := by
      refine ⟨hTleH, ?_⟩
      rw [hTsub_eq]
      refine isHallSubgroup_of (G := H) (subgroupPrimeSet T) (P : Subgroup H) ?_ ?_
      · intro s hsP
        have hs_q : s ∈ ({q} : Set Nat.Primes) := hPprimeSet_subset (by
          simpa [subgroupPrimeSet] using hsP)
        have hs_eq : s = q := by simpa using hs_q
        subst s
        have hqT : q ∈ subgroupPrimeSet T := by
          have hqP : q.val ∣ Nat.card (P : Subgroup H) :=
            Sylow.dvd_card_of_dvd_card P (by simpa [q] using Nat.dvd_of_mem_primeFactors hr)
          have hcard : Nat.card (T.subgroupOf H) = Nat.card T :=
            Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTleH).toEquiv
          have hqSub : q.val ∣ Nat.card (T.subgroupOf H) := by
            simpa [hTsub_eq] using hqP
          have hqTcard : q.val ∣ Nat.card T := by
            simpa [hcard] using hqSub
          simpa [subgroupPrimeSet] using hqTcard
        exact hqT
      · intro s hsT hsidx
        have hs_q : s ∈ ({q} : Set Nat.Primes) := hTprimeSet hsT
        have hs_eq : s = q := by simpa using hs_q
        subst s
        exact P.not_dvd_index hsidx
    have hT_msigma : T ≤ section10Msigma M :=
      section15_corollary15_4_centralizing_sylow_le_msigma
        hHall hNil hSleH hSne hSp hSHall hM hNormSleM hSsigma hSHallSigma
        hTleH hTp hTHall
    change (P : Subgroup H) ≤ C
    intro y hyP
    change ((y : H) : G) ∈ section10Msigma M
    exact hT_msigma (Subgroup.mem_map_of_mem H.subtype hyP)
  intro x hxH
  have hxC : (⟨x, hxH⟩ : H) ∈ C := htop_le_C trivial
  change x ∈ section10Msigma M at hxC
  exact hxC

/-- Corollary 15.4: every nonidentity nilpotent Hall subgroup of `G` is
contained in `M_σ` for a suitable maximal subgroup `M`. -/
public theorem CFSG.corollary_15_4
    {H : Subgroup G}
    (hHne : H ≠ ⊥)
    (hHall : section15HallSubgroupOf H (⊤ : Subgroup G))
    (hNil : Group.IsNilpotent H) :
    ∃ M : Subgroup G, M ∈ section9MaximalSubgroups G ∧ H ≤ section10Msigma M := by
  rcases section15_corollary15_4_exists_nontrivial_sylow
      hHne hHall hNil with
    ⟨p, S, hSleH, hSne, hSp, hSHall⟩
  rcases section15_corollary15_4_exists_maximal_for_sylow
      hHall hSleH hSne hSp hSHall with
    ⟨M, hMcont, hSsigma, hSHallSigma⟩
  exact
    ⟨M, hMcont.1,
      section15_corollary15_4_nilpotent_hall_le_msigma_of_chosen_sylow
        hHne hHall hNil hSleH hSne hSp hSHall hMcont.1 hMcont.2
        hSsigma hSHallSigma⟩

end Section15
