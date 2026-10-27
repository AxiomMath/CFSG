module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970API
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_17ii
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ControlCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27FittingDecomposition
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection5.theorem_5_5_a
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The `t`-centralization of `F_π(M)` for Lemma 2.7

Bender 1.7(ii) says `O_p(M)` centralizes `O^p(F*(Ĥ))` for every
`p ∈ π(F(Ĥ))`.  Since `t ∈ O₂(Ĥ) ≤ F*(Ĥ)` has order two, it lies in
`O^p(F*(Ĥ))` for every odd `p ∈ π`; hence `t` centralizes each odd `p`-core
of `M`.  Together with centralization of `O₂(M)` this gives
`t ∈ C_G(F_π(M))`.  The nilpotence of `F(M)` is used to decompose
`O_π(F(M))` into its prime-power parts.
-/

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

private theorem piCore_le_iSup_pCore_of_nilpotent
    {G : Type u} [Group G] [Finite G] (π : Set ℕ) (hG : Group.IsNilpotent G)
    (hpi : ∀ p : ℕ, p ∈ (Nat.card (↥(piCore π G))).primeFactors → p ∈ π) :
    piCore π G ≤ ⨆ p ∈ π, pCore p G := by
  classical
  let N : Subgroup G := piCore π G
  have : N.Normal := piCore_normal_local π
  have : Group.IsNilpotent (↥N) := by
    let : Group.IsNilpotent G := hG
    exact Subgroup.isNilpotent N
  have hN_eq : N = ⨆ p ∈ (Nat.card (↥N)).primeFactors,
      ((default : Sylow p (↥N)).map N.subtype) := by
    calc
      N = ((⨆ p ∈ (Nat.card (↥N)).primeFactors,
          ((default : Sylow p (↥N)) : Subgroup (↥N))).map N.subtype) := by
        rw [Sylow.iSup_sylow_eq_top (G := ↥N),
          ← MonoidHom.range_eq_map N.subtype, Subgroup.range_subtype]
      _ = ⨆ p ∈ (Nat.card (↥N)).primeFactors,
          ((default : Sylow p (↥N)).map N.subtype) := by
        simp [Subgroup.map_iSup]
  change N ≤ ⨆ p ∈ π, pCore p G
  rw [hN_eq]
  refine iSup₂_le ?_
  intro p hp
  have hpπ : p ∈ π := hpi p hp
  have : Fact (Nat.Prime p) := ⟨Nat.prime_of_mem_primeFactors hp⟩
  refine le_iSup_of_le p (le_iSup_of_le hpπ ?_)
  exact sylow_map_le_pCore_local
    (G := G) (N := N) (inferInstance : N.Normal) inferInstance
    (default : Sylow p (↥N))

/-- In a nilpotent ambient subgroup, `O_π` is contained in the join of its
prime-power parts. -/
public theorem piCoreOf_le_iSup_qCoreOf_of_isNilpotent
    {G : Type u} [Group G] [Finite G]
    (F : Subgroup G) (π : Set ℕ) (hFnil : Group.IsNilpotent (↥F)) :
    piCoreOf F π ≤ ⨆ p ∈ π, qCoreOf F p := by
  classical
  have hcard : Nat.card (↥(piCore π (↥F))) =
      Nat.card (↥(piCoreOf F π)) := by
    dsimp [piCoreOf]
    exact Nat.card_congr (Subgroup.equivMapOfInjective (piCore π (↥F)) F.subtype
      F.subtype_injective).toEquiv
  have hpi : ∀ p : ℕ, p ∈ (Nat.card (↥(piCore π (↥F)))).primeFactors → p ∈ π := by
    intro p hp
    apply piCoreOf_primeDivisors F π p
    rwa [← hcard]
  have hle : piCore π (↥F) ≤ ⨆ p ∈ π, pCore p (↥F) :=
    piCore_le_iSup_pCore_of_nilpotent (G := ↥F) π hFnil hpi
  have hmap := Subgroup.map_mono (f := F.subtype) hle
  have hmap_eq : ((⨆ p ∈ π, pCore p (↥F)).map F.subtype : Subgroup G) =
      ⨆ p ∈ π, (pCore p (↥F)).map F.subtype := by
    simp [Subgroup.map_iSup]
  change (piCore π (↥F)).map F.subtype ≤
    ⨆ p ∈ π, (pCore p (↥F)).map F.subtype
  rw [← hmap_eq]
  exact hmap

/-- An element centralizing every prime-power part of `O_π(F)` centralizes
`O_π(F)` itself. -/
public theorem mem_centralizer_piCoreOf_of_mem_centralizer_qCores
    {G : Type u} [Group G] [Finite G]
    (F : Subgroup G) (π : Set ℕ) (t : G) (hFnil : Group.IsNilpotent ↥F)
    (h : ∀ p : ℕ, p ∈ π → t ∈ Subgroup.centralizer (qCoreOf F p : Set G)) :
    t ∈ Subgroup.centralizer (piCoreOf F π : Set G) := by
  classical
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hxsup : x ∈ ⨆ p : {p // p ∈ π}, qCoreOf F p.1 := by
    have hxsup' : x ∈ ⨆ p ∈ π, qCoreOf F p :=
      (piCoreOf_le_iSup_qCoreOf_of_isNilpotent F π hFnil) hx
    have hEq : (⨆ p : {p // p ∈ π}, qCoreOf F p.1) =
        (⨆ p ∈ π, qCoreOf F p) :=
      (iSup_subtype' (p := fun p : ℕ => p ∈ π)
        (f := fun p : ℕ => fun _ : p ∈ π => qCoreOf F p)).symm
    rw [hEq]
    exact hxsup'
  rw [Subgroup.iSup_eq_closure] at hxsup
  refine Subgroup.closure_induction'' ?_ ?_ ?_ ?_ hxsup
  · intro y hy
    rcases (Set.mem_iUnion).1 hy with ⟨p, hyp⟩
    have htp : t ∈ Subgroup.centralizer (qCoreOf F p.1 : Set G) := h p.1 p.2
    exact (Subgroup.mem_centralizer_iff.mp htp y hyp)
  · intro y hy
    rcases (Set.mem_iUnion).1 hy with ⟨p, hyp⟩
    have htp : t ∈ Subgroup.centralizer (qCoreOf F p.1 : Set G) := h p.1 p.2
    exact (Subgroup.mem_centralizer_iff.mp htp y⁻¹ ((qCoreOf F p.1).inv_mem hyp))
  · simp
  · intro y z _ _ hy hz
    calc
      (y * z) * t = y * (z * t) := by group
      _ = y * (t * z) := by rw [hz]
      _ = (y * t) * z := by group
      _ = (t * y) * z := by rw [hy]
      _ = t * (y * z) := by group

/-- The Lemma 2.7 centralization input: once `t` centralizes `O₂(M)`,
Bender 1.7(ii) gives `t ∈ C_G(F_π(M))` for `π = π(F(Ĥ))`. -/
public theorem t_centralizes_piCoreOf_fittingSubgroupOf_of_centralizes_twoCore
    {G : Type u} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G) (c : CentralizerSetup G)
    (M : Subgroup G) (hAM : NormalizerControlledBy c.Hhat M)
    (htwo : c.t ∈ Subgroup.centralizer (twoCoreOf M : Set G))
    (htTwo : c.t ∈ twoCoreOf c.Hhat) :
    let π := primesOfOrder (fittingSubgroupOf c.Hhat)
    c.t ∈ Subgroup.centralizer
      (piCoreOf (fittingSubgroupOf M) π : Set G) := by
  classical
  intro π
  have hπprime : ∀ p ∈ π, p.Prime := by
    intro p hp
    simpa [π] using (Nat.prime_of_mem_primeFactors hp)
  have hq2 : qCoreOf M 2 = twoCoreOf M := by
    rw [twoCoreOf_eq_piCoreOf_2, qCoreOf_eq_piCoreOf_singleton M 2 Nat.prime_two]
  have hq : ∀ p : ℕ, p ∈ π → c.t ∈ Subgroup.centralizer (qCoreOf M p : Set G) := by
    intro p hp
    have hpprime : p.Prime := hπprime p hp
    by_cases hp2 : p = 2
    · subst p
      simpa [hq2] using htwo
    · have hpodd : Odd p := hpprime.odd_of_ne_two hp2
      rcases controlCore_of_normalizerControlledBy hAM with
        ⟨S, _hSne, hSF, hSM, hSsub, hCS⟩
      have hcomm : ⁅qCoreOf M p,
          pResidualOf (generalizedFittingSubgroupOf c.Hhat) p⁆ = ⊥ :=
        bender1970_1_7_ii_commutator_pResidual
          hsimple c.Hhat c.Hhat_maximal
          S hSF hSsub hCS hSM p hpprime hp
      have htFstar : c.t ∈ generalizedFittingSubgroupOf c.Hhat := by
        have hle : twoCoreOf c.Hhat ≤ fittingSubgroupOf c.Hhat :=
          qCoreOf_le_fittingSubgroupOf c.Hhat 2 Nat.prime_two
        exact (le_sup_left : fittingSubgroupOf c.Hhat ≤
          generalizedFittingSubgroupOf c.Hhat) (hle htTwo)
      have hord : orderOf c.t = 2 :=
        orderOf_eq_prime c.t_involution.2 c.t_involution.1
      have hcop : Nat.Coprime p (orderOf c.t) := by
        rw [hord]
        exact Nat.coprime_two_right.mpr hpodd
      have htRes : c.t ∈ pResidualOf (generalizedFittingSubgroupOf c.Hhat) p :=
        mem_pResidualOf_of_order_coprime
          (generalizedFittingSubgroupOf c.Hhat) p hpprime htFstar hcop
      have hcomm' : ⁅pResidualOf (generalizedFittingSubgroupOf c.Hhat) p,
          qCoreOf M p⁆ = ⊥ := by
        simpa [Subgroup.commutator_comm] using hcomm
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer
        (H₁ := pResidualOf (generalizedFittingSubgroupOf c.Hhat) p)
        (H₂ := qCoreOf M p)).1 hcomm' htRes
  have hqF : ∀ p : ℕ, p ∈ π → c.t ∈ Subgroup.centralizer
      (qCoreOf (fittingSubgroupOf M) p : Set G) := by
    intro p hp
    have hle : qCoreOf (fittingSubgroupOf M) p ≤ qCoreOf M p :=
      qCoreOf_le_qCoreOf_of_isNormalIn (fittingSubgroupOf M) M p
        (fittingSubgroupOf_isNormalIn M)
    exact (Subgroup.centralizer_le
      (show (qCoreOf (fittingSubgroupOf M) p : Set G) ⊆
        (qCoreOf M p : Set G) from hle)) (hq p hp)
  exact mem_centralizer_piCoreOf_of_mem_centralizer_qCores
    (fittingSubgroupOf M) π c.t (fittingSubgroupOf_isNilpotent M) hqF

/-- `O₂(M)` centralizes the odd part of `F(Ĥ)`, by Bender 1.7(ii) with
`p = 2`: the odd part of `F(Ĥ)` lies in `O²(F*(Ĥ))`. -/
public theorem twoCoreOf_centralizes_oddPart_fittingSubgroupOf_of_control
    {G : Type u} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G) (c : CentralizerSetup G)
    (M : Subgroup G) (hAM : NormalizerControlledBy c.Hhat M)
    (h2π : 2 ∈ primesOfOrder (fittingSubgroupOf c.Hhat)) :
    twoCoreOf M ≤ Subgroup.centralizer
      (piCoreOf (fittingSubgroupOf c.Hhat) {q : ℕ | Odd q} : Set G) := by
  classical
  rcases controlCore_of_normalizerControlledBy hAM with
    ⟨S, _hSne, hSF, hSM, hSsub, hCS⟩
  have hcomm : ⁅qCoreOf M 2,
      pResidualOf (generalizedFittingSubgroupOf c.Hhat) 2⁆ = ⊥ :=
    bender1970_1_7_ii_commutator_pResidual
      hsimple c.Hhat c.Hhat_maximal S hSF hSsub hCS hSM 2 Nat.prime_two h2π
  have hPleC : qCoreOf M 2 ≤ Subgroup.centralizer
      ((pResidualOf (generalizedFittingSubgroupOf c.Hhat) 2 : Subgroup G) : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer
      (H₁ := qCoreOf M 2)
      (H₂ := pResidualOf (generalizedFittingSubgroupOf c.Hhat) 2)).1 hcomm
  let A : Subgroup G :=
    piCoreOf (fittingSubgroupOf c.Hhat) {q : ℕ | Odd q}
  have hAleFstar : A ≤ generalizedFittingSubgroupOf c.Hhat := by
    intro x hx
    exact (le_sup_left : fittingSubgroupOf c.Hhat ≤
      generalizedFittingSubgroupOf c.Hhat) ((piCoreOf_le
        (fittingSubgroupOf c.Hhat) {q : ℕ | Odd q}) hx)
  have hAleR : A ≤ pResidualOf (generalizedFittingSubgroupOf c.Hhat) 2 := by
    intro x hx
    have hxF : x ∈ fittingSubgroupOf c.Hhat :=
      (piCoreOf_le (fittingSubgroupOf c.Hhat) {q : ℕ | Odd q}) hx
    have hxFstar : x ∈ generalizedFittingSubgroupOf c.Hhat :=
      (le_sup_left : fittingSubgroupOf c.Hhat ≤
        generalizedFittingSubgroupOf c.Hhat) hxF
    have hAodd : Odd (Nat.card (↥A)) := by
      rw [← Nat.not_even_iff_odd]
      intro heven
      have h2dvd : 2 ∣ Nat.card (↥A) := even_iff_two_dvd.mp heven
      have h2pf : 2 ∈ (Nat.card (↥A)).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2dvd, Nat.card_pos.ne'⟩
      have h2odd : Odd 2 := by
        simpa using (piCoreOf_primeDivisors
          (fittingSubgroupOf c.Hhat) {q : ℕ | Odd q} 2 h2pf)
      norm_num at h2odd
    have hxodd : Odd (orderOf x) := by
      have hdvd : orderOf x ∣ Nat.card (↥A) := by
        let : Fintype (↥A) := Fintype.ofFinite _
        have h := orderOf_dvd_card (x := (⟨x, hx⟩ : A))
        simpa [Nat.card_eq_fintype_card, Subgroup.orderOf_mk] using h
      exact Odd.of_dvd_nat hAodd hdvd
    exact mem_pResidualOf_of_order_coprime
      (generalizedFittingSubgroupOf c.Hhat) 2 Nat.prime_two hxFstar
      (Nat.coprime_two_left.mpr hxodd)
  have hC : Subgroup.centralizer
      ((pResidualOf (generalizedFittingSubgroupOf c.Hhat) 2 : Subgroup G) : Set G) ≤
    Subgroup.centralizer (A : Set G) :=
    Subgroup.centralizer_le (show (A : Set G) ⊆
      (pResidualOf (generalizedFittingSubgroupOf c.Hhat) 2 : Set G) from hAleR)
  have hPleCA : qCoreOf M 2 ≤ Subgroup.centralizer (A : Set G) := hPleC.trans hC
  have hq2 : qCoreOf M 2 = twoCoreOf M := by
    rw [twoCoreOf_eq_piCoreOf_2, qCoreOf_eq_piCoreOf_singleton M 2 Nat.prime_two]
  simpa [hq2, A] using hPleCA

end CFSG.GorensteinWalter
