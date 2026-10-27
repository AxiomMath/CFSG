module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970API
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ControlCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27Infra
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27TwoCoreInHhat
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Theorem26
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.MinimalCounterexample
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma22
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# `O₂(M) = 1` for Lemma 2.7

The paper's final normalizer step: once `O₂(M) ≤ O₂(Ĥ)`, a nontrivial
`O₂(M)` is impossible.  When `O₂(Ĥ)` is cyclic this follows from
characteristicity in the cyclic subgroup; when it is a Klein four, every
involution there is conjugate to `t` inside `Ĥ`, so the order-two normal
subgroup `O₂(M)` has centralizer (hence normalizer) inside `Ĥ`.
-/

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

private local instance fact_prime_two : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- `O₂(N)` is normal in `N`, in ambient form. -/
private theorem twoCoreOf_isNormalIn {G : Type u} [Group G]
    (N : Subgroup G) : IsNormalIn (twoCoreOf N) N := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases (Subgroup.mem_map).1 hx with ⟨f, _hf, hfx⟩
    rw [← hfx]
    change (f : G) ∈ N
    simp
  · intro h hh k hk
    rcases (Subgroup.mem_map).1 hk with ⟨f, hf, hfk⟩
    rw [← hfk]
    have hconj : (⟨h, hh⟩ : ↥N) * f * (⟨h, hh⟩ : ↥N)⁻¹ ∈ pCore 2 N :=
      (pCore_normal (G := N)).conj_mem (n := f) hf (g := ⟨h, hh⟩)
    refine Subgroup.mem_map.mpr ⟨(⟨h, hh⟩ : ↥N) * f * (⟨h, hh⟩ : ↥N)⁻¹, hconj, ?_⟩
    rw [hfk]
    simpa using hfk

/-- `S0` has order `2^m`. -/
private theorem natCard_S0_eq_two_pow {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) :
    Nat.card (↥c.S0) = 2 ^ c.m := by
  have hcardS : Nat.card (↥(c.S : Subgroup G)) = 2 * 2 ^ c.m := by
    rcases c.dihedralEquiv with ⟨e⟩
    calc
      Nat.card (↥(c.S : Subgroup G)) = Nat.card (DihedralGroup (2 ^ c.m)) := by
        exact Nat.card_congr e.toEquiv
      _ = 2 * 2 ^ c.m := by
        rw [Nat.card_eq_fintype_card]
        exact DihedralGroup.card
  have hindex : Nat.card (↥(c.S : Subgroup G)) = 2 * Nat.card (↥c.S0) :=
    c.S_index_two
  rw [hcardS] at hindex
  exact (Nat.mul_left_cancel (by norm_num : 0 < 2) hindex).symm

/-- From `CentralizerStructure`, `O₂(Ĥ) ≤ S`. -/
private theorem twoCoreOf_Hhat_le_S_of_centralizerStructure
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (h26 : CentralizerStructure c) :
    twoCoreOf c.Hhat ≤ (c.S : Subgroup G) := by
  rw [← h26.2.1]
  exact inf_le_left

/-- If `t ∉ O₂(M)`, then `4 ∤ |O₂(M)|`. -/
private theorem not_four_dvd_twoCoreOf_of_not_mem_t
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (M : Subgroup G)
    (hM : Lemma27Hypothesis c M) (h26 : CentralizerStructure c)
    (htPnot : c.t ∉ twoCoreOf M) :
    ¬ 4 ∣ Nat.card (↥(twoCoreOf M)) := by
  intro h4
  let N : Subgroup (↥M) := (twoCoreOf M).subgroupOf M
  have hNnormal : N.Normal := by
    have hnorm : IsNormalIn (twoCoreOf M) M := twoCoreOf_isNormalIn M
    exact Subgroup.normal_subgroupOf_of_le_normalizer (H := M) (N := twoCoreOf M)
      (le_normalizer_of_isNormalIn hnorm)
  have hPleM : twoCoreOf M ≤ M := Subgroup.map_subtype_le (H := M) (pCore 2 M)
  have h4N : 4 ∣ Nat.card N := by
    have hcard : Nat.card N = Nat.card (↥(twoCoreOf M)) :=
      (Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe (H := twoCoreOf M) (K := M) hPleM).toEquiv)
    rwa [hcard]
  have htN := normal_subgroup_of_card_div_four_contains_t hmin c M hM h26 hNnormal h4N
  have hmap : N.map M.subtype = twoCoreOf M :=
    Subgroup.map_subgroupOf_eq_of_le hPleM
  have htP : c.t ∈ twoCoreOf M := by
    simpa [hmap] using htN
  exact htPnot htP

/-- A nontrivial `2`-group whose order is not divisible by four has order
two. -/
private theorem card_twoCoreOf_eq_two_of_ne_bot_of_not_four_dvd
    {G : Type u} [Group G] [Finite G]
    (M : Subgroup G) (hPne : twoCoreOf M ≠ ⊥)
    (hnot4 : ¬ 4 ∣ Nat.card (↥(twoCoreOf M))) :
    Nat.card (↥(twoCoreOf M)) = 2 := by
  have hPp : IsPGroup 2 (twoCoreOf M) := by
    have hq2 : qCoreOf M 2 = twoCoreOf M := by
      rw [twoCoreOf_eq_piCoreOf_2, qCoreOf_eq_piCoreOf_singleton M 2 Nat.prime_two]
    exact (qCoreOf_isPGroup M 2).of_equiv (MulEquiv.subgroupCongr hq2)
  rcases (IsPGroup.iff_card (p := 2) (G := twoCoreOf M)).mp hPp with ⟨n, hn⟩
  have hnpos : 1 ≤ n := by
    by_contra h
    have hn0 : n = 0 := by omega
    have hcard1 : Nat.card (↥(twoCoreOf M)) = 1 := by simpa [hn0] using hn
    have hbot : twoCoreOf M = ⊥ := Subgroup.eq_bot_of_card_eq (H := twoCoreOf M) hcard1
    exact hPne hbot
  have hnle1 : n ≤ 1 := by
    by_contra h
    have hn2 : 2 ≤ n := by omega
    have h4 : 4 ∣ Nat.card (↥(twoCoreOf M)) := by
      rw [hn]
      exact pow_dvd_pow 2 hn2
    exact hnot4 h4
  have hn1 : n = 1 := by omega
  rw [hn, hn1]
  norm_num

/-- A subgroup of order two has a nonidentity element. -/
private theorem exists_ne_one_mem_of_card_eq_two
    {G : Type u} [Group G] [Finite G]
    (P : Subgroup G) (hcard : Nat.card (↥P) = 2) :
    ∃ u : G, u ∈ P ∧ u ≠ 1 := by
  rcases (Nat.card_eq_two_iff.mp hcard) with ⟨x, y, hxy, _huniv⟩
  by_cases hx1 : x = 1
  · refine ⟨(y : P), y.2, ?_⟩
    intro hy1
    apply hxy
    rw [hx1]
    ext
    exact hy1.symm
  · exact ⟨(x : P), x.2, by
      intro hx1'
      exact hx1 (Subtype.ext hx1')⟩

/-- `O₂(M) = 1` under the Lemma 2.7 hypotheses. -/
public theorem twoCoreOf_eq_bot_of_Lemma27Hypothesis
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (M : Subgroup G)
    (hM : Lemma27Hypothesis c M) :
    twoCoreOf M = ⊥ := by
  classical
  rcases theorem_2_6 hmin c with h26
  rcases hM with ⟨hMproper, hControl, hMnotle, hEt, hSylow, hBranch⟩
  by_contra hPne
  have hPleO2H : twoCoreOf M ≤ twoCoreOf c.Hhat :=
    twoCoreOf_le_twoCoreOf_Hhat_of_Lemma27Hypothesis hmin c M
      ⟨hMproper, hControl, hMnotle, hEt, hSylow, hBranch⟩ h26
  by_cases htP : c.t ∈ twoCoreOf M
  · rcases h26.2.2 with hfirst | hsecond
    · have hPleS0 : twoCoreOf M ≤ c.S0 := hPleO2H.trans hfirst.1
      have hNleH : Subgroup.normalizer (twoCoreOf M : Set G) ≤ c.H := by
        intro g hg
        rw [c.H_eq_centralizer, Subgroup.mem_centralizer_iff]
        intro y hy
        have hyt : y = c.t := by simpa using hy
        rw [hyt]
        have hconj : g * c.t * g⁻¹ ∈ twoCoreOf M :=
          (Subgroup.mem_normalizer_iff.mp hg c.t).mp htP
        have hconjS0 : g * c.t * g⁻¹ ∈ c.S0 := hPleS0 hconj
        let x : ↥c.S0 := ⟨g * c.t * g⁻¹, hconjS0⟩
        let z : ↥c.S0 := ⟨c.t, c.t_mem_S0⟩
        have hx1 : x ≠ 1 := by
          intro hx
          apply c.t_involution.1
          have hxval : g * c.t * g⁻¹ = 1 := by
            simpa [x] using congrArg Subtype.val hx
          calc
            c.t = g⁻¹ * (g * c.t * g⁻¹) * g := by group
            _ = g⁻¹ * 1 * g := by rw [hxval]
            _ = 1 := by simp
        have hx2 : x ^ 2 = 1 := by
          apply Subtype.ext
          have ht2 : c.t * c.t = 1 := by
            simpa [pow_two] using c.t_involution.2
          calc
            (g * c.t * g⁻¹) ^ 2 = g * (c.t * c.t) * g⁻¹ := by
              rw [pow_two]
              group
            _ = g * 1 * g⁻¹ := by rw [ht2]
            _ = 1 := by simp
        have hz1 : z ≠ 1 := by
          intro hz
          apply c.t_involution.1
          simpa [z] using congrArg Subtype.val hz
        have hz2 : z ^ 2 = 1 := by
          apply Subtype.ext
          simpa [z, pow_two] using c.t_involution.2
        have hxz : x = z :=
          unique_involution_of_cyclic_two_group c.S0_cyclic c.one_le_m
            (natCard_S0_eq_two_pow c) x z hx1 hx2 hz1 hz2
        have hconj_eq : g * c.t * g⁻¹ = c.t := by
          simpa [x, z] using congrArg Subtype.val hxz
        have h2 : g⁻¹ * c.t * g = c.t := by
          calc
            g⁻¹ * c.t * g = g⁻¹ * (g * c.t * g⁻¹) * g := by rw [hconj_eq]
            _ = c.t := by group
        have hcomm : c.t * g = g * c.t := by
          calc
            c.t * g = g * (g⁻¹ * c.t * g) := by group
            _ = g * c.t := by rw [h2]
        exact hcomm
      have hNleHhat : Subgroup.normalizer (twoCoreOf M : Set G) ≤ c.Hhat := by
        rw [hfirst.2]
        exact hNleH
      have hMleN : M ≤ Subgroup.normalizer (twoCoreOf M : Set G) :=
        le_normalizer_of_isNormalIn (twoCoreOf_isNormalIn M)
      exact hMnotle (hMleN.trans hNleHhat)
    · have hVK4 : IsKleinFour (twoCoreOf c.Hhat) := by
        let eN : pCore 2 c.Hhat ≃* twoCoreOf c.Hhat :=
          Subgroup.equivMapOfInjective (pCore 2 c.Hhat) c.Hhat.subtype
            c.Hhat.subtype_injective
        exact {
          card_four := (Nat.card_congr eN.toEquiv).symm.trans hsecond.1.card_four
          exponent_two :=
            (Monoid.exponent_eq_of_mulEquiv eN).symm.trans hsecond.1.exponent_two
        }
      by_cases hPV : twoCoreOf M = twoCoreOf c.Hhat
      · have hHleN : c.Hhat ≤ Subgroup.normalizer (twoCoreOf M : Set G) := by
          rw [hPV]
          exact le_normalizer_of_isNormalIn (twoCoreOf_isNormalIn c.Hhat)
        have hMleN : M ≤ Subgroup.normalizer (twoCoreOf M : Set G) :=
          le_normalizer_of_isNormalIn (twoCoreOf_isNormalIn M)
        have hNneTop : Subgroup.normalizer (twoCoreOf M : Set G) ≠ ⊤ := by
          intro htop
          have hPnormal : (twoCoreOf M).Normal :=
            (Subgroup.normalizer_eq_top_iff).mp htop
          rcases (haveI := hPnormal; (minimalCounterexample_isSimple hmin).eq_bot_or_eq_top_of_normal
              (twoCoreOf M)) with hPbot | hPtop
          · exact hPne hPbot
          · have hPleHhat : twoCoreOf M ≤ c.Hhat :=
              hPleO2H.trans (twoCoreOf_isNormalIn c.Hhat).1
            have hHhattop : c.Hhat = ⊤ := top_unique (by
              intro x hx
              exact hPleHhat (hPtop ▸ hx))
            exact c.Hhat_maximal.1 hHhattop
        have hN_eq : Subgroup.normalizer (twoCoreOf M : Set G) = c.Hhat :=
          (c.Hhat_maximal.ne_top_iff_eq hHleN).mp hNneTop
        exact hMnotle (hMleN.trans (by rw [hN_eq]))
      · have hPcard2 : Nat.card (↥(twoCoreOf M)) = 2 := by
          have hPleV : twoCoreOf M ≤ twoCoreOf c.Hhat := hPleO2H
          have hcard_ne4 : Nat.card (↥(twoCoreOf M)) ≠ 4 := by
            intro hc
            apply hPV
            exact Subgroup.eq_of_le_of_card_ge hPleV (by
              rw [hVK4.card_four]
              exact le_of_eq hc.symm)
          have hPp : IsPGroup 2 (twoCoreOf M) := by
            have hq2 : qCoreOf M 2 = twoCoreOf M := by
              rw [twoCoreOf_eq_piCoreOf_2, qCoreOf_eq_piCoreOf_singleton M 2 Nat.prime_two]
            exact (qCoreOf_isPGroup M 2).of_equiv (MulEquiv.subgroupCongr hq2)
          rcases (IsPGroup.iff_card (p := 2) (G := twoCoreOf M)).mp hPp with ⟨n, hn⟩
          have hnpos : 1 ≤ n := by
            by_contra h
            have hn0 : n = 0 := by omega
            have hcard1 : Nat.card (↥(twoCoreOf M)) = 1 := by simpa [hn0] using hn
            have hbot : twoCoreOf M = ⊥ := Subgroup.eq_bot_of_card_eq (H := twoCoreOf M) hcard1
            exact hPne hbot
          have hnle1 : n ≤ 1 := by
            have hcard_le : Nat.card (↥(twoCoreOf M)) ≤ 4 := by
              have hle := Subgroup.card_le_of_le hPleV
              rwa [hVK4.card_four] at hle
            have hnle2 : n ≤ 2 := by
              by_contra h
              have hn3 : 3 ≤ n := by omega
              have hge8 : 8 ≤ 2 ^ n := by
                calc
                  8 = 2 ^ 3 := by norm_num
                  _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num : 0 < 2) hn3
              have hle4 : 2 ^ n ≤ 4 := by
                rw [← hn]
                exact hcard_le
              omega
            have hn_ne2 : n ≠ 2 := by
              intro hn2'
              apply hcard_ne4
              rw [hn, hn2']
              norm_num
            omega
          have hn1 : n = 1 := by omega
          rw [hn, hn1]
          norm_num
        have hPzp : twoCoreOf M = Subgroup.zpowers c.t := by
          have htp : c.t ∈ twoCoreOf M := htP
          have hle : Subgroup.zpowers c.t ≤ twoCoreOf M :=
            Subgroup.zpowers_le.mpr htp
          have hord : orderOf c.t = 2 := orderOf_eq_prime
            c.t_involution.2 c.t_involution.1
          have hle2 : Nat.card (↥(twoCoreOf M)) ≤ Nat.card (Subgroup.zpowers c.t) := by
            rw [hPcard2, Nat.card_zpowers, hord]
          exact (Subgroup.eq_of_le_of_card_ge hle hle2).symm
        have hNleH : Subgroup.normalizer (twoCoreOf M : Set G) ≤ c.H := by
          intro g hg
          rw [c.H_eq_centralizer, Subgroup.mem_centralizer_iff]
          intro y hy
          have hyt : y = c.t := by simpa using hy
          rw [hyt]
          have hconj : g * c.t * g⁻¹ ∈ twoCoreOf M :=
            (Subgroup.mem_normalizer_iff.mp hg c.t).mp htP
          rw [hPzp] at hconj
          rcases Subgroup.mem_zpowers_iff.mp hconj with ⟨k, hk⟩
          have hk2 : c.t ^ k = 1 ∨ c.t ^ k = c.t := by
            have hord : orderOf c.t = 2 := orderOf_eq_prime
              c.t_involution.2 c.t_involution.1
            rw [← zpow_mod_orderOf, hord]
            rcases Int.emod_two_eq_zero_or_one k with hk0 | hk1
            · left
              change k % (2 : ℤ) = 0 at hk0
              simp [hk0]
            · right
              change k % (2 : ℤ) = 1 at hk1
              simp [hk1]
          have hne : g * c.t * g⁻¹ ≠ 1 := by
            intro h1
            apply c.t_involution.1
            calc
              c.t = g⁻¹ * (g * c.t * g⁻¹) * g := by group
              _ = g⁻¹ * 1 * g := by rw [h1]
              _ = 1 := by simp
          rcases hk2 with hk1' | hkt
          · have : g * c.t * g⁻¹ = 1 := hk.symm.trans hk1'
            exfalso
            exact hne this
          · have hconj_eq : g * c.t * g⁻¹ = c.t := hk.symm.trans hkt
            have h2 : g⁻¹ * c.t * g = c.t := by
              calc
                g⁻¹ * c.t * g = g⁻¹ * (g * c.t * g⁻¹) * g := by rw [hconj_eq]
                _ = c.t := by group
            have hcomm : c.t * g = g * c.t := by
              calc
                c.t * g = g * (g⁻¹ * c.t * g) := by group
                _ = g * c.t := by rw [h2]
            exact hcomm
        have hMleN : M ≤ Subgroup.normalizer (twoCoreOf M : Set G) :=
          le_normalizer_of_isNormalIn (twoCoreOf_isNormalIn M)
        exact hMnotle (hMleN.trans (hNleH.trans c.H_le_Hhat))
  · have hnot4 : ¬ 4 ∣ Nat.card (↥(twoCoreOf M)) :=
      not_four_dvd_twoCoreOf_of_not_mem_t hmin c M
        ⟨hMproper, hControl, hMnotle, hEt, hSylow, hBranch⟩ h26 htP
    have hPcard2 : Nat.card (↥(twoCoreOf M)) = 2 :=
      card_twoCoreOf_eq_two_of_ne_bot_of_not_four_dvd M hPne hnot4
    obtain ⟨u, huP, hu_ne⟩ := exists_ne_one_mem_of_card_eq_two (twoCoreOf M) hPcard2
    have huInv : IsInvolution u := by
      let : Fintype (↥(twoCoreOf M)) := Fintype.ofFinite _
      have hord_dvd : orderOf u ∣ Nat.card (↥(twoCoreOf M)) := by
        have h := orderOf_dvd_card (x := (⟨u, huP⟩ : twoCoreOf M))
        have h' : orderOf u ∣ Fintype.card (↥(twoCoreOf M)) := by
          simpa [Subgroup.orderOf_mk] using h
        simpa [Nat.card_eq_fintype_card] using h'
      have hord_ne1 : orderOf u ≠ 1 := by
        intro hord
        have hu1 : u = 1 := (orderOf_eq_one_iff).mp hord
        exact hu_ne hu1
      have hord2 : orderOf u = 2 := by
        rw [hPcard2] at hord_dvd
        have hle : orderOf u ≤ 2 := Nat.le_of_dvd (by norm_num) hord_dvd
        have hpos : 0 < orderOf u := orderOf_pos u
        have hne1 : orderOf u ≠ 1 := by
          intro h
          apply hord_ne1 h
        omega
      exact ⟨hu_ne, by
        have hord_dvd2 : orderOf u ∣ 2 := by rwa [hPcard2] at hord_dvd
        exact (orderOf_dvd_iff_pow_eq_one).mp hord_dvd2⟩
    have huord : orderOf u = 2 :=
      orderOf_eq_prime (by simpa [pow_two] using huInv.2) hu_ne
    have huO2H : u ∈ twoCoreOf c.Hhat := hPleO2H huP
    rcases h26.2.2 with hfirst | hsecond
    · -- `O₂(Ĥ) ≤ S0` cyclic: every nontrivial subgroup contains the unique
      -- involution `t`, so `t ∈ O₂(M)`.
      have hcyc : IsCyclic (↥(twoCoreOf c.Hhat)) := by
        let : IsCyclic c.S0 := c.S0_cyclic
        exact Subgroup.isCyclic_of_le (H := twoCoreOf c.Hhat) (H' := c.S0) hfirst.1
      have hPp : IsPGroup 2 (twoCoreOf c.Hhat) := by
        have hq2 : qCoreOf c.Hhat 2 = twoCoreOf c.Hhat := by
          rw [twoCoreOf_eq_piCoreOf_2, qCoreOf_eq_piCoreOf_singleton c.Hhat 2 Nat.prime_two]
        exact (qCoreOf_isPGroup c.Hhat 2).of_equiv (MulEquiv.subgroupCongr hq2)
      rcases (IsPGroup.iff_card (p := 2) (G := twoCoreOf c.Hhat)).mp hPp with ⟨n, hn⟩
      have hnpos : 1 ≤ n := by
        by_contra h
        have hn0 : n = 0 := by omega
        have hcard1 : Nat.card (↥(twoCoreOf c.Hhat)) = 1 := by simpa [hn0] using hn
        have hbot : twoCoreOf c.Hhat = ⊥ :=
          Subgroup.eq_bot_of_card_eq (H := twoCoreOf c.Hhat) hcard1
        have hu1 : u = 1 := by
          have huBot : u ∈ (⊥ : Subgroup G) := by
            rw [← hbot]
            exact huO2H
          exact Subgroup.mem_bot.mp huBot
        exact hu_ne hu1
      have htH : c.t ∈ twoCoreOf c.Hhat := centralizerStructure_t_mem_twoCore c h26
      have hxz : (⟨u, huO2H⟩ : twoCoreOf c.Hhat) = ⟨c.t, htH⟩ :=
        unique_involution_of_cyclic_two_group hcyc hnpos hn
          (⟨u, huO2H⟩) (⟨c.t, htH⟩)
          (by
            intro h
            apply hu_ne
            exact congrArg Subtype.val h)
          (by
            apply Subtype.ext
            simpa [pow_two] using huInv.2)
          (by
            intro h
            apply c.t_involution.1
            exact congrArg Subtype.val h)
          (by
            apply Subtype.ext
            simpa [pow_two] using c.t_involution.2)
      have hu_eq_t : u = c.t := congrArg Subtype.val hxz
      have htPmem : c.t ∈ twoCoreOf M := hu_eq_t ▸ huP
      exact htP htPmem
    · -- `O₂(Ĥ)` is a Klein four: every involution there is conjugate to `t`
      -- inside `Ĥ`, so `C_G(u) ≤ Ĥ`.  Since `O₂(M)` has order two and is
      -- normal in `M`, the normalizer of `O₂(M)` is `C_G(u)`, forcing
      -- `M ≤ Ĥ`, contradiction.
      have hO2Hne : twoCoreOf c.Hhat ≠ ⊥ := by
        intro hbot
        have hPbot : pCore 2 c.Hhat = ⊥ :=
          (Subgroup.map_eq_bot_iff_of_injective (H := pCore 2 c.Hhat)
            (f := c.Hhat.subtype) c.Hhat.subtype_injective).1 hbot
        have hcard : Nat.card (↥(pCore 2 c.Hhat)) =
            Nat.card (↥(⊥ : Subgroup (↥c.Hhat))) := by
          rw [hPbot]
        have hcard1 : Nat.card (↥(⊥ : Subgroup (↥c.Hhat))) = 1 := by
          simp
        have hcard4 : Nat.card (↥(pCore 2 c.Hhat)) = 4 := hsecond.1.card_four
        omega
      have hUne : c.U ≠ ⊥ := (lemma_2_2 hmin c).2
      have hNorm : Subgroup.normalizer (c.U : Set G) = c.Hhat :=
        theorem26_normalizer_U_eq_Hhat hmin c hO2Hne hUne
      have hPleC : twoCoreOf M ≤ Subgroup.centralizer (c.U : Set G) :=
        twoCoreOf_centralizes_U_of_Lemma27Hypothesis hmin c M
          ⟨hMproper, hControl, hMnotle, hEt, hSylow, hBranch⟩ h26
      have hPleS : twoCoreOf M ≤ (c.S : Subgroup G) :=
        hPleO2H.trans (twoCoreOf_Hhat_le_S_of_centralizerStructure c h26)
      have huC : u ∈ (c.S : Subgroup G) ⊓ Subgroup.centralizer (c.U : Set G) :=
        ⟨hPleS huP, hPleC huP⟩
      have htTwo : c.t ∈ twoCoreOf c.Hhat := centralizerStructure_t_mem_twoCore c h26
      have htC : c.t ∈ (c.S : Subgroup G) ⊓ Subgroup.centralizer (c.U : Set G) := by
        rw [← h26.2.1] at htTwo
        exact htTwo
      obtain ⟨g, hgH, hgut⟩ :=
        theorem26_involutions_in_C_conjugate hmin c hNorm huInv c.t_involution huC htC
      have hCuleH : Subgroup.centralizer ({u} : Set G) ≤ c.Hhat := by
        intro x hx
        have hxu : x * u = u * x := (Subgroup.mem_centralizer_singleton_iff.mp hx)
        have hu_eq : u = g⁻¹ * c.t * g := by
          calc
            u = g⁻¹ * (g * u * g⁻¹) * g := by group
            _ = g⁻¹ * c.t * g := by rw [hgut]
        have ht_eq : c.t = g * u * g⁻¹ := by
          calc
            c.t = g * (g⁻¹ * c.t * g) * g⁻¹ := by group
            _ = g * u * g⁻¹ := by rw [hu_eq]
        have hyC : g * x * g⁻¹ ∈ Subgroup.centralizer ({c.t} : Set G) := by
          rw [Subgroup.mem_centralizer_singleton_iff]
          calc
            (g * x * g⁻¹) * c.t = (g * x * g⁻¹) * (g * u * g⁻¹) := by rw [ht_eq]
            _ = g * (x * u) * g⁻¹ := by group
            _ = g * (u * x) * g⁻¹ := by rw [hxu]
            _ = (g * u * g⁻¹) * (g * x * g⁻¹) := by group
            _ = c.t * (g * x * g⁻¹) := by rw [ht_eq]
        have hyH : g * x * g⁻¹ ∈ c.H := by
          rw [c.H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
          rw [Subgroup.mem_centralizer_singleton_iff] at hyC
          exact hyC
        have hxH : x ∈ c.Hhat := by
          have hprod : g⁻¹ * ((g * x * g⁻¹) * g) ∈ c.Hhat :=
            c.Hhat.mul_mem (c.Hhat.inv_mem hgH)
              (c.Hhat.mul_mem (c.H_le_Hhat hyH) hgH)
          simpa [mul_assoc] using hprod
        exact hxH
      have hMleC : M ≤ Subgroup.centralizer ({u} : Set G) := by
        intro m hm
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hconj : m * u * m⁻¹ ∈ twoCoreOf M :=
          (twoCoreOf_isNormalIn M).2 m hm u huP
        have hPzp : twoCoreOf M = Subgroup.zpowers u := by
          have hle : Subgroup.zpowers u ≤ twoCoreOf M := Subgroup.zpowers_le.mpr huP
          have hle2 : Nat.card (↥(twoCoreOf M)) ≤ Nat.card (Subgroup.zpowers u) := by
            rw [hPcard2, Nat.card_zpowers, huord]
          exact (Subgroup.eq_of_le_of_card_ge hle hle2).symm
        have hconjzp : m * u * m⁻¹ ∈ Subgroup.zpowers u := by
          rwa [hPzp] at hconj
        rcases Subgroup.mem_zpowers_iff.mp hconjzp with ⟨k, hk⟩
        have hk2 : u ^ k = 1 ∨ u ^ k = u := by
          rw [← zpow_mod_orderOf, huord]
          rcases Int.emod_two_eq_zero_or_one k with hk0 | hk1
          · left
            change k % (2 : ℤ) = 0 at hk0
            simp [hk0]
          · right
            change k % (2 : ℤ) = 1 at hk1
            simp [hk1]
        have hne1 : m * u * m⁻¹ ≠ 1 := by
          intro h1
          apply hu_ne
          calc
            u = m⁻¹ * (m * u * m⁻¹) * m := by group
            _ = m⁻¹ * 1 * m := by rw [h1]
            _ = 1 := by simp
        rcases hk2 with hk1' | hku
        · have hconj1 : m * u * m⁻¹ = 1 := hk.symm.trans hk1'
          exfalso
          exact hne1 hconj1
        · have hconj_eq : m * u * m⁻¹ = u := hk.symm.trans hku
          calc
            m * u = (m * u * m⁻¹) * m := by group
            _ = u * m := by rw [hconj_eq]
      exact hMnotle (hMleC.trans hCuleH)

end CFSG.GorensteinWalter
