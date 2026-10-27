module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoNormalForm
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Theorem76
import CFSG.GroupTheory.PGroup.ElemAbelianSq
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
import CFSG.SignalizerFunctorTheorem.Inheritance.Diagonal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace CaseTwoTransitive

variable {c : Ctx812E G} (t : CaseTwoTransitive c)

private theorem exists_orderOf_three_mem_S_centralizer_y :
    ∃ z ∈ t.d.S, z ∈ Subgroup.centralizer ({t.y} : Set G) ∧ orderOf z = 3 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hbase : CFSG.GroupTheory.WreathThree.base (t.d.H 0) t.y = t.d.S := t.base_eq
  have hcardD0 : Nat.card (t.d.S ⊓ Subgroup.centralizer ({t.y} : Set G) : Subgroup G) =
      Nat.card (t.d.H 0) := by
    calc Nat.card (t.d.S ⊓ Subgroup.centralizer ({t.y} : Set G) : Subgroup G)
        = Nat.card (CFSG.GroupTheory.WreathThree.base (t.d.H 0) t.y ⊓
            Subgroup.centralizer ({t.y} : Set G) : Subgroup G) := by rw [hbase]
      _ = Nat.card (t.d.H 0) :=
          CFSG.GroupTheory.WreathThree.card_base_inf_centralizer t.isWreathThree t.hy3
            (Subgroup.mem_sup_right (Subgroup.mem_zpowers t.y))
            (CFSG.GroupTheory.WreathThree.not_mem_base t.isWreathThree)
  have hH0p : IsPGroup 3 (t.d.H 0) := t.d.hS.isPGroup.to_le (t.d.H_le_S 0)
  obtain ⟨a, ha⟩ := hH0p.exists_card_eq
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h0 | hpos
    · exfalso
      apply t.d.H_ne_bot 0
      apply Subgroup.card_eq_one.mp
      rw [ha, h0, pow_zero]
    · exact hpos
  have hcardD : Nat.card (t.d.S ⊓ Subgroup.centralizer ({t.y} : Set G) : Subgroup G) =
      3 ^ a := by
    rw [hcardD0, ha]
  have hdvdD : 3 ∣ Nat.card (t.d.S ⊓ Subgroup.centralizer ({t.y} : Set G) : Subgroup G) := by
    rw [hcardD]
    exact dvd_pow_self 3 (by omega)
  obtain ⟨zD, hzD⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(t.d.S ⊓ Subgroup.centralizer ({t.y} : Set G))) 3 hdvdD
  exact ⟨(zD : G), zD.2.1, zD.2.2, (Subgroup.orderOf_coe zD).trans hzD⟩

theorem centralizer_y_le_of_two_le_pRank {p : ℕ}
    (hp : p ∈ c.sig)
    (hSE : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.StronglyEmbeddedFive)
    (h2 : 2 ≤ CFSG.Open.pRank p (c.S.M ⊓ Subgroup.centralizer ({t.y} : Set G))) :
    Subgroup.centralizer ({t.y} : Set G) ≤ c.S.M := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hHM
  let H : Subgroup G := Subgroup.centralizer ({t.y} : Set G)
  let Q : Subgroup G := CFSG.Open.pCoreOf 2 c.S.M
  have hHM' : ¬ H ≤ c.S.M := by simpa [H] using hHM
  have hH_ne_top : H ≠ ⊤ := by
    intro htop
    haveI : IsSimpleGroup G := c.standing.simple
    have hycenter : t.y ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ H := by rw [htop]; exact Subgroup.mem_top g
      exact Subgroup.mem_centralizer_singleton_iff.mp hg
    have hcenter : Subgroup.center G = ⊥ :=
      CFSG.SignalizerFunctorTheorem.Diagonal.center_eq_bot c.standing.nonab
    have hy1 : t.y = 1 := by
      have hybot : t.y ∈ (⊥ : Subgroup G) := by rwa [hcenter] at hycenter
      exact Subgroup.mem_bot.mp hybot
    have hord := t.orderOf_y
    rw [hy1, orderOf_one] at hord
    omega
  have hconfig : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Sec7Core4.Config
      (c.toSec7Core4 hp) H := by
    refine ⟨hH_ne_top, hHM', ?_⟩
    change 2 ≤ CFSG.Open.pRank p (H ⊓ c.S.M)
    simpa [H, inf_comm] using h2
  have hQH : Q ⊓ H = ⊥ :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Sec7Core4.step74
      (c.toSec7Core4 hp) (c.five_le_of_mem_sigma hp) c.three_not_mem_beta hSE H hconfig
  obtain ⟨z, hzS, hzC, hzord⟩ := t.exists_orderOf_three_mem_S_centralizer_y
  have hSL : t.d.S ≤ c.L := by
    rw [← t.hdL]
    exact t.d.hS.le
  have hzM : z ∈ c.S.M := c.hyp81.1 (hSL hzS)
  have hyM : t.y ∈ c.S.M := t.hP.le t.hyP
  have hyS : t.y ∉ t.d.S := by
    rw [← t.base_eq]
    exact CFSG.GroupTheory.WreathThree.not_mem_base t.isWreathThree
  have hy_not_z : t.y ∉ Subgroup.zpowers z := by
    intro hyz
    exact hyS (Subgroup.zpowers_le.mpr hzS hyz)
  have hSP : t.d.S ≤ t.P := by
    rw [t.hdS]
    exact inf_le_left
  let E : Subgroup G := Subgroup.zpowers z ⊔ Subgroup.zpowers t.y
  have hzy : ∀ a ∈ Subgroup.zpowers z, a * t.y = t.y * a := by
    intro a ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    have hcz : Commute z t.y := Subgroup.mem_centralizer_singleton_iff.mp hzC
    exact (hcz.zpow_left n).eq
  have hpair := CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute
    (r := 3) (X := Subgroup.zpowers z) (v := t.y)
    (by rw [Nat.card_zpowers, hzord]) t.orderOf_y hy_not_z hzy
  have hEelt : CFSG.Open.IsElemAbelian 3 E := hpair.1
  have hEcard : Nat.card E = 3 ^ 2 := hpair.2
  have hEM : E ≤ c.S.M := by
    change Subgroup.zpowers z ⊔ Subgroup.zpowers t.y ≤ c.S.M
    exact sup_le (Subgroup.zpowers_le.mpr hzM) (Subgroup.zpowers_le.mpr hyM)
  have hEnorm : E ≤ Subgroup.normalizer (Q : Set G) :=
    hEM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 c.S.M)
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 c.S.M
  have hQcoprime : Nat.Coprime 3 (Nat.card Q) := by
    obtain ⟨n, hn⟩ := hQ2.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right n
      ((Nat.coprime_primes Nat.prime_three Nat.prime_two).mpr (by norm_num))
  have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity
    (p := 3) Nat.prime_three (A := E) (X := Q) hEelt (by rw [hEcard]) hEnorm hQcoprime
  have hstep4 : ∀ e ∈ E, e ≠ 1 → e ∉ Subgroup.zpowers z →
      Q ⊓ Subgroup.centralizer ({e} : Set G) = ⊥ := by
    intro e heE he1 hez
    have heP : e ∈ t.P := by
      have hEP : E ≤ t.P := by
        change Subgroup.zpowers z ⊔ Subgroup.zpowers t.y ≤ t.P
        exact sup_le ((Subgroup.zpowers_le.mpr hzS).trans hSP)
          (Subgroup.zpowers_le.mpr t.hyP)
      exact hEP heE
    have he3 : e ^ 3 = 1 := hEelt.2 e heE
    have heS : e ∉ t.d.S := by
      intro heS
      let F : Subgroup G := E ⊓ t.d.S
      have hzF : Subgroup.zpowers z ≤ F := by
        intro w hw
        exact ⟨Subgroup.mem_sup_left hw, Subgroup.zpowers_le.mpr hzS hw⟩
      have heF : e ∈ F := ⟨heE, heS⟩
      have hFdvd : Nat.card F ∣ Nat.card E := Subgroup.card_dvd_of_le inf_le_left
      have hFcard_gt : 3 < Nat.card F := by
        by_contra hle
        have hle' : Nat.card F ≤ 3 := le_of_not_gt hle
        have hFz : F = Subgroup.zpowers z :=
          (Subgroup.eq_of_le_of_card_ge hzF (by
            rw [Nat.card_zpowers, hzord]
            exact hle')).symm
        exact hez (hFz ▸ heF)
      have hFcard9 : Nat.card F = 3 ^ 2 := by
        obtain ⟨k, hk_le, hk_card⟩ :=
          (Nat.dvd_prime_pow (p := 3) (m := 2) (i := Nat.card F) Nat.prime_three).mp (by
            rw [hEcard] at hFdvd
            exact hFdvd)
        have hk_cases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
        rcases hk_cases with hk0 | hk1 | hk2
        · rw [hk0] at hk_card
          rw [hk_card] at hFcard_gt
          norm_num at hFcard_gt
        · rw [hk1] at hk_card
          rw [hk_card] at hFcard_gt
          norm_num at hFcard_gt
        · rw [hk2] at hk_card
          exact hk_card
      have hFE : F = E := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hEcard, hFcard9])
      have hyF : t.y ∈ F := by
        rw [hFE]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t.y)
      exact hyS hyF.2
    rcases t.mem_AA_or_exists_conj_eq heP he3 with heA | ⟨s, hsS, hs⟩
    · exact absurd (t.d.AA_le_S heA) heS
    · rw [eq_bot_iff]
      rintro q ⟨hqQ, hqC⟩
      have hqe : q * e = e * q := Subgroup.mem_centralizer_singleton_iff.mp hqC
      have hsM : s ∈ c.S.M := c.hyp81.1 (hSL hsS)
      have hQnorm : c.S.M ≤ Subgroup.normalizer (Q : Set G) :=
        CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 c.S.M
      have hqQ' : s * q * s⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (hQnorm hsM) q).mp hqQ
      have hconj : (s * q * s⁻¹) * (s * e * s⁻¹) =
          (s * e * s⁻¹) * (s * q * s⁻¹) := by
        calc (s * q * s⁻¹) * (s * e * s⁻¹) = s * (q * e) * s⁻¹ := by group
          _ = s * (e * q) * s⁻¹ := by rw [hqe]
          _ = (s * e * s⁻¹) * (s * q * s⁻¹) := by group
      have hCy : s * q * s⁻¹ ∈ Subgroup.centralizer ({t.y} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        rcases hs with hs | hs
        · rwa [hs] at hconj
        · rw [hs] at hconj
          have hc : Commute (s * q * s⁻¹) t.y⁻¹ := hconj
          simpa using hc.inv_right.eq
      have hq'bot : s * q * s⁻¹ = 1 := by
        have hmem : s * q * s⁻¹ ∈ (⊥ : Subgroup G) := by
          simpa [hQH] using (show s * q * s⁻¹ ∈ Q ⊓ H from ⟨hqQ', hCy⟩)
        exact Subgroup.mem_bot.mp hmem
      rw [Subgroup.mem_bot]
      calc q = s⁻¹ * (s * q * s⁻¹) * s := by group
        _ = 1 := by rw [hq'bot]; group
  have hQleCz : Q ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [← hgen]
    refine iSup_le fun a => iSup_le fun haE => iSup_le fun ha1 => ?_
    by_cases haz : a ∈ Subgroup.zpowers z
    · have hCeq : Subgroup.centralizer ({a} : Set G) =
          Subgroup.centralizer ({z} : Set G) := by
        have hzp : Subgroup.zpowers a = Subgroup.zpowers z := by
          have hdvd : orderOf a ∣ 3 := by
            rw [← hzord]
            exact orderOf_dvd_of_mem_zpowers haz
          have haord : orderOf a = 3 := by
            rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
            · exact absurd (orderOf_eq_one_iff.mp h1) ha1
            · exact h3
          refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr haz) ?_
          rw [Nat.card_zpowers, Nat.card_zpowers, haord, hzord]
        calc Subgroup.centralizer ({a} : Set G)
            = Subgroup.centralizer (Subgroup.zpowers a : Set G) := by
              rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
          _ = Subgroup.centralizer (Subgroup.zpowers z : Set G) := by rw [hzp]
          _ = Subgroup.centralizer ({z} : Set G) := by
              rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      rw [hCeq]
      exact inf_le_right
    · have hbot : Q ⊓ Subgroup.centralizer ({a} : Set G) = ⊥ := hstep4 a haE ha1 haz
      rw [hbot]
      exact bot_le
  have hzCQ : z ∈ Subgroup.centralizer (Q : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact Subgroup.mem_centralizer_singleton_iff.mp (hQleCz hq)
  have hzQ : z ∈ Q := c.standing.charTwo c.S.M c.S.maxLocal.1 ⟨hzM, hzCQ⟩
  have hz2 : IsPGroup 2 (Subgroup.zpowers z) :=
    hQ2.to_le (Subgroup.zpowers_le.mpr hzQ)
  obtain ⟨n, hn⟩ := hz2.exists_card_eq
  rw [Nat.card_zpowers, hzord] at hn
  rcases n with _ | m
  · norm_num at hn
  · have hdvd : 2 ∣ 3 := by
      rw [hn]
      exact dvd_pow_self 2 (Nat.succ_ne_zero m)
    norm_num at hdvd

end CaseTwoTransitive

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
