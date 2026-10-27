module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSevenCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSevenTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinNoCentralizingInvolution
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinDataComplete
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinIntersectionD6
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddFixedPointFreeKleinFourQuotient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FittingEqSelfOfCardThree
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinConjugateVUIndex
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourCentralizerTransport
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-! The cardinal part of restriction (7).  The printed source also labels the
full intersection as `D₆`; that is incompatible with its order-nine sentence.
The endpoint retained here is the consistent quotient `D/(D ∩ VU) ≃ D₆`. -/

public theorem firstCase_klein_restrictionSeven_card_three
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    {n : ℕ} {y : G} {X : Subgroup G}
    (hyJ : y ∈ firstCaseJ c n)
    (hn : 4 ≤ n)
    (hXne : X ≠ ⊥) (hXle : X ≤ c.Hhat)
    (hXodd : Nat.Coprime 2 (Nat.card X))
    (hXinv : ∀ x : G, x ∈ X → x ∈ invertedElements c.Hhat y)
    (hC_even : Even (Nat.card (Subgroup.centralizer (X : Set G))))
    (hN_even : Even (Nat.card
      ((Subgroup.normalizer (X : Set G) ⊓ c.Hhat : Subgroup G)))) :
    Nat.card c.U = 3 ∧
      (let D := c.Hhat ⊓ conjugateSubgroup c.Hhat y
       let N := D ⊓ (twoCoreOf c.Hhat ⊔ c.U)
       (N.subgroupOf D).index = 6) := by
  have hcore := firstCase_klein_restrictionSeven_core hmin c hfirst hklein
    hyJ hXne hXle hXodd hXinv hC_even hN_even
  have hXcard : Nat.card X = 3 := hcore.1
  have hFUcent : c.FU ≤ Subgroup.centralizer (X : Set G) := hcore.2
  obtain ⟨g, L, hLHall, hLne, hXgL, _hgnot, hNXg, _hFUcentXg⟩ :=
    firstCase_klein_restrictionSeven_transfer hmin c hfirst hklein
      hyJ hXne hXle hXodd hXinv hC_even
  have hmapN :
      conjugateSubgroup (Subgroup.normalizer (X : Set G)) g =
        Subgroup.normalizer (conjugateSubgroup X g : Set G) := by
    change (Subgroup.normalizer (X : Set G)).map
        (MulAut.conj g).toMonoidHom = _
    exact Subgroup.map_normalizer_eq_of_bijective X
      (MulAut.conj g).bijective
  have hNle : Subgroup.normalizer (X : Set G) ≤
      conjugateSubgroup c.Hhat g⁻¹ := by
    intro z hz
    have hzg : g * z * g⁻¹ ∈ c.Hhat := by
      apply hNXg
      rw [← hmapN]
      exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
    apply Subgroup.mem_map.mpr
    refine ⟨g * z * g⁻¹, hzg, ?_⟩
    simpa [MulAut.conj_apply] using
      (show g⁻¹ * (g * z * g⁻¹) * g = z by group)
  have hFUleHconj : c.FU ≤ conjugateSubgroup c.Hhat g⁻¹ := by
    calc
      c.FU ≤ Subgroup.centralizer (X : Set G) := hFUcent
      _ ≤ Subgroup.normalizer (X : Set G) :=
        Subgroup.centralizer_le_normalizer (X : Set G)
      _ ≤ conjugateSubgroup c.Hhat g⁻¹ := hNle
  let V : Subgroup G := twoCoreOf c.Hhat
  let Vg : Subgroup G := conjugateSubgroup V g⁻¹
  let Lg : Subgroup G := conjugateSubgroup L g⁻¹
  have hXleLg : X ≤ Lg := by
    intro x hx
    have hxg : g * x * g⁻¹ ∈ L :=
      hXgL (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
    apply Subgroup.mem_map.mpr
    refine ⟨g * x * g⁻¹, hxg, ?_⟩
    simpa [MulAut.conj_apply] using
      (show g⁻¹ * (g * x * g⁻¹) * g = x by group)
  have hVcentU : V ≤ Subgroup.centralizer (c.U : Set G) := by
    have h26 := theorem_2_6 hmin c
    simpa [V, h26.1] using twoCoreOf_centralizes_oddCoreOf c.Hhat
  have hLleU : L ≤ c.U := hLHall.1.trans (fittingSubgroupOf_le c.U)
  have hVcentL : V ≤ Subgroup.centralizer (L : Set G) :=
    hVcentU.trans (Subgroup.centralizer_le (show (L : Set G) ⊆ (c.U : Set G) from
      fun z hz => hLleU hz))
  have hVgcentLg : Vg ≤ Subgroup.centralizer (Lg : Set G) := by
    change V.map (MulAut.conj g⁻¹).toMonoidHom ≤
      Subgroup.centralizer ((L.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup G) : Set G)
    exact centralizer_map_le_of_conj L V g hVcentL
  have hVgcentX : Vg ≤ Subgroup.centralizer (X : Set G) :=
    hVgcentLg.trans (Subgroup.centralizer_le (show (X : Set G) ⊆ (Lg : Set G) from
      fun z hz => hXleLg hz))
  have hVg_escape : ¬ Vg ≤ c.Hhat := by
    intro hVgH
    have hVgcard : Nat.card Vg = 4 := by
      have hmapcard : Nat.card Vg = Nat.card V := by
        exact Nat.card_congr
          (Subgroup.equivMapOfInjective V (MulAut.conj g⁻¹).toMonoidHom
            (MulAut.conj g⁻¹).injective).toEquiv.symm
      rw [hmapcard]
      simpa [V] using (firstCase_klein_V_klein c hklein).card_four
    have hVgne : Vg ≠ ⊥ := by
      intro hbot
      rw [hbot] at hVgcard
      simp at hVgcard
    obtain ⟨s, hsne⟩ :=
      (Subgroup.ne_bot_iff_exists_ne_one (H := Vg)).mp hVgne
    let sG : G := s
    have hsVg : sG ∈ Vg := s.property
    have hsneG : sG ≠ 1 := by
      intro hs
      apply hsne
      exact Subtype.ext hs
    have hVK : IsKleinFour Vg := by
      change IsKleinFour (V.map (MulAut.conj g⁻¹).toMonoidHom)
      exact isKleinFour_map_mulEquiv V
        (firstCase_klein_V_klein c hklein) (MulAut.conj g⁻¹)
    have hsI : IsInvolution sG := by
      refine ⟨hsneG, ?_⟩
      simpa [pow_two] using congrArg Subtype.val
        (hVK.mul_self ⟨sG, hsVg⟩)
    exact firstCase_klein_no_centralizing_involution_of_inverted_card_three
      hmin c hfirst hklein
      (by simpa [firstCaseJ] using hyJ |>.1)
      (by simpa [firstCaseJ] using hyJ |>.2.1)
      hXne hXle hXodd hXinv hXcard (hVgH hsVg) hsI
      (fun x hx => by
        have hcx := (Subgroup.mem_centralizer_iff.mp (hVgcentX hsVg)) x hx
        rw [← hcx]
        simp)
  have hFfree : c.FU ⊓ Subgroup.centralizer (Vg : Set G) = ⊥ := by
    apply le_bot_iff.mp
    intro z hz
    by_cases hz1 : z = 1
    · exact Subgroup.mem_bot.mpr hz1
    let Q : Subgroup G := Subgroup.zpowers z
    have hQne : Q ≠ ⊥ := by
      intro hQbot
      apply hz1
      have hzQ : z ∈ Q := Subgroup.mem_zpowers z
      rw [hQbot] at hzQ
      exact Subgroup.mem_bot.mp hzQ
    have hQle : Q ≤ c.FU := Subgroup.zpowers_le.mpr hz.1
    have hVgN : Vg ≤ Subgroup.normalizer (Q : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      intro v hv q hq
      rcases Subgroup.mem_zpowers_iff.mp hq with ⟨m, rfl⟩
      have hcomm : v * z = z * v :=
        (Subgroup.mem_centralizer_iff.mp hz.2) v hv
      have hpow : v * z ^ m * v⁻¹ = z ^ m := by
        have hc := (Commute.zpow_right ((commute_iff_eq _ _).2 hcomm) m).eq
        rw [hc]
        simp
      exact Subgroup.mem_zpowers_iff.mpr ⟨m, by simpa [hpow]⟩
    have hQnorm := hfirst.2 Q hQne hQle
    exfalso
    exact hVg_escape (fun v hv => hQnorm (hVgN hv))
  have hUodd : Nat.Coprime 2 (Nat.card c.U) := by
    have h26 := theorem_2_6 hmin c
    rw [h26.1]
    change Nat.Coprime 2 (Nat.card (oddCoreOf c.Hhat))
    rw [show Nat.card (oddCoreOf c.Hhat) = Nat.card (pPrimeCore 2 c.Hhat) by
      simpa [oddCoreOf] using
        (Subgroup.card_map_of_injective (K := pPrimeCore 2 c.Hhat)
          c.Hhat.subtype_injective)]
    exact pPrimeCore_coprime_card (p := 2) (G := c.Hhat)
  have hFodd : Odd (Nat.card c.FU) :=
    Odd.of_dvd_nat (Nat.coprime_two_left.mp hUodd)
      (Subgroup.card_dvd_of_le (fittingSubgroupOf_le c.U))
  have hFne : c.FU ≠ ⊥ := by
    obtain ⟨_d, K, hKHall, hKne, _hKall⟩ :=
      firstCase_klein_data_complete hmin c hfirst hklein
    intro hFUbot
    apply hKne
    apply le_antisymm
    · intro k hk
      exact hFUbot ▸ (hKHall.1 hk)
    · exact bot_le
  have hVgleH : Vg ≤ conjugateSubgroup c.Hhat g⁻¹ := by
    exact Subgroup.map_mono (show V ≤ c.Hhat from by
      dsimp [V]
      exact Subgroup.map_subtype_le (pCore 2 c.Hhat))
  have hUgleH : conjugateSubgroup c.U g⁻¹ ≤ conjugateSubgroup c.Hhat g⁻¹ := by
    exact Subgroup.map_mono (show c.U ≤ c.Hhat from by
      exact (theorem_2_6 hmin c).1 ▸
        Subgroup.map_subtype_le (pPrimeCore 2 c.Hhat))
  have hVgnorm : IsNormalIn Vg (conjugateSubgroup c.Hhat g⁻¹) := by
    refine ⟨hVgleH, ?_⟩
    intro h hh v hv
    rcases Subgroup.mem_map.mp hv with ⟨v0, hv0, rfl⟩
    rcases Subgroup.mem_map.mp hh with ⟨h0, hh0, rfl⟩
    refine Subgroup.mem_map.mpr ⟨h0 * v0 * h0⁻¹, ?_, ?_⟩
    · have hVnorm : IsNormalIn V c.Hhat := by
        refine ⟨Subgroup.map_subtype_le (pCore 2 c.Hhat), ?_⟩
        intro a ha b hb
        rcases Subgroup.mem_map.mp hb with ⟨b0, hb0, rfl⟩
        exact Subgroup.mem_map.mpr ⟨
          (⟨a, ha⟩ : c.Hhat) * b0 * (⟨a, ha⟩ : c.Hhat)⁻¹,
          (pCore_normal (p := 2) (G := c.Hhat)).conj_mem b0 hb0
            (⟨a, ha⟩ : c.Hhat), by simp⟩
      exact hVnorm.2 h0 hh0 v0 hv0
    · simpa [MulAut.conj_apply] using
        (show g⁻¹ * (h0 * v0 * h0⁻¹) * g =
          (g⁻¹ * h0 * g) * (g⁻¹ * v0 * g) *
            (g⁻¹ * h0 * g)⁻¹ by group)
  have hUgnorm : IsNormalIn (conjugateSubgroup c.U g⁻¹)
      (conjugateSubgroup c.Hhat g⁻¹) := by
    refine ⟨hUgleH, ?_⟩
    intro h hh u hu
    rcases Subgroup.mem_map.mp hu with ⟨u0, hu0, rfl⟩
    rcases Subgroup.mem_map.mp hh with ⟨h0, hh0, rfl⟩
    have hUnorm : IsNormalIn c.U c.Hhat := by
      have h26 := theorem_2_6 hmin c
      rw [h26.1]
      refine ⟨?_, ?_⟩
      · intro x hx
        rcases Subgroup.mem_map.mp hx with ⟨u, hu, rfl⟩
        exact u.2
      · intro h hh u hu
        rcases Subgroup.mem_map.mp hu with ⟨u0, hu0, rfl⟩
        refine Subgroup.mem_map.mpr ⟨
          (⟨h, hh⟩ : c.Hhat) * u0 * (⟨h, hh⟩ : c.Hhat)⁻¹,
          ?_, by simp⟩
        exact (pPrimeCore_normal (p := 2) (G := c.Hhat)).conj_mem
          u0 hu0 (⟨h, hh⟩ : c.Hhat)
    refine Subgroup.mem_map.mpr ⟨h0 * u0 * h0⁻¹,
      hUnorm.2 h0 hh0 u0 hu0, ?_⟩
    simpa [MulAut.conj_apply] using
      (show g⁻¹ * (h0 * u0 * h0⁻¹) * g =
        (g⁻¹ * h0 * g) * (g⁻¹ * u0 * g) *
          (g⁻¹ * h0 * g)⁻¹ by group)
  have hVUcent : Vg ≤ Subgroup.centralizer
      (conjugateSubgroup c.U g⁻¹ : Set G) := by
    change V.map (MulAut.conj g⁻¹).toMonoidHom ≤
      Subgroup.centralizer ((c.U.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup G) : Set G)
    exact centralizer_map_le_of_conj c.U V g hVcentU
  have hVKg : IsKleinFour Vg := by
    change IsKleinFour (V.map (MulAut.conj g⁻¹).toMonoidHom)
    exact isKleinFour_map_mulEquiv V
      (firstCase_klein_V_klein c hklein) (MulAut.conj g⁻¹)
  have hUoddg : Odd (Nat.card (conjugateSubgroup c.U g⁻¹)) := by
    have hcard : Nat.card (conjugateSubgroup c.U g⁻¹) = Nat.card c.U := by
      exact Nat.card_congr
        (Subgroup.equivMapOfInjective c.U (MulAut.conj g⁻¹).toMonoidHom
          (MulAut.conj g⁻¹).injective).toEquiv.symm
    rw [hcard]
    exact Nat.coprime_two_left.mp hUodd
  have hFcard : Nat.card c.FU = 3 := by
    apply odd_fixedPointFree_subgroup_card_three_of_kleinFour_quotient
      (conjugateSubgroup c.Hhat g⁻¹) Vg
      (conjugateSubgroup c.U g⁻¹) c.FU
      hVgleH hUgleH hVgnorm hUgnorm hVKg hUoddg hVUcent
      hFUleHconj hFodd hFne hFfree
      (by
        simpa [Vg, V, conjugateSubgroup, Subgroup.map_sup] using
          firstCase_klein_conjugate_VU_index_six hmin c hfirst hklein g)
  have hFUeq : c.FU = c.U :=
    fittingSubgroupOf_eq_self_of_card_three c.U hUodd hFcard
  have hUcard : Nat.card c.U = 3 := by
    rw [← hFUeq]
    exact hFcard
  have hyI : IsInvolution y := by
    simpa [firstCaseJ] using hyJ |>.1
  have hyH : y ∉ c.Hhat := by
    simpa [firstCaseJ] using hyJ |>.2.1
  have hI : 4 ≤ Nat.card {x : G // x ∈ invertedElements c.Hhat y} := by
    rw [← firstCase_klein_coset_involution_card_eq c hyI hyH]
    have hcoset : firstCaseCosetInvolutions c y = n := by
      simpa [firstCaseJ] using hyJ |>.2.2
    rw [hcoset]
    exact hn
  have hidx := firstCase_klein_restrictionSix_index_eq
    hmin c hfirst hklein hyI hyH hI
  exact ⟨hUcard, hidx⟩

end CFSG.GorensteinWalter
