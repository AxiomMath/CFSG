module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinHighFiber
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSevenCardThree
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSevenNLeU
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixFiberSplit
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinOddCoreOrderThree
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinIntersectionOddCoreRelIndex
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinNoCentralizingInvolution
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinDataComplete
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.InvertedElementsLeInfConjugate
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSevenNormalizerIntersection
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.KleinFourCentralizerWitness
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCorePInfPg
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PrimeOrderSubgroupIntersection
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG
noncomputable section
open scoped Pointwise
namespace CFSG.GorensteinWalter
universe u

set_option maxHeartbeats 1000000 in
public theorem firstCase_klein_restrictionSeven_exact
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    {n : ℕ} {y : G} {X : Subgroup G}
    (hyJ : y ∈ firstCaseJ c n)
    (hn : 4 ≤ n) (hXne : X ≠ ⊥) (hXle : X ≤ c.Hhat)
    (hXodd : Nat.Coprime 2 (Nat.card X))
    (hXinv : ∀ x : G, x ∈ X → x ∈ invertedElements c.Hhat y)
    (hC_even : Even (Nat.card (Subgroup.centralizer (X : Set G))))
    (hN_even : Even (Nat.card ((Subgroup.normalizer (X : Set G) ⊓ c.Hhat : Subgroup G)))) :
    n = 4 := by
  classical
  have hy : IsInvolution y := by simpa [firstCaseJ] using hyJ |>.1
  have hyH : y ∉ c.Hhat := by simpa [firstCaseJ] using hyJ |>.2.1
  have hI : 4 ≤ Nat.card {z : G // z ∈ invertedElements c.Hhat y} := by
    rw [← firstCase_klein_coset_involution_card_eq c hy hyH]
    simpa [firstCaseJ] using hyJ |>.2.2 ▸ hn
  have hidx := firstCase_klein_restrictionSix_index_eq hmin c hfirst hklein hy hyH hI
  have hOidx := firstCase_klein_intersection_oddCore_index_two_of_index_six
    hmin c hfirst hklein hy hyH hidx
  have hrel := firstCase_klein_intersection_oddCore_relIndex_three
    hmin c hfirst hklein hy hyH hidx
  have hcardU := (firstCase_klein_restrictionSeven_card_three
    hmin c hfirst hklein hyJ hn hXne hXle hXodd hXinv hC_even hN_even).1
  have hcore := firstCase_klein_restrictionSeven_core
    hmin c hfirst hklein hyJ hXne hXle hXodd hXinv hC_even hN_even
  have hFUeq : c.FU = c.U := by
    have hFUle := fittingSubgroupOf_le c.U
    have hFUne : c.FU ≠ ⊥ := by
      obtain ⟨_, K, hKHall, hKne, _⟩ := firstCase_klein_data_complete hmin c hfirst hklein
      intro hbot
      apply hKne
      apply le_antisymm
      · intro k hk; exact hbot ▸ hKHall.1 hk
      · exact bot_le
    have hdvd : Nat.card c.FU ∣ 3 := by rw [← hcardU]; exact Subgroup.card_dvd_of_le hFUle
    have hle : Nat.card c.FU ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
    have hne1 : Nat.card c.FU ≠ 1 := by intro h; exact hFUne (Subgroup.eq_bot_of_card_eq c.FU h)
    have hcard : Nat.card c.FU = 3 := by interval_cases h : Nat.card c.FU <;> simp_all
    exact Subgroup.eq_of_le_of_card_ge hFUle (by rw [hcard, hcardU])
  have hHcard : Nat.card c.H = 8 * Nat.card c.U := by
    have hSU : (c.S : Subgroup G) ⊔ c.U = c.H :=
      fact_2_preamble_H_eq_SU hmin c
    have hUnorm : IsNormalIn c.U c.H := by
      change IsNormalIn (oddCoreOf c.H) c.H
      refine ⟨?_, ?_⟩
      · intro x hx
        rcases Subgroup.mem_map.mp hx with ⟨u, hu, rfl⟩
        exact u.2
      · intro h hh u hu
        rcases Subgroup.mem_map.mp hu with ⟨u0, hu0, rfl⟩
        refine Subgroup.mem_map.mpr ⟨
          (⟨h, hh⟩ : c.H) * u0 * (⟨h, hh⟩ : c.H)⁻¹, ?_, by simp⟩
        exact (pPrimeCore_normal (p := 2) (G := c.H)).conj_mem
          u0 hu0 (⟨h, hh⟩ : c.H)
    have hSleH : (c.S : Subgroup G) ≤ c.H := centralizerSetup_S_le_H c
    have hSnormU : (c.S : Subgroup G) ≤ Subgroup.normalizer (c.U : Set G) :=
      hSleH.trans (le_normalizer_of_isNormalIn hUnorm)
    have hUcop : Nat.Coprime 2 (Nat.card c.U) := by
      change Nat.Coprime 2 (Nat.card (oddCoreOf c.H))
      rw [show Nat.card (oddCoreOf c.H) = Nat.card (pPrimeCore 2 c.H) by
        simpa [oddCoreOf] using
          (Subgroup.card_map_of_injective (K := pPrimeCore 2 c.H)
            c.H.subtype_injective)]
      exact pPrimeCore_coprime_card (p := 2) (G := c.H)
    have hScop : Nat.Coprime (Nat.card (c.S : Subgroup G)) (Nat.card c.U) := by
      have hSpow : ∃ k : ℕ, Nat.card (c.S : Subgroup G) = 2 ^ k := by
        obtain ⟨e⟩ := c.dihedralEquiv
        have hcard : Nat.card (c.S : Subgroup G) = 2 * 2 ^ c.m :=
          (Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card
        refine ⟨c.m + 1, ?_⟩
        calc
          Nat.card (c.S : Subgroup G) = 2 * 2 ^ c.m := hcard
          _ = 2 ^ (c.m + 1) := by rw [pow_succ]; ring
      obtain ⟨k, hk⟩ := hSpow
      rw [hk]
      exact hUcop.pow_left _
    have hdisj : Disjoint (c.S : Subgroup G) c.U :=
      Subgroup.disjoint_of_coprime_natCard hScop
    rw [← hSU]
    rw [sup_comm (c.S : Subgroup G) c.U]
    rw [card_sup_eq_mul_of_disjoint_of_le_normalizer (G := G)
      c.U (c.S : Subgroup G) hSnormU hdisj.symm]
    rw [firstCase_klein_S_card hmin c hfirst hklein]
    ring
  have hNleU := firstCase_klein_restrictionSeven_N_le_U hmin c hfirst hklein hy hyH hidx
  -- restriction six gives the two odd fibres
  obtain ⟨s, x, hsI, hsD, hsy, hfib⟩ := firstCase_klein_restrictionSix_order_three
    hmin c hfirst hklein hy hyH hI
  let D : Subgroup G := c.Hhat ⊓ conjugateSubgroup c.Hhat y
  let N : Subgroup G := D ⊓ (twoCoreOf c.Hhat ⊔ c.U)
  let O : Subgroup G := oddCoreOf D
  have hNleU' : N ≤ c.U := by
    simpa [D, N] using hNleU
  have hOidx' : (O.subgroupOf D).index = 2 := by
    simpa [D, O] using hOidx
  have hrel' : N.relIndex O = 3 := by
    simpa [D, N, O] using hrel
  have hInvEq : Nat.card {z : G // z ∈ invertedElements D y} =
      Nat.card {z : G // z ∈ invertedElements c.Hhat y} := by
    let f : {z : G // z ∈ invertedElements c.Hhat y} →
        {z : G // z ∈ invertedElements D y} := fun z =>
      let hzD := invertedElements_subset_inf_conjugateSubgroup c.Hhat y z.2
      ⟨z.1, ⟨⟨hzD.1, hzD.2⟩, z.2.2⟩⟩
    have hf : Function.Bijective f := by
      constructor
      · intro a b hab
        apply Subtype.ext
        simpa using congrArg (fun q => (q.1 : G)) hab
      · intro z
        exact ⟨⟨z.1, ⟨(show z.1 ∈ c.Hhat from (inf_le_left : D ≤ c.Hhat) z.2.1), z.2.2⟩⟩, rfl⟩
    exact Nat.card_congr (Equiv.ofBijective f hf).symm
  have hsplit := firstCase_klein_restrictionSix_fiber_card_split D O
    (by
      dsimp [O]
      exact Subgroup.map_subtype_le (pPrimeCore 2 (↥D)))
    (by simpa [D, O] using hOidx)
    (by exact Nat.coprime_two_left.mpr (odd_card_oddCoreOf D))
    hy hsI hsD hsy
  have hsplit' : Nat.card {z : G // z ∈ invertedElements c.Hhat y} =
      Nat.card {z : G // z ∈ invertedElements O y} +
        Nat.card {z : G // z ∈ invertedElements O (s * y)} := by
    rw [← hInvEq]
    exact hsplit
  have hYle3 : Nat.card {z : G // z ∈ invertedElements O y} ≤ 3 := by
    by_cases hY1 : Nat.card {z : G // z ∈ invertedElements O y} = 1
    · omega
    · exact le_of_eq (firstCase_klein_oddCore_inverted_card_three
        hmin c hfirst hklein hy hyH hidx hY1)
  have hSYcard3 : ∀ hSY1 : Nat.card {z : G // z ∈ invertedElements O (s * y)} ≠ 1,
      Nat.card {z : G // z ∈ invertedElements O (s * y)} = 3 := by
    intro hSY1
    let w : G := s * y
    have hwH : w ∉ c.Hhat := by
      intro hw
      apply hyH
      have hyEq : y = s⁻¹ * w := by simp [w]
      rw [hyEq]
      exact c.Hhat.mul_mem
        (c.Hhat.inv_mem ((inf_le_left : D ≤ c.Hhat) hsD)) hw
    have hwI : IsInvolution w := by
      refine ⟨?_, ?_⟩
      · intro hw1
        apply hwH
        simpa [hw1] using c.Hhat.one_mem
      · dsimp [w]
        have hs2 : s * s = 1 := by simpa [pow_two] using hsI.2
        have hy2 : y * y = 1 := by simpa [pow_two] using hy.2
        calc
          (s * y) ^ 2 = s * (y * s) * y := by simp [pow_two, mul_assoc]
          _ = s * (s * y) * y := by rw [hsy]
          _ = (s * s) * (y * y) := by group
          _ = 1 := by rw [hs2, hy2]; simp
    have hconjEq : conjugateSubgroup c.Hhat w =
        conjugateSubgroup c.Hhat y := by
      dsimp [w, conjugateSubgroup]
      rw [hsy]
      exact map_conj_mul_right_eq_of_mem_normalizer y
        ⟨s, Subgroup.le_normalizer ((inf_le_left : D ≤ c.Hhat) hsD)⟩
    have hI_w : 4 ≤ Nat.card {z : G // z ∈ invertedElements c.Hhat w} := by
      rw [← firstCase_klein_coset_involution_card_eq c hwI hwH]
      have hcardw := firstCase_klein_coset_representative_card_eq c
        ((inf_le_left : D ≤ c.Hhat) hsD) hy hsy hsI hyH
      rw [hcardw]
      rw [show firstCaseCosetInvolutions c y = n by
        simpa [firstCaseJ] using hyJ |>.2.2]
      exact hn
    have hidxW := firstCase_klein_restrictionSix_index_eq
      (y := w) hmin c hfirst hklein hwI hwH hI_w
    have hSY1' : Nat.card {z : G // z ∈ invertedElements
        (oddCoreOf (c.Hhat ⊓ conjugateSubgroup c.Hhat w : Subgroup G)) w} ≠ 1 := by
      simpa [O, hconjEq, w] using hSY1
    have hcardW := firstCase_klein_oddCore_inverted_card_three
      hmin c hfirst hklein hwI hwH hidxW hSY1'
    have hcardW' : Nat.card {z : G // z ∈ invertedElements O w} = 3 := by
      simpa [O, hconjEq] using hcardW
    simpa [w] using hcardW'
  have hSYle3 : Nat.card {z : G // z ∈ invertedElements O (s * y)} ≤ 3 := by
    by_cases hSY1 : Nat.card {z : G // z ∈ invertedElements O (s * y)} = 1
    · omega
    · exact (hSYcard3 hSY1).le
  have hYcases : Nat.card {z : G // z ∈ invertedElements O y} = 1 ∨
      Nat.card {z : G // z ∈ invertedElements O y} = 3 := by
    by_cases hY1 : Nat.card {z : G // z ∈ invertedElements O y} = 1
    · exact Or.inl hY1
    · exact Or.inr (firstCase_klein_oddCore_inverted_card_three
        hmin c hfirst hklein hy hyH hidx hY1)
  have hSYcases : Nat.card {z : G // z ∈ invertedElements O (s * y)} = 1 ∨
      Nat.card {z : G // z ∈ invertedElements O (s * y)} = 3 := by
    by_cases hSY1 : Nat.card {z : G // z ∈ invertedElements O (s * y)} = 1
    · exact Or.inl hSY1
    · exact Or.inr (hSYcard3 hSY1)
  have hcoset : firstCaseCosetInvolutions c y = n := by
    simpa [firstCaseJ] using hyJ |>.2.2
  have hcardInv : Nat.card {z : G // z ∈ invertedElements c.Hhat y} = n := by
    rw [← firstCase_klein_coset_involution_card_eq c hy hyH]
    exact hcoset
  rcases hYcases with hY1 | hY3 <;> rcases hSYcases with hSY1 | hSY3
  · exfalso
    rw [hcardInv, hY1, hSY1] at hsplit'
    omega
  · rw [hcardInv, hY1, hSY3] at hsplit'
    omega
  · rw [hcardInv, hY3, hSY1] at hsplit'
    omega
  · by_cases hNbot : N = ⊥
    · have hOcard3 : Nat.card O = 3 := by
        rw [hNbot] at hrel'
        simpa [Subgroup.relIndex] using hrel'
      have hYne1 : Nat.card {z : G // z ∈ invertedElements O y} ≠ 1 := by
        rw [hY3]
        norm_num
      obtain ⟨x, hxO, hxne, hxord, hxinv⟩ :=
        firstCase_klein_oddCore_inverted_order_three
          hmin c hfirst hklein hy hyH hidx hYne1
      let R : Subgroup G := Subgroup.zpowers x
      have hRleO : R ≤ O := by
        exact Subgroup.zpowers_le.mpr hxO
      have hRcard : Nat.card R = 3 := by
        rw [Nat.card_zpowers, hxord]
      have hReqO : R = O := by
        apply Subgroup.eq_of_le_of_card_ge hRleO
        rw [hRcard, hOcard3]
      have hRinvY : ∀ z : G, z ∈ R →
          z ∈ invertedElements O y := by
        intro z hz
        rcases Subgroup.mem_zpowers_iff.mp hz with ⟨m, rfl⟩
        refine ⟨O.zpow_mem hxO m, ?_⟩
        calc
          y * x ^ m * y⁻¹ = (y * x * y⁻¹) ^ m := by exact conj_zpow.symm
          _ = (x⁻¹) ^ m := by rw [hxinv.2]
          _ = (x ^ m)⁻¹ := by simp
      have hs2 : s * s = 1 := by simpa [pow_two] using hsI.2
      have hy2 : y * y = 1 := by simpa [pow_two] using hy.2
      let w : G := s * y
      have hwH : w ∉ c.Hhat := by
        intro hw
        apply hyH
        have hyEq : y = s⁻¹ * w := by simp [w]
        rw [hyEq]
        exact c.Hhat.mul_mem (c.Hhat.inv_mem ((inf_le_left : D ≤ c.Hhat) hsD)) hw
      have hwI : IsInvolution w := by
        refine ⟨?_, ?_⟩
        · intro hw1
          apply hwH
          simpa [hw1] using c.Hhat.one_mem
        · dsimp [w]
          calc
            (s * y) ^ 2 = s * (y * s) * y := by simp [pow_two, mul_assoc]
            _ = s * (s * y) * y := by rw [hsy]
            _ = (s * s) * (y * y) := by group
            _ = 1 := by rw [hs2, hy2]; simp
      have hconjEqW : conjugateSubgroup c.Hhat w =
          conjugateSubgroup c.Hhat y := by
        dsimp [w, conjugateSubgroup]
        rw [hsy]
        exact map_conj_mul_right_eq_of_mem_normalizer y
          ⟨s, Subgroup.le_normalizer ((inf_le_left : D ≤ c.Hhat) hsD)⟩
      have hIw : 4 ≤ Nat.card {z : G // z ∈ invertedElements c.Hhat w} := by
        rw [← firstCase_klein_coset_involution_card_eq c hwI hwH]
        have hcardw := firstCase_klein_coset_representative_card_eq c
          ((inf_le_left : D ≤ c.Hhat) hsD) hy hsy hsI hyH
        rw [hcardw]
        rw [show firstCaseCosetInvolutions c y = n by
          simpa [firstCaseJ] using hyJ |>.2.2]
        exact hn
      have hidxW := firstCase_klein_restrictionSix_index_eq
        (y := w) hmin c hfirst hklein hwI hwH hIw
      have hSYne1 : Nat.card {z : G // z ∈ invertedElements O w} ≠ 1 := by
        rw [hSY3]
        norm_num
      have hOeqW : oddCoreOf
          (c.Hhat ⊓ conjugateSubgroup c.Hhat w : Subgroup G) = O := by
        dsimp [O]
        rw [hconjEqW]
      have hSYne1W : Nat.card {z : G // z ∈ invertedElements
          (oddCoreOf (c.Hhat ⊓ conjugateSubgroup c.Hhat w : Subgroup G)) w} ≠ 1 := by
        rw [hOeqW]
        exact hSYne1
      obtain ⟨xw, hxwO, hxwne, hxword, hxwinv⟩ :=
        firstCase_klein_oddCore_inverted_order_three
          hmin c hfirst hklein hwI hwH hidxW hSYne1W
      have hRwinv : x ∈ invertedElements O w := by
        have hxwO' : xw ∈ O := by
          rw [← hOeqW]
          exact hxwO
        let Rw : Subgroup G := Subgroup.zpowers xw
        have hRwleO : Rw ≤ O := Subgroup.zpowers_le.mpr hxwO'
        have hRwcard : Nat.card Rw = 3 := by
          rw [Nat.card_zpowers, hxword]
        have hRweqO : Rw = O := by
          apply Subgroup.eq_of_le_of_card_ge hRwleO
          rw [hRwcard, hOcard3]
        have hRwinvAll : ∀ q : G, q ∈ Rw →
            q ∈ invertedElements O w := by
          intro q hq
          rcases Subgroup.mem_zpowers_iff.mp hq with ⟨m, rfl⟩
          refine ⟨O.zpow_mem hxwO' m, ?_⟩
          calc
            w * xw ^ m * w⁻¹ = (w * xw * w⁻¹) ^ m := by exact conj_zpow.symm
            _ = (xw⁻¹) ^ m := by rw [hxwinv.2]
            _ = (xw ^ m)⁻¹ := by simp
        have hxRw : x ∈ Rw := by
          rw [hRweqO]
          exact hxO
        exact hRwinvAll x hxRw
      have hsCentX : ∀ z : G, z ∈ R → s * z * s⁻¹ = z := by
        intro z hz
        have hzY := (hRinvY z hz).2
        have hzW := hRwinv
        have hzO : z ∈ O := (hRleO hz)
        have hzW' : z ∈ invertedElements O w := by
          have hRwle : Subgroup.zpowers xw ≤ O := by
            exact Subgroup.zpowers_le.mpr (by
              rw [← hOeqW]
              exact hxwO)
          have hRwcard : Nat.card (Subgroup.zpowers xw) = 3 := by
            rw [Nat.card_zpowers, hxword]
          have hRweqO : Subgroup.zpowers xw = O := by
            apply Subgroup.eq_of_le_of_card_ge hRwle
            rw [hRwcard, hOcard3]
          have hzRw : z ∈ Subgroup.zpowers xw := by
            rw [hRweqO]
            exact hzO
          rcases Subgroup.mem_zpowers_iff.mp hzRw with ⟨m, rfl⟩
          refine ⟨O.zpow_mem (by rw [← hOeqW]; exact hxwO) m, ?_⟩
          calc
            w * xw ^ m * w⁻¹ = (w * xw * w⁻¹) ^ m := by exact conj_zpow.symm
            _ = (xw⁻¹) ^ m := by rw [hxwinv.2]
            _ = (xw ^ m)⁻¹ := by simp
        have hzw : w * z * w⁻¹ = z⁻¹ := hzW'.2
        have hzy : y * z * y⁻¹ = z⁻¹ := hzY
        have hs_eq : s = y * w := by
          dsimp [w]
          calc
            s = s * 1 := by simp
            _ = s * (y * y) := by rw [hy2]
            _ = (s * y) * y := by group
            _ = (y * s) * y := by rw [hsy]
            _ = y * (s * y) := by group
        calc
          s * z * s⁻¹ = (y * w) * z * (y * w)⁻¹ := by rw [← hs_eq]
          _ = y * (w * z * w⁻¹) * y⁻¹ := by group
          _ = y * z⁻¹ * y⁻¹ := by rw [hzw]
          _ = z := by
            have h := congrArg (fun q : G => q⁻¹) hzy
            calc
              y * z⁻¹ * y⁻¹ = y * (z⁻¹ * y⁻¹) := by simp [mul_assoc]
              _ = z := by simpa [mul_assoc] using h
      have hRne : R ≠ ⊥ := by
        intro hbot
        apply hxne
        have : x ∈ (⊥ : Subgroup G) := by
          rw [← hbot]
          exact Subgroup.mem_zpowers x
        exact Subgroup.mem_bot.mp this
      have hOleD : O ≤ D := by
        dsimp [O]
        exact Subgroup.map_subtype_le (pPrimeCore 2 (↥D))
      have hRleH : R ≤ c.Hhat := hRleO.trans (hOleD.trans inf_le_left)
      have hRodd : Nat.Coprime 2 (Nat.card R) := by
        rw [hRcard]
        norm_num
      have hsH : s ∈ c.Hhat := (inf_le_left : D ≤ c.Hhat) hsD
      have hRinvH : ∀ z : G, z ∈ R → z ∈ invertedElements c.Hhat y := by
        intro z hz
        exact ⟨hRleH hz, (hRinvY z hz).2⟩
      exact False.elim (firstCase_klein_no_centralizing_involution_of_inverted_card_three
        hmin c hfirst hklein hy hyH hRne hRleH hRodd hRinvH hRcard hsH hsI hsCentX)
    · have hNcard_dvd : Nat.card N ∣ Nat.card c.U :=
        Subgroup.card_dvd_of_le hNleU'
      have hNcard_dvd3 : Nat.card N ∣ 3 := by
        simpa [hcardU] using hNcard_dvd
      have hNcard : Nat.card N = 3 := by
        have hne1 : Nat.card N ≠ 1 := by
          intro h1
          apply hNbot
          exact Subgroup.eq_bot_of_card_eq N h1
        rcases (Nat.dvd_prime Nat.prime_three).mp hNcard_dvd3 with h1 | h3
        · exact (hne1 h1).elim
        · exact h3
      have hNeqU : N = c.U := by
        apply Subgroup.eq_of_le_of_card_ge hNleU'
        rw [hNcard, hcardU]
      have hNleD : N ≤ D := inf_le_left
      have hNnormal : (N.subgroupOf D).Normal := by
        apply (Subgroup.normal_subgroupOf_iff (show N ≤ D from inf_le_left)).2
        intro n0 d0 hn0 hd0
        refine ⟨?_, ?_⟩
        · exact D.mul_mem (D.mul_mem hd0 (hNleD hn0)) (D.inv_mem hd0)
        · have hBnorm : IsNormalIn (twoCoreOf c.Hhat ⊔ c.U) c.Hhat :=
            firstCase_klein_VU_normal_in_Hhat hmin c
          exact hBnorm.2 d0 ((inf_le_left : D ≤ c.Hhat) hd0) n0
            ((inf_le_right : N ≤ twoCoreOf c.Hhat ⊔ c.U) hn0)
      have hNodd : Nat.Coprime 2 (Nat.card N) :=
        firstCase_klein_intersection_odd_of_index_six
          hmin c hfirst hklein hy hyH hidx
      have hNsubodd : Nat.Coprime 2 (Nat.card (N.subgroupOf D)) := by
        have hcardNsub : Nat.card (N.subgroupOf D) = Nat.card N :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show N ≤ D from inf_le_left)).toEquiv
        rw [hcardNsub]
        exact hNodd
      have hNsub_core : N.subgroupOf D ≤ pPrimeCore 2 (↥D) := by
        exact le_sSup ⟨hNnormal, hNsubodd⟩
      have hmapN : (N.subgroupOf D).map D.subtype = N :=
        Subgroup.map_subgroupOf_eq_of_le (show N ≤ D from inf_le_left)
      have hNleO : N ≤ O := by
        dsimp [O, oddCoreOf]
        rw [← hmapN]
        exact Subgroup.map_mono hNsub_core
      have hOcard : Nat.card O = 9 := by
        have hrel'' : (N.subgroupOf O).index = 3 := by
          exact hrel'
        have hcardNsubO : Nat.card (N.subgroupOf O) = Nat.card N := by
          exact Nat.card_congr
            (Subgroup.subgroupOfEquivOfLe hNleO).toEquiv
        have hm := (N.subgroupOf O).card_mul_index
        rw [hcardNsubO, hNcard, hrel''] at hm
        norm_num at hm ⊢
        exact hm.symm
      have hXleD : X ≤ D := by
        intro z hz
        refine ⟨hXle hz, ?_⟩
        apply Subgroup.mem_map.mpr
        refine ⟨z⁻¹, ?_, ?_⟩
        · have hzInv := (hXinv z hz).2
          exact hXle (X.inv_mem hz)
        · have hzInv := (hXinv z hz).2
          calc
            y * z⁻¹ * y⁻¹ = (y * z * y⁻¹)⁻¹ := by group
            _ = (z⁻¹)⁻¹ := by rw [hzInv]
            _ = z := by simp
      have hXleO : X ≤ O := by
        let XD : Subgroup (↥D) := X.subgroupOf D
        let OD : Subgroup (↥D) := O.subgroupOf D
        have hXDodd : Odd (Nat.card XD) := by
          have hcardXD : Nat.card XD = Nat.card X := by
            exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXleD).toEquiv
          rw [hcardXD]
          exact Nat.coprime_two_left.mp hXodd
        have hODnormal : OD.Normal := by
          apply (Subgroup.normal_subgroupOf_iff (show O ≤ D from by
            dsimp [O]
            exact Subgroup.map_subtype_le (pPrimeCore 2 (↥D)))).2
          intro o0 d0 ho0 hd0
          rcases Subgroup.mem_map.mp ho0 with ⟨o1, ho1, rfl⟩
          let d0' : D := ⟨d0, hd0⟩
          exact Subgroup.mem_map.mpr ⟨d0' * o1 * d0'⁻¹,
            (pPrimeCore_normal (p := 2) (G := (↥D))).conj_mem
              o1 ho1 d0', by simp [d0']⟩
        have hODindex : OD.index = 2 := by
          simpa [OD] using hOidx'
        have hle : XD ≤ OD :=
          odd_card_subgroup_le_normal_index_two OD XD hODnormal hODindex hXDodd
        intro z hz
        have hz' : (⟨z, hXleD hz⟩ : D) ∈ XD := by
          exact hz
        exact Subgroup.mem_subgroupOf.mp (hle hz')
      have hUXdisj : Disjoint c.U X := by
        apply (disjoint_iff_inf_le).2
        intro z hz
        have hInf := firstCase_klein_inverted_subgroup_inf_VU_eq_bot
          hmin c hfirst hklein hy hyH hXle hXinv
        have hzbot : z ∈ (⊥ : Subgroup G) := by
          rw [← hInf]
          exact ⟨hz.2, (show z ∈ twoCoreOf c.Hhat ⊔ c.U from
            (le_sup_right : c.U ≤ twoCoreOf c.Hhat ⊔ c.U) hz.1)⟩
        exact hzbot
      have hUnormX : c.U ≤ Subgroup.normalizer (X : Set G) := by
        exact (hFUeq ▸ (firstCase_klein_restrictionSeven_core
          hmin c hfirst hklein hyJ hXne hXle hXodd hXinv hC_even hN_even).2).trans
          (Subgroup.centralizer_le_normalizer (X : Set G))
      have hUXcard : Nat.card (↥(c.U ⊔ X)) = 9 := by
        rw [sup_comm c.U X]
        rw [card_sup_eq_mul_of_disjoint_of_le_normalizer (G := G) X c.U
          hUnormX hUXdisj.symm, hcore.1, hcardU]
      have hOleD : O ≤ D := by
        dsimp [O]
        exact Subgroup.map_subtype_le (pPrimeCore 2 (↥D))
      have hUXleO : c.U ⊔ X ≤ O := by
        exact sup_le (hNeqU ▸ hNleO) hXleO
      have hOeqUX : O = c.U ⊔ X := by
        symm
        apply Subgroup.eq_of_le_of_card_ge hUXleO
        rw [hOcard, hUXcard]
      obtain ⟨g, hgnot, hXgU, hDgEq⟩ :=
        firstCase_klein_restrictionSeven_normalizer_intersection
          hmin c hfirst hklein hyJ hn hXne hXle hXodd hXinv hC_even hN_even
      let A' : Subgroup G := conjugateSubgroup c.Hhat g⁻¹
      let E : Subgroup G := c.Hhat ⊓ A'
      let Vg : Subgroup G := conjugateSubgroup (twoCoreOf c.Hhat) g⁻¹
      have hEeq : E = Subgroup.normalizer (X : Set G) ⊓ c.Hhat := by
        simpa [E, A'] using hDgEq
      have hXcard : Nat.card X = 3 := hcore.1
      have hVgcentX : Vg ≤ Subgroup.centralizer (X : Set G) := by
        have hVcentU : twoCoreOf c.Hhat ≤ Subgroup.centralizer (c.U : Set G) := by
          simpa [(theorem_2_6 hmin c).1] using
            twoCoreOf_centralizes_oddCoreOf c.Hhat
        have hmapU : conjugateSubgroup c.U g⁻¹ = X := by
          have hm := congrArg (fun K : Subgroup G => conjugateSubgroup K g⁻¹) hXgU
          have hcancel : conjugateSubgroup (conjugateSubgroup X g) g⁻¹ = X := by
            simpa using (conj_inv_then_conj_eq X g⁻¹)
          rw [hcancel] at hm
          exact hm.symm
        change (twoCoreOf c.Hhat).map (MulAut.conj g⁻¹).toMonoidHom ≤
          Subgroup.centralizer (X : Set G)
        rw [← hmapU]
        exact centralizer_map_le_of_conj c.U (twoCoreOf c.Hhat) g hVcentU
      have hVgKlein : IsKleinFour Vg := by
        change IsKleinFour ((twoCoreOf c.Hhat).map (MulAut.conj g⁻¹).toMonoidHom)
        exact isKleinFour_map_mulEquiv (twoCoreOf c.Hhat)
          (firstCase_klein_V_klein c hklein) (MulAut.conj g⁻¹)
      have hVgcard : Nat.card Vg = 4 := hVgKlein.card_four
      have hVgleA' : Vg ≤ A' := by
        dsimp [Vg, A']
        exact Subgroup.map_mono (Subgroup.map_subtype_le (pCore 2 c.Hhat))
      have hVgnormA' : IsNormalIn Vg A' := by
        refine ⟨hVgleA', ?_⟩
        intro a ha v hv
        rcases Subgroup.mem_map.mp ha with ⟨a0, ha0, rfl⟩
        rcases Subgroup.mem_map.mp hv with ⟨v0, hv0, rfl⟩
        refine Subgroup.mem_map.mpr ⟨a0 * v0 * a0⁻¹, ?_, ?_⟩
        · have hVnorm : IsNormalIn (twoCoreOf c.Hhat) c.Hhat := by
            refine ⟨Subgroup.map_subtype_le (pCore 2 c.Hhat), ?_⟩
            intro h hh v hv
            rcases Subgroup.mem_map.mp hv with ⟨v0, hv0, rfl⟩
            exact Subgroup.mem_map.mpr ⟨(⟨h, hh⟩ : c.Hhat) * v0 *
              (⟨h, hh⟩ : c.Hhat)⁻¹,
              (pCore_normal (p := 2) (G := c.Hhat)).conj_mem v0 hv0
                (⟨h, hh⟩ : c.Hhat), by simp⟩
          exact hVnorm.2 a0 ha0 v0 hv0
        · simpa [MulAut.conj_apply] using
            (show g⁻¹ * (a0 * v0 * a0⁻¹) * g =
              (g⁻¹ * a0 * g) * (g⁻¹ * v0 * g) *
                (g⁻¹ * a0 * g)⁻¹ by group)
      have hE_le_normVg : E ≤ Subgroup.normalizer (Vg : Set G) := by
        exact (inf_le_right : E ≤ A').trans (le_normalizer_of_isNormalIn hVgnormA')
      have hEVg_bot : E ⊓ Vg = ⊥ := by
        apply le_bot_iff.mp
        intro z hz
        by_cases hz1 : z = 1
        · exact Subgroup.mem_bot.mpr hz1
        have hzI : IsInvolution z := by
          refine ⟨hz1, ?_⟩
          simpa [pow_two] using congrArg Subtype.val
            (hVgKlein.mul_self ⟨z, hz.2⟩)
        have hzH : z ∈ c.Hhat := (inf_le_left : E ≤ c.Hhat) hz.1
        have hzcent : ∀ q : G, q ∈ X → z * q * z⁻¹ = q := by
          intro q hq
          have hc := (Subgroup.mem_centralizer_iff.mp (hVgcentX hz.2)) q hq
          calc
            z * q * z⁻¹ = q * z * z⁻¹ := by rw [hc]
            _ = q := by simp
        exact False.elim (firstCase_klein_no_centralizing_involution_of_inverted_card_three
          hmin c hfirst hklein hy hyH hXne hXle hXodd hXinv hXcard hzH hzI hzcent)
      have hEeven : Even (Nat.card E) := by
        rw [hEeq]
        exact hN_even
      have hO_le_E : O ≤ E := by
        rw [hEeq]
        rw [hOeqUX]
        apply sup_le <;> apply le_inf
        · exact hUnormX
        · exact (theorem_2_6 hmin c).1 ▸
            (Subgroup.map_subtype_le (pPrimeCore 2 c.Hhat))
        · exact Subgroup.le_normalizer
        · exact hXle
      have hEcard_dvd : 4 * Nat.card E ∣ 72 := by
        have hAsup : Vg ⊔ E ≤ A' := sup_le hVgleA' inf_le_right
        have hcardSup : Nat.card (↥(Vg ⊔ E)) = 4 * Nat.card E := by
          rw [card_sup_eq_mul_of_disjoint_of_le_normalizer (G := G) Vg E
            hE_le_normVg (by simpa [disjoint_iff_inf_le, inf_comm] using hEVg_bot)]
          rw [hVgcard]
        have hdvd := Subgroup.card_dvd_of_le hAsup
        rw [hcardSup] at hdvd
        have hAcard : Nat.card A' = 72 := by
          have hHhatH : Nat.card c.Hhat = 3 * Nat.card c.H := by
            have hidxH := firstCase_H_index_eq_three_mul_Hhat_index hmin c hfirst hklein
            have hmulH := c.H.card_mul_index
            have hmulHH := c.Hhat.card_mul_index
            have hpos : 0 < c.Hhat.index := by
              rw [Subgroup.index_eq_card]
              exact Nat.card_pos
            apply Nat.eq_of_mul_eq_mul_right hpos
            calc
              Nat.card c.Hhat * c.Hhat.index = Nat.card G := hmulHH
              _ = Nat.card c.H * c.H.index := hmulH.symm
              _ = Nat.card c.H * (3 * c.Hhat.index) := by rw [hidxH]
              _ = (3 * Nat.card c.H) * c.Hhat.index := by ring
          have hconjcard : Nat.card A' = Nat.card c.Hhat := by
            exact Nat.card_congr
              (Subgroup.equivMapOfInjective c.Hhat (MulAut.conj g⁻¹).toMonoidHom
                (MulAut.conj g⁻¹).injective).toEquiv.symm
          rw [hconjcard, hHhatH, hHcard, hcardU]
        rw [hAcard] at hdvd
        exact hdvd
      have hEcard_le : Nat.card E ≤ 18 := by
        have hle : 4 * Nat.card E ≤ 72 := Nat.le_of_dvd (by norm_num) hEcard_dvd
        omega
      have hEcard_lower : 18 ≤ Nat.card E := by
        have hOcarddvd : Nat.card O ∣ Nat.card E := Subgroup.card_dvd_of_le hO_le_E
        have h2dvd : 2 ∣ Nat.card E := hEeven.two_dvd
        have h18dvd : 18 ∣ Nat.card E := by
          have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 2 9)
            h2dvd (by simpa [hOcard] using hOcarddvd)
          norm_num at this ⊢
          exact this
        exact Nat.le_of_dvd (Nat.card_pos) h18dvd
      have hEcard : Nat.card E = 18 := by omega
      have hVne : twoCoreOf c.Hhat ≠ ⊥ := by
        intro hbot
        have hfour := (firstCase_klein_V_klein c hklein).card_four
        rw [hbot] at hfour
        simp at hfour
      have hUne : c.U ≠ ⊥ := (lemma_2_2 hmin c).2
      have hNormU : Subgroup.normalizer (c.U : Set G) = c.Hhat :=
        theorem26_normalizer_U_eq_Hhat hmin c hVne hUne
      have hNormMap : conjugateSubgroup (Subgroup.normalizer (X : Set G)) g = c.Hhat := by
        change (Subgroup.normalizer (X : Set G)).map
          (MulAut.conj g).toMonoidHom = _
        rw [Subgroup.map_normalizer_eq_of_bijective X (MulAut.conj g).bijective]
        change Subgroup.normalizer (conjugateSubgroup X g : Set G) = c.Hhat
        rw [hXgU, hNormU]
      have hyNormX : y ∈ Subgroup.normalizer (X : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro z
        constructor
        · intro hz
          rw [(hXinv z hz).2]
          exact X.inv_mem hz
        · intro hz
          have hz' := hXinv (y * z * y⁻¹) hz
          have hy2 : y * y = 1 := by simpa [pow_two] using hy.2
          have hcalc : y * (y * z * y⁻¹) * y⁻¹ = z := by
            have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
            calc
              y * (y * z * y⁻¹) * y⁻¹ = (y * y) * z * (y⁻¹ * y⁻¹) := by group
              _ = (y * y) * z * (y * y) := by rw [hyinv]
              _ = z := by simp [hy2]
          have heq : z = (y * z * y⁻¹)⁻¹ := by
            calc
              z = y * (y * z * y⁻¹) * y⁻¹ := hcalc.symm
              _ = (y * z * y⁻¹)⁻¹ := hz'.2
          rw [heq]
          exact X.inv_mem hz
      have hyA' : y ∈ A' := by
        have hgy : g * y * g⁻¹ ∈ c.Hhat := by
          rw [← hNormMap]
          exact Subgroup.mem_map.mpr ⟨y, hyNormX, rfl⟩
        exact Subgroup.mem_map.mpr ⟨g * y * g⁻¹, hgy, by
          simpa [MulAut.conj_apply] using
            (show g⁻¹ * (g * y * g⁻¹) * g = y by group)⟩
      have hDmap_le : conjugateSubgroup D y ≤ D := by
        intro z hz
        rcases Subgroup.mem_map.mp hz with ⟨d0, hd0, rfl⟩
        refine ⟨?_, ?_⟩
        · rcases Subgroup.mem_map.mp hd0.2 with ⟨h0, hh0, hEq⟩
          change y * d0 * y⁻¹ ∈ c.Hhat
          rw [← hEq]
          have hy2 : y * y = 1 := by simpa [pow_two] using hy.2
          change y * (y * h0 * y⁻¹) * y⁻¹ ∈ c.Hhat
          have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
          have hcalc : y * (y * h0 * y⁻¹) * y⁻¹ = h0 := by
            calc
              y * (y * h0 * y⁻¹) * y⁻¹ = (y * y) * h0 * (y⁻¹ * y⁻¹) := by group
              _ = (y * y) * h0 * (y * y) := by rw [hyinv]
              _ = h0 := by simp [hy2]
          rw [hcalc]
          exact hh0
        · change y * d0 * y⁻¹ ∈ conjugateSubgroup c.Hhat y
          apply Subgroup.mem_map.mpr
          exact ⟨d0, hd0.1, rfl⟩
      have hUconj_leD : conjugateSubgroup c.U y ≤ D := by
        exact (Subgroup.map_mono (show c.U ≤ D from
          (hNeqU ▸ hNleO).trans hOleD)).trans hDmap_le
      have hUconj_leO : conjugateSubgroup c.U y ≤ O := by
        let UY : Subgroup G := conjugateSubgroup c.U y
        let UYD : Subgroup (↥D) := UY.subgroupOf D
        have hUYcard : Nat.card UYD = 3 := by
          have hcardmap : Nat.card UY = Nat.card c.U := by
            exact Nat.card_congr
              (Subgroup.equivMapOfInjective c.U (MulAut.conj y).toMonoidHom
                (MulAut.conj y).injective).toEquiv.symm
          have hsubcard : Nat.card UYD = Nat.card UY := by
            exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUconj_leD).toEquiv
          rw [hsubcard, hcardmap, hcardU]
        have hUYodd : Odd (Nat.card UYD) := by rw [hUYcard]; norm_num
        have hODnormal : (O.subgroupOf D).Normal := by
          apply (Subgroup.normal_subgroupOf_iff (show O ≤ D from hOleD)).2
          intro o0 d0 ho0 hd0
          rcases Subgroup.mem_map.mp ho0 with ⟨o1, ho1, rfl⟩
          let d0' : D := ⟨d0, hd0⟩
          exact Subgroup.mem_map.mpr ⟨d0' * o1 * d0'⁻¹,
            (pPrimeCore_normal (p := 2) (G := (↥D))).conj_mem o1 ho1 d0', by simp [d0']⟩
        have hle : UYD ≤ O.subgroupOf D := by
          exact odd_card_subgroup_le_normal_index_two
            (O.subgroupOf D) UYD hODnormal hOidx' hUYodd
        intro z hz
        have hz' : (⟨z, hUconj_leD hz⟩ : D) ∈ UYD := hz
        exact Subgroup.mem_subgroupOf.mp (hle hz')
      have hmapOle : conjugateSubgroup O y ≤ O := by
        change (O.map (MulAut.conj y).toMonoidHom) ≤ O
        rw [hOeqUX, Subgroup.map_sup]
        have hXmap : conjugateSubgroup X y ≤ X := by
          intro z hz
          rcases Subgroup.mem_map.mp hz with ⟨x0, hx0, rfl⟩
          change y * x0 * y⁻¹ ∈ X
          rw [(hXinv x0 hx0).2]
          exact X.inv_mem hx0
        apply sup_le
        · have hUmap : (c.U.map (MulAut.conj y).toMonoidHom) ≤ O := by
            simpa [conjugateSubgroup] using hUconj_leO
          rw [hOeqUX] at hUmap
          exact hUmap
        · exact hXmap.trans le_sup_right
      have hyNormO : y ∈ Subgroup.normalizer (O : Set G) := by
        rw [Subgroup.mem_normalizer_iff_map_conj_eq]
        apply le_antisymm hmapOle
        intro z hz
        apply Subgroup.mem_map.mpr
        have hzmap : y * z * y⁻¹ ∈ conjugateSubgroup O y := by
          exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
        refine ⟨y * z * y⁻¹, hmapOle hzmap, ?_⟩
        have hy2 : y * y = 1 := by simpa [pow_two] using hy.2
        have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
        calc
          y * (y * z * y⁻¹) * y⁻¹ = (y * y) * z * (y⁻¹ * y⁻¹) := by group
          _ = (y * y) * z * (y * y) := by rw [hyinv]
          _ = z := by simp [hy2]
      have hE_normO : E ≤ Subgroup.normalizer (O : Set G) := by
        rw [Subgroup.le_normalizer_iff]
        intro e he z hz
        have heH : e ∈ c.Hhat := (inf_le_left : E ≤ c.Hhat) he
        have heX : e ∈ Subgroup.normalizer (X : Set G) := by
          rw [hEeq] at he
          exact (inf_le_left : Subgroup.normalizer (X : Set G) ⊓ c.Hhat ≤
            Subgroup.normalizer (X : Set G)) he
        have hUnormH : IsNormalIn c.U c.Hhat := by
          rw [(theorem_2_6 hmin c).1]
          refine ⟨Subgroup.map_subtype_le (pPrimeCore 2 c.Hhat), ?_⟩
          intro h hh u hu
          rcases Subgroup.mem_map.mp hu with ⟨u0, hu0, rfl⟩
          exact Subgroup.mem_map.mpr ⟨
            (⟨h, hh⟩ : c.Hhat) * u0 * (⟨h, hh⟩ : c.Hhat)⁻¹,
            (pPrimeCore_normal (p := 2) (G := c.Hhat)).conj_mem
              u0 hu0 (⟨h, hh⟩ : c.Hhat), by simp⟩
        have hmapO : conjugateSubgroup O e ≤ O := by
          change O.map (MulAut.conj e).toMonoidHom ≤ O
          rw [hOeqUX, Subgroup.map_sup]
          apply sup_le
          · have hUmap : c.U.map (MulAut.conj e).toMonoidHom ≤ c.U := by
              intro u hu
              rcases Subgroup.mem_map.mp hu with ⟨u0, hu0, rfl⟩
              exact hUnormH.2 e heH u0 hu0
            exact hUmap.trans le_sup_left
          · have hXmap : conjugateSubgroup X e ≤ X := by
              intro x0 hx0
              rcases Subgroup.mem_map.mp hx0 with ⟨x1, hx1, rfl⟩
              exact (Subgroup.mem_normalizer_iff.mp heX x1).mp hx1
            exact hXmap.trans le_sup_right
        have hzmap : e * z * e⁻¹ ∈ conjugateSubgroup O e := by
          exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
        exact hmapO hzmap
      have hOleA' : O ≤ A' := hO_le_E.trans inf_le_right
      let O' : Subgroup (↥A') := O.subgroupOf A'
      have hO'card : Nat.card O' = 9 := by
        have hsubcard : Nat.card O' = Nat.card O := by
          exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOleA').toEquiv
        rw [hsubcard, hOcard]
      have hAcard : Nat.card A' = 72 := by
        have hHhatH : Nat.card c.Hhat = 3 * Nat.card c.H := by
          have hidxH := firstCase_H_index_eq_three_mul_Hhat_index hmin c hfirst hklein
          have hmulH := c.H.card_mul_index
          have hmulHH := c.Hhat.card_mul_index
          have hpos : 0 < c.Hhat.index := by
            rw [Subgroup.index_eq_card]
            exact Nat.card_pos
          apply Nat.eq_of_mul_eq_mul_right hpos
          calc
            Nat.card c.Hhat * c.Hhat.index = Nat.card G := hmulHH
            _ = Nat.card c.H * c.H.index := hmulH.symm
            _ = Nat.card c.H * (3 * c.Hhat.index) := by rw [hidxH]
            _ = (3 * Nat.card c.H) * c.Hhat.index := by ring
        have hconjcard : Nat.card A' = Nat.card c.Hhat := by
          exact Nat.card_congr
            (Subgroup.equivMapOfInjective c.Hhat (MulAut.conj g⁻¹).toMonoidHom
              (MulAut.conj g⁻¹).injective).toEquiv.symm
        rw [hconjcard, hHhatH, hHcard, hcardU]
      let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hAfac : (Nat.card A').factorization 3 = 2 := by
        rw [hAcard]
        rw [show (72 : ℕ) = 3 ^ 2 * 8 by norm_num]
        rw [Nat.factorization_mul (by norm_num) (by norm_num)]
        rw [Nat.factorization_pow]
        simp [Nat.prime_three.factorization_self]
        exact Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ (8 : ℕ))
      let P : Sylow 3 (↥A') := Sylow.ofCard O' (by
        rw [hO'card, hAfac]
        norm_num)
      have hPsub : (P : Subgroup (↥A')) = O' := by rfl
      have hEsub_le : E.subgroupOf A' ≤ Subgroup.normalizer (P : Set (↥A')) := by
        apply (Subgroup.le_normalizer_iff).2
        intro e he p hp
        rw [hPsub] at hp ⊢
        have hpO : (p : G) ∈ O := Subgroup.mem_subgroupOf.mp hp
        have hiff := (Subgroup.mem_normalizer_iff.mp (hE_normO he)) (p : G)
        exact Subgroup.mem_subgroupOf.mpr (hiff.mp hpO)
      have hySub_mem : (⟨y, hyA'⟩ : A') ∈ Subgroup.normalizer (P : Set (↥A')) := by
        apply (Subgroup.mem_normalizer_iff).2
        intro p
        constructor
        · intro hp
          rw [hPsub] at hp ⊢
          have hpO : (p : G) ∈ O := Subgroup.mem_subgroupOf.mp hp
          have hiff := (Subgroup.mem_normalizer_iff.mp hyNormO) (p : G)
          exact Subgroup.mem_subgroupOf.mpr (hiff.mp hpO)
        · intro hp
          rw [hPsub] at hp ⊢
          have hpOconj : y * (p : G) * y⁻¹ ∈ O := by
            simpa using (Subgroup.mem_subgroupOf.mp hp)
          have hiff := (Subgroup.mem_normalizer_iff.mp hyNormO) (p : G)
          exact Subgroup.mem_subgroupOf.mpr (hiff.mpr hpOconj)
      have hEsubcard : Nat.card (E.subgroupOf A') = 18 := by
        have hsubcard : Nat.card (E.subgroupOf A') = Nat.card E := by
          exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : E ≤ A')).toEquiv
        rw [hsubcard, hEcard]
      have hNPAcard_dvd : Nat.card (Subgroup.normalizer (P : Set (↥A'))) ∣ 72 := by
        have hle : Subgroup.normalizer (P : Set (↥A')) ≤ (⊤ : Subgroup (↥A')) := le_top
        simpa [hAcard] using Subgroup.card_dvd_of_le hle
      have hEsubcard_dvd : Nat.card (E.subgroupOf A') ∣
          Nat.card (Subgroup.normalizer (P : Set (↥A'))) :=
        Subgroup.card_dvd_of_le hEsub_le
      have h18dvdN : 18 ∣ Nat.card (Subgroup.normalizer (P : Set (↥A'))) := by
        rw [← hEsubcard]
        exact hEsubcard_dvd
      have hy_not_Esub : (⟨y, hyA'⟩ : A') ∉ E.subgroupOf A' := by
        intro hyE
        have hyE' : y ∈ E := Subgroup.mem_subgroupOf.mp hyE
        exact hyH ((inf_le_left : E ≤ c.Hhat) hyE')
      have hNPAcard_lower : 36 ≤ Nat.card (Subgroup.normalizer (P : Set (↥A'))) := by
        have hNPAcard_ge : Nat.card (E.subgroupOf A') ≤
            Nat.card (Subgroup.normalizer (P : Set (↥A'))) :=
          Nat.le_of_dvd (Nat.card_pos) hEsubcard_dvd
        have hNPAne : Nat.card (Subgroup.normalizer (P : Set (↥A'))) ≠
            Nat.card (E.subgroupOf A') := by
          intro heq
          have hEqSub : E.subgroupOf A' = Subgroup.normalizer (P : Set (↥A')) :=
            Subgroup.eq_of_le_of_card_ge hEsub_le (by simpa [heq])
          exact hy_not_Esub (by rw [hEqSub]; exact hySub_mem)
        rw [hEsubcard] at hNPAcard_ge hNPAne
        obtain ⟨k, hk⟩ := h18dvdN
        have hkpos : 0 < k := by
          have hpos : 0 < Nat.card (Subgroup.normalizer (P : Set (↥A'))) := Nat.card_pos
          omega
        have hkge2 : 2 ≤ k := by omega
        rw [hk] at hNPAne ⊢
        omega
      have hNPAindex_mul : Nat.card (Subgroup.normalizer (P : Set (↥A'))) *
          (Subgroup.normalizer (P : Set (↥A'))).index = Nat.card (↥A') :=
        (Subgroup.normalizer (P : Set (↥A'))).card_mul_index
      have hNPAindex_le : (Subgroup.normalizer (P : Set (↥A'))).index ≤ 2 := by
        have hidxpos : 0 < (Subgroup.normalizer (P : Set (↥A'))).index := by
          rw [Subgroup.index_eq_card]
          exact Nat.card_pos
        rw [hAcard] at hNPAindex_mul
        by_contra hidx
        have hidxge : 3 ≤ (Subgroup.normalizer (P : Set (↥A'))).index := by omega
        have hmul_le :
            36 * 3 ≤
              Nat.card (Subgroup.normalizer (P : Set (↥A'))) *
                (Subgroup.normalizer (P : Set (↥A'))).index :=
          Nat.mul_le_mul hNPAcard_lower hidxge
        rw [hNPAindex_mul] at hmul_le
        norm_num at hmul_le
      have hNPAindex_cases : (Subgroup.normalizer (P : Set (↥A'))).index = 1 ∨
          (Subgroup.normalizer (P : Set (↥A'))).index = 2 := by
        have hidxpos : 0 < (Subgroup.normalizer (P : Set (↥A'))).index := by
          rw [Subgroup.index_eq_card]
          exact Nat.card_pos
        rcases Nat.lt_or_eq_of_le hNPAindex_le with hlt | heq
        · left
          have hle1 : (Subgroup.normalizer (P : Set (↥A'))).index ≤ 1 := by
            exact Nat.le_of_lt_succ (by simpa [Nat.succ_eq_add_one] using hlt)
          have hne0 : (Subgroup.normalizer (P : Set (↥A'))).index ≠ 0 :=
            Nat.ne_of_gt hidxpos
          have hone : 1 ≤ (Subgroup.normalizer (P : Set (↥A'))).index :=
            (Nat.one_le_iff_ne_zero).2 hne0
          exact Nat.le_antisymm hle1 hone
        · right
          exact heq
      have hSylCard : Nat.card (Sylow 3 (↥A')) =
          (Subgroup.normalizer (P : Set (↥A'))).index := by
        simpa [P] using P.card_eq_index_normalizer
      have hSylMod := card_sylow_modEq_one 3 (↥A')
      have hNPAindex_one : (Subgroup.normalizer (P : Set (↥A'))).index = 1 := by
        rcases hNPAindex_cases with h1 | h2
        · exact h1
        · rw [hSylCard, h2] at hSylMod
          norm_num at hSylMod
      have hNPA_top : Subgroup.normalizer (P : Set (↥A')) = ⊤ :=
        (Subgroup.index_eq_one.mp hNPAindex_one)
      have hPnormal : P.Normal := by
        apply Sylow.normal_of_normalizer_normal P
        rw [hNPA_top]
        infer_instance
      have hOsubnormal : (O.subgroupOf A').Normal := by
        change (O' : Subgroup (↥A')).Normal
        rw [← hPsub]
        exact hPnormal
      have hOnormalA' : IsNormalIn O A' := by
        refine ⟨hOleA', ?_⟩
        intro a ha o ho
        have ho' : (⟨o, hOleA' ho⟩ : A') ∈ O.subgroupOf A' :=
          Subgroup.mem_subgroupOf.mpr ho
        have hconj :
            (⟨a, ha⟩ : A') * (⟨o, hOleA' ho⟩ : A') * (⟨a, ha⟩ : A')⁻¹ ∈
              O.subgroupOf A' :=
          hOsubnormal.conj_mem (⟨o, hOleA' ho⟩ : A') ho'
            (⟨a, ha⟩ : A')
        exact Subgroup.mem_subgroupOf.mp hconj
      have hVg_normO : Vg ≤ Subgroup.normalizer (O : Set G) :=
        hVgleA'.trans (le_normalizer_of_isNormalIn hOnormalA')
      let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hVgP : IsPGroup 2 (↥Vg) := by
        apply IsPGroup.of_card (n := 2)
        rw [hVgcard]
        norm_num
      let : IsMulCommutative (↥Vg) := IsKleinFour.isMulCommutative
      let : CommGroup (↥Vg) := IsMulCommutative.instCommGroup
      let : Fact (IsPGroup 2 (↥Vg)) := ⟨hVgP⟩
      let : Vg.Normalizes O := ⟨hVg_normO⟩
      let : MulDistribMulAction (↥Vg) (↥O) :=
        Subgroup.conjMulDistribMulActionOfLeNormalizer Vg O hVg_normO
      have hOodd : Nat.Coprime 2 (Nat.card (↥O)) := by
        rw [hOcard]
        norm_num
      have htop :=
        iSup_fixedPointSubgroup_zpowers_eq_top_of_noncyclic_abelian_pGroup_action
          (G := ↥O) (A := ↥Vg) (p := 2) (hG := hOodd)
          (hncyc := IsKleinFour.not_isCyclic)
      have htop_map : (⊤ : Subgroup (↥O)).map O.subtype = O := by
        simpa [MonoidHom.range_eq_map] using (Subgroup.range_subtype (H := O))
      have hnotall : ¬ ∀ v : ↥Vg, ∀ hv1 : v ≠ 1,
          (fixedPointSubgroup (↥(Subgroup.zpowers v)) (↥O)).map O.subtype ≤ X := by
        intro hall
        have hOleX : O ≤ X := by
          calc
            O = (⊤ : Subgroup (↥O)).map O.subtype := htop_map.symm
            _ = (⨆ (v : ↥Vg) (_ : v ≠ 1),
                fixedPointSubgroup (↥(Subgroup.zpowers v)) (↥O)).map O.subtype := by
                  rw [htop]
            _ ≤ X := by
              rw [Subgroup.map_iSup]
              refine iSup_le ?_
              intro v
              rw [Subgroup.map_iSup]
              refine iSup_le ?_
              intro hv1
              exact hall v hv1
        have hdiv : Nat.card O ∣ Nat.card X := Subgroup.card_dvd_of_le hOleX
        rw [hOcard, hXcard] at hdiv
        norm_num at hdiv
      push_neg at hnotall
      rcases hnotall with ⟨v, hv1, hvnot⟩
      have hexmem : ∃ q : G, q ∈
          (fixedPointSubgroup (↥(Subgroup.zpowers v)) (↥O)).map O.subtype ∧
          q ∉ X := by
        by_contra h
        push_neg at h
        exact hvnot h
      rcases hexmem with ⟨z, hzmap, hzx⟩
      rcases Subgroup.mem_map.mp hzmap with ⟨zO, hzfix, rfl⟩
      let zG : G := zO
      have hzO : zG ∈ O := zO.property
      have hzxG : zG ∉ X := hzx
      have hzne : zG ≠ 1 := by
        intro hz1
        apply hzxG
        simpa [hz1] using X.one_mem
      have hzfix' := hzfix ⟨v, Subgroup.mem_zpowers v⟩
      have hvz : (v : G) * zG * (v : G)⁻¹ = zG := by
        have hcoe := congrArg Subtype.val hzfix'
        have hformula := Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe
          Vg O (a := v) (k := zO)
        exact hformula.symm.trans hcoe
      let : IsMulCommutative (↥O) := by
        apply IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3)
        simpa [hOcard]
      let : CommGroup (↥O) := IsMulCommutative.instCommGroup
      have hconj_eq_of_memO : ∀ a b : G, a ∈ O → b ∈ O →
          a * b * a⁻¹ = b := by
        intro a b ha hb
        have hcomm : a * b = b * a := congrArg Subtype.val
          (mul_comm (⟨a, ha⟩ : O) (⟨b, hb⟩ : O))
        calc
          a * b * a⁻¹ = b * a * a⁻¹ := by rw [hcomm]
          _ = b := by simp
      let Rz : Subgroup G := Subgroup.zpowers zG
      have hRzleO : Rz ≤ O := by
        exact Subgroup.zpowers_le.mpr hzO
      have hRzne : Rz ≠ ⊥ := by
        intro hbot
        apply hzne
        have hzRz : zG ∈ Rz := Subgroup.mem_zpowers zG
        rw [hbot] at hzRz
        exact Subgroup.mem_bot.mp hzRz
      have hRzcard_dvd : Nat.card Rz ∣ 9 := by
        have hd := Subgroup.card_dvd_of_le hRzleO
        simpa [hOcard] using hd
      have hRzcard_ne1 : Nat.card Rz ≠ 1 := by
        intro hcard
        exact hRzne (Subgroup.eq_bot_of_card_eq Rz hcard)
      have hRzcard_cases : Nat.card Rz = 3 ∨ Nat.card Rz = 9 := by
        have hdvdpow : Nat.card Rz ∣ 3 ^ 2 := by simpa using hRzcard_dvd
        rcases (Nat.dvd_prime_pow Nat.prime_three).mp hdvdpow with ⟨k, hk, hEq⟩
        have hkne0 : k ≠ 0 := by
          intro hk0
          apply hRzcard_ne1
          simpa [hk0] using hEq
        have hkpos : 1 ≤ k := (Nat.one_le_iff_ne_zero).2 hkne0
        rcases Nat.lt_or_eq_of_le hk with hlt | heq
        · left
          have hk1 : k = 1 := by omega
          simpa [hk1] using hEq
        · right
          simpa [heq] using hEq
      have hRzneX : Rz ≠ X := by
        intro heq
        apply hzxG
        have hzRz : zG ∈ Rz := Subgroup.mem_zpowers zG
        rw [heq] at hzRz
        exact hzRz
      have hXnormRz : X ≤ Subgroup.normalizer (Rz : Set G) := by
        intro a ha
        rw [Subgroup.mem_normalizer_iff]
        intro q
        constructor
        · intro hq
          rw [hconj_eq_of_memO a q (hXleO ha) (hRzleO hq)]
          exact hq
        · intro hq
          have hqO : a * q * a⁻¹ ∈ O := hRzleO hq
          have heq : q = a * q * a⁻¹ := by
            calc
              q = a⁻¹ * (a * q * a⁻¹) * a := by group
              _ = a * q * a⁻¹ := by
                simpa only [inv_inv] using hconj_eq_of_memO a⁻¹
                  (a * q * a⁻¹) (O.inv_mem (hXleO ha)) hqO
          rw [heq]
          exact hq
      have hRzcent : Rz ≤ Subgroup.centralizer ({(v : G)} : Set G) := by
        intro q hq
        rw [Subgroup.mem_centralizer_iff]
        intro t ht
        have ht' : t = (v : G) := by simpa using ht
        subst t
        rcases Subgroup.mem_zpowers_iff.mp hq with ⟨m, rfl⟩
        have hcommEq : zG * (v : G) = (v : G) * zG := by
          have h := congrArg (fun r : G => r * (v : G)) hvz
          simpa [mul_assoc] using h.symm
        have hcomm : Commute zG (v : G) :=
          (commute_iff_eq zG (v : G)).2 hcommEq
        exact (hcomm.zpow_left m).eq.symm
      have hXcent : X ≤ Subgroup.centralizer ({(v : G)} : Set G) := by
        intro q hq
        rw [Subgroup.mem_centralizer_iff]
        intro t ht
        have ht' : t = (v : G) := by simpa using ht
        subst t
        exact (Subgroup.mem_centralizer_iff.mp (hVgcentX v.property) q hq).symm
      have hsupEq : Rz ⊔ X = O := by
        rcases hRzcard_cases with hRz3 | hRz9
        · have hXRzdisj : Disjoint Rz X := by
            apply (disjoint_iff_inf_le).2
            intro q hq
            by_cases hq1 : q = 1
            · exact Subgroup.mem_bot.mpr hq1
            · have heq := subgroup_eq_of_card_eq_prime_of_common_ne_one
                Nat.prime_three Rz X hRz3 hXcard hq.1 hq.2 hq1
              exact False.elim (hRzneX heq)
          have hsupcard : Nat.card (↥(Rz ⊔ X)) = 9 := by
            calc
              Nat.card (↥(Rz ⊔ X)) = Nat.card (↥Rz) * Nat.card (↥X) :=
                card_sup_eq_mul_of_disjoint_of_le_normalizer (G := G) Rz X
                  hXnormRz hXRzdisj
              _ = 9 := by rw [hRz3, hXcard]
          have hsup_leO : Rz ⊔ X ≤ O := sup_le hRzleO hXleO
          apply Subgroup.eq_of_le_of_card_ge hsup_leO
          rw [hOcard, hsupcard]
        · have hRzEq : Rz = O := by
            apply Subgroup.eq_of_le_of_card_ge hRzleO
            rw [hRz9, hOcard]
          apply le_antisymm (sup_le hRzleO hXleO)
          rw [← hRzEq]
          exact le_sup_left
      have hsupCent : Rz ⊔ X ≤ Subgroup.centralizer ({(v : G)} : Set G) :=
        sup_le hRzcent hXcent
      have hvCentO : (v : G) ∈ Subgroup.centralizer (O : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro q hq
        have hq' : q ∈ Rz ⊔ X := by rw [hsupEq]; exact hq
        exact ((Subgroup.mem_centralizer_iff.mp (hsupCent hq')) (v : G) (by simp)).symm
      have hvCentU : (v : G) ∈ Subgroup.centralizer (c.U : Set G) := by
        apply (Subgroup.centralizer_le (show (c.U : Set G) ⊆ (O : Set G) from
          fun q hq => (hNeqU ▸ hNleO) hq))
        exact hvCentO
      have hvNormU : (v : G) ∈ Subgroup.normalizer (c.U : Set G) :=
        Subgroup.centralizer_le_normalizer (c.U : Set G) hvCentU
      have hvH : (v : G) ∈ c.Hhat := by
        rw [← hNormU]
        exact hvNormU
      have hvI : IsInvolution (v : G) := by
        refine ⟨?_, ?_⟩
        · intro hvEq
          exact hv1 (Subtype.ext hvEq)
        · have hvself := congrArg Subtype.val
            (hVgKlein.mul_self ⟨(v : G), v.property⟩)
          simpa only [Subgroup.coe_mul, Subgroup.coe_one, pow_two] using hvself
      have hvCentX' : ∀ q : G, q ∈ X →
          (v : G) * q * (v : G)⁻¹ = q := by
        intro q hq
        have hc := (Subgroup.mem_centralizer_iff.mp (hVgcentX v.property)) q hq
        calc
          (v : G) * q * (v : G)⁻¹ = q * (v : G) * (v : G)⁻¹ := by rw [hc]
          _ = q := by simp
      exact False.elim (firstCase_klein_no_centralizing_involution_of_inverted_card_three
        hmin c hfirst hklein hy hyH hXne hXle hXodd hXinv hXcard hvH hvI hvCentX')

/-- In restriction (7), the odd intersection `D ∩ VU` is trivial: the
alternative `N = U` forces the odd core `O(D)` to have order nine and
leads to a Sylow-`3` normalizer contradiction.  This is the
fixed-point-free input for the `KV`-action on the `b₄`-cosets. -/
public theorem firstCase_klein_restrictionSeven_N_eq_bot
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    {n : ℕ} {y : G} {X : Subgroup G}
    (hyJ : y ∈ firstCaseJ c n)
    (hn : 4 ≤ n) (hXne : X ≠ ⊥) (hXle : X ≤ c.Hhat)
    (hXodd : Nat.Coprime 2 (Nat.card X))
    (hXinv : ∀ x : G, x ∈ X → x ∈ invertedElements c.Hhat y)
    (hC_even : Even (Nat.card (Subgroup.centralizer (X : Set G))))
    (hN_even : Even (Nat.card ((Subgroup.normalizer (X : Set G) ⊓ c.Hhat : Subgroup G)))) :
    let D := c.Hhat ⊓ conjugateSubgroup c.Hhat y
    let N := D ⊓ (twoCoreOf c.Hhat ⊔ c.U)
    N = ⊥ := by
  classical
  intro D N
  have hy : IsInvolution y := by simpa [firstCaseJ] using hyJ |>.1
  have hyH : y ∉ c.Hhat := by simpa [firstCaseJ] using hyJ |>.2.1
  have hI : 4 ≤ Nat.card {z : G // z ∈ invertedElements c.Hhat y} := by
    rw [← firstCase_klein_coset_involution_card_eq c hy hyH]
    simpa [firstCaseJ] using hyJ |>.2.2 ▸ hn
  have hidx := firstCase_klein_restrictionSix_index_eq hmin c hfirst hklein hy hyH hI
  have hOidx := firstCase_klein_intersection_oddCore_index_two_of_index_six
    hmin c hfirst hklein hy hyH hidx
  have hrel := firstCase_klein_intersection_oddCore_relIndex_three
    hmin c hfirst hklein hy hyH hidx
  have hcardU := (firstCase_klein_restrictionSeven_card_three
    hmin c hfirst hklein hyJ hn hXne hXle hXodd hXinv hC_even hN_even).1
  have hcore := firstCase_klein_restrictionSeven_core
    hmin c hfirst hklein hyJ hXne hXle hXodd hXinv hC_even hN_even
  have hFUeq : c.FU = c.U := by
    have hFUle := fittingSubgroupOf_le c.U
    have hFUne : c.FU ≠ ⊥ := by
      obtain ⟨_, K, hKHall, hKne, _⟩ := firstCase_klein_data_complete hmin c hfirst hklein
      intro hbot
      apply hKne
      apply le_antisymm
      · intro k hk; exact hbot ▸ hKHall.1 hk
      · exact bot_le
    have hdvd : Nat.card c.FU ∣ 3 := by rw [← hcardU]; exact Subgroup.card_dvd_of_le hFUle
    have hle : Nat.card c.FU ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
    have hne1 : Nat.card c.FU ≠ 1 := by intro h; exact hFUne (Subgroup.eq_bot_of_card_eq c.FU h)
    have hcard : Nat.card c.FU = 3 := by interval_cases h : Nat.card c.FU <;> simp_all
    exact Subgroup.eq_of_le_of_card_ge hFUle (by rw [hcard, hcardU])
  have hHcard : Nat.card c.H = 8 * Nat.card c.U := by
    have hSU : (c.S : Subgroup G) ⊔ c.U = c.H :=
      fact_2_preamble_H_eq_SU hmin c
    have hUnorm : IsNormalIn c.U c.H := by
      change IsNormalIn (oddCoreOf c.H) c.H
      refine ⟨?_, ?_⟩
      · intro x hx
        rcases Subgroup.mem_map.mp hx with ⟨u, hu, rfl⟩
        exact u.2
      · intro h hh u hu
        rcases Subgroup.mem_map.mp hu with ⟨u0, hu0, rfl⟩
        refine Subgroup.mem_map.mpr ⟨
          (⟨h, hh⟩ : c.H) * u0 * (⟨h, hh⟩ : c.H)⁻¹, ?_, by simp⟩
        exact (pPrimeCore_normal (p := 2) (G := c.H)).conj_mem
          u0 hu0 (⟨h, hh⟩ : c.H)
    have hSleH : (c.S : Subgroup G) ≤ c.H := centralizerSetup_S_le_H c
    have hSnormU : (c.S : Subgroup G) ≤ Subgroup.normalizer (c.U : Set G) :=
      hSleH.trans (le_normalizer_of_isNormalIn hUnorm)
    have hUcop : Nat.Coprime 2 (Nat.card c.U) := by
      change Nat.Coprime 2 (Nat.card (oddCoreOf c.H))
      rw [show Nat.card (oddCoreOf c.H) = Nat.card (pPrimeCore 2 c.H) by
        simpa [oddCoreOf] using
          (Subgroup.card_map_of_injective (K := pPrimeCore 2 c.H)
            c.H.subtype_injective)]
      exact pPrimeCore_coprime_card (p := 2) (G := c.H)
    have hScop : Nat.Coprime (Nat.card (c.S : Subgroup G)) (Nat.card c.U) := by
      have hSpow : ∃ k : ℕ, Nat.card (c.S : Subgroup G) = 2 ^ k := by
        obtain ⟨e⟩ := c.dihedralEquiv
        have hcard : Nat.card (c.S : Subgroup G) = 2 * 2 ^ c.m :=
          (Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card
        refine ⟨c.m + 1, ?_⟩
        calc
          Nat.card (c.S : Subgroup G) = 2 * 2 ^ c.m := hcard
          _ = 2 ^ (c.m + 1) := by rw [pow_succ]; ring
      obtain ⟨k, hk⟩ := hSpow
      rw [hk]
      exact hUcop.pow_left _
    have hdisj : Disjoint (c.S : Subgroup G) c.U :=
      Subgroup.disjoint_of_coprime_natCard hScop
    rw [← hSU]
    rw [sup_comm (c.S : Subgroup G) c.U]
    rw [card_sup_eq_mul_of_disjoint_of_le_normalizer (G := G)
      c.U (c.S : Subgroup G) hSnormU hdisj.symm]
    rw [firstCase_klein_S_card hmin c hfirst hklein]
    ring
  have hNleU := firstCase_klein_restrictionSeven_N_le_U hmin c hfirst hklein hy hyH hidx
  let O : Subgroup G := oddCoreOf D
  have hNleU' : N ≤ c.U := by
    simpa [D, N] using hNleU
  have hOidx' : (O.subgroupOf D).index = 2 := by
    simpa [D, O] using hOidx
  have hrel' : N.relIndex O = 3 := by
    simpa [D, N, O] using hrel
  by_cases hNbot : N = ⊥
  · exact hNbot
  · have hNcard_dvd : Nat.card N ∣ Nat.card c.U :=
      Subgroup.card_dvd_of_le hNleU'
    have hNcard_dvd3 : Nat.card N ∣ 3 := by
      simpa [hcardU] using hNcard_dvd
    have hNcard : Nat.card N = 3 := by
      have hne1 : Nat.card N ≠ 1 := by
        intro h1
        apply hNbot
        exact Subgroup.eq_bot_of_card_eq N h1
      rcases (Nat.dvd_prime Nat.prime_three).mp hNcard_dvd3 with h1 | h3
      · exact (hne1 h1).elim
      · exact h3
    have hNeqU : N = c.U := by
      apply Subgroup.eq_of_le_of_card_ge hNleU'
      rw [hNcard, hcardU]
    have hNleD : N ≤ D := inf_le_left
    have hNnormal : (N.subgroupOf D).Normal := by
      apply (Subgroup.normal_subgroupOf_iff (show N ≤ D from inf_le_left)).2
      intro n0 d0 hn0 hd0
      refine ⟨?_, ?_⟩
      · exact D.mul_mem (D.mul_mem hd0 (hNleD hn0)) (D.inv_mem hd0)
      · have hBnorm : IsNormalIn (twoCoreOf c.Hhat ⊔ c.U) c.Hhat :=
          firstCase_klein_VU_normal_in_Hhat hmin c
        exact hBnorm.2 d0 ((inf_le_left : D ≤ c.Hhat) hd0) n0
          ((inf_le_right : N ≤ twoCoreOf c.Hhat ⊔ c.U) hn0)
    have hNodd : Nat.Coprime 2 (Nat.card N) :=
      firstCase_klein_intersection_odd_of_index_six
        hmin c hfirst hklein hy hyH hidx
    have hNsubodd : Nat.Coprime 2 (Nat.card (N.subgroupOf D)) := by
      have hcardNsub : Nat.card (N.subgroupOf D) = Nat.card N :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show N ≤ D from inf_le_left)).toEquiv
      rw [hcardNsub]
      exact hNodd
    have hNsub_core : N.subgroupOf D ≤ pPrimeCore 2 (↥D) := by
      exact le_sSup ⟨hNnormal, hNsubodd⟩
    have hmapN : (N.subgroupOf D).map D.subtype = N :=
      Subgroup.map_subgroupOf_eq_of_le (show N ≤ D from inf_le_left)
    have hNleO : N ≤ O := by
      dsimp [O, oddCoreOf]
      rw [← hmapN]
      exact Subgroup.map_mono hNsub_core
    have hOcard : Nat.card O = 9 := by
      have hrel'' : (N.subgroupOf O).index = 3 := by
        exact hrel'
      have hcardNsubO : Nat.card (N.subgroupOf O) = Nat.card N := by
        exact Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe hNleO).toEquiv
      have hm := (N.subgroupOf O).card_mul_index
      rw [hcardNsubO, hNcard, hrel''] at hm
      norm_num at hm ⊢
      exact hm.symm
    have hXleD : X ≤ D := by
      intro z hz
      refine ⟨hXle hz, ?_⟩
      apply Subgroup.mem_map.mpr
      refine ⟨z⁻¹, ?_, ?_⟩
      · have hzInv := (hXinv z hz).2
        exact hXle (X.inv_mem hz)
      · have hzInv := (hXinv z hz).2
        calc
          y * z⁻¹ * y⁻¹ = (y * z * y⁻¹)⁻¹ := by group
          _ = (z⁻¹)⁻¹ := by rw [hzInv]
          _ = z := by simp
    have hXleO : X ≤ O := by
      let XD : Subgroup (↥D) := X.subgroupOf D
      let OD : Subgroup (↥D) := O.subgroupOf D
      have hXDodd : Odd (Nat.card XD) := by
        have hcardXD : Nat.card XD = Nat.card X := by
          exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXleD).toEquiv
        rw [hcardXD]
        exact Nat.coprime_two_left.mp hXodd
      have hODnormal : OD.Normal := by
        apply (Subgroup.normal_subgroupOf_iff (show O ≤ D from by
          dsimp [O]
          exact Subgroup.map_subtype_le (pPrimeCore 2 (↥D)))).2
        intro o0 d0 ho0 hd0
        rcases Subgroup.mem_map.mp ho0 with ⟨o1, ho1, rfl⟩
        let d0' : D := ⟨d0, hd0⟩
        exact Subgroup.mem_map.mpr ⟨d0' * o1 * d0'⁻¹,
          (pPrimeCore_normal (p := 2) (G := (↥D))).conj_mem
            o1 ho1 d0', by simp [d0']⟩
      have hODindex : OD.index = 2 := by
        simpa [OD] using hOidx'
      have hle : XD ≤ OD :=
        odd_card_subgroup_le_normal_index_two OD XD hODnormal hODindex hXDodd
      intro z hz
      have hz' : (⟨z, hXleD hz⟩ : D) ∈ XD := by
        exact hz
      exact Subgroup.mem_subgroupOf.mp (hle hz')
    have hUXdisj : Disjoint c.U X := by
      apply (disjoint_iff_inf_le).2
      intro z hz
      have hInf := firstCase_klein_inverted_subgroup_inf_VU_eq_bot
        hmin c hfirst hklein hy hyH hXle hXinv
      have hzbot : z ∈ (⊥ : Subgroup G) := by
        rw [← hInf]
        exact ⟨hz.2, (show z ∈ twoCoreOf c.Hhat ⊔ c.U from
          (le_sup_right : c.U ≤ twoCoreOf c.Hhat ⊔ c.U) hz.1)⟩
      exact hzbot
    have hUnormX : c.U ≤ Subgroup.normalizer (X : Set G) := by
      exact (hFUeq ▸ (firstCase_klein_restrictionSeven_core
        hmin c hfirst hklein hyJ hXne hXle hXodd hXinv hC_even hN_even).2).trans
        (Subgroup.centralizer_le_normalizer (X : Set G))
    have hUXcard : Nat.card (↥(c.U ⊔ X)) = 9 := by
      rw [sup_comm c.U X]
      rw [card_sup_eq_mul_of_disjoint_of_le_normalizer (G := G) X c.U
        hUnormX hUXdisj.symm, hcore.1, hcardU]
    have hOleD : O ≤ D := by
      dsimp [O]
      exact Subgroup.map_subtype_le (pPrimeCore 2 (↥D))
    have hUXleO : c.U ⊔ X ≤ O := by
      exact sup_le (hNeqU ▸ hNleO) hXleO
    have hOeqUX : O = c.U ⊔ X := by
      symm
      apply Subgroup.eq_of_le_of_card_ge hUXleO
      rw [hOcard, hUXcard]
    obtain ⟨g, hgnot, hXgU, hDgEq⟩ :=
      firstCase_klein_restrictionSeven_normalizer_intersection
        hmin c hfirst hklein hyJ hn hXne hXle hXodd hXinv hC_even hN_even
    let A' : Subgroup G := conjugateSubgroup c.Hhat g⁻¹
    let E : Subgroup G := c.Hhat ⊓ A'
    let Vg : Subgroup G := conjugateSubgroup (twoCoreOf c.Hhat) g⁻¹
    have hEeq : E = Subgroup.normalizer (X : Set G) ⊓ c.Hhat := by
      simpa [E, A'] using hDgEq
    have hXcard : Nat.card X = 3 := hcore.1
    have hVgcentX : Vg ≤ Subgroup.centralizer (X : Set G) := by
      have hVcentU : twoCoreOf c.Hhat ≤ Subgroup.centralizer (c.U : Set G) := by
        simpa [(theorem_2_6 hmin c).1] using
          twoCoreOf_centralizes_oddCoreOf c.Hhat
      have hmapU : conjugateSubgroup c.U g⁻¹ = X := by
        have hm := congrArg (fun K : Subgroup G => conjugateSubgroup K g⁻¹) hXgU
        have hcancel : conjugateSubgroup (conjugateSubgroup X g) g⁻¹ = X := by
          simpa using (conj_inv_then_conj_eq X g⁻¹)
        rw [hcancel] at hm
        exact hm.symm
      change (twoCoreOf c.Hhat).map (MulAut.conj g⁻¹).toMonoidHom ≤
        Subgroup.centralizer (X : Set G)
      rw [← hmapU]
      exact centralizer_map_le_of_conj c.U (twoCoreOf c.Hhat) g hVcentU
    have hVgKlein : IsKleinFour Vg := by
      change IsKleinFour ((twoCoreOf c.Hhat).map (MulAut.conj g⁻¹).toMonoidHom)
      exact isKleinFour_map_mulEquiv (twoCoreOf c.Hhat)
        (firstCase_klein_V_klein c hklein) (MulAut.conj g⁻¹)
    have hVgcard : Nat.card Vg = 4 := hVgKlein.card_four
    have hVgleA' : Vg ≤ A' := by
      dsimp [Vg, A']
      exact Subgroup.map_mono (Subgroup.map_subtype_le (pCore 2 c.Hhat))
    have hVgnormA' : IsNormalIn Vg A' := by
      refine ⟨hVgleA', ?_⟩
      intro a ha v hv
      rcases Subgroup.mem_map.mp ha with ⟨a0, ha0, rfl⟩
      rcases Subgroup.mem_map.mp hv with ⟨v0, hv0, rfl⟩
      refine Subgroup.mem_map.mpr ⟨a0 * v0 * a0⁻¹, ?_, ?_⟩
      · have hVnorm : IsNormalIn (twoCoreOf c.Hhat) c.Hhat := by
          refine ⟨Subgroup.map_subtype_le (pCore 2 c.Hhat), ?_⟩
          intro h hh v hv
          rcases Subgroup.mem_map.mp hv with ⟨v0, hv0, rfl⟩
          exact Subgroup.mem_map.mpr ⟨(⟨h, hh⟩ : c.Hhat) * v0 *
            (⟨h, hh⟩ : c.Hhat)⁻¹,
            (pCore_normal (p := 2) (G := c.Hhat)).conj_mem v0 hv0
              (⟨h, hh⟩ : c.Hhat), by simp⟩
        exact hVnorm.2 a0 ha0 v0 hv0
      · simpa [MulAut.conj_apply] using
          (show g⁻¹ * (a0 * v0 * a0⁻¹) * g =
            (g⁻¹ * a0 * g) * (g⁻¹ * v0 * g) *
              (g⁻¹ * a0 * g)⁻¹ by group)
    have hE_le_normVg : E ≤ Subgroup.normalizer (Vg : Set G) := by
      exact (inf_le_right : E ≤ A').trans (le_normalizer_of_isNormalIn hVgnormA')
    have hEVg_bot : E ⊓ Vg = ⊥ := by
      apply le_bot_iff.mp
      intro z hz
      by_cases hz1 : z = 1
      · exact Subgroup.mem_bot.mpr hz1
      have hzI : IsInvolution z := by
        refine ⟨hz1, ?_⟩
        simpa [pow_two] using congrArg Subtype.val
          (hVgKlein.mul_self ⟨z, hz.2⟩)
      have hzH : z ∈ c.Hhat := (inf_le_left : E ≤ c.Hhat) hz.1
      have hzcent : ∀ q : G, q ∈ X → z * q * z⁻¹ = q := by
        intro q hq
        have hc := (Subgroup.mem_centralizer_iff.mp (hVgcentX hz.2)) q hq
        calc
          z * q * z⁻¹ = q * z * z⁻¹ := by rw [hc]
          _ = q := by simp
      exact False.elim (firstCase_klein_no_centralizing_involution_of_inverted_card_three
        hmin c hfirst hklein hy hyH hXne hXle hXodd hXinv hXcard hzH hzI hzcent)
    have hEeven : Even (Nat.card E) := by
      rw [hEeq]
      exact hN_even
    have hO_le_E : O ≤ E := by
      rw [hEeq]
      rw [hOeqUX]
      apply sup_le <;> apply le_inf
      · exact hUnormX
      · exact (theorem_2_6 hmin c).1 ▸
          (Subgroup.map_subtype_le (pPrimeCore 2 c.Hhat))
      · exact Subgroup.le_normalizer
      · exact hXle
    have hEcard_dvd : 4 * Nat.card E ∣ 72 := by
      have hAsup : Vg ⊔ E ≤ A' := sup_le hVgleA' inf_le_right
      have hcardSup : Nat.card (↥(Vg ⊔ E)) = 4 * Nat.card E := by
        rw [card_sup_eq_mul_of_disjoint_of_le_normalizer (G := G) Vg E
          hE_le_normVg (by simpa [disjoint_iff_inf_le, inf_comm] using hEVg_bot)]
        rw [hVgcard]
      have hdvd := Subgroup.card_dvd_of_le hAsup
      rw [hcardSup] at hdvd
      have hAcard : Nat.card A' = 72 := by
        have hHhatH : Nat.card c.Hhat = 3 * Nat.card c.H := by
          have hidxH := firstCase_H_index_eq_three_mul_Hhat_index hmin c hfirst hklein
          have hmulH := c.H.card_mul_index
          have hmulHH := c.Hhat.card_mul_index
          have hpos : 0 < c.Hhat.index := by
            rw [Subgroup.index_eq_card]
            exact Nat.card_pos
          apply Nat.eq_of_mul_eq_mul_right hpos
          calc
            Nat.card c.Hhat * c.Hhat.index = Nat.card G := hmulHH
            _ = Nat.card c.H * c.H.index := hmulH.symm
            _ = Nat.card c.H * (3 * c.Hhat.index) := by rw [hidxH]
            _ = (3 * Nat.card c.H) * c.Hhat.index := by ring
        have hconjcard : Nat.card A' = Nat.card c.Hhat := by
          exact Nat.card_congr
            (Subgroup.equivMapOfInjective c.Hhat (MulAut.conj g⁻¹).toMonoidHom
              (MulAut.conj g⁻¹).injective).toEquiv.symm
        rw [hconjcard, hHhatH, hHcard, hcardU]
      rw [hAcard] at hdvd
      exact hdvd
    have hEcard_le : Nat.card E ≤ 18 := by
      have hle : 4 * Nat.card E ≤ 72 := Nat.le_of_dvd (by norm_num) hEcard_dvd
      omega
    have hEcard_lower : 18 ≤ Nat.card E := by
      have hOcarddvd : Nat.card O ∣ Nat.card E := Subgroup.card_dvd_of_le hO_le_E
      have h2dvd : 2 ∣ Nat.card E := hEeven.two_dvd
      have h18dvd : 18 ∣ Nat.card E := by
        have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 2 9)
          h2dvd (by simpa [hOcard] using hOcarddvd)
        norm_num at this ⊢
        exact this
      exact Nat.le_of_dvd (Nat.card_pos) h18dvd
    have hEcard : Nat.card E = 18 := by omega
    have hVne : twoCoreOf c.Hhat ≠ ⊥ := by
      intro hbot
      have hfour := (firstCase_klein_V_klein c hklein).card_four
      rw [hbot] at hfour
      simp at hfour
    have hUne : c.U ≠ ⊥ := (lemma_2_2 hmin c).2
    have hNormU : Subgroup.normalizer (c.U : Set G) = c.Hhat :=
      theorem26_normalizer_U_eq_Hhat hmin c hVne hUne
    have hNormMap : conjugateSubgroup (Subgroup.normalizer (X : Set G)) g = c.Hhat := by
      change (Subgroup.normalizer (X : Set G)).map
        (MulAut.conj g).toMonoidHom = _
      rw [Subgroup.map_normalizer_eq_of_bijective X (MulAut.conj g).bijective]
      change Subgroup.normalizer (conjugateSubgroup X g : Set G) = c.Hhat
      rw [hXgU, hNormU]
    have hyNormX : y ∈ Subgroup.normalizer (X : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · intro hz
        rw [(hXinv z hz).2]
        exact X.inv_mem hz
      · intro hz
        have hz' := hXinv (y * z * y⁻¹) hz
        have hy2 : y * y = 1 := by simpa [pow_two] using hy.2
        have hcalc : y * (y * z * y⁻¹) * y⁻¹ = z := by
          have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
          calc
            y * (y * z * y⁻¹) * y⁻¹ = (y * y) * z * (y⁻¹ * y⁻¹) := by group
            _ = (y * y) * z * (y * y) := by rw [hyinv]
            _ = z := by simp [hy2]
        have heq : z = (y * z * y⁻¹)⁻¹ := by
          calc
            z = y * (y * z * y⁻¹) * y⁻¹ := hcalc.symm
            _ = (y * z * y⁻¹)⁻¹ := hz'.2
        rw [heq]
        exact X.inv_mem hz
    have hyA' : y ∈ A' := by
      have hgy : g * y * g⁻¹ ∈ c.Hhat := by
        rw [← hNormMap]
        exact Subgroup.mem_map.mpr ⟨y, hyNormX, rfl⟩
      exact Subgroup.mem_map.mpr ⟨g * y * g⁻¹, hgy, by
        simpa [MulAut.conj_apply] using
          (show g⁻¹ * (g * y * g⁻¹) * g = y by group)⟩
    have hDmap_le : conjugateSubgroup D y ≤ D := by
      intro z hz
      rcases Subgroup.mem_map.mp hz with ⟨d0, hd0, rfl⟩
      refine ⟨?_, ?_⟩
      · rcases Subgroup.mem_map.mp hd0.2 with ⟨h0, hh0, hEq⟩
        change y * d0 * y⁻¹ ∈ c.Hhat
        rw [← hEq]
        have hy2 : y * y = 1 := by simpa [pow_two] using hy.2
        change y * (y * h0 * y⁻¹) * y⁻¹ ∈ c.Hhat
        have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
        have hcalc : y * (y * h0 * y⁻¹) * y⁻¹ = h0 := by
          calc
            y * (y * h0 * y⁻¹) * y⁻¹ = (y * y) * h0 * (y⁻¹ * y⁻¹) := by group
            _ = (y * y) * h0 * (y * y) := by rw [hyinv]
            _ = h0 := by simp [hy2]
        rw [hcalc]
        exact hh0
      · change y * d0 * y⁻¹ ∈ conjugateSubgroup c.Hhat y
        apply Subgroup.mem_map.mpr
        exact ⟨d0, hd0.1, rfl⟩
    have hUconj_leD : conjugateSubgroup c.U y ≤ D := by
      exact (Subgroup.map_mono (show c.U ≤ D from
        (hNeqU ▸ hNleO).trans hOleD)).trans hDmap_le
    have hUconj_leO : conjugateSubgroup c.U y ≤ O := by
      let UY : Subgroup G := conjugateSubgroup c.U y
      let UYD : Subgroup (↥D) := UY.subgroupOf D
      have hUYcard : Nat.card UYD = 3 := by
        have hcardmap : Nat.card UY = Nat.card c.U := by
          exact Nat.card_congr
            (Subgroup.equivMapOfInjective c.U (MulAut.conj y).toMonoidHom
              (MulAut.conj y).injective).toEquiv.symm
        have hsubcard : Nat.card UYD = Nat.card UY := by
          exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUconj_leD).toEquiv
        rw [hsubcard, hcardmap, hcardU]
      have hUYodd : Odd (Nat.card UYD) := by rw [hUYcard]; norm_num
      have hODnormal : (O.subgroupOf D).Normal := by
        apply (Subgroup.normal_subgroupOf_iff (show O ≤ D from hOleD)).2
        intro o0 d0 ho0 hd0
        rcases Subgroup.mem_map.mp ho0 with ⟨o1, ho1, rfl⟩
        let d0' : D := ⟨d0, hd0⟩
        exact Subgroup.mem_map.mpr ⟨d0' * o1 * d0'⁻¹,
          (pPrimeCore_normal (p := 2) (G := (↥D))).conj_mem o1 ho1 d0', by simp [d0']⟩
      have hle : UYD ≤ O.subgroupOf D := by
        exact odd_card_subgroup_le_normal_index_two
          (O.subgroupOf D) UYD hODnormal hOidx' hUYodd
      intro z hz
      have hz' : (⟨z, hUconj_leD hz⟩ : D) ∈ UYD := hz
      exact Subgroup.mem_subgroupOf.mp (hle hz')
    have hmapOle : conjugateSubgroup O y ≤ O := by
      change (O.map (MulAut.conj y).toMonoidHom) ≤ O
      rw [hOeqUX, Subgroup.map_sup]
      have hXmap : conjugateSubgroup X y ≤ X := by
        intro z hz
        rcases Subgroup.mem_map.mp hz with ⟨x0, hx0, rfl⟩
        change y * x0 * y⁻¹ ∈ X
        rw [(hXinv x0 hx0).2]
        exact X.inv_mem hx0
      apply sup_le
      · have hUmap : (c.U.map (MulAut.conj y).toMonoidHom) ≤ O := by
          simpa [conjugateSubgroup] using hUconj_leO
        rw [hOeqUX] at hUmap
        exact hUmap
      · exact hXmap.trans le_sup_right
    have hyNormO : y ∈ Subgroup.normalizer (O : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      apply le_antisymm hmapOle
      intro z hz
      apply Subgroup.mem_map.mpr
      have hzmap : y * z * y⁻¹ ∈ conjugateSubgroup O y := by
        exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
      refine ⟨y * z * y⁻¹, hmapOle hzmap, ?_⟩
      have hy2 : y * y = 1 := by simpa [pow_two] using hy.2
      have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
      calc
        y * (y * z * y⁻¹) * y⁻¹ = (y * y) * z * (y⁻¹ * y⁻¹) := by group
        _ = (y * y) * z * (y * y) := by rw [hyinv]
        _ = z := by simp [hy2]
    have hE_normO : E ≤ Subgroup.normalizer (O : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      intro e he z hz
      have heH : e ∈ c.Hhat := (inf_le_left : E ≤ c.Hhat) he
      have heX : e ∈ Subgroup.normalizer (X : Set G) := by
        rw [hEeq] at he
        exact (inf_le_left : Subgroup.normalizer (X : Set G) ⊓ c.Hhat ≤
          Subgroup.normalizer (X : Set G)) he
      have hUnormH : IsNormalIn c.U c.Hhat := by
        rw [(theorem_2_6 hmin c).1]
        refine ⟨Subgroup.map_subtype_le (pPrimeCore 2 c.Hhat), ?_⟩
        intro h hh u hu
        rcases Subgroup.mem_map.mp hu with ⟨u0, hu0, rfl⟩
        exact Subgroup.mem_map.mpr ⟨
          (⟨h, hh⟩ : c.Hhat) * u0 * (⟨h, hh⟩ : c.Hhat)⁻¹,
          (pPrimeCore_normal (p := 2) (G := c.Hhat)).conj_mem
            u0 hu0 (⟨h, hh⟩ : c.Hhat), by simp⟩
      have hmapO : conjugateSubgroup O e ≤ O := by
        change O.map (MulAut.conj e).toMonoidHom ≤ O
        rw [hOeqUX, Subgroup.map_sup]
        apply sup_le
        · have hUmap : c.U.map (MulAut.conj e).toMonoidHom ≤ c.U := by
            intro u hu
            rcases Subgroup.mem_map.mp hu with ⟨u0, hu0, rfl⟩
            exact hUnormH.2 e heH u0 hu0
          exact hUmap.trans le_sup_left
        · have hXmap : conjugateSubgroup X e ≤ X := by
            intro x0 hx0
            rcases Subgroup.mem_map.mp hx0 with ⟨x1, hx1, rfl⟩
            exact (Subgroup.mem_normalizer_iff.mp heX x1).mp hx1
          exact hXmap.trans le_sup_right
      have hzmap : e * z * e⁻¹ ∈ conjugateSubgroup O e := by
        exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
      exact hmapO hzmap
    have hOleA' : O ≤ A' := hO_le_E.trans inf_le_right
    let O' : Subgroup (↥A') := O.subgroupOf A'
    have hO'card : Nat.card O' = 9 := by
      have hsubcard : Nat.card O' = Nat.card O := by
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOleA').toEquiv
      rw [hsubcard, hOcard]
    have hAcard : Nat.card A' = 72 := by
      have hHhatH : Nat.card c.Hhat = 3 * Nat.card c.H := by
        have hidxH := firstCase_H_index_eq_three_mul_Hhat_index hmin c hfirst hklein
        have hmulH := c.H.card_mul_index
        have hmulHH := c.Hhat.card_mul_index
        have hpos : 0 < c.Hhat.index := by
          rw [Subgroup.index_eq_card]
          exact Nat.card_pos
        apply Nat.eq_of_mul_eq_mul_right hpos
        calc
          Nat.card c.Hhat * c.Hhat.index = Nat.card G := hmulHH
          _ = Nat.card c.H * c.H.index := hmulH.symm
          _ = Nat.card c.H * (3 * c.Hhat.index) := by rw [hidxH]
          _ = (3 * Nat.card c.H) * c.Hhat.index := by ring
      have hconjcard : Nat.card A' = Nat.card c.Hhat := by
        exact Nat.card_congr
          (Subgroup.equivMapOfInjective c.Hhat (MulAut.conj g⁻¹).toMonoidHom
            (MulAut.conj g⁻¹).injective).toEquiv.symm
      rw [hconjcard, hHhatH, hHcard, hcardU]
    let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hAfac : (Nat.card A').factorization 3 = 2 := by
      rw [hAcard]
      rw [show (72 : ℕ) = 3 ^ 2 * 8 by norm_num]
      rw [Nat.factorization_mul (by norm_num) (by norm_num)]
      rw [Nat.factorization_pow]
      simp [Nat.prime_three.factorization_self]
      exact Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ (8 : ℕ))
    let P : Sylow 3 (↥A') := Sylow.ofCard O' (by
      rw [hO'card, hAfac]
      norm_num)
    have hPsub : (P : Subgroup (↥A')) = O' := by rfl
    have hEsub_le : E.subgroupOf A' ≤ Subgroup.normalizer (P : Set (↥A')) := by
      apply (Subgroup.le_normalizer_iff).2
      intro e he p hp
      rw [hPsub] at hp ⊢
      have hpO : (p : G) ∈ O := Subgroup.mem_subgroupOf.mp hp
      have hiff := (Subgroup.mem_normalizer_iff.mp (hE_normO he)) (p : G)
      exact Subgroup.mem_subgroupOf.mpr (hiff.mp hpO)
    have hySub_mem : (⟨y, hyA'⟩ : A') ∈ Subgroup.normalizer (P : Set (↥A')) := by
      apply (Subgroup.mem_normalizer_iff).2
      intro p
      constructor
      · intro hp
        rw [hPsub] at hp ⊢
        have hpO : (p : G) ∈ O := Subgroup.mem_subgroupOf.mp hp
        have hiff := (Subgroup.mem_normalizer_iff.mp hyNormO) (p : G)
        exact Subgroup.mem_subgroupOf.mpr (hiff.mp hpO)
      · intro hp
        rw [hPsub] at hp ⊢
        have hpOconj : y * (p : G) * y⁻¹ ∈ O := by
          simpa using (Subgroup.mem_subgroupOf.mp hp)
        have hiff := (Subgroup.mem_normalizer_iff.mp hyNormO) (p : G)
        exact Subgroup.mem_subgroupOf.mpr (hiff.mpr hpOconj)
    have hEsubcard : Nat.card (E.subgroupOf A') = 18 := by
      have hsubcard : Nat.card (E.subgroupOf A') = Nat.card E := by
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : E ≤ A')).toEquiv
      rw [hsubcard, hEcard]
    have hNPAcard_dvd : Nat.card (Subgroup.normalizer (P : Set (↥A'))) ∣ 72 := by
      have hle : Subgroup.normalizer (P : Set (↥A')) ≤ (⊤ : Subgroup (↥A')) := le_top
      simpa [hAcard] using Subgroup.card_dvd_of_le hle
    have hEsubcard_dvd : Nat.card (E.subgroupOf A') ∣
        Nat.card (Subgroup.normalizer (P : Set (↥A'))) :=
      Subgroup.card_dvd_of_le hEsub_le
    have h18dvdN : 18 ∣ Nat.card (Subgroup.normalizer (P : Set (↥A'))) := by
      rw [← hEsubcard]
      exact hEsubcard_dvd
    have hy_not_Esub : (⟨y, hyA'⟩ : A') ∉ E.subgroupOf A' := by
      intro hyE
      have hyE' : y ∈ E := Subgroup.mem_subgroupOf.mp hyE
      exact hyH ((inf_le_left : E ≤ c.Hhat) hyE')
    have hNPAcard_lower : 36 ≤ Nat.card (Subgroup.normalizer (P : Set (↥A'))) := by
      have hNPAcard_ge : Nat.card (E.subgroupOf A') ≤
          Nat.card (Subgroup.normalizer (P : Set (↥A'))) :=
        Nat.le_of_dvd (Nat.card_pos) hEsubcard_dvd
      have hNPAne : Nat.card (Subgroup.normalizer (P : Set (↥A'))) ≠
          Nat.card (E.subgroupOf A') := by
        intro heq
        have hEqSub : E.subgroupOf A' = Subgroup.normalizer (P : Set (↥A')) :=
          Subgroup.eq_of_le_of_card_ge hEsub_le (by simpa [heq])
        exact hy_not_Esub (by rw [hEqSub]; exact hySub_mem)
      rw [hEsubcard] at hNPAcard_ge hNPAne
      obtain ⟨k, hk⟩ := h18dvdN
      have hkpos : 0 < k := by
        have hpos : 0 < Nat.card (Subgroup.normalizer (P : Set (↥A'))) := Nat.card_pos
        omega
      have hkge2 : 2 ≤ k := by omega
      rw [hk] at hNPAne ⊢
      omega
    have hNPAindex_mul : Nat.card (Subgroup.normalizer (P : Set (↥A'))) *
        (Subgroup.normalizer (P : Set (↥A'))).index = Nat.card (↥A') :=
      (Subgroup.normalizer (P : Set (↥A'))).card_mul_index
    have hNPAindex_le : (Subgroup.normalizer (P : Set (↥A'))).index ≤ 2 := by
      have hidxpos : 0 < (Subgroup.normalizer (P : Set (↥A'))).index := by
        rw [Subgroup.index_eq_card]
        exact Nat.card_pos
      rw [hAcard] at hNPAindex_mul
      by_contra hidx
      have hidxge : 3 ≤ (Subgroup.normalizer (P : Set (↥A'))).index := by omega
      have hmul_le :
          36 * 3 ≤
            Nat.card (Subgroup.normalizer (P : Set (↥A'))) *
              (Subgroup.normalizer (P : Set (↥A'))).index :=
        Nat.mul_le_mul hNPAcard_lower hidxge
      rw [hNPAindex_mul] at hmul_le
      norm_num at hmul_le
    have hNPAindex_cases : (Subgroup.normalizer (P : Set (↥A'))).index = 1 ∨
        (Subgroup.normalizer (P : Set (↥A'))).index = 2 := by
      have hidxpos : 0 < (Subgroup.normalizer (P : Set (↥A'))).index := by
        rw [Subgroup.index_eq_card]
        exact Nat.card_pos
      rcases Nat.lt_or_eq_of_le hNPAindex_le with hlt | heq
      · left
        have hle1 : (Subgroup.normalizer (P : Set (↥A'))).index ≤ 1 := by
          exact Nat.le_of_lt_succ (by simpa [Nat.succ_eq_add_one] using hlt)
        have hne0 : (Subgroup.normalizer (P : Set (↥A'))).index ≠ 0 :=
          Nat.ne_of_gt hidxpos
        have hone : 1 ≤ (Subgroup.normalizer (P : Set (↥A'))).index :=
          (Nat.one_le_iff_ne_zero).2 hne0
        exact Nat.le_antisymm hle1 hone
      · right
        exact heq
    have hSylCard : Nat.card (Sylow 3 (↥A')) =
        (Subgroup.normalizer (P : Set (↥A'))).index := by
      simpa [P] using P.card_eq_index_normalizer
    have hSylMod := card_sylow_modEq_one 3 (↥A')
    have hNPAindex_one : (Subgroup.normalizer (P : Set (↥A'))).index = 1 := by
      rcases hNPAindex_cases with h1 | h2
      · exact h1
      · rw [hSylCard, h2] at hSylMod
        norm_num at hSylMod
    have hNPA_top : Subgroup.normalizer (P : Set (↥A')) = ⊤ :=
      (Subgroup.index_eq_one.mp hNPAindex_one)
    have hPnormal : P.Normal := by
      apply Sylow.normal_of_normalizer_normal P
      rw [hNPA_top]
      infer_instance
    have hOsubnormal : (O.subgroupOf A').Normal := by
      change (O' : Subgroup (↥A')).Normal
      rw [← hPsub]
      exact hPnormal
    have hOnormalA' : IsNormalIn O A' := by
      refine ⟨hOleA', ?_⟩
      intro a ha o ho
      have ho' : (⟨o, hOleA' ho⟩ : A') ∈ O.subgroupOf A' :=
        Subgroup.mem_subgroupOf.mpr ho
      have hconj :
          (⟨a, ha⟩ : A') * (⟨o, hOleA' ho⟩ : A') * (⟨a, ha⟩ : A')⁻¹ ∈
            O.subgroupOf A' :=
        hOsubnormal.conj_mem (⟨o, hOleA' ho⟩ : A') ho'
          (⟨a, ha⟩ : A')
      exact Subgroup.mem_subgroupOf.mp hconj
    have hVg_normO : Vg ≤ Subgroup.normalizer (O : Set G) :=
      hVgleA'.trans (le_normalizer_of_isNormalIn hOnormalA')
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hVgP : IsPGroup 2 (↥Vg) := by
      apply IsPGroup.of_card (n := 2)
      rw [hVgcard]
      norm_num
    let : IsMulCommutative (↥Vg) := IsKleinFour.isMulCommutative
    let : CommGroup (↥Vg) := IsMulCommutative.instCommGroup
    let : Fact (IsPGroup 2 (↥Vg)) := ⟨hVgP⟩
    let : Vg.Normalizes O := ⟨hVg_normO⟩
    let : MulDistribMulAction (↥Vg) (↥O) :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer Vg O hVg_normO
    have hOodd : Nat.Coprime 2 (Nat.card (↥O)) := by
      rw [hOcard]
      norm_num
    have htop :=
      iSup_fixedPointSubgroup_zpowers_eq_top_of_noncyclic_abelian_pGroup_action
        (G := ↥O) (A := ↥Vg) (p := 2) (hG := hOodd)
        (hncyc := IsKleinFour.not_isCyclic)
    have htop_map : (⊤ : Subgroup (↥O)).map O.subtype = O := by
      simpa [MonoidHom.range_eq_map] using (Subgroup.range_subtype (H := O))
    have hnotall : ¬ ∀ v : ↥Vg, ∀ hv1 : v ≠ 1,
        (fixedPointSubgroup (↥(Subgroup.zpowers v)) (↥O)).map O.subtype ≤ X := by
      intro hall
      have hOleX : O ≤ X := by
        calc
          O = (⊤ : Subgroup (↥O)).map O.subtype := htop_map.symm
          _ = (⨆ (v : ↥Vg) (_ : v ≠ 1),
              fixedPointSubgroup (↥(Subgroup.zpowers v)) (↥O)).map O.subtype := by
                rw [htop]
          _ ≤ X := by
            rw [Subgroup.map_iSup]
            refine iSup_le ?_
            intro v
            rw [Subgroup.map_iSup]
            refine iSup_le ?_
            intro hv1
            exact hall v hv1
      have hdiv : Nat.card O ∣ Nat.card X := Subgroup.card_dvd_of_le hOleX
      rw [hOcard, hXcard] at hdiv
      norm_num at hdiv
    push_neg at hnotall
    rcases hnotall with ⟨v, hv1, hvnot⟩
    have hexmem : ∃ q : G, q ∈
        (fixedPointSubgroup (↥(Subgroup.zpowers v)) (↥O)).map O.subtype ∧
        q ∉ X := by
      by_contra h
      push_neg at h
      exact hvnot h
    rcases hexmem with ⟨z, hzmap, hzx⟩
    rcases Subgroup.mem_map.mp hzmap with ⟨zO, hzfix, rfl⟩
    let zG : G := zO
    have hzO : zG ∈ O := zO.property
    have hzxG : zG ∉ X := hzx
    have hzne : zG ≠ 1 := by
      intro hz1
      apply hzxG
      simpa [hz1] using X.one_mem
    have hzfix' := hzfix ⟨v, Subgroup.mem_zpowers v⟩
    have hvz : (v : G) * zG * (v : G)⁻¹ = zG := by
      have hcoe := congrArg Subtype.val hzfix'
      have hformula := Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe
        Vg O (a := v) (k := zO)
      exact hformula.symm.trans hcoe
    let : IsMulCommutative (↥O) := by
      apply IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3)
      simpa [hOcard]
    let : CommGroup (↥O) := IsMulCommutative.instCommGroup
    have hconj_eq_of_memO : ∀ a b : G, a ∈ O → b ∈ O →
        a * b * a⁻¹ = b := by
      intro a b ha hb
      have hcomm : a * b = b * a := congrArg Subtype.val
        (mul_comm (⟨a, ha⟩ : O) (⟨b, hb⟩ : O))
      calc
        a * b * a⁻¹ = b * a * a⁻¹ := by rw [hcomm]
        _ = b := by simp
    let Rz : Subgroup G := Subgroup.zpowers zG
    have hRzleO : Rz ≤ O := by
      exact Subgroup.zpowers_le.mpr hzO
    have hRzne : Rz ≠ ⊥ := by
      intro hbot
      apply hzne
      have hzRz : zG ∈ Rz := Subgroup.mem_zpowers zG
      rw [hbot] at hzRz
      exact Subgroup.mem_bot.mp hzRz
    have hRzcard_dvd : Nat.card Rz ∣ 9 := by
      have hd := Subgroup.card_dvd_of_le hRzleO
      simpa [hOcard] using hd
    have hRzcard_ne1 : Nat.card Rz ≠ 1 := by
      intro hcard
      exact hRzne (Subgroup.eq_bot_of_card_eq Rz hcard)
    have hRzcard_cases : Nat.card Rz = 3 ∨ Nat.card Rz = 9 := by
      have hdvdpow : Nat.card Rz ∣ 3 ^ 2 := by simpa using hRzcard_dvd
      rcases (Nat.dvd_prime_pow Nat.prime_three).mp hdvdpow with ⟨k, hk, hEq⟩
      have hkne0 : k ≠ 0 := by
        intro hk0
        apply hRzcard_ne1
        simpa [hk0] using hEq
      have hkpos : 1 ≤ k := (Nat.one_le_iff_ne_zero).2 hkne0
      rcases Nat.lt_or_eq_of_le hk with hlt | heq
      · left
        have hk1 : k = 1 := by omega
        simpa [hk1] using hEq
      · right
        simpa [heq] using hEq
    have hRzneX : Rz ≠ X := by
      intro heq
      apply hzxG
      have hzRz : zG ∈ Rz := Subgroup.mem_zpowers zG
      rw [heq] at hzRz
      exact hzRz
    have hXnormRz : X ≤ Subgroup.normalizer (Rz : Set G) := by
      intro a ha
      rw [Subgroup.mem_normalizer_iff]
      intro q
      constructor
      · intro hq
        rw [hconj_eq_of_memO a q (hXleO ha) (hRzleO hq)]
        exact hq
      · intro hq
        have hqO : a * q * a⁻¹ ∈ O := hRzleO hq
        have heq : q = a * q * a⁻¹ := by
          calc
            q = a⁻¹ * (a * q * a⁻¹) * a := by group
            _ = a * q * a⁻¹ := by
              simpa only [inv_inv] using hconj_eq_of_memO a⁻¹
                (a * q * a⁻¹) (O.inv_mem (hXleO ha)) hqO
        rw [heq]
        exact hq
    have hRzcent : Rz ≤ Subgroup.centralizer ({(v : G)} : Set G) := by
      intro q hq
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      have ht' : t = (v : G) := by simpa using ht
      subst t
      rcases Subgroup.mem_zpowers_iff.mp hq with ⟨m, rfl⟩
      have hcommEq : zG * (v : G) = (v : G) * zG := by
        have h := congrArg (fun r : G => r * (v : G)) hvz
        simpa [mul_assoc] using h.symm
      have hcomm : Commute zG (v : G) :=
        (commute_iff_eq zG (v : G)).2 hcommEq
      exact (hcomm.zpow_left m).eq.symm
    have hXcent : X ≤ Subgroup.centralizer ({(v : G)} : Set G) := by
      intro q hq
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      have ht' : t = (v : G) := by simpa using ht
      subst t
      exact (Subgroup.mem_centralizer_iff.mp (hVgcentX v.property) q hq).symm
    have hsupEq : Rz ⊔ X = O := by
      rcases hRzcard_cases with hRz3 | hRz9
      · have hXRzdisj : Disjoint Rz X := by
          apply (disjoint_iff_inf_le).2
          intro q hq
          by_cases hq1 : q = 1
          · exact Subgroup.mem_bot.mpr hq1
          · have heq := subgroup_eq_of_card_eq_prime_of_common_ne_one
              Nat.prime_three Rz X hRz3 hXcard hq.1 hq.2 hq1
            exact False.elim (hRzneX heq)
        have hsupcard : Nat.card (↥(Rz ⊔ X)) = 9 := by
          calc
            Nat.card (↥(Rz ⊔ X)) = Nat.card (↥Rz) * Nat.card (↥X) :=
              card_sup_eq_mul_of_disjoint_of_le_normalizer (G := G) Rz X
                hXnormRz hXRzdisj
            _ = 9 := by rw [hRz3, hXcard]
        have hsup_leO : Rz ⊔ X ≤ O := sup_le hRzleO hXleO
        apply Subgroup.eq_of_le_of_card_ge hsup_leO
        rw [hOcard, hsupcard]
      · have hRzEq : Rz = O := by
          apply Subgroup.eq_of_le_of_card_ge hRzleO
          rw [hRz9, hOcard]
        apply le_antisymm (sup_le hRzleO hXleO)
        rw [← hRzEq]
        exact le_sup_left
    have hsupCent : Rz ⊔ X ≤ Subgroup.centralizer ({(v : G)} : Set G) :=
      sup_le hRzcent hXcent
    have hvCentO : (v : G) ∈ Subgroup.centralizer (O : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have hq' : q ∈ Rz ⊔ X := by rw [hsupEq]; exact hq
      exact ((Subgroup.mem_centralizer_iff.mp (hsupCent hq')) (v : G) (by simp)).symm
    have hvCentU : (v : G) ∈ Subgroup.centralizer (c.U : Set G) := by
      apply (Subgroup.centralizer_le (show (c.U : Set G) ⊆ (O : Set G) from
        fun q hq => (hNeqU ▸ hNleO) hq))
      exact hvCentO
    have hvNormU : (v : G) ∈ Subgroup.normalizer (c.U : Set G) :=
      Subgroup.centralizer_le_normalizer (c.U : Set G) hvCentU
    have hvH : (v : G) ∈ c.Hhat := by
      rw [← hNormU]
      exact hvNormU
    have hvI : IsInvolution (v : G) := by
      refine ⟨?_, ?_⟩
      · intro hvEq
        exact hv1 (Subtype.ext hvEq)
      · have hvself := congrArg Subtype.val
          (hVgKlein.mul_self ⟨(v : G), v.property⟩)
        simpa only [Subgroup.coe_mul, Subgroup.coe_one, pow_two] using hvself
    have hvCentX' : ∀ q : G, q ∈ X →
        (v : G) * q * (v : G)⁻¹ = q := by
      intro q hq
      have hc := (Subgroup.mem_centralizer_iff.mp (hVgcentX v.property)) q hq
      calc
        (v : G) * q * (v : G)⁻¹ = q * (v : G) * (v : G)⁻¹ := by rw [hc]
        _ = q := by simp
    exact False.elim (firstCase_klein_no_centralizing_involution_of_inverted_card_three
      hmin c hfirst hklein hy hyH hXne hXle hXodd hXinv hXcard hvH hvI hvCentX')

end CFSG.GorensteinWalter
