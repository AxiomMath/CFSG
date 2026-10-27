module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinJ3CentralizerOdd
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinCardThreeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreA7
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.HhatQuotientS4
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearThreeQuotientInversion
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-! The source's final `A₀` route is discharged in the linear quotient: after
conjugating `y` to `t`, a nontrivial fixed subgroup `A₀` becomes `U`, and the
order-three subgroup inverted by `t` has nontrivial image in the `S₄` quotient.
The latter is impossible by `no_involution_inverts_of_quotient_linear_three_pgl2`.
-/

private theorem card_conjugate_local
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (g : G) :
    Nat.card (conjugateSubgroup H g) = Nat.card H := by
  unfold conjugateSubgroup
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

public theorem firstCase_klein_J3_A0_impossible
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    {y : G} (hyJ : y ∈ firstCaseJ c 3)
    {X : Subgroup G} (hXne : X ≠ ⊥) (hXle : X ≤ c.Hhat)
    (hXcard : Nat.card X = 3)
    (hXinv : ∀ x : G, x ∈ X → x ∈ invertedElements c.Hhat y)
    (hXinf : X ⊓ (twoCoreOf c.Hhat ⊔ c.U) = ⊥)
    (hA0ne : Subgroup.centralizer (X : Set G) ⊓
      Subgroup.centralizer ({y} : Set G) ≠ ⊥) : False := by
  classical
  have hy : IsInvolution y := by simpa [firstCaseJ] using hyJ |>.1
  have hyH : y ∉ c.Hhat := by simpa [firstCaseJ] using hyJ |>.2.1
  have hU3 : Nat.card c.U = 3 :=
    firstCase_klein_U_card_three_pre_b3 hmin c hfirst hklein
  have hVne : twoCoreOf c.Hhat ≠ ⊥ := by
    intro hbot
    have hfour := (firstCase_klein_V_klein c hklein).card_four
    have hcard : Nat.card (twoCoreOf c.Hhat) = 1 := by rw [hbot]; simp
    omega
  have hUne : c.U ≠ ⊥ := (lemma_2_2 hmin c).2
  have hNormU : Subgroup.normalizer (c.U : Set G) = c.Hhat :=
    theorem26_normalizer_U_eq_Hhat hmin c hVne hUne
  obtain ⟨g, hgy⟩ := fact_2_preamble_involutions_conjugate_proved
    hmin y c.t hy c.t_involution
  let A0 : Subgroup G := Subgroup.centralizer (X : Set G) ⊓
      Subgroup.centralizer ({y} : Set G)
  let A0g : Subgroup G := conjugateSubgroup A0 g
  have hA0gH : A0g ≤ c.H := by
    intro z hz
    rcases Subgroup.mem_map.mp hz with ⟨a, ha, hza⟩
    rw [c.H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
    have hza' : z = g * a * g⁻¹ := by
      simpa [A0g, conjugateSubgroup] using hza.symm
    rw [hza']
    rcases ha with ⟨_haX, hay⟩
    have hay' : a * y = y * a :=
      Subgroup.mem_centralizer_singleton_iff.mp hay
    calc
      (g * a * g⁻¹) * c.t = g * (a * y) * g⁻¹ := by rw [← hgy]; group
      _ = g * (y * a) * g⁻¹ := by rw [hay']
      _ = (g * y * g⁻¹) * (g * a * g⁻¹) := by group
      _ = c.t * (g * a * g⁻¹) := by rw [hgy]
  have hAodd : Nat.Coprime 2
      (Nat.card (Subgroup.centralizer (X : Set G))) := by
    exact Nat.coprime_two_left.mpr (firstCase_klein_J3_centralizer_odd
      hmin c hfirst hklein hyJ hXne hXle hXcard hXinv hXinf)
  have hA0leA : A0 ≤ Subgroup.centralizer (X : Set G) := inf_le_left
  have hA0odd : Nat.Coprime 2 (Nat.card A0) := by
    have hdvd : Nat.card A0 ∣
        Nat.card (Subgroup.centralizer (X : Set G)) :=
      Subgroup.card_dvd_of_le hA0leA
    exact hAodd.of_dvd_right hdvd
  have hA0godd : Nat.Coprime 2 (Nat.card A0g) := by
    rw [card_conjugate_local]
    exact hA0odd
  have hA0gne : A0g ≠ ⊥ := by
    intro hbot
    apply hA0ne
    apply le_bot_iff.mp
    intro a ha
    have hamap : g * a * g⁻¹ ∈ A0g := by
      dsimp [A0g]
      rw [conjugateSubgroup, Subgroup.mem_map]
      exact ⟨a, ha, by simp [MulAut.conj_apply]⟩
    rw [hbot] at hamap
    have hzero : g * a * g⁻¹ = 1 := Subgroup.mem_bot.mp hamap
    exact Subgroup.mem_bot.mpr (by simpa [A0] using hzero)
  have hA0gU : A0g ≤ c.U :=
    odd_order_subgroup_le_U_of_H_eq_SU hmin c hA0gH hA0godd
  have hA0gcard : Nat.card A0g = 3 := by
    have hdvd : Nat.card A0g ∣ 3 := by
      rw [← hU3]
      exact Subgroup.card_dvd_of_le hA0gU
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exfalso
      apply hA0gne
      exact Subgroup.eq_bot_of_card_eq A0g h1
    · exact h3
  have hA0gUeq : A0g = c.U := by
    apply Subgroup.eq_of_le_of_card_ge hA0gU
    rw [hA0gcard, hU3]
  let H : Subgroup G := c.Hhat
  let Xg : Subgroup G := conjugateSubgroup X g
  have hXgHhat : Xg ≤ c.Hhat := by
    intro z hz
    have hzU : z ∈ Subgroup.centralizer (c.U : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have huA0g : u ∈ A0g := by rw [hA0gUeq]; exact hu
      rcases Subgroup.mem_map.mp huA0g with ⟨a, ha, hau⟩
      rcases Subgroup.mem_map.mp hz with ⟨x, hx, hzx⟩
      have haux : x * a = a * x :=
        Subgroup.mem_centralizer_iff.mp
          (Subgroup.mem_centralizer_iff.mp ha.1) x hx
      have hz' : z = g * x * g⁻¹ := by
        simpa [Xg, conjugateSubgroup] using hzx.symm
      have hau' : u = g * a * g⁻¹ := by
        simpa [A0g, conjugateSubgroup] using hau.symm
      rw [hz', hau']
      calc
        (g * a * g⁻¹) * (g * x * g⁻¹) = g * (a * x) * g⁻¹ := by group
        _ = g * (x * a) * g⁻¹ := by rw [haux]
        _ = (g * x * g⁻¹) * (g * a * g⁻¹) := by group
    have hzN : z ∈ Subgroup.normalizer (c.U : Set G) :=
      (Subgroup.centralizer_le_normalizer (c.U : Set G)) hzU
    rw [hNormU] at hzN
    exact hzN
  have hXgcard : Nat.card Xg = 3 := by
    rw [card_conjugate_local]
    exact hXcard
  let P : Subgroup H := Xg.subgroupOf H
  have hPcard : Nat.card P = 3 := by
    rw [natCard_subgroupOf_eq Xg H hXgHhat]
    exact hXgcard
  have hPp : IsPGroup 3 P := by
    apply IsPGroup.of_card (G := P) (n := 1)
    rw [hPcard]
    norm_num
  have hXgInv : ∀ z : G, z ∈ Xg →
      c.t * z * c.t⁻¹ = z⁻¹ := by
    intro z hz
    rcases Subgroup.mem_map.mp hz with ⟨x, hx, hzx⟩
    have hz' : z = g * x * g⁻¹ := by
      simpa [Xg, conjugateSubgroup] using hzx.symm
    rw [hz', ← hgy]
    calc
      (g * y * g⁻¹) * (g * x * g⁻¹) * (g * y * g⁻¹)⁻¹ =
          g * (y * x * y⁻¹) * g⁻¹ := by group
      _ = g * (x⁻¹) * g⁻¹ := by rw [(hXinv x hx).2]
      _ = (g * x * g⁻¹)⁻¹ := by group
  have hPmapne : P.map (QuotientGroup.mk' (pPrimeCore 2 H)) ≠ ⊥ := by
    intro hbot
    have hXgU : Xg ≤ c.U := by
      intro z hz
      let zH : H := ⟨z, hXgHhat hz⟩
      have hzP : zH ∈ P := Subgroup.mem_subgroupOf.mpr hz
      have hzmap : QuotientGroup.mk' (pPrimeCore 2 H) zH = 1 := by
        have hzmem : QuotientGroup.mk' (pPrimeCore 2 H) zH ∈
            P.map (QuotientGroup.mk' (pPrimeCore 2 H)) :=
          Subgroup.mem_map.mpr ⟨zH, hzP, rfl⟩
        rw [hbot] at hzmem
        exact Subgroup.mem_bot.mp hzmem
      have hzO : zH ∈ pPrimeCore 2 H :=
        (QuotientGroup.eq_one_iff (N := pPrimeCore 2 H) zH).mp hzmap
      have hOmap : (pPrimeCore 2 c.Hhat).map c.Hhat.subtype = c.U := by
        rw [show c.U = oddCoreOf c.Hhat by exact (theorem_2_6 hmin c).1]
        rfl
      have hzUmap : z ∈ (pPrimeCore 2 H).map H.subtype :=
        Subgroup.mem_map.mpr ⟨zH, hzO, rfl⟩
      simpa [H, hOmap] using hzUmap
    have hXgcent : Xg ≤ Subgroup.centralizer ({c.t} : Set G) := by
      intro z hz
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hzU := hXgU hz
      have htcent : c.t ∈ Subgroup.centralizer (c.U : Set G) := by
        have h26 := theorem_2_6 hmin c
        have htV := centralizerStructure_t_mem_twoCore c h26
        have hVC : twoCoreOf c.Hhat ≤
            Subgroup.centralizer (c.U : Set G) := by
          simpa [h26.1] using twoCoreOf_centralizes_oddCoreOf c.Hhat
        exact hVC htV
      exact Subgroup.mem_centralizer_iff.mp htcent z hzU
    have hXgodd : Odd (Nat.card Xg) := by
      rw [hXgcard]
      norm_num
    have hXgbot := oddOrder_subgroup_eq_bot_of_inverted_and_centralized
      Xg c.t hXgodd hXgcent hXgInv
    apply hXne
    have hmapbot : X.map (MulAut.conj g).toMonoidHom = ⊥ := by
      change conjugateSubgroup X g = ⊥
      exact hXgbot
    exact (Subgroup.map_eq_bot_iff_of_injective X
      (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective).mp hmapbot
  let Q : Type u := H ⧸ pPrimeCore 2 H
  let L : Subgroup Q := ⊤
  have hLnormal : L.Normal := by dsimp [L]; infer_instance
  have hLindex : Odd L.index := by simp [L]
  let K : Type u := ULift (ZMod 3)
  let eK : K ≃+* ZMod 3 := ULift.ringEquiv
  have hpgl : Nonempty (L ≃* PGL2 K) := by
    let eQ : Q ≃* Equiv.Perm (Fin 4) :=
      (firstCase_hhat_quotient_U_s4_of_U_card_three hmin c hfirst hklein hU3).some
    exact ⟨(Subgroup.topEquiv (G := Q)).trans
      ((eQ.trans pgl2_three_equiv_perm.symm).trans (pgl2RingEquiv eK).symm)⟩
  have htHhat : c.t ∈ c.Hhat := by
    have htH : c.t ∈ c.H := by
      rw [c.H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
    exact c.H_le_Hhat htH
  let tH : H := ⟨c.t, htHhat⟩
  let T : Subgroup H := pCore 2 H
  have hTnormal : T.Normal := by dsimp [T]; infer_instance
  have hT2 : IsPGroup 2 T := by dsimp [T]; exact pCore_isPGroup
  have htT : tH ∈ T := by
    have htV := centralizerStructure_t_mem_twoCore c (theorem_2_6 hmin c)
    rcases Subgroup.mem_map.mp htV with ⟨z, hz, hzt⟩
    have hzH : (z : H) = tH := by
      apply Subtype.ext
      simpa [tH] using hzt
    rw [← hzH]
    exact hz
  have ht1 : tH ≠ 1 := by
    intro h
    exact c.t_involution.1 (by simpa [tH] using congrArg Subtype.val h)
  have ht2 : tH ^ 2 = 1 := by
    apply Subtype.ext
    simpa [tH, pow_two] using c.t_involution.2
  have htinvP : ∀ z : H, z ∈ P → tH * z * tH⁻¹ = z⁻¹ := by
    intro z hz
    apply Subtype.ext
    have hzXg : (z : G) ∈ Xg := hz
    simpa [tH] using hXgInv (z : G) hzXg
  let K0 : Type u := ULift (ZMod 3)
  have hK0 : Nat.card K0 = 3 := by simp [K0]
  exact no_involution_inverts_of_quotient_linear_three_pgl2
    (A := H) (K := K0) hK0 L hLnormal hLindex
    (by simpa [K0] using hpgl) P 3 Nat.prime_three (by norm_num)
    hPp hPmapne tH T hTnormal hT2 htT ht1 ht2 htinvP

end CFSG.GorensteinWalter
