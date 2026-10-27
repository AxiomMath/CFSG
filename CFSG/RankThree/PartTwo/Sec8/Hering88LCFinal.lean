module

public import CFSG.RankThree.PartTwo.Sec8.Hering88LCOuter
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofLink
import CFSG.RankThree.PartTwo.Sec8.Hering88LCKSide

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering88LC

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open Hering88N
open scoped commutatorElement

theorem kF88LinkCoreD83_of (h45 : Sec4.Item4_5) (h83 : Item83) (h418 : Item418Theta)
    (hF : KF84Field) : KF88LinkCoreD83 := by
  intro G _ _ A c L a b X h Y hY hIJ x hx hxY hD83 d hdS hdnx hUq _ hUx hle
  classical
  obtain ⟨A₀, d', n', hD⟩ := hD83
  have h84 : Pair84A := pair84A_of h418 hF
  set K := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({b} : Set G)) with hKdef
  set U := inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({d} : Set G)) with hUdef
  obtain ⟨hAc, hA3⟩ := Hering88C.pair_commute_pow_three h
  obtain ⟨hbA, -, -, -⟩ := Item87Proof.isGammaIndex_cases h.isGammaIndex
  have hcA : c ∈ A := h.mem_A
  have hcbA : Subgroup.closure ({c, b} : Set G) ≤ A := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hcA
    · exact hbA
  have hdA : d ∈ A := hcbA hdS
  have hxA : x ∈ A := by
    rcases hx with rfl | rfl
    · exact hcA
    · exact hbA
  have ha3 : a ^ 3 = 1 := hA3 a h.a_mem
  have hd3 : d ^ 3 = 1 := hA3 d hdA
  have hx3 : x ^ 3 = 1 := hA3 x hxA
  have hAN := Hering88C.le_normalizer_of_pair h45 h hY
  have hdN : d ∈ Subgroup.normalizer (Y : Set G) := hAN hdA
  have hxN : x ∈ Subgroup.normalizer (Y : Set G) := hAN hxA
  have hdx : d * x = x * d := hAc d hdA x hxA
  have hd1 : d ≠ 1 := fun h1 => hdnx (by rw [h1]; exact Subgroup.one_mem _)
  have hYbar := ybarOne_of h45 h83 h84 hF h hY hIJ hx hxY hD
  have hYF := ybarFacts_of hYbar
  have hZ := hYF.center
  have hxout : ¬ KFacts.IsInnerAut (barAut Y x hxN) := by
    rcases hxY with h' | h'
    · exact (KFacts.InducesStdKind.inducesOuterTheta Y h' (by decide)).2
    · exact (KFacts.InducesStdKind.inducesOuterTheta Y h' (by decide)).2
  have hxU : Sec4.InducesOuterTheta x U :=
    KFacts.InducesStdKind.inducesOuterTheta U hUx (by decide)
  by_cases hdin : KFacts.IsInnerAut (barAut Y d hdN)
  swap
  · rcases outer_residual hYbar hd3 ⟨hdN, hdin⟩ with hbot | h3
    · exact not_isQuasisimple_of_residual_eq_bot hdN hd3 hbot hUq
    · exact false_of_outer hZ hYF.cyc hdN hd3 hxN hx3 hdx hdin hxout h3 hxU
  obtain ⟨g, hg⟩ := hdin
  have hg1 : g ≠ 1 := by
    rintro rfl
    have h1 : barAut Y d hdN = 1 := by rw [← hg, map_one]
    have hSC := kF88SwapCent_holds h45 h84 G A c L a b X 1 h Y hY hIJ x hx hxY
    have hmem : d ∈ (Subgroup.zpowers a : Set G) := by
      rw [← hSC]
      refine ⟨hdA, fun z hz => ?_⟩
      have hzb := congrArg (fun φ : MulAut (Y ⧸ aschbacherSolvableCore 3 Y) =>
        φ (QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨z, hz⟩)) h1
      simp only [MulAut.one_apply] at hzb
      rw [barAut_mk hdN hz (conj_mem_of_mem_normalizer hdN hz)] at hzb
      have hθ := (QuotientGroup.eq_iff_div_mem).mp hzb
      exact ⟨_, hθ, by simp [div_eq_mul_inv]⟩
    exact Hering88C.a_not_mem_closure hF h
      ((Subgroup.zpowers_le.mpr hdS) (Item87Proof.mem_zpowers_of_mem_zpowers ha3 hd1 hmem))
  have hg3 : g ^ 3 = 1 :=
    eq_of_conj_eq hZ (by rw [map_pow, hg, barAut_pow_three hdN hd3, map_one])
  have hCg : barCentralizer (Subgroup.zpowers d) Y =
      Subgroup.centralizer ({g} : Set (Y ⧸ aschbacherSolvableCore 3 Y)) :=
    barCentralizer_eq_centralizer hdN hg.symm
  have hUimg : imageModTheta Y U = inSubgroup perfectResidual
      (Subgroup.centralizer ({g} : Set (Y ⧸ aschbacherSolvableCore 3 Y))) := by
    rw [hUdef, KFacts.imageModTheta_perfectResidual_centralizer_eq hdN ⟨1, by rwa [pow_one]⟩,
      hCg]
  have hne : inSubgroup perfectResidual
      (Subgroup.centralizer ({g} : Set (Y ⧸ aschbacherSolvableCore 3 Y))) ≠ ⊥ := by
    intro hbot
    exact not_isQuasisimple_of_residual_eq_bot hdN hd3 (by rw [hCg]; exact hbot) hUq
  have hmemC : ∀ {w : G} (hwY : w ∈ Y), w ∈ Subgroup.centralizer ({d} : Set G) →
      QuotientGroup.mk' (aschbacherSolvableCore 3 Y) ⟨w, hwY⟩ ∈
        Subgroup.centralizer ({g} : Set (Y ⧸ aschbacherSolvableCore 3 Y)) := by
    intro w hwY hwd
    rw [← hCg, KFacts.mem_barCentralizer_zpowers_iff hdN]
    exact barAut_mk_of_commute hdN hwY hwd
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    (PartOne.mem_thetaComponentsAt_iff.mp h.mem_thetaComponentsAt).1
  have hKX : K ≤ X := h.pairRel.2.2.2.1
  have hKcb : K ≤ Subgroup.centralizer {c} ⊓ Subgroup.centralizer {b} :=
    le_inf ((Item87Proof.residual_le _).trans (inf_le_left.trans hLc))
      ((Item87Proof.residual_le _).trans inf_le_right)
  have hKd : K ≤ Subgroup.centralizer ({d} : Set G) := by
    intro k hk
    have hk' : k ∈ Subgroup.centralizer ((Subgroup.closure ({c, b} : Set G) : Subgroup G) :
        Set G) := by
      rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
      intro w hw
      obtain ⟨hkc, hkb⟩ := Subgroup.mem_inf.mp (hKcb hk)
      rcases hw with rfl | rfl
      · exact (Subgroup.mem_centralizer_singleton_iff.mp hkc).symm
      · exact (Subgroup.mem_centralizer_singleton_iff.mp hkb).symm
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hk' d hdS).symm
  have hKa : KFacts.InducesStdKind K a .field := hF G A c L a b X 1 h
  have hk84 := h84 G A c L a b X 1 h
  have haX : a ∈ Subgroup.normalizer (X : Set G) := by
    rcases hk84 with hk | hk
    · exact hk.mem_normalizer
    · exact hk.mem_normalizer
  obtain ⟨-, -, -, -, -, e₀, m, hem⟩ := h.mem_pairOmega
  have hFX := Item8KFacts2Proof.residualFacts_barCentralizer hem.2.2.1
    (Item87Proof.isGammaType_of_isGammaIndex hem) (h.not_unitary (3 * m)) ha3 hk84
    (h.gTwoPartner m)
  have hJY : sec8J X a ≤ Y := le_sup_right.trans hIJ
  have hY3 : ∀ u : K, (u : G) ∈ Subgroup.centralizer ({a} : Set G) → u ^ 3 = 1 → (u : G) ∈ Y :=
    fun u hua hu3 => hJY (Item8KFacts2Proof.mem_inSubgroup_perfectResidual_of_pow_three haX ha3
      hFX.1 (hKX u.2) hua (by simpa using congrArg Subtype.val hu3))
  have hKtype := Item87Res2Proof.quot_cases_of_isGammaIndex h.isGammaIndex
  rcases hYF.link with ⟨hI, h25⟩ | hP
  swap
  ·
    obtain ⟨u, p, hua, hu3, hup⟩ :=
      exists_noncomm_three ha3 hKa (hKtype.imp (fun h' => h'.2) id)
    have huY := hY3 u hua hu3
    have hud := hKd u.2
    have huU : (u : G) ∈ U := by
      refine mem_residual_of_mem_imageModTheta huY hud ?_ (e := 1)
        (by rw [pow_one]; simpa using congrArg Subtype.val hu3)
      rw [hUimg]
      exact hP.perf g hg3 hg1 (hmemC huY hud)
    exact hup (hle (Subgroup.commutator_mem_commutator ⟨huU, u.2⟩ p.2))
  rcases hKtype with ⟨hRee, -⟩ | heK
  ·
    apply h25
    exact (iside_ree h hRee).trans ((card_quot_theta_dvd_card_imageModTheta
      (le_sup_left.trans hIJ)).trans (Subgroup.card_subgroup_dvd_card _))
  obtain ⟨t, u, hta, hua, ⟨e, hte⟩, hu3, hu1, htu⟩ := exists_inverting_pair ha3 hKa heK
  have huY := hY3 u hua hu3
  have hud := hKd u.2
  have htd : (t : G) * d = d * t := Subgroup.mem_centralizer_singleton_iff.mp (hKd t.2)
  have hJt : (t : G) ∈ Subgroup.normalizer ((sec8J X a : Subgroup G) : Set G) :=
    CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual _
      (Subgroup.le_normalizer
        (⟨hKX t.2, hta⟩ : (t : G) ∈ X ⊓ Subgroup.centralizer ({a} : Set G)))
  have htN : (t : G) ∈ Subgroup.normalizer (Y : Set G) :=
    Sec15.le_normalizer_of_mem_thetaComponentsIn (A := Subgroup.zpowers (t : G))
      (Subgroup.zpowers_le.mpr (Subgroup.le_normalizer hta)) hY hJY
      (Item87Proof.isPerfect_residual _)
      (Item812Res6.sec8J_ne_bot_of_gTwoPartner kF87INontriv_holds h84 h)
      (Subgroup.zpowers_le.mpr hJt) (Subgroup.mem_zpowers _)
  have hτg : barAut Y t htN g = g := by
    have hcomm := barAut_commute htN hdN htd
    rw [← hg] at hcomm
    have e' : barAut Y t htN * MulAut.conj g * (barAut Y t htN)⁻¹ = MulAut.conj g := by
      rw [hcomm, mul_inv_cancel_right]
    rw [KFacts.mul_mulAutConj_mul_inv] at e'
    exact eq_of_conj_eq hZ e'
  have hτ2 : barAut Y t htN ^ 2 ^ e = 1 := by
    have h' : (⟨(t : G), htN⟩ : Subgroup.normalizer (Y : Set G)) ^ 2 ^ e = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hte)
    change ((Sec4.thetaQuotMulAut Y).comp (Sec4.compAction Y)) ⟨t, htN⟩ ^ 2 ^ e = 1
    rw [← map_pow, h', map_one]
  obtain ⟨s, hs⟩ := hI.lc1 (barAut Y t htN) ⟨e, hτ2⟩ g hg3 hg1 hτg
  obtain ⟨hwY, hwimg⟩ := commutator_mem_imageModTheta hZ hdN hd3 htN htd hg.symm hs.symm
    (hI.lc2 g hg3 hg1 hne) huY hud
  set w : K := t * u * t⁻¹ * u⁻¹ with hw
  set q := QuotientGroup.mk' (aschbacherSolvableCore 3 K) with hq
  have hū3 : q u ^ 3 = 1 := by rw [← map_pow, hu3, map_one]
  have hqw : q w = q u := by
    rw [hw, map_mul, map_mul, map_mul, map_inv, map_inv, htu]
    calc (q u)⁻¹ * (q u)⁻¹ = (q u)⁻¹ * (q u)⁻¹ * q u ^ 3 := by rw [hū3, mul_one]
      _ = q u := by group
  obtain ⟨r, hr, hwr3⟩ := exists_threePart w (by show q w ^ 3 = 1; rw [hqw, hū3])
  have hwG : ((w : K) : G) = t * u * t⁻¹ * u⁻¹ := rfl
  have hw3Y : ((w ^ r : K) : G) ∈ Y := by
    rw [Subgroup.coe_pow, hwG]
    exact pow_mem hwY r
  have hw3d : ((w ^ r : K) : G) ∈ Subgroup.centralizer ({d} : Set G) := hKd (w ^ r).2
  have hw3U : ((w ^ r : K) : G) ∈ U := by
    refine mem_residual_of_mem_imageModTheta hw3Y hw3d ?_ (e := 1)
      (by rw [pow_one]; simpa using congrArg Subtype.val hwr3)
    have hpow : (⟨((w ^ r : K) : G), hw3Y⟩ : Y) = ⟨t * u * t⁻¹ * u⁻¹, hwY⟩ ^ r :=
      Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_pow, hwG])
    rw [hpow, map_pow]
    exact pow_mem hwimg r
  have hnc : q (w ^ r) * q t ≠ q t * q (w ^ r) := by
    intro hc
    rw [map_pow, hqw] at hc
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (mem_zpowers_pow_of_cube hū3 hr)
    have hcu : q u * q t = q t * q u := by
      rw [← hk]
      exact (Commute.zpow_left hc k).eq
    apply hu1
    have h1 : (q u)⁻¹ = q u := by rw [← htu, ← hcu, mul_inv_cancel_right]
    have h2 : q u * q u = 1 := by
      nth_rewrite 2 [← h1]
      exact mul_inv_cancel _
    calc q u = q u ^ 3 * (q u * q u)⁻¹ := by group
      _ = 1 := by rw [hū3, h2, inv_one, one_mul]
  exact commutator_not_mem_theta hnc
    (hle (Subgroup.commutator_mem_commutator ⟨hw3U, (w ^ r).2⟩ t.2))

end CFSG.RankThree.PartTwo.Sec8.Hering88LC

end
