module

public import CFSG.RankThree.PartTwo.Sec13.K135R3Prime
public import CFSG.RankThree.PartTwo.Sec13.K135SFFinal
public import CFSG.RankThree.PartTwo.Sec13.K135SFGL12Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
public import CFSG.RankThree.PartTwo.Sec13.F135LastR2
public import CFSG.RankThree.PartTwo.Sec13.F135LastR3D1
public import CFSG.RankThree.PartTwo.Sec13.F135LastR3Layer
public import CFSG.RankThree.PartTwo.Sec13.F135LastR3Lift
public import CFSG.RankThree.PartTwo.Sec13.F135LastR4Card
public import CFSG.RankThree.PartTwo.Sec13.F135LastR4Comm
public import CFSG.RankThree.PartTwo.Sec13.F135LastR5
public import CFSG.RankThree.PartTwo.Sec13.F135LastR5Cube
public import CFSG.RankThree.PartTwo.Sec13.K135D1cPrime

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13
open scoped commutatorElement

theorem r3_holds_gl12 (hLP : Sec4.Item4_1LargePrime)
    (hTC : Sec4.Item4_1ThreeCover) (h42 : Sec4.Item4_2) (hMP : KFactMultPrime)
    (hMPG : K135SF.KFactMultPrimeGL12) : R3 := by
  intro G _ _ A c L p C c3
  have hcrit := c3.crit
  have hp : p.Prime := hcrit.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hp7 : 7 ≤ p := c3.p_ge_seven
  have hp2 : p ≠ 2 := by omega
  have hzL := c3.z_mem
  have hY : Nat.card c3.Y = p := c3.Y_card
  obtain ⟨hY', hYc⟩ := r5g_Y_sub hp hY
  have hYD : c3.Y ≤ dPrime L p C c3.z := c3.Y_le.trans inf_le_left
  have hDp : IsPGroup p (dPrime L p C c3.z) := isPGroup_dPrime hcrit hzL
  have hDexp : ∀ x ∈ dPrime L p C c3.z, x ^ p = 1 := dPrime_exp hcrit hzL
  obtain ⟨hEp, hEexp, hYE, -⟩ := r5g_E_facts hDp hDexp hYD hY c3.Y_not_frattini
  have hTF : TheoremFourHyp G := c3.data.toTheoremFourHyp
  have hYne : c3.Y ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hY
    exact hp.one_lt.ne hY
  have hMne : cM c3.Y ≠ ⊤ := r5g_cM_ne_top hTF.isSimpleGroup hTF.nonabelian hYne
  have hSM : SectionFourHyp (cM c3.Y) := hTF.sectionFourHyp hMne
  have hlr : CFSG.Assembly.RankThreeEven.localRank p G < 3 := hTF.localRank_lt p hp (by omega)
  have hnoM := hno_of_localRank hp hlr (cM c3.Y)
  have hu : c3.u ∈ cM c3.Y := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (c3.Y_le hy).2
  obtain ⟨hU2, hUf⟩ := r5g_U_facts c3.U_eq
  have hYΦ : c3.Y.subgroupOf (cM c3.Y) ⊓
      (commutator ↥(eOf (dPrime L p C c3.z) c3.Y)).map (eOf (dPrime L p C c3.z) c3.Y).subtype =
      ⊥ := r4_E_comm_inf hDp hDexp hY c3.Y_not_frattini
  have hE4 : p ^ 4 ≤ Nat.card (eOf (dPrime L p C c3.z) c3.Y) :=
    r4_card_eOf hDp hDexp (dPrime_frattini_central hcrit hzL) hYD hY c3.Dp_rank
  have hYcE : ∀ y ∈ c3.Y.subgroupOf (cM c3.Y), ∀ x ∈ eOf (dPrime L p C c3.z) c3.Y,
      y * x = x * y := fun y hy x _ => ((Subgroup.mem_center_iff.mp (hYc hy)) x).symm
  obtain ⟨A₀, hA₀E, hA₀el, hA₀3⟩ := r4_exists_cube hEp hEexp hYE hY' hYcE hYΦ
    (le_trans (Nat.pow_le_pow_right hp.pos (by norm_num)) hE4)
  haveI hRn : (CFSG.pPrimeCore p (cM c3.Y)).Normal := inferInstance
  obtain ⟨hR, hcoreN⟩ := r3_pPrimeCore_facts (M := cM c3.Y) hp
  have hRodd : Odd (Nat.card (CFSG.pPrimeCore p (cM c3.Y))) :=
    r3_odd_of_cube hp _ hR hA₀el hA₀3 hnoM
  have hRodd2 : ¬ 2 ∣ Nat.card (CFSG.pPrimeCore p (cM c3.Y)) :=
    Nat.not_even_iff_odd.mpr hRodd |> fun h => by
      rw [← even_iff_two_dvd]
      exact Nat.not_even_iff_odd.mpr hRodd
  have hnoN := r3_hnoN hp hp2 _ hR hnoM
  have hlrN := r3_localRank_lt hp hnoN
  have hmult : ∀ J : Subgroup (cM c3.Y ⧸ CFSG.pPrimeCore p (cM c3.Y)), CFSG.IsComponent J →
      ¬ p ∣ Nat.card (Subgroup.center ↥J) := by
    intro J hJ
    rcases K135SF.list42_or_gl12_of_pPrimeCore hLP hTC h42 hSM hp hp2 hRodd J hJ with
      hL | ⟨hK, hGL⟩
    · exact hMP _ hJ.1 hL p hp hp7
    · exact hMPG _ hJ.1 hK hGL p hp hp7
  have hinjE := r4g_inj hp (CFSG.pPrimeCore p (cM c3.Y)) hR hEp
  have hinjE' := r3_inj_of_comp (CFSG.pPrimeCore p (cM c3.Y)) hinjE
  have hYΦ' : c3.Y.subgroupOf (cM c3.Y) ⊓ ⁅eOf (dPrime L p C c3.z) c3.Y, eOf (dPrime L p C c3.z) c3.Y⁆ =
      ⊥ := by
    have h := hYΦ
    unfold commutator at h
    rwa [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype] at h
  have hĒp : IsPGroup p ((eOf (dPrime L p C c3.z) c3.Y).map
      (QuotientGroup.mk' (CFSG.pPrimeCore p (cM c3.Y)))) := hEp.map _
  have hĒexp : ∀ e ∈ (eOf (dPrime L p C c3.z) c3.Y).map
      (QuotientGroup.mk' (CFSG.pPrimeCore p (cM c3.Y))), e ^ p = 1 := by
    rintro _ ⟨e, he, rfl⟩
    rw [← map_pow, hEexp e he, map_one]
  have hĒ4 : p ^ 4 ≤ Nat.card ((eOf (dPrime L p C c3.z) c3.Y).map
      (QuotientGroup.mk' (CFSG.pPrimeCore p (cM c3.Y)))) := by
    rw [r4g_card_map _ hinjE]
    exact hE4
  have hYbE : (c3.Y.subgroupOf (cM c3.Y)).map (QuotientGroup.mk' (CFSG.pPrimeCore p (cM c3.Y))) ≤
      (eOf (dPrime L p C c3.z) c3.Y).map (QuotientGroup.mk' (CFSG.pPrimeCore p (cM c3.Y))) :=
    Subgroup.map_mono hYE
  have hYbc := r3_map_center_le (CFSG.pPrimeCore p (cM c3.Y)) hYc
  have hYbcard : Nat.card ((c3.Y.subgroupOf (cM c3.Y)).map
      (QuotientGroup.mk' (CFSG.pPrimeCore p (cM c3.Y)))) = p := by
    have hinjY := r4g_inj hp (CFSG.pPrimeCore p (cM c3.Y)) hR
      (IsPGroup.of_card (n := 1) (by rw [hY', pow_one]) : IsPGroup p (c3.Y.subgroupOf (cM c3.Y)))
    rw [r4g_card_map _ hinjY, hY']
  have hYbΦ := r3_inf_comm_map (CFSG.pPrimeCore p (cM c3.Y)) hinjE' hYE hYΦ'
  have hinjA := r4g_inj hp (CFSG.pPrimeCore p (cM c3.Y)) hR
    (IsPGroup.of_card hA₀3 : IsPGroup p A₀)
  have hAel := r3_isElemAbelian_map (QuotientGroup.mk' (CFSG.pPrimeCore p (cM c3.Y))) hA₀el
  have hA3 : Nat.card (A₀.map (QuotientGroup.mk' (CFSG.pPrimeCore p (cM c3.Y)))) = p ^ 3 := by
    rw [r4g_card_map _ hinjA, hA₀3]
  have h3 : ∀ J₀ J₁ J₂ : Subgroup (cM c3.Y ⧸ CFSG.pPrimeCore p (cM c3.Y)), CFSG.IsComponent J₀ →
      CFSG.IsComponent J₁ → CFSG.IsComponent J₂ → J₀ ≠ J₁ → J₀ ≠ J₂ → J₁ ≠ J₂ → False :=
    fun J₀ J₁ J₂ h₀ h₁ h₂ h01 h02 h12 =>
      r3_three_components hp hnoN hAel hA3 hYbcard hYbc hmult h₀ h₁ h₂ h01 h02 h12
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hfix : ∀ J : Subgroup (cM c3.Y ⧸ CFSG.pPrimeCore p (cM c3.Y)), CFSG.IsComponent J →
      (eOf (dPrime L p C c3.z) c3.Y).map (QuotientGroup.mk' (CFSG.pPrimeCore p (cM c3.Y))) ≤
        Subgroup.normalizer (J : Set (cM c3.Y ⧸ CFSG.pPrimeCore p (cM c3.Y))) :=
    fun J hJ g hg => r3_fix_of_odd h3 hodd (hĒexp g hg) hJ
  have hUA : c3.U ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({c3.u} : Set G)) ⊓
      Subgroup.centralizer (c3.Y : Set G) := by
    rw [c3.U_eq]
    exact r5gl_commutator_le fun b hb x hx => r5gl_A_conj hb hx
  have hUM : c3.U ≤ cM c3.Y := hUA.trans inf_le_right
  have hBM : dPrime L p C c3.z ⊓ cM c3.Y ⊓ Subgroup.centralizer ({c3.u} : Set G) ≤ cM c3.Y :=
    inf_le_left.trans inf_le_right
  have hUB : ⁅c3.U, dPrime L p C c3.z ⊓ cM c3.Y ⊓ Subgroup.centralizer ({c3.u} : Set G)⁆ =
      c3.U := r4_U_comm hp hp2 hDp c3.U_eq
  have hmapcomm := r4_map_comm (cM c3.Y) (CFSG.pPrimeCore p (cM c3.Y)) hUM hBM hUB
  have hU2' : IsPGroup 2 (c3.U.subgroupOf (cM c3.Y)) := hU2.comap_subtype (K := cM c3.Y)
  have hŪ2 : IsPGroup 2 ((c3.U.subgroupOf (cM c3.Y)).map
      (QuotientGroup.mk' (CFSG.pPrimeCore p (cM c3.Y)))) := hU2'.map _
  have hŪ1 : (c3.U.subgroupOf (cM c3.Y)).map (QuotientGroup.mk' (CFSG.pPrimeCore p (cM c3.Y))) ≠
      ⊥ := by
    intro h
    have hinj := r4g_inj Nat.prime_two (CFSG.pPrimeCore p (cM c3.Y)) hRodd2 hU2'
    have hc := r4g_card_map (CFSG.pPrimeCore p (cM c3.Y)) hinj
    rw [h, Subgroup.card_bot] at hc
    have hU' : c3.U.subgroupOf (cM c3.Y) = ⊥ := Subgroup.card_eq_one.mp hc.symm
    apply c3.U_ne
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hUM hx⟩ : cM c3.Y) ∈ c3.U.subgroupOf (cM c3.Y) := hx
    rw [hU'] at hx'
    have := Subgroup.mem_bot.mp hx'
    simpa using congrArg Subtype.val this
  have hBbĒ : ((dPrime L p C c3.z ⊓ cM c3.Y ⊓ Subgroup.centralizer ({c3.u} : Set G)).subgroupOf
      (cM c3.Y)).map (QuotientGroup.mk' (CFSG.pPrimeCore p (cM c3.Y))) ≤
      (eOf (dPrime L p C c3.z) c3.Y).map (QuotientGroup.mk' (CFSG.pPrimeCore p (cM c3.Y))) := by
    rintro _ ⟨e, he, rfl⟩
    have he' : (e : G) ∈ dPrime L p C c3.z ⊓ cM c3.Y ⊓ Subgroup.centralizer ({c3.u} : Set G) :=
      Subgroup.mem_subgroupOf.mp he
    exact ⟨e, Subgroup.mem_subgroupOf.mpr he'.1, rfl⟩
  have hBbN : ((dPrime L p C c3.z ⊓ cM c3.Y ⊓ Subgroup.centralizer ({c3.u} : Set G)).subgroupOf
      (cM c3.Y)).map (QuotientGroup.mk' (CFSG.pPrimeCore p (cM c3.Y))) ≤
      Subgroup.normalizer (((c3.U.subgroupOf (cM c3.Y)).map
        (QuotientGroup.mk' (CFSG.pPrimeCore p (cM c3.Y))) : Subgroup _) : Set _) := by
    rintro _ ⟨e, he, rfl⟩
    exact r5g_map_normalizer _ _ (r5g_subgroupOf_normalizer (cM c3.Y) _ (hUf (e : G) he))
  have hnot := r3_exists_not_centralizing hp hp7 hlrN hcoreN hŪ2 hŪ1 (hĒp.to_le hBbĒ)
    (fun x hx => hĒexp x (hBbĒ hx)) hBbN hmapcomm.symm
  obtain ⟨J, hJ, hJnc⟩ := r3_exists_comp_of_not_le_centralizer_layer hnot
  haveI hker := normal_ker_components (cM c3.Y ⧸ CFSG.pPrimeCore p (cM c3.Y))
  have hB𝒦 : ((dPrime L p C c3.z ⊓ cM c3.Y ⊓ Subgroup.centralizer ({c3.u} : Set G)).subgroupOf
      (cM c3.Y)).map (QuotientGroup.mk' (CFSG.pPrimeCore p (cM c3.Y))) ≤
      ⨅ K : {K : Subgroup (cM c3.Y ⧸ CFSG.pPrimeCore p (cM c3.Y)) // CFSG.IsComponent K},
        Subgroup.normalizer (K.1 : Set (cM c3.Y ⧸ CFSG.pPrimeCore p (cM c3.Y))) :=
    fun b hb => Subgroup.mem_iInf.2 fun K => hfix K.1 K.2 (hBbĒ hb)
  have hŪ𝒦 : (c3.U.subgroupOf (cM c3.Y)).map (QuotientGroup.mk' (CFSG.pPrimeCore p (cM c3.Y))) ≤
      ⨅ K : {K : Subgroup (cM c3.Y ⧸ CFSG.pPrimeCore p (cM c3.Y)) // CFSG.IsComponent K},
        Subgroup.normalizer (K.1 : Set (cM c3.Y ⧸ CFSG.pPrimeCore p (cM c3.Y))) :=
    hmapcomm.le.trans ((Subgroup.commutator_mono le_rfl hB𝒦).trans
      (Subgroup.commutator_le_right _ _))
  have hŪN : (c3.U.subgroupOf (cM c3.Y)).map (QuotientGroup.mk' (CFSG.pPrimeCore p (cM c3.Y))) ≤
      Subgroup.normalizer (J : Set (cM c3.Y ⧸ CFSG.pPrimeCore p (cM c3.Y))) :=
    fun x hx => Subgroup.mem_iInf.1 (hŪ𝒦 hx) ⟨J, hJ⟩
  have hJU := r3_comm_eq_of_not_centralize hJ hŪN hJnc
  have hu2' : ((⟨c3.u, hu⟩ : cM c3.Y) : cM c3.Y ⧸ CFSG.pPrimeCore p (cM c3.Y)) *
      ((⟨c3.u, hu⟩ : cM c3.Y) : cM c3.Y ⧸ CFSG.pPrimeCore p (cM c3.Y)) = 1 := by
    rw [← QuotientGroup.mk_mul]
    have : (⟨c3.u, hu⟩ : cM c3.Y) * ⟨c3.u, hu⟩ = 1 := Subtype.ext c3.u_sq
    rw [this, QuotientGroup.mk_one]
  have hFu : ∀ f ∈ ((dPrime L p C c3.z ⊓ cM c3.Y ⊓ Subgroup.centralizer ({c3.u} : Set G)).subgroupOf
      (cM c3.Y)).map (QuotientGroup.mk' (CFSG.pPrimeCore p (cM c3.Y))),
      ((⟨c3.u, hu⟩ : cM c3.Y) : cM c3.Y ⧸ CFSG.pPrimeCore p (cM c3.Y)) * f =
        f * ((⟨c3.u, hu⟩ : cM c3.Y) : cM c3.Y ⧸ CFSG.pPrimeCore p (cM c3.Y)) := by
    rintro _ ⟨b, hb, rfl⟩
    have hb' : (b : G) ∈ Subgroup.centralizer ({c3.u} : Set G) := (Subgroup.mem_subgroupOf.mp hb).2
    have hcomm : (⟨c3.u, hu⟩ : cM c3.Y) * b = b * ⟨c3.u, hu⟩ :=
      Subtype.ext (Subgroup.mem_centralizer_iff.mp hb' c3.u rfl)
    exact (map_mul (QuotientGroup.mk' (CFSG.pPrimeCore p (cM c3.Y))) _ _).symm.trans
      ((congrArg (QuotientGroup.mk' (CFSG.pPrimeCore p (cM c3.Y))) hcomm).trans
        (map_mul _ _ _))
  have hJu : ((⟨c3.u, hu⟩ : cM c3.Y) : cM c3.Y ⧸ CFSG.pPrimeCore p (cM c3.Y)) ∈
      Subgroup.normalizer (J : Set (cM c3.Y ⧸ CFSG.pPrimeCore p (cM c3.Y))) :=
    r3_u_normalizes hp hnoN hmult
      (fun K hK => r3_p_dvd_component hp hnoN hAel hA3 hK) hYbcard hYbc hu2'
      (fun x hx => hĒexp x (hBbĒ hx)) hFu (fun K hK g hg => hfix K hK (hBbĒ hg)) hŪ2 hBbN
      hmapcomm.le hJ hŪN hJnc
  exact ⟨{ c3 with
    R := CFSG.pPrimeCore p (cM c3.Y)
    R_normal := inferInstance
    R_eq := (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_eq_map
      hp (cM c3.Y)).symm
    R_odd := hRodd
    R_coprime := (Nat.Prime.coprime_iff_not_dvd hp).mpr hR
    J := J
    J_comp := hJ
    J_normE := fun e he => hfix J hJ ⟨e, he, rfl⟩
    J_normc := fun hc => by
      have hc3 : ((⟨c, hc⟩ : cM c3.Y) : cM c3.Y ⧸ CFSG.pPrimeCore p (cM c3.Y)) ^ 3 = 1 := by
        rw [← QuotientGroup.mk_pow]
        have : (⟨c, hc⟩ : cM c3.Y) ^ 3 = 1 := Subtype.ext (by
          have h := pow_orderOf_eq_one c
          rwa [orderOf_c c3.data] at h)
        rw [this, QuotientGroup.mk_one]
      exact r3_fix_of_odd h3 (by decide : Odd 3) hc3 hJ
    J_U := hJU
    J_normU := hŪN
    J_normu := fun _ => hJu }⟩

end CFSG.RankThree.PartTwo.Sec13.F135Last
