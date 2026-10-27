module

public import CFSG.RankThree.PartTwo.Sec13.F135LastR4Comm
public import CFSG.RankThree.PartTwo.Sec13.F135LastR4Card
public import CFSG.RankThree.PartTwo.Sec13.F135LastR4Aux
public import CFSG.RankThree.PartTwo.Sec13.F135LastR4Eker
public import CFSG.RankThree.PartTwo.Sec13.F135LastR5Data
public import CFSG.RankThree.PartTwo.Sec13.F135LastR4U
public import CFSG.RankThree.PartTwo.Sec13.K135SFFinal
public import CFSG.RankThree.PartTwo.Sec13.K135SFGL12Defs
public import CFSG.RankThree.PartTwo.Sec13.F135LastR2
public import CFSG.RankThree.PartTwo.Sec13.F135LastR5Cube

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13
open scoped commutatorElement

theorem r4_Eker_of_cases (hG1 : KFactG1) (hG1G : K135SF.KFactG1GL12) {M : Type} [Group M] [Finite M] {p : ℕ} [Fact p.Prime]
    (hp7 : 7 ≤ p) (R : Subgroup M) [R.Normal] (hR : ¬ p ∣ Nat.card R)
    (Y E : Subgroup M) (hY : Nat.card Y = p) (hYc : Y ≤ Subgroup.center M)
    (hE : IsPGroup p E) (hEexp : ∀ e ∈ E, e ^ p = 1) (hYE : Y ≤ E)
    (hYΦ : Y ⊓ (commutator ↥E).map E.subtype = ⊥)
    (J : Subgroup (M ⧸ R)) (hJq : CFSG.IsQuasisimple J)
    (hcases : Sec4.Census.List42 (J ⧸ Subgroup.center J) ∨
      (CFSG.IsKGroup (J ⧸ Subgroup.center J) ∧ K135SF.GL12Data (J ⧸ Subgroup.center J)))
    (hEN : E.map (QuotientGroup.mk' R) ≤ Subgroup.normalizer (J : Set (M ⧸ R)))
    (Ū Eu : Subgroup (M ⧸ R)) (hŪN : Ū ≤ Subgroup.normalizer (J : Set (M ⧸ R)))
    (hŪ2 : IsPGroup 2 Ū) (hŪne : ¬ Ū ≤ Subgroup.centralizer (J : Set (M ⧸ R)))
    (hEuE : Eu ≤ E.map (QuotientGroup.mk' R))
    (hŪEu : Eu ≤ Subgroup.normalizer (Ū : Set (M ⧸ R)))
    (hcomm : Ū ≤ ⁅Ū, Eu⁆ ⊔ Subgroup.centralizer (J : Set (M ⧸ R)))
    (hno : ∀ A T : Subgroup M, CFSG.Open.IsElemAbelian p A → Nat.card A = p ^ 3 → T ≠ ⊥ →
      IsPGroup 2 T → ¬ A ≤ Subgroup.normalizer (T : Set M)) :
    ∀ e ∈ E, QuotientGroup.mk' R e ∈ Subgroup.centralizer (J : Set (M ⧸ R)) → e ∈ Y := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  have hperf : Group.IsPerfect (↥J) := hJq.1
  have hEbexp : ∀ e ∈ E.map (QuotientGroup.mk' R), e ^ p = 1 := by
    rintro _ ⟨e, he, rfl⟩
    rw [← map_pow, hEexp e he, map_one]
  obtain ⟨nf, hnfEu, hact1, -, V, hVne, hV2, hxV, hVx⟩ :=
    r5e_xV J hperf hp hp7 (E.map (QuotientGroup.mk' R)) Eu Ū hEbexp hEN hŪN hŪ2 hŪne
      hEuE hŪEu hcomm
  obtain ⟨f₀, hf₀E, hf₀⟩ := Subgroup.mem_map.mp (hEuE hnfEu)
  have hnfp : nf ^ p = 1 := by
    apply Subtype.val_injective
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hf₀, ← map_pow, hEexp f₀ hf₀E, map_one]
  have hfJp : (J.normalizerMonoidHom nf) ^ p = 1 := by
    rw [← map_pow, hnfp, map_one]
  have hfJne : J.normalizerMonoidHom nf ≠ 1 := by
    intro h
    apply hact1
    show centerQuotMulAut (↥J) (J.normalizerMonoidHom nf) = 1
    rw [h, map_one]
  have hord : orderOf (J.normalizerMonoidHom nf) = p := orderOf_eq_prime hfJp hfJne
  obtain ⟨T, hT1, hT2, hTmap⟩ : ∃ T : Subgroup ↥J, T ≠ ⊥ ∧ IsPGroup 2 T ∧
      T.map (J.normalizerMonoidHom nf).toMonoidHom = T := by
    rcases hcases with hList | ⟨hK, hGL⟩
    · exact hG1 (↥J) hJq hList p hp hp7 (J.normalizerMonoidHom nf) hord V hVne hV2 hxV hVx
    · exact hG1G (↥J) hJq hK hGL p hp hp7 (J.normalizerMonoidHom nf) hord V hVne hV2 hxV hVx
  have hJinj : Function.Injective (⇑J.subtype) := fun a b h => Subtype.ext h
  have hT'1 : T.map J.subtype ≠ ⊥ := fun h =>
    hT1 ((Subgroup.map_eq_bot_iff_of_injective T hJinj).mp h)
  have hT'2 : IsPGroup 2 (T.map J.subtype) := hT2.map J.subtype
  have hT'J : T.map J.subtype ≤ J := Subgroup.map_subtype_le T
  have hnorm : (nf : M ⧸ R) ∈
      Subgroup.normalizer ((T.map J.subtype : Subgroup (M ⧸ R)) : Set (M ⧸ R)) :=
    r4_normalizer_of_map J nf T hTmap
  have hTf : QuotientGroup.mk' R f₀ ∈
      Subgroup.normalizer ((T.map J.subtype : Subgroup (M ⧸ R)) : Set (M ⧸ R)) := by
    rw [hf₀]
    exact hnorm
  have hfJ : QuotientGroup.mk' R f₀ ∉ Subgroup.centralizer (J : Set (M ⧸ R)) := by
    rw [hf₀]
    intro hc
    exact hact1 ((actS_eq_one_iff hperf nf).mpr hc)
  exact r4_Eker hp2 R hR Y E hY hYc hE hEexp hYE hYΦ J f₀ hf₀E hfJ (T.map J.subtype) hT'J
    hT'1 hT'2 hTf hno

theorem r4_holds_gl12 (hLP : Sec4.Item4_1LargePrime)
    (hTC : Sec4.Item4_1ThreeCover) (h42 : Sec4.Item4_2) (hG1 : KFactG1)
    (hG1G : K135SF.KFactG1GL12) : R4 := by
  intro G _ _ A c L p C c4
  haveI : c4.R.Normal := c4.R_normal
  have hcrit := c4.crit
  have hp : p.Prime := hcrit.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hp7 : 7 ≤ p := c4.p_ge_seven
  have hp2 : p ≠ 2 := by omega
  have hzL := c4.z_mem
  have hY : Nat.card c4.Y = p := c4.Y_card
  obtain ⟨hY', hYc⟩ := r5g_Y_sub hp hY
  have hYD : c4.Y ≤ dPrime L p C c4.z := c4.Y_le.trans inf_le_left
  have hDp : IsPGroup p (dPrime L p C c4.z) := isPGroup_dPrime hcrit hzL
  have hDexp : ∀ x ∈ dPrime L p C c4.z, x ^ p = 1 := dPrime_exp hcrit hzL
  obtain ⟨hEp, hEexp, hYE, -⟩ := r5g_E_facts hDp hDexp hYD hY c4.Y_not_frattini
  have hTF : TheoremFourHyp G := c4.data.toTheoremFourHyp
  have hYne : c4.Y ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hY
    exact hp.one_lt.ne hY
  have hMne : cM c4.Y ≠ ⊤ := r5g_cM_ne_top hTF.isSimpleGroup hTF.nonabelian hYne
  have hSM : SectionFourHyp (cM c4.Y) := hTF.sectionFourHyp hMne
  have hJq : CFSG.IsQuasisimple c4.J := c4.J_comp.1
  have hcases : Sec4.Census.List42 (↥c4.J ⧸ Subgroup.center ↥c4.J) ∨
      (CFSG.IsKGroup (↥c4.J ⧸ Subgroup.center ↥c4.J) ∧
        K135SF.GL12Data (↥c4.J ⧸ Subgroup.center ↥c4.J)) :=
    K135SF.list42_or_gl12_of_relPPrimeCore hLP hTC h42 (cM c4.Y) hSM hp hp2 c4.R c4.R_eq c4.R_odd
      c4.R_coprime c4.J c4.J_comp
  have hR : ¬ p ∣ Nat.card c4.R := (Nat.Prime.coprime_iff_not_dvd hp).mp c4.R_coprime
  have hlr : CFSG.Assembly.RankThreeEven.localRank p G < 3 := hTF.localRank_lt p hp (by omega)
  have hno := hno_of_localRank hp hlr (cM c4.Y)
  have hu : c4.u ∈ cM c4.Y := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (c4.Y_le hy).2
  obtain ⟨hU2, hUf⟩ := r5g_U_facts c4.U_eq
  have hJ1 : c4.J ≠ ⊥ := by
    intro h
    obtain ⟨a, b, hab⟩ := hJq.2.2
    apply hab
    induction a using QuotientGroup.induction_on with
    | H a' =>
      induction b using QuotientGroup.induction_on with
      | H b' =>
        have ha : a' = 1 := Subtype.ext (by simpa [h] using a'.2)
        have hb : b' = 1 := Subtype.ext (by simpa [h] using b'.2)
        simp [ha, hb]
  have hUA : c4.U ≤ CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({c4.u} : Set G)) ⊓
      Subgroup.centralizer (c4.Y : Set G) := by
    rw [c4.U_eq]
    exact r5gl_commutator_le fun b hb x hx => r5gl_A_conj hb hx
  have hUM : c4.U ≤ cM c4.Y := hUA.trans inf_le_right
  have hBM : dPrime L p C c4.z ⊓ cM c4.Y ⊓ Subgroup.centralizer ({c4.u} : Set G) ≤ cM c4.Y :=
    inf_le_left.trans inf_le_right
  have hUB : ⁅c4.U, dPrime L p C c4.z ⊓ cM c4.Y ⊓ Subgroup.centralizer ({c4.u} : Set G)⁆ =
      c4.U := r4_U_comm hp hp2 hDp c4.U_eq
  have hmapcomm := r4_map_comm (cM c4.Y) c4.R hUM hBM hUB
  have hcomm : (c4.U.subgroupOf (cM c4.Y)).map (QuotientGroup.mk' c4.R) ≤
      ⁅(c4.U.subgroupOf (cM c4.Y)).map (QuotientGroup.mk' c4.R),
        ((dPrime L p C c4.z ⊓ cM c4.Y ⊓ Subgroup.centralizer ({c4.u} : Set G)).subgroupOf
          (cM c4.Y)).map (QuotientGroup.mk' c4.R)⁆ ⊔
        Subgroup.centralizer (c4.J : Set (cM c4.Y ⧸ c4.R)) :=
    le_sup_of_le_left hmapcomm.le
  have hUne : ¬ (c4.U.subgroupOf (cM c4.Y)).map (QuotientGroup.mk' c4.R) ≤
      Subgroup.centralizer (c4.J : Set (cM c4.Y ⧸ c4.R)) := by
    intro hle
    apply hJ1
    have hJU := c4.J_U
    have hbot : ⁅c4.J, (c4.U.subgroupOf (cM c4.Y)).map (QuotientGroup.mk' c4.R)⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro j hj v hv
      have hvc := Subgroup.mem_centralizer_iff.mp (hle hv) j hj
      rw [Subgroup.mem_bot, commutatorElement_def, hvc]
      group
    rw [← hJU, hbot]
  have hunc : ¬ (((⟨c4.u, hu⟩ : cM c4.Y) : cM c4.Y ⧸ c4.R) ∈
      Subgroup.centralizer (c4.J : Set (cM c4.Y ⧸ c4.R))) :=
    r4_u_nontrivial c4.u_sq hu c4.U_eq c4.R c4.R_odd c4.J hJq.1 hJ1 c4.J_U
  have hEN : (eOf (dPrime L p C c4.z) c4.Y).map (QuotientGroup.mk' c4.R) ≤
      Subgroup.normalizer (c4.J : Set (cM c4.Y ⧸ c4.R)) := by
    rintro _ ⟨e, he, rfl⟩
    exact c4.J_normE e he
  have hU2' : IsPGroup 2 ((c4.U.subgroupOf (cM c4.Y)).map (QuotientGroup.mk' c4.R)) :=
    (hU2.comap_subtype (K := cM c4.Y)).map _
  have hEuE : ((dPrime L p C c4.z ⊓ cM c4.Y ⊓ Subgroup.centralizer ({c4.u} : Set G)).subgroupOf
      (cM c4.Y)).map (QuotientGroup.mk' c4.R) ≤
      (eOf (dPrime L p C c4.z) c4.Y).map (QuotientGroup.mk' c4.R) := by
    rintro _ ⟨e, he, rfl⟩
    have he' : (e : G) ∈ dPrime L p C c4.z ⊓ cM c4.Y ⊓ Subgroup.centralizer ({c4.u} : Set G) :=
      Subgroup.mem_subgroupOf.mp he
    exact ⟨e, Subgroup.mem_subgroupOf.mpr he'.1, rfl⟩
  have hUEu : ((dPrime L p C c4.z ⊓ cM c4.Y ⊓ Subgroup.centralizer ({c4.u} : Set G)).subgroupOf
      (cM c4.Y)).map (QuotientGroup.mk' c4.R) ≤
      Subgroup.normalizer (((c4.U.subgroupOf (cM c4.Y)).map (QuotientGroup.mk' c4.R) :
        Subgroup (cM c4.Y ⧸ c4.R)) : Set (cM c4.Y ⧸ c4.R)) := by
    rintro _ ⟨e, he, rfl⟩
    exact r5g_map_normalizer c4.R _ (r5g_subgroupOf_normalizer (cM c4.Y) _ (hUf (e : G) he))
  have hker := r4_Eker_of_cases hG1 hG1G hp7 c4.R hR (c4.Y.subgroupOf (cM c4.Y))
    (eOf (dPrime L p C c4.z) c4.Y) hY' hYc hEp hEexp hYE
    (r4_E_comm_inf hDp hDexp hY c4.Y_not_frattini) c4.J hJq hcases hEN
    ((c4.U.subgroupOf (cM c4.Y)).map (QuotientGroup.mk' c4.R))
    (((dPrime L p C c4.z ⊓ cM c4.Y ⊓ Subgroup.centralizer ({c4.u} : Set G)).subgroupOf
      (cM c4.Y)).map (QuotientGroup.mk' c4.R))
    c4.J_normU hU2' hUne hEuE hUEu hcomm hno
  have hEker : Subgroup.centralizer (c4.J : Set (cM c4.Y ⧸ c4.R)) ⊓
      (eOf (dPrime L p C c4.z) c4.Y).map (QuotientGroup.mk' c4.R) ≤
      (c4.Y.subgroupOf (cM c4.Y)).map (QuotientGroup.mk' c4.R) := by
    rintro x ⟨hxc, e, he, rfl⟩
    exact ⟨e, hker e he hxc, rfl⟩
  have hE4 : p ^ 4 ≤ Nat.card (eOf (dPrime L p C c4.z) c4.Y) :=
    r4_card_eOf hDp hDexp (dPrime_frattini_central hcrit hzL) hYD hY c4.Dp_rank
  have hidx := r4_E_index hp c4.R hR hEp (le_of_eq hY') hE4 c4.J hEker
  exact ⟨{ c4 with
    E_index := hidx
    U_nontrivial := hUne
    u_nontrivial := fun _ => hunc
    U_comm_Eu := hcomm
    E_ker := hEker }⟩

end CFSG.RankThree.PartTwo.Sec13.F135Last
