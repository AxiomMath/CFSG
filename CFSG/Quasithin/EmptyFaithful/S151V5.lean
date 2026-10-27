module

public import CFSG.Quasithin.EmptyFaithful.S151XC
public import CFSG.Quasithin.EmptyFaithful.T1515eA
public import CFSG.Quasithin.EmptyFaithful.S151ZT
public import CFSG.Quasithin.EmptyFaithful.S151V0
public import CFSG.Quasithin.EmptyFaithful.S151V3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.FLc
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem case15122Two_of_ln3 (hK : KnownFacts15122Types) {T Mc M Z₁ L : Subgroup G}
    (hb : IsLnBlock L 3) (h22 : Lemma15122Concl T Mc M Z₁ L) : Case15122Two T M Mc Z₁ L := by
  obtain ⟨e, β, hs⟩ := exists_lnStr hb
  have h9 := s151v_not_nine_dvd_card hs
  have hquot : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) ∣ Nat.card ↥L := Subgroup.card_quotient_dvd_card _
  have hcen : Nat.card (↥L ⧸ Subgroup.center ↥L) ∣ Nat.card ↥L := Subgroup.card_quotient_dvd_card _
  rcases h22 with h | h | h | h | h | h | h
  · exfalso
    obtain ⟨e7⟩ := quotPCore_equiv_alt_of_isAltBlockType h.1
    apply h9
    have := hK.alt7.nine_dvd_card
    rw [← Nat.card_congr e7.toEquiv] at this
    exact this.trans hquot
  · exact h
  · exfalso
    apply h9
    rcases h.2.1 with h1 | h1
    · exact (hK.l42 _ h1).nine_dvd_card.trans hquot
    · exact (hK.l52 _ h1).nine_dvd_card.trans hquot
  · exfalso
    apply h9
    rcases h.1 with h1 | h1 | h1
    · exact (hK.u33 _ h1).nine_dvd_card
    · exact (hK.tits _ h1).nine_dvd_card
    · exact (hK.d42 _ h1).nine_dvd_card
  · exfalso
    apply h9
    rcases h.1 with h1 | h1 | h1 | h1 | h1 | h1
    · exact (hK.j2 _ h1).nine_dvd_card.trans hcen
    · exact (hK.he _ h1).nine_dvd_card.trans hcen
    · exact (hK.m12 _ h1).nine_dvd_card.trans hcen
    · exact (hK.m22 _ h1).nine_dvd_card.trans hcen
    · exact (hK.m23 _ h1).nine_dvd_card.trans hcen
    · exact (hK.m24 _ h1).nine_dvd_card.trans hcen
  · exfalso
    exact h9 (hK.m11 _ h.1).nine_dvd_card
  · exfalso
    apply h9
    rcases h.1 with h1 | h1
    · exact (hK.l42 _ h1).nine_dvd_card
    · exact (hK.l52 _ h1).nine_dvd_card

omit [Finite G] in
theorem oTwoUpper_oPrimeResidualOf_three (X : Subgroup G) :
    oTwoUpper (oPrimeResidualOf 3 X) = oPrimeResidualOf 3 X := by
  refine le_antisymm (oTwoUpper_le _) ?_
  refine (Subgroup.closure_le (oTwoUpper (oPrimeResidualOf 3 X))).mpr ?_
  intro x hx
  obtain ⟨hxX, k, hk⟩ := hx
  apply Subgroup.subset_closure
  refine ⟨Subgroup.subset_closure ⟨hxX, k, hk⟩, ?_⟩
  rw [hk]
  exact Odd.pow (by decide)

omit [Finite G] in
theorem isMaxSubgroupIn_of_isMaxParabolic2 {L B P : Subgroup G}
    (hselfN : L ⊓ Subgroup.normalizer (B : Set G) ≤ B) (hB : IsSylowTwoOf B L) (hBP : B ≤ P)
    (hP : IsMaxParabolic2 L P) : IsMaxSubgroupIn L P := by
  refine ⟨lt_of_le_of_ne hP.1.1 hP.2.1, fun K hK hKL => ?_⟩
  by_contra hKne
  have hKpar : IsParabolic2 L K := ⟨hKL, B, hB, hselfN.trans (hBP.trans hK.le)⟩
  exact hK.ne (hP.2.2 K hKpar hKne hK.le).symm

omit [Finite G] in
theorem pow_action_of_card_three {Y V : Subgroup G} (hYN : Y ≤ Subgroup.normalizer (V : Set G))
    (h3 : Nat.card (autOn Y V) = 3) {c : G} (hcY : c ∈ Y) (hc : ∃ a ∈ V, c * a * c⁻¹ ≠ a) :
    ∀ y ∈ Y, ∃ i : ℕ, ∀ a ∈ V, y * a * y⁻¹ = c ^ i * a * (c ^ i)⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hσ : conjAct V ⟨c, hYN hcY⟩ ∈ autOn Y V := mem_autOn_iff_exists.mpr ⟨c, hYN hcY, hcY, rfl⟩
  let σ : autOn Y V := ⟨conjAct V ⟨c, hYN hcY⟩, hσ⟩
  have hσ1 : σ ≠ 1 := by
    intro h
    obtain ⟨a, ha, hne⟩ := hc
    apply hne
    have h1 : conjAct V ⟨c, hYN hcY⟩ = 1 := congrArg Subtype.val h
    have h2 := congrArg (fun φ : MulAut V => ((φ ⟨a, ha⟩ : V) : G)) h1
    exact h2
  intro y hy
  have hτ : conjAct V ⟨y, hYN hy⟩ ∈ autOn Y V := mem_autOn_iff_exists.mpr ⟨y, hYN hy, hy, rfl⟩
  have hmem : (⟨conjAct V ⟨y, hYN hy⟩, hτ⟩ : autOn Y V) ∈ Submonoid.powers σ :=
    mem_powers_of_prime_card h3 hσ1
  obtain ⟨i, hi⟩ := hmem
  refine ⟨i, fun a ha => ?_⟩
  have h1 : (conjAct V ⟨c, hYN hcY⟩) ^ i = conjAct V ⟨y, hYN hy⟩ := congrArg Subtype.val hi
  rw [← map_pow] at h1
  have h2 := congrArg (fun φ : MulAut V => ((φ ⟨a, ha⟩ : V) : G)) h1
  have h3' : ((⟨c, hYN hcY⟩ ^ i : Subgroup.normalizer (V : Set G)) : G) = c ^ i := by
    rw [Subgroup.coe_pow]
  have h4 : ((conjAct V (⟨c, hYN hcY⟩ ^ i) ⟨a, ha⟩ : V) : G) = c ^ i * a * (c ^ i)⁻¹ := by
    show ((⟨c, hYN hcY⟩ ^ i : Subgroup.normalizer (V : Set G)) : G) * a *
      ((⟨c, hYN hcY⟩ ^ i : Subgroup.normalizer (V : Set G)) : G)⁻¹ = c ^ i * a * (c ^ i)⁻¹
    rw [h3']
  rw [h4] at h2
  exact h2.symm

theorem v2_data (hK : KnownFacts15122Types) {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G}
    (h15 : Lemma1515Concl T Mc M) (hc : Ctx15124 T Mc M Z₁ Z₂ V₁ V₂ L) (hb : IsLnBlock L 3) :
    oPrimeResidualOf 3 (M ⊓ L) ≤ L ∧ V₂ ≤ oPrimeResidualOf 3 (M ⊓ L) ∧
      (∀ y ∈ oPrimeResidualOf 3 (M ⊓ L), ∀ a ∈ V₂, y * a * y⁻¹ ∈ V₂) ∧
      (∃ c ∈ oPrimeResidualOf 3 (M ⊓ L), ∀ a ∈ V₂, c * a * c⁻¹ = a → a = 1) := by
  classical
  have hS := hc.ctx.setting
  have hq := hc.ctx.qtfe
  have hMf := hc.ctx.mf
  have hLG : L ≤ g1_1516 Z₁ := le_of_mem_cComp hc.hL.comp
  obtain ⟨-, -, hMLpar, hPpar, hne, -⟩ := case15122Two_of_ln3 hK hb hc.h22
  have hsyl : IsSylowTwoOf (s1516 T Z₁ ⊓ L) L :=
    lemma_15_1_20_sylow hc.h18.four (hc.hL.isL1520 hc.h18.four (hS.pCore_g1_ne_bot hq hMf))
  obtain ⟨hselfN, hlat⟩ := input15122Rank2Lat_L3 G L _ hb hsyl
  have hTM : T ≤ M := hMf.1.1.2
  have hSMZ : s1516 T Z₁ ≤ mZ1516 Mc Z₁ := fun x hx =>
    ⟨s1516_le_g1 T Z₁ hx, hq.t_le_mc (s1516_le T Z₁ hx)⟩
  have hBML : s1516 T Z₁ ⊓ L ≤ mZ1516 Mc Z₁ ⊓ L := inf_le_inf_right _ hSMZ
  have hBP : s1516 T Z₁ ⊓ L ≤ M ⊓ L := inf_le_inf_right _ ((s1516_le T Z₁).trans hTM)
  have hMLmax := isMaxSubgroupIn_of_isMaxParabolic2 hselfN hsyl hBML hMLpar
  have hPmax := isMaxSubgroupIn_of_isMaxParabolic2 hselfN hsyl hBP hPpar
  obtain ⟨P', hP'⟩ := hlat _ hMLmax hBML
  have hPeq : M ⊓ L = P' := (hP'.only _ hPmax hBP).resolve_left (fun h => hne h.symm)
  have hcard3 : Nat.card ↥(M ⊓ L) = 3 * Nat.card ↥(s1516 T Z₁ ⊓ L) := by
    rw [hPeq]; exact hP'.card3
  have hsup := zb_oPrime_sup_eq hBP hcard3 hsyl.2.1
  set Y₀ := oPrimeResidualOf 3 (M ⊓ L) with hY₀
  have hY₀L : Y₀ ≤ L := zb_oPrime_le.trans inf_le_right
  have hnot : ¬ Y₀ ≤ mZ1516 Mc Z₁ := by
    intro hle
    have hYML : Y₀ ≤ mZ1516 Mc Z₁ ⊓ L := le_inf hle hY₀L
    have hPle : M ⊓ L ≤ mZ1516 Mc Z₁ ⊓ L := by
      rw [← hsup]; exact sup_le hYML hBML
    rcases lt_or_eq_of_le hPle with hlt | heq
    · exact hMLpar.2.1 (hPmax.2 _ hlt inf_le_right)
    · exact hne heq.symm
  have hY₀Y : Y₀ ≤ oPrimeResidualOf 3 (M ⊓ g1_1516 Z₁) :=
    oPrimeResidualOf_mono1516 3 (inf_le_inf_left M hLG)
  obtain ⟨hcomm, hindex⟩ := lemma_15_1_24_three hS h15 hc.small Y₀
    (oTwoUpper_oPrimeResidualOf_three _) hY₀Y hnot
  have hV2ab : IsElemAbelian 2 V₂ := isElemAbelian_mono151 hS.v2_le (hS.V_isElemAbelian hq hMf)
  have hcommV : ∀ a ∈ V₂, ∀ b ∈ V₂, a * b = b * a := by
    intro a ha b hb
    have := hV2ab.1
    have h1 := mul_comm' (⟨a, ha⟩ : V₂) ⟨b, hb⟩
    exact congrArg (fun z : V₂ => (z : G)) h1
  have hYN : Y₀ ≤ Subgroup.normalizer (V₂ : Set G) := hY₀Y.trans (hS.y_facts hc.small).1.2.2.2
  have hnorm : ∀ y ∈ Y₀, ∀ a ∈ V₂, y * a * y⁻¹ ∈ V₂ := fun y hy a ha =>
    (Subgroup.mem_normalizer_iff.mp (hYN hy) a).mp ha
  have hV2T : V₂ ≤ T := hS.v2_le.trans (hS.V_le_T hq hMf)
  have hV2L : V₂ ≤ Subgroup.normalizer (L : Set G) :=
    le_sup_right.trans (hc.h19.seven L hc.hL.comp hc.hL.quasi hc.hL.not_le).1
  have hV2N : V₂ ≤ Subgroup.normalizer ((M ⊓ L : Subgroup G) : Set G) := fun v hv =>
    zb_mem_normalizer_inf (Subgroup.le_normalizer (hTM (hV2T hv))) (hV2L hv)
  have hV2NY : ∀ v ∈ V₂, v ∈ Subgroup.normalizer (Y₀ : Set G) := fun v hv =>
    zb_normalizes_oPrime (hV2N hv)
  have hV2Y₀ : V₂ ≤ Y₀ := by
    have hle : ⁅V₂, Y₀⁆ ≤ Y₀ := by
      rw [Subgroup.commutator_le]
      intro a ha y hy
      have h1 := (Subgroup.mem_normalizer_iff.mp (hV2NY a ha) y).mp hy
      have h2 : ⁅a, y⁆ = (a * y * a⁻¹) * y⁻¹ := by simp only [commutatorElement_def, mul_assoc]
      rw [h2]
      exact Y₀.mul_mem h1 (Y₀.inv_mem hy)
    rw [hcomm] at hle
    exact hle
  obtain ⟨c, hcY, hcne⟩ : ∃ c ∈ Y₀, c ∉ Subgroup.centralizer (V₂ : Set G) := by
    by_contra hall
    push Not at hall
    have h1 : Y₀ ⊓ Subgroup.centralizer (V₂ : Set G) = Y₀ := inf_eq_left.mpr hall
    rw [h1, Subgroup.relIndex_self] at hindex
    exact absurd hindex (by norm_num)
  have hc' : ∃ a ∈ V₂, c * a * c⁻¹ ≠ a := by
    by_contra hall
    push Not at hall
    apply hcne
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have := hall a ha
    calc a * c = (c * a * c⁻¹) * c := by rw [this]
      _ = c * a := by group
  have h3 : Nat.card (autOn Y₀ V₂) = 3 := by rw [card_autOn_eq_relIndex hYN]; exact hindex
  have hpow := pow_action_of_card_three hYN h3 hcY hc'
  exact ⟨hY₀L, hV2Y₀, hnorm, c, hcY, fpf_of_commutator_eq hcommV hnorm hcY hpow hcomm.ge⟩

end CFSG.Quasithin
