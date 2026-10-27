module

public import CFSG.RankThree.PartTwo.Sec18.Item18ResProofAlt1C
public import CFSG.RankThree.PartTwo.Sec18.Item183OneProofRem
public import CFSG.RankThree.PartTwo.Sec18.Item183OneProofRemRank

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)
open scoped Pointwise

open Rem187QProof

theorem rem187Q_of_alt1C
    (h1812 : Item181_2)
    (h1841 : Item184_1) (hAlt : Item182Alt1C) : Rem187Q := by
  intro G _ _ A M H c hHc _ _ hQ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h : Sec18Std G A M := hHc.toSec18Std
  have : IsSimpleGroup G := h.isSimpleGroup
  have hA : IsE27 A := isE27_of_mem_partTwoE h.mem_partTwoE
  have hH : H ∈ scriptH A M := hHc.mem_scriptH
  have hH₀ := (mem_scriptH_iff_mem_scriptH₀.mp hH).1
  have hAH : A ≤ H := le_of_mem_scriptH₀ hH₀
  set L := inSubgroup perfectResidual H with hLdef
  set C := Subgroup.centralizer ({c} : Set G) with hCdef
  set Z := Subgroup.zpowers c with hZdef
  have hcS : c ∈ sectionCentralizer A L (CFSG.Open.pCoreOf 2 L) := by
    rw [hHc.centralizer_eq]
    exact Subgroup.mem_zpowers c
  have hcA : c ∈ A := hcS.1
  have hcL := hcS.2
  obtain ⟨⟨eL⟩, c₀, hc₀3, hc₀⟩ := h1841 G A M h H hH
  have hc1 : c ≠ 1 := by
    intro hc
    have hZc : (Subgroup.zpowers c₀ : Set G) = Subgroup.zpowers c := hc₀.symm.trans
      hHc.centralizer_eq
    have h1 : Subgroup.zpowers c₀ = Subgroup.zpowers c := SetLike.coe_injective hZc
    have h2 := congrArg (fun S : Subgroup G => Nat.card S) h1
    simp only [Nat.card_zpowers, hc₀3, hc, orderOf_one] at h2
    norm_num at h2
  have hc3 : orderOf c = 3 := by
    have hZc : (Subgroup.zpowers c₀ : Set G) = Subgroup.zpowers c := hc₀.symm.trans
      hHc.centralizer_eq
    have h1 : Subgroup.zpowers c₀ = Subgroup.zpowers c := SetLike.coe_injective hZc
    have h2 := congrArg (fun S : Subgroup G => Nat.card S) h1
    simp only [Nat.card_zpowers, hc₀3] at h2
    exact h2.symm
  have hcpow : c ^ 3 = 1 := hA.1.2 c hcA
  have hAC : A ≤ C := fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨c, hcA⟩))
  have hCZ : C ≤ Subgroup.normalizer (Z : Set G) := centralizer_le_normalizer_zpowers c
  obtain ⟨s, ⟨hsS, hsA, hgf, hsH, X, hXn, hX, hXt, -⟩, -, -⟩ := h1812 G A M h H hH
  have hout : Sec4.InducesOuterTheta s L := hgf.inducesOuterTheta _ (by decide)
  obtain ⟨Hc, hHcH, hHcC, hHcres⟩ :=
    exists_mem_scriptH_le_centralizer h hH hsH hsS hsA hout hcA hcL
  set Lc := inSubgroup perfectResidual (H ⊓ C) with hLcdef
  obtain ⟨h9, hcnL⟩ := card_inf_ge_and_not_mem h hH eL hsH hsS hX hXt hcA hc1 hcL
  have hLcHC : Lc ≤ H ⊓ C := Subgroup.map_subtype_le _
  have hLcL : Lc ≤ L := inSubgroup_perfectResidual_mono inf_le_left
  set B := A ⊓ Lc with hBdef
  have hBA : B ≤ A := inf_le_left
  have hBLc : B ≤ Lc := inf_le_right
  have hBC : B ≤ C := hBA.trans hAC
  have hBZ : B ⊓ Z = ⊥ := by
    rw [eq_bot_iff]
    intro b hb
    by_contra hb1
    have hb1' : b ≠ 1 := fun h => hb1 (Subgroup.mem_bot.mpr h)
    have hZb : (Z : Set G) = Subgroup.zpowers b :=
      coe_zpowers_eq_of_mem rfl hc3 hb.2 hb1'
    have hcb : c ∈ Subgroup.zpowers b := by
      rw [← SetLike.mem_coe, ← hZb]
      exact Subgroup.mem_zpowers c
    exact hcnL (hLcL (hBLc ((Subgroup.zpowers_le.mpr hb.1) hcb)))
  have hB9 : Nat.card B = 9 := by
    have hdvd : Nat.card B ∣ 3 ^ 3 := by
      rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← hA.2]
      exact Subgroup.card_dvd_of_le hBA
    obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    interval_cases k
    · rw [hk] at h9; norm_num at h9
    · rw [hk] at h9; norm_num at h9
    · rw [hk]; norm_num
    · exfalso
      have heq : B = A := Subgroup.eq_of_le_of_card_ge hBA (by rw [hk, hA.2]; norm_num)
      have hcB : c ∈ B := heq ▸ hcA
      have : c ∈ B ⊓ Z := ⟨hcB, Subgroup.mem_zpowers c⟩
      rw [hBZ, Subgroup.mem_bot] at this
      exact hc1 this
  have hABZ : A = B ⊔ Z := by
    have hle : B ⊔ Z ≤ A := sup_le hBA (Subgroup.zpowers_le.mpr hcA)
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    have h1 := Sec6.card_sup_mul_card_inf (X := B) (N := Z) (hBC.trans hCZ)
    rw [hBZ, Subgroup.card_bot, mul_one, hB9, Nat.card_zpowers, hc3] at h1
    rw [h1, hA.2]
  set Q := CFSG.Open.pCoreOf 2 C with hQdef
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 C
  set XQ := Subgroup.normalizer (Q : Set G) with hXQdef
  have hXQ2 : CFSG.Assembly.IsTwoLocal XQ := ⟨Q, hQ, hQ2, rfl⟩
  have hXQtop : XQ ≠ ⊤ := normalizer_ne_top_of_isPGroup_two h.nonabelian hQ2 hQ
  have hCXQ : C ≤ XQ := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 C
  have hXQO : CFSG.Open.pCoreOf 2 XQ ≠ ⊥ := by
    have hle : Q ≤ CFSG.Open.pCoreOf 2 XQ :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hQ2
    exact fun hb => hQ (le_bot_iff.mp (hb ▸ hle))
  have hHcXQ : Hc ≤ XQ := hHcC.trans hCXQ
  have hcHc : c ∈ sectionCentralizer A (inSubgroup perfectResidual Hc)
      (CFSG.Open.pCoreOf 2 (inSubgroup perfectResidual Hc)) := by
    refine ⟨hcA, fun l hl => ?_⟩
    rw [hHcres] at hl
    have hlc : c * l = l * c := (Subgroup.mem_centralizer_singleton_iff.mp (hLcHC hl).2).symm
    rw [hlc, mul_inv_cancel_right, mul_inv_cancel]
    exact Subgroup.one_mem _
  obtain ⟨KQ, hKQ, hKQeq₀⟩ := hAlt G A M h Hc hHcH XQ hHcXQ hXQtop c hcA hc1 hCXQ hcHc
  have hKQeq : KQ = Lc ⊔ CFSG.Open.pCoreOf 2 KQ := by rw [← hHcres]; exact hKQeq₀
  have hKQXQ : KQ ≤ XQ := le_of_mem_oTwoComponentsIn hKQ
  have hLcKQ : Lc ≤ KQ := hKQeq ▸ le_sup_left
  have hKQO : CFSG.Open.pCoreOf 2 KQ ≠ ⊥ :=
    pCoreOf_ne_bot_of_mem_oTwoComponentsIn h.charTwoType hXQ2 hKQ
  have hKQp : ⁅KQ, KQ⁆ = KQ := commutator_eq_of_mem_oTwoComponentsIn hKQ
  have hNLc : ∀ x, x ∈ XQ → x ∈ Subgroup.normalizer (Lc : Set G) →
      x ∈ Subgroup.normalizer (KQ : Set G) := fun x hx hxL =>
    mem_normalizer_of_eq_sup hKQ hKQeq hx hxL
  have hHcLc : Hc ≤ Subgroup.normalizer (Lc : Set G) := by
    rw [← hHcres]
    exact le_normalizer_inSubgroup_perfectResidual Hc
  have hAHc : A ≤ Hc := le_of_mem_scriptH₀ (mem_scriptH_iff_mem_scriptH₀.mp hHcH).1
  have hAKQ : A ≤ Subgroup.normalizer (KQ : Set G) := fun a ha =>
    hNLc a (hCXQ (hAC ha)) (hHcLc (hAHc ha))
  set HQ := KQ ⊔ A ⊔ CFSG.Open.pCoreOf 2 (Hc ⊓ M) with hHQdef
  have hHQ : HQ ∈ scriptH A M := mem_scriptH_of_eq_sup h hHcH hHcXQ hXQtop hKQ hKQeq₀
  have hKQHQ : KQ ≤ HQ := le_sup_left.trans le_sup_left
  have hHQKQ : HQ ≤ Subgroup.normalizer (KQ : Set G) := by
    refine sup_le (sup_le Subgroup.le_normalizer hAKQ) fun x hx => ?_
    have hxHc : x ∈ Hc := (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hx).1
    exact hNLc x (hHcXQ hxHc) (hHcLc hxHc)
  have hHQres : inSubgroup perfectResidual HQ = KQ := by
    have hn : (KQ.subgroupOf HQ).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKQHQ).mpr hHQKQ
    exact (eq_of_mem_oTwoComponentsIn_of_mem_scriptH hHQ
      (mem_oTwoComponentsIn_of_le hKQ hKQHQ hn.isSubnormal)).symm
  obtain ⟨⟨eKQ⟩, cQ, hcQ3, hcQ⟩ := h1841 G A M h HQ hHQ
  rw [hHQres] at hcQ
  have hKQcard : Nat.card (KQ ⧸ CFSG.pCore 2 KQ) = 20160 :=
    (card_quotient_pCore_congr hHQres).symm.trans
      ((Nat.card_congr eKQ.toEquiv).trans KFacts.L34.card_projSL)
  have hcKQ : c ∈ Subgroup.normalizer (KQ : Set G) := hAKQ hcA
  have hcSKQ : c ∈ sectionCentralizer A KQ (CFSG.Open.pCoreOf 2 KQ) := by
    refine mem_sectionCentralizer_of_eq_sup hcA hLcKQ hKQeq hcKQ fun y hy => ?_
    have hyc : c * y = y * c :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hLcHC hy).2).symm
    rw [hyc, mul_inv_cancel_right, mul_inv_cancel]
    exact Subgroup.one_mem _
  have hCAKQ : sectionCentralizer A KQ (CFSG.Open.pCoreOf 2 KQ) = (Z : Set G) :=
    coe_zpowers_eq_of_mem hcQ hcQ3 hcSKQ hc1
  have hNZXQ : Subgroup.normalizer (Z : Set G) ≤ XQ := fun g hg =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 C
      (mem_normalizer_centralizer_of_mem_normalizer_zpowers hg)
  have hBK : B ≤ KQ := hBLc.trans hLcKQ
  have hBtriv : ∀ b ∈ B, (∀ k ∈ KQ, b * k * b⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 XQ) → b = 1 := by
    intro b hb hbk
    have hbS : b ∈ sectionCentralizer A KQ (CFSG.Open.pCoreOf 2 KQ) := by
      refine ⟨hb.1, fun k hk => ?_⟩
      have h1 : b * k * b⁻¹ * k⁻¹ ∈ KQ :=
        KQ.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAKQ hb.1) k).mp hk) (KQ.inv_mem hk)
      have hle : CFSG.Open.pCoreOf 2 XQ ⊓ KQ ≤ CFSG.Open.pCoreOf 2 KQ :=
        CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
          (fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
            ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 XQ (hKQXQ hx),
              Subgroup.le_normalizer hx⟩)
          ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 XQ).to_le inf_le_left)
      exact hle ⟨hbk k hk, h1⟩
    rw [hCAKQ] at hbS
    have : b ∈ B ⊓ Z := ⟨hb, hbS⟩
    rw [hBZ, Subgroup.mem_bot] at this
    exact this
  have hrank : CFSG.Assembly.RankThreeEven.localRank 3 G ≤ 3 :=
    h.toTheoremFourHyp.localRank_three.le
  have hNZKQ : Subgroup.normalizer (Z : Set G) ≤ Subgroup.normalizer (KQ : Set G) :=
    fun g hg => mem_normalizer_of_localRank hXQO hKQ hBK (fun b hb => hA.1.2 b (hBA hb))
      (fun b hb b' hb' => congrArg Subtype.val (hA.1.1.is_comm.comm ⟨b, hBA hb⟩ ⟨b', hBA hb'⟩))
      hB9 hBtriv hrank (hNZXQ hg)
  have hBSyl : CFSG.ABGLocalTools.IsSylowOf 3 B (KQ ⊓ C) := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_inf hBK hBC, ?_, fun h3 => ?_⟩
    · exact IsPGroup.of_card (n := 2) (by rw [hB9]; norm_num)
    · have h1 := Subgroup.relIndex_mul_card B (KQ ⊓ C)
      rw [inf_eq_left.mpr (le_inf hBK hBC), hB9] at h1
      have h27 : 27 ∣ Nat.card (KQ ⊓ C : Subgroup G) := by
        rw [← h1]
        exact (show (27 : ℕ) = 3 * 9 by norm_num) ▸ Nat.mul_dvd_mul_right h3 9
      have hdvd : Nat.card (KQ ⊓ C : Subgroup G) ∣ Nat.card KQ :=
        Subgroup.card_dvd_of_le inf_le_left
      have hKcard : Nat.card KQ = Nat.card (CFSG.pCore 2 KQ) * 20160 := by
        rw [← hKQcard, ← Subgroup.index_eq_card, Subgroup.card_mul_index]
      obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (p := 2) (G := KQ)).exists_card_eq
      rw [hKcard, ha] at hdvd
      have h2 : 27 ∣ 2 ^ a * 20160 := h27.trans hdvd
      have hcop : Nat.Coprime 27 (2 ^ a) := Nat.Coprime.pow_right a (by norm_num)
      have := hcop.dvd_of_dvd_mul_left h2
      norm_num at this
  set 𝓕 : Set (Subgroup G) := {H' : Subgroup G | H' ∈ scriptH A M ∧ KQ ≤ H'} with h𝓕
  set R : Subgroup G := ⨆ H' ∈ 𝓕, CFSG.Open.pCoreOf 2 H' with hRdef
  have hRM : R ≤ M := iSup₂_le fun H' hH'𝓕 =>
    le_of_le_normalizer_of_isPGroup_two h (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H')
      ((le_of_mem_scriptH₀ (mem_scriptH_iff_mem_scriptH₀.mp hH'𝓕.1).1).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H'))
  have hO2R : ∀ H' ∈ 𝓕, CFSG.Open.pCoreOf 2 H' ≤ R := fun H' hH' =>
    le_iSup₂ (f := fun H' (_ : H' ∈ 𝓕) => CFSG.Open.pCoreOf 2 H') H' hH'
  have hHQ𝓕 : HQ ∈ 𝓕 := ⟨hHQ, hKQHQ⟩
  have hKQOHQ : CFSG.Open.pCoreOf 2 KQ ≤ CFSG.Open.pCoreOf 2 HQ := by
    rw [← hHQres]
    exact pCoreOf_perfectResidual_le HQ
  have hR1 : R ≠ ⊥ := fun hb =>
    hKQO (le_bot_iff.mp (hb ▸ hKQOHQ.trans (hO2R HQ hHQ𝓕)))
  have hMtop : M ≠ ⊤ :=
    ne_top_of_pCoreOf_ne_bot h.nonabelian (pCoreOf_ne_bot_of_isMaximalTwoLocal h.mem_scriptM.1)
  have hNRtop : Subgroup.normalizer (R : Set G) ≠ ⊤ := by
    intro htop
    have hRn : R.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal R with hb | ht
    · exact hR1 hb
    · exact hMtop (top_le_iff.mp (ht ▸ hRM))
  have hKQR : KQ ≤ Subgroup.normalizer (R : Set G) := fun y hy =>
    mem_normalizer_iSup h (Or.inl hy)
  have hNZR : Subgroup.normalizer (Z : Set G) ≤ Subgroup.normalizer (R : Set G) := by
    intro g hg
    obtain ⟨y, hy, w, hwA, hwZ, rfl⟩ := exists_mul_of_frattini hNZKQ hBSyl hABZ hg
    exact Subgroup.mul_mem _ (hKQR hy.1) (mem_normalizer_iSup h (Or.inr ⟨hwA, hNZKQ hwZ⟩))
  have hres𝓕 : ∀ H' ∈ 𝓕, inSubgroup perfectResidual H' =
      KQ ⊔ CFSG.Open.pCoreOf 2 (inSubgroup perfectResidual H') := by
    intro H' ⟨hH', hKH'⟩
    have hKL' : KQ ≤ inSubgroup perfectResidual H' := le_inSubgroup_perfectResidual hKQp hKH'
    refine eq_sup_pCoreOf_of_card_le hKL' ?_
    obtain ⟨⟨e'⟩, -⟩ := h1841 G A M h H' hH'
    rw [hKQcard, Nat.card_congr e'.toEquiv, KFacts.L34.card_projSL]
  have hle𝓕 : ∀ H' ∈ 𝓕, H' ≤ Subgroup.normalizer (R : Set G) := by
    intro H' hH'𝓕
    obtain ⟨hH', hKH'⟩ := id hH'𝓕
    have hH'₀ := (mem_scriptH_iff_mem_scriptH₀.mp hH').1
    obtain ⟨s', ⟨-, hs'A, -⟩, hs'eq, -⟩ := h1812 G A M h H' hH'
    have hO2 : CFSG.Open.pCoreOf 2 H' ≤ Subgroup.normalizer (R : Set G) :=
      (hO2R H' hH'𝓕).trans Subgroup.le_normalizer
    have hres : inSubgroup perfectResidual H' ≤ Subgroup.normalizer (R : Set G) := by
      rw [hres𝓕 H' ⟨hH', hKH'⟩]
      exact sup_le hKQR ((pCoreOf_perfectResidual_le H').trans hO2)
    have hAR : A ≤ Subgroup.normalizer (R : Set G) := fun a ha => hNZR (hCZ (hAC ha))
    have hs'R : s' ∈ Subgroup.normalizer (R : Set G) := by
      refine hNZR (hCZ ?_)
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hs'A c hcA).symm
    have hT : CFSG.Open.pCoreOf 2 (H' ⊓ M) ≤ Subgroup.normalizer (R : Set G) := by
      rw [hs'eq]
      exact sup_le (Subgroup.zpowers_le.mpr hs'R) hO2
    exact hH'₀.1.le.trans (sup_le (sup_le hres hAR) hT)
  obtain ⟨H₁, hHQH₁, hH₁max⟩ :=
    Finite.exists_le_maximal (p := fun Y : Subgroup G => Y ∈ scriptH A M) hHQ
  have hH₁ : H₁ ∈ scriptH A M := hH₁max.prop
  have hH₁₀ := (mem_scriptH_iff_mem_scriptH₀.mp hH₁).1
  have hAH₁ : A ≤ H₁ := le_of_mem_scriptH₀ hH₁₀
  have hKQH₁ : KQ ≤ H₁ := hKQHQ.trans hHQH₁
  have hH₁𝓕 : H₁ ∈ 𝓕 := ⟨hH₁, hKQH₁⟩
  have hH₁R : H₁ ≤ Subgroup.normalizer (R : Set G) := hle𝓕 H₁ hH₁𝓕
  set L₁ := inSubgroup perfectResidual H₁ with hL₁def
  have hKQL₁ : KQ ≤ L₁ := le_inSubgroup_perfectResidual hKQp hKQH₁
  have hcmem₁ : c ∈ sectionCentralizer A L₁ (CFSG.Open.pCoreOf 2 L₁) := by
    have hKQO₁ : CFSG.Open.pCoreOf 2 KQ ≤ CFSG.Open.pCoreOf 2 L₁ :=
      pCoreOf_le_pCoreOf_of_eq_sup hKQL₁ (hres𝓕 H₁ hH₁𝓕)
    exact mem_sectionCentralizer_of_eq_sup hcA hKQL₁ (hres𝓕 H₁ hH₁𝓕)
      (le_normalizer_inSubgroup_perfectResidual H₁ (hAH₁ hcA))
      fun y hy => hKQO₁ (hcSKQ.2 y hy)
  obtain ⟨K₁, hK₁, hK₁eq⟩ := hAlt G A M h H₁ hH₁ _ hH₁R hNRtop c hcA hc1
    (fun x hx => hNZR (hCZ hx)) hcmem₁
  have hK₁mem := mem_scriptH_of_eq_sup h hH₁ hH₁R hNRtop hK₁ hK₁eq
  have hL₁K₁ : L₁ ≤ K₁ := hK₁eq ▸ le_sup_left
  have hH₁le : H₁ ≤ K₁ ⊔ A ⊔ CFSG.Open.pCoreOf 2 (H₁ ⊓ M) :=
    hH₁₀.1.le.trans (sup_le (sup_le (hL₁K₁.trans (le_sup_left.trans le_sup_left))
      (le_sup_right.trans le_sup_left)) le_sup_right)
  have hge : K₁ ⊔ A ⊔ CFSG.Open.pCoreOf 2 (H₁ ⊓ M) ≤ H₁ := hH₁max.le_of_ge hK₁mem hH₁le
  have hK₁L₁ : K₁ ≤ L₁ := le_inSubgroup_perfectResidual
    (commutator_eq_of_mem_oTwoComponentsIn hK₁) ((le_sup_left.trans le_sup_left).trans hge)
  have hL₁Y : L₁ ∈ oTwoComponentsIn (Subgroup.normalizer (R : Set G)) :=
    (le_antisymm hL₁K₁ hK₁L₁) ▸ hK₁
  have hNZL₁ : Subgroup.normalizer (Z : Set G) ≤ Subgroup.normalizer (L₁ : Set G) := by
    intro g hg
    have hgR := hNZR hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    by_contra hne
    have hL₁g := map_conj_mem_oTwoComponentsIn hL₁Y hgR
    have hKQg : KQ ≤ L₁.map (MulAut.conj g).toMonoidHom := by
      rw [← map_conj_eq_of_mem_normalizer (hNZKQ hg)]
      exact Subgroup.map_mono hKQL₁
    have hcomm : ⁅KQ, KQ⁆ ≤ CFSG.Open.pCoreOf 2 (Subgroup.normalizer (R : Set G)) := by
      rw [Subgroup.commutator_le]
      intro k hk k' hk'
      exact Sec19.Step1910Proof.commutator_mem_pCoreOf hL₁Y hL₁g (Ne.symm hne) (hKQL₁ hk)
        (hKQg hk')
    rw [hKQp] at hcomm
    have hK2 : IsPGroup 2 KQ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le hcomm
    have : Nontrivial KQ := (Subgroup.nontrivial_iff_ne_bot KQ).mpr
      (ne_bot_of_mem_oTwoComponentsIn hKQ)
    have : Group.IsPerfect KQ := isPerfect_of_mem_oTwoComponentsIn hKQ
    exact Group.IsPerfect.not_isNilpotent KQ hK2.isNilpotent
  have hO2H₁ : CFSG.Open.pCoreOf 2 H₁ ≠ ⊥ := by
    have hle : CFSG.Open.pCoreOf 2 KQ ≤ CFSG.Open.pCoreOf 2 H₁ := by
      have h1 := Rem187Bypass.pCoreOf_perfectResidual_le_of_le h1841 h hHQ hH₁ hHQH₁
      rw [hHQres] at h1
      exact h1.trans (pCoreOf_perfectResidual_le H₁)
    exact fun hb => hKQO (le_bot_iff.mp (hb ▸ hle))
  have hL₁eq := hres𝓕 H₁ hH₁𝓕
  have hcent : sectionCentralizer A L₁ (CFSG.Open.pCoreOf 2 L₁) = (Z : Set G) := by
    obtain ⟨-, c₁, hc₁3, hc₁⟩ := h1841 G A M h H₁ hH₁
    have hKQO₁ : CFSG.Open.pCoreOf 2 KQ ≤ CFSG.Open.pCoreOf 2 L₁ :=
      pCoreOf_le_pCoreOf_of_eq_sup hKQL₁ hL₁eq
    have hcmem : c ∈ sectionCentralizer A L₁ (CFSG.Open.pCoreOf 2 L₁) :=
      mem_sectionCentralizer_of_eq_sup hcA hKQL₁ hL₁eq
        (le_normalizer_inSubgroup_perfectResidual H₁ (hAH₁ hcA))
        fun y hy => hKQO₁ (hcSKQ.2 y hy)
    exact coe_zpowers_eq_of_mem hc₁ hc₁3 hcmem hc1
  exact ⟨H₁, c, ⟨h, hH₁, hcent⟩, hH₁max, hO2H₁, fun _ => hNZL₁⟩

theorem rem187Q_of_item4443
    (h4443 : Sec4.Item4_44_3)
    (h1812 : Item181_2) (h1841 : Item184_1) (h183K : Item183K) : Rem187Q :=
  rem187Q_of_alt1C h1812 h1841 (item182Alt1C_of h4443 h1812 h183K)

theorem rem187_of_item4443
    (h4443 : Sec4.Item4_44_3)
    (h1812 : Item181_2) (h1841 : Item184_1) (h183K : Item183K) : Rem187 :=
  rank3II_rem_18_7_of_item184 h1841 (rem187Q_of_item4443 h4443 h1812 h1841 h183K)

end CFSG.RankThree.PartTwo.Sec18
