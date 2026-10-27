module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Q8108
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1515A
public import CFSG.RankThree.PartOne.K159.Z
public import CFSG.GroupTheory.ElemAbelianRank
public import CFSG.GroupTheory.TwoWeightData
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm211Aux
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8YCfgAct
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointSetup
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.GammaQ108Final
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.TwoComponentSylowJoin
public import CFSG.LocalAnalysis.UniquenessCase.UC22S217U3A

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 TheoremCAt)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedFive)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne (IsSL3Four)

variable {G : Type} [Group G] [Finite G]

theorem le_of_commuting_elemAbelian_of_pRank_three_le
    {M Q Z : Subgroup G} (hQM : Q ≤ M)
    (hQrank : CFSG.Open.pRank 3 Q = 3) (hZP : Z ≤ M)
    (hZel : CFSG.Open.IsElemAbelian 3 Z) (hZne : Z ≠ ⊥)
    (hcomm : ∀ z ∈ Z, ∀ q ∈ Q, z * q = q * z)
    (hm3 : CFSG.Open.pRank 3 M ≤ 3) : Z ≤ Q := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let W : Subgroup G := CFSG.RankThree.PartOne.omegaOne 3 Q
  have hW_le_Q : W ≤ Q := CFSG.RankThree.PartOne.K159.omegaOne_le' 3 Q
  have hW_rank : CFSG.Open.pRank 3 W = 3 := by
    apply le_antisymm
    · exact (CFSG.SectionRank.pRank_mono (p := 3) (by norm_num : 1 < 3) hW_le_Q).trans_eq hQrank
    · obtain ⟨E, hEQ, hE, hEcard⟩ :=
        CFSG.SectionRank.exists_pRank (p := 3) (by norm_num : 1 < 3) Q
      have hEcard' : Nat.card E = 3 ^ 3 := by rw [hEcard, hQrank]
      have hE_le_W : E ≤ W := by
        intro x hx
        exact Subgroup.subset_closure ⟨hEQ hx, hE.2 x hx⟩
      exact CFSG.SectionRank.le_pRank (p := 3) (by norm_num : 1 < 3) hE_le_W hE hEcard'
  by_contra hZnotQ
  have hZnotW : ¬ Z ≤ W := fun h => hZnotQ (h.trans hW_le_Q)
  have hlt : Z ⊓ W < Z := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro h
    exact hZnotW (by rw [h.symm]; exact inf_le_right)
  have hZinf_el : CFSG.Open.IsElemAbelian 3 (Z ⊓ W) := hZel.mono inf_le_left
  have hcardZ : Nat.card ↥Z = 3 ^ CFSG.Open.pRank 3 Z :=
    CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_three hZel
  have hcardInf : Nat.card ↥(Z ⊓ W) = 3 ^ CFSG.Open.pRank 3 (Z ⊓ W) :=
    CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_three hZinf_el
  have hrank_le : CFSG.Open.pRank 3 (Z ⊓ W) ≤ CFSG.Open.pRank 3 Z :=
    CFSG.SectionRank.pRank_mono (p := 3) (by norm_num : 1 < 3) inf_le_left
  have hrank_lt : CFSG.Open.pRank 3 (Z ⊓ W) < CFSG.Open.pRank 3 Z := by
    rcases lt_or_eq_of_le hrank_le with h | h
    · exact h
    · exfalso
      apply hlt.ne
      apply Subgroup.eq_of_le_of_card_ge inf_le_left
      rw [hcardInf, hcardZ, h]
  have hZrank_pos : 0 < CFSG.Open.pRank 3 Z := by
    by_contra h
    have h0 : CFSG.Open.pRank 3 Z = 0 := by omega
    have hcard1 : Nat.card Z = 1 := by rw [hcardZ, h0]; simp
    exact hZne (Subgroup.eq_bot_of_card_eq Z hcard1)
  have hcommZW : ∀ z ∈ Z, ∀ w ∈ W, z * w = w * z :=
    fun z hz w hw => hcomm z hz w (hW_le_Q hw)
  have hrank_sum :=
    CFSG.LocalAnalysis.RankThreeUC.S15.pRank_add_le_pRank_sup_add_pRank_inf
      (A := Z) (B := W) hcommZW Nat.prime_three
  have hsup_rank : 4 ≤ CFSG.Open.pRank 3 (Z ⊔ W) := by omega
  have hsup_le_M : CFSG.Open.pRank 3 (Z ⊔ W) ≤ CFSG.Open.pRank 3 M :=
    CFSG.SectionRank.pRank_mono (p := 3) (by norm_num : 1 < 3)
      (sup_le hZP (hW_le_Q.trans hQM))
  omega

theorem normalizer_le_of_gammaQ
    {M Q P : Subgroup G}
    (hQM : Q ≤ M) (hQp : IsPGroup 3 Q) (hQrank : CFSG.Open.pRank 3 Q = 3)
    (hQP : Q ≤ P) (hP : CFSG.ABGLocalTools.IsSylowOf 3 P M)
    (hm3 : CFSG.Open.pRank 3 M ≤ 3)
    (hΓQ : CFSG.Open.rankThreeGamma 1 3 Q ≤ M) :
    Subgroup.normalizer (P : Set G) ≤ M := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPp : IsPGroup 3 P := hP.isPGroup
  have hPM : P ≤ M := hP.le
  obtain ⟨E₀, hE₀Q, hE₀el, hE₀card⟩ :=
    CFSG.SectionRank.exists_pRank (p := 3) (by norm_num : 1 < 3) Q
  have hE₀card' : Nat.card E₀ = 27 := by rw [hE₀card, hQrank]; norm_num
  have hP_card_ge : 27 ≤ Nat.card P :=
    hE₀card'.symm.trans_le (Subgroup.card_le_of_le (hE₀Q.trans hQP))
  have hP_ne_bot : P ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hP_card_ge
    omega
  haveI : Nontrivial ↥P :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let ZP : Subgroup G := (Subgroup.center P).map P.subtype
  let Z : Subgroup G := CFSG.RankThree.PartOne.omegaOne 3 ZP
  have hZP_le_P : ZP ≤ P := Subgroup.map_subtype_le _
  have hZ_le_ZP : Z ≤ ZP := CFSG.RankThree.PartOne.K159.omegaOne_le' 3 ZP
  have hZ_le_P : Z ≤ P := hZ_le_ZP.trans hZP_le_P
  have hZP_comm : ∀ x ∈ ZP, ∀ y ∈ ZP, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    exact congrArg (fun x : Subgroup.center P => ((x : ↥P) : G))
      (mul_comm' (⟨a, ha⟩ : Subgroup.center P) ⟨b, hb⟩)
  have hZ_comm : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x := by
    change ∀ x ∈ Subgroup.closure {x : G | x ∈ ZP ∧ x ^ 3 = 1},
      ∀ y ∈ Subgroup.closure {x : G | x ∈ ZP ∧ x ^ 3 = 1}, x * y = y * x
    exact CFSG.GroupTheory.TwoWeights.closure_comm (fun x hx y hy => hZP_comm x hx.1 y hy.1)
  have hZ_pow : ∀ x ∈ Z, x ^ 3 = 1 := by
    change ∀ x ∈ Subgroup.closure {x : G | x ∈ ZP ∧ x ^ 3 = 1}, x ^ 3 = 1
    exact CFSG.GroupTheory.TwoWeights.closure_pow_eq_one
      (fun x hx => hx.2) (fun x hx y hy => hZP_comm x hx.1 y hy.1)
  have hZ_elem : CFSG.Open.IsElemAbelian 3 Z :=
    ⟨⟨⟨fun a b => Subtype.ext (hZ_comm a a.2 b b.2)⟩⟩, hZ_pow⟩
  have hZP_pgroup : IsPGroup 3 ZP := hPp.to_le hZP_le_P
  have hZP_ne_bot : ZP ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card ZP = Nat.card (Subgroup.center P) :=
      Subgroup.card_map_of_injective P.subtype_injective
    have hcenter : Nontrivial (Subgroup.center P) := hPp.center_nontrivial
    have h1 : Nat.card ZP = 1 := by rw [hbot, Subgroup.card_bot]
    rw [hcard] at h1
    have hcenter_gt : 1 < Nat.card (Subgroup.center P) :=
      Finite.one_lt_card_iff_nontrivial.mpr hcenter
    omega
  have hZ_ne_bot : Z ≠ ⊥ := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hZP_pgroup
    have hcard_gt : 1 < Nat.card ZP := by
      by_contra hle
      have hcard1 : Nat.card ZP = 1 := by
        have hpos : 0 < Nat.card ZP := Nat.card_pos
        omega
      exact hZP_ne_bot (Subgroup.eq_bot_of_card_eq ZP hcard1)
    have hn_pos : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · rw [h0, pow_zero] at hn
        omega
      · exact hpos
    have h3dvd : 3 ∣ Nat.card ZP := by
      rw [hn]
      exact dvd_pow_self 3 (by omega)
    obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := ↥ZP) 3 h3dvd
    have hxmem : (x : G) ∈ Z := by
      refine Subgroup.subset_closure ⟨x.2, ?_⟩
      have hxpow : x ^ 3 = 1 := by rw [← hxord]; exact pow_orderOf_eq_one x
      exact congrArg Subtype.val hxpow
    have hxne : (x : G) ≠ 1 := by
      intro h1
      have hx1 : x = 1 := Subtype.ext h1
      rw [hx1, orderOf_one] at hxord
      norm_num at hxord
    intro hbot
    rw [hbot] at hxmem
    exact hxne (Subgroup.mem_bot.mp hxmem)
  have hZP_central : ∀ z ∈ ZP, ∀ p ∈ P, z * p = p * z := by
    intro z hz p hp
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hz
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp ha ⟨p, hp⟩)).symm
  have hZ_central_Q : ∀ z ∈ Z, ∀ q ∈ Q, z * q = q * z :=
    fun z hz q hq => hZP_central z (hZ_le_ZP hz) q ((hQP hq))
  have hZ_le_Q : Z ≤ Q :=
    le_of_commuting_elemAbelian_of_pRank_three_le hQM hQrank
      (hZ_le_P.trans hPM) hZ_elem hZ_ne_bot hZ_central_Q hm3
  have hNP_le_NZP : Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (ZP : Set G) :=
    CFSG.SignalizerFunctorTheorem.McBride.Near.Thm211.normalizer_le_normalizer_map_subtype
      (Y := P) (Subgroup.center P)
  have hNZP_le_NZ : Subgroup.normalizer (ZP : Set G) ≤ Subgroup.normalizer (Z : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hg ⊢
    have hmap := CFSG.RankThree.PartOne.K159.omegaOne_map_of_injective'
      (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective 3 ZP
    have hmap' : Z = Z.map (MulAut.conj g).toMonoidHom := by
      simpa [hg] using hmap
    exact hmap'.symm
  have hNP_le_NZ : Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (Z : Set G) :=
    hNP_le_NZP.trans hNZP_le_NZ
  have hZrank_pos : 1 ≤ CFSG.Open.pRank 3 Z := by
    exact Nat.succ_le_of_lt (by
      by_contra h
      have h0 : CFSG.Open.pRank 3 Z = 0 := by omega
      have hcardZ : Nat.card ↥Z = 3 ^ CFSG.Open.pRank 3 Z :=
        CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_three hZ_elem
      have hcard1 : Nat.card Z = 1 := by rw [hcardZ, h0]; simp
      exact hZ_ne_bot (Subgroup.eq_bot_of_card_eq Z hcard1))
  have hNZ_le_M : Subgroup.normalizer (Z : Set G) ≤ M := by
    have hΓ : CFSG.Open.GLBCore 3 1 Q ≤ M := by
      simpa [CFSG.Open.rankThreeGamma] using hΓQ
    exact (CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore
      (p := 3) (k := 1) hZ_le_Q hZrank_pos).trans hΓ
  exact hNP_le_NZ.trans hNZ_le_M

theorem q8108_explicit
    (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hC : CFSG.Yardstones.Mf4cdcdf2e013.TheoremCAt S.M)
    (hnot : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 S.M)
    (hSE : StronglyEmbeddedFive)
    {L L' : Subgroup G} (hL : L ∈ calC S.M)
    (hset : conjSetOf S.M L = {L, L'}) (hLL' : L' ≠ L)
    (hSL : IsSL3Four (Bar2 L))
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P S.M) :
    let Q := (P ⊓ L) ⊔ (P ⊓ L')
    Q ≤ conjClosure S.M L ∧ Q ≤ P ∧ IsPGroup 3 Q ∧ (∀ x ∈ Q, x ^ 3 = 1) ∧
      CFSG.IsExtraspecial 3 Q ∧ Nat.card Q = 3 ^ 5 ∧
      CFSG.Open.pRank 3 Q = 3 ∧
      (∀ x ∈ Q, x ≠ 1 → ∃ E : Subgroup G, x ∈ E ∧ E ≤ Q ∧
        CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9) ∧
      CFSG.Open.rankThreeGamma 1 3 Q ≤ S.M := by
  dsimp only
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hL'conj : L' ∈ conjSetOf S.M L := by
    rw [hset]
    simp
  have hL'calC : L' ∈ calC S.M := by
    obtain ⟨g, hgM, hL'map⟩ := hL'conj
    rw [hL'map]
    exact CFSG.LocalAnalysis.UniquenessCase.UC6S846.calC_map S.M (MulAut.conj g)
      (CFSG.LocalAnalysis.UniquenessCase.UC6S846.mem_normalizer_iff_map_conj.1
        (Subgroup.le_normalizer hgM)) hL
  have hSL' : IsSL3Four (Bar2 L') := by
    obtain ⟨g, -, hL'map⟩ := hL'conj
    obtain ⟨eBar⟩ := uc22p20d_bar2_conj g L
    have hL'map' : L' = uc22p20bCj g L := by
      simpa [uc22p20bCj] using hL'map
    have e : Bar2 L ≃* Bar2 L' := by
      rw [hL'map']
      exact eBar
    exact isSL3Four_of_mulEquiv e hSL
  set R : Subgroup G := P ⊓ L with hRdef
  set R' : Subgroup G := P ⊓ L' with hR'def
  have hLM : L ≤ S.M := hL.1.le
  have hL'M : L' ≤ S.M := hL'calC.1.le
  have hR_sylow : CFSG.ABGLocalTools.IsSylowOf 3 R L := by
    rw [hRdef]
    exact CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.YCfg.isSylowOf_inf_of_subnormalIn
      hP hLM hL.1.subgroupOf
  have hR'_sylow : CFSG.ABGLocalTools.IsSylowOf 3 R' L' := by
    rw [hR'def]
    exact CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.YCfg.isSylowOf_inf_of_subnormalIn
      hP hL'M hL'calC.1.subgroupOf
  set A : Subgroup (Bar2 S.M) := barImage S.M L with hAdef
  set B : Subgroup (Bar2 S.M) := barImage S.M L' with hBdef
  set PA : Subgroup (Bar2 S.M) := barImage S.M R with hPAdef
  set PB : Subgroup (Bar2 S.M) := barImage S.M R' with hPBdef
  obtain ⟨eA, -⟩ := uc22p22l_barImage_equiv (L := S.M) (K := L) hL
  obtain ⟨eB, -⟩ := uc22p22l_barImage_equiv (L := S.M) (K := L') hL'calC
  have hSL_A : IsSL3Four ↥A := isSL3Four_of_mulEquiv eA hSL
  have hSL_B : IsSL3Four ↥B := isSL3Four_of_mulEquiv eB hSL'
  have hPA_sylow : CFSG.ABGLocalTools.IsSylowOf 3 PA A := by
    rw [hPAdef, hAdef]
    exact isSylowOf_barImage_of_isSylowOf hLM hR_sylow eA
  have hPB_sylow : CFSG.ABGLocalTools.IsSylowOf 3 PB B := by
    rw [hPBdef, hBdef]
    exact isSylowOf_barImage_of_isSylowOf hL'M hR'_sylow eB
  have hPA_le : PA ≤ A := hPA_sylow.le
  have hPB_le : PB ≤ B := hPB_sylow.le
  have hPA_abs : CFSG.ABGLocalTools.IsSylowOf 3 (PA.subgroupOf A) ⊤ := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (p := 3) A
      (A := PA.subgroupOf A) (B := ⊤)]
    simpa [Subgroup.subgroupOf_map_subtype, Subgroup.map_top, Subgroup.range_subtype,
      inf_eq_left.mpr hPA_le] using hPA_sylow
  have hPB_abs : CFSG.ABGLocalTools.IsSylowOf 3 (PB.subgroupOf B) ⊤ := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (p := 3) B
      (A := PB.subgroupOf B) (B := ⊤)]
    simpa [Subgroup.subgroupOf_map_subtype, Subgroup.map_top, Subgroup.range_subtype,
      inf_eq_left.mpr hPB_le] using hPB_sylow
  obtain ⟨hPA_ext, hPA_card⟩ :=
    isExtraspecial_sylow_three_of_isSL3Four_of_certificates hSL_A hPA_abs
  obtain ⟨hPB_ext, hPB_card⟩ :=
    isExtraspecial_sylow_three_of_isSL3Four_of_certificates hSL_B hPB_abs
  have hPAexp_abs : ∀ x : PA.subgroupOf A, x ^ 3 = 1 :=
    pow_three_of_isSL3Four_sylow hSL_A hPA_abs
  have hPBexp_abs : ∀ x : PB.subgroupOf B, x ^ 3 = 1 :=
    pow_three_of_isSL3Four_sylow hSL_B hPB_abs
  have hPAexp : ∀ x : PA, x ^ 3 = 1 := by
    intro x
    have h := hPAexp_abs ((Subgroup.subgroupOfEquivOfLe hPA_le).symm x)
    have h' := congrArg (Subgroup.subgroupOfEquivOfLe hPA_le) h
    simpa using h'
  have hPBexp : ∀ x : PB, x ^ 3 = 1 := by
    intro x
    have h := hPBexp_abs ((Subgroup.subgroupOfEquivOfLe hPB_le).symm x)
    have h' := congrArg (Subgroup.subgroupOfEquivOfLe hPB_le) h
    simpa using h'
  have hPA_ext' : CFSG.IsExtraspecial 3 ↥PA := by
    haveI : CFSG.IsExtraspecial 3 ↥(PA.subgroupOf A) := hPA_ext
    exact CFSG.LocalAnalysis.WeakClosure81.isExtraspecial_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hPA_le).symm
  set Q : Subgroup G := R ⊔ R' with hQdef
  have hRP : R ≤ P := by rw [hRdef]; exact inf_le_left
  have hR'P : R' ≤ P := by rw [hR'def]; exact inf_le_left
  have hRL : R ≤ L := by rw [hRdef]; exact inf_le_right
  have hR'L' : R' ≤ L' := by rw [hR'def]; exact inf_le_right
  have hLX : L ≤ conjClosure S.M L :=
    uc22s217u3a_le_conjClosure ⟨1, S.M.one_mem, by ext; simp⟩
  have hL'X : L' ≤ conjClosure S.M L := uc22s217u3a_le_conjClosure hL'conj
  have hQX : Q ≤ conjClosure S.M L := by
    rw [hQdef]
    exact sup_le (hRL.trans hLX) (hR'L'.trans hL'X)
  have hQM : Q ≤ S.M := by
    rw [hQdef]
    exact sup_le (hRP.trans hP.le) (hR'P.trans hP.le)
  have hQp : IsPGroup 3 Q := by
    rw [hQdef]
    exact hP.isPGroup.to_le (sup_le hRP hR'P)
  have hdata : CFSG.IsExtraspecial 3 Q ∧ (∀ x : Q, x ^ 3 = 1) ∧
      Nat.card Q = 3 ^ 5 ∧ CFSG.Open.pRank 3 Q = 3 := by
    by_cases hne : L = L'
    · exact (hLL' hne.symm).elim
    ·
      have hAB : A ≠ B := by
        intro h
        apply hne
        apply uc22p22u_calC_ext hL hL'calC
        calc barImage S.M L = A := hAdef.symm
          _ = B := h
          _ = barImage S.M L' := hBdef
      have hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a :=
        fun a ha b hb => uc22p22l_barImage_commute hL hL'calC hne a ha b hb
      have hZA : A ⊓ B ≤ (Subgroup.center ↥A).map A.subtype := by
        rintro x ⟨hxA, hxB⟩
        refine Subgroup.mem_map.mpr ⟨⟨x, hxA⟩, ?_, rfl⟩
        rw [Subgroup.mem_center_iff]
        intro a
        apply Subtype.ext
        exact hcomm a a.2 x hxB
      have hZB : A ⊓ B ≤ (Subgroup.center ↥B).map B.subtype := by
        rintro x ⟨hxA, hxB⟩
        refine Subgroup.mem_map.mpr ⟨⟨x, hxB⟩, ?_, rfl⟩
        rw [Subgroup.mem_center_iff]
        intro b
        apply Subtype.ext
        exact (hcomm x hxA b b.2).symm
      have hrank : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 S.M)) ≤ 3 := by
        rw [pRank_bar2_eq_of_odd (Y := S.M) Nat.prime_three (by norm_num : (3 : ℕ) ≠ 2)]
        exact pRank_three_le_three_of_not_strong hS hU S hMS hnot
      obtain ⟨hQbar_ext_raw, hQbar_card_raw, hQbar_rank_raw⟩ :=
        isExtraspecial_sup_of_two_SL3Four_sylow (Y := Bar2 S.M)
          hSL_A hSL_B hAB hcomm hZA hZB hrank hPA_sylow hPB_sylow
      set Qbar : Subgroup (Bar2 S.M) := PA ⊔ PB with hQbardef
      have hQbar_ext : CFSG.IsExtraspecial 3 ↥Qbar := by
        rw [hQbardef]
        exact hQbar_ext_raw
      have hQbar_card : Nat.card ↥Qbar = 3 ^ 5 := by
        rw [hQbardef]
        exact hQbar_card_raw
      have hcommPAPB : ∀ a ∈ PA, ∀ b ∈ PB, a * b = b * a :=
        fun a ha b hb => hcomm a (hPA_le ha) b (hPB_le hb)
      have hQbar_exp : Monoid.exponent ↥Qbar = 3 := by
        rw [hQbardef]
        exact exponent_sup_eq_three hcommPAPB hPAexp hPBexp hQbar_card_raw
      have hbarQ_eq : barImage S.M Q = Qbar := by
        rw [hQdef, hQbardef, hPAdef, hPBdef]
        show barImage S.M (R ⊔ R') = barImage S.M R ⊔ barImage S.M R'
        simp only [barImage, Subgroup.subgroupOf_sup (hRP.trans hP.le) (hR'P.trans hP.le),
          Subgroup.map_sup]
      have hQ_iso : ↥Q ≃* ↥Qbar :=
        (equiv_barImage_of_isPGroup hQM hQp).trans (MulEquiv.subgroupCongr hbarQ_eq)
      have hQ_ext : CFSG.IsExtraspecial 3 Q := by
        haveI : CFSG.IsExtraspecial 3 ↥Qbar := hQbar_ext
        exact CFSG.LocalAnalysis.WeakClosure81.isExtraspecial_of_mulEquiv hQ_iso
      have hQ_exp : ∀ x : Q, x ^ 3 = 1 := by
        intro x
        have hx : (hQ_iso x) ^ 3 = 1 := by
          rw [← hQbar_exp]
          exact Monoid.pow_exponent_eq_one _
        exact hQ_iso.injective (by simpa [map_pow] using hx)
      have hQcard : Nat.card Q = 3 ^ 5 := by
        rw [← hQbar_card]
        exact Nat.card_congr hQ_iso.toEquiv
      have hQbar_rank : CFSG.Open.pRank 3 Qbar = 3 := by
        rw [hQbardef]
        exact hQbar_rank_raw
      have hQrank : CFSG.Open.pRank 3 Q = 3 := by
        rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup Q,
          CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num : 1 < 3) hQ_iso,
          ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup Qbar]
        exact hQbar_rank
      exact ⟨hQ_ext, hQ_exp, hQcard, hQrank⟩
  obtain ⟨hQ_ext, hQ_exp, hQcard, hQrank⟩ := hdata
  have hQexp_pt : ∀ x ∈ Q, x ^ 3 = 1 := fun x hx =>
    by simpa using congrArg Subtype.val (hQ_exp ⟨x, hx⟩)
  have hE9contain : ∀ x ∈ Q, x ≠ 1 → ∃ E : Subgroup G, x ∈ E ∧ E ≤ Q ∧
      CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
    intro x hx _
    exact exists_elemAbelian_nine_of_isExtraspecial_of_pow_three hQ_ext hQ_exp hx
  have hQP : Q ≤ P := by
    rw [hQdef]
    exact sup_le hRP hR'P
  have hΓQ : CFSG.Open.rankThreeGamma 1 3 Q ≤ S.M :=
    rankThreeGamma_Q_le_of_le_X (hS := hS) (hU := hU) (S := S) (hMS := hMS)
      (hC := hC) (hnot := hnot) (hSE := hSE) (hL := hL) (hset := hset)
      (hSL := hSL) (hQX := hQX) (hQp := hQp) (hQexp := hQexp_pt)
      (hE9contain := hE9contain)
  exact ⟨hQX, hQP, hQp, hQexp_pt, hQ_ext, hQcard, hQrank, hE9contain, hΓQ⟩



theorem normalizer_sylow_le_8108
    (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hC : CFSG.Yardstones.Mf4cdcdf2e013.TheoremCAt S.M)
    (hnot : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 S.M)
    (hSE : StronglyEmbeddedFive)
    {L L' : Subgroup G} (hL : L ∈ calC S.M)
    (hset : conjSetOf S.M L = {L, L'}) (hLL' : L' ≠ L)
    (hSL : IsSL3Four (Bar2 L))
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P S.M) :
    Subgroup.normalizer (P : Set G) ≤ S.M := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfacts := q8108_explicit hS hU S hMS hC hnot hSE hL hset hLL' hSL hP
  dsimp only at hfacts
  obtain ⟨-, hQP, hQp, -, -, -, hQrank, -, hΓQ⟩ := hfacts
  have hQM : (P ⊓ L) ⊔ (P ⊓ L') ≤ S.M := hQP.trans hP.le
  have hm3 : CFSG.Open.pRank 3 S.M ≤ 3 :=
    pRank_three_le_three_of_not_strong hS hU S hMS hnot
  exact normalizer_le_of_gammaQ hQM hQp hQrank hQP hP hm3 hΓQ

theorem q8108_singleton_pRank
    (S : Setup4 G) {L L' : Subgroup G} (hL : L ∈ calC S.M)
    (hLL : L' = L) (hSL : IsSL3Four (Bar2 L))
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P S.M) :
    CFSG.Open.pRank 3 ((P ⊓ L) ⊔ (P ⊓ L')) = 2 := by
  have hR_sylow : CFSG.ABGLocalTools.IsSylowOf 3 (P ⊓ L) L :=
    CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.YCfg.isSylowOf_inf_of_subnormalIn
      hP hL.1.le hL.1.subgroupOf
  have hQeq : (P ⊓ L) ⊔ (P ⊓ L') = P ⊓ L := by rw [hLL, sup_idem]
  rw [hQeq]
  exact (CFSG.LocalAnalysis.RankFourTheoremC.pRank_eq_of_isSylowOf
    Nat.prime_three hR_sylow).trans
    (pRank_three_eq_two_of_mem_calC_of_isSL3Four hL hSL)

theorem q8108_singleton_card
    (S : Setup4 G) {L L' : Subgroup G} (hL : L ∈ calC S.M)
    (hLL : L' = L) (hSL : IsSL3Four (Bar2 L))
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P S.M) :
    Nat.card ↥((P ⊓ L) ⊔ (P ⊓ L')) = 27 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLM : L ≤ S.M := hL.1.le
  have hR_sylow : CFSG.ABGLocalTools.IsSylowOf 3 (P ⊓ L) L :=
    CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.YCfg.isSylowOf_inf_of_subnormalIn
      hP hLM hL.1.subgroupOf
  have hQeq : (P ⊓ L) ⊔ (P ⊓ L') = P ⊓ L := by rw [hLL, sup_idem]
  set A : Subgroup (Bar2 S.M) := barImage S.M L with hAdef
  set PA : Subgroup (Bar2 S.M) := barImage S.M (P ⊓ L) with hPAdef
  obtain ⟨eA, -⟩ := uc22p22l_barImage_equiv (L := S.M) (K := L) hL
  have hSL_A : IsSL3Four ↥A := isSL3Four_of_mulEquiv eA hSL
  have hPA_sylow : CFSG.ABGLocalTools.IsSylowOf 3 PA A := by
    rw [hPAdef, hAdef]
    exact isSylowOf_barImage_of_isSylowOf hLM hR_sylow eA
  have hPA_abs : CFSG.ABGLocalTools.IsSylowOf 3 (PA.subgroupOf A) ⊤ := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (p := 3) A
      (A := PA.subgroupOf A) (B := ⊤)]
    simpa [Subgroup.subgroupOf_map_subtype, Subgroup.map_top, Subgroup.range_subtype,
      inf_eq_left.mpr hPA_sylow.le] using hPA_sylow
  obtain ⟨-, hPA_card_abs⟩ :=
    isExtraspecial_sylow_three_of_isSL3Four_of_certificates hSL_A hPA_abs
  have hPA_card : Nat.card PA = 27 := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPA_sylow.le).toEquiv]
    exact hPA_card_abs
  have eR : ↥(P ⊓ L) ≃* ↥PA := by
    rw [hPAdef]
    exact equiv_barImage_of_isPGroup (M := S.M) (Q := P ⊓ L)
      (hR_sylow.le.trans hLM) hR_sylow.isPGroup
  rw [hQeq]
  exact (Nat.card_congr eR.toEquiv).trans hPA_card

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
