module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.CoreSlices
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.CoreFacts
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.CoreBasic
import CFSG.GroupTheory.PGroup.LtInfNormalizer
import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
import CFSG.LocalAnalysis.UniquenessCase.UC6S19
import CFSG.LocalAnalysis.EvenBN.GMSK.QuasiCentreLayerDatum
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.HardMathSupport.Dickson.Sec6.I1431SporAux.RuNo65
import CFSG.GH74.KGroups.Sz8
import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
import CFSG.Quasithin.EmptyFaithful.S1422Basic
import CFSG.Sporadic.HNSchreier.Algebra

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ABGLocalTools (IsSylowOf)

namespace CoreSetup

variable {X : Type} [Group X] [Finite X] {K L T Y : Subgroup X}

private lemma twentyfive_dvd_sylow (hcardK : Nat.card ↥K = 145926144000)
    (R : Sylow 5 ↥K) : 25 ∣ Nat.card (R : Subgroup ↥K) := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h25K : 25 ∣ Nat.card ↥K := by rw [hcardK]; norm_num
  have h5idx : ¬ 5 ∣ (R : Subgroup ↥K).index := R.not_dvd_index
  have hcop : Nat.Coprime 25 (R : Subgroup ↥K).index := by
    simpa using
      (Nat.prime_five.coprime_pow_of_not_dvd (m := 2) (a := (R : Subgroup ↥K).index) h5idx).symm
  have h25R : 25 ∣ Nat.card (R : Subgroup ↥K) * (R : Subgroup ↥K).index := by
    rw [Subgroup.card_mul_index]
    exact h25K
  exact hcop.dvd_of_dvd_mul_right h25R

private lemma qcConjAut_pow_coe {H : Type} [Group H] {Y : Subgroup H} {a : H}
    (ha : a ∈ Subgroup.normalizer (Y : Set H)) (m : ℕ) (z : ↥Y) :
    (↑(((CFSG.LocalAnalysis.EvenBN.GMSK.qcConjAut Y ha) ^ m) z) : H) =
      a ^ m * (↑z : H) * (a ^ m)⁻¹ := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ']
      change Subgroup.subtype Y
        ((CFSG.LocalAnalysis.EvenBN.GMSK.qcConjAut Y ha)
          (((CFSG.LocalAnalysis.EvenBN.GMSK.qcConjAut Y ha) ^ m) z)) = _
      rw [show Subgroup.subtype Y
        ((CFSG.LocalAnalysis.EvenBN.GMSK.qcConjAut Y ha)
          (((CFSG.LocalAnalysis.EvenBN.GMSK.qcConjAut Y ha) ^ m) z)) =
          a * Subgroup.subtype Y
            (((CFSG.LocalAnalysis.EvenBN.GMSK.qcConjAut Y ha) ^ m) z) * a⁻¹
          from CFSG.LocalAnalysis.EvenBN.GMSK.qcConjAut_apply_coe Y ha _]
      change a * (↑(((CFSG.LocalAnalysis.EvenBN.GMSK.qcConjAut Y ha) ^ m) z) : H) * a⁻¹ =
        a ^ (m + 1) * (↑z : H) * (a ^ (m + 1))⁻¹
      rw [ih, pow_succ]
      group

theorem false_of_mulEquiv_ru
    (h : CoreSetup X K L T Y 3) (eRu : ↥K ≃* CFSG.Blueprint.NativeSporadic.Ru) : False := by
  classical
  have hcardK : Nat.card ↥K = 145926144000 :=
    (Nat.card_congr eRu.toEquiv).trans CFSG.Sporadic.Ru.card_Ru
  have hcardBar : Nat.card (Bar2 L) = 29120 := by
    have hc := CFSG.LocalAnalysis.EvenBN.GMSK.card_of_lieModel_twistedB2 (X := Bar2 L) (n := 3) h.sz
    norm_num at hc ⊢
    exact hc
  have h5L : 5 ∣ Nat.card L := by
    have h5bar : 5 ∣ Nat.card (Bar2 L) := by rw [hcardBar]; norm_num
    exact h5bar.trans (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥L))
  have h13L : 13 ∣ Nat.card L := by
    have h13bar : 13 ∣ Nat.card (Bar2 L) := by rw [hcardBar]; norm_num
    exact h13bar.trans (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥L))
  obtain ⟨A, hAL, hAcard⟩ := exists_card_eq_five_le h.sz
  have hAprime : (Nat.card A).Prime := by rw [hAcard]; norm_num
  have hA2 : Nat.card A ≠ 2 := by rw [hAcard]; norm_num
  have hAnormL : normalizer (A : Set X) ≤ normalizer (L : Set X) :=
    h.normalizer_le_normalizer hAL hAprime hA2
  have hAK : A ≤ K := hAL.trans h.le
  let A' : Subgroup ↥K := A.subgroupOf K
  have hA'card : Nat.card ↥A' = 5 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv, hAcard]
  have hA'p : IsPGroup 5 ↥A' := IsPGroup.of_card (n := 1) (by rw [hA'card]; norm_num)
  obtain ⟨R, hA'R⟩ := hA'p.exists_le_sylow
  let RX : Subgroup X := (R : Subgroup ↥K).map K.subtype
  have hRXcard : Nat.card RX = Nat.card (R : Subgroup ↥K) :=
    Subgroup.card_map_of_injective K.subtype_injective
  have hRXp : IsPGroup 5 RX := R.isPGroup'.map K.subtype
  have hA_le_RX : A ≤ RX := by
    intro a ha
    have ha' : (⟨a, hAK ha⟩ : ↥K) ∈ A' := by
      change ((⟨a, hAK ha⟩ : ↥K) : X) ∈ A
      exact ha
    exact Subgroup.mem_map.mpr ⟨⟨a, hAK ha⟩, hA'R ha', rfl⟩
  have h25R : 25 ∣ Nat.card (R : Subgroup ↥K) := twentyfive_dvd_sylow hcardK R
  have h25RX : 25 ∣ Nat.card RX := by rw [hRXcard]; exact h25R
  have hA_lt_RX : A < RX := by
    refine lt_of_le_of_ne hA_le_RX ?_
    intro heq
    have hcardeq : Nat.card A = Nat.card RX := by rw [heq]
    obtain ⟨k, hk⟩ := h25RX
    rw [hAcard] at hcardeq
    omega
  let D : Subgroup X := RX ⊓ normalizer (A : Set X)
  have hD5 : IsPGroup 5 D := hRXp.to_inf_left
  have hA_lt_D : A < D :=
    CFSG.GroupTheory.lt_inf_normalizer_of_isPGroup (p := 5) hRXp hA_lt_RX
  have hD_le_NL : D ≤ normalizer (L : Set X) := inf_le_right.trans hAnormL
  have hDgt : 5 < Nat.card D := by
    have hlt := Subgroup.card_lt_of_lt hA_lt_D
    rwa [hAcard] at hlt
  obtain ⟨dExp, hDcard⟩ := (IsPGroup.iff_card (p := 5) (G := ↥D)).mp hD5
  have hDge : 25 ≤ Nat.card D := by
    rw [hDcard]
    have h5lt : 5 < 5 ^ dExp := by rwa [← hDcard]
    have hdExp2 : 2 ≤ dExp := by
      rcases dExp with _ | _ | dExp
      · norm_num at h5lt
      · norm_num at h5lt
      · omega
    calc 25 = 5 ^ 2 := by norm_num
      _ ≤ 5 ^ dExp := Nat.pow_le_pow_right (by norm_num) hdExp2
  let φ : ↥D →* MulAut (Bar2 L) :=
    (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL L).comp (Subgroup.inclusion hD_le_NL)
  have hD_dvd_5 : Nat.card φ.range ∣ 5 ^ dExp := by
    refine ⟨Nat.card φ.ker, ?_⟩
    rw [mul_comm]
    exact hDcard.symm.trans (Subgroup.card_ker_mul_card_range φ).symm
  have hrange_le5 : Nat.card φ.range ≤ 5 := by
    obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_five).mp hD_dvd_5
    have hj1 : j ≤ 1 := by
      by_contra hcon
      have h2 : 2 ≤ j := by omega
      have h25dvd : 25 ∣ Nat.card φ.range := by
        rw [hjeq]
        have hpow : 5 ^ 2 ∣ 5 ^ j := pow_dvd_pow 5 h2
        simpa using hpow
      have h25_87360 : 25 ∣ 87360 := h25dvd.trans (by
        obtain ⟨eSz⟩ := CFSG.GH74.KGroups.Sz8.equiv_of_lieModel h.sz
        have hcardAut : Nat.card (MulAut (Bar2 L)) = 87360 :=
          CFSG.GH74.KGroups.Sz8.card_mulAut eSz
        have h := Subgroup.card_subgroup_dvd_card φ.range
        rwa [hcardAut] at h)
      norm_num at h25_87360
    calc Nat.card φ.range = 5 ^ j := hjeq
      _ ≤ 5 ^ 1 := Nat.pow_le_pow_right (by norm_num) hj1
      _ = 5 := by norm_num
  have hker_ge : 5 ≤ Nat.card φ.ker := by
    have hmul := Subgroup.card_ker_mul_card_range φ
    have hpos : 0 < Nat.card φ.range := Nat.card_pos
    nlinarith
  have hker_dvd_5 : Nat.card φ.ker ∣ 5 ^ dExp := by
    refine ⟨Nat.card φ.range, ?_⟩
    have hmul := Subgroup.card_ker_mul_card_range φ
    exact hDcard.symm.trans hmul.symm
  obtain ⟨mExp, hmExp, hkereq⟩ := (Nat.dvd_prime_pow Nat.prime_five).mp hker_dvd_5
  have hmExp1 : 1 ≤ mExp := by
    rcases Nat.eq_zero_or_pos mExp with h0 | hpos
    · rw [h0, pow_zero] at hkereq
      omega
    · exact hpos
  have h5ker : 5 ∣ Nat.card φ.ker := by
    rw [hkereq]
    exact dvd_pow_self 5 (by omega)
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨c₀, hc₀order⟩ := exists_prime_orderOf_dvd_card' (G := ↥φ.ker) 5 h5ker
  let c : X := ((c₀ : ↥D) : X)
  have hcD : c ∈ D := (c₀ : ↥D).2
  have hcorder : orderOf c = 5 := by
    dsimp only [c]
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hc₀order]
  have hφc : φ ⟨c, hcD⟩ = 1 := by
    have hmem : φ (c₀ : ↥D) = 1 := MonoidHom.mem_ker.mp c₀.2
    exact hmem
  have hfix : ∀ x : ↥L, c * (x : X) * c⁻¹ * (x : X)⁻¹ ∈ CFSG.Open.pCoreOf 2 L := by
    intro x
    have harg : (Subgroup.inclusion hD_le_NL) ⟨c, hcD⟩ = ⟨c, hD_le_NL hcD⟩ := by
      apply Subtype.ext
      rw [Subgroup.coe_inclusion]
    have hρ : CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL L
        ⟨c, hD_le_NL hcD⟩ = 1 := by
      have h := hφc
      dsimp only [φ] at h
      rw [← harg]
      exact h
    have hcomm := (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL_fix_iff L
      ⟨c, hD_le_NL hcD⟩ x).mp (by rw [hρ]; rfl)
    simpa using hcomm
  let : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  obtain ⟨y₀, hy₀order⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 13 h13L
  let y : X := (y₀ : X)
  have hyL : y ∈ L := y₀.2
  have hyorder : orderOf y = 13 := by
    dsimp only [y]
    rw [Subgroup.orderOf_coe, hy₀order]
  let Y13 : Subgroup X := Subgroup.zpowers y
  have hYcard : Nat.card Y13 = 13 := by
    dsimp only [Y13]
    rw [Nat.card_zpowers, hyorder]
  have hYleL : Y13 ≤ L := by
    rw [Subgroup.zpowers_le]
    exact hyL
  let O : Subgroup X := CFSG.Open.pCoreOf 2 L
  have hOleL : O ≤ L := Subgroup.map_subtype_le _
  have hO2 : IsPGroup 2 ↥O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  obtain ⟨oExp, hOcard⟩ := (IsPGroup.iff_card (p := 2) (G := ↥O)).mp hO2
  have hL_le_NO : L ≤ normalizer (O : Set X) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
  have hY_le_NO : Y13 ≤ normalizer (O : Set X) := hYleL.trans hL_le_NO
  let P : Subgroup X := O ⊔ Y13
  have hPleL : P ≤ L := sup_le hOleL hYleL
  have hYleP : Y13 ≤ P := le_sup_right
  have hOleP : O ≤ P := le_sup_left
  have hinf : Y13 ⊓ O = ⊥ := by
    have hdvd13 : Nat.card ↥(Y13 ⊓ O) ∣ 13 := by
      simpa [hYcard] using Subgroup.card_dvd_of_le (inf_le_left : Y13 ⊓ O ≤ Y13)
    have hdvdO : Nat.card ↥(Y13 ⊓ O) ∣ Nat.card O :=
      Subgroup.card_dvd_of_le inf_le_right
    rw [hOcard] at hdvdO
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 13)).mp hdvd13 with h1 | h13
    · exact (Subgroup.card_eq_one).mp h1
    · exfalso
      rw [h13] at hdvdO
      have h132 : 13 ∣ 2 := (by norm_num : Nat.Prime 13).dvd_of_dvd_pow hdvdO
      norm_num at h132
  have hcardP : Nat.card P = 13 * Nat.card O := by
    have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := Y13) (K := O) hY_le_NO
    have h' : Nat.card ↥(Y13 ⊔ O) = 13 * Nat.card O := by
      simpa [hinf, hYcard] using h
    dsimp only [P]
    rw [sup_comm]
    exact h'
  have hY_syl : IsSylowOf 13 Y13 P := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨hYleP, ?_, ?_⟩
    · exact IsPGroup.of_card (n := 1) (by rw [hYcard]; norm_num)
    · intro hdvd
      have hrel := Subgroup.relIndex_mul_card Y13 P
      rw [inf_eq_left.mpr hYleP, hYcard, hcardP] at hrel
      have hrel' : Y13.relIndex P = Nat.card O := by omega
      rw [hrel'] at hdvd
      rw [hOcard] at hdvd
      have h132 : 13 ∣ 2 := (by norm_num : Nat.Prime 13).dvd_of_dvd_pow hdvd
      norm_num at h132
  have hcNO : c ∈ normalizer (O : Set X) :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.normalizer_le_normalizer_pCoreOf L
      (hD_le_NL hcD)
  have hcyO : c * y * c⁻¹ * y⁻¹ ∈ O := hfix ⟨y, hyL⟩
  have hcy : c * y * c⁻¹ ∈ P := by
    have h1 : c * y * c⁻¹ = (c * y * c⁻¹ * y⁻¹) * y := by group
    rw [h1]
    exact P.mul_mem (hOleP hcyO) (hYleP (Subgroup.mem_zpowers y))
  let γ : MulAut X := MulAut.conj c
  have hγO : Subgroup.map γ.toMonoidHom O = O := by
    have h := (Subgroup.mem_normalizer_iff_map_conj_eq).mp hcNO
    simpa [γ] using h
  have hγY : Subgroup.map γ.toMonoidHom Y13 = Subgroup.zpowers (γ y) := by
    dsimp only [Y13]
    rw [MonoidHom.map_zpowers]
    rfl
  have hγy : γ y = c * y * c⁻¹ := by
    dsimp only [γ]
    rw [MulAut.conj_apply]
  have hmapP_le : Subgroup.map γ.toMonoidHom P ≤ P := by
    dsimp only [P]
    rw [Subgroup.map_sup, hγO, hγY, hγy]
    exact sup_le hOleP (Subgroup.zpowers_le.mpr hcy)
  have hγP : Subgroup.map γ.toMonoidHom P = P := by
    refine Subgroup.eq_of_le_of_card_ge hmapP_le ?_
    have hcardmap : Nat.card ↥(Subgroup.map γ.toMonoidHom P) = Nat.card P :=
      Subgroup.card_map_of_injective γ.injective (K := P)
    rw [hcardmap]
  have hcNP : c ∈ normalizer (P : Set X) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    simpa [γ] using hγP
  let H : Subgroup X := Subgroup.zpowers c ⊔ P
  have hcH : c ∈ H := Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
  have hPleH : P ≤ H := le_sup_right
  have hHleK : H ≤ K := by
    refine sup_le ?_ (hPleL.trans h.le)
    rw [Subgroup.zpowers_le]
    exact Subgroup.map_subtype_le (R : Subgroup ↥K) (Subgroup.mem_inf.mp hcD).1
  have hHleNP : H ≤ normalizer (P : Set X) := by
    refine sup_le ?_ Subgroup.le_normalizer
    rw [Subgroup.zpowers_le]
    exact hcNP
  have hH_eq : H = P ⊔ (H ⊓ normalizer (Y13 : Set X)) :=
    CFSG.LocalAnalysis.UniquenessCase.UC6.frattini_of_isSylowOf (p := 13) hPleH hHleNP hY_syl
  let M : Subgroup X := H ⊓ normalizer (Y13 : Set X)
  have hH_eqM : H = P ⊔ M := hH_eq
  have h5H : 5 ∣ Nat.card H := by
    have h := Subgroup.orderOf_dvd_natCard H hcH
    rwa [hcorder] at h
  have h5P : ¬ 5 ∣ Nat.card P := by
    rw [hcardP, hOcard]
    intro h
    rcases (Nat.prime_five.dvd_mul.mp h) with h5 | h5
    · exact (by norm_num : ¬ (5 : ℕ) ∣ 13) h5
    · exact (by norm_num : ¬ (5 : ℕ) ∣ 2) (Nat.prime_five.dvd_of_dvd_pow h5)
  have hdvd : Nat.card H ∣ Nat.card P * Nat.card M := by
    have hM_le_NP : M ≤ normalizer (P : Set X) := inf_le_left.trans hHleNP
    have hmul := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := M) (K := P) hM_le_NP
    refine ⟨Nat.card ↥(M ⊓ P), ?_⟩
    have hHM : Nat.card H = Nat.card ↥(M ⊔ P) := by rw [hH_eqM, sup_comm]
    rw [hHM, mul_comm (Nat.card P) (Nat.card M)]
    exact hmul.symm
  have h5M : 5 ∣ Nat.card M := by
    have h5PM : 5 ∣ Nat.card P * Nat.card M := h5H.trans hdvd
    rcases (Nat.prime_five.dvd_mul.mp h5PM) with h5 | h5
    · exact absurd h5 h5P
    · exact h5
  obtain ⟨c'₀, hc'₀order⟩ := exists_prime_orderOf_dvd_card' (G := ↥M) 5 h5M
  let c' : X := (c'₀ : X)
  have hc'M : c' ∈ M := c'₀.2
  have hc'order : orderOf c' = 5 := by
    dsimp only [c']
    rw [Subgroup.orderOf_coe, hc'₀order]
  have hc'H : c' ∈ H := (Subgroup.mem_inf.mp hc'M).1
  have hc'K : c' ∈ K := hHleK hc'H
  have hc'NY : c' ∈ normalizer (Y13 : Set X) := (Subgroup.mem_inf.mp hc'M).2
  let ψ : MulAut ↥Y13 := CFSG.LocalAnalysis.EvenBN.GMSK.qcConjAut Y13 hc'NY
  have hψ5 : ψ ^ 5 = 1 := by
    dsimp only [ψ]
    ext z
    rw [qcConjAut_pow_coe hc'NY 5 z]
    have hc'pow : c' ^ 5 = 1 := by rw [← hc'order]; exact pow_orderOf_eq_one c'
    rw [hc'pow]
    simp
  have hψ12 : ψ ^ 12 = 1 := by
    let : IsCyclic ↥Y13 := Subgroup.isCyclic_zpowers y
    have hcardAut : Nat.card (MulAut ↥Y13) = 12 := by
      rw [IsCyclic.card_mulAut, hYcard, Nat.totient_prime (by norm_num : Nat.Prime 13)]
    have hdvd12 : orderOf ψ ∣ 12 := by
      rw [← hcardAut]
      exact orderOf_dvd_natCard ψ
    exact (orderOf_dvd_iff_pow_eq_one).mp hdvd12
  have hψ1 : ψ = 1 := by
    have hdvd5 : orderOf ψ ∣ 5 := (orderOf_dvd_iff_pow_eq_one).mpr hψ5
    have hdvd12 : orderOf ψ ∣ 12 := (orderOf_dvd_iff_pow_eq_one).mpr hψ12
    have h1 : orderOf ψ = 1 := by
      have h := Nat.dvd_gcd hdvd5 hdvd12
      have hg : Nat.gcd 5 12 = 1 := by norm_num
      rw [hg] at h
      exact Nat.dvd_one.mp h
    exact orderOf_eq_one_iff.mp h1
  have hconj : c' * y * c'⁻¹ = y := by
    have hψy : ψ ⟨y, Subgroup.mem_zpowers y⟩ = ⟨y, Subgroup.mem_zpowers y⟩ := by
      rw [hψ1]
      rfl
    have h := congrArg (fun z : ↥Y13 => (z : X)) hψy
    dsimp only [ψ] at h
    rw [CFSG.LocalAnalysis.EvenBN.GMSK.qcConjAut_apply_coe] at h
    exact h
  have hcomm : Commute c' y := by
    calc c' * y = (c' * y * c'⁻¹) * c' := by group
      _ = y * c' := by rw [hconj]
  have hc'y_order : orderOf (c' * y) = 65 := by
    have hco : Nat.Coprime (orderOf c') (orderOf y) := by
      rw [hc'order, hyorder]
      norm_num
    rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hco, hc'order, hyorder]
  have hc'yK : c' * y ∈ K := K.mul_mem hc'K (h.le hyL)
  have hRuorder : orderOf (eRu ⟨c' * y, hc'yK⟩) = 65 := by
    rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe (⟨c' * y, hc'yK⟩ : ↥K)]
    exact hc'y_order
  exact CFSG.HardMathSupport.Dickson.Sec6.I1431.noOrder65_Ru _ hRuorder

end CoreSetup

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410
