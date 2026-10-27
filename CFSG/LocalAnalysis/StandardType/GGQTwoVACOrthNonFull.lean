module

public import CFSG.LocalAnalysis.StandardType.GGQTwoVACOrthRest
public import CFSG.LocalAnalysis.StandardType.GGQTwoCavQuotient
public import CFSG.LocalAnalysis.StandardType.GGQTwoCavImageOrder
public import CFSG.GroupTheory.CentralizerMapMulEquiv
public import CFSG.GroupTheory.IsComponentOfMap
public import CFSG.LocalAnalysis.StandardType.GGQTwoTBCOrthComp
public import CFSG.LocalAnalysis.StandardType.GGQTwoRationalWeyl
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CRankInv
public import CFSG.GroupTheory.InvolutionPair
public import CFSG.LocalAnalysis.StandardType.GGQTwoVACLinClass
import CFSG.LocalAnalysis.StandardType.GGTriD4NoneAutRank

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open CFSG.LocalAnalysis.GorensteinLyons
open Polynomial
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.PartOne.KCOrthogonal

variable {G : Type} [Group G] [Finite G]

theorem ggQ2OrthNonFull_torus_frame_of_charSum {K : Type} [Field K] [Finite K] [CharP K 2]
    [Fact (Nat.Prime 3)]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hpq : 3 ∣ Nat.card K - 1 ∨ 3 ∣ Nat.card K + 1) {m : ℕ}
    (hV : Module.finrank K V = 2 * m)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    (hchar : OrdPNsOm.charSum Q ⊤ ≡ -1 [ZMOD 3])
    {E : Subgroup ↥(orthDerived Q)} (hE : IsElemAbelian 3 E)
    (h3 : 3 ^ 3 ≤ Nat.card E)
    (hsc : ∀ g : ↥(orthDerived Q), (∀ z ∈ E, g * z = z * g) → g ^ 3 = 1 → g ∈ E) :
    ∃ (r : ℕ) (τ : (Fin r → Multiplicative (ZMod 3)) →* (V ≃ₗ[K] V)),
      Function.Injective τ ∧ MonoidHom.range τ = E.map (orthDerived Q).subtype ∧ r = m - 1 := by
  classical
  have hne : ∃ b ∈ E, b ≠ 1 := by
    by_contra h
    push Not at h
    have hE1 : E = ⊥ := (Subgroup.eq_bot_iff_forall E).mpr fun x hx => h x hx
    rw [hE1, Subgroup.card_bot] at h3
    omega
  let A : Subgroup (V ≃ₗ[K] V) := E.map (orthDerived Q).subtype
  have hAΩ : A ≤ orthDerived Q := Subgroup.map_subtype_le _
  have hApow : ∀ a ∈ A, a ^ 3 = 1 := by
    rintro _ ⟨e, he, rfl⟩
    exact congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[K] V)) (hE.2 e he)
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨f, hf, rfl⟩
    exact congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[K] V))
      (TableB.IsElemAbelian.comm hE he hf)
  have hmax : ∀ g ∈ orthDerived Q, g ^ 3 = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A := by
    intro g hg hgp hgc
    refine ⟨⟨g, hg⟩, ?_, rfl⟩
    refine hsc ⟨g, hg⟩ (fun e he => ?_) (Subtype.ext (by simpa using hgp))
    apply Subtype.ext
    exact hgc (e : V ≃ₗ[K] V) ⟨e, he, rfl⟩
  have hneA : ∃ b ∈ A, b ≠ 1 := by
    obtain ⟨b, hb, hb1⟩ := hne
    exact ⟨b, ⟨b, hb, rfl⟩, fun h => hb1 (Subtype.ext h)⟩
  obtain ⟨r, τ, F, -, -, hdimle, hτinj, hrange, -, -, -, hcharAlt⟩ :=
    OrthTorus.exists_torus_frame_full (p := 3) (hp2 := by norm_num) (hpq := hpq) (hQ := hQ)
      (hT := hT) (A := A) (hAΩ := hAΩ) (hApow := hApow) (hAcomm := hAcomm) (hmax := hmax)
      (hne := hneA)
  have hr : r = m - 1 := by
    rcases hcharAlt with ⟨hpos, hfin⟩ | ⟨-, hfin, -⟩
    · exact absurd (hchar.symm.trans hpos)
        (OrthTorus.neg_one_not_modEq_one Nat.prime_three (by norm_num))
    · omega
  exact ⟨r, τ, hτinj, hrange, hr⟩

theorem ggQ2OrthNonFull_card_range {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] {r : ℕ}
    {τ : (Fin r → Multiplicative (ZMod 3)) →* (V ≃ₗ[K] V)}
    (hτinj : Function.Injective τ) :
    Nat.card (MonoidHom.range τ) = 3 ^ r := by
  have h1 : Nat.card (Fin r → Multiplicative (ZMod 3)) = 3 ^ r := by
    rw [Nat.card_congr (Equiv.piCongrRight fun _ => Multiplicative.toAdd),
      Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  have h2 : Nat.card (MonoidHom.range τ) = Nat.card (Fin r → Multiplicative (ZMod 3)) :=
    Nat.card_congr (MonoidHom.ofInjective hτinj).toEquiv.symm
  rw [h2, h1]

theorem ggQ2OrthNonFull_card_of_charSum {K : Type} [Field K] [Finite K] [CharP K 2]
    [Fact (Nat.Prime 3)]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hpq : 3 ∣ Nat.card K - 1 ∨ 3 ∣ Nat.card K + 1) {m : ℕ}
    (hV : Module.finrank K V = 2 * m)
    (hT : ∃ T : Submodule K V, Module.finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    (hchar : OrdPNsOm.charSum Q ⊤ ≡ -1 [ZMOD 3])
    {E : Subgroup ↥(orthDerived Q)} (hE : IsElemAbelian 3 E)
    (h3 : 3 ^ 3 ≤ Nat.card E)
    (hsc : ∀ g : ↥(orthDerived Q), (∀ z ∈ E, g * z = z * g) → g ^ 3 = 1 → g ∈ E) :
    Nat.card E = 3 ^ (m - 1) := by
  obtain ⟨r, τ, hτinj, hrange, hr⟩ :=
    ggQ2OrthNonFull_torus_frame_of_charSum hQ hpq hV hT hchar hE h3 hsc
  have hcardA : Nat.card (E.map (orthDerived Q).subtype) = Nat.card E :=
    Subgroup.card_map_of_injective (orthDerived Q).subtype_injective
  rw [← hr, ← hcardA, ← hrange]
  exact ggQ2OrthNonFull_card_range hτinj

theorem ggQ2OrthNonFull_A5_case_impossible {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J)
    (hidx : ((Subgroup.centralizer (J : Set G)).subgroupOf B).index ≤ 3) : False := by
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  have hDJ : LargeEvenStdSub 3 B x L D J := hcfg.2.2
  have hDcard : Nat.card D = 9 := by
    rw [hDJ.1.2.2.1]
    norm_num
  have hDinf : D = B ⊓ Subgroup.centralizer (J : Set G) := hDJ.1.2.2.2.2.2.2
  have hcardB4 : 81 ≤ Nat.card B := by
    have hBc : Nat.card B = 3 ^ LargeEvenTwoLocalRank 3 G := hcfg.1.2.2.2.2.2.2.1.1.2.1
    have h4 : 4 ≤ LargeEvenTwoLocalRank 3 G := hcfg.1.2.2.2.2.2.1.2.2.2
    calc 81 = 3 ^ 4 := by norm_num
      _ ≤ 3 ^ LargeEvenTwoLocalRank 3 G := Nat.pow_le_pow_right (by norm_num) h4
      _ = Nat.card B := hBc.symm
  have hcardC : Nat.card ((Subgroup.centralizer (J : Set G)).subgroupOf B) = 9 := by
    have hmap : ((Subgroup.centralizer (J : Set G)).subgroupOf B).map B.subtype =
        Subgroup.centralizer (J : Set G) ⊓ B := Subgroup.subgroupOf_map_subtype _ _
    have hinj : Nat.card (((Subgroup.centralizer (J : Set G)).subgroupOf B).map B.subtype) =
        Nat.card ((Subgroup.centralizer (J : Set G)).subgroupOf B) :=
      Subgroup.card_map_of_injective B.subtype_injective
    rw [hmap, inf_comm, ← hDinf, hDcard] at hinj
    exact hinj.symm
  have hmul := Subgroup.index_mul_card
    (H := (Subgroup.centralizer (J : Set G)).subgroupOf B)
  rw [hcardC] at hmul
  have hle : Nat.card B ≤ 27 := by
    calc Nat.card B = ((Subgroup.centralizer (J : Set G)).subgroupOf B).index * 9 := hmul.symm
      _ ≤ 3 * 9 := Nat.mul_le_mul_right 9 hidx
      _ = 27 := by norm_num
  omega

omit [Finite G] in
theorem ggQ2OrthNonFull_extract_plus {Bs L : Subgroup G}
    (hL : GGInnerDiagOnLabel (fun _ lab => GGQ2VACLabOrthNonFull 3 lab ∧ lab.tag = .D) 3 Bs L) :
    ∃ (K : Type) (hfield : Field K) (hfin : Finite K), letI := hfield; letI := hfin;
      Nat.card K = 2 ∧ ∃ (m : ℕ), 4 ≤ m ∧ Odd m ∧
        ∃ (θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K m)
          (_ : Bs ≤ Subgroup.normalizer (L : Set G)),
          commutator L = ⊤ ∧
          ∀ b ∈ Bs, ∃ φ ∈ LargeEvenInnSet (OrthRest.RPlus K m),
            LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ := by
  obtain ⟨hperf, lab, hlab, hraw⟩ := hL
  obtain ⟨R, hR, I, F, hQ⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ, hP⟩ := hQ
  obtain ⟨⟨hNF, htag⟩, hBsN, hBsI0⟩ := hP
  obtain ⟨⟨hgl, -⟩, h4, hpar⟩ := hNF
  have hn1 : lab.n = 1 := by
    have h1 : 1 ≤ lab.n := hlab.1
    have h2 : lab.n < 2 := hgl
    omega
  have hodd : Odd lab.rank := by
    rcases hpar with h | h
    · exact Nat.not_even_iff_odd.mp h.2
    · exact absurd (htag ▸ h.1) (by decide)
  have hrank3 : lab.rank ≠ 3 := by omega
  dsimp only [CFSG.Assembly.LargeEvenRawDatumLegacy] at hraw
  rw [htag] at hraw
  dsimp only at hraw
  rw [if_neg hrank3, hn1] at hraw
  obtain ⟨K, i1, i2, hK, hQ⟩ := hraw
  obtain ⟨-, -, θ', hP'⟩ := hQ
  exact ⟨K, i1, i2, hK, lab.rank, h4, hodd, θ', hP'.2.1, hperf, hP'.2.2⟩

omit [Finite G] in
theorem ggQ2OrthNonFull_extract_minus {Bs L : Subgroup G}
    (hL : GGInnerDiagOnLabel (fun _ lab => GGQ2VACLabOrthNonFull 3 lab ∧ lab.tag = .twD) 3 Bs L) :
    ∃ (K : Type) (hfield : Field K) (hfin : Finite K), letI := hfield; letI := hfin;
      Nat.card K = 2 ∧ ∃ (m : ℕ), 4 ≤ m ∧ Even m ∧ ∃ (b c : K),
        (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧
        ∃ (θ : L ⧸ Subgroup.center L ≃* OrthRest.RMinus K (m - 1) b c)
          (_ : Bs ≤ Subgroup.normalizer (L : Set G)),
          commutator L = ⊤ ∧
          ∀ b' ∈ Bs, ∃ φ ∈ LargeEvenInnSet (OrthRest.RMinus K (m - 1) b c),
            LargeEvenInduces θ (fun l l' => (l' : G) = b'⁻¹ * l * b') φ := by
  obtain ⟨hperf, lab, hlab, hraw⟩ := hL
  obtain ⟨R, hR, I, F, hQ⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ, hP⟩ := hQ
  obtain ⟨⟨hNF, htag⟩, hBsN, hBsI0⟩ := hP
  obtain ⟨⟨hgl, -⟩, h4, hpar⟩ := hNF
  have hn1 : lab.n = 1 := by
    have h1 : 1 ≤ lab.n := hlab.1
    have h2 : lab.n < 2 := hgl
    omega
  have heven : Even lab.rank := by
    rcases hpar with h | h
    · exact absurd (htag ▸ h.1) (by decide)
    · exact h.2
  have hrank2 : lab.rank ≠ 2 := by omega
  have hrank3 : lab.rank ≠ 3 := by omega
  dsimp only [CFSG.Assembly.LargeEvenRawDatumLegacy] at hraw
  rw [htag] at hraw
  dsimp only at hraw
  rw [if_neg hrank2, if_neg hrank3, hn1] at hraw
  obtain ⟨K, i1, i2, hK, b, c, hbc, hQ⟩ := hraw
  obtain ⟨-, -, θ', hP'⟩ := hQ
  exact ⟨K, i1, i2, hK, lab.rank, h4, heven, b, c, hbc, θ', hP'.2.1, hperf, hP'.2.2⟩

theorem ggQ2OrthNonFull_card_plus {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {m : ℕ} (hm : 4 ≤ m) (hodd : Odd m)
    {E : Subgroup ↥(orthDerived (TableBOrth.qPlusForm K m))} (hE : IsElemAbelian 3 E)
    (h3 : 3 ^ 3 ≤ Nat.card E)
    (hsc : ∀ g : ↥(orthDerived (TableBOrth.qPlusForm K m)), (∀ z ∈ E, g * z = z * g) →
      g ^ 3 = 1 → g ∈ E) :
    Nat.card E = 3 ^ (m - 1) := by
  have : CharP K 2 := charP_two_of_card (m := 1) (by rw [hK, pow_one])
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hpq : 3 ∣ Nat.card K + 1 := by rw [hK]
  have hT := OrthTorus.exists_totallySingular_qPlusForm (K := K) (n := n) (by omega)
  have hchar : OrdPNsOm.charSum (TableBOrth.qPlusForm K (n + 1)) ⊤ ≡ -1 [ZMOD 3] := by
    rw [OrthTorus.charSum_qPlusForm]
    have h := (OrthTorus.modEq_neg_one_of_dvd hpq).pow (n + 1)
    rwa [Odd.neg_one_pow hodd] at h
  have hdim : Module.finrank K (Fin (n + 1) ⊕ Fin (n + 1) → K) = 2 * (n + 1) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  exact ggQ2OrthNonFull_card_of_charSum (TableBOrth.nondegenerate_qPlusForm (n + 1))
    (Or.inr hpq) hdim hT hchar hE h3 hsc

theorem ggQ2OrthNonFull_card_minus {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {m : ℕ} (hm : 4 ≤ m) (heven : Even m) {b c : K}
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {E : Subgroup ↥(orthDerived (TableBOrth.qMinusForm K (m - 1) b c))}
    (hE : IsElemAbelian 3 E) (h3 : 3 ^ 3 ≤ Nat.card E)
    (hsc : ∀ g : ↥(orthDerived (TableBOrth.qMinusForm K (m - 1) b c)),
      (∀ z ∈ E, g * z = z * g) → g ^ 3 = 1 → g ∈ E) :
    Nat.card E = 3 ^ (m - 1) := by
  have : CharP K 2 := charP_two_of_card (m := 1) (by rw [hK, pow_one])
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hp : 3 ∣ Nat.card K + 1 := by rw [hK]
  obtain ⟨hchar, hTfun⟩ := OrthTorus.charSum_qMinusForm (K := K) (m := n) hbc
  have hchar' : OrdPNsOm.charSum (TableBOrth.qMinusForm K n b c) ⊤ ≡ -1 [ZMOD 3] := by
    rw [hchar, hK]
    have h2 : (2 : ℤ) ≡ -1 [ZMOD 3] := by
      rw [Int.modEq_iff_dvd]
      norm_num
    have hp2 := h2.pow (n + 1)
    rw [Even.neg_one_pow heven] at hp2
    simpa using hp2.neg
  have hT := hTfun (by omega)
  have hdim : Module.finrank K (LargeEvenMinusIdx n → K) = 2 * (n + 1) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
    ring
  exact ggQ2OrthNonFull_card_of_charSum (TableBOrth.nondegenerate_qMinusForm n hbc) (Or.inr hp)
    hdim hT hchar' hE h3 hsc

omit [Finite G] in
theorem center_eq_bot_of_mulEquiv_orthDerived {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} {R : Type} [Group R] (η : R ≃* ↥(orthDerived Q))
    (hZ : Subgroup.center ↥(orthDerived Q) = ⊥) : Subgroup.center R = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have h1 : η z ∈ Subgroup.center ↥(orthDerived Q) := by
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro g
    obtain ⟨y, rfl⟩ := η.surjective g
    rw [← map_mul, ← map_mul, hz y]
  rw [hZ, Subgroup.mem_bot] at h1
  exact η.injective (h1.trans (map_one η).symm)

omit [Finite G] in
theorem selfCent_map_of_mulEquiv {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {R : Type} [Group R] (η : R ≃* ↥(orthDerived Q))
    (ER : Subgroup R) (hERsc : ∀ g : R, (∀ z ∈ ER, g * z = z * g) → g ^ 3 = 1 → g ∈ ER) :
    ∀ g : ↥(orthDerived Q), (∀ z ∈ ER.map η.toMonoidHom, g * z = z * g) → g ^ 3 = 1 →
      g ∈ ER.map η.toMonoidHom := by
  intro g hg hg3
  have hcomm : ∀ a ∈ ER, η.symm g * a = a * η.symm g := by
    intro a ha
    refine η.injective ?_
    rw [map_mul, map_mul, η.apply_symm_apply]
    exact hg (η a) ⟨a, ha, rfl⟩
  have hg3' : η.symm g ^ 3 = 1 :=
    η.injective (by rw [map_pow, η.apply_symm_apply, hg3, map_one])
  exact ⟨η.symm g, hERsc (η.symm g) hcomm hg3', η.apply_symm_apply g⟩

omit [Finite G] in
theorem map_conj_eq_of_innerModel {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {R : Type} [Group R] {Bs L : Subgroup G}
    (η : R ≃* ↥(orthDerived Q)) (θ : L ⧸ Subgroup.center L ≃* R)
    {hN : Bs ≤ Subgroup.normalizer (L : Set G)} (Λ : R →* MulAut ↥L) (ER : Subgroup R)
    (hERmap : ER.map Λ = (ggGamma L hN).range)
    (hpt : ∀ e : R, gl2MarkingAutHom θ (Λ e) = MulAut.conj e) :
    (ER.map η.toMonoidHom).map (MulAut.conj : ↥(orthDerived Q) →*
        MulAut ↥(orthDerived Q)) =
      (ggBeta L θ hN).range.map (MulAut.congr η).toMonoidHom := by
  have hβ : (ggBeta L θ hN).range = (ggGamma L hN).range.map (gl2MarkingAutHom θ) := by
    rw [← MonoidHom.range_comp, QTwoCav.markingAutHom_comp_gamma θ hN]
  have hERconj : ER.map (MulAut.conj : R →* MulAut R) = (ggBeta L θ hN).range := by
    rw [hβ, ← hERmap, Subgroup.map_map]
    congr 1
    refine MonoidHom.ext fun e => ?_
    exact (hpt e).symm
  rw [← hERconj, Subgroup.map_map, Subgroup.map_map]
  congr 1
  refine MonoidHom.ext fun r => ?_
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
  exact (congr_conj η r).symm

omit [Finite G] in
theorem gl2MarkingAutHom_liftConj {R : Type} [Group R] {L : Subgroup G}
    (θ : L ⧸ Subgroup.center L ≃* R) (Λ : R →* MulAut ↥L)
    (hΛeq : ∀ {e : R} {x : ↥L}, ggQuotHom θ x = e → Λ e = MulAut.conj x) :
    ∀ e : R, gl2MarkingAutHom θ (Λ e) = MulAut.conj e := by
  intro e
  obtain ⟨l, rfl⟩ := ggQuotHom_surjective θ e
  rw [show Λ (ggQuotHom θ l) = MulAut.conj l from hΛeq rfl, gl2MarkingAutHom_apply,
    gl2MarkingAut_conj]
  rfl

theorem ggQ2OrthNonFull_exists_E_plus
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {m : ℕ} (hm : 4 ≤ m) (hm1 : 1 ≤ m) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J)
    {θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K m}
    {hN : Bs ≤ Subgroup.normalizer (L : Set G)}
    (hBsI0 : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenInnSet (OrthRest.RPlus K m),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :
    ∃ E : Subgroup ↥(orthDerived (TableBOrth.qPlusForm K m)),
      IsElemAbelian 3 E ∧ 3 ^ 3 ≤ Nat.card E ∧
      (∀ g : ↥(orthDerived (TableBOrth.qPlusForm K m)),
        (∀ z ∈ E, g * z = z * g) → g ^ 3 = 1 → g ∈ E) ∧
      E.map (MulAut.conj : ↥(orthDerived (TableBOrth.qPlusForm K m)) →*
          MulAut ↥(orthDerived (TableBOrth.qPlusForm K m))) =
        (ggBeta L θ hN).range.map
          (MulAut.congr (OrthTorus.rPlusEquiv K hm1)).toMonoidHom := by
  classical
  let η := OrthTorus.rPlusEquiv K hm1
  have hAI : ∀ a ∈ (ggGamma L hN).range, ∃ φ ∈ LargeEvenInnSet (OrthRest.RPlus K m),
      ∀ l : L, φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta L θ hN b, ggBeta_mem L θ hN hBsI0 b, fun l => ggBeta_ggQuotHom L hN θ b l⟩
  have hdim : Module.finrank K (Fin m ⊕ Fin m → K) = 2 * m := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  have hZΩ : Subgroup.center ↥(orthDerived (TableBOrth.qPlusForm K m)) = ⊥ :=
    (OrthRestOdd.orthDerived_facts (TableBOrth.qPlusForm K m)
      (TableBOrth.nondegenerate_qPlusForm m) (by rw [hdim]; omega)).2.1
  have hZR : Subgroup.center (OrthRest.RPlus K m) = ⊥ :=
    center_eq_bot_of_mulEquiv_orthDerived η hZΩ
  have hIp : GGOutdiagPrime 3 (OrthRest.RPlus K m) (LargeEvenInnSet _) := fun φ hφ _ => hφ
  have hcp : GGCenterPrime 3 (OrthRest.RPlus K m) :=
    CorFourTwoOpen.ggCenterPrime_omegaPlus Nat.prime_three (by norm_num) (by omega)
  obtain ⟨Λ, hΛeq, -, -, hAΛ, hERab, hERcard, hERsc⟩ :=
    TwE6TB.exists_innerModel Nat.prime_three hZR hIp hcp (ggQuotHom θ)
      (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hS.2.1.1
      (QTwoCav.gamma_hyps hS hN).1 hAI (QTwoCav.gamma_hyps hS hN).2
  let ER : Subgroup (OrthRest.RPlus K m) := (ggGamma L hN).range.comap Λ
  have hERmap : ER.map Λ = (ggGamma L hN).range := by
    rw [Subgroup.map_comap_eq,
      inf_eq_right.mpr fun a ha => by obtain ⟨e, he⟩ := hAΛ a ha; exact ⟨e, he⟩]
  have hpt := gl2MarkingAutHom_liftConj θ Λ hΛeq
  have hEeq := map_conj_eq_of_innerModel η θ Λ ER hERmap hpt
  refine ⟨ER.map η.toMonoidHom, TableB.isElemAbelian_map hERab η.toMonoidHom, ?_,
    selfCent_map_of_mulEquiv η ER hERsc, hEeq⟩
  rw [Subgroup.card_map_of_injective η.injective, hERcard]
  exact ggQ2Orth_three_le_card_gamma hS hN

theorem ggQ2OrthNonFull_exists_E_minus
    {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ} (hm : 4 ≤ m) {b c : K}
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J)
    {θ : L ⧸ Subgroup.center L ≃* OrthRest.RMinus K (m - 1) b c}
    {hN : Bs ≤ Subgroup.normalizer (L : Set G)}
    (hBsI0 : ∀ b' ∈ Bs, ∃ φ ∈ LargeEvenInnSet (OrthRest.RMinus K (m - 1) b c),
      LargeEvenInduces θ (fun l l' => (l' : G) = b'⁻¹ * l * b') φ) :
    ∃ E : Subgroup ↥(orthDerived (TableBOrth.qMinusForm K (m - 1) b c)),
      IsElemAbelian 3 E ∧ 3 ^ 3 ≤ Nat.card E ∧
      (∀ g : ↥(orthDerived (TableBOrth.qMinusForm K (m - 1) b c)),
        (∀ z ∈ E, g * z = z * g) → g ^ 3 = 1 → g ∈ E) ∧
      E.map (MulAut.conj : ↥(orthDerived (TableBOrth.qMinusForm K (m - 1) b c)) →*
          MulAut ↥(orthDerived (TableBOrth.qMinusForm K (m - 1) b c))) =
        (ggBeta L θ hN).range.map
          (MulAut.congr (OrthTorus.rMinusEquiv K (m - 1) b c)).toMonoidHom := by
  classical
  let η := OrthTorus.rMinusEquiv K (m - 1) b c
  have hAI : ∀ a ∈ (ggGamma L hN).range, ∃ φ ∈ LargeEvenInnSet (OrthRest.RMinus K (m - 1) b c),
      ∀ l : L, φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta L θ hN b, ggBeta_mem L θ hN hBsI0 b, fun l => ggBeta_ggQuotHom L hN θ b l⟩
  have hdim : Module.finrank K (LargeEvenMinusIdx (m - 1) → K) = 2 * m := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]; omega
  have hZΩ : Subgroup.center ↥(orthDerived (TableBOrth.qMinusForm K (m - 1) b c)) = ⊥ :=
    (OrthRestOdd.orthDerived_facts (TableBOrth.qMinusForm K (m - 1) b c)
      (TableBOrth.nondegenerate_qMinusForm (m - 1) hbc) (by rw [hdim]; omega)).2.1
  have hZR : Subgroup.center (OrthRest.RMinus K (m - 1) b c) = ⊥ :=
    center_eq_bot_of_mulEquiv_orthDerived η hZΩ
  have hIp : GGOutdiagPrime 3 (OrthRest.RMinus K (m - 1) b c) (LargeEvenInnSet _) :=
    fun φ hφ _ => hφ
  have hcp : GGCenterPrime 3 (OrthRest.RMinus K (m - 1) b c) :=
    CorFourTwoOpen.ggCenterPrime_omegaMinus Nat.prime_three (by norm_num) (by omega) hbc
  obtain ⟨Λ, hΛeq, -, -, hAΛ, hERab, hERcard, hERsc⟩ :=
    TwE6TB.exists_innerModel Nat.prime_three hZR hIp hcp (ggQuotHom θ)
      (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hS.2.1.1
      (QTwoCav.gamma_hyps hS hN).1 hAI (QTwoCav.gamma_hyps hS hN).2
  let ER : Subgroup (OrthRest.RMinus K (m - 1) b c) := (ggGamma L hN).range.comap Λ
  have hERmap : ER.map Λ = (ggGamma L hN).range := by
    rw [Subgroup.map_comap_eq,
      inf_eq_right.mpr fun a ha => by obtain ⟨e, he⟩ := hAΛ a ha; exact ⟨e, he⟩]
  have hpt := gl2MarkingAutHom_liftConj θ Λ hΛeq
  have hEeq := map_conj_eq_of_innerModel η θ Λ ER hERmap hpt
  refine ⟨ER.map η.toMonoidHom, TableB.isElemAbelian_map hERab η.toMonoidHom, ?_,
    selfCent_map_of_mulEquiv η ER hERsc, hEeq⟩
  rw [Subgroup.card_map_of_injective η.injective, hERcard]
  exact ggQ2Orth_three_le_card_gamma hS hN

theorem ggQ2OrthNonFull_automizer_eq {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} {R : Type} [Group R]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    (η : R ≃* ↥(orthDerived Q)) (θ : L ⧸ Subgroup.center L ≃* R)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hZ : Subgroup.center ↥(orthDerived Q) = ⊥) (E : Subgroup ↥(orthDerived Q))
    (hE : E.map (MulAut.conj : ↥(orthDerived Q) →* MulAut ↥(orthDerived Q)) =
      (ggBeta L θ hN).range.map (MulAut.congr η).toMonoidHom) :
    Nat.card (ggAutomizer ((J.subgroupOf L).map (η.toMonoidHom.comp (ggQuotHom θ))) E) =
      Nat.card (ggAutomizer J Bs) := by
  classical
  have hperf : commutator L = ⊤ := hS.2.1.1
  have hconj : Function.Injective
      (MulAut.conj : ↥(orthDerived Q) →* MulAut ↥(orthDerived Q)) :=
    conj_injective_of_center_eq_bot hZ
  have hJbar : ((J.subgroupOf L).map (η.toMonoidHom.comp (ggQuotHom θ))).map
      (MulAut.conj : ↥(orthDerived Q) →* MulAut ↥(orthDerived Q)) =
      (((J.subgroupOf L).map (ggQuotHom θ)).map (MulAut.conj : R →* MulAut R)).map
        (MulAut.congr η).toMonoidHom := by
    ext φ
    simp only [Subgroup.mem_map]
    constructor
    · rintro ⟨-, ⟨l, hl, rfl⟩, hφ⟩
      exact ⟨MulAut.conj (ggQuotHom θ l), ⟨ggQuotHom θ l, ⟨l, hl, rfl⟩, rfl⟩,
        (congr_conj η (ggQuotHom θ l)).trans hφ⟩
    · rintro ⟨-, ⟨-, ⟨l, hl, rfl⟩, rfl⟩, hφ⟩
      exact ⟨η (ggQuotHom θ l), ⟨l, hl, rfl⟩,
        (congr_conj η (ggQuotHom θ l)).symm.trans hφ⟩
  have hcard1 : Nat.card (ggAutomizer ((J.subgroupOf L).map
      (η.toMonoidHom.comp (ggQuotHom θ))) E) = Nat.card (ggAutomizer
        (((J.subgroupOf L).map (η.toMonoidHom.comp (ggQuotHom θ))).map
          (MulAut.conj : ↥(orthDerived Q) →* MulAut ↥(orthDerived Q))) (E.map
            (MulAut.conj : ↥(orthDerived Q) →* MulAut ↥(orthDerived Q)))) := by
    rw [F4AutWeyl.ggAutomizer_map_eq hconj _ E rfl]
    exact (Subgroup.card_map_of_injective (f := (MulAut.congr _).toMonoidHom)
      (MulAut.congr _).injective).symm
  rw [hcard1, hJbar, hE]
  have hcard2 : Nat.card (ggAutomizer
      ((((J.subgroupOf L).map (ggQuotHom θ)).map (MulAut.conj : R →* MulAut R)).map
        (MulAut.congr η).toMonoidHom)
      (((ggBeta L θ hN).range).map (MulAut.congr η).toMonoidHom)) = Nat.card
        (ggAutomizer (((J.subgroupOf L).map (ggQuotHom θ)).map
          (MulAut.conj : R →* MulAut R)) (ggBeta L θ hN).range) := by
    rw [F4AutWeyl.ggAutomizer_map_eq (MulAut.congr η).injective _ _ rfl]
    exact Subgroup.card_map_of_injective (f := (MulAut.congr _).toMonoidHom)
      (MulAut.congr _).injective
  rw [hcard2, QTwoCav.card_automizer_quotient_image_eq θ hperf hN,
    QTwoCav.card_automizer_inner_image_eq_of_setting hS Nat.prime_three (by norm_num) hN]

open CFSG.LocalAnalysis.GLTheoremA.S172C.Cent CFSG.StandardType.OmNsRootGen

theorem ggQ2OrthNonFull_frame {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hK : Nat.card K = 2) {ℓ : ℕ} (hdim : Module.finrank K V = 2 * ℓ) (h4 : 4 ≤ ℓ)
    (htype : CFSG.GroupTheory.WeirSylow.IsPlusType Q ↔ Odd ℓ)
    {E : Subgroup ↥(orthDerived Q)} (hE : IsElemAbelian 3 E)
    (hsc : ∀ g : ↥(orthDerived Q), (∀ z ∈ E, g * z = z * g) → g ^ 3 = 1 → g ∈ E) :
    ∃ (k : ℕ) (U : Fin k → Submodule K V) (e : Fin k → ↥(orthDerived Q)) (u : Fin k → V)
      (c t : K) (f f' : V),
      IsCoherentFrame Q 3 U e E u c t ∧ k + 1 = ℓ ∧
      f ∈ polarPerp Q (⨆ j, U j) ∧ f' ∈ polarPerp Q (⨆ j, U j) ∧
      Q f = 0 ∧ Q f' = 0 ∧ QuadraticMap.polar Q f f' = 1 := by
  have hpq : 3 ∣ Nat.card K + 1 := by rw [hK]
  exact TorDNs.exists_nonFullCoherentFrame (p := 3) hQ Nat.prime_three (by norm_num) hpq
    hdim h4 htype hE hsc

theorem ggQ2OrthNonFull_beta_inn {R : Type} [Group R] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    (θ : L ⧸ Subgroup.center L ≃* R) (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBsI0 : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenInnSet R,
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :
    ∀ d : ↥D, ∃ r : R, ggBeta L θ (QTwoCav.d_le_normalizer hS hN) d = MulAut.conj r := by
  intro d
  have hdBs : (d : G) ∈ Bs := hS.1.1.2.1.1 (hS.1.1.2.2.1.1 d.2)
  obtain ⟨φ, hφ, hind⟩ := hBsI0 ((d : G)⁻¹) (inv_mem hdBs)
  have hφeq : φ = ggBeta L θ (QTwoCav.d_le_normalizer hS hN) d := by
    rw [ggBeta_eq]
    have h := eq_ggLAut_of_induces L θ (b := ((d : G)⁻¹))
      (inv_mem (QTwoCav.d_le_normalizer hS hN d.2)) hind
    refine h.trans ?_
    congr 1
    exact Subtype.ext (inv_inv (d : G))
  obtain ⟨r, hr⟩ := hφ
  exact ⟨r, hφeq.symm.trans hr.symm⟩

theorem ggQ2OrthNonFull_component {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {R : Type} [Group R]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J)
    (θ : L ⧸ Subgroup.center L ≃* R) (η : R ≃* ↥(orthDerived Q))
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hInn : ∀ d : ↥D, ∃ r : R,
      ggBeta L θ (QTwoCav.d_le_normalizer hS hN) d = MulAut.conj r) :
    ∃ (d : ↥D) (r : R),
      ggBeta L θ (QTwoCav.d_le_normalizer hS hN) d = MulAut.conj r ∧
      ggBeta L θ (QTwoCav.d_le_normalizer hS hN) d ≠ 1 ∧
      IsComponentOf (((J.subgroupOf L).map (ggQuotHom θ)).map η.toMonoidHom)
        (Subgroup.centralizer ({η r} : Set ↥(orthDerived Q))) := by
  classical
  obtain ⟨d, hd1, -, hfixD⟩ :=
    QTwoCav.exists_beta_d_generator θ Nat.prime_three hS hN
  obtain ⟨r, hr⟩ := hInn d
  have hJq : IsComponentOf ((J.subgroupOf L).map (ggQuotHom θ))
      (⨅ e : ↥D, ggFix (ggBeta L θ (QTwoCav.d_le_normalizer hS hN) e)) := by
    exact QTwoCav.isComponentOf_quotient_image (QTwoCav.d_le_normalizer hS hN) θ
      hS.1.1.2.2.1.2.2.2.2.2.1
  rw [hfixD] at hJq
  have hfix : ggFix (ggBeta L θ (QTwoCav.d_le_normalizer hS hN) d) =
      Subgroup.centralizer ({r} : Set R) := by
    rw [hr]
    ext x
    rw [mem_ggFix, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
    constructor
    · intro hx
      calc x * r = r * x * r⁻¹ * r := by rw [hx]
        _ = r * x := by group
    · intro hx
      calc r * x * r⁻¹ = (x * r) * r⁻¹ := by rw [hx]
        _ = x := by group
  have hJmap : IsComponentOf (((J.subgroupOf L).map (ggQuotHom θ)).map η.toMonoidHom)
      ((Subgroup.centralizer ({r} : Set R)).map η.toMonoidHom) := by
    rw [← hfix]
    exact CFSG.Assembly.isComponentOf_iff_open.mpr
      (CFSG.isComponentOf_map_mulEquiv η
        (CFSG.Assembly.isComponentOf_iff_open.mp hJq))
  have hcent : (Subgroup.centralizer ({r} : Set R)).map η.toMonoidHom =
      Subgroup.centralizer ({η r} : Set ↥(orthDerived Q)) :=
    CFSG.GroupTheory.centralizer_singleton_map_mulEquiv η r
  rw [hcent] at hJmap
  exact ⟨d, r, hr, hd1, hJmap⟩

theorem ggQ2OrthNonFull_comp_cases {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} {ℓ : ℕ} (hK : Nat.card K = 2)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hdim : Module.finrank K V = 2 * ℓ)
    {e : ↥(orthDerived Q)} (he3 : orderOf e = 3)
    {Jbar : Subgroup ↥(orthDerived Q)}
    (hJ : IsComponentOf Jbar (Subgroup.centralizer ({e} : Set ↥(orthDerived Q)))) :
    Jbar = (specialBlock Q (e : V ≃ₗ[K] V) (X ^ 2 + X + 1)).subgroupOf (orthDerived Q) ∨
      (Jbar = (supportedFixedDerived Q (e : V ≃ₗ[K] V)).subgroupOf (orthDerived Q) ∧
        (6 ≤ Module.finrank K (fixedSpace (e : V ≃ₗ[K] V)) ∨
          (Module.finrank K (fixedSpace (e : V ≃ₗ[K] V)) = 4 ∧
            ¬ CFSG.GroupTheory.WeirSylow.IsPlusType
              (Q.comp (fixedSpace (e : V ≃ₗ[K] V)).subtype)))) := by
  classical
  have hev3 : orderOf (e : V ≃ₗ[K] V) = 3 := (Subgroup.orderOf_coe e).trans he3
  have hcentmap : (Subgroup.centralizer ({e} : Set ↥(orthDerived Q))).map
      (orthDerived Q).subtype =
      orthDerived Q ⊓ Subgroup.centralizer ({(e : V ≃ₗ[K] V)} : Set (V ≃ₗ[K] V)) := by
    ext g
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      simpa using congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy)
    · rintro ⟨hgΩ, hgC⟩
      refine ⟨⟨g, hgΩ⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_, rfl⟩
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hgC)
  have hJv : IsComponentOf (Jbar.map (orthDerived Q).subtype)
      (orthDerived Q ⊓ Subgroup.centralizer ({(e : V ≃ₗ[K] V)} : Set (V ≃ₗ[K] V))) := by
    rw [← hcentmap]
    exact CFSG.Assembly.isComponentOf_iff_open.mpr
      (CFSG.LocalAnalysis.GLTheoremA.I142N.isComponentOf_map (orthDerived Q).subtype
        (fun g hg => by
          have hg1 : g = 1 := Subtype.ext (by
            rw [← map_one (orthDerived Q).subtype] at hg
            exact hg)
          rw [hg1]
          exact Subgroup.one_mem _)
        (CFSG.Assembly.isComponentOf_iff_open.mp hJ))
  rcases ggTBC_orth_comp_cases (F := K) hK hQ hdim e.2 hev3 hJv with hsp | ⟨hsp, hcond⟩
  · left
    have hle : specialBlock Q (e : V ≃ₗ[K] V) (X ^ 2 + X + 1) ≤ orthDerived Q := by
      rw [← hsp]
      exact Subgroup.map_subtype_le _
    exact Subgroup.map_injective (orthDerived Q).subtype_injective
      (by rw [hsp, Subgroup.map_subgroupOf_eq_of_le hle])
  · right
    refine ⟨?_, hcond⟩
    have hle : supportedFixedDerived Q (e : V ≃ₗ[K] V) ≤ orthDerived Q := by
      rw [← hsp]
      exact Subgroup.map_subtype_le _
    exact Subgroup.map_injective (orthDerived Q).subtype_injective
      (by rw [hsp, Subgroup.map_subgroupOf_eq_of_le hle])

theorem ggQ2OrthNonFull_component_of_innerModel {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {R : Type} [Group R]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J)
    (θ : L ⧸ Subgroup.center L ≃* R) (η : R ≃* ↥(orthDerived Q))
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hZ : Subgroup.center ↥(orthDerived Q) = ⊥) {E : Subgroup ↥(orthDerived Q)}
    (hE : E.map (MulAut.conj : ↥(orthDerived Q) →* MulAut ↥(orthDerived Q)) =
      (ggBeta L θ hN).range.map (MulAut.congr η).toMonoidHom)
    (hBsI0 : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenInnSet R,
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :
    ∃ t : ↥(orthDerived Q), t ∈ E ∧ orderOf t = 3 ∧
      IsComponentOf ((J.subgroupOf L).map (η.toMonoidHom.comp (ggQuotHom θ)))
        (Subgroup.centralizer ({t} : Set ↥(orthDerived Q))) := by
  classical
  have hZR : Subgroup.center R = ⊥ := center_eq_bot_of_mulEquiv_orthDerived η hZ
  obtain ⟨d, r, hr, hd1, hcomp⟩ :=
    ggQ2OrthNonFull_component hS θ η hN (ggQ2OrthNonFull_beta_inn hS θ hN hBsI0)
  have hdBs : (d : G) ∈ Bs := hS.1.1.2.1.1 (hS.1.1.2.2.1.1 d.2)
  have hbetaeq : ggBeta L θ hN ⟨(d : G), hdBs⟩ =
      ggBeta L θ (QTwoCav.d_le_normalizer hS hN) d := by
    rw [ggBeta_eq, ggBeta_eq]
  have hmem : MulAut.conj (η r) ∈
      (ggBeta L θ hN).range.map (MulAut.congr η).toMonoidHom := by
    have h0 : MulAut.congr η (ggBeta L θ hN ⟨(d : G), hdBs⟩) ∈
        (ggBeta L θ hN).range.map (MulAut.congr η).toMonoidHom :=
      Subgroup.mem_map_of_mem _ ⟨⟨(d : G), hdBs⟩, rfl⟩
    rw [hbetaeq, hr, congr_conj] at h0
    exact h0
  have htE : η r ∈ E := by
    rw [← hE] at hmem
    obtain ⟨e', he', hee'⟩ := Subgroup.mem_map.mp hmem
    exact (conj_injective_of_center_eq_bot hZ hee') ▸ he'
  have hr1 : r ≠ 1 := by
    intro h1
    apply hd1
    rw [hr, h1]
    exact map_one (MulAut.conj : R →* MulAut R)
  have hβ3 : (ggBeta L θ (QTwoCav.d_le_normalizer hS hN) d) ^ 3 = 1 := by
    have hd3 : d ^ 3 = 1 := Subtype.ext (by
      simpa [Subgroup.coe_pow, Subgroup.coe_one]
        using hS.1.1.2.2.1.2.1.2 (d : G) d.2)
    rw [← map_pow, hd3, map_one]
  have ht3 : orderOf (η r) = 3 := by
    have hβord : orderOf (ggBeta L θ (QTwoCav.d_le_normalizer hS hN) d) = 3 :=
      orderOf_eq_prime hβ3 hd1
    have hprod : orderOf (MulAut.conj r) = 3 := by rw [← hr]; exact hβord
    have hrord : orderOf r = 3 :=
      (orderOf_injective (MulAut.conj : R →* MulAut R)
        (conj_injective_of_center_eq_bot hZR) r).symm.trans hprod
    exact (MulEquiv.orderOf_eq η r).trans hrord
  refine ⟨η r, htE, ht3, ?_⟩
  rw [← Subgroup.map_map]
  exact hcomp

theorem ggQ2OrthNonFull_model_plus
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {m : ℕ} (hm : 4 ≤ m) (hodd : Odd m)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    {θ : L ⧸ Subgroup.center L ≃* OrthRest.RPlus K m}
    {hN : Bs ≤ Subgroup.normalizer (L : Set G)}
    (hBsI0 : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenInnSet (OrthRest.RPlus K m),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :
    ∃ (E : Subgroup ↥(orthDerived (TableBOrth.qPlusForm K m)))
      (ψ : ↥L →* ↥(orthDerived (TableBOrth.qPlusForm K m))),
      Function.Surjective ψ ∧ ψ.ker = Subgroup.center ↥L ∧
      IsElemAbelian 3 E ∧ Nat.card E = 3 ^ (m - 1) ∧
      (∀ g : ↥(orthDerived (TableBOrth.qPlusForm K m)),
        (∀ z ∈ E, g * z = z * g) → g ^ 3 = 1 → g ∈ E) ∧
      Nat.card (ggAutomizer ((J.subgroupOf L).map ψ) E) = Nat.card (ggAutomizer J Bs) ∧
      ∃ (t : ↥(orthDerived (TableBOrth.qPlusForm K m))), t ∈ E ∧ orderOf t = 3 ∧
        IsComponentOf ((J.subgroupOf L).map ψ)
          (Subgroup.centralizer ({t} : Set ↥(orthDerived (TableBOrth.qPlusForm K m)))) := by
  classical
  have : CharP K 2 := charP_two_of_card (m := 1) (by rw [hK, pow_one])
  have hm1 : 1 ≤ m := by omega
  let η := OrthTorus.rPlusEquiv K hm1
  obtain ⟨E, hEab, h3, hEsc, hEeq⟩ :=
    ggQ2OrthNonFull_exists_E_plus (hN := hN) hm hm1 hS hBsI0
  have hdim : Module.finrank K (Fin m ⊕ Fin m → K) = 2 * m := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    ring
  have hZ : Subgroup.center ↥(orthDerived (TableBOrth.qPlusForm K m)) = ⊥ :=
    (OrthRestOdd.orthDerived_facts (TableBOrth.qPlusForm K m)
      (TableBOrth.nondegenerate_qPlusForm m) (by rw [hdim]; omega)).2.1
  have hker : (η.toMonoidHom.comp (ggQuotHom θ)).ker = Subgroup.center ↥L := by
    rw [show (η.toMonoidHom.comp (ggQuotHom θ)).ker = (ggQuotHom θ).ker from ?_]
    · rw [ker_ggQuotHom]
    · ext l
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply]
      exact ⟨fun h => η.injective (by simpa using h), fun h => by simp [h]⟩
  obtain ⟨t, htE, ht3, hcomp⟩ :=
    ggQ2OrthNonFull_component_of_innerModel hS θ η hN hZ hEeq hBsI0
  exact ⟨E, η.toMonoidHom.comp (ggQuotHom θ), η.surjective.comp (ggQuotHom_surjective θ),
    hker, hEab, ggQ2OrthNonFull_card_plus hK hm hodd hEab h3 hEsc, hEsc,
    ggQ2OrthNonFull_automizer_eq hS η θ hN hZ E hEeq, t, htE, ht3, hcomp⟩

theorem ggQ2OrthNonFull_model_minus
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {m : ℕ} (hm : 4 ≤ m) (heven : Even m) {b c : K}
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    {θ : L ⧸ Subgroup.center L ≃* OrthRest.RMinus K (m - 1) b c}
    {hN : Bs ≤ Subgroup.normalizer (L : Set G)}
    (hBsI0 : ∀ b' ∈ Bs, ∃ φ ∈ LargeEvenInnSet (OrthRest.RMinus K (m - 1) b c),
      LargeEvenInduces θ (fun l l' => (l' : G) = b'⁻¹ * l * b') φ) :
    ∃ (E : Subgroup ↥(orthDerived (TableBOrth.qMinusForm K (m - 1) b c)))
      (ψ : ↥L →* ↥(orthDerived (TableBOrth.qMinusForm K (m - 1) b c))),
      Function.Surjective ψ ∧ ψ.ker = Subgroup.center ↥L ∧
      IsElemAbelian 3 E ∧ Nat.card E = 3 ^ (m - 1) ∧
      (∀ g : ↥(orthDerived (TableBOrth.qMinusForm K (m - 1) b c)),
        (∀ z ∈ E, g * z = z * g) → g ^ 3 = 1 → g ∈ E) ∧
      Nat.card (ggAutomizer ((J.subgroupOf L).map ψ) E) = Nat.card (ggAutomizer J Bs) ∧
      ∃ (t : ↥(orthDerived (TableBOrth.qMinusForm K (m - 1) b c))), t ∈ E ∧ orderOf t = 3 ∧
        IsComponentOf ((J.subgroupOf L).map ψ)
          (Subgroup.centralizer
            ({t} : Set ↥(orthDerived (TableBOrth.qMinusForm K (m - 1) b c)))) := by
  classical
  have : CharP K 2 := charP_two_of_card (m := 1) (by rw [hK, pow_one])
  have hm1 : 1 ≤ m := by omega
  let η := OrthTorus.rMinusEquiv K (m - 1) b c
  obtain ⟨E, hEab, h3, hEsc, hEeq⟩ :=
    ggQ2OrthNonFull_exists_E_minus (hN := hN) hm hbc hS hBsI0
  have hdim : Module.finrank K (LargeEvenMinusIdx (m - 1) → K) = 2 * m := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_fin]
    omega
  have hZ : Subgroup.center ↥(orthDerived (TableBOrth.qMinusForm K (m - 1) b c)) = ⊥ :=
    (OrthRestOdd.orthDerived_facts (TableBOrth.qMinusForm K (m - 1) b c)
      (TableBOrth.nondegenerate_qMinusForm (m - 1) hbc) (by rw [hdim]; omega)).2.1
  have hker : (η.toMonoidHom.comp (ggQuotHom θ)).ker = Subgroup.center ↥L := by
    rw [show (η.toMonoidHom.comp (ggQuotHom θ)).ker = (ggQuotHom θ).ker from ?_]
    · rw [ker_ggQuotHom]
    · ext l
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply]
      exact ⟨fun h => η.injective (by simpa using h), fun h => by simp [h]⟩
  obtain ⟨t, htE, ht3, hcomp⟩ :=
    ggQ2OrthNonFull_component_of_innerModel hS θ η hN hZ hEeq hBsI0
  exact ⟨E, η.toMonoidHom.comp (ggQuotHom θ), η.surjective.comp (ggQuotHom_surjective θ),
    hker, hEab, ggQ2OrthNonFull_card_minus hK hm heven hbc hEab h3 hEsc, hEsc,
    ggQ2OrthNonFull_automizer_eq hS η θ hN hZ E hEeq, t, htE, ht3, hcomp⟩

theorem ggQ2OrthNonFull_model_of_D
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J)
    (hD : GGInnerDiagOnLabel (fun _ lab => GGQ2VACLabOrthNonFull 3 lab ∧ lab.tag = .D) 3 Bs L) :
    ∃ (K : Type) (hfield : Field K) (hfin : Finite K), letI := hfield; letI := hfin;
      Nat.card K = 2 ∧ ∃ (V : Type) (hV : AddCommGroup V), letI := hV;
      ∃ (hM : Module K V), letI := hM;
      ∃ (hFd : FiniteDimensional K V), letI := hFd;
      ∃ (Q : QuadraticForm K V) (ℓ : ℕ) (E : Subgroup ↥(orthDerived Q))
        (ψ : ↥L →* ↥(orthDerived Q)),
        (QuadraticMap.polarBilin Q).Nondegenerate ∧ Module.finrank K V = 2 * ℓ ∧ 4 ≤ ℓ ∧
        (CFSG.GroupTheory.WeirSylow.IsPlusType Q ↔ Odd ℓ) ∧
        Function.Surjective ψ ∧ ψ.ker = Subgroup.center ↥L ∧
        IsElemAbelian 3 E ∧ Nat.card E = 3 ^ (ℓ - 1) ∧
        (∀ g : ↥(orthDerived Q), (∀ z ∈ E, g * z = z * g) → g ^ 3 = 1 → g ∈ E) ∧
        Nat.card (ggAutomizer ((J.subgroupOf L).map ψ) E) = Nat.card (ggAutomizer J Bs) ∧
        ∃ (t : ↥(orthDerived Q)), t ∈ E ∧ orderOf t = 3 ∧
          IsComponentOf ((J.subgroupOf L).map ψ)
            (Subgroup.centralizer ({t} : Set ↥(orthDerived Q))) := by
  obtain ⟨K, i1, i2, rest⟩ := ggQ2OrthNonFull_extract_plus hD
  obtain ⟨hK, m, h4, hodd, θ, hN, -, hBsI0⟩ := rest
  exact
    letI : Field K := i1
    letI : Finite K := i2
    letI : CharP K 2 := charP_two_of_card (m := 1) (by rw [hK, pow_one])
    (by
      obtain ⟨E, ψ, hψ, hker, hEab, hEcard, hEsc, haut, t, htE, ht3, hcomp⟩ :=
        ggQ2OrthNonFull_model_plus (θ := θ) (hN := hN) hK h4 hodd hS hBsI0
      have hdim : Module.finrank K (Fin m ⊕ Fin m → K) = 2 * m := by
        rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
        ring
      exact ⟨K, i1, i2, hK, Fin m ⊕ Fin m → K, inferInstance, inferInstance, inferInstance,
        TableBOrth.qPlusForm K m, m, E, ψ, TableBOrth.nondegenerate_qPlusForm m, hdim, h4,
        ⟨fun _ => hodd, fun _ => CFSG.GroupTheory.WeirSylow.isPlusType_quadPlus K m⟩, hψ,
        hker, hEab, hEcard, hEsc, haut, t, htE, ht3, hcomp⟩)

theorem ggQ2OrthNonFull_model_of_twD
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J)
    (hD : GGInnerDiagOnLabel (fun _ lab => GGQ2VACLabOrthNonFull 3 lab ∧ lab.tag = .twD) 3 Bs L) :
    ∃ (K : Type) (hfield : Field K) (hfin : Finite K), letI := hfield; letI := hfin;
      Nat.card K = 2 ∧ ∃ (V : Type) (hV : AddCommGroup V), letI := hV;
      ∃ (hM : Module K V), letI := hM;
      ∃ (hFd : FiniteDimensional K V), letI := hFd;
      ∃ (Q : QuadraticForm K V) (ℓ : ℕ) (E : Subgroup ↥(orthDerived Q))
        (ψ : ↥L →* ↥(orthDerived Q)),
        (QuadraticMap.polarBilin Q).Nondegenerate ∧ Module.finrank K V = 2 * ℓ ∧ 4 ≤ ℓ ∧
        (CFSG.GroupTheory.WeirSylow.IsPlusType Q ↔ Odd ℓ) ∧
        Function.Surjective ψ ∧ ψ.ker = Subgroup.center ↥L ∧
        IsElemAbelian 3 E ∧ Nat.card E = 3 ^ (ℓ - 1) ∧
        (∀ g : ↥(orthDerived Q), (∀ z ∈ E, g * z = z * g) → g ^ 3 = 1 → g ∈ E) ∧
        Nat.card (ggAutomizer ((J.subgroupOf L).map ψ) E) = Nat.card (ggAutomizer J Bs) ∧
        ∃ (t : ↥(orthDerived Q)), t ∈ E ∧ orderOf t = 3 ∧
          IsComponentOf ((J.subgroupOf L).map ψ)
            (Subgroup.centralizer ({t} : Set ↥(orthDerived Q))) := by
  obtain ⟨K, i1, i2, rest⟩ := ggQ2OrthNonFull_extract_minus hD
  obtain ⟨hK, m, h4, heven, b, c, hbc, θ, hN, -, hBsI0⟩ := rest
  exact
    letI : Field K := i1
    letI : Finite K := i2
    letI : CharP K 2 := charP_two_of_card (m := 1) (by rw [hK, pow_one])
    (by
      obtain ⟨E, ψ, hψ, hker, hEab, hEcard, hEsc, haut, t, htE, ht3, hcomp⟩ :=
        ggQ2OrthNonFull_model_minus (θ := θ) (hN := hN) hK h4 heven hbc hS hBsI0
      have hdim : Module.finrank K (LargeEvenMinusIdx (m - 1) → K) = 2 * m := by
        rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
          Fintype.card_fin, Fintype.card_fin]
        omega
      have htype : CFSG.GroupTheory.WeirSylow.IsPlusType
          (TableBOrth.qMinusForm K (m - 1) b c) ↔ Odd m :=
        ⟨fun h => absurd ((CFSG.GroupTheory.WeirSylow.isPlusType_congr
            (TableBOrth.qMinusIsometry (m - 1) b c)).mp h)
            (CFSG.GroupTheory.WeirSylow.not_isPlusType_quadMinus (by omega) hbc),
          fun h => absurd heven (Nat.not_even_iff_odd.mpr h)⟩
      exact ⟨K, i1, i2, hK, LargeEvenMinusIdx (m - 1) → K, inferInstance, inferInstance,
        inferInstance, TableBOrth.qMinusForm K (m - 1) b c, m, E, ψ,
        TableBOrth.nondegenerate_qMinusForm (m - 1) hbc, hdim, h4, htype, hψ, hker, hEab,
        hEcard, hEsc, haut, t, htE, ht3, hcomp⟩)

theorem ggQ2OrthNonFull_model
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J)
    (hL : GGInnerDiagOnLabel GGQ2VACLabOrthNonFull 3 Bs L) :
    ∃ (K : Type) (hfield : Field K) (hfin : Finite K), letI := hfield; letI := hfin;
      Nat.card K = 2 ∧ ∃ (V : Type) (hV : AddCommGroup V), letI := hV;
      ∃ (hM : Module K V), letI := hM;
      ∃ (hFd : FiniteDimensional K V), letI := hFd;
      ∃ (Q : QuadraticForm K V) (ℓ : ℕ) (E : Subgroup ↥(orthDerived Q))
        (ψ : ↥L →* ↥(orthDerived Q)),
        (QuadraticMap.polarBilin Q).Nondegenerate ∧ Module.finrank K V = 2 * ℓ ∧ 4 ≤ ℓ ∧
        (CFSG.GroupTheory.WeirSylow.IsPlusType Q ↔ Odd ℓ) ∧
        Function.Surjective ψ ∧ ψ.ker = Subgroup.center ↥L ∧
        IsElemAbelian 3 E ∧ Nat.card E = 3 ^ (ℓ - 1) ∧
        (∀ g : ↥(orthDerived Q), (∀ z ∈ E, g * z = z * g) → g ^ 3 = 1 → g ∈ E) ∧
        Nat.card (ggAutomizer ((J.subgroupOf L).map ψ) E) = Nat.card (ggAutomizer J Bs) ∧
        ∃ (t : ↥(orthDerived Q)), t ∈ E ∧ orderOf t = 3 ∧
          IsComponentOf ((J.subgroupOf L).map ψ)
            (Subgroup.centralizer ({t} : Set ↥(orthDerived Q))) := by
  have hL' : GGInnerDiagOnLabel (fun _ lab =>
      (GGQ2VACLabOrthNonFull 3 lab ∧ lab.tag = .D) ∨
        (GGQ2VACLabOrthNonFull 3 lab ∧ lab.tag = .twD)) 3 Bs L :=
    hL.mono_label fun lab h => by
      obtain ⟨horth, h4, hpar⟩ := h
      rcases horth.2 with hD | htw
      · exact Or.inl ⟨⟨horth, h4, hpar⟩, hD⟩
      · exact Or.inr ⟨⟨horth, h4, hpar⟩, htw⟩
  rcases hL'.elim_or with hD | htw
  · exact ggQ2OrthNonFull_model_of_D hS hD
  · exact ggQ2OrthNonFull_model_of_twD hS htw

section SignChangePair

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.StandardType.OmNsRootGen

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ} {k : ℕ} {U : Fin k → Submodule F V}
  {e : Fin k → ↥(orthDerived Q)} {E : Subgroup ↥(orthDerived Q)} {u : Fin k → V} {c t : F}
  {a b : Fin k}

omit [Finite F] [CharP F 2] [FiniteDimensional F V] in
theorem signChange_comm (hF : IsCoherentFrame Q p U e E u c t) {v : V}
    (hv : v ∈ polarPerp Q (⨆ j, U j)) (hab : a ≠ b) :
    signChange Q u v a * signChange Q u v b = signChange Q u v b * signChange Q u v a := by
  have hua : polar Q (u a) (u b) = 0 :=
    hF.perp a b hab (u a) (hF.mem a) (u b) (hF.mem b)
  have hva : polar Q (u a) v = 0 :=
    mem_polarPerp_iff.1 hv (u a) (le_iSup U a (hF.mem a))
  have hvb : polar Q (u b) v = 0 :=
    mem_polarPerp_iff.1 hv (u b) (le_iSup U b (hF.mem b))
  have hAB : reflect Q (u a) * reflect Q (u b) = reflect Q (u b) * reflect Q (u a) :=
    (CFSG.LocalAnalysis.GLTheoremA.S172C.Rank.commute_reflect_of_polar_eq_zero hua).eq
  have hAV : reflect Q (u a) * reflect Q v = reflect Q v * reflect Q (u a) :=
    (CFSG.LocalAnalysis.GLTheoremA.S172C.Rank.commute_reflect_of_polar_eq_zero hva).eq
  have hBV : reflect Q (u b) * reflect Q v = reflect Q v * reflect Q (u b) :=
    (CFSG.LocalAnalysis.GLTheoremA.S172C.Rank.commute_reflect_of_polar_eq_zero hvb).eq
  rw [signChange]
  exact (Commute.mul_left (Commute.mul_right hAB hAV)
    (Commute.mul_right hBV.symm (Commute.refl (reflect Q v)))).eq

omit [Finite F] [CharP F 2] [FiniteDimensional F V] in
theorem coherentFrame_e_ne_inv (hF : IsCoherentFrame Q p U e E u c t) (hp : p = 3)
    (i : Fin k) : e i ≠ (e i)⁻¹ := by
  have h3 : orderOf (e i) = 3 := by rw [hF.orderOf_eq i, hp]
  intro heq
  have hsq : e i * e i = 1 := by
    nth_rewrite 1 [heq]
    exact inv_mul_cancel _
  have hdvd : orderOf (e i) ∣ 2 := by
    apply orderOf_dvd_iff_pow_eq_one.mpr
    rwa [pow_two]
  rw [h3] at hdvd
  norm_num at hdvd

theorem signChange_conj_self_subgroup (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hF : IsCoherentFrame Q p U e E u c t) {v : V}
    (hv : v ∈ polarPerp Q (⨆ j, U j)) (hQv : Q v ≠ 0) (i : Fin k) :
    (⟨signChange Q u v i, signChange_mem_orthDerived hQ hF hQv⟩ : ↥(orthDerived Q)) *
      e i * (⟨signChange Q u v i, signChange_mem_orthDerived hQ hF hQv⟩ :
        ↥(orthDerived Q)) = (e i)⁻¹ := by
  apply Subtype.ext
  simpa using signChange_conj_self hF hv (a := i)

theorem signChange_conj_of_ne_subgroup (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hF : IsCoherentFrame Q p U e E u c t) {v : V}
    (hv : v ∈ polarPerp Q (⨆ j, U j)) (hQv : Q v ≠ 0) {i j : Fin k} (hij : j ≠ i) :
    (⟨signChange Q u v i, signChange_mem_orthDerived hQ hF hQv⟩ : ↥(orthDerived Q)) *
      e j * (⟨signChange Q u v i, signChange_mem_orthDerived hQ hF hQv⟩ :
        ↥(orthDerived Q)) = e j := by
  apply Subtype.ext
  simpa using signChange_conj_of_ne hF hv (a := i) (j := j) hij

theorem signChange_pair_conj_self (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hF : IsCoherentFrame Q p U e E u c t) {v : V}
    (hv : v ∈ polarPerp Q (⨆ j, U j)) (hQv : Q v ≠ 0) (hab : a ≠ b) :
    let g : ↥(orthDerived Q) :=
      ⟨signChange Q u v a, signChange_mem_orthDerived hQ hF hQv⟩
    let h : ↥(orthDerived Q) :=
      ⟨signChange Q u v b, signChange_mem_orthDerived hQ hF hQv⟩
    (g * h) * e a * (g * h) = (e a)⁻¹ := by
  let g : ↥(orthDerived Q) :=
    ⟨signChange Q u v a, signChange_mem_orthDerived hQ hF hQv⟩
  let h : ↥(orthDerived Q) :=
    ⟨signChange Q u v b, signChange_mem_orthDerived hQ hF hQv⟩
  have hh : (h : V ≃ₗ[F] V) * (e a : V ≃ₗ[F] V) * (h : V ≃ₗ[F] V) =
      (e a : V ≃ₗ[F] V) := by
    simpa [h] using signChange_conj_of_ne hF hv (a := b) (j := a) hab
  have hg : (g : V ≃ₗ[F] V) * (e a : V ≃ₗ[F] V) * (g : V ≃ₗ[F] V) =
      ((e a : ↥(orthDerived Q)) : V ≃ₗ[F] V)⁻¹ := by
    simpa [g] using signChange_conj_self hF hv (a := a)
  have hcomm : g * h = h * g := by
    apply Subtype.ext
    simpa [g, h] using signChange_comm hF hv hab
  have hcomm' : (g : V ≃ₗ[F] V) * (h : V ≃ₗ[F] V) =
      (h : V ≃ₗ[F] V) * (g : V ≃ₗ[F] V) := by
    simpa using congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V)) hcomm
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  calc ((g : V ≃ₗ[F] V) * (h : V ≃ₗ[F] V)) * (e a : V ≃ₗ[F] V) *
        ((g : V ≃ₗ[F] V) * (h : V ≃ₗ[F] V))
      = (g : V ≃ₗ[F] V) * (h : V ≃ₗ[F] V) * (e a : V ≃ₗ[F] V) *
          (h : V ≃ₗ[F] V) * (g : V ≃ₗ[F] V) := by
          rw [hcomm']
          group
    _ = (g : V ≃ₗ[F] V) * ((h : V ≃ₗ[F] V) * (e a : V ≃ₗ[F] V) *
          (h : V ≃ₗ[F] V)) * (g : V ≃ₗ[F] V) := by group
    _ = (g : V ≃ₗ[F] V) * (e a : V ≃ₗ[F] V) * (g : V ≃ₗ[F] V) := by rw [hh]
    _ = ((e a : ↥(orthDerived Q)) : V ≃ₗ[F] V)⁻¹ := hg

theorem signChange_mem_normalizer (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hF : IsCoherentFrame Q p U e E u c t) {v : V}
    (hv : v ∈ polarPerp Q (⨆ j, U j)) (hQv : Q v ≠ 0) (i : Fin k) :
    (⟨signChange Q u v i, signChange_mem_orthDerived hQ hF hQv⟩ :
      ↥(orthDerived Q)) ∈ Subgroup.normalizer (E : Set ↥(orthDerived Q)) := by
  let g : ↥(orthDerived Q) :=
    ⟨signChange Q u v i, signChange_mem_orthDerived hQ hF hQv⟩
  have hg2 : g * g = 1 := by
    apply Subtype.ext
    simpa [g] using signChange_mul_self hF hv (a := i)
  have hg_inv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg2
  have hconj_self : g * e i * g = (e i)⁻¹ := by
    simpa [g] using signChange_conj_self_subgroup hQ hF hv hQv i
  have hconj_ne : ∀ j, j ≠ i → g * e j * g = e j := by
    intro j hj
    simpa [g] using signChange_conj_of_ne_subgroup hQ hF hv hQv (i := i) (j := j) hj
  have hconj : ∀ x ∈ E, g * x * g⁻¹ ∈ E := by
    intro x hx
    rw [← hF.closure_eq] at hx ⊢
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        by_cases hji : j = i
        · subst hji
          rw [hg_inv, hconj_self]
          exact Subgroup.inv_mem _ (Subgroup.subset_closure ⟨j, rfl⟩)
        · rw [hg_inv, hconj_ne j hji]
          exact Subgroup.subset_closure ⟨j, rfl⟩
    | one => simp
    | mul x y hx hy ihx ihy =>
        have hxy : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
        rw [hxy]
        exact Subgroup.mul_mem _ ihx ihy
    | inv x hx ih =>
        have hx' : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
        rw [hx']
        exact Subgroup.inv_mem _ ih
  refine Subgroup.mem_normalizer_iff.2 fun x => ⟨fun hx => hconj x hx, ?_⟩
  intro hx
  have hz : g * (g * x * g⁻¹) * g⁻¹ ∈ E := hconj (g * x * g⁻¹) hx
  have hgg : g * (g * x * g⁻¹) * g⁻¹ = x := by
    rw [hg_inv]
    calc g * (g * x * g) * g = (g * g) * x * (g * g) := by group
      _ = x := by rw [hg2]; group
  simpa [hgg] using hz

theorem signChange_ne_one (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hF : IsCoherentFrame Q p U e E u c t) {v : V}
    (hv : v ∈ polarPerp Q (⨆ j, U j)) (hQv : Q v ≠ 0) (hp : p = 3) (i : Fin k) :
    (⟨signChange Q u v i, signChange_mem_orthDerived hQ hF hQv⟩ :
      ↥(orthDerived Q)) ≠ 1 := by
  intro hg1
  have hconj := signChange_conj_self_subgroup hQ hF hv hQv i
  rw [hg1] at hconj
  exact coherentFrame_e_ne_inv hF hp i (by simpa using hconj)

theorem signChange_pair_ne (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hF : IsCoherentFrame Q p U e E u c t) {v : V}
    (hv : v ∈ polarPerp Q (⨆ j, U j)) (hQv : Q v ≠ 0) (hp : p = 3) (hab : a ≠ b) :
    (⟨signChange Q u v a, signChange_mem_orthDerived hQ hF hQv⟩ : ↥(orthDerived Q)) ≠
      (⟨signChange Q u v b, signChange_mem_orthDerived hQ hF hQv⟩ :
        ↥(orthDerived Q)) := by
  intro hgh
  have hh2 : (⟨signChange Q u v b, signChange_mem_orthDerived hQ hF hQv⟩ :
      ↥(orthDerived Q)) *
      (⟨signChange Q u v b, signChange_mem_orthDerived hQ hF hQv⟩ :
        ↥(orthDerived Q)) = 1 := by
    apply Subtype.ext
    simpa using signChange_mul_self hF hv (a := b)
  have hone : (⟨signChange Q u v a, signChange_mem_orthDerived hQ hF hQv⟩ :
      ↥(orthDerived Q)) *
      (⟨signChange Q u v b, signChange_mem_orthDerived hQ hF hQv⟩ :
        ↥(orthDerived Q)) = 1 := by
    rw [hgh]
    exact hh2
  have hx : (⟨signChange Q u v a, signChange_mem_orthDerived hQ hF hQv⟩ *
      ⟨signChange Q u v b, signChange_mem_orthDerived hQ hF hQv⟩ : ↥(orthDerived Q)) *
      e a * (⟨signChange Q u v a, signChange_mem_orthDerived hQ hF hQv⟩ *
      ⟨signChange Q u v b, signChange_mem_orthDerived hQ hF hQv⟩) = (e a)⁻¹ := by
    simpa using signChange_pair_conj_self hQ hF hv hQv hab
  rw [hone] at hx
  exact coherentFrame_e_ne_inv hF hp a (by simpa using hx)

theorem signChange_pair_closure_eq (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hF : IsCoherentFrame Q p U e E u c t) {v : V}
    (hv : v ∈ polarPerp Q (⨆ j, U j)) (hQv : Q v ≠ 0) (hp : p = 3) (hab : a ≠ b) :
    (Subgroup.closure
      ({⟨signChange Q u v a, signChange_mem_orthDerived hQ hF hQv⟩,
        ⟨signChange Q u v b, signChange_mem_orthDerived hQ hF hQv⟩} :
        Set ↥(orthDerived Q)) : Set ↥(orthDerived Q)) =
      {1, ⟨signChange Q u v a, signChange_mem_orthDerived hQ hF hQv⟩,
        ⟨signChange Q u v b, signChange_mem_orthDerived hQ hF hQv⟩,
        ⟨signChange Q u v a, signChange_mem_orthDerived hQ hF hQv⟩ *
        ⟨signChange Q u v b, signChange_mem_orthDerived hQ hF hQv⟩} := by
  let g : ↥(orthDerived Q) :=
    ⟨signChange Q u v a, signChange_mem_orthDerived hQ hF hQv⟩
  let h : ↥(orthDerived Q) :=
    ⟨signChange Q u v b, signChange_mem_orthDerived hQ hF hQv⟩
  have hg2 : g * g = 1 := by
    apply Subtype.ext
    simpa [g] using signChange_mul_self hF hv (a := a)
  have hh2 : h * h = 1 := by
    apply Subtype.ext
    simpa [h] using signChange_mul_self hF hv (a := b)
  have hcomm : g * h = h * g := by
    apply Subtype.ext
    simpa [g, h] using signChange_comm hF hv hab
  have hg1 : g ≠ 1 := signChange_ne_one hQ hF hv hQv hp a
  have hh1 : h ≠ 1 := signChange_ne_one hQ hF hv hQv hp b
  have hne : g ≠ h := signChange_pair_ne hQ hF hv hQv hp hab
  have : Finite ↥(orthDerived Q) := by
    have : Finite V := Module.finite_of_finite F
    have : Finite (V ≃ₗ[F] V) :=
      Finite.of_injective (fun e : V ≃ₗ[F] V => (e : V → V))
        fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
    exact Subtype.finite
  simpa [g, h] using CFSG.GroupTheory.coe_closure_pair_eq hg2 hh2 hcomm hg1 hh1 hne

theorem signChange_not_centralizes (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hF : IsCoherentFrame Q p U e E u c t) {v : V}
    (hv : v ∈ polarPerp Q (⨆ j, U j)) (hQv : Q v ≠ 0) (hp : p = 3) (i : Fin k) :
    ¬ (∀ y ∈ E, (⟨signChange Q u v i, signChange_mem_orthDerived hQ hF hQv⟩ :
        ↥(orthDerived Q)) * y *
        (⟨signChange Q u v i, signChange_mem_orthDerived hQ hF hQv⟩ :
          ↥(orthDerived Q))⁻¹ = y) := by
  let g : ↥(orthDerived Q) :=
    ⟨signChange Q u v i, signChange_mem_orthDerived hQ hF hQv⟩
  have hg2 : g * g = 1 := by
    apply Subtype.ext
    simpa [g] using signChange_mul_self hF hv (a := i)
  have hg_inv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg2
  have hei : e i ∈ E := by
    rw [← hF.closure_eq]
    exact Subgroup.subset_closure ⟨i, rfl⟩
  intro hcent
  have hfix : g * e i * g⁻¹ = e i := hcent (e i) hei
  have hfix' : g * e i * g = e i := by simpa [hg_inv] using hfix
  exact coherentFrame_e_ne_inv hF hp i
    (hfix'.symm.trans (signChange_conj_self_subgroup hQ hF hv hQv i))

theorem signChange_pair_mul_not_centralizes (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hF : IsCoherentFrame Q p U e E u c t) {v : V}
    (hv : v ∈ polarPerp Q (⨆ j, U j)) (hQv : Q v ≠ 0) (hp : p = 3) (hab : a ≠ b) :
    ¬ (∀ y ∈ E, ((⟨signChange Q u v a, signChange_mem_orthDerived hQ hF hQv⟩ :
        ↥(orthDerived Q)) * ⟨signChange Q u v b, signChange_mem_orthDerived hQ hF hQv⟩) *
        y * ((⟨signChange Q u v a, signChange_mem_orthDerived hQ hF hQv⟩ :
          ↥(orthDerived Q)) * ⟨signChange Q u v b, signChange_mem_orthDerived hQ hF hQv⟩)⁻¹
          = y) := by
  let g : ↥(orthDerived Q) :=
    ⟨signChange Q u v a, signChange_mem_orthDerived hQ hF hQv⟩
  let h : ↥(orthDerived Q) :=
    ⟨signChange Q u v b, signChange_mem_orthDerived hQ hF hQv⟩
  have hg2 : g * g = 1 := by
    apply Subtype.ext
    simpa [g] using signChange_mul_self hF hv (a := a)
  have hh2 : h * h = 1 := by
    apply Subtype.ext
    simpa [h] using signChange_mul_self hF hv (a := b)
  have hcomm : g * h = h * g := by
    apply Subtype.ext
    simpa [g, h] using signChange_comm hF hv hab
  have hgh2 : (g * h) * (g * h) = 1 := by
    calc (g * h) * (g * h) = g * (h * g) * h := by group
      _ = g * (g * h) * h := by rw [← hcomm]
      _ = (g * g) * (h * h) := by group
      _ = 1 := by rw [hg2, hh2, one_mul]
  have hgh_inv : (g * h)⁻¹ = g * h := inv_eq_of_mul_eq_one_right hgh2
  have hghconj : (g * h) * e a * (g * h) = (e a)⁻¹ := by
    simpa [g, h] using signChange_pair_conj_self hQ hF hv hQv hab
  have hea : e a ∈ E := by
    rw [← hF.closure_eq]
    exact Subgroup.subset_closure ⟨a, rfl⟩
  intro hcent
  have hfix : g * h * e a * (g * h)⁻¹ = e a := hcent (e a) hea
  have hfix' : g * h * e a * (g * h) = e a := by simpa [hgh_inv] using hfix
  exact coherentFrame_e_ne_inv hF hp a (hfix'.symm.trans hghconj)

theorem signChange_pair_trivial_kernel (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hF : IsCoherentFrame Q p U e E u c t) {v : V}
    (hv : v ∈ polarPerp Q (⨆ j, U j)) (hQv : Q v ≠ 0) (hp : p = 3) (hab : a ≠ b) :
    ∀ x ∈ Subgroup.closure
      ({⟨signChange Q u v a, signChange_mem_orthDerived hQ hF hQv⟩,
        ⟨signChange Q u v b, signChange_mem_orthDerived hQ hF hQv⟩} :
        Set ↥(orthDerived Q)),
      (∀ y ∈ E, x * y * x⁻¹ = y) → x = 1 := by
  intro x hx hcent
  let g : ↥(orthDerived Q) :=
    ⟨signChange Q u v a, signChange_mem_orthDerived hQ hF hQv⟩
  let h : ↥(orthDerived Q) :=
    ⟨signChange Q u v b, signChange_mem_orthDerived hQ hF hQv⟩
  have hcases : (Subgroup.closure ({g, h} : Set ↥(orthDerived Q)) :
      Set ↥(orthDerived Q)) = {1, g, h, g * h} := by
    simpa [g, h] using signChange_pair_closure_eq hQ hF hv hQv hp hab
  change x ∈ (Subgroup.closure ({g, h} : Set ↥(orthDerived Q)) : Set _) at hx
  rw [hcases] at hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · rfl
  · exact absurd hcent (signChange_not_centralizes hQ hF hv hQv hp a)
  · exact absurd hcent (signChange_not_centralizes hQ hF hv hQv hp b)
  · exact absurd hcent (signChange_pair_mul_not_centralizes hQ hF hv hQv hp hab)

theorem four_dvd_ggAutomizer_signChange_pair (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hF : IsCoherentFrame Q p U e E u c t) {v : V}
    (hv : v ∈ polarPerp Q (⨆ j, U j)) (hQv : Q v ≠ 0) (hp : p = 3) (hab : a ≠ b)
    (J' : Subgroup ↥(orthDerived Q))
    (hga : (⟨signChange Q u v a, signChange_mem_orthDerived hQ hF hQv⟩ :
      ↥(orthDerived Q)) ∈ J')
    (hgb : (⟨signChange Q u v b, signChange_mem_orthDerived hQ hF hQv⟩ :
      ↥(orthDerived Q)) ∈ J') :
    4 ∣ Nat.card (ggAutomizer J' E) := by
  let g : ↥(orthDerived Q) :=
    ⟨signChange Q u v a, signChange_mem_orthDerived hQ hF hQv⟩
  let h : ↥(orthDerived Q) :=
    ⟨signChange Q u v b, signChange_mem_orthDerived hQ hF hQv⟩
  have hgJ : g ∈ J' := hga
  have hhJ : h ∈ J' := hgb
  have hgN : g ∈ Subgroup.normalizer (E : Set ↥(orthDerived Q)) :=
    signChange_mem_normalizer hQ hF hv hQv a
  have hhN : h ∈ Subgroup.normalizer (E : Set ↥(orthDerived Q)) :=
    signChange_mem_normalizer hQ hF hv hQv b
  have hg2 : g * g = 1 := by
    apply Subtype.ext
    simpa [g] using signChange_mul_self hF hv (a := a)
  have hh2 : h * h = 1 := by
    apply Subtype.ext
    simpa [h] using signChange_mul_self hF hv (a := b)
  have hcomm : g * h = h * g := by
    apply Subtype.ext
    simpa [g, h] using signChange_comm hF hv hab
  have hg1 : g ≠ 1 := signChange_ne_one hQ hF hv hQv hp a
  have hh1 : h ≠ 1 := signChange_ne_one hQ hF hv hQv hp b
  have hne : g ≠ h := signChange_pair_ne hQ hF hv hQv hp hab
  have hker := signChange_pair_trivial_kernel hQ hF hv hQv hp hab
  have : Finite ↥(orthDerived Q) := by
    have : Finite V := Module.finite_of_finite F
    have : Finite (V ≃ₗ[F] V) :=
      Finite.of_injective (fun e : V ≃ₗ[F] V => (e : V → V))
        fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
    exact Subtype.finite
  exact GGQ2Lin.ggQ2Lin_four_dvd_aut
    hgJ hhJ hgN hhN hg2 hh2 hcomm hg1 hh1 hne (by simpa [g, h] using hker)

end SignChangePair

end CFSG.StandardType

end
