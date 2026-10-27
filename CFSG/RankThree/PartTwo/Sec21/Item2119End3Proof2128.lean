module

public import CFSG.RankThree.PartTwo.Sec21.Item2119End2Proof2128
public import CFSG.RankThree.PartTwo.Sec21.Item2119End3Proof2128Tools
import CFSG.RankThree.PartTwo.Sec19.Step1911Proof
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)
open scoped commutatorElement

namespace Item2119End3Proof

theorem card_le_of_commute_of_extraspecial {P : Type*} [Group P] [Finite P]
    (hP : IsExtraspecialPGroup 3 P) (h243 : Nat.card P = 243) {B : Subgroup P}
    (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) : Nat.card B ≤ 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ3 : Nat.card (Subgroup.center P) = 3 := hP.2.2.2
  have hcomm : ∀ a b : P, ⁅a, b⁆ ∈ Subgroup.center P := by
    intro a b
    rw [← hP.2.1, _root_.commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
  by_contra hlt
  push Not at hlt
  by_cases htop : B = ⊤
  · have hZ : Subgroup.center P = ⊤ := by
      rw [eq_top_iff]
      intro a _
      rw [Subgroup.mem_center_iff]
      intro g
      exact hB g (htop ▸ Subgroup.mem_top g) a (htop ▸ Subgroup.mem_top a)
    rw [hZ, Subgroup.card_top, h243] at hZ3
    norm_num at hZ3
  obtain ⟨x, hxB⟩ : ∃ x, x ∉ B := by
    by_contra h
    push Not at h
    exact htop (eq_top_iff.mpr fun y _ => h y)
  have hdvd : Nat.card B ∣ 3 ^ 5 := by
    rw [show (3 : ℕ) ^ 5 = 243 by norm_num, ← h243]
    exact Subgroup.card_subgroup_dvd_card B
  obtain ⟨k, hk, hBk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  have hB81 : Nat.card B = 81 := by
    interval_cases k
    · rw [hBk] at hlt; norm_num at hlt
    · rw [hBk] at hlt; norm_num at hlt
    · rw [hBk] at hlt; norm_num at hlt
    · rw [hBk] at hlt; norm_num at hlt
    · rw [hBk]; norm_num
    · exfalso
      exact htop (Subgroup.eq_top_of_card_eq B (by rw [hBk, h243]; norm_num))
  have hsup : B ⊔ Subgroup.zpowers x = ⊤ := by
    have hne : B ≠ B ⊔ Subgroup.zpowers x := by
      intro h
      apply hxB
      rw [h]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    have h3 := card_eq_three_mul_of_lt le_sup_left hne
      (by rw [hB81, show (3 : ℕ) * 81 = 243 by norm_num, ← h243]
          exact Subgroup.card_subgroup_dvd_card _)
    exact Subgroup.eq_top_of_card_eq _ (by rw [h3, hB81, h243])
  let f : B →* P :=
    { toFun := fun b => ⁅(b : P), x⁆
      map_one' := by simp
      map_mul' := fun b₁ b₂ => by
        change ⁅(b₁ : P) * b₂, x⁆ = ⁅(b₁ : P), x⁆ * ⁅(b₂ : P), x⁆
        have hc := Subgroup.mem_center_iff.mp (hcomm (b₂ : P) x)
        have e1 : ⁅(b₁ : P) * b₂, x⁆ = (b₁ : P) * ⁅(b₂ : P), x⁆ * (x * (b₁ : P)⁻¹ * x⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e1, hc (b₁ : P), hc ⁅(b₁ : P), x⁆]
        simp only [commutatorElement_def]
        group }
  have hrange : Nat.card f.range ≤ 3 := by
    rw [← hZ3]
    refine Subgroup.card_le_of_le ?_
    rintro _ ⟨b, rfl⟩
    exact hcomm _ _
  have hker : Nat.card f.ker ≤ 3 := by
    rw [← hZ3]
    let F : f.ker → Subgroup.center P := fun b => ⟨((b : B) : P), by
      have hb : ⁅((b : B) : P), x⁆ = 1 := b.2
      rw [commutatorElement_eq_one_iff_mul_comm] at hb
      have hle : B ⊔ Subgroup.zpowers x ≤ Subgroup.centralizer {((b : B) : P)} := by
        refine sup_le (fun y hy => ?_) ?_
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact (hB _ (b : B).2 y hy).symm
        · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
          exact hb.symm
      rw [hsup] at hle
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top g))⟩
    refine Nat.card_le_card_of_injective F fun b₁ b₂ h => ?_
    have h' : ((b₁ : B) : P) = ((b₂ : B) : P) := congrArg (fun w : Subgroup.center P => (w : P)) h
    exact Subtype.ext (Subtype.ext h')
  have hcard := Subgroup.index_mul_card f.ker
  rw [Subgroup.index_ker] at hcard
  have h9 : Nat.card B ≤ 9 := by
    rw [← hcard]
    calc Nat.card f.range * Nat.card f.ker ≤ 3 * 3 := Nat.mul_le_mul hrange hker
      _ = 9 := by norm_num
  omega

variable {G : Type} [Group G] [Finite G]

theorem inf_centralizer_eq {Q F : Subgroup G} (hQ : IsExtraspecialPGroup 3 Q)
    (h243 : Nat.card Q = 243) (hFQ : F ≤ Q) (hF27 : Nat.card F = 27)
    (hFc : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x) : Q ⊓ Subgroup.centralizer (F : Set G) = F := by
  refine le_antisymm ?_ (le_inf hFQ fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => hFc y hy x hx)
  intro y ⟨hyQ, hyC⟩
  by_contra hyF
  set B := F ⊔ Subgroup.zpowers y with hB
  have hBQ : B ≤ Q := sup_le hFQ (Subgroup.zpowers_le.mpr hyQ)
  have hFCF : F ≤ Subgroup.centralizer (F : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun z hz => hFc z hz x hx
  have hZCF : Subgroup.zpowers y ≤ Subgroup.centralizer (F : Set G) :=
    Subgroup.zpowers_le.mpr hyC
  have hFCZ : F ≤ Subgroup.centralizer (Subgroup.zpowers y : Set G) :=
    Subgroup.le_centralizer_iff.mp hZCF
  have hZCZ : Subgroup.zpowers y ≤ Subgroup.centralizer (Subgroup.zpowers y : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_zpow (Commute.refl y) j i).eq
  have hBC : B ≤ Subgroup.centralizer (B : Set G) := by
    refine sup_le ?_ ?_
    · exact Subgroup.le_centralizer_iff.mp (sup_le hFCF hZCF)
    · exact Subgroup.le_centralizer_iff.mp (sup_le hFCZ hZCZ)
  have hlt : F < B := by
    refine lt_of_le_of_ne le_sup_left fun h => hyF ?_
    rw [h]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hB27 : 27 < Nat.card B := hF27 ▸ Subgroup.card_lt_of_lt hlt
  have hle := card_le_of_commute_of_extraspecial hQ h243 (B := B.subgroupOf Q) (by
    intro a ha b hb
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hBC (Subgroup.mem_subgroupOf.mp hb)) _
      (Subgroup.mem_subgroupOf.mp ha))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBQ).toEquiv] at hle
  omega

theorem not_dvd_card_of_lBar {Le L : Subgroup G} (eLe : lBar Le ≃* lBar L)
    (eL : lBar L ≃* projSL 3 (GaloisField 2 2)) : ¬ 27 ∣ Nat.card Le := by
  have hL34 : Nat.card (projSL 3 (GaloisField 2 2)) = 20160 := by
    have h1 := Sec19.Step1911Proof.card_projSL (m := 3) (e := 2) (by norm_num) (by norm_num)
    have h2 := Sec19.Step1911Proof.ordA_two_mul_gcd 2
    rw [show (3 : ℕ) - 1 = 2 by norm_num] at h1
    rw [← h1] at h2
    norm_num at h2
    omega
  have hbar : Nat.card (lBar Le) = 20160 := by
    rw [Nat.card_congr (eLe.trans eL).toEquiv, hL34]
  have hθ : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 Le) :=
    three_not_dvd_card_aschbacherSolvableCore
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 Le)
  intro h27
  have hcop : Nat.Coprime 27 (Nat.card (aschbacherSolvableCore 3 Le)) := by
    rw [show (27 : ℕ) = 3 ^ 3 by norm_num]
    exact Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ)
  have h27' : 27 ∣ Nat.card (lBar Le) * Nat.card (aschbacherSolvableCore 3 Le) := by
    rw [← hcard]
    exact h27
  have h1 := hcop.dvd_of_dvd_mul_right h27'
  rw [hbar] at h1
  norm_num at h1

omit [Finite G] in
theorem autIn_le_of_le {H K X : Subgroup G}
    (h : H ⊓ Subgroup.normalizer (X : Set G) ≤ K) : Sec4.autIn H X ≤ Sec4.autIn K X := by
  intro σ hσ
  obtain ⟨g, hN, hg, rfl⟩ := Sec4.mem_autIn_iff.mp hσ
  exact Sec4.mem_autIn_iff.mpr ⟨g, hN, h ⟨hg, hN⟩, rfl⟩

omit [Finite G] in
theorem autIn_sup {H K X : Subgroup G} (hH : H ≤ Subgroup.normalizer (X : Set G))
    (hK : K ≤ Subgroup.normalizer (X : Set G)) :
    Sec4.autIn (H ⊔ K) X = Sec4.autIn H X ⊔ Sec4.autIn K X := by
  have hHK : H ⊔ K ≤ Subgroup.normalizer (X : Set G) := sup_le hH hK
  simp only [Sec4.autIn, inf_eq_left.mpr hH, inf_eq_left.mpr hK, inf_eq_left.mpr hHK]
  rw [Subgroup.subgroupOf_sup hH hK, Subgroup.map_sup]

omit [Finite G] in
theorem card_autIn_mul_card_inf {U X : Subgroup G} (hU : U ≤ Subgroup.normalizer (X : Set G)) :
    Nat.card (Sec4.autIn U X) * Nat.card (U ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) =
      Nat.card U := by
  set f := X.normalizerMonoidHom.comp (Subgroup.inclusion hU) with hf
  have hrange : Sec4.autIn U X = f.range := by
    ext σ
    rw [Sec4.mem_autIn_iff, MonoidHom.mem_range]
    constructor
    · rintro ⟨h, hN, hH, rfl⟩
      exact ⟨⟨h, hH⟩, rfl⟩
    · rintro ⟨u, rfl⟩
      exact ⟨u, hU u.2, u.2, rfl⟩
  have hker : f.ker = (Subgroup.centralizer (X : Set G)).subgroupOf U := by
    ext u
    rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
      Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    rfl
  have hcardker :
      Nat.card f.ker = Nat.card (U ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) := by
    rw [hker, ← Subgroup.inf_subgroupOf_left]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [hrange, ← hcardker, ← Subgroup.index_ker, Subgroup.index_mul_card]

omit [Finite G] in
theorem trivOnQuot_eq_fixQuot (X B : Subgroup G) : trivOnQuot X B = fixQuot (B.subgroupOf X) :=
  rfl

omit [Finite G] in
theorem mem_zpowers_subtype {X : Subgroup G} {d : G} (hdX : d ∈ X) {y : X}
    (hy : (y : G) ∈ Subgroup.zpowers d) : y ∈ Subgroup.zpowers (⟨d, hdX⟩ : X) := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext ?_⟩
  rw [Subgroup.coe_zpow, hk]

end Item2119End3Proof

open Item2119End3Proof Item2119End2Proof

theorem item2128Card : Item2128Card := by
  intro G _ _ A E U c L d U₀ a X hE h23 h24 Lf hLf h26 F hF h27 hQ hQX e he hed hYN hYtriv hdF
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨eL34⟩ := h26
  obtain ⟨hFe, hF27, -, -, ⟨eQ8⟩⟩ := hF e he hed
  obtain ⟨-, -, -, ⟨eLe⟩, hdLe, -⟩ := hLf e he hed
  obtain ⟨hQS, -, hQstar, -, -⟩ := hQ
  obtain ⟨hQext, hQ243, -⟩ := hQX
  set Q := q2127Of A d F with hQdef
  set Le := Lf e with hLedef
  set Fe := F e with hFedef
  have hAe : IsElemAbelian 3 A := hE.cfg.pair.mem_S.1.1
  have hdA : d ∈ A := hE.mem_d.1
  have hd1 : d ≠ 1 := hE.ne_one_d
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  have hFc : ∀ x ∈ Fe, ∀ y ∈ Fe, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hFe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hFQ : Fe ≤ Q := le_sup_right.trans (le_iSup₂_of_le e ⟨he, hed⟩ le_rfl)
  have hQN : Q ≤ Subgroup.normalizer (Fe : Set G) := le_sup_right.trans hYN
  have hLN : Le ⊓ Subgroup.normalizer (Fe : Set G) ≤ Subgroup.normalizer (Fe : Set G) :=
    inf_le_right
  have hQNA : Q ≤ Subgroup.normalizer (A : Set G) := by
    obtain ⟨S, hS⟩ := hQS
    rw [← hS]
    exact Subgroup.map_subtype_le _
  have hdc : ∀ q ∈ Q, q * d * q⁻¹ = d := by
    intro q hq
    have hmem : A.normalizerMonoidHom ⟨q, hQNA hq⟩ ∈ starOf A Q :=
      ⟨⟨q, hQNA hq⟩, Subgroup.mem_subgroupOf.mpr hq, rfl⟩
    rw [hQstar] at hmem
    exact congrArg Subtype.val ((mem_fixOn_iff.mp hmem.2) ⟨d, hdA⟩ (Subgroup.mem_zpowers d))
  have hcommQ := comm_mem_zpowers hQext (hFQ hdF) hd1 hd3 hdc
  have hVc : ∀ x y : Fe, x * y = y * x := fun x y => Subtype.ext (hFc x x.2 y y.2)
  have hV3 : ∀ x : Fe, x ^ 3 = 1 := fun x => Subtype.ext (by simpa using hFe.2 x x.2)
  have hT : Le.subgroupOf Fe ≠ ⊤ := by
    intro h
    have hle : Fe ≤ Le := by
      intro x hx
      have hx' : (⟨x, hx⟩ : Fe) ∈ Le.subgroupOf Fe := by rw [h]; exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.mp hx'
    apply not_dvd_card_of_lBar eLe eL34
    rw [← hF27]
    exact Subgroup.card_dvd_of_le hle
  have hLL : Sec4.autIn (Le ⊓ Subgroup.normalizer (Fe : Set G)) Fe = Sec4.autIn Le Fe := by
    simp only [Sec4.autIn, inf_assoc, inf_idem]
  have hAY : Sec4.autIn (y2128Of Le Fe Q) Fe = Sec4.autIn Le Fe ⊔ Sec4.autIn Q Fe := by
    rw [show y2128Of Le Fe Q = (Le ⊓ Subgroup.normalizer (Fe : Set G)) ⊔ Q from rfl,
      autIn_sup hLN hQN, hLL]
  have hQ8T : Sec4.autIn Le Fe ≤ fixQuot (Le.subgroupOf Fe) := by
    rw [← trivOnQuot_eq_fixQuot]
    exact (le_sup_left.trans hAY.symm.le).trans hYtriv
  have hQ9 : ∀ φ ∈ Sec4.autIn Q Fe, ∀ x : Fe, x⁻¹ * φ x ∈ Subgroup.zpowers (⟨d, hdF⟩ : Fe) := by
    intro φ hφ x
    obtain ⟨q, hqN, hqQ, rfl⟩ := Sec4.mem_autIn_iff.mp hφ
    apply mem_zpowers_subtype hdF
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Sec4.normalizerMonoidHom_apply_coe]
    exact hcommQ x (hFQ x.2) q hqQ
  have hQ9d : ∀ φ ∈ Sec4.autIn Q Fe, φ ⟨d, hdF⟩ = ⟨d, hdF⟩ := by
    intro φ hφ
    obtain ⟨q, hqN, hqQ, rfl⟩ := Sec4.mem_autIn_iff.mp hφ
    apply Subtype.ext
    rw [Sec4.normalizerMonoidHom_apply_coe]
    exact hdc q hqQ
  have hQ9card : Nat.card (Sec4.autIn Q Fe) = 9 := by
    have h1 := card_autIn_mul_card_inf hQN
    rw [inf_centralizer_eq hQext hQ243 hFQ hF27 hFc, hF27, hQ243] at h1
    norm_num at h1
    omega
  have hT9 : Nat.card (Le.subgroupOf Fe) = 9 := card_eq_nine hV3 hF27 hT eQ8 hQ8T
  have hdT : (⟨d, hdF⟩ : Fe) ∈ Le.subgroupOf Fe := Subgroup.mem_subgroupOf.mpr hdLe
  have hd1' : (⟨d, hdF⟩ : Fe) ≠ 1 := fun h => hd1 (congrArg Subtype.val h)
  rw [hAY]
  exact card_sup_eq hVc hV3 hF27 hT9 hdT hd1' eQ8 hQ8T hQ9 hQ9d hQ9card

theorem item2128 : Item2128 :=
  item2128_of item2128Card

end CFSG.RankThree.PartTwo.Sec21
