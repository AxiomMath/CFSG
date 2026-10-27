module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P218s
public import CFSG.LocalAnalysis.UniquenessCase.UC22S218GLift
import CFSG.LocalAnalysis.UniquenessCase.UC22S218GAbs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Facts13
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsFifteenTorus
import CFSG.LocalAnalysis.UniquenessCase.UC1K31
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rs
import CFSG.LocalAnalysis.UniquenessCase.UC6S846g
import CFSG.LocalAnalysis.UniquenessCase.UC6Syl
import CFSG.RankThree.PartOne.S12.Sec15Frattini

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)

variable {G : Type} [Group G] [Finite G]

theorem not_dvd_card_solvableRadical {L : Subgroup G} (hq : CFSG.Open.IsQuasisimple (Bar2 L))
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hZ : ¬ ℓ ∣ Nat.card (center (Bar2 L))) :
    ¬ ℓ ∣ Nat.card (CFSG.solvableRadical ↥L) := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  intro hdvd
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' ℓ hdvd
  have hyR : ((y : ↥(CFSG.solvableRadical ↥L)) : ↥L) ∈ CFSG.solvableRadical ↥L := y.2
  have hw : (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) (y : ↥L) ∈ center (Bar2 L) := by
    rw [← uc22p21k_map_solvableRadical_eq_center hq]
    exact mem_map_of_mem _ hyR
  have hordy : orderOf ((y : ↥(CFSG.solvableRadical ↥L)) : ↥L) = ℓ := by
    rw [← hy]
    exact (Subgroup.orderOf_coe y)
  have hd : orderOf ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)) (y : ↥L)) ∣ ℓ :=
    hordy ▸ orderOf_map_dvd _ _
  rcases (Nat.dvd_prime hℓ).1 hd with h1 | h1
  ·
    have h2 : (y : ↥L) ∈ CFSG.pCore 2 ↥L :=
      (QuotientGroup.eq_one_iff _).1 (orderOf_eq_one_iff.1 h1)
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨_, h2⟩
    have h3 : orderOf ((y : ↥(CFSG.solvableRadical ↥L)) : ↥L) ∣ 2 ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      exact congrArg Subtype.val hk
    rw [hordy] at h3
    exact hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 (hℓ.dvd_of_dvd_pow h3))
  ·
    have h2 := Subgroup.orderOf_dvd_natCard (center (Bar2 L)) hw
    rw [h1] at h2
    exact hZ h2

theorem two_le_pRank_inf_of_frattini {p : ℕ} (hp : p.Prime) {L M B : Subgroup G} (hLM : L ≤ M)
    [(L.subgroupOf M).Normal] (hfr : ∀ m ∈ M, ∃ l ∈ L, l⁻¹ * m ∈ B)
    (hcop : ∀ h ∈ L, h ∈ B → h ^ p = 1 → h = 1)
    (hrank : CFSG.Open.pRank p L + 2 ≤ CFSG.Open.pRank p M) :
    2 ≤ CFSG.Open.pRank p (M ⊓ B) := by
  have h1 := uc22p218s_pRank_top_le_add hp (L.subgroupOf M) ((M ⊓ B).subgroupOf M)
    (fun m => by
      obtain ⟨l, hlL, hl⟩ := hfr m m.2
      refine ⟨⟨l, hLM hlL⟩⁻¹ * m, mem_subgroupOf.2 ⟨M.mul_mem (M.inv_mem (hLM hlL)) m.2, hl⟩, ?_⟩
      rw [mul_inv_cancel_right, mem_subgroupOf]
      exact L.inv_mem hlL)
    (fun c hcC hcN hcp => Subtype.ext (hcop _ (mem_subgroupOf.1 hcN)
      (mem_inf.1 (mem_subgroupOf.1 hcC)).2 (by simpa using congrArg Subtype.val hcp)))
  rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup M, UCK.K31.pRank_subgroupOf_eq hp.one_lt hLM,
    UCK.K31.pRank_subgroupOf_eq hp.one_lt (inf_le_left : M ⊓ B ≤ M)] at h1
  omega

theorem le_centralizer_of_facts {Tor Out : ℕ → Prop} {L M R E : Subgroup G} {n s r : ℕ}
    (hF : TorusFacts218 (BarInf L) n Tor Out) (hs : Odd s) (hsn : s ∣ n) (hr : r.Prime)
    (hr2 : r ≠ 2) (hrs : r ∣ 2 ^ s - 1) (hrK : ¬ r ∣ Nat.card (CFSG.solvableRadical ↥L))
    (hML : M ≤ normalizer (L : Set G)) (hR : IsSylowOf r R M) (hER : E ≤ R) (hEL : E ≤ L)
    (hEr : ∀ e ∈ E, e ^ r = 1) : E ≤ centralizer (R : Set G) := by
  have : Fact r.Prime := ⟨hr⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRp : IsPGroup r R := hR.isPGroup
  have hY2 : ¬ r ∣ Nat.card (Sylow 2 ↥L) :=
    not_dvd_card_sylow_of_quotient (CFSG.solvableRadical ↥L) hr hrK
      (hF.not_dvd_card_sylow hs hsn hr hrs)
  obtain ⟨S', hS'⟩ := uc22p218s_exists_sylow_le_normalizer hr Nat.prime_two hRp
    (hR.le.trans hML) hY2
  obtain ⟨S, hS, hRS⟩ : ∃ S : Subgroup G, IsSylowOf 2 S L ∧ R ≤ normalizer (S : Set G) :=
    ⟨_, ⟨S', rfl⟩, hS'⟩
  have hRK : R ≤ normalizer (OInf L : Set G) :=
    (hR.le.trans hML).trans (normalizer_le_normalizer_OInf L)
  have hRSK : R ≤ normalizer ((S ⊔ OInf L : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_sup_of_mem (hRS hx) (hRK hx)
  obtain ⟨b, hb⟩ := hRp.exists_card_eq
  have hdisj : Disjoint R (S ⊔ OInf L) := by
    refine Subgroup.disjoint_of_coprime_natCard ?_
    rw [hb]
    exact Nat.Coprime.pow_left b
      ((Nat.Prime.coprime_iff_not_dvd hr).2 (not_dvd_card_sup_OInf hS hr hr2 hrK))
  intro e he
  rw [mem_centralizer_iff]
  intro x hx
  obtain ⟨a, ha⟩ := hRp ⟨x, hx⟩
  have hxa : x ^ r ^ a = 1 := congrArg Subtype.val ha
  obtain ⟨k, hk⟩ := exists_pow_conj_mem hS hF (hML (hR.le hx)) (hRSK hx)
    (hr.odd_of_ne_two hr2).pow hxa
  have hxE : ∀ f ∈ E, x * f * x⁻¹ = f ^ k := by
    intro f hf
    have h1 := hk f (hEL hf) (hRSK (hER hf))
    have h2 : x * f * x⁻¹ * (f ^ k)⁻¹ ∈ R :=
      mul_mem (mul_mem (mul_mem hx (hER hf)) (inv_mem hx)) (inv_mem (pow_mem (hER hf) k))
    exact mul_inv_eq_one.1 (disjoint_def.1 hdisj h2 h1)
  have h3 := uc22p218s_conj_eq_self_of_pow hEr hxE hxa e he
  calc x * e = x * e * x⁻¹ * x := by group
    _ = e * x := by rw [h3]

theorem not_stronglyEmbedded_of_facts {Tor Out : ℕ → Prop} (D : Data G) (Ch : Choice2011 G)
    (h211 : S21_1 D Ch) (hH : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G} (hLM : L ≤ D.M)
    (hML : D.M ≤ normalizer (L : Set G)) {n s r : ℕ} (hF : TorusFacts218 (BarInf L) n Tor Out)
    (hs : Odd s) (hsn : s ∣ n) (hr : r.Prime) (hr2 : r ≠ 2) (hrs : r ∣ 2 ^ s - 1) :
    ¬ IsStronglyPEmbedded r D.M := by
  intro hsp
  have : Fact r.Prime := ⟨hr⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hyL, hy, hyT⟩ := exists_orderOf_eq_mem_normalizer hF D.sylowM.isPGroup
    (D.sylowM.le.trans hML) (D.sylowM.inf_of_le_normalizer hLM hML) hs hsn hrs
  have hyp : IsPGroup r (zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy, pow_one])
  have hy1 : zpowers y ≠ ⊥ := by
    intro h
    rw [zpowers_eq_bot.1 h, orderOf_one] at hy
    exact hr.one_lt.ne hy
  exact uc22p218s_false_of_le_normalizer D Ch h211 hH c hr hr2 hy
    (uc22p22r_mem_uniqueSet_of_sp D hr hsp ((zpowers_le.2 hyL).trans hLM) hyp hy1) hyT

theorem normal_of_facts {Tor Out : ℕ → Prop} (D : Data G) (Ch : Choice2011 G)
    (hSg : UC6S846.SigmaStd D) (h211 : S21_1 D Ch) (hH : H1930 D) (c : Ctx21 D Ch)
    {L : Subgroup G} (hL : L ∈ calC D.M) {n : ℕ} (hF : TorusFacts218 (BarInf L) n Tor Out)
    (hZ : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card (center (Bar2 L)) → ¬ Tor ℓ ∧ ¬ Out ℓ)
    (hn : ¬ IsPowTwo n) : (L.subgroupOf D.M).Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLM : L ≤ D.M := hL.1.le
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hLM]
  by_contra hML
  obtain ⟨s, hs, hs1, hsn⟩ := PartTwo.s13_exists_odd_divisor hn
  have hs3 : 3 ≤ s := by
    obtain ⟨k, rfl⟩ := hs
    omega
  have h8 : 8 ≤ 2 ^ s :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs3
  obtain ⟨r, hr, hrs⟩ := Nat.exists_prime_and_dvd (show 2 ^ s - 1 ≠ 1 by omega)
  have : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := uc22p218c_ne_two_of_dvd (by omega) hrs
  have hZr : ¬ r ∣ Nat.card (center (Bar2 L)) := fun h =>
    (hZ r hr h).1 (hF.tor_of_dvd hs hsn hr hrs)
  have hrK : ¬ r ∣ Nat.card (CFSG.solvableRadical ↥L) :=
    not_dvd_card_solvableRadical hL.2.2 hr hr2 hZr
  obtain ⟨E, hEL, hEel, hEc⟩ := CFSG.SectionRank.exists_pRank hr.one_lt L
  rw [pRank_eq_pRank_barInf hr hrK, hF.pRank_eq_two hs hsn hr hrs] at hEc
  have h4 : 4 ≤ CFSG.Open.pRank r D.M := by
    have := UC6S846.calCRankTwice D.M L hL hML r hr hr2 hZr E hEL hEel 2 hEc
    omega
  have hsp : IsStronglyPEmbedded r D.M :=
    UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hL) (hSg.four_mem r hr hr2 h4)
  have hT₁ : IsPGroup 2 (D.T ⊓ normalizer (L : Set G) : Subgroup G) :=
    D.sylowM.isPGroup.to_le inf_le_left
  have hTL : IsSylowOf 2 ((D.T ⊓ normalizer (L : Set G) : Subgroup G) ⊓ L) L := by
    rw [inf_assoc, inf_eq_right.2 (le_normalizer : L ≤ normalizer (L : Set G))]
    exact uc22p2214_isSylowOf_inf D.sylowM hL.1
  obtain ⟨y, hyL, hy, hyN⟩ :=
    exists_orderOf_eq_mem_normalizer hF hT₁ inf_le_right hTL hs hsn hrs
  obtain ⟨x, hxcl, hx, hxN⟩ := exists_mem_conjClosure_orderOf_mem_normalizer D.sylowM hL hr hr2
    hZr ⟨y, hyL, hy, zpowers_le.1 hyN⟩
  have hclM : conjClosure D.M L ≤ D.M := by
    refine iSup₂_le fun K hK => ?_
    obtain ⟨g, hg, rfl⟩ := hK
    rintro _ ⟨z, hz, rfl⟩
    simpa [MulAut.conj_apply] using D.M.mul_mem (D.M.mul_mem hg (hLM hz)) (D.M.inv_mem hg)
  have hxp : IsPGroup r (zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  have hx1 : zpowers x ≠ ⊥ := by
    intro h
    rw [zpowers_eq_bot.1 h, orderOf_one] at hx
    exact hr.one_lt.ne hx
  exact uc22p218s_false_of_le_normalizer D Ch h211 hH c hr hr2 hx
    (uc22p22r_mem_uniqueSet_of_sp D hr hsp ((zpowers_le.2 hxcl).trans hclM) hxp hx1)
    (zpowers_le.2 hxN)

theorem exists_pair_of_tor {Tor Out : ℕ → Prop} {L : Subgroup G} {n s p r : ℕ}
    (hF : TorusFacts218 (BarInf L) n Tor Out) (hs : Odd s) (hsn : s ∣ n) (hr : r.Prime)
    (hrs : r ∣ 2 ^ s - 1) (hp : p.Prime) (hTor : Tor p) (hpr : p ≠ r)
    (hpK : ¬ p ∣ Nat.card (CFSG.solvableRadical ↥L))
    (hrK : ¬ r ∣ Nat.card (CFSG.solvableRadical ↥L)) :
    ∃ E Q : Subgroup G, E ≤ L ∧ IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧ Q ≤ L ∧
      IsElemAbelian p Q ∧ Nat.card Q = p ^ 2 ∧ ∀ x ∈ Q, ∃ k : ℕ, ∀ e ∈ E, x * e * x⁻¹ = e ^ k := by
  obtain ⟨E₁, Q₁, hE₁, hE₁c, hQ₁, hQ₁c, hpow₁⟩ := hF.exists_pair hs hsn hr hrs hp hTor hpr
  obtain ⟨E₂, Q₂, hE₂, hE₂c, hQ₂, hQ₂c, hpow₂⟩ :=
    exists_pair_lift (CFSG.solvableRadical ↥L) hp hr hpr hpK hrK hE₁ hE₁c hQ₁ hQ₁c hpow₁
  refine ⟨E₂.map L.subtype, Q₂.map L.subtype, Subgroup.map_subtype_le E₂, hE₂.map _, ?_,
    Subgroup.map_subtype_le Q₂, hQ₂.map _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective L.subtype_injective, hE₂c]
  · rw [Subgroup.card_map_of_injective L.subtype_injective, hQ₂c]
  · rintro _ ⟨q, hq, rfl⟩
    obtain ⟨k, hk⟩ := hpow₂ q hq
    refine ⟨k, ?_⟩
    rintro _ ⟨e, he, rfl⟩
    have h := congrArg (fun z : ↥L => (z : G)) (hk e he)
    simpa using h

theorem exists_pair_of_out {Tor Out : ℕ → Prop} {L M : Subgroup G} {n s p r : ℕ} (hLM : L ≤ M)
    [(L.subgroupOf M).Normal] (hF : TorusFacts218 (BarInf L) n Tor Out) (hs : Odd s)
    (hsn : s ∣ n) (hp : p.Prime) (hp2 : p ≠ 2) (hOut : Out p)
    (hpK : ¬ p ∣ Nat.card (CFSG.solvableRadical ↥L)) (hr : r.Prime) (hr2 : r ≠ 2)
    (hrs : r ∣ 2 ^ s - 1) (hrK : ¬ r ∣ Nat.card (CFSG.solvableRadical ↥L)) (hpr : p ≠ r)
    (hrank : CFSG.Open.pRank p L + 2 ≤ CFSG.Open.pRank p M) :
    ∃ E Q : Subgroup G, E ≤ L ∧ IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧ Q ≤ M ∧
      IsElemAbelian p Q ∧ Nat.card Q = p ^ 2 ∧ ∀ x ∈ Q, ∃ k : ℕ, ∀ e ∈ E, x * e * x⁻¹ = e ^ k := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact r.Prime := ⟨hr⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hML : M ≤ normalizer (L : Set G) := le_normalizer_of_normal_subgroupOf hLM
  have hMK : M ≤ normalizer (OInf L : Set G) := hML.trans (normalizer_le_normalizer_OInf L)
  have hrL : CFSG.Open.pRank r L = 2 := by
    rw [pRank_eq_pRank_barInf hr hrK, hF.pRank_eq_two hs hsn hr hrs]
  obtain ⟨E₀, hE₀L, hE₀el, hE₀c⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank hr hrL.ge
  obtain ⟨S', hS'⟩ := uc22p218s_exists_sylow_le_normalizer hr Nat.prime_two hE₀el.isPGroup
    (hE₀L.trans le_normalizer)
    (not_dvd_card_sylow_of_quotient (CFSG.solvableRadical ↥L) hr hrK
      (hF.not_dvd_card_sylow hs hsn hr hrs))
  obtain ⟨S, hS, hE₀S⟩ : ∃ S : Subgroup G, IsSylowOf 2 S L ∧ E₀ ≤ normalizer (S : Set G) :=
    ⟨_, ⟨S', rfl⟩, hS'⟩
  have hE₀SK : E₀ ≤ normalizer ((S ⊔ OInf L : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_sup_of_mem (hE₀S hx) (le_normalizer_OInf L (hE₀L hx))
  obtain ⟨Q, hQ, hQel, hQc⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hp
    (two_le_pRank_inf_of_frattini hp hLM (B := normalizer ((S ⊔ OInf L : Subgroup G) : Set G))
      (fun m hm => by
        obtain ⟨l, hlL, hl⟩ :=
          CFSG.RankThree.PartOne.Sec15Frattini.exists_mem_normalizer_of_isSylowOf hS (hML hm)
        exact ⟨l, hlL, mem_normalizer_sup_of_mem hl
          (mul_mem (inv_mem (le_normalizer_OInf L hlL)) (hMK hm))⟩)
      (fun h hhL hhS hhp => eq_one_of_pow_eq_one_of_facts hS hF hp hp2 hOut hpK hhL hhS hhp)
      hrank)
  have hQM : Q ≤ M := hQ.trans inf_le_left
  have hQS : Q ≤ normalizer ((S ⊔ OInf L : Subgroup G) : Set G) := hQ.trans inf_le_right
  have hpow : ∀ x ∈ Q, ∃ k : ℕ, ∀ h ∈ L, h ∈ normalizer ((S ⊔ OInf L : Subgroup G) : Set G) →
      x * h * x⁻¹ * (h ^ k)⁻¹ ∈ S ⊔ OInf L := fun x hx =>
    exists_pow_conj_mem hS hF (hML (hQM hx)) (hQS hx) (hp.odd_of_ne_two hp2) (hQel.2 x hx)
  obtain ⟨E, hEL, hEel, hEc, hEpow⟩ := exists_pow_conj_of_coprime (L := L)
    (S := S ⊔ OInf L) hp hr hpr (sup_le hS.le (OInf_le L))
    (not_dvd_card_sup_OInf hS hr hr2 hrK) (not_dvd_card_sup_OInf hS hp hp2 hpK) hE₀L hE₀SK hE₀el
    hE₀c hQel hQS hpow
  exact ⟨E, Q, hEL, hEel, hEc, hQM, hQel, hQc, hEpow⟩

theorem stronglyEmbedded_of_torus_of_facts {Tor Out : ℕ → Prop} (D : Data G)
    (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hML : D.M ≤ normalizer (L : Set G)) {n s p r : ℕ} (hF : TorusFacts218 (BarInf L) n Tor Out)
    (hs : Odd s) (hsn : s ∣ n) (hp : p.Prime) (h76 : Conclusion76 D.M p) (hr : r.Prime)
    (hr2 : r ≠ 2) (hrs : r ∣ 2 ^ s - 1) (hrK : ¬ r ∣ Nat.card (CFSG.solvableRadical ↥L))
    (hrσ : r ∉ D.sig) {E Q : Subgroup G} (hEL : E ≤ L) (hEel : IsElemAbelian r E)
    (hEc : Nat.card E = r ^ 2) (hQM : Q ≤ D.M) (hQel : IsElemAbelian p Q)
    (hQc : Nat.card Q = p ^ 2) (hpow : ∀ x ∈ Q, ∃ k : ℕ, ∀ e ∈ E, x * e * x⁻¹ = e ^ k) :
    IsStronglyPEmbedded r D.M := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact r.Prime := ⟨hr⟩
  have hns := UC6S846.not_solvable_of_mem_calC hL
  have hEM : E ≤ D.M := hEL.trans hL.1.le
  have hE1 : E ≠ ⊥ := by
    rintro rfl
    rw [card_bot] at hEc
    exact (Nat.one_lt_pow two_ne_zero hr.one_lt).ne hEc
  obtain ⟨x, hxQ, hx1, hxC⟩ := uc22p218s_exists_mem_centralizer hp hr hQel hQc hEel hE1 hpow
  have hxle : zpowers x ≤ D.M ⊓ centralizer (E : Set G) := zpowers_le.2 ⟨hQM hxQ, hxC⟩
  have hpos : 1 ≤ CFSG.Open.pRank p (D.M ⊓ centralizer (E : Set G)) :=
    UC6S846.le_pRank' hp hxle (isElemAbelian_zpowers (hQel.2 x hxQ))
      (by rw [Nat.card_zpowers, orderOf_eq_prime (hQel.2 x hxQ) hx1, pow_one])
  have hXN : ∀ X : Subgroup G, X ≤ E → Nat.card X = r →
      1 < CFSG.Open.pRank p (D.M ⊓ normalizer (X : Set G)) := by
    intro X hXE _
    have hQX : Q ≤ normalizer (X : Set G) := le_normalizer_iff.2 fun x hx y hy => by
      obtain ⟨k, hk⟩ := hpow x hx
      rw [hk y (hXE hy)]
      exact pow_mem hy k
    have h2 : 2 ≤ CFSG.Open.pRank p (D.M ⊓ normalizer (X : Set G)) :=
      UC6S846.le_pRank' hp (le_inf hQM hQX) hQel hQc
    omega
  obtain ⟨R, hR, hER⟩ := UC6.exists_isSylowOf_ge hEM hEel.isPGroup
  have hEC : E ≤ centralizer (R : Set G) :=
    le_centralizer_of_facts hF hs hsn hr hr2 hrs hrK hML hR hER hEL hEel.2
  exact h614 (UC6S846.sig_subset_sig1 hSg hns) r hr hr2 hrσ R hR E (le_inf hER hEC) hEel hEc
    (h76 r hr E hEM hEel hEc hpos hXN)

theorem uc22s218n_pRank_le_three_of_facts_ex {Tor Out : ℕ → Prop} (D : Data G) (Ch : Choice2011 G)
    (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) (h211 : S21_1 D Ch)
    (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p) (hH : H1930 D)
    (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M) {n : ℕ}
    (hF : TorusFacts218 (BarInf L) n Tor Out)
    (hZ : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card (center (Bar2 L)) → ¬ Tor ℓ ∧ ¬ Out ℓ)
    (hn : ¬ IsPowTwo n) {p : ℕ} (hp : p ∈ D.sig)
    (hex : ¬ Tor p → ¬ Out p → 4 ≤ CFSG.Open.pRank p D.M → (L.subgroupOf D.M).Normal →
      ∀ {s r : ℕ}, Odd s → s ∣ n → r.Prime → r ∣ 2 ^ s - 1 →
        ¬ r ∣ Nat.card (CFSG.solvableRadical ↥L) →
        ∃ E Q : Subgroup G, E ≤ L ∧ IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧ Q ≤ D.M ∧
          IsElemAbelian p Q ∧ Nat.card Q = p ^ 2 ∧
          ∀ x ∈ Q, ∃ k : ℕ, ∀ e ∈ E, x * e * x⁻¹ = e ^ k) :
    CFSG.Open.pRank p D.M ≤ 3 := by
  by_contra h4
  have hns := UC6S846.not_solvable_of_mem_calC hL
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have hsp := UC6S846.sp_of_mem_sig hSg hns hp
  have hLM : L ≤ D.M := hL.1.le
  have : (L.subgroupOf D.M).Normal := normal_of_facts D Ch hSg h211 hH c hL hF hZ hn
  have hML : D.M ≤ normalizer (L : Set G) := le_normalizer_of_normal_subgroupOf hLM
  obtain ⟨s, hs, hs1, hsn⟩ := PartTwo.s13_exists_odd_divisor hn
  have hCL : ∀ q : ℕ, q.Prime → q ≠ 2 → q ∣ 2 ^ s - 1 → ¬ IsStronglyPEmbedded q D.M :=
    fun q hq hq2 hqs => not_stronglyEmbedded_of_facts D Ch h211 hH c hLM hML hF hs hsn hq hq2 hqs
  by_cases hps : p ∣ 2 ^ s - 1
  · exact hCL p hpp hp2 hps hsp
  have hs3 : 3 ≤ s := by
    obtain ⟨k, rfl⟩ := hs
    omega
  have h8 : 8 ≤ 2 ^ s :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs3
  obtain ⟨r, hr, hrs⟩ := Nat.exists_prime_and_dvd (show 2 ^ s - 1 ≠ 1 by omega)
  have hr2 : r ≠ 2 := uc22p218c_ne_two_of_dvd (by omega) hrs
  have hrσ : r ∉ D.sig := fun hrσ => hCL r hr hr2 hrs (UC6S846.sp_of_mem_sig hSg hns hrσ)
  have hpr : p ≠ r := by
    rintro rfl
    exact hps hrs
  have hrK : ¬ r ∣ Nat.card (CFSG.solvableRadical ↥L) :=
    not_dvd_card_solvableRadical hL.2.2 hr hr2
      (fun h => (hZ r hr h).1 (hF.tor_of_dvd hs hsn hr hrs))
  obtain ⟨E, Q, hEL, hEel, hEc, hQM, hQel, hQc, hpow⟩ : ∃ E Q : Subgroup G, E ≤ L ∧
      IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧ Q ≤ D.M ∧ IsElemAbelian p Q ∧
        Nat.card Q = p ^ 2 ∧ ∀ x ∈ Q, ∃ k : ℕ, ∀ e ∈ E, x * e * x⁻¹ = e ^ k := by
    by_cases hTp : Tor p
    · have hpK : ¬ p ∣ Nat.card (CFSG.solvableRadical ↥L) :=
        not_dvd_card_solvableRadical hL.2.2 hpp hp2 (fun h => (hZ p hpp h).1 hTp)
      obtain ⟨E, Q, hEL, hEel, hEc, hQL, hQel, hQc, hpow⟩ :=
        exists_pair_of_tor hF hs hsn hr hrs hpp hTp hpr hpK hrK
      exact ⟨E, Q, hEL, hEel, hEc, hQL.trans hLM, hQel, hQc, hpow⟩
    · by_cases hOp : Out p
      · have hpK : ¬ p ∣ Nat.card (CFSG.solvableRadical ↥L) :=
          not_dvd_card_solvableRadical hL.2.2 hpp hp2 (fun h => (hZ p hpp h).2 hOp)
        have hrank : CFSG.Open.pRank p L + 2 ≤ CFSG.Open.pRank p D.M := by
          have h1 := hF.pRank_le_two hpp hp2 hOp
          rw [← pRank_eq_pRank_barInf hpp hpK] at h1
          omega
        exact exists_pair_of_out hLM hF hs hsn hpp hp2 hOp hpK hr hr2 hrs hrK hpr hrank
      · exact hex hTp hOp (by omega) inferInstance hs hsn hr hrs hrK
  exact hCL r hr hr2 hrs (stronglyEmbedded_of_torus_of_facts D hSg h614 hL hML hF hs hsn hpp
    (h76 p hp hsp) hr hr2 hrs hrK hrσ hEL hEel hEc hQM hQel hQc hpow)

theorem uc22s218n_pRank_le_three_of_facts {Tor Out : ℕ → Prop} (D : Data G) (Ch : Choice2011 G)
    (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) (h211 : S21_1 D Ch)
    (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p) (hH : H1930 D)
    (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M) {n : ℕ}
    (hF : TorusFacts218 (BarInf L) n Tor Out)
    (hZ : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card (center (Bar2 L)) → ¬ Tor ℓ ∧ ¬ Out ℓ)
    (hn : ¬ IsPowTwo n) {p : ℕ} (hp : p ∈ D.sig) (hTO : Tor p ∨ Out p) :
    CFSG.Open.pRank p D.M ≤ 3 :=
  uc22s218n_pRank_le_three_of_facts_ex D Ch hSg h614 h211 h76 hH c hL hF hZ hn hp
    (fun hT hO => (hTO.elim hT hO).elim)

end CFSG.LocalAnalysis.UniquenessCase.UC22
