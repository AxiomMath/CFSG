module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsD
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07
public import CFSG.RankThree.PartOne.AUTSL.Interface
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.CentralizingRank
public import CFSG.GroupTheory.ConjActionModPCore
public import CFSG.GroupTheory.CoprimeCentralizerRank
public import CFSG.Holt.General.NoRelevantBasic
public import CFSG.LocalAnalysis.SteinbergCCSQTKTwoCoreQuotient
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdRank
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem card_bar_of_isL3 {L : Subgroup G} (hshape : IsL3 (Bar2 L) 2) :
    Nat.card (Bar2 L) = 2 ^ 6 * 3 ^ 2 * 5 * 7 := by
  obtain ⟨K, hfield, hfin, hKcard, ⟨e⟩⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hshape
  letI := hfield
  letI := hfin
  have hk : Nat.card K = 4 := by rw [hKcard]; norm_num
  rw [Nat.card_congr e.toEquiv, CFSG.RankThree.PartTwo.KFacts.L34.card_projectiveSL hk]
  norm_num

theorem card_mulAut_bar_of_isL3 {L : Subgroup G} (hshape : IsL3 (Bar2 L) 2) :
    Nat.card (MulAut (Bar2 L)) = 2 ^ 8 * 3 ^ 3 * 5 * 7 := by
  obtain ⟨K, hfield, hfin, hKcard, ⟨e⟩⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hshape
  letI := hfield
  letI := hfin
  have hk : Nat.card K = 4 := by rw [hKcard]; norm_num
  rw [Nat.card_congr (MulAut.congr e).toEquiv,
    CFSG.RankThree.PartTwo.KFacts.L34.card_mulAut hk]
  norm_num

theorem card_sylow_three_eq_nine {L A : Subgroup G}
    (hshape : IsL3 (Bar2 L) 2)
    (hA : CFSG.ABGLocalTools.IsSylowOf 3 A L) : Nat.card A = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcardBar : Nat.card (Bar2 L) = 2 ^ 6 * 3 ^ 2 * 5 * 7 := card_bar_of_isL3 hshape
  have hcardO : Nat.card (pCoreOf 2 L) = Nat.card (CFSG.pCore 2 ↥L) :=
    Subgroup.card_map_of_injective L.subtype_injective
  have hcardL : Nat.card L = Nat.card (Bar2 L) * Nat.card (pCoreOf 2 L) := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L)
    show Nat.card ↥L = Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) * Nat.card ↥(pCoreOf 2 L)
    rw [hcardO]
    exact h
  have hfacBar : (Nat.card (Bar2 L)).factorization 3 = 2 := by
    rw [hcardBar, show 2 ^ 6 * 3 ^ 2 * 5 * 7 = 3 ^ 2 * 2240 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]
  have hO2card : Nat.card (pCoreOf 2 L) = Nat.card (CFSG.pCore 2 ↥L) :=
    Subgroup.card_map_of_injective L.subtype_injective
  have hfacO : (Nat.card (pCoreOf 2 L)).factorization 3 = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    rw [hO2card]
    exact CFSG.LocalAnalysis.SQTKTwoCoreQuotient.not_dvd_card_pCore_two Nat.prime_three
      (by norm_num)
  have hfacL : (Nat.card L).factorization 3 = 2 := by
    rw [hcardL, Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne'), Finsupp.add_apply,
      hfacBar, hfacO, add_zero]
  rw [hA.card_eq, hfacL]
  norm_num

theorem isElemAbelian_sylow_three {L A : Subgroup G}
    (hshape : IsL3 (Bar2 L) 2)
    (hA : CFSG.ABGLocalTools.IsSylowOf 3 A L) : IsElemAbelian 3 A := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAcard : Nat.card A = 9 := card_sylow_three_eq_nine hshape hA
  obtain ⟨K, hfield, hfin, hKcard, ⟨e⟩⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hshape
  letI := hfield
  letI := hfin
  have hk : Nat.card K = 4 := by rw [hKcard]; norm_num
  let π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  let iA : ↥A →* ↥L := Subgroup.inclusion hA.le
  let g : ↥A →* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 K :=
    e.toMonoidHom.comp (π.comp iA)
  have hcardO : ∃ k : ℕ, Nat.card (pCoreOf 2 L) = 2 ^ k := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
    exact ⟨k, by simpa only [pCoreOf, Subgroup.card_map_of_injective L.subtype_injective] using hk⟩
  obtain ⟨k, hkO⟩ := hcardO
  have hcop : Nat.Coprime (Nat.card A) (Nat.card (pCoreOf 2 L)) := by
    rw [hAcard, hkO]
    exact ((Nat.Coprime.pow_left 2 (by norm_num : Nat.Coprime 3 2))).pow_right k
  have hbot : A ⊓ pCoreOf 2 L = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  have hg : Function.Injective g := by
    intro a b hab
    have h1 : π (iA a) = π (iA b) := e.injective hab
    have h1' : (QuotientGroup.mk (iA a) : ↥L ⧸ CFSG.pCore 2 ↥L) =
        QuotientGroup.mk (iA b) := h1
    have h2 : (iA a)⁻¹ * (iA b) ∈ CFSG.pCore 2 ↥L :=
      QuotientGroup.eq.mp h1'
    have h3 : ((a : G)⁻¹ * (b : G)) ∈ pCoreOf 2 L := by
      change ((a : G)⁻¹ * (b : G)) ∈ (CFSG.pCore 2 ↥L).map L.subtype
      exact Subgroup.mem_map_of_mem L.subtype h2
    have h4 : ((a : G)⁻¹ * (b : G)) ∈ A := A.mul_mem (A.inv_mem a.2) b.2
    have h5 : ((a : G)⁻¹ * (b : G)) = 1 := by
      have : ((a : G)⁻¹ * (b : G)) ∈ A ⊓ pCoreOf 2 L := ⟨h4, h3⟩
      rw [hbot] at this
      exact Subgroup.mem_bot.mp this
    have h6 : (b : G) = (a : G) := by
      have := congrArg (fun x : G => (a : G) * x) h5
      simpa [mul_assoc] using this
    exact Subtype.ext h6.symm
  have hgcard : Nat.card g.range = 9 := by
    rw [← hAcard]
    exact (Nat.card_congr (MonoidHom.ofInjective hg).toEquiv).symm
  have hEel : CFSG.IsElementaryAbelian 3 g.range :=
    CFSG.RankThree.PartTwo.KFacts.L34.isElementaryAbelian_of_card_eq_nine hk hgcard
  have hcomm : ∀ a b : ↥A, g a * g b = g b * g a := by
    intro a b
    have := mul_comm' (⟨g a, ⟨a, rfl⟩⟩ : ↥g.range) ⟨g b, ⟨b, rfl⟩⟩
    exact congrArg Subtype.val this
  have hpow : ∀ a : ↥A, g a ^ 3 = 1 := by
    intro a
    have h1 : (⟨g a, ⟨a, rfl⟩⟩ : ↥g.range) ^ 3 = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 3 ↥g.range) ⟨g a, ⟨a, rfl⟩⟩
    simpa using congrArg Subtype.val h1
  obtain ⟨hc, hp⟩ := CFSG.SectionRank.comm_pow_of_injective (p := 3) hg hcomm hpow
  exact ⟨⟨⟨hc⟩⟩, fun x hx => by simpa using hp ⟨x, hx⟩⟩

theorem prime_sq_not_dvd_aut_L34 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    ¬ p ^ 2 ∣ 2 ^ 8 * 3 ^ 3 * 5 * 7 := by
  rintro hsq
  have h2 : ¬ p ∣ 2 := by
    intro h
    rcases (Nat.dvd_prime Nat.prime_two).mp h with h1 | h2
    · exact hp.ne_one h1
    · exact hp2 h2
  have h3 : ¬ p ∣ 3 := by
    intro h
    rcases (Nat.dvd_prime Nat.prime_three).mp h with h1 | h3
    · exact hp.ne_one h1
    · exact hp3 h3
  have h2' : ¬ p ∣ 2 ^ 8 := fun h => h2 (Nat.Prime.dvd_of_dvd_pow hp h)
  have h3' : ¬ p ∣ 3 ^ 3 := fun h => h3 (Nat.Prime.dvd_of_dvd_pow hp h)
  have hdvd0 : p ∣ 2 ^ 8 * 3 ^ 3 * 5 * 7 := by
    simpa using (pow_dvd_pow p (by norm_num : 1 ≤ 2)).trans hsq
  have hdvd : p ∣ 2 ^ 8 * 3 ^ 3 * (5 * 7) := by
    rwa [show (2 : ℕ) ^ 8 * 3 ^ 3 * 5 * 7 = 2 ^ 8 * 3 ^ 3 * (5 * 7) by ring] at hdvd0
  rcases (Nat.Prime.dvd_mul hp).mp hdvd with h | h
  · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact absurd h h2'
    · exact absurd h h3'
  have hp57 : p = 5 ∨ p = 7 := by
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp h with h1 | h5
      · exact absurd h1 hp.ne_one
      · exact Or.inl h5
    · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp h with h1 | h7
      · exact absurd h1 hp.ne_one
      · exact Or.inr h7
  rcases hp57 with rfl | rfl <;> norm_num at hsq

theorem two_le_pRank_inf_centralizer_of_le_L (D : Data G) {V₀ V L : Subgroup G} {p q : ℕ}
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D)
    (ctx : Ctx17_58 D V₀ V L p) (hp3 : p ≠ 3) {B : Subgroup G}
    (hq : q.Prime) (hq2 : q ≠ 2) (hBL : B ≤ L) (hB : IsPGroup q B) :
    2 ≤ CFSG.Open.pRank p (D.M ⊓ centralizer (B : Set G)) := by
  have hpmem : p ∈ D.sig := ctx.hyp54.1
  have hp : p.Prime := (D.sig_prime p hpmem).1
  have hp2 : p ≠ 2 := (D.sig_prime p hpmem).2
  have hLM : L ≤ D.M := ctx.memC.1.le
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.Prime := ⟨hq⟩
  have hNM : D.M ≤ normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp
      (ctx.hyp54.2 L ctx.memC).1
  let a := CFSG.GroupTheory.conjModPCore 2 L D.M hNM
  have hrank := CFSG.GroupTheory.pRank_le_pRank_map_ker_add_pRank_range
    (p := 2) (q := p) hp L D.M hNM
  have hrange : CFSG.Open.pRank p a.range ≤ 1 := by
    have hle : CFSG.Open.pRank p a.range ≤
        CFSG.Open.pRank p (⊤ : Subgroup (MulAut (Bar2 L))) :=
      CFSG.SectionRank.pRank_mono hp.one_lt le_top
    have htop : CFSG.Open.pRank p (⊤ : Subgroup (MulAut (Bar2 L))) ≤ 1 := by
      refine CFSG.QuasithinUnique.Id2519.pRank_le_one_of_not_sq_dvd hp ?_
      rw [card_mulAut_bar_of_isL3 ctx.shapeL]
      exact prime_sq_not_dvd_aut_L34 hp hp2 hp3
    exact hle.trans htop
  have hrank' : CFSG.Open.pRank p D.M ≤
      CFSG.Open.pRank p (a.ker.map D.M.subtype) + CFSG.Open.pRank p a.range := by
    simpa [a] using hrank
  have hM3 : 3 ≤ CFSG.Open.pRank p D.M := hSg.three_le p hpmem
  have hker : 2 ≤ CFSG.Open.pRank p (a.ker.map D.M.subtype) := by omega
  obtain ⟨E, hEker, hEea, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank hp.one_lt (a.ker.map D.M.subtype)
  have hE2 : 2 ≤ CFSG.Open.pRank p E := by
    have h := CFSG.SectionRank.le_pRank hp.one_lt (H := E) (E := E) le_rfl hEea hEcard
    omega
  have hO2M : pCoreOf 2 L ≤ D.M := (Subgroup.map_subtype_le (CFSG.pCore 2 ↥L)).trans hLM
  have hO2char : D.M ≤ normalizer (pCoreOf 2 L) :=
    hNM.trans (CFSG.Holt.General.NoRelevant.normalizer_le_normalizer_map (M := L)
      (K := CFSG.pCore 2 ↥L))
  have hO2eq : ((pCoreOf 2 L).subgroupOf L) = CFSG.pCore 2 ↥L := by
    ext x
    simp [pCoreOf]
  have hO2norm : ((pCoreOf 2 L).subgroupOf L).Normal := by
    rw [hO2eq]
    infer_instance
  have hLN : L ≤ normalizer (pCoreOf 2 L) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.map_subtype_le (CFSG.pCore 2 ↥L))).mp hO2norm
  have hEN : E ≤ D.M := hEker.trans (Subgroup.map_subtype_le a.ker)
  have hRN : E ≤ normalizer (pCoreOf 2 L) := hEN.trans hO2char
  have hBN : B ≤ normalizer (pCoreOf 2 L) := hBL.trans hLN
  have hO2card : Nat.card (pCoreOf 2 L) = Nat.card (CFSG.pCore 2 ↥L) :=
    Subgroup.card_map_of_injective L.subtype_injective
  have hpO : ¬ p ∣ Nat.card (pCoreOf 2 L) := by
    rw [hO2card]
    exact CFSG.LocalAnalysis.SQTKTwoCoreQuotient.not_dvd_card_pCore_two hp hp2
  have hqO : ¬ q ∣ Nat.card (pCoreOf 2 L) := by
    rw [hO2card]
    exact CFSG.LocalAnalysis.SQTKTwoCoreQuotient.not_dvd_card_pCore_two hq hq2
  have hcomm : ⁅E, B⁆ ≤ pCoreOf 2 L := by
    rw [Subgroup.commutator_le]
    intro e he x hx
    have he' := (CFSG.GroupTheory.mem_map_ker_conjModPCore_iff 2 L D.M hNM).mp (hEker he)
    rw [commutatorElement_def]
    exact he'.2 x (hBL hx)
  have hpc := CFSG.GroupTheory.pRank_le_pRank_inf_centralizer_of_commutator_le
    (p := p) (q := q) (M := D.M) (N := pCoreOf 2 L) (R := E) (B := B)
    hEN hO2M hRN hBN hEea.isPGroup hB hpO hqO hcomm
  exact hE2.trans hpc

theorem pRank_inf_centralizer_of_isL3_of_ne_three (D : Data G) {V₀ V : Subgroup G}
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D)
    (_h76 : F07.R76 D) {L : Subgroup G} {p : ℕ} (ctx : Ctx17_58 D V₀ V L p)
    (A : Subgroup G) (hA : CFSG.ABGLocalTools.IsSylowOf 3 A L) (hp3 : p ≠ 3) :
    2 ≤ CFSG.Open.pRank p (D.M ⊓ centralizer (A : Set G)) := by
  have hAea : IsElemAbelian 3 A := isElemAbelian_sylow_three ctx.shapeL hA
  exact two_le_pRank_inf_centralizer_of_le_L D hSg ctx hp3 Nat.prime_three (by norm_num)
    hA.le hAea.isPGroup

open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 in
theorem seventeen_fiftynine (D : Data G) {V₀ V : Subgroup G}
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D)
    (h76 : F07.R76 D) :
    R17_59At D V₀ V := by
  intro L p ctx A hA
  have hpmem : p ∈ D.sig := ctx.hyp54.1
  have hp : p.Prime := (D.sig_prime p hpmem).1
  have hp2 : p ≠ 2 := (D.sig_prime p hpmem).2
  have hLM : L ≤ D.M := ctx.memC.1.le
  have hAM : A ≤ D.M := hA.le.trans hLM
  have hAcard : Nat.card A = 9 := card_sylow_three_eq_nine ctx.shapeL hA
  have hAea : IsElemAbelian 3 A := isElemAbelian_sylow_three ctx.shapeL hA
  have hA3 : IsPGroup 3 A := hAea.isPGroup
  have hAr : 2 ≤ CFSG.Open.pRank 3 A := by
    have h := CFSG.SectionRank.le_pRank (p := 3) (by norm_num) (H := A) (E := A) le_rfl hAea
      (k := 2) (by simpa using hAcard)
    simpa using h
  have hns : ¬ Group.IsSolvable ↥D.M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.not_solvable_of_mem_calC ctx.memC
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M :=
    hSg.sig1_sp p (CFSG.LocalAnalysis.UniquenessCase.UC6S846.sig_subset_sig1 hSg hns hpmem)
  have h76M : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 D.M p :=
    h76 p hp hp2 hsp
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF : 2 ≤ CFSG.Open.pRank p (D.M ⊓ centralizer (A : Set G)) := by
    by_cases hp3 : p = 3
    · subst p
      have hAle : A ≤ D.M ⊓ centralizer (A : Set G) := by
        refine le_inf hAM ?_
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        haveI : IsMulCommutative ↥A := hAea.1
        exact congrArg Subtype.val (mul_comm' (⟨y, hy⟩ : A) ⟨x, hx⟩)
      have h := CFSG.SectionRank.le_pRank (p := 3) (by norm_num)
        (H := D.M ⊓ centralizer (A : Set G)) (E := A) hAle hAea (k := 2) (by simpa using hAcard)
      simpa using h
    · exact pRank_inf_centralizer_of_isL3_of_ne_three D hSg h76 ctx A hA hp3
  exact rankThreeGamma_le_of_two_le_pRank_inf_centralizer hsp h76M hAM hA3 hAr hF

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
