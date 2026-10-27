module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.InP11OfStrongly
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ElevenTenP
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveNineteenPerm
public import CFSG.GroupTheory.SteinbergCBFTFactorization
public import CFSG.HardMathSupport.Malle.OvergroupTransport.Transport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem exists_isSylowIn_normalized_of_coprime
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] {K Q : Subgroup G}
    (hQ : IsPGroup q Q) (hQK : Q ≤ normalizer (K : Set G)) (hcop : ¬ q ∣ Nat.card K) :
    ∃ P : Subgroup G, CFSG.Quasithin.IsSylowIn p P K ∧ Q ≤ normalizer (P : Set G) := by
  obtain ⟨S, hS⟩ := CFSG.GroupTheory.FT63ChII.exists_sylow_normalized
    (p := q) (q := p) (W := K) (A := Q) hQ hQK hcop
  refine ⟨(S : Subgroup K).map K.subtype, ?_, hS⟩
  exact CFSG.Quasithin.isSylowIn_of_card_eq (Subgroup.map_subtype_le _) (by
    rw [Subgroup.card_map_of_injective K.subtype_injective, S.card_eq_multiplicity])

private theorem seventeen_two_K_facts (D : Data G) {Dsub : Subgroup G} (hDM : Dsub ≤ D.M)
    (hnormal : ((Dsub ⊔ pCoreOf 2 D.M).subgroupOf D.M).Normal) :
    D.M ≤ Subgroup.normalizer ((Dsub ⊔ pCoreOf 2 D.M : Subgroup G) : Set G) ∧
      pCoreOf 2 D.M ≤ D.T ∧
      Dsub ≤ Subgroup.normalizer ((pCoreOf 2 D.M : Subgroup G) : Set G) ∧
      Permutes Dsub D.T := by
  have hKle : Dsub ⊔ pCoreOf 2 D.M ≤ D.M :=
    sup_le hDM (CFSG.LieType.BorelTits.pCoreOf_le 2 D.M)
  have hKnormal : D.M ≤ Subgroup.normalizer ((Dsub ⊔ pCoreOf 2 D.M : Subgroup G) : Set G) :=
    (CFSG.Quasithin.BlueprintB2.normal_subgroupOf_iff_le_normalizer hKle).1 hnormal
  have hTM : CFSG.Quasithin.IsSylowIn 2 D.T D.M := TwelveShort.isSylowIn_of_le D D.sylowM.le
  have hOM : pCoreOf 2 D.M ≤ D.M := CFSG.LieType.BorelTits.pCoreOf_le 2 D.M
  have hOT : pCoreOf 2 D.M ≤ D.T :=
    CFSG.Quasithin.IsSylowIn.le_of_normal hTM hOM
      ((CFSG.Quasithin.BlueprintB2.normal_subgroupOf_iff_le_normalizer hOM).2
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M)
  have hDsubN : Dsub ≤ Subgroup.normalizer ((pCoreOf 2 D.M : Subgroup G) : Set G) :=
    hDM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M)
  exact ⟨hKnormal, hOT, hDsubN,
    TwelveNineteen.permutes_of_le_normalizer_sup hOT (D.sylowM.le.trans hKnormal) hDsubN⟩

private theorem seventeen_two_one_sigma (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Dsub : Subgroup G} (hDM : Dsub ≤ D.M) (hDp : IsPGroup p Dsub)
    (hDnc : ¬ IsCyclic ↥Dsub) (hexp : ∀ x ∈ Dsub, x ^ p = 1)
    (hnormal : ((Dsub ⊔ pCoreOf 2 D.M).subgroupOf D.M).Normal) (hpσ : p ∈ D.sig) :
    F11.InP11 D Dsub := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, -, -, hperm⟩ := seventeen_two_K_facts D hDM hnormal
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M :=
    hSg.sig1_sp p (by rwa [← h1219])
  exact inP11_of_strongly hp hp2 hsp hDM hDp hexp hDnc hperm

private theorem seventeen_two_disjoint_card (D : Data G) {p m n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Dsub : Subgroup G} (hDM : Dsub ≤ D.M) (hn : Nat.card ↥Dsub = p ^ n)
    (hm : Nat.card ↥(pCoreOf 2 D.M : Subgroup G) = 2 ^ m) :
    Disjoint (pCoreOf 2 D.M) Dsub ∧
      Nat.card ↥(Dsub ⊔ pCoreOf 2 D.M : Subgroup G) =
        Nat.card ↥(pCoreOf 2 D.M : Subgroup G) * Nat.card ↥Dsub := by
  have hdisj : Disjoint (pCoreOf 2 D.M) Dsub := by
    refine Subgroup.disjoint_of_coprime_natCard ?_
    rw [hm, hn]
    have hcop2p : Nat.Coprime 2 p :=
      (Nat.coprime_primes Nat.prime_two hp).2 (by omega)
    exact (hcop2p.pow_left m).pow_right n
  exact ⟨hdisj, by
    rw [sup_comm,
      CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
        (pCoreOf 2 D.M) Dsub
        (hDM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M)) hdisj]⟩

private theorem seventeen_two_sylow_p_normalized (D : Data G) {p q : ℕ}
    {Dsub : Subgroup G} (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (hpq : q ≠ p) (hDM : Dsub ≤ D.M) (hDp : IsPGroup p Dsub)
    (hnormal : ((Dsub ⊔ pCoreOf 2 D.M).subgroupOf D.M).Normal) :
    ∃ (Q P : Subgroup G), CFSG.ABGLocalTools.IsSylowOf q Q D.M ∧
      CFSG.Quasithin.IsSylowIn p P (Dsub ⊔ pCoreOf 2 D.M) ∧
      Q ≤ Subgroup.normalizer (P : Set G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨hKnormal, -, -, -⟩ := seventeen_two_K_facts D hDM hnormal
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hDp
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M)
  obtain ⟨-, hcardK⟩ := seventeen_two_disjoint_card D hp hp2 hDM hn hm
  have hcopK : ¬ q ∣ Nat.card ↥(Dsub ⊔ pCoreOf 2 D.M : Subgroup G) := by
    rw [hcardK, hm, hn]
    intro hdiv
    rcases (Nat.Prime.dvd_mul hq).1 hdiv with h | h
    · exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h))
    · exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow h))
  obtain ⟨S⟩ : Nonempty (Sylow q D.M) := inferInstance
  let Q : Subgroup G := (S : Subgroup D.M).map D.M.subtype
  have hQ : CFSG.ABGLocalTools.IsSylowOf q Q D.M := ⟨S, rfl⟩
  have hQp : IsPGroup q Q := S.isPGroup'.map D.M.subtype
  have hQK : Q ≤ Subgroup.normalizer ((Dsub ⊔ pCoreOf 2 D.M : Subgroup G) : Set G) :=
    CFSG.ABGLocalTools.IsSylowOf.le hQ |>.trans hKnormal
  obtain ⟨P, hPsyl, hQnormP⟩ :=
    exists_isSylowIn_normalized_of_coprime (p := p) (q := q) hQp hQK hcopK
  exact ⟨Q, P, hQ, hPsyl, hQnormP⟩

private theorem seventeen_two_D_sylow_p (D : Data G) {p : ℕ} {Dsub : Subgroup G}
    (hp : p.Prime) (hp2 : p ≠ 2) (hDM : Dsub ≤ D.M) (hDp : IsPGroup p Dsub)
    (hnormal : ((Dsub ⊔ pCoreOf 2 D.M).subgroupOf D.M).Normal) :
    CFSG.ABGLocalTools.IsSylowOf p Dsub (Dsub ⊔ pCoreOf 2 D.M) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hDp
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M)
  obtain ⟨-, hcardK⟩ := seventeen_two_disjoint_card D hp hp2 hDM hn hm
  have hrel : Dsub.relIndex (Dsub ⊔ pCoreOf 2 D.M) = Nat.card ↥(pCoreOf 2 D.M : Subgroup G) := by
    have h := Subgroup.relIndex_mul_card (H := Dsub) (K := Dsub ⊔ pCoreOf 2 D.M)
    rw [inf_eq_left.2 (le_sup_left : Dsub ≤ Dsub ⊔ pCoreOf 2 D.M), hcardK] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have hDsylIn : CFSG.Quasithin.IsSylowIn p Dsub (Dsub ⊔ pCoreOf 2 D.M) := by
    refine ⟨le_sup_left, hDp, ?_⟩
    rw [hrel, hm]
    intro hdiv
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdiv))
  exact (CFSG.ABGLocalTools.isSylowOf_iff (p := p) (P := Dsub)
    (K := Dsub ⊔ pCoreOf 2 D.M)).2 hDsylIn

private theorem seventeen_two_rank_normalizer (D : Data G) {p q : ℕ}
    {Dsub Q P : Subgroup G} (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime) (hDM : Dsub ≤ D.M)
    (hDp : IsPGroup p Dsub) (hnormal : ((Dsub ⊔ pCoreOf 2 D.M).subgroupOf D.M).Normal)
    (hQ : CFSG.ABGLocalTools.IsSylowOf q Q D.M)
    (hPsyl : CFSG.Quasithin.IsSylowIn p P (Dsub ⊔ pCoreOf 2 D.M))
    (hQnormP : Q ≤ Subgroup.normalizer (P : Set G)) :
    CFSG.Open.pRank q (D.M ⊓ Subgroup.normalizer (Dsub : Set G)) =
      CFSG.Open.pRank q D.M := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨Knormal, -, -, -⟩ := seventeen_two_K_facts D hDM hnormal
  have hDsylOf : CFSG.ABGLocalTools.IsSylowOf p Dsub (Dsub ⊔ pCoreOf 2 D.M) :=
    seventeen_two_D_sylow_p D hp hp2 hDM hDp hnormal
  have hDsyl : CFSG.Quasithin.IsSylowIn p Dsub (Dsub ⊔ pCoreOf 2 D.M) :=
    (CFSG.ABGLocalTools.isSylowOf_iff (p := p) (P := Dsub)
      (K := Dsub ⊔ pCoreOf 2 D.M)).1 hDsylOf
  obtain ⟨k, hkK, hkiff⟩ :=
    CFSG.Quasithin.Ch1Sec3.exists_conj_of_isSylowIn (p := p) hPsyl hDsyl
  have hkmap : P.map (MulAut.conj k).toMonoidHom = Dsub := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hkiff (k * y * k⁻¹)).2 (by
        have h : k⁻¹ * (k * y * k⁻¹) * k = y := by group
        rw [h]; exact hy)
    · intro hx
      refine ⟨k⁻¹ * x * k, (hkiff x).1 hx, ?_⟩
      show k * (k⁻¹ * x * k) * k⁻¹ = x
      group
  have hkM : k ∈ D.M := (sup_le hDM (CFSG.LieType.BorelTits.pCoreOf_le 2 D.M)) hkK
  have hMmap : D.M.map (MulAut.conj k).toMonoidHom = D.M :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hkM)
  have hmap : (D.M ⊓ Subgroup.normalizer (P : Set G)).map
      (MulAut.conj k).toMonoidHom = D.M ⊓ Subgroup.normalizer (Dsub : Set G) := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj k).injective, hMmap,
      Subgroup.map_equiv_normalizer_eq P (MulAut.conj k), hkmap]
  have hconjrank : CFSG.Open.pRank q (D.M ⊓ Subgroup.normalizer (P : Set G)) =
      CFSG.Open.pRank q (D.M ⊓ Subgroup.normalizer (Dsub : Set G)) := by
    have h := CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_map_of_injective
      q (f := (MulAut.conj k).toMonoidHom) (MulAut.conj k).injective
      (D.M ⊓ Subgroup.normalizer (P : Set G))
    rw [hmap] at h
    exact h.symm
  obtain ⟨S, hSQ⟩ := hQ
  have hQle : Q ≤ D.M := by
    rw [← hSQ]
    exact Subgroup.map_subtype_le _
  have hrankQ : CFSG.Open.pRank q Q = CFSG.Open.pRank q D.M := by
    have h1 : CFSG.Open.pRank q Q = CFSG.Open.pRank q (S : Subgroup D.M) := by
      rw [← hSQ]
      exact CFSG.HardMathSupport.Malle.OvergroupTransport.pRank_map_of_injective
        q (f := D.M.subtype) D.M.subtype_injective (S : Subgroup D.M)
    have h2 : CFSG.Open.pRank q (S : Subgroup D.M) =
        CFSG.Open.pRank q (⊤ : Subgroup D.M) :=
      CFSG.PreuniquenessRankFour.Helpers.pRank_sylow_eq_globalRank q hq S
    have h3 : CFSG.Open.pRank q (⊤ : Subgroup D.M) = CFSG.Open.pRank q D.M :=
      (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := q) D.M).symm
    rw [h1, h2, h3]
  have hge : CFSG.Open.pRank q D.M ≤
      CFSG.Open.pRank q (D.M ⊓ Subgroup.normalizer (P : Set G)) := by
    rw [← hrankQ]
    exact CFSG.SectionRank.pRank_mono hq.one_lt (le_inf hQle hQnormP)
  have hle : CFSG.Open.pRank q (D.M ⊓ Subgroup.normalizer (P : Set G)) ≤
      CFSG.Open.pRank q D.M :=
    CFSG.SectionRank.pRank_mono hq.one_lt inf_le_left
  exact hconjrank.symm.trans (le_antisymm hle hge)

private theorem seventeen_two_sylow_normalizes (D : Data G) {p : ℕ} {Dsub P : Subgroup G}
    (hp : p.Prime) (hp2 : p ≠ 2) (hDM : Dsub ≤ D.M) (hDp : IsPGroup p Dsub)
    (hnormal : ((Dsub ⊔ pCoreOf 2 D.M).subgroupOf D.M).Normal)
    (hDP : Dsub ≤ P) (hPsyl : CFSG.ABGLocalTools.IsSylowOf p P D.M) :
    P ≤ Subgroup.normalizer (Dsub : Set G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨Knormal, -, -, -⟩ := seventeen_two_K_facts D hDM hnormal
  let Y : Subgroup G := P ⊓ (Dsub ⊔ pCoreOf 2 D.M)
  have hYleK : Y ≤ Dsub ⊔ pCoreOf 2 D.M := by
    dsimp [Y]; exact inf_le_right
  have hYleP : Y ≤ P := by
    dsimp [Y]; exact inf_le_left
  have hYp : IsPGroup p Y := (CFSG.ABGLocalTools.IsSylowOf.isPGroup hPsyl).to_le hYleP
  have hDsyl : CFSG.ABGLocalTools.IsSylowOf p Dsub (Dsub ⊔ pCoreOf 2 D.M) :=
    seventeen_two_D_sylow_p D hp hp2 hDM hDp hnormal
  have hYcard : Nat.card ↥Y ≤ Nat.card ↥Dsub :=
    CFSG.SignalizerFunctorTheorem.Glauberman.IsSylowOf.card_le hp hDsyl hYp hYleK
  have hPK : Y = Dsub :=
    (Subgroup.eq_of_le_of_card_ge (by
      dsimp [Y]
      exact le_inf hDP le_sup_left) hYcard).symm
  have hforward : ∀ p' ∈ P, ∀ x ∈ Dsub, p' * x * p'⁻¹ ∈ Dsub := by
    intro p' hp' x hx
    have hxP : x ∈ P := hDP hx
    have hxK : x ∈ Dsub ⊔ pCoreOf 2 D.M :=
      (le_sup_left : Dsub ≤ Dsub ⊔ pCoreOf 2 D.M) hx
    have hpK : p' * x * p'⁻¹ ∈ Dsub ⊔ pCoreOf 2 D.M :=
      (Subgroup.mem_normalizer_iff.1
        (Knormal ((CFSG.ABGLocalTools.IsSylowOf.le hPsyl) hp')) x).1 hxK
    have hpP : p' * x * p'⁻¹ ∈ P :=
      P.mul_mem (P.mul_mem hp' hxP) (P.inv_mem hp')
    rw [← hPK]
    exact ⟨hpP, hpK⟩
  intro p' hp'
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hforward p' hp' x
  · intro hx
    have h := hforward p'⁻¹ (P.inv_mem hp') (p' * x * p'⁻¹) hx
    simpa [mul_assoc] using h

private theorem seventeen_two_rank_normalizer_all (D : Data G) (hSg : UC6S846.SigmaStd D)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Dsub : Subgroup G} (hDM : Dsub ≤ D.M)
    (hDp : IsPGroup p Dsub) (hnormal : ((Dsub ⊔ pCoreOf 2 D.M).subgroupOf D.M).Normal)
    (hpσ : p ∉ D.sig) :
    ∀ q ∈ D.sig, CFSG.Open.pRank q (D.M ⊓ Subgroup.normalizer (Dsub : Set G)) =
      CFSG.Open.pRank q D.M := by
  intro q hqσ
  obtain ⟨hq, hq2⟩ := D.sig_prime q hqσ
  have hpq : q ≠ p := fun h => hpσ (h ▸ hqσ)
  obtain ⟨Q, P, hQ, hPsyl, hQnormP⟩ :=
    seventeen_two_sylow_p_normalized D hp hq hp2 hq2 hpq hDM hDp hnormal
  exact seventeen_two_rank_normalizer D hp hp2 hq hDM hDp hnormal hQ hPsyl hQnormP

private theorem seventeen_two_one_not_sigma (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) (h77 : F07.R77Eq D) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Dsub : Subgroup G} (hDM : Dsub ≤ D.M) (hDp : IsPGroup p Dsub)
    (hDnc : ¬ IsCyclic ↥Dsub) (hexp : ∀ x ∈ Dsub, x ^ p = 1)
    (hclass : ⁅⁅Dsub, Dsub⁆, Dsub⁆ = ⊥)
    (hnormal : ((Dsub ⊔ pCoreOf 2 D.M).subgroupOf D.M).Normal) (hpσ : p ∉ D.sig) :
    F11.InP11 D Dsub := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, -, -, hperm⟩ := seventeen_two_K_facts D hDM hnormal
  have hΓ : rankThreeGamma 1 p Dsub ≤ D.M :=
    s11_TenP_rankThreeGamma_le D hSg h1219 h77 hp hp2 hDM hDp hDnc hexp hclass
      (seventeen_two_rank_normalizer_all D hSg hp hp2 hDM hDp hnormal hpσ)
  obtain ⟨P', hDP', hPsylM⟩ :=
    CFSG.SignalizerFunctorTheorem.Glauberman.exists_isSylowOf_ge hp hDM hDp
  have hPN : P' ≤ Subgroup.normalizer (Dsub : Set G) :=
    seventeen_two_sylow_normalizes D hp hp2 hDM hDp hnormal hDP' hPsylM
  exact ⟨p, hp, hp2, hDM, hDp, hexp, hDnc, hperm, hΓ,
    Or.inr ⟨Dsub, hDnc, ⟨P', hPsylM, hDP', hPN⟩, hΓ⟩⟩

theorem seventeen_two_one (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h77 : F07.R77Eq D) {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V) : R17_2_1At D V₀ V := by
  intro p Dsub hp hp2 hDM hDp hDnc hexp hclass hnormal
  by_cases hpσ : p ∈ D.sig
  · exact seventeen_two_one_sigma D hSg h1219 hp hp2 hDM hDp hDnc hexp hnormal hpσ
  · exact seventeen_two_one_not_sigma D hSg h1219 h77 hp hp2 hDM hDp hDnc hexp hclass hnormal hpσ

theorem seventeen_two_two (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h77 : F07.R77Eq D) {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    (h17_1 : R17_1At D V₀ V hV) : R17_2_2At D V₀ V hV := by
  intro p Dsub hp hp2 hDM hDp hDnc hexp hclass hnormal
  haveI : Fact p.Prime := ⟨hp⟩
  have hP : F11.InP11 D Dsub :=
    seventeen_two_one D hSg h1219 h77 hV p Dsub hp hp2 hDM hDp hDnc hexp hclass hnormal
  obtain ⟨hPStarEmpty, hPconfig⟩ := h17_1
  obtain ⟨hV0, hk, hm⟩ := hPconfig ⟨Dsub, hP⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hDp
  have ha0 : a ≠ 0 := by
    intro h0
    apply hDnc
    have hcard : Nat.card ↥Dsub = 1 := by rw [ha, h0]; simp
    haveI : Subsingleton ↥Dsub := (Nat.card_eq_one_iff_unique.mp hcard).1
    exact isCyclic_of_subsingleton
  have ha1 : a ≠ 1 := by
    intro h1
    apply hDnc
    have hcard : Nat.card ↥Dsub = p := by rw [ha, h1]; simp
    exact isCyclic_of_card_dvd_prime (p := p) (by rw [hcard])
  have ha2 : 2 ≤ a := by omega
  have hge : p ^ 2 ≤ Nat.card ↥Dsub := by
    rw [ha]
    exact Nat.pow_le_pow_right hp.pos ha2
  have hle : Nat.card ↥Dsub ≤ p ^ 2 := by
    by_contra h
    have hlt : p ^ 2 < Nat.card ↥Dsub := Nat.lt_of_not_ge h
    exact hPStarEmpty Dsub ⟨hP, fun _ => ⟨p, hp, hDp, Or.inl hlt⟩⟩
  exact ⟨le_antisymm hle hge, hV0, hk, hm⟩


end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
