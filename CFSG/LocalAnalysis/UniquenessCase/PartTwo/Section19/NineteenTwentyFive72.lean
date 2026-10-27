module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.NoL2SzSection
public import CFSG.Adapters.LieModelSimple
public import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
public import CFSG.RankThree.PartOne.S12.Sec1320
public import CFSG.LocalAnalysis.StronglyEmbedded.Normalizer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.RankThreeUC
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem hasL2SzSection_of_le {n : ℕ} {X X' : Subgroup G} (h : HasL2SzSection n X)
    (hle : X ≤ X') : HasL2SzSection n X' := by
  obtain ⟨Y, hY, Z, hZ, hS⟩ := h
  exact ⟨Y, hY.trans hle, Z, hZ, hS⟩

theorem hasL2SzSection_of_surjective {n : ℕ} {X Y : Subgroup G} (hYX : Y ≤ X) {S : Type}
    [Group S] (hS : IsL2 S n ∨ IsSz S n) (f : ↥Y →* S) (hf : Function.Surjective f) :
    HasL2SzSection n X := by
  refine ⟨Y, hYX, f.ker, inferInstance, ?_⟩
  let e : ↥Y ⧸ f.ker ≃* S := QuotientGroup.quotientKerEquivOfSurjective f hf
  rcases hS with hS | hS
  · exact Or.inl (CFSG.Blueprint.LieModel.of_mulEquiv e.symm hS)
  · exact Or.inr (CFSG.Blueprint.LieModel.of_mulEquiv e.symm hS)

theorem isSimpleGroup_of_isL2_or_isSz {S : Type} [Group S] {n : ℕ} (hS : IsL2 S n ∨ IsSz S n) :
    IsSimpleGroup S := by
  rcases hS with hS | hS
  · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hS
  · exact CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hS

theorem even_card_of_isL2_or_isSz {S : Type} [Group S] {n : ℕ} (hS : IsL2 S n ∨ IsSz S n) :
    Even (Nat.card S) := by
  rcases hS with hS | hS
  · exact CFSG.RankThree.PartOne.Sec1320.even_card_of_psl_two
      (CFSG.Blueprint.LieModel.statedClassicalModel hS (by decide))
  · have hn : 1 ≤ n := hS.admissible.2.1
    have h2 := CFSG.LocalAnalysis.EvenBN.GMSK.factorization_two_card_of_lieModel_twistedB2 hS
    refine even_iff_two_dvd.mpr (Nat.dvd_of_factorization_pos ?_)
    rw [h2]
    omega

theorem hasL2SzSection_map_of_odd {H : Subgroup G} {K : Subgroup ↥H} [K.Normal]
    (hK : Odd (Nat.card K)) {n : ℕ} {X : Subgroup G} (hXH : X ≤ H) (h : HasL2SzSection n X) :
    HasL2SzSection n ((X.subgroupOf H).map (QuotientGroup.mk' K)) := by
  obtain ⟨Y, hYX, Z, hZ, hS⟩ := h
  have hYH : Y ≤ H := hYX.trans hXH
  set Y' : Subgroup (↥H ⧸ K) := (Y.subgroupOf H).map (QuotientGroup.mk' K) with hY'
  have hY'le : Y' ≤ (X.subgroupOf H).map (QuotientGroup.mk' K) :=
    Subgroup.map_mono (fun x hx => hYX hx)
  let ι : ↥Y →* ↥H := Subgroup.inclusion hYH
  let φ₀ : ↥Y →* ↥H ⧸ K := (QuotientGroup.mk' K).comp ι
  have hφ₀mem : ∀ y : ↥Y, φ₀ y ∈ Y' := fun y =>
    ⟨ι y, Subgroup.mem_subgroupOf.mpr y.2, rfl⟩
  let φ : ↥Y →* ↥Y' := φ₀.codRestrict Y' hφ₀mem
  have hφ : Function.Surjective φ := by
    rintro ⟨_, ⟨x, hx, rfl⟩⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    rfl
  haveI : IsSimpleGroup (↥Y ⧸ Z) := isSimpleGroup_of_isL2_or_isSz hS
  have hker : φ.ker ≤ (QuotientGroup.mk' Z).ker := by
    have hnorm : (φ.ker.map (QuotientGroup.mk' Z)).Normal :=
      (MonoidHom.normal_ker φ).map _ (QuotientGroup.mk'_surjective Z)
    have hoddN : Odd (Nat.card φ.ker) := by
      have hle : φ.ker.map ι ≤ K := by
        rintro _ ⟨y, hy, rfl⟩
        have h1 : φ y = 1 := hy
        have h2 : φ₀ y = 1 := congrArg Subtype.val h1
        exact (QuotientGroup.eq_one_iff _).mp h2
      have hinj : Function.Injective ι := Subgroup.inclusion_injective hYH
      have hdvd : Nat.card φ.ker ∣ Nat.card K := by
        rw [← Subgroup.card_map_of_injective hinj]
        exact Subgroup.card_dvd_of_le hle
      exact Odd.of_dvd_nat hK hdvd
    have hoddI : Odd (Nat.card (φ.ker.map (QuotientGroup.mk' Z))) :=
      Odd.of_dvd_nat hoddN (Subgroup.card_map_dvd _ _)
    rcases hnorm.eq_bot_or_eq_top with hbot | htop
    · exact (Subgroup.map_eq_bot_iff _).mp hbot
    · exfalso
      have hcard : Nat.card (φ.ker.map (QuotientGroup.mk' Z)) = Nat.card (↥Y ⧸ Z) := by
        rw [htop, Subgroup.card_top]
      rw [hcard] at hoddI
      exact (Nat.not_even_iff_odd.mpr hoddI) (even_card_of_isL2_or_isSz hS)
  let f' : ↥Y' →* ↥Y ⧸ Z :=
    (QuotientGroup.lift φ.ker (QuotientGroup.mk' Z) hker).comp
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm.toMonoidHom
  have hf' : Function.Surjective f' := by
    intro s
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective Z s
    refine ⟨φ y, ?_⟩
    change QuotientGroup.lift φ.ker (QuotientGroup.mk' Z) hker
      ((QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm (φ y)) = _
    have : (QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm (φ y) =
        (QuotientGroup.mk y : ↥Y ⧸ φ.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [this]
    rfl
  exact hasL2SzSection_of_surjective hY'le hS f' hf'

theorem gap19_25_72_of (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G} {t : G}
    {B : Subgroup G} {r : ℕ} (h : Ctx19_10 D V₀ V p L A t B r)
    (h71 : F07.R71 D) (h72 : F07.R72 D) (hKf : K_19_25_noL2SzSection)
    (hsp : IsStronglyPEmbedded p D.M) (hn3 : 3 ≤ S17.nOf L) :
    Gap19_25_72 D V₀ V p L A t B r h := by
  intro A₁ hA₁A hA₁card hrank hsec
  by_contra hNM
  have hp : p.Prime := (D.sig_prime p h.hyp.hp).1
  have hp2 : p ≠ 2 := (D.sig_prime p h.hyp.hp).2
  haveI : Fact p.Prime := ⟨hp⟩
  set H : Subgroup G := normalizer (A₁ : Set G) with hHdef
  have hr : r.Prime := h.hr.1
  have hA₁M : A₁ ≤ D.M := hA₁A.trans (A_le_M_of_ctx19_10 D h)
  have hHtop : H ≠ ⊤ := by
    intro htop
    haveI : A₁.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases D.standing.simple.eq_bot_or_eq_top_of_normal A₁ with hbot | htop'
    · rw [hbot, Subgroup.card_bot] at hA₁card
      exact hr.one_lt.ne hA₁card
    · exact hsp.1 (eq_top_iff.mpr (htop' ▸ hA₁M))
  have hCH : D.M ⊓ centralizer (A₁ : Set G) ≤ H ⊓ D.M :=
    fun x hx => ⟨Subgroup.centralizer_le_normalizer (A₁ : Set G) hx.2, hx.1⟩
  have hrankH : 1 < CFSG.Open.pRank p (H ⊓ D.M) :=
    lt_of_lt_of_le hrank (CFSG.SectionRank.pRank_mono hp.one_lt hCH)
  have h7 : F07.Sec7Hyp D p H := ⟨hp, hp2, hsp, hHtop, hNM, hrankH⟩
  obtain ⟨hFstar, hlist⟩ := h72 p H h7
  obtain ⟨hKodd, hKM, -⟩ := h71 p H h7
  have hdvd : p ∣ Nat.card (H ⊓ D.M : Subgroup G) := by
    have hpow : p ^ 2 ∣ Nat.card (H ⊓ D.M : Subgroup G) :=
      (pow_dvd_pow p hrankH).trans
        (CFSG.RankThreeEvenClassification.Helpers.prime_power_pRank_dvd_card p hp (H ⊓ D.M))
    exact (dvd_pow_self p (by norm_num : (2 : ℕ) ≠ 0)).trans hpow
  have hY : IsStronglyPEmbedded p ((H ⊓ D.M).subgroupOf H) := hsp.subgroupOf hNM hdvd
  have hKle : CFSG.pPrimeCore p ↥H ≤ (H ⊓ D.M).subgroupOf H := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr ⟨x.2, hKM (Subgroup.mem_map_of_mem H.subtype hx)⟩
  have hKcop : ¬ p ∣ Nat.card (CFSG.pPrimeCore p ↥H) :=
    (hp.coprime_iff_not_dvd).mp (CFSG.pPrimeCore_coprime_card (G := ↥H) (p := p))
  have hNbar := hY.map_quotient hKle hKcop
  have hKodd' : Odd (Nat.card (CFSG.pPrimeCore p ↥H)) := by
    have : Nat.card (F07.PPrimeCoreIn p H) = Nat.card (CFSG.pPrimeCore p ↥H) :=
      Subgroup.card_map_of_injective H.subtype_injective
    rwa [← this]
  have hsecHM : HasL2SzSection (S17.nOf L) (H ⊓ D.M) :=
    hasL2SzSection_of_le hsec fun x hx => ⟨Subgroup.centralizer_le_normalizer (A₁ : Set G) hx.1,
      IOf_le_M D p h.hyp.hL.1.1.le hx.2⟩
  have hsecbar := hasL2SzSection_map_of_odd hKodd' inf_le_left hsecHM
  exact hKf (F07.QuotK7 p H) p (F07.ImageModK p H (Opp p H)) hp hp2 hFstar
    (CFSG.pPrimeCore_quotient_eq_bot hp) hlist _ hNbar (S17.nOf L) hn3 hsecbar

theorem three_le_nOf_of_setting1910 {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L : Subgroup G}
    (h : Setting1910 D V₀ V p L) : 3 ≤ S17.nOf L := by
  obtain ⟨-, h1 | h2 | h3⟩ := h
  · obtain ⟨hSp, hodd, -, -⟩ := h1
    obtain ⟨-, hf1, -, hne⟩ := hSp.admissible
    rcases hodd with ⟨k, hk⟩
    rcases Nat.lt_or_ge (S17.nOf L) 3 with hlt | hge
    · exfalso
      have h1 : S17.nOf L = 1 := by omega
      exact hne (by rw [h1]; rfl)
    · exact hge
  · obtain ⟨-, -, hn, -⟩ := h2
    omega
  · obtain ⟨-, hn, -⟩ := h3
    omega

theorem gap19_25_72_of_sigmaStd (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} (h : Ctx19_10 D V₀ V p L A t B r)
    (hSg : UC6S846.SigmaStd D) (h71 : F07.R71 D) (h72 : F07.R72 D)
    (hKf : K_19_25_noL2SzSection) : Gap19_25_72 D V₀ V p L A t B r h :=
  gap19_25_72_of D h h71 h72 hKf
    (hSg.sig1_sp p (UC6S846.sig_subset_sig1 hSg (UC6S846.not_solvable_of_mem_calC h.hyp.hL.1)
      h.hyp.hp))
    (three_le_nOf_of_setting1910 h.h1910)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
