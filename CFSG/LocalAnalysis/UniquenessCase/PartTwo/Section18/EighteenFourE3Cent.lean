module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenFourStruct
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.DeltaAPI
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyEightAut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyEightCentralizer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenGlueB
public import CFSG.GroupTheory.CoprimeCentralizerTransport
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
public import CFSG.GroupTheory.PGroup.CardCoprime
public import CFSG.HardMathSupport.Curtis.Coordinator.AutBounds
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompHatA6

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
    (rankThreeGamma_le_of_two_le_pRank_inf_centralizer)
open CFSG.GroupTheory.CoprimeActionSupport
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem barImage_sup_normal {D : Data G} {V₀ V L K : Subgroup G}
    (c : A5Data18 D V₀ V L) (hK : K ∈ calC D.M) (hKne : K ≠ L)
    (hdich : (UC22.conjClosure D.M L = L ⊔ K ∧ ∃ x ∈ D.M, K = conjSubgroup L x) ∨
      (UC22.conjClosure D.M L = L ∧ (L.subgroupOf D.M).Normal ∧ (K.subgroupOf D.M).Normal)) :
    (barImage D.M (L ⊔ K)).Normal := by
  rcases hdich with ⟨hcl, -⟩ | ⟨-, hLn, hKn⟩
  · rw [← hcl]
    apply s13_barImage_normal
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer c.hyp.X_le_M]
    exact TwelveTwentyThree.le_normalizer_conjClosure D.M L
  · have hLM : L ≤ D.M := s13_le_of_mem_calC c.hyp.hL.1
    have hKM : K ≤ D.M := s13_le_of_mem_calC hK
    apply s13_barImage_normal
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (sup_le hLM hKM)]
    refine (le_inf ?_ ?_).trans (Subgroup.inf_normalizer_le_normalizer_sup L K)
    · exact (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mp hLn
    · exact (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mp hKn

private theorem barImage_sup_inf_centralizer_eq_bot {D : Data G} {L K : Subgroup G}
    (hA : S17.IsA5xA5 ↥(barImage D.M (L ⊔ K))) :
    barImage D.M (L ⊔ K) ⊓
        Subgroup.centralizer (barImage D.M (L ⊔ K) : Set (Bar2 D.M)) = ⊥ :=
  CFSG.AGLEmbedding.inf_centralizer_eq_bot_of_center
    (S17.center_eq_bot_of_isA5xA5 hA)

private theorem pRank_five_barImage_sup_eq_two {D : Data G} {L K : Subgroup G}
    (hA : S17.IsA5xA5 ↥(barImage D.M (L ⊔ K))) :
    CFSG.Open.pRank 5 (barImage D.M (L ⊔ K)) = 2 := by
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
  exact S17.pRank_eq_two_of_isA5xA5 hA (Or.inr rfl)

private theorem pRank_five_centralizer_le_one {D : Data G} {L K : Subgroup G}
    (hA : S17.IsA5xA5 ↥(barImage D.M (L ⊔ K))) (heM : S17.eM D.M = 3) :
    CFSG.Open.pRank 5
      (Subgroup.centralizer (barImage D.M (L ⊔ K) : Set (Bar2 D.M))) ≤ 1 := by
  have hadd := S17.pRank_add_pRank_le_of_le_centralizer (D := D) (X := L ⊔ K)
    Nat.prime_five (by norm_num) hA
    (C := Subgroup.centralizer (barImage D.M (L ⊔ K) : Set (Bar2 D.M))) le_rfl
  have hA2 : CFSG.Open.pRank 5 (barImage D.M (L ⊔ K)) = 2 :=
    pRank_five_barImage_sup_eq_two hA
  have htop : CFSG.Open.pRank 5 (barImage D.M (L ⊔ K) ⊔
      Subgroup.centralizer (barImage D.M (L ⊔ K) : Set (Bar2 D.M))) ≤ 3 := by
    calc CFSG.Open.pRank 5 (barImage D.M (L ⊔ K) ⊔
          Subgroup.centralizer (barImage D.M (L ⊔ K) : Set (Bar2 D.M)))
        ≤ CFSG.Open.pRank 5 (⊤ : Subgroup (Bar2 D.M)) :=
          CFSG.SectionRank.pRank_mono (by norm_num) le_top
      _ = CFSG.Open.pRank 5 D.M := s13_pRank_bar_top Nat.prime_five (by norm_num) D.M
      _ ≤ S17.eM D.M := S17.pRank_le_eM_of_odd_prime Nat.prime_five (by norm_num)
      _ = 3 := heM
  omega

private theorem exists_cyclic_five_subgroup_centralizer {D : Data G} {V₀ V L K : Subgroup G}
    (c : A5Data18 D V₀ V L)
    (hAn : (barImage D.M (L ⊔ K)).Normal)
    (hA : S17.IsA5xA5 ↥(barImage D.M (L ⊔ K))) :
    ∃ (Z : Subgroup (Bar2 D.M)) (e : ℕ),
      Z = CFSG.RankThree.PartOne.pElementSubgroup 5
        (Subgroup.centralizer (barImage D.M (L ⊔ K) : Set (Bar2 D.M))) ∧ 1 ≤ e ∧
      Z ≤ Subgroup.centralizer (barImage D.M (L ⊔ K) : Set (Bar2 D.M)) ∧
      IsPGroup 5 Z ∧ IsCyclic ↥Z ∧ Nat.card Z = 5 ^ e ∧ Z ≠ ⊥ := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let Q := CFSG.RankThree.PartOne.pElementSubgroup 5 (⊤ : Subgroup (Bar2 D.M))
  let C := Subgroup.centralizer (barImage D.M (L ⊔ K) : Set (Bar2 D.M))
  let Z := CFSG.RankThree.PartOne.pElementSubgroup 5 C
  obtain ⟨e, he1, ⟨m⟩⟩ := c.shape
  have hcardA5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have : (barImage D.M (L ⊔ K)).Normal := hAn
  have hQsup : Q = barImage D.M (L ⊔ K) ⊔ Z :=
    S17.pElementSubgroup_top_eq_sup_of_isA5xA5 (Q := Bar2 D.M) (A := barImage D.M (L ⊔ K)) hA
  have hZle : Z ≤ C := s13_Thirteen2_pElementSubgroup_le 5 C
  have hdisj : barImage D.M (L ⊔ K) ⊓ Z = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    have hx' : x ∈ barImage D.M (L ⊔ K) ⊓ C := ⟨hx.1, hZle hx.2⟩
    rw [barImage_sup_inf_centralizer_eq_bot hA] at hx'
    simpa using hx'
  have hcomm : ∀ a ∈ barImage D.M (L ⊔ K), ∀ b ∈ Z, a * b = b * a := by
    intro a ha b hb
    exact Subgroup.mem_centralizer_iff.mp (hZle hb) a ha
  have hZmod : Nat.card (Multiplicative (ZMod (5 ^ e))) = 5 ^ e := by
    rw [Nat.card_congr
      (Multiplicative.ofAdd : ZMod (5 ^ e) ≃ Multiplicative (ZMod (5 ^ e))).symm,
      Nat.card_zmod]
  have hcardQ : Nat.card ↥Q = 3600 * 5 ^ e := by
    rw [Nat.card_congr m.toEquiv]
    simp only [Nat.card_prod, hcardA5, hZmod]
    ring
  have hcardA : Nat.card ↥(barImage D.M (L ⊔ K)) = 3600 := by
    obtain ⟨eA⟩ := hA
    rw [Nat.card_congr eA.toEquiv, Nat.card_prod, hcardA5]
  have hprod : ↥(barImage D.M (L ⊔ K)) × ↥Z ≃* ↥Q := by
    rw [hQsup]
    exact CFSG.Quasithin.Vol2.Ch10.SecE.prodEquivSup hcomm hdisj
  have hcardZ : Nat.card Z = 5 ^ e := by
    have hmul : 3600 * 5 ^ e = 3600 * Nat.card Z := by
      rw [← hcardQ, ← Nat.card_congr hprod.toEquiv, Nat.card_prod, hcardA]
    have hmul' : Nat.card Z * 3600 = 5 ^ e * 3600 := by
      rw [mul_comm (Nat.card Z) 3600, mul_comm (5 ^ e) 3600]
      exact hmul.symm
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 3600) hmul'
  have hZP : IsPGroup 5 Z := IsPGroup.of_card (n := e) hcardZ
  have hZrank : CFSG.Open.pRank 5 Z ≤ 1 :=
    (CFSG.SectionRank.pRank_mono (p := 5) (by norm_num) hZle).trans
      (pRank_five_centralizer_le_one (D := D) (L := L) (K := K) hA c.eM)
  have hZcyc : IsCyclic ↥Z :=
    CFSG.Quasithin.isCyclic_of_pRank_le_one (p := 5) (by norm_num) le_rfl hZP hZrank
  have hZne : Z ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card Z = 1 := by rw [hbot, Subgroup.card_bot]
    rw [hcardZ] at h1
    have : 5 ^ e ≠ 1 := by
      have : 1 < 5 ^ e := Nat.one_lt_pow (by omega) (by norm_num)
      omega
    exact this h1
  exact ⟨Z, e, rfl, he1, hZle, hZP, hZcyc, hcardZ, hZne⟩

private theorem exists_central_pair_of_sylow_three {B : Type} [Group B] [Finite B]
    {A L₀ K₀ : Subgroup B} [A.Normal]
    (hAalt : S17.IsA5xA5 ↥A) (hOutA : IsPGroup 2 (Outer ↥A))
    (h3C : 3 ∣ Nat.card ↥(Subgroup.centralizer (A : Set B)))
    (hsup : A = L₀ ⊔ K₀) (hL₀alt : UC22.IsAlt ↥L₀ 5)
    (hcommLK : ∀ l ∈ L₀, ∀ k ∈ K₀, l * k = k * l)
    {P : Subgroup B} (hPsyl : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤) :
    ∃ r z : B, r ∈ P ⊓ L₀ ∧ z ∈ P ⊓ Subgroup.centralizer (A : Set B) ∧
      orderOf r = 3 ∧ orderOf z = 3 ∧ r * z = z * r ∧
      (∀ x ∈ P, r * x = x * r) ∧ (∀ x ∈ P, z * x = x * z) ∧
      (∀ i j : Fin 3, r ^ (i : ℕ) * z ^ (j : ℕ) = 1 → i = 0 ∧ j = 0) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let C : Subgroup B := Subgroup.centralizer (A : Set B)
  have hCn : C.Normal := Subgroup.normal_centralizer
  have hAC : A ⊓ C = ⊥ :=
    CFSG.AGLEmbedding.inf_centralizer_eq_bot_of_center (S17.center_eq_bot_of_isA5xA5 hAalt)
  have hP3 : IsPGroup 3 P := hPsyl.isPGroup
  have hOut3 : ¬ 3 ∣ Nat.card (Outer ↥A) :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup hOutA Nat.prime_three (by norm_num)
  have hPN : P ≤ Subgroup.normalizer (A : Set B) :=
    le_top.trans (Subgroup.normalizer_eq_top_iff.mpr ‹A.Normal›).ge
  have hPle : P ≤ A ⊔ C :=
    CFSG.HardMathSupport.Curtis.Coordinator.le_sup_centralizer_of_isPGroup_of_not_dvd
      Nat.prime_three hPN hP3 hOut3
  have hPsylAC : CFSG.ABGLocalTools.IsSylowOf 3 P (A ⊔ C) := hPsyl.of_le hPle le_top
  have hNA : A ⊔ C ≤ Subgroup.normalizer (A : Set B) :=
    le_top.trans (Subgroup.normalizer_eq_top_iff.mpr ‹A.Normal›).ge
  have hNC : A ⊔ C ≤ Subgroup.normalizer (C : Set B) :=
    le_top.trans (Subgroup.normalizer_eq_top_iff.mpr hCn).ge
  have hPAsyl : CFSG.ABGLocalTools.IsSylowOf 3 (P ⊓ A) A :=
    hPsylAC.inf_of_le_normalizer le_sup_left hNA
  have hPCsyl : CFSG.ABGLocalTools.IsSylowOf 3 (P ⊓ C) C :=
    hPsylAC.inf_of_le_normalizer le_sup_right hNC
  have hcardA5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hcardA : Nat.card ↥A = 3600 := by
    obtain ⟨eA⟩ := hAalt
    rw [Nat.card_congr eA.toEquiv, Nat.card_prod, hcardA5]
  have hPAcard : Nat.card ↥(P ⊓ A) = 9 := by
    rw [hPAsyl.card_eq, hcardA]
    norm_num [Nat.factorization]
  have hPCcard3 : 3 ∣ Nat.card ↥(P ⊓ C) := by
    have hmul := Subgroup.relIndex_mul_card (H := P ⊓ C) (K := C)
    have hinf : (P ⊓ C) ⊓ C = P ⊓ C := inf_of_le_left inf_le_right
    rw [hinf] at hmul
    have hrel : ¬ 3 ∣ (P ⊓ C).relIndex C :=
      (CFSG.ABGLocalTools.isSylowOf_iff.mp hPCsyl).2.2
    have h3 := h3C
    rw [← hmul] at h3
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h | h
    · exact absurd h hrel
    · exact h
  have : Nontrivial ↥(P ⊓ C) := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    have := Nat.le_of_dvd Nat.card_pos hPCcard3
    omega
  have hPC3 : IsPGroup 3 ↥(P ⊓ C) := hPCsyl.isPGroup
  have hACcent : A ≤ Subgroup.centralizer (C : Set B) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact (Subgroup.mem_centralizer_iff.mp hc a ha).symm
  have hcardAC : Nat.card ↥(A ⊔ C) = Nat.card ↥A * Nat.card ↥C := by
    have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := A) (K := C) (hACcent.trans (Subgroup.centralizer_le_normalizer _))
    rwa [hAC, Subgroup.card_bot, mul_one] at h
  have hPcard : Nat.card ↥P = Nat.card ↥(P ⊓ A) * Nat.card ↥(P ⊓ C) := by
    rw [hPsylAC.card_eq, hPAsyl.card_eq, hPCsyl.card_eq, hcardAC,
      Nat.factorization_mul (Nat.card_pos (α := A)).ne' (Nat.card_pos (α := C)).ne',
      ← pow_add]
    rfl
  have hPAcent : P ⊓ A ≤ Subgroup.centralizer (P ⊓ C : Set B) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact (Subgroup.mem_centralizer_iff.mp hc.2 a ha.2).symm
  have hdisjPAC : (P ⊓ A) ⊓ (P ⊓ C) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxAC : x ∈ A ⊓ C := ⟨hx.1.2, hx.2.2⟩
    rw [hAC, Subgroup.mem_bot] at hxAC
    exact Subgroup.mem_bot.mpr hxAC
  have hsupPAC : (P ⊓ A) ⊔ (P ⊓ C) = P := by
    refine eq_of_le_of_card_ge (sup_le inf_le_left inf_le_left) ?_
    have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := P ⊓ A) (K := P ⊓ C) (hPAcent.trans (Subgroup.centralizer_le_normalizer _))
    rw [hdisjPAC, Subgroup.card_bot, mul_one] at h
    rw [hPcard]
    exact h.ge
  have hdecomp : ∀ x ∈ P, ∃ a ∈ P ⊓ A, ∃ c ∈ P ⊓ C, x = a * c := by
    intro x hx
    let PA : Subgroup P := (P ⊓ A).subgroupOf P
    let PC : Subgroup P := (P ⊓ C).subgroupOf P
    have hcommP : ∀ a ∈ PA, ∀ c ∈ PC, a * c = c * a := by
      intro a ha c hc
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hPAcent (Subgroup.mem_subgroupOf.mp ha))
        ((c : P) : B) (Subgroup.mem_subgroupOf.mp hc)).symm
    have hdisjP : PA ⊓ PC = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      have hyA : (y : B) ∈ P ⊓ A := Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hy).1
      have hyC : (y : B) ∈ P ⊓ C := Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hy).2
      have hyb : (y : B) ∈ A ⊓ C := ⟨hyA.2, hyC.2⟩
      rw [hAC, Subgroup.mem_bot] at hyb
      exact Subgroup.mem_bot.mpr (Subtype.ext hyb)
    have hjoin : PA ⊔ PC = ⊤ := by
      rw [← Subgroup.subgroupOf_sup (inf_le_left : P ⊓ A ≤ P) (inf_le_left : P ⊓ C ≤ P),
        hsupPAC, Subgroup.subgroupOf_self]
    obtain ⟨⟨⟨a, ha⟩, ⟨c, hc⟩⟩, hac⟩ :=
      (CFSG.Quasithin.Vol2.Ch10.SecE.prodEquivSup hcommP hdisjP).surjective
        ⟨⟨x, hx⟩, by rw [hjoin]; exact Subgroup.mem_top _⟩
    have hcoe := CFSG.Quasithin.Vol2.Ch10.SecE.coe_prodEquivSup hcommP hdisjP
      (⟨a, ha⟩, ⟨c, hc⟩)
    rw [hac] at hcoe
    exact ⟨(a : B), Subgroup.mem_subgroupOf.mp ha, (c : B), Subgroup.mem_subgroupOf.mp hc,
      congrArg Subtype.val hcoe⟩
  have hL₀A : L₀ ≤ A := by rw [hsup]; exact le_sup_left
  have hNL₀ : A ≤ Subgroup.normalizer (L₀ : Set B) := by
    rw [hsup]
    refine sup_le Subgroup.le_normalizer ?_
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro l
    constructor
    · intro hl
      have h := hcommLK l hl k hk
      have h1 : k * l * k⁻¹ = l := by
        calc k * l * k⁻¹ = (l * k) * k⁻¹ := by rw [← h]
          _ = l := by group
      rwa [h1]
    · intro hl
      have h := hcommLK (k * l * k⁻¹) hl k hk
      have h1 : l = k⁻¹ * (k * l * k⁻¹) * k := by group
      have h2 : k⁻¹ * (k * l * k⁻¹) * k = k * l * k⁻¹ := by
        calc k⁻¹ * (k * l * k⁻¹) * k = k⁻¹ * ((k * l * k⁻¹) * k) := by group
          _ = k⁻¹ * (k * (k * l * k⁻¹)) := by rw [h]
          _ = k * l * k⁻¹ := by group
      rw [h1, h2]
      exact hl
  have hPL₀syl : CFSG.ABGLocalTools.IsSylowOf 3 (P ⊓ L₀) L₀ := by
    have h := hPAsyl.inf_of_le_normalizer hL₀A hNL₀
    rwa [inf_assoc, inf_eq_right.mpr hL₀A] at h
  have hcardL₀ : Nat.card ↥L₀ = 60 :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Om8Excl.card_isAlt_five hL₀alt
  have hPL₀card : Nat.card ↥(P ⊓ L₀) = 3 := by
    rw [hPL₀syl.card_eq, hcardL₀, Nat.factorization_def _ Nat.prime_three]
    rw [show (60 : ℕ) = 20 * 3 by norm_num,
      padicValNat.mul (by norm_num) (by norm_num),
      padicValNat.eq_zero_of_not_dvd (by norm_num), padicValNat.self] <;>
      norm_num
  obtain ⟨rP, hrPord⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(P ⊓ L₀)) 3 (by rw [hPL₀card])
  have hPCne : P ⊓ C ≠ ⊥ := by
    rintro h
    rw [h, Subgroup.card_bot] at hPCcard3
    omega
  obtain ⟨zP, hzPC, hzPord, hzPcomm⟩ :=
    CFSG.AGLEmbedding.exists_center_orderOf_eq (G := B) (p := 3) hPC3 hPCne
  refine ⟨(rP : B), zP, rP.2, hzPC, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, hrPord]
  · exact hzPord
  · exact Subgroup.mem_centralizer_iff.mp hzPC.2 (rP : B) (hL₀A rP.2.2)
  ·
    intro x hx
    obtain ⟨a, ha, c, hc, rfl⟩ := hdecomp x hx
    have hra : (rP : B) * a = a * (rP : B) := by
      let : CommGroup ↥(P ⊓ A) :=
        (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hPAcard).instCommGroup
      exact congrArg Subtype.val
        (mul_comm (⟨(rP : B), ⟨rP.2.1, hL₀A rP.2.2⟩⟩ : ↥(P ⊓ A)) ⟨a, ha⟩)
    have hrc : (rP : B) * c = c * (rP : B) :=
      Subgroup.mem_centralizer_iff.mp hc.2 (rP : B) (hL₀A rP.2.2)
    calc (rP : B) * (a * c) = ((rP : B) * a) * c := by group
      _ = (a * (rP : B)) * c := by rw [hra]
      _ = a * ((rP : B) * c) := by group
      _ = a * (c * (rP : B)) := by rw [hrc]
      _ = (a * c) * (rP : B) := by group
  ·
    intro x hx
    obtain ⟨a, ha, c, hc, rfl⟩ := hdecomp x hx
    have hza : zP * a = a * zP :=
      (Subgroup.mem_centralizer_iff.mp hzPC.2 a ha.2).symm
    have hzc : zP * c = c * zP := (hzPcomm c hc).eq
    calc zP * (a * c) = (zP * a) * c := by group
      _ = (a * zP) * c := by rw [hza]
      _ = a * (zP * c) := by group
      _ = a * (c * zP) := by rw [hzc]
      _ = (a * c) * zP := by group
  ·
    intro i j hij
    have hmemA : (rP : B) ^ (i : ℕ) ∈ A := A.pow_mem (hL₀A rP.2.2) _
    have heq : (rP : B) ^ (i : ℕ) = (zP ^ (j : ℕ))⁻¹ :=
      eq_inv_of_mul_eq_one_left hij
    have hmemC : (zP ^ (j : ℕ))⁻¹ ∈ C := C.inv_mem (C.pow_mem hzPC.2 _)
    have hmem : (rP : B) ^ (i : ℕ) ∈ A ⊓ C := ⟨hmemA, heq ▸ hmemC⟩
    rw [hAC, Subgroup.mem_bot] at hmem
    have hri : (rP : B) ^ (i : ℕ) = 1 := hmem
    have hi : (i : ℕ) = 0 := by
      have hdvd := orderOf_dvd_of_pow_eq_one hri
      rw [Subgroup.orderOf_coe, hrPord] at hdvd
      have hi3 : (i : ℕ) < 3 := i.isLt
      omega
    have hj : (j : ℕ) = 0 := by
      have hzpow : zP ^ (j : ℕ) = 1 := by
        rw [hri, one_mul] at hij
        exact hij
      have hdvd := orderOf_dvd_of_pow_eq_one hzpow
      rw [hzPord] at hdvd
      have hj3 : (j : ℕ) < 3 := j.isLt
      omega
    exact ⟨Fin.ext hi, Fin.ext hj⟩

theorem A5Data18.stronglyEmbedded_three
    {D : Data G} {V₀ V L K : Subgroup G}
    (c : A5Data18 D V₀ V L)
    (hK : K ∈ calC D.M) (hKne : K ≠ L) (hAltK : UC22.IsAlt (Bar2 K) 5)
    (hcomm : ⁅L, K⁆ ≤ pCoreOf 2 D.M)
    (hdich : (UC22.conjClosure D.M L = L ⊔ K ∧ ∃ x ∈ D.M, K = conjSubgroup L x) ∨
      (UC22.conjClosure D.M L = L ∧ (L.subgroupOf D.M).Normal ∧ (K.subgroupOf D.M).Normal))
    (h76 : UC22.F07.R76Sig D) (h614 : UC6.R6_14 D) (hSg : UC6S846.SigmaStd D)
    (h1768 : S17.R17_68At D V₀ V)
    (h3 : 3 ∣ Nat.card ↥(Subgroup.centralizer (barImage D.M (L ⊔ K) : Set (Bar2 D.M)))) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hLM : L ≤ D.M := s13_le_of_mem_calC c.hyp.hL.1
  have hKM : K ≤ D.M := s13_le_of_mem_calC hK
  let B := Bar2 D.M
  let A : Subgroup B := barImage D.M (L ⊔ K)
  let C : Subgroup B := Subgroup.centralizer (A : Set B)
  let L₀ : Subgroup B := barImage D.M L
  let K₀ : Subgroup B := barImage D.M K
  have hcommLK : ∀ a ∈ L₀, ∀ b ∈ K₀, a * b = b * a :=
    modO2Image_commute hcomm
  have hA5 : S17.IsA5xA5 ↥A :=
    isA5xA5_barImage_sup_of_calC c.hyp.hL.1 hK hKne c.alt hAltK hcommLK
  have hAn : A.Normal := barImage_sup_normal c hK hKne hdich
  have hAC : A ⊓ C = ⊥ :=
    CFSG.AGLEmbedding.inf_centralizer_eq_bot_of_center (S17.center_eq_bot_of_isA5xA5 hA5)
  have h3C : 3 ∣ Nat.card ↥C := h3
  have hOutA : IsPGroup 2 (Outer ↥A) := S17.isPGroup_two_outer_of_isA5xA5 hA5
  have hsupA : A = L₀ ⊔ K₀ := s13_barImage_sup hLM hKM
  have hL₀alt : UC22.IsAlt ↥L₀ 5 := by
    obtain ⟨e1⟩ := c.alt
    obtain ⟨e2⟩ := s13_bar_equiv c.hyp.hL.1
    exact ⟨e2.symm.trans e1⟩
  obtain ⟨R, hRsyl⟩ := CFSG.ABGLocalTools.exists_isSylowOf (G := G) 3 D.M
  have hRM : R ≤ D.M := hRsyl.le
  obtain ⟨Q, hQeq⟩ := hRsyl.exists_sylow_eq_subgroupOf
  let Qsub : Subgroup ↥D.M := Q
  let θ : ↥D.M →* B := QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)
  let P : Subgroup B := Qsub.map θ
  have hQsub_eq : Qsub = R.subgroupOf D.M := hQeq
  have hP_eq : P = barImage D.M R := by
    rw [barImage, ← hQsub_eq]
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤ := by
    let Sbar : Sylow 3 B := Sylow.mapSurjective (f := θ) (QuotientGroup.mk'_surjective _) Q
    refine ⟨Sbar.subtype le_top, ?_⟩
    rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le le_top, Sylow.coe_mapSurjective]
  obtain ⟨r, z, hrPL₀, hzPC, hrord, hzord, hrz, hrc, hzc, hind⟩ :=
    exists_central_pair_of_sylow_three (A := A) (L₀ := L₀) (K₀ := K₀)
      hA5 hOutA h3C hsupA hL₀alt hcommLK hPsyl
  have hN2 : IsPGroup 2 (CFSG.pCore 2 ↥D.M) := CFSG.pCore_isPGroup
  have hN3 : ¬ 3 ∣ Nat.card ↥(CFSG.pCore 2 ↥D.M) :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup hN2 Nat.prime_three (by norm_num)
  have hN5 : ¬ 5 ∣ Nat.card ↥(CFSG.pCore 2 ↥D.M) :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup hN2 Nat.prime_five (by norm_num)
  have hQ3 : IsPGroup 3 Qsub := show IsPGroup 3 Qsub from Q.isPGroup'
  have hbot : Qsub ⊓ CFSG.pCore 2 ↥D.M = ⊥ :=
    CFSG.GroupTheory.SteinbergBS.inf_eq_bot_of_isPGroup_of_not_dvd hN3 hQ3
  obtain ⟨rM, hrMQ, hrMmap⟩ :=
    Subgroup.mem_map.mp (show r ∈ Qsub.map θ from hrPL₀.1)
  have hrM3 : rM ^ 3 = 1 := by
    have hmem : rM ^ 3 ∈ Qsub ⊓ CFSG.pCore 2 ↥D.M := by
      refine ⟨Qsub.pow_mem hrMQ 3, ?_⟩
      have hk : rM ^ 3 ∈ (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)).ker :=
        MonoidHom.mem_ker.mpr (by rw [map_pow, hrMmap, ← hrord]; exact pow_orderOf_eq_one r)
      rwa [QuotientGroup.ker_mk'] at hk
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem
  have hrMne : rM ≠ 1 := by
    intro h1
    rw [h1, map_one] at hrMmap
    have h2 : orderOf r = 1 := by rw [← hrMmap]; exact orderOf_one
    rw [hrord] at h2
    omega
  have hrMord : orderOf rM = 3 := orderOf_eq_prime hrM3 hrMne
  obtain ⟨zM, hzMQ, hzMmap⟩ :=
    Subgroup.mem_map.mp (show z ∈ Qsub.map θ from hzPC.1)
  have hzM3 : zM ^ 3 = 1 := by
    have hmem : zM ^ 3 ∈ Qsub ⊓ CFSG.pCore 2 ↥D.M := by
      refine ⟨Qsub.pow_mem hzMQ 3, ?_⟩
      have hk : zM ^ 3 ∈ (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)).ker :=
        MonoidHom.mem_ker.mpr (by rw [map_pow, hzMmap, ← hzord]; exact pow_orderOf_eq_one z)
      rwa [QuotientGroup.ker_mk'] at hk
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem
  have hzMne : zM ≠ 1 := by
    intro h1
    rw [h1, map_one] at hzMmap
    have h2 : orderOf z = 1 := by rw [← hzMmap]; exact orderOf_one
    rw [hzord] at h2
    omega
  have hzMord : orderOf zM = 3 := orderOf_eq_prime hzM3 hzMne
  have hrGR : (rM : G) ∈ R := by
    have h := hrMQ
    rw [hQsub_eq] at h
    exact Subgroup.mem_subgroupOf.mp h
  have hzGR : (zM : G) ∈ R := by
    have h := hzMQ
    rw [hQsub_eq] at h
    exact Subgroup.mem_subgroupOf.mp h
  have hrGord : orderOf (rM : G) = 3 := (Subgroup.orderOf_coe rM).trans hrMord
  have hzGord : orderOf (zM : G) = 3 := (Subgroup.orderOf_coe zM).trans hzMord
  have hrG3 : (rM : G) ^ 3 = 1 := by rw [← hrGord]; exact pow_orderOf_eq_one _
  have hzG3 : (zM : G) ^ 3 = 1 := by rw [← hzGord]; exact pow_orderOf_eq_one _
  have hcommM : rM * zM = zM * rM := by
    have h1 : θ (rM * zM) = θ (zM * rM) := by
      simp [θ, map_mul, hrMmap, hzMmap, hrz]
    have hmem : rM * zM * (zM * rM)⁻¹ ∈ Qsub ⊓ CFSG.pCore 2 ↥D.M := by
      refine ⟨?_, ?_⟩
      · exact Qsub.mul_mem
          (Qsub.mul_mem hrMQ hzMQ)
          (Qsub.inv_mem (Qsub.mul_mem hzMQ hrMQ))
      · have hk : rM * zM * (zM * rM)⁻¹ ∈
            (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)).ker :=
          MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, h1, mul_inv_cancel])
        rwa [QuotientGroup.ker_mk'] at hk
    rw [hbot, Subgroup.mem_bot] at hmem
    exact mul_inv_eq_one.mp hmem
  have hrcR : ∀ x ∈ R, (rM : G) * x = x * (rM : G) := by
    intro x hx
    let xM : ↥D.M := ⟨x, hRM hx⟩
    have hxMQ : xM ∈ Qsub := by
      rw [hQsub_eq]; exact Subgroup.mem_subgroupOf.mpr hx
    have hcentral : r * θ xM = θ xM * r := hrc (θ xM) (Subgroup.mem_map_of_mem θ hxMQ)
    have h1 : θ (rM * xM * (xM * rM)⁻¹) = 1 := by
      rw [map_mul, map_inv,
        show θ (rM * xM) = r * θ xM from by rw [map_mul, hrMmap],
        show θ (xM * rM) = θ xM * r from by rw [map_mul, hrMmap],
        hcentral, mul_inv_cancel]
    have hmem : rM * xM * (xM * rM)⁻¹ ∈ Qsub ⊓ CFSG.pCore 2 ↥D.M := by
      refine ⟨?_, ?_⟩
      · exact Qsub.mul_mem
          (Qsub.mul_mem hrMQ hxMQ)
          (Qsub.inv_mem (Qsub.mul_mem hxMQ hrMQ))
      · have hk : rM * xM * (xM * rM)⁻¹ ∈
            (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)).ker := MonoidHom.mem_ker.mpr h1
        rwa [QuotientGroup.ker_mk'] at hk
    rw [hbot, Subgroup.mem_bot] at hmem
    have h2 := mul_inv_eq_one.mp hmem
    simpa [xM, map_mul] using congrArg D.M.subtype h2
  have hzcR : ∀ x ∈ R, (zM : G) * x = x * (zM : G) := by
    intro x hx
    let xM : ↥D.M := ⟨x, hRM hx⟩
    have hxMQ : xM ∈ Qsub := by
      rw [hQsub_eq]; exact Subgroup.mem_subgroupOf.mpr hx
    have hcentral : z * θ xM = θ xM * z := hzc (θ xM) (Subgroup.mem_map_of_mem θ hxMQ)
    have h1 : θ (zM * xM * (xM * zM)⁻¹) = 1 := by
      rw [map_mul, map_inv,
        show θ (zM * xM) = z * θ xM from by rw [map_mul, hzMmap],
        show θ (xM * zM) = θ xM * z from by rw [map_mul, hzMmap],
        hcentral, mul_inv_cancel]
    have hmem : zM * xM * (xM * zM)⁻¹ ∈ Qsub ⊓ CFSG.pCore 2 ↥D.M := by
      refine ⟨?_, ?_⟩
      · exact Qsub.mul_mem
          (Qsub.mul_mem hzMQ hxMQ)
          (Qsub.inv_mem (Qsub.mul_mem hxMQ hzMQ))
      · have hk : zM * xM * (xM * zM)⁻¹ ∈
            (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)).ker := MonoidHom.mem_ker.mpr h1
        rwa [QuotientGroup.ker_mk'] at hk
    rw [hbot, Subgroup.mem_bot] at hmem
    have h2 := mul_inv_eq_one.mp hmem
    simpa [xM, map_mul] using congrArg D.M.subtype h2
  have hrzG : (rM : G) * zM = zM * (rM : G) := by
    simpa [map_mul] using congrArg D.M.subtype hcommM
  have hindG : ∀ i j : Fin 3, (rM : G) ^ (i : ℕ) * (zM : G) ^ (j : ℕ) = 1 → i = 0 ∧ j = 0 := by
    intro i j hij
    have hM : rM ^ (i : ℕ) * zM ^ (j : ℕ) = 1 := by
      apply D.M.subtype_injective
      simpa [map_mul, map_pow] using hij
    apply hind i j
    have h1 : θ (rM ^ (i : ℕ) * zM ^ (j : ℕ)) = r ^ (i : ℕ) * z ^ (j : ℕ) := by
      rw [map_mul, map_pow, map_pow, hrMmap, hzMmap]
    rw [← h1, hM, map_one]
  obtain ⟨E, hEea, hEcard, hEsub⟩ :=
    CFSG.Quasithin.H13.S126C.exists_elemAbelian_nine_le_closure (G := G)
      hrzG hrG3 hzG3 hindG
  have hclosureR : Subgroup.closure ({(rM : G), (zM : G)} : Set G) ≤ R := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hrGR
    · exact hzGR
  have hER : E ≤ R := hEsub.trans hclosureR
  have hEcent : E ≤ Subgroup.centralizer (R : Set G) := by
    refine hEsub.trans ?_
    rw [Subgroup.closure_le]
    intro x hx
    change x ∈ Subgroup.centralizer (R : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases hx with h | h
    · rw [h]; exact (hrcR y hy).symm
    · rw [h]; exact (hzcR y hy).symm
  have hEM : E ≤ D.M := hER.trans hRM
  obtain ⟨Z, e, hZdef, he1, hZleC, hZP, hZcyc, hZcard, hZne⟩ :=
    exists_cyclic_five_subgroup_centralizer (D := D) (V₀ := V₀) (V := V) (L := L) (K := K)
      c hAn hA5
  let Ebar : Subgroup B := Subgroup.closure ({r, z} : Set B)
  have hK₀A : K₀ ≤ A := by rw [hsupA]; exact le_sup_right
  have hL₀A : L₀ ≤ A := by rw [hsupA]; exact le_sup_left
  have hEclosureM : E.subgroupOf D.M ≤ Subgroup.closure ({rM, zM} : Set ↥D.M) := by
    intro x hx
    have hx' : D.M.subtype x ∈ E := Subgroup.mem_subgroupOf.mp hx
    have hx'' : D.M.subtype x ∈ Subgroup.closure ({(rM : G), (zM : G)} : Set G) := hEsub hx'
    rw [show Subgroup.closure ({(rM : G), (zM : G)} : Set G) =
        (Subgroup.closure ({rM, zM} : Set ↥D.M)).map D.M.subtype from ?_] at hx''
    · obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx''
      rwa [D.M.subtype_injective hyx] at hy
    · rw [MonoidHom.map_closure]
      congr 1
      ext y
      simp
  have hEbar_le : barImage D.M E ≤ Ebar := by
    have h := Subgroup.map_mono (f := θ) hEclosureM
    have h2 : (Subgroup.closure ({rM, zM} : Set ↥D.M)).map θ = Ebar := by
      rw [MonoidHom.map_closure]
      congr 1
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        rcases hx with rfl | rfl
        · rw [hrMmap]; exact Or.inl rfl
        · rw [hzMmap]; exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨rM, Or.inl rfl, hrMmap⟩
        · exact ⟨zM, Or.inr rfl, hzMmap⟩
    rwa [h2] at h
  have hEbar_le_centK : Ebar ≤ Subgroup.centralizer (K₀ : Set B) := by
    rw [Subgroup.closure_le]
    intro y hy
    change y ∈ Subgroup.centralizer (K₀ : Set B)
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    rcases hy with h | h
    · rw [h]; exact (hcommLK r hrPL₀.2 k hk).symm
    · rw [h]; exact Subgroup.mem_centralizer_iff.mp hzPC.2 k (hK₀A hk)
  have hK₀_le : K₀ ≤ Subgroup.centralizer (Ebar : Set B) := by
    intro k hk
    change k ∈ Subgroup.centralizer (Ebar : Set B)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hEbar_le_centK hy) k hk).symm
  have hZC : Z ≤ C := hZleC
  have hZinv : ∀ y ∈ Z, z * y * z⁻¹ ∈ Z := by
    rw [hZdef]
    simpa [C, A, CFSG.LocalAnalysis.UniquenessCase.UC22.Opp, inv_inv] using
      s13_Bar13_opp_conjInv (p := 5) (M := C) (X := C)
      (fun g hg x hx => C.mul_mem (C.mul_mem hg hx) (C.inv_mem hg)) z hzPC.2
  have hZinv' : ∀ y ∈ Z, z⁻¹ * y * z ∈ Z := by
    rw [hZdef]
    have h := s13_Bar13_opp_conjInv (p := 5) (M := C) (X := C)
      (fun g hg x hx => C.mul_mem (C.mul_mem hg hx) (C.inv_mem hg)) z⁻¹ (C.inv_mem hzPC.2)
    intro y hy
    have h' := h y hy
    rwa [inv_inv] at h'
  have hzN : z ∈ Subgroup.normalizer (Z : Set B) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact hZinv y
    · intro hy
      have h := hZinv' (z * y * z⁻¹) hy
      rwa [show z⁻¹ * (z * y * z⁻¹) * z = y by group] at h
  let φ : MulAut ↥Z := Z.normalizerMonoidHom ⟨z, hzN⟩
  have hφapply : ∀ y : ↥Z, ((φ y : ↥Z) : B) = z * (y : B) * z⁻¹ :=
    fun y => Subgroup.normalizerMonoidHom_apply_apply_coe Z ⟨z, hzN⟩ y
  have hz3 : z ^ 3 = 1 := by rw [← hzord]; exact pow_orderOf_eq_one z
  have hφ3 : φ ^ 3 = 1 := by
    have hzNpow : (⟨z, hzN⟩ : Subgroup.normalizer (Z : Set B)) ^ 3 = 1 := by
      ext
      simpa using hz3
    rw [show φ = Z.normalizerMonoidHom ⟨z, hzN⟩ from rfl, ← map_pow, hzNpow, map_one]
  have hord3 : orderOf φ ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hφ3
  have hcardAut : Nat.card (MulAut ↥Z) = 4 * 5 ^ (e - 1) := by
    rw [IsCyclic.card_mulAut, hZcard,
      Nat.totient_prime_pow Nat.prime_five (by omega), Nat.mul_comm]
  have hordAut : orderOf φ ∣ Nat.card (MulAut ↥Z) := orderOf_dvd_natCard φ
  have hφ1 : φ = 1 := by
    have hdvd : orderOf φ ∣ Nat.gcd 3 (Nat.card (MulAut ↥Z)) := Nat.dvd_gcd hord3 hordAut
    rw [hcardAut] at hdvd
    have hgcd : Nat.gcd 3 (4 * 5 ^ (e - 1)) = 1 :=
      Nat.coprime_iff_gcd_eq_one.mp
        (Nat.Coprime.mul_right (by norm_num) (Nat.Coprime.pow_right _ (by norm_num)))
    rw [hgcd] at hdvd
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)
  have hzZ : ∀ y ∈ Z, z * y = y * z := by
    intro y hy
    have h := congrArg (fun ψ : MulAut ↥Z => ((ψ ⟨y, hy⟩ : ↥Z) : B)) hφ1
    rw [show ((φ ⟨y, hy⟩ : ↥Z) : B) = z * y * z⁻¹ from hφapply ⟨y, hy⟩,
      MulAut.one_apply] at h
    calc z * y = (z * y * z⁻¹) * z := by group
      _ = y * z := by rw [h]
  have hEbar_le_centZ : Ebar ≤ Subgroup.centralizer (Z : Set B) := by
    rw [Subgroup.closure_le]
    intro x hx
    change x ∈ Subgroup.centralizer (Z : Set B)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases hx with h | h
    · rw [h]; exact (Subgroup.mem_centralizer_iff.mp (hZleC hy) r (hL₀A hrPL₀.2)).symm
    · rw [h]; exact (hzZ y hy).symm
  have hZ_le : Z ≤ Subgroup.centralizer (Ebar : Set B) := by
    intro y hy
    change y ∈ Subgroup.centralizer (Ebar : Set B)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (hEbar_le_centZ hx) y hy).symm
  have hKZ_le : K₀ ⊔ Z ≤ Subgroup.centralizer (Ebar : Set B) := sup_le hK₀_le hZ_le
  have hKZrank : 2 ≤ CFSG.Open.pRank 5 (K₀ ⊔ Z) := by
    have hcommKZ : ∀ a ∈ K₀, ∀ b ∈ Z, a * b = b * a := by
      intro a ha b hb
      exact Subgroup.mem_centralizer_iff.mp (hZleC hb) a (hK₀A ha)
    have hdisjKZ : K₀ ⊓ Z = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hxAC : x ∈ A ⊓ C := ⟨hK₀A hx.1, hZleC hx.2⟩
      rw [hAC, Subgroup.mem_bot] at hxAC
      exact Subgroup.mem_bot.mpr hxAC
    have hadd := CFSG.LocalAnalysis.RankThreeUC.S15.pRank_add_le_pRank_sup_of_commute
      Nat.prime_five hcommKZ hdisjKZ
    have hK5 : CFSG.Open.pRank 5 K₀ = 1 := by
      rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
      obtain ⟨e1⟩ := s13_bar_equiv hK
      obtain ⟨e2⟩ := hAltK
      rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 5) (by norm_num)
        (e1.symm.trans e2)]
      exact S17.pRank_five_alternating_five
    have hZ5 : CFSG.Open.pRank 5 Z = 1 := by
      refine le_antisymm (CFSG.SectionRank.pRank_le_one_of_isCyclic Nat.prime_five hZcyc) ?_
      have h5dvd : 5 ∣ Nat.card ↥Z := by
        rw [hZcard]; exact dvd_pow_self 5 (by omega)
      obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card' (G := ↥Z) 5 h5dvd
      have hyB : orderOf (y : B) = 5 := (Subgroup.orderOf_coe y).trans hyord
      have hE5 : CFSG.Open.IsElemAbelian 5 (Subgroup.zpowers (y : B)) :=
        CFSG.Open.isElemAbelian_zpowers (by rw [← hyB]; exact pow_orderOf_eq_one _)
      have hcard5 : Nat.card (Subgroup.zpowers (y : B)) = 5 := by
        rw [Nat.card_zpowers, hyB]
      exact CFSG.SectionRank.le_pRank (by norm_num) (Subgroup.zpowers_le.mpr y.2) hE5
        (k := 1) (by rw [hcard5]; norm_num)
    omega
  have h5rank : 2 ≤ CFSG.Open.pRank 5 (Subgroup.centralizer (barImage D.M E : Set B)) := by
    have hmono : CFSG.Open.pRank 5 (K₀ ⊔ Z) ≤
        CFSG.Open.pRank 5 (Subgroup.centralizer (barImage D.M E : Set B)) :=
      CFSG.SectionRank.pRank_mono (by norm_num)
        (hKZ_le.trans (Subgroup.centralizer_le hEbar_le))
    omega
  have hEsubP : IsPGroup 3 ↥(E.subgroupOf D.M) := hEea.isPGroup.comap_subtype
  have htransport := CFSG.GroupTheory.CoprimeTransport.pRank_centralizer_map_mk_eq
    (G := ↥D.M) (N := CFSG.pCore 2 ↥D.M) (p := 5) (s := 3) hN3 hN5
    (E := E.subgroupOf D.M) hEsubP
  have hbridge : CFSG.Open.pRank 5 (Subgroup.centralizer ((E.subgroupOf D.M) : Set ↥D.M)) =
      CFSG.Open.pRank 5 (D.M ⊓ Subgroup.centralizer (E : Set G)) := by
    have hsub : (Subgroup.centralizer (E : Set G)).subgroupOf D.M =
        (D.M ⊓ Subgroup.centralizer (E : Set G)).subgroupOf D.M := by
      ext x
      simp
    rw [CFSG.centralizer_subgroupOf_eq E D.M hEM, hsub]
    exact CFSG.Quasithin.H13.Ch4.L436.pRank_subgroupOf_eq_pRank inf_le_left Nat.prime_five
  have hF : 2 ≤ CFSG.Open.pRank 5 (D.M ⊓ Subgroup.centralizer (E : Set G)) := by
    rw [← hbridge, htransport.symm]
    exact h5rank
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 5 D.M := c.hyp.stronglyPEmbedded hSg
  have h76' : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 D.M 5 :=
    h76 5 c.hyp.hp (by norm_num) hsp
  have hΓ : CFSG.Open.rankThreeGamma 1 3 E ≤ D.M :=
    rankThreeGamma_le_of_two_le_pRank_inf_centralizer
      (p := 5) (r := 3) hsp h76' hEM hEea.isPGroup (by
        refine CFSG.LocalAnalysis.UniquenessCase.UC6S846.le_pRank' Nat.prime_three le_rfl hEea
          (k := 2) ?_
        rw [hEcard]; norm_num) hF
  have hsub : D.sig ⊆ D.sig1 :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.sig_subset_sig1 hSg c.hyp.not_solvable
  have h3sig : 3 ∉ D.sig := c.three_not_mem_sig h1768
  exact h614 hsub 3 Nat.prime_three (by norm_num) h3sig R hRsyl E
    (le_inf hER hEcent) hEea hEcard hΓ

theorem A5Data18.k_eq_one_of_three_dvd
    {D : Data G} {V₀ V L K : Subgroup G}
    (c : A5Data18 D V₀ V L)
    (hK : K ∈ calC D.M) (hKne : K ≠ L) (hAltK : UC22.IsAlt (Bar2 K) 5)
    (hcomm : ⁅L, K⁆ ≤ pCoreOf 2 D.M)
    (hdich : (UC22.conjClosure D.M L = L ⊔ K ∧ ∃ x ∈ D.M, K = conjSubgroup L x) ∨
      (UC22.conjClosure D.M L = L ∧ (L.subgroupOf D.M).Normal ∧ (K.subgroupOf D.M).Normal))
    (h76 : UC22.F07.R76Sig D) (h614 : UC6.R6_14 D) (hSg : UC6S846.SigmaStd D)
    (h1768 : S17.R17_68At D V₀ V)
    (h3 : 3 ∣ Nat.card ↥(Subgroup.centralizer (barImage D.M (L ⊔ K) : Set (Bar2 D.M)))) :
    D.k = 1 :=
  Data.k_eq_one_of_isStronglyPEmbedded D
    (c.stronglyEmbedded_three hK hKne hAltK hcomm hdich h76 h614 hSg h1768 h3)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
