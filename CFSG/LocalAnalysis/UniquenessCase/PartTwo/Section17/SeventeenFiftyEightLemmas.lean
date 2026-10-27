module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftyNine
public import CFSG.Quasithin.Vol2.Ch12Sec6P31LieD
public import CFSG.GroupTheory.TPermutingTorus
public import CFSG.GroupTheory.PermutingProducts
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Row159
public import CFSG.SignalizerFunctorTheorem.McBride.Functor.Sections
public import CFSG.Blueprint.LieModelAPI
public import CFSG.Quasithin.Background.RonanE611Block
public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXU3P
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary
public import CFSG.GroupTheory.ElemAbelianRank
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Perm
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1517B
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Bridge13
public import CFSG.RankThree.PartTwo.Sec3.TwoThreeStructure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.GroupTheory
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem normalSimple_of_hyp1754 (D : Data G) {p : ℕ} (hThin : ThinList13)
    (hp : Hyp1754 D p) : s13_NormalSimple (Bar2 D.M) := by
  intro J hJ
  obtain ⟨L, hL, rfl⟩ := s13_exists_calC_of_component D.M hJ
  refine ⟨s13_barImage_normal (hp.2 L hL).1, ?_⟩
  obtain ⟨e⟩ := s13_bar_equiv hL
  rcases (hp.2 L hL).2 with hthin | ⟨n, hU⟩ | hL3
  · exact (MulEquiv.isSimpleGroup_congr e).1 (s13_list_bar hThin D hL hthin).1
  · exact (MulEquiv.isSimpleGroup_congr e).1 (s13_isSimple_of_isU3 hU)
  · exact (MulEquiv.isSimpleGroup_congr e).1
      (CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL3)

theorem calC_of_calC_Lp (D : Data G) {p : ℕ} {K : Subgroup G}
    (hK : K ∈ calC (Lp D p)) : K ∈ calC D.M := by
  refine ⟨?_, hK.2.1, hK.2.2⟩
  exact hK.1.trans (CFSG.ClassicalInvolution.isSubnormal_of_normal_subgroupOf (Lp_le_M D p)
    (s13_Lp_normal D.M p))

theorem not_three_dvd_card_pCoreOf_two (D : Data G) :
    ¬ 3 ∣ Nat.card (pCoreOf 2 D.M) := by
  have h := CFSG.LocalAnalysis.SQTKTwoCoreQuotient.not_dvd_card_pCore_two
    (H := ↥D.M) Nat.prime_three (by norm_num)
  have heq : Nat.card (pCoreOf 2 D.M) = Nat.card (CFSG.pCore 2 ↥D.M) := by
    rw [pCoreOf, Subgroup.card_map_of_injective D.M.subtype_injective]
  rwa [heq]

theorem exists_conj_sup_isElemAbelian_permutes {D : Data G} {E₁ E₂ : Subgroup G}
    (hE₁M : E₁ ≤ D.M) (hE₂M : E₂ ≤ D.M)
    (hE₁ : IsElemAbelian 3 E₁) (hE₂ : IsElemAbelian 3 E₂)
    (hperm₁ : Permutes E₁ D.T) (hperm₂ : Permutes E₂ D.T)
    (hcomm : ⁅E₁, E₂⁆ ≤ pCoreOf 2 D.M)
    (hdisj : E₁ ⊓ (E₂ ⊔ pCoreOf 2 D.M) = ⊥)
    (hrank : 2 ≤ CFSG.Open.pRank 3 E₁ + CFSG.Open.pRank 3 E₂) :
    ∃ n ∈ pCoreOf 2 D.M,
      IsElemAbelian 3 (E₁ ⊔ E₂.map (MulAut.conj n).toMonoidHom) ∧
      2 ≤ CFSG.Open.pRank 3 (E₁ ⊔ E₂.map (MulAut.conj n).toMonoidHom) ∧
      Permutes (E₁ ⊔ E₂.map (MulAut.conj n).toMonoidHom) D.T := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hO2M : pCoreOf 2 D.M ≤ D.M := CFSG.LieType.BorelTits.pCoreOf_le 2 D.M
  have hMn : D.M ≤ Subgroup.normalizer (pCoreOf 2 D.M : Set G) :=
    Subgroup.le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 D.M)
  have hp3O : ¬ 3 ∣ Nat.card (pCoreOf 2 D.M) := not_three_dvd_card_pCoreOf_two D
  obtain ⟨n, hnO, hnle⟩ :=
    CFSG.GroupTheory.exists_map_conj_le_centralizer_of_commutator_le (p := 3) (q := 3)
      (N := pCoreOf 2 D.M) (R := E₂) (B := E₁)
      (hE₂M.trans hMn) (hE₁M.trans hMn) hE₂.isPGroup hE₁.isPGroup hp3O hp3O
      (by rw [Subgroup.commutator_comm]; exact hcomm)
  have hnM : n ∈ D.M := hO2M hnO
  set E₂' : Subgroup G := E₂.map (MulAut.conj n).toMonoidHom with hE₂'def
  have hE₂' : IsElemAbelian 3 E₂' := hE₂.map _
  have hcomm' : ∀ a ∈ E₁, ∀ b ∈ E₂', a * b = b * a := by
    intro a ha b hb
    exact Subgroup.mem_centralizer_iff.mp (hnle hb) a ha
  have hE₂'le : E₂' ≤ E₂ ⊔ pCoreOf 2 D.M := by
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨e, he, rfl⟩ := hx
    have heM : e ∈ D.M := hE₂M he
    have hcommO : n * e * n⁻¹ * e⁻¹ ∈ pCoreOf 2 D.M := by
      have h1 : e * n * e⁻¹ ∈ pCoreOf 2 D.M :=
        (Subgroup.mem_normalizer_iff.mp (hMn heM) n).mp hnO
      have h2 : e * n * e⁻¹ * n⁻¹ ∈ pCoreOf 2 D.M :=
        (pCoreOf 2 D.M).mul_mem h1 ((pCoreOf 2 D.M).inv_mem hnO)
      have h3 : n * e * n⁻¹ * e⁻¹ = (e * n * e⁻¹ * n⁻¹)⁻¹ := by group
      rw [h3]
      exact (pCoreOf 2 D.M).inv_mem h2
    have h4 : (MulEquiv.toMonoidHom (MulAut.conj n)) e = (n * e * n⁻¹ * e⁻¹) * e := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [h4]
    exact (E₂ ⊔ pCoreOf 2 D.M).mul_mem (Subgroup.mem_sup_right hcommO) (Subgroup.mem_sup_left he)
  have hdisj' : E₁ ⊓ E₂' = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ E₁ ⊓ (E₂ ⊔ pCoreOf 2 D.M) := ⟨hx.1, hE₂'le hx.2⟩
    rw [hdisj] at hx'
    exact Subgroup.mem_bot.mp hx'
  refine ⟨n, hnO, ?_, ?_, ?_⟩
  · exact IsElemAbelian.sup_of_commute hE₁ hE₂' hcomm'
  · show 2 ≤ CFSG.Open.pRank 3 (E₁ ⊔ E₂')
    have hle := CFSG.LocalAnalysis.RankThreeUC.S15.pRank_add_le_pRank_sup_of_commute
      (q := 3) Nat.prime_three hcomm' hdisj'
    have hconj : CFSG.Open.pRank 3 E₂' = CFSG.Open.pRank 3 E₂ :=
      CFSG.LocalAnalysis.RankThreeUC.S15.exists_yComponent_dvd_aux_pRank_map_conj
        (by norm_num) E₂ n
    omega
  · show Permutes (E₁ ⊔ E₂') D.T
    have hnT : n ∈ D.T := CFSG.Quasithin.pCoreOf_two_le_of_isSylowTwoOf
      (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mpr D.sylowM) hnO
    have hTn : (D.T.map (MulAut.conj n).toMonoidHom : Subgroup G) = D.T :=
      CFSG.LieType.Steinberg.map_conj_of_mem hnT
    have hperm₂' : Permutes E₂' D.T := by
      have h := CFSG.GroupTheory.map_permutes_map (MulAut.conj n).toMonoidHom hperm₂
      rwa [hTn] at h
    have hsup : ((E₁ ⊔ E₂' : Subgroup G) : Set G) = (E₁ : Set G) * (E₂' : Set G) :=
      CFSG.HardMathSupport.Solomon.UniquenessMaximal.Permutable.coe_sup
        (CFSG.HardMathSupport.Solomon.UniquenessMaximal.permutable_of_mul_subset
          (fun x hx => by
            obtain ⟨a, ha, b, hb, rfl⟩ := hx
            exact ⟨b, hb, a, ha, (hcomm' a ha b hb).symm⟩))
    rw [Permutes, hsup]
    calc (E₁ : Set G) * (E₂' : Set G) * (D.T : Set G)
        = (E₁ : Set G) * ((E₂' : Set G) * (D.T : Set G)) := mul_assoc _ _ _
      _ = (E₁ : Set G) * ((D.T : Set G) * (E₂' : Set G)) := by rw [hperm₂']
      _ = ((E₁ : Set G) * (D.T : Set G)) * (E₂' : Set G) := (mul_assoc _ _ _).symm
      _ = ((D.T : Set G) * (E₁ : Set G)) * (E₂' : Set G) := by rw [hperm₁]
      _ = (D.T : Set G) * ((E₁ : Set G) * (E₂' : Set G)) := mul_assoc _ _ _

theorem card_normalizer_inf_sylow_of_isL3 {D : Data G} {K : Subgroup G}
    (hKM : K ≤ D.M) (hKn : (K.subgroupOf D.M).Normal) (hshape : IsL3 (Bar2 K) 2) :
    Nat.card ↥(K ⊓ Subgroup.normalizer ((D.T ⊓ K : Subgroup G) : Set G))
      = 3 * Nat.card ↥(D.T ⊓ K) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hMK : D.M ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mp hKn
  have hSylK : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ K) K :=
    D.sylowM.inf_of_le_normalizer hKM hMK
  have hSyl : CFSG.QuasithinUnique.IsSylowTwoOf (D.T ⊓ K) K :=
    CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mpr hSylK
  set S : Subgroup G := D.T ⊓ K with hSdef
  set B : Subgroup G := K ⊓ Subgroup.normalizer (S : Set G) with hBdef
  set OK : Subgroup ↥K := CFSG.pCore 2 ↥K with hOKdef
  set S₁ : Subgroup ↥K := S.subgroupOf K with hS₁def
  set π : ↥K →* Bar2 K := QuotientGroup.mk' OK with hπdef
  set Sstar : Subgroup (Bar2 K) := S₁.map π with hSstardef
  set Bstar : Subgroup (Bar2 K) := Subgroup.normalizer (Sstar : Set (Bar2 K)) with hBstardef
  have hSK : S ≤ K := inf_le_right
  have hBK : B ≤ K := inf_le_left
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective OK
  change Nat.card ↥B = 3 * Nat.card ↥S
  obtain ⟨m, hm⟩ : ∃ m, Nat.card ↥OK = 2 ^ m :=
    IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥K))
  have hKcard : Nat.card ↥K = 2 ^ 6 * 3 ^ 2 * 5 * 7 * 2 ^ m := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup OK, hm]
    congr 1
    exact card_bar_of_isL3 hshape
  have hKfac : (Nat.card ↥K).factorization 2 = 6 + m := by
    rw [hKcard, show (2:ℕ) ^ 6 * 3 ^ 2 * 5 * 7 * 2 ^ m
        = 2 ^ (6 + m) * (3 ^ 2 * (5 * 7)) by ring]
    rw [Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
      Nat.Prime.factorization Nat.prime_two, Finsupp.single_eq_same, mul_one,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3 ^ 2 * (5 * 7)), add_zero]
  have hScard : Nat.card ↥S = 2 ^ 6 * Nat.card ↥OK := by
    have h2 : Nat.card ↥S = 2 ^ (Nat.card ↥K).factorization 2 := hSylK.card_eq
    rw [h2, hKfac, hm, ← pow_add]
  have hS₁S : Nat.card ↥S₁ = Nat.card ↥S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSK).toEquiv
  have hOle : OK ≤ S₁ := by
    intro y hy
    rw [Subgroup.mem_subgroupOf]
    exact CFSG.Quasithin.pCoreOf_two_le_of_isSylowTwoOf hSyl
      (Subgroup.mem_map_of_mem K.subtype (by simpa [hOKdef] using hy))
  have hS₁eq : S₁ = Sstar.comap π := by
    have hker : π.ker ≤ S₁ := by
      rw [hπdef, QuotientGroup.ker_mk']
      exact hOle
    rw [hSstardef]
    exact (Subgroup.comap_map_eq_self hker).symm
  have hidxS : S₁.index = Sstar.index := by
    rw [hS₁eq]
    exact Subgroup.index_comap_of_surjective Sstar hπsurj
  have hSstarcard : Nat.card ↥Sstar = 64 := by
    have h1 : Nat.card ↥S₁ * S₁.index = Nat.card ↥K := Subgroup.card_mul_index S₁
    have h2 : Nat.card ↥K = Nat.card (Bar2 K) * Nat.card ↥OK :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup OK
    have h3 : Nat.card ↥Sstar * Sstar.index = Nat.card (Bar2 K) :=
      Subgroup.card_mul_index Sstar
    have hidxpos : 0 < S₁.index := by
      rcases Nat.eq_zero_or_pos S₁.index with h0 | h0
      · rw [h0, mul_zero] at h1
        exact absurd h1.symm (Nat.card_pos.ne')
      · exact h0
    have key : Nat.card ↥S₁ * S₁.index = (Nat.card ↥Sstar * Nat.card ↥OK) * S₁.index := by
      rw [h1, h2, ← h3, ← hidxS]
      ring
    have h4 := Nat.eq_of_mul_eq_mul_right hidxpos key
    rw [hS₁S, hScard] at h4
    have h5 := Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥OK)) h4
    omega
  have hPsl : CFSG.Quasithin.IsPSL 3 2 2 (Bar2 K) :=
    (CFSG.Blueprint.LieModel.classical_iff (t := .PSL) (n := 3) (p := 2) (f := 2)
      (by decide)).mp hshape
  have hSstaridx : Sstar.index = 315 := by
    have h := Subgroup.card_mul_index Sstar
    rw [hSstarcard, card_bar_of_isL3 hshape] at h
    have h' : Sstar.index * 64 = 315 * 64 := by
      rw [mul_comm Sstar.index 64, h]
      norm_num
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 64) h'
  have hSstarSyl : CFSG.QuasithinUnique.IsSylowTwoOf Sstar ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · exact IsPGroup.iff_card.mpr ⟨6, by rw [hSstarcard]; norm_num⟩
    · show ¬ 2 ∣ Sstar.relIndex ⊤
      rw [Subgroup.relIndex_top_right, hSstaridx]
      norm_num
  have hBstarcard : Nat.card ↥Bstar = 192 :=
    CFSG.Quasithin.H13.S126P31.psl34_card_normalizer_sylow hPsl Sstar hSstarSyl
  set B₁ : Subgroup ↥K := B.subgroupOf K with hB₁def
  have hB₁eq : B₁ = Bstar.comap π := by
    have h1 : Bstar.comap π = Subgroup.normalizer (S₁ : Set ↥K) := by
      rw [hBstardef, Subgroup.comap_normalizer_eq_of_surjective Sstar hπsurj, hS₁eq]
    rw [h1, hB₁def, hBdef]
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff,
      Subgroup.mem_normalizer_iff]
    constructor
    · rintro ⟨-, hxN⟩ y
      show y ∈ S₁ ↔ x * y * x⁻¹ ∈ S₁
      rw [hS₁def, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      simpa using Subgroup.mem_normalizer_iff.mp hxN (y : G)
    · intro hxN
      refine ⟨x.2, ?_⟩
      intro y
      constructor
      · intro hy
        have hyK : y ∈ K := hSK hy
        have hy1 : (⟨y, hyK⟩ : ↥K) ∈ S₁ := by
          rw [hS₁def, Subgroup.mem_subgroupOf]
          exact hy
        have h := (hxN ⟨y, hyK⟩).mp hy1
        rw [hS₁def, Subgroup.mem_subgroupOf] at h
        simpa using h
      · intro hy
        have hyK : y ∈ K := by
          have h1 : (↑x)⁻¹ * (↑x * y * ↑x⁻¹) * (↑x) ∈ K :=
            K.mul_mem (K.mul_mem (K.inv_mem x.2) (hSK hy)) x.2
          simpa [mul_assoc] using h1
        have hy1 : x * (⟨y, hyK⟩ : ↥K) * x⁻¹ ∈ S₁ := by
          rw [hS₁def, Subgroup.mem_subgroupOf]
          simpa using hy
        have h2 := (hxN ⟨y, hyK⟩).mpr hy1
        rw [hS₁def, Subgroup.mem_subgroupOf] at h2
        exact h2
  have hB₁card : Nat.card ↥B₁ = 3 * Nat.card ↥S₁ := by
    have h1 : Nat.card ↥B₁ * B₁.index = Nat.card ↥K := Subgroup.card_mul_index B₁
    have h2 : Nat.card ↥K = Nat.card (Bar2 K) * Nat.card ↥OK :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup OK
    have h3 : Nat.card ↥Bstar * Bstar.index = Nat.card (Bar2 K) :=
      Subgroup.card_mul_index Bstar
    have hidxB : B₁.index = Bstar.index := by
      rw [hB₁eq]
      exact Subgroup.index_comap_of_surjective Bstar hπsurj
    have hidxpos : 0 < B₁.index := by
      rcases Nat.eq_zero_or_pos B₁.index with h0 | h0
      · rw [h0, mul_zero] at h1
        exact absurd h1.symm (Nat.card_pos.ne')
      · exact h0
    have key : Nat.card ↥B₁ * B₁.index = (Nat.card ↥Bstar * Nat.card ↥OK) * B₁.index := by
      rw [h1, h2, ← h3, ← hidxB]
      ring
    have h4 := Nat.eq_of_mul_eq_mul_right hidxpos key
    rw [h4, hBstarcard, hS₁S, hScard]
    ring
  have hBcard : Nat.card ↥B = Nat.card ↥B₁ :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBK).toEquiv).symm
  rw [hBcard, hB₁card]
  rw [hS₁S]

theorem one_le_pRank_three_of_three_dvd_card {B : Subgroup G} (h3 : 3 ∣ Nat.card B) :
    1 ≤ CFSG.Open.pRank 3 B := by
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) 3 h3
  have hx3 : (x : ↥B) ^ 3 = 1 := by
    rw [← hxord]
    exact pow_orderOf_eq_one _
  have hzx : IsElemAbelian 3 (Subgroup.zpowers (x : G)) := by
    rw [Subgroup.zpowers_eq_closure]
    refine IsElemAbelian.closure_of_commute ?_ ?_
    · intro a ha b hb
      rw [Set.mem_singleton_iff] at ha hb
      rw [ha, hb]
    · intro a ha
      rw [Set.mem_singleton_iff] at ha
      rw [ha]
      simpa using congrArg Subtype.val hx3
  have hzxcard : Nat.card ↥(Subgroup.zpowers (x : G)) = 3 := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hxord]
  have hmem : 1 ∈ {k : ℕ | ∃ E : Subgroup G, E ≤ B ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k} :=
    ⟨Subgroup.zpowers (x : G), Subgroup.zpowers_le.mpr x.2, hzx, by rw [hzxcard]; norm_num⟩
  exact le_csSup (CFSG.SectionRank.pRank_bddAbove (by norm_num) B) hmem

theorem exists_elemAbelian_permutes_of_isL3 {D : Data G} {K : Subgroup G}
    (hKM : K ≤ D.M) (hKn : (K.subgroupOf D.M).Normal) (hshape : IsL3 (Bar2 K) 2) :
    ∃ E ≤ K, IsElemAbelian 3 E ∧ 1 ≤ CFSG.Open.pRank 3 E ∧ Permutes E D.T := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hMK : D.M ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mp hKn
  have hSylK : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ K) K :=
    D.sylowM.inf_of_le_normalizer hKM hMK
  have hSyl : CFSG.QuasithinUnique.IsSylowTwoOf (D.T ⊓ K) K :=
    CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mpr hSylK
  set S : Subgroup G := D.T ⊓ K with hSdef
  set B : Subgroup G := K ⊓ Subgroup.normalizer (S : Set G) with hBdef
  have hSK : S ≤ K := inf_le_right
  have hBK : B ≤ K := inf_le_left
  have hSB : S ≤ B := le_inf hSK (Subgroup.le_normalizer)
  have hBN : B ≤ Subgroup.normalizer (S : Set G) := inf_le_right
  haveI hnormal : (S.subgroupOf B).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSB).mpr hBN
  have hTS : D.T ≤ Subgroup.normalizer (S : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨hyT, hyK⟩
      exact ⟨D.T.mul_mem (D.T.mul_mem ht hyT) (D.T.inv_mem ht),
        (Subgroup.mem_normalizer_iff.mp (hMK (hTM ht)) y).mp hyK⟩
    · rintro ⟨hyT, hyK⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer ht) y).mpr hyT,
        (Subgroup.mem_normalizer_iff.mp (hMK (hTM ht)) y).mpr hyK⟩
  have hTB : D.T ≤ Subgroup.normalizer (B : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨hyK, hyN⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hMK (hTM ht)) y).mp hyK, ?_⟩
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hTS ht) hyN)
        (Subgroup.inv_mem _ (hTS ht))
    · rintro ⟨hyK, hyN⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hMK (hTM ht)) y).mpr hyK, ?_⟩
      have h1 : t⁻¹ * (t * y * t⁻¹) * t = y := by group
      have h2 := Subgroup.mul_mem (Subgroup.normalizer (S : Set G))
        (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hTS ht)) hyN) (hTS ht)
      rwa [h1] at h2
  have hcardB : Nat.card ↥B = 3 * Nat.card ↥S := card_normalizer_inf_sylow_of_isL3 hKM hKn hshape
  have hidx : (S.subgroupOf B).index = 3 := by
    have h1 : Nat.card ↥(S.subgroupOf B) * (S.subgroupOf B).index = Nat.card ↥B :=
      Subgroup.card_mul_index _
    rw [show Nat.card ↥(S.subgroupOf B) = Nat.card ↥S from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSB).toEquiv, hcardB] at h1
    have h2 : Nat.card ↥S * (S.subgroupOf B).index = Nat.card ↥S * 3 := by
      rw [h1]
      ring
    exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := ↥S)) h2
  have hqcard : Nat.card (B ⧸ S.subgroupOf B) = 3 := by
    rw [← Subgroup.index_eq_card]
    exact hidx
  have hab : ∀ a b : B ⧸ S.subgroupOf B, a * b = b * a := by
    intro a b
    by_cases ha : a = 1
    · rw [ha, one_mul, mul_one]
    by_cases hb : b = 1
    · rw [hb, mul_one, one_mul]
    have hda : Nat.card ↥(Subgroup.zpowers a) ∣ 3 := by
      rw [← hqcard]
      exact Subgroup.card_subgroup_dvd_card _
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hda with h1 | h3
    · rw [Subgroup.card_eq_one] at h1
      have hmem : a ∈ Subgroup.zpowers a := Subgroup.mem_zpowers a
      rw [h1, Subgroup.mem_bot] at hmem
      exact absurd hmem ha
    · have htop : Subgroup.zpowers a = ⊤ :=
        Subgroup.eq_top_of_card_eq _ (by rw [h3, hqcard])
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (htop ▸ Subgroup.mem_top b)
      rw [← hk]
      exact (Commute.zpow_right (Commute.refl a) k).eq
  obtain ⟨E, hEB, hEel, hEcard, hperm⟩ :=
    CFSG.GroupTheory.exists_elemAbelian_permutes_of_abelian_quotient (B := B) (S := S)
      (T := D.T) (r := 3) hab hSB inf_le_left
      hTB hTS (by norm_num : Nat.Prime 3) (by norm_num : 3 ≠ 2) (hSylK.isPGroup)
  refine ⟨E, hEB.trans hBK, hEel, ?_, hperm⟩
  have hdvdB : 3 ∣ Nat.card ↥B := ⟨Nat.card ↥S, hcardB⟩
  have hrankB : 1 ≤ CFSG.Open.pRank 3 B :=
    one_le_pRank_three_of_three_dvd_card hdvdB
  have hrankE : CFSG.Open.pRank 3 B = CFSG.Open.pRank 3 E := by
    have h1 : Nat.card ↥E = 3 ^ CFSG.Open.pRank 3 E :=
      CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian (by norm_num) hEel
    rw [h1] at hEcard
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) hEcard).symm
  rw [← hrankE]
  exact hrankB

theorem subgroupOf_sylow_eq_comap_map {D : Data G} {K : Subgroup G}
    (hKM : K ≤ D.M) (hKn : (K.subgroupOf D.M).Normal) :
    (D.T ⊓ K).subgroupOf K =
      (((D.T ⊓ K).subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))).comap
        (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMK : D.M ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mp hKn
  have hSylK : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ K) K :=
    D.sylowM.inf_of_le_normalizer hKM hMK
  have hSyl : CFSG.QuasithinUnique.IsSylowTwoOf (D.T ⊓ K) K :=
    CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mpr hSylK
  have hker : (QuotientGroup.mk' (CFSG.pCore 2 ↥K)).ker ≤ (D.T ⊓ K).subgroupOf K := by
    intro y hy
    rw [QuotientGroup.ker_mk'] at hy
    rw [Subgroup.mem_subgroupOf]
    exact CFSG.Quasithin.pCoreOf_two_le_of_isSylowTwoOf hSyl
      (Subgroup.mem_map_of_mem K.subtype (by simpa using hy))
  exact (Subgroup.comap_map_eq_self hker).symm

theorem subgroupOf_inf_normalizer_map_eq {D : Data G} {K : Subgroup G}
    (hKM : K ≤ D.M) (hKn : (K.subgroupOf D.M).Normal) :
    ((K ⊓ Subgroup.normalizer ((D.T ⊓ K : Subgroup G) : Set G)).subgroupOf K).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) =
      Subgroup.normalizer ((((D.T ⊓ K).subgroupOf K).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥K))) : Set (Bar2 K)) := by
  classical
  have hSK : D.T ⊓ K ≤ K := inf_le_right
  set S₁ : Subgroup ↥K := (D.T ⊓ K).subgroupOf K with hS₁def
  set B₁ : Subgroup ↥K :=
    (K ⊓ Subgroup.normalizer ((D.T ⊓ K : Subgroup G) : Set G)).subgroupOf K with hB₁def
  set π : ↥K →* Bar2 K := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπdef
  have hS₁ : S₁ = (S₁.map π).comap π := by
    rw [hS₁def, hπdef]
    exact subgroupOf_sylow_eq_comap_map hKM hKn
  have hBcomap : B₁ = (Subgroup.normalizer (S₁.map π : Set (Bar2 K))).comap π := by
    rw [hB₁def]
    rw [show (K ⊓ Subgroup.normalizer ((D.T ⊓ K : Subgroup G) : Set G)).subgroupOf K =
        Subgroup.normalizer (S₁ : Set ↥K) from by
      rw [hS₁def]
      exact CFSG.Quasithin.RonanE611.subgroupOf_normalizer_eq hSK]
    conv_lhs => rw [hS₁]
    exact (Subgroup.comap_normalizer_eq_of_surjective (H := S₁.map π)
      (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K))).symm
  rw [hBcomap, Subgroup.map_comap_eq_self_of_surjective
    (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K))]

theorem card_inf_normalizer_eq_card_normalizer_bar_mul {D : Data G} {K : Subgroup G}
    (hKM : K ≤ D.M) (hKn : (K.subgroupOf D.M).Normal) :
    Nat.card ↥(K ⊓ Subgroup.normalizer ((D.T ⊓ K : Subgroup G) : Set G)) =
      Nat.card ↥(Subgroup.normalizer ((((D.T ⊓ K).subgroupOf K).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥K))) : Set (Bar2 K))) *
        Nat.card ↥(CFSG.pCore 2 ↥K) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMK : D.M ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mp hKn
  have hSylK : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ K) K :=
    D.sylowM.inf_of_le_normalizer hKM hMK
  have hSyl : CFSG.QuasithinUnique.IsSylowTwoOf (D.T ⊓ K) K :=
    CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mpr hSylK
  set S₁ : Subgroup ↥K := (D.T ⊓ K).subgroupOf K with hS₁def
  set B₁ : Subgroup ↥K := (K ⊓ Subgroup.normalizer ((D.T ⊓ K : Subgroup G) : Set G)).subgroupOf K
    with hB₁def
  have hSK : D.T ⊓ K ≤ K := inf_le_right
  have hBK : K ⊓ Subgroup.normalizer ((D.T ⊓ K : Subgroup G) : Set G) ≤ K := inf_le_left
  have hOle : CFSG.pCore 2 ↥K ≤ S₁ := by
    intro y hy
    rw [hS₁def, Subgroup.mem_subgroupOf]
    exact CFSG.Quasithin.pCoreOf_two_le_of_isSylowTwoOf hSyl
      (Subgroup.mem_map_of_mem K.subtype (by simpa using hy))
  have hSB : D.T ⊓ K ≤ K ⊓ Subgroup.normalizer ((D.T ⊓ K : Subgroup G) : Set G) :=
    le_inf hSK Subgroup.le_normalizer
  have hOleB : CFSG.pCore 2 ↥K ≤ B₁ := by
    intro y hy
    rw [hB₁def, Subgroup.mem_subgroupOf]
    exact hSB (Subgroup.mem_subgroupOf.mp (hOle hy))
  have hcard : Nat.card ↥B₁ =
      Nat.card ↥(B₁.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))) *
        Nat.card ↥(CFSG.pCore 2 ↥K) :=
    (CFSG.SignalizerFunctorTheorem.McBride.card_map_mk'_mul_card hOleB).symm
  have hBmap : B₁.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) =
      Subgroup.normalizer ((((D.T ⊓ K).subgroupOf K).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥K))) : Set (Bar2 K)) := by
    rw [hB₁def]
    exact subgroupOf_inf_normalizer_map_eq hKM hKn
  rw [hBmap] at hcard
  have hcardB : Nat.card ↥(K ⊓ Subgroup.normalizer ((D.T ⊓ K : Subgroup G) : Set G)) =
      Nat.card ↥B₁ :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBK).toEquiv).symm
  rw [hcardB, hcard]

theorem exists_elemAbelian_permutes_of_borel_commutative {D : Data G} {K : Subgroup G}
    (hKM : K ≤ D.M) (hKn : (K.subgroupOf D.M).Normal)
    {Sstar : Subgroup (Bar2 K)}
    (hSstar : Sstar = ((D.T ⊓ K).subgroupOf K).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥K)))
    (h3 : 3 ∣ Nat.card ↥(Subgroup.normalizer (Sstar : Set (Bar2 K))))
    (hcomm : ∀ a b : Bar2 K,
      a ∈ Subgroup.normalizer (Sstar : Set (Bar2 K)) →
      b ∈ Subgroup.normalizer (Sstar : Set (Bar2 K)) →
      a * b * a⁻¹ * b⁻¹ ∈ Sstar) :
    ∃ E ≤ K, IsElemAbelian 3 E ∧ 1 ≤ CFSG.Open.pRank 3 E ∧ Permutes E D.T := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  subst hSstar
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hMK : D.M ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mp hKn
  have hSylK : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ K) K :=
    D.sylowM.inf_of_le_normalizer hKM hMK
  set SS : Subgroup G := D.T ⊓ K with hSSdef
  set BB : Subgroup G := K ⊓ Subgroup.normalizer (SS : Set G) with hBBdef
  set π : ↥K →* Bar2 K := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπdef
  have hSK : SS ≤ K := by rw [hSSdef]; exact inf_le_right
  have hBK : BB ≤ K := by rw [hBBdef]; exact inf_le_left
  have hSB : SS ≤ BB := by
    rw [hBBdef]
    exact le_inf hSK Subgroup.le_normalizer
  have hBN : BB ≤ Subgroup.normalizer (SS : Set G) := by
    rw [hBBdef]; exact inf_le_right
  haveI hnormal : (SS.subgroupOf BB).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSB).mpr hBN
  have h3B : 3 ∣ Nat.card ↥BB := by
    show 3 ∣ Nat.card ↥(K ⊓ Subgroup.normalizer ((D.T ⊓ K : Subgroup G) : Set G))
    rw [card_inf_normalizer_eq_card_normalizer_bar_mul hKM hKn]
    exact dvd_mul_of_dvd_left h3 _
  have hquot : ∀ a b : ↥BB ⧸ SS.subgroupOf BB, a * b = b * a := by
    intro a b
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (SS.subgroupOf BB) a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (SS.subgroupOf BB) b
    have hxN : π (Subgroup.inclusion hBK x) ∈
        Subgroup.normalizer (((SS.subgroupOf K).map π) : Set (Bar2 K)) := by
      have hmem : Subgroup.inclusion hBK x ∈
          (K ⊓ Subgroup.normalizer (SS : Set G)).subgroupOf K :=
        Subgroup.mem_subgroupOf.mpr x.2
      have h := Subgroup.mem_map_of_mem π hmem
      rw [subgroupOf_inf_normalizer_map_eq hKM hKn] at h
      simpa [hSSdef, hπdef] using h
    have hyN : π (Subgroup.inclusion hBK y) ∈
        Subgroup.normalizer (((SS.subgroupOf K).map π) : Set (Bar2 K)) := by
      have hmem : Subgroup.inclusion hBK y ∈
          (K ⊓ Subgroup.normalizer (SS : Set G)).subgroupOf K :=
        Subgroup.mem_subgroupOf.mpr y.2
      have h := Subgroup.mem_map_of_mem π hmem
      rw [subgroupOf_inf_normalizer_map_eq hKM hKn] at h
      simpa [hSSdef, hπdef] using h
    have hc : π (Subgroup.inclusion hBK (x * y * x⁻¹ * y⁻¹)) ∈
        (SS.subgroupOf K).map π := by
      have h1 : π (Subgroup.inclusion hBK (x * y * x⁻¹ * y⁻¹)) =
          π (Subgroup.inclusion hBK x) * π (Subgroup.inclusion hBK y) *
            (π (Subgroup.inclusion hBK x))⁻¹ * (π (Subgroup.inclusion hBK y))⁻¹ := by
        simp only [map_mul, map_inv]
      rw [h1]
      exact hcomm _ _ hxN hyN
    have hcK : Subgroup.inclusion hBK (x * y * x⁻¹ * y⁻¹) ∈ SS.subgroupOf K := by
      rw [subgroupOf_sylow_eq_comap_map hKM hKn]
      exact hc
    have hmemS : (x * y * x⁻¹ * y⁻¹ : ↥BB) ∈ SS.subgroupOf BB := by
      rw [Subgroup.mem_subgroupOf]
      simpa using (Subgroup.mem_subgroupOf.mp hcK)
    have h1 : QuotientGroup.mk' (SS.subgroupOf BB) (x * y * x⁻¹ * y⁻¹) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hmemS
    have h2 : QuotientGroup.mk' (SS.subgroupOf BB) (x * y * x⁻¹ * y⁻¹) =
        QuotientGroup.mk' (SS.subgroupOf BB) x * QuotientGroup.mk' (SS.subgroupOf BB) y *
          (QuotientGroup.mk' (SS.subgroupOf BB) x)⁻¹ *
          (QuotientGroup.mk' (SS.subgroupOf BB) y)⁻¹ := by
      simp only [map_mul, map_inv]
    rw [h2] at h1
    calc QuotientGroup.mk' (SS.subgroupOf BB) x * QuotientGroup.mk' (SS.subgroupOf BB) y
        = (QuotientGroup.mk' (SS.subgroupOf BB) x * QuotientGroup.mk' (SS.subgroupOf BB) y *
            (QuotientGroup.mk' (SS.subgroupOf BB) x)⁻¹ *
            (QuotientGroup.mk' (SS.subgroupOf BB) y)⁻¹) *
          (QuotientGroup.mk' (SS.subgroupOf BB) y *
            QuotientGroup.mk' (SS.subgroupOf BB) x) := by
          group
      _ = 1 * (QuotientGroup.mk' (SS.subgroupOf BB) y *
            QuotientGroup.mk' (SS.subgroupOf BB) x) := by rw [h1]
      _ = QuotientGroup.mk' (SS.subgroupOf BB) y *
            QuotientGroup.mk' (SS.subgroupOf BB) x := one_mul _
  have hTS : D.T ≤ Subgroup.normalizer (SS : Set G) := by
    rw [hSSdef]
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨hyT, hyK⟩
      exact ⟨D.T.mul_mem (D.T.mul_mem ht hyT) (D.T.inv_mem ht),
        (Subgroup.mem_normalizer_iff.mp (hMK (hTM ht)) y).mp hyK⟩
    · rintro ⟨hyT, hyK⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer ht) y).mpr hyT,
        (Subgroup.mem_normalizer_iff.mp (hMK (hTM ht)) y).mpr hyK⟩
  have hTB : D.T ≤ Subgroup.normalizer (BB : Set G) := by
    rw [hBBdef]
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨hyK, hyN⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hMK (hTM ht)) y).mp hyK, ?_⟩
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hTS ht) hyN)
        (Subgroup.inv_mem _ (hTS ht))
    · rintro ⟨hyK, hyN⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hMK (hTM ht)) y).mpr hyK, ?_⟩
      have h1 : t⁻¹ * (t * y * t⁻¹) * t = y := by group
      have h2 := Subgroup.mul_mem (Subgroup.normalizer (SS : Set G))
        (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hTS ht)) hyN) (hTS ht)
      rwa [h1] at h2
  obtain ⟨E, hEB, hEel, hEcard, hperm⟩ :=
    CFSG.GroupTheory.exists_elemAbelian_permutes_of_abelian_quotient (B := BB) (S := SS)
      (T := D.T) (r := 3) hquot hSB inf_le_left hTB hTS
      (by norm_num) (by norm_num) (by rw [hSSdef]; exact hSylK.isPGroup)
  refine ⟨E, hEB.trans hBK, hEel, ?_, hperm⟩
  have hdvdB : 3 ∣ Nat.card ↥BB := h3B
  have hrankB : 1 ≤ CFSG.Open.pRank 3 BB :=
    one_le_pRank_three_of_three_dvd_card hdvdB
  have hrankE : CFSG.Open.pRank 3 BB = CFSG.Open.pRank 3 E := by
    have h1 : Nat.card ↥E = 3 ^ CFSG.Open.pRank 3 E :=
      CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian (by norm_num) hEel
    rw [h1] at hEcard
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) hEcard).symm
  rw [← hrankE]
  exact hrankB

theorem exists_elemAbelian_permutes_of_isL2_even {D : Data G} {K : Subgroup G}
    (hKM : K ≤ D.M) (hKn : (K.subgroupOf D.M).Normal)
    {a : ℕ} (ha : Even a) (hshape : IsL2 (Bar2 K) a) :
    ∃ E ≤ K, IsElemAbelian 3 E ∧ 1 ≤ CFSG.Open.pRank 3 E ∧ Permutes E D.T := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hMK : D.M ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mp hKn
  have hSylK : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ K) K :=
    D.sylowM.inf_of_le_normalizer hKM hMK
  have hSyl : CFSG.QuasithinUnique.IsSylowTwoOf (D.T ⊓ K) K :=
    CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mpr hSylK
  set S₁ : Subgroup ↥K := (D.T ⊓ K).subgroupOf K with hS₁def
  set Sstar : Subgroup (Bar2 K) := S₁.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) with hSstardef
  have hS₁syl : CFSG.Quasithin.IsSylowIn 2 S₁ ⊤ := by
    have h := (CFSG.Quasithin.E1.isSylowIn_subgroupOf_iff (p := 2)
      (P := D.T ⊓ K) (K := K) (H := K) inf_le_right le_rfl).mpr hSyl
    simpa [hS₁def, Subgroup.subgroupOf_self] using h
  have hSstarSyl : CFSG.QuasithinUnique.IsSylowTwoOf Sstar ⊤ := by
    have h := CFSG.Quasithin.E1.isSylowIn_two_map_top
      (f := QuotientGroup.mk' (CFSG.pCore 2 ↥K))
      (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K)) hS₁syl
    exact CFSG.Quasithin.E1.isSylowIn_two_iff.mp h
  have hPSLbar : CFSG.Quasithin.IsPSL 2 2 a (Bar2 K) :=
    (CFSG.Blueprint.LieModel.classical_iff (t := .PSL) (n := 2) (p := 2) (f := a)
      (by decide)).mp hshape
  have hPSL : CFSG.Quasithin.IsPSL 2 2 a ↥(⊤ : Subgroup (Bar2 K)) :=
    CFSG.Quasithin.IsPSL.of_mulEquiv Subgroup.topEquiv.symm hPSLbar
  obtain ⟨-, -, hcardB, -, hcommstar, -, -⟩ :=
    CFSG.Quasithin.H13.P31X.l2BorelFacts_holds a (s13_two_le_of_isL2 hshape)
      (Bar2 K) (⊤) Sstar hPSL hSstarSyl
  have h3 : 3 ∣ Nat.card ↥(Subgroup.normalizer (Sstar : Set (Bar2 K))) := by
    have hB := hcardB
    rw [top_inf_eq] at hB
    rw [hB]
    have h3a : 3 ∣ 2 ^ a - 1 := by
      simpa using Nat.pow_sub_one_dvd_pow_sub_one 2 (even_iff_two_dvd.mp ha)
    exact dvd_mul_of_dvd_right h3a (2 ^ a)
  refine exists_elemAbelian_permutes_of_borel_commutative hKM hKn hSstardef.symm h3 ?_
  intro x y hx hy
  exact hcommstar x (by simpa [hSstardef] using hx) y (by simpa [hSstardef] using hy)

theorem exists_elemAbelian_permutes_of_isSU3_even
    {D : Data G} {K : Subgroup G}
    (hKM : K ≤ D.M) (hKn : (K.subgroupOf D.M).Normal)
    {n : ℕ} (hn : Even n) (hshape : IsSU3 (Bar2 K) n) :
    ∃ E ≤ K, IsElemAbelian 3 E ∧ 1 ≤ CFSG.Open.pRank 3 E ∧ Permutes E D.T := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn2 : 2 ≤ n := s13_two_le_of_isU3 hshape.2
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hMK : D.M ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mp hKn
  have hSylK : CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ K) K :=
    D.sylowM.inf_of_le_normalizer hKM hMK
  have hSyl : CFSG.QuasithinUnique.IsSylowTwoOf (D.T ⊓ K) K :=
    CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.mpr hSylK
  set S₁ : Subgroup ↥K := (D.T ⊓ K).subgroupOf K with hS₁def
  set Sstar : Subgroup (Bar2 K) := S₁.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) with hSstardef
  have hS₁syl : CFSG.Quasithin.IsSylowIn 2 S₁ ⊤ := by
    have h := (CFSG.Quasithin.E1.isSylowIn_subgroupOf_iff (p := 2)
      (P := D.T ⊓ K) (K := K) (H := K) inf_le_right le_rfl).mpr hSyl
    simpa [hS₁def, Subgroup.subgroupOf_self] using h
  have hSstarSyl : CFSG.QuasithinUnique.IsSylowTwoOf Sstar ⊤ := by
    have h := CFSG.Quasithin.E1.isSylowIn_two_map_top
      (f := QuotientGroup.mk' (CFSG.pCore 2 ↥K))
      (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K)) hS₁syl
    exact CFSG.Quasithin.E1.isSylowIn_two_iff.mp h
  have hperf : Group.IsPerfect (↥(⊤ : Subgroup (Bar2 K))) := by
    rw [Group.IsPerfect.top_iff]
    exact Group.isPerfect_def.mpr hshape.1.1
  have hPSUbar : CFSG.Quasithin.IsPSU 3 2 n
      (Bar2 K ⧸ Subgroup.center (Bar2 K)) :=
    (CFSG.Blueprint.LieModel.classical_iff (by decide)).1 hshape.2
  let eTop : ↥(⊤ : Subgroup (Bar2 K)) ≃* Bar2 K := Subgroup.topEquiv
  let eQ : (↥(⊤ : Subgroup (Bar2 K)) ⧸
      Subgroup.center ↥(⊤ : Subgroup (Bar2 K))) ≃*
      (Bar2 K ⧸ Subgroup.center (Bar2 K)) :=
    QuotientGroup.congr _ _ eTop (Subgroup.map_center_eq eTop)
  have hPSU : CFSG.Quasithin.IsPSU 3 2 n
      (↥(⊤ : Subgroup (Bar2 K)) ⧸
        Subgroup.center ↥(⊤ : Subgroup (Bar2 K))) :=
    CFSG.Quasithin.IsPSU.of_mulEquiv eQ.symm hPSUbar
  obtain ⟨hZ, hcardB, -, hgen, -⟩ :=
    CFSG.Quasithin.H13.P31X.u3BorelFacts_holds n hn2 (Bar2 K) (⊤) Sstar
      hperf hPSU hSstarSyl
  have hgcd : Nat.gcd 3 (2 ^ n + 1) = 1 := by
    have h3n : 3 ∣ 2 ^ n - 1 := by
      have h := Nat.pow_sub_one_dvd_pow_sub_one 2 (even_iff_two_dvd.mp hn)
      simpa using h
    have hcop : Nat.Coprime 3 (2 ^ n + 1) := by
      rw [Nat.prime_three.coprime_iff_not_dvd]
      intro h3
      have hsub : 3 ∣ (2 ^ n + 1) - (2 ^ n - 1) := Nat.dvd_sub h3 h3n
      have heq : 2 ^ n + 1 - (2 ^ n - 1) = 2 := by
        have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
        omega
      rw [heq] at hsub
      norm_num at hsub
    exact Nat.coprime_iff_gcd_eq_one.mp hcop
  have hZ1 : Nat.card ↥(Subgroup.center ↥(⊤ : Subgroup (Bar2 K))) = 1 := by
    have h := hZ
    rw [hgcd] at h
    exact Nat.dvd_one.mp h
  have h3 : 3 ∣ Nat.card ↥(Subgroup.normalizer (Sstar : Set (Bar2 K))) := by
    have hB := hcardB
    rw [top_inf_eq] at hB
    have h3R : 3 ∣ Nat.card ↥Sstar * (4 ^ n - 1) *
        Nat.card ↥(Subgroup.center ↥(⊤ : Subgroup (Bar2 K))) := by
      rw [hZ1, mul_one]
      refine dvd_mul_of_dvd_right ?_ (Nat.card ↥Sstar)
      have h := Nat.pow_sub_one_dvd_pow_sub_one 4 (one_dvd n)
      have h3 : (4 : ℕ) ^ 1 - 1 = 3 := by norm_num
      rwa [h3] at h
    have h : 3 ∣ Nat.card ↥(Subgroup.normalizer (Sstar : Set (Bar2 K))) *
        Nat.gcd 3 (2 ^ n + 1) := by
      rw [hB]
      exact h3R
    rwa [hgcd, mul_one] at h
  refine exists_elemAbelian_permutes_of_borel_commutative hKM hKn hSstardef.symm h3 ?_
  intro x y hx hy
  have hcyc : ∃ g ∈ (⊤ : Subgroup (Bar2 K)) ⊓
      Subgroup.normalizer (Sstar : Set (Bar2 K)),
      ∀ b ∈ (⊤ : Subgroup (Bar2 K)) ⊓
        Subgroup.normalizer (Sstar : Set (Bar2 K)),
        ∃ k : ℕ, (g ^ k)⁻¹ * b ∈ Sstar := hgen
  have habel := CFSG.Quasithin.H13.P31X.habel_of_cyc
    (B := (⊤ : Subgroup (Bar2 K)) ⊓ Subgroup.normalizer (Sstar : Set (Bar2 K)))
    (U := Sstar) (le_inf le_top Subgroup.le_normalizer) inf_le_right hcyc
  exact habel x (by simpa [← hSstardef] using hx) y (by simpa [← hSstardef] using hy)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
