module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Statements
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Ctx19One
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.GLBCoreNormalizer
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatSporadicBenderLarge
public import CFSG.Quasithin.Vol2.Ch10SecB3Aut
public import CFSG.RankThree.PartTwo.Sec15.Liebeck155KFacts
public import CFSG.GroupTheory.PElementSubgroup
public import CFSG.GroupTheory.PRankCommutingPerfect
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.CalCCoprimeAction
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.PermutesPairNormalizer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Bar13
public import CFSG.Quasithin.H13.U3L14D6
public import CFSG.RankThree.PartOne.S12.Sec15Frattini

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped commutatorElement Pointwise IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem commutator_eq_bot_of_isPGroup_three (D : Data G) (V₀ V : Subgroup G) (p : ℕ)
    (L K : Subgroup G) (h : Ctx19_1 D V₀ V p L K)
    (h192 : R19_2At D V₀ V p L K h)
    (h193 : R19_3At D V₀ V p L K h)
    {Y : Subgroup G} (hY : IsPGroup 3 ↥Y) (hYM : Y ≤ D.M) :
    ⁅V₀, Y⁆ = ⊥ := by
  have hYLE : Y ≤ L ⊔ K := by
    have hLK : Opp 3 D.M = L ⊔ K := h192
    rw [← hLK]
    exact le_pElementSubgroup_of_isPGroup (by norm_num) hY hYM
  have h1 : ⁅V₀, Y⁆ ≤ ⁅V₀, L ⊔ K⁆ :=
    Subgroup.commutator_mono le_rfl hYLE
  have h2 : ⁅V₀, L ⊔ K⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact h193
  exact le_bot_iff.1 (h1.trans (le_of_eq h2))

theorem prime_le_seven_of_isPGroup_commutator_ne_bot {D : Data G} {V₀ Y : Subgroup G} {q : ℕ}
    (hV₀ : IsElemAbelian 2 V₀) (hVnorm : D.M ≤ normalizer (V₀ : Set G))
    (hY : IsPGroup q Y) (hYM : Y ≤ D.M) (hq : q.Prime) (hodd : Odd (Nat.card Y))
    (hcomm : ⁅V₀, Y⁆ ≠ ⊥) (hrank : mSub V₀ ≤ 4) : q ≤ 7 := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hVp : IsPGroup 2 V₀ := CFSG.Open.IsElemAbelian.isPGroup hV₀
  have hYV : Y ≤ normalizer (V₀ : Set G) := hYM.trans hVnorm
  let φ : ↥Y →* MulAut ↥V₀ := V₀.normalizerMonoidHom.comp (Subgroup.inclusion hYV)
  have hφne : φ ≠ 1 := by
    intro h1
    apply hcomm
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h2 : φ ⟨y, hy⟩ = 1 := by rw [h1]; rfl
    have h3 : (φ ⟨y, hy⟩) ⟨v, hv⟩ = ⟨v, hv⟩ := by rw [h2]; rfl
    have h4 : y * v * y⁻¹ = v := by
      have h5 := congrArg (fun w : ↥V₀ => (w : G)) h3
      simpa [φ, Subgroup.normalizerMonoidHom_apply_apply_coe] using h5
    calc y * v = (y * v * y⁻¹) * y := by group
      _ = v * y := by rw [h4]
  have hrange_ne : φ.range ≠ ⊥ := by
    intro hbot
    apply hφne
    ext y v
    have hmem : φ y ∈ φ.range := ⟨y, rfl⟩
    rw [hbot] at hmem
    have h1 : φ y = 1 := by simpa using hmem
    rw [h1]
    rfl
  have hqrange : IsPGroup q ↥φ.range :=
    hY.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hq_dvd_range : q ∣ Nat.card ↥φ.range := by
    rcases hqrange.card_eq_or_dvd with h1 | h1
    · exact absurd (Subgroup.card_eq_one.mp h1) hrange_ne
    · exact h1
  have hdvd_mulAut : q ∣ Nat.card (MulAut ↥V₀) :=
    hq_dvd_range.trans (Subgroup.card_subgroup_dvd_card φ.range)
  let m := mSub V₀
  have hcard : Nat.card V₀ = 2 ^ m := card_eq_two_pow_mSub hVp
  haveI : IsMulCommutative ↥V₀ := hV₀.1
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2)
    (fun a b => mul_comm' a b)
    (fun a => by
      have h2 : ((a : G)) ^ 2 = 1 := hV₀.2 a a.2
      exact Subtype.ext (by simpa using h2)) (n := m) hcard
  have hGL : Nat.card (MulAut ↥V₀) = Nat.card (GL (Fin m) (ZMod 2)) :=
    CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL (p := 2) e
  rw [hGL, CFSG.SectionRank.Ccomm.card_GL_zmod (p := 2)] at hdvd_mulAut
  obtain ⟨i, -, hqi⟩ := (Prime.dvd_finset_prod_iff hq.prime _).1 hdvd_mulAut
  have hi : (i : ℕ) ≤ m := le_of_lt i.2
  have hfac : (2 : ℕ) ^ m - 2 ^ (i : ℕ) = 2 ^ (i : ℕ) * (2 ^ (m - (i : ℕ)) - 1) := by
    rw [Nat.mul_sub_left_distrib, mul_one, pow_mul_pow_sub (2 : ℕ) hi]
  rw [hfac] at hqi
  have hYne : Y ≠ ⊥ := by
    rintro rfl
    simp at hcomm
  have hq2 : q ≠ 2 := by
    rintro rfl
    have h2 : 2 ∣ Nat.card Y := by
      rcases (hY.card_eq_or_dvd) with h1 | h1
      · exact absurd (Subgroup.card_eq_one.mp h1) hYne
      · exact h1
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  have hqnot : ¬ q ∣ 2 ^ (i : ℕ) := by
    intro h
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h))
  have hdvd : q ∣ 2 ^ (m - (i : ℕ)) - 1 := by
    rcases (Nat.Prime.dvd_mul hq).1 hqi with h | h
    · exact absurd h hqnot
    · exact h
  have hdpos : 1 ≤ m - (i : ℕ) := by omega
  have hdle : m - (i : ℕ) ≤ 4 := by omega
  set d := m - (i : ℕ) with hd
  interval_cases d
  · have hle : q ≤ 1 := by simpa using Nat.le_of_dvd (by norm_num) hdvd
    omega
  · have hle : q ≤ 3 := by simpa using Nat.le_of_dvd (by norm_num) hdvd
    omega
  · have hle : q ≤ 7 := by simpa using Nat.le_of_dvd (by norm_num) hdvd
    omega
  · have h15 : q ∣ 15 := by simpa using hdvd
    have h35 : q ∣ 3 * 5 := by norm_num; exact h15
    rcases (Nat.Prime.dvd_mul hq).1 h35 with h | h
    · have hq3 : q = 3 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).1 h
      omega
    · have hq5 : q = 5 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).1 h
      omega

theorem normalizer_le_of_isPGroup_five {D : Data G} (hSg : UC6S846.SigmaStd D)
    (hns : ¬ Group.IsSolvable ↥D.M) (h5 : 5 ∈ D.sig) {Q : Subgroup G}
    (hQ : IsPGroup 5 Q) (hQne : Q ≠ ⊥) (hQM : Q ≤ D.M) :
    normalizer (Q : Set G) ≤ D.M := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact (UC6S846.sp_of_mem_sig hSg hns h5).normalizer_le hQne hQ hQM



theorem card_mulAut_bar2_of_isAlt_five {J : Subgroup G} (h : IsAlt (Bar2 J) 5) :
    Nat.card (MulAut (Bar2 J)) = 120 := by
  obtain ⟨e⟩ := h
  exact CFSG.Quasithin.Vol2.Ch10.SecB.card_mulAut_of_equiv_A5 e

theorem card_mulAut_bar2_of_isL2_two {J : Subgroup G} (h : IsL2 (Bar2 J) 2) :
    Nat.card (MulAut (Bar2 J)) = 120 := by
  have hsc : CFSG.Assembly.LowTwoRank.StatedClassicalModel (Bar2 J) .PSL 2 2 2 :=
    CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)
  obtain ⟨e⟩ :=
    CFSG.RankThree.PartTwo.Sec15.Liebeck155.nonempty_mulEquiv_alt5_of_statedClassicalModel hsc
  exact CFSG.Quasithin.Vol2.Ch10.SecB.card_mulAut_of_equiv_A5 e

theorem card_bar2_of_isU3_two {J : Subgroup G} (h : IsU3 (Bar2 J) 2) :
    Nat.card (Bar2 J) = 62400 := by
  have hsc : CFSG.Assembly.LowTwoRank.StatedClassicalModel (Bar2 J) .PSU 3 2 2 :=
    CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)
  have h1 := (CFSG.Timmesfeld.card_statedClassicalModel_two hsc).2.1 rfl
  rw [h1]
  decide

theorem center_bar2_of_isU3_two {J : Subgroup G} (h : IsU3 (Bar2 J) 2) :
    Subgroup.center (Bar2 J) = ⊥ := by
  have hsimple : IsSimpleGroup (Bar2 J) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h
  haveI := hsimple
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center (Bar2 J)) with hc | hc
  · exact hc
  · exfalso
    haveI : IsMulCommutative (Bar2 J) := ⟨⟨fun a b => by
      have ha : a ∈ Subgroup.center (Bar2 J) := by rw [hc]; exact Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.mp ha b).symm⟩⟩
    have hprime : (Nat.card (Bar2 J)).Prime := Group.is_simple_iff_prime_card.mp hsimple
    rw [card_bar2_of_isU3_two h] at hprime
    norm_num at hprime

theorem card_mulAut_bar2_of_isU3_two {J : Subgroup G} (h : IsU3 (Bar2 J) 2) :
    Nat.card (MulAut (Bar2 J)) = 249600 := by
  rw [CFSG.SeitzReduction.RankOne.card_mulAut_of_center_eq_bot
    (center_bar2_of_isU3_two h), card_bar2_of_isU3_two h,
    CFSG.LocalAnalysis.EvenBN.GMSK.SporadicBender.card_outer_of_lieModel_PSU3 h]
  norm_num

theorem not_seven_dvd_card_mulAut_of_shape {J : Subgroup G}
    (h : IsL2 (Bar2 J) 2 ∨ IsU3 (Bar2 J) 2) :
    ¬ 7 ∣ Nat.card (MulAut (Bar2 J)) := by
  rcases h with h | h
  · rw [card_mulAut_bar2_of_isL2_two h]; norm_num
  · rw [card_mulAut_bar2_of_isU3_two h]; norm_num

theorem not_seven_dvd_card_mulAut_of_isAlt_five {J : Subgroup G} (h : IsAlt (Bar2 J) 5) :
    ¬ 7 ∣ Nat.card (MulAut (Bar2 J)) := by
  rw [card_mulAut_bar2_of_isAlt_five h]; norm_num

theorem exists_sylow_commutator_ne_bot {V₀ Y : Subgroup G}
    (hcomm : ⁅V₀, Y⁆ ≠ ⊥) :
    ∃ q : ℕ, q.Prime ∧ ∃ Q : Sylow q ↥Y,
      ⁅V₀, ((Q : Subgroup ↥Y).map Y.subtype)⁆ ≠ ⊥ := by
  by_contra h
  simp only [not_exists, not_and, ne_eq, not_not] at h
  apply hcomm
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
  have htop : Y = ⨆ p ∈ (Nat.card Y).primeFactors,
      (((default : Sylow p ↥Y) : Subgroup ↥Y).map Y.subtype) := by
    calc Y = (⊤ : Subgroup ↥Y).map Y.subtype := by
          rw [Subgroup.map_top, Subgroup.range_subtype]
      _ = (⨆ p ∈ (Nat.card Y).primeFactors,
            ((default : Sylow p ↥Y) : Subgroup ↥Y)).map Y.subtype := by
          rw [Sylow.iSup_sylow_eq_top]
      _ = ⨆ p ∈ (Nat.card Y).primeFactors,
            (((default : Sylow p ↥Y) : Subgroup ↥Y).map Y.subtype) := by
          simp_rw [Subgroup.map_iSup]
  rw [htop]
  refine iSup₂_le fun p hp => ?_
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hQ := h p hpprime (default : Sylow p ↥Y)
  rw [Subgroup.commutator_comm] at hQ
  rwa [Subgroup.commutator_eq_bot_iff_le_centralizer] at hQ

theorem commutator_le_pCore_of_mem_calC_le_sup {D : Data G} {J L K : Subgroup G}
    (hJ : J ∈ calC D.M) (hL : L ∈ calC D.M) (hK : K ∈ calC D.M)
    (hJL : J ≠ L) (hJK : J ≠ K) (hLK : L ≠ K) :
    ⁅J, L ⊔ K⁆ ≤ pCoreOf 2 J := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLJ : L ≤ normalizer (J : Set G) := calC_le_normalizer_of_ne hJ hL hJL
  have hKJ : K ≤ normalizer (J : Set G) := calC_le_normalizer_of_ne hJ hK hJK
  have hLO : L ≤ normalizer (pCoreOf 2 J : Set G) :=
    hLJ.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 J)
  have hLKnorm : K ≤ normalizer (L : Set G) := calC_le_normalizer_of_ne hL hK hLK
  have hLKmul : ((L ⊔ K : Subgroup G) : Set G) = (L : Set G) * K :=
    Subgroup.coe_mul_of_right_le_normalizer_left L K hLKnorm
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have hy' : y ∈ (L : Set G) * K := hLKmul ▸ hy
  obtain ⟨l, hl, k, hk, rfl⟩ := hy'
  have hxl : ⁅x, l⁆ ∈ pCoreOf 2 J :=
    (calC_commutator_le_of_ne hJ hL hJL (Subgroup.commutator_mem_commutator hx hl)).1
  have hxk : ⁅x, k⁆ ∈ pCoreOf 2 J :=
    (calC_commutator_le_of_ne hJ hK hJK (Subgroup.commutator_mem_commutator hx hk)).1
  have hconj : l * ⁅x, k⁆ * l⁻¹ ∈ pCoreOf 2 J :=
    (Subgroup.mem_normalizer_iff.mp (hLO hl) _).mp hxk
  have hprod := (pCoreOf 2 J).mul_mem hxl hconj
  convert hprod using 1
  group

theorem eq_left_or_right_of_mem_calC_le_sup {D : Data G} {J L K : Subgroup G}
    (hJ : J ∈ calC D.M) (hL : L ∈ calC D.M) (hK : K ∈ calC D.M)
    (hLK : L ≠ K) (hJle : J ≤ L ⊔ K) : J = L ∨ J = K := by
  by_contra h
  push Not at h
  obtain ⟨hJL, hJK⟩ := h
  have hcomm := commutator_le_pCore_of_mem_calC_le_sup hJ hL hK hJL hJK hLK
  have hJJ : J ≤ pCoreOf 2 J := by
    calc J = ⁅J, J⁆ := hJ.2.1.symm
      _ ≤ ⁅J, L ⊔ K⁆ := Subgroup.commutator_mono le_rfl hJle
      _ ≤ pCoreOf 2 J := hcomm
  have htop : CFSG.pCore 2 ↥J = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hxO : (x : G) ∈ pCoreOf 2 J := hJJ x.2
    rw [pCoreOf] at hxO
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxO
    have hy' : y = x := Subtype.ext hyx
    rwa [hy'] at hy
  haveI : Subsingleton (Bar2 J) := QuotientGroup.subsingleton_iff.mpr htop
  haveI : Subsingleton (Bar2 J ⧸ Subgroup.center (Bar2 J)) := inferInstance
  haveI : Nontrivial (Bar2 J ⧸ Subgroup.center (Bar2 J)) := hJ.2.2.2.toNontrivial
  obtain ⟨a, b, hab⟩ := exists_pair_ne (Bar2 J ⧸ Subgroup.center (Bar2 J))
  exact hab (Subsingleton.elim a b)

theorem permutesPair_of_ctx19_one {D : Data G} {V₀ V : Subgroup G} {p : ℕ}
    {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K) : PermutesPair D.M L K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : L ≠ K := h.hne.symm
  have hLp_le : L ⊔ K ≤ D.M := by
    rw [← h.hLK]
    exact S17.Lp_le_M D 5
  have hMLp : D.M ≤ normalizer (S17.Lp D 5 : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (S17.Lp_le_M D 5)).mp
      (s13_Lp_normal D.M 5)
  have hLle : L ≤ S17.Lp D 5 := by rw [h.hLK]; exact le_sup_left
  have hKle : K ≤ S17.Lp D 5 := by rw [h.hLK]; exact le_sup_right
  have hconj : ∀ (J : Subgroup G) (m : G), J ∈ calC D.M → J ≤ S17.Lp D 5 →
      m ∈ D.M → J.map (MulAut.conj m).toMonoidHom = L ∨
        J.map (MulAut.conj m).toMonoidHom = K := by
    intro J m hJ hJle hm
    have hM : D.M.map (MulAut.conj m).toMonoidHom = D.M :=
      UC6S846.mem_normalizer_iff_map_conj.1 (Subgroup.le_normalizer hm)
    have hJ' : J.map (MulAut.conj m).toMonoidHom ∈ calC D.M :=
      UC6S846.calC_map D.M (MulAut.conj m) hM hJ
    have hJ'le : J.map (MulAut.conj m).toMonoidHom ≤ L ⊔ K := by
      rw [← h.hLK]
      exact Subgroup.map_mono hJle |>.trans (le_of_eq
        (UC6S846.mem_normalizer_iff_map_conj.mp (hMLp hm)))
    by_contra hcontra
    push Not at hcontra
    exact (eq_left_or_right_of_mem_calC_le_sup hJ' h.hyp.hL.1 h.hK hne hJ'le) |>.elim
      hcontra.1 hcontra.2
  intro m hm
  have hL' := hconj L m h.hyp.hL.1 hLle hm
  have hK' := hconj K m h.hK hKle hm
  rcases hL' with hL' | hL' <;> rcases hK' with hK' | hK'
  · exfalso
    exact hne (Subgroup.map_injective (MulAut.conj m).injective (hL'.trans hK'.symm))
  · exact Or.inl ⟨hL', hK'⟩
  · exact Or.inr ⟨hL', hK'⟩
  · exfalso
    exact hne (Subgroup.map_injective (MulAut.conj m).injective (hL'.trans hK'.symm))



theorem normalizer_le_of_isPGroup_seven {D : Data G} {V₀ V : Subgroup G} {p : ℕ}
    {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K) (h869 : F08.R869 D) {Q : Subgroup G}
    (hQ : IsPGroup 7 Q) (hQM : Q ≤ D.M) (hcomm : ⁅V₀, Q⁆ ≠ ⊥) :
    normalizer (Q : Set G) ≤ D.M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hne : L ≠ K := h.hne.symm
  have hperm : PermutesPair D.M L K := permutesPair_of_ctx19_one h
  have hQnorm : Q ≤ normalizer (L : Set G) ⊓ normalizer (K : Set G) :=
    le_normalizer_inf_of_permutesPair hperm Nat.prime_seven (by norm_num) hQ hQM
  have hQLn : Q ≤ normalizer (L : Set G) := hQnorm.trans inf_le_left
  have hQKn : Q ≤ normalizer (K : Set G) := hQnorm.trans inf_le_right
  have hYL : ∀ w ∈ Q, ∀ l ∈ L, w * l * w⁻¹ * l⁻¹ ∈ pCoreOf 2 L :=
    acts_trivially_of_isPGroup_of_not_dvd_card_mulAut Nat.prime_seven
      (not_seven_dvd_card_mulAut_of_shape h.shape) hQ hQLn
  have hYK : ∀ w ∈ Q, ∀ k ∈ K, w * k * w⁻¹ * k⁻¹ ∈ pCoreOf 2 K :=
    acts_trivially_of_isPGroup_of_not_dvd_card_mulAut Nat.prime_seven
      (not_seven_dvd_card_mulAut_of_isAlt_five h.hKshape) hQ hQKn
  have hLKle : L ⊔ K ≤ D.M := by
    rw [← h.hLK]
    exact S17.Lp_le_M D 5
  have hKLnorm : K ≤ normalizer (L : Set G) :=
    calC_le_normalizer_of_ne h.hyp.hL.1 h.hK hne
  have hLKnorm : L ≤ normalizer (K : Set G) :=
    calC_le_normalizer_of_ne h.hK h.hyp.hL.1 h.hne
  have hO2L : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ K) :=
    CFSG.Quasithin.H13.U3.pCoreOf_le_pCoreOf_sup_of_le hKLnorm
  have hO2K : pCoreOf 2 K ≤ pCoreOf 2 (L ⊔ K) := by
    have h' := CFSG.Quasithin.H13.U3.pCoreOf_le_pCoreOf_sup_of_le (T := L) (P := K) hLKnorm
    rwa [sup_comm] at h'
  have hQc : ∀ w ∈ Q, ∀ y ∈ L ⊔ K, w * y * w⁻¹ * y⁻¹ ∈ pCoreOf 2 (L ⊔ K) := by
    intro w hw y hy
    have hy' : y ∈ (L : Set G) * K :=
      (Subgroup.coe_mul_of_right_le_normalizer_left L K hKLnorm) ▸ hy
    obtain ⟨l, hl, k, hk, rfl⟩ := hy'
    have h1 : w * l * w⁻¹ * l⁻¹ ∈ pCoreOf 2 (L ⊔ K) := hO2L (hYL w hw l hl)
    have h2 : l * (w * k * w⁻¹ * k⁻¹) * l⁻¹ ∈ pCoreOf 2 (L ⊔ K) := by
      have hxk : w * k * w⁻¹ * k⁻¹ ∈ pCoreOf 2 K := hYK w hw k hk
      have hlN : l ∈ normalizer (pCoreOf 2 K : Set G) :=
        (hLKnorm.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)) hl
      exact hO2K ((Subgroup.mem_normalizer_iff.mp hlN _).mp hxk)
    have hprod := (pCoreOf 2 (L ⊔ K)).mul_mem h1 h2
    convert hprod using 1
    group
  have hMn : D.M ≤ normalizer ((L ⊔ K : Subgroup G) : Set G) := by
    rw [← h.hLK]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (S17.Lp_le_M D 5)).mp
      (s13_Lp_normal D.M 5)
  have hQnLK : Q ≤ normalizer ((L ⊔ K : Subgroup G) : Set G) := hQM.trans hMn
  have hXeq := eq_sup_centralizer_of_acts_trivially (p := 7) (by norm_num) (by norm_num)
    hQ hQnLK hQc
  have hthin : ¬ F08.Thin8 (L ⊔ K) := by
    intro hthin
    have h5L : 5 ∣ Nat.card L := by
      rw [← h.p_eq]
      exact (S17.mem_calLp).mp h.hyp.hL |>.2.2
    have h5K : 5 ∣ Nat.card K := by
      rw [card_eq_card_pCoreOf_mul_card_bar2 K]
      exact dvd_mul_of_dvd_right (by rw [card_bar2_of_isAlt_five h.hKshape]; norm_num) _
    have h1le : 1 ≤ CFSG.Open.pRank 5 L :=
      CFSG.AGLEmbedding.KFactProofs.GLBCoreNormalizer.one_le_pRank_of_dvd
        (K := G) (T := L) Nat.prime_five h5L
    have hcomm5 : ⁅L, K⁆ ≤ pCoreOf 2 (L ⊔ K) :=
      (calC_commutator_le_of_ne h.hyp.hL.1 h.hK hne).trans (inf_le_left.trans hO2L)
    have hrank := CFSG.GroupTheory.pRank_add_one_le_of_commutator_le_pCoreOf
      (q := 5) (by norm_num) le_sup_left le_sup_right hcomm5 h.hK.2.1 h5K
    have hle := hthin 5 Nat.prime_five (by norm_num)
    omega
  have hprod : F08.IsProdOfCalC D.M (L ⊔ K) := by
    refine ⟨2, fun i : Fin 2 => if i = 0 then L else K, ?_, ?_⟩
    · intro i
      fin_cases i <;> simp [h.hyp.hL.1, h.hK]
    · rw [show (List.ofFn fun i : Fin 2 =>
          ((if i = 0 then L else K : Subgroup G) : Set G)) = [(L : Set G), (K : Set G)] by
        rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_zero]
        simp]
      rw [List.prod_cons, List.prod_cons, List.prod_nil, mul_one]
      exact Subgroup.coe_mul_of_right_le_normalizer_left L K hKLnorm
  let X : Subgroup G := (L ⊔ K) ⊓ centralizer (Q : Set G)
  have hX : calNOf X = {D.M} :=
    h869 (L ⊔ K) (Or.inr ⟨hLKle, hMn, hprod⟩) X inf_le_left hXeq.symm hthin
  haveI : IsSimpleGroup G := D.standing.simple
  have hQne : Q ≠ ⊥ := by
    intro hbot
    rw [hbot] at hcomm
    simp at hcomm
  have hTne : D.T ≠ ⊥ :=
      CFSG.LocalAnalysis.RankThreeUC.ne_bot_of_isSylowOf_two D.maxLocal.1 D.sylowM
  have hNne : normalizer (Q : Set G) ≠ ⊤ := by
    intro htop
    haveI : Q.Normal := Subgroup.normalizer_eq_top_iff.1 htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Q with hbot | htopQ
    · exact hQne hbot
    · have hT2 : IsPGroup 2 D.T := D.sylowM.isPGroup
      have hTQ : D.T ≤ Q := by rw [htopQ]; exact le_top
      have hT7 : IsPGroup 7 D.T := hQ.to_le hTQ
      have hT1 : D.T = ⊥ :=
        disjoint_self.mp (IsPGroup.disjoint_of_ne 2 7 (by norm_num) D.T D.T hT2 hT7)
      exact hTne hT1
  obtain ⟨N, hNc, hNle⟩ :=
    (IsCoatomic.eq_top_or_exists_le_coatom (normalizer (Q : Set G))).resolve_left hNne
  have hXN : X ≤ N := (inf_le_right.trans (centralizer_le_normalizer Q)).trans hNle
  have hNM : N ∈ calNOf X := ⟨hNc, hXN⟩
  rw [hX] at hNM
  exact hNM ▸ hNle

theorem normalizer_le_of_isPGroup_odd {D : Data G} {V₀ V : Subgroup G} {p : ℕ}
    {L K : Subgroup G} (h : Ctx19_1 D V₀ V p L K)
    (h192 : R19_2At D V₀ V p L K h) (h193 : R19_3At D V₀ V p L K h)
    (h194 : R19_4At D V₀ V p L K h)
    (hSg : UC6S846.SigmaStd D) (h869 : F08.R869 D)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {Q : Subgroup G}
    (hQ : IsPGroup q Q) (hQM : Q ≤ D.M) (hcomm : ⁅V₀, Q⁆ ≠ ⊥) :
    normalizer (Q : Set G) ≤ D.M := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hodd : Odd (Nat.card Q) := by
    obtain ⟨k, hk⟩ := hQ.exists_card_eq
    rw [hk]
    exact (hq.odd_of_ne_two hq2).pow
  have hpairs := hyp123_pairFacts h.hyp.hyp125.1
  have hqle : q ≤ 7 :=
    prime_le_seven_of_isPGroup_commutator_ne_bot hpairs.elemAbelian₀ hpairs.le_normalizer₀
      hQ hQM hq hodd hcomm h194
  have hq3 : q ≠ 3 := by
    intro hq3
    subst hq3
    exact hcomm (commutator_eq_bot_of_isPGroup_three D V₀ V p L K h h192 h193 hQ hQM)
  have hq3le : 3 ≤ q := by
    have := hq.two_le
    omega
  have hns : ¬ Group.IsSolvable ↥D.M := UC6S846.not_solvable_of_mem_calC h.hK
  have h5 : 5 ∈ D.sig := h.p_eq ▸ h.hyp.hp
  interval_cases q
  · exact absurd rfl hq3
  · norm_num at hq
  · exact normalizer_le_of_isPGroup_five hSg hns h5 hQ (by
      intro hbot
      rw [hbot] at hcomm
      simp at hcomm) hQM
  · norm_num at hq
  · exact normalizer_le_of_isPGroup_seven h h869 hQ hQM hcomm

theorem nineteen_six {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {L K : Subgroup G}
    (h : Ctx19_1 D V₀ V p L K)
    (h192 : R19_2At D V₀ V p L K h) (h193 : R19_3At D V₀ V p L K h)
    (h194 : R19_4At D V₀ V p L K h)
    (hSg : UC6S846.SigmaStd D) (h869 : F08.R869 D) :
    R19_6At D V₀ V p L K h := by
  intro Y hYM hYodd hcomm
  obtain ⟨q, hq, Q, hQcomm⟩ := exists_sylow_commutator_ne_bot hcomm
  let Qg : Subgroup G := (Q : Subgroup ↥Y).map Y.subtype
  have hQcomm' : ⁅V₀, Qg⁆ ≠ ⊥ := hQcomm
  have hQp : IsPGroup q Qg := (Q.isPGroup').map Y.subtype
  have hQm : Qg ≤ D.M := by
    rintro _ ⟨y, -, rfl⟩
    exact hYM y.2
  have hq2 : q ≠ 2 := by
    intro hq2
    subst hq2
    have hQodd : Odd (Nat.card Qg) := by
      rw [Subgroup.card_map_of_injective Y.subtype_injective]
      exact Odd.of_dvd_nat hYodd (Subgroup.card_subgroup_dvd_card (Q : Subgroup ↥Y))
    have hbot : Qg = ⊥ := by
      by_contra hne
      have h2dvd : 2 ∣ Nat.card Qg :=
        hQp.card_eq_or_dvd.resolve_left (fun h1 => hne (Subgroup.card_eq_one.mp h1))
      exact (Nat.not_even_iff_odd.mpr hQodd) (even_iff_two_dvd.mpr h2dvd)
    rw [hbot] at hQcomm'
    simp at hQcomm'
  have hNQ : normalizer (Qg : Set G) ≤ D.M :=
    normalizer_le_of_isPGroup_odd h h192 h193 h194 hSg h869 hq hq2 hQp hQm hQcomm'
  haveI : Fact q.Prime := ⟨hq⟩
  have hQsyl : CFSG.ABGLocalTools.IsSylowOf q Qg Y := ⟨Q, rfl⟩
  intro g hg
  obtain ⟨k, hkY, hkQ⟩ :=
    CFSG.RankThree.PartOne.Sec15Frattini.exists_mem_normalizer_of_isSylowOf hQsyl hg
  have hkgM : k⁻¹ * g ∈ D.M := hNQ hkQ
  have hgEq : g = k * (k⁻¹ * g) := by group
  rw [hgEq]
  exact D.M.mul_mem (hYM hkY) hkgM


end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
