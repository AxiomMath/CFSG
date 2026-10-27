module

public import CFSG.RankThree.PartTwo.Sec19.Item19Res3ProofAsc93
public import CFSG.RankThree.PartTwo.Sec19.Steps195
public import CFSG.RankThree.PartTwo.Sec19.Step1919EndProof
import CFSG.RankThree.PartTwo.Sec19.Item19Res4ProofTripleA6
import CFSG.RankThree.PartTwo.Sec19.Step1911Proof
public import CFSG.RankThree.PartTwo.Sec19.Step1911EndProof
import CFSG.RankThree.PartTwo.KFacts.KS18M12Proof
import CFSG.RankThree.PartTwo.Sec19.Step1910O2Proof
import CFSG.RankThree.PartTwo.Sec19.Step198DProof
import CFSG.RankThree.PartTwo.Sec13.Item131bProofHeis
import CFSG.RankThree.PartTwo.Sec19.Item19Res3ProofCensus194
import CFSG.RankThree.PartOne.LIT.RankPSL3
import CFSG.RankThree.PartOne.LIT.RankMatrix
public import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
public import CFSG.RankThree.PartTwo.Sec19.Step1914E

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaMinus)

namespace Item19Res4Proof

theorem not_isTripleA6_of_trialityD4
    {X : Type} [Group X]
    (hX : IsTripleA6 X) {p f : ℕ}
    (hD4 : CFSG.Blueprint.ChevalleyExceptionalModel X .trialityD4 p f) : False := by
  obtain ⟨hp, hf, hcard⟩ := Step1911Proof.card_of_trialityD4 hD4
  have hq : 2 ≤ p ^ f := hp.two_le.trans (Nat.le_self_pow (by omega) p)
  exact Step1911Proof.ne_ordTrialityD4 hq (by norm_num) (by norm_num) (by norm_num)
    ((card_eq_of_isTripleA6 hX).symm.trans hcard)

end Item19Res4Proof

open Step1911Proof in
theorem step1911_of_wide3
    (h194 : Item194UsedWide3) :
    Step1911 := by
  intro G _ _ A c L E M hctx K hK hLK hK8 d hdD hdc H hH hHM hKJ
  have hE := hctx.isE27
  have hdE : d ∈ E := (Subgroup.mem_inf.mp hdD).1
  have hEC : E ≤ Subgroup.centralizer ({d} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hE.1.1.is_comm.comm ⟨x, hx⟩ ⟨d, hdE⟩))
  have hEH : E ≤ H := fun x hx => hH.2 (hEC hx)
  obtain ⟨-, hJ⟩ := h194 G hctx.toSec19Std E M H hE hctx.mem_scriptM
    (mem_scriptM_iff.mpr ⟨hH.1, fun x hx => hEH hx⟩) hHM
  obtain ⟨hlist, hpar⟩ := hJ K hKJ
  refine ⟨?_, ?_⟩
  · rcases hK8 with h | ⟨⟨p, f, hD4⟩, -⟩
    · exact h
    · rcases hlist with hlist | hsmall | htriple
      · exact (not_isList194_of_trialityD4 hlist hD4).elim
      · exact (not_isSmall194_of_trialityD4 hsmall hD4).elim
      · exact (Item19Res4Proof.not_isTripleA6_of_trialityD4 htriple hD4).elim
  · rcases hpar with ⟨-, h⟩ | ⟨-, hext⟩
    · exact h
    · exact (false_of_isExtOf hE hctx.inf_noncyclic hLK hEH hext).elim

open Step1919EndProof in
theorem step1919End_of_parabolic_wide3
    (h194 : Item194UsedWide3) (h1914 : Step1914) (hG2P : KS1919G2P) (hU48 : KS1919U48) :
    Step1919End := by
  intro G _ _ A c L E M hctx hLM H hH hHM K hKJ hEK
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEE : E ∈ partTwoE G := hctx.mem_partTwoT.1
  have hE := isE27_of_mem_partTwoE hEE
  have hE3 : IsPGroup 3 E := hE.isPGroup
  have hEH : E ≤ H := fun x hx => hH.2 (hctx.le_centralizer hx)
  have hK : K ∈ oTwoComponentsIn M := hKJ.1
  have hEne : E ≠ ⊥ := by
    intro h
    have h2 := hE.2
    rw [h, Subgroup.card_bot] at h2
    norm_num at h2
  obtain ⟨-, hJ⟩ := h194 G hctx.toSec19Std E M H hE hctx.mem_scriptM
    (mem_scriptM_iff.mpr ⟨hH.1, fun x hx => hEH hx⟩) hHM
  obtain ⟨hlist, hpar⟩ := hJ K hKJ
  have hEnc : ¬ IsCyclic (E ⊓ K : Subgroup G) := by
    rw [inf_of_le_left hEK]
    intro hcyc
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := E)
    have h27 : orderOf g = 27 := by rw [orderOf_eq_card_of_forall_mem_zpowers hg, hE.2]
    have hg3 : g ^ 3 = 1 := Subtype.ext (by simpa using hE.1.2 _ g.2)
    have h1 := orderOf_dvd_of_pow_eq_one hg3
    rw [h27] at h1
    norm_num at h1
  obtain ⟨hA10, hpp⟩ : IsEmpty (K ⧸ CFSG.pCore 2 K ≃* alternatingGroup (Fin 10)) ∧
      IsProperParabolic (starIm K H) := by
    rcases hpar with h | ⟨-, hext⟩
    · exact h
    · exact (Step1911Proof.false_of_isExtOf hE hEnc le_rfl hEH hext).elim
  have hEs : CFSG.Open.IsElemAbelian 3 (starIm K E) := isElemAbelian_starIm hE.1
  have hEs27 : Nat.card (starIm K E) = 27 := (card_starIm hE3 hEK).trans hE.2
  have hEsc : ∀ x ∈ starIm K E, ∀ y ∈ starIm K E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hEs.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h3 : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (K ⧸ CFSG.pCore 2 K)) :=
    CFSG.SectionRank.le_pRank (by norm_num) le_top hEs (by rw [hEs27]; norm_num)
  have hperf : Group.IsPerfect (K ⧸ CFSG.pCore 2 K) := by
    have := isPerfect_of_mem_oTwoComponentsIn hK
    infer_instance
  replace hlist : IsList194 (K ⧸ CFSG.pCore 2 K) ∨ IsSmall194 (K ⧸ CFSG.pCore 2 K) := by
    rcases hlist with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (Item19Res4Proof.card_ne_twentySeven_of_isTripleA6 h (starIm K E) hEs hEs27).elim
  have hZ := center_eq_bot_of_isList194_wide hlist hperf h3
  have h9 := rank3II_19_14E_of h1914 KFacts.ks18M12 G A c L E M hctx hLM
  have hFE : E ⊓ L ≤ E := inf_le_left
  have hFgam : Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G) ≤ M := by
    have hFab : CFSG.Assembly.IsElemAbelian 3 (E ⊓ L) := Late.isElemAbelian_of_le hE.1 hFE
    exact (normalizer_le_gamma hFE (two_le_pRank_of_elemAbelian hFab h9.ge)).trans
      hctx.mem_scriptM.2
  set Y := Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G) ⊓
    Subgroup.normalizer (E : Set G) with hY
  have hYE : Y ≤ Subgroup.normalizer (E : Set G) := inf_le_right
  have hYK : Y ≤ Subgroup.normalizer (K : Set G) := fun y hy =>
    mem_normalizer_of_mem hK hEK hE.1.2 hEne hZ (hFgam hy.1) hy.2
  have hEY : E ≤ Y := by
    refine le_inf (fun e he => Subgroup.centralizer_le_normalizer _ ?_) Subgroup.le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact congrArg Subtype.val (hE.1.1.is_comm.comm ⟨f, hFE hf⟩ ⟨e, he⟩)
  have hrange : (E.normalizerMonoidHom.comp (Subgroup.inclusion hYE)).range =
      Sec4.autIn (Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G)) E := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  have h216 := two_hundred_sixteen_dvd_card ((h1914 G A c L E M hctx).2 hLM)
  have h729 : 3 ^ 6 ∣ Nat.card (MulAut (K ⧸ CFSG.pCore 2 K)) := by
    have h1 : 27 * 27 ∣ Nat.card E *
        Nat.card (E.normalizerMonoidHom.comp (Subgroup.inclusion hYE)).range := by
      rw [hE.2, hrange]
      exact Nat.mul_dvd_mul_left 27 ((by norm_num : (27 : ℕ) ∣ 216).trans h216)
    have h2 := h1.trans ((card_mul_card_range_dvd hEK hEY hYE hYK hE.1.1 hE.1.2 hZ).trans
      (Subgroup.card_subgroup_dvd_card _))
    exact (by norm_num : (3 : ℕ) ^ 6 = 27 * 27) ▸ h2
  have h27 : 27 ∣ Nat.card (K ⧸ CFSG.pCore 2 K) :=
    hEs27 ▸ Subgroup.card_subgroup_dvd_card (starIm K E)
  rcases hlist with hlist | hsmall
  swap
  · exact false_of_isSmall194 hsmall h27 h3
  rcases hlist with ⟨n, hn, h | h | h | hG⟩ | h | h | h | h | h | h | h | h | ⟨b, b', hbb, h⟩ | h
  ·
    obtain ⟨e⟩ := h
    have h2 := pRank_three_SL_le (F := GaloisField 2 n) three_ne_zero_of_charTwo
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e] at h2
    omega
  ·
    obtain ⟨e⟩ := h
    have h2 := CFSG.RankThree.PartOne.LIT.pRank_projSL_three_le (K := GaloisField 2 n) (f := n)
      hn (GaloisField.card 2 n (by omega)) Nat.prime_three (by norm_num)
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e] at h2
    omega
  ·
    obtain ⟨e⟩ := h
    have h2 := CFSG.RankThree.PartOne.LIT.pRank_projSp_two_le (K := GaloisField 2 n)
      Nat.prime_three (by norm_num)
      (CFSG.RankThree.PartOne.LIT.natCast_ne_zero_of_charTwo Nat.prime_three (by norm_num))
    rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e] at h2
    omega
  ·
    have h2 := hG2P _ n hG (starIm K H) hpp (starIm K E)
      (Subgroup.map_mono fun x hx => hEH hx) hEsc hEs.2
    omega
  ·
    obtain ⟨e⟩ := h
    refine not_dvd_card_mulAut_of_mulEquiv e ?_ not_nine_dvd_card_outer_projSU_four_two h729
    rw [Step1911Proof.card_projSU_four le_rfl]
    norm_num
  ·
    have h2 := hU48 _ h (starIm K H) hpp (starIm K E)
      (Subgroup.map_mono fun x hx => hEH hx) hEsc hEs.2
    omega
  ·
    obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, Step1911Proof.card_projSL (by norm_num) le_rfl] at h27
    exact absurd h27 (by decide)
  ·
    obtain ⟨e⟩ := h
    refine not_dvd_card_mulAut_of_mulEquiv e ?_
      (not_nine_dvd_card_outer_projSL (by norm_num) (by norm_num) le_rfl (by norm_num)) h729
    rw [Step1911Proof.card_projSL (by norm_num) (by norm_num)]
    decide
  ·
    obtain ⟨e⟩ := h
    rw [Nat.card_congr e.toEquiv, Step1911Proof.card_projSL (by norm_num) le_rfl] at h27
    exact absurd h27 (by decide)
  ·
    obtain ⟨e⟩ := h
    refine not_dvd_card_mulAut_of_mulEquiv e ?_
      (not_nine_dvd_card_outer_projSL (by norm_num) le_rfl (by norm_num) (by norm_num)) h729
    rw [Step1911Proof.card_projSL (by norm_num) le_rfl]
    decide
  ·
    obtain ⟨e⟩ := h
    refine not_dvd_card_mulAut_of_mulEquiv e ?_
      (not_nine_dvd_card_outer_projSL (by norm_num) le_rfl (by norm_num) (by norm_num)) h729
    rw [Step1911Proof.card_projSL (by norm_num) le_rfl]
    decide
  ·
    obtain ⟨e⟩ := h
    refine not_dvd_card_mulAut_of_mulEquiv e ?_ not_nine_dvd_card_outer_projSp h729
    rw [Step1911Proof.card_projSp 3 le_rfl]
    decide
  ·
    obtain ⟨e⟩ := h
    refine not_dvd_card_mulAut_of_mulEquiv e ?_ (not_nine_dvd_card_outer_projOmegaMinus hbb) h729
    rw [Step1911Proof.card_projOmegaMinus hbb]
    decide
  ·
    obtain ⟨e⟩ := h
    exact hA10.false e

open Step1910Proof in
theorem step1910_of_wide3
    (h194 : Item194UsedWide3) :
    Step1910 := by
  intro G _ _ A c L E M hctx K hK hLK _ d hdD _ _ H hH hHM
  refine ⟨hK, fun hKH => ?_⟩
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hst := hctx.toPartTwoStanding
  have hS := hctx.partTwoS_eq
  have hE := hctx.isE27
  have hAE : A ∈ partTwoE G := hctx.mem_partTwoE
  have hA := isE27_of_mem_partTwoE hAE
  have hA3 : IsPGroup 3 A := hA.isPGroup
  have hAe : ∀ a ∈ A, a ^ 3 = 1 := hA.1.2
  have hEe : ∀ e ∈ E, e ^ 3 = 1 := hE.1.2
  have hdE : d ∈ E := hdD.1
  have hdA : d ∈ A := hdD.2
  have hEH : E ≤ H := fun x hx => hH.2 (le_centralizer_of_mem hE.1.1 hdE hx)
  have hAH : A ≤ H := fun x hx => hH.2 (le_centralizer_of_mem hA.1.1 hdA hx)
  have hAM : A ≤ M := hctx.le_normalizer.trans
    ((normalizer_le_gamma le_rfl (by rw [hE.pRank_eq]; norm_num)).trans hctx.mem_scriptM.2)
  set Q := CFSG.Open.pCoreOf 2 M with hQdef
  have hQ : Q ≠ ⊥ := pCoreOf_ne_bot_of_isMaximalTwoLocal hctx.mem_scriptM.1
  have hKM : K ≤ M := le_of_mem_oTwoComponentsIn hK
  have hLM : L ≤ M := hLK.trans hKM
  have hL := hctx.mem_lA.1
  have hLA : A ≤ Subgroup.normalizer (L : Set G) := hctx.mem_lA.2.1
  obtain ⟨⟨J, hJM, hJH⟩, hJall⟩ := h194 G hctx.toSec19Std E M H hE hctx.mem_scriptM
    (mem_scriptM_iff.mpr ⟨hH.1, fun x hx => hEH hx⟩) hHM
  obtain ⟨hlist, hpar⟩ := hJall J ⟨hJM, hJH⟩
  have hJK : J ≠ K := fun h => hJH (h ▸ hKH)
  have hqJ := Sec18.isQuasisimple_of_mem_oTwoComponentsIn hJM
  have hperfJ : Group.IsPerfect (J ⧸ CFSG.pCore 2 J) := hqJ.1
  have hLne : L ≠ ⊥ := by
    intro h
    have hq := Sec12.isQuasisimple_thetaQuot_of_mem hL
    have : Nontrivial (L ⧸ aschbacherSolvableCore 3 L) := LocalCores.isQuasisimple_nontrivial hq
    obtain ⟨u, v, huv⟩ := exists_pair_ne (L ⧸ aschbacherSolvableCore 3 L)
    apply huv
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective v
    have hu : u = 1 := Subtype.ext (by
      change (u : G) = 1
      rw [← Subgroup.mem_bot, ← h]
      exact u.2)
    have hv : v = 1 := Subtype.ext (by
      change (v : G) = 1
      rw [← Subgroup.mem_bot, ← h]
      exact v.2)
    rw [hu, hv]
  have hLperf : ⁅L, L⁆ = L := Subgroup.isPerfect_iff.mp (isPerfect_of_mem_thetaComponentsIn hL)
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    by_contra hne
    have hKa := Sec18.map_conj_mem_oTwoComponentsIn hK (hAM ha)
    have hLKa : L ≤ K.map (MulAut.conj a).toMonoidHom := by
      intro l hl
      refine ⟨a⁻¹ * l * a, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
      have := (Subgroup.mem_normalizer_iff.mp (hLA (Subgroup.inv_mem _ ha)) l).mp hl
      exact hLK (by simpa using this)
    have hLQ : L ≤ Q := by
      rw [← hLperf, Subgroup.commutator_le]
      intro l hl l' hl'
      rw [commutatorElement_def]
      exact commutator_mem_pCoreOf hK hKa (Ne.symm hne) (hLK hl) (hLKa hl')
    have hL2 : IsPGroup 2 L := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le hLQ
    have : Group.IsSolvable L := by
      have := hL2.isNilpotent
      infer_instance
    have : Nontrivial L := (Subgroup.nontrivial_iff_ne_bot L).mpr hLne
    have : Group.IsPerfect L := isPerfect_of_mem_thetaComponentsIn hL
    exact Group.IsPerfect.not_isSolvable L inferInstance
  have hlist' : (IsList194 (J ⧸ CFSG.pCore 2 J) ∨ IsSmall194 (J ⧸ CFSG.pCore 2 J)) ∨
      IsTripleA6 (J ⧸ CFSG.pCore 2 J) := by
    rcases hlist with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  obtain ⟨xb, hxb3, hxbc⟩ : ∃ x : J ⧸ CFSG.pCore 2 J, x ^ 3 = 1 ∧
      x ∉ Subgroup.center (J ⧸ CFSG.pCore 2 J) := by
    rcases hlist' with h | h
    · exact exists_noncentral_of_isList194_wide h hperfJ
    · exact Item19Res4Proof.exists_noncentral_of_isTripleA6 h
  have hJAc : ∀ y ∈ J, y ∈ A → y ∈ Subgroup.zpowers c := by
    intro y hyJ hyA
    have hsec : y ∈ Late.sectionCentralizer A L ((aschbacherSolvableCore 3 L).map L.subtype) := by
      refine ⟨hyA, fun l hl => ?_⟩
      have h1 := commutator_mem_pCoreOf hJM hK hJK hyJ (hLK hl)
      have h2 : y * l * y⁻¹ * l⁻¹ ∈ L := L.mul_mem
        ((Subgroup.mem_normalizer_iff.mp (hLA hyA) l).mp hl) (L.inv_mem hl)
      exact inf_pCoreOf_le_theta hLM ⟨h2, h1⟩
    rw [hctx.mem_lA.2.2.1] at hsec
    exact hsec
  by_cases hAJ : A ≤ Subgroup.normalizer (J : Set G)
  ·
    have h3J : 3 ∣ Nat.card J := by
      have hxb1 : xb ≠ 1 := fun h => hxbc (h ▸ Subgroup.one_mem _)
      have h1 := orderOf_dvd_natCard xb
      rw [orderOf_eq_prime hxb3 hxb1] at h1
      exact h1.trans (by
        rw [(CFSG.pCore 2 J).card_eq_card_quotient_mul_card_subgroup]
        exact dvd_mul_right _ _)
    obtain ⟨y, hyJ, hy1, hy3, hyA⟩ := exists_mem_of_le_normalizer hA3 hAJ h3J
    have hyAmem : y ∈ A := mem_of_le_centralizer hst hS hAE hy3 fun a ha =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hyA a ha)
    have hyc := hJAc y hyJ hyAmem
    have hcy : Subgroup.zpowers y = Subgroup.zpowers c := by
      have hyo : orderOf y = 3 := orderOf_eq_prime hy3 hy1
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hyc) ?_
      rw [hctx.zpowers_mem_omegaA.2.1, Nat.card_zpowers, hyo]
    have hcJ : c ∈ J := by
      have : c ∈ Subgroup.zpowers y := hcy ▸ Subgroup.mem_zpowers c
      exact (Subgroup.zpowers_le.mpr hyJ) this
    have hco : orderOf c = 3 := by
      rw [← Nat.card_zpowers]
      exact hctx.zpowers_mem_omegaA.2.1
    have hcZ : ((⟨c, hcJ⟩ : J) : J ⧸ CFSG.pCore 2 J) ∈ Subgroup.center (J ⧸ CFSG.pCore 2 J) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
      have h1 := commutator_mem_pCoreOf hJM hK hJK g.2 (hLK hctx.mem_L)
      have h2 : (g : G) * c * (g : G)⁻¹ * c⁻¹ ∈ CFSG.Open.pCoreOf 2 J :=
        inf_pCoreOf_le hJM ⟨J.mul_mem (J.mul_mem (J.mul_mem g.2 hcJ) (J.inv_mem g.2))
          (J.inv_mem hcJ), h1⟩
      have h3 : (g * ⟨c, hcJ⟩ * g⁻¹ * (⟨c, hcJ⟩ : J)⁻¹ : J) ∈ CFSG.pCore 2 J := by
        rw [Step1911EndProof.mem_pCore_iff]
        exact h2
      have h4 : ((g * ⟨c, hcJ⟩ * g⁻¹ * (⟨c, hcJ⟩ : J)⁻¹ : J) : J ⧸ CFSG.pCore 2 J) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr h3
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_inv] at h4
      exact Step1910O2Proof.mul_comm_of_commutator_eq_one h4
    have hc1 := mk_ne_one_of_orderOf (J := J) (c := ⟨c, hcJ⟩) hco
    have hparJ : IsProperParabolic (starIm J H) := by
      rcases hpar with ⟨-, h⟩ | ⟨⟨e⟩, -⟩
      · exact h
      · have := alternatingGroup.isSimpleGroup (α := Fin 10) (by simp)
        exact (KFacts.false_of_isSimpleGroup_of_mulEquiv e hperfJ hcZ hc1).elim
    obtain ⟨x, hx3, hxc, hxf⟩ : ∃ x : J ⧸ CFSG.pCore 2 J, x ^ 3 = 1 ∧
        x ∉ Subgroup.center (J ⧸ CFSG.pCore 2 J) ∧ ∀ a : A, quotAct hAJ a x = x := by
      rcases hlist' with hlist | htriple
      ·
        obtain ⟨n, -, ⟨ψ⟩⟩ :=
          Step1911EndProof.exists_mulEquiv_SL_of_isList194_wide hlist hperfJ hcZ hc1
        have hψZ : ψ ((⟨c, hcJ⟩ : J) : J ⧸ CFSG.pCore 2 J) ∈
            Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n)) := by
          rw [Subgroup.mem_center_iff] at hcZ ⊢
          intro s
          obtain ⟨t, rfl⟩ := ψ.surjective s
          rw [← map_mul, ← map_mul, hcZ t]
        obtain ⟨r, hr3, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hψZ
        rw [Fintype.card_fin] at hr3
        have hr1 : r ≠ 1 := by
          rintro rfl
          apply hc1
          apply ψ.injective
          rw [map_one]
          apply Subtype.ext
          rw [← hr, map_one]
          rfl
        exact exists_fixed_of_mulEquiv_SL hAJ hAH hAe hr1 hr3 ψ hparJ
      ·
        have hW3 : ∀ w ∈ (quotAct hAJ).range, w ^ 3 = 1 := by
          rintro _ ⟨a, rfl⟩
          have ha : a ^ 3 = 1 := Subtype.ext (by simpa using hAe a a.2)
          rw [← map_pow, ha, map_one]
        have hWP : ∀ w ∈ (quotAct hAJ).range, ∀ p ∈ starIm J H, w p ∈ starIm J H := by
          rintro _ ⟨a, rfl⟩ _ ⟨j, hjH, rfl⟩
          obtain ⟨j', hj', hact⟩ := quotAct_mk hAJ a j
          refine ⟨j', Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
          · rw [hj']
            exact H.mul_mem (H.mul_mem (hAH a.2) (Subgroup.mem_subgroupOf.mp hjH))
              (H.inv_mem (hAH a.2))
          · exact hact.symm
        obtain ⟨x, hx3, hxc, hxf⟩ :=
          Item19Res4Proof.exists_fixed_of_isTripleA6 htriple _ hW3 _ hparJ hWP
        exact ⟨x, hx3, hxc, fun a => hxf _ ⟨a, rfl⟩⟩
    obtain ⟨y', hy'3, hy'A, hy'c⟩ := exists_lift_of_fixed hA3 hAJ hxf hx3 hxc
    have hy'Amem : (y' : G) ∈ A := mem_of_le_centralizer hst hS hAE hy'3 fun a ha =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hy'A a ha)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hJAc y' y'.2 hy'Amem)
    apply hy'c
    have hy'eq : y' = (⟨c, hcJ⟩ : J) ^ k := Subtype.ext (by rw [Subgroup.coe_zpow, ← hk])
    rw [hy'eq, QuotientGroup.mk_zpow]
    exact Subgroup.zpow_mem _ hcZ k
  ·
    obtain ⟨a, ha, haJ⟩ := Set.not_subset.mp hAJ
    set J₂ := J.map (MulAut.conj a).toMonoidHom with hJ₂
    have hJ₂M : J₂ ∈ oTwoComponentsIn M := Sec18.map_conj_mem_oTwoComponentsIn hJM (hAM ha)
    have hJJ₂ : J ≠ J₂ := by
      intro h
      apply haJ
      change a ∈ Subgroup.normalizer (J : Set G)
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact h.symm
    have hJ₂K : J₂ ≠ K := by
      intro h
      apply hJK
      have h1 : J₂.map (MulAut.conj a⁻¹).toMonoidHom = J := by
        rw [hJ₂, Subgroup.map_map]
        convert Subgroup.map_id J
        ext g
        simp [MulAut.conj_apply, mul_assoc]
      rw [← h1, h]
      exact Late.map_conj_eq_of_mem_normalizer (hAK (Subgroup.inv_mem _ ha))
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xb
    have hx3 : (x : G) ^ 3 ∈ Q := by
      have h1 : x ^ 3 ∈ CFSG.pCore 2 J := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
        exact hxb3
      rw [Step1911EndProof.mem_pCore_iff] at h1
      exact Sec18.pCoreOf_le_pCoreOf_of_mem_oTwoComponentsIn hJM (by simpa using h1)
    obtain ⟨g, hg⟩ : ∃ g : J, (x : J ⧸ CFSG.pCore 2 J) * g ≠ g * x := by
      by_contra hall
      push Not at hall
      apply hxbc
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
      exact (hall g).symm
    have hxnc : (x : G) * g * (x : G)⁻¹ * (g : G)⁻¹ ∉ Q := by
      intro h
      apply hg
      have h2 : (x * g * x⁻¹ * g⁻¹ : J) ∈ CFSG.pCore 2 J := by
        rw [Step1911EndProof.mem_pCore_iff]
        exact inf_pCoreOf_le hJM ⟨(x * g * x⁻¹ * g⁻¹ : J).2, h⟩
      have h3 : ((x * g * x⁻¹ * g⁻¹ : J) : J ⧸ CFSG.pCore 2 J) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr h2
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_inv] at h3
      exact Step1910O2Proof.mul_comm_of_commutator_eq_one h3
    have haQ : a ∈ Subgroup.normalizer (Q : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M (hAM ha)
    have hx₂ : a * x * a⁻¹ ∈ J₂ := ⟨x, x.2, rfl⟩
    have hx₂3 : (a * x * a⁻¹) ^ 3 ∈ Q := by
      rw [conj_pow]
      exact (Subgroup.mem_normalizer_iff.mp haQ _).mp hx3
    have hx₂nc : ∃ j ∈ J₂, (a * x * a⁻¹) * j * (a * x * a⁻¹)⁻¹ * j⁻¹ ∉ Q := by
      refine ⟨a * g * a⁻¹, ⟨g, g.2, rfl⟩, fun h => hxnc ?_⟩
      have e : (a * x * a⁻¹) * (a * g * a⁻¹) * (a * x * a⁻¹)⁻¹ * (a * g * a⁻¹)⁻¹ =
          a * ((x : G) * g * (x : G)⁻¹ * (g : G)⁻¹) * a⁻¹ := by group
      rw [e] at h
      exact (Subgroup.mem_normalizer_iff.mp haQ _).mpr h
    have hF9 : 9 ≤ Nat.card (E ⊓ L : Subgroup G) :=
      Step198DProof.nine_le_card_of_not_isCyclic (fun e he => hEe e he.1) hctx.inf_noncyclic
    have h4 := four_le_localRank hQ hK hJM hJ₂M hJK hJ₂K hJJ₂ (inf_le_right.trans hLK)
      (fun e he => hEe e he.1)
      (fun e he f hf => congrArg Subtype.val (hE.1.1.is_comm.comm ⟨e, he.1⟩ ⟨f, hf.1⟩))
      hF9 x.2 hx₂ hx3 hx₂3 ⟨g, g.2, hxnc⟩ hx₂nc
    rw [hst.toTheoremFourHyp.localRank_three] at h4
    omega

open Step1911EndProof in
theorem step1911End_of_spor_wide3
    (h194 : Item194UsedWide3) (h131 : Item131) (hspor : SporadicModels131) : Step1911End := by
  intro G _ _ A c L E M hctx K hK hLK hKL d hdD hdc H hHd hHM hKJ hpar
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hst := hctx.toPartTwoStanding
  have hFE : partTwoF G = partTwoE G :=
    (hst.toTheoremFourHyp.partTwoF_eq_partTwoE hctx.partTwoS_eq).1
  have hD : Sec13Data G A c L := ⟨hst, hctx.partTwoS_eq, hFE ▸ hctx.mem_partTwoE,
    hctx.not_mem_partTwoT, hctx.zpowers_mem_omegaA, hctx.mem_lA⟩
  have hcL : c ∈ L := hctx.mem_L
  have hE := hctx.isE27
  have hAM : A ≤ M := hctx.le_normalizer.trans
    ((normalizer_le_gamma le_rfl (by rw [hE.pRank_eq]; norm_num)).trans hctx.mem_scriptM.2)
  have hAK : ∀ a ∈ A, a ∈ Subgroup.normalizer (K : Set G) := fun a ha =>
    Sec18.mem_normalizer_of_eq_sup hK hKL (hAM ha) (hD.le_normalizer ha)
  have hAH : ∀ a ∈ A, a ∈ H := fun a ha =>
    hHd.2 (Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute ha hdD.2))
  have hEH : (E : Set G) ⊆ H := fun e he =>
    hHd.2 (Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hE.1.1.is_comm.comm ⟨e, he⟩ ⟨d, hdD.1⟩)))
  have hlist3 : IsList194 (K ⧸ CFSG.pCore 2 K) ∨ IsSmall194 (K ⧸ CFSG.pCore 2 K) ∨
      IsTripleA6 (K ⧸ CFSG.pCore 2 K) :=
    ((h194 G hctx.toSec19Std E M H hE hctx.mem_scriptM ⟨hHd.1, hEH⟩ hHM).2 K hKJ).1
  have hq := Sec18.isQuasisimple_of_mem_oTwoComponentsIn hK
  have hcZ := phiL_mem_center hLK hKL hcL hD.le_centralizer
  have hc1 := phiL_ne_one hLK hcL hD.orderOf_eq
  have hlist : IsList194 (K ⧸ CFSG.pCore 2 K) ∨ IsSmall194 (K ⧸ CFSG.pCore 2 K) := by
    rcases hlist3 with h | h | htriple
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      have hZ3 : ∀ z ∈ Subgroup.center (K ⧸ CFSG.pCore 2 K), z ^ 3 = 1 := fun z hz =>
        Item19Res4Proof.pow_three_eq_one_of_mem_center htriple hz
      have hθ := phiL_eq_one_iff_mem_theta hK hLK hKL hZ3
      have hker : (phiL hLK).ker = aschbacherSolvableCore 3 L := by
        ext m
        rw [MonoidHom.mem_ker, hθ]
      let eL : L ⧸ aschbacherSolvableCore 3 L ≃* K ⧸ CFSG.pCore 2 K :=
        (QuotientGroup.quotientMulEquivOfEq hker).symm.trans
          (QuotientGroup.quotientKerEquivOfSurjective _ (phiL_surjective hLK hKL))
      exact Item131bProof.not_isTripleCover_six (Step1910O2Proof.type_of_mem h131 hspor hD hcL)
        (Item19Res3Proof.isTripleA6_of_mulEquiv eL htriple)
  obtain ⟨n, hn1, ⟨ψ⟩⟩ := exists_mulEquiv_SL_of_isList194_wide hlist hq.1 hcZ hc1
  have hψZ : ∀ z ∈ Subgroup.center (K ⧸ CFSG.pCore 2 K),
      ψ z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n)) := by
    intro z hz
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro s
    obtain ⟨t, rfl⟩ := ψ.surjective s
    rw [← map_mul, ← map_mul, hz t]
  have hn : 2 ≤ n := by
    by_contra hn2
    obtain rfl : n = 1 := by omega
    apply hc1
    apply ψ.injective
    rw [map_one]
    exact eq_one_of_mem_center_two (hψZ _ hcZ)
  have hZ3 : ∀ z ∈ Subgroup.center (K ⧸ CFSG.pCore 2 K), z ^ 3 = 1 := by
    intro z hz
    apply ψ.injective
    rw [map_pow, map_one]
    exact pow_three_eq_one_of_mem_center (hψZ z hz)
  have hθ := phiL_eq_one_iff_mem_theta hK hLK hKL hZ3
  have hAP : ∀ (a : G) (ha : a ∈ A) (m : L), phiL hLK m ∈ starIm K H →
      phiL hLK ⟨a * m * a⁻¹, (Subgroup.mem_normalizer_iff.mp (hD.le_normalizer ha) m).mp m.2⟩ ∈
        starIm K H := fun a ha m hm =>
    phiL_conj_mem_starIm hLK (hAH a ha) (hAK a ha) (hD.le_normalizer ha) hm
  rcases (item131_seven_of_mem h131 hspor hD hcL).1 with hSL | ⟨hHeis, -⟩
  · exact false_of_isSLThreePiTwo hD hSL hLK hKL hθ hn ψ hpar hAP
  · exact false_of_isHeisCentral hD hHeis hLK hKL hθ ψ hpar hAP

theorem step1911End_of_wide3
    (h194 : Item194UsedWide3) (h131 : Item131) : Step1911End :=
  step1911End_of_spor_wide3 h194 h131 Sec13.sporadicModels131

end CFSG.RankThree.PartTwo.Sec19
