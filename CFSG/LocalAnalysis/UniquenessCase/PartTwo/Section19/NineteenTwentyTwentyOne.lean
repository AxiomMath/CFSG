module

public import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Even.Arithmetic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.GapsNineteenTwenty
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwentyForce
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.BarOfInterTransfer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFactsNineteenTwenty
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwentyFive72
public import CFSG.GroupTheory.ConjActionModPCore
public import CFSG.GroupTheory.ConjQuot
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Kernel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case2Ord
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKOmegaPlusSix
public import CFSG.Quasithin.Vol2.Ch11SecA11Ord
public import CFSG.Quasithin.H13.VolIA38Orders
public import CFSG.GroupTheory.PCoreSurjective
public import CFSG.LocalAnalysis.AGLEmbedding.SUPairModel
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThirteenSolvOf

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open CFSG.Blueprint Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.GroupTheory
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem l2_card_not_mem_jzeroShape {n : ℕ} (hn : 1 ≤ n) (hn2 : n ≠ 2) :
    2 ^ n * ((2 ^ n) ^ 2 - 1) ∉ ({3, 60, 360, 20160, 1451520} : Finset ℕ) := by
  intro hmem
  have hle : 2 ^ n * ((2 ^ n) ^ 2 - 1) ≤ 1451520 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h | h <;> omega
  have hbound : n ≤ 6 := by
    by_contra hn7
    have h7 : 7 ≤ n := by omega
    have hmono : 2 ^ 7 * ((2 ^ 7) ^ 2 - 1) ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
      refine Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) h7) ?_
      exact Nat.sub_le_sub_right (Nat.pow_le_pow_left
        (Nat.pow_le_pow_right (by norm_num) h7) 2) 1
    norm_num at hmono
    omega
  interval_cases n
  · norm_num at hmem
  · exact (hn2 rfl).elim
  · norm_num at hmem
  · norm_num at hmem
  · norm_num at hmem
  · norm_num at hmem

theorem conjModPCore_map_barOfInter {D : Data G} {V₀ V : Subgroup G} {p : ℕ}
    {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ} {Y N Dsub H S : Subgroup G}
    (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S)
    (h17 : A ≤ normalizer (Dsub : Set G)) {a : G} (ha : a ∈ A) :
    (barOfInter D.M Dsub).map (conjModPCore 2 Dsub A h17 ⟨a, ha⟩).toMonoidHom =
      barOfInter D.M Dsub := by
  have haD : a ∈ normalizer (Dsub : Set G) := h17 ha
  have haV : a ∈ normalizer ((Dsub ⊓ D.M : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hD : Dsub.map (MulAut.conj a).toMonoidHom = Dsub :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (h17 ha)
    have hM : D.M.map (MulAut.conj a).toMonoidHom = D.M :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (Subgroup.le_normalizer (A_le_M_of_ctx19_10 (D := D) h.ctx ha))
    have hD' : Dsub.map (↑(MulAut.conj a)) = Dsub := hD
    have hM' : D.M.map (↑(MulAut.conj a)) = D.M := hM
    rw [Subgroup.map_inf _ _ _ (MulAut.conj a).injective, hD', hM']
  have hcomp : (conjModPCore 2 Dsub A h17 ⟨a, ha⟩).toMonoidHom.comp
      (QuotientGroup.mk' (CFSG.pCore 2 ↥Dsub)) =
      (QuotientGroup.mk' (CFSG.pCore 2 ↥Dsub)).comp
        (Dsub.normalizerMonoidHom ⟨a, haD⟩ : ↥Dsub →* ↥Dsub) := by
    ext x
    change (conjModPCore 2 Dsub A h17 ⟨a, ha⟩) (QuotientGroup.mk x) =
      (QuotientGroup.mk' (CFSG.pCore 2 ↥Dsub))
        ((Dsub.normalizerMonoidHom ⟨a, haD⟩ : ↥Dsub →* ↥Dsub) x)
    rw [conjModPCore_mk]
    rfl
  rw [barOfInter, Subgroup.map_map, hcomp, ← Subgroup.map_map,
    map_subgroupOf_normalizerMonoidHom_eq haD haV]

theorem false_of_A7_or_L32 (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} {Y N Dsub H S : Subgroup G}
    (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S)
    (h17 : R19_17At D V₀ V p L A t B r Y N Dsub H S h)
    (h12 : R19_12At D V₀ V p L A t B r h.ctx)
    (hodd : K_19_20_oddAut) (h20b : Gap19_20b D)
    (hshape : (CFSG.Blueprint.LieModel (Bar2 Dsub) .PSL 3 2 1 ∧
        IsNontrivialParabolic (Bar2 Dsub) (barOfInter D.M Dsub)) ∨
      (IsAlt (Bar2 Dsub) 7 ∧ (barOfInter D.M Dsub).index = 35)) : False := by
  classical
  have h17' : A ≤ normalizer (Dsub : Set G) := h17
  have hAodd : Odd (Nat.card A) := odd_card_of_ctx19_10 h.ctx
  have hEnonempty : ∃ E : Subgroup G, E ≤ A ∧ E ≠ ⊥ ∧ ¬ 3 ∣ Nat.card E ∧
      normalizer (E : Set G) ≤ D.M := by
    by_cases hEven : Even (S17.nOf L)
    · exact h20b V₀ V p L A t B r h.ctx hEven
    · have hOdd : Odd (S17.nOf L) := Nat.not_even_iff_odd.mp hEven
      obtain ⟨E, hEA, hEel, hEcard⟩ :=
        exists_isElemAbelian_card_prime_sq_of_isZModSq h.ctx.hAcard h.ctx.hr.1 h.ctx.hr.2
      have hrne3 : r ≠ 3 := by
        rintro rfl
        have h3sq : 3 ∣ (2 ^ S17.nOf L - 1) ^ 2 := by
          simpa [pow_two, card_eq_of_isZModSq h.ctx.hAcard] using h.ctx.hr.2
        exact CFSG.SignalizerFunctorTheorem.McBride.PSL2Even.not_three_dvd_pow_sub_one hOdd
          (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3sq)
      have hE3 : ¬ 3 ∣ Nat.card E := by
        intro h3E
        rw [hEcard] at h3E
        have hsq : 3 ∣ r ^ 2 := by simpa [pow_two] using h3E
        have h3r : 3 ∣ r := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hsq
        exact hrne3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three h.ctx.hr.1).mp h3r).symm
      have hEne : E ≠ ⊥ := by
        intro hbot
        have h1 : Nat.card E = 1 := by rw [hbot, Subgroup.card_bot]
        rw [hEcard] at h1
        have hr2 : 2 ≤ r := h.ctx.hr.1.two_le
        have h4 : 2 ^ 2 ≤ r ^ 2 := Nat.pow_le_pow_left hr2 2
        norm_num at h4
        omega
      refine ⟨E, hEA, hEne, hE3, ?_⟩
      exact CFSG.LocalAnalysis.RankThreeUC.normalizer_le_of_mem_uniqueSet D.maxLocal
        (h12 E hEA hEel hEcard)
  obtain ⟨E, hEA, hEne, hE3, hNEM⟩ := hEnonempty
  have hEodd : Odd (Nat.card E) :=
    Odd.of_dvd_nat hAodd (Subgroup.card_dvd_of_le hEA)
  let f : ↥E →* MulAut (Bar2 Dsub) :=
    (conjModPCore 2 Dsub A h17').comp (Subgroup.inclusion hEA)
  have hEalpha : ∀ e : ↥E, f e = 1 := by
    intro e
    have hαodd : Odd (orderOf (f e)) :=
      Odd.of_dvd_nat hEodd ((orderOf_map_dvd f e).trans (orderOf_dvd_natCard e))
    have hα3 : (f e) ^ 3 = 1 :=
      hodd (Bar2 Dsub) (barOfInter D.M Dsub) hshape (f e) hαodd
        (conjModPCore_map_barOfInter h h17' (hEA e.2))
    have hdvd3 : orderOf (f e) ∣ 3 := orderOf_dvd_of_pow_eq_one hα3
    have hdvdE : orderOf (f e) ∣ Nat.card E :=
      (orderOf_map_dvd f e).trans (orderOf_dvd_natCard e)
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with h1 | h3
    · exact orderOf_eq_one_iff.mp h1
    · exact absurd (h3 ▸ hdvdE) hE3
  have hEN : E ≤ normalizer (Dsub : Set G) := hEA.trans h17'
  have hcom : ∀ (e : ↥E) (x : ↥Dsub),
      (e : G) * (x : G) * (e : G)⁻¹ * (x : G)⁻¹ ∈ pCoreOf 2 Dsub := by
    intro e x
    have hmemD : (e : G) * (x : G) * (e : G)⁻¹ ∈ Dsub :=
      (Subgroup.mem_normalizer_iff.mp (hEN e.2) (x : G)).mp x.2
    have h2 : f e (QuotientGroup.mk x) = QuotientGroup.mk x := by
      rw [hEalpha e, MulAut.one_apply]
    have h3 : conjModPCore 2 Dsub A h17' ⟨(e : G), hEA e.2⟩ (QuotientGroup.mk x) =
        QuotientGroup.mk x := h2
    rw [conjModPCore_mk] at h3
    have h4 : ((⟨(e : G) * (x : G) * (e : G)⁻¹, hmemD⟩ : ↥Dsub) / x) ∈
        CFSG.pCore 2 ↥Dsub := QuotientGroup.eq_iff_div_mem.mp h3
    have h5 : (((⟨(e : G) * (x : G) * (e : G)⁻¹, hmemD⟩ : ↥Dsub) / x : ↥Dsub) : G) ∈
        pCoreOf 2 Dsub := (CFSG.mem_openPCoreOf_iff _).mpr h4
    simpa [div_eq_mul_inv, mul_assoc] using h5
  have hEpcore : E ≤ normalizer (pCoreOf 2 Dsub : Set G) :=
    hEN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Dsub)
  set N : Subgroup ↥Dsub := CFSG.pCore 2 ↥Dsub with hN
  have : N.Normal := CFSG.pCore_normal
  have : Subgroup.Normalizes E Dsub := ⟨hEN⟩
  let : MulDistribMulAction ↥E ↥Dsub :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer E Dsub hEN
  have hinv : CFSG.IsInvariant ↥E ↥Dsub N := by
    refine ⟨fun e y => ?_⟩
    have hiffG := Subgroup.mem_normalizer_iff.mp (hEpcore e.2) (y : G)
    have hsm : ((e • y : ↥Dsub) : G) = (e : G) * (y : G) * (e : G)⁻¹ :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe (A := E) (K := Dsub) e y
    have h1 : (y : ↥Dsub) ∈ N ↔ (y : G) ∈ pCoreOf 2 Dsub :=
      (CFSG.mem_openPCoreOf_iff y).symm
    have h2 : e • y ∈ N ↔ ((e • y : ↥Dsub) : G) ∈ pCoreOf 2 Dsub :=
      (CFSG.mem_openPCoreOf_iff (e • y)).symm
    rw [h2, h1, hsm]
    exact hiffG
  have hNsolv : Group.IsSolvable ↥N := by
    have := (CFSG.pCore_isPGroup (p := 2) (G := ↥Dsub)).isNilpotent
    infer_instance
  have hcop : Nat.Coprime (Nat.card ↥E) (Nat.card ↥N) := by
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥Dsub)).exists_card_eq
    rw [hk]
    exact hEodd.coprime_two_right.pow_right k
  let : MulAction.QuotientAction ↥E N := CFSG.quotientAction_of_isInvariant (A := ↥E) N hinv
  let : MulDistribMulAction ↥E (↥Dsub ⧸ N) :=
    CFSG.quotientMulDistribMulAction (A := ↥E) (G := ↥Dsub) N hinv
  have hfix : CFSG.fixedPointSubgroup ↥E (↥Dsub ⧸ N) = ⊤ := by
    rw [eq_top_iff]
    intro q _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    intro e
    rw [MulAction.Quotient.smul_coe (H := N) e x]
    rw [QuotientGroup.eq_iff_div_mem]
    have hxsm : ((e • x : ↥Dsub) : G) = (e : G) * (x : G) * (e : G)⁻¹ :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe (A := E) (K := Dsub) e x
    have hmem : (((e • x : ↥Dsub) / x : ↥Dsub) : G) ∈ pCoreOf 2 Dsub := by
      have hval : (((e • x : ↥Dsub) / x : ↥Dsub) : G) =
          (e : G) * (x : G) * (e : G)⁻¹ * (x : G)⁻¹ := by
        rw [div_eq_mul_inv]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hxsm, mul_assoc]
      rw [hval]
      exact hcom e x
    rw [← CFSG.mem_openPCoreOf_iff]
    exact hmem
  have hlift := CFSG.SolvableHall.coprime_solvable_kernel_fixed_point_lifting
    (A := ↥E) (G := ↥Dsub) N hinv hNsolv hcop
  have htop : (CFSG.fixedPointSubgroup ↥E ↥Dsub).map (QuotientGroup.mk' N) = ⊤ := by
    rw [hfix] at hlift
    exact hlift.symm
  have hDsub_le : Dsub ≤ (CFSG.fixedPointSubgroup ↥E ↥Dsub).map Dsub.subtype ⊔
      pCoreOf 2 Dsub := by
    intro x hx
    have hx' : QuotientGroup.mk' N (⟨x, hx⟩ : ↥Dsub) ∈
        (CFSG.fixedPointSubgroup ↥E ↥Dsub).map (QuotientGroup.mk' N) := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨c, hc, hcx⟩ := Subgroup.mem_map.mp hx'
    have hcx' : c⁻¹ * (⟨x, hx⟩ : ↥Dsub) ∈ N := QuotientGroup.eq.mp hcx
    have hxeq : (⟨x, hx⟩ : ↥Dsub) = c * (c⁻¹ * (⟨x, hx⟩ : ↥Dsub)) := by group
    have hxval : x = (c : G) * ((c⁻¹ * (⟨x, hx⟩ : ↥Dsub) : ↥Dsub) : G) :=
      congrArg Subtype.val hxeq
    have hcG : (c : G) ∈ (CFSG.fixedPointSubgroup ↥E ↥Dsub).map Dsub.subtype :=
      Subgroup.mem_map_of_mem _ hc
    have hxG : ((c⁻¹ * (⟨x, hx⟩ : ↥Dsub) : ↥Dsub) : G) ∈ pCoreOf 2 Dsub :=
      (CFSG.mem_openPCoreOf_iff _).mpr hcx'
    rw [hxval]
    exact Subgroup.mul_mem_sup hcG hxG
  have hCM : (CFSG.fixedPointSubgroup ↥E ↥Dsub).map Dsub.subtype ≤ D.M := by
    intro c hc
    obtain ⟨c0, hc0, rfl⟩ := Subgroup.mem_map.mp hc
    have hcent : (c0 : G) ∈ centralizer (E : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      have hfixe : (⟨e, he⟩ : ↥E) • c0 = c0 := hc0 ⟨e, he⟩
      have hsm : ((⟨e, he⟩ : ↥E) • c0 : ↥Dsub) = c0 := hfixe
      have hamb : (e : G) * (c0 : G) * (e : G)⁻¹ = (c0 : G) := by
        have := congrArg Subtype.val hsm
        simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using this
      calc e * (c0 : G) = (e * (c0 : G) * (e : G)⁻¹) * e := by group
        _ = (c0 : G) * e := by rw [hamb]
    exact hNEM (Subgroup.centralizer_le_normalizer (E : Set G) hcent)
  exact h.hD.2 (hDsub_le.trans (sup_le hCM h.hO2))

theorem nonempty_bar2_jzero_equiv (M L : Subgroup G) :
    Nonempty (Bar2 (S17.oUpperTwo (Opp 2 (L ⊓ M))) ≃*
      Bar2 (S17.oUpperTwo (Opp 2 (barOfInter M L)))) := by
  classical
  have hOppL : Opp 2 (L ⊓ M) ≤ L := by
    rw [Opp, CFSG.RankThree.PartOne.pElementSubgroup, Subgroup.closure_le]
    rintro x ⟨hx, -⟩
    exact hx.1
  set L₀ : Subgroup G := S17.oUpperTwo (Opp 2 (L ⊓ M)) with hL₀
  set S₁ : Subgroup (Bar2 L) := S17.oUpperTwo (Opp 2 (barOfInter M L)) with hS₁
  have hL₀L : L₀ ≤ L := (S17.oUpperTwo_le _).trans hOppL
  have hsub : (pCoreOf 2 L).subgroupOf L = CFSG.pCore 2 ↥L := by
    rw [pCoreOf, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective L.subtype_injective]
  have himg : (L₀.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) = S₁ := by
    have h1 : ((CFSG.ComponentClassification.AS76b.oUpperTwo
          ((Opp 2 (L ⊓ M)).subgroupOf L)).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) =
        CFSG.ComponentClassification.AS76b.oUpperTwo (Opp 2 (barOfInter M L)) := by
      rw [CFSG.AGLEmbedding.SUPair.map_oUpperTwo, map_opp_inter_eq_opp_barOfInter M L]
    have h2 : CFSG.ComponentClassification.AS76b.oUpperTwo ((Opp 2 (L ⊓ M)).subgroupOf L) =
        (CFSG.ComponentClassification.AS76b.oUpperTwo (Opp 2 (L ⊓ M))).subgroupOf L :=
      (CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.SolvThree.oUpperTwo_subgroupOf
        hOppL).symm
    rw [h2] at h1
    rw [hL₀, hS₁]
    simpa only [S17.oUpperTwo] using h1
  have hrange : ∀ x : ↥L₀,
      QuotientGroup.mk' (CFSG.pCore 2 ↥L) (Subgroup.inclusion hL₀L x) ∈ S₁ := by
    intro x
    have hx : QuotientGroup.mk' (CFSG.pCore 2 ↥L) (Subgroup.inclusion hL₀L x) ∈
        (L₀.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr x.2)
    rwa [himg] at hx
  set g : ↥L₀ →* ↥S₁ :=
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (Subgroup.inclusion hL₀L)).codRestrict
      S₁ hrange with hg
  have hgsurj : Function.Surjective g := by
    intro y
    have hy : (y : Bar2 L) ∈ (L₀.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
      rw [himg]
      exact y.2
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    refine ⟨⟨x.1, Subgroup.mem_subgroupOf.mp hx⟩, ?_⟩
    apply Subtype.ext
    show QuotientGroup.mk' (CFSG.pCore 2 ↥L)
      (Subgroup.inclusion hL₀L ⟨x.1, Subgroup.mem_subgroupOf.mp hx⟩) = (y : Bar2 L)
    rw [← hxy]
    rfl
  have hkerle : g.ker ≤ (pCoreOf 2 L).comap L₀.subtype := by
    intro x hx
    have hx1 : g x = 1 := by simpa using hx
    have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥L) (Subgroup.inclusion hL₀L x) = 1 := by
      simpa [g] using congrArg Subtype.val hx1
    have h3 : Subgroup.inclusion hL₀L x ∈ CFSG.pCore 2 ↥L := by
      rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥L), MonoidHom.mem_ker]
      exact h2
    rw [← hsub] at h3
    exact Subgroup.mem_subgroupOf.mp h3
  have hker : IsPGroup 2 g.ker :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).comap_subtype.to_le hkerle
  exact CFSG.nonempty_quotient_pCore_equiv_of_surjective_of_isPGroup_ker g hgsurj hker

theorem p19_19_false (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} {Y N Dsub H S : Subgroup G}
    (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S)
    (hshape : Shape19_16_124 (Bar2 Dsub) (barOfInter D.M Dsub))
    (hJ0shape : K_19_20_J0shape)
    (h17 : R19_17At D V₀ V p L A t B r Y N Dsub H S h)
    (h123 : 3 ∈ piSet A → Concl19_12 D A 3) (h13 : Concl19_13 D A)
    (hforce : K_19_20_force)
    (hJ0 : P19_19 D p L A Dsub (S17.oUpperTwo (Opp 2 (Dsub ⊓ D.M))))
    (hne168 : Nat.card (Bar2 Dsub) ≠ 168) : False := by
  rcases hJ0 with h191 | h192
  · obtain ⟨-, -, -, hL2, -⟩ := h191
    have hn3 := three_le_nOf_of_setting1910 h.ctx.h1910
    have hn1 : 1 ≤ S17.nOf L := by omega
    have hn2 : S17.nOf L ≠ 2 := by omega
    have hcard : Nat.card (Bar2 (S17.oUpperTwo (Opp 2 (Dsub ⊓ D.M)))) =
        2 ^ S17.nOf L * ((2 ^ S17.nOf L) ^ 2 - 1) := by
      have hc := LieModel.card_eq_lieOrd
        (X := Bar2 (S17.oUpperTwo (Opp 2 (Dsub ⊓ D.M)))) (t := .PSL) (n := 2)
        (p := 2) (f := S17.nOf L) (by norm_num) hL2
      rw [hc]
      have hq : CFSG.EvenSmallLie.CatalogOrders.lieOrd .PSL 2 (2 ^ S17.nOf L) =
          CFSG.Open.ordA 1 (2 ^ S17.nOf L) := rfl
      rw [hq, CFSG.Quasithin.H13.VolI.ordA_one_two_pow hn1]
    have hmem0 := hJ0shape (Bar2 Dsub) (barOfInter D.M Dsub) hshape
    obtain ⟨e⟩ := nonempty_bar2_jzero_equiv D.M Dsub
    have hmem1 : Nat.card (Bar2 (S17.oUpperTwo (Opp 2 (Dsub ⊓ D.M)))) ∈
        ({3, 60, 360, 20160, 1451520} : Finset ℕ) := by
      rw [Nat.card_congr e.toEquiv]
      exact hmem0
    refine l2_card_not_mem_jzeroShape hn1 hn2 ?_
    rw [← hcard]
    exact hmem1
  · obtain ⟨hle, hn⟩ := jzero_le_and_normal D.M Dsub
    exact hne168 (card_eq_of_isL3 (bar2_isL3_of_subset_mul D h h17 h123 h13 hforce
      (Or.inl hshape) hle hn h192.1 h192.2.1))

theorem card_neq_of_p19_16_4 (D : Data G) {Dsub : Subgroup G} (h4 : P19_16_4 D Dsub) :
    Nat.card (Bar2 Dsub) ≠ 168 ∧ Nat.card (Bar2 Dsub) ≠ 2520 := by
  obtain ⟨m, hm, hdata⟩ := h4
  rcases hm with rfl | rfl
  · rcases hdata with ⟨ε, hΩ, -⟩ | ⟨hAlt, -⟩
    · cases ε
      · have hΩ' : IsOmegaMinus (Bar2 Dsub) 6 1 := by simpa [IsOmegaEps2] using hΩ
        have hc := s16c1_card_isOmegaMinus_six hΩ'
        constructor <;> rw [hc] <;> norm_num
      · have hΩ' : IsOmegaPlus (Bar2 Dsub) 6 1 := by simpa [IsOmegaEps2] using hΩ
        have hA8 := s15k_omp6_isAlt8 hΩ'
        have hc := CFSG.Quasithin.Vol2.Ch11.SecA.card_of_isAlt (k := 8) (by norm_num) hA8
        norm_num at hc
        constructor <;> rw [hc] <;> norm_num
    · have hA8 : IsAlt (Bar2 Dsub) 8 := by simpa using hAlt
      have hc := CFSG.Quasithin.Vol2.Ch11.SecA.card_of_isAlt (k := 8) (by norm_num) hA8
      norm_num at hc
      constructor <;> rw [hc] <;> norm_num
  · rcases hdata with ⟨ε, hΩ, -⟩ | ⟨hAlt, -⟩
    · cases ε
      · have hΩ' : IsOmegaMinus (Bar2 Dsub) 8 1 := by simpa [IsOmegaEps2] using hΩ
        have hc := s16c1610_card_of_isOmegaMinus_eight hΩ'
        constructor <;> rw [hc] <;> norm_num
      · have hΩ' : IsOmegaPlus (Bar2 Dsub) 8 1 := by simpa [IsOmegaEps2] using hΩ
        have hlm : LieModel (Bar2 Dsub) .POmegaPlus 4 2 1 := by
          refine Or.inl ⟨by decide, ?_⟩
          refine ⟨⟨Nat.prime_two, by norm_num, by norm_num⟩, ?_⟩
          obtain ⟨-, K, hKf, hKi, hK, ⟨e⟩⟩ := hΩ'
          exact ⟨K, hKf, hKi, hK, ⟨e⟩⟩
        have hc := LieModel.card_eq_lieOrd (X := Bar2 Dsub) (t := .POmegaPlus) (n := 4)
          (p := 2) (f := 1) (by norm_num) hlm
        have hval : CFSG.EvenSmallLie.CatalogOrders.lieOrd .POmegaPlus 4 (2 ^ 1) =
            174182400 := by decide
        rw [hval] at hc
        constructor <;> rw [hc] <;> norm_num
    · have hA10 : IsAlt (Bar2 Dsub) 10 := by simpa using hAlt
      have hc := CFSG.Quasithin.Vol2.Ch11.SecA.card_of_isAlt (k := 10) (by norm_num) hA10
      norm_num at hc
      constructor <;> rw [hc] <;> norm_num

theorem nineteen_twenty_one (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} {Y N Dsub H S : Subgroup G}
    (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S)
    (h16 : R19_16At D V₀ V p L A t B r Y N Dsub H S h)
    (h17 : R19_17At D V₀ V p L A t B r Y N Dsub H S h)
    (h18 : R19_18At D V₀ V p L A t B r Y N Dsub H S h)
    (h19 : R19_19At D V₀ V p L A t B r Y N Dsub H S h)
    (h12 : R19_12At D V₀ V p L A t B r h.ctx)
    (h123 : 3 ∈ piSet A → Concl19_12 D A 3) (h13 : Concl19_13 D A)
    (hodd : K_19_20_oddAut) (hJ0 : K_19_20_J0shape) (hforce : K_19_20_force)
    (h20b : Gap19_20b D) :
    R19_20_1At D V₀ V p L A t B r Y N Dsub H S h := by
  change P19_16_5 D Dsub
  rcases (show P19_16 D Dsub from h16) with h1 | h2 | h3 | h4 | h5
  · exfalso
    have hshape : Shape19_16_124 (Bar2 Dsub) (barOfInter D.M Dsub) := Or.inl ⟨h1.1, h1.2⟩
    have hJ0le : S17.oUpperTwo (Opp 2 (Dsub ⊓ D.M)) ≤ IOf D p L := h18.1 (Or.inl h1)
    have hcard : Nat.card (Bar2 Dsub) = 1814400 := by
      have hc := CFSG.Quasithin.Vol2.Ch11.SecA.card_of_isAlt (k := 10) (by norm_num) h1.1
      norm_num at hc
      exact hc
    exact p19_19_false D h hshape hJ0 h17 h123 h13 hforce (h19.1 (Or.inl h1) hJ0le)
      (by rw [hcard]; norm_num)
  · exfalso
    have hidx : (barOfInter D.M Dsub).index = 15 := by
      rw [index_barOfInter (M := D.M) (L := Dsub) h.hO2]
      exact h2.2
    have hshape : Shape19_16_124 (Bar2 Dsub) (barOfInter D.M Dsub) :=
      Or.inr (Or.inl ⟨h2.1, hidx⟩)
    have hJ0le : S17.oUpperTwo (Opp 2 (Dsub ⊓ D.M)) ≤ IOf D p L := h18.1 (Or.inr (Or.inl h2))
    have hcard : Nat.card (Bar2 Dsub) = 1080 := by
      obtain ⟨hcover, hZcard⟩ := h2.1
      have hcardq : Nat.card (Bar2 Dsub ⧸ Subgroup.center (Bar2 Dsub)) = 360 := by
        have hc := CFSG.Quasithin.Vol2.Ch11.SecA.card_of_isAlt (k := 6)
          (by norm_num) hcover.2
        norm_num at hc
        exact hc
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center (Bar2 Dsub)),
        hcardq, hZcard]
    exact p19_19_false D h hshape hJ0 h17 h123 h13 hforce
      (h19.1 (Or.inr (Or.inl h2)) hJ0le) (by rw [hcard]; norm_num)
  · exact (false_of_A7_or_L32 D h h17 h12 hodd h20b
      (Or.inr ⟨h3.1, by rw [index_barOfInter (M := D.M) (L := Dsub) h.hO2]; exact h3.2⟩)).elim
  · exfalso
    have hshape : Shape19_16_124 (Bar2 Dsub) (barOfInter D.M Dsub) := Or.inr (Or.inr h4)
    have hJ0le : S17.oUpperTwo (Opp 2 (Dsub ⊓ D.M)) ≤ IOf D p L :=
      h18.1 (Or.inr (Or.inr (Or.inr h4)))
    exact p19_19_false D h hshape hJ0 h17 h123 h13 hforce
      (h19.1 (Or.inr (Or.inr (Or.inr h4))) hJ0le) (card_neq_of_p19_16_4 D h4).1
  · exact h5

theorem nineteen_twenty_two (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} {Y N Dsub H S : Subgroup G}
    (h : Ctx19_14 D V₀ V p L A t B r Y N Dsub H S)
    (h17 : R19_17At D V₀ V p L A t B r Y N Dsub H S h)
    (h19 : R19_19At D V₀ V p L A t B r Y N Dsub H S h)
    (h201 : R19_20_1At D V₀ V p L A t B r Y N Dsub H S h)
    (h12 : R19_12At D V₀ V p L A t B r h.ctx)
    (h123 : 3 ∈ piSet A → Concl19_12 D A 3) (h13 : Concl19_13 D A)
    (hodd : K_19_20_oddAut) (hforce : K_19_20_force) (h20b : Gap19_20b D) :
    R19_20_2At D V₀ V p L A t B r Y N Dsub H S h := by
  intro d K J hfam i hJi
  have h201' : P19_16_5 D Dsub := h201
  rcases h19.2 h201' d K J hfam i hJi with h191 | h192
  · exact h191
  · exfalso
    obtain ⟨hle, hn⟩ := dynkin_J_le_and_normal hfam i
    have hL3 : LieModel (Bar2 Dsub) .PSL 3 2 1 := by
      rcases h192.2.2 with hLie | h1 | h2 | h3
      · exact bar2_isL3_of_subset_mul D h h17 h123 h13 hforce
          (Or.inr ⟨hLie, h201'.1, h201'.2⟩) hle hn h192.1 h192.2.1
      · exact bar2_isL3_of_subset_mul D h h17 h123 h13 hforce
          (Or.inl (Or.inl ⟨h1.1, h1.2⟩)) hle hn h192.1 h192.2.1
      · have hidx : (barOfInter D.M Dsub).index = 15 := by
          rw [index_barOfInter (M := D.M) (L := Dsub) h.hO2]
          exact h2.2
        exact bar2_isL3_of_subset_mul D h h17 h123 h13 hforce
          (Or.inl (Or.inr (Or.inl ⟨h2.1, hidx⟩))) hle hn h192.1 h192.2.1
      · exact (false_of_A7_or_L32 D h h17 h12 hodd h20b (Or.inr ⟨h3.1, by
          rw [index_barOfInter (M := D.M) (L := Dsub) h.hO2]
          exact h3.2⟩)).elim
    exact false_of_A7_or_L32 D h h17 h12 hodd h20b (Or.inl ⟨hL3, h201'.2⟩)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
