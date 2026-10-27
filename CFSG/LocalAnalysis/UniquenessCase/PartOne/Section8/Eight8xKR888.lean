module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight8xKPorts2
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight8xKPorts887
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65X0CardTypes
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65Z0
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.CommutatorCentre
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.InnerBarDecompOut
import CFSG.LocalAnalysis.UniquenessCase.UC22P21d
import CFSG.LocalAnalysis.SteinbergBQInvolutionHullStructure
import CFSG.GroupTheory.IsCyclicOfLeOfPRankLeOne
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.OuterJ2
import CFSG.Quasithin.Background.SmithB45HatA6Out
import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data Bar2 IsSpor pRank_bar2_eq_of_odd)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08 (R869)
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (SigmaStd sp_of_mem_sig not_solvable_of_mem_calC)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped commutatorElement

private structure r888s_Ctx {G : Type} [Group G] [Finite G] (D : Data G) (L P : Subgroup G) :
    Prop where
  hset : Set880 D L P
  hSg : SigmaStd D
  h869 : R869 D
  h882 : R882 D
  h885 : R885 D
  h886 : R886 D
  h887 : R887 D
  hIns : List880PRankInspection
  hJ2 : J2FivePRank

private theorem r888s_ZOf_le {G : Type} [Group G] (Q : Subgroup G) : ZOf Q ≤ Q :=
  inf_le_left

private theorem r888s_ZOf_le_P {G : Type} [Group G] {P Q : Subgroup G} (hQ : Q ≤ P) :
    ZOf Q ≤ P :=
  (r888s_ZOf_le Q).trans hQ

private theorem r888s_J2 {G : Type} [Group G] [Finite G] {D : Data G} {L P : Subgroup G}
    (ctx : r888s_Ctx D L P) : IsSpor (Bar2 L) .J2 :=
  (ctx.h885 L P ctx.hset).1

private theorem r888s_sig {G : Type} [Group G] [Finite G] {D : Data G} {L P : Subgroup G}
    (ctx : r888s_Ctx D L P) : D.sig = {5} :=
  (ctx.h885 L P ctx.hset).2.1

private theorem r888s_pRank5L {G : Type} [Group G] [Finite G] {D : Data G} {L P : Subgroup G}
    (ctx : r888s_Ctx D L P) : CFSG.Open.pRank 5 L = 2 := by
  rw [← pRank_bar2_eq_of_odd (Y := L) Nat.prime_five (by norm_num)]
  exact (ctx.hJ2 (Bar2 L) (r888s_J2 ctx)).1

private theorem r888s_norm {G : Type} [Group G] [Finite G] {D : Data G} {L P : Subgroup G}
    (ctx : r888s_Ctx D L P) : D.M ≤ normalizer (L : Set G) :=
  normalizer_of_set880_of_two_le_pRank D ctx.h882 ctx.hIns ctx.hset Nat.prime_five (by norm_num)
    (by rw [r888s_pRank5L ctx])

private theorem r888s_le {G : Type} [Group G] [Finite G] {D : Data G} {L P : Subgroup G}
    (ctx : r888s_Ctx D L P) : L ≤ D.M :=
  CFSG.Quasithin.A3.subnormal_le ctx.hset.mem.1

private theorem r888s_sylowQ {G : Type} [Group G] [Finite G] {D : Data G} {L P : Subgroup G}
    (ctx : r888s_Ctx D L P) : IsSylowOf 3 (P ⊓ L) L :=
  ctx.hset.sylow.inf_of_le_normalizer (r888s_le ctx) (r888s_norm ctx)

private theorem r888s_SPE5 {G : Type} [Group G] [Finite G] {D : Data G} {L P : Subgroup G}
    (ctx : r888s_Ctx D L P) : IsStronglyPEmbedded 5 D.M :=
  sp_of_mem_sig ctx.hSg (not_solvable_of_mem_calC ctx.hset.mem)
    (by rw [r888s_sig ctx]; exact Set.mem_singleton 5)

private theorem r888s_rank3M {G : Type} [Group G] [Finite G] {D : Data G} {L P : Subgroup G}
    (ctx : r888s_Ctx D L P) : CFSG.Open.pRank 3 D.M ≤ 3 := by
  by_contra h
  have h4 : 4 ≤ CFSG.Open.pRank 3 D.M := by omega
  have h3 : 3 ∈ D.sig := ctx.hSg.four_mem 3 Nat.prime_three (by norm_num) h4
  rw [r888s_sig ctx] at h3
  exact absurd (Set.mem_singleton_iff.mp h3) (by norm_num)

private theorem r888s_card_bar2 {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (h : IsSpor (Bar2 L) .J2) : Nat.card (Bar2 L) = 604800 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.Sporadic.J2.card_J2

private theorem r888s_fact3 {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (h : IsSpor (Bar2 L) .J2) : (Nat.card ↥L).factorization 3 = 3 := by
  let O : Subgroup ↥L := CFSG.pCore 2 ↥L
  have hπ : Function.Surjective (QuotientGroup.mk' O) := QuotientGroup.mk'_surjective O
  have hcardmul : Nat.card O * Nat.card (Bar2 L) = Nat.card ↥L := by
    have hh := Subgroup.card_ker_mul_card_of_surjective (f := QuotientGroup.mk' O) hπ
    simpa [O, Bar2, QuotientGroup.ker_mk'] using hh
  have hO2 : IsPGroup 2 O := CFSG.pCore_isPGroup
  obtain ⟨n, hn⟩ := hO2.exists_card_eq
  have h3O : ¬ 3 ∣ Nat.card O := by
    rw [hn]
    intro h3
    have h32 : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    norm_num at h32
  have hfacO : (Nat.card O).factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd h3O
  have hfacB : (Nat.card (Bar2 L)).factorization 3 = 3 := by
    rw [r888s_card_bar2 h]
    have hb3a : 3 ^ 3 ∣ (604800 : ℕ) := by norm_num
    have hb3b : ¬ 3 ^ 4 ∣ (604800 : ℕ) := by norm_num
    have hn0 : (604800 : ℕ) ≠ 0 := by norm_num
    have hle : 3 ≤ (604800 : ℕ).factorization 3 :=
      (Nat.prime_three.pow_dvd_iff_le_factorization (k := 3) hn0).mp hb3a
    have hlt : (604800 : ℕ).factorization 3 < 4 := by
      by_contra hge
      exact hb3b ((Nat.prime_three.pow_dvd_iff_le_factorization (k := 4) hn0).mpr (by omega))
    omega
  have hO0 : Nat.card O ≠ 0 := Nat.card_pos.ne'
  have hB0 : Nat.card (Bar2 L) ≠ 0 := Nat.card_pos.ne'
  rw [← hcardmul, Nat.factorization_mul hO0 hB0, Finsupp.add_apply, hfacO, hfacB, zero_add]

private theorem r888s_card_Q {G : Type} [Group G] [Finite G]
    {D : Data G} {L P : Subgroup G} (ctx : r888s_Ctx D L P) :
    Nat.card (P ⊓ L : Subgroup G) = 27 := by
  have h := IsSylowOf.card_eq (r888s_sylowQ ctx)
  rw [h, r888s_fact3 (r888s_J2 ctx)]
  norm_num

private theorem r888s_commutator_Q {G : Type} [Group G] [Finite G]
    {D : Data G} {L P : Subgroup G} (ctx : r888s_Ctx D L P) : ⁅P ⊓ L, P ⊓ L⁆ = ZOf (P ⊓ L) := by
  have h3 : Nat.card (P ⊓ L : Subgroup G) = 3 ^ 3 := by
    rw [r888s_card_Q ctx]; norm_num
  exact CFSG.AGLEmbeddingD2.Wilson.Proving.commutator_eq_inf_centralizer_of_card
    Nat.prime_three (P ⊓ L) h3 (ctx.h886 L P ctx.hset).1

private theorem r888pd_center_eq_bot_of_isSpor_J2
    {X : Type} [Group X] [Finite X] (hJ : IsSpor X .J2) : Subgroup.center X = ⊥ := by
  have hcard : Nat.card X = 604800 := by
    obtain ⟨e⟩ := hJ
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.J2.card_J2
  obtain ⟨e⟩ := hJ
  have : IsSimpleGroup X := @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.J2.isSimpleGroup_J2 e
  refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X)).resolve_right fun ht => ?_
  have hprime : (Nat.card X).Prime :=
    (@Group.is_simple_iff_prime_card X _ (Subgroup.center_eq_top_iff.1 ht)).1 inferInstance
  rw [hcard] at hprime
  norm_num at hprime

private theorem r888s_step_P_decomp
    {G : Type} [Group G] [Finite G] {D : Data G}
    {L P : Subgroup G} (ctx : r888s_Ctx D L P) :
    P ≤ (P ⊓ L) ⊔ centralizerBar P L ∧
      (∀ c ∈ centralizerBar P L, ∀ q ∈ (P ⊓ L : Subgroup G), c * q = q * c) ∧
      (P ⊓ L) ⊓ centralizerBar P L = ⊥ := by
  have hPNL : P ≤ Subgroup.normalizer (L : Set G) :=
    (ctx.hset.sylow.le).trans (r888s_norm ctx)
  have hP3 : IsPGroup 3 P := ctx.hset.sylow.isPGroup
  have hPN : P ≤ Subgroup.normalizer ((P ⊓ L : Subgroup G) : Set G) :=
    (le_inf P.le_normalizer hPNL).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hQnormP : ((P ⊓ L).subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hPN
  have hOut : ¬ 3 ∣ Nat.card
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer (Bar2 L)) :=
    not_three_dvd_card_outer_of_isSpor_J2 (r888s_J2 ctx)
  have hPC : P ≤ (P ⊓ L) ⊔ centralizerBar P L :=
    le_sup_centralizerBar_of_out (Q := P ⊓ L) hOut hP3 hPNL inf_le_left inf_le_right rfl
      hQnormP (r888s_sylowQ ctx)
  have hQO : (P ⊓ L) ⊓ CFSG.Open.pCoreOf 2 L = ⊥ := by
    have h1 : IsPGroup 3 ↥(P ⊓ L) := (r888s_sylowQ ctx).isPGroup
    have h2 : IsPGroup 2 ↥(CFSG.Open.pCoreOf 2 L) :=
      CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
    exact (IsPGroup.disjoint_of_ne 3 2 (by norm_num) (P ⊓ L)
      (CFSG.Open.pCoreOf 2 L) h1 h2).eq_bot
  have hQC : ⁅P ⊓ L, centralizerBar P L⁆ = ⊥ :=
    commutator_eq_bot_centralizerBar inf_le_right hQO hPN
  refine ⟨hPC, ?_, ?_⟩
  · intro c hc q hq
    have hmem : ⁅q, c⁆ ∈ ⁅P ⊓ L, centralizerBar P L⁆ :=
      Subgroup.commutator_mem_commutator hq hc
    rw [hQC, Subgroup.mem_bot] at hmem
    exact (commutatorElement_eq_one_iff_mul_comm.mp hmem).symm
  · exact inf_centralizerBar_eq_bot_of_ker inf_le_right hQO
      (inf_centralizerBar_le_pCore_of_center_bar2
        (r888pd_center_eq_bot_of_isSpor_J2 (r888s_J2 ctx)))

private theorem r888s_normalizer_conj {G : Type} [Group G] {Z : Subgroup G} (h : G) :
    Subgroup.normalizer ((Z.map (MulAut.conj h).toMonoidHom : Subgroup G) : Set G) ≤
      (Subgroup.normalizer (Z : Set G)).map (MulAut.conj h).toMonoidHom := by
  have hZh : (Z.map (MulAut.conj h).toMonoidHom).map (MulAut.conj h⁻¹).toMonoidHom = Z := by
    rw [Subgroup.map_map]
    have hc : (MulAut.conj h⁻¹).toMonoidHom.comp (MulAut.conj h).toMonoidHom =
        MonoidHom.id G := by
      ext z; simp [MulAut.conj_apply, mul_assoc]
    rw [hc, Subgroup.map_id]
  have h1 : (Subgroup.normalizer
        ((Z.map (MulAut.conj h).toMonoidHom : Subgroup G) : Set G)).map
        (MulAut.conj h⁻¹).toMonoidHom ≤ Subgroup.normalizer (Z : Set G) := by
    have h := Subgroup.le_normalizer_map (H := (Z.map (MulAut.conj h).toMonoidHom : Subgroup G))
      (MulAut.conj h⁻¹).toMonoidHom
    rwa [hZh] at h
  have h2 := Subgroup.map_mono (f := (MulAut.conj h).toMonoidHom) h1
  have hc : (MulAut.conj h).toMonoidHom.comp (MulAut.conj h⁻¹).toMonoidHom =
      MonoidHom.id G := by
    ext z; simp [MulAut.conj_apply, mul_assoc]
  rwa [Subgroup.map_map, hc, Subgroup.map_id] at h2

private theorem r888s_step_5prime {G : Type} [Group G] [Finite G] {D : Data G}
    {L P : Subgroup G} (ctx : r888s_Ctx D L P) :
    ∀ h : G, h ∉ D.M → ¬ 5 ∣ Nat.card ↥(D.M ⊓ centralizer
      (((ZOf (P ⊓ L)).map (MulAut.conj h).toMonoidHom : Subgroup G) : Set G)) := by
  intro h hh h5
  have hcent : Subgroup.centralizer
        (((ZOf (P ⊓ L)).map (MulAut.conj h).toMonoidHom : Subgroup G) : Set G) ≤
      D.M.map (MulAut.conj h).toMonoidHom :=
    (Subgroup.centralizer_le_normalizer _).trans
      ((r888s_normalizer_conj (Z := ZOf (P ⊓ L)) h).trans
        (Subgroup.map_mono (ctx.h887 L P ctx.hset)))
  have hle : D.M ⊓ Subgroup.centralizer
        (((ZOf (P ⊓ L)).map (MulAut.conj h).toMonoidHom : Subgroup G) : Set G) ≤
      D.M ⊓ D.M.map (MulAut.conj h).toMonoidHom :=
    inf_le_inf_left _ hcent
  exact (r888s_SPE5 ctx).2.2 h hh (h5.trans (Subgroup.card_dvd_of_le hle))

private theorem r888f5l_card_of_isA6Z3 {Y : Type} [Group Y]
    (h : CFSG.LocalAnalysis.UniquenessCase.UC22.F08.IsA6Z3 Y) : Nat.card Y = 1080 := by
  obtain ⟨-, hz, e⟩ := h
  have hq : Nat.card (Y ⧸ Subgroup.center Y) = 360 := by
    obtain ⟨e⟩ := e
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Alternating.Multipliers.nat_card_alternatingGroup_fin 4
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Y)
  rw [hq, hz] at hcard
  omega

private theorem r888f5l_exists_five_mem_inf_centralizer {G : Type} [Group G] [Finite G]
    {L Z : Subgroup G} (hZL : Z ≤ L) (hZ : IsPGroup 3 Z)
    (hA6 : CFSG.LocalAnalysis.UniquenessCase.UC22.F08.IsA6Z3
      ↥(centralizer ((((Z.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) :
        Subgroup (Bar2 L)) : Set (Bar2 L))))) :
    ∃ a : G, a ∈ L ⊓ centralizer (Z : Set G) ∧ orderOf a = 5 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h5 : 5 ∣ Nat.card ↥(centralizer ((((Z.subgroupOf L).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) : Subgroup (Bar2 L)) : Set (Bar2 L)))) := by
    rw [r888f5l_card_of_isA6Z3 hA6]
    norm_num
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 5 h5
  have hymem : (y : Bar2 L) ∈ ((L ⊓ centralizer (Z : Set G)).subgroupOf L).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
    rw [r887_map_centralizer_eq_centralizer_map hZL hZ]
    exact y.2
  obtain ⟨x, hx, hxy⟩ := hymem
  have hdvd : 5 ∣ orderOf x := by
    have h1 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥L) x) ∣ orderOf x := orderOf_map_dvd _ x
    have h2 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥L) x) = 5 := by
      rw [hxy, Subgroup.orderOf_coe, hy]
    rwa [h2] at h1
  have hx0 : orderOf x ≠ 0 := (orderOf_pos x).ne'
  refine ⟨((x ^ (orderOf x / 5) : ↥L) : G), ?_, ?_⟩
  · have hxG : (x : G) ∈ L ⊓ centralizer (Z : Set G) := Subgroup.mem_subgroupOf.mp hx
    exact (L ⊓ centralizer (Z : Set G)).pow_mem hxG _
  · rw [Subgroup.orderOf_coe]
    exact orderOf_pow_orderOf_div hx0 hdvd

private theorem r888s_step_five_L {G : Type} [Group G] [Finite G] {D : Data G}
    {L P : Subgroup G} (ctx : r888s_Ctx D L P) :
    ∃ f ∈ L, orderOf f = 5 ∧ ∀ z ∈ ZOf (P ⊓ L), ⁅z, f⁆ ∈ CFSG.Open.pCoreOf 2 L := by
  have hZL : ZOf (P ⊓ L) ≤ L := (r888s_ZOf_le (P ⊓ L)).trans inf_le_right
  have hZ : IsPGroup 3 (ZOf (P ⊓ L)) :=
    IsPGroup.of_card (n := 1) (by rw [(ctx.h886 L P ctx.hset).1]; norm_num)
  obtain ⟨f, hf, hf5⟩ := r888f5l_exists_five_mem_inf_centralizer hZL hZ
    (ctx.h886 L P ctx.hset).2.2.2
  refine ⟨f, (Subgroup.mem_inf.mp hf).1, hf5, ?_⟩
  intro z hz
  rw [Subgroup.mem_centralizer_iff_commutator_eq_one.mp (Subgroup.mem_inf.mp hf).2 z hz]
  exact (CFSG.Open.pCoreOf 2 L).one_mem

private theorem r888s_step_five_C
    {G : Type} [Group G] [Finite G] {D : Data G}
    {L P : Subgroup G} (ctx : r888s_Ctx D L P) :
    ∃ f ∈ centralizerBar D.M L, orderOf f = 5 := by
  obtain ⟨f, hf, -, hf5⟩ := r887_exists_five_centralizerBar_inf_centralizer (Z := ⊥)
    (r888s_le ctx) (r888s_norm ctx) bot_le IsPGroup.of_bot (r888s_J2 ctx)
    (ctx.hSg.three_le 5 (by rw [r888s_sig ctx]; exact Set.mem_singleton 5))
  exact ⟨f, hf, hf5⟩

private theorem r888s_step_K5 {G : Type} [Group G] [Finite G] {D : Data G}
    {L P : Subgroup G} (ctx : r888s_Ctx D L P) :
    ∀ W : Subgroup G, W ≤ D.M → IsPGroup 3 W → ∀ f ∈ D.M, orderOf f = 5 →
      (∀ w ∈ W, ⁅w, f⁆ ∈ CFSG.Open.pCoreOf 2 L) →
      5 ∣ Nat.card ↥(D.M ⊓ centralizer (W : Set G)) := by
  intro W hW hW3 f hfM hf5 hcommW
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hO : IsPGroup 2 (CFSG.Open.pCoreOf 2 L) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hMN : D.M ≤ normalizer (L : Set G) := r888s_norm ctx
  have hON : D.M ≤ normalizer (CFSG.Open.pCoreOf 2 L : Set G) := fun x hx =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) L (hMN hx)
  have hAM : Subgroup.zpowers f ≤ D.M := Subgroup.zpowers_le.2 hfM
  have hAO : Subgroup.zpowers f ≤ normalizer (CFSG.Open.pCoreOf 2 L : Set G) :=
    hAM.trans hON
  have hEO : W ≤ normalizer (CFSG.Open.pCoreOf 2 L : Set G) := hW.trans hON
  have hAcard : Nat.card (Subgroup.zpowers f) = 5 := by rw [Nat.card_zpowers, hf5]
  have hA : IsPGroup 5 (Subgroup.zpowers f) :=
    IsPGroup.of_card (n := 1) (by simpa using hAcard)
  have hcomm : ∀ e ∈ W, ∀ a ∈ Subgroup.zpowers f,
      e * a * e⁻¹ * a⁻¹ ∈ CFSG.Open.pCoreOf 2 L := by
    intro e he a ha
    have heN : e ∈ normalizer (CFSG.Open.pCoreOf 2 L : Set G) := hEO he
    have hfN : f ∈ normalizer (CFSG.Open.pCoreOf 2 L : Set G) := hON hfM
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    have hef : e * f * e⁻¹ * f⁻¹ ∈ CFSG.Open.pCoreOf 2 L := by
      simpa only [commutatorElement_def] using hcommW e he
    simpa using r887_commutator_zpow_mem hfN heN hef 1 k
  obtain ⟨A', hA'C, hA'sup, ⟨φ⟩⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.exists_centralizing_copy
      (ℓ := 3) (p := 5) Nat.prime_three (by norm_num) Nat.prime_five (by norm_num)
      (CFSG.Open.pCoreOf 2 L) (Subgroup.zpowers f) W hO hAO hEO hA hW3 hcomm
  have hA'M : A' ≤ D.M :=
    hA'sup.trans (sup_le hAM
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans (r888s_le ctx)))
  have hA'card : Nat.card A' = 5 := by rw [Nat.card_congr φ.toEquiv, hAcard]
  have hdvd : Nat.card A' ∣ Nat.card ↥(D.M ⊓ centralizer (W : Set G)) :=
    Subgroup.card_dvd_of_le (le_inf hA'M hA'C)
  rwa [hA'card] at hdvd

private def r888gen_commNormalizer {G : Type} [Group G] (O : Subgroup G) (f : G) :
    Subgroup G where
  carrier := {x : G | x ∈ Subgroup.normalizer (O : Set G) ∧ ⁅x, f⁆ ∈ O}
  one_mem' := by
    refine ⟨(Subgroup.normalizer (O : Set G)).one_mem, ?_⟩
    simp
  mul_mem' := by
    rintro x y ⟨hxN, hxf⟩ ⟨hyN, hyf⟩
    refine ⟨(Subgroup.normalizer (O : Set G)).mul_mem hxN hyN, ?_⟩
    rw [commutatorElement_mul_left_eq_conj_mul]
    exact O.mul_mem ((Subgroup.mem_normalizer_iff.mp hxN ⁅y, f⁆).mp hyf) hxf
  inv_mem' := by
    rintro x ⟨hxN, hxf⟩
    refine ⟨(Subgroup.normalizer (O : Set G)).inv_mem hxN, ?_⟩
    rw [commutatorElement_inv_left]
    have hfx : ⁅f, x⁆ ∈ O := by
      rw [← commutatorElement_inv]
      exact O.inv_mem hxf
    simpa using
      (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (O : Set G)).inv_mem hxN) ⁅f, x⁆).mp hfx

private theorem r888s_step_generator
    {G : Type} [Group G] [Finite G] {D : Data G} {L P : Subgroup G}
    (ctx : r888s_Ctx D L P) {g : G}
    (hY : (ZOf (P ⊓ L)).map (MulAut.conj g).toMonoidHom ≤ P)
    (hbad : ∀ m ∈ D.M, (ZOf (P ⊓ L)).map (MulAut.conj g).toMonoidHom ≠
      (ZOf (P ⊓ L)).map (MulAut.conj m).toMonoidHom) :
    ∃ q c : G, q ∈ (P ⊓ L : Subgroup G) ∧ c ∈ centralizerBar P L ∧
      orderOf q = 3 ∧ q ∉ ZOf (P ⊓ L) ∧ orderOf c = 3 ∧ c ≠ 1 ∧
      (ZOf (P ⊓ L)).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers (q * c) := by
  let Y : Subgroup G := (ZOf (P ⊓ L)).map (MulAut.conj g).toMonoidHom
  have hg : g ∉ D.M := fun hgm => hbad g hgm rfl
  have h5 : ¬ 5 ∣ Nat.card ↥(D.M ⊓ centralizer (Y : Set G)) :=
    fun h => r888s_step_5prime ctx g hg h
  have hZc : Nat.card (ZOf (P ⊓ L)) = 3 := (ctx.h886 L P ctx.hset).1
  have hYc : Nat.card Y = 3 := by
    show Nat.card ((ZOf (P ⊓ L)).map (MulAut.conj g).toMonoidHom) = 3
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hZc]
  have hYp : IsPGroup 3 Y := IsPGroup.of_card (n := 1) (by rw [hYc]; norm_num)
  have hYcyc : IsCyclic Y := isCyclic_of_card_dvd_prime (p := 3) (by rw [hYc])
  obtain ⟨y, hyY⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top Y).mp hYcyc
  have hyYmem : y ∈ Y := hyY ▸ Subgroup.mem_zpowers y
  have hyP : y ∈ P := hY hyYmem
  obtain ⟨hPle, hCQ, hQC⟩ := r888s_step_P_decomp ctx
  obtain ⟨q, hq, c, hc, rfl⟩ :=
    exists_mul_mem_sup_of_commute hCQ (hPle hyP)
  have hcomm : Commute q c := (hCQ c hc q hq).symm
  have hord : orderOf (q * c) = 3 := by
    rw [← Nat.card_zpowers, hyY, hYc]
  have hy3 : (q * c) ^ 3 = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one (q * c)
  have hmul : q ^ 3 * c ^ 3 = 1 := by
    rw [← hcomm.mul_pow, hy3]
  have hq3 : q ^ 3 = 1 := by
    have hq3Q : q ^ 3 ∈ (P ⊓ L : Subgroup G) := (P ⊓ L).pow_mem hq 3
    have hc3C : c ^ 3 ∈ centralizerBar P L := (centralizerBar P L).pow_mem hc 3
    have hq3bot : q ^ 3 ∈ (P ⊓ L) ⊓ centralizerBar P L := by
      refine Subgroup.mem_inf.mpr ⟨hq3Q, ?_⟩
      rw [eq_inv_of_mul_eq_one_left hmul]
      exact (centralizerBar P L).inv_mem hc3C
    rw [hQC] at hq3bot
    exact Subgroup.mem_bot.mp hq3bot
  have hc3 : c ^ 3 = 1 := by
    have hq3Q : q ^ 3 ∈ (P ⊓ L : Subgroup G) := (P ⊓ L).pow_mem hq 3
    have hc3C : c ^ 3 ∈ centralizerBar P L := (centralizerBar P L).pow_mem hc 3
    have hc3bot : c ^ 3 ∈ (P ⊓ L) ⊓ centralizerBar P L := by
      refine Subgroup.mem_inf.mpr ⟨?_, hc3C⟩
      rw [eq_inv_of_mul_eq_one_right hmul]
      exact (P ⊓ L).inv_mem hq3Q
    rw [hQC] at hc3bot
    exact Subgroup.mem_bot.mp hc3bot
  by_cases hc1 : c = 1
  · have hYQ : Y ≤ P ⊓ L := by
      rw [hyY.symm, hc1, mul_one]
      exact Subgroup.zpowers_le.mpr hq
    obtain ⟨f, hfC, hf5⟩ := r888s_step_five_C ctx
    have hfM : f ∈ D.M := centralizerBar_le D.M L hfC
    have hfO : ∀ w ∈ Y, ⁅w, f⁆ ∈ CFSG.Open.pCoreOf 2 L := by
      intro w hw
      have hwL : w ∈ L := (inf_le_right : (P ⊓ L : Subgroup G) ≤ L) (hYQ hw)
      rw [← commutatorElement_inv]
      exact (CFSG.Open.pCoreOf 2 L).inv_mem ((mem_centralizerBar_iff.mp hfC).2 w hwL)
    have hYM : Y ≤ D.M := hY.trans ctx.hset.sylow.le
    exact absurd (r888s_step_K5 ctx Y hYM hYp f hfM hf5 hfO) h5
  · by_cases hqZ : q ∈ ZOf (P ⊓ L)
    · obtain ⟨f, hfL, hf5, hfZ⟩ := r888s_step_five_L ctx
      have hfM : f ∈ D.M := r888s_le ctx hfL
      let W : Subgroup G := r888gen_commNormalizer (CFSG.Open.pCoreOf 2 L) f
      have hZW : ZOf (P ⊓ L) ≤ W := by
        intro z hz
        have hzL : z ∈ L := (inf_le_right : (P ⊓ L : Subgroup G) ≤ L) (r888s_ZOf_le (P ⊓ L) hz)
        have hzN : z ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hzL
        exact ⟨(CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) L) hzN,
          hfZ z hz⟩
      have hCW : centralizerBar P L ≤ W := by
        intro x hx
        have hxP : x ∈ P := centralizerBar_le P L hx
        have hxN : x ∈ Subgroup.normalizer (L : Set G) :=
          r888s_norm ctx (ctx.hset.sylow.le hxP)
        exact ⟨(CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) L) hxN,
          (mem_centralizerBar_iff.mp hx).2 f hfL⟩
      have hqcW : q * c ∈ W := W.mul_mem (hZW hqZ) (hCW hc)
      have hYW : Y ≤ W := by
        rw [hyY.symm]
        exact Subgroup.zpowers_le.mpr hqcW
      have hfO : ∀ w ∈ Y, ⁅w, f⁆ ∈ CFSG.Open.pCoreOf 2 L := fun w hw => (hYW hw).2
      have hYM : Y ≤ D.M := hY.trans ctx.hset.sylow.le
      exact absurd (r888s_step_K5 ctx Y hYM hYp f hfM hf5 hfO) h5
    · have hq1 : q ≠ 1 := fun h1 => hqZ (h1 ▸ (ZOf (P ⊓ L)).one_mem)
      exact ⟨q, c, hq, hc, orderOf_eq_prime hq3 hq1, hqZ,
        orderOf_eq_prime hc3 hc1, hc1, hyY.symm⟩

private theorem r888cc_Q_not_cyclic {G : Type} [Group G] [Finite G]
    {D : Data G} {L P : Subgroup G} (ctx : r888s_Ctx D L P) :
    ¬ IsCyclic ↥(P ⊓ L) := by
  intro hcyc
  have hcycI : IsCyclic ↥(P ⊓ L) := hcyc
  have hcomm : IsMulCommutative ↥(P ⊓ L) := inferInstance
  have hbot : ⁅(P ⊓ L : Subgroup G), (P ⊓ L : Subgroup G)⁆ = ⊥ :=
    Subgroup.commutator_self_eq_bot_iff.mpr hcomm
  rw [r888s_commutator_Q ctx] at hbot
  have hZ : Nat.card (ZOf (P ⊓ L)) = 3 := (ctx.h886 L P ctx.hset).1
  rw [hbot, Subgroup.card_bot] at hZ
  norm_num at hZ

private theorem r888cc_pRank_Q {G : Type} [Group G] [Finite G]
    {D : Data G} {L P : Subgroup G} (ctx : r888s_Ctx D L P) :
    2 ≤ CFSG.Open.pRank 3 (P ⊓ L) := by
  by_contra h
  have hle1 : CFSG.Open.pRank 3 (P ⊓ L) ≤ 1 := by omega
  have hQ3 : IsPGroup 3 ↥(P ⊓ L) := ctx.hset.sylow.isPGroup.to_le inf_le_left
  exact r888cc_Q_not_cyclic ctx
    (CFSG.isCyclic_of_le_of_pRank_le_one Nat.prime_three (by norm_num) hQ3 le_rfl hle1)

private theorem r888cc_pRank_C_le_one
    {G : Type} [Group G] [Finite G] {D : Data G} {L P : Subgroup G} (ctx : r888s_Ctx D L P) :
    CFSG.Open.pRank 3 (centralizerBar P L) ≤ 1 := by
  by_contra h
  have hC2 : 2 ≤ CFSG.Open.pRank 3 (centralizerBar P L) := by omega
  have hQrank : 2 ≤ CFSG.Open.pRank 3 (P ⊓ L) := r888cc_pRank_Q ctx
  obtain ⟨E, hEQ, hEel, hEcard⟩ :=
    CFSG.PreuniquenessRankFour.Helpers.pRank_attained 3 Nat.prime_three (P ⊓ L)
  obtain ⟨F, hFC, hFel, hFcard⟩ :=
    CFSG.PreuniquenessRankFour.Helpers.pRank_attained 3 Nat.prime_three (centralizerBar P L)
  have hcommEF : ∀ e ∈ E, ∀ f ∈ F, e * f = f * e := by
    intro e he f hf
    exact ((r888s_step_P_decomp ctx).2.1 f (hFC hf) e (hEQ he)).symm
  have hEFel : IsElemAbelian 3 (E ⊔ F) := hEel.sup_of_commute hFel hcommEF
  have hEcen : E ≤ Subgroup.centralizer (F : Set G) := by
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    exact (hcommEF e he f hf).symm
  have hEFN : E ≤ Subgroup.normalizer (F : Set G) :=
    hEcen.trans (Subgroup.centralizer_le_normalizer (F : Set G))
  have hEFbot : E ⊓ F = ⊥ := by
    have hcalc : E ⊓ F ≤ ⊥ := by
      calc E ⊓ F ≤ (P ⊓ L) ⊓ centralizerBar P L := inf_le_inf hEQ hFC
        _ = ⊥ := (r888s_step_P_decomp ctx).2.2
    exact le_antisymm hcalc bot_le
  have hEFcard : Nat.card ↥(E ⊔ F) =
      3 ^ (CFSG.Open.pRank 3 (P ⊓ L) + CFSG.Open.pRank 3 (centralizerBar P L)) := by
    have hprod := CFSG.LocalAnalysis.SteinbergBQ.card_sup_mul_card_inf_of_normalizes hEFN
    rw [hEFbot, Subgroup.card_bot, mul_one, hEcard, hFcard, ← pow_add] at hprod
    exact hprod
  have hEFM : E ⊔ F ≤ D.M :=
    sup_le (hEQ.trans (inf_le_left.trans ctx.hset.sylow.le))
      (hFC.trans ((centralizerBar_le P L).trans ctx.hset.sylow.le))
  have hle := CFSG.LocalAnalysis.UniquenessCase.UC6S846.le_pRank' Nat.prime_three hEFM hEFel hEFcard
  have hM := r888s_rank3M ctx
  omega

private theorem r888cc_isCyclic_C
    {G : Type} [Group G] [Finite G] {D : Data G} {L P : Subgroup G} (ctx : r888s_Ctx D L P) :
    IsCyclic (centralizerBar P L) := by
  have hC3 : IsPGroup 3 (centralizerBar P L) :=
    ctx.hset.sylow.isPGroup.to_le (centralizerBar_le P L)
  exact CFSG.isCyclic_of_le_of_pRank_le_one Nat.prime_three (by norm_num) hC3 le_rfl
    (r888cc_pRank_C_le_one ctx)

private theorem r888cc_commutator_le
    {G : Type} [Group G] [Finite G] {D : Data G} {L P : Subgroup G} (ctx : r888s_Ctx D L P) :
    ⁅P, P⁆ ≤ ZOf (P ⊓ L) := by
  have hcyc : IsCyclic (centralizerBar P L) := r888cc_isCyclic_C ctx
  have hcycI : IsCyclic (centralizerBar P L) := hcyc
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨q₁, hq₁, c₁, hc₁, rfl⟩ :=
    exists_mul_mem_sup_of_commute (r888s_step_P_decomp ctx).2.1 ((r888s_step_P_decomp ctx).1 hx)
  obtain ⟨q₂, hq₂, c₂, hc₂, rfl⟩ :=
    exists_mul_mem_sup_of_commute (r888s_step_P_decomp ctx).2.1 ((r888s_step_P_decomp ctx).1 hy)
  have hc₁c₂ : Commute c₁ c₂ :=
    congrArg Subtype.val
      (mul_comm' (⟨c₁, hc₁⟩ : centralizerBar P L) (⟨c₂, hc₂⟩ : centralizerBar P L))
  have hcomm : ⁅q₁ * c₁, q₂ * c₂⁆ = ⁅q₁, q₂⁆ := by
    have h1 : Commute c₁ (q₂ * c₂) :=
      Commute.mul_right
        (show Commute c₁ q₂ from (r888s_step_P_decomp ctx).2.1 c₁ hc₁ q₂ hq₂) hc₁c₂
    have h2 : Commute q₁ c₂ :=
      (show Commute c₂ q₁ from (r888s_step_P_decomp ctx).2.1 c₂ hc₂ q₁ hq₁).symm
    rw [commutatorElement_mul_left_eq_conj_mul, h1.commutator_eq,
      commutatorElement_mul_right_eq_mul_conj, h2.commutator_eq]
    group
  rw [hcomm, ← r888s_commutator_Q ctx]
  exact Subgroup.commutator_mem_commutator hq₁ hq₂

private theorem r888s_step_C_cyclic
    {G : Type} [Group G] [Finite G] {D : Data G}
    {L P : Subgroup G} (ctx : r888s_Ctx D L P) :
    IsCyclic (centralizerBar P L) ∧ ⁅P, P⁆ ≤ ZOf (P ⊓ L) :=
  ⟨r888cc_isCyclic_C ctx, r888cc_commutator_le ctx⟩

private theorem r888np_Z_elem {G : Type} [Group G] {Q : Subgroup G}
    (hZ : Nat.card (ZOf Q) = 3) : IsElemAbelian 3 (ZOf Q) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun a ha => ?_⟩
  · exact (Subgroup.mem_centralizer_iff.mp a.2.2 (b : G) b.2.1).symm
  · have h := pow_card_eq_one' (x := (⟨a, ha⟩ : ZOf Q))
    rw [hZ] at h
    simpa using congrArg Subtype.val h

private theorem r888np_E_elem {G : Type} [Group G] {Q : Subgroup G} {q : G}
    (hq : q ∈ Q) (hZ : Nat.card (ZOf Q) = 3) (hq3 : orderOf q = 3) :
    IsElemAbelian 3 (ZOf Q ⊔ Subgroup.zpowers q) := by
  have hZel : IsElemAbelian 3 (ZOf Q) := r888np_Z_elem hZ
  have hqel : IsElemAbelian 3 (Subgroup.zpowers q) :=
    isElemAbelian_zpowers (x := q) (p := 3) (by rw [← hq3]; exact pow_orderOf_eq_one q)
  refine hZel.sup_of_commute hqel ?_
  intro a ha b hb
  have hbQ : b ∈ Q := Subgroup.zpowers_le.mpr hq hb
  exact (Subgroup.mem_centralizer_iff.mp ha.2 b hbQ).symm

private theorem r888np_sup_zpowers_elem_card {G : Type} [Group G] [Finite G] {P L E : Subgroup G}
    {c : G}
    (hEel : IsElemAbelian 3 E) (hEcard : Nat.card E = 9) (hEQ : E ≤ P ⊓ L)
    (hc : c ∈ centralizerBar P L) (hc3 : orderOf c = 3)
    (hdisj : (P ⊓ L) ⊓ centralizerBar P L = ⊥)
    (hcomm : ∀ a ∈ E, a * c = c * a) :
    IsElemAbelian 3 (E ⊔ Subgroup.zpowers c) ∧ Nat.card ↥(E ⊔ Subgroup.zpowers c) = 27 := by
  have hcE : c ∈ Subgroup.centralizer (E : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun y hy => hcomm y hy
  have hczN : Subgroup.zpowers c ≤ Subgroup.normalizer (E : Set G) :=
    (Subgroup.zpowers_le.mpr hcE).trans (Subgroup.centralizer_le_normalizer (E : Set G))
  have hinf : E ⊓ Subgroup.zpowers c = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : z ∈ (P ⊓ L) ⊓ centralizerBar P L :=
      ⟨hEQ hz.1, (Subgroup.zpowers_le.mpr hc) hz.2⟩
    rwa [hdisj] at hz'
  have hcard : Nat.card ↥(E ⊔ Subgroup.zpowers c) = 27 := by
    have h := CFSG.LocalAnalysis.SteinbergBQ.card_sup_mul_card_inf_of_normalizes
      (X := Subgroup.zpowers c) (N := E) hczN
    rw [sup_comm, inf_comm, hinf, hEcard, Nat.card_zpowers c, hc3] at h
    simp only [Nat.card_unique, mul_one] at h
    omega
  have hCel : IsElemAbelian 3 (Subgroup.zpowers c) :=
    isElemAbelian_zpowers (x := c) (p := 3) (by rw [← hc3]; exact pow_orderOf_eq_one c)
  have hcommE : ∀ a ∈ E, ∀ b ∈ Subgroup.zpowers c, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hb
    rw [← hk]
    have hca : Commute a c := hcomm a ha
    exact (hca.zpow_right k).eq
  exact ⟨hEel.sup_of_commute hCel hcommE, hcard⟩

private theorem r888s_step_NP
    {G : Type} [Group G] [Finite G] {D : Data G}
    {L P : Subgroup G} (ctx : r888s_Ctx D L P) {q c : G}
    (hq : q ∈ (P ⊓ L : Subgroup G)) (hc : c ∈ centralizerBar P L) (hq3 : orderOf q = 3)
    (hqZ : q ∉ ZOf (P ⊓ L)) (hc3 : orderOf c = 3) :
    ∃ A : Subgroup G, A ≤ P ∧ IsElemAbelian 3 A ∧ Nat.card A = 27 ∧ q * c ∈ A := by
  have hZcard : Nat.card (ZOf (P ⊓ L)) = 3 := (ctx.h886 L P ctx.hset).1
  obtain ⟨-, hcomm, hdisj⟩ := r888s_step_P_decomp ctx
  have hZqcard : Nat.card (Subgroup.zpowers q) = 3 := by rw [Nat.card_zpowers q, hq3]
  have hZne : ZOf (P ⊓ L) ≠ Subgroup.zpowers q := by
    intro h
    exact hqZ (by rw [h]; exact Subgroup.mem_zpowers q)
  have hE9 : Nat.card ↥(ZOf (P ⊓ L) ⊔ Subgroup.zpowers q) = 9 :=
    card_sup_eq_nine_of_card_three_of_ne hZcard hZqcard hZne
      (fun a ha b hb =>
        (Subgroup.mem_centralizer_iff.mp ha.2 b (Subgroup.zpowers_le.mpr hq hb)).symm)
  have hEel : IsElemAbelian 3 (ZOf (P ⊓ L) ⊔ Subgroup.zpowers q) :=
    r888np_E_elem hq hZcard hq3
  have hEQ : ZOf (P ⊓ L) ⊔ Subgroup.zpowers q ≤ P ⊓ L :=
    sup_le (r888s_ZOf_le _) (Subgroup.zpowers_le.mpr hq)
  have hcommEc : ∀ a ∈ ZOf (P ⊓ L) ⊔ Subgroup.zpowers q, a * c = c * a :=
    fun a ha => (hcomm c hc a (hEQ ha)).symm
  obtain ⟨hAel, hAcard⟩ :=
    r888np_sup_zpowers_elem_card hEel hE9 hEQ hc hc3 hdisj hcommEc
  refine ⟨(ZOf (P ⊓ L) ⊔ Subgroup.zpowers q) ⊔ Subgroup.zpowers c, ?_, hAel, hAcard, ?_⟩
  · exact sup_le
      (sup_le (r888s_ZOf_le_P (P := P) (Q := P ⊓ L) inf_le_left)
        (Subgroup.zpowers_le.mpr hq.1))
      ((Subgroup.zpowers_le.mpr hc).trans (centralizerBar_le P L))
  · exact ((ZOf (P ⊓ L) ⊔ Subgroup.zpowers q) ⊔ Subgroup.zpowers c).mul_mem
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers q)))
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers c))

private theorem r888e27_Bcentral
    {G : Type} [Group G] [Finite G] {D : Data G}
    {L P : Subgroup G} (ctx : r888s_Ctx D L P) {c : G}
    (hc : c ∈ centralizerBar P L) (_hc3 : orderOf c = 3) :
    ∀ p ∈ P, ∀ b ∈ ZOf (P ⊓ L) ⊔ Subgroup.zpowers c, p * b = b * p := by
  let Z := ZOf (P ⊓ L)
  let Q := P ⊓ L
  let C := centralizerBar P L
  have hdecomp := r888s_step_P_decomp ctx
  have hcommCQ : ∀ c ∈ C, ∀ q ∈ Q, c * q = q * c := hdecomp.2.1
  have hPC : P ≤ Q ⊔ C := hdecomp.1
  have hZleQ : Z ≤ Q := r888s_ZOf_le Q
  have hZleP : Z ≤ P := r888s_ZOf_le_P inf_le_left
  have hcentral_Z : ∀ p ∈ P, ∀ z ∈ Z, p * z = z * p := by
    intro p hp z hz
    obtain ⟨q, hq, c', hc', rfl⟩ :=
      exists_mul_mem_sup_of_commute (Q := Q) (C := C) hcommCQ (hPC hp)
    have hzQ : z ∈ Q := hZleQ hz
    have hzC : z ∈ Subgroup.centralizer (Q : Set G) := hz.2
    have hqz : Commute q z := Subgroup.mem_centralizer_iff.mp hzC q hq
    have hcz : Commute c' z := hcommCQ c' hc' z hzQ
    exact (hqz.mul_left hcz).eq
  have hcentral_c : ∀ p ∈ P, p * c = c * p := by
    intro p hp
    obtain ⟨q, hq, c', hc', rfl⟩ :=
      exists_mul_mem_sup_of_commute (Q := Q) (C := C) hcommCQ (hPC hp)
    have hqc : Commute q c := (hcommCQ c hc q hq).symm
    have hcc : Commute c' c := by
      exact congrArg Subtype.val (@mul_comm' C _
        (@IsCyclic.isMulCommutative C _ (r888s_step_C_cyclic ctx).1)
        (⟨c', hc'⟩ : C) (⟨c, hc⟩ : C))
    exact (hqc.mul_left hcc).eq
  have hcommZc : ∀ a ∈ Z, ∀ y ∈ Subgroup.zpowers c, a * y = y * a := by
    intro a ha y hy
    have haP : a ∈ P := hZleP ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_right (hcentral_c a haP) k).eq
  intro p hp b hb
  obtain ⟨z, hz, y, hy, rfl⟩ :=
    exists_mul_mem_sup_of_commute (Q := Z) (C := Subgroup.zpowers c)
      (fun y hy a ha => (hcommZc a ha y hy).symm) hb
  have hzp : Commute p z := hcentral_Z p hp z hz
  have hyp : Commute p y := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact Commute.zpow_right (hcentral_c p hp) k
  exact (hzp.mul_right hyp).eq

private theorem r888e27_elemAbelian
    {G : Type} [Group G] [Finite G] {D : Data G}
    {L P : Subgroup G} (ctx : r888s_Ctx D L P) {c : G}
    (hc : c ∈ centralizerBar P L) (hc3 : orderOf c = 3) :
    IsElemAbelian 3 (ZOf (P ⊓ L) ⊔ Subgroup.zpowers c) := by
  let Z := ZOf (P ⊓ L)
  have hBcentral := r888e27_Bcentral ctx hc hc3
  have hZcard : Nat.card Z = 3 := (ctx.h886 L P ctx.hset).1
  have hZel : IsElemAbelian 3 Z := by
    constructor
    · exact @IsCyclic.isMulCommutative Z _ (isCyclic_of_prime_card (p := 3) hZcard)
    · intro x hx
      have hxdiv : orderOf x ∣ Nat.card Z := by
        rw [← Nat.card_zpowers]
        exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hx)
      rw [hZcard] at hxdiv
      exact orderOf_dvd_iff_pow_eq_one.mp hxdiv
  have hc3pow : c ^ 3 = 1 := by
    rw [← hc3]
    exact pow_orderOf_eq_one c
  have hcel : IsElemAbelian 3 (Subgroup.zpowers c) := isElemAbelian_zpowers hc3pow
  have hcomm : ∀ a ∈ Z, ∀ b ∈ Subgroup.zpowers c, a * b = b * a := by
    intro a ha b hb
    have haP : a ∈ P := (r888s_ZOf_le_P inf_le_left) ha
    exact hBcentral a haP b (Subgroup.mem_sup_right hb)
  exact IsElemAbelian.sup_of_commute hZel hcel hcomm

private theorem r888e27_card_B
    {G : Type} [Group G] [Finite G] {D : Data G}
    {L P : Subgroup G} (ctx : r888s_Ctx D L P) {c : G}
    (hc : c ∈ centralizerBar P L) (hc3 : orderOf c = 3) :
    Nat.card ↥(ZOf (P ⊓ L) ⊔ Subgroup.zpowers c) = 9 := by
  let Z := ZOf (P ⊓ L)
  have hBcentral := r888e27_Bcentral ctx hc hc3
  have hZcard : Nat.card Z = 3 := (ctx.h886 L P ctx.hset).1
  have hccard : Nat.card (Subgroup.zpowers c) = 3 := by
    rw [Nat.card_zpowers, hc3]
  have hZne : Z ≠ Subgroup.zpowers c := by
    intro h
    have hZleC : Z ≤ centralizerBar P L := h ▸ Subgroup.zpowers_le.mpr hc
    have hZleQ : Z ≤ P ⊓ L := r888s_ZOf_le (P ⊓ L)
    have hZbot : Z ≤ ⊥ := by
      rw [← (r888s_step_P_decomp ctx).2.2]
      exact le_inf hZleQ hZleC
    have h1 : Nat.card Z = 1 := by
      have hZeq : Z = ⊥ := bot_unique hZbot
      rw [hZeq, Subgroup.card_bot]
    omega
  have hcomm : ∀ x ∈ Z, ∀ y ∈ Subgroup.zpowers c, x * y = y * x := by
    intro x hx y hy
    have hxP : x ∈ P := (r888s_ZOf_le_P inf_le_left) hx
    exact hBcentral x hxP y (Subgroup.mem_sup_right hy)
  exact card_sup_eq_nine_of_card_three_of_ne hZcard hccard hZne hcomm

private theorem r888e27_B_le_A
    {G : Type} [Group G] [Finite G] {D : Data G}
    {L P : Subgroup G} (ctx : r888s_Ctx D L P) {c : G}
    (hc : c ∈ centralizerBar P L) (hc3 : orderOf c = 3)
    {A : Subgroup G} (hAP : A ≤ P) (hA : IsElemAbelian 3 A) (hAc : Nat.card A = 27) :
    ZOf (P ⊓ L) ⊔ Subgroup.zpowers c ≤ A := by
  let Z := ZOf (P ⊓ L)
  let B := Z ⊔ Subgroup.zpowers c
  by_contra hnot
  obtain ⟨x, hxB, hxA⟩ := Set.not_subset.mp hnot
  have hBcentral := r888e27_Bcentral ctx hc hc3
  have hBel : IsElemAbelian 3 B := r888e27_elemAbelian ctx hc hc3
  have hBP : B ≤ P := by
    apply sup_le
    · exact r888s_ZOf_le_P inf_le_left
    · exact Subgroup.zpowers_le.mpr (centralizerBar_le P L hc)
  have hx3 : x ^ 3 = 1 := hBel.2 x hxB
  have hx_ne_one : x ≠ 1 := by
    intro hx1
    apply hxA
    rw [hx1]
    exact A.one_mem
  have hxOrder : orderOf x = 3 := by
    have hdvd : orderOf x ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hx3
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx_ne_one
    · exact h
  have hxcard : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, hxOrder]
  have hinf : A ⊓ Subgroup.zpowers x = ⊥ := by
    by_contra hne
    have hcard_inf : Nat.card ↥(A ⊓ Subgroup.zpowers x) = 3 := by
      have hdvd : Nat.card ↥(A ⊓ Subgroup.zpowers x) ∣ 3 := by
        rw [← hxcard]
        exact Subgroup.card_dvd_of_le inf_le_right
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exfalso
        exact hne (Subgroup.eq_bot_of_card_eq (A ⊓ Subgroup.zpowers x) h)
      · exact h
    have hEq : A ⊓ Subgroup.zpowers x = Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hcard_inf, hxcard])
    exact hxA (hEq.symm ▸ Subgroup.mem_zpowers x).1
  have hxel : IsElemAbelian 3 (Subgroup.zpowers x) := isElemAbelian_zpowers hx3
  have hsup_comm : ∀ a ∈ A, ∀ b ∈ Subgroup.zpowers x, a * b = b * a := by
    intro a ha b hb
    have haP : a ∈ P := hAP ha
    have hbB : b ∈ B := Subgroup.zpowers_le.mpr hxB hb
    exact hBcentral a haP b hbB
  have hxcentA : x ∈ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact hBcentral a (hAP ha) x hxB
  have hnorm : Subgroup.zpowers x ≤ Subgroup.normalizer (A : Set G) :=
    (Subgroup.zpowers_le.mpr hxcentA).trans (Subgroup.centralizer_le_normalizer (A : Set G))
  have hcard_sup : Nat.card ↥(A ⊔ Subgroup.zpowers x) = 3 ^ 4 := by
    have h := CFSG.LocalAnalysis.SteinbergBQ.card_sup_mul_card_inf_of_normalizes
      (X := Subgroup.zpowers x) (N := A) hnorm
    rw [sup_comm, inf_comm, hinf, Subgroup.card_bot, mul_one, hAc, hxcard] at h
    rw [h]
    norm_num
  have hsupel : IsElemAbelian 3 (A ⊔ Subgroup.zpowers x) :=
    IsElemAbelian.sup_of_commute hA hxel hsup_comm
  have hEM : A ⊔ Subgroup.zpowers x ≤ D.M := by
    apply sup_le
    · exact hAP.trans (CFSG.ABGLocalTools.IsSylowOf.le ctx.hset.sylow)
    · exact (Subgroup.zpowers_le.mpr (hBP hxB)).trans
        (CFSG.ABGLocalTools.IsSylowOf.le ctx.hset.sylow)
  have hrank : 4 ≤ CFSG.Open.pRank 3 D.M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.le_pRank' Nat.prime_three hEM hsupel hcard_sup
  have hle := r888s_rank3M ctx
  omega

private theorem r888e27_P_normalizes_A
    {G : Type} [Group G] [Finite G] {D : Data G}
    {L P : Subgroup G} (ctx : r888s_Ctx D L P) {c : G}
    (hc : c ∈ centralizerBar P L) (hc3 : orderOf c = 3)
    {A : Subgroup G} (hAP : A ≤ P) (hA : IsElemAbelian 3 A) (hAc : Nat.card A = 27) :
    P ≤ normalizer (A : Set G) := by
  have hBA : ZOf (P ⊓ L) ⊔ Subgroup.zpowers c ≤ A := r888e27_B_le_A ctx hc hc3 hAP hA hAc
  have hPP : ⁅P, P⁆ ≤ ZOf (P ⊓ L) := (r888s_step_C_cyclic ctx).2
  intro p hp
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · rintro x ⟨a, ha, rfl⟩
    change p * a * p⁻¹ ∈ A
    have hpa : p * a * p⁻¹ = ⁅p, a⁆ * a := by
      rw [commutatorElement_def]
      group
    rw [hpa]
    exact A.mul_mem (hBA (Subgroup.mem_sup_left (hPP (Subgroup.commutator_mem_commutator hp (hAP ha))))) ha
  · rw [Subgroup.card_map_of_injective (MulAut.conj p).injective]

private theorem r888s_step_E27
    {G : Type} [Group G] [Finite G] {D : Data G}
    {L P : Subgroup G} (ctx : r888s_Ctx D L P) {c : G}
    (hc : c ∈ centralizerBar P L) (hc3 : orderOf c = 3)
    {A : Subgroup G} (hAP : A ≤ P) (hA : IsElemAbelian 3 A) (hAc : Nat.card A = 27) :
    Nat.card ↥(ZOf (P ⊓ L) ⊔ Subgroup.zpowers c) = 9 ∧
      ZOf (P ⊓ L) ⊔ Subgroup.zpowers c ≤ A ∧ P ≤ normalizer (A : Set G) := by
  exact ⟨r888e27_card_B ctx hc hc3, r888e27_B_le_A ctx hc hc3 hAP hA hAc,
    r888e27_P_normalizes_A ctx hc hc3 hAP hA hAc⟩

private theorem r888ax_mem_zpowers_of_pow_three {G : Type} [Group G] [Finite G]
    {C : Subgroup G} (hC : IsCyclic ↥C)
    {c x : G} (hc : c ∈ C) (hx : x ∈ C) (hc3 : orderOf c = 3) (hx3 : x ^ 3 = 1) :
    x ∈ Subgroup.zpowers c := by
  classical
  let _fintype : Fintype ↥C := Fintype.ofFinite ↥C
  have hc3' : orderOf (⟨c, hc⟩ : ↥C) = 3 := by
    simpa using (Subgroup.orderOf_coe (⟨c, hc⟩ : ↥C)).symm.trans hc3
  let S : Subgroup ↥C := Subgroup.zpowers ⟨c, hc⟩
  have hScard' : Nat.card ↥S = 3 := by
    rw [Nat.card_zpowers, hc3']
  have hScard : (S : Set ↥C).ncard = 3 := by
    rw [← Nat.card_coe_set_eq]
    change Nat.card ↥S = 3
    exact hScard'
  have hsub : (S : Set ↥C) ⊆ {a : ↥C | a ^ 3 = 1} := by
    intro a ha
    have hdvd : orderOf a ∣ Nat.card S := S.orderOf_dvd_natCard ha
    rw [hScard'] at hdvd
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  have hbound : ({a : ↥C | a ^ 3 = 1} : Set ↥C).ncard ≤ 3 := by
    have h := IsCyclic.card_pow_eq_one_le (α := ↥C) (n := 3) (by norm_num)
    rw [← Set.toFinset_ofPred, ← Set.ncard_eq_toFinset_card'] at h
    exact h
  have heq : (S : Set ↥C) = {a : ↥C | a ^ 3 = 1} :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hScard]; exact hbound)
  have hx3' : (⟨x, hx⟩ : ↥C) ^ 3 = 1 := by
    apply Subtype.ext
    simpa using hx3
  have hxS : (⟨x, hx⟩ : ↥C) ∈ S := by
    have : (⟨x, hx⟩ : ↥C) ∈ (S : Set ↥C) := by
      rw [heq]; exact hx3'
    exact this
  rw [Subgroup.mem_zpowers_iff] at hxS ⊢
  obtain ⟨k, hk⟩ := hxS
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

private theorem r888ax_inf_centralizer_eq
    {G : Type} [Group G] [Finite G] {D : Data G}
    {L P : Subgroup G} (ctx : r888s_Ctx D L P) {c : G}
    (hc : c ∈ centralizerBar P L) (hc3 : orderOf c = 3)
    {A : Subgroup G} (hAP : A ≤ P) (hA : IsElemAbelian 3 A) (hAc : Nat.card A = 27) :
    A ⊓ centralizer ((P ⊓ L : Subgroup G) : Set G) =
      ZOf (P ⊓ L) ⊔ Subgroup.zpowers c := by
  obtain ⟨hPle, hcomm, -⟩ := r888s_step_P_decomp ctx
  obtain ⟨hB9, hBA, -⟩ := r888s_step_E27 ctx hc hc3 hAP hA hAc
  obtain ⟨hCcyc, -⟩ := r888s_step_C_cyclic ctx
  have hZcard : Nat.card (ZOf (P ⊓ L)) = 3 := (ctx.h886 L P ctx.hset).1
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxA, hxcent⟩ := hx
    have hxsup : x ∈ (P ⊓ L) ⊔ centralizerBar P L := hPle (hAP hxA)
    obtain ⟨q, hq, d, hd, hxqd⟩ := exists_mul_mem_sup_of_commute hcomm hxsup
    have hx3 : x ^ 3 = 1 := hA.2 x hxA
    have hqZ : q ∈ ZOf (P ⊓ L) := by
      have hq_eq : q = x * d⁻¹ := by rw [hxqd]; group
      rw [ZOf, Subgroup.mem_inf]
      refine ⟨hq, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [hq_eq]
      have hxy : y * x = x * y := (Subgroup.mem_centralizer_iff.mp hxcent) y hy
      have hdy : Commute d y := hcomm d hd y hy
      calc y * (x * d⁻¹) = (y * x) * d⁻¹ := by group
        _ = (x * y) * d⁻¹ := by rw [hxy]
        _ = x * (y * d⁻¹) := by group
        _ = x * (d⁻¹ * y) := by rw [← hdy.inv_left.eq]
        _ = (x * d⁻¹) * y := by group
    have hq3 : q ^ 3 = 1 := by
      have hdvd : orderOf q ∣ Nat.card (ZOf (P ⊓ L)) :=
        (ZOf (P ⊓ L)).orderOf_dvd_natCard hqZ
      rw [hZcard] at hdvd
      exact orderOf_dvd_iff_pow_eq_one.mp hdvd
    have hd3 : d ^ 3 = 1 := by
      have hqd : Commute q d := (hcomm d hd q hq).symm
      have h := hqd.mul_pow 3
      rw [← hxqd, hx3, hq3, one_mul] at h
      exact h.symm
    have hdc : d ∈ Subgroup.zpowers c :=
      r888ax_mem_zpowers_of_pow_three hCcyc hc hd hc3 hd3
    rw [hxqd]
    exact (ZOf (P ⊓ L) ⊔ Subgroup.zpowers c).mul_mem
      (Subgroup.mem_sup_left hqZ) (Subgroup.mem_sup_right hdc)
  · refine sup_le ?_ ?_
    · refine le_inf (fun z hz => hBA (Subgroup.mem_sup_left hz)) ?_
      exact inf_le_right
    · refine le_inf ?_ ?_
      · exact Subgroup.zpowers_le.mpr
          (hBA (Subgroup.mem_sup_right (Subgroup.mem_zpowers c)))
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        intro y hy
        exact (hcomm c hc y hy).symm

private theorem r888ax_inf_centralizerBar_eq
    {G : Type} [Group G] [Finite G] {D : Data G}
    {L P : Subgroup G} (ctx : r888s_Ctx D L P) {c : G}
    (hc : c ∈ centralizerBar P L) (hc3 : orderOf c = 3)
    {A : Subgroup G} (hAP : A ≤ P) (hA : IsElemAbelian 3 A) (hAc : Nat.card A = 27) :
    A ⊓ centralizerBar D.M L = Subgroup.zpowers c := by
  obtain ⟨-, hBA, -⟩ := r888s_step_E27 ctx hc hc3 hAP hA hAc
  obtain ⟨hCcyc, -⟩ := r888s_step_C_cyclic ctx
  have hcDM : c ∈ D.M := ctx.hset.sylow.le (mem_centralizerBar_iff.mp hc).1
  have hcDMC : c ∈ centralizerBar D.M L :=
    mem_centralizerBar_iff.mpr ⟨hcDM, (mem_centralizerBar_iff.mp hc).2⟩
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxA, hxCB⟩ := hx
    have hx3 : x ^ 3 = 1 := hA.2 x hxA
    exact r888ax_mem_zpowers_of_pow_three hCcyc hc
      (mem_centralizerBar_iff.mpr ⟨hAP hxA, (mem_centralizerBar_iff.mp hxCB).2⟩) hc3 hx3
  · exact Subgroup.zpowers_le.mpr
      (Subgroup.mem_inf.mpr ⟨hBA (Subgroup.mem_sup_right (Subgroup.mem_zpowers c)), hcDMC⟩)

private theorem r888s_step_axis
    {G : Type} [Group G] [Finite G] {D : Data G}
    {L P : Subgroup G} (ctx : r888s_Ctx D L P) {c : G}
    (hc : c ∈ centralizerBar P L) (hc3 : orderOf c = 3)
    {A : Subgroup G} (hAP : A ≤ P) (hA : IsElemAbelian 3 A) (hAc : Nat.card A = 27) :
    ⁅A, P ⊓ L⁆ = ZOf (P ⊓ L) ∧
      A ⊓ centralizer ((P ⊓ L : Subgroup G) : Set G) = ZOf (P ⊓ L) ⊔ Subgroup.zpowers c ∧
      A ⊓ centralizerBar D.M L = Subgroup.zpowers c := by
  have hZcard : Nat.card (ZOf (P ⊓ L)) = 3 := (ctx.h886 L P ctx.hset).1
  obtain ⟨-, hPP⟩ := r888s_step_C_cyclic ctx
  obtain ⟨hB9, -, -⟩ := r888s_step_E27 ctx hc hc3 hAP hA hAc
  have hB_eq := r888ax_inf_centralizer_eq ctx hc hc3 hAP hA hAc
  refine ⟨?_, hB_eq, r888ax_inf_centralizerBar_eq ctx hc hc3 hAP hA hAc⟩
  let K : Subgroup G := ⁅A, P ⊓ L⁆
  change K = ZOf (P ⊓ L)
  have hle : K ≤ ZOf (P ⊓ L) :=
    (Subgroup.commutator_mono hAP inf_le_left).trans hPP
  have hspace : K ≠ ⊥ := by
    intro hbot
    have hAcent : A ≤ centralizer ((P ⊓ L : Subgroup G) : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    have hAeq : A = ZOf (P ⊓ L) ⊔ Subgroup.zpowers c := by
      rw [← hB_eq]
      exact le_antisymm (le_inf le_rfl hAcent) inf_le_left
    have hcard9 : Nat.card A = 9 := by rw [hAeq]; exact hB9
    rw [hAc] at hcard9
    norm_num at hcard9
  have hdvd : Nat.card K ∣ Nat.card (ZOf (P ⊓ L)) :=
    Subgroup.card_dvd_of_le hle
  rw [hZcard] at hdvd
  have hne1 : Nat.card K ≠ 1 :=
    fun h1 => hspace ((Subgroup.eq_bot_iff_card K).mpr h1)
  have hcardcomm : Nat.card K = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact absurd h1 hne1
    · exact h3
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcardcomm, hZcard])

private def r888cb_fixMod {G : Type} [Group G] (O : Subgroup G) (f : G) : Subgroup G where
  carrier := {x | x ∈ Subgroup.normalizer (O : Set G) ∧ ⁅x, f⁆ ∈ O}
  one_mem' := by
    refine ⟨(Subgroup.normalizer (O : Set G)).one_mem, ?_⟩
    simp
  mul_mem' := by
    intro x y hx hy
    obtain ⟨hxN, hxO⟩ := hx
    obtain ⟨hyN, hyO⟩ := hy
    refine ⟨(Subgroup.normalizer (O : Set G)).mul_mem hxN hyN, ?_⟩
    rw [commutatorElement_mul_left_eq_conj_mul]
    exact O.mul_mem ((Subgroup.mem_normalizer_iff.mp hxN (⁅y, f⁆)).1 hyO) hxO
  inv_mem' := by
    intro x hx
    obtain ⟨hxN, hxO⟩ := hx
    have hxinvN : x⁻¹ ∈ Subgroup.normalizer (O : Set G) :=
      (Subgroup.normalizer (O : Set G)).inv_mem hxN
    have hfx : ⁅f, x⁆ ∈ O := by
      rw [← commutatorElement_inv]
      exact O.inv_mem hxO
    refine ⟨hxinvN, ?_⟩
    rw [commutatorElement_inv_left]
    simpa using (Subgroup.mem_normalizer_iff.mp hxinvN (⁅f, x⁆)).1 hfx

private theorem r888cb_commutator_mem_of_mem_sup {G : Type} [Group G] [Finite G]
    {D : Data G} {L P : Subgroup G} (ctx : r888s_Ctx D L P) {c f : G}
    (hc : c ∈ centralizerBar P L) (hfL : f ∈ L)
    (hfcomm : ∀ z ∈ ZOf (P ⊓ L), ⁅z, f⁆ ∈ CFSG.Open.pCoreOf 2 L) :
    ∀ x ∈ ZOf (P ⊓ L) ⊔ Subgroup.zpowers c, ⁅x, f⁆ ∈ CFSG.Open.pCoreOf 2 L := by
  have hcNL : c ∈ Subgroup.normalizer (L : Set G) :=
    r888s_norm ctx ((ctx.hset.sylow).le (centralizerBar_le P L hc))
  have hcNO : c ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 L : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (r := 2) L hcNL
  have hZS : ZOf (P ⊓ L) ≤ r888cb_fixMod (CFSG.Open.pCoreOf 2 L) f := by
    intro z hz
    exact ⟨(CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) L)
      ((r888s_ZOf_le (P ⊓ L)).trans (inf_le_right : P ⊓ L ≤ L) hz), hfcomm z hz⟩
  have hcS : c ∈ r888cb_fixMod (CFSG.Open.pCoreOf 2 L) f :=
    ⟨hcNO, (mem_centralizerBar_iff.mp hc).2 f hfL⟩
  have hsup : ZOf (P ⊓ L) ⊔ Subgroup.zpowers c ≤
      r888cb_fixMod (CFSG.Open.pCoreOf 2 L) f :=
    sup_le hZS (Subgroup.zpowers_le.mpr hcS)
  intro x hx
  exact (hsup hx).2

private theorem r888s_step_claimB {G : Type} [Group G] [Finite G] {D : Data G}
    {L P : Subgroup G} (ctx : r888s_Ctx D L P) {c : G} (hc : c ∈ centralizerBar P L) :
    ∀ h : G, (ZOf (P ⊓ L)).map (MulAut.conj h).toMonoidHom ≤
        ZOf (P ⊓ L) ⊔ Subgroup.zpowers c →
      (ZOf (P ⊓ L)).map (MulAut.conj h).toMonoidHom = ZOf (P ⊓ L) := by
  intro h hW
  have hsupP : ZOf (P ⊓ L) ⊔ Subgroup.zpowers c ≤ P :=
    sup_le (r888s_ZOf_le_P inf_le_left) (Subgroup.zpowers_le.mpr (centralizerBar_le P L hc))
  by_cases hh : h ∈ D.M
  · have hWP : (ZOf (P ⊓ L)).map (MulAut.conj h).toMonoidHom ≤ P := hW.trans hsupP
    have hWL : (ZOf (P ⊓ L)).map (MulAut.conj h).toMonoidHom ≤ L := by
      have hmap : (ZOf (P ⊓ L)).map (MulAut.conj h).toMonoidHom ≤
          L.map (MulAut.conj h).toMonoidHom :=
        Subgroup.map_mono ((r888s_ZOf_le (P ⊓ L)).trans (inf_le_right : P ⊓ L ≤ L))
      have hLmap : L.map (MulAut.conj h).toMonoidHom = L :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (r888s_norm ctx hh)
      rwa [hLmap] at hmap
    exact (ctx.h886 L P ctx.hset).2.2.1 h hh (le_inf hWP hWL)
  · obtain ⟨f, hfL, hf5, hfcomm⟩ := r888s_step_five_L ctx
    have hcomm : ∀ w ∈ (ZOf (P ⊓ L)).map (MulAut.conj h).toMonoidHom,
        ⁅w, f⁆ ∈ CFSG.Open.pCoreOf 2 L :=
      fun w hw => r888cb_commutator_mem_of_mem_sup ctx hc hfL hfcomm w (hW hw)
    have hWM : (ZOf (P ⊓ L)).map (MulAut.conj h).toMonoidHom ≤ D.M :=
      (hW.trans hsupP).trans (ctx.hset.sylow).le
    have hWcard : Nat.card ↥((ZOf (P ⊓ L)).map (MulAut.conj h).toMonoidHom) = 3 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj h).injective, (ctx.h886 L P ctx.hset).1]
    have hW3 : IsPGroup 3 ((ZOf (P ⊓ L)).map (MulAut.conj h).toMonoidHom) :=
      IsPGroup.of_card (n := 1) (by rw [hWcard]; norm_num)
    have h5 := r888s_step_K5 ctx ((ZOf (P ⊓ L)).map (MulAut.conj h).toMonoidHom)
      hWM hW3 f (r888s_le ctx hfL) hf5 hcomm
    exact absurd h5 (r888s_step_5prime ctx h hh)

private theorem r888rep_P_le_centralizer
    {G : Type} [Group G] [Finite G] {D : Data G} {L P : Subgroup G} (ctx : r888s_Ctx D L P) :
    P ≤ Subgroup.centralizer (ZOf (P ⊓ L) : Set G) := by
  obtain ⟨hP, hC, -⟩ := r888s_step_P_decomp ctx
  refine hP.trans (sup_le ?_ ?_)
  · intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp hz.2 q hq).symm
  · intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (hC c hc z hz.1).symm

private theorem r888rep_sylow_centralizer
    {G : Type} [Group G] [Finite G] {D : Data G} {L P : Subgroup G} (ctx : r888s_Ctx D L P) :
    IsSylowOf 3 P (Subgroup.centralizer (ZOf (P ⊓ L) : Set G)) :=
  IsSylowOf.of_le ctx.hset.sylow (r888rep_P_le_centralizer ctx)
    ((Subgroup.centralizer_le_normalizer (ZOf (P ⊓ L) : Set G)).trans
      (ctx.h887 L P ctx.hset))

private theorem r888rep_A0_le_centralizer {G : Type} [Group G] {L P : Subgroup G} {g : G}
    {A : Subgroup G}
    (hAY : A ≤ Subgroup.centralizer
      (((ZOf (P ⊓ L)).map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) :
    A.map (MulAut.conj g⁻¹).toMonoidHom ≤
      Subgroup.centralizer (ZOf (P ⊓ L) : Set G) := by
  intro a ha
  obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hgz : MulAut.conj g z ∈
      ((ZOf (P ⊓ L)).map (MulAut.conj g).toMonoidHom : Subgroup G) :=
    Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hz
  have hcomm := (Subgroup.mem_centralizer_iff.mp (hAY ha')) (MulAut.conj g z) hgz
  simp only [MulAut.conj_apply] at hcomm
  have hcomm' : z * (g⁻¹ * a' * g) = (g⁻¹ * a' * g) * z := by
    calc z * (g⁻¹ * a' * g)
        = g⁻¹ * ((g * z * g⁻¹) * a') * g := by group
      _ = g⁻¹ * (a' * (g * z * g⁻¹)) * g := by rw [hcomm]
      _ = (g⁻¹ * a' * g) * z := by group
  simpa [MulAut.conj_apply] using hcomm'

private theorem r888rep_exists_k
    {G : Type} [Group G] [Finite G] {D : Data G} {L P : Subgroup G}
    (ctx : r888s_Ctx D L P) {A : Subgroup G} (hA : IsPGroup 3 A)
    (hAC : A ≤ Subgroup.centralizer (ZOf (P ⊓ L) : Set G)) :
    ∃ k ∈ Subgroup.centralizer (ZOf (P ⊓ L) : Set G),
      A ≤ P.map (MulAut.conj k).toMonoidHom := by
  let Cz := Subgroup.centralizer (ZOf (P ⊓ L) : Set G)
  have hAsub : IsPGroup 3 (A.subgroupOf Cz) := hA.comap_subtype
  obtain ⟨S, hAS⟩ := hAsub.exists_le_sylow
  have hS : IsSylowOf 3 ((S : Subgroup ↥Cz).map Cz.subtype) Cz := ⟨S, rfl⟩
  obtain ⟨k, hkCz, hconj⟩ :=
    IsSylowOf.exists_mem_conj (r888rep_sylow_centralizer ctx) hS
  refine ⟨k, hkCz, ?_⟩
  intro a ha
  have haS : a ∈ (S : Subgroup ↥Cz).map Cz.subtype := by
    refine ⟨⟨a, hAC ha⟩, hAS ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    exact ha
  exact Subgroup.mem_map.mpr ⟨k⁻¹ * a * k, (hconj a).mp haS, by
    show k * (k⁻¹ * a * k) * k⁻¹ = a
    group⟩

private theorem r888s_step_repair
    {G : Type} [Group G] [Finite G] {D : Data G}
    {L P : Subgroup G} (ctx : r888s_Ctx D L P) {g : G} {A : Subgroup G} (hA : IsPGroup 3 A)
    (hAY : A ≤ centralizer
      (((ZOf (P ⊓ L)).map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) :
    ∃ g' : G, (ZOf (P ⊓ L)).map (MulAut.conj g').toMonoidHom =
        (ZOf (P ⊓ L)).map (MulAut.conj g).toMonoidHom ∧
      A ≤ P.map (MulAut.conj g').toMonoidHom := by
  have hA0 : A.map (MulAut.conj g⁻¹).toMonoidHom ≤
      Subgroup.centralizer (ZOf (P ⊓ L) : Set G) :=
    r888rep_A0_le_centralizer hAY
  have hA0p : IsPGroup 3 (A.map (MulAut.conj g⁻¹).toMonoidHom) := hA.map _
  obtain ⟨k, hkCz, hk⟩ := r888rep_exists_k ctx hA0p hA0
  have hcomp : (MulAut.conj (g * k)).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp (MulAut.conj k).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hkZ : (ZOf (P ⊓ L)).map (MulAut.conj k).toMonoidHom = ZOf (P ⊓ L) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((Subgroup.centralizer_le_normalizer (ZOf (P ⊓ L) : Set G)) hkCz)
  refine ⟨g * k, ?_, ?_⟩
  · rw [hcomp, ← Subgroup.map_map, hkZ]
  · have hAeq : A = (A.map (MulAut.conj g⁻¹).toMonoidHom).map
        (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.map_map]
      have hc : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
          MonoidHom.id G := by
        ext x
        simp [MulAut.conj_apply, mul_assoc]
      rw [hc, Subgroup.map_id]
    rw [hAeq]
    calc (A.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom
        ≤ (P.map (MulAut.conj k).toMonoidHom).map (MulAut.conj g).toMonoidHom :=
          Subgroup.map_mono hk
      _ = P.map (MulAut.conj (g * k)).toMonoidHom := by
          rw [Subgroup.map_map, ← hcomp]

private theorem r888cnj_centralizer_conj {G : Type} [Group G] (Q : Subgroup G) (g : G) :
    Subgroup.centralizer ((Q.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) =
      (Subgroup.centralizer (Q : Set G)).map (MulAut.conj g).toMonoidHom := by
  ext x
  constructor
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · change ∀ y ∈ (Q : Set G), y * (g⁻¹ * x * g) = (g⁻¹ * x * g) * y
      intro y hy
      have hy' : g * y * g⁻¹ ∈ Q.map (MulAut.conj g).toMonoidHom :=
        Subgroup.mem_map.mpr ⟨y, hy, by simp [MulAut.conj_apply]⟩
      have h : (g * y * g⁻¹) * x = x * (g * y * g⁻¹) := hx (g * y * g⁻¹) hy'
      calc y * (g⁻¹ * x * g) = g⁻¹ * ((g * y * g⁻¹) * x) * g := by group
        _ = g⁻¹ * (x * (g * y * g⁻¹)) * g := by rw [h]
        _ = (g⁻¹ * x * g) * y := by group
    · change g * (g⁻¹ * x * g) * g⁻¹ = x
      group
  · rintro ⟨a, ha, rfl⟩
    change ∀ z ∈ ((Q.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G),
      z * ((MulAut.conj g).toMonoidHom a) = ((MulAut.conj g).toMonoidHom a) * z
    intro z hz
    obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp hz
    rw [← hyz]
    change (g * y * g⁻¹) * (g * a * g⁻¹) = (g * a * g⁻¹) * (g * y * g⁻¹)
    calc (g * y * g⁻¹) * (g * a * g⁻¹) = g * (y * a) * g⁻¹ := by group
      _ = g * (a * y) * g⁻¹ := by rw [ha y hy]
      _ = (g * a * g⁻¹) * (g * y * g⁻¹) := by group

private theorem r888cnj_conj_comp_inv {G : Type} [Group G] (g : G) :
    ((MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom) = MonoidHom.id G := by
  ext x; simp [MulAut.conj_apply, mul_assoc]

private theorem r888cnj_conj_inv_comp {G : Type} [Group G] (g : G) :
    ((MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom) = MonoidHom.id G := by
  ext x; simp [MulAut.conj_apply, mul_assoc]

private theorem r888cnj_conj_axis
    {G : Type} [Group G] [Finite G] {D : Data G}
    {L P : Subgroup G} (ctx : r888s_Ctx D L P) {c g : G}
    (hc : c ∈ centralizerBar P L) (hc3 : orderOf c = 3)
    (hgZ : (ZOf (P ⊓ L)).map (MulAut.conj g).toMonoidHom ≠ ZOf (P ⊓ L))
    {A₀ : Subgroup G} (hA₀P : A₀ ≤ P) (hA₀ : IsElemAbelian 3 A₀) (hA₀c : Nat.card A₀ = 27) :
    (P ⊓ L).map (MulAut.conj g).toMonoidHom ≤
        normalizer ((A₀.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) ∧
      ⁅A₀.map (MulAut.conj g).toMonoidHom, (P ⊓ L).map (MulAut.conj g).toMonoidHom⁆ =
        (ZOf (P ⊓ L)).map (MulAut.conj g).toMonoidHom ∧
      A₀.map (MulAut.conj g).toMonoidHom ⊓ centralizer
          (((P ⊓ L).map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) =
        (ZOf (P ⊓ L) ⊔ Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom ∧
      ¬ ZOf (P ⊓ L) ≤ (ZOf (P ⊓ L) ⊔ Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨-, hBA₀, hPA₀⟩ := r888s_step_E27 ctx hc hc3 hA₀P hA₀ hA₀c
  obtain ⟨hA₀Q, hA₀C, -⟩ := r888s_step_axis ctx hc hc3 hA₀P hA₀ hA₀c
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (Subgroup.map_mono (inf_le_left.trans hPA₀)).trans (Subgroup.le_normalizer_map _)
  · have hmc : ⁅A₀.map (MulAut.conj g).toMonoidHom, (P ⊓ L).map (MulAut.conj g).toMonoidHom⁆
        = (⁅A₀, P ⊓ L⁆).map (MulAut.conj g).toMonoidHom :=
      (Subgroup.map_commutator (H₁ := A₀) (H₂ := P ⊓ L)
        (f := (MulAut.conj g).toMonoidHom)).symm
    rw [hmc, hA₀Q]
  · rw [r888cnj_centralizer_conj (P ⊓ L) g]
    rw [← Subgroup.map_inf_eq A₀ (Subgroup.centralizer ((P ⊓ L : Subgroup G) : Set G))
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective, hA₀C]
  · intro h
    have h1 : (ZOf (P ⊓ L)).map (MulAut.conj g⁻¹).toMonoidHom ≤
        ZOf (P ⊓ L) ⊔ Subgroup.zpowers c := by
      have hmono := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) h
      calc (ZOf (P ⊓ L)).map (MulAut.conj g⁻¹).toMonoidHom
          ≤ (((ZOf (P ⊓ L)) ⊔ Subgroup.zpowers c).map
              (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom := hmono
        _ = ((ZOf (P ⊓ L)) ⊔ Subgroup.zpowers c).map
              ((MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom) := by
              rw [Subgroup.map_map]
        _ = ((ZOf (P ⊓ L)) ⊔ Subgroup.zpowers c).map (MonoidHom.id G) := by
              rw [r888cnj_conj_inv_comp]
        _ = ZOf (P ⊓ L) ⊔ Subgroup.zpowers c := by rw [Subgroup.map_id]
    have h2 : (ZOf (P ⊓ L)).map (MulAut.conj g⁻¹).toMonoidHom = ZOf (P ⊓ L) :=
      r888s_step_claimB ctx hc g⁻¹ h1
    have h3 : (ZOf (P ⊓ L)).map (MulAut.conj g).toMonoidHom = ZOf (P ⊓ L) := by
      have hh := congrArg (fun X : Subgroup G => X.map (MulAut.conj g).toMonoidHom) h2
      rw [Subgroup.map_map, r888cnj_conj_comp_inv, Subgroup.map_id] at hh
      exact hh.symm
    exact hgZ h3

private theorem r888s_step_conj
    {G : Type} [Group G] [Finite G] {D : Data G}
    {L P : Subgroup G} (ctx : r888s_Ctx D L P) {c g : G}
    (hc : c ∈ centralizerBar P L) (hc3 : orderOf c = 3)
    (hgZ : (ZOf (P ⊓ L)).map (MulAut.conj g).toMonoidHom ≠ ZOf (P ⊓ L))
    {A : Subgroup G} (hAP : A ≤ P.map (MulAut.conj g).toMonoidHom) (hA : IsElemAbelian 3 A)
    (hAc : Nat.card A = 27) :
    (P ⊓ L).map (MulAut.conj g).toMonoidHom ≤ normalizer (A : Set G) ∧
      ⁅A, (P ⊓ L).map (MulAut.conj g).toMonoidHom⁆ =
        (ZOf (P ⊓ L)).map (MulAut.conj g).toMonoidHom ∧
      A ⊓ centralizer (((P ⊓ L).map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) =
        (ZOf (P ⊓ L) ⊔ Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom ∧
      ¬ ZOf (P ⊓ L) ≤ (ZOf (P ⊓ L) ⊔ Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom := by
  have hA₀P : A.map (MulAut.conj g⁻¹).toMonoidHom ≤ P := by
    have h := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hAP
    rwa [Subgroup.map_map, r888cnj_conj_inv_comp, Subgroup.map_id] at h
  have hA₀ : IsElemAbelian 3 (A.map (MulAut.conj g⁻¹).toMonoidHom) :=
    hA.map (MulAut.conj g⁻¹).toMonoidHom
  have hA₀c : Nat.card (A.map (MulAut.conj g⁻¹).toMonoidHom) = 27 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hAc]
  have hAeq : (A.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = A := by
    rw [Subgroup.map_map, r888cnj_conj_comp_inv, Subgroup.map_id]
  have h := r888cnj_conj_axis ctx hc hc3 hgZ hA₀P hA₀ hA₀c
  rwa [hAeq] at h

private theorem r888s69_centralizer_ne_top {G : Type} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G) (hnonab : ∃ a b : G, a * b ≠ b * a) {c : G}
    (hc1 : c ≠ 1) : Subgroup.centralizer ({c} : Set G) ≠ ⊤ := by
  intro htop
  have hcenter : c ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer ({c} : Set G) := by
      rw [htop]; exact Subgroup.mem_top g
    exact ((Subgroup.mem_centralizer_iff.mp hg) c (Set.mem_singleton c)).symm
  have hbot : Subgroup.center G = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnonab
      have ha : a ∈ Subgroup.center G := by rw [h]; exact Subgroup.mem_top a
      exact hab (Subgroup.mem_center_iff.mp ha b).symm
  refine hc1 ?_
  have hmem : c ∈ (⊥ : Subgroup G) := by simpa [hbot] using hcenter
  exact Subgroup.mem_bot.mp hmem

private theorem r888s_step_869 {G : Type} [Group G] [Finite G] {D : Data G}
    {L P : Subgroup G} (ctx : r888s_Ctx D L P) {c : G}
    (hc : c ∈ centralizerBar P L) (hc3 : orderOf c = 3) :
    centralizer ({c} : Set G) ≤ D.M := by
  have hc1 : c ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hc3
    norm_num at hc3
  have hAcard : Nat.card (Subgroup.zpowers c) = 3 := by
    rw [Nat.card_zpowers, hc3]
  have hAc : ∀ a ∈ Subgroup.zpowers c, UC22.CentralizesBar a L := by
    intro a ha
    refine UC22.uc22p21d_centralizesBar_iff.mpr ?_
    intro l hl
    have haC : a ∈ centralizerBar P L := (Subgroup.zpowers_le.mpr hc) ha
    have hcomm : ⁅a, l⁆ ∈ CFSG.Open.pCoreOf 2 L := (mem_centralizerBar_iff.mp haC).2 l hl
    simpa only [commutatorElement_def] using hcomm
  have hXO : (L ⊓ centralizer ((Subgroup.zpowers c : Subgroup G) : Set G)) ⊔
      CFSG.Open.pCoreOf 2 L = L :=
    UC22.uc22p21d_sup_pCore_eq Nat.prime_three (by norm_num) hAcard hAc
  have hthin : ¬ UC22.F08.Thin8 L := by
    intro h
    have hle : CFSG.Open.pRank 5 L ≤ 1 := h 5 Nat.prime_five (by norm_num)
    rw [r888s_pRank5L ctx] at hle
    norm_num at hle
  have hN : UC22.calNOf
      (L ⊓ centralizer ((Subgroup.zpowers c : Subgroup G) : Set G)) = {D.M} :=
    ctx.h869 L (Or.inl ctx.hset.mem)
      (L ⊓ centralizer ((Subgroup.zpowers c : Subgroup G) : Set G)) inf_le_left hXO hthin
  have hcent_eq : Subgroup.centralizer ((Subgroup.zpowers c : Subgroup G) : Set G) =
      Subgroup.centralizer ({c} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hne : Subgroup.centralizer ({c} : Set G) ≠ ⊤ :=
    r888s69_centralizer_ne_top D.standing.simple D.standing.nonab hc1
  obtain ⟨N, hNcoat, hNle⟩ := (IsCoatomic.eq_top_or_exists_le_coatom
    (Subgroup.centralizer ({c} : Set G))).resolve_left hne
  have hXle : L ⊓ centralizer ((Subgroup.zpowers c : Subgroup G) : Set G) ≤ N :=
    (inf_le_right.trans (le_of_eq hcent_eq)).trans hNle
  have hNmem : N ∈ UC22.calNOf
      (L ⊓ centralizer ((Subgroup.zpowers c : Subgroup G) : Set G)) := ⟨hNcoat, hXle⟩
  rw [hN, Set.mem_singleton_iff] at hNmem
  rwa [hNmem] at hNle

private theorem r888fin_sylow_transport {G : Type} [Group G] [Finite G] {D : Data G}
    {L P : Subgroup G} (ctx : r888s_Ctx D L P) {g : G}
    (hQg : (P ⊓ L).map (MulAut.conj g).toMonoidHom ≤ D.M) :
    ∃ m ∈ D.M, (P ⊓ L).map (MulAut.conj (m * g)).toMonoidHom ≤ P := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQp : IsPGroup 3 ↥(P ⊓ L) := (r888s_sylowQ ctx).isPGroup
  have hQgp : IsPGroup 3 ((P ⊓ L).map (MulAut.conj g).toMonoidHom) :=
    hQp.map (MulAut.conj g).toMonoidHom
  have hQgpM : IsPGroup 3 (((P ⊓ L).map (MulAut.conj g).toMonoidHom).subgroupOf D.M) :=
    hQgp.comap_subtype
  obtain ⟨S, hQS⟩ := hQgpM.exists_le_sylow
  have hS : IsSylowOf 3 ((S : Subgroup ↥D.M).map D.M.subtype) D.M := ⟨S, rfl⟩
  obtain ⟨k, hkM, hconj⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj ctx.hset.sylow hS
  have hQkP : ((P ⊓ L).map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj k⁻¹).toMonoidHom ≤ P := by
    rintro _ ⟨y, hy, rfl⟩
    have hyM : y ∈ D.M := hQg hy
    have hyS : y ∈ (S : Subgroup ↥D.M).map D.M.subtype :=
      ⟨⟨y, hyM⟩, hQS (Subgroup.mem_subgroupOf.mpr hy), rfl⟩
    simpa [MulAut.conj_apply] using (hconj y).mp hyS
  have hcomp : (MulAut.conj k⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (k⁻¹ * g)).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  refine ⟨k⁻¹, D.M.inv_mem hkM, ?_⟩
  rw [← hcomp, ← Subgroup.map_map]
  exact hQkP

private theorem r888fin_Z_le_of_conj
    {G : Type} [Group G] [Finite G] {D : Data G}
    {L P : Subgroup G} (ctx : r888s_Ctx D L P) {m : G}
    (hmP : (P ⊓ L).map (MulAut.conj m).toMonoidHom ≤ P) :
    (ZOf (P ⊓ L)).map (MulAut.conj m).toMonoidHom ≤ ZOf (P ⊓ L) := by
  conv_lhs => rw [← r888s_commutator_Q ctx]
  rw [Subgroup.map_commutator]
  exact (Subgroup.commutator_mono hmP hmP).trans (r888s_step_C_cyclic ctx).2

private theorem r888s_step_final
    {G : Type} [Group G] [Finite G] {D : Data G}
    {L P : Subgroup G} (ctx : r888s_Ctx D L P) {g : G}
    (hQg : (P ⊓ L).map (MulAut.conj g).toMonoidHom ≤ D.M) : g ∈ D.M := by
  obtain ⟨m, hmM, hmP⟩ := r888fin_sylow_transport ctx hQg
  have hZle : (ZOf (P ⊓ L)).map (MulAut.conj (m * g)).toMonoidHom ≤ ZOf (P ⊓ L) :=
    r888fin_Z_le_of_conj ctx hmP
  have hcard : Nat.card ((ZOf (P ⊓ L)).map (MulAut.conj (m * g)).toMonoidHom) =
      Nat.card (ZOf (P ⊓ L)) :=
    Subgroup.card_map_of_injective (MulAut.conj (m * g)).injective
  have hZeq : (ZOf (P ⊓ L)).map (MulAut.conj (m * g)).toMonoidHom = ZOf (P ⊓ L) :=
    Subgroup.eq_of_le_of_card_ge hZle (by rw [hcard])
  have hmgN : m * g ∈ Subgroup.normalizer ((ZOf (P ⊓ L) : Subgroup G) : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hZeq
  have hmgM : m * g ∈ D.M := ctx.h887 L P ctx.hset hmgN
  have hg_eq : g = m⁻¹ * (m * g) := by group
  rw [hg_eq]
  exact D.M.mul_mem (D.M.inv_mem hmM) hmgM

private theorem r888s_map_conj_one {G : Type} [Group G] (X : Subgroup G) :
    X.map (MulAut.conj (1 : G)).toMonoidHom = X := by
  have hc : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
    ext z; simp
  rw [hc, Subgroup.map_id]

private theorem r888s_hfusion
    {G : Type} [Group G] [Finite G] {D : Data G} {L P : Subgroup G} (ctx : r888s_Ctx D L P) :
    ∀ g : G, (ZOf (P ⊓ L)).map (MulAut.conj g).toMonoidHom ≤ P →
      ∃ m ∈ D.M, (ZOf (P ⊓ L)).map (MulAut.conj g).toMonoidHom =
        (ZOf (P ⊓ L)).map (MulAut.conj m).toMonoidHom := by
  intro g hY
  by_contra hcon
  have hbad : ∀ m ∈ D.M, (ZOf (P ⊓ L)).map (MulAut.conj g).toMonoidHom ≠
      (ZOf (P ⊓ L)).map (MulAut.conj m).toMonoidHom := fun m hm h => hcon ⟨m, hm, h⟩
  obtain ⟨q, c, hq, hc, hq3, hqZ, hc3, -, hYqc⟩ := r888s_step_generator ctx hY hbad
  obtain ⟨A, hAP, hAel, hAc, hqcA⟩ := r888s_step_NP ctx hq hc hq3 hqZ hc3
  obtain ⟨hB9, hBA, hPA⟩ := r888s_step_E27 ctx hc hc3 hAP hAel hAc
  obtain ⟨hAQ, hAB, hAC⟩ := r888s_step_axis ctx hc hc3 hAP hAel hAc
  have hYA : (ZOf (P ⊓ L)).map (MulAut.conj g).toMonoidHom ≤ A := by
    rw [hYqc]
    exact Subgroup.zpowers_le.mpr hqcA
  have hAY : A ≤ centralizer
      (((ZOf (P ⊓ L)).map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact IsElemAbelian.comm hAel (hYA hy) ha
  obtain ⟨g', hg'Y, hAPg'⟩ :=
    r888s_step_repair ctx (IsPGroup.of_card (n := 3) (by rw [hAc]; norm_num)) hAY
  rw [← hg'Y] at hbad hYA
  have hne : (ZOf (P ⊓ L)).map (MulAut.conj g').toMonoidHom ≠ ZOf (P ⊓ L) := fun h =>
    hbad 1 D.M.one_mem (by rw [h, r888s_map_conj_one])
  obtain ⟨hQA', hAQ', hAB', hZB'⟩ := r888s_step_conj ctx hc hc3 hne hAPg' hAel hAc
  have hZc : Nat.card (ZOf (P ⊓ L)) = 3 := (ctx.h886 L P ctx.hset).1
  have hYc : Nat.card ((ZOf (P ⊓ L)).map (MulAut.conj g').toMonoidHom) = 3 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g').injective, hZc]
  have hB9' : Nat.card ((ZOf (P ⊓ L) ⊔ Subgroup.zpowers c).map
      (MulAut.conj g').toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g').injective, hB9]
  have hYB : ¬ (ZOf (P ⊓ L)).map (MulAut.conj g').toMonoidHom ≤
      ZOf (P ⊓ L) ⊔ Subgroup.zpowers c := fun h => hne (r888s_step_claimB ctx hc g' h)
  have hQA : P ⊓ L ≤ normalizer (A : Set G) := inf_le_left.trans hPA
  obtain ⟨t, htH, -, htinv, -, htcent, htU⟩ := exists_two_element_of_transvections hAel hAc
    hQA hQA' hAQ hAQ' hAB hAB' hZc hYc hB9 hB9' le_sup_left (Subgroup.map_mono le_sup_left)
    hYB hZB'
  have htNZ : t ∈ normalizer ((ZOf (P ⊓ L) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_
      (by rw [Subgroup.card_map_of_injective (MulAut.conj t).injective])
    rintro _ ⟨x, hx, rfl⟩
    change t * x * t⁻¹ ∈ ZOf (P ⊓ L)
    rw [htinv x (Subgroup.mem_sup_left hx)]
    exact (ZOf (P ⊓ L)).inv_mem hx
  have htM : t ∈ D.M := ctx.h887 L P ctx.hset htNZ
  have htA : t ∈ normalizer (A : Set G) := sup_le hQA hQA' htH
  have htC : t ∈ normalizer ((centralizerBar D.M L : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (centralizerBar_le D.M L)).mp
      (centralizerBar_normal (r888s_norm ctx)) htM
  have htc : t ∈ normalizer ((Subgroup.zpowers c : Subgroup G) : Set G) := by
    rw [← hAC]
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨htA, htC⟩
  rcases htU (Subgroup.zpowers c) (le_sup_right.trans hBA) (by rw [Nat.card_zpowers, hc3])
      htc with hcZY | hcCt
  · apply hYB
    have hZY : Nat.card ↥(ZOf (P ⊓ L) ⊔ (ZOf (P ⊓ L)).map (MulAut.conj g').toMonoidHom) = 9 :=
      card_sup_eq_nine_of_card_three_of_ne hZc hYc (Ne.symm hne)
        (fun x hx y hy => IsElemAbelian.comm hAel (hBA (Subgroup.mem_sup_left hx)) (hYA hy))
    rw [Subgroup.eq_of_le_of_card_ge (sup_le le_sup_left hcZY) (by rw [hZY, hB9])]
    exact le_sup_right
  · have hcCt' : c ∈ A ⊓ centralizer ({t} : Set G) := by
      rw [← hcCt]
      exact Subgroup.mem_zpowers c
    have hQc : (P ⊓ L).map (MulAut.conj g').toMonoidHom ≤ centralizer ({c} : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      rintro y rfl
      exact ((Subgroup.mem_centralizer_iff.mp (htcent hcCt')) x (Subgroup.mem_sup_right hx)).symm
    exact hbad g' (r888s_step_final ctx (hQc.trans (r888s_step_869 ctx hc hc3))) rfl

theorem r888_of_inputs
    {G : Type} [Group G] [Finite G] (D : Data G) (hSg : SigmaStd D) (h869 : R869 D)
    (h882 : R882 D) (h885 : R885 D) (h886 : R886 D) (h887 : R887 D)
    (hIns : List880PRankInspection) (hJ2 : J2FivePRank) : R888 D := by
  intro L P hset
  refine mem_uniqueSet_of_fusion_control hset.sylow (r888s_ZOf_le_P inf_le_left)
    (h886 L P hset).1 (h887 L P hset) ?_
  exact r888s_hfusion ⟨hset, hSg, h869, h882, h885, h886, h887, hIns, hJ2⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
