module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftySix
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftyNine
public import CFSG.Quasithin.Vol2.F134Orders
public import CFSG.SignalizerFunctorTheorem.McBride.Models.Suzuki.Arith
public import CFSG.GroupTheory.FittingCentralizerCoprime
public import CFSG.GroupTheory.CharacteristicExponentClassTwo
public import CFSG.GroupTheory.CentralExtensionPGroup
public import CFSG.GroupTheory.OddPGroupNoncyclicChar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F13
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.RankThree.PartOne (pElementSubgroup)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem dvd_card_bar2_of_isSz_sub_one {L : Subgroup G} {p n : ℕ} (h : IsSz (Bar2 L) n)
    (hdvd : p ∣ 2 ^ n - 1) : p ∣ Nat.card (Bar2 L) := by
  have hsz : CFSG.Blueprint.SuzukiModel (Bar2 L) 2 n := by
    have h' := h
    unfold IsSz CFSG.Blueprint.LieModel at h'
    rcases h' with h1 | h2 | h3 | h4
    · exact absurd h1.1 (by decide)
    · exact absurd h2.2.1 (by decide)
    · exact absurd h3.2.1 (by decide)
    · exact h4.2.2
  obtain ⟨-, a, ha, K, hfield, hfinite, hf, hKcard, ⟨e⟩⟩ := hsz
  letI := hfield
  letI := hfinite
  have hKcard' : Nat.card K = 2 ^ (2 * a + 1) := by rw [← hf]; exact hKcard
  have hcard : Nat.card (Bar2 L) =
      Nat.card (CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup a) := by
    rw [Nat.card_congr e.toEquiv,
      Nat.card_congr
        (CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup
          hKcard').toEquiv]
  have hdvd' : p ∣ 2 ^ (2 * a + 1) - 1 := by rwa [hf] at hdvd
  rw [hcard, CFSG.SectionRank.card_suzukiMatrixGroup a ha]
  exact dvd_mul_of_dvd_right hdvd' _

theorem conjSetOf_eq_of_isStronglyPEmbedded {D : Data G} {p : ℕ}
    (hstr : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M) {X : Subgroup G}
    (hXM : X ≤ D.M) (hXcard : Nat.card X = p) :
    conjSetOf (⊤ : Subgroup G) X ∩ {Y : Subgroup G | Y ≤ D.M} = conjSetOf D.M X := by
  apply le_antisymm
  · rintro Y ⟨⟨g, -, rfl⟩, hY⟩
    have hcardY : Nat.card (X.map (MulAut.conj g).toMonoidHom) = p := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hXcard]
    have hgM : g ∈ D.M := by
      by_contra hg
      have hle : X.map (MulAut.conj g).toMonoidHom ≤
          D.M ⊓ D.M.map (MulAut.conj g).toMonoidHom :=
        le_inf hY (Subgroup.map_mono hXM)
      have hdvd : p ∣ Nat.card (D.M ⊓ D.M.map (MulAut.conj g).toMonoidHom :
          Subgroup G) := hcardY ▸ Subgroup.card_dvd_of_le hle
      exact (hstr.2.2 g hg) hdvd
    exact ⟨g, hgM, rfl⟩
  · rintro Y ⟨m, hm, rfl⟩
    refine ⟨⟨m, Subgroup.mem_top m, rfl⟩, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact D.M.mul_mem (D.M.mul_mem hm (hXM hx)) (D.M.inv_mem hm)

theorem opp_pCoreOf_two_eq_bot {M : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Opp p (CFSG.Open.pCoreOf 2 M) = ⊥ := by
  by_contra hne
  obtain ⟨s, hs, hsord⟩ :=
    s13_exists_orderOf_of_pElementSubgroup_ne_bot hp (by simpa [Opp] using hne)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsH : s ∈ CFSG.Open.pCoreOf 2 M := (s13_Bar13_opp_le p (CFSG.Open.pCoreOf 2 M)) hs
  obtain ⟨m, hm⟩ := IsPGroup.iff_orderOf.mp
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M) ⟨s, hsH⟩
  have h2 : orderOf s = 2 ^ m := (Subgroup.orderOf_coe _).trans hm
  rw [hsord] at h2
  have hpdvd : p ∣ 2 ^ m := by rw [← h2]
  have h2dvd : p ∣ 2 := Nat.Prime.dvd_of_dvd_pow hp hpdvd
  rcases (Nat.dvd_prime Nat.prime_two).mp h2dvd with h1 | h2
  · exact hp.ne_one h1
  · exact hp2 h2

theorem centSection_bot_bot (M : Subgroup G) : centSection M ⊥ ⊥ = M := by
  ext m
  constructor
  · intro hm
    exact centSection_le M ⊥ ⊥ hm
  · intro hm
    refine ⟨hm, ?_, ?_, ?_⟩
    · rw [Subgroup.normalizer_eq_top_iff.mpr Subgroup.normal_bot]
      exact Subgroup.mem_top _
    · rw [Subgroup.normalizer_eq_top_iff.mpr Subgroup.normal_bot]
      exact Subgroup.mem_top _
    · intro a ha
      rw [Subgroup.mem_bot] at ha
      rw [ha]
      simp

theorem layer_eq_bot_of_three_not_mem {D : Data G} {V₀ V : Subgroup G} {p : ℕ}
    (hp : Hyp1754 D p) (hThin : ThinList13) (h3 : 3 ∉ piSet D.M)
    (h55 : R17_55At D V₀ V)
    (hstrong : ∀ q ∈ piSet D.M, q ≠ 2 → q ≠ 5 →
      CFSG.RankThree.PartOne.IsStronglyPEmbedded q D.M) :
    CFSG.layer (Bar2 D.M) = ⊥ := by
  classical
  by_contra hne
  have hex : ∃ J : Subgroup (Bar2 D.M), CFSG.IsComponent J ∧ J ≠ ⊥ := by
    by_contra h
    push Not at h
    exact hne (by
      rw [s13_Layer13_layer_eq_iSup]
      exact iSup₂_eq_bot.mpr fun J hJ => h J (s13_Layer13_mem_comps.mp hJ))
  obtain ⟨J, hJ, hJne⟩ := hex
  obtain ⟨L, hL, rfl⟩ := s13_exists_calC_of_component D.M hJ
  have hLbar3 : 3 ∣ Nat.card (Bar2 L) := by
    have hnormal : (barImage D.M L).Normal := s13_barImage_normal (hp.2 L hL).1
    rcases (hp.2 L hL).2 with hthin | ⟨n, hU⟩ | hL3
    · obtain ⟨-, hlist⟩ := s13_list_bar hThin D hL hthin
      rcases hlist with ⟨a, hL2⟩ | ⟨q, hq, hq2, hL2odd⟩ | ⟨a, hSz⟩ | hJ1
      · exact three_dvd_card_of_isL2Even hL2
      · exact CFSG.LocalAnalysis.UniquenessCase.UC22.three_dvd_card_of_isL2Odd
          (by have := s13_five_le_of_isL2Odd hL2odd; omega) hL2odd
      ·
        exfalso
        obtain ⟨hodd, hn3⟩ := s13_odd_three_le_of_isSz hSz
        have heven : Even (2 ^ a) := by
          cases a with
          | zero => omega
          | succ k => exact ⟨2 ^ k, by rw [pow_succ]; ring⟩
        have hodd' : Odd (2 ^ a - 1) :=
          Nat.Even.sub_odd Nat.one_le_two_pow heven odd_one
        have hgt : 2 ^ a - 1 ≠ 1 := by
          have h7 : 7 ≤ 2 ^ a - 1 := by
            have hp3 : 2 ^ 3 ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hn3
            omega
          omega
        obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd hgt
        have hr2 : r ≠ 2 := by
          intro h2
          have h2dvd : 2 ∣ 2 ^ a - 1 := h2 ▸ hrdvd
          exact (Nat.not_even_iff_odd.mpr hodd') (even_iff_two_dvd.mpr h2dvd)
        have hr5 : r ≠ 5 := by
          intro h5
          obtain ⟨m, hm⟩ := hodd
          rw [hm] at hrdvd
          exact (CFSG.SignalizerFunctorTheorem.McBride.SzModel.not_five_dvd_two_pow_sub_one m)
            (h5 ▸ hrdvd)
        have hrdvdBar : r ∣ Nat.card (Bar2 L) := dvd_card_bar2_of_isSz_sub_one hSz hrdvd
        obtain ⟨X, hXL, hXcard⟩ := s13_exists_subgroup_of_dvd_card_bar hr hrdvdBar
        have hXle : X ≤ D.M := hXL.trans (s13_le_of_mem_calC hL)
        have hrpi : r ∈ piSet D.M := by
          refine ⟨hr, ?_⟩
          rw [← hXcard]
          exact Subgroup.card_dvd_of_le hXle
        have hstr : CFSG.RankThree.PartOne.IsStronglyPEmbedded r D.M :=
          hstrong r hrpi hr2 hr5
        exact (h55 L (s13_le_of_mem_calC hL) (hp.2 L hL).1 a (Or.inr hSz) a hodd
          (dvd_rfl) r hr hrdvd X hXL hXcard)
          (conjSetOf_eq_of_isStronglyPEmbedded hstr hXle hXcard)
      · exact three_dvd_card_of_isJ1 hJ1
    · exact CFSG.Quasithin.F134.three_dvd_card_of_statedPSU_three
        (CFSG.Blueprint.LieModel.statedClassicalModel hU (by decide))
    · rw [card_bar_of_isL3 hL3]
      norm_num
  have h3L : 3 ∣ Nat.card ↥L :=
    hLbar3.trans (Subgroup.card_quotient_dvd_card (CFSG.pCore 2 ↥L))
  have h3M : 3 ∣ Nat.card D.M := h3L.trans (Subgroup.card_dvd_of_le (s13_le_of_mem_calC hL))
  exact h3 ⟨Nat.prime_three, h3M⟩

variable {G : Type} [Group G] [Finite G]

theorem exists_lift_of_normal_isPGroup (M : Subgroup G) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) {K : Subgroup (Bar2 M)} (hK : K.Normal) (hKq : IsPGroup q K) :
    ∃ Dg : Subgroup G, Dg ≤ M ∧ IsPGroup q Dg ∧ Nonempty (Dg ≃* K) ∧
      ((Dg ⊔ CFSG.Open.pCoreOf 2 M).subgroupOf M).Normal := by
  classical
  let N2 : Subgroup ↥M := CFSG.pCore 2 ↥M
  haveI : N2.Normal := CFSG.pCore_normal
  obtain ⟨k2, hk2⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup : IsPGroup 2 ↥N2)
  let π : ↥M →* Bar2 M := QuotientGroup.mk' N2
  have hcop : q.Coprime (Nat.card N2) := by
    rw [hk2]
    exact ((Nat.coprime_primes hq Nat.prime_two).2 hq2).pow_right k2
  obtain ⟨DsubM, hDsubMp, ⟨eDsub⟩, hDsup⟩ :=
    CFSG.GroupTheory.exists_isPGroup_of_coprime_kernel N2 hq hcop (K := K) hKq
  let Dg : Subgroup G := DsubM.map M.subtype
  have hsubmap : ((K.comap π).map M.subtype).subgroupOf M = K.comap π :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
  refine ⟨Dg, Subgroup.map_subtype_le _, hDsubMp.map M.subtype,
    ⟨(DsubM.equivMapOfInjective M.subtype M.subtype_injective).symm.trans eDsub⟩, ?_⟩
  rw [show Dg ⊔ CFSG.Open.pCoreOf 2 M = (DsubM ⊔ N2).map M.subtype by
      rw [Subgroup.map_sup]; rfl, hDsup, hsubmap]
  exact Subgroup.Normal.comap hK π

theorem commutator3_eq_map {X : Type*} [Group X] (H : Subgroup X) :
    ⁅⁅H, H⁆, H⁆ = Subgroup.map H.subtype
      ⁅⁅(⊤ : Subgroup ↥H), (⊤ : Subgroup ↥H)⁆, (⊤ : Subgroup ↥H)⁆ := by
  rw [Subgroup.map_commutator, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

theorem transfer_of_mulEquiv {X Y : Type*} [Group X] [Group Y] {S : Subgroup X} {T : Subgroup Y}
    (e : S ≃* T) {q : ℕ} (hnc : ¬ IsCyclic T) (hexp : ∀ y ∈ T, y ^ q = 1)
    (hcl : ⁅⁅T, T⁆, T⁆ = ⊥) :
    ¬ IsCyclic S ∧ (∀ x ∈ S, x ^ q = 1) ∧ ⁅⁅S, S⁆, S⁆ = ⊥ := by
  refine ⟨fun h => hnc (isCyclic_of_surjective e.toMonoidHom e.surjective),
    CFSG.AGLEmbedding.pow_eq_one_of_mulEquiv e hexp, ?_⟩
  have hT : ⁅⁅(⊤ : Subgroup ↥T), (⊤ : Subgroup ↥T)⁆, (⊤ : Subgroup ↥T)⁆ = ⊥ := by
    rw [commutator3_eq_map] at hcl
    exact (Subgroup.map_eq_bot_iff_of_injective _ T.subtype_injective).mp hcl
  have hS : ⁅⁅(⊤ : Subgroup ↥S), (⊤ : Subgroup ↥S)⁆, (⊤ : Subgroup ↥S)⁆ = ⊥ := by
    have hmap : Subgroup.map e.symm.toMonoidHom
        ⁅⁅(⊤ : Subgroup ↥T), (⊤ : Subgroup ↥T)⁆, (⊤ : Subgroup ↥T)⁆ =
        ⁅⁅(⊤ : Subgroup ↥S), (⊤ : Subgroup ↥S)⁆, (⊤ : Subgroup ↥S)⁆ := by
      rw [Subgroup.map_commutator, Subgroup.map_commutator, Subgroup.map_top_of_surjective _
        e.symm.surjective]
    rw [← hmap, hT, Subgroup.map_bot]
  rw [commutator3_eq_map, hS, Subgroup.map_bot]

theorem card_eq_sq_of_normal_bar (D : Data G) {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    (h22 : R17_2_2At D V₀ V hV) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {K : Subgroup (Bar2 D.M)} (hK : K.Normal) (hKq : IsPGroup q K) (hKnc : ¬ IsCyclic K)
    (hKexp : ∀ x ∈ K, x ^ q = 1) (hKcl : ⁅⁅K, K⁆, K⁆ = ⊥) : Nat.card K = q ^ 2 := by
  obtain ⟨Dg, hDM, hDp, ⟨e⟩, hDn⟩ := exists_lift_of_normal_isPGroup D.M hq hq2 hK hKq
  obtain ⟨hnc, hexp, hcl⟩ := transfer_of_mulEquiv e hKnc hKexp hKcl
  rw [← Nat.card_congr e.toEquiv]
  exact (h22 q Dg hq hq2 hDM hDp hnc hexp hcl hDn).1

theorem five_of_normal_bar (D : Data G) {V₀ V : Subgroup G} (h25 : R17_2_5At D V₀ V)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hqs : q ∈ D.sig)
    {K : Subgroup (Bar2 D.M)} (hK : K.Normal) (hKq : IsPGroup q K) (hKnc : ¬ IsCyclic K)
    (hKexp : ∀ x ∈ K, x ^ q = 1) (hKcl : ⁅⁅K, K⁆, K⁆ = ⊥) :
    q = 5 ∧ 3 ∉ piSet D.M ∧
      ∀ r ∈ piSet D.M, r ≠ 2 → r ≠ 5 → CFSG.RankThree.PartOne.IsStronglyPEmbedded r D.M := by
  obtain ⟨Dg, hDM, hDp, ⟨e⟩, hDn⟩ := exists_lift_of_normal_isPGroup D.M hq hq2 hK hKq
  obtain ⟨hnc, hexp, hcl⟩ := transfer_of_mulEquiv e hKnc hKexp hKcl
  exact h25 q Dg hq hq2 hDM hDp hnc hexp hcl hDn hqs

theorem commutator_bar_pow_mem_centralizer_pCore (D : Data G) {V₀ V : Subgroup G}
    (hV : Hyp125 D V₀ V) (h22 : R17_2_2At D V₀ V hV) (h23 : R17_2_3At D V₀ V hV)
    {q : ℕ} (hq : q.Prime) {x : Bar2 D.M} (hx : x ∈ commutator (Bar2 D.M)) :
    ∃ n : ℕ, x ^ q ^ n ∈ Subgroup.centralizer (CFSG.pCore q (Bar2 D.M) : Set (Bar2 D.M)) := by
  classical
  let Q := Bar2 D.M
  by_cases hq2 : q = 2
  · subst q
    refine ⟨0, ?_⟩
    rw [s13_pCore_bar_eq_bot D.M]
    exact Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [SetLike.mem_coe, Subgroup.mem_bot] at hh
      rw [hh, one_mul, mul_one]
  by_cases hQq : CFSG.pCore q Q = ⊥
  · refine ⟨0, ?_⟩
    rw [hQq]
    exact Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [SetLike.mem_coe, Subgroup.mem_bot] at hh
      rw [hh, one_mul, mul_one]
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Nontrivial ↥(CFSG.pCore q Q) := (Subgroup.nontrivial_iff_ne_bot _).2 hQq
  let Qq : Subgroup Q := CFSG.pCore q Q
  haveI : Qq.Normal := CFSG.pCore_normal
  have hQqp : IsPGroup q ↥Qq := CFSG.pCore_isPGroup
  obtain ⟨Cq, hCqchar, -, hCqcomm, hCqexp, hCqfix⟩ :=
    CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup (p := q) hq2 hQqp
  let CqQ : Subgroup Q := Cq.map Qq.subtype
  have hCqQnormal : CqQ.Normal := by
    haveI : Cq.Characteristic := hCqchar
    exact ConjAct.normal_of_characteristic_of_normal
  haveI : CqQ.Normal := hCqQnormal
  let eC : ↥Cq ≃* ↥CqQ := Cq.equivMapOfInjective Qq.subtype Qq.subtype_injective
  have hCqQp : IsPGroup q ↥CqQ := hQqp.to_subgroup Cq |>.map Qq.subtype
  let φ : Q →* MulAut ↥Qq := MulAut.conjNormal (H := Qq)
  have hA : IsPGroup q ((commutator Q).map φ) := by
    by_cases hcycCq : IsCyclic ↥Cq
    ·
      have hcomm : commutator Q ≤ Subgroup.centralizer (CqQ : Set Q) :=
        CFSG.LocalAnalysis.CyclicNormalConj.commutator_le_centralizer
          (isCyclic_of_surjective eC.toMonoidHom eC.surjective)
      refine hCqfix.to_le ?_
      rintro _ ⟨y, hy, rfl⟩
      rw [mem_fixingSubgroup_iff]
      intro c hc
      apply Subtype.ext
      change (((MulAut.conjNormal (H := Qq) y) c : Qq) : Q) = (c : Q)
      rw [MulAut.conjNormal_apply,
        ← Subgroup.mem_centralizer_iff.mp (hcomm hy) (c : Q)
          (Subgroup.mem_map_of_mem Qq.subtype hc),
        mul_inv_cancel_right]
    obtain ⟨hCqQcard, Wstar, hWstar_normal, hWstar_le, hWstarcard⟩ :
        Nat.card CqQ = q ^ 2 ∧ ∃ Wstar : Subgroup Q, Wstar.Normal ∧ Wstar ≤ CqQ ∧
          Nat.card Wstar = q := by
      let N2 : Subgroup ↥D.M := CFSG.pCore 2 ↥D.M
      haveI : N2.Normal := CFSG.pCore_normal
      obtain ⟨k2, hk2⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup : IsPGroup 2 ↥N2)
      let π : ↥D.M →* Q := QuotientGroup.mk' N2
      have hcop : q.Coprime (Nat.card N2) := by
        rw [hk2]
        exact ((Nat.coprime_primes hq Nat.prime_two).2 hq2).pow_right k2
      have hq_not_dvd_N2 : ¬ q ∣ Nat.card N2 := (Nat.Prime.coprime_iff_not_dvd hq).mp hcop
      obtain ⟨DsubM, hDsubMp, ⟨eDsub⟩, hDsup⟩ :=
        CFSG.GroupTheory.exists_isPGroup_of_coprime_kernel N2 hq hcop (K := CqQ) hCqQp
      have hDmap : DsubM.map π = CqQ := by
        have h := congrArg (Subgroup.map π) hDsup
        rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq,
          Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)] at h
      let Dg : Subgroup G := DsubM.map D.M.subtype
      have hDleM : Dg ≤ D.M := Subgroup.map_subtype_le _
      have hDp : IsPGroup q ↥Dg := hDsubMp.map D.M.subtype
      let eDC : ↥Dg ≃* ↥Cq :=
        ((DsubM.equivMapOfInjective D.M.subtype D.M.subtype_injective).symm.trans eDsub).trans
          eC.symm
      have hDnc : ¬ IsCyclic ↥Dg := fun hcyc =>
        hcycCq (isCyclic_of_surjective eDC.toMonoidHom eDC.surjective)
      have hDexp : ∀ x ∈ Dg, x ^ q = 1 := CFSG.AGLEmbedding.pow_eq_one_of_mulEquiv eDC hCqexp
      have hCtop : ⁅⁅(⊤ : Subgroup ↥Cq), (⊤ : Subgroup ↥Cq)⁆, (⊤ : Subgroup ↥Cq)⁆ = ⊥ :=
        Subgroup.commutator_top_right_eq_bot_iff_le_center.mpr
          (CFSG.RankThree.PartOne.PlaneCore.commutator_le_center_of_critical hCqcomm)
      have hDtop : ⁅⁅(⊤ : Subgroup ↥Dg), (⊤ : Subgroup ↥Dg)⁆, (⊤ : Subgroup ↥Dg)⁆ = ⊥ := by
        have hmap : (⁅⁅(⊤ : Subgroup ↥Dg), (⊤ : Subgroup ↥Dg)⁆, (⊤ : Subgroup ↥Dg)⁆).map
            eDC.toMonoidHom = ⊥ := by
          rw [Subgroup.map_commutator, Subgroup.map_commutator, Subgroup.map_top,
            MonoidHom.range_eq_top.mpr eDC.surjective, hCtop]
        exact (Subgroup.map_eq_bot_iff_of_injective _ (f := eDC.toMonoidHom)
          eDC.injective).mp hmap
      have hDclass : ⁅⁅Dg, Dg⁆, Dg⁆ = ⊥ := by
        have h := congrArg (Subgroup.map Dg.subtype) hDtop
        rwa [Subgroup.map_commutator, Subgroup.map_commutator, Subgroup.map_top,
          Subgroup.range_subtype, Subgroup.map_bot] at h
      have hsubmap : ((CqQ.comap π).map D.M.subtype).subgroupOf D.M = CqQ.comap π :=
        Subgroup.comap_map_eq_self_of_injective D.M.subtype_injective _
      have hDnormal : ((Dg ⊔ CFSG.Open.pCoreOf 2 D.M).subgroupOf D.M).Normal := by
        rw [show Dg ⊔ CFSG.Open.pCoreOf 2 D.M = (DsubM ⊔ N2).map D.M.subtype by
            rw [Subgroup.map_sup]; rfl, hDsup, hsubmap]
        exact Subgroup.Normal.comap hCqQnormal π
      have hDcard : Nat.card Dg = q ^ 2 :=
        (h22 q Dg hq hq2 hDleM hDp hDnc hDexp hDclass hDnormal).1
      have hCqQcard : Nat.card CqQ = q ^ 2 := by
        rw [← Nat.card_congr eC.toEquiv, ← Nat.card_congr eDC.toEquiv]
        exact hDcard
      have hDsubMleH : DsubM ≤ CqQ.comap π := hDsup ▸ le_sup_left
      have hirr := (h23 q Dg hq hq2 hDleM hDp hDnc hDexp hDclass hDnormal).1
      rw [IrrOn] at hirr
      push Not at hirr
      obtain ⟨W, hWle, hWN, hWnebot, hWneD⟩ := hirr
      have hWleM : W ≤ D.M := hWle.trans hDleM
      have hWcard : Nat.card W = q :=
        CFSG.GroupTheory.card_eq_prime_of_le_of_card_eq_sq hWle hDcard hWnebot hWneD
      let Wstar : Subgroup Q := (W.subgroupOf D.M).map π
      have hWstar_le : Wstar ≤ CqQ := by
        rintro x ⟨m, hm, rfl⟩
        obtain ⟨d, hd, hdm⟩ := Subgroup.mem_map.mp (hWle hm)
        have hdm' : d = m := Subtype.ext hdm
        rw [← hdm']
        exact Subgroup.mem_comap.mp (hDsubMleH hd)
      have hNtop : (Subgroup.normalizer (DsubM : Set ↥D.M)).map π = ⊤ := by
        rw [CFSG.GroupTheory.normal_coprime_quotient_normalizer q N2 hq_not_dvd_N2 DsubM
          hDsubMp, hDmap]
        exact Subgroup.normalizer_eq_top_iff.mpr hCqQnormal
      have hQleW : (⊤ : Subgroup Q) ≤ Subgroup.normalizer (Wstar : Set Q) := by
        rw [← hNtop]
        rintro _ ⟨n, hn, rfl⟩
        have hnWg : ((n : ↥D.M) : G) ∈ Subgroup.normalizer (W : Set G) := by
          have hnG : ((n : ↥D.M) : G) ∈ Subgroup.normalizer (Dg : Set G) := by
            have hmapn := Subgroup.le_normalizer_map (H := DsubM) D.M.subtype
              (Subgroup.mem_map_of_mem D.M.subtype hn)
            simpa [Dg] using hmapn
          exact hWN ⟨n.2, hnG⟩
        have hnW : n ∈ Subgroup.normalizer ((W.subgroupOf D.M : Subgroup ↥D.M) : Set ↥D.M) := by
          have h1 : n ∈ (Subgroup.normalizer (W : Set G)).subgroupOf D.M :=
            Subgroup.mem_subgroupOf.mpr hnWg
          simpa [Subgroup.subgroupOf_normalizer_eq hWleM] using h1
        have hmapn := Subgroup.le_normalizer_map (H := W.subgroupOf D.M) π
          (Subgroup.mem_map_of_mem π hnW)
        simpa [Wstar] using hmapn
      have hWstar_normal : Wstar.Normal :=
        Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hQleW)
      have hWstarcard : Nat.card Wstar = q :=
        (CFSG.RankThree.PartOne.StrongP.card_map_quotient_of_coprime (E := W.subgroupOf D.M)
          ((hDp.to_le hWle).comap_of_injective D.M.subtype D.M.subtype_injective)
          hq_not_dvd_N2).trans
          ((Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWleM).toEquiv).trans hWcard)
      exact ⟨hCqQcard, Wstar, hWstar_normal, hWstar_le, hWstarcard⟩
    haveI : Wstar.Normal := hWstar_normal
    have hcW : commutator Q ≤ Subgroup.centralizer (Wstar : Set Q) :=
      CFSG.LocalAnalysis.CyclicNormalConj.commutator_le_centralizer
        (isCyclic_of_prime_card hWstarcard)
    have hquot_card : Nat.card (↥CqQ ⧸ Wstar.subgroupOf CqQ) = q := by
      have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Wstar.subgroupOf CqQ)
      rw [hCqQcard, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWstar_le).toEquiv,
        hWstarcard] at h
      have h' : Nat.card (↥CqQ ⧸ Wstar.subgroupOf CqQ) * q = q * q := by
        rw [← h]
        ring
      exact Nat.eq_of_mul_eq_mul_right hq.pos h'
    haveI : IsCyclic (↥CqQ ⧸ Wstar.subgroupOf CqQ) := isCyclic_of_prime_card hquot_card
    have hsec := CFSG.GroupTheory.map_commutator_eq_bot_of_isCyclic
      (CFSG.RankThree.PartTwo.Sec3.sectionAction CqQ Wstar)
    refine CFSG.GroupTheory.isPGroup_of_forall_fix_disp (C := Cq) (W := Wstar.comap Qq.subtype)
      (hQqp.to_subgroup _) hCqfix ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩ w hw
      apply Subtype.ext
      change (((MulAut.conjNormal (H := Qq) y) w : Qq) : Q) = (w : Q)
      rw [MulAut.conjNormal_apply,
        ← Subgroup.mem_centralizer_iff.mp (hcW hy) (w : Q) hw, mul_inv_cancel_right]
    · rintro _ ⟨y, hy, rfl⟩ c hc
      have hy1 : CFSG.RankThree.PartTwo.Sec3.sectionAction CqQ Wstar y = 1 := by
        have hmem : CFSG.RankThree.PartTwo.Sec3.sectionAction CqQ Wstar y ∈
            (commutator Q).map (CFSG.RankThree.PartTwo.Sec3.sectionAction CqQ Wstar) :=
          Subgroup.mem_map_of_mem _ hy
        rwa [hsec, Subgroup.mem_bot] at hmem
      let cc : ↥CqQ := ⟨(c : Q), Subgroup.mem_map_of_mem Qq.subtype hc⟩
      have h2 : (cc : ↥CqQ ⧸ Wstar.subgroupOf CqQ) =
          ((MulAut.conjNormal (H := CqQ) y cc : ↥CqQ) : ↥CqQ ⧸ Wstar.subgroupOf CqQ) := by
        rw [← CFSG.RankThree.PartTwo.Sec3.sectionAction_mk, hy1, MulAut.one_apply]
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h2
      show ((c⁻¹ * (MulAut.conjNormal (H := Qq) y) c : Qq) : Q) ∈ Wstar
      simpa [cc, MulAut.conjNormal_apply] using h2
  obtain ⟨n, hn⟩ := hA ⟨φ x, Subgroup.mem_map_of_mem φ hx⟩
  refine ⟨n, ?_⟩
  have hn' : (φ x) ^ q ^ n = 1 := by
    simpa using congrArg Subtype.val hn
  have hker : x ^ q ^ n ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_pow, hn']
  rwa [CFSG.AGLEmbedding.ker_conjNormal_eq_centralizer Qq] at hker

theorem mem_centralizer_pCore_of_pElement (D : Data G) {V₀ V : Subgroup G}
    (hV : Hyp125 D V₀ V) (h22 : R17_2_2At D V₀ V hV) (h23 : R17_2_3At D V₀ V hV)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hqp : q ≠ p) {y : Bar2 D.M}
    (hy : y ∈ commutator (Bar2 D.M)) {k : ℕ} (hyk : y ^ p ^ k = 1) :
    y ∈ Subgroup.centralizer (CFSG.pCore q (Bar2 D.M) : Set (Bar2 D.M)) := by
  obtain ⟨n, hn⟩ := commutator_bar_pow_mem_centralizer_pCore D hV h22 h23 hq hy
  have hcop : (q ^ n).Coprime (orderOf y) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hyk)
      (Nat.Coprime.pow n k ((Nat.coprime_primes hq hp).mpr hqp))
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have h := pow_mem hn m
  rwa [hm] at h

theorem mem_centralizer_layer_of_pElement (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    (hp : Hyp1754 D p) (hThin : ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian)
    (h33 : R17_33_2At D V₀ V) {y : Bar2 D.M}
    (hcomm : y ∈ commutator (Bar2 D.M)) {k : ℕ} (hyk : y ^ p ^ k = 1)
    (hyC : y ∈ Subgroup.centralizer
      (pElementSubgroup p (CFSG.layer (Bar2 D.M)) : Set (Bar2 D.M))) :
    y ∈ Subgroup.centralizer (CFSG.layer (Bar2 D.M) : Set (Bar2 D.M)) := by
  have hpp := D.sig_prime p hp.1
  have hshape := shape_of_hyp1754 D hp h33
  have hns : s13_NormalSimple (Bar2 D.M) := by
    intro J hJ
    obtain ⟨L, hL, rfl⟩ := s13_exists_calC_of_component D.M hJ
    exact ⟨s13_barImage_normal (hp.2 L hL).1,
      isSimple_barImage_of_shape hL hThin (hshape L hL)⟩
  have hzle : Subgroup.zpowers y ≤
      Subgroup.centralizer (CFSG.layer (Bar2 D.M) : Set (Bar2 D.M)) := by
    rw [s13_Layer13_layer_eq_iSup]
    refine CFSG.subgroup_le_centralizer_iSup_of_le_centralizer _ fun J => ?_
    refine CFSG.subgroup_le_centralizer_iSup_of_le_centralizer _ fun hJ => ?_
    rw [Subgroup.zpowers_le]
    have hJc : CFSG.IsComponent J := s13_Layer13_mem_comps.mp hJ
    by_cases hpJ : p ∣ Nat.card J
    · have hJle : J ≤ pElementSubgroup p (CFSG.layer (Bar2 D.M)) := by
        rw [s13_pElementSubgroup_layer_eq hns hpp.1]
        exact le_iSup₂_of_le J (s13_mem_compsP.mpr ⟨hJc, hpJ⟩) le_rfl
      exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hJle) hyC
    · obtain ⟨L, hL, rfl⟩ := s13_exists_calC_of_component D.M hJc
      have hL3inner : IsL3 (Bar2 L) 2 → p ≠ 3 := fun hL3 hp3 => by
        apply hpJ
        obtain ⟨e⟩ := s13_bar_equiv hL
        rw [← Nat.card_congr e.toEquiv, card_bar_of_isL3 hL3, hp3]
        norm_num
      exact CFSG.GroupTheory.mem_centralizer_of_mem_sup_centralizer_of_coprime _
        (mem_sup_centralizer_barImage_of_shape hL hThin hCyc hp (hshape L hL) hL3inner
          hcomm hyk) hyk
        (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hpp.1).mpr hpJ))
  exact hzle (Subgroup.mem_zpowers y)

theorem barImage_Sp_le_pCore (D : Data G) {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    {p : ℕ} (hp : Hyp1754 D p) (hThin : ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian)
    (h638 : UC6.R6_38 D) (h33 : R17_33_2At D V₀ V)
    (h22 : R17_2_2At D V₀ V hV) (h23 : R17_2_3At D V₀ V hV) :
    barImage D.M (Sp D p) ≤ CFSG.pCore p (Bar2 D.M) := by
  have hpp : p.Prime := (D.sig_prime p hp.1).1
  have hp2 : p ≠ 2 := (D.sig_prime p hp.1).2
  haveI : Fact p.Prime := ⟨hpp⟩
  have htop : CFSG.GH74.GLS.oResidual p (Bar2 D.M) = ⊤ :=
    uc22p21c_oResidual_bar_eq_top hpp (h638 p hpp hp2 (Or.inl hp.1))
  let S : Set (Bar2 D.M) := {x | x ∈ Subgroup.centralizer
    (pElementSubgroup p (CFSG.layer (Bar2 D.M)) : Set (Bar2 D.M)) ∧ ∃ k : ℕ, orderOf x = p ^ k}
  have hY : barImage D.M (Sp D p) = Subgroup.closure S := by
    rw [sp_eq_f13Sp, s13_barImage_Sp D.M hpp]
    rfl
  have hScomm : ∀ s ∈ S, s ∈ commutator (Bar2 D.M) := fun s hs => by
    obtain ⟨-, k, hk⟩ := hs
    exact uc22p21c_mem_commutator_of_oResidual_eq_top htop (k := k) (hk ▸ dvd_rfl)
  have hSpow : ∀ s ∈ S, ∃ k : ℕ, s ^ p ^ k = 1 := fun s hs => by
    obtain ⟨-, k, hk⟩ := hs
    exact ⟨k, hk ▸ pow_orderOf_eq_one s⟩
  have hYcomm : Subgroup.closure S ≤ commutator (Bar2 D.M) := (Subgroup.closure_le _).mpr hScomm
  have h1 : Subgroup.closure S ≤
      Subgroup.centralizer (CFSG.layer (Bar2 D.M) : Set (Bar2 D.M)) := by
    rw [Subgroup.closure_le]
    intro s hs
    obtain ⟨k, hk⟩ := hSpow s hs
    exact mem_centralizer_layer_of_pElement D hp hThin hCyc h33 (hScomm s hs) hk hs.1
  have h2 : ∀ q : ℕ, q.Prime → q ≠ p → Subgroup.closure S ≤
      Subgroup.centralizer (CFSG.pCore q (Bar2 D.M) : Set (Bar2 D.M)) := by
    intro q hq hqp
    rw [Subgroup.closure_le]
    intro s hs
    obtain ⟨k, hk⟩ := hSpow s hs
    exact mem_centralizer_pCore_of_pElement D hV h22 h23 hpp hq hqp (hScomm s hs) hk
  have h3 : ∀ x ∈ Subgroup.closure S, ∃ n : ℕ,
      x ^ p ^ n ∈ Subgroup.centralizer (CFSG.pCore p (Bar2 D.M) : Set (Bar2 D.M)) :=
    fun x hx => commutator_bar_pow_mem_centralizer_pCore D hV h22 h23 hpp (hYcomm hx)
  haveI := CFSG.GroupTheory.isNilpotent_of_le_centralizer_layer_pCores hpp h1 h2 h3
  have hYp : IsPGroup p (Subgroup.closure S) := by
    have hcl := CFSG.GroupTheory.isPGroup_closure_of_isNilpotent (Y := ↥(Subgroup.closure S))
      (p := p) (S := (Subgroup.closure S).subtype ⁻¹' S) fun s hs => by
        obtain ⟨k, hk⟩ := hSpow _ hs
        exact ⟨k, Subtype.ext (by simpa using hk)⟩
    rw [Subgroup.closure_preimage_eq_top] at hcl
    exact hcl.of_equiv Subgroup.topEquiv
  have hYn : (barImage D.M (Sp D p)).Normal := by
    rw [sp_eq_f13Sp]
    exact s13_barImage_normal (s13_Sp_normal D.M p)
  rw [hY] at hYn ⊢
  exact CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup hYn hYp

theorem pRank_Sp_le (D : Data G) {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    {p : ℕ} (hp : Hyp1754 D p) (hThin : ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian)
    (h638 : UC6.R6_38 D) (h33 : R17_33_2At D V₀ V)
    (h22 : R17_2_2At D V₀ V hV) (h23 : R17_2_3At D V₀ V hV) :
    CFSG.Open.pRank p (Sp D p) ≤ CFSG.Open.pRank p (CFSG.pCore p (Bar2 D.M)) := by
  have hpp : p.Prime := (D.sig_prime p hp.1).1
  have hp2 : p ≠ 2 := (D.sig_prime p hp.1).2
  rw [← CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_pRank_barImage hpp hp2 (Sp_le D p)]
  exact CFSG.SectionRank.pRank_mono hpp.one_lt
    (barImage_Sp_le_pCore D hV hp hThin hCyc h638 h33 h22 h23)

theorem seventeen_fiftyseven (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V)
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D)
    (hThin : ThinList13) (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian)
    (h638 : UC6.R6_38 D) (h33 : R17_33_2At D V₀ V)
    (h22 : R17_2_2At D V₀ V hV) (h23 : R17_2_3At D V₀ V hV) (h25 : R17_2_5At D V₀ V)
    (h55 : R17_55At D V₀ V) :
    R17_57At D V₀ V := by
  intro p hp
  by_contra hle
  push Not at hle
  have hpp : p.Prime := (D.sig_prime p hp.1).1
  have hp2 : p ≠ 2 := (D.sig_prime p hp.1).2
  haveI : Fact p.Prime := ⟨hpp⟩
  have hrk := pRank_Sp_le D hV hp hThin hCyc h638 h33 h22 h23
  have hnc : ¬ IsCyclic ↥(CFSG.pCore p (Bar2 D.M)) := fun hcyc => by
    have := CFSG.SectionRank.pRank_le_one_of_isCyclic hpp hcyc
    omega
  obtain ⟨W, hWP, hWchar, hWnc, hWexp, hWcl⟩ :=
    CFSG.GroupTheory.exists_characteristic_noncyclic_exponent_classTwo hp2
      (CFSG.pCore_isPGroup (p := p) (G := Bar2 D.M)) hnc
  have hWn : W.Normal := CFSG.RankThree.PartOne.OddCore37.normal_of_characteristic hWP hWchar
  obtain ⟨hp5, h3, hstr⟩ := five_of_normal_bar D h25 hpp hp2 hp.1 hWn
    ((CFSG.pCore_isPGroup (p := p) (G := Bar2 D.M)).to_le hWP) hWnc hWexp hWcl
  have hlayer : CFSG.layer (Bar2 D.M) = ⊥ :=
    layer_eq_bot_of_three_not_mem hp hThin h3 h55 hstr
  have hO2E : oTwoEOf D.M = CFSG.Open.pCoreOf 2 D.M := by
    show barPreimage D.M (CFSG.layer (Bar2 D.M)) = CFSG.Open.pCoreOf 2 D.M
    rw [hlayer]
    show ((⊥ : Subgroup (Bar2 D.M)).comap
      (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M))).map D.M.subtype = CFSG.Open.pCoreOf 2 D.M
    rw [MonoidHom.comap_bot, QuotientGroup.ker_mk']
    rfl
  have hLp : Lp D p = ⊥ := by
    rw [Lp, hO2E]
    exact opp_pCoreOf_two_eq_bot hpp hp2
  have hcent : centSection D.M (Lp D p) (CFSG.Open.pCoreOf 2 (Lp D p)) = D.M := by
    rw [hLp]
    have hbot : CFSG.Open.pCoreOf 2 (⊥ : Subgroup G) = ⊥ := by
      rw [CFSG.Open.pCoreOf,
        Subgroup.eq_bot_of_subsingleton (CFSG.pCore 2 ↥(⊥ : Subgroup G))]
      simp
    rw [hbot, centSection_bot_bot]
  have hSp : Sp D p = Opp p D.M := by
    rw [Sp, hcent]
  have hrankM : CFSG.Open.pRank p (Sp D p) = CFSG.Open.pRank p D.M := by
    rw [hSp]
    exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.s13_pRank_pElementSubgroup hpp D.M
  have h3le : 3 ≤ CFSG.Open.pRank p (CFSG.pCore p (Bar2 D.M)) := by
    have := hSg.three_le p hp.1
    omega
  obtain ⟨X, hXP, hXchar, hXexp, hXcl, hXcard⟩ :=
    CFSG.GroupTheory.exists_characteristic_exponent_classTwo_card_ge_cube hp2
      (CFSG.pCore_isPGroup (p := p) (G := Bar2 D.M)) h3le
  have hXn : X.Normal := CFSG.RankThree.PartOne.OddCore37.normal_of_characteristic hXP hXchar
  have hXnc : ¬ IsCyclic ↥X := by
    intro hcyc
    have hexp : Monoid.exponent ↥X ∣ p :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (hXexp g.1 g.2)
    rw [IsCyclic.exponent_eq_card] at hexp
    have hle' : Nat.card ↥X ≤ p := Nat.le_of_dvd hpp.pos hexp
    have hlt : p < p ^ 3 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 3 := Nat.pow_lt_pow_right hpp.one_lt (by norm_num)
    omega
  have hXsq := card_eq_sq_of_normal_bar D hV h22 hpp hp2 hXn
    ((CFSG.pCore_isPGroup (p := p) (G := Bar2 D.M)).to_le hXP) hXnc hXexp hXcl
  have : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hpp.one_lt (by norm_num)
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
