module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9.R920OddStrong
import CFSG.GroupTheory.PCoreSurjective
import CFSG.Holt.Induced
import CFSG.LocalAnalysis.UniquenessCase.UCFront09R98W
import CFSG.RankThree.GroupTheory.SteinbergBMCrossPrimeLocalCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] def xbar9 (Y H : Subgroup G) : Subgroup (F09.Lbar9 Y H) :=
  (F09.img9 H (Opp 3 Y)).subgroupOf (F09.img9 H (F09.L9 Y H))

@[expose] def wbar9 (D : Data G) (Y H : Subgroup G) : Subgroup (F09.Lbar9 Y H) :=
  (F09.img9 H (H ⊓ D.M)).subgroupOf (F09.img9 H (F09.L9 Y H))

@[expose] def toImg9 {H K : Subgroup G} (hKH : K ≤ H) : ↥K →* ↥(F09.img9 H K) :=
  ((QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)).comp (Subgroup.inclusion hKH)).codRestrict
    (F09.img9 H K) fun x =>
      Subgroup.mem_map.2 ⟨Subgroup.inclusion hKH x, Subgroup.mem_subgroupOf.2 x.2, rfl⟩

theorem toImg9_surjective {H K : Subgroup G} (hKH : K ≤ H) :
    Function.Surjective (toImg9 hKH) := by
  rintro ⟨z, hz⟩
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hz
  exact ⟨⟨y, Subgroup.mem_subgroupOf.1 hy⟩, Subtype.ext rfl⟩

theorem mem_ker_toImg9 {H K : Subgroup G} (hKH : K ≤ H) {x : ↥K} :
    x ∈ (toImg9 hKH).ker ↔ (x : G) ∈ F09.I9 H := by
  rw [MonoidHom.mem_ker, ← Subtype.coe_inj, Subgroup.coe_one]
  change (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)) (Subgroup.inclusion hKH x) = 1 ↔ _
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, F09.I9]
  exact (Subgroup.mem_map_iff_mem H.subtype_injective).symm

theorem coprime_card_ker_toImg9 {H K : Subgroup G} (hKH : K ≤ H) :
    Nat.Coprime 3 (Nat.card (toImg9 hKH).ker) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hker : (toImg9 hKH).ker = (CFSG.pPrimeCore 3 ↥H).comap (Subgroup.inclusion hKH) := by
    ext x
    rw [mem_ker_toImg9, Subgroup.mem_comap, F09.I9]
    exact Subgroup.mem_map_iff_mem (x := Subgroup.inclusion hKH x) H.subtype_injective
  rw [hker]
  exact Nat.Coprime.coprime_dvd_right
    (Subgroup.card_comap_dvd_of_injective _ _ (Subgroup.inclusion_injective hKH))
    CFSG.pPrimeCore_coprime_card

namespace SliceCore

variable {D : Data G} {L D₃ Y H : Subgroup G}

theorem opp_inf_I9_le_pCoreOf (S : SliceCore D L D₃ Y H) :
    Opp 3 Y ⊓ F09.I9 H ≤ pCoreOf 2 (Opp 3 Y) := by
  have hs := S.isSimpleGroup_bar2_opp
  have hHI : H ≤ normalizer (F09.I9 H : Set G) :=
    CFSG.RankThree.GroupTheory.SteinbergBM.le_normalizer_inSubgroup_pPrimeCore 3 H
  have hXH : Opp 3 Y ≤ H := (opp_le 3 Y).trans S.Y_le_H
  set Q := CFSG.pCore 2 ↥(Opp 3 Y)
  set J : Subgroup ↥(Opp 3 Y) := (F09.I9 H).subgroupOf (Opp 3 Y) with hJ
  have hJn : J.Normal := ⟨fun x hx g => by
    rw [hJ, Subgroup.mem_subgroupOf] at hx ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (hHI (hXH g.2)) (x : G)).mp hx⟩
  haveI : (J.map (QuotientGroup.mk' Q)).Normal := hJn.map _ (QuotientGroup.mk'_surjective Q)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (J.map (QuotientGroup.mk' Q)) with h | h
  · intro x hx
    have h1 : QuotientGroup.mk' Q ⟨x, hx.1⟩ ∈ J.map (QuotientGroup.mk' Q) :=
      ⟨_, Subgroup.mem_subgroupOf.mpr hx.2, rfl⟩
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact (CFSG.mem_openPCoreOf_iff (⟨x, hx.1⟩ : ↥(Opp 3 Y))).2 h1
  · exfalso
    have h1 : Nat.card (Bar2 (Opp 3 Y)) ∣ Nat.card J := by
      rw [← Subgroup.card_top (G := Bar2 (Opp 3 Y)), ← h]
      exact Subgroup.card_map_dvd _ _
    have h2 : Nat.card J ∣ Nat.card (F09.I9 H) := by
      rw [← Subgroup.card_map_of_injective (Opp 3 Y).subtype_injective, hJ,
        Subgroup.subgroupOf_map_subtype]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hcop : Nat.Coprime 3 (Nat.card (F09.I9 H)) :=
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      CFSG.RankThree.GroupTheory.SteinbergBM.coprime_card_inSubgroup_pPrimeCore H
    exact absurd (Nat.Coprime.coprime_dvd_right (S.three_dvd_card_bar2_opp.trans (h1.trans h2))
      hcop) (by decide)

theorem isPGroup_ker_toImg9 (S : SliceCore D L D₃ Y H) (hXH : Opp 3 Y ≤ H) :
    IsPGroup 2 (toImg9 hXH).ker := by
  have hO : IsPGroup 2 ↥(pCoreOf 2 (Opp 3 Y)) := by
    rw [CFSG.openPCoreOf_eq_map_pCore]
    exact CFSG.pCore_isPGroup.map _
  intro g
  have hg : ((g : ↥(Opp 3 Y)) : G) ∈ pCoreOf 2 (Opp 3 Y) :=
    S.opp_inf_I9_le_pCoreOf ⟨(g : ↥(Opp 3 Y)).2, (mem_ker_toImg9 hXH).1 g.2⟩
  obtain ⟨k, hk⟩ := hO ⟨_, hg⟩
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  simpa using congrArg Subtype.val hk

end SliceCore

namespace Slice

variable {D : Data G} {L D₃ Y H : Subgroup G} {q : ℕ}

theorem isL2Odd_bar2_xbar9 (S : Slice D L D₃ Y H q) (hq : q = 7) :
    IsL2Odd (Bar2 (xbar9 Y H)) 7 := by
  subst hq
  have hXH : Opp 3 Y ≤ H := (opp_le 3 Y).trans S.Y_le_H
  have hle : F09.img9 H (Opp 3 Y) ≤ F09.img9 H (F09.L9 Y H) :=
    Subgroup.map_mono fun y hy => F09.opp_le_L9 Y H hy
  obtain ⟨e⟩ := CFSG.nonempty_quotient_pCore_equiv_of_surjective_of_isPGroup_ker (toImg9 hXH)
    (toImg9_surjective hXH) (S.isPGroup_ker_toImg9 hXH)
  exact CFSG.Blueprint.LieModel.of_mulEquiv
    (e.trans (UC6S846.bar2Equiv (Subgroup.subgroupOfEquivOfLe hle)).symm) S.shape_opp

end Slice

theorem isCyclic_of_isPGroup_lbar9 {D : Data G} {Y H E : Subgroup G} (hyp : F09.Hyp91 D Y H E) :
    ∀ P : Subgroup (F09.Lbar9 Y H), IsPGroup 3 P → IsCyclic P := by
  intro P hP
  obtain ⟨hYH, -, hrk⟩ := hyp.2.1
  have hLH : F09.L9 Y H ≤ H := L9_le_of_le hYH
  have hrank : CFSG.Open.pRank 3 P ≤ 1 :=
    calc CFSG.Open.pRank 3 P ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (F09.Lbar9 Y H)) :=
          CFSG.RankThreeCoreUniqueness.Helpers.pRank_mono 3 (by norm_num) le_top
      _ = CFSG.Open.pRank 3 (⊤ : Subgroup ↥(F09.L9 Y H)) :=
          (CFSG.RankThreeCoreUniqueness.Helpers.pRank_top_eq_of_coprime_kernel 3 Nat.prime_three
            (toImg9 hLH) (toImg9_surjective hLH) (coprime_card_ker_toImg9 hLH)).symm
      _ = CFSG.Open.pRank 3 (F09.L9 Y H) :=
          (CFSG.RankThreeCoreUniqueness.Helpers.pRank_subgroup_eq_internal_top 3 (by norm_num)
            _).symm
      _ = 1 := hrk
  exact CFSG.LocalAnalysis.UniquenessCase.UCK.K31.isCyclic_of_pRank_le_one Nat.prime_three
    (by norm_num) hP hrank

namespace Slice

variable {D : Data G} {L D₃ Y H : Subgroup G} {q : ℕ}

theorem exists_le_opp_card_eq_img9_eq (S : Slice D L D₃ Y H q) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {Qb : Subgroup (F09.Hbar9 H)} (hQ : IsPGroup p Qb)
    (hQX : Qb ≤ F09.img9 H (Opp 3 Y)) :
    ∃ A : Subgroup G, A ≤ Opp 3 Y ∧ Nat.card A = Nat.card Qb ∧ F09.img9 H A = Qb := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXH : Opp 3 Y ≤ H := (opp_le 3 Y).trans S.Y_le_H
  set ψ := toImg9 hXH
  set Qc : Subgroup ↥(F09.img9 H (Opp 3 Y)) := Qb.subgroupOf (F09.img9 H (Opp 3 Y))
  have eQ : ↥Qc ≃* ↥Qb := Subgroup.subgroupOfEquivOfLe hQX
  obtain ⟨P, -, -, hP, hPQ⟩ := CFSG.Holt.exists_isPGroup_map_eq_of_map_le (H := ⊤) (E := ⊥) ψ
    (hQ.of_equiv eQ.symm)
    (by rw [Subgroup.map_top_of_surjective ψ (toImg9_surjective hXH)]; exact le_top)
    IsPGroup.of_bot bot_le (by rw [Subgroup.map_bot]; exact bot_le)
  have hcop : p.Coprime (Nat.card ψ.ker) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (S.isPGroup_ker_toImg9 hXH)
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  obtain ⟨e⟩ :=
    CFSG.RankThreeCoreUniqueness.Helpers.coprime_kernel_pGroup_equiv_image p hp ψ hcop P hP
  refine ⟨P.map (Opp 3 Y).subtype, Subgroup.map_subtype_le P, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (Opp 3 Y).subtype_injective, Nat.card_congr e.toEquiv, hPQ,
      Nat.card_congr eQ.toEquiv]
  · ext z
    constructor
    · intro hz
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hz
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hy)
      have h1 : ψ x ∈ Qc := hPQ ▸ Subgroup.mem_map_of_mem ψ hx
      have hxy' : Subgroup.inclusion hXH x = y := Subtype.ext hxy
      have h2 : ((ψ x : ↥(F09.img9 H (Opp 3 Y))) : F09.Hbar9 H) =
          QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H) y := by
        rw [← hxy']
        rfl
      rw [← h2]
      exact Subgroup.mem_subgroupOf.1 h1
    · intro hz
      have hz' : (⟨z, hQX hz⟩ : ↥(F09.img9 H (Opp 3 Y))) ∈ P.map ψ := by
        rw [hPQ]
        exact Subgroup.mem_subgroupOf.2 hz
      obtain ⟨x, hx, hxz⟩ := Subgroup.mem_map.1 hz'
      exact Subgroup.mem_map.2 ⟨Subgroup.inclusion hXH x,
        Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨x, hx, rfl⟩), congrArg Subtype.val hxz⟩

theorem normalizer_le_wbar9 (S : Slice D L D₃ Y H q)
    (hN : ∀ A : Subgroup G, A ≤ Y → (Nat.card A).Prime → Odd (Nat.card A) →
      normalizer (A : Set G) ≤ D.M) :
    ∀ Dq : Subgroup (F09.Lbar9 Y H), Dq ≤ xbar9 Y H → Nat.card Dq = 3 →
      normalizer (Dq : Set (F09.Lbar9 Y H)) ≤ wbar9 D Y H := by
  intro Dq hDq h3 xb hxb
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Lb := F09.img9 H (F09.L9 Y H)
  have hDb : Nat.card (Dq.map Lb.subtype) = 3 := by
    rw [Subgroup.card_map_of_injective Lb.subtype_injective, h3]
  have hDbX : Dq.map Lb.subtype ≤ F09.img9 H (Opp 3 Y) := by
    rintro _ ⟨d, hd, rfl⟩
    exact hDq hd
  obtain ⟨A, hAX, hAc, hAD⟩ := S.exists_le_opp_card_eq_img9_eq Nat.prime_three (by norm_num)
    (IsPGroup.of_card (n := 1) (by rw [hDb, pow_one])) hDbX
  rw [hDb] at hAc
  have hAH : A ≤ H := hAX.trans ((opp_le 3 Y).trans S.Y_le_H)
  have hNA : normalizer (A : Set G) ≤ D.M :=
    hN A (hAX.trans (opp_le 3 Y)) (by rw [hAc]; exact Nat.prime_three) (by rw [hAc]; decide)
  have hA3 : IsPGroup 3 (A.subgroupOf H) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv, hAc, pow_one])
  have hx : (xb : F09.Hbar9 H) ∈ normalizer ((F09.img9 H A : Subgroup (F09.Hbar9 H)) :
      Set (F09.Hbar9 H)) := by
    rw [hAD]
    exact Subgroup.le_normalizer_map Lb.subtype ⟨xb, hxb, rfl⟩
  obtain ⟨g, hg, hgx⟩ := CFSG.AGLEmbedding.exists_mem_normalizer_mk_eq_of_mem_normalizer
    Nat.prime_three (CFSG.pPrimeCore 3 ↥H) CFSG.pPrimeCore_coprime_card hA3 hx
  have hgM : (g : G) ∈ D.M := by
    apply hNA
    have := Subgroup.le_normalizer_map H.subtype ⟨g, hg, rfl⟩
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hAH] at this
  rw [wbar9, Subgroup.mem_subgroupOf]
  exact Subgroup.mem_map.2 ⟨g, Subgroup.mem_subgroupOf.2 ⟨g.2, hgM⟩, hgx⟩

end Slice

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section9
