module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31Kl1
public import CFSG.Quasithin.Vol2.Ch12Sec6P31Kl2
public import CFSG.Quasithin.Vol2.Ch12Sec6P31Claim
public import CFSG.Quasithin.Vol2.Ch12Sec6P31e

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.LieType.BorelTits S126 S126P31
open CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

@[expose] def KListWeak12631 : Prop :=
  Lemma12_6_29 → ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) [IsMulCommutative ↥V]
    (F : Frame126 T L V), Hyp126 G T L V → V ⊓ Subgroup.centralizer (L : Set G) = ⊥ →
      ∀ H K : Subgroup G, IsHK T L F.V1 H K → HypF918 T V L F.V1 F.V5 H K →
        IsAlt 5 (↥(star H K) ⧸ Subgroup.center ↥(star H K)) ∨
          IsPSL 3 2 2 (↥(star H K) ⧸ Subgroup.center ↥(star H K))

namespace S126P31

theorem commutator_eq_top_of_perfect {Y : Type*} [Group Y] {X : Subgroup Y} (h : ⁅X, X⁆ = X) :
    commutator ↥X = ⊤ := by
  apply Subgroup.map_injective X.subtype_injective
  rw [Subgroup.map_subtype_commutator, h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

section Hodd

variable {Y : Type*} [Group Y] [Finite Y]

theorem pCoreOf_eq_self_P31 {p : ℕ} {Q : Subgroup Y} (hQ : IsPGroup p Q) : pCoreOf p Q = Q := by
  refine le_antisymm (pCoreOf_le p Q) fun y hy => ?_
  have htop : (⊤ : Subgroup Q) ≤ CFSG.Open.pCore p Q :=
    le_pCore p Subgroup.normal_top (hQ.of_equiv Subgroup.topEquiv.symm)
  exact ⟨⟨y, hy⟩, htop (Subgroup.mem_top _), rfl⟩

theorem pCoreOf_le_top_of_isSubnormal_P31 {p : ℕ} [Fact p.Prime] {K : Subgroup Y}
    (hK : K.IsSubnormal) : pCoreOf p K ≤ pCoreOf p ⊤ := by
  induction hK with
  | top => exact le_rfl
  | step H K hle hK hN ih =>
    refine le_trans ?_ ih
    refine le_pCoreOf_of_le_normalizer p ((pCoreOf_le p H).trans hle) ?_ (pCoreOf_isPGroup p H)
    intro m hm
    have hmH : m ∈ Subgroup.normalizer (H : Set Y) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp hN hm
    exact normalizer_le_normalizer_pCoreOf p H hmH

theorem eq_one_of_central_two_element
    (hO2 : ∀ N : Subgroup Y, N.Normal → IsPGroup 2 N → N = ⊥) {X : Subgroup Y}
    (hX : X.IsSubnormal) {z : ↥X} (hz : z ∈ Subgroup.center ↥X) {k : ℕ} (hzk : z ^ 2 ^ k = 1) :
    z = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z' : Subgroup ↥X := Subgroup.zpowers z with hZ'
  set Z : Subgroup Y := Z'.map X.subtype with hZ
  have hZ'c : Z' ≤ Subgroup.center ↥X := (Subgroup.zpowers_le).2 hz
  have hZX : Z ≤ X := Subgroup.map_subtype_le _
  have hZn : (Z.subgroupOf X).Normal := by
    have : Z.subgroupOf X = Z' := Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
    rw [this]
    exact Subgroup.normal_of_le_center hZ'c
  have hZsub : Z.IsSubnormal := Subgroup.IsSubnormal.step Z X hZX hX hZn
  have hZ'p : IsPGroup 2 Z' := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hzk)
    exact IsPGroup.of_card (n := j) (by rw [hZ', Nat.card_zpowers, hj])
  have hZp : IsPGroup 2 Z := hZ'p.map _
  have hle : Z ≤ pCoreOf 2 (⊤ : Subgroup Y) := by
    rw [← pCoreOf_eq_self_P31 hZp]
    exact pCoreOf_le_top_of_isSubnormal_P31 hZsub
  have hcore : pCoreOf 2 (⊤ : Subgroup Y) = ⊥ := by
    refine hO2 _ ?_ (pCoreOf_isPGroup 2 ⊤)
    exact Subgroup.normalizer_eq_top_iff.1 (top_le_iff.1 (le_normalizer_pCoreOf 2 ⊤))
  have hzZ : (z : Y) ∈ Z := ⟨z, Subgroup.mem_zpowers z, rfl⟩
  rw [hcore] at hle
  exact Subtype.ext (Subgroup.mem_bot.1 (hle hzZ))

end Hodd

section ThreeRank

variable {Q : Type} [Group Q] [Finite Q]

theorem three_rank_of_iso (hLie : L34LieFacts12631) (X : Subgroup Q) {F' : Type} [Field F']
    [Finite F'] (hF4 : Nat.card F' = 4)
    (h : Nonempty (↥X ≃* PSL3Model F') ∨ Nonempty (↥X ≃* ↥(StatedSL 3 F'))) :
    ∃ A B : Subgroup Q, A ≤ X ∧ B ≤ X ∧ Nat.card A = 3 ∧ Nat.card B = 3 ∧
      A ≤ Subgroup.centralizer (B : Set Q) ∧ A ⊓ B = ⊥ := by
  rcases h with h | h
  · exact ((hLie F' hF4 Q X).1 h).three_rank
  · exact ((hLie F' hF4 Q X).2 h).three_rank

theorem le_of_inf_ne_bot_of_card_three {C X : Subgroup Q} (hC : Nat.card C = 3)
    (h : C ⊓ X ≠ ⊥) : C ≤ X := by
  have hd : Nat.card ↥(C ⊓ X) ∣ 3 := hC ▸ Subgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime Nat.prime_three).1 hd with h1 | h3
  · exact absurd (Subgroup.eq_bot_of_card_eq _ h1) h
  · have : C ⊓ X = C :=
      Subgroup.eq_of_le_of_card_ge (inf_le_left : C ⊓ X ≤ C) (by rw [h3, hC])
    exact this ▸ inf_le_right

end ThreeRank

theorem isPSL_three_two_two_props {Y : Type} [Group Y] (h : IsPSL 3 2 2 Y) :
    IsSimpleGroup Y ∧ Nat.card Y = 20160 := by
  refine ⟨(CFSG.LieType.Simplicity.fam_PSL_simplicity Y 3 2 2 h).2, ?_⟩
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have h1 := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := K) (n := 3)
    (by norm_num)
  rw [Nat.card_congr e.toEquiv, h1, hK]
  decide

theorem isQuasisimple_of_quot_psl {X : Type} [Group X] [Finite X] (hperf : commutator X = ⊤)
    (h : IsPSL 3 2 2 (X ⧸ Subgroup.center X)) : CFSG.IsQuasisimple X := by
  obtain ⟨hs, hc⟩ := isPSL_three_two_two_props h
  refine ⟨⟨hperf⟩, hs, ?_⟩
  by_contra hcomm
  push Not at hcomm
  exact not_comm_of_simple_card (X := X ⧸ Subgroup.center X) (by rw [hc]; norm_num)
    (fun a b => hcomm a b)

section ConjClosure

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem conjClosure_eq_of_psl_sl (hLie : L34LieFacts12631) (F : Frame126 T L V)
    (hH : Hyp126 G T L V) {H K : Subgroup G} (h918 : HypF918 T V L F.V1 F.V5 H K)
    (hq : CFSG.IsQuasisimple ↥(star H K))
    (hc3 : Nat.card ↥(Subgroup.center ↥(star H K)) ≤ 3) {F' : Type} [Field F'] [Finite F']
    (hF4 : Nat.card F' = 4)
    (hiso : Nonempty (↥(star H K) ≃* PSL3Model F') ∨
      Nonempty (↥(star H K) ≃* ↥(StatedSL 3 F'))) :
    conjClosure K T = K := by
  by_contra hne
  have h := h918.toHypF98.toHypF91
  have hTH : T ≤ H := h.T_le_H
  obtain ⟨t₀, ht₀, ht₀K⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (K : Set G) := by
    by_contra hall
    push Not at hall
    exact hne (le_antisymm (conjClosure_le fun t ht k hk =>
      (Subgroup.mem_normalizer_iff.1 (hall t ht) k).1 hk) (le_conjClosure K T))
  have hKc : K ∈ cComp H := h918.K_cComp
  have hK₂c : conjSub t₀ K ∈ cComp H := L1233.conjSub_mem_cComp hKc (hTH ht₀)
  have hKK₂ : K ≠ conjSub t₀ K := fun he => ht₀K (L1233.mem_normalizer_of_conjSub_eq he.symm)
  set X := star H K with hX
  set X₂ := star H (conjSub t₀ K) with hX₂
  have e₂ : ↥X₂ ≃* ↥X :=
    (MulEquiv.subgroupCongr (L1233.star_conjSub (hTH ht₀))).trans
      ((X.equivMapOfInjective _ (MulAut.conj _).injective).symm)
  have hq₂ : CFSG.IsQuasisimple ↥X₂ := CFSG.IsQuasisimple.of_mulEquiv e₂ hq
  have hC₁ : CFSG.IsComponent X :=
    ⟨hq, A3.subnormal_top_iff.mp (subnormal_of_mem_cComp (L1233.star_mem_cComp hKc))⟩
  have hC₂ : CFSG.IsComponent X₂ :=
    ⟨hq₂, A3.subnormal_top_iff.mp (subnormal_of_mem_cComp (L1233.star_mem_cComp hK₂c))⟩
  have hcomm : ∀ x ∈ X, ∀ y ∈ X₂, x * y = y * x := by
    rcases CFSG.LocalCores.distinct_components_commute hC₁ hC₂ with h1 | h1
    · exact absurd (L1233.star_injOn hKc hK₂c h1) hKK₂
    · intro x hx y hy
      have h2 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h1 hx
      exact (Subgroup.mem_centralizer_iff.1 h2 y hy).symm
  obtain ⟨A, B, hAX, hBX, hA3, hB3, hAB, hiAB⟩ := three_rank_of_iso hLie X hF4 hiso
  have hiso₂ : Nonempty (↥X₂ ≃* PSL3Model F') ∨ Nonempty (↥X₂ ≃* ↥(StatedSL 3 F')) := by
    rcases hiso with he | he
    · obtain ⟨e⟩ := he
      exact Or.inl ⟨e₂.trans e⟩
    · obtain ⟨e⟩ := he
      exact Or.inr ⟨e₂.trans e⟩
  obtain ⟨A', B', hA'X, hB'X, hA'3, hB'3, hA'B', hiA'B'⟩ := three_rank_of_iso hLie X₂ hF4 hiso₂
  have hC : ∃ C : Subgroup (HStar H), C ≤ X₂ ∧ Nat.card C = 3 ∧ C ⊓ X = ⊥ := by
    by_cases hA'' : A' ⊓ X = ⊥
    · exact ⟨A', hA'X, hA'3, hA''⟩
    by_cases hB'' : B' ⊓ X = ⊥
    · exact ⟨B', hB'X, hB'3, hB''⟩
    exfalso
    have hA'le : A' ≤ X := le_of_inf_ne_bot_of_card_three hA'3 hA''
    have hB'le : B' ≤ X := le_of_inf_ne_bot_of_card_three hB'3 hB''
    set Z' : Subgroup (HStar H) := (Subgroup.center ↥X).map X.subtype with hZ'
    have hZA : A' ≤ Z' := fun a ha =>
      ⟨⟨a, hA'le ha⟩, Subgroup.mem_center_iff.2 fun g =>
        Subtype.ext (hcomm g g.2 a (hA'X ha)), rfl⟩
    have hZB : B' ≤ Z' := fun a ha =>
      ⟨⟨a, hB'le ha⟩, Subgroup.mem_center_iff.2 fun g =>
        Subtype.ext (hcomm g g.2 a (hB'X ha)), rfl⟩
    have hcAB : ∀ a ∈ A', ∀ b ∈ B', a * b = b * a := fun a ha b hb =>
      hcomm a (hA'le ha) b (hB'X hb)
    have h9 := L1233.card_sup_of_commute hcAB hiA'B'
    rw [hA'3, hB'3] at h9
    have hle := Subgroup.card_le_of_le (sup_le hZA hZB)
    rw [h9, hZ', Subgroup.card_map_of_injective X.subtype_injective] at hle
    omega
  obtain ⟨C, hCX₂, hC3, hCX⟩ := hC
  refine false_of_three hH (pCoreOf_ne_bot h) hA3 hB3 hC3 hAB ?_ ?_ hiAB ?_
  · exact fun a ha => Subgroup.mem_centralizer_iff.2 fun c hc =>
      (hcomm a (hAX ha) c (hCX₂ hc)).symm
  · exact fun b hb => Subgroup.mem_centralizer_iff.2 fun c hc =>
      (hcomm b (hBX hb) c (hCX₂ hc)).symm
  · refine le_bot_iff.1 ?_
    calc (A ⊔ B) ⊓ C ≤ X ⊓ C := inf_le_inf_right C (sup_le hAX hBX)
      _ = ⊥ := by rw [inf_comm]; exact hCX

end ConjClosure

end S126P31

theorem kList12631_of
    (hLie : L34LieFacts12631) (h1229 : Lemma12_6_29)
    (h1230 : Lemma12_6_30) (hweak : KListWeak12631) : KList12631 := by
  intro G _ _ T L V _ F hH hZ H K hIs
  have h918 : HypF918 T V L F.V1 F.V5 H K := ((h1230 G T L V F hH hZ).2 H K hIs).2.2
  have hperf : ⁅star H K, star H K⁆ = star H K :=
    perfect_of_mem_cComp (L1233.star_mem_cComp h918.K_cComp)
  have hcomm : commutator ↥(star H K) = ⊤ := S126P31.commutator_eq_top_of_perfect hperf
  have hO2 : ∀ N : Subgroup (HStar H), N.Normal → IsPGroup 2 N → N = ⊥ :=
    fun N hn hp => S126P31.eq_bot_of_isPGroup hn hp
  have hsub : (star H K).IsSubnormal :=
    A3.subnormal_top_iff.mp (subnormal_of_mem_cComp (L1233.star_mem_cComp h918.K_cComp))
  have hodd : ∀ z ∈ Subgroup.center ↥(star H K), ∀ k : ℕ, z ^ 2 ^ k = 1 → z = 1 :=
    fun z hz k hzk => S126P31.eq_one_of_central_two_element hO2 hsub hz hzk
  rcases hweak h1229 G T L V F hH hZ H K hIs h918 with hA | hP
  · exact Or.inl (S126P31.mulEquiv_alt5_of_central_quotient hcomm hodd hA.some)
  · obtain ⟨F', hFld, hFin, hF4, hiso⟩ :=
      S126P31.exists_mulEquiv_psl_or_sl_of_quotient hcomm hodd hP
    have hq : CFSG.IsQuasisimple ↥(star H K) := S126P31.isQuasisimple_of_quot_psl hcomm hP
    have hc3 : Nat.card ↥(Subgroup.center ↥(star H K)) ≤ 3 :=
      Nat.le_of_dvd (by norm_num) (S126P31.card_center_dvd_three_of_quotient hcomm hodd hP)
    exact Or.inr ⟨S126P31.conjClosure_eq_of_psl_sl hLie F hH h918 hq hc3 hF4 hiso,
      F', hFld, hFin, hF4, hiso⟩

end CFSG.Quasithin.H13
