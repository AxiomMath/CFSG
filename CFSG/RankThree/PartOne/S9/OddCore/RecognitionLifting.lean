module

public import CFSG.RankThree.PartOne.S9.OddCore.RecognitionBasic
public import CFSG.RankThree.PartOne.S9.StatementsTwoAction

public section

namespace CFSG.RankThree.PartOne.OddCore37

open CFSG CFSG.Assembly.RankThreeEven
open scoped commutatorElement

section Local

variable {G : Type*} [Group G] [Finite G]

theorem pRank_le_localRank_of_le_normalizer {q : ℕ} (hq : q.Prime) {T D : Subgroup G}
    (hT0 : T ≠ ⊥) (hT2 : IsPGroup 2 T) (hD : D ≤ Subgroup.normalizer (T : Set G)) :
    CFSG.pRank q ↥D ≤ localRank q G := by
  refine (pRank_le_of_le hq hD).trans ?_
  rw [← assembly_pRank_eq hq]
  exact CFSG.RankThree.Classical.pRank_le_localRank hq.one_lt ⟨T, hT0, hT2, rfl⟩

omit [Finite G] in
theorem le_normalizer_map_subtype (H : Subgroup G) (N : Subgroup ↥H) [N.Normal] :
    H ≤ Subgroup.normalizer ((N.map H.subtype : Subgroup G) : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨⟨h, hh⟩ * n * ⟨h, hh⟩⁻¹, Subgroup.Normal.conj_mem inferInstance n hn ⟨h, hh⟩, rfl⟩
  · rintro ⟨n, hn, hne⟩
    refine ⟨⟨h, hh⟩⁻¹ * n * ⟨h, hh⟩, by
      simpa using Subgroup.Normal.conj_mem inferInstance n hn ⟨h, hh⟩⁻¹, ?_⟩
    have hne' : (n : G) = h * g * h⁻¹ := hne
    change h⁻¹ * (n : G) * h = g
    rw [hne']
    group

end Local

section Omega

variable {G G' : Type*} [Group G] [Group G']

theorem map_omegaOne (f : G →* G') (hf : Function.Injective f) (q : ℕ) (K : Subgroup G) :
    (omegaOne q K).map f = omegaOne q (K.map f) := by
  unfold omegaOne
  rw [MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨hxK, hxq⟩, rfl⟩
    exact ⟨Subgroup.mem_map_of_mem f hxK, by rw [← map_pow, hxq, map_one]⟩
  · rintro ⟨⟨x, hxK, rfl⟩, hyq⟩
    exact ⟨x, ⟨hxK, hf (by rw [map_pow, map_one]; exact hyq)⟩, rfl⟩

theorem le_omegaOne {q : ℕ} {K D : Subgroup G} (hDK : D ≤ K) (hD : ∀ x ∈ D, x ^ q = 1) :
    D ≤ omegaOne q K :=
  fun x hx => Subgroup.subset_closure ⟨hDK hx, hD x hx⟩

end Omega

section Comparison

variable {G : Type*} [Group G]

theorem commutator_le_center_of_inf_centralizer {X : Subgroup G}
    (hz : X ⊓ Subgroup.centralizer (X : Set G) = ⁅X, X⁆) :
    commutator ↥X ≤ Subgroup.center ↥X := by
  rw [commutator_def, Subgroup.commutator_le]
  intro x _ y _
  rw [Subgroup.mem_center_iff]
  intro z
  have hxy : ((⁅x, y⁆ : ↥X) : G) ∈ ⁅X, X⁆ := Subgroup.commutator_mem_commutator x.2 y.2
  rw [← hz] at hxy
  exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hxy.2 z z.2)

variable [Finite G]

theorem false_of_le_extraspecial {q : ℕ} (hq : q.Prime) {D X : Subgroup G}
    (hD : IsElementaryAbelian q D) (hDcard : Nat.card D = q ^ 4) (hDX : D ≤ X)
    (hXcard : Nat.card X = q ^ 5) (hcomm : Nat.card (⁅X, X⁆ : Subgroup G) = q)
    (hz : X ⊓ Subgroup.centralizer (X : Set G) = ⁅X, X⁆) : False := by
  have hclass := commutator_le_center_of_inf_centralizer hz
  set D' : Subgroup ↥X := D.subgroupOf X with hD'
  have hD'card : Nat.card D' = q ^ 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDX).toEquiv, hDcard]
  have hcen : Nat.card (Subgroup.center ↥X) = q := by
    rw [← Subgroup.card_map_of_injective X.subtype_injective,
      CFSG.SectionRank.Ccomm.map_center_subtype, hz, hcomm]
  obtain ⟨x, hx⟩ : ∃ x : ↥X, x ∉ D' := by
    by_contra hall
    push Not at hall
    have htop : D' = ⊤ := eq_top_iff.2 fun y _ => hall y
    rw [htop, Subgroup.card_top, hXcard] at hD'card
    have hlt : q ^ 4 < q ^ 5 := Nat.pow_lt_pow_right hq.one_lt (by norm_num)
    omega
  have hlt : D' < D' ⊔ Subgroup.zpowers x :=
    lt_of_le_of_ne le_sup_left fun h =>
      hx (h ▸ (le_sup_right : Subgroup.zpowers x ≤ D' ⊔ Subgroup.zpowers x)
        (Subgroup.mem_zpowers x))
  have hXcard' : Nat.card ↥X = Nat.card D' * q := by
    rw [hD'card, show Nat.card ↥X = q ^ 5 from hXcard]
    ring
  have htop := CFSG.RankThree.PartTwo.eq_top_of_lt_of_card_eq_mul hq hlt hXcard'
  have hsub : D' ⊓ Subgroup.centralizer {x} ≤ Subgroup.center ↥X := by
    rintro d ⟨hd, hdx⟩
    rw [Subgroup.mem_center_iff]
    have hDc : D' ≤ Subgroup.centralizer ({d} : Set ↥X) := by
      intro e he
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hed := hD.toIsMulCommutative.is_comm.comm (⟨(e : G), Subgroup.mem_subgroupOf.1 he⟩ : D)
        ⟨(d : G), Subgroup.mem_subgroupOf.1 hd⟩
      have hed' : (e : G) * (d : G) = (d : G) * (e : G) := congrArg Subtype.val hed
      exact Subtype.ext hed'
    have hxc : x ∈ Subgroup.centralizer ({d} : Set ↥X) :=
      Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_singleton_iff.1 hdx).symm
    have hle : D' ⊔ Subgroup.zpowers x ≤ Subgroup.centralizer ({d} : Set ↥X) :=
      sup_le hDc (Subgroup.zpowers_le.2 hxc)
    intro g
    have hg : g ∈ Subgroup.centralizer ({d} : Set ↥X) := hle (htop ▸ Subgroup.mem_top g)
    exact (Subgroup.mem_centralizer_singleton_iff.1 hg)
  have h1 := CFSG.RankThree.PartTwo.card_le_card_inf_centralizer_mul hclass x D'
  have h2 : Nat.card (D' ⊓ Subgroup.centralizer {x} : Subgroup ↥X) ≤ q := by
    rw [← hcen]
    exact Subgroup.card_le_of_le hsub
  rw [hD'card, hcen] at h1
  have h3 : q ^ 4 ≤ q * q := h1.trans (Nat.mul_le_mul_right q h2)
  have h4 : q * q < q ^ 4 := by
    have : q ^ 2 < q ^ 4 := Nat.pow_lt_pow_right hq.one_lt (by norm_num)
    nlinarith
  omega

end Comparison


section Eq

variable {G : Type*} [Group G] [Finite G]

theorem eq_of_isQDShape_le {q : ℕ} (hq : q.Prime) {D X : Subgroup G} (hD : IsQDShape q D)
    (hX : IsQDShape q X) (hDX : D ≤ X) : D = X := by
  have hle := Subgroup.card_le_of_le hDX
  have h45 : q ^ 4 < q ^ 5 := Nat.pow_lt_pow_right hq.one_lt (by norm_num)
  rcases isQDShape_card hD with hDc | hDc <;> rcases isQDShape_card hX with hXc | hXc
  · exact Subgroup.eq_of_le_of_card_ge hDX (by rw [hXc, hDc])
  · exfalso
    rcases hD with ⟨hel, -⟩ | ⟨-, hc, -⟩
    · rcases hX with ⟨-, hc⟩ | ⟨-, -, hcomm, hz, -⟩
      · omega
      · exact false_of_le_extraspecial hq hel hDc hDX hXc hcomm hz
    · omega
  · omega
  · exact Subgroup.eq_of_le_of_card_ge hDX (by rw [hXc, hDc])

end Eq

end CFSG.RankThree.PartOne.OddCore37

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly.RankThreeEven CFSG.RankThree.GroupTheory
open CFSG.RankThree.PartOne.OddCore37
open scoped commutatorElement

theorem smallOddCoreActionLiftingInsideLocalGroup_of (hI2 : TwoLocalRankTwoOddCoreAction) :
    SmallOddCoreActionLiftingInsideLocalGroup := by
  intro G _ _ q hq hq5 hloc H A R Q D hAH hA hRH hAR hR2 hRA hRqd hQsyl hRAQ hDQ hDchar hRD
    hDshape
  have : Fact q.Prime := ⟨hq⟩
  set J : Subgroup ↥H := pCore 2 ↥H with hJ
  set π := QuotientGroup.mk' J with hπ
  set F' : Subgroup ↥H := (pCore q (↥H ⧸ J)).comap π with hF'
  set F : Subgroup G := F'.map H.subtype with hF
  obtain ⟨hQF, hQp, hQidx⟩ := hQsyl
  have hFH : F ≤ H := Subgroup.map_subtype_le _
  have hDH : D ≤ H := hDQ.trans (hQF.trans hFH)
  have hD3 : 3 ≤ CFSG.pRank q ↥D := three_le_pRank_of_isQDShape hq hDshape
  have hJbot : J = ⊥ := by
    by_contra hJne
    have hJ'0 : J.map H.subtype ≠ ⊥ := fun h =>
      hJne ((Subgroup.map_eq_bot_iff_of_injective J H.subtype_injective).1 h)
    have hJ'2 : IsPGroup 2 (J.map H.subtype) := (pCore_isPGroup (p := 2) (G := ↥H)).map _
    have hHN := le_normalizer_map_subtype H J
    have := pRank_le_localRank_of_le_normalizer hq hJ'0 hJ'2 (hDH.trans hHN)
    omega
  have hπinj : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, hπ, QuotientGroup.ker_mk', hJbot]
  have hF'eq : F' = pCore q ↥H := by
    apply le_antisymm
    · exact le_sSup ⟨Subgroup.Normal.comap pCore_normal π,
        (pCore_isPGroup (p := q) (G := ↥H ⧸ J)).comap_of_injective π hπinj⟩
    · intro x hx
      have hmap : (pCore q ↥H).map π ≤ pCore q (↥H ⧸ J) :=
        le_sSup ⟨Subgroup.Normal.map pCore_normal π (QuotientGroup.mk'_surjective J),
          (pCore_isPGroup (p := q) (G := ↥H)).map π⟩
      exact hmap (Subgroup.mem_map_of_mem π hx)
  have hFeq : F = inSubgroup (pCore q) H := by
    rw [hF, hF'eq]
    rfl
  have hFp : IsPGroup q F := by
    rw [hFeq]
    exact (pCore_isPGroup (p := q) (G := ↥H)).map _
  have hFQ : F ≤ Q := by
    obtain ⟨n, hn⟩ := hFp.index (Q.subgroupOf F)
    have hn0 : n = 0 := by
      by_contra hn0
      exact hQidx (by rw [Subgroup.relIndex, hn]; exact dvd_pow_self q hn0)
    rw [hn0, pow_zero] at hn
    exact Subgroup.relIndex_eq_one.1 hn
  have hQeq : Q = inSubgroup (pCore q) H := (le_antisymm hQF hFQ).trans hFeq
  have hAA : Nat.card (A.subgroupOf H) = 5 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv, hA]
  have hRne : R ≠ ⊥ := by
    obtain ⟨e⟩ := hRqd
    intro h
    have h1 : Nat.card R = 1 := by rw [h, Subgroup.card_bot]
    have h2 : Nat.card R = Nat.card QD32 := Nat.card_congr e.toEquiv
    rw [h1, CFSG.RankThree.GroupTheory.card_QD32] at h2
    omega
  have hRR : Subgroup.map H.subtype (R.subgroupOf H) = R := Subgroup.map_subgroupOf_eq_of_le hRH
  have hAA' : Subgroup.map H.subtype (A.subgroupOf H) = A := Subgroup.map_subgroupOf_eq_of_le hAH
  have hRne' : R.subgroupOf H ≠ ⊥ := fun h => hRne (by rw [← hRR, h, Subgroup.map_bot])
  have hnorm : A.subgroupOf H ≤ Subgroup.normalizer ((R.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro r
    have := Subgroup.mem_normalizer_iff.1 (hAR (Subgroup.mem_subgroupOf.1 ha)) (r : G)
    simpa [Subgroup.mem_subgroupOf] using this
  have hcomm : ⁅R.subgroupOf H, A.subgroupOf H⁆ = R.subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator, hRR, hAA', hRA]
  have hRO : ⁅R.subgroupOf H, pCore q ↥H⁆ ≠ ⊥ := by
    intro h
    apply hRD
    have h1 := congrArg (Subgroup.map H.subtype) h
    rw [Subgroup.map_commutator, hRR, Subgroup.map_bot] at h1
    refine le_bot_iff.1 ?_
    rw [← h1]
    refine Subgroup.commutator_mono le_rfl ?_
    rw [hQeq] at hDQ
    exact hDQ
  have hR2' : IsPGroup 2 (R.subgroupOf H) := hR2.of_equiv (Subgroup.subgroupOfEquivOfLe hRH).symm
  obtain ⟨-, -, hX⟩ := hI2 ↥H 5 q (A.subgroupOf H) (R.subgroupOf H) (by norm_num) hq
    (by norm_num) (by omega) (by omega) hAA hnorm hR2' hRne' hcomm hRO
    ((localRank_subgroup_le hq H).trans hloc)
  have hXshape : IsQDShape q (omegaOne q (inSubgroup (pCore q) H)) := by
    have h1 := (isQDShape_map_iff H.subtype H.subtype_injective q _).2 hX
    rw [map_omegaOne H.subtype H.subtype_injective] at h1
    exact h1
  have hDX : D ≤ omegaOne q (inSubgroup (pCore q) H) :=
    le_omegaOne (hQeq ▸ hDQ) (isQDShape_pow_eq_one hDshape)
  refine ⟨?_, hQeq, eq_of_isQDShape_le hq hDshape hXshape hDX⟩
  show J.map H.subtype = ⊥
  rw [hJbot, Subgroup.map_bot]

end CFSG.RankThree.PartOne
