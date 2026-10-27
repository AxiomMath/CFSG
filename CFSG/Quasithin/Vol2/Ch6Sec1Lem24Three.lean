module

public import CFSG.Quasithin.Background.A1bLemma126
public import CFSG.Quasithin.Vol2.Ch5Sec1BorelTorus
public import CFSG.Quasithin.Vol2.Ch5Sec1Hall
public import CFSG.Quasithin.Vol2.Ch6Sec1GreenBook

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped commutatorElement

section Generic

variable {G : Type} [Group G]

theorem conj_commutatorElement_eq {x w v a b : G} (hw : x * w * x⁻¹ = a * w)
    (hv : x * v * x⁻¹ = b * v) (haw : Commute a w) (hav : Commute a v) (hbw : Commute b w)
    (hbv : Commute b v) (hab : Commute a b) : x * ⁅w, v⁆ * x⁻¹ = ⁅w, v⁆ := by
  have hbc : Commute b ⁅w, v⁆ := by
    rw [commutatorElement_def]
    exact ((hbw.mul_right hbv).mul_right hbw.inv_right).mul_right hbv.inv_right
  have hav' : Commute a (b * v) := hab.mul_right hav
  calc x * ⁅w, v⁆ * x⁻¹
      = (x * w * x⁻¹) * (x * v * x⁻¹) * (x * w * x⁻¹)⁻¹ * (x * v * x⁻¹)⁻¹ := by
        rw [commutatorElement_def]; group
    _ = (a * w) * (b * v) * (a * w)⁻¹ * (b * v)⁻¹ := by rw [hw, hv]
    _ = w * (a * (b * v) * a⁻¹) * w⁻¹ * (b * v)⁻¹ := by rw [haw.eq]; group
    _ = w * (b * v) * w⁻¹ * (b * v)⁻¹ := by rw [hav'.mul_inv_cancel]
    _ = b * ⁅w, v⁆ * b⁻¹ := by
        rw [commutatorElement_def, show w * (b * v) = b * w * v by rw [← mul_assoc, ← hbw.eq]]
        group
    _ = ⁅w, v⁆ := hbc.mul_inv_cancel

end Generic

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {n : ℕ}

namespace Hyp6116

theorem centralizerMod_normalizer_le (h432 : Stmt4_3_2) (h6111 : Stmt6_1_11)
    (h6119 : Stmt6_1_19) (h : Hyp6116 G T M L V n) :
    centralizerMod (ch6ZS T L V) (Subgroup.normalizer (ch6ZS T L V : Set G))
        (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G))) ≤
      Subgroup.centralizer (ch6ZS T L V : Set G) := by
  set Z := ch6ZS T L V with hZ
  set I := Subgroup.centralizer (Z : Set G) with hI
  set U := conjClosure V I with hU
  have hnab := h.lemma_6_1_20_two h432 h6111 h6119
  obtain ⟨u, huU, huC⟩ : ∃ u ∈ U, u ∉ Subgroup.centralizer (U : Set G) := by
    by_contra hcon
    push Not at hcon
    exact hnab ⟨⟨fun a b =>
      Subtype.ext ((Subgroup.mem_centralizer_iff.mp (hcon _ a.2)) _ b.2).symm⟩⟩
  have hZU : ⁅U, Subgroup.zpowers u⁆ = Z := h.lemma_6_1_20_three h432 u huU huC
  have hZV : Z ≤ V := inf_le_left
  have hUI : U ≤ I :=
    (h.lemma_6_1_20_one h432).1.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 I)
  have hcomm : ∀ w ∈ U, ∀ z ∈ Z, Commute z w := fun w hw z hz =>
    (Subgroup.mem_centralizer_iff.mp (hUI hw) z hz)
  have hZZ : ∀ z ∈ Z, ∀ z' ∈ Z, Commute z z' := fun z hz z' hz' =>
    hcomm z' (le_conjClosure V I (hZV hz')) z hz
  intro x hx
  obtain ⟨-, -, hxU⟩ := mem_centralizerMod.mp hx
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [← hZU] at hz
  have hle : ⁅U, Subgroup.zpowers u⁆ ≤ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.commutator_le]
    intro w hw v hv
    have hvU : v ∈ U := Subgroup.zpowers_le.mpr huU hv
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have ha := hxU w hw
    have hb := hxU v hvU
    have key := conj_commutatorElement_eq (x := x) (w := w) (v := v)
      (a := x * w * x⁻¹ * w⁻¹) (b := x * v * x⁻¹ * v⁻¹) (by group) (by group)
      (hcomm w hw _ ha) (hcomm v hvU _ ha) (hcomm w hw _ hb) (hcomm v hvU _ hb) (hZZ _ ha _ hb)
    calc x * ⁅w, v⁆ = x * ⁅w, v⁆ * x⁻¹ * x := by group
      _ = ⁅w, v⁆ * x := by rw [key]
  have hzx := Subgroup.mem_centralizer_iff.mp (hle hz) x rfl
  exact hzx.symm

theorem lemma_6_1_24_three (h432 : Stmt4_3_2) (h6111 : Stmt6_1_11) (h6119 : Stmt6_1_19)
    (h : Hyp6116 G T M L V n) {l : G} (hl : l ∈ L)
    (hlN : l ∉ Subgroup.normalizer (ch6ZS T L V : Set G)) :
    ∀ N : Subgroup G,
      centralizerMod (ch6ZS T L V) (Subgroup.centralizer (ch6ZS T L V : Set G))
          (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G))) ≤ N →
      N ≤ Subgroup.centralizer (ch6ZS T L V : Set G) →
      Subgroup.centralizer (ch6ZS T L V : Set G) ≤ Subgroup.normalizer (N : Set G) →
      ∀ _ : ((centralizerMod (ch6ZS T L V) (Subgroup.centralizer (ch6ZS T L V : Set G))
          (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)))).subgroupOf N).Normal,
        Group.IsNilpotent (↥N ⧸ (centralizerMod (ch6ZS T L V)
          (Subgroup.centralizer (ch6ZS T L V : Set G))
          (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)))).subgroupOf N) →
        ⁅pCoreOf 2 (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ⊔
            conjSubgroup (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G))) l), N⁆ ≤
          centralizerMod (ch6ZS T L V) (Subgroup.normalizer (ch6ZS T L V : Set G))
            (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCHI := h.centralizerMod_normalizer_le h432 h6111 h6119
  have h1 := h.lemma_6_1_24_one h432 h6111 h6119 hl hlN
  obtain ⟨hRel, -, hRD⟩ := h.lemma_6_1_24_two h432 h6111 h6119 hl hlN
  have h4 := h.lemma_6_1_24_four h432
  have h21 := stmt6_1_21 h432 h6111 h6119 G T M L V n h l hl hlN
  dsimp only at h21
  have h17 := (stmt6_1_17 h432 G T M L V n h _ h.isInHS_sup).2.2.1
  rw [inf_eq_right.mpr le_sup_left, h.conjClosure_sup_T_eq] at h17
  have hUeq := h.conjClosure_normalizer_eq h432
  obtain ⟨hUO, -⟩ := h.lemma_6_1_20_one h432
  set Z := ch6ZS T L V with hZ
  set I := Subgroup.centralizer (Z : Set G) with hI
  set H := Subgroup.normalizer (Z : Set G) with hH
  set U := conjClosure V I with hU
  set R := pCoreOf 2 (U ⊔ conjSubgroup U l) with hR
  set CI := centralizerMod Z I U with hCI
  set CH := centralizerMod Z H U with hCH
  intro N hCN hNI hIN hCNn hnil
  have hZV : Z ≤ V := inf_le_left
  have hIH : I ≤ H := Subgroup.centralizer_le_normalizer _
  have hHI : H ≤ Subgroup.normalizer (I : Set G) := F7.normalizer_le_normalizer_centralizer _
  have hHU : H ≤ Subgroup.normalizer (U : Set G) := by
    have := le_normalizer_conjClosure V H
    rwa [hUeq] at this
  have hCHH : CH ≤ H := centralizerMod_le_left _ _ _
  have hCHeq : CH = CI :=
    le_antisymm (fun x hx => ⟨hCHI hx, hx.2.1, hx.2.2⟩) (centralizerMod_mono_left U hIH)
  have hCH2 : IsPGroup 2 CH := by
    have e : CH = pCoreOf 2 I := hCHeq.trans h17.symm
    rw [e]
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  obtain ⟨⟨-, -, hL1⟩, ⟨hRAB, -⟩, -, -, hRMV, -⟩ := h21
  have hRI : R ≤ I := by
    rw [hRAB]
    refine sup_le (inf_le_left.trans (hUO.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 I))) ?_
    exact inf_le_right.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hZV))
  have hRH : R ≤ H := hRI.trans hIH
  obtain ⟨DL, hDL⟩ := h.toHyp5_0_1.exists_isHall_borel
  have hcDL := (h.toHyp5_0_1.isCyclic_card_of_isHall l2TorusFact hDL).2
  have hDL1 : DL ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hcDL
    have h22 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h.two_le
    omega
  have hDH : DL ≤ H := hDL.1.trans h.toHyp611Nat.borelL_le_normalizer_ZS
  have hDR : DL ≤ Subgroup.normalizer (R : Set G) := by
    have hDX : DL ≤ U ⊔ conjSubgroup U l := by
      rw [hL1]
      exact (hDL.1.trans inf_le_left).trans le_sup_left
    exact hDX.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hRD' := hRD DL hDL DL le_rfl hDL1
  have hCUV : U ⊓ Subgroup.centralizer (V : Set G) ≤ CH := by
    rw [h1]
    exact centralizerMod_mono_left U hRH
  have hHCH : H ≤ Subgroup.normalizer (CH : Set G) :=
    le_normalizer_centralizerMod le_rfl Subgroup.le_normalizer hHU
  set C' : Subgroup ↥H := CH.subgroupOf H with hC'
  have hC'n : C'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hCHH).mpr hHCH
  have hC'2 : IsPGroup 2 C' := hCH2.of_equiv (Subgroup.subgroupOfEquivOfLe hCHH).symm
  set π : ↥H →* ↥H ⧸ C' := QuotientGroup.mk' C' with hπ
  have hπ1 : ∀ x : ↥H, π x = 1 ↔ (x : G) ∈ CH := fun x => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf
  have hbar : ∀ (X : Subgroup G) (Y : Subgroup (↥H ⧸ C')),
      (∀ x (hx : x ∈ X) (hxH : x ∈ H), π ⟨x, hxH⟩ ∈ Y) → (X.subgroupOf H).map π ≤ Y := by
    rintro X Y hXY _ ⟨x, hx, rfl⟩
    exact hXY x hx x.2
  have hmem : ∀ {X : Subgroup G} {x : G} (hx : x ∈ X) (hxH : x ∈ H),
      π ⟨x, hxH⟩ ∈ (X.subgroupOf H).map π := fun {X x} hx hxH =>
    ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have hnorm : ∀ {X Y : Subgroup G}, Y ≤ Subgroup.normalizer (X : Set G) →
      (Y.subgroupOf H).map π ≤ Subgroup.normalizer (((X.subgroupOf H).map π : Subgroup _) :
        Set (↥H ⧸ C')) := by
    intro X Y hYX
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hyx : (y : G) * x * (y : G)⁻¹ ∈ X :=
        (Subgroup.mem_normalizer_iff.mp (hYX (Subgroup.mem_subgroupOf.mp hy)) x).mp
          (Subgroup.mem_subgroupOf.mp hx)
      refine ⟨y * x * y⁻¹, Subgroup.mem_subgroupOf.mpr hyx, ?_⟩
      rw [map_mul, map_mul, map_inv]
    · intro hw
      obtain ⟨w', rfl⟩ : ∃ w', π w' = w := QuotientGroup.mk'_surjective C' w
      obtain ⟨x, hx, hxw⟩ := hw
      have hx' : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hx
      have hyx : (y : G)⁻¹ * x * (y : G)⁻¹⁻¹ ∈ X :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _
          (hYX (Subgroup.mem_subgroupOf.mp hy))) x).mp hx'
      refine ⟨y⁻¹ * x * y, Subgroup.mem_subgroupOf.mpr (by simpa using hyx), ?_⟩
      rw [map_mul, map_mul, map_inv, hxw]
      group
  set Ib := (I.subgroupOf H).map π with hIb
  set Rb := (R.subgroupOf H).map π with hRb
  set Nb := (N.subgroupOf H).map π with hNb
  set Db := (DL.subgroupOf H).map π with hDb
  have hRIb : Rb ≤ Ib := Subgroup.map_mono fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hRI (Subgroup.mem_subgroupOf.mp hx))
  have hNIb : Nb ≤ Ib := Subgroup.map_mono fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hNI (Subgroup.mem_subgroupOf.mp hx))
  have hIbn : (⊤ : Subgroup (↥H ⧸ C')) ≤ Subgroup.normalizer (Ib : Set (↥H ⧸ C')) := by
    rintro w -
    obtain ⟨w', rfl⟩ : ∃ w', π w' = w := QuotientGroup.mk'_surjective C' w
    exact hnorm (X := I) (Y := H) hHI (hmem w'.2 w'.2)
  have hNbn : Ib ≤ Subgroup.normalizer (Nb : Set (↥H ⧸ C')) := hnorm hIN
  have hRbel : IsElemAbelian 2 Rb := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
    · obtain ⟨_, ⟨r, hr, rfl⟩⟩ := a
      obtain ⟨_, ⟨s, hs, rfl⟩⟩ := b
      apply Subtype.ext
      have hrs := (hRel r (Subgroup.mem_subgroupOf.mp hr) s (Subgroup.mem_subgroupOf.mp hs)).1
      have h1' : π (r * s * r⁻¹ * s⁻¹) = 1 := (hπ1 _).mpr (hCUV hrs)
      simp only [Subgroup.coe_mul]
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1'
      calc π r * π s = π r * π s * (π r)⁻¹ * (π s)⁻¹ * (π s * π r) := by group
        _ = π s * π r := by rw [h1', one_mul]
    · obtain ⟨r, hr, rfl⟩ := ha
      have hr2 := (hRel r (Subgroup.mem_subgroupOf.mp hr) r (Subgroup.mem_subgroupOf.mp hr)).2
      rw [← map_pow]
      exact (hπ1 _).mpr (hCUV hr2)
  have hRb2 : IsPGroup 2 Rb := CFSG.Quasithin.B2F.isPGroup_of_isElemAbelian hRbel
  have hRbD : ⁅Rb, Db⁆ = Rb := by
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      rintro _ ⟨r, hr, rfl⟩ _ ⟨d, hd, rfl⟩
      have hrd : (r : G) * d * (r : G)⁻¹ * (d : G)⁻¹ ∈ R := by
        have e : (r : G) * d * (r : G)⁻¹ * (d : G)⁻¹ = r * (d * (r : G)⁻¹ * (d : G)⁻¹) := by
          group
        rw [e]
        exact R.mul_mem (Subgroup.mem_subgroupOf.mp hr) ((Subgroup.mem_normalizer_iff.mp
          (hDR (Subgroup.mem_subgroupOf.mp hd)) _).mp (R.inv_mem (Subgroup.mem_subgroupOf.mp hr)))
      have := hmem hrd (hRH hrd)
      have e : ⁅π r, π d⁆ = π (r * d * r⁻¹ * d⁻¹) := by
        rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]
      rw [e]
      exact this
    ·
      have hpre : R ≤ (⁅Rb, Db⁆.comap π).map H.subtype := by
        rw [hRD']
        refine sup_le ?_ ?_
        · rw [Subgroup.commutator_le]
          intro r hr d hd
          have hrH := hRH hr
          have hdH := hDH hd
          refine ⟨⟨r, hrH⟩ * ⟨d, hdH⟩ * ⟨r, hrH⟩⁻¹ * ⟨d, hdH⟩⁻¹, ?_, rfl⟩
          show π (⟨r, hrH⟩ * ⟨d, hdH⟩ * ⟨r, hrH⟩⁻¹ * ⟨d, hdH⟩⁻¹) ∈ ⁅Rb, Db⁆
          rw [map_mul, map_mul, map_mul, map_inv, map_inv]
          exact Subgroup.commutator_mem_commutator (hmem hr hrH) (hmem hd hdH)
        · intro x hx
          refine ⟨⟨x, hCHH (hCUV hx)⟩, ?_, rfl⟩
          show π ⟨x, _⟩ ∈ ⁅Rb, Db⁆
          rw [(hπ1 _).mpr (hCUV hx)]
          exact Subgroup.one_mem _
      refine hbar R _ fun x hx hxH => ?_
      obtain ⟨y, hy, hyx⟩ := hpre hx
      have : y = ⟨x, hxH⟩ := Subtype.ext hyx
      rw [← this]
      exact hy
  have hDb_odd : Odd (Nat.card Db) := by
    have hdvd : Nat.card Db ∣ Nat.card DL := by
      have := Subgroup.card_map_dvd (DL.subgroupOf H) π
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDH).toEquiv] at this
    exact Odd.of_dvd_nat hDL.2.1 hdvd
  have hDres : opResidual 2 Db = Db := by
    refine le_antisymm (opResidual_le 2 Db) fun x hx => mem_opResidual_of_coprime hx ?_
    have hodd : Odd (orderOf x) :=
      Odd.of_dvd_nat hDb_odd (Subgroup.orderOf_dvd_natCard Db hx)
    exact (Nat.coprime_two_right.mpr hodd)
  have hO2H : pCoreOf 2 H ≠ ⊥ := by
    intro hb
    have hle : Z ≤ pCoreOf 2 H := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      Subgroup.le_normalizer le_rfl
      ((CFSG.Quasithin.B2F.isPGroup_of_isElemAbelian h.toHyp611.isElemAbelian).to_le hZV)
    rw [hb, le_bot_iff] at hle
    exact h.toHyp611Nat.ZS_ne_bot hle
  have hSQ := isSQTKSub_of_inH h.qtke h.simple h.nonabelian
    (⟨h.toHyp611Nat.T_le_normalizer_ZS, hO2H⟩ : InH T H)
  have hrank : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ X : Subgroup (↥H ⧸ C'),
      CFSG.Open.pRank p X ≤ 2 := by
    intro p hp hp2 X
    have : Fact p.Prime := ⟨hp⟩
    calc CFSG.Open.pRank p X ≤ CFSG.Open.pRank p (⊤ : Subgroup (↥H ⧸ C')) :=
          CFSG.SectionRank.pRank_mono hp.one_lt le_top
      _ = CFSG.Open.pRank p (⊤ : Subgroup ↥H) :=
          CFSG.SectionRank.pRank_quotient_two_group C' hC'2 hp hp2
      _ ≤ 2 := hSQ.2 p hp hp2
  set H₁ := Ib ⊔ Db with hH₁
  have hH₁I : H₁ ≤ Subgroup.normalizer (Ib : Set (↥H ⧸ C')) := le_top.trans hIbn
  have hq : ∀ q : ℕ, q.Prime → q ≠ 2 → Rb ≤ Subgroup.centralizer (pCoreOf q Ib : Set _) := by
    intro q hq hq2
    have : Fact q.Prime := ⟨hq⟩
    have hc := centralizes_pCoreOf hq2 (le_sup_right : Db ≤ H₁) hDres
      (hRIb.trans le_sup_left) hRb2 hRbD hRbel (hrank q hq hq2 _)
    have hle : pCoreOf q Ib ≤ pCoreOf q H₁ :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer q
        ((CFSG.LieType.BorelTits.pCoreOf_le q Ib).trans le_sup_left)
        (hH₁I.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf q Ib))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup q Ib)
    exact hc.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hle))
  have hO2I : pCoreOf 2 Ib = ⊥ := by
    set P := ((pCoreOf 2 Ib).comap π).map H.subtype with hP
    have hPmem : ∀ x : ↥H, (x : G) ∈ P ↔ π x ∈ pCoreOf 2 Ib := fun x => by
      constructor
      · rintro ⟨y, hy, hyx⟩
        rwa [show y = x from Subtype.ext hyx] at hy
      · intro hx
        exact ⟨x, hx, rfl⟩
    have hPI : P ≤ I := by
      rintro _ ⟨y, hy, rfl⟩
      show (y : G) ∈ I
      obtain ⟨i, hi, hiy⟩ := CFSG.LieType.BorelTits.pCoreOf_le 2 Ib hy
      have hk : π (i⁻¹ * y) = 1 := by rw [map_mul, map_inv, hiy, inv_mul_cancel]
      have hiyC := hCHI ((hπ1 _).mp hk)
      have e : (y : G) = (i : G) * ((i⁻¹ * y : ↥H) : G) := by simp
      rw [e]
      exact I.mul_mem (Subgroup.mem_subgroupOf.mp hi) hiyC
    have hIP : I ≤ Subgroup.normalizer (P : Set G) := by
      intro i hi
      refine mem_normalizer_of_forall_conj_mem_of_le fun x hx => ?_
      have hxH : x ∈ H := Subgroup.map_subtype_le _ hx
      have hiH : i ∈ H := hIH hi
      have hx' := (hPmem ⟨x, hxH⟩).mp hx
      have hc : π (⟨i, hiH⟩ * ⟨x, hxH⟩ * ⟨i, hiH⟩⁻¹) ∈ pCoreOf 2 Ib := by
        rw [map_mul, map_mul, map_inv]
        exact (Subgroup.mem_normalizer_iff.mp
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Ib (hmem hi hiH)) _).mp hx'
      exact (hPmem ⟨i * x * i⁻¹, H.mul_mem (H.mul_mem hiH hxH) (H.inv_mem hiH)⟩).mpr hc
    have hP2 : ∀ x ∈ P, ∃ k : ℕ, x ^ 2 ^ k ∈ CI := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Ib ⟨π y, hy⟩
      refine ⟨k, ?_⟩
      have hk' : π (y ^ 2 ^ k) = 1 := by
        rw [map_pow]
        simpa using congrArg Subtype.val hk
      rw [← hCHeq]
      simpa using (hπ1 _).mp hk'
    have hPC := h4 P hPI hIP hP2
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨w', rfl⟩ : ∃ w', π w' = w := QuotientGroup.mk'_surjective C' w
    have hw' : (w' : G) ∈ P := (hPmem w').mpr hw
    rw [Subgroup.mem_bot]
    exact (hπ1 w').mpr (hCHeq ▸ hPC hw')
  have hNH : N ≤ H := hNI.trans hIH
  have hNbnil : Group.IsNilpotent ↥Nb := by
    let f : ↥N →* ↥Nb :=
      (π.comp (Subgroup.inclusion hNH)).codRestrict Nb fun x => hmem x.2 (hNH x.2)
    have hfs : Function.Surjective f := by
      rintro ⟨_, ⟨y, hy, rfl⟩⟩
      exact ⟨⟨y, Subgroup.mem_subgroupOf.mp hy⟩, rfl⟩
    have hker : CI.subgroupOf N ≤ f.ker := by
      intro x hx
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      show π ⟨x, hNH x.2⟩ = 1
      exact (hπ1 _).mpr (hCHeq ▸ Subgroup.mem_subgroupOf.mp hx)
    have := hnil
    refine Group.nilpotent_of_surjective (QuotientGroup.lift (CI.subgroupOf N) f hker) ?_
    intro w
    obtain ⟨x, rfl⟩ := hfs w
    exact ⟨QuotientGroup.mk x, rfl⟩
  have hNbodd : Odd (Nat.card Nb) := by
    have := hNbnil
    obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 ↥Nb))
    have hSn : (S : Subgroup ↥Nb).Normal := inferInstance
    have hsub : ((S : Subgroup ↥Nb).map Nb.subtype).subgroupOf Nb = S :=
      Subgroup.comap_map_eq_self_of_injective Nb.subtype_injective _
    have hNbS : Nb ≤ Subgroup.normalizer
        (((S : Subgroup ↥Nb).map Nb.subtype : Subgroup _) : Set (↥H ⧸ C')) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le _)).mp
        (by rw [hsub]; exact hSn)
    have hSle : (S : Subgroup ↥Nb).map Nb.subtype ≤ pCoreOf 2 Nb :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (Subgroup.map_subtype_le _) hNbS
        (S.isPGroup'.map _)
    have hNbO : pCoreOf 2 Nb ≤ pCoreOf 2 Ib :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 Nb).trans hNIb)
        (hNbn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Nb))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Nb)
    have hSbot : (S : Subgroup ↥Nb) = ⊥ := by
      have h0 : (S : Subgroup ↥Nb).map Nb.subtype = ⊥ := by
        rw [eq_bot_iff, ← hO2I]
        exact hSle.trans hNbO
      exact (Subgroup.map_eq_bot_iff_of_injective _ Nb.subtype_injective).mp h0
    have hnd := S.not_dvd_index
    rw [hSbot, Subgroup.index_bot] at hnd
    exact Nat.not_even_iff_odd.mp fun he => hnd (even_iff_two_dvd.mp he)
  have hcent := centralizes_of_normal_odd hRIb hRb2 hq hNIb
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hNIb).mpr hNbn) hNbodd
  rw [Subgroup.commutator_le]
  intro r hr x hx
  have hrH := hRH hr
  have hxH := hNH hx
  have hc := Subgroup.mem_centralizer_iff.mp (hcent (hmem hr hrH)) _ (hmem hx hxH)
  have h1' : π (⟨r, hrH⟩ * ⟨x, hxH⟩ * ⟨r, hrH⟩⁻¹ * ⟨x, hxH⟩⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hc]
    group
  exact (hπ1 _).mp h1'

end Hyp6116

end CFSG.Quasithin.H13
