module

public import CFSG.RankThree.PartTwo.Sec21.FF81Defs
import CFSG.RankThree.PartTwo.Sec21.FF81KFacts
import CFSG.RankThree.PartTwo.Sec21.FF81J
import CFSG.RankThree.PartTwo.Sec21.FF81Sec44
import CFSG.ClassicalGroups.Symplectic.Simple
import CFSG.Timmesfeld.Orders.Classical
import CFSG.GroupTheory.ElemAbelianClosure

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.Open (IsElemAbelian IsTwoLocal)

variable {G : Type} [Group G] [Finite G] {b : G} {L : Subgroup G}

theorem FF81Hyp.card_L (h : FF81Hyp b L) : Nat.card L = 1451520 := by
  rw [(CFSG.Timmesfeld.card_statedClassicalModel_two h.model).2.2.1 rfl]
  norm_num [CFSG.Open.ordBC, Finset.prod_Icc_succ_top]

theorem FF81Hyp.inf_cenS_self (h : FF81Hyp b L) : L ⊓ CenS L = ⊥ := by
  have : IsSimpleGroup L :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp L 3 2 1 h.model
  have hZ : Subgroup.center L = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center L) with h0 | h0
    · exact h0
    · exfalso
      have hcomm : commutator L = ⊥ := by
        rw [commutator_def, eq_bot_iff, Subgroup.commutator_le]
        intro x _ y _
        have hx : x ∈ Subgroup.center L := by rw [h0]; exact Subgroup.mem_top x
        rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
        exact (Subgroup.mem_center_iff.mp hx y).symm
      have htop : (⊤ : Subgroup L) = ⊥ := by
        rw [← h.quasi.1.commutator_eq_top, hcomm]
      have h1 : Nat.card L = 1 := by
        rw [← Subgroup.card_top (G := L), htop, Subgroup.card_bot]
      rw [h.card_L] at h1
      norm_num at h1
  refine eq_bot_iff.mpr fun x hx => ?_
  have hxZ : (⟨x, hx.1⟩ : L) ∈ Subgroup.center L := Subgroup.mem_center_iff.mpr fun y =>
    Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 y y.2)
  rw [hZ, Subgroup.mem_bot] at hxZ
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hxZ)

theorem FF81Hyp.b_cube (h : FF81Hyp b L) : b ^ 3 = 1 := by
  rw [← h.ord]; exact pow_orderOf_eq_one b

theorem FF81Hyp.b_ne_one (h : FF81Hyp b L) : b ≠ 1 := fun h1 => by
  have := h.ord; rw [h1, orderOf_one] at this; norm_num at this

theorem b_mem_cen (b : G) : b ∈ Cen b := Subgroup.mem_centralizer_singleton_iff.mpr rfl

theorem FF81Hyp.b_mem_cenS (h : FF81Hyp b L) : b ∈ CenS L :=
  Subgroup.mem_centralizer_iff.mpr fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mp (h.hLC hy)

theorem FF81Hyp.card_zpowers (h : FF81Hyp b L) : Nat.card (Subgroup.zpowers b) = 3 := by
  rw [Nat.card_zpowers, h.ord]

theorem comm_zpow_of_mem_cen {y : G} (hy : y ∈ Cen b) (k : ℤ) : y * b ^ k = b ^ k * y :=
  (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp hy : Commute y b) k).eq

theorem cen_le_cenS_zpowers_of_cen : Cen b ≤ CenS (Subgroup.zpowers b) := fun y hy =>
  Subgroup.mem_centralizer_iff.mpr fun z hz => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (comm_zpow_of_mem_cen hy k).symm

theorem cen_le_nor_zpowers : Cen b ≤ Nor (Subgroup.zpowers b) := fun y hy =>
  Subgroup.centralizer_le_normalizer _ (cen_le_cenS_zpowers_of_cen hy)

theorem FF81Hyp.zpowers_inf_L (h : FF81Hyp b L) : Subgroup.zpowers b ⊓ L = ⊥ := by
  refine eq_bot_iff.mpr fun x hx => ?_
  rw [← h.inf_cenS_self]
  exact ⟨hx.2, (Subgroup.zpowers_le.mpr h.b_mem_cenS) hx.1⟩

theorem FF81Hyp.conj_mem_D (h : FF81Hyp b L) {g d : G} (hg : g ∈ Cen b)
    (hd : d ∈ Cen b ⊓ CenS L) : g * d * g⁻¹ ∈ Cen b ⊓ CenS L := by
  refine ⟨(Cen b).mul_mem ((Cen b).mul_mem hg hd.1) ((Cen b).inv_mem hg), ?_⟩
  refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
  have hx' : g⁻¹ * x * g ∈ L :=
    (Subgroup.mem_normalizer_iff.mp (h.hLN hg) (g⁻¹ * x * g)).mpr
      (by rw [show g * (g⁻¹ * x * g) * g⁻¹ = x by group]; exact hx)
  have hc := Subgroup.mem_centralizer_iff.mp hd.2 _ hx'
  calc x * (g * d * g⁻¹) = g * ((g⁻¹ * x * g) * d) * g⁻¹ := by group
    _ = g * (d * (g⁻¹ * x * g)) * g⁻¹ := by rw [hc]
    _ = g * d * g⁻¹ * x := by group

theorem FF81Hyp.cen_le_nor_D (h : FF81Hyp b L) : Cen b ≤ Nor (Cen b ⊓ CenS L) := fun g hg =>
  Subgroup.mem_normalizer_iff.mpr fun d => ⟨fun hd => h.conj_mem_D hg hd, fun hd => by
    have := h.conj_mem_D ((Cen b).inv_mem hg) hd
    rwa [show g⁻¹ * (g * d * g⁻¹) * g⁻¹⁻¹ = d by group] at this⟩

theorem FF81Hyp.exists_decomp (h : FF81Hyp b L) {x : G} (hx : x ∈ Cen b) :
    ∃ l ∈ L, l⁻¹ * x ∈ Cen b ⊓ CenS L := by
  obtain ⟨l, hlL, hl⟩ := kf_sp62Out G L h.model x (h.hLN hx)
  refine ⟨l, hlL, (Cen b).mul_mem ((Cen b).inv_mem (h.hLC hlL)) hx,
    Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
  have := hl y hy
  calc y * (l⁻¹ * x) = l⁻¹ * (l * y * l⁻¹) * x := by group
    _ = l⁻¹ * (x * y * x⁻¹) * x := by rw [this]
    _ = l⁻¹ * x * y := by group

theorem FF81Hyp.mem_zpowers_of_cube (h : FF81Hyp b L) {d : G} (hdb : d ∈ Cen b)
    (hdL : d ∈ CenS L) (hd3 : d ^ 3 = 1) : d ∈ Subgroup.zpowers b := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_cases hd1 : d = 1
  · rw [hd1]; exact Subgroup.one_mem _
  set H := CenS L
  set u : ↥H := ⟨d, hdL⟩
  set v : ↥H := ⟨b, h.b_mem_cenS⟩
  have hou : orderOf u = 3 := by
    rw [← Subgroup.orderOf_coe]; exact orderOf_eq_prime hd3 hd1
  have hov : orderOf v = 3 := by rw [← Subgroup.orderOf_coe]; exact h.ord
  have hzu : IsPGroup 3 (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hou, pow_one])
  have hzv : IsPGroup 3 (Subgroup.zpowers v) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hov, pow_one])
  have huv : u * v = v * u := Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hdb)
  have hle : Subgroup.zpowers u ≤
      Subgroup.normalizer ((Subgroup.zpowers v : Subgroup ↥H) : Set ↥H) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    rintro w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact ((Commute.zpow_left (show Commute v u from huv.symm) k)).eq
  obtain ⟨P, hP⟩ := (IsPGroup.to_sup_of_normal_right' hzu hzv hle).exists_le_sylow
  haveI := h.cyc P
  have hmu : u ∈ (P : Subgroup ↥H) := hP (Subgroup.mem_sup_left (Subgroup.mem_zpowers u))
  have hmv : v ∈ (P : Subgroup ↥H) := hP (Subgroup.mem_sup_right (Subgroup.mem_zpowers v))
  have heq : Subgroup.zpowers (⟨u, hmu⟩ : (P : Subgroup ↥H)) =
      Subgroup.zpowers (⟨v, hmv⟩ : (P : Subgroup ↥H)) :=
    IsCyclic.subgroup_eq_iff_card_eq.mpr (by
      rw [Nat.card_zpowers, Nat.card_zpowers,
        ((Subgroup.orderOf_coe (⟨u, hmu⟩ : (P : Subgroup ↥H))).symm.trans hou),
        ((Subgroup.orderOf_coe (⟨v, hmv⟩ : (P : Subgroup ↥H))).symm.trans hov)])
  have hmem : (⟨u, hmu⟩ : (P : Subgroup ↥H)) ∈
      Subgroup.zpowers (⟨v, hmv⟩ : (P : Subgroup ↥H)) := by
    rw [← heq]; exact Subgroup.mem_zpowers _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  exact Subgroup.mem_zpowers_iff.mpr ⟨k, by
    simpa [u, v] using congrArg (fun z : (P : Subgroup ↥H) => ((z : ↥H) : G)) hk⟩

theorem FF81Hyp.cube_decomp (h : FF81Hyp b L) {x : G} (hx : x ∈ Cen b) (hx3 : x ^ 3 = 1) :
    ∃ l ∈ L, l ^ 3 = 1 ∧ ∃ k : ℤ, x = l * b ^ k := by
  obtain ⟨l, hlL, hd⟩ := h.exists_decomp hx
  set d := l⁻¹ * x with hddef
  have hld : Commute l d := Subgroup.mem_centralizer_iff.mp hd.2 l hlL
  have hxd : x = l * d := by rw [hddef]; group
  have h3 : l ^ 3 * d ^ 3 = 1 := by rw [← hld.mul_pow, ← hxd, hx3]
  have hl3 : l ^ 3 = 1 := by
    have hmem : l ^ 3 ∈ L ⊓ CenS L := ⟨L.pow_mem hlL 3, by
      rw [eq_inv_of_mul_eq_one_left h3]; exact (CenS L).inv_mem ((CenS L).pow_mem hd.2 3)⟩
    rw [h.inf_cenS_self, Subgroup.mem_bot] at hmem
    exact hmem
  have hd3 : d ^ 3 = 1 := by rwa [hl3, one_mul] at h3
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (h.mem_zpowers_of_cube hd.1 hd.2 hd3)
  exact ⟨l, hlL, hl3, k, by rw [hk]; exact hxd⟩

theorem FF81Hyp.card_elem_le (h : FF81Hyp b L)
    (hrk : ∀ E : Subgroup G, E ≤ L → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x ^ 3 = 1) →
      Nat.card E ≤ 27)
    {E : Subgroup G} (hEC : E ≤ Cen b) (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (h3 : ∀ x ∈ E, x ^ 3 = 1) :
    Nat.card E ≤ 81 ∧ (Nat.card E = 81 → b ∈ E ∧ Nat.card ↥(E ⊓ L) = 27) := by
  set Z := Subgroup.zpowers b
  set X := E ⊔ Z with hX
  have hEab : IsElemAbelian 3 E := ⟨⟨⟨fun x y => Subtype.ext (hc x x.2 y y.2)⟩⟩, h3⟩
  have hXab : IsElemAbelian 3 X :=
    CFSG.Open.IsElemAbelian.sup_of_commute hEab (CFSG.Open.isElemAbelian_zpowers h.b_cube)
      (fun x hx y hy => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        exact comm_zpow_of_mem_cen (hEC hx) k)
  have hXC : X ≤ Cen b := sup_le hEC (Subgroup.zpowers_le.mpr (b_mem_cen b))
  set Y := X ⊓ L with hY
  have hYcard : Nat.card Y ≤ 27 :=
    hrk Y inf_le_right (fun x hx y hy => hXab.comm hx.1 hy.1) (fun x hx => hXab.2 x hx.1)
  have hXY : X ≤ Y ⊔ Z := by
    intro x hx
    obtain ⟨l, hlL, -, k, rfl⟩ := h.cube_decomp (hXC hx) (hXab.2 x hx)
    have hbk : b ^ k ∈ X := Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers b k)
    have hlX : l ∈ X := by
      have := X.mul_mem hx (X.inv_mem hbk)
      rwa [mul_inv_cancel_right] at this
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hlX, hlL⟩)
      (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers b k))
  have hYZ : Nat.card ↥(Y ⊔ Z) ≤ Nat.card Y * 3 := by
    have := card_sup_le_mul Y Z ((inf_le_left.trans hXC).trans cen_le_nor_zpowers)
    rwa [h.card_zpowers] at this
  have hX81 : Nat.card X ≤ Nat.card Y * 3 := (Subgroup.card_le_of_le hXY).trans hYZ
  have hEX : Nat.card E ≤ Nat.card X := Subgroup.card_le_of_le le_sup_left
  have hY81 : Nat.card Y * 3 ≤ 81 := by omega
  refine ⟨hEX.trans (hX81.trans hY81), fun h81 => ?_⟩
  have hXE : X = E :=
    (Subgroup.eq_of_le_of_card_ge le_sup_left (h81 ▸ hX81.trans hY81)).symm
  refine ⟨hXE ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers b), ?_⟩
  have hYE : Y = E ⊓ L := by rw [hY, hXE]
  have h1 : 81 ≤ Nat.card Y * 3 := h81 ▸ hEX.trans hX81
  rw [← hYE]
  omega

theorem isElemAbelian_subgroupOf_of_forall {E C : Subgroup G} (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (h3 : ∀ x ∈ E, x ^ 3 = 1) : IsElemAbelian 3 (E.subgroupOf C) :=
  ⟨⟨⟨fun x y => Subtype.ext (Subtype.ext (hc _ (Subgroup.mem_subgroupOf.mp x.2) _
    (Subgroup.mem_subgroupOf.mp y.2)))⟩⟩,
    fun x hx => Subtype.ext (by simpa using h3 _ (Subgroup.mem_subgroupOf.mp hx))⟩

theorem FF81Hyp.le_four (h : FF81Hyp b L)
    (hrk : ∀ E : Subgroup G, E ≤ L → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x ^ 3 = 1) →
      Nat.card E ≤ 27)
    {F : Subgroup ↥(Cen b)} (hF : IsElemAbelian 3 F) {k : ℕ} (hk : Nat.card F = 3 ^ k) :
    k ≤ 4 := by
  have hcF := (h.card_elem_le hrk (E := F.map (Cen b).subtype) (Subgroup.map_subtype_le F)
    (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact congrArg Subtype.val (hF.comm hx hy))
    (by
      rintro _ ⟨x, hx, rfl⟩
      exact congrArg Subtype.val (hF.2 x hx))).1
  rw [Subgroup.card_map_of_injective (Cen b).subtype_injective, hk] at hcF
  by_contra hlt
  have : 3 ^ 5 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem FF81Hyp.bddAbove_localRank (h : FF81Hyp b L)
    (hrk : ∀ E : Subgroup G, E ≤ L → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x ^ 3 = 1) →
      Nat.card E ≤ 27) :
    BddAbove {k | ∃ H : Subgroup ↥(Cen b), IsTwoLocal H ∧ CFSG.Open.pRank 3 H = k} := by
  refine ⟨4, ?_⟩
  rintro _ ⟨H, -, rfl⟩
  refine csSup_le' ?_
  rintro j ⟨F, -, hF, hj⟩
  exact h.le_four hrk hF hj

theorem FF81Hyp.le_localRank (h : FF81Hyp b L)
    (hrk : ∀ E : Subgroup G, E ≤ L → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x ^ 3 = 1) →
      Nat.card E ≤ 27)
    {E T : Subgroup G} (hEC : E ≤ Cen b) (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (h3 : ∀ x ∈ E, x ^ 3 = 1) {k : ℕ} (hk : Nat.card E = 3 ^ k) (hTC : T ≤ Cen b)
    (hT2 : IsPGroup 2 T) (hT1 : T ≠ ⊥) (hET : E ≤ Nor T) : k ≤ localRank 3 ↥(Cen b) := by
  set T' := T.subgroupOf (Cen b)
  have hT'2 : IsPGroup 2 T' := hT2.comap_of_injective (Cen b).subtype Subtype.coe_injective
  have hT'1 : T' ≠ ⊥ := by
    intro h0
    apply hT1
    refine eq_bot_iff.mpr fun x hx => ?_
    have : (⟨x, hTC hx⟩ : Cen b) ∈ T' := Subgroup.mem_subgroupOf.mpr hx
    rw [h0, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  have hE'N : E.subgroupOf (Cen b) ≤ Subgroup.normalizer (T' : Set ↥(Cen b)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.mp (hET (Subgroup.mem_subgroupOf.mp hx)) y
  have hH2 : IsTwoLocal (Subgroup.normalizer (T' : Set ↥(Cen b))) := ⟨T', hT'1, hT'2, rfl⟩
  have hpk : k ≤ CFSG.Open.pRank 3 (Subgroup.normalizer (T' : Set ↥(Cen b))) :=
    le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three _)
      ⟨_, hE'N, isElemAbelian_subgroupOf_of_forall hc h3,
        by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEC).toEquiv, hk]⟩
  exact hpk.trans (le_csSup (h.bddAbove_localRank hrk) ⟨_, hH2, rfl⟩)

theorem FF81Hyp.no_e81_local (h : FF81Hyp b L) (hTF : KF_Sp6TorusFree)
    (hrk : ∀ E : Subgroup G, E ≤ L → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x ^ 3 = 1) →
      Nat.card E ≤ 27)
    {E T : Subgroup G} (hEC : E ≤ Cen b) (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (h3 : ∀ x ∈ E, x ^ 3 = 1) (hE81 : Nat.card E = 81) (hTC : T ≤ Cen b)
    (hT2 : IsPGroup 2 T) (hT1 : T ≠ ⊥) (hET : E ≤ Nor T) : False := by
  have hlr : localRank 3 ↥(Cen b) = 4 := by
    refine le_antisymm (csSup_le' ?_) ?_
    · rintro _ ⟨H, -, rfl⟩
      refine csSup_le' ?_
      rintro j ⟨F, -, hF, hj⟩
      exact h.le_four hrk hF hj
    · exact h.le_localRank hrk hEC hc h3 (k := 4) (by rw [hE81]; norm_num) hTC hT2 hT1 hET
  obtain ⟨W, hWC, hW2, hEW, hnot⟩ := h.a5 E hEC ⟨⟨⟨fun x y => Subtype.ext (hc x x.2 y y.2)⟩⟩, h3⟩
    ⟨T, hTC, hT2, hT1, hET⟩ (by rw [hlr, hE81]; norm_num)
  obtain ⟨-, hEL⟩ := (h.card_elem_le hrk hEC hc h3).2 hE81
  set D := Cen b ⊓ CenS L with hD
  set A := (W ⊔ D) ⊓ L with hA
  have hAnor : E ⊓ L ≤ Nor A := fun x hx =>
    mem_normalizer_sup_inf (hEW hx.1) (h.cen_le_nor_D (h.hLC hx.2)) (Subgroup.le_normalizer hx.2)
  have hAD : A ⊓ D = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    rw [← h.inf_cenS_self]; exact ⟨hx.1.2, hx.2.2⟩
  have e1 := card_sup_mul_card_inf A D (fun x hx => h.cen_le_nor_D (h.hLC hx.2))
  rw [hAD, Subgroup.card_bot, mul_one] at e1
  have e2 := card_sup_mul_card_inf W D (fun x hx => h.cen_le_nor_D (hWC hx))
  have hdvd1 : Nat.card A * Nat.card D ∣ Nat.card ↥(W ⊔ D) := by
    rw [← e1]; exact Subgroup.card_dvd_of_le (sup_le inf_le_left le_sup_right)
  have hdvd2 : Nat.card ↥(W ⊔ D) ∣ Nat.card W * Nat.card D := Dvd.intro _ e2
  have hAW : Nat.card A ∣ Nat.card W :=
    Nat.dvd_of_mul_dvd_mul_right Nat.card_pos (hdvd1.trans hdvd2)
  obtain ⟨n, hn⟩ := hW2.exists_card_eq
  have hAco : Nat.Coprime 3 (Nat.card A) :=
    Nat.Coprime.coprime_dvd_right (hn ▸ hAW) (Nat.Coprime.pow_right n (by norm_num))
  have hEL3 : IsElemAb 3 3 (E ⊓ L) :=
    ⟨CFSG.IsElementaryAbelian.of_forall (fun x hx y hy => hc x hx.1 y hy.1)
      (fun x hx => h3 x hx.1), by rw [hEL]; norm_num⟩
  have hA1 := hTF G L h.model (E ⊓ L) inf_le_right hEL3 A inf_le_right hAnor hAco
  have hWL : ∀ w ∈ W, w ∈ CenS L := by
    intro w hw
    obtain ⟨l, hlL, hd⟩ := h.exists_decomp (hWC hw)
    have hlA : l ∈ A := by
      refine ⟨?_, hlL⟩
      have : w * (l⁻¹ * w)⁻¹ ∈ W ⊔ D :=
        Subgroup.mul_mem _ (Subgroup.mem_sup_left hw) (Subgroup.mem_sup_right (D.inv_mem hd))
      rwa [show w * (l⁻¹ * w)⁻¹ = l by group] at this
    rw [hA1, Subgroup.mem_bot] at hlA
    have := hd.2
    rwa [hlA, inv_one, one_mul] at this
  apply hnot
  intro e he
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  obtain ⟨l, hlL, -, k, rfl⟩ := h.cube_decomp (hEC he) (h3 e he)
  have hwl : l * w = w * l := Subgroup.mem_centralizer_iff.mp (hWL w hw) l hlL
  have hwb : w * b ^ k = b ^ k * w := comm_zpow_of_mem_cen (hWC hw) k
  calc w * (l * b ^ k) = (w * l) * b ^ k := by group
    _ = (l * w) * b ^ k := by rw [hwl]
    _ = l * (w * b ^ k) := by group
    _ = l * (b ^ k * w) := by rw [hwb]
    _ = l * b ^ k * w := by group

theorem FF81Hyp.localRank_cen (h : FF81Hyp b L) (hTF : KF_Sp6TorusFree)
    (hrk : ∀ E : Subgroup G, E ≤ L → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x ^ 3 = 1) →
      Nat.card E ≤ 27)
    {b₁ b₃ s : G} (hb₁ : b₁ ∈ L) (hb₃ : b₃ ∈ L) (h13 : b₁ * b₃ = b₃ * b₁) (h1 : b₁ ^ 3 = 1)
    (h3 : b₃ ^ 3 = 1) (h9 : Nat.card (Subgroup.closure ({b₁, b₃} : Set G)) = 9) (hs : s ∈ L)
    (hs2 : orderOf s = 2) (hs1 : s * b₁ = b₁ * s) (hs3 : s * b₃ = b₃ * s) :
    localRank 3 ↥(Cen b) = 3 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_antisymm (csSup_le' ?_) ?_
  · rintro _ ⟨H, ⟨P, hP1, hP2, rfl⟩, rfl⟩
    refine csSup_le' ?_
    rintro j ⟨F, hFH, hF, hj⟩
    have hj4 := h.le_four hrk hF hj
    by_contra hlt
    have hj4' : j = 4 := by omega
    subst hj4'
    exact h.no_e81_local hTF hrk (E := F.map (Cen b).subtype) (T := P.map (Cen b).subtype)
      (Subgroup.map_subtype_le F)
      (by
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        exact congrArg Subtype.val (hF.comm hx hy))
      (by
        rintro _ ⟨x, hx, rfl⟩
        exact congrArg Subtype.val (hF.2 x hx))
      (by rw [Subgroup.card_map_of_injective (Cen b).subtype_injective, hj]; norm_num)
      (Subgroup.map_subtype_le P) (hP2.map _)
      (fun h0 => hP1 ((Subgroup.map_eq_bot_iff_of_injective P (Cen b).subtype_injective).mp h0))
      ((Subgroup.map_mono hFH).trans (Subgroup.le_normalizer_map _))
  · set K₀ := Subgroup.closure ({b₁, b₃} : Set G)
    have hK₀L : K₀ ≤ L := (Subgroup.closure_le _).mpr (by
      rintro x (rfl | rfl); exacts [hb₁, hb₃])
    have hK₀ab : IsElemAbelian 3 K₀ := CFSG.Open.IsElemAbelian.closure_of_commute
      (by
        rintro x (rfl | rfl) y (rfl | rfl)
        exacts [rfl, h13, h13.symm, rfl])
      (by rintro x (rfl | rfl); exacts [h1, h3])
    set K := K₀ ⊔ Subgroup.zpowers b
    have hKab : IsElemAbelian 3 K :=
      CFSG.Open.IsElemAbelian.sup_of_commute hK₀ab (CFSG.Open.isElemAbelian_zpowers h.b_cube)
        (fun x hx y hy => by
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
          exact comm_zpow_of_mem_cen (h.hLC (hK₀L hx)) k)
    have hKC : K ≤ Cen b :=
      sup_le (hK₀L.trans h.hLC) (Subgroup.zpowers_le.mpr (b_mem_cen b))
    have hinf : K₀ ⊓ Subgroup.zpowers b = ⊥ := eq_bot_iff.mpr fun x hx => by
      rw [← h.zpowers_inf_L]; exact ⟨hx.2, hK₀L hx.1⟩
    have hcard := card_sup_mul_card_inf K₀ (Subgroup.zpowers b)
      ((hK₀L.trans h.hLC).trans cen_le_nor_zpowers)
    rw [hinf, Subgroup.card_bot, mul_one, h9, h.card_zpowers] at hcard
    have hs1' : s ≠ 1 := fun h0 => by rw [h0, orderOf_one] at hs2; norm_num at hs2
    have hKN : K ≤ Nor (Subgroup.zpowers s) := by
      refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
      refine sup_le ((Subgroup.closure_le _).mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · rintro x (rfl | rfl)
        · exact cen_le_cenS_zpowers_of_cen (Subgroup.mem_centralizer_singleton_iff.mpr hs1.symm)
        · exact cen_le_cenS_zpowers_of_cen (Subgroup.mem_centralizer_singleton_iff.mpr hs3.symm)
      · exact cen_le_cenS_zpowers_of_cen (Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp (h.hLC hs)).symm)
    exact h.le_localRank hrk hKC (fun x hx y hy => hKab.comm hx hy) hKab.2 (k := 3)
      (by rw [hcard]; norm_num) (Subgroup.zpowers_le.mpr (h.hLC hs))
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs2, pow_one]))
      (fun h0 => hs1' (Subgroup.zpowers_eq_bot.mp h0)) hKN

end CFSG.RankThree.PartTwo.Sec21.FF81
