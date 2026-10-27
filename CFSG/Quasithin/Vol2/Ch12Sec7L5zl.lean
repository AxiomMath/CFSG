module

public import CFSG.Quasithin.Vol2.Ch12Sec7L5zk
public import CFSG.Quasithin.Vol2.Ch12Sec7L5zj
public import CFSG.Quasithin.Vol2.Ch12Sec7L5u

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.S127

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem conj_mem_centralizer {g x : G} (hg : g ∈ Subgroup.normalizer (V : Set G))
    (hx : x ∈ Subgroup.centralizer (V : Set G)) :
    g * x * g⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro v hv
  have hv' : g⁻¹ * v * g ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) v).mp hv
    simpa using this
  have h1 := hx _ hv'
  calc v * (g * x * g⁻¹) = g * ((g⁻¹ * v * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * v * g)) * g⁻¹ := by rw [h1]
    _ = g * x * g⁻¹ * v := by group

theorem inf_centralizer_le_Q
    (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) :
    (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (L ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hy := h.hyp
  obtain ⟨-, -, hTV⟩ := S127.card_eq_of_1222 h1222 h
  obtain ⟨-, -, hLC, -, -, -⟩ := setup1271_of h1222 G T L V h
  have hTL := hy.normalizes
  have hT2 : IsPGroup 2 T := hy.sylow.1
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := S127.Mod.L_le_normalizer h
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le hLV hTV
  refine le_pCoreOf_of_le_normalizer 2 inf_le_left (fun g hg => ?_) ?_
  · refine Subgroup.mem_normalizer_fintype fun x hx => ⟨(L ⊔ T).mul_mem
      ((L ⊔ T).mul_mem hg hx.1) ((L ⊔ T).inv_mem hg), conj_mem_centralizer (hLTV hg) hx.2⟩
  · rintro ⟨d, hdLT, hdC⟩
    have hd : d ∈ (↑(L ⊔ T) : Set G) := hdLT
    rw [Subgroup.coe_mul_of_right_le_normalizer_left L T hTL] at hd
    obtain ⟨l, hl, t, ht, rfl⟩ := Set.mem_mul.mp hd
    obtain ⟨k, hk⟩ := hT2 ⟨t, ht⟩
    have hk' : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hpow : ∀ n : ℕ, ∃ l' ∈ L, (l * t) ^ n = l' * t ^ n := by
      intro n
      induction n with
      | zero => exact ⟨1, L.one_mem, by simp⟩
      | succ n ih =>
        obtain ⟨l', hl', he⟩ := ih
        have htl : t ^ n * l * (t ^ n)⁻¹ ∈ L :=
          (Subgroup.mem_normalizer_iff.mp (hTL (T.pow_mem ht n)) l).mp hl
        refine ⟨l' * (t ^ n * l * (t ^ n)⁻¹), L.mul_mem hl' htl, ?_⟩
        rw [pow_succ, he, pow_succ]
        group
    obtain ⟨l', hl', he⟩ := hpow (2 ^ k)
    rw [hk', mul_one] at he
    have hmem : (l * t) ^ 2 ^ k ∈ L ⊓ Subgroup.centralizer (V : Set G) :=
      ⟨he ▸ hl', Subgroup.pow_mem _ hdC _⟩
    rw [hLC] at hmem
    obtain ⟨j, hj⟩ := (pCoreOf_isPGroup 2 L) ⟨_, hmem⟩
    have hj' : ((l * t) ^ 2 ^ k) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    refine ⟨k + j, Subtype.ext ?_⟩
    rw [SubmonoidClass.coe_pow, pow_add, pow_mul]
    exact hj'

theorem no2_of_hyp (hy : Hyp1223 G T L V) :
    ∀ (N : Subgroup ↥L) [N.Normal], IsPGroup 2 (↥L ⧸ N) → N = ⊤ := by
  intro N hN hp
  have h := hy.faithful.2.1 (N.map L.subtype) (Subgroup.map_subtype_le N)
    (by rw [map_subtype_subgroupOf']; exact hN) (fun x hx => by
      obtain ⟨k, hk⟩ := hp (QuotientGroup.mk ⟨x, hx⟩)
      refine ⟨k, ⟨⟨x, hx⟩ ^ 2 ^ k, ?_, rfl⟩⟩
      rw [← QuotientGroup.mk_pow] at hk
      exact (QuotientGroup.eq_one_iff _).mp hk)
  rw [eq_top_iff]
  intro y _
  have hy' : (y : G) ∈ N.map L.subtype := by rw [h]; exact y.2
  obtain ⟨n, hn, hny⟩ := hy'
  have : n = y := Subtype.ext hny
  rw [← this]
  exact hn

theorem isHatA6Block_of_comm_le
    (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) (hcomm : ⁅pCoreOf 2 L, L⁆ ≤ V) :
    CFSG.Quasithin.IsHatA6Block L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hy := h.hyp
  obtain ⟨-, hV64, hTV⟩ := S127.card_eq_of_1222 h1222 h
  obtain ⟨hVab, -, hLC, hX3, -, hXfix⟩ := setup1271_of h1222 G T L V h
  have hTL := hy.normalizes
  have hT2 : IsPGroup 2 T := hy.sylow.1
  have hVT : V ≤ T := S127.L713.V_le_T h1222 h
  have hV2 : IsPGroup 2 V := hT2.to_le hVT
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := S127.Mod.L_le_normalizer h
  have hVL : V ≤ L := by
    have hc : ⁅V, L⁆ ≤ L := by
      rw [Subgroup.commutator_le]
      intro v hv l hl
      have hvl : v * l * v⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hTL (hVT hv)) l).mp hl
      rw [commutatorElement_def]
      exact L.mul_mem hvl (L.inv_mem hl)
    calc V = ⁅V, L⁆ := hy.irrPlus.2.2.2.1.symm
      _ ≤ L := hc
  have hVO : V ≤ pCoreOf 2 L := le_pCoreOf_of_le_normalizer 2 hVL hLV hV2
  have hUV : QuasithinUnique.blockU L = V := by
    refine le_antisymm hcomm ?_
    show V ≤ ⁅QuasithinUnique.blockQ L, L⁆
    calc V = ⁅V, L⁆ := hy.irrPlus.2.2.2.1.symm
      _ ≤ ⁅pCoreOf 2 L, L⁆ := Subgroup.commutator_mono hVO le_rfl
  obtain ⟨x, hxX, hxC⟩ : ∃ x ∈ S127.XOf L, x ∉ Subgroup.centralizer (V : Set G) := by
    by_contra hno
    have hbot : autOn (S127.XOf L) V = ⊥ := by
      rw [eq_bot_iff]
      intro a ha
      obtain ⟨y, hyN, hyX, rfl⟩ := S127.Mod.mem_autOn'.1 ha
      rw [Subgroup.mem_bot]
      exact (S127.Mod.conjAct_eq_one' hyN).2 (by_contra fun hy' => hno ⟨y, hyX, hy'⟩)
    rw [hbot, Subgroup.card_bot] at hX3
    norm_num at hX3
  have hxL : x ∈ L := S127.L5.XOf_le L hxX
  have hVCL : V ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
    rw [eq_bot_iff, ← hXfix x hxX hxC]
    exact inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hxL))
  have hQne : pCoreOf 2 (L ⊔ T) ≠ ⊥ := by
    intro hb
    have hVQ : V ≤ pCoreOf 2 (L ⊔ T) :=
      le_pCoreOf_of_le_normalizer 2 (hVT.trans le_sup_right) (sup_le hLV hTV) hV2
    rw [hb] at hVQ
    exact hy.irrPlus.2.1 (le_bot_iff.mp hVQ)
  have hchLT : QuasithinUnique.CharTwo (L ⊔ T) :=
    charTwo_of_inH hy.qtke.2.1 (hy.sylow.1.toSylow hy.sylow.2) ⟨le_sup_right, hQne⟩
  have hchL : QuasithinUnique.CharTwo L :=
    QuasithinUnique.CharTwo.of_normal hchLT le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer hTL))
  have hshort : QuasithinUnique.IsShort2 L := by
    refine ⟨no2_of_hyp hy, hchL, ⟨?_, ?_⟩, Or.inl hy.quasisimple, ?_⟩
    · rw [hUV]
      refine le_inf hVO fun v hv => Subgroup.mem_centralizer_iff.mpr fun q hq => ?_
      have hqC : q ∈ Subgroup.centralizer (V : Set G) := by
        have hq' : q ∈ pCoreOf 2 L := hq
        rw [← hLC] at hq'
        exact hq'.2
      exact (Subgroup.mem_centralizer_iff.mp hqC v hv).symm
    · intro y hy'
      rw [hUV] at hy'
      exact hVab.2 y hy'
    · have hZ : QuasithinUnique.blockZ L = V ⊓ Subgroup.centralizer (L : Set G) := by
        rw [QuasithinUnique.blockZ, hUV]
      rw [hZ, hUV]
      exact ⟨hy.irrPlus.2.2.2.2.1, fun W hW1 hW2 hW3 => hy.irrPlus.2.2.2.2.2.1 W hW1 hW2 hW3⟩
  obtain ⟨hOn, hq, hcen, hA6⟩ := h.hatA6
  have hOeq : (Subgroup.centralizer (V : Set G)).subgroupOf L = CFSG.pCore 2 ↥L := by
    rw [← ASInputs.C113.pCoreOf_subgroupOf, ← hLC]
    ext y
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun hc => ⟨y.2, hc⟩, fun hc => hc.2⟩
  have hHat : IsHat (↥L ⧸ (Subgroup.centralizer (V : Set G)).subgroupOf L)
      (alternatingGroup (Fin 6)) := ⟨hq, hcen, hA6⟩
  refine ⟨hshort, IsHat.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hOeq) hHat, ?_, ?_⟩
  · rw [hUV, hV64]
  · rw [hUV, hLC]

theorem centralizer_V_eq
    (h1222 : Stmt12_2_2) (h1226 : Stmt12_2_6) (h129 : Stmt12_2_9) (h1241 : Lemma12_4_1)
    (h10 : Lemma12_7_10) (h11 : Lemma12_7_11) {t : G} (h : Setting1273 G T L V t)
    (hcomm : ⁅pCoreOf 2 L, L⁆ ≤ V) : Subgroup.centralizer (V : Set G) = V :=
  ((lemma12_7_6_of h1222 h1226 G T L V h.hyp (isHatA6Block_of_comm_le h1222 h.hyp hcomm)).2
    (lemma12_7_12_of h1222 h129 h1241 h10 h11 G T L V t h)).2.2.1

namespace L715.Set714

open S127.L716 G31
open scoped IsMulCommutative

variable {t z : G} (s : Set714 G T L V t z)
include s

theorem card_U
    (h1222 : Stmt12_2_2) : Nat.card ↥(U714 T L V z) = 2 * Nat.card ↥(Ut T L V z) := by
  have hzU : Subgroup.zpowers z ≤ U714 T L V z := Subgroup.zpowers_le_of_mem s.z_mem_U
  have h1 : Nat.card ↥(Ut T L V z) = (Subgroup.zpowers z).relIndex (U714 T L V z) :=
    card_secImg hzU (s.U_le_N h1222)
  have h2 := Subgroup.relIndex_mul_card (Subgroup.zpowers z) (U714 T L V z)
  rw [inf_of_le_left hzU, Nat.card_zpowers, s.orderOf_z, ← h1] at h2
  rw [← h2, mul_comm]

theorem card_U_inf_C
    (h1222 : Stmt12_2_2) (hU : autOn (U714 T L V z) V = autOn (R1 T L V) V) :
    Nat.card ↥(U714 T L V z ⊓ Subgroup.centralizer (V : Set G)) * 4 =
      Nat.card ↥(U714 T L V z) := by
  have h := s.setting.hyp
  obtain ⟨hcomm, -, hTV⟩ := S127.card_eq_of_1222 h1222 h
  have := hcomm
  obtain ⟨-, -, h4, -, -, -⟩ := S127.Mod.lemma12_7_2_two h1222 h
  have hUN : U714 T L V z ≤ Subgroup.normalizer (V : Set G) := (s.U_le_T h1222).1.trans hTV
  have h1 := card_autOn_eq_relIndex hUN
  rw [hU, h4] at h1
  have h2 := Subgroup.relIndex_mul_card (U714 T L V z ⊓ Subgroup.centralizer (V : Set G))
    (U714 T L V z)
  rw [inf_right_comm, inf_idem, ← h1] at h2
  rw [← h2, mul_comm]

theorem exists_l_q
    (h1222 : Stmt12_2_2) (hU : autOn (U714 T L V z) V = autOn (R1 T L V) V) :
    ∃ u ∈ U714 T L V z, ∃ l ∈ L, ∃ q₀ ∈ pCoreOf 2 (L ⊔ T), u = l * q₀ ∧
      l * l ∈ Subgroup.centralizer (V : Set G) ∧ l ∉ Subgroup.centralizer (V : Set G) := by
  have h := s.setting.hyp
  have hy := h.hyp
  obtain ⟨hcomm, -, hTV⟩ := S127.card_eq_of_1222 h1222 h
  have := hcomm
  obtain ⟨-, -, h4, hr2, -, -⟩ := S127.Mod.lemma12_7_2_two h1222 h
  have hUT := (s.U_le_T h1222).1
  have hUN : U714 T L V z ≤ Subgroup.normalizer (V : Set G) := hUT.trans hTV
  obtain ⟨u, huU, huV⟩ : ∃ u ∈ U714 T L V z, u ∉ Subgroup.centralizer (V : Set G) := by
    by_contra hno
    push Not at hno
    have hbot : autOn (U714 T L V z) V = ⊥ := by
      rw [eq_bot_iff]
      intro a ha
      obtain ⟨y, hyN, hyU, rfl⟩ := S127.Mod.mem_autOn'.1 ha
      rw [Subgroup.mem_bot]
      exact (S127.Mod.conjAct_eq_one' hyN).2 (hno y hyU)
    rw [hU] at hbot
    rw [hbot, Subgroup.card_bot] at h4
    norm_num at h4
  have hmem : conjAct V ⟨u, hUN huU⟩ ∈ autOn (R1 T L V) V := by
    rw [← hU]
    exact S127.Mod.conjAct_mem_autOn huU (hUN huU)
  obtain ⟨r, hrN, hrR, hru⟩ := S127.Mod.mem_autOn'.1 hmem
  have hc : r⁻¹ * u ∈ Subgroup.centralizer (V : Set G) := by
    rw [← S127.Mod.conjAct_eq_one' ((Subgroup.normalizer (V : Set G)).mul_mem
      ((Subgroup.normalizer (V : Set G)).inv_mem hrN) (hUN huU))]
    have e : conjAct V ⟨r⁻¹ * u, (Subgroup.normalizer (V : Set G)).mul_mem
        ((Subgroup.normalizer (V : Set G)).inv_mem hrN) (hUN huU)⟩ =
        (conjAct V ⟨r, hrN⟩)⁻¹ * conjAct V ⟨u, hUN huU⟩ := by
      rw [← map_inv, ← map_mul]
      rfl
    rw [e, hru, inv_mul_cancel]
  have hsylLT : QuasithinUnique.IsSylowTwoOf T (L ⊔ T) :=
    S127.L713.isSylowTwoOf_of_le hy.sylow le_sup_right
  have hQL : pCoreOf 2 (L ⊔ T) ≤ Subgroup.normalizer (L : Set G) :=
    (pCoreOf_two_le_of_isSylowTwoOf hsylLT).trans hy.normalizes
  have hrLQ : r ∈ (↑(L ⊔ pCoreOf 2 (L ⊔ T)) : Set G) := (pCoreOf_le 2 _ hrR).1
  rw [Subgroup.coe_mul_of_right_le_normalizer_left L _ hQL] at hrLQ
  obtain ⟨l, hl, q₁, hq₁, rfl⟩ := Set.mem_mul.mp hrLQ
  have hQC := S127.Mod.Q_le_centralizer h1222 h
  have hcQ : (l * q₁)⁻¹ * u ∈ pCoreOf 2 (L ⊔ T) := by
    refine inf_centralizer_le_Q h1222 h ⟨?_, hc⟩
    exact (L ⊔ T).mul_mem ((L ⊔ T).inv_mem ((L ⊔ T).mul_mem (Subgroup.mem_sup_left hl)
      (pCoreOf_le 2 _ hq₁))) (Subgroup.mem_sup_right (hUT huU))
  refine ⟨u, huU, l, hl, q₁ * ((l * q₁)⁻¹ * u), (pCoreOf 2 (L ⊔ T)).mul_mem hq₁ hcQ,
    by group, ?_, ?_⟩
  · have hr := hr2 _ hrR
    have hq₁C := hQC hq₁
    have e : l * l = (l * q₁) ^ 2 * ((l * q₁)⁻¹ * q₁⁻¹ * (l * q₁)⁻¹⁻¹) * q₁⁻¹ := by
      rw [pow_two]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hr (conj_mem_centralizer
      ((Subgroup.normalizer (V : Set G)).inv_mem hrN) (Subgroup.inv_mem _ hq₁C)))
      (Subgroup.inv_mem _ hq₁C)
  · intro hlC
    apply huV
    have e : u = l * q₁ * ((l * q₁)⁻¹ * u) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hlC (hQC hq₁)) hc

omit s in
theorem mul_mem_of_card_le {A W : Subgroup G} (hA : Nat.card ↥A ≤ 2 * Nat.card ↥(A ⊓ W)) :
    ∀ a₁ ∈ A, ∀ a ∈ A, a₁ ∉ W → a ∉ W → a₁⁻¹ * a ∈ W := by
  classical
  intro a₁ ha₁ a ha ha₁W haW
  by_contra hne
  have h1 := Subgroup.relIndex_mul_card W A
  rw [inf_comm] at h1
  have hpos : 0 < Nat.card ↥(A ⊓ W) := Nat.card_pos
  have hrel : W.relIndex A ≤ 2 := by
    by_contra hlt
    push Not at hlt
    have : 3 * Nat.card ↥(A ⊓ W) ≤ Nat.card ↥A := by
      rw [← h1]
      exact Nat.mul_le_mul_right _ hlt
    omega
  have : Fintype (↥A ⧸ W.subgroupOf A) := Fintype.ofFinite _
  have hd : ∀ x y : ↥A, (x : G)⁻¹ * y ∉ W →
      (QuotientGroup.mk x : ↥A ⧸ W.subgroupOf A) ≠ QuotientGroup.mk y := by
    intro x y hxy h
    exact hxy (Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp h))
  have h3 : ({QuotientGroup.mk 1, QuotientGroup.mk ⟨a₁, ha₁⟩, QuotientGroup.mk ⟨a, ha⟩} :
      Finset (↥A ⧸ W.subgroupOf A)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair]
    · exact hd _ _ hne
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hd _ _ (by simpa using ha₁W), hd _ _ (by simpa using haW)⟩
  have h4 : 3 ≤ W.relIndex A := by
    rw [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card, ← h3]
    exact Finset.card_le_univ _
  omega

theorem comm_le_V
    (h1222 : Stmt12_2_2) (hU : autOn (U714 T L V z) V = autOn (R1 T L V) V) {d : ℕ}
    (hd : Nat.card ↥(Ut T L V z) = 2 ^ d) (hd4 : d ≤ 4) :
    ∀ q ∈ pCoreOf 2 (L ⊔ T), ∀ l' ∈ L, l' * q * l'⁻¹ * q⁻¹ ∈ V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := s.setting.hyp
  have hy := h.hyp
  obtain ⟨hcomm, -, hTV⟩ := S127.card_eq_of_1222 h1222 h
  have := hcomm
  obtain ⟨-, -, hLC, -, -, -⟩ := setup1271_of h1222 G T L V h
  obtain ⟨hOn, hq, hcen, ⟨e⟩⟩ := h.hatA6
  have hTL := hy.normalizes
  have hT2 : IsPGroup 2 T := hy.sylow.1
  have hVT : V ≤ T := S127.L713.V_le_T h1222 h
  have hV2 : IsPGroup 2 V := hT2.to_le hVT
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := S127.Mod.L_le_normalizer h
  have hO2 : IsPGroup 2 ↥((Subgroup.centralizer (V : Set G)).subgroupOf L) := by
    rintro ⟨x, hx⟩
    have hxP : (x : G) ∈ pCoreOf 2 L := by rw [← hLC]; exact ⟨x.2, hx⟩
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 L) ⟨_, hxP⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hk
  have hsylLT : QuasithinUnique.IsSylowTwoOf T (L ⊔ T) :=
    S127.L713.isSylowTwoOf_of_le hy.sylow le_sup_right
  have hQL : pCoreOf 2 (L ⊔ T) ≤ Subgroup.normalizer (L : Set G) :=
    (pCoreOf_two_le_of_isSylowTwoOf hsylLT).trans hTL
  have hVQ : V ≤ pCoreOf 2 (L ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 (hVT.trans le_sup_right) (sup_le hLV hTV) hV2
  have hLQ : L ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) :=
    le_sup_left.trans (le_normalizer_pCoreOf 2 _)
  obtain ⟨u, huU, l, hl, q₀, hq₀, rfl, hl2, hlV⟩ := s.exists_l_q h1222 hU
  have hUT := s.U_le_T h1222
  have hcommQ : ∀ p ∈ pCoreOf 2 (L ⊔ T), p⁻¹ * (l * q₀ * p * (l * q₀)⁻¹) ∈
      U714 T L V z ⊓ Subgroup.centralizer (V : Set G) := by
    intro p hp
    have hpT := pCoreOf_two_le_of_isSylowTwoOf hsylLT hp
    have hpu : p⁻¹ * (l * q₀) * p ∈ U714 T L V z := by
      have := (Subgroup.mem_normalizer_iff.mp (hUT.2 (T.inv_mem hpT)) _).mp huU
      simpa using this
    have huQ : l * q₀ * p * (l * q₀)⁻¹ ∈ pCoreOf 2 (L ⊔ T) :=
      (Subgroup.mem_normalizer_iff.mp ((le_normalizer_pCoreOf 2 (L ⊔ T))
        (Subgroup.mem_sup_right (hUT.1 huU))) p).mp hp
    refine ⟨?_, S127.Mod.Q_le_centralizer h1222 h
      ((pCoreOf 2 (L ⊔ T)).mul_mem ((pCoreOf 2 (L ⊔ T)).inv_mem hp) huQ)⟩
    have e : p⁻¹ * (l * q₀ * p * (l * q₀)⁻¹) = p⁻¹ * (l * q₀) * p * (l * q₀)⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ hpu (Subgroup.inv_mem _ huU)
  have hA2 := mul_mem_of_card_le (A := U714 T L V z ⊓ Subgroup.centralizer (V : Set G))
    (W := V) (by
      have h1 := s.card_U h1222
      have h2 := s.card_U_inf_C h1222 hU
      rw [hd] at h1
      have hV1 : V1 T L V ≤ U714 T L V z ⊓ Subgroup.centralizer (V : Set G) ⊓ V := by
        intro v hv
        have hvV : v ∈ V := (inf_le_left : V1 T L V ≤ V) hv
        refine ⟨⟨le_conjClosure _ _ hv, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩, hvV⟩
        exact congrArg Subtype.val (hcomm.is_comm.comm ⟨w, hw⟩ ⟨v, hvV⟩)
      have h3 := Subgroup.card_le_of_le hV1
      rw [(S127.Mod.lemma12_7_2_two h1222 h).1.2] at h3
      have h16 : 2 ^ d ≤ 16 := by
        calc 2 ^ d ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hd4
          _ = 16 := by norm_num
      omega)
  exact NoTransv.comm_le_of_transv (O := (Subgroup.centralizer (V : Set G)).subgroupOf L)
    (fun x => Iff.rfl) hO2 hq hcen e (no2_of_hyp hy) (pCoreOf_isPGroup 2 _) hVQ
    (S127.Mod.Q_le_centralizer h1222 h) hLQ hQL hLV hl hq₀ hl2 hlV hcommQ hA2

theorem inf_V_le_V1
    [IsMulCommutative ↥(Ut T L V z)] (h1222 : Stmt12_2_2) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (hU : autOn (U714 T L V z) V = autOn (R1 T L V) V) :
    U714 T L V z ⊓ V ≤ V1 T L V := by
  have h := s.setting.hyp
  obtain ⟨hcomm, -, hTV⟩ := S127.card_eq_of_1222 h1222 h
  have := hcomm
  obtain ⟨-, -, -, -, -, hV1eq⟩ := S127.Mod.lemma12_7_2_two h1222 h
  have hsq := s.sq_eq_one_U h1222 h37 h38 h39 hU
  have hinv : ∀ x ∈ U714 T L V z, x⁻¹ = x := fun x hx =>
    inv_eq_of_mul_eq_one_left (by rw [← pow_two]; exact hsq x hx)
  have hUab : ∀ a ∈ U714 T L V z, ∀ b ∈ U714 T L V z, a * b = b * a := fun a ha b hb => by
    have := hinv (a * b) (Subgroup.mul_mem _ ha hb)
    rw [mul_inv_rev, hinv a ha, hinv b hb] at this
    exact this.symm
  have hRN : R1 T L V ≤ Subgroup.normalizer (V : Set G) :=
    (pCoreOf_le 2 _).trans (s.P1_le_normalizer_V h1222)
  rintro v ⟨hvU, hvV⟩
  rw [← hV1eq]
  refine ⟨hvV, Subgroup.mem_centralizer_iff.mpr fun r hr => ?_⟩
  have hmem : conjAct V ⟨r, hRN hr⟩ ∈ autOn (U714 T L V z) V := by
    rw [hU]
    exact S127.Mod.conjAct_mem_autOn hr (hRN hr)
  obtain ⟨u, huN, huU, hur⟩ := S127.Mod.mem_autOn'.1 hmem
  have h1 := congrArg (fun φ : MulAut ↥V => ((φ ⟨v, hvV⟩ : ↥V) : G)) hur
  simp only [S127.Mod.conjAct_val] at h1
  have huv := hUab u huU v hvU
  calc r * v = r * v * r⁻¹ * r := by group
    _ = u * v * u⁻¹ * r := by rw [h1]
    _ = v * r := by rw [huv, mul_inv_cancel_right]

theorem dim_ne_four
    [IsMulCommutative ↥(Ut T L V z)] (h1222 : Stmt12_2_2) (h1226 : Stmt12_2_6)
    (h129 : Stmt12_2_9) (h1241 : Lemma12_4_1) (h10 : Lemma12_7_10) (h11 : Lemma12_7_11)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (hU : autOn (U714 T L V z) V = autOn (R1 T L V) V) (hd : Nat.card ↥(Ut T L V z) = 2 ^ 4) :
    False := by
  have h := s.setting.hyp
  obtain ⟨hcomm, -, -⟩ := S127.card_eq_of_1222 h1222 h
  have := hcomm
  have hTL := h.hyp.normalizes
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := S127.Mod.L_le_normalizer h
  have hQL := s.comm_le_V h1222 hU hd le_rfl
  have hOQ : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans le_sup_left)
      (sup_le (le_normalizer_pCoreOf 2 L) (hTL.trans (normalizer_le_normalizer_pCoreOf 2 L)))
      (pCoreOf_isPGroup 2 L)
  have hcommL : ⁅pCoreOf 2 L, L⁆ ≤ V := by
    rw [Subgroup.commutator_le]
    intro q hq l' hl'
    rw [commutatorElement_def]
    have e : q * l' * q⁻¹ * l'⁻¹ = (l' * q * l'⁻¹ * q⁻¹)⁻¹ := by group
    rw [e]
    exact V.inv_mem (hQL q (hOQ hq) l' hl')
  have hCV := centralizer_V_eq h1222 h1226 h129 h1241 h10 h11 s.setting hcommL
  have h1 := s.card_U h1222
  have h2 := s.card_U_inf_C h1222 hU
  rw [hd] at h1
  rw [hCV] at h2
  have h3 := Subgroup.card_le_of_le (s.inf_V_le_V1 h1222 h37 h38 h39 hU)
  rw [(S127.Mod.lemma12_7_2_two h1222 h).1.2] at h3
  omega

end L715.Set714

end CFSG.Quasithin.H13.S127
