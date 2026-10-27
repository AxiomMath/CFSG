module

public import CFSG.Quasithin.Vol2.Ch4Sec3L436Sp4KZ
public import CFSG.Quasithin.Background.A3Structure318
public import CFSG.LieType.Simplicity.Classical
public import CFSG.Quasithin.Background.InternalSecTwo
public import CFSG.Quasithin.Vol2.Ch4Sec3L436Sp4QZ

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank CFSG.Blueprint L436

variable {G : Type} [Group G] [Finite G]

namespace L436

omit [Finite G] in
theorem quotPCore_subgroupOf_mulEquiv {L H : Subgroup G} (hLH : L ≤ H) :
    Nonempty ((↥(L.subgroupOf H) ⧸ CFSG.pCore 2 ↥(L.subgroupOf H)) ≃*
      (↥L ⧸ CFSG.pCore 2 ↥L)) := by
  let e : ↥(L.subgroupOf H) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLH
  have hmap : (CFSG.pCore 2 ↥(L.subgroupOf H)).map (e : ↥(L.subgroupOf H) →* ↥L) =
      CFSG.pCore 2 ↥L := by
    have := CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 e
    exact this
  exact ⟨QuotientGroup.congr _ _ e hmap⟩

theorem pRank_subgroupOf_eq_pRank {L H : Subgroup G} (hLH : L ≤ H) {p : ℕ} (hp : p.Prime) :
    CFSG.Open.pRank p (L.subgroupOf H) = CFSG.Open.pRank p L := by
  have : Fact p.Prime := ⟨hp⟩
  have e : ↥(L.subgroupOf H) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLH
  rw [← pRank_top_subtype (p := p) (L.subgroupOf H), ← pRank_top_subtype (p := p) L]
  exact CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e

omit [Finite G] in
theorem isSimpleGroup_of_isPSLEps3q {X : Type} [Group X] {s : Bool} {q : ℕ}
    (h : IsPSLEps3q s q X) : IsSimpleGroup X := by
  obtain ⟨p, e, -, -, -, hX⟩ := h
  cases s
  · exact (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity X 3 p e hX).2
  · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity X 3 p e hX).2

omit [Finite G] in
theorem eq_one_of_forall_commute {X : Type} [Group X] [IsSimpleGroup X] (hp : Group.IsPerfect X)
    {x : X} (hx : ∀ y : X, x * y = y * x) : x = 1 := by
  have hc : Subgroup.center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · exact h
    · exfalso
      have hcomm : commutator X = ⊥ := by
        rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro a _
        rw [Subgroup.mem_centralizer_iff]
        intro b _
        have hb : b ∈ Subgroup.center X := h ▸ Subgroup.mem_top b
        exact (Subgroup.mem_center_iff.mp hb a).symm
      have htop : (⊤ : Subgroup X) = ⊥ := by rw [← Group.isPerfect_def.mp hp, hcomm]
      obtain ⟨a, ha⟩ := exists_ne (1 : X)
      have : a ∈ (⊥ : Subgroup X) := htop ▸ Subgroup.mem_top a
      exact ha (Subgroup.mem_bot.mp this)
  have hz : x ∈ Subgroup.center X := Subgroup.mem_center_iff.mpr fun y => (hx y).symm
  rw [hc] at hz
  exact Subgroup.mem_bot.mp hz

omit [Finite G] in
theorem commutator_mem_pCoreOf_of_quasisimple {X N : Subgroup G}
    (hq : CFSG.IsQuasisimple (↥X ⧸ CFSG.pCore 2 ↥X)) (hNX : N ≤ X)
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) (hne : ¬ X ≤ N ⊔ pCoreOf 2 X) :
    ∀ c ∈ N, ∀ k ∈ X, c * k * c⁻¹ * k⁻¹ ∈ pCoreOf 2 X := by
  classical
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥X) with hπ
  have hNn : (N.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNX).2 hXN
  have hMn : ((N.subgroupOf X).map π).Normal :=
    Subgroup.Normal.map hNn π (QuotientGroup.mk'_surjective _)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hMn with h | h
  · exfalso
    apply hne
    intro x hx
    have hmem : π ⟨x, hx⟩ ∈ (N.subgroupOf X).map π := h ▸ Subgroup.mem_top _
    obtain ⟨m, hm, hmx⟩ := hmem
    have hk : m⁻¹ * ⟨x, hx⟩ ∈ CFSG.pCore 2 ↥X := by
      rw [← QuotientGroup.eq]
      exact hmx
    have hx' : x = (m : G) * ((m⁻¹ * ⟨x, hx⟩ : ↥X) : G) := by simp
    rw [hx']
    refine mul_mem (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hm))
      (Subgroup.mem_sup_right ?_)
    exact ⟨_, hk, rfl⟩
  · intro c hc k hk
    have hcX := hNX hc
    have hz : π ⟨c, hcX⟩ ∈ Subgroup.center _ := h ⟨⟨c, hcX⟩, hc, rfl⟩
    have hcomm : π ⟨c, hcX⟩ * π ⟨k, hk⟩ = π ⟨k, hk⟩ * π ⟨c, hcX⟩ :=
      (Subgroup.mem_center_iff.mp hz _).symm
    have h1 : π (⟨c, hcX⟩ * ⟨k, hk⟩ * ⟨c, hcX⟩⁻¹ * ⟨k, hk⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
      group
    have h2 := (QuotientGroup.eq_one_iff _).mp h1
    exact ⟨_, h2, rfl⟩

end L436

namespace Setting436Sp4

variable {T M L I H K : Subgroup G} {n : ℕ} {t : G} (s : Setting436Sp4 G T M L n I H K t)
include s

theorem isSimpleGroup_modO2_K₂ :
    IsSimpleGroup (ModO2 (sp4K₂ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L))) :=
  (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 2 n s.concl.psl).2

theorem mem_Q₁_of_commutator_mem {v : G}
    (hv : v ∈ sp4K₂ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L))
    (hc : ∀ k ∈ sp4K₂ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L),
      v * k * v⁻¹ * k⁻¹ ∈ sp4Q₁ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L)) :
    v ∈ sp4Q₁ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) := by
  classical
  set K₂ := sp4K₂ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) with hK₂
  have := s.isSimpleGroup_modO2_K₂
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K₂) with hπ
  have hperf : Group.IsPerfect ↥K₂ :=
    Subgroup.isPerfect_iff.mpr (CFSG.Quasithin.perfectCore_perfect _)
  have hperf' : Group.IsPerfect (ModO2 K₂) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K₂))
  have hmem : ∀ x : ↥K₂, (x : G) ∈ pCoreOf 2 K₂ → x ∈ CFSG.pCore 2 ↥K₂ := by
    rintro x ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    rw [← this]
    exact hy
  have h1 : π ⟨v, hv⟩ = 1 := by
    refine L436.eq_one_of_forall_commute hperf' fun y => ?_
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K₂) y
    have hk : ⟨v, hv⟩ * k * ⟨v, hv⟩⁻¹ * k⁻¹ ∈ CFSG.pCore 2 ↥K₂ := hmem _ (hc k k.2)
    have h2 : π (⟨v, hv⟩ * k * ⟨v, hv⟩⁻¹ * k⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr hk
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h2
    calc π ⟨v, hv⟩ * π k = (π ⟨v, hv⟩ * π k * (π ⟨v, hv⟩)⁻¹ * (π k)⁻¹) * (π k * π ⟨v, hv⟩) := by
          group
      _ = π k * π ⟨v, hv⟩ := by rw [h2, one_mul]
  have h3 := (QuotientGroup.eq_one_iff _).mp h1
  exact ⟨_, h3, rfl⟩

omit s in
theorem K₂_inf_pCoreOf_le {KZ : Subgroup G}
    (hK₂ : sp4K₂ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) ≤ KZ) :
    sp4K₂ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) ⊓ pCoreOf 2 KZ ≤
      sp4Q₁ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
    ((pCoreOf_isPGroup 2 KZ).to_le inf_le_right)
  intro k hk
  exact mem_normalizer_inf (Subgroup.le_normalizer hk) (le_normalizer_pCoreOf 2 KZ (hK₂ hk))

theorem exists_involution {y : G} (hy3 : y ^ 3 = 1)
    (hyV : y ∈ Subgroup.normalizer (v432 T M L : Set G))
    (hyK : ∀ k ∈ sp4K₂ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L),
      y * k * y⁻¹ * k⁻¹ ∈ sp4Q₁ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L))
    (hyK' : ∀ k ∈ sp4K₂ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L),
      y⁻¹ * k * y * k⁻¹ ∈ sp4Q₁ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L)) :
    ∃ v ∈ v432 T M L, v ∉ sp4Q₁ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) ∧ y * v = v * y := by
  classical
  set V := v432 T M L with hV
  set Q₁ := sp4Q₁ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) with hQ₁
  have hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := mul_comm_of_exp_two s.concl.V_sq
  obtain ⟨v₀, hv₀V, hv₀Q⟩ : ∃ v₀ ∈ V, v₀ ∉ Q₁ := by
    by_contra hno
    push Not at hno
    have hle : V ≤ V ⊓ Q₁ := fun v hv => ⟨hv, hno v hv⟩
    have h1 : (V ⊓ Q₁).relIndex V = 1 := Subgroup.relIndex_eq_one.mpr hle
    have h4 := s.four_le_two_pow
    rw [s.concl.index_V] at h1
    omega
  have hyVm : ∀ v ∈ V, y * v * y⁻¹ ∈ V := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp hyV v).mp hv
  have hyVm' : ∀ v ∈ V, y⁻¹ * v * y ∈ V := fun v hv => by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hyV) v).mp hv
    simpa using this
  set v₁ := y * v₀ * y⁻¹ with hv₁
  set v₂ := y⁻¹ * v₀ * y with hv₂
  have hv₁V : v₁ ∈ V := hyVm v₀ hv₀V
  have hv₂V : v₂ ∈ V := hyVm' v₀ hv₀V
  refine ⟨v₀ * v₁ * v₂, mul_mem (mul_mem hv₀V hv₁V) hv₂V, fun hvQ => hv₀Q ?_, ?_⟩
  ·
    have hb₁ : v₁ * v₀⁻¹ ∈ Q₁ := hyK v₀ (s.concl.V_le_K₂ hv₀V)
    have hb₂ : v₂ * v₀⁻¹ ∈ Q₁ := hyK' v₀ (s.concl.V_le_K₂ hv₀V)
    have hsq : v₀ * v₀ = 1 := by rw [← sq]; exact s.concl.V_sq v₀ hv₀V
    have hq : v₀ * (v₁ * v₀⁻¹) * v₀⁻¹ ∈ Q₁ :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ (s.concl.V_le_K₂ hv₀V)) _).mp hb₁
    have hrw : v₀ = ((v₀ * (v₁ * v₀⁻¹) * v₀⁻¹) * (v₂ * v₀⁻¹))⁻¹ * (v₀ * v₁ * v₂) := by
      calc v₀ = ((v₀ * (v₁ * v₀⁻¹) * v₀⁻¹) * (v₂ * v₀⁻¹))⁻¹ *
            (v₀ * v₁ * (v₀ * v₀)⁻¹ * v₂) := by group
        _ = ((v₀ * (v₁ * v₀⁻¹) * v₀⁻¹) * (v₂ * v₀⁻¹))⁻¹ * (v₀ * v₁ * v₂) := by
            rw [hsq, inv_one, mul_one]
    rw [hrw]
    exact mul_mem (inv_mem (mul_mem hq hb₂)) hvQ
  ·
    have hy2 : y * y = y⁻¹ := by
      rw [← mul_eq_one_iff_eq_inv, ← pow_three']
      exact hy3
    have e1 : y * v₁ * y⁻¹ = v₂ := by
      calc y * v₁ * y⁻¹ = (y * y) * v₀ * (y * y)⁻¹ := by rw [hv₁]; group
        _ = v₂ := by rw [hy2, inv_inv]
    have e2 : y * v₂ * y⁻¹ = v₀ := by rw [hv₂]; group
    have hc : y * (v₀ * v₁ * v₂) * y⁻¹ = v₀ * v₁ * v₂ := by
      calc y * (v₀ * v₁ * v₂) * y⁻¹ = (y * v₀ * y⁻¹) * (y * v₁ * y⁻¹) * (y * v₂ * y⁻¹) := by
            group
        _ = v₁ * v₂ * v₀ := by rw [← hv₁, e1, e2]
        _ = v₀ * (v₁ * v₂) := (hVab _ hv₀V _ (mul_mem hv₁V hv₂V)).symm
        _ = v₀ * v₁ * v₂ := (mul_assoc v₀ v₁ v₂).symm
    exact mul_inv_eq_iff_eq_mul.mp hc

theorem sqtkGroup_GZ :
    SQTKGroup ↥(Subgroup.normalizer (sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G)) := by
  have hyp := s.sk.base.hyp
  have := hyp.simple
  exact InternalSec.sqtkGroup_of_localSQTK (qtkeCore_of_cat hyp.nonabelian hyp.qtke).1 s.inH_GZ.2

omit s in
theorem pCoreOf_subgroupOf_le_pPrimeCore {X KZ : Subgroup G} (hKZX : KZ ≤ X)
    (hXKZ : X ≤ Subgroup.normalizer (KZ : Set G)) :
    (pCoreOf 2 KZ).subgroupOf X ≤ CFSG.pPrimeCore 3 ↥X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : pCoreOf 2 KZ ≤ X := (pCoreOf_le 2 KZ).trans hKZX
  have hn : ((pCoreOf 2 KZ).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hle).2
      (hXKZ.trans (normalizer_le_normalizer_pCoreOf 2 KZ))
  have hcard : Nat.card ↥((pCoreOf 2 KZ).subgroupOf X) = Nat.card ↥(pCoreOf 2 KZ) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (pCoreOf_isPGroup 2 KZ)
  have hcop : Nat.Coprime 3 (Nat.card ↥((pCoreOf 2 KZ).subgroupOf X)) := by
    rw [hcard, hk]
    exact Nat.Coprime.pow_right _ (by norm_num)
  exact le_sSup ⟨hn, hcop⟩

omit s in
theorem mem_centralizer_of_mem_starImage {Z KZ : Subgroup G}
    (hKZ : KZ ≤ Subgroup.centralizer (Z : Set G)) {p : ℕ} [Fact p.Prime] {y : G}
    (hyN : y ∈ Subgroup.normalizer (Z : Set G)) (hyo : orderOf y = p)
    (hmem : QuotientGroup.mk' (CFSG.pPrimeCore p ↥(Subgroup.normalizer (Z : Set G))) ⟨y, hyN⟩ ∈
      starImage p (KZ.subgroupOf (Subgroup.normalizer (Z : Set G)))) :
    y ∈ Subgroup.centralizer (Z : Set G) := by
  classical
  set GZ := Subgroup.normalizer (Z : Set G) with hGZ
  obtain ⟨k, hk, hky⟩ := hmem
  have ho : k⁻¹ * ⟨y, hyN⟩ ∈ CFSG.pPrimeCore p ↥GZ := by
    rw [← QuotientGroup.eq]
    exact hky
  set o : ↥GZ := k⁻¹ * ⟨y, hyN⟩ with hodef
  have hocop : Nat.Coprime p (orderOf o) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard _ ho) CFSG.pPrimeCore_coprime_card
  have hkZ : (k : G) ∈ Subgroup.centralizer (Z : Set G) := hKZ (Subgroup.mem_subgroupOf.mp hk)
  have hZm : ∀ g ∈ GZ, ∀ z ∈ Z, g * z * g⁻¹ ∈ Z := fun g hg z hz =>
    (Subgroup.mem_normalizer_iff.mp hg z).mp hz
  have hact : ∀ z ∈ Z, (o : G) * z * (o : G)⁻¹ = y * z * y⁻¹ := by
    intro z hz
    have h1 := Subgroup.mem_centralizer_iff.mp hkZ _ (hZm y hyN z hz)
    have e : (o : G) = (k : G)⁻¹ * y := by simp [hodef]
    rw [e]
    calc (k : G)⁻¹ * y * z * ((k : G)⁻¹ * y)⁻¹ = (k : G)⁻¹ * (y * z * y⁻¹ * (k : G)) := by group
      _ = (k : G)⁻¹ * ((k : G) * (y * z * y⁻¹)) := by rw [← h1]
      _ = y * z * y⁻¹ := by group
  have hpow : ∀ j : ℕ, ∀ z ∈ Z, (o : G) ^ j * z * ((o : G) ^ j)⁻¹ = y ^ j * z * (y ^ j)⁻¹ := by
    intro j
    induction j with
    | zero => intro z _; simp
    | succ j ih =>
      intro z hz
      have hz' : y ^ j * z * (y ^ j)⁻¹ ∈ Z := by
        have := hZm _ (pow_mem hyN j) z hz
        simpa using this
      calc (o : G) ^ (j + 1) * z * ((o : G) ^ (j + 1))⁻¹
          = (o : G) * ((o : G) ^ j * z * ((o : G) ^ j)⁻¹) * (o : G)⁻¹ := by group
        _ = (o : G) * (y ^ j * z * (y ^ j)⁻¹) * (o : G)⁻¹ := by rw [ih z hz]
        _ = y * (y ^ j * z * (y ^ j)⁻¹) * y⁻¹ := hact _ hz'
        _ = y ^ (j + 1) * z * (y ^ (j + 1))⁻¹ := by group
  have hym : y ^ orderOf o ∈ Subgroup.centralizer (Z : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have h1 := hpow (orderOf o) z hz
    have h2 : (o : G) ^ orderOf o = 1 := by
      rw [← Subgroup.coe_pow, pow_orderOf_eq_one, Subgroup.coe_one]
    rw [h2, one_mul, inv_one, mul_one] at h1
    calc z * y ^ orderOf o = (y ^ orderOf o * z * (y ^ orderOf o)⁻¹) * y ^ orderOf o := by
          rw [← h1]
      _ = y ^ orderOf o * z := by group
  have hcop' : Nat.Coprime (orderOf y) (orderOf o) := by rw [hyo]; exact hocop
  have hord : orderOf (y ^ orderOf o) = orderOf y := Nat.Coprime.orderOf_pow hcop'
  have hle : Subgroup.zpowers (y ^ orderOf o) ≤ Subgroup.zpowers y :=
    Subgroup.zpowers_le.mpr (Subgroup.npow_mem_zpowers y _)
  have heq : Subgroup.zpowers (y ^ orderOf o) = Subgroup.zpowers y :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hord])
  have hy : y ∈ Subgroup.zpowers (y ^ orderOf o) := heq ▸ Subgroup.mem_zpowers y
  exact (Subgroup.zpowers_le.mpr hym) hy

theorem pRank_KZ_le_one (hF : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK) {KZ : Subgroup G}
    (hKZ : KZ ∈ cComp (Subgroup.centralizer
      (sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G)))
    (hK₂ : sp4K₂ K (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) ≤ KZ)
    (hKZn : (KZ.subgroupOf (Subgroup.normalizer
      (sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G))).Normal)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n - 1) :
    CFSG.Open.pRank p KZ ≤ 1 ∨ (p = 3 ∧ A318Case2 (starImage 3 (KZ.subgroupOf
      (Subgroup.normalizer (sp4Z (H ⊓ M ⊓ K) (T ⊓ H ⊓ K) (v432 T M L) : Set G))))) := by
  classical
  set P := H ⊓ M ⊓ K with hP
  set S := T ⊓ H ⊓ K with hS
  set V := v432 T M L with hV
  set Z := sp4Z P S V with hZ
  set K₂ := sp4K₂ K P S V with hK₂def
  set Q₁ := sp4Q₁ K P S V with hQ₁
  set GZ := Subgroup.normalizer (Z : Set G) with hGZ
  have : Fact p.Prime := ⟨hp⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨hr, hn2⟩ := hcon
  have hH : SQTKGroup ↥GZ := s.sqtkGroup_GZ
  have hSQ := SQTKHyp.of_sqtkGroup ↥GZ hH
  have hKZ' := cComp_normalizer hKZ
  have hKZGZ : KZ ≤ GZ := le_of_mem_cComp hKZ'
  have hLc := subgroupOf_mem_cComp hKZ'
  have hq := s.KZ_quasisimple h36 hKZ hK₂
  obtain ⟨e₀⟩ := L436.quotPCore_subgroupOf_mulEquiv hKZGZ
  have hQ' := CFSG.LocalCores.isQuasisimple_of_mulEquiv e₀.symm hq
  have hr' : 1 < CFSG.Open.pRank p (KZ.subgroupOf GZ) := by
    rw [L436.pRank_subgroupOf_eq_pRank hKZGZ hp]
    exact hr
  have hconc := a318 hF hH (h36 _ hSQ) (h38 _ hSQ) hLc hQ' hp hp2 hr'
  obtain ⟨y, hyN, hyC, hyo, hyV, -, hyK, hyK'⟩ := s.exists_elt_Y₁ hp hpn
  set y' : ↥GZ := ⟨y, hyN⟩ with hy'
  have hy'o : orderOf y' = p := by rw [← Subgroup.orderOf_coe]; exact hyo
  have hyKZ : y' ∉ KZ.subgroupOf GZ := fun h =>
    hyC (le_of_mem_cComp hKZ (Subgroup.mem_subgroupOf.mp h))
  rcases hconc with h1 | ⟨hp3, h2⟩ | ⟨hp3, -, h3⟩
  · apply hyKZ
    rw [h1]
    exact Subgroup.subset_closure ⟨Subgroup.mem_top _, 1, by rw [pow_one, hy'o]⟩
  · exact hn2 hp3 (hp3 ▸ h2)
  · subst hp3
    rcases h3 with h3a | h3b
    · apply hyKZ
      rw [h3a]
      exact Subgroup.subset_closure ⟨Subgroup.mem_top _, hy'o⟩
    · obtain ⟨sb, q, x, -, hxo, -, -, -, -, hcard, hconj⟩ := h3b
      set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥GZ) with hπ
      set SK := starImage 3 (KZ.subgroupOf GZ) with hSK
      set ys := π y' with hys
      have hy3 : y ^ 3 = 1 := by
        have := pow_orderOf_eq_one y
        rwa [hyo] at this
      have hyS : ys ∉ SK := fun h =>
        hyC (mem_centralizer_of_mem_starImage (le_of_mem_cComp hKZ) hyN hyo h)
      have hys1 : ys ≠ 1 := fun h => hyS (h ▸ one_mem _)
      have hyso : orderOf ys = 3 := by
        have hy'3 : y' ^ 3 = 1 := by
          have := pow_orderOf_eq_one y'
          rwa [hy'o] at this
        have hd : orderOf ys ∣ 3 := orderOf_dvd_of_pow_eq_one (by
          rw [hys, ← map_pow, hy'3, map_one])
        rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
        · exact absurd (orderOf_eq_one_iff.mp h) hys1
        · exact h
      have hYc : Nat.card ↥(Subgroup.zpowers ys) = 3 := by rw [Nat.card_zpowers, hyso]
      have hYS : ¬ Subgroup.zpowers ys ≤ SK := fun h => hyS (h (Subgroup.mem_zpowers ys))
      obtain ⟨l, hlS, hYeq⟩ := hconj _ hYc hYS
      have hysmem : ys ∈ (Subgroup.zpowers x).map (MulAut.conj l).toMonoidHom :=
        hYeq ▸ Subgroup.mem_zpowers ys
      obtain ⟨z, hz, hzy⟩ := hysmem
      have hzy' : l * z * l⁻¹ = ys := hzy
      obtain ⟨v, hvV, hvQ, hvy⟩ := s.exists_involution hy3 hyV hyK hyK'
      have hvKZ : v ∈ KZ := hK₂ (s.concl.V_le_K₂ hvV)
      set v' : ↥GZ := ⟨v, hKZGZ hvKZ⟩ with hv'
      set vs := π v' with hvs
      have hvsS : vs ∈ SK := ⟨v', Subgroup.mem_subgroupOf.mpr hvKZ, rfl⟩
      have hvs2 : vs ^ 2 = 1 := by
        rw [hvs, ← map_pow]
        have : v' ^ 2 = 1 := Subtype.ext (s.concl.V_sq v hvV)
        rw [this, map_one]
      have hvsys : vs * ys = ys * vs := by
        rw [hvs, hys, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext hvy.symm
      have hvs1 : vs ≠ 1 := by
        intro h1
        have hvO : v' ∈ CFSG.pPrimeCore 3 ↥GZ := (QuotientGroup.eq_one_iff _).mp h1
        set N := KZ ⊓ (CFSG.pPrimeCore 3 ↥GZ).map GZ.subtype with hN
        have hNX : N ≤ KZ := inf_le_left
        have hON : (CFSG.pPrimeCore 3 ↥GZ).map GZ.subtype ≤
            Subgroup.normalizer (((CFSG.pPrimeCore 3 ↥GZ).map GZ.subtype : Subgroup G) : Set G) :=
          Subgroup.le_normalizer
        have hGZO : GZ ≤ Subgroup.normalizer
            (((CFSG.pPrimeCore 3 ↥GZ).map GZ.subtype : Subgroup G) : Set G) := by
          intro g hg
          rw [Subgroup.mem_normalizer_iff]
          intro w
          constructor
          · rintro ⟨w', hw', rfl⟩
            exact ⟨⟨g, hg⟩ * w' * ⟨g, hg⟩⁻¹,
              (CFSG.pPrimeCore_normal (p := 3) (G := ↥GZ)).conj_mem _ hw' _, rfl⟩
          · rintro ⟨w', hw', hw'e⟩
            refine ⟨⟨g, hg⟩⁻¹ * w' * ⟨g, hg⟩, ?_, ?_⟩
            · have := (CFSG.pPrimeCore_normal (p := 3) (G := ↥GZ)).conj_mem _ hw' ⟨g, hg⟩⁻¹
              simpa using this
            · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hw'e ⊢
              rw [hw'e]
              group
        have hXN : KZ ≤ Subgroup.normalizer (N : Set G) := fun k hk =>
          mem_normalizer_inf (Subgroup.le_normalizer hk) (hGZO (hKZGZ hk))
        have hne : ¬ KZ ≤ N ⊔ pCoreOf 2 KZ := by
          intro hle
          have hO2 : pCoreOf 2 KZ ≤ (CFSG.pPrimeCore 3 ↥GZ).map GZ.subtype := by
            intro w hw
            have hw' : (⟨w, (pCoreOf_le 2 KZ).trans hKZGZ hw⟩ : ↥GZ) ∈ CFSG.pPrimeCore 3 ↥GZ :=
              pCoreOf_subgroupOf_le_pPrimeCore hKZGZ
                ((Subgroup.normal_subgroupOf_iff_le_normalizer hKZGZ).1 hKZn) hw
            exact ⟨_, hw', rfl⟩
          have hsub : KZ ≤ (CFSG.pPrimeCore 3 ↥GZ).map GZ.subtype :=
            hle.trans (sup_le inf_le_right hO2)
          obtain ⟨a, haK, hao⟩ := s.exists_elt_K₂ Nat.prime_three hpn
          obtain ⟨a', ha', ha'e⟩ := hsub (hK₂ haK)
          have hdvd : 3 ∣ Nat.card ↥(CFSG.pPrimeCore 3 ↥GZ) := by
            have h1 : orderOf a' = 3 := by
              rw [← hao, ← ha'e, Subgroup.coe_subtype, Subgroup.orderOf_coe]
            have h2 := Subgroup.orderOf_dvd_natCard (CFSG.pPrimeCore 3 ↥GZ) ha'
            rwa [h1] at h2
          have := (CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥GZ))
          exact absurd (Nat.Coprime.eq_one_of_dvd this hdvd) (by norm_num)
        have hvN : v ∈ N := ⟨hvKZ, ⟨v', hvO, rfl⟩⟩
        have hcomm := L436.commutator_mem_pCoreOf_of_quasisimple hq hNX hXN hne v hvN
        have hvK₂ : v ∈ K₂ := s.concl.V_le_K₂ hvV
        refine hvQ (s.mem_Q₁_of_commutator_mem hvK₂ fun k hk => ?_)
        have hvk : v * k * v⁻¹ * k⁻¹ ∈ K₂ :=
          mul_mem (mul_mem (mul_mem hvK₂ hk) (inv_mem hvK₂)) (inv_mem hk)
        exact K₂_inf_pCoreOf_le hK₂ (Subgroup.mem_inf.mpr ⟨hvk, hcomm k (hK₂ hk)⟩)
      have hvso : orderOf vs = 2 := by
        have hd : orderOf vs ∣ 2 := orderOf_dvd_of_pow_eq_one hvs2
        rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
        · exact absurd (orderOf_eq_one_iff.mp h) hvs1
        · exact h
      set w := l⁻¹ * vs * l with hw
      have hwS : w ∈ SK := mul_mem (mul_mem (inv_mem hlS) hvsS) hlS
      have hwz : w * z = z * w := by
        have e : z = l⁻¹ * ys * l := by rw [← hzy']; group
        rw [hw, e]
        calc l⁻¹ * vs * l * (l⁻¹ * ys * l) = l⁻¹ * (vs * ys) * l := by group
          _ = l⁻¹ * (ys * vs) * l := by rw [hvsys]
          _ = l⁻¹ * ys * l * (l⁻¹ * vs * l) := by group
      have hz1 : z ≠ 1 := by
        intro h
        apply hys1
        rw [← hzy', h, mul_one, mul_inv_cancel]
      have hzx : Subgroup.zpowers z = Subgroup.zpowers x := by
        have hle : Subgroup.zpowers z ≤ Subgroup.zpowers x := Subgroup.zpowers_le.mpr hz
        have hzo : orderOf z = 3 := by
          have hd : orderOf z ∣ 3 := by
            have := orderOf_dvd_of_mem_zpowers hz
            rwa [hxo] at this
          rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
          · exact absurd (orderOf_eq_one_iff.mp h) hz1
          · exact h
        exact Subgroup.eq_of_le_of_card_ge hle
          (by rw [Nat.card_zpowers, Nat.card_zpowers, hzo, hxo])
      have hwx : w * x = x * w := by
        have hxz : x ∈ Subgroup.zpowers z := hzx ▸ Subgroup.mem_zpowers x
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxz
        exact (Commute.zpow_right hwz k)
      have hwo : orderOf w = 2 := by
        rw [hw, show l⁻¹ * vs * l = (MulAut.conj l⁻¹) vs by simp,
          MulEquiv.orderOf_eq]
        exact hvso
      have hwC : w ∈ SK ⊓ Subgroup.centralizer ({x} : Set _) :=
        ⟨hwS, Subgroup.mem_centralizer_singleton_iff.mpr hwx⟩
      have h2 : 2 ∣ Nat.card ↥(SK ⊓ Subgroup.centralizer ({x} : Set _)) := by
        have := Subgroup.orderOf_dvd_natCard _ hwC
        rwa [hwo] at this
      rw [hcard] at h2
      split_ifs at h2
      · have : Even (q * (q + 1)) := Nat.even_mul_succ_self q
        have e : q ^ 2 + q + 1 = q * (q + 1) + 1 := by ring
        rw [e] at h2
        exact (Nat.not_even_iff_odd.mpr (Even.add_one this)) (even_iff_two_dvd.mpr h2)
      · have : Even (q * (q - 1)) := Nat.even_mul_pred_self q
        have e : q ^ 2 - q + 1 = q * (q - 1) + 1 := by
          rcases Nat.eq_zero_or_pos q with h0 | hpos
          · subst h0; rfl
          · have : q ^ 2 - q = q * (q - 1) := by
              rw [Nat.mul_sub_one, sq]
            rw [this]
        rw [e] at h2
        exact (Nat.not_even_iff_odd.mpr (Even.add_one this)) (even_iff_two_dvd.mpr h2)

end Setting436Sp4

end CFSG.Quasithin.H13.Ch4
