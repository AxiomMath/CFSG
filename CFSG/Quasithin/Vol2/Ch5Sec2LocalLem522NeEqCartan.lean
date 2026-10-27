module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522NeEq
public import CFSG.Quasithin.Vol2.Ch11SecSXK3
public import CFSG.Quasithin.Vol2.Ch11SecA11Transport
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalL2Two

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def Stmt5_2_2_eq_cartan_rank2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D L₂ Dp : Subgroup G) (n p : ℕ),
    Hyp5_2_2p G T M L V H B D L₂ Dp n p → L₂ < oTwoUpper H → LieModel (O2Q L₂) .PSL 2 2 2 →
    quasithinIsCComponent (oTwoUpper H) H → ¬ IsBenderAny (O2Q (oTwoUpper H)) →
    ∀ P : Subgroup G, IsMaxParabolicOver (oTwoUpper H) (T ⊓ oTwoUpper H) P →
      quasithinIsCComponent L₂ P →
      IsElemAbelian 3 B ∧ Nat.card ↥B = 9 ∧
        Lin2.IsHallTwoPrimeOf (B ⊓ L₂) (L₂ ⊓ Subgroup.normalizer ((T ⊓ L₂ : Subgroup G) : Set G))

theorem mem_normalizer_inf_of_mul {Q : Type} [Group Q] [Finite Q] {K S : Subgroup Q} {a c : Q}
    (ha : a ∈ K) (hc : ∀ y ∈ K, c * y = y * c)
    (hx : a * c ∈ Subgroup.normalizer (S : Set Q)) :
    a ∈ Subgroup.normalizer ((S ⊓ K : Subgroup Q) : Set Q) := by
  refine mem_normalizer_of_conj_mem' fun s hs =>
    ⟨?_, K.mul_mem (K.mul_mem ha hs.2) (K.inv_mem ha)⟩
  have h1 := (Subgroup.mem_normalizer_iff.mp hx s).mp hs.1
  have e : a * c * s * (a * c)⁻¹ = a * s * a⁻¹ := by
    calc a * c * s * (a * c)⁻¹ = a * (c * s) * c⁻¹ * a⁻¹ := by group
      _ = a * (s * c) * c⁻¹ * a⁻¹ := by rw [hc s hs.2]
      _ = a * s * a⁻¹ := by group
  rwa [e] at h1

section General

variable {G : Type} [Group G] [Finite G]

theorem isCyclic_card_of_isHall_borelOf {T L₀ D : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    (hlie : LieModel (O2Q L₀) .PSL 2 2 n) (hSyl : IsSylowTwoOf (T ⊓ L₀) L₀)
    (hD : Lin2.IsHallTwoPrimeOf D (borelOf L₀ T)) : IsCyclic ↥D ∧ Nat.card D = 2 ^ n - 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hDB : D ≤ borelOf L₀ T := hD.1
  have hDL : D ≤ L₀ := hDB.trans inf_le_left
  have hTLL : T ⊓ L₀ ≤ L₀ := inf_le_right
  set π : ↥L₀ →* ↥L₀ ⧸ CFSG.pCore 2 ↥L₀ := QuotientGroup.mk' (CFSG.pCore 2 ↥L₀) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  set D' : Subgroup ↥L₀ := D.subgroupOf L₀ with hD'
  set S' : Subgroup ↥L₀ := (T ⊓ L₀).subgroupOf L₀ with hS'
  have hPS : CFSG.pCore 2 ↥L₀ ≤ S' := by
    intro x hx
    rw [hS', Subgroup.mem_subgroupOf]
    have hx' : (x : G) ∈ pCoreOf 2 L₀ := ⟨x, by assumption, rfl⟩
    exact F7.isSylowTwoOf_pCoreOf_le hSyl hx'
  have hS'2 : IsPGroup 2 S' :=
    hSyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTLL).symm
  have hcD' : Nat.card D' = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDL).toEquiv
  have hD'odd : Odd (Nat.card D') := hcD' ▸ hD.2.1
  have hDP : D' ⊓ CFSG.pCore 2 ↥L₀ = ⊥ := by
    refine (Subgroup.disjoint_of_coprime_natCard ?_).eq_bot
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp (CFSG.pCore_isPGroup (p := 2) (G := ↥L₀))
    rw [hm]
    exact Nat.Coprime.pow_right m (Nat.coprime_two_right.mpr hD'odd)
  have hinj : Function.Injective (π.comp D'.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    have hx' : (x : ↥L₀) ∈ D' ⊓ CFSG.pCore 2 ↥L₀ := ⟨x.2, hx⟩
    rw [hDP, Subgroup.mem_bot] at hx'
    exact (Subgroup.mem_bot).mpr (Subtype.ext hx')
  have hrange : (π.comp D'.subtype).range = D'.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let eD : ↥D ≃* ↥(D'.map π) :=
    ((Subgroup.subgroupOfEquivOfLe hDL).symm.trans (MonoidHom.ofInjective hinj)).trans
      (MulEquiv.subgroupCongr hrange)
  set Db : Subgroup (↥L₀ ⧸ CFSG.pCore 2 ↥L₀) := D'.map π with hDb
  set Sb : Subgroup (↥L₀ ⧸ CFSG.pCore 2 ↥L₀) := S'.map π with hSb
  have hSb2 : IsPGroup 2 Sb := hS'2.map π
  have hSbSyl : IsSylowTwoOf Sb ⊤ := by
    refine ⟨le_top, hSb2, ?_⟩
    show ¬ 2 ∣ Sb.relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    intro h2
    exact hSyl.2.2 (h2.trans (Subgroup.index_map_dvd _ hπs))
  have hDbN : Db ≤ Subgroup.normalizer (Sb : Set (↥L₀ ⧸ CFSG.pCore 2 ↥L₀)) := by
    refine (Subgroup.map_mono ?_).trans (Subgroup.le_normalizer_map π)
    exact le_normalizer_subgroupOf (hDB.trans inf_le_right)
  have hcDb : Nat.card Db = Nat.card D := (Nat.card_congr eD.toEquiv).symm
  have hDbSb : Db ⊓ Sb = ⊥ := by
    refine (Subgroup.disjoint_of_coprime_natCard ?_).eq_bot
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hSb2
    rw [hm, hcDb]
    exact Nat.Coprime.pow_right m (Nat.coprime_two_right.mpr hD.2.1)
  have hsup : Db ⊔ Sb = Subgroup.normalizer (Sb : Set (↥L₀ ⧸ CFSG.pCore 2 ↥L₀)) := by
    refine le_antisymm (sup_le hDbN Subgroup.le_normalizer) ?_
    intro xb hxb
    obtain ⟨x, rfl⟩ := hπs xb
    have hx1 : x ∈ Subgroup.normalizer ((Sb.comap π : Subgroup ↥L₀) : Set ↥L₀) :=
      Subgroup.le_normalizer_comap π hxb
    have hcomap : Sb.comap π = S' := by
      rw [hSb, Subgroup.comap_map_eq, hπ, QuotientGroup.ker_mk']
      exact sup_eq_left.mpr hPS
    rw [hcomap] at hx1
    have hxN : (x : G) ∈ Subgroup.normalizer ((T ⊓ L₀ : Subgroup G) : Set G) :=
      mem_normalizer_of_mem_normalizer_subgroupOf hTLL hx1
    have hxB : (x : G) ∈ D ⊔ (T ⊓ L₀) := by
      rw [sup_eq_of_isHall_isSylow hD
        (A4.isSylowTwoOf_mono hSyl (le_inf inf_le_right Subgroup.le_normalizer) inf_le_left)]
      exact Subgroup.mem_inf.mpr ⟨x.2, hxN⟩
    have hx2 : x ∈ D' ⊔ S' := by
      rw [hD', hS', ← Subgroup.subgroupOf_sup hDL hTLL, Subgroup.mem_subgroupOf]
      exact hxB
    have hx3 : π x ∈ (D' ⊔ S').map π := Subgroup.mem_map_of_mem π hx2
    rwa [Subgroup.map_sup] at hx3
  obtain ⟨hcyc, hcard⟩ :=
    l2TorusFact (↥L₀ ⧸ CFSG.pCore 2 ↥L₀) n hn hlie Sb Db hSbSyl hDbN hDbSb hsup
  exact ⟨isCyclic_of_surjective eD.symm.toMonoidHom eD.symm.surjective, hcDb ▸ hcard⟩

theorem isHallTwoPrimeOf_inf_of_le_normalizer {B Y N : Subgroup G}
    (hB : Lin2.IsHallTwoPrimeOf B Y) (hNY : N ≤ Y) (hYN : Y ≤ Subgroup.normalizer (N : Set G)) :
    Lin2.IsHallTwoPrimeOf (B ⊓ N) N := by
  obtain ⟨hBY, hBodd, k, hk⟩ := hB
  have hBN : B ≤ Subgroup.normalizer (N : Set G) := hBY.trans hYN
  refine ⟨inf_le_right, Odd.of_dvd_nat hBodd (Subgroup.card_dvd_of_le inf_le_left), ?_⟩
  have h1 := C5.card_sup_mul_card_inf_of_le_normalizer hBN
  have h2 := C5.card_eq_card_mul_relIndex (le_sup_left : B ≤ B ⊔ N)
  have h3 := C5.card_eq_card_mul_relIndex (inf_le_right : B ⊓ N ≤ N)
  have h4 : B.relIndex (B ⊔ N) * (B ⊔ N).relIndex Y = B.relIndex Y :=
    Subgroup.relIndex_mul_relIndex _ _ _ le_sup_left (sup_le hBY hNY)
  have hpos : 0 < Nat.card ↥B * Nat.card ↥(B ⊓ N) := Nat.mul_pos Nat.card_pos Nat.card_pos
  have h5 : (B ⊓ N).relIndex N = B.relIndex (B ⊔ N) := by
    refine Nat.eq_of_mul_eq_mul_left hpos ?_
    calc Nat.card ↥B * Nat.card ↥(B ⊓ N) * (B ⊓ N).relIndex N = Nat.card ↥B * Nat.card ↥N := by
          rw [h3]
          ring
      _ = Nat.card ↥(B ⊔ N) * Nat.card ↥(B ⊓ N) := h1.symm
      _ = Nat.card ↥B * Nat.card ↥(B ⊓ N) * B.relIndex (B ⊔ N) := by
          rw [h2]
          ring
  have h6 : (B ⊓ N).relIndex N ∣ 2 ^ k := by
    rw [h5, ← hk, ← h4]
    exact Dvd.intro _ rfl
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h6
  exact ⟨j, hj⟩

omit [Finite G] in
theorem inf_le_borelOf {T K K₁ : Subgroup G} (hK₁K : K₁ ≤ K) :
    K ⊓ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) ⊓ K₁ ≤ borelOf K₁ T := by
  intro y hy
  have h := Subgroup.inf_normalizer_le_normalizer_inf ⟨hy.1.2, Subgroup.le_normalizer hy.2⟩
  rw [inf_assoc, inf_eq_right.mpr hK₁K] at h
  exact Subgroup.mem_inf.mpr ⟨hy.2, h⟩

omit [Finite G] in
theorem mem_modO2Image_borelOf {H T K₁ : Subgroup G} (hK₁H : K₁ ≤ H) (hOT : pCoreOf 2 H ≤ T)
    {a : ↥H ⧸ CFSG.pCore 2 ↥H} (ha : a ∈ modO2Image H K₁)
    (haN : a ∈ Subgroup.normalizer
      ((modO2Image H (T ⊓ K₁) : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) : Set (↥H ⧸ CFSG.pCore 2 ↥H))) :
    a ∈ modO2Image H (borelOf K₁ T) := by
  obtain ⟨y, hy, rfl⟩ := ha
  have hyK : (y : G) ∈ K₁ := Subgroup.mem_subgroupOf.mp hy
  have h1 := mem_normalizer_sup_pCoreOf (inf_le_right.trans hK₁H) haN
  have h2 : ((T ⊓ K₁) ⊔ pCoreOf 2 H) ⊓ K₁ = T ⊓ K₁ :=
    le_antisymm (le_inf (inf_le_left.trans (sup_le inf_le_left hOT)) inf_le_right)
      (le_inf le_sup_left inf_le_right)
  have h3 := Subgroup.inf_normalizer_le_normalizer_inf ⟨h1, Subgroup.le_normalizer hyK⟩
  rw [h2] at h3
  exact ⟨y, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hyK, h3⟩), rfl⟩

end General

namespace TwoComp

variable {G : Type} [Group G] [Finite G] {T H K₁ K₂ : Subgroup G}

omit [Finite G] in
theorem inf_le_pCoreOf (tc : TwoComp T H K₁ K₂) (hK₁H : K₁ ≤ H) :
    K₁ ⊓ K₂ ≤ pCoreOf 2 H := by
  intro x hx
  have hxH : x ∈ H := hK₁H hx.1
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x, hxH⟩ ∈
      modO2Image H K₁ ⊓ modO2Image H K₂ :=
    ⟨⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.mpr hx.1, rfl⟩,
      ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.mpr hx.2, rfl⟩⟩
  rw [tc.inf, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  rw [Vol2.Ch11.SecS.pCoreOf_two_eq_map]
  exact ⟨_, h1, rfl⟩

theorem elemAbelian_nine (tc : TwoComp T H K₁ K₂) (hK₁ : K₁ ∈ cComp H)
    (hTH : IsSylowTwoOf T H) (hL4 : LieModel (O2Q K₁) .PSL 2 2 2) {B : Subgroup G}
    (hB : Lin2.IsHallTwoPrimeOf B
      (oTwoUpper H ⊓ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G))) :
    IsElemAbelian 3 B ∧ Nat.card ↥B = 9 ∧ Lin2.IsHallTwoPrimeOf (B ⊓ K₁) (borelOf K₁ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK₂ : K₂ ∈ cComp H := tc.cK₂
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hK₁K : K₁ ≤ oTwoUpper H := tc.sup ▸ le_sup_left
  have hK₂K : K₂ ≤ oTwoUpper H := tc.sup ▸ le_sup_right
  have hK₁H : K₁ ≤ H := hK₁K.trans hKH
  have hK₂H : K₂ ≤ H := hK₂K.trans hKH
  have hOT : pCoreOf 2 H ≤ T := F7.isSylowTwoOf_pCoreOf_le hTH
  have hKN₁ : oTwoUpper H ≤ Subgroup.normalizer (K₁ : Set G) := by
    rw [tc.sup]
    exact sup_le Subgroup.le_normalizer (le_normalizer_of_mem_cComp hK₁ hK₂)
  have hKN₂ : oTwoUpper H ≤ Subgroup.normalizer (K₂ : Set G) := by
    rw [tc.sup]
    exact sup_le (le_normalizer_of_mem_cComp hK₂ hK₁) Subgroup.le_normalizer
  have hY₁ := tc.borelOf_le hK₁ hTH
  have hY₂ := (tc.symm hK₁).borelOf_le hK₂ hTH
  obtain ⟨Y, hYdef⟩ : ∃ Y : Subgroup G,
      Y = oTwoUpper H ⊓ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) := ⟨_, rfl⟩
  rw [← hYdef] at hB hY₁ hY₂
  have hYK : Y ≤ oTwoUpper H := by
    rw [hYdef]
    exact inf_le_left
  have hYN : Y ≤ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) := by
    rw [hYdef]
    exact inf_le_right
  have hBY : B ≤ Y := hB.1
  have hBK : B ≤ oTwoUpper H := hBY.trans hYK
  have hBH : B ≤ H := hBK.trans hKH
  have hBodd : Odd (Nat.card ↥B) := hB.2.1
  have hBO : B ⊓ pCoreOf 2 H = ⊥ := by
    rw [inf_comm]
    exact Vol2.Ch11.SecS.inf_eq_bot_of_odd (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H) hBodd
  have hHall : ∀ {Ki : Subgroup G}, Ki ≤ oTwoUpper H →
      oTwoUpper H ≤ Subgroup.normalizer (Ki : Set G) → borelOf Ki T ≤ Y →
      Lin2.IsHallTwoPrimeOf (B ⊓ Ki) (borelOf Ki T) := by
    intro Ki hKiK hKN hYi
    have h2 : Y ⊓ Ki = borelOf Ki T := by
      refine le_antisymm ?_ (le_inf hYi inf_le_left)
      rw [hYdef]
      exact inf_le_borelOf hKiK
    have hYN' : Y ≤ Subgroup.normalizer ((borelOf Ki T : Subgroup G) : Set G) := by
      intro y hy
      have h1 : y ∈ Subgroup.normalizer ((Y ⊓ Ki : Subgroup G) : Set G) :=
        Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hy, hKN (hYK hy)⟩
      rwa [h2] at h1
    have h := isHallTwoPrimeOf_inf_of_le_normalizer hB hYi hYN'
    have h3 : B ⊓ borelOf Ki T = B ⊓ Ki := by
      refine le_antisymm (inf_le_inf_left B inf_le_left) fun x hx => ⟨hx.1, ?_⟩
      rw [← h2]
      exact ⟨hBY hx.1, hx.2⟩
    rwa [h3] at h
  have hHall₁ := hHall hK₁K hKN₁ hY₁
  have hHall₂ := hHall hK₂K hKN₂ hY₂
  have hL4₂ : LieModel (O2Q K₂) .PSL 2 2 2 := by
    obtain ⟨t, -, hK₂eq⟩ := tc.conj
    let e₀ : ↥K₁ ≃* ↥K₂ := Vol2.Ch11.SecA.mapEquivOfEq (MulAut.conj t) hK₂eq.symm
    exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
      (QuotientGroup.congr (CFSG.pCore 2 ↥K₁) (CFSG.pCore 2 ↥K₂) e₀
        (Vol2.Ch11.SecA.pCore_map_mulEquiv' 2 e₀)) hL4
  have hc₁ : Nat.card ↥(B ⊓ K₁) = 3 :=
    (isCyclic_card_of_isHall_borelOf le_rfl hL4
      (A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hK₁) hTH) hHall₁).2.trans
      (by norm_num)
  have hc₂ : Nat.card ↥(B ⊓ K₂) = 3 :=
    (isCyclic_card_of_isHall_borelOf le_rfl hL4₂
      (A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hK₂) hTH) hHall₂).2.trans
      (by norm_num)
  have hBB : (B ⊓ K₂) ⊓ (B ⊓ K₁) = ⊥ := by
    rw [eq_bot_iff, ← hBO]
    intro x hx
    exact ⟨hx.1.1, tc.inf_le_pCoreOf hK₁H ⟨hx.2.2, hx.1.2⟩⟩
  have hB₂N : B ⊓ K₂ ≤ Subgroup.normalizer ((B ⊓ K₁ : Subgroup G) : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx.1, hKN₁ (hBK hx.1)⟩
  have h9 : Nat.card ↥((B ⊓ K₂) ⊔ (B ⊓ K₁)) = 9 := by
    have h := C5.card_sup_mul_card_inf_of_le_normalizer hB₂N
    rw [hBB, Subgroup.card_bot, mul_one, hc₁, hc₂] at h
    omega
  have hsupB : (B ⊓ K₂) ⊔ (B ⊓ K₁) ≤ B := sup_le inf_le_left inf_le_left
  have hdvd₁ : 9 ∣ Nat.card ↥B := by
    rw [← h9]
    exact Subgroup.card_dvd_of_le hsupB
  have hcomm : ∀ x ∈ modO2Image H K₁, ∀ y ∈ modO2Image H K₂, x * y = y * x := tc.comm
  have hKb : modO2Image H (oTwoUpper H) = modO2Image H K₁ ⊔ modO2Image H K₂ := by
    rw [tc.sup]
    exact modO2Image_sup hK₁H hK₂H
  have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm).2
  have hK₁b : modO2Image H K₁ ≤ modO2Image H (oTwoUpper H) :=
    Subgroup.map_mono fun x hx => hK₁K hx
  have hK₂b : modO2Image H K₂ ≤ modO2Image H (oTwoUpper H) :=
    Subgroup.map_mono fun x hx => hK₂K hx
  have hS₁ : modO2Image H (T ⊓ oTwoUpper H) ⊓ modO2Image H K₁ = modO2Image H (T ⊓ K₁) := by
    rw [← modO2Image_inf_of_pCoreOf_le hOT, inf_assoc, inf_eq_right.mpr hK₁b,
      modO2Image_inf_of_pCoreOf_le hOT]
  have hS₂ : modO2Image H (T ⊓ oTwoUpper H) ⊓ modO2Image H K₂ = modO2Image H (T ⊓ K₂) := by
    rw [← modO2Image_inf_of_pCoreOf_le hOT, inf_assoc, inf_eq_right.mpr hK₂b,
      modO2Image_inf_of_pCoreOf_le hOT]
  have hBb : modO2Image H B ≤ modO2Image H (borelOf K₁ T) ⊔ modO2Image H (borelOf K₂ T) := by
    rintro _ ⟨b, hb, rfl⟩
    have hbB : (b : G) ∈ B := Subgroup.mem_subgroupOf.mp hb
    have hbK : QuotientGroup.mk' (CFSG.pCore 2 ↥H) b ∈
        ((modO2Image H K₁ ⊔ modO2Image H K₂ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :
          Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
      rw [← hKb]
      exact ⟨b, Subgroup.mem_subgroupOf.mpr (hBK hbB), rfl⟩
    have hbN : QuotientGroup.mk' (CFSG.pCore 2 ↥H) b ∈ Subgroup.normalizer
        ((modO2Image H (T ⊓ oTwoUpper H) : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :
          Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
      Vol2.Ch11.SecS.modO2Image_le_normalizer (A := T ⊓ oTwoUpper H) (B := B)
        (hBY.trans hYN) ⟨b, hb, rfl⟩
    rw [hset] at hbK
    obtain ⟨a, ha, c, hc, hac⟩ := hbK
    rw [← hac] at hbN ⊢
    have ha' : a ∈ modO2Image H (borelOf K₁ T) := by
      refine mem_modO2Image_borelOf hK₁H hOT ha ?_
      rw [← hS₁]
      exact mem_normalizer_inf_of_mul ha (fun y hy => (hcomm y hy c hc).symm) hbN
    have hc' : c ∈ modO2Image H (borelOf K₂ T) := by
      refine mem_modO2Image_borelOf hK₂H hOT hc ?_
      rw [← hS₂]
      refine mem_normalizer_inf_of_mul hc (fun y hy => hcomm a ha y hy) ?_
      rwa [← hcomm a ha c hc]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha') (Subgroup.mem_sup_right hc')
  obtain ⟨k₁, hk₁⟩ := hHall₁.2.2
  obtain ⟨k₂, hk₂⟩ := hHall₂.2.2
  have hY₁c : Nat.card ↥(borelOf K₁ T) = 3 * 2 ^ k₁ := by
    rw [C5.card_eq_card_mul_relIndex hHall₁.1, hc₁, hk₁]
  have hY₂c : Nat.card ↥(borelOf K₂ T) = 3 * 2 ^ k₂ := by
    rw [C5.card_eq_card_mul_relIndex hHall₂.1, hc₂, hk₂]
  have hY₁b : modO2Image H (borelOf K₁ T) ≤ modO2Image H K₁ :=
    Subgroup.map_mono fun z hz => hz.1
  have hY₂b : modO2Image H (borelOf K₂ T) ≤ modO2Image H K₂ :=
    Subgroup.map_mono fun z hz => hz.1
  have hd : Nat.card ↥B ∣ 9 * 2 ^ (k₁ + k₂) := by
    rw [← Vol2.Ch11.SecS.card_modO2Image_of_odd hBH hBodd]
    refine (Subgroup.card_dvd_of_le hBb).trans ?_
    have h1 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
      (modO2Image H (borelOf K₁ T)) (modO2Image H (borelOf K₂ T))
      (fun x hx y hy => hcomm x (hY₁b hx) y (hY₂b hy))).1
    refine (Dvd.intro _ h1).trans ?_
    have h2 := Subgroup.card_dvd_of_surjective (barMap_surjective (hY₁.trans (hYK.trans hKH)))
    have h3 := Subgroup.card_dvd_of_surjective (barMap_surjective (hY₂.trans (hYK.trans hKH)))
    calc Nat.card ↥(modO2Image H (borelOf K₁ T)) * Nat.card ↥(modO2Image H (borelOf K₂ T)) ∣
          Nat.card ↥(borelOf K₁ T) * Nat.card ↥(borelOf K₂ T) := Nat.mul_dvd_mul h2 h3
      _ = 9 * 2 ^ (k₁ + k₂) := by
          rw [hY₁c, hY₂c, pow_add]
          ring
  have hdvd₂ : Nat.card ↥B ∣ 9 :=
    Nat.Coprime.dvd_of_dvd_mul_right ((Nat.coprime_two_right.mpr hBodd).pow_right _) hd
  have hB9 : Nat.card ↥B = 9 := Nat.dvd_antisymm hdvd₂ hdvd₁
  have hBc : IsMulCommutative ↥B :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hB9]; norm_num)
  have hBeq : (B ⊓ K₂) ⊔ (B ⊓ K₁) = B :=
    Subgroup.eq_of_le_of_card_ge hsupB (hB9.trans h9.symm).le
  have hBcomm : ∀ x ∈ B ⊓ K₂, ∀ y ∈ B ⊓ K₁, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hBc.is_comm.comm ⟨x, hx.1⟩ ⟨y, hy.1⟩)
  have hset' := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hBcomm).2
  have h3 : ∀ {P : Subgroup G}, Nat.card ↥P = 3 → ∀ x ∈ P, x ^ 3 = 1 := by
    intro P hP x hx
    have h1 := orderOf_dvd_natCard (⟨x, hx⟩ : ↥P)
    rw [Subgroup.orderOf_mk, hP] at h1
    exact orderOf_dvd_iff_pow_eq_one.mp h1
  refine ⟨⟨hBc, fun b hb => ?_⟩, hB9, hHall₁⟩
  have hb' : b ∈ (((B ⊓ K₂) ⊔ (B ⊓ K₁) : Subgroup G) : Set G) := by
    rw [hBeq]
    exact hb
  rw [hset'] at hb'
  obtain ⟨x, hx, y, hy, rfl⟩ := hb'
  rw [Commute.mul_pow (hBcomm x hx y hy) 3, h3 hc₂ x hx, h3 hc₁ y hy, one_mul]

end TwoComp

theorem stmt5_2_2_eq_cartan_of (h510 : Stmt5_1_10) (h38 : Vol2Native.A38ForSQTKCat)
    (hres : Stmt5_2_2_eq_cartan_rank2) : Stmt5_2_2_eq_cartan := by
  intro G _ _ T M L V H B D L₂ Dp n p hyp hL₂K hL4
  have h := hyp.toHyp5_0_1
  have : IsSimpleGroup G := h.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hyp.hStar.1.1
  obtain ⟨K₁, hK₁, hKeq, hcase⟩ := hyp.choice
  rcases hcase with ⟨-, rfl⟩ | ⟨hnb, rfl, P, hP, hL₂P⟩
  ·
    obtain ⟨-, -, hBorel, hBH, -⟩ := h510 G T M L H B D n hyp.toHyp5_1_8 hyp.notation59
    rw [hyp.toHyp5_1_8.borel_eq hBorel] at hBH
    obtain ⟨K₂, tc⟩ := exists_twoComp h38 hloc hyp.hStar.1.2 hTH hK₁ hKeq hL₂K
    exact tc.elemAbelian_nine hK₁ hTH hL4 hBH
  · exact hres G T M L V H B D L₂ Dp n p hyp hL₂K hL4 hK₁ hnb P hP hL₂P

end CFSG.Quasithin.H13
