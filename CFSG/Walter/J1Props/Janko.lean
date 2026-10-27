module

public import CFSG.Walter.J1Props.Transfer
public import CFSG.Walter.J1Recog.Main

public section

namespace CFSG.Walter.J1Props

open CFSG.Walter.J1

structure JankoHyp₀ (G : Type) [Group G] [Finite G] where
  index_ne_two : ∀ H : Subgroup G, H.index ≠ 2
  abelian_sylow : HasAbelianSylowTwo G
  t : G
  orderOf_t : orderOf t = 2
  F : Subgroup G
  le_centralizer : F ≤ Subgroup.centralizer ({t} : Set G)
  t_not_mem : t ∉ F
  centralizer_eq : Subgroup.centralizer ({t} : Set G) = Subgroup.zpowers t ⊔ F
  iso : F ≃* alternatingGroup (Fin 5)

theorem mem_of_pow_eq_one_of_coprime {X : Type*} [Group X] [Finite X] (N : Subgroup X) [N.Normal]
    {x : X} {n : ℕ} (hx : x ^ n = 1) (hn : Nat.Coprime n N.index) : x ∈ N := by
  have h1 : orderOf (x : X ⧸ N) ∣ n := orderOf_dvd_of_pow_eq_one (by
    rw [← QuotientGroup.mk_pow, hx, QuotientGroup.mk_one])
  have h2 : orderOf (x : X ⧸ N) ∣ N.index := by
    rw [Subgroup.index_eq_card]
    exact orderOf_dvd_natCard _
  have h3 : orderOf (x : X ⧸ N) = 1 := Nat.eq_one_of_dvd_coprimes hn h1 h2
  rw [← QuotientGroup.eq_one_iff]
  exact orderOf_eq_one_iff.mp h3

namespace JankoHyp₀

variable {G : Type} [Group G] [Finite G] (h : JankoHyp₀ G)

@[expose] def toJankoHyp (hs : IsSimpleGroup G) : JankoHyp G where
  isSimpleGroup := hs
  abelian_sylow := h.abelian_sylow
  t := h.t
  orderOf_t := h.orderOf_t
  F := h.F
  le_centralizer := h.le_centralizer
  t_not_mem := h.t_not_mem
  centralizer_eq := h.centralizer_eq
  iso := h.iso

include h in
theorem index_ne_two' : ∀ H : Subgroup G, H.Normal → H.index ≠ 2 :=
  fun H _ => h.index_ne_two H

theorem t_mul_t : h.t * h.t = 1 := by
  rw [← pow_two, ← h.orderOf_t, pow_orderOf_eq_one]

theorem t_ne_one : h.t ≠ 1 := by
  intro h1
  have := h.orderOf_t
  rw [h1, orderOf_one] at this
  omega

theorem commute_of_mem_F {x : G} (hx : x ∈ h.F) : x * h.t = h.t * x :=
  Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer hx)

theorem zpowers_le_normalizer : Subgroup.zpowers h.t ≤ Subgroup.normalizer (h.F : Set G) := by
  rw [Subgroup.zpowers_le]
  refine mem_normalizer_of_conj_mem fun x hx => ?_
  rw [← h.commute_of_mem_F hx, mul_inv_cancel_right]
  exact hx

theorem mem_centralizer_t {x : G} :
    x ∈ Subgroup.centralizer ({h.t} : Set G) ↔ x ∈ h.F ∨ h.t * x ∈ h.F := by
  rw [h.centralizer_eq, ← SetLike.mem_coe,
    Subgroup.coe_mul_of_left_le_normalizer_right _ _ h.zpowers_le_normalizer, Set.mem_mul]
  constructor
  · rintro ⟨a, ha, f, hf, rfl⟩
    rcases (mem_zpowers_of_orderOf_eq_two h.orderOf_t).mp ha with rfl | rfl
    · left
      rwa [one_mul]
    · right
      rwa [← mul_assoc, h.t_mul_t, one_mul]
  · rintro (hx | hx)
    · exact ⟨1, Subgroup.one_mem _, x, hx, one_mul x⟩
    · exact ⟨h.t, Subgroup.mem_zpowers _, h.t * x, hx, by rw [← mul_assoc, h.t_mul_t, one_mul]⟩

theorem mem_F_of_odd {x : G} (hx : x ∈ Subgroup.centralizer ({h.t} : Set G))
    (hodd : Odd (orderOf x)) : x ∈ h.F := by
  rcases h.mem_centralizer_t.mp hx with hx | hx
  · exact hx
  · exfalso
    set y := h.t * x
    have hxy : x = h.t * y := by rw [← mul_assoc, h.t_mul_t, one_mul]
    have hc : Commute h.t y := (h.commute_of_mem_F hx).symm
    obtain ⟨k, hk⟩ := hodd
    have h2 : h.t ^ 2 = 1 := by rw [← h.orderOf_t, pow_orderOf_eq_one]
    have h1 : (h.t * y) ^ (2 * k + 1) = 1 := by
      rw [← hk, ← hxy]
      exact pow_orderOf_eq_one x
    rw [hc.mul_pow, pow_succ h.t, pow_mul, h2, one_pow, one_mul] at h1
    apply h.t_not_mem
    have : h.t = (y ^ (2 * k + 1))⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [this]
    exact h.F.inv_mem (h.F.pow_mem hx _)

theorem card_F : Nat.card h.F = 60 := A5Sub.card_eq h.iso

theorem card_centralizer : Nat.card (Subgroup.centralizer ({h.t} : Set G)) = 120 := by
  have hdisj : Disjoint (Subgroup.zpowers h.t) h.F := by
    rw [Subgroup.disjoint_def]
    intro x hx hxF
    rcases (mem_zpowers_of_orderOf_eq_two h.orderOf_t).mp hx with rfl | rfl
    · rfl
    · exact absurd hxF h.t_not_mem
  rw [h.centralizer_eq, sup_comm, GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer,
    h.card_F, Nat.card_zpowers, h.orderOf_t]
  · exact h.zpowers_le_normalizer
  · exact hdisj.symm

theorem sylow_le_centralizer (S : Sylow 2 G) (htS : h.t ∈ S) :
    (S : Subgroup G) ≤ Subgroup.centralizer ({h.t} : Set G) := by
  intro x hx
  have := h.abelian_sylow S
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (this.is_comm.comm ⟨x, hx⟩ ⟨h.t, htS⟩))

include h in
theorem exists_sylow_mem_t : ∃ S : Sylow 2 G, h.t ∈ S := by
  have ht2 : IsPGroup 2 (Subgroup.zpowers h.t) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, h.orderOf_t, pow_one])
  obtain ⟨S, hS⟩ := ht2.exists_le_sylow
  exact ⟨S, hS (Subgroup.mem_zpowers _)⟩

theorem relIndex_inf_F (S : Sylow 2 G) (htS : h.t ∈ S) :
    ((S : Subgroup G) ⊓ h.F).relIndex S = 2 := by
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨h.t, htS⟩, fun b => ?_⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.mem_inf]
  have hbS : (b : G) ∈ (S : Subgroup G) := b.2
  have hbC := h.sylow_le_centralizer S htS hbS
  by_cases hb : (b : G) ∈ h.F
  · refine Or.inr ⟨⟨hbS, hb⟩, fun ⟨_, hbt⟩ => h.t_not_mem ?_⟩
    have : h.t = (b : G)⁻¹ * (b * h.t) := by group
    rw [this]
    exact h.F.mul_mem (h.F.inv_mem hb) hbt
  · refine Or.inl ⟨⟨(S : Subgroup G).mul_mem hbS htS, ?_⟩, fun ⟨_, hb'⟩ => hb hb'⟩
    rcases h.mem_centralizer_t.mp hbC with hb' | hb'
    · exact absurd hb' hb
    · rw [Subgroup.mem_centralizer_singleton_iff.mp hbC]
      exact hb'

theorem card_sylow_of_mem (S : Sylow 2 G) (htS : h.t ∈ S) : Nat.card (S : Subgroup G) = 8 := by
  have h1 := Subgroup.relIndex_mul_card ((S : Subgroup G) ⊓ h.F) S
  rw [h.relIndex_inf_F S htS, inf_assoc, inf_comm h.F, ← inf_assoc, inf_idem] at h1
  have hV4 : Nat.card ((S : Subgroup G) ⊓ h.F : Subgroup G) ∣ 4 :=
    A5Sub.card_dvd_four_of_isPGroup h.iso inf_le_right (S.isPGroup'.to_le inf_le_left)
  have h8 : 8 ∣ Nat.card (S : Subgroup G) := by
    have : 2 ^ 3 ∣ Nat.card G := by
      have := Subgroup.card_subgroup_dvd_card (Subgroup.centralizer ({h.t} : Set G))
      rw [h.card_centralizer] at this
      exact (by norm_num : 2 ^ 3 ∣ 120).trans this
    exact S.pow_dvd_card_of_pow_dvd_card this
  have hle : Nat.card ((S : Subgroup G) ⊓ h.F : Subgroup G) ≤ 4 := Nat.le_of_dvd (by norm_num) hV4
  have hpos : 0 < Nat.card ((S : Subgroup G) ⊓ h.F : Subgroup G) := Nat.card_pos
  omega

include h in
theorem card_sylow (S : Sylow 2 G) : Nat.card (S : Subgroup G) = 8 := by
  obtain ⟨T, hT⟩ := h.exists_sylow_mem_t
  rw [Sylow.card_eq_multiplicity, ← Sylow.card_eq_multiplicity T, h.card_sylow_of_mem T hT]

theorem mul_self_of_mem_sylow (S : Sylow 2 G) (htS : h.t ∈ S) {x : G} (hx : x ∈ S) :
    x * x = 1 := by
  have hF : ∀ y ∈ (S : Subgroup G) ⊓ h.F, y * y = 1 := by
    intro y hy
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨y, hy.1⟩
    have hk' := congrArg Subtype.val hk
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at hk'
    rw [← pow_two]
    exact A5Sub.sq_eq_one_of_pow h.iso hy.2 hk'
  have hxC := h.sylow_le_centralizer S htS hx
  rcases h.mem_centralizer_t.mp hxC with hxF | hxF
  · exact hF x ⟨hx, hxF⟩
  · have hy := hF _ ⟨(S : Subgroup G).mul_mem htS hx, hxF⟩
    have hc : h.t * x = x * h.t := (Subgroup.mem_centralizer_singleton_iff.mp hxC).symm
    calc x * x = (h.t * h.t) * (x * x) := by rw [h.t_mul_t, one_mul]
      _ = h.t * (h.t * x) * x := by group
      _ = h.t * (x * h.t) * x := by rw [hc]
      _ = (h.t * x) * (h.t * x) := by group
      _ = 1 := hy

theorem exists_conj_eq_t {x : G} (hx : orderOf x = 2) : ∃ g : G, g * x * g⁻¹ = h.t :=
  exists_conj_of_orderOf_eq_two h.index_ne_two' h.abelian_sylow h.card_sylow hx h.orderOf_t

theorem sylow_le_of_mem {L : Subgroup G} [L.Normal] {x : G} (hxL : x ∈ L) (hx : orderOf x = 2)
    (S : Sylow 2 G) (htS : h.t ∈ S) : (S : Subgroup G) ≤ L := by
  have hinv : ∀ y : G, orderOf y = 2 → y ∈ L := by
    intro y hy
    obtain ⟨g, hg⟩ := h.exists_conj_eq_t hx
    obtain ⟨k, hk⟩ := h.exists_conj_eq_t hy
    have htL : h.t ∈ L := by rw [← hg]; exact Subgroup.Normal.conj_mem inferInstance x hxL g
    have : y = k⁻¹ * h.t * k⁻¹⁻¹ := by rw [← hk]; group
    rw [this]
    exact Subgroup.Normal.conj_mem inferInstance _ htL _
  intro s hs
  by_cases hs1 : s = 1
  · rw [hs1]
    exact L.one_mem
  · exact hinv s (orderOf_eq_two_iff.mpr ⟨h.mul_self_of_mem_sylow S htS hs, hs1⟩)

theorem inf_centralizer_t_eq_bot {K : Subgroup G} [hK : K.Normal] (hodd : Odd (Nat.card K)) :
    K ⊓ Subgroup.centralizer ({h.t} : Set G) = ⊥ := by
  have hKF : K ⊓ h.F = ⊥ := by
    have : IsSimpleGroup h.F := A5Sub.isSimpleGroup h.iso
    have hn : ((K ⊓ h.F).subgroupOf h.F).Normal := by
      rw [Subgroup.inf_subgroupOf_right]
      exact hK.subgroupOf h.F
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((K ⊓ h.F).subgroupOf h.F) with h0 | h0
    · rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hx.2⟩ : h.F) ∈ (K ⊓ h.F).subgroupOf h.F := hx
      rw [h0, Subgroup.mem_bot] at this
      exact congrArg Subtype.val this
    · exfalso
      have hle : h.F ≤ K := fun x hx => by
        have : (⟨x, hx⟩ : h.F) ∈ (K ⊓ h.F).subgroupOf h.F := h0 ▸ Subgroup.mem_top _
        exact this.1
      have hdvd : Nat.card h.F ∣ Nat.card K := Subgroup.card_dvd_of_le hle
      rw [h.card_F] at hdvd
      obtain ⟨k, hk⟩ := hodd
      omega
  rw [eq_bot_iff]
  intro x ⟨hxK, hxC⟩
  have hodd' : Odd (orderOf x) := Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard K hxK)
  rw [← hKF]
  exact ⟨hxK, h.mem_F_of_odd hxC hodd'⟩

include h in
theorem eq_bot_of_odd (K : Subgroup G) [hK : K.Normal] (hodd : Odd (Nat.card K)) : K = ⊥ := by
  have hKt := h.inf_centralizer_t_eq_bot hodd
  have hinv : ∀ v : G, orderOf v = 2 → K ⊓ Subgroup.centralizer ({v} : Set G) = ⊥ := by
    intro v hv
    obtain ⟨g, hg⟩ := h.exists_conj_eq_t hv
    rw [eq_bot_iff]
    intro x ⟨hxK, hxC⟩
    have hgx : g * x * g⁻¹ ∈ K ⊓ Subgroup.centralizer ({h.t} : Set G) := by
      refine ⟨hK.conj_mem x hxK g, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have hc := Subgroup.mem_centralizer_singleton_iff.mp hxC
      rw [← hg]
      calc g * x * g⁻¹ * (g * v * g⁻¹) = g * (x * v) * g⁻¹ := by group
        _ = g * (v * x) * g⁻¹ := by rw [hc]
        _ = g * v * g⁻¹ * (g * x * g⁻¹) := by group
    rw [hKt, Subgroup.mem_bot] at hgx
    rw [Subgroup.mem_bot]
    have := congrArg (fun w => g⁻¹ * w * g) hgx
    simpa [mul_assoc] using this
  obtain ⟨f, hf⟩ := exists_prime_orderOf_dvd_card' (G := h.F) 2 (by rw [h.card_F]; norm_num)
  have hf2 : orderOf (f : G) = 2 := by rwa [Subgroup.orderOf_coe]
  have hff : (f : G) * f = 1 := (orderOf_eq_two_iff.mp hf2).1
  have htf : orderOf (h.t * f) = 2 := by
    refine orderOf_eq_two_iff.mpr ⟨?_, fun h1 => h.t_not_mem ?_⟩
    · have hc := h.commute_of_mem_F f.2
      calc h.t * f * (h.t * f) = h.t * (f * h.t) * f := by group
        _ = h.t * (h.t * f) * f := by rw [hc]
        _ = (h.t * h.t) * (f * f) := by group
        _ = 1 := by rw [h.t_mul_t, hff, one_mul]
    · rw [eq_inv_of_mul_eq_one_left h1]
      exact h.F.inv_mem f.2
  exact eq_bot_of_four_group h.t_mul_t hff (hinv _ h.orderOf_t) (hinv _ hf2) (hinv _ htf)

theorem sylow_le_of_ne_bot {L : Subgroup G} [hL : L.Normal] (hL1 : L ≠ ⊥) (S : Sylow 2 G)
    (htS : h.t ∈ S) : (S : Subgroup G) ≤ L := by
  have heven : 2 ∣ Nat.card L := by
    by_contra hno
    exact hL1 (h.eq_bot_of_odd L (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hno)))
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := L) 2 heven
  exact h.sylow_le_of_mem x.2 (by rwa [Subgroup.orderOf_coe]) S htS

theorem centralizer_le_of_odd_index (G₁ : Subgroup G) [hG₁ : G₁.Normal] (hodd : Odd G₁.index) :
    Subgroup.centralizer ({h.t} : Set G) ≤ G₁ := by
  have hco2 : Nat.Coprime 2 G₁.index := Nat.coprime_two_left.mpr hodd
  have htG : h.t ∈ G₁ := mem_of_pow_eq_one_of_coprime G₁ (by rw [pow_two]; exact h.t_mul_t) hco2
  have hFG : h.F ≤ G₁ := by
    have : IsSimpleGroup h.F := A5Sub.isSimpleGroup h.iso
    have hn : (G₁.subgroupOf h.F).Normal := hG₁.subgroupOf h.F
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (G₁.subgroupOf h.F) with h0 | h0
    · exfalso
      let φ : h.F →* G ⧸ G₁ := (QuotientGroup.mk' G₁).comp h.F.subtype
      have hinj : Function.Injective φ := by
        rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
        intro x hx
        have hx' : (x : G) ∈ G₁ := (QuotientGroup.eq_one_iff _).mp hx
        have : x ∈ G₁.subgroupOf h.F := hx'
        rwa [h0] at this
      have hdvd : Nat.card h.F ∣ Nat.card (G ⧸ G₁) := by
        have := Subgroup.card_dvd_of_le (le_top : φ.range ≤ ⊤)
        rw [Subgroup.card_top] at this
        rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
        exact this
      rw [h.card_F, ← Subgroup.index_eq_card] at hdvd
      obtain ⟨k, hk⟩ := hodd
      omega
    · intro x hx
      have : (⟨x, hx⟩ : h.F) ∈ G₁.subgroupOf h.F := h0 ▸ Subgroup.mem_top _
      exact this
  rw [h.centralizer_eq]
  exact sup_le (Subgroup.zpowers_le.mpr htG) hFG

include h in
theorem index_ne_two_of_odd_index (G₁ : Subgroup G) [hG₁ : G₁.Normal] (hodd : Odd G₁.index)
    (H : Subgroup G₁) : H.index ≠ 2 := by
  intro hH
  have hCG := h.centralizer_le_of_odd_index G₁ hodd
  have hHn : H.Normal := Subgroup.normal_of_index_eq_two hH
  have h3 : ∀ z : G₁, z ^ 3 = 1 → z ∈ H := fun z hz =>
    mem_of_pow_eq_one_of_coprime H hz (by rw [hH]; norm_num)
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := h.F) 3 (by rw [h.card_F]; norm_num)
  have hy3 : (y : G) ^ 3 = 1 := by rw [← Subgroup.orderOf_coe] at hy; rw [← hy, pow_orderOf_eq_one]
  have hy1 : (y : G) ≠ 1 := by
    intro h1
    rw [← Subgroup.orderOf_coe, h1, orderOf_one] at hy
    omega
  set C := Subgroup.normalClosure ({(y : G)} : Set G) with hC
  set H' := H.map G₁.subtype with hH'
  have hCH : C ≤ H' := by
    rw [hC, Subgroup.normalClosure, Subgroup.closure_le]
    intro x hx
    obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    rw [Set.mem_singleton_iff] at ha
    subst ha
    obtain ⟨c, rfl⟩ := isConj_iff.mp hax
    have hmem : c * (y : G) * c⁻¹ ∈ G₁ := hG₁.conj_mem _ (hCG (h.le_centralizer y.2)) c
    refine ⟨⟨_, hmem⟩, h3 _ (Subtype.ext ?_), rfl⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [conj_pow, hy3, mul_one, mul_inv_cancel]
  have hC1 : C ≠ ⊥ := by
    intro h0
    apply hy1
    have : (y : G) ∈ C := Subgroup.subset_normalClosure (Set.mem_singleton _)
    rwa [h0, Subgroup.mem_bot] at this
  obtain ⟨S, htS⟩ := h.exists_sylow_mem_t
  have hSC := h.sylow_le_of_ne_bot hC1 S htS
  have hSH : (S : Subgroup G) ≤ H' := hSC.trans hCH
  have hrel : H'.relIndex G₁ = 2 := by
    rw [Subgroup.relIndex, hH', Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective G₁.subtype_injective]
    exact hH
  have hH'G : H' ≤ G₁ := Subgroup.map_subtype_le H
  have h2 : 2 ∣ (S : Subgroup G).index := by
    rw [← Subgroup.relIndex_mul_index hSH, ← Subgroup.relIndex_mul_index hH'G, hrel]
    exact Dvd.dvd.mul_left (Dvd.intro _ rfl) _
  exact S.not_dvd_index h2

include h in
theorem eq_top_of_odd_index (G₁ : Subgroup G) [hG₁ : G₁.Normal] (hodd : Odd G₁.index) :
    G₁ = ⊤ := by
  have hCG := h.centralizer_le_of_odd_index G₁ hodd
  have htG : h.t ∈ G₁ := hCG (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  obtain ⟨S, htS⟩ := h.exists_sylow_mem_t
  have hSG : (S : Subgroup G) ≤ G₁ := (h.sylow_le_centralizer S htS).trans hCG
  have hab : HasAbelianSylowTwo G₁ := by
    intro Q
    obtain ⟨S', hS'⟩ := (Q.isPGroup'.map G₁.subtype).exists_le_sylow
    have hc := h.abelian_sylow S'
    refine ⟨⟨fun a b => ?_⟩⟩
    have ha : ((a : G₁) : G) ∈ (S' : Subgroup G) := hS' ⟨a, a.2, rfl⟩
    have hb : ((b : G₁) : G) ∈ (S' : Subgroup G) := hS' ⟨b, b.2, rfl⟩
    have hab := congrArg Subtype.val (hc.is_comm.comm ⟨_, ha⟩ ⟨_, hb⟩)
    apply Subtype.ext
    apply Subtype.ext
    exact hab
  have h8 : ∀ Q : Sylow 2 G₁, Nat.card (Q : Subgroup G₁) = 8 := by
    intro Q
    rw [Sylow.card_eq_multiplicity, ← Sylow.card_eq_multiplicity (S.subtype hSG),
      Sylow.coe_subtype, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSG).toEquiv,
      h.card_sylow S]
  have hG₁2 : ∀ H : Subgroup G₁, H.Normal → H.index ≠ 2 := fun H _ =>
    h.index_ne_two_of_odd_index G₁ hodd H
  have ht2 : orderOf (⟨h.t, htG⟩ : G₁) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact h.orderOf_t
  rw [eq_top_iff]
  intro g _
  have hgt : g * h.t * g⁻¹ ∈ G₁ := hG₁.conj_mem _ htG g
  have hgt2 : orderOf (⟨_, hgt⟩ : G₁) = 2 := by
    rw [← Subgroup.orderOf_coe]
    change orderOf (g * h.t * g⁻¹) = 2
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, h.orderOf_t]
  obtain ⟨k, hk⟩ := exists_conj_of_orderOf_eq_two hG₁2 hab h8 hgt2 ht2
  have hk' : (k : G) * (g * h.t * g⁻¹) * (k : G)⁻¹ = h.t := congrArg Subtype.val hk
  have hkg : (k : G) * g ∈ Subgroup.centralizer ({h.t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (k : G) * g * h.t = (k : G) * (g * h.t * g⁻¹) * (k : G)⁻¹ * ((k : G) * g) := by group
      _ = h.t * ((k : G) * g) := by rw [hk']
  have : g = (k : G)⁻¹ * ((k : G) * g) := by group
  rw [this]
  exact G₁.mul_mem (G₁.inv_mem k.2) (hCG hkg)

include h in
theorem isSimpleGroup : IsSimpleGroup G := by
  have : Nontrivial G := ⟨⟨h.t, 1, h.t_ne_one⟩⟩
  refine ⟨fun L hL => ?_⟩
  by_cases hL1 : L = ⊥
  · exact Or.inl hL1
  · right
    obtain ⟨S, htS⟩ := h.exists_sylow_mem_t
    have hSL := h.sylow_le_of_ne_bot hL1 S htS
    apply h.eq_top_of_odd_index L
    have h1 : L.index ∣ (S : Subgroup G).index := Subgroup.index_dvd_of_le hSL
    have h2 : ¬ 2 ∣ (S : Subgroup G).index := S.not_dvd_index
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h3 => h2 (h3.trans h1))

include h in
theorem nonempty_mulEquiv_walterJ1 : Nonempty (G ≃* CFSG.Open.walterJ1) :=
  J1Recog.nonempty_mulEquiv_walterJ1 (h.toJankoHyp h.isSimpleGroup)

end JankoHyp₀

end CFSG.Walter.J1Props
