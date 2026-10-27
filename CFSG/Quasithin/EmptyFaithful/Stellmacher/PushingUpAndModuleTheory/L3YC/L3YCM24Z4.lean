module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Z4c
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Z6c

public section

namespace CFSG.Quasithin.Stellmacher.PU.L3YC.M24

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.QuasithinUnique.Ch1.SporLat
open CFSG.QuasithinUnique.Ch1.SporLat.M24
open CFSG.Blueprint CFSG.Sporadic.Mathieu
open CFSG.Quasithin.A312M24
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot
open CFSG.QuasithinUnique
open scoped Pointwise commutatorElement

section General

variable {G : Type} [Group G]

theorem normal_subgroupOf_sup {B T : Subgroup G} (hN : T ≤ Subgroup.normalizer (B : Set G)) :
    (B.subgroupOf (B ⊔ T)).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer (sup_le Subgroup.le_normalizer hN)

theorem isPGroup_quot_sup {B T : Subgroup G} (hT : IsPGroup 2 T)
    (hN : T ≤ Subgroup.normalizer (B : Set G)) :
    have := normal_subgroupOf_sup hN
    IsPGroup 2 (↥(B ⊔ T) ⧸ B.subgroupOf (B ⊔ T)) := by
  have := normal_subgroupOf_sup hN
  set Z := B ⊔ T with hZ
  have hBZ : B ≤ Z := le_sup_left
  have hTZ : T ≤ Z := le_sup_right
  set N : Subgroup ↥Z := B.subgroupOf Z with hNdef
  have hsup : B.subgroupOf Z ⊔ T.subgroupOf Z = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hBZ hTZ, ← hZ, Subgroup.subgroupOf_self]
  have hmapB : (B.subgroupOf Z).map (QuotientGroup.mk' N) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have htop : (T.subgroupOf Z).map (QuotientGroup.mk' N) = ⊤ := by
    have h1 := congrArg (Subgroup.map (QuotientGroup.mk' N)) hsup
    rw [Subgroup.map_sup, hmapB, bot_sup_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] at h1
    exact h1
  have hT' : IsPGroup 2 ↥(T.subgroupOf Z) :=
    hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTZ).symm
  refine hT'.of_surjective ((QuotientGroup.mk' N).comp (T.subgroupOf Z).subtype) fun q => ?_
  have hq : q ∈ (T.subgroupOf Z).map (QuotientGroup.mk' N) := by
    rw [htop]
    exact Subgroup.mem_top q
  obtain ⟨t, ht, rfl⟩ := hq
  exact ⟨⟨t, ht⟩, rfl⟩

theorem card_sup_eq_quot_mul [Finite G] {B T : Subgroup G} (hN : T ≤ Subgroup.normalizer (B : Set G)) :
    have := normal_subgroupOf_sup hN
    Nat.card ↥(B ⊔ T) = Nat.card (↥(B ⊔ T) ⧸ B.subgroupOf (B ⊔ T)) * Nat.card B := by
  have := normal_subgroupOf_sup hN
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (B.subgroupOf (B ⊔ T))]
  congr 1
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv

theorem card_sup_eq_two_pow [Finite G] {B T : Subgroup G} (hT : IsPGroup 2 T)
    (hN : T ≤ Subgroup.normalizer (B : Set G)) :
    ∃ t : ℕ, Nat.card ↥(B ⊔ T) = Nat.card B * 2 ^ t := by
  have := normal_subgroupOf_sup hN
  obtain ⟨t, ht⟩ := (IsPGroup.iff_card (p := 2)).mp (isPGroup_quot_sup hT hN)
  exact ⟨t, by rw [card_sup_eq_quot_mul hN, ht, mul_comm]⟩

theorem commutator_sup_le_of_card_two [Finite G] {B T : Subgroup G}
    (hN : T ≤ Subgroup.normalizer (B : Set G)) (hc : Nat.card ↥(B ⊔ T) = Nat.card B * 2) :
    ⁅B ⊔ T, B ⊔ T⁆ ≤ B := by
  have := normal_subgroupOf_sup hN
  have h2 : Nat.card (↥(B ⊔ T) ⧸ B.subgroupOf (B ⊔ T)) = 2 := by
    have hpos : 0 < Nat.card B := Nat.card_pos
    rw [card_sup_eq_quot_mul hN] at hc
    exact Nat.eq_of_mul_eq_mul_right hpos (hc.trans (mul_comm _ _))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsCyclic (↥(B ⊔ T) ⧸ B.subgroupOf (B ⊔ T)) := isCyclic_of_prime_card h2
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have hxy : (QuotientGroup.mk (⟨x, hx⟩ : ↥(B ⊔ T)) : ↥(B ⊔ T) ⧸ B.subgroupOf (B ⊔ T)) *
      QuotientGroup.mk (⟨y, hy⟩ : ↥(B ⊔ T)) =
      QuotientGroup.mk (⟨y, hy⟩ : ↥(B ⊔ T)) * QuotientGroup.mk (⟨x, hx⟩ : ↥(B ⊔ T)) :=
    (IsCyclic.commGroup (α := ↥(B ⊔ T) ⧸ B.subgroupOf (B ⊔ T))).mul_comm _ _
  have h3 : ⁅(⟨x, hx⟩ : ↥(B ⊔ T)), ⟨y, hy⟩⁆ ∈ B.subgroupOf (B ⊔ T) := by
    rw [← QuotientGroup.eq_one_iff]
    have := map_commutatorElement (QuotientGroup.mk' (B.subgroupOf (B ⊔ T)))
      (⟨x, hx⟩ : ↥(B ⊔ T)) ⟨y, hy⟩
    simp only [QuotientGroup.mk'_apply] at this
    rw [this]
    exact commutatorElement_eq_one_iff_mul_comm.mpr hxy
  rw [Subgroup.mem_subgroupOf] at h3
  rw [commutatorElement_def]
  simpa [commutatorElement_def] using h3

end General

section Perfect

variable {G : Type} [Group G]

theorem odd_mem_perfectCore' [Finite G] {T B : Subgroup G} (hT : IsPGroup 2 T)
    (hBA : B ≤ perfectCore (B ⊔ T)) {x : G} (hx : x ∈ B ⊔ T) {m : ℕ} (hm : m % 2 = 1)
    (hxm : x ^ m = 1) : x ∈ perfectCore (B ⊔ T) := by
  set Z := B ⊔ T with hZ
  set A := perfectCore Z with hA
  have hAZ : A ≤ Z := perfectCore_le Z
  have hTZ : T ≤ Z := le_sup_right
  have hBZ : B ≤ Z := le_sup_left
  have hAnorm : (A.subgroupOf Z).Normal := perfectCore_normal Z
  set N : Subgroup ↥Z := A.subgroupOf Z with hN
  have : N.Normal := hAnorm
  have hsup : B.subgroupOf Z ⊔ T.subgroupOf Z = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hBZ hTZ, ← hZ, Subgroup.subgroupOf_self]
  have hBN : B.subgroupOf Z ≤ N := fun b hb => hBA hb
  have hmapB : (B.subgroupOf Z).map (QuotientGroup.mk' N) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hBN
  have htop : (T.subgroupOf Z).map (QuotientGroup.mk' N) = ⊤ := by
    have h1 := congrArg (Subgroup.map (QuotientGroup.mk' N)) hsup
    rw [Subgroup.map_sup, hmapB, bot_sup_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] at h1
    exact h1
  have hT' : IsPGroup 2 ↥(T.subgroupOf Z) :=
    hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTZ).symm
  have hQ : IsPGroup 2 (↥Z ⧸ N) := by
    refine hT'.of_surjective ((QuotientGroup.mk' N).comp (T.subgroupOf Z).subtype) fun q => ?_
    have hq : q ∈ (T.subgroupOf Z).map (QuotientGroup.mk' N) := by
      rw [htop]
      exact Subgroup.mem_top q
    obtain ⟨t, ht, rfl⟩ := hq
    exact ⟨⟨t, ht⟩, rfl⟩
  have hg : (⟨x, hx⟩ : ↥Z) ^ m = 1 := Subtype.ext (by simpa using hxm)
  exact mem_of_pow_eq_one_odd N hQ hm hg

theorem le_perfectCore_of_commutators_z' [Finite G] {T B : Subgroup G} (hT : IsPGroup 2 T)
    (hBA : B ≤ perfectCore (B ⊔ T)) {V : Subgroup G} (hVZ : V ≤ B ⊔ T) {u z c₁ c₂ : G}
    (hu : u ∈ B ⊔ T) {m : ℕ} (hm : m % 2 = 1) (hum : u ^ m = 1)
    (hc₁ : ∃ x ∈ V, ⁅x, u⁆ = c₁) (hc₂ : ∃ x ∈ V, ⁅x, u⁆ = c₂) (hz : ⁅c₁, c₂⁆ = z)
    (hV : ∀ v ∈ V, ∃ x ∈ V, ⁅x, u⁆ = v ∨ ⁅x, u⁆ = v * z) : V ≤ perfectCore (B ⊔ T) := by
  have hP : ∀ x ∈ V, ⁅x, u⁆ ∈ perfectCore (B ⊔ T) := fun x hx =>
    comm_mem_perfectCore (hVZ hx) (odd_mem_perfectCore' hT hBA hu hm hum)
  have hzP : z ∈ perfectCore (B ⊔ T) := by
    obtain ⟨x₁, hx₁, rfl⟩ := hc₁
    obtain ⟨x₂, hx₂, rfl⟩ := hc₂
    rw [← hz, commutatorElement_def]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hP x₁ hx₁) (hP x₂ hx₂))
      (Subgroup.inv_mem _ (hP x₁ hx₁))) (Subgroup.inv_mem _ (hP x₂ hx₂))
  intro v hv
  obtain ⟨x, hx, h | h⟩ := hV v hv
  · rw [← h]
    exact hP x hx
  · have : v = ⁅x, u⁆ * z⁻¹ := by rw [h]; group
    rw [this]
    exact Subgroup.mul_mem _ (hP x hx) (Subgroup.inv_mem _ hzP)

end Perfect

section Native


theorem V4_le_perfectCore' [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] {B : Subgroup G24} (hBA : B ≤ perfectCore (B ⊔ m24CtxE.S))
    (hY : B ⊔ m24CtxE.S = Z4) : V4 ≤ perfectCore Z4 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hV, hc1, hc2, hs1, hs2, hz⟩ := V4_check
  obtain ⟨c₁, hc₁T, hc₁⟩ := exists_comm_of_enum (gens := wordG m24Sg V4w)
    (by rw [V4g_tab]; exact V4_check.1) (tab_u4) hc1 hs1
  obtain ⟨c₂, hc₂T, hc₂⟩ := exists_comm_of_enum (gens := wordG m24Sg V4w)
    (by rw [V4g_tab]; exact V4_check.1) (tab_u4) hc2 hs2
  have hcc : ⁅c₁, c₂⁆ = z0 := by
    refine comm_eq_of_mul_eq ?_
    rw [mul_assoc]
    apply eq_of_tab_eq (n := 24)
    rw [tab_mul, tab_mul, tab_mul, hc₁T, hc₂T, tab_z0]
    exact hz
  have := le_perfectCore_of_commutators_z' m24_S_isPGroup hBA (hY ▸ V4_le_Z4) (hY ▸ u4_mem)
    (m := 7) (by norm_num) u4_pow hc₁ hc₂ hcc
    (comm_z_of_enum (gens := wordG m24Sg V4w) enumV4 tab_u4 tab_z0 hV)
  rwa [hY] at this

theorem Z4_perfect' [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] {B : Subgroup G24} (hBA : B ≤ perfectCore (B ⊔ m24CtxE.S))
    (hY : B ⊔ m24CtxE.S = Z4) : perfectCore Z4 = Z4 :=
  perfectCore_eq_self_of_le_ker rho4 rho4_range_perfect (V4_le_perfectCore' hBA hY)
    (le_of_eq rho4_ker.2)

theorem card_sup_S [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] {B : Subgroup G24} (hN : m24CtxE.S ≤ Subgroup.normalizer (B : Set G24))
    (hcard : Nat.card B = 10752) : Nat.card ↥(B ⊔ m24CtxE.S) = 21504 := by
  obtain ⟨t, ht⟩ := card_sup_eq_two_pow m24_S_isPGroup hN
  rw [hcard] at ht
  have h1 : Nat.card m24CtxE.S ∣ Nat.card ↥(B ⊔ m24CtxE.S) := Subgroup.card_dvd_of_le le_sup_right
  have h2 : Nat.card ↥(B ⊔ m24CtxE.S) ∣ Nat.card G24 := Subgroup.card_subgroup_dvd_card _
  have hS : Nat.card m24CtxE.S = 2 ^ 10 := m24CtxE.S_card
  rw [hS] at h1
  rw [m24_card] at h2
  rw [ht] at h1 h2
  rcases t with _ | _ | u
  · exfalso
    norm_num at h1
  · rw [ht]
    norm_num
  · exfalso
    have h3 : 2 ^ 11 * 21 ∣ 2 ^ 10 * 239085 := by
      refine Dvd.dvd.trans ?_ h2
      refine ⟨2 ^ u, ?_⟩
      rw [pow_add, pow_add]
      ring
    have : 2 ^ 10 * (2 * 21) ∣ 2 ^ 10 * 239085 := by
      convert h3 using 1
    have h4 := Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
    omega

theorem member_of_card_21504 [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] {j : ℕ} (hj : j < 13) (h : memIdx[j]! = 21) :
    m24CtxE.Y j = Z4 ∨ m24CtxE.Y j = Z6 := by
  have hj46 : j = 4 ∨ j = 6 := idx_21 j hj h
  obtain ⟨-, a, ha, hZa⟩ := Z4_eq
  obtain ⟨-, b, hb, hZb⟩ := Z6_eq
  have hab : a ≠ b := fun h => Z4_ne_Z6 (hZa.trans (h ▸ hZb.symm))
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hj46 with rfl | rfl <;>
    first
      | exact absurd rfl hab
      | with_reducible exact Or.inl hZa.symm
      | with_reducible exact Or.inr hZb.symm

theorem sup_S_eq_Z6 [CFSG.QuasithinUnique.Ch1.SporLat.M24.M24Lat] {B : Subgroup G24} (hperf : ⁅B, B⁆ = B)
    (hN : m24CtxE.S ≤ Subgroup.normalizer (B : Set G24)) (hcard : Nat.card B = 10752) :
    B ⊔ m24CtxE.S = Z6 := by
  have hZc := card_sup_S hN hcard
  have hSZ : m24CtxE.S ≤ B ⊔ m24CtxE.S := le_sup_right
  have hne : B ⊔ m24CtxE.S ≠ ⊤ := by
    intro h
    rw [h, Subgroup.card_top, m24_card] at hZc
    omega
  obtain ⟨j, hj, hZj, hc⟩ := overgroup_member hSZ hne
  have hidx : memIdx[j]! = 21 := by
    rw [hZc] at hc
    omega
  rcases member_of_card_21504 hj hidx with h4 | h6
  · exfalso
    have hY : B ⊔ m24CtxE.S = Z4 := hZj.trans h4
    have hBA : B ≤ perfectCore (B ⊔ m24CtxE.S) := le_perfectCore_of_perfect le_sup_left hperf
    have hp := Z4_perfect' hBA hY
    have hZZ : ⁅Z4, Z4⁆ = Z4 := by
      have := perfectCore_perfect Z4
      rwa [hp] at this
    have hc2 : Nat.card ↥(B ⊔ m24CtxE.S) = Nat.card B * 2 := by rw [hZc, hcard]
    have hle : ⁅B ⊔ m24CtxE.S, B ⊔ m24CtxE.S⁆ ≤ B := commutator_sup_le_of_card_two hN hc2
    rw [hY, hZZ] at hle
    have := Subgroup.card_le_of_le (hY ▸ hle : Z4 ≤ B)
    rw [hcard] at this
    have h4c := (Z4_eq).1
    omega
  · exact hZj.trans h6


end Native


end CFSG.Quasithin.Stellmacher.PU.L3YC.M24
