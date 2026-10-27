module

public import CFSG.Quasithin.H13.L32NLem14333j

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint L14332 CFSG.LieType.BorelTits CFSG.Quasithin.SL3Model
open scoped commutatorElement MatrixGroups

namespace L14333

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {T L V V₂ K : Subgroup G} {g a z b d x : G} {D : HatModelU (fsuU T V)}
  (c : Ctx G T L V V₂ K g a z b d x D)
include c

theorem isSylowTwoOf_TL : QuasithinUnique.IsSylowTwoOf (T ⊓ L) L := by
  have hTG := c.ctx.hyp.fsu.sylow
  have hTS : QuasithinUnique.IsSylowTwoOf T (L ⊔ T) :=
    ⟨le_sup_right, hTG.1, fun h2 =>
      hTG.2 (h2.trans (Subgroup.relIndex_dvd_index_of_le le_sup_right))⟩
  exact A4.isSylowTwoOf_inf_normal hTS le_sup_left (sup_le Subgroup.le_normalizer c.T_le_normL)

theorem P_le_T : pCoreOf 2 L ≤ T :=
  (QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf c.isSylowTwoOf_TL).trans inf_le_left

theorem card_TL (hyp : AlmostSpecialL3Hyp 1 V (fsuV1 T V) L T (l32nH T V)) :
    Nat.card ↥(T ⊓ L) = 2 ^ 9 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨_, S⟩ := c.setting
  obtain ⟨-, hPcard⟩ := c.pCoreOf_eq hyp
  have hS := c.isSylowTwoOf_TL
  obtain ⟨m, hm⟩ := hS.2.1.exists_card_eq
  have hodd : Odd ((T ⊓ L).relIndex L) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hS.2.2)
  have h := Subgroup.relIndex_mul_card (T ⊓ L) L
  rw [inf_eq_left.mpr (inf_le_right : T ⊓ L ≤ L), hm, S.card_L, hPcard] at h
  have hm9 : m = 9 := by
    have h' : 2 ^ m * (T ⊓ L).relIndex L = 2 ^ 9 * 21 :=
      calc 2 ^ m * (T ⊓ L).relIndex L = (T ⊓ L).relIndex L * 2 ^ m := mul_comm _ _
        _ = 168 * 64 := h
        _ = 2 ^ 9 * 21 := by norm_num
    exact two_pow_eq_of_mul_odd hodd (by decide) h'
  rw [hm, hm9]

theorem card_T (hTS : QuasithinUnique.IsSylowTwoOf T (l32nH T V)) :
    Nat.card ↥T = 8 * Nat.card ↥(pCoreOf 2 (l32nH T V)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := c.ctx.T2.exists_card_eq
  obtain ⟨q, hq⟩ := (pCoreOf_isPGroup 2 (l32nH T V)).exists_card_eq
  have hH : Nat.card ↥(l32nH T V) = Nat.card ↥(pCoreOf 2 (l32nH T V)) * 120 := by
    have h := Subgroup.card_ker_mul_card_range (imgHom D)
    rw [imgHom_ker, ← c.q_eq, MonoidHom.range_eq_top.mpr (imgHom_surjective D), Subgroup.card_top,
      card_img_l32nH c.ii] at h
    rw [← h, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (pCoreOf_le 2 _)).toEquiv]
  have hoddH : Odd (T.relIndex (l32nH T V)) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hTS.2.2)
  have hHT := Subgroup.relIndex_mul_card T (l32nH T V)
  rw [inf_eq_left.mpr hTS.1, hm, hH, hq] at hHT
  have hmq : m = q + 3 := by
    have h' : 2 ^ m * T.relIndex (l32nH T V) = 2 ^ (q + 3) * 15 :=
      calc 2 ^ m * T.relIndex (l32nH T V) = T.relIndex (l32nH T V) * 2 ^ m := mul_comm _ _
        _ = 2 ^ q * 120 := hHT
        _ = 2 ^ (q + 3) * 15 := by rw [pow_add]; ring
    exact two_pow_eq_of_mul_odd hoddH (by decide) h'
  rw [hm, hq, hmq, pow_add]
  ring

theorem conj_d (hyp : AlmostSpecialL3Hyp 1 V (fsuV1 T V) L T (l32nH T V)) {h : G}
    (hh : h ∈ l32nH T V) : h * d * h⁻¹ = d ∨ h * d * h⁻¹ = d⁻¹ := by
  set e := h * d * h⁻¹ with he
  have heZ : e ∈ centerOf (fsuU T V) :=
    (Subgroup.mem_normalizer_iff.mp (l32nH_le_normalizer_zU hh) d).mp c.d_mem
  have hee : e * e = z := by
    calc e * e = h * (d * d) * h⁻¹ := by rw [he]; group
      _ = z := by rw [c.d_sq]; exact c.ctx.H_V1 h hh z c.z_mem
  have hc : e * d⁻¹ = d⁻¹ * e :=
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (inv_mem c.d_mem)).2 e
      (Subgroup.mem_inf.mp heZ).1
  have h1 : e * d⁻¹ ∈ centerOf (fsuU T V) := mul_mem heZ (inv_mem c.d_mem)
  have h2 : e * d⁻¹ * (e * d⁻¹) = 1 := by
    calc e * d⁻¹ * (e * d⁻¹) = e * (d⁻¹ * e) * d⁻¹ := by group
      _ = e * (e * d⁻¹) * d⁻¹ := by rw [← hc]
      _ = (e * e) * (d * d)⁻¹ := by group
      _ = 1 := by rw [hee, c.d_sq]; group
  have hV : e * d⁻¹ ∈ V := c.mem_V_of_mul_self hyp ((le_sup_right.trans (c.sup_zU_le_P hyp)) h1) h2
  have hV1 : e * d⁻¹ ∈ fsuV1 T V := by rw [← c.vZ]; exact ⟨hV, h1⟩
  rcases c.eq_of_mem_V1 hV1 with h3 | h3
  · left
    calc e = e * d⁻¹ * d := by group
      _ = d := by rw [h3, one_mul]
  · right
    have h4 : d * d * d * d = 1 := by
      have h := pow_orderOf_eq_one d
      rw [c.orderOf_d, show (4 : ℕ) = 1 + 1 + 1 + 1 from rfl, pow_add, pow_add, pow_add,
        pow_one] at h
      exact h
    calc e = e * d⁻¹ * d := by group
      _ = d * d * d := by rw [h3, ← c.d_sq]
      _ = d⁻¹ := eq_inv_of_mul_eq_one_left h4

theorem mem_zU_of_mem_Q (hyp : AlmostSpecialL3Hyp 1 V (fsuV1 T V) L T (l32nH T V)) {q : G}
    (hq : q ∈ pCoreOf 2 (l32nH T V)) (hqx : q * x = x * q) (hqd : q * d = d * q) :
    q ∈ centerOf (fsuU T V) := by
  have hqT := c.q_le hq
  have hx : x * q * x⁻¹ = q := by rw [← hqx]; group
  have hZ : ∀ e ∈ centerOf (fsuU T V), q * e = e * q := by
    intro e he
    rw [← c.zpowers_d] at he
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    exact (Commute.zpow_right hqd k).eq
  have hK := c.comm_K_of_comm_U hyp hqT fun u hu => c.comm_U_of_comm hq hx hZ hu
  exact c.mem_zU_of_comm_K hyp hqT fun k hk => (hK k hk).symm

theorem le_L_of_comm_d (hyp : AlmostSpecialL3Hyp 1 V (fsuV1 T V) L T (l32nH T V))
    (hTS : QuasithinUnique.IsSylowTwoOf T (l32nH T V))
    (h : ∀ q ∈ pCoreOf 2 (l32nH T V), q * x = x * q → q * d = d * q) : T ≤ L := by
  have hQU : pCoreOf 2 (l32nH T V) ≤ fsuU T V := by
    intro q hq
    obtain ⟨u, hu, s, hs, hsx, rfl⟩ := c.exists_mul_Q hq
    have hsx' : s * x = x * s := by
      calc s * x = (x * s * x⁻¹) * x := by rw [hsx]
        _ = x * s := by group
    exact mul_mem hu (Subgroup.mem_inf.mp (c.mem_zU_of_mem_Q hyp hs hsx' (h s hs hsx'))).1
  have h1 := Subgroup.card_le_of_le hQU
  have h2 := Subgroup.card_le_of_le (fsuU_le_pCoreOf c.ctx)
  rw [c.card_U] at h1 h2
  have hT : Nat.card ↥T = 2 ^ 9 := by rw [c.card_T hTS, le_antisymm h1 h2]; norm_num
  have heq : T ⊓ L = T := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hT, c.card_TL hyp])
  intro t ht
  have : t ∈ T ⊓ L := by rw [heq]; exact ht
  exact this.2

end Ctx

structure Inv (G : Type) [Group G] [Finite G] (T L V V₂ K : Subgroup G) (g a z b d x r : G)
    (D : HatModelU (fsuU T V)) : Prop extends Ctx G T L V V₂ K g a z b d x D where
  hyp : AlmostSpecialL3Hyp 1 V (fsuV1 T V) L T (l32nH T V)
  hTS : QuasithinUnique.IsSylowTwoOf T (l32nH T V)
  r_Q : r ∈ pCoreOf 2 (l32nH T V)
  r_x : r * x = x * r
  r_d : r * d * r⁻¹ = d⁻¹
  r_V : ∀ v ∈ V, r * v = v * r
  r_P : ∀ p ∈ pCoreOf 2 L, r * p * r⁻¹ = p⁻¹
  r_L : ∀ l ∈ L, r * l * r⁻¹ * l⁻¹ ∈ V
  r_sq : r * r = 1

namespace Inv

variable {T L V V₂ K : Subgroup G} {g a z b d x r : G} {D : HatModelU (fsuU T V)}
  (ι : Inv G T L V V₂ K g a z b d x r D)
include ι

theorem r_T : r ∈ T := ι.q_le ι.r_Q

theorem r_notL : r ∉ L := ι.not_mem_L ι.hyp ι.r_V ι.r_d

theorem r_inv : r⁻¹ = r := inv_eq_of_mul_eq_one_right ι.r_sq

theorem mem_Q {q : G} (hq : q ∈ pCoreOf 2 (l32nH T V)) :
    q ∈ fsuU T V ∨ q * r⁻¹ ∈ fsuU T V := by
  obtain ⟨u, hu, s, hs, hsx, rfl⟩ := ι.exists_mul_Q hq
  have hsx' : s * x = x * s := by
    calc s * x = (x * s * x⁻¹) * x := by rw [hsx]
      _ = x * s := by group
  rcases ι.conj_d ι.hyp (pCoreOf_le 2 _ hs) with h1 | h1
  · left
    have hsd : s * d = d * s := by
      calc s * d = s * d * s⁻¹ * s := by group
        _ = d * s := by rw [h1]
    exact mul_mem hu (Subgroup.mem_inf.mp (ι.mem_zU_of_mem_Q ι.hyp hs hsx' hsd)).1
  · right
    have hsr : s * r⁻¹ ∈ pCoreOf 2 (l32nH T V) := mul_mem hs (inv_mem ι.r_Q)
    have hsrx : s * r⁻¹ * x = x * (s * r⁻¹) := by
      rw [ι.r_inv, mul_assoc, ι.r_x, ← mul_assoc, hsx', mul_assoc]
    have hrd' : r⁻¹ * d * r = d⁻¹ := by
      calc r⁻¹ * d * r = r * d * r⁻¹ := by rw [ι.r_inv]
        _ = d⁻¹ := ι.r_d
    have hsrd : s * r⁻¹ * d = d * (s * r⁻¹) := by
      calc s * r⁻¹ * d = (s * (r⁻¹ * d * r) * s⁻¹) * (s * r⁻¹) := by group
        _ = (s * d * s⁻¹)⁻¹ * (s * r⁻¹) := by rw [hrd']; group
        _ = d * (s * r⁻¹) := by rw [h1, inv_inv]
    rw [mul_assoc]
    exact mul_mem hu (Subgroup.mem_inf.mp (ι.mem_zU_of_mem_Q ι.hyp hsr hsrx hsrd)).1

theorem mem_U_of_mem_L {q : G} (hq : q ∈ pCoreOf 2 (l32nH T V)) (hqL : q ∈ L) : q ∈ fsuU T V := by
  rcases ι.mem_Q hq with h | h
  · exact h
  · exfalso
    have h1 : r⁻¹ ∈ L := by
      have := L.mul_mem (L.inv_mem hqL) (ι.U_le_L ι.hyp h)
      rwa [inv_mul_cancel_left] at this
    exact ι.r_notL (by rwa [inv_mem_iff] at h1)

theorem card_Q_le : Nat.card ↥(pCoreOf 2 (l32nH T V)) ≤ 128 := by
  have hsub : (pCoreOf 2 (l32nH T V) : Set G) ⊆
      (fsuU T V : Set G) ∪ (fun u => u * r) '' (fsuU T V : Set G) := by
    intro q hq
    rcases ι.mem_Q hq with h | h
    · exact Or.inl h
    · exact Or.inr ⟨q * r⁻¹, h, by group⟩
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 := Set.ncard_union_le (fsuU T V : Set G) ((fun u => u * r) '' (fsuU T V : Set G))
  have h3 : ((fun u => u * r) '' (fsuU T V : Set G)).ncard = (fsuU T V : Set G).ncard :=
    Set.ncard_image_of_injective _ (mul_left_injective r)
  have hU : (fsuU T V : Set G).ncard = 64 := by rw [← Nat.card_coe_set_eq]; exact ι.card_U
  have hQ : Nat.card ↥(pCoreOf 2 (l32nH T V)) = (pCoreOf 2 (l32nH T V) : Set G).ncard :=
    Nat.card_coe_set_eq _
  omega

theorem card_T_eq : Nat.card ↥T = 2 ^ 10 ∧ L.relIndex T = 2 := by
  have hT := ι.card_T ι.hTS
  have hQ := ι.card_Q_le
  have h := Subgroup.relIndex_mul_card L T
  rw [inf_comm, ι.card_TL ι.hyp] at h
  have hne : L.relIndex T ≠ 1 := fun h1 => ι.r_notL (Subgroup.relIndex_eq_one.mp h1 ι.r_T)
  have hpos : 0 < Nat.card ↥T := Nat.card_pos
  have h2 : L.relIndex T = 2 := by
    have : L.relIndex T * 512 ≤ 1024 := by
      calc L.relIndex T * 512 = L.relIndex T * 2 ^ 9 := by norm_num
        _ = Nat.card ↥T := h
        _ ≤ 1024 := by omega
    have h0 : L.relIndex T ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at h
      omega
    omega
  refine ⟨?_, h2⟩
  rw [← h, h2]
  norm_num

theorem mul_mem_iff {a b : G} (ha : a ∈ T) (hb : b ∈ T) : a * b ∈ L ↔ (a ∈ L ↔ b ∈ L) :=
  Subgroup.mul_mem_iff_of_index_two (H := L.subgroupOf T) ι.card_T_eq.2 (a := ⟨a, ha⟩)
    (b := ⟨b, hb⟩)

theorem comm_mem {a b : G} (ha : a ∈ T) (hb : b ∈ T) : a * b * a⁻¹ * b⁻¹ ∈ L := by
  have hab := T.mul_mem ha hb
  have haba := T.mul_mem hab (T.inv_mem ha)
  rw [ι.mul_mem_iff haba (T.inv_mem hb), ι.mul_mem_iff hab (T.inv_mem ha), ι.mul_mem_iff ha hb,
    inv_mem_iff (x := a), inv_mem_iff (x := b)]
  tauto

theorem sq_mem {a : G} (ha : a ∈ T) : a * a ∈ L := (ι.mul_mem_iff ha ha).mpr Iff.rfl

theorem card_X_ge : 2 ^ 7 ≤ Nat.card ↥(T ⊓ Subgroup.centralizer ({r} : Set G)) := by
  obtain ⟨-, hPcard⟩ := ι.pCoreOf_eq ι.hyp
  set X := T ⊓ Subgroup.centralizer ({r} : Set G) with hX
  set XL := T ⊓ L ⊓ Subgroup.centralizer ({r} : Set G) with hXL
  have hPT := ι.P_le_T
  have hle : T ⊓ L ≤ pCoreOf 2 L ⊔ XL := by
    intro t ht
    obtain ⟨p, hp, hpt⟩ := ι.exists_mul_comm ι.hyp ι.r_P ι.r_L ht.2
    have hptX : p * t ∈ XL := ⟨⟨T.mul_mem (hPT hp) ht.1, L.mul_mem (pCoreOf_le 2 L hp) ht.2⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr hpt.symm⟩
    have e : t = p⁻¹ * (p * t) := by group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left (inv_mem hp)) (Subgroup.mem_sup_right hptX)
  have hV : V ≤ pCoreOf 2 L ⊓ XL := by
    intro v hv
    have hvP : v ∈ pCoreOf 2 L := (le_sup_left.trans (ι.sup_zU_le_P ι.hyp)) hv
    exact ⟨hvP, ⟨hPT hvP, pCoreOf_le 2 L hvP⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr (ι.r_V v hv).symm⟩
  have hXLN : XL ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) := fun y hy =>
    le_normalizer_pCoreOf 2 L hy.1.2
  have hcard := L32NSet14.card_sup_mul_card_inf hXLN
  rw [sup_comm, inf_comm, hPcard] at hcard
  have h1 := Subgroup.card_le_of_le hle
  rw [ι.card_TL ι.hyp] at h1
  have h2 := Subgroup.card_le_of_le hV
  rw [ι.card_V] at h2
  have hXL64 : 64 ≤ Nat.card ↥XL := by
    have h3 := Nat.mul_le_mul h1 h2
    rw [hcard] at h3
    norm_num at h3
    omega
  have hXLX : XL ≤ X := fun y hy => ⟨hy.1.1, hy.2⟩
  have hrX : r ∈ X := ⟨ι.r_T, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hXLX
  have hk1 : k ≠ 1 := by
    intro h1
    rw [h1, mul_one] at hk
    have heq := Subgroup.eq_of_le_of_card_ge hXLX hk.le
    have : r ∈ XL := by rw [heq]; exact hrX
    exact ι.r_notL this.1.2
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hk
    exact (Nat.card_pos (α := ↥X)).ne' hk
  calc 2 ^ 7 = 64 * 2 := by norm_num
    _ ≤ Nat.card ↥XL * k := Nat.mul_le_mul hXL64 (by omega)
    _ = Nat.card ↥X := hk.symm

end Inv

end L14333

end CFSG.Quasithin.H13
