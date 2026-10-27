module

public import CFSG.Quasithin.Vol2.Ch12Sec7L5zx
import all CFSG.Quasithin.Vol2.Ch12Sec7ModData
import all CFSG.Quasithin.Vol2.Ch12Sec7ModData2

public section

namespace CFSG.Quasithin.H13.S127.L715.Set714

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S127 S127.Mod
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {t z : G} (s : Set714 G T L V t z)
include s

theorem exists_yX
    [IsMulCommutative ↥V] (h1222 : Stmt12_2_2) {C : Coding ↥V} (hC : Std C T L) :
    ∃ y ∈ XOf L, ∃ hyN : y ∈ Subgroup.normalizer (V : Set G), y ^ 3 = 1 ∧
      C.cB (conjAct V ⟨y, hyN⟩) ∈ zs6 ∧ C.cB (conjAct V ⟨y, hyN⟩) ≠ B6.id := by
  have h := s.setting.hyp
  have hXN : XOf L ≤ Subgroup.normalizer (V : Set G) :=
    (S127.L5.XOf_le L).trans (S127.Mod.L_le_normalizer h)
  obtain ⟨a, ha⟩ := hC.1.2 w6 (zs6_sub_gm6 _ w6_mem_zs6)
  have haX : a ∈ autOn (XOf L) V := (mem_autOn_XOf h1222 h hC.1 a).2 (ha ▸ w6_mem_zs6)
  obtain ⟨x, hxN, hxX, rfl⟩ := mem_autOn'.1 haX
  obtain ⟨-, -, hLC, -, -, -⟩ := setup1271_of h1222 G T L V h
  have hK2 : IsPGroup 2 ↥(XOf L ⊓ Subgroup.centralizer (V : Set G)) := by
    have hle : XOf L ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 L := by
      rw [← hLC]
      exact inf_le_inf_right _ (S127.L5.XOf_le L)
    exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le hle
  have h3 : (conjAct V ⟨x, hxN⟩) ^ 3 = 1 := by
    apply C.cB_injective
    rw [C.cB_pow, ha, C.cB_one, w6_pow3]
  obtain ⟨y, hyX, hy3, e, he⟩ := S127.Mod.exists_lift_three hXN hK2 hxX h3
  refine ⟨y, hyX, hXN hyX, hy3, ?_⟩
  set b := conjAct V ⟨y, hXN hyX⟩ with hb
  have hb3 : b ^ 3 = 1 := by
    rw [hb, ← map_pow]
    have : (⟨y, hXN hyX⟩ : ↥(Subgroup.normalizer (V : Set G))) ^ 3 = 1 :=
      Subtype.ext (by simpa using hy3)
    rw [this, map_one]
  have hbpow : b ^ e = b ^ (e % 3) := by
    conv_lhs => rw [← Nat.div_add_mod e 3, pow_add, pow_mul, hb3, one_pow, one_mul]
  have hx : conjAct V ⟨x, hxN⟩ = b ^ (e % 3) := by rw [he, hbpow]
  have hcases : e % 3 = 0 ∨ e % 3 = 1 ∨ e % 3 = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · exfalso
    rw [h0, pow_zero] at hx
    have := congrArg C.cB hx
    rw [ha, C.cB_one] at this
    exact w6_ne_id this
  · rw [h1, pow_one] at hx
    rw [← hx, ha]
    exact ⟨w6_mem_zs6, w6_ne_id⟩
  · rw [h2] at hx
    have hb4 : b = (conjAct V ⟨x, hxN⟩) ^ 2 := by
      rw [hx, ← pow_mul]
      calc b = b ^ 3 * b := by rw [hb3, one_mul]
        _ = b ^ 4 := by rw [← pow_succ]
    rw [hb4, C.cB_pow, ha]
    exact ⟨w6_sq_mem_zs6, w6_sq_ne_id⟩

omit [Finite G] s in
theorem norm_eq_one {V : Subgroup G} (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) {y : G}
    (hyN : y ∈ Subgroup.normalizer (V : Set G)) (hy3 : y ^ 3 = 1)
    (hfix : ∀ v ∈ V, y * v * y⁻¹ = v → v = 1) {v : G} (hv : v ∈ V) :
    v * (y * v * y⁻¹) * (y * y * v * (y * y)⁻¹) = 1 := by
  have hm : ∀ w ∈ V, y * w * y⁻¹ ∈ V := fun w hw => (Subgroup.mem_normalizer_iff.mp hyN w).mp hw
  have hv1 := hm v hv
  have hv2 : y * y * v * (y * y)⁻¹ ∈ V := by
    have := hm _ hv1
    have e : y * (y * v * y⁻¹) * y⁻¹ = y * y * v * (y * y)⁻¹ := by group
    rwa [e] at this
  apply hfix _ (V.mul_mem (V.mul_mem hv hv1) hv2)
  have hy3' : y * y * y = 1 := by rw [← hy3, pow_succ, pow_two]
  have hv3 : y * (y * y * v * (y * y)⁻¹) * y⁻¹ = v := by
    have e : y * (y * y * v * (y * y)⁻¹) * y⁻¹ = (y * y * y) * v * (y * y * y)⁻¹ := by group
    rw [e, hy3', one_mul, inv_one, mul_one]
  have e : y * (v * (y * v * y⁻¹) * (y * y * v * (y * y)⁻¹)) * y⁻¹ =
      ((y * v * y⁻¹) * (y * y * v * (y * y)⁻¹)) * (y * (y * y * v * (y * y)⁻¹) * y⁻¹) := by
    group
  rw [e, hv3, hVc _ (V.mul_mem hv1 hv2) _ hv]
  exact (mul_assoc _ _ _).symm

end CFSG.Quasithin.H13.S127.L715.Set714

namespace CFSG.Quasithin.H13.S127.Mod

theorem zs6_pow_of_ne : ∀ a ∈ zs6, ∀ b ∈ zs6, b ≠ B6.id → a = B6.id ∨ a = b ∨ a = b.comp b := by
  decide

end CFSG.Quasithin.H13.S127.Mod

namespace CFSG.Quasithin.H13.S127.L715.Set714

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S127 S127.Mod
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {t z : G} (s : Set714 G T L V t z)
include s

theorem mem_X [IsMulCommutative ↥V]
    (h1222 : Stmt12_2_2) {C : Coding ↥V} (hC : Std C T L) {y : G} (hyL : y ∈ L)
    (hyN : y ∈ Subgroup.normalizer (V : Set G)) (hyz : C.cB (conjAct V ⟨y, hyN⟩) ∈ zs6)
    (hy1 : C.cB (conjAct V ⟨y, hyN⟩) ≠ B6.id) {x : G} (hx : x ∈ XOf L) :
    ∃ j : ℕ, (y ^ j)⁻¹ * x ∈ pCoreOf 2 (L ⊔ T) := by
  have h := s.setting.hyp
  have hxL : x ∈ L := S127.L5.XOf_le L hx
  have hxN : x ∈ Subgroup.normalizer (V : Set G) := S127.Mod.L_le_normalizer h hxL
  have hxz : C.cB (conjAct V ⟨x, hxN⟩) ∈ zs6 :=
    (mem_autOn_XOf h1222 h hC.1 _).1 (conjAct_mem_autOn hx hxN)
  have hpow : ∀ j : ℕ, ∃ hj : y ^ j ∈ Subgroup.normalizer (V : Set G),
      conjAct V ⟨y ^ j, hj⟩ = (conjAct V ⟨y, hyN⟩) ^ j := fun j =>
    ⟨Subgroup.pow_mem _ hyN j, by rw [← map_pow]; rfl⟩
  have key : ∃ j : ℕ, conjAct V ⟨x, hxN⟩ = (conjAct V ⟨y, hyN⟩) ^ j := by
    rcases zs6_pow_of_ne _ hxz _ hyz hy1 with h0 | h1 | h2
    · exact ⟨0, by rw [pow_zero]; exact C.cB_eq_one.1 h0⟩
    · exact ⟨1, by rw [pow_one]; exact C.cB_injective h1⟩
    · exact ⟨2, C.cB_injective (by rw [h2, pow_two, C.cB_mul])⟩
  obtain ⟨j, hj⟩ := key
  refine ⟨j, S127.inf_centralizer_le_Q h1222 h ⟨?_, ?_⟩⟩
  · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left (L.pow_mem hyL j)))
      (Subgroup.mem_sup_left hxL)
  · show (y ^ j)⁻¹ * x ∈ Subgroup.centralizer (V : Set G)
    obtain ⟨hjN, hje⟩ := hpow j
    have hm : (y ^ j)⁻¹ * x ∈ Subgroup.normalizer (V : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hjN) hxN
    rw [← conjAct_eq_one' hm]
    have e : (⟨(y ^ j)⁻¹ * x, hm⟩ : ↥(Subgroup.normalizer (V : Set G))) =
        (⟨y ^ j, hjN⟩)⁻¹ * ⟨x, hxN⟩ := rfl
    rw [e, map_mul, map_inv, hje, hj, inv_mul_cancel]

theorem exists_mul_centralizer
    (h1222 : Stmt12_2_2) {y : G} (hyN : y ∈ Subgroup.normalizer (V : Set G)) (hy3 : y ^ 3 = 1)
    (hfix : ∀ v ∈ V, y * v * y⁻¹ = v → v = 1)
    (hcomm : ∀ q ∈ pCoreOf 2 (L ⊔ T), y * q * y⁻¹ * q⁻¹ ∈ V) {q : G}
    (hq : q ∈ pCoreOf 2 (L ⊔ T)) :
    ∃ v ∈ V, ∃ c ∈ pCoreOf 2 (L ⊔ T), y * c * y⁻¹ = c ∧ q = v * c := by
  have h := s.setting.hyp
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((S127.card_eq_of_1222 h1222 h).1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hV2 : ∀ a ∈ V, a * a = 1 := fun a ha => by
    rw [← pow_two]
    exact S127.sq_eq_one_of_mem h.hyp ha
  set Q := pCoreOf 2 (L ⊔ T)
  have hVQ : V ≤ Q := by
    have hy := h.hyp
    have hVT : V ≤ T := S127.L713.V_le_T h1222 h
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hVT.trans le_sup_right)
      (sup_le (S127.Mod.L_le_normalizer h) (S127.Mod.T_le_normalizer h1222 h))
      (hy.sylow.1.to_le hVT)
  have hvqV : y * q * y⁻¹ * q⁻¹ ∈ V := hcomm q hq
  have hm : ∀ w ∈ V, y * w * y⁻¹ ∈ V := fun w hw => (Subgroup.mem_normalizer_iff.mp hyN w).mp hw
  obtain ⟨vq, hvq⟩ : ∃ vq, vq = y * q * y⁻¹ * q⁻¹ := ⟨_, rfl⟩
  rw [← hvq] at hvqV
  obtain ⟨v', hv'⟩ : ∃ v', v' = y * vq * y⁻¹ := ⟨_, rfl⟩
  have hv'V : v' ∈ V := hv' ▸ hm _ hvqV
  obtain ⟨w₂, hw₂⟩ : ∃ w₂, w₂ = y * y * vq * (y * y)⁻¹ := ⟨_, rfl⟩
  have hw₂V : w₂ ∈ V := by
    have := hm _ hv'V
    have e : y * v' * y⁻¹ = w₂ := by rw [hv', hw₂]; group
    rwa [e] at this
  have hn : vq * v' * w₂ = 1 := by
    rw [hv', hw₂]
    exact norm_eq_one hVc hyN hy3 hfix hvqV
  have h2 : w₂ * vq = v' := by
    have h4 : w₂ * vq * v' = 1 := by
      rw [hVc _ hw₂V _ hvqV, mul_assoc, hVc _ hw₂V _ hv'V, ← mul_assoc]
      exact hn
    calc w₂ * vq = w₂ * vq * v' * v' := by rw [mul_assoc _ v' v', hV2 _ hv'V, mul_one]
      _ = v' := by rw [h4, one_mul]
  refine ⟨v', hv'V, v' * q, Q.mul_mem (hVQ hv'V) hq, ?_, ?_⟩
  · have e1 : y * (v' * q) * y⁻¹ = (y * v' * y⁻¹) * (vq * q) := by rw [hvq]; group
    have e2 : y * v' * y⁻¹ = w₂ := by rw [hv', hw₂]; group
    rw [e1, e2, ← mul_assoc, h2]
  · rw [← mul_assoc, hV2 _ hv'V, one_mul]

theorem pCoreOf_L_le :
    pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) := by
  have h := s.setting.hyp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left)
    (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
      (h.hyp.normalizes.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)

theorem comm_le_or_exists
    [IsMulCommutative ↥V] (h1222 : Stmt12_2_2) {C : Coding ↥V}
    (hC : Std C T L) (hne : s.setting.hyp.hyp.MVbar ≠ autOn L V)
    (hT : ∀ a ∈ autOn T V, C.cB a ∈ s0p)
    (hbig : ∀ a, a ∈ autOn (U714 T L V z) V ↔ C.cB a ∈ e8) :
    ⁅pCoreOf 2 L, L⁆ ≤ V ∨ ∃ w ∈ pCoreOf 2 (L ⊔ T),
      w ∈ Subgroup.centralizer (pCoreOf 2 (L ⊔ T) : Set G) ∧
      w ∈ Subgroup.centralizer (XOf L : Set G) ∧ w ≠ 1 ∧ w * w = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := s.setting.hyp
  set Q := pCoreOf 2 (L ⊔ T) with hQdef
  have hQ2 : IsPGroup 2 ↥Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hQC : Q ≤ Subgroup.centralizer (V : Set G) := S127.Mod.Q_le_centralizer h1222 h
  obtain ⟨y, hyX, hyN, hy3, hyz, hy1⟩ := s.exists_yX h1222 hC
  have hyL : y ∈ L := S127.L5.XOf_le L hyX
  have hcomm := s.comm_y_mem_V h1222 hC hne hT hbig hyL hyN hy3 hyz
  obtain ⟨-, -, -, -, -, hXfix⟩ := setup1271_of h1222 G T L V h
  have hyC : y ∉ Subgroup.centralizer (V : Set G) := by
    intro hyc
    apply hy1
    rw [(conjAct_eq_one' hyN).2 hyc, C.cB_one]
  have hfix : ∀ v ∈ V, y * v * y⁻¹ = v → v = 1 := by
    intro v hv hyv
    have hm : v ∈ V ⊓ Subgroup.centralizer ({y} : Set G) := by
      refine ⟨hv, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc v * y = y * v * y⁻¹ * y := by rw [hyv]
        _ = y * v := by group
    rw [hXfix y hyX hyC] at hm
    exact (Subgroup.mem_bot).1 hm
  by_cases hc : ∀ c ∈ Q, y * c * y⁻¹ = c → c = 1
  · left
    have hQV : Q ≤ V := by
      intro q hq
      obtain ⟨v, hv, c, hcQ, hcy, rfl⟩ := s.exists_mul_centralizer h1222 hyN hy3 hfix hcomm hq
      rw [hc c hcQ hcy, mul_one]
      exact hv
    calc ⁅pCoreOf 2 L, L⁆ ≤ ⁅V, L⁆ :=
          Subgroup.commutator_mono (s.pCoreOf_L_le.trans hQV) le_rfl
      _ ≤ V := S127.Mod.commutator_le_V h L le_rfl
  · right
    push Not at hc
    obtain ⟨c, hcQ, hcy, hc1⟩ := hc
    set C' := Q ⊓ Subgroup.centralizer ({y} : Set G) with hC'
    have hcC' : c ∈ C' := ⟨hcQ, Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc c * y = y * c * y⁻¹ * y := by rw [hcy]
        _ = y * c := by group)⟩
    have hp : IsPGroup 2 ↥C' := hQ2.to_le inf_le_left
    have hnt : Nontrivial ↥C' := ⟨⟨⟨c, hcC'⟩, 1, fun he => hc1 (congrArg Subtype.val he)⟩⟩
    have hcnt := hp.center_nontrivial
    have h2c : 2 ∣ Nat.card ↥(Subgroup.center ↥C') := by
      obtain ⟨k, hk⟩ := (hp.to_subgroup (Subgroup.center _)).exists_card_eq
      have h1 : 1 < Nat.card ↥(Subgroup.center ↥C') := Finite.one_lt_card
      rw [hk] at h1 ⊢
      rcases k with _ | k
      · simp at h1
      · exact dvd_pow_self 2 (Nat.succ_ne_zero k)
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 h2c
    have hwQ : ((w : ↥C') : G) ∈ Q := (w : ↥C').2.1
    have hwy : ((w : ↥C') : G) ∈ Subgroup.centralizer ({y} : Set G) := (w : ↥C').2.2
    have hwZ : ((w : ↥C') : G) ∈ Subgroup.centralizer (Q : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun q hq => ?_
      obtain ⟨v, hv, c', hc'Q, hc'y, rfl⟩ :=
        s.exists_mul_centralizer h1222 hyN hy3 hfix hcomm hq
      have hc'C : c' ∈ C' := ⟨hc'Q, Subgroup.mem_centralizer_singleton_iff.mpr (by
        calc c' * y = y * c' * y⁻¹ * y := by rw [hc'y]
          _ = y * c' := by group)⟩
      have h1 : ((w : ↥C') : G) * c' = c' * (w : ↥C') :=
        (congrArg Subtype.val (Subgroup.mem_center_iff.mp w.2 ⟨c', hc'C⟩)).symm
      have h2 : v * ((w : ↥C') : G) = (w : ↥C') * v :=
        (Subgroup.mem_centralizer_iff.mp (hQC hwQ) v hv)
      calc v * c' * ((w : ↥C') : G) = v * (c' * (w : ↥C')) := by group
        _ = v * ((w : ↥C') * c') := by rw [h1]
        _ = (w : ↥C') * (v * c') := by rw [← mul_assoc, h2, mul_assoc]
    refine ⟨_, hwQ, hwZ, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_, ?_, ?_⟩
    · obtain ⟨j, hj⟩ := s.mem_X h1222 hC hyL hyN hyz hy1 hx
      have hwyj : y ^ j * ((w : ↥C') : G) = (w : ↥C') * y ^ j := by
        have h1 : ((w : ↥C') : G) * y = y * (w : ↥C') :=
          Subgroup.mem_centralizer_singleton_iff.mp hwy
        exact ((Commute.pow_left h1.symm j))
      have hwq := Subgroup.mem_centralizer_iff.mp hwZ _ hj
      have e : x = y ^ j * ((y ^ j)⁻¹ * x) := by group
      rw [e, mul_assoc, hwq, ← mul_assoc, hwyj, mul_assoc]
    · intro h1
      have : w = 1 := Subtype.ext (Subtype.ext h1)
      rw [this, orderOf_one] at hw
      exact absurd hw (by norm_num)
    · have h2 := pow_orderOf_eq_one w
      rw [hw, pow_two] at h2
      have := congrArg (fun a : ↥(Subgroup.center ↥C') => ((a : ↥C') : G)) h2
      simpa using this

end CFSG.Quasithin.H13.S127.L715.Set714
