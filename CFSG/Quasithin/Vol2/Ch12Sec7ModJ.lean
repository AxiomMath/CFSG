module

public import CFSG.Quasithin.Vol2.Ch12Sec7ModI
public import CFSG.Quasithin.Vol2.Ch12Sec7ModCert
import all CFSG.Quasithin.Vol2.Ch12Sec7ModData
import all CFSG.Quasithin.Vol2.Ch12Sec7ModData2
public import CFSG.Quasithin.Vol2.Ch12Sec7L23c
public import CFSG.Quasithin.Vol2.Ch12Sec7ModH

public section

namespace CFSG.Quasithin.H13.S127.Mod

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative commutatorElement

theorem p1c_zero : 0 ∈ p1c := by decide

theorem p1c_xor : ∀ a ∈ p1c, ∀ b ∈ p1c, a ^^^ b ∈ p1c := by decide

theorem p1c_nodup : p1c.Nodup := by decide

theorem p1c_lt : ∀ c ∈ p1c, c < 64 := by decide

theorem l2c_zero : 0 ∈ l2c := by decide

theorem l2c_xor : ∀ a ∈ l2c, ∀ b ∈ l2c, a ^^^ b ∈ l2c := by decide

theorem l2c_nodup : l2c.Nodup := by decide

theorem l2c_lt : ∀ c ∈ l2c, c < 64 := by decide

theorem fix_s0 : ∀ c < 64, (∀ B ∈ s0, B.app c = c) ↔ c ∈ p1c := by decide

theorem comm_s0 : ∀ B ∈ s0, ∀ c < 64, c ^^^ B.app c ∈ l2c := by decide

theorem zs6_presv_p1c : ∀ z ∈ zs6, ∀ c ∈ p1c, z.app c ∈ p1c := by decide

theorem zs6_presv_l2c : ∀ z ∈ zs6, ∀ c ∈ l2c, z.app c ∈ l2c := by decide

theorem id_mem_r1 : B6.id ∈ r1 := by decide

theorem r1_closed : ∀ x ∈ r1, ∀ y ∈ r1, x.comp y ∈ r1 := by decide

theorem r1_nodup : r1.Nodup := by decide

theorem r1_sq : ∀ r ∈ r1, r.comp r = B6.id := by decide

theorem r1m_inGm : ∀ A ∈ r1m, A.Valid ∧ inGm A = true ∧ presv p1c A.toB6 = true := by decide

theorem r1_comm : ∀ r ∈ r1, ∀ c < 64, c ^^^ r.app c ∈ p1c := by decide

theorem r1_comm_surj : ∀ r ∈ r1, r ≠ B6.id → ∀ p ∈ p1c, ∃ c < 64, c ^^^ r.app c = p := by
  decide

theorem r1_fix : ∀ c < 64, (∀ r ∈ r1, r.app c = c) ↔ c ∈ p1c := by decide

theorem id_mem_r2 : B6.id ∈ r2 := by decide

theorem r2_closed : ∀ x ∈ r2, ∀ y ∈ r2, x.comp y ∈ r2 := by decide

theorem r2_nodup : r2.Nodup := by decide

theorem r2_sq : ∀ r ∈ r2, r.comp r = B6.id := by decide

theorem r2m_inGm : ∀ A ∈ r2m, A.Valid ∧ inGm A = true ∧ presv l2c A.toB6 = true := by decide

theorem r2_comm : ∀ r ∈ r2, ∀ c < 64, c ^^^ r.app c ∈ l2c := by decide

theorem r2_fix : ∀ r ∈ r2, r ≠ B6.id → ∀ c < 64, (r.app c = c ↔ c ∈ l2c) := by decide

theorem two6_of_sq {r : B6} (h : r.comp r = B6.id) : two6 r = true := by
  have h1 : r.pow 1 = r := B6.comp_id
  have h2 : r.pow 2 = B6.id := by
    show r.comp (r.pow 1) = _
    rw [h1, h]
  have h3 : r.pow 3 = r := by
    show r.comp (r.pow 2) = _
    rw [h2, B6.comp_id]
  have h4 : r.pow 4 = B6.id := by
    show r.comp (r.pow 3) = _
    rw [h3, h]
  simp [two6, h4]

theorem presv_iff (l : List ℕ) (B : B6) : presv l B = true ↔ ∀ c ∈ l, B.app c ∈ l := by
  simp [presv, List.all_eq_true]

theorem toB6_pow {A : Mc} (hA : A.Valid) : ∀ n, (A.pow n).toB6 = A.toB6.pow n
  | 0 => toB6_one
  | n + 1 => by rw [Mc.pow, toB6_mul hA (Mc.pow_valid hA n), toB6_pow hA n]; rfl

theorem gm6_pow60 : ∀ B ∈ gm6, B.pow 60 = B6.id := by
  intro B hB
  obtain ⟨A, hA, rfl⟩ := List.mem_map.1 hB
  have hall := cert_gmList_mem
  obtain ⟨hv, -, hp⟩ := hall A hA
  rw [← toB6_pow hv, hp, toB6_one]

theorem gm6_valid : ∀ B ∈ gm6, B.Valid := by
  intro B hB
  obtain ⟨A, hA, rfl⟩ := List.mem_map.1 hB
  have hall := cert_gmList_mem
  exact toB6_valid (hall A hA).1

section Coding

variable {W : Type} [CommGroup W] [Finite W] (C : Coding W)

omit [Finite W] in
theorem cB_inv_eq {a : MulAut W} (ha : C.cB a ∈ gm6) :
    C.cB a⁻¹ = inv6 (C.cB a) := by
  have h60 : a ^ 60 = 1 := (C.pow_eq_one_iff a 60).2 (gm6_pow60 _ ha)
  have e : a⁻¹ = a ^ 59 := by
    rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ]
    exact h60
  rw [e, C.cB_pow]
  rfl

omit [Finite W] in
theorem pow_four_of_isPGroup {H : Subgroup (MulAut W)}
    (hH : IsPGroup 2 H) {a : MulAut W} (haH : a ∈ H) (ha : C.cB a ∈ gm6) :
    two6 (C.cB a) = true := by
  obtain ⟨k, hk⟩ := hH ⟨a, haH⟩
  have hk' : a ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h60 : a ^ 60 = 1 := (C.pow_eq_one_iff a 60).2 (gm6_pow60 _ ha)
  have hdvd : orderOf a ∣ Nat.gcd (2 ^ k) 60 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one h60)
  have h4 : Nat.gcd (2 ^ k) 60 ∣ 4 := by
    have hg : Nat.gcd (2 ^ k) 60 ∣ 2 ^ k := Nat.gcd_dvd_left _ _
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hg
    rw [hj]
    have hj60 : 2 ^ j ∣ 60 := hj ▸ Nat.gcd_dvd_right _ _
    have : j ≤ 2 := by
      by_contra hj2
      have : 2 ^ 3 ∣ 60 := dvd_trans (pow_dvd_pow 2 (by omega)) hj60
      norm_num at this
    exact pow_dvd_pow 2 this
  have h4' : a ^ 4 = 1 := orderOf_dvd_iff_pow_eq_one.1 (dvd_trans hdvd h4)
  simp only [two6, ← C.cB_pow, h4', C.cB_one, beq_self_eq_true]

end Coding

section Comm

variable {G : Type} [Group G] {V : Subgroup G} [IsMulCommutative ↥V]

omit [IsMulCommutative ↥V] in
theorem commutator_eq_coe {x : G} (hx : x ∈ Subgroup.normalizer (V : Set G)) (v : ↥V) :
    ⁅(v : G), x⁆ = ((v * (conjAct V ⟨x, hx⟩ v)⁻¹ : ↥V) : G) := by
  rw [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, conjAct_val]
  group

theorem cd_commutator (C : Coding ↥V) {x : G} (hx : x ∈ Subgroup.normalizer (V : Set G))
    (v : ↥V) : C.cd (v * (conjAct V ⟨x, hx⟩ v)⁻¹) =
      C.cd v ^^^ (C.cB (conjAct V ⟨x, hx⟩)).app (C.cd v) := by
  rw [C.cd_mul, C.cd_inv, C.cd_apply]

theorem commutator_le_subG (C : Coding ↥V) {l : List ℕ} {h0 : 0 ∈ l}
    {hxor : ∀ a ∈ l, ∀ b ∈ l, a ^^^ b ∈ l} {K : Subgroup G}
    (hK : K ≤ Subgroup.normalizer (V : Set G))
    (h : ∀ x (hx : x ∈ Subgroup.normalizer (V : Set G)), x ∈ K → ∀ c < 64,
      c ^^^ (C.cB (conjAct V ⟨x, hx⟩)).app c ∈ l) :
    ⁅V, K⁆ ≤ C.subG l h0 hxor := by
  rw [Subgroup.commutator_le]
  intro g hg x hxK
  rw [show g = ((⟨g, hg⟩ : ↥V) : G) from rfl, commutator_eq_coe (hK hxK)]
  rw [C.mem_subG, cd_commutator]
  exact h x (hK hxK) hxK _ (C.cd_lt _)

end Comm

section Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

omit [Finite G] in
theorem Std.s0_surj {C : Coding ↥V} (hC : Std C T L) :
    ∀ B ∈ s0, ∃ a ∈ autOn (T ⊓ L) V, C.cB a = B := by
  intro B hB
  obtain ⟨a, ha⟩ := hC.1.2 B (s0_sub_gm6 B hB)
  exact ⟨a, (hC.2 a).2 (ha ▸ hB), ha⟩

omit [IsMulCommutative ↥V] in
theorem TL_le_normalizer (h : Hyp1271 G T L V) :
    T ⊓ L ≤ Subgroup.normalizer (V : Set G) :=
  inf_le_right.trans (L_le_normalizer h)

theorem V1_eq (h : Hyp1271 G T L V) {C : Coding ↥V}
    (hC : Std C T L) : V1 T L V = C.subG p1c p1c_zero p1c_xor := by
  apply C.eq_subG inf_le_left
  intro v
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, ← fix_s0 _ (C.cd_lt v)]
  constructor
  · rintro ⟨-, hv⟩ B hB
    obtain ⟨a, ha, rfl⟩ := hC.s0_surj B hB
    obtain ⟨x, hx, hxK, rfl⟩ := mem_autOn'.1 ha
    exact (commute_iff_code C hx v).1 (hv x hxK)
  · intro hv
    refine ⟨v.2, fun x hxK => ?_⟩
    have hx := TL_le_normalizer h hxK
    exact (commute_iff_code C hx v).2
      (hv _ ((hC.2 _).1 (conjAct_mem_autOn hxK hx)))

theorem V2_eq
    (h : Hyp1271 G T L V) {C : Coding ↥V} (hC : Std C T L) :
    V2 T L V = C.subG l2c l2c_zero l2c_xor := by
  apply le_antisymm
  · apply commutator_le_subG C (TL_le_normalizer h)
    intro x hx hxK c hc
    exact comm_s0 _ ((hC.2 _).1 (conjAct_mem_autOn hxK hx)) c hc
  · intro g hg
    obtain ⟨hgV, hgl⟩ := hg
    obtain ⟨B, hB, c, hc, hcB⟩ := cert_s0span _ hgl
    obtain ⟨a, ha, rfl⟩ := hC.s0_surj B hB
    obtain ⟨x, hx, hxK, rfl⟩ := mem_autOn'.1 ha
    have hc' : c < 64 := List.mem_range.1 hc
    have hmem := Subgroup.commutator_mem_commutator (C.dc c).2 hxK
    rw [commutator_eq_coe hx] at hmem
    have e : (C.dc c * (conjAct V ⟨x, hx⟩ (C.dc c))⁻¹ : ↥V) = ⟨g, hgV⟩ := by
      apply C.cd_injective
      rw [cd_commutator, C.cd_dc c hc', hcB]
    rw [e] at hmem
    exact hmem

theorem cB_mem_zs6_of_mem_XOf
    (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) {C : Coding ↥V} (hC : IdentL C (autOn L V))
    {x : G} (hxX : x ∈ XOf L) (hx : x ∈ Subgroup.normalizer (V : Set G)) :
    C.cB (conjAct V ⟨x, hx⟩) ∈ zs6 := by
  have hxL : x ∈ L := XOf_le L hxX
  have hxm : C.cB (conjAct V ⟨x, hx⟩) ∈ gm6 := (hC.1 _).1 (conjAct_mem_autOn hxL hx)
  refine cert_center _ hxm fun D hD => ?_
  obtain ⟨a, rfl⟩ := hC.2 D hD
  obtain ⟨l, hl, hlL, rfl⟩ := mem_autOn'.1 ((hC.1 a).2 hD)
  rw [← C.cB_mul, ← C.cB_mul]
  congr 1
  have hc := commutator_mem_centralizer_of_mem_XOf h1222 h hxX hlL
  have hN : x * l * x⁻¹ * l⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hl) (Subgroup.inv_mem _ hx))
      (Subgroup.inv_mem _ hl)
  have h1 := (conjAct_eq_one' hN).2 hc
  have e : conjAct V ⟨x * l * x⁻¹ * l⁻¹, hN⟩ =
      conjAct V ⟨x, hx⟩ * conjAct V ⟨l, hl⟩ * (conjAct V ⟨x, hx⟩)⁻¹ * (conjAct V ⟨l, hl⟩)⁻¹ := by
    rw [← map_mul, ← map_inv, ← map_mul, ← map_inv, ← map_mul]
    rfl
  rw [e] at h1
  have := mul_inv_eq_one.1 h1
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this

omit [IsMulCommutative ↥V] in
theorem Q_le_centralizer (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) :
    pCoreOf 2 (L ⊔ T) ≤ Subgroup.centralizer (V : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLV := L_le_normalizer h
  have hTV := T_le_normalizer h1222 h
  set Q := pCoreOf 2 (L ⊔ T) with hQ
  have hQp : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hQV : Q ≤ Subgroup.normalizer (V : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (sup_le hLV hTV)
  have hLQ : L ≤ Subgroup.normalizer (Q : Set G) :=
    le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  set W := V ⊓ Subgroup.centralizer (Q : Set G) with hW
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := by
    apply le_normalizer_of_maps
    intro l hl w hw
    refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 (hLV hl) w).1 hw.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hq' : l⁻¹ * q * l ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.1 (hLQ (L.inv_mem hl)) q).1 hq
      simpa using this
    have hc := Subgroup.mem_centralizer_iff.1 hw.2 _ hq'
    calc q * (l * w * l⁻¹) = l * ((l⁻¹ * q * l) * w) * l⁻¹ := by group
      _ = l * (w * (l⁻¹ * q * l)) * l⁻¹ := by rw [hc]
      _ = l * w * l⁻¹ * q := by group
  have hirr := (modules_g_of_1222 h1222 h).2.2.2.2.2
  obtain ⟨z, hzV, hz1, hzQ⟩ := exists_fixed_of_isPGroup hQp hQV (by
    rw [card_V h1222 h]
    norm_num)
  have hzW : z ∈ W := ⟨hzV, Subgroup.mem_centralizer_iff.2 fun q hq =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hzQ hq))⟩
  rcases hirr.2 W inf_le_left hLW with hbot | htop
  · exact absurd ((Subgroup.mem_bot.1 (hbot ▸ hzW))) hz1
  · intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hvW : v ∈ W := htop ▸ hv
    exact (Subgroup.mem_centralizer_iff.1 hvW.2 q hq).symm

omit [IsMulCommutative ↥V] in
theorem LQ_le_normalizer (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) :
    L ⊔ pCoreOf 2 (L ⊔ T) ≤ Subgroup.normalizer (V : Set G) :=
  sup_le (L_le_normalizer h) ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans
    (sup_le (L_le_normalizer h) (T_le_normalizer h1222 h)))

omit [IsMulCommutative ↥V] in
theorem autOn_LQ (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) :
    autOn (L ⊔ pCoreOf 2 (L ⊔ T)) V = autOn L V := by
  apply le_antisymm _ (A4.autOn_mono le_sup_left)
  intro a ha
  obtain ⟨x, hx, hxK, rfl⟩ := mem_autOn'.1 ha
  have hLQ : L ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) :=
    le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hx' : x ∈ ((L ⊔ pCoreOf 2 (L ⊔ T) : Subgroup G) : Set G) := hxK
  rw [Subgroup.coe_mul_of_left_le_normalizer_right L _ hLQ] at hx'
  obtain ⟨l, hl, q, hq, rfl⟩ := hx'
  have hlN := L_le_normalizer h hl
  have hqN : q ∈ Subgroup.normalizer (V : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans
      (sup_le (L_le_normalizer h) (T_le_normalizer h1222 h)) hq
  have e : conjAct V ⟨l * q, hx⟩ = conjAct V ⟨l, hlN⟩ := by
    rw [conjAct_mul' hlN hqN, (conjAct_eq_one' hqN).2 (Q_le_centralizer h1222 h hq), mul_one]
  rw [e]
  exact conjAct_mem_autOn hl hlN

end Setting

end CFSG.Quasithin.H13.S127.Mod

end
