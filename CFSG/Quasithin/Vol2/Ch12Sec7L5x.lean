module

public import CFSG.Quasithin.Vol2.Ch12Sec7L5w
public import CFSG.Quasithin.Vol2.Ch12Sec7ModR

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S127
open scoped IsMulCommutative

namespace S127.L715

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_L1 {T L V X : Subgroup G} (hXL : X ≤ Subgroup.normalizer (L : Set G))
    (hXV1 : X ≤ Subgroup.normalizer (V1 T L V : Set G)) :
    X ≤ Subgroup.normalizer (L1 T L V : Set G) := by
  refine le_trans ?_ (S127.Mod.normalizer_le_normalizer_oTwoUpper _)
  refine le_normalizer_of_conj_mem fun x hx w hw => ?_
  refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hXL hx) w).mp hw.1, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hv' : x⁻¹ * v * x ∈ V1 T L V := by
    have := (Subgroup.mem_normalizer_iff.mp (hXV1 (X.inv_mem hx)) v).mp hv
    simpa using this
  have hc := Subgroup.mem_centralizer_iff.mp hw.2 _ hv'
  calc v * (x * w * x⁻¹) = x * ((x⁻¹ * v * x) * w) * x⁻¹ := by group
    _ = x * (w * (x⁻¹ * v * x)) * x⁻¹ := by rw [hc]
    _ = x * w * x⁻¹ * v := by group

omit [Finite G] in
@[expose] def cModV {V V₁ X : Subgroup G} (hV : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hXV : X ≤ Subgroup.normalizer (V : Set G)) : Subgroup G where
  carrier := {v | v ∈ V ∧ ∀ x ∈ X, x * v * x⁻¹ * v⁻¹ ∈ V₁}
  one_mem' := ⟨V.one_mem, fun x _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, hax⟩ ⟨hb, hbx⟩
    refine ⟨V.mul_mem ha hb, fun x hx => ?_⟩
    have hxa : x * a * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hXV hx) a).mp ha
    have hxb : x * b * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hXV hx) b).mp hb
    have e : x * (a * b) * x⁻¹ * (a * b)⁻¹ =
        (x * a * x⁻¹ * a⁻¹) * (x * b * x⁻¹ * b⁻¹) := by
      have h1 : a⁻¹ * (x * b * x⁻¹ * b⁻¹) = (x * b * x⁻¹ * b⁻¹) * a⁻¹ :=
        hV _ (V.inv_mem ha) _ (V.mul_mem hxb (V.inv_mem hb))
      calc x * (a * b) * x⁻¹ * (a * b)⁻¹ = (x * a * x⁻¹) * ((x * b * x⁻¹ * b⁻¹) * a⁻¹) := by
            group
        _ = (x * a * x⁻¹) * (a⁻¹ * (x * b * x⁻¹ * b⁻¹)) := by rw [h1]
        _ = (x * a * x⁻¹ * a⁻¹) * (x * b * x⁻¹ * b⁻¹) := by group
    rw [e]
    exact V₁.mul_mem (hax x hx) (hbx x hx)
  inv_mem' := by
    rintro a ⟨ha, hax⟩
    refine ⟨V.inv_mem ha, fun x hx => ?_⟩
    have hxa : x * a * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hXV hx) a).mp ha
    have h1 : (x * a * x⁻¹)⁻¹ * a = a * (x * a * x⁻¹)⁻¹ := hV _ (V.inv_mem hxa) _ ha
    have e : x * a⁻¹ * x⁻¹ * a⁻¹⁻¹ = (x * a * x⁻¹ * a⁻¹)⁻¹ := by
      calc x * a⁻¹ * x⁻¹ * a⁻¹⁻¹ = (x * a * x⁻¹)⁻¹ * a := by group
        _ = a * (x * a * x⁻¹)⁻¹ := h1
        _ = (x * a * x⁻¹ * a⁻¹)⁻¹ := by group
    rw [e]
    exact V₁.inv_mem (hax x hx)

theorem card_modEq_of_fpf {V₁ W : Subgroup G} {y : G} (hy3 : y ^ 3 = 1)
    (hyV₁ : ∀ v ∈ V₁, y * v = v * y) (hV₁W : V₁ ≤ W) (hyW : y ∈ Subgroup.normalizer (W : Set G))
    (hfpf : ∀ w ∈ W, y * w * y⁻¹ * w⁻¹ ∈ V₁ → w ∈ V₁) :
    Nat.card ↥W ≡ Nat.card ↥V₁ [MOD 3] := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype ↥W := Fintype.ofFinite _
  let f : Function.End ↥W := fun w =>
    ⟨y * (w : G) * y⁻¹, (Subgroup.mem_normalizer_iff.mp hyW w).mp w.2⟩
  have hf : f ^ 3 ^ 1 = 1 := by
    funext w
    apply Subtype.ext
    show y * (y * (y * (w : G) * y⁻¹) * y⁻¹) * y⁻¹ = w
    have e : y * (y * (y * (w : G) * y⁻¹) * y⁻¹) * y⁻¹ = y ^ 3 * (w : G) * (y ^ 3)⁻¹ := by
      rw [pow_succ, pow_succ, pow_one]
      group
    rw [e, hy3, one_mul, inv_one, mul_one]
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 3) (n := 1) hf
  have hfix : Fintype.card (Function.fixedPoints f) = Nat.card ↥V₁ := by
    rw [← Nat.card_eq_fintype_card]
    refine Nat.card_congr
      { toFun := fun w => ⟨(w.1 : G), ?_⟩
        invFun := fun v => ⟨⟨v, hV₁W v.2⟩, ?_⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    · apply hfpf _ w.1.2
      have hw : y * (w.1 : G) * y⁻¹ = w.1 := congrArg Subtype.val w.2
      rw [hw, mul_inv_cancel]
      exact V₁.one_mem
    · apply Subtype.ext
      show y * (v : G) * y⁻¹ = v
      rw [hyV₁ v v.2, mul_inv_cancel_right]
  rw [hfix, Fintype.card_eq_nat_card] at hmod
  exact hmod

namespace Set714

variable {T L V : Subgroup G} {t z : G} (s : Set714 G T L V t z)
include s

theorem relIndex_L1
    (h1222 : Stmt12_2_2) : (pCoreOf 2 (L1 T L V)).relIndex (L1 T L V) = 3 := by
  have := (S127.card_eq_of_1222 h1222 s.setting.hyp).1
  have h5 := (S127.Mod.lemma12_7_2_five h1222 s.setting.hyp).2.1
  have hmem : L1 T L V ∈ {I : Subgroup G | I ≤ P1 T L V ∧
      T ≤ Subgroup.normalizer (I : Set G) ∧ oTwoUpper I = I ∧ (pCoreOf 2 I).relIndex I = 3} := by
    rw [h5]
    exact Set.mem_insert _ _
  exact hmem.2.2.2

omit [Finite G] s in
theorem L1_le_P1 : L1 T L V ≤ P1 T L V := fun _ hl =>
  Subgroup.mem_inf.mpr ⟨(le_sup_left : L ≤ L ⊔ pCoreOf 2 (L ⊔ T))
    (((oTwoUpper_le _).trans inf_le_left) hl),
    Subgroup.centralizer_le_normalizer _ (((oTwoUpper_le _).trans inf_le_right) hl)⟩

theorem P1_le_normalizer_L : P1 T L V ≤ Subgroup.normalizer (L : Set G) :=
  inf_le_left.trans (sup_le Subgroup.le_normalizer
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans
      (sup_le Subgroup.le_normalizer s.setting.hyp.hyp.normalizes)))

theorem P1_le_normalizer_V (h1222 : Stmt12_2_2) : P1 T L V ≤ Subgroup.normalizer (V : Set G) :=
  inf_le_left.trans (sup_le (S127.Mod.L_le_normalizer s.setting.hyp)
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans
      (sup_le (S127.Mod.L_le_normalizer s.setting.hyp)
        (S127.Mod.T_le_normalizer h1222 s.setting.hyp))))

theorem pCoreOf_L1_le_R1 : pCoreOf 2 (L1 T L V) ≤ R1 T L V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPL1 : P1 T L V ≤ Subgroup.normalizer (L1 T L V : Set G) :=
    le_normalizer_L1 s.P1_le_normalizer_L inf_le_right
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans L1_le_P1)
    (hPL1.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)

theorem R1_comm_mem
    (h1222 : Stmt12_2_2) {r : G} (hr : r ∈ R1 T L V) {v : G} (hv : v ∈ V) :
    r * v * r⁻¹ * v⁻¹ ∈ V1 T L V := by
  have := (S127.card_eq_of_1222 h1222 s.setting.hyp).1
  obtain ⟨-, -, -, -, hR, -⟩ := (S127.Mod.lemma12_7_2_two h1222 s.setting.hyp)
  by_cases hrC : r ∈ Subgroup.centralizer (V : Set G)
  · rw [(Subgroup.mem_centralizer_iff.mp hrC v hv).symm, mul_inv_cancel_right, mul_inv_cancel]
    exact Subgroup.one_mem _
  · have hc : v * r * v⁻¹ * r⁻¹ ∈ V1 T L V := by
      rw [← hR r hr hrC]
      exact Subgroup.commutator_mem_commutator hv (Subgroup.mem_zpowers r)
    have e : r * v * r⁻¹ * v⁻¹ = (v * r * v⁻¹ * r⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ hc

theorem fpf
    (h1222 : Stmt12_2_2) {y : G} (hyL1 : y ∈ L1 T L V) (hy3 : orderOf y = 3) :
    ∀ v ∈ V, y * v * y⁻¹ * v⁻¹ ∈ V1 T L V → v ∈ V1 T L V := by
  have h := s.setting.hyp
  obtain ⟨hcomm, -, -⟩ := S127.card_eq_of_1222 h1222 h
  have hV : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hLV := S127.Mod.L_le_normalizer h
  have hL1L : L1 T L V ≤ L := (oTwoUpper_le _).trans inf_le_left
  have hL1C : L1 T L V ≤ Subgroup.centralizer (V1 T L V : Set G) :=
    (oTwoUpper_le _).trans inf_le_right
  have hV1V : V1 T L V ≤ V := inf_le_left
  have hy1 : ∀ a ∈ V1 T L V, y * a * y⁻¹ = a := fun a ha => by
    rw [(Subgroup.mem_centralizer_iff.mp (hL1C hyL1) a ha).symm, mul_inv_cancel_right]
  set W₀ := cModV (V₁ := V1 T L V) hV (hL1L.trans hLV) with hW₀
  have hV1W : V1 T L V ≤ W₀ := fun a ha => ⟨hV1V ha, fun l hl => by
    rw [(Subgroup.mem_centralizer_iff.mp (hL1C hl) a ha).symm, mul_inv_cancel_right,
      mul_inv_cancel]
    exact Subgroup.one_mem _⟩
  have hPW : P1 T L V ≤ Subgroup.normalizer (W₀ : Set G) := by
    refine le_normalizer_of_conj_mem fun g hg w hw => ⟨(Subgroup.mem_normalizer_iff.mp
      (s.P1_le_normalizer_V h1222 hg) w).mp hw.1, fun l hl => ?_⟩
    have hPL1 : P1 T L V ≤ Subgroup.normalizer (L1 T L V : Set G) :=
      le_normalizer_L1 s.P1_le_normalizer_L inf_le_right
    have hl' : g⁻¹ * l * g ∈ L1 T L V := by
      have := (Subgroup.mem_normalizer_iff.mp (hPL1 ((P1 T L V).inv_mem hg)) l).mp hl
      simpa using this
    have e : l * (g * w * g⁻¹) * l⁻¹ * (g * w * g⁻¹)⁻¹ =
        g * ((g⁻¹ * l * g) * w * (g⁻¹ * l * g)⁻¹ * w⁻¹) * g⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp
      ((inf_le_right : P1 T L V ≤ Subgroup.normalizer (V1 T L V : Set G)) hg) _).mp (hw.2 _ hl')
  have hW₀V : W₀ ≤ V := fun w hw => hw.1
  have := hcomm
  obtain ⟨hirr, -⟩ := S127.Mod.lemma12_7_2_three h1222 h
  rcases hirr.2.2.2 W₀ hV1W hW₀V hPW with heq | heq
  · intro v hv hyv
    rw [← heq]
    refine ⟨hv, fun l hl => ?_⟩
    have hN2 : IsPGroup 2 ↥(pCoreOf 2 (L1 T L V)) := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
    obtain ⟨k, hk⟩ := S127.Mod.idx3_coset hN2 (s.relIndex_L1 h1222) hyL1 hy3 hl
    have hpow : ∀ n : ℕ, y ^ n * v * (y ^ n)⁻¹ * v⁻¹ ∈ V1 T L V := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have e : y ^ (n + 1) * v * (y ^ (n + 1))⁻¹ * v⁻¹ =
            (y * (y ^ n * v * (y ^ n)⁻¹ * v⁻¹) * y⁻¹) * (y * v * y⁻¹ * v⁻¹) := by
          rw [pow_succ']
          group
        rw [e, hy1 _ ih]
        exact Subgroup.mul_mem _ ih hyv
    set q := l * (y ^ k)⁻¹ with hq
    have hl_eq : l = q * y ^ k := by rw [hq]; group
    have hqR : q ∈ R1 T L V := s.pCoreOf_L1_le_R1 hk
    have hqL1 : q ∈ L1 T L V := (CFSG.LieType.BorelTits.pCoreOf_le 2 _) hk
    set a := y ^ k * v * (y ^ k)⁻¹ * v⁻¹ with ha
    have e : l * v * l⁻¹ * v⁻¹ = (q * a * q⁻¹) * (q * v * q⁻¹ * v⁻¹) := by
      rw [hl_eq, ha]
      group
    rw [e, (Subgroup.mem_centralizer_iff.mp (hL1C hqL1) a (hpow k)).symm, mul_inv_cancel_right]
    exact Subgroup.mul_mem _ (hpow k) (s.R1_comm_mem h1222 hqR hv)
  · exfalso
    have hyC : y ∈ Subgroup.centralizer (V : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hv0 : v ∈ W₀ := heq ▸ hv
      set a := y * v * y⁻¹ * v⁻¹ with ha
      have haV1 : a ∈ V1 T L V := hv0.2 y hyL1
      have ha2 : a * a = 1 := by
        rw [← pow_two]
        exact S127.sq_eq_one_of_mem h.hyp (hV1V haV1)
      have hyv : y * v * y⁻¹ = a * v := by rw [ha]; group
      have h3 : y ^ 3 * v * (y ^ 3)⁻¹ = a * v := by
        have e : y ^ 3 * v * (y ^ 3)⁻¹ = y * (y * (y * v * y⁻¹) * y⁻¹) * y⁻¹ := by
          rw [pow_succ, pow_succ, pow_one]
          group
        rw [e, hyv]
        have e2 : y * (y * (a * v) * y⁻¹) * y⁻¹ =
            (y * (y * a * y⁻¹) * y⁻¹) * (y * (y * v * y⁻¹) * y⁻¹) := by group
        rw [e2, hy1 a haV1, hy1 a haV1, hyv]
        have e3 : y * (a * v) * y⁻¹ = (y * a * y⁻¹) * (y * v * y⁻¹) := by group
        rw [e3, hy1 a haV1, hyv, ← mul_assoc, ← mul_assoc, ha2, one_mul]
      have hy31 : y ^ 3 = 1 := by rw [← hy3]; exact pow_orderOf_eq_one y
      rw [hy31, one_mul, inv_one, mul_one] at h3
      have ha1 : a = 1 := by
        have := congrArg (· * v⁻¹) h3
        simpa using this.symm
      rw [ha] at ha1
      have : y * v * y⁻¹ = v := by
        have := congrArg (· * v) ha1
        simpa using this
      calc v * y = y * v * y⁻¹ * y := by rw [this]
        _ = y * v := by group
    have hyO : y ∈ pCoreOf 2 L := by
      rw [← S127.inf_centralizer_eq_of_1222 h1222 h]
      exact ⟨hL1L hyL1, hyC⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) ⟨y, hyO⟩
    have hdvd : orderOf y ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one (by
      simpa using congrArg Subtype.val hn)
    rw [hy3] at hdvd
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd) (by norm_num)

theorem comm_mem_U
    (h1222 : Stmt12_2_2) {a b : G} (ha : a ∈ U714 T L V z) (hb : b ∈ U714 T L V z) :
    a * b * a⁻¹ * b⁻¹ ∈ Subgroup.zpowers z := by
  have hA := s.almostSpecialHyp h1222
  rw [← s.conjClosure_eq h1222] at ha hb
  have hU := hA.G22_one.2
  have hcc := hA.conjClosure_le_N
  have hmemY : ∀ u (hu : u ∈ conjClosure (V1 T L V) (H714 T L V z)),
      tmk (Subgroup.zpowers z) ⟨u, hcc hu⟩ ∈
        omegaOneCenterOf (tildeOf (Subgroup.zpowers z) (pCoreOf 2 (H714 T L V z))) :=
    fun u hu => (secImg_le_iff.1 hU) ⟨u, hcc hu⟩ hu
  have hyQ := omegaOneCenterOf_le _ (hmemY b hb)
  have hxy := (mem_centralizer_of_mem_omegaOneCenterOf (hmemY a ha) hyQ).symm
  exact commutator_mem_of_secMk_commute hxy

theorem card_V_cTil
    (h1222 : Stmt12_2_2) :
    Nat.card ↥V = 4 * Nat.card ↥(V ⊓ cTil (s.H_le_Gz h1222) (s.H_le_normalizer_U h1222)) ∨
      Nat.card ↥V = 16 * Nat.card ↥(V ⊓ cTil (s.H_le_Gz h1222) (s.H_le_normalizer_U h1222)) := by
  have h := s.setting.hyp
  set W := V ⊓ cTil (s.H_le_Gz h1222) (s.H_le_normalizer_U h1222) with hWdef
  obtain ⟨y, hyL1, hy3⟩ := S127.Mod.idx3_exists (s.relIndex_L1 h1222)
  have hV64 : Nat.card ↥V = 2 ^ 6 := (S127.card_eq_of_1222 h1222 h).2.1
  have := (S127.card_eq_of_1222 h1222 h).1
  have hV14 : Nat.card ↥(V1 T L V) = 4 := (S127.Mod.lemma12_7_2_two h1222 h).1.2
  have hV1V : V1 T L V ≤ V := inf_le_left
  have hL1C : L1 T L V ≤ Subgroup.centralizer (V1 T L V : Set G) :=
    (oTwoUpper_le _).trans inf_le_right
  have hV1W : V1 T L V ≤ W := fun v hv =>
    ⟨hV1V hv, ⟨V_le_H714 T L V z (hV1V hv), fun u hu =>
      s.comm_mem_U h1222 (le_conjClosure _ _ hv) hu⟩⟩
  have hWV : W ≤ V := inf_le_left
  have hWne : ¬ V ≤ W := fun hle => s.not_le_cTil h1222 (hle.trans inf_le_right)
  have hyH : y ∈ H714 T L V z := (le_sup_left.trans le_sup_right : L1 T L V ≤ _) hyL1
  have hyW : y ∈ Subgroup.normalizer (W : Set G) := by
    refine le_normalizer_of_conj_mem (X := Subgroup.zpowers y) (fun x hx w hw => ?_)
      (Subgroup.mem_zpowers y)
    have hxH : x ∈ H714 T L V z := Subgroup.zpowers_le_of_mem hyH hx
    have hxV : x ∈ Subgroup.normalizer (V : Set G) := Subgroup.zpowers_le_of_mem
      ((S127.Mod.L_le_normalizer h) (((oTwoUpper_le _).trans inf_le_left) hyL1)) hx
    exact ⟨(Subgroup.mem_normalizer_iff.mp hxV w).mp hw.1,
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_cTil _ _ hxH) w).mp hw.2⟩
  have hy31 : y ^ 3 = 1 := by rw [← hy3]; exact pow_orderOf_eq_one y
  have hmod := card_modEq_of_fpf hy31
    (fun v hv => (Subgroup.mem_centralizer_iff.mp (hL1C hyL1) v hv).symm) hV1W hyW
    (fun w hw => s.fpf h1222 hyL1 hy3 w (hWV hw))
  rw [hV14] at hmod
  have hd : Nat.card ↥W ∣ 2 ^ 6 := hV64 ▸ Subgroup.card_dvd_of_le hWV
  have h4 : 4 ∣ Nat.card ↥W := hV14 ▸ Subgroup.card_dvd_of_le hV1W
  have hne : Nat.card ↥W ≠ 2 ^ 6 := fun he =>
    hWne (Subgroup.eq_of_le_of_card_ge hWV (by rw [he, hV64])).ge
  obtain ⟨k, hk, hWk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  rw [hV64]
  rw [hWk] at hmod h4 hne ⊢
  interval_cases k <;> simp_all [Nat.ModEq]

end Set714

end S127.L715

end CFSG.Quasithin.H13
