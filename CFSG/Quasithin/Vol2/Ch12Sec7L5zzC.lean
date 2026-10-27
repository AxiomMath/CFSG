module

public import CFSG.Quasithin.Vol2.Ch12Sec7L5zzB
public import CFSG.Quasithin.Vol2.Ch12Sec7L5zy
import all CFSG.Quasithin.Vol2.Ch12Sec7ModData
import all CFSG.Quasithin.Vol2.Ch12Sec7ModData2
import all CFSG.Quasithin.Vol2.Ch12Sec7L5zz
public import CFSG.Quasithin.Vol2.Ch12Sec7L5zzA

public section

namespace CFSG.Quasithin.H13.S127

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.LieType.BorelTits

variable {G : Type} [Group G]

@[expose] def WZ (T L : Subgroup G) : Subgroup G where
  carrier := {w | w ∈ pCoreOf 2 (L ⊔ T) ∧ w ∈ Subgroup.centralizer (pCoreOf 2 (L ⊔ T) : Set G) ∧
    w ∈ Subgroup.centralizer (XOf L : Set G) ∧ w * w = 1}
  mul_mem' := by
    rintro a b ⟨haQ, haZ, haX, ha2⟩ ⟨hbQ, hbZ, hbX, hb2⟩
    refine ⟨Subgroup.mul_mem _ haQ hbQ, Subgroup.mul_mem _ haZ hbZ, Subgroup.mul_mem _ haX hbX, ?_⟩
    have hab : b * a = a * b := Subgroup.mem_centralizer_iff.mp haZ b hbQ
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * a * (b * b) := by rw [hab]; group
      _ = 1 := by rw [ha2, hb2, one_mul]
  one_mem' := ⟨Subgroup.one_mem _, Subgroup.one_mem _, Subgroup.one_mem _, mul_one 1⟩
  inv_mem' := by
    rintro a ⟨haQ, haZ, haX, ha2⟩
    have e : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    rw [e]
    exact ⟨haQ, haZ, haX, ha2⟩

theorem WZ_comm {T L : Subgroup G} {a b : G} (ha : a ∈ WZ T L) (hb : b ∈ WZ T L) :
    a * b = b * a :=
  (Subgroup.mem_centralizer_iff.mp hb.2.1 a ha.1)

instance (T L : Subgroup G) : IsMulCommutative ↥(WZ T L) :=
  ⟨⟨fun a b => Subtype.ext (WZ_comm a.2 b.2)⟩⟩

theorem act4_lt : ∀ (f : Fin 6 → Fin 6) (m : ℕ), Mod.act4 f m < 16 := by
  have hex : ∀ a : Fin 6, Mod.ex a < 2 ^ 4 := by decide
  have hx : ∀ a b : ℕ, a < 2 ^ 4 → b < 2 ^ 4 → a ^^^ b < 2 ^ 4 :=
    fun a b ha hb => Nat.xor_lt_two_pow ha hb
  have hi : ∀ (c : Bool) (a b : Fin 6), (if c then Mod.ex a ^^^ Mod.ex b else 0) < 2 ^ 4 := by
    intro c a b
    cases c
    · exact Nat.two_pow_pos 4
    · exact hx _ _ (hex a) (hex b)
  intro f m
  exact hx _ _ (hx _ _ (hx _ _ (hi _ _ _) (hi _ _ _)) (hi _ _ _)) (hi _ _ _)

end CFSG.Quasithin.H13.S127

namespace CFSG.Quasithin.H13.S127.Mod

theorem i2_mem_e8 : i2 ∈ e8 := by decide

@[expose] def u23 : B6 := ⟨1, 3, 4, 12, 21, 63⟩

theorem u23_mem_e8 : u23 ∈ e8 := by decide

@[expose] def rot6 : Mc := ⟨32, 12, 21⟩

theorem rot6_inGm : rot6.Valid ∧ inGm rot6 = true := by decide

theorem permFn_i2 : ∀ i : Fin 6, permFn i2 i = Equiv.swap 0 1 i := by decide

theorem permFn_u23 : ∀ i : Fin 6, permFn u23 i = Equiv.swap 2 3 i := by decide

theorem permFn_rot : ∀ i : Fin 6, permFn (rot6.toB6.comp i2) i = finRotate 6 i := by decide

end CFSG.Quasithin.H13.S127.Mod

namespace CFSG.Quasithin.H13.S127.L715.Set714

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.LieType.BorelTits S127 S127.Mod
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {t z : G} (s : Set714 G T L V t z)
include s

theorem LT_le_normalizer_V (h1222 : Stmt12_2_2) : L ⊔ T ≤ Subgroup.normalizer (V : Set G) :=
  sup_le (S127.Mod.L_le_normalizer s.setting.hyp)
    (S127.Mod.T_le_normalizer h1222 s.setting.hyp)

theorem LT_le_normalizer_L : L ⊔ T ≤ Subgroup.normalizer (L : Set G) :=
  sup_le Subgroup.le_normalizer s.setting.hyp.hyp.normalizes

theorem LT_le_normalizer_WZ (h1222 : Stmt12_2_2) :
    L ⊔ T ≤ Subgroup.normalizer (WZ T L : Set G) := by
  intro g hg
  have hgQ : g ∈ Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) :=
    le_normalizer_pCoreOf 2 (L ⊔ T) hg
  have hgX : g ∈ Subgroup.normalizer (XOf L : Set G) :=
    S127.Mod.normalizer_XOf h1222 s.setting.hyp (s.LT_le_normalizer_L hg)
      (s.LT_le_normalizer_V h1222 hg)
  refine Subgroup.mem_normalizer_fintype fun w hw => ?_
  obtain ⟨hwQ, hwZ, hwX, hw2⟩ := hw
  refine ⟨(Subgroup.mem_normalizer_iff.mp hgQ w).mp hwQ, S127.conj_mem_centralizer hgQ hwZ,
    S127.conj_mem_centralizer hgX hwX, ?_⟩
  calc g * w * g⁻¹ * (g * w * g⁻¹) = g * (w * w) * g⁻¹ := by group
    _ = 1 := by rw [hw2, mul_one, mul_inv_cancel]

theorem WZ_le_T : WZ T L ≤ T := fun _ hw => S127.Mod.Q_le_T s.setting.hyp hw.1

theorem eq_one_of_mem_WZ
    [IsMulCommutative ↥V] (h1222 : Stmt12_2_2) {C : Coding ↥V} (hC : Std C T L) {w : G}
    (hwW : w ∈ WZ T L) (hwV : w ∈ V) : w = 1 := by
  have h := s.setting.hyp
  obtain ⟨y, hyX, hyN, -, -, hy1⟩ := s.exists_yX h1222 hC
  obtain ⟨-, -, -, -, -, hXfix⟩ := setup1271_of h1222 G T L V h
  have hyC : y ∉ Subgroup.centralizer (V : Set G) := by
    intro hyc
    apply hy1
    rw [(conjAct_eq_one' hyN).2 hyc, C.cB_one]
  have hm : w ∈ V ⊓ Subgroup.centralizer ({y} : Set G) :=
    ⟨hwV, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hwW.2.2.1 y hyX).symm⟩
  rw [hXfix y hyX hyC] at hm
  exact (Subgroup.mem_bot).1 hm

theorem quad_WZ
    [IsMulCommutative ↥V] (h1222 : Stmt12_2_2) {C : Coding ↥V} (hC : Std C T L) {u u' w : G}
    (hu : u ∈ U714 T L V z) (hu' : u' ∈ U714 T L V z) (hw : w ∈ WZ T L) :
    u' * (u * w * u⁻¹ * w⁻¹) * u'⁻¹ = u * w * u⁻¹ * w⁻¹ := by
  have hUT := s.U_le_T h1222
  have hWN := s.LT_le_normalizer_WZ h1222
  have huLT : u ∈ L ⊔ T := Subgroup.mem_sup_right (hUT.1 hu)
  have hu'LT : u' ∈ L ⊔ T := Subgroup.mem_sup_right (hUT.1 hu')
  set x := u * w * u⁻¹ * w⁻¹ with hx
  have hxW : x ∈ WZ T L :=
    Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hWN huLT) w).mp hw)
      (Subgroup.inv_mem _ hw)
  have hxU : x ∈ U714 T L V z := by
    have hwT : w ∈ T := s.WZ_le_T hw
    have h1 : w * u⁻¹ * w⁻¹ ∈ U714 T L V z :=
      (Subgroup.mem_normalizer_iff.mp (hUT.2 hwT) u⁻¹).mp (Subgroup.inv_mem _ hu)
    have e : x = u * (w * u⁻¹ * w⁻¹) := by rw [hx]; group
    rw [e]
    exact Subgroup.mul_mem _ hu h1
  have hc := s.comm_mem_U h1222 hu' hxU
  have hcV : u' * x * u'⁻¹ * x⁻¹ ∈ V := (Subgroup.zpowers_le_of_mem s.z_mem_V) hc
  have hcW : u' * x * u'⁻¹ * x⁻¹ ∈ WZ T L :=
    Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hWN hu'LT) x).mp hxW)
      (Subgroup.inv_mem _ hxW)
  have h1 := s.eq_one_of_mem_WZ h1222 hC hcW hcV
  exact mul_inv_eq_one.mp h1

theorem eq_one_of_cent (h712 : Lemma12_7_12) {w : G} (hw : w ∈ WZ T L)
    (hc : ∀ l ∈ L, l * w * l⁻¹ = w) : w = 1 := by
  have h := h712 G T L V t s.setting
  have hm : w ∈ T ⊓ Subgroup.centralizer (L : Set G) := by
    refine ⟨s.WZ_le_T hw, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
    calc l * w = l * w * l⁻¹ * l := by group
      _ = w * l := by rw [hc l hl]
  rw [h] at hm
  exact (Subgroup.mem_bot).1 hm

theorem code_LT
    [IsMulCommutative ↥V] (h1222 : Stmt12_2_2) {C : Coding ↥V} (hC : Std C T L)
    (g : ↥(L ⊔ T)) :
    (IsLin (C.cB (conjAct V (Subgroup.inclusion (s.LT_le_normalizer_V h1222) g))) ∨
      IsSemi (C.cB (conjAct V (Subgroup.inclusion (s.LT_le_normalizer_V h1222) g)))) ∧
      ∀ c ∈ oVecL,
        (C.cB (conjAct V (Subgroup.inclusion (s.LT_le_normalizer_V h1222) g))).app c ∈ oVecL := by
  have h := s.setting.hyp
  have hLTM : L ⊔ T ≤ h.hyp.MV := sup_le (S127.Mod.L_le_MV h) (S127.Mod.T_le_MV h1222 h)
  have hm : conjAct V (Subgroup.inclusion (s.LT_le_normalizer_V h1222) g) ∈ h.hyp.MVbar :=
    conjAct_mem_autOn (hLTM g.2) _
  obtain ⟨-, hO, hlin, hsemi⟩ := MVbar_code h hC.1 hm
  refine ⟨?_, hO⟩
  by_cases hL : conjAct V (Subgroup.inclusion (s.LT_le_normalizer_V h1222) g) ∈ autOn L V
  · exact Or.inl (hlin.1 hL)
  · exact Or.inr (hsemi hL)

@[expose] noncomputable def piLT
    [IsMulCommutative ↥V] (h1222 : Stmt12_2_2) {C : Coding ↥V} (hC : Std C T L) :
    ↥(L ⊔ T) →* Equiv.Perm (Fin 6) :=
  piHom C (s.LT_le_normalizer_V h1222) (s.code_LT h1222 hC)

theorem piLT_apply
    [IsMulCommutative ↥V] (h1222 : Stmt12_2_2) {C : Coding ↥V} (hC : Std C T L) {g : G}
    (hg : g ∈ L ⊔ T) (hgN : g ∈ Subgroup.normalizer (V : Set G)) (i : Fin 6) :
    s.piLT h1222 hC ⟨g, hg⟩ i = permFn (C.cB (conjAct V ⟨g, hgN⟩)) i := rfl

theorem exists_U_code
    [IsMulCommutative ↥V] (h1222 : Stmt12_2_2) {C : Coding ↥V} (hC : Std C T L)
    (hne : s.setting.hyp.hyp.MVbar ≠ autOn L V) (hT : ∀ a ∈ autOn T V, C.cB a ∈ s0p)
    (hbig : ∀ a, a ∈ autOn (U714 T L V z) V ↔ C.cB a ∈ e8) {c : B6} (hc : c ∈ e8) :
    ∃ u ∈ U714 T L V z, ∃ huN : u ∈ Subgroup.normalizer (V : Set G),
      C.cB (conjAct V ⟨u, huN⟩) = c := by
  obtain ⟨a, -, ha⟩ := T_surj h1222 s.setting.hyp hC hne hT c (e8_sub_s0p c hc)
  obtain ⟨u, huN, huU, rfl⟩ := mem_autOn'.1 ((hbig a).2 (ha ▸ hc))
  exact ⟨u, huU, huN, ha⟩

theorem piLT_surjective
    [IsMulCommutative ↥V] (h1222 : Stmt12_2_2) {C : Coding ↥V} (hC : Std C T L)
    (hne : s.setting.hyp.hyp.MVbar ≠ autOn L V) (hT : ∀ a ∈ autOn T V, C.cB a ∈ s0p)
    (hbig : ∀ a, a ∈ autOn (U714 T L V z) V ↔ C.cB a ∈ e8) :
    Function.Surjective (s.piLT h1222 hC) := by
  have h := s.setting.hyp
  have hUT := (s.U_le_T h1222).1
  obtain ⟨u, huU, huN, hu⟩ := s.exists_U_code h1222 hC hne hT hbig i2_mem_e8
  have huLT : u ∈ L ⊔ T := Subgroup.mem_sup_right (hUT huU)
  have hrot : rot6.toB6 ∈ gm6 := gm6_of_gmList rot6_inGm
  obtain ⟨a, ha⟩ := hC.1.2 _ hrot
  obtain ⟨l, hlN, hlL, rfl⟩ := mem_autOn'.1 ((hC.1.1 a).2 (ha ▸ hrot))
  have hlLT : l ∈ L ⊔ T := Subgroup.mem_sup_left hlL
  have h1 : s.piLT h1222 hC ⟨u, huLT⟩ = Equiv.swap 0 ((finRotate 6) 0) := by
    refine Equiv.ext fun i => ?_
    rw [s.piLT_apply h1222 hC huLT huN, hu, permFn_i2]
    rfl
  have h2 : s.piLT h1222 hC (⟨l, hlLT⟩ * ⟨u, huLT⟩) = finRotate 6 := by
    refine Equiv.ext fun i => ?_
    have hm : l * u ∈ Subgroup.normalizer (V : Set G) := Subgroup.mul_mem _ hlN huN
    have e : (⟨l * u, hm⟩ : ↥(Subgroup.normalizer (V : Set G))) = ⟨l, hlN⟩ * ⟨u, huN⟩ := rfl
    show s.piLT h1222 hC ⟨l * u, Subgroup.mul_mem _ hlLT huLT⟩ i = _
    rw [s.piLT_apply h1222 hC _ hm, e, map_mul, C.cB_mul, ha, hu, permFn_rot]
  have htop := Equiv.Perm.closure_cycle_adjacent_swap (isCycle_finRotate (n := 4))
    support_finRotate (0 : Fin 6)
  intro σ
  have hσ : σ ∈ (s.piLT h1222 hC).range := by
    have hle : Subgroup.closure ({finRotate 6, Equiv.swap 0 ((finRotate 6) 0)} :
        Set (Equiv.Perm (Fin 6))) ≤ (s.piLT h1222 hC).range := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact ⟨_, h2⟩
      · exact ⟨_, h1⟩
    exact hle (htop ▸ Subgroup.mem_top σ)
  exact hσ

theorem exists_pow_of_piLT_eq_one
    [IsMulCommutative ↥V] (h1222 : Stmt12_2_2) {C : Coding ↥V}
    (hC : Std C T L) {y : G} (hyL : y ∈ L) (hyN : y ∈ Subgroup.normalizer (V : Set G))
    (hyz : C.cB (conjAct V ⟨y, hyN⟩) ∈ zs6) (hy1 : C.cB (conjAct V ⟨y, hyN⟩) ≠ B6.id)
    {g : ↥(L ⊔ T)} (hg : s.piLT h1222 hC g = 1) :
    ∃ j : ℕ, (y ^ j)⁻¹ * g ∈ pCoreOf 2 (L ⊔ T) := by
  have h := s.setting.hyp
  have hgN : (g : G) ∈ Subgroup.normalizer (V : Set G) := s.LT_le_normalizer_V h1222 g.2
  have hLTM : L ⊔ T ≤ h.hyp.MV := sup_le (S127.Mod.L_le_MV h) (S127.Mod.T_le_MV h1222 h)
  have hnm : C.cB (conjAct V ⟨g, hgN⟩) ∈ nm6 :=
    (MVbar_code h hC.1 (conjAct_mem_autOn (hLTM g.2) hgN)).1
  have hfix : ∀ i : Fin 6, permFn (C.cB (conjAct V ⟨g, hgN⟩)) i = i := fun i => by
    have := congrArg (fun σ : Equiv.Perm (Fin 6) => σ i) hg
    simpa [s.piLT_apply h1222 hC g.2 hgN] using this
  have hgz := cert54_ker _ hnm hfix
  have hpow : ∀ j : ℕ, ∃ hj : y ^ j ∈ Subgroup.normalizer (V : Set G),
      conjAct V ⟨y ^ j, hj⟩ = (conjAct V ⟨y, hyN⟩) ^ j := fun j =>
    ⟨Subgroup.pow_mem _ hyN j, by rw [← map_pow]; rfl⟩
  have key : ∃ j : ℕ, conjAct V ⟨g, hgN⟩ = (conjAct V ⟨y, hyN⟩) ^ j := by
    rcases zs6_pow_of_ne _ hgz _ hyz hy1 with h0 | h1 | h2
    · exact ⟨0, by rw [pow_zero]; exact C.cB_eq_one.1 h0⟩
    · exact ⟨1, by rw [pow_one]; exact C.cB_injective h1⟩
    · exact ⟨2, C.cB_injective (by rw [h2, pow_two, C.cB_mul])⟩
  obtain ⟨j, hj⟩ := key
  refine ⟨j, S127.inf_centralizer_le_Q h1222 h ⟨?_, ?_⟩⟩
  · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left (L.pow_mem hyL j))) g.2
  · show (y ^ j)⁻¹ * g ∈ Subgroup.centralizer (V : Set G)
    obtain ⟨hjN, hje⟩ := hpow j
    have hm : (y ^ j)⁻¹ * g ∈ Subgroup.normalizer (V : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hjN) hgN
    rw [← conjAct_eq_one' hm]
    have e : (⟨(y ^ j)⁻¹ * g, hm⟩ : ↥(Subgroup.normalizer (V : Set G))) =
        (⟨y ^ j, hjN⟩)⁻¹ * ⟨g, hgN⟩ := rfl
    rw [e, map_mul, map_inv, hje, hj, inv_mul_cancel]

@[expose] noncomputable def actW (h1222 : Stmt12_2_2) : ↥(L ⊔ T) →* MulAut ↥(WZ T L) :=
  (conjAct (WZ T L)).comp (Subgroup.inclusion (s.LT_le_normalizer_WZ h1222))

theorem actW_apply (h1222 : Stmt12_2_2) (g : ↥(L ⊔ T)) (w : ↥(WZ T L)) :
    ((s.actW h1222 g w : ↥(WZ T L)) : G) = g * w * (g : G)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe (WZ T L) _ w

theorem ker_piLT_le
    [IsMulCommutative ↥V] (h1222 : Stmt12_2_2) {C : Coding ↥V}
    (hC : Std C T L) : (s.piLT h1222 hC).ker ≤ (s.actW h1222).ker := by
  obtain ⟨y, hyX, hyN, -, hyz, hy1⟩ := s.exists_yX h1222 hC
  have hyL : y ∈ L := S127.L5.XOf_le L hyX
  intro g hg
  rw [MonoidHom.mem_ker] at hg ⊢
  obtain ⟨j, hj⟩ := s.exists_pow_of_piLT_eq_one h1222 hC hyL hyN hyz hy1 hg
  refine MulEquiv.ext fun w => Subtype.ext ?_
  rw [s.actW_apply, MulAut.one_apply]
  obtain ⟨-, hwZ, hwX, -⟩ := w.2
  have hyw : y ^ j * (w : G) = w * y ^ j :=
    (Commute.pow_left (Subgroup.mem_centralizer_iff.mp hwX y hyX) j).eq
  obtain ⟨q, hq⟩ : ∃ q, q = (y ^ j)⁻¹ * (g : G) := ⟨_, rfl⟩
  have hqw : q * (w : G) = w * q := Subgroup.mem_centralizer_iff.mp hwZ q (hq ▸ hj)
  have e : (g : G) = y ^ j * q := by rw [hq]; group
  rw [e]
  calc y ^ j * q * w * (y ^ j * q)⁻¹ = y ^ j * (q * w) * q⁻¹ * (y ^ j)⁻¹ := by group
    _ = y ^ j * w * (y ^ j)⁻¹ := by rw [hqw]; group
    _ = w := by rw [hyw]; group

@[expose] noncomputable def rhoW
    [IsMulCommutative ↥V] (h1222 : Stmt12_2_2) {C : Coding ↥V}
    (hC : Std C T L) (hne : s.setting.hyp.hyp.MVbar ≠ autOn L V)
    (hT : ∀ a ∈ autOn T V, C.cB a ∈ s0p)
    (hbig : ∀ a, a ∈ autOn (U714 T L V z) V ↔ C.cB a ∈ e8) :
    Equiv.Perm (Fin 6) →* MulAut ↥(WZ T L) :=
  (s.piLT h1222 hC).liftOfRightInverse (Function.surjInv (s.piLT_surjective h1222 hC hne hT hbig))
    (Function.rightInverse_surjInv _) ⟨s.actW h1222, s.ker_piLT_le h1222 hC⟩

theorem rhoW_piLT
    [IsMulCommutative ↥V] (h1222 : Stmt12_2_2) {C : Coding ↥V}
    (hC : Std C T L) (hne : s.setting.hyp.hyp.MVbar ≠ autOn L V)
    (hT : ∀ a ∈ autOn T V, C.cB a ∈ s0p)
    (hbig : ∀ a, a ∈ autOn (U714 T L V z) V ↔ C.cB a ∈ e8) (g : ↥(L ⊔ T)) :
    s.rhoW h1222 hC hne hT hbig (s.piLT h1222 hC g) = s.actW h1222 g :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ g

theorem exists_theta
    [IsMulCommutative ↥V] (h1222 : Stmt12_2_2)
    (h712 : Lemma12_7_12) {C : Coding ↥V} (hC : Std C T L)
    (hne : s.setting.hyp.hyp.MVbar ≠ autOn L V) (hT : ∀ a ∈ autOn T V, C.cB a ∈ s0p)
    (hbig : ∀ a, a ∈ autOn (U714 T L V z) V ↔ C.cB a ∈ e8) (hW1 : ∃ w ∈ WZ T L, w ≠ 1) :
    ∃ Θ : ℕ → G, Θ 0 = 1 ∧ (∀ m m', Θ (m ^^^ m') = Θ m * Θ m') ∧
      (∀ m < 16, Θ m = 1 → m = 0) ∧ (∀ m, Θ m ∈ WZ T L) ∧
      ∀ g, g ∈ L ⊔ T → ∀ (hgN : g ∈ Subgroup.normalizer (V : Set G)) (m : ℕ),
        g * Θ m * g⁻¹ = Θ (act4 (permFn (C.cB (conjAct V ⟨g, hgN⟩))) m) := by
  set ρ := s.rhoW h1222 hC hne hT hbig with hρ
  have hρπ := s.rhoW_piLT h1222 hC hne hT hbig
  have hUT := (s.U_le_T h1222).1
  obtain ⟨u, huU, huN, hu⟩ := s.exists_U_code h1222 hC hne hT hbig i2_mem_e8
  obtain ⟨u', hu'U, hu'N, hu'⟩ := s.exists_U_code h1222 hC hne hT hbig u23_mem_e8
  have huLT : u ∈ L ⊔ T := Subgroup.mem_sup_right (hUT huU)
  have hu'LT : u' ∈ L ⊔ T := Subgroup.mem_sup_right (hUT hu'U)
  have hπu : s.piLT h1222 hC ⟨u, huLT⟩ = Equiv.swap 0 1 :=
    Equiv.ext fun i => by rw [s.piLT_apply h1222 hC huLT huN, hu, permFn_i2]
  have hπu' : s.piLT h1222 hC ⟨u', hu'LT⟩ = Equiv.swap 2 3 :=
    Equiv.ext fun i => by rw [s.piLT_apply h1222 hC hu'LT hu'N, hu', permFn_u23]
  have hW : ∀ w : ↥(WZ T L), w * w = 1 := fun w => Subtype.ext w.2.2.2.2
  have hQ : ∀ w, ρ (Equiv.swap 0 1) (ρ (Equiv.swap 2 3) w * w⁻¹) = ρ (Equiv.swap 2 3) w * w⁻¹ := by
    intro w
    rw [← hπu, ← hπu', hρπ, hρπ]
    apply Subtype.ext
    rw [s.actW_apply, Subgroup.coe_mul, Subgroup.coe_inv, s.actW_apply]
    exact s.quad_WZ h1222 hC hu'U huU w.2
  have hF : ∀ w, (∀ σ, ρ σ w = w) → w = 1 := by
    intro w hw
    apply Subtype.ext
    refine s.eq_one_of_cent h712 w.2 fun l hl => ?_
    have := hw (s.piLT h1222 hC ⟨l, Subgroup.mem_sup_left hl⟩)
    rw [hρπ] at this
    have h2 := congrArg Subtype.val this
    rwa [s.actW_apply] at h2
  obtain ⟨w, hwW, hw1⟩ := hW1
  have hN : ∃ w : ↥(WZ T L), w ≠ 1 := ⟨⟨w, hwW⟩, fun h1 => hw1 (congrArg Subtype.val h1)⟩
  obtain ⟨Θ, h0, hxor, hinj, hequiv⟩ := FourA.exists_theta hW hQ hF hN
  refine ⟨fun m => Θ m, congrArg Subtype.val h0, fun m m' => congrArg Subtype.val (hxor m m'),
    fun m hm h1 => hinj m hm (Subtype.ext h1), fun m => (Θ m).2, ?_⟩
  intro g hg hgN m
  have h1 := congrArg Subtype.val (hequiv (s.piLT h1222 hC ⟨g, hg⟩) m)
  rw [hρπ, s.actW_apply] at h1
  exact h1

end CFSG.Quasithin.H13.S127.L715.Set714
