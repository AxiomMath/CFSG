module

public import CFSG.Quasithin.Vol2.Ch12Sec7L5zq

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.S127.L715.Set714

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.ASInputs S127 S127.L715 S127.L716
  G31 CFSG.LargeExtraspecial Module QuadraticMap
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {t z : G}
  (s : Set714 G T L V t z)
include s

theorem exists_U_of_R1
    (h1222 : Stmt12_2_2) (hU : autOn (U714 T L V z) V = autOn (R1 T L V) V) {r : G}
    (hr : r ∈ R1 T L V) : ∃ u ∈ U714 T L V z, ∀ x ∈ V, r * x * r⁻¹ = u * x * u⁻¹ := by
  have hRN : R1 T L V ≤ Subgroup.normalizer (V : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (s.P1_le_normalizer_V h1222)
  have := s.isMulCommutative_V h1222
  have hmem : conjAct V ⟨r, hRN hr⟩ ∈ autOn (U714 T L V z) V := by
    rw [hU]
    exact S127.Mod.conjAct_mem_autOn hr (hRN hr)
  obtain ⟨u, huN, huU, hur⟩ := S127.Mod.mem_autOn'.1 hmem
  refine ⟨u, huU, fun x hx => ?_⟩
  have h1 := congrArg (fun φ : MulAut ↥V => ((φ ⟨x, hx⟩ : ↥V) : G)) hur
  simp only [S127.Mod.conjAct_val] at h1
  exact h1.symm

theorem comm_R1_mem
    (h1222 : Stmt12_2_2) (hU : autOn (U714 T L V z) V = autOn (R1 T L V) V) {r : G}
    (hr : r ∈ R1 T L V) {x : G} (hx : x ∈ V ⊓ s.Qz h1222) :
    r * x * r⁻¹ * x⁻¹ ∈ Subgroup.zpowers z := by
  obtain ⟨u, hu, hux⟩ := s.exists_U_of_R1 h1222 hU hr
  rw [hux x hx.1]
  have e : u * x * u⁻¹ * x⁻¹ = (x * u * x⁻¹ * u⁻¹)⁻¹ := by group
  rw [e]
  exact Subgroup.inv_mem _ (hx.2.2 u hu)

theorem L1_conj_mem (h1222 : Stmt12_2_2) {l : G}
    (hl : l ∈ L1 T L V) {x : G} (hx : x ∈ V ⊓ s.Qz h1222) : l * x * l⁻¹ ∈ V ⊓ s.Qz h1222 := by
  have hlL : l ∈ L := (oTwoUpper_le _).trans inf_le_left hl
  have hlH : l ∈ H714 T L V z := (le_sup_left.trans le_sup_right : L1 T L V ≤ _) hl
  exact ⟨(Subgroup.mem_normalizer_iff.mp (S127.Mod.L_le_normalizer s.setting.hyp hlL) x).mp hx.1,
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_cTil _ _ hlH) x).mp hx.2⟩

theorem T_conj_mem (h1222 : Stmt12_2_2) {t₀ : G} (ht : t₀ ∈ T) {x : G}
    (hx : x ∈ V ⊓ s.Qz h1222) :
    t₀ * x * t₀⁻¹ ∈ V ⊓ s.Qz h1222 :=
  ⟨(Subgroup.mem_normalizer_iff.mp (S127.Mod.T_le_normalizer h1222 s.setting.hyp ht) x).mp hx.1,
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_cTil _ _ (T_le_H ht)) x).mp hx.2⟩

end CFSG.Quasithin.H13.S127.L715.Set714

namespace CFSG.Quasithin.H13.S127.L715.Set714.N3

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.ASInputs S127 S127.L715 S127.L716
  G31 CFSG.LargeExtraspecial Module QuadraticMap
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {t z : G}
  {s : Set714 G T L V t z} {h1222 : Stmt12_2_2} (hn : s.N3 h1222)
include hn

theorem mem_QG {x : G}
    (hx : x ∈ s.Qz h1222) : x ∈ hn.setting.QG := by
  rw [hn.setting_QG]
  exact hx

noncomputable abbrev rhoQ
    (g : hn.setting.M) : hn.setting.Qt ≃ₗ[ZMod 2] hn.setting.Qt :=
  ((hn.setting.ρ g : hn.setting.O) : hn.setting.Qt ≃ₗ[ZMod 2] hn.setting.Qt)

theorem rhoQ_cl
    (g : hn.setting.M) {x : G} (hx : x ∈ s.Qz h1222) :
    hn.rhoQ g (hn.setting.cl x) = hn.setting.cl ((g : G) * x * (g : G)⁻¹) :=
  hn.setting.ρ_cl g (hn.mem_QG hx)

theorem rhoQ_mul
    (a b : hn.setting.M) (w : hn.setting.Qt) :
    hn.rhoQ (a * b) w = hn.rhoQ a (hn.rhoQ b w) := by
  simp only [rhoQ, map_mul, Subgroup.coe_mul, LinearEquiv.mul_apply]

theorem rhoQ_pow
    (a : hn.setting.M) (k : ℕ) :
    hn.rhoQ (a ^ k) = hn.rhoQ a ^ k := by
  simp only [rhoQ, map_pow, SubgroupClass.coe_pow]

theorem rhoQ_one
    (w : hn.setting.Qt) : hn.rhoQ 1 w = w := by
  simp only [rhoQ, map_one, OneMemClass.coe_one]
  rfl

theorem cl_eq_of_mem_zpowers
    {a x : G} (ha : a ∈ s.Qz h1222) (hx : x ∈ s.Qz h1222)
    (h : a * x⁻¹ ∈ Subgroup.zpowers z) : hn.setting.cl a = hn.setting.cl x := by
  have hzx : z * x = x * z := s.z_comm_H h1222 (s.Qz_le_H h1222 hx)
  rw [hn.setting.cl_eq_cl_iff (hn.mem_QG ha) (hn.mem_QG hx)]
  show x = a ∨ x = a * z
  rcases (Setting.mem_zpowers_iff_of_mul_self s.z_mul_z).mp h with h1 | h1
  · exact Or.inl (mul_inv_eq_one.mp h1).symm
  · right
    have ha' : a = z * x := by rw [← h1]; group
    calc x = x * (z * z) := by rw [s.z_mul_z, mul_one]
      _ = z * x * z := by rw [← mul_assoc, ← hzx]
      _ = a * z := by rw [ha']

theorem mul_inv_mem_of_cl_eq
    {a x : G} (ha : a ∈ s.Qz h1222) (hx : x ∈ s.Qz h1222)
    (h : hn.setting.cl a = hn.setting.cl x) : a * x⁻¹ ∈ Subgroup.zpowers z := by
  rcases (hn.setting.cl_eq_cl_iff (hn.mem_QG ha) (hn.mem_QG hx)).mp h with rfl | rfl
  · rw [mul_inv_cancel]
    exact Subgroup.one_mem _
  · show a * (a * z)⁻¹ ∈ _
    have haGz : a ∈ Subgroup.centralizer ({z} : Set G) := s.H_le_Gz h1222 (s.Qz_le_H h1222 ha)
    rw [show a * (a * z)⁻¹ = a * z⁻¹ * a⁻¹ by group,
      conj_eq_of_mem_zpowers (Subgroup.inv_mem _ (Subgroup.mem_zpowers z)) haGz]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers z)

theorem finrank_clSub
    {X : Subgroup G} (hXQ : X ≤ s.Qz h1222) (hzX : z ∈ X) {k : ℕ}
    (hX : Nat.card ↥X = 2 ^ (k + 1)) : finrank (ZMod 2) (hn.setting.clSub X) = k := by
  have hle : X ≤ hn.setting.QG := by rw [hn.setting_QG]; exact hXQ
  have h1 := hn.setting.card_clPre (hn.setting.clSub X)
  rw [hn.setting.clPre_clSub hle hzX, hX, hn.setting.card_submodule, pow_succ] at h1
  have h2 : 2 ^ k = 2 ^ finrank (ZMod 2) (hn.setting.clSub X) := by omega
  exact (Nat.pow_right_injective le_rfl h2).symm

theorem finrank_W1 :
    finrank (ZMod 2) (hn.setting.clSub (U714 T L V z)) = 3 :=
  hn.finrank_clSub (s.U_le_Qz hn) s.z_mem_U (by rw [hn.card_U]; norm_num)

theorem finrank_A0 :
    finrank (ZMod 2) (hn.setting.clSub (V ⊓ s.Qz h1222)) = 3 :=
  hn.finrank_clSub inf_le_right ⟨s.z_mem_V, s.U_le_Qz hn s.z_mem_U⟩ (by rw [hn.card_VQ]; norm_num)

theorem q_W1 :
    ∀ w ∈ hn.setting.clSub (U714 T L V z), hn.setting.q w = 0 := by
  intro w hw
  obtain ⟨x, hx, hxQ, rfl⟩ := hn.setting.mem_clSub_iff.mp hw
  rw [hn.setting.q_cl_eq_zero_iff hxQ]
  exact hn.sq_U x hx

theorem q_A0 :
    ∀ a ∈ hn.setting.clSub (V ⊓ s.Qz h1222), hn.setting.q a = 0 := by
  intro a ha
  obtain ⟨x, hx, hxQ, rfl⟩ := hn.setting.mem_clSub_iff.mp ha
  rw [hn.setting.q_cl_eq_zero_iff hxQ]
  exact S127.sq_eq_one_of_mem s.setting.hyp.hyp hx.1

theorem rhoQ_W1
    (m : hn.setting.M) :
    ∀ w ∈ hn.setting.clSub (U714 T L V z), hn.rhoQ m w ∈ hn.setting.clSub (U714 T L V z) := by
  intro w hw
  obtain ⟨x, hx, hxQ, rfl⟩ := hn.setting.mem_clSub_iff.mp hw
  rw [hn.rhoQ_cl m (s.U_le_Qz hn hx)]
  have hmx : (m : G) * x * (m : G)⁻¹ ∈ U714 T L V z :=
    (Subgroup.mem_normalizer_iff.mp (hn.Gz_le_normalizer_U m.2) x).mp hx
  exact hn.setting.cl_mem_clSub hmx (hn.mem_QG (s.U_le_Qz hn hmx))

theorem cl_v_ne {v : G}
    (hv : v ∈ V1 T L V) (hvz : v ∉ Subgroup.zpowers z) : hn.setting.cl v ≠ 0 := by
  have hvQ : v ∈ s.Qz h1222 := s.U_le_Qz hn (le_conjClosure _ _ hv)
  rw [Ne, hn.setting.cl_eq_zero_iff (hn.mem_QG hvQ)]
  rintro (h | h)
  · exact hvz (h ▸ Subgroup.one_mem _)
  · exact hvz (h ▸ Subgroup.mem_zpowers z)

theorem cl_V1 {v : G}
    (hv : v ∈ V1 T L V) (hvz : v ∉ Subgroup.zpowers z) {x : G} (hx : x ∈ V1 T L V) :
    hn.setting.cl x = 0 ∨ hn.setting.cl x = hn.setting.cl v := by
  have hxQ : x ∈ s.Qz h1222 := s.U_le_Qz hn (le_conjClosure _ _ hx)
  have hvQ : v ∈ s.Qz h1222 := s.U_le_Qz hn (le_conjClosure _ _ hv)
  by_cases hxz : x ∈ Subgroup.zpowers z
  · left
    rw [hn.setting.cl_eq_zero_iff (hn.mem_QG hxQ)]
    exact (Setting.mem_zpowers_iff_of_mul_self s.z_mul_z).mp hxz
  · right
    have hzV1 : Subgroup.zpowers z ≤ V1 T L V := Subgroup.zpowers_le_of_mem s.mem
    have hcard : Nat.card ↥(V1 T L V) ≤ 2 * Nat.card ↥(V1 T L V ⊓ Subgroup.zpowers z) := by
      rw [inf_of_le_right hzV1, Nat.card_zpowers, s.orderOf_z, s.card_V1 h1222]
    have h := mul_mem_of_card_le hcard x hx v hv hxz hvz
    refine hn.cl_eq_of_mem_zpowers hxQ hvQ ?_
    have hxGz : x ∈ Subgroup.centralizer ({z} : Set G) :=
      s.V_le_Gz h1222 ((inf_le_left : V1 T L V ≤ V) hx)
    rw [show x * v⁻¹ = x * (x⁻¹ * v)⁻¹ * x⁻¹ by group,
      conj_eq_of_mem_zpowers (Subgroup.inv_mem _ h) hxGz]
    exact Subgroup.inv_mem _ h

theorem A0_inf_W1 {v : G}
    (hv : v ∈ V1 T L V) (hvz : v ∉ Subgroup.zpowers z) {w : hn.setting.Qt}
    (hwA : w ∈ hn.setting.clSub (V ⊓ s.Qz h1222)) (hwU : w ∈ hn.setting.clSub (U714 T L V z)) :
    w = 0 ∨ w = hn.setting.cl v := by
  obtain ⟨x, hx, hxQ, rfl⟩ := hn.setting.mem_clSub_iff.mp hwA
  obtain ⟨u, hu, huQ, hux⟩ := hn.setting.mem_clSub_iff.mp hwU
  have hxU : x ∈ U714 T L V z := by
    rcases (hn.setting.cl_eq_cl_iff huQ hxQ).mp hux with rfl | rfl
    · exact hu
    · exact Subgroup.mul_mem _ hu s.z_mem_U
  exact hn.cl_V1 hv hvz (hn.UV ⟨hxU, hx.1⟩)

theorem rhoQ_L1
    (hU : autOn (U714 T L V z) V = autOn (R1 T L V) V) {y : G} (hyL1 : y ∈ L1 T L V)
    (hy3 : orderOf y = 3) {l : G} (hl : l ∈ L1 T L V) :
    ∃ k : ℕ, ∀ a ∈ hn.setting.clSub (V ⊓ s.Qz h1222),
      hn.rhoQ ⟨l, s.L1_le_Gz hl⟩ a = ((hn.rhoQ ⟨y, s.L1_le_Gz hyL1⟩) ^ k) a := by
  have hN2 : IsPGroup 2 ↥(pCoreOf 2 (L1 T L V)) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  obtain ⟨k, hk⟩ := S127.Mod.idx3_coset hN2 (s.relIndex_L1 h1222) hyL1 hy3 hl
  refine ⟨k, fun a ha => ?_⟩
  obtain ⟨x, hx, hxQ, rfl⟩ := hn.setting.mem_clSub_iff.mp ha
  have hxQz : x ∈ s.Qz h1222 := hx.2
  have hyk : y ^ k ∈ L1 T L V := Subgroup.pow_mem _ hyL1 k
  have hx' : y ^ k * x * (y ^ k)⁻¹ ∈ V ⊓ s.Qz h1222 := s.L1_conj_mem h1222 hyk hx
  rw [← hn.rhoQ_pow, hn.rhoQ_cl _ hxQz, hn.rhoQ_cl _ hxQz]
  set r := l * (y ^ k)⁻¹ with hr
  have hrR : r ∈ R1 T L V := s.pCoreOf_L1_le_R1 hk
  have hc := s.comm_R1_mem h1222 hU hrR hx'
  have hl' : l = r * y ^ k := by rw [hr]; group
  have e : l * x * l⁻¹ = r * (y ^ k * x * (y ^ k)⁻¹) * r⁻¹ := by rw [hl']; group
  show hn.setting.cl (l * x * l⁻¹) = hn.setting.cl (((y ^ k : G)) * x * (y ^ k : G)⁻¹)
  rw [e]
  refine hn.cl_eq_of_mem_zpowers ?_ hx'.2 hc
  rw [← e]
  exact s.L1_conj_mem h1222 hl hx |>.2

section Y

variable {y : G}
  (hyL1 : y ∈ L1 T L V) (hy3 : orderOf y = 3)

noncomputable abbrev Yt : Submodule (ZMod 2) hn.setting.Qt :=
  (hn.setting.clSub (V ⊓ s.Qz h1222)).map
    ((hn.rhoQ ⟨y, s.L1_le_Gz hyL1⟩).toLinearMap - LinearMap.id)

include hyL1

theorem rhoQ_y_A0 {a : hn.setting.Qt} (ha : a ∈ hn.setting.clSub (V ⊓ s.Qz h1222)) :
    hn.rhoQ ⟨y, s.L1_le_Gz hyL1⟩ a ∈ hn.setting.clSub (V ⊓ s.Qz h1222) := by
  obtain ⟨x, hx, hxQ, rfl⟩ := hn.setting.mem_clSub_iff.mp ha
  rw [hn.rhoQ_cl _ hx.2]
  have hx' := s.L1_conj_mem h1222 hyL1 hx
  exact hn.setting.cl_mem_clSub hx' (hn.mem_QG hx'.2)

theorem rhoQ_y_v {v : G} (hv : v ∈ V1 T L V) :
    hn.rhoQ ⟨y, s.L1_le_Gz hyL1⟩ (hn.setting.cl v) = hn.setting.cl v := by
  have hvQ : v ∈ s.Qz h1222 := s.U_le_Qz hn (le_conjClosure _ _ hv)
  rw [hn.rhoQ_cl _ hvQ]
  have hyC : y ∈ Subgroup.centralizer (V1 T L V : Set G) :=
    ((oTwoUpper_le _).trans inf_le_right) hyL1
  show hn.setting.cl (y * v * y⁻¹) = hn.setting.cl v
  rw [(Subgroup.mem_centralizer_iff.mp hyC v hv).symm, mul_inv_cancel_right]

include hy3 in
theorem rhoQ_y_cube (w : hn.setting.Qt) :
    hn.rhoQ ⟨y, s.L1_le_Gz hyL1⟩ (hn.rhoQ ⟨y, s.L1_le_Gz hyL1⟩
      (hn.rhoQ ⟨y, s.L1_le_Gz hyL1⟩ w)) = w := by
  rw [← hn.rhoQ_mul, ← hn.rhoQ_mul]
  have h3 : (⟨y, s.L1_le_Gz hyL1⟩ * ⟨y, s.L1_le_Gz hyL1⟩ * ⟨y, s.L1_le_Gz hyL1⟩ :
      hn.setting.M) = 1 := by
    apply Subtype.ext
    show y * y * y = 1
    have hy3' : y ^ 3 = 1 := by rw [← hy3]; exact pow_orderOf_eq_one y
    rw [← hy3', pow_succ, pow_two]
  rw [h3, hn.rhoQ_one]

include hy3 in
theorem fix_y {v : G} (hv : v ∈ V1 T L V) (hvz : v ∉ Subgroup.zpowers z) {a : hn.setting.Qt}
    (ha : a ∈ hn.setting.clSub (V ⊓ s.Qz h1222))
    (hfix : hn.rhoQ ⟨y, s.L1_le_Gz hyL1⟩ a = a) : a = 0 ∨ a = hn.setting.cl v := by
  obtain ⟨x, hx, hxQ, rfl⟩ := hn.setting.mem_clSub_iff.mp ha
  rw [hn.rhoQ_cl _ hx.2] at hfix
  have hx' := s.L1_conj_mem h1222 hyL1 hx
  have hmem : y * x * y⁻¹ * x⁻¹ ∈ V1 T L V :=
    Subgroup.zpowers_le_of_mem s.mem (hn.mul_inv_mem_of_cl_eq hx'.2 hx.2 hfix)
  have hxV1 := s.fpf h1222 hyL1 hy3 x hx.1 hmem
  exact hn.cl_V1 hv hvz hxV1

theorem Yt_le_A0 : hn.Yt hyL1 ≤ hn.setting.clSub (V ⊓ s.Qz h1222) := by
  rintro _ ⟨a, ha, rfl⟩
  exact Submodule.sub_mem _ (hn.rhoQ_y_A0 hyL1 ha) ha

include hy3 in
theorem cl_v_not_mem_Yt {v : G} (hv : v ∈ V1 T L V) (hvz : v ∉ Subgroup.zpowers z) :
    hn.setting.cl v ∉ hn.Yt hyL1 := by
  rintro ⟨a, ha, hav⟩
  set ρy := hn.rhoQ ⟨y, s.L1_le_Gz hyL1⟩ with hρy
  have h0 : ρy a - a = hn.setting.cl v := hav
  have hfv := hn.rhoQ_y_v hyL1 hv
  have h1 : ρy (ρy a) - ρy a = hn.setting.cl v := by
    rw [← map_sub, h0, hfv]
  have h2 : ρy (ρy (ρy a)) - ρy (ρy a) = hn.setting.cl v := by
    rw [← map_sub, h1, hfv]
  rw [hn.rhoQ_y_cube hyL1 hy3] at h2
  have h3 : (ρy a - a) + (ρy (ρy a) - ρy a) + (a - ρy (ρy a)) = 0 := by abel
  rw [h0, h1, h2] at h3
  have h4 : hn.setting.cl v + hn.setting.cl v = 0 :=
    CFSG.RankThree.OrthogonalInvolutions.add_self_vec (ZMod 2) _
  rw [h4, zero_add] at h3
  exact hn.cl_v_ne hv hvz h3

include hy3 in
theorem finrank_Yt {v : G} (hv : v ∈ V1 T L V) (hvz : v ∉ Subgroup.zpowers z) :
    finrank (ZMod 2) (hn.Yt hyL1) = 2 := by
  set A0 := hn.setting.clSub (V ⊓ s.Qz h1222) with hA0
  set f := (hn.rhoQ ⟨y, s.L1_le_Gz hyL1⟩).toLinearMap - LinearMap.id with hf
  have hvA : hn.setting.cl v ∈ A0 := by
    have hvQ : v ∈ s.Qz h1222 := s.U_le_Qz hn (le_conjClosure _ _ hv)
    exact hn.setting.cl_mem_clSub ⟨(inf_le_left : V1 T L V ≤ V) hv, hvQ⟩ (hn.mem_QG hvQ)
  have hrn := LinearMap.finrank_range_add_finrank_ker (f.domRestrict A0)
  rw [LinearMap.range_domRestrict, hn.finrank_A0] at hrn
  have hker : LinearMap.ker (f.domRestrict A0) =
      Submodule.span (ZMod 2) {(⟨hn.setting.cl v, hvA⟩ : ↥A0)} := by
    apply le_antisymm
    · intro a ha
      rw [LinearMap.mem_ker, LinearMap.domRestrict_apply, hf, LinearMap.sub_apply,
        LinearEquiv.coe_toLinearMap, LinearMap.id_apply, sub_eq_zero] at ha
      rcases hn.fix_y hyL1 hy3 hv hvz a.2 ha with h | h
      · rw [show a = 0 from Subtype.ext h]
        exact Submodule.zero_mem _
      · rw [show a = ⟨hn.setting.cl v, hvA⟩ from Subtype.ext h]
        exact Submodule.mem_span_singleton_self _
    · rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker, LinearMap.domRestrict_apply,
        hf, LinearMap.sub_apply, LinearEquiv.coe_toLinearMap, LinearMap.id_apply, sub_eq_zero]
      exact hn.rhoQ_y_v hyL1 hv
  have hne : (⟨hn.setting.cl v, hvA⟩ : ↥A0) ≠ 0 := fun h =>
    hn.cl_v_ne hv hvz (congrArg Subtype.val h)
  rw [hker, finrank_span_singleton hne] at hrn
  show finrank (ZMod 2) (A0.map f) = 2
  omega

include hy3 in
theorem disjoint_Yt_W1 {v : G} (hv : v ∈ V1 T L V) (hvz : v ∉ Subgroup.zpowers z) :
    Disjoint (hn.Yt hyL1) (hn.setting.clSub (U714 T L V z)) := by
  rw [Submodule.disjoint_def]
  intro w hwY hwU
  rcases hn.A0_inf_W1 hv hvz (hn.Yt_le_A0 hyL1 hwY) hwU with h | h
  · exact h
  · exact absurd (h ▸ hwY) (hn.cl_v_not_mem_Yt hyL1 hy3 hv hvz)

end Y

theorem rhoQ_T_A0 {t₀ : G}
    (ht : t₀ ∈ T) {a : hn.setting.Qt} (ha : a ∈ hn.setting.clSub (V ⊓ s.Qz h1222)) :
    hn.rhoQ ⟨t₀, s.le_cent ht⟩ a ∈ hn.setting.clSub (V ⊓ s.Qz h1222) := by
  obtain ⟨x, hx, hxQ, rfl⟩ := hn.setting.mem_clSub_iff.mp ha
  rw [hn.rhoQ_cl _ hx.2]
  have hx' := s.T_conj_mem h1222 ht hx
  exact hn.setting.cl_mem_clSub hx' (hn.mem_QG hx'.2)

section T

variable {y : G}
  (hyL1 : y ∈ L1 T L V) (hy3 : orderOf y = 3)
include hyL1 hy3

theorem rhoQ_T_Yt (hU : autOn (U714 T L V z) V = autOn (R1 T L V) V) {v : G}
    (hv : v ∈ V1 T L V) (hvz : v ∉ Subgroup.zpowers z) {t₀ : G} (ht : t₀ ∈ T)
    {b : hn.setting.Qt} (hb : b ∈ hn.Yt hyL1) : hn.rhoQ ⟨t₀, s.le_cent ht⟩ b ∈ hn.Yt hyL1 := by
  have hy := s.setting.hyp.hyp
  obtain ⟨a, ha, rfl⟩ := hb
  set ρy := hn.rhoQ ⟨y, s.L1_le_Gz hyL1⟩ with hρy
  set ρt := hn.rhoQ ⟨t₀, s.le_cent ht⟩ with hρt
  have hTL1 : T ≤ Subgroup.normalizer (L1 T L V : Set G) :=
    T_le_normalizer_L1 hy.normalizes (s.T_le_normalizer_V1 h1222)
  have hl : t₀ * y * t₀⁻¹ ∈ L1 T L V := (Subgroup.mem_normalizer_iff.mp (hTL1 ht) y).mp hyL1
  obtain ⟨k, hk⟩ := hn.rhoQ_L1 hU hyL1 hy3 hl
  have hlt : ∀ w, hn.rhoQ ⟨t₀ * y * t₀⁻¹, s.L1_le_Gz hl⟩ (ρt w) = ρt (ρy w) := by
    intro w
    have e : (⟨t₀ * y * t₀⁻¹, s.L1_le_Gz hl⟩ * ⟨t₀, s.le_cent ht⟩ : hn.setting.M) =
        ⟨t₀, s.le_cent ht⟩ * ⟨y, s.L1_le_Gz hyL1⟩ :=
      Subtype.ext (by show t₀ * y * t₀⁻¹ * t₀ = t₀ * y; group)
    rw [← hn.rhoQ_mul, e, hn.rhoQ_mul]
  have h3 : ρy ^ 3 = 1 := by
    rw [hρy, ← hn.rhoQ_pow]
    have hy3' : (⟨y, s.L1_le_Gz hyL1⟩ : hn.setting.M) ^ 3 = 1 :=
      Subtype.ext (by
        show y ^ 3 = 1
        rw [← hy3, pow_orderOf_eq_one])
    rw [hy3']
    exact LinearEquiv.ext fun w => hn.rhoQ_one w
  have hpow : ρy ^ k = ρy ^ (k % 3) := by
    conv_lhs => rw [← Nat.mod_add_div k 3, pow_add, pow_mul, h3, one_pow, mul_one]
  set a' := ρt a with ha'
  have ha'A : a' ∈ hn.setting.clSub (V ⊓ s.Qz h1222) := hn.rhoQ_T_A0 ht ha
  have hρta : ρt (ρy a) = (ρy ^ (k % 3)) a' := by
    rw [← hlt, hk a' ha'A, hpow]
  have hgoal : ρt (((ρy.toLinearMap - LinearMap.id :
      hn.setting.Qt →ₗ[ZMod 2] hn.setting.Qt)) a) = (ρy ^ (k % 3)) a' - a' := by
    rw [LinearMap.sub_apply, LinearEquiv.coe_toLinearMap, LinearMap.id_apply, map_sub, hρta]
  rw [hgoal]
  rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h0 | h1 | h2
  ·
    exfalso
    have hfixA : ∀ c ∈ hn.setting.clSub (V ⊓ s.Qz h1222), ρy c = c := by
      intro c hc
      have hc' := hn.rhoQ_T_A0 ht hc
      have := hk _ hc'
      rw [hpow, h0, pow_zero, LinearEquiv.coe_one, id_eq, hlt] at this
      exact ρt.injective this
    have hcard := hn.setting.card_submodule (hn.setting.clSub (V ⊓ s.Qz h1222))
    rw [hn.finrank_A0] at hcard
    have hle : Nat.card ↥(hn.setting.clSub (V ⊓ s.Qz h1222)) ≤ 2 := by
      classical
      refine (Nat.card_le_card_of_injective (fun c : ↥(hn.setting.clSub (V ⊓ s.Qz h1222)) =>
        (decide ((c : hn.setting.Qt) = 0) : Bool)) ?_).trans (by simp)
      intro c₁ c₂ hc
      rcases hn.fix_y hyL1 hy3 hv hvz c₁.2 (hfixA _ c₁.2) with h₁ | h₁ <;>
        rcases hn.fix_y hyL1 hy3 hv hvz c₂.2 (hfixA _ c₂.2) with h₂ | h₂
      · exact Subtype.ext (h₁.trans h₂.symm)
      · simp [h₁, h₂, hn.cl_v_ne hv hvz] at hc
      · simp [h₁, h₂, hn.cl_v_ne hv hvz] at hc
      · exact Subtype.ext (h₁.trans h₂.symm)
    omega
  · rw [h1, pow_one]
    exact ⟨a', ha'A, by
      rw [LinearMap.sub_apply, LinearEquiv.coe_toLinearMap, LinearMap.id_apply]⟩
  · rw [h2, pow_two, LinearEquiv.mul_apply]
    refine ⟨ρy a' + a', Submodule.add_mem _ (hn.rhoQ_y_A0 hyL1 ha'A) ha'A, ?_⟩
    rw [LinearMap.sub_apply, LinearEquiv.coe_toLinearMap, LinearMap.id_apply, map_add]
    abel

end T

end CFSG.Quasithin.H13.S127.L715.Set714.N3
