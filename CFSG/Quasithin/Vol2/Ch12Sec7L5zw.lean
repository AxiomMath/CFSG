module

public import CFSG.Quasithin.Vol2.Ch12Sec7L5zv
public import CFSG.Quasithin.Vol2.Ch12Sec7L5y

public section

namespace CFSG.Quasithin.H13.S127.Mod

@[expose] def wi1 : List ℕ := [0, 5, 11, 14, 17, 20, 26, 31]

theorem wi1_fix : ∀ c ∈ wi1, i1.app c = c := by decide

theorem wi1_comm : ∀ c < 64, i1.app c ^^^ c ∈ wi1 := by decide

theorem wi1_surj : ∀ w ∈ wi1, ∃ c < 64, w = c ^^^ i1.app c := by decide

theorem i1_app_10 : i1.app 10 = 15 := by decide

theorem id_app : ∀ c < 64, B6.id.app c = c := by decide

theorem mem_p1c_10 : 10 ∈ p1c := by decide

end CFSG.Quasithin.H13.S127.Mod

namespace CFSG.Quasithin.H13.S127.L715.Set714

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S127 S127.Mod S127.L716
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {t z : G} (s : Set714 G T L V t z)
include s

abbrev ZU (T L V : Subgroup G) (z : G) : Subgroup G :=
  U714 T L V z ⊓ Subgroup.centralizer (U714 T L V z : Set G)

theorem H_le_normalizer_ZU (h1222 : Stmt12_2_2) :
    H714 T L V z ≤ Subgroup.normalizer (ZU T L V z : Set G) := by
  intro h hh
  have hN := s.H_le_normalizer_U h1222 hh
  refine Subgroup.mem_normalizer_fintype fun x hx => ⟨?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp hN x).mp hx.1
  · refine Subgroup.mem_centralizer_iff.mpr fun u hu => ?_
    have hu' : h⁻¹ * u * h ∈ U714 T L V z := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hN) u).mp hu
      simpa using this
    have hc := Subgroup.mem_centralizer_iff.mp hx.2 _ hu'
    calc u * (h * x * h⁻¹) = h * ((h⁻¹ * u * h) * x) * h⁻¹ := by group
      _ = h * (x * (h⁻¹ * u * h)) * h⁻¹ := by rw [hc]
      _ = h * x * h⁻¹ * u := by group

section Small

variable [IsMulCommutative ↥V] {C : Coding ↥V}

omit [Finite G] s in
theorem code_U
    (hsmall : ∀ a, a ∈ autOn (U714 T L V z) V ↔ C.cB a = B6.id ∨ C.cB a = i1) {u : G}
    (hu : u ∈ U714 T L V z) (huN : u ∈ Subgroup.normalizer (V : Set G)) :
    C.cB (conjAct V ⟨u, huN⟩) = B6.id ∨ C.cB (conjAct V ⟨u, huN⟩) = i1 :=
  (hsmall _).1 (conjAct_mem_autOn hu huN)

omit [IsMulCommutative ↥V] in
theorem U_le_normalizer_V
    (h1222 : Stmt12_2_2) : U714 T L V z ≤ Subgroup.normalizer (V : Set G) :=
  (s.U_le_T h1222).1.trans (S127.Mod.T_le_normalizer h1222 s.setting.hyp)

theorem comm_code
    (h1222 : Stmt12_2_2)
    (hsmall : ∀ a, a ∈ autOn (U714 T L V z) V ↔ C.cB a = B6.id ∨ C.cB a = i1) {u : G}
    (hu : u ∈ U714 T L V z) (v : ↥V) :
    C.cd ⟨u * v * u⁻¹ * v⁻¹, V.mul_mem ((Subgroup.mem_normalizer_iff.1
      (s.U_le_normalizer_V h1222 hu) v).1 v.2) (V.inv_mem v.2)⟩ ∈ wi1 := by
  have huN := s.U_le_normalizer_V h1222 hu
  have e : (⟨u * v * u⁻¹ * v⁻¹, V.mul_mem ((Subgroup.mem_normalizer_iff.1 huN v).1 v.2)
      (V.inv_mem v.2)⟩ : ↥V) = ⟨u * v * u⁻¹, (Subgroup.mem_normalizer_iff.1 huN v).1 v.2⟩ * v⁻¹ :=
    rfl
  rw [e, C.cd_mul, C.cd_inv, cd_conj C huN v]
  rcases code_U hsmall hu huN with h1 | h1
  · rw [h1, id_app _ (C.cd_lt v), Nat.xor_self]
    decide
  · rw [h1]
    exact wi1_comm _ (C.cd_lt v)

theorem conj_eq_of_code
    (h1222 : Stmt12_2_2)
    (hsmall : ∀ a, a ∈ autOn (U714 T L V z) V ↔ C.cB a = B6.id ∨ C.cB a = i1) {u : G}
    (hu : u ∈ U714 T L V z) (w : ↥V) (hw : C.cd w ∈ wi1) : u * w * u⁻¹ = w := by
  have huN := s.U_le_normalizer_V h1222 hu
  have h1 : C.cd ⟨u * w * u⁻¹, (Subgroup.mem_normalizer_iff.1 huN w).1 w.2⟩ = C.cd w := by
    rw [cd_conj C huN w]
    rcases code_U hsmall hu huN with h2 | h2
    · rw [h2, id_app _ (C.cd_lt w)]
    · rw [h2, wi1_fix _ hw]
  exact congrArg Subtype.val (C.cd_injective h1)

theorem mem_U_of_code
    (h1222 : Stmt12_2_2) {u₁ : G} (hu₁ : u₁ ∈ U714 T L V z)
    (hi : C.cB (conjAct V ⟨u₁, s.U_le_normalizer_V h1222 hu₁⟩) = i1) (w : ↥V)
    (hw : C.cd w ∈ wi1) : (w : G) ∈ U714 T L V z := by
  have huN := s.U_le_normalizer_V h1222 hu₁
  obtain ⟨c, hc, hwc⟩ := wi1_surj _ hw
  set v := C.dc c with hv
  have hcv : C.cd v = c := C.cd_dc c hc
  have hm : (u₁ * v * u₁⁻¹ : G) ∈ V := (Subgroup.mem_normalizer_iff.1 huN v).1 v.2
  have h1 : C.cd (v⁻¹ * ⟨u₁ * v * u₁⁻¹, hm⟩) = C.cd w := by
    rw [C.cd_mul, C.cd_inv, cd_conj C huN v, hi, hcv, hwc]
  have h2 : (w : G) = (v : G)⁻¹ * (u₁ * v * u₁⁻¹) :=
    (congrArg Subtype.val (C.cd_injective h1)).symm
  rw [h2]
  have hvU : (v : G)⁻¹ * u₁ * v ∈ U714 T L V z := by
    have hvH : ((v : G))⁻¹ ∈ H714 T L V z := V_le_H714 T L V z (V.inv_mem v.2)
    have := (Subgroup.mem_normalizer_iff.mp (s.H_le_normalizer_U h1222 hvH) u₁).mp hu₁
    simpa using this
  have e : (v : G)⁻¹ * (u₁ * v * u₁⁻¹) = ((v : G)⁻¹ * u₁ * v) * u₁⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem _ hvU (Subgroup.inv_mem _ hu₁)

theorem comm_mem_ZU
    (h1222 : Stmt12_2_2)
    (hsmall : ∀ a, a ∈ autOn (U714 T L V z) V ↔ C.cB a = B6.id ∨ C.cB a = i1) {u₁ : G}
    (hu₁ : u₁ ∈ U714 T L V z)
    (hi : C.cB (conjAct V ⟨u₁, s.U_le_normalizer_V h1222 hu₁⟩) = i1) {u : G}
    (hu : u ∈ U714 T L V z) {v : G} (hv : v ∈ V) : u * v * u⁻¹ * v⁻¹ ∈ ZU T L V z := by
  have huN := s.U_le_normalizer_V h1222 hu
  set w : ↥V := ⟨u * v * u⁻¹ * v⁻¹, V.mul_mem ((Subgroup.mem_normalizer_iff.1 huN v).1 hv)
    (V.inv_mem hv)⟩ with hw
  have hwc : C.cd w ∈ wi1 := s.comm_code h1222 hsmall hu ⟨v, hv⟩
  refine ⟨s.mem_U_of_code h1222 hu₁ hi w hwc, Subgroup.mem_centralizer_iff.mpr fun u' hu' => ?_⟩
  have h1 := s.conj_eq_of_code h1222 hsmall hu' w hwc
  calc u' * (w : G) = u' * w * u'⁻¹ * u' := by group
    _ = w * u' := by rw [h1]

theorem ZU_le_centralizer
    (h1222 : Stmt12_2_2) (hC : Std C T L)
    (hsmall : ∀ a, a ∈ autOn (U714 T L V z) V ↔ C.cB a = B6.id ∨ C.cB a = i1) :
    ZU T L V z ≤ Subgroup.centralizer (V : Set G) := by
  intro x hx
  have hxN := s.U_le_normalizer_V h1222 hx.1
  rcases code_U hsmall hx.1 hxN with h1 | h1
  · exact (conjAct_eq_one' hxN).1 (C.cB_eq_one.1 h1)
  · exfalso
    set v₁ := C.dc 10 with hv₁
    have hv₁c : C.cd v₁ = 10 := C.cd_dc 10 (by norm_num)
    have hv₁V1 : (v₁ : G) ∈ V1 T L V := by
      rw [V1_eq s.setting.hyp hC]
      exact (C.mem_subG v₁).2 (hv₁c ▸ mem_p1c_10)
    have hv₁U : (v₁ : G) ∈ U714 T L V z := le_conjClosure _ _ hv₁V1
    have hcomm := Subgroup.mem_centralizer_iff.mp hx.2 _ hv₁U
    have h2 : C.cd ⟨x * v₁ * x⁻¹, (Subgroup.mem_normalizer_iff.1 hxN v₁).1 v₁.2⟩ = 15 := by
      rw [cd_conj C hxN v₁, h1, hv₁c, i1_app_10]
    have h3 : (⟨x * v₁ * x⁻¹, (Subgroup.mem_normalizer_iff.1 hxN v₁).1 v₁.2⟩ : ↥V) = v₁ :=
      Subtype.ext (show x * v₁ * x⁻¹ = v₁ by rw [← hcomm, mul_inv_cancel_right])
    rw [h3, hv₁c] at h2
    exact absurd h2 (by norm_num)

end Small

abbrev Zt (T L V : Subgroup G) (z : G) : Subgroup ↥(Ut T L V z) :=
  (tildeOf (Subgroup.zpowers z) (ZU T L V z)).subgroupOf (Ut T L V z)

omit s in
@[expose] def stabSeries (T L V : Subgroup G) (z : G) : Subgroup (MulAut ↥(Ut T L V z)) where
  carrier := {φ | φ ∈ Hs T L V z ∧ (∀ x, x⁻¹ * φ x ∈ Zt T L V z) ∧ ∀ x ∈ Zt T L V z, φ x = x}
  one_mem' := ⟨Subgroup.one_mem _, fun x => by simp, fun x _ => rfl⟩
  mul_mem' := by
    rintro φ ψ ⟨hφ, hφ1, hφ2⟩ ⟨hψ, hψ1, hψ2⟩
    refine ⟨Subgroup.mul_mem _ hφ hψ, fun x => ?_, fun x hx => ?_⟩
    · have e : x⁻¹ * (φ * ψ) x = (x⁻¹ * ψ x) * ((ψ x)⁻¹ * φ (ψ x)) := by
        rw [MulAut.mul_apply]
        group
      rw [e]
      exact Subgroup.mul_mem _ (hψ1 x) (hφ1 (ψ x))
    · rw [MulAut.mul_apply, hψ2 x hx, hφ2 x hx]
  inv_mem' := by
    rintro φ ⟨hφ, hφ1, hφ2⟩
    refine ⟨Subgroup.inv_mem _ hφ, fun x => ?_, fun x hx => ?_⟩
    · have h := hφ1 (φ⁻¹ x)
      rw [MulAut.apply_inv_self] at h
      have e : x⁻¹ * φ⁻¹ x = ((φ⁻¹ x)⁻¹ * x)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ h
    · have h := hφ2 x hx
      calc φ⁻¹ x = φ⁻¹ (φ x) := by rw [h]
        _ = x := MulAut.inv_apply_self _ _ _

theorem Hs_conj_Zt
    (h1222 : Stmt12_2_2) {ψ : MulAut ↥(Ut T L V z)} (hψ : ψ ∈ Hs T L V z) {x : ↥(Ut T L V z)}
    (hx : x ∈ Zt T L V z) : ψ x ∈ Zt T L V z := by
  obtain ⟨y, hyN, hyH, rfl⟩ := mem_autOn'.1 hψ
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  rw [conjAct_val]
  obtain ⟨h, hh, rfl⟩ := mem_secImg.1 hyH
  have hhN : (h : G) ∈ Subgroup.normalizer (ZU T L V z : Set G) := s.H_le_normalizer_ZU h1222 hh
  exact secMk_conj_mem_secImg hhN hx

theorem Hs_le_normalizer_stabSeries
    (h1222 : Stmt12_2_2) :
    Hs T L V z ≤ Subgroup.normalizer (stabSeries T L V z : Set (MulAut ↥(Ut T L V z))) := by
  intro ψ hψ
  refine Subgroup.mem_normalizer_fintype fun φ hφ => ?_
  obtain ⟨hφH, hφ1, hφ2⟩ := hφ
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hψ hφH) (Subgroup.inv_mem _ hψ), fun x => ?_,
    fun x hx => ?_⟩
  · have e : x⁻¹ * (ψ * φ * ψ⁻¹) x = ψ ((ψ⁻¹ x)⁻¹ * φ (ψ⁻¹ x)) := by
      rw [MulAut.mul_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.apply_inv_self]
    rw [e]
    exact s.Hs_conj_Zt h1222 hψ (hφ1 _)
  · have hx' : ψ⁻¹ x ∈ Zt T L V z := s.Hs_conj_Zt h1222 (Subgroup.inv_mem _ hψ) hx
    rw [MulAut.mul_apply, MulAut.mul_apply, hφ2 _ hx', MulAut.apply_inv_self]

theorem sq_stabSeries
    (h1222 : Stmt12_2_2) {φ : MulAut ↥(Ut T L V z)} (hφ : φ ∈ stabSeries T L V z) :
    φ * φ = 1 := by
  obtain ⟨-, hφ1, hφ2⟩ := hφ
  have hab := (s.elemAbelian_Ut h1222)
  refine MulEquiv.ext fun x => ?_
  have hd := hφ1 x
  set d := x⁻¹ * φ x with hdd
  have hx : φ x = x * d := by rw [hdd]; group
  have hd2 : d * d = 1 := by
    have := hab.2 _ d.2
    exact Subtype.ext (by simpa [pow_two] using this)
  rw [MulAut.mul_apply, hx, map_mul, hφ2 d hd, hx, mul_assoc, hd2, mul_one, MulAut.one_apply]

theorem stabSeries_eq_bot
    (h1222 : Stmt12_2_2) : stabSeries T L V z = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ↥(stabSeries T L V z) := fun φ =>
    ⟨1, Subtype.ext (by rw [pow_one, pow_two]; exact s.sq_stabSeries h1222 φ.2)⟩
  have hle : stabSeries T L V z ≤ pCoreOf 2 (Hs T L V z) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (fun φ hφ => hφ.1)
      (s.Hs_le_normalizer_stabSeries h1222) hp
  rw [s.pCoreOf_Hs h1222] at hle
  exact le_bot_iff.mp hle

theorem false_of_small
    [IsMulCommutative ↥V] (h1222 : Stmt12_2_2) {C : Coding ↥V} (hC : Std C T L)
    (hsmall : ∀ a, a ∈ autOn (U714 T L V z) V ↔ C.cB a = B6.id ∨ C.cB a = i1) : False := by
  obtain ⟨a, ha, ha1⟩ := s.exists_ne_one_U h1222
  have hai : C.cB a = i1 := ((hsmall a).1 ha).resolve_left fun he => ha1 (C.cB_eq_one.1 he)
  obtain ⟨u₁, hu₁N, hu₁, rfl⟩ := mem_autOn'.1 ha
  have hi : C.cB (conjAct V ⟨u₁, s.U_le_normalizer_V h1222 hu₁⟩) = i1 := hai
  apply s.not_le_cTil h1222
  intro v hv
  refine (s.mem_ker_phiV h1222 ⟨v, hv⟩).1 ?_
  have hvN := s.V_le_N h1222 hv
  have hmem : s.phiV h1222 ⟨v, hv⟩ ∈ stabSeries T L V z := by
    refine ⟨s.phiV_mem_Hs h1222 _, fun x => ?_, fun x hx => ?_⟩
    · rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, s.phiV_apply h1222]
      obtain ⟨u, hu, hxu⟩ := mem_secImg.1 x.2
      rw [← hxu]
      have hc : (u : G)⁻¹ * v * u * v⁻¹ ∈ ZU T L V z := by
        have := s.comm_mem_ZU h1222 hsmall hu₁ hi ((U714 T L V z).inv_mem hu) hv
        simpa using this
      change (secMk _ _ u)⁻¹ * (secMk _ _ ⟨v, hvN⟩ * secMk _ _ u * (secMk _ _ ⟨v, hvN⟩)⁻¹) ∈ _
      have e : (secMk _ _ u)⁻¹ * (secMk _ _ ⟨v, hvN⟩ * secMk _ _ u * (secMk _ _ ⟨v, hvN⟩)⁻¹) =
          secMk (Subgroup.normalizer (Subgroup.zpowers z : Set G)) (Subgroup.zpowers z)
            (u⁻¹ * ⟨v, hvN⟩ * u * ⟨v, hvN⟩⁻¹) := by
        simp only [map_mul, map_inv]
        group
      rw [e]
      exact secMk_mem_secImg (by simpa using hc)
    · apply Subtype.ext
      rw [s.phiV_apply h1222]
      rw [Subgroup.mem_subgroupOf] at hx
      obtain ⟨w, hw, hxw⟩ := mem_secImg.1 hx
      rw [← hxw]
      have hwC := s.ZU_le_centralizer h1222 hC hsmall hw
      have hvw : (⟨v, hvN⟩ * w * ⟨v, hvN⟩⁻¹ : ↥(Subgroup.normalizer
          (Subgroup.zpowers z : Set G))) = w := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [Subgroup.mem_centralizer_iff.mp hwC v hv, mul_inv_cancel_right]
      change secMk _ _ ⟨v, hvN⟩ * secMk _ _ w * (secMk _ _ ⟨v, hvN⟩)⁻¹ = secMk _ _ w
      rw [← map_inv, ← map_mul, ← map_mul, hvw]
  rw [s.stabSeries_eq_bot h1222] at hmem
  exact (Subgroup.mem_bot).1 hmem

end CFSG.Quasithin.H13.S127.L715.Set714
