module

public import CFSG.Quasithin.H13.A6S1379c

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped Pointwise

theorem g0135_mem : swap (0 : Fin 6) 1 * swap 3 5 ∈ alternatingGroup (Fin 6) :=
  Equiv.Perm.mem_alternatingGroup.2 (by decide)

theorem conj_g0135_45 :
    (swap (0 : Fin 6) 1 * swap 3 5)⁻¹ * swap 4 5 * (swap 0 1 * swap 3 5) = swap 3 4 := by decide

theorem y_perm : swap (4 : Fin 6) 5 * swap 3 4 * swap 4 5 = swap 3 5 := by decide

theorem swap45_sq : swap (4 : Fin 6) 5 * swap 4 5 = 1 := by decide

theorem swap34_sq : swap (3 : Fin 6) 4 * swap 3 4 = 1 := by decide

theorem act4f_g_y : act4f (swap (0 : Fin 6) 1 * swap 3 5)⁻¹ e0123 = act4f (swap 3 5)⁻¹ e0123 := by
  decide

theorem W4_cases : ∀ x : P6, InW4 x →
    InW3 x ∨ InW3 (x * act4f (swap (0 : Fin 6) 1 * swap 3 5)⁻¹ e0123) := by
  decide +kernel

theorem r_pow_cases (i : ℤ) :
    ((swap (4 : Fin 6) 5 * swap 3 4) ^ i = 1 → (3 : ℤ) ∣ i) ∧
      swap (4 : Fin 6) 5 * (swap 4 5 * swap 3 4) ^ i ≠ 1 := by
  have h3 : (swap (4 : Fin 6) 5 * swap 3 4) ^ (3 : ℤ) = 1 := by decide
  rw [zpow_eq_zpow_emod i h3]
  have h0 := Int.emod_nonneg i (by norm_num : (3 : ℤ) ≠ 0)
  have h1 := Int.emod_lt_of_pos i (by norm_num : (0 : ℤ) < 3)
  have key : ∀ k : ℤ, 0 ≤ k → k < 3 →
      ((swap (4 : Fin 6) 5 * swap 3 4) ^ k = 1 → k = 0) ∧
        swap (4 : Fin 6) 5 * (swap 4 5 * swap 3 4) ^ k ≠ 1 := by
    intro k hk0 hk3
    interval_cases k <;> decide
  obtain ⟨k1, k2⟩ := key _ h0 h1
  refine ⟨fun h => ?_, k2⟩
  have := k1 h
  exact Int.dvd_of_emod_eq_zero this

theorem conj_354_012 :
    swap (0 : Fin 6) 3 * swap 1 5 * swap 1 2 * swap 1 4 ∈ alternatingGroup (Fin 6) ∧
      (swap (0 : Fin 6) 3 * swap 1 5 * swap 1 2 * swap 1 4) * (swap 4 5 * swap 3 4) *
        (swap (0 : Fin 6) 3 * swap 1 5 * swap 1 2 * swap 1 4)⁻¹ = swap 0 1 * swap 1 2 :=
  ⟨Equiv.Perm.mem_alternatingGroup.2 (by decide), by decide⟩

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem cLT_le_T (hhat : ¬ IsHatA6 L) :
    (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTN := S.T_le_NL
  have hCL : ∀ l ∈ L, l ∈ Subgroup.centralizer (V : Set G) → ∃ k : ℕ, l ^ 2 ^ k = 1 := by
    intro l hl hlC
    have hlO := S.inf_centralizer_le_pCoreOf hhat ⟨hl, hlC⟩
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 L ⟨l, hlO⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hC2 : IsPGroup 2 ↥((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) := by
    rintro ⟨x, hxLT, hxC⟩
    have hx : x ∈ ((L : Set G) * (T : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left L T hTN]
      exact hxLT
    obtain ⟨l, hl, t, ht, rfl⟩ := hx
    obtain ⟨a, ha⟩ := S.h13.sylow.1 ⟨t, ht⟩
    have hta : t ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
    obtain ⟨l', hl', he⟩ := A5.pow_mem_mul_of_normalizes hl (hTN ht) (2 ^ a)
    rw [hta, mul_one] at he
    have hC : (l * t) ^ 2 ^ a ∈ Subgroup.centralizer (V : Set G) := Subgroup.pow_mem _ hxC _
    rw [he] at hC
    obtain ⟨k, hk⟩ := hCL l' hl' hC
    refine ⟨a + k, Subtype.ext ?_⟩
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one, pow_add, pow_mul, he, hk]
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le S.frame.L_le S.frame.T_le
  have hCn : L ⊔ T ≤
      Subgroup.normalizer (((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ g ∈ L ⊔ T, ∀ c, c ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) →
        g * c * g⁻¹ ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) := by
      intro g hg c hc
      refine ⟨(L ⊔ T).mul_mem ((L ⊔ T).mul_mem hg hc.1) ((L ⊔ T).inv_mem hg), ?_⟩
      show g * c * g⁻¹ ∈ Subgroup.centralizer (V : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hv' : g⁻¹ * v * g ∈ V :=
        (Subgroup.mem_normalizer_iff''.mp (hLTV hg) v).mp hv
      have hcomm := Subgroup.mem_centralizer_iff.mp hc.2 _ hv'
      calc v * (g * c * g⁻¹) = g * ((g⁻¹ * v * g) * c) * g⁻¹ := by group
        _ = g * (c * (g⁻¹ * v * g)) * g⁻¹ := by rw [hcomm]
        _ = g * c * g⁻¹ * v := by group
    intro c
    refine ⟨key g hg c, fun hc => ?_⟩
    simpa [mul_assoc] using key g⁻¹ ((L ⊔ T).inv_mem hg) _ hc
  exact (le_pCoreOf_of_le_normalizer 2 inf_le_left hCn hC2).trans
    (pCoreOf_le_of_sylow S.h13.sylow le_sup_right)

theorem le_normalizer_cLT :
    L ⊔ T ≤ Subgroup.normalizer (((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) :
      Set G) := by
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le S.frame.L_le S.frame.T_le
  refine A5.le_normalizer_of_forall_conj_mem fun g hg c hc => ⟨?_, ?_⟩
  · exact (L ⊔ T).mul_mem ((L ⊔ T).mul_mem hg hc.1) ((L ⊔ T).inv_mem hg)
  · exact A5.conj_mem_centralizer_of_mem_normalizer (hLTV hg) hc.2

theorem exists_g0135 : ∃ g : ↥(Subgroup.normalizer (V : Set G)), (g : G) ∈ L ∧
    S.frame.ρ g = swap 0 1 * swap 3 5 :=
  (S.frame.image_L _).2 g0135_mem

structure Conf (H : Subgroup G) where
  g : ↥(Subgroup.normalizer (V : Set G))
  g_mem : (g : G) ∈ L
  rho_g : S.frame.ρ g = swap 0 1 * swap 3 5
  v : ↥(Subgroup.normalizer (V : Set G))
  v_mem : (v : G) ∈ conjClosure V H
  v_sq : (v : G) * v = 1
  rho_v : S.frame.ρ v = swap 4 5

namespace Conf

variable {S} {H : Subgroup G} (C : S.Conf H)

@[expose] def w : ↥(Subgroup.normalizer (V : Set G)) := C.g⁻¹ * C.v * C.g

@[expose] def y : ↥(Subgroup.normalizer (V : Set G)) := C.v * C.w * C.v

@[expose] def VHg : Subgroup G := conjSub (C.g : G)⁻¹ (conjClosure V H)

@[expose] def I : Subgroup G := conjClosure V H ⊔ C.VHg

@[expose] def ZI : Subgroup G := conjClosure V H ⊓ C.VHg

@[expose] def W (_ : S.Conf H) : Subgroup G := conjClosure V H ⊓ Subgroup.centralizer (V : Set G)

@[expose] def A : Subgroup G := C.VHg ⊓ Subgroup.centralizer (V : Set G)

@[expose] def N : Subgroup G := C.I ⊓ Subgroup.centralizer (V : Set G)

theorem mem_VHg {x : G} : x ∈ C.VHg ↔ (C.g : G) * x * (C.g : G)⁻¹ ∈ conjClosure V H := by
  rw [VHg, mem_conjSub, inv_inv]

theorem rho_w : S.frame.ρ C.w = swap 3 4 := by
  rw [w, map_mul, map_mul, map_inv, C.rho_g, C.rho_v]
  exact conj_g0135_45

theorem rho_y : S.frame.ρ C.y = swap 3 5 := by
  rw [y, map_mul, map_mul, C.rho_w, C.rho_v]
  exact y_perm

theorem w_coe : (C.w : G) = (C.g : G)⁻¹ * C.v * C.g := rfl

theorem y_coe : (C.y : G) = (C.v : G) * C.w * C.v := rfl

theorem w_sq : (C.w : G) * C.w = 1 := by
  rw [w_coe]
  calc (C.g : G)⁻¹ * C.v * C.g * ((C.g : G)⁻¹ * C.v * C.g) = (C.g : G)⁻¹ * (C.v * C.v) * C.g := by
        group
    _ = 1 := by rw [C.v_sq]; group

theorem v_inv : (C.v : G)⁻¹ = C.v := inv_eq_of_mul_eq_one_right C.v_sq

theorem w_inv : (C.w : G)⁻¹ = C.w := inv_eq_of_mul_eq_one_right C.w_sq

theorem w_mem : (C.w : G) ∈ C.VHg := by
  rw [mem_VHg, w_coe]
  have e : (C.g : G) * ((C.g : G)⁻¹ * C.v * C.g) * (C.g : G)⁻¹ = C.v := by group
  rw [e]
  exact C.v_mem

theorem VH_le_I : conjClosure V H ≤ C.I := le_sup_left

theorem VHg_le_I : C.VHg ≤ C.I := le_sup_right

theorem v_mem_I : (C.v : G) ∈ C.I := C.VH_le_I C.v_mem

theorem w_mem_I : (C.w : G) ∈ C.I := C.VHg_le_I C.w_mem

theorem y_mem_I : (C.y : G) ∈ C.I := by
  rw [y_coe]
  exact C.I.mul_mem (C.I.mul_mem C.v_mem_I C.w_mem_I) C.v_mem_I

theorem W_le : C.W ≤ conjClosure V H := inf_le_left

theorem W_le_N : C.W ≤ C.N := inf_le_inf_right _ C.VH_le_I

theorem A_le_N : C.A ≤ C.N := inf_le_inf_right _ C.VHg_le_I

theorem ZI_le_VH : C.ZI ≤ conjClosure V H := inf_le_left

theorem ZI_le_VHg : C.ZI ≤ C.VHg := inf_le_right

theorem V_le_ZI : V ≤ C.ZI := by
  intro x hx
  exact ⟨le_conjClosure _ _ hx,
    (C.mem_VHg).2 (le_conjClosure _ _ ((Subgroup.mem_normalizer_iff.mp C.g.2 x).mp hx))⟩

end Conf

section NonAb

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H))
include hNS h13315 h1356two hH hab

theorem VH_le_QH : conjClosure V H ≤ pCoreOf 2 H :=
  conjClosure_le fun _ hh v hv =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hh) v).mp
      (S.V_le_QH hNS h13315 h1356two hH hab hv)

theorem VH_le_T : conjClosure V H ≤ T :=
  (S.VH_le_QH hNS h13315 h1356two hH hab).trans
    (pCoreOf_le_of_sylow S.h13.sylow (S.hypF91 hNS h13315 h1356two hH).T_le_H)

theorem isPGroup_VH : IsPGroup 2 (conjClosure V H) :=
  S.h13.sylow.1.to_le (S.VH_le_T hNS h13315 h1356two hH hab)

theorem exists_conf
    (hna : ¬ IsElemAbelian 2 (conjClosure V H)) : Nonempty (S.Conf H) := by
  obtain ⟨g, hgL, hρg⟩ := S.exists_g0135
  obtain ⟨h, hh, w, hw, hwN, hρw⟩ := S.exists_conjSub_rho_45 hNS h13315 h1356two hH hab hna
  have hw' : h⁻¹ * w * h ∈ V := mem_conjSub.1 hw
  have hwVH : w ∈ conjClosure V H := by
    have e : w = h * (h⁻¹ * w * h) * h⁻¹ := by group
    rw [e]
    exact mem_conjClosure hh hw'
  have hsq : w * w = 1 := by
    have h2 : (h⁻¹ * w * h) ^ 2 = 1 := S.elemAbelian_V.2 _ hw'
    have e : w * w = h * (h⁻¹ * w * h) ^ 2 * h⁻¹ := by rw [pow_two]; group
    rw [e, h2]
    group
  exact ⟨⟨g, hgL, hρg, ⟨w, hwN⟩, hwVH, hsq, hρw⟩⟩

theorem VH_le_NV :
    conjClosure V H ≤ Subgroup.normalizer (V : Set G) :=
  (S.VH_le_T hNS h13315 h1356two hH hab).trans S.frame.T_le

omit hab in
theorem T_le_normalizer_VH :
    T ≤ Subgroup.normalizer (conjClosure V H : Set G) :=
  (S.hypF91 hNS h13315 h1356two hH).T_le_H.trans (le_normalizer_conjClosure V H)

omit hab in
theorem cLT_le_normalizer_VH (hhat : ¬ IsHatA6 L) :
    (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (conjClosure V H : Set G) :=
  (S.cLT_le_T hhat).trans (S.T_le_normalizer_VH hNS h13315 h1356two hH)

namespace Conf

variable {S} (C : S.Conf H)

theorem VHg_le_NV :
    C.VHg ≤ Subgroup.normalizer (V : Set G) := by
  intro x hx
  have h1 := S.VH_le_NV hNS h13315 h1356two hH hab ((C.mem_VHg).1 hx)
  have e : x = (C.g : G)⁻¹ * ((C.g : G) * x * (C.g : G)⁻¹) * C.g := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ C.g.2) h1) C.g.2

theorem I_le_NV : C.I ≤ Subgroup.normalizer (V : Set G) :=
  sup_le (S.VH_le_NV hNS h13315 h1356two hH hab) (C.VHg_le_NV hNS h13315 h1356two hH hab)

theorem VHg_le_LT : C.VHg ≤ L ⊔ T := by
  intro x hx
  have h1 : (C.g : G) * x * (C.g : G)⁻¹ ∈ T :=
    S.VH_le_T hNS h13315 h1356two hH hab ((C.mem_VHg).1 hx)
  have hgLT : (C.g : G) ∈ L ⊔ T := le_sup_left (a := L) C.g_mem
  have e : x = (C.g : G)⁻¹ * ((C.g : G) * x * (C.g : G)⁻¹) * C.g := by group
  rw [e]
  exact (L ⊔ T).mul_mem ((L ⊔ T).mul_mem ((L ⊔ T).inv_mem hgLT) (le_sup_right (a := L) h1)) hgLT

theorem I_le_LT : C.I ≤ L ⊔ T :=
  sup_le ((S.VH_le_T hNS h13315 h1356two hH hab).trans le_sup_right)
    (C.VHg_le_LT hNS h13315 h1356two hH hab)

theorem rho_VHg {x : G} (hx : x ∈ C.VHg) :
    ∃ hxN : x ∈ Subgroup.normalizer (V : Set G),
      S.frame.ρ ⟨x, hxN⟩ = 1 ∨ S.frame.ρ ⟨x, hxN⟩ = swap 3 4 := by
  have hxN := C.VHg_le_NV hNS h13315 h1356two hH hab hx
  refine ⟨hxN, ?_⟩
  obtain ⟨hyN, hρ⟩ := S.rho_VH hNS h13315 h1356two hH hab ((C.mem_VHg).1 hx)
  have e : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (V : Set G))) =
      C.g⁻¹ * ⟨(C.g : G) * x * (C.g : G)⁻¹, hyN⟩ * C.g := by
    apply Subtype.ext
    show x = (C.g : G)⁻¹ * ((C.g : G) * x * (C.g : G)⁻¹) * C.g
    group
  rw [e, map_mul, map_mul, map_inv, C.rho_g]
  rcases hρ with h | h
  · left
    rw [h, mul_one, inv_mul_cancel]
  · right
    rw [h]
    exact conj_g0135_45

theorem ZI_le_centralizer :
    C.ZI ≤ Subgroup.centralizer (V : Set G) := by
  intro x hx
  obtain ⟨hxN, h1⟩ := S.rho_VH hNS h13315 h1356two hH hab (C.ZI_le_VH hx)
  obtain ⟨hxN', h2⟩ := C.rho_VHg hNS h13315 h1356two hH hab (C.ZI_le_VHg hx)
  refine (S.rho_eq_one_iff ⟨x, hxN⟩).1 ?_
  rcases h1 with h1 | h1
  · exact h1
  · rcases h2 with h2 | h2
    · exact h2
    · exact absurd (h1.symm.trans h2) (by decide)

theorem ZI_le_W : C.ZI ≤ C.W :=
  le_inf C.ZI_le_VH (C.ZI_le_centralizer hNS h13315 h1356two hH hab)

theorem ZI_le_A : C.ZI ≤ C.A :=
  le_inf C.ZI_le_VHg (C.ZI_le_centralizer hNS h13315 h1356two hH hab)

theorem N_le_cLT :
    C.N ≤ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) :=
  inf_le_inf_right _ (C.I_le_LT hNS h13315 h1356two hH hab)

section Hat

variable (hhat : ¬ IsHatA6 L)
include hhat

omit hab in
theorem cLT_le_normalizer_VHg :
    (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (C.VHg : Set G) := by
  have hgN : (C.g : G) ∈ Subgroup.normalizer
      (((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) :=
    S.le_normalizer_cLT (le_sup_left (a := L) C.g_mem)
  refine A5.le_normalizer_of_forall_conj_mem fun q hq x hx => ?_
  rw [mem_VHg] at hx ⊢
  have hq' : (C.g : G) * q * (C.g : G)⁻¹ ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) :=
    (Subgroup.mem_normalizer_iff.mp hgN q).mp hq
  have h1 := (Subgroup.mem_normalizer_iff.mp
    (S.cLT_le_normalizer_VH hNS h13315 h1356two hH hhat hq') _).mp hx
  have e : (C.g : G) * (q * x * q⁻¹) * (C.g : G)⁻¹ =
      ((C.g : G) * q * (C.g : G)⁻¹) * ((C.g : G) * x * (C.g : G)⁻¹) *
        ((C.g : G) * q * (C.g : G)⁻¹)⁻¹ := by group
  rw [e]
  exact h1

omit hab in
theorem cLT_le_normalizer_I :
    (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (C.I : Set G) := by
  refine A5.le_normalizer_of_forall_conj_mem fun q hq x hx => ?_
  have h1 := S.cLT_le_normalizer_VH hNS h13315 h1356two hH hhat hq
  have h2 := C.cLT_le_normalizer_VHg hNS h13315 h1356two hH hhat hq
  have hle : conjClosure V H ⊔ C.VHg ≤ C.I.comap (MulAut.conj q).toMonoidHom := by
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact C.VH_le_I ((Subgroup.mem_normalizer_iff.mp h1 y).mp hy)
    · rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact C.VHg_le_I ((Subgroup.mem_normalizer_iff.mp h2 y).mp hy)
  have := hle hx
  rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this

theorem isPGroup_N : IsPGroup 2 C.N :=
  S.h13.sylow.1.to_le ((C.N_le_cLT hNS h13315 h1356two hH hab).trans (S.cLT_le_T hhat))

theorem W_le_normalizer_A :
    C.W ≤ Subgroup.normalizer (C.A : Set G) := by
  intro x hx
  have hxQ : x ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) :=
    C.N_le_cLT hNS h13315 h1356two hH hab (C.W_le_N hx)
  have h1 := C.cLT_le_normalizer_VHg hNS h13315 h1356two hH hhat hxQ
  have hxN := S.VH_le_NV hNS h13315 h1356two hH hab (C.W_le hx)
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · rintro ⟨ha1, ha2⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp h1 a).mp ha1,
      A5.conj_mem_centralizer_of_mem_normalizer hxN ha2⟩
  · rintro ⟨ha1, ha2⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp h1 a).mpr ha1, ?_⟩
    have := A5.conj_mem_centralizer_of_mem_normalizer (Subgroup.inv_mem _ hxN) ha2
    simpa [mul_assoc] using this

end Hat

end Conf

end NonAb

end Setting4

end CFSG.Quasithin.H13.A6
