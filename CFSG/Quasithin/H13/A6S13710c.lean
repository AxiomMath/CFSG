module

public import CFSG.Quasithin.H13.A6S13710b
public import CFSG.Quasithin.H13.A6Nu

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

theorem swap34_not_mem_R8 : swap (3 : Fin 6) 4 ∉ R8 := by decide

theorem g0135_sq : (swap (0 : Fin 6) 1 * swap 3 5) * (swap 0 1 * swap 3 5) = 1 := by decide

theorem card_fix_354 :
    Fintype.card {x : P6 // InW4 x ∧ act4f (swap 4 5 * swap 3 4) x = x} = 4 := by
  decide +kernel

theorem K4L_fix_012 : ∀ κ ∈ K4L,
    (swap (0 : Fin 6) 1 * swap 1 2) * κ * (swap 0 1 * swap 1 2)⁻¹ = κ → κ = 1 := by decide +kernel

theorem c012_fix45 :
    (swap (0 : Fin 6) 1 * swap 1 2 : Perm (Fin 6)) 4 = 4 ∧
      (swap (0 : Fin 6) 1 * swap 1 2 : Perm (Fin 6)) 5 = 5 := by
  decide

instance : DecidablePred (· ∈ K4sub) := fun σ => decidable_of_iff (σ ∈ K4L) Iff.rfl

theorem card_K4sub : Nat.card K4sub = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem two_pow_sq_mod_three (e : ℕ) : (2 ^ e) ^ 2 % 3 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, Nat.pow_mod]
  norm_num

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

theorem card_cfix_V (c : ↥(Subgroup.normalizer (V : Set G)))
    (hc : S.frame.ρ c = swap 4 5 * swap 3 4) : Nat.card (cfix (c : G) V) = 4 := by
  have key : ∀ v : ↥V, ((c : G) * v = v * c ↔
      act4f (swap 4 5 * swap 3 4) (S.frame.ψ v : P6) = (S.frame.ψ v : P6)) := by
    intro v
    rw [← hc]
    constructor
    · intro h
      have h' : (c : G) * v * (c : G)⁻¹ = v := by rw [h]; group
      exact congrArg Subtype.val ((S.conj_eq_iff c v).1 h')
    · intro h
      have h' := (S.conj_eq_iff c v).2 (Subtype.ext h)
      calc (c : G) * v = (c : G) * v * (c : G)⁻¹ * c := by group
        _ = v * c := by rw [h']
  let e : ↥(cfix (c : G) V) ≃ {x : P6 // InW4 x ∧ act4f (swap 4 5 * swap 3 4) x = x} :=
    { toFun := fun v => ⟨(S.frame.ψ ⟨v, (mem_cfix.1 v.2).1⟩ : P6),
        (S.frame.ψ ⟨v, (mem_cfix.1 v.2).1⟩).2, (key _).1 (mem_cfix.1 v.2).2⟩
      invFun := fun x => ⟨(S.frame.ψ.symm ⟨x.1, x.2.1⟩ : G), mem_cfix.2
        ⟨(S.frame.ψ.symm ⟨x.1, x.2.1⟩).2, (key _).2 (by
          rw [S.frame.ψ.apply_symm_apply]
          exact x.2.2)⟩⟩
      left_inv := fun v => by
        apply Subtype.ext
        show ((S.frame.ψ.symm (S.frame.ψ ⟨v, (mem_cfix.1 v.2).1⟩) : ↥V) : G) = v
        rw [MulEquiv.symm_apply_apply]
      right_inv := fun x => by
        apply Subtype.ext
        show ((S.frame.ψ (S.frame.ψ.symm ⟨x.1, x.2.1⟩) : ↥W4) : P6) = x.1
        rw [MulEquiv.apply_symm_apply] }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  exact card_fix_354

theorem nu_V (c : ↥(Subgroup.normalizer (V : Set G)))
    (hc : S.frame.ρ c = swap 4 5 * swap 3 4) : nu (c : G) V = 4 := by
  have h1 := Subgroup.relIndex_mul_card (cfix (c : G) V) V
  rw [inf_eq_left.2 (show cfix (c : G) V ≤ V from inf_le_left), card_cfix_V c hc,
    S.card_V] at h1
  unfold nu
  omega

theorem V1_le_UH (S : Setting4 G T L V) {H : Subgroup G} :
    fsuV1 T V ≤ conjClosure S.V3 H :=
  (S.V1_le_V2.trans S.V2_le_V3).trans (le_conjClosure _ _)

namespace Conf

variable {H : Subgroup G} (C : S.Conf H)

theorem UHg_le_VHg : conjSub (C.g : G)⁻¹ (conjClosure S.V3 H) ≤ C.VHg :=
  conjSub_mono _ (conjClosure_mono S.V3_le_V le_rfl)

@[expose] noncomputable def c3 : ↥(Subgroup.normalizer (V : Set G)) := C.r ^ (Nat.card C.N ^ 2)

theorem c3_coe : (C.c3 : G) = (C.r : G) ^ (Nat.card C.N ^ 2) := by
  rw [c3]
  simp

theorem c3_cube : (C.c3 : G) ^ 3 = 1 := by
  have h1 : ((C.r : G) ^ 3) ^ Nat.card C.N = 1 := by
    have := congrArg Subtype.val (pow_card_eq_one' (G := ↥C.N) (x := ⟨_, C.r_cube_mem_N⟩))
    rwa [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this
  rw [c3_coe, ← pow_mul, mul_comm, pow_two, ← mul_assoc, pow_mul, pow_mul, h1, one_pow]

theorem c3_mem_I : (C.c3 : G) ∈ C.I := by
  rw [c3_coe]
  exact C.I.pow_mem C.r_mem_I _

theorem g_sq_mem (hhat : ¬ IsHatA6 L) :
    (C.g : G) * C.g ∈ L₁Of L (fsuV1 T V) ⊔ T := by
  have h : S.frame.ρ (C.g * C.g) = 1 := by
    rw [map_mul, C.rho_g]
    exact g0135_sq
  have hC := (S.rho_eq_one_iff _).1 h
  have hO := S.inf_centralizer_le_pCoreOf hhat ⟨L.mul_mem C.g_mem C.g_mem, hC⟩
  exact le_sup_right (a := L₁Of L (fsuV1 T V)) (S.pCoreOf_L_le_T hO)

end Conf

section NonAb

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H))
include hNS h13315 h1356two hH hab

theorem UH_le_centralizer_V :
    conjClosure S.V3 H ≤ Subgroup.centralizer (V : Set G) := by
  have hF := S.hypF91 hNS h13315 h1356two hH
  have hV := hF.le_pCoreOf_iff_le_centralizer.1 (S.V_le_QH hNS h13315 h1356two hH hab)
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact (Subgroup.mem_centralizer_iff.mp (hV hv).2 u hu).symm

theorem UH_le_cLT :
    conjClosure S.V3 H ≤ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) :=
  le_inf ((S.UH_le_T hNS h1356two h13315 hH).trans le_sup_right)
    (S.UH_le_centralizer_V hNS h13315 h1356two hH hab)

omit hab in
theorem comm_VH_HC {x : G} (hxQ : x ∈ pCoreOf 2 H)
    (hxC : x ∈ Subgroup.centralizer (conjClosure S.V3 H : Set G)) {y : G}
    (hy : y ∈ conjClosure V H) : y * x * y⁻¹ * x⁻¹ ∈ fsuV1 T V := by
  have hF := S.hypF91 hNS h13315 h1356two hH
  have hQT : pCoreOf 2 H ≤ T := pCoreOf_le_of_sylow S.h13.sylow hF.T_le_H
  let K : Subgroup G :=
    { carrier := {y | y ∈ H ∧ y * x * y⁻¹ * x⁻¹ ∈ fsuV1 T V}
      mul_mem' := by
        rintro y₁ y₂ ⟨h1H, h1⟩ ⟨h2H, h2⟩
        refine ⟨H.mul_mem h1H h2H, ?_⟩
        have e : y₁ * y₂ * x * (y₁ * y₂)⁻¹ * x⁻¹ =
            y₁ * (y₂ * x * y₂⁻¹ * x⁻¹) * y₁⁻¹ * (y₁ * x * y₁⁻¹ * x⁻¹) := by group
        rw [e, S.conj_V1_of_mem hH h1H h2]
        exact (fsuV1 T V).mul_mem h2 h1
      one_mem' := ⟨H.one_mem, by simp⟩
      inv_mem' := by
        rintro y ⟨hyH, h⟩
        refine ⟨H.inv_mem hyH, ?_⟩
        have e : y⁻¹ * x * y⁻¹⁻¹ * x⁻¹ = y⁻¹ * (y * x * y⁻¹ * x⁻¹)⁻¹ * y⁻¹⁻¹ := by group
        rw [e, S.conj_V1_of_mem hH (H.inv_mem hyH) ((fsuV1 T V).inv_mem h)]
        exact (fsuV1 T V).inv_mem h }
  have hle : conjClosure V H ≤ K := by
    refine conjClosure_le fun h hh v hv => ⟨H.mul_mem (H.mul_mem hh (hF.V_le_H hv))
      (H.inv_mem hh), ?_⟩
    have hx'Q : h⁻¹ * x * h ∈ pCoreOf 2 H := by
      have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (H.inv_mem hh)) x).mp hxQ
      simpa using this
    have hx'C : h⁻¹ * x * h ∈ Subgroup.centralizer (S.V3 : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hw' : h * w * h⁻¹ ∈ conjClosure S.V3 H := mem_conjClosure hh hw
      have hc := Subgroup.mem_centralizer_iff.mp hxC _ hw'
      calc w * (h⁻¹ * x * h) = h⁻¹ * ((h * w * h⁻¹) * x) * h := by group
        _ = h⁻¹ * (x * (h * w * h⁻¹)) * h := by rw [hc]
        _ = h⁻¹ * x * h * w := by group
    have hx'N : h⁻¹ * x * h ∈ Subgroup.normalizer (V : Set G) := S.frame.T_le (hQT hx'Q)
    have hρ := fixW3_iff _ (S.fixW3_of_centralizer (x := ⟨_, hx'N⟩) hx'C)
    have h1 := S.comm_mem_V1_of_rho (u := ⟨_, hx'N⟩) hρ hv
    have h2 : v * (h⁻¹ * x * h) * v⁻¹ * (h⁻¹ * x * h)⁻¹ ∈ fsuV1 T V := by
      have e : v * (h⁻¹ * x * h) * v⁻¹ * (h⁻¹ * x * h)⁻¹ =
          ((h⁻¹ * x * h) * v * (h⁻¹ * x * h)⁻¹ * v⁻¹)⁻¹ := by group
      rw [e]
      exact (fsuV1 T V).inv_mem h1
    have e : h * v * h⁻¹ * x * (h * v * h⁻¹)⁻¹ * x⁻¹ =
        h * (v * (h⁻¹ * x * h) * v⁻¹ * (h⁻¹ * x * h)⁻¹) * h⁻¹ := by group
    rw [e, S.conj_V1_of_mem hH hh h2]
    exact h2
  exact (hle hy).2

theorem comm_VH_mem_V {x y : G} (hx : x ∈ conjClosure V H)
    (hy : y ∈ conjClosure V H) : x * y * x⁻¹ * y⁻¹ ∈ V :=
  ((S.V1_le_V2.trans S.V2_le_V3).trans S.V3_le_V)
    (S.comm_VH_mem_V1 hNS h13315 h1356two hH hab hx hy)

namespace Conf

variable (C : S.Conf H)

theorem UH_le_W : conjClosure S.V3 H ≤ C.W :=
  le_inf (conjClosure_mono S.V3_le_V le_rfl) (S.UH_le_centralizer_V hNS h13315 h1356two hH hab)

omit hNS h13315 h1356two hH in
theorem V1g_inf_UH (hna : ¬ IsElemAbelian 2 (conjClosure V H))
    {x : G} (hx : x ∈ conjSub (C.g : G)⁻¹ (fsuV1 T V)) (hxU : x ∈ conjClosure S.V3 H) : x = 1 := by
  rcases (S.mem_conjSub_V1 (C.g : G)).1 hx with h | h
  · exact h
  · exfalso
    refine C.V1g_not_le_UH hab hna fun y hy => ?_
    rcases (S.mem_conjSub_V1 (C.g : G)).1 hy with h' | h'
    · rw [h']; exact (conjClosure S.V3 H).one_mem
    · rw [h', ← h]; exact hxU

theorem UHg_le_cLT :
    conjSub (C.g : G)⁻¹ (conjClosure S.V3 H) ≤ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) := by
  intro x hx
  rw [mem_conjSub, inv_inv] at hx
  have h1 := S.UH_le_cLT hNS h13315 h1356two hH hab hx
  have hgN := S.le_normalizer_cLT ((L ⊔ T).inv_mem (le_sup_left (a := L) C.g_mem))
  have := (Subgroup.mem_normalizer_iff.mp hgN _).mp h1
  have e : (C.g : G)⁻¹ * ((C.g : G) * x * (C.g : G)⁻¹) * (C.g : G)⁻¹⁻¹ = x := by group
  rwa [e] at this

theorem VHg_inf_QH_le_A {x : G} (hx : x ∈ C.VHg)
    (hxQ : x ∈ pCoreOf 2 H) : x ∈ C.A := by
  refine ⟨hx, ?_⟩
  obtain ⟨hxN, hR⟩ := S.rho_QH_mem_R8 hNS h13315 h1356two hH hxQ
  obtain ⟨hxN', h⟩ := C.rho_VHg hNS h13315 h1356two hH hab hx
  refine (S.rho_eq_one_iff ⟨x, hxN⟩).1 ?_
  rcases h with h | h
  · exact h
  · have h' : S.frame.ρ ⟨x, hxN⟩ = swap 3 4 := h
    rw [h'] at hR
    exact absurd hR swap34_not_mem_R8

theorem comm_VHg_mem_V {x y : G} (hx : x ∈ C.VHg)
    (hy : y ∈ C.VHg) : x * y * x⁻¹ * y⁻¹ ∈ V := by
  have hV := S.comm_VH_mem_V hNS h13315 h1356two hH hab ((C.mem_VHg).1 hx) ((C.mem_VHg).1 hy)
  have key : (C.g : G) * (x * y * x⁻¹ * y⁻¹) * (C.g : G)⁻¹ ∈ V := by
    have e : (C.g : G) * (x * y * x⁻¹ * y⁻¹) * (C.g : G)⁻¹ =
        (C.g : G) * x * (C.g : G)⁻¹ * ((C.g : G) * y * (C.g : G)⁻¹) *
          ((C.g : G) * x * (C.g : G)⁻¹)⁻¹ * ((C.g : G) * y * (C.g : G)⁻¹)⁻¹ := by group
    rw [e]
    exact hV
  exact (Subgroup.mem_normalizer_iff.mp C.g.2 _).mpr key

theorem c3_mod_V {x : G} (hx : x ∈ C.ZI) :
    x⁻¹ * ((C.c3 : G) * x * (C.c3 : G)⁻¹) ∈ V := by
  have hmul : ∀ a b : G, a ∈ Subgroup.normalizer (V : Set G) → x⁻¹ * (a * x * a⁻¹) ∈ V →
      x⁻¹ * (b * x * b⁻¹) ∈ V → x⁻¹ * (a * b * x * (a * b)⁻¹) ∈ V := by
    intro a b ha h1 h2
    have e : x⁻¹ * (a * b * x * (a * b)⁻¹) =
        (x⁻¹ * (a * x * a⁻¹)) * (a * (x⁻¹ * (b * x * b⁻¹)) * a⁻¹) := by group
    rw [e]
    exact V.mul_mem h1 ((Subgroup.mem_normalizer_iff.mp ha _).mp h2)
  have hv : x⁻¹ * ((C.v : G) * x * (C.v : G)⁻¹) ∈ V := by
    have := S.comm_VH_mem_V hNS h13315 h1356two hH hab ((conjClosure V H).inv_mem hx.1) C.v_mem
    have e : x⁻¹ * ((C.v : G) * x * (C.v : G)⁻¹) = x⁻¹ * C.v * x⁻¹⁻¹ * (C.v : G)⁻¹ := by group
    rw [e]
    exact this
  have hw : x⁻¹ * ((C.w : G) * x * (C.w : G)⁻¹) ∈ V := by
    have := C.comm_VHg_mem_V hNS h13315 h1356two hH hab (C.VHg.inv_mem hx.2) C.w_mem
    have e : x⁻¹ * ((C.w : G) * x * (C.w : G)⁻¹) = x⁻¹ * C.w * x⁻¹⁻¹ * (C.w : G)⁻¹ := by group
    rw [e]
    exact this
  have hr : x⁻¹ * ((C.r : G) * x * (C.r : G)⁻¹) ∈ V := by
    rw [r_coe]
    exact hmul _ _ C.v.2 hv hw
  have hrN : (C.r : G) ∈ Subgroup.normalizer (V : Set G) := C.r.2
  have hpow : ∀ k : ℕ, x⁻¹ * ((C.r : G) ^ k * x * ((C.r : G) ^ k)⁻¹) ∈ V := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      exact hmul _ _ (Subgroup.pow_mem _ hrN k) ih hr
  rw [c3_coe]
  exact hpow _

section Hat

variable (hhat : ¬ IsHatA6 L)
include hhat

theorem UHg_le_normalizer_UH :
    conjSub (C.g : G)⁻¹ (conjClosure S.V3 H) ≤
      Subgroup.normalizer (conjClosure S.V3 H : Set G) :=
  (C.UHg_le_cLT hNS h13315 h1356two hH hab).trans ((S.cLT_le_T hhat).trans
    ((S.hypF91 hNS h13315 h1356two hH).T_le_H.trans (le_normalizer_conjClosure _ _)))

theorem comm_DH_UHg (hna : ¬ IsElemAbelian 2 (conjClosure V H))
    {d u : G} (hd : d ∈ conjClosure S.V3 H ⊓ conjSub (C.g : G)⁻¹ (pCoreOf 2 H))
    (hu : u ∈ conjSub (C.g : G)⁻¹ (conjClosure S.V3 H)) : d * u = u * d := by
  have hF := S.hypF91 hNS h13315 h1356two hH
  have hne : conjSub (C.g : G)⁻¹ (fsuV1 T V) ≠ fsuV1 T V := by
    intro h
    apply C.V1g_not_le_UH hab hna
    rw [h]
    exact S.V1_le_UH
  have h1 : ⁅d, u⁆ ∈ conjSub (C.g : G)⁻¹ (fsuV1 T V) :=
    (hF.F96_3 hne).1 (Subgroup.commutator_mem_commutator
      ⟨conjClosure_mono S.V3_le_V le_rfl hd.1, hd.2⟩ hu)
  have h2 : ⁅d, u⁆ ∈ conjClosure S.V3 H := by
    rw [commutatorElement_def]
    have h3 : u * d⁻¹ * u⁻¹ ∈ conjClosure S.V3 H :=
      (Subgroup.mem_normalizer_iff.mp (C.UHg_le_normalizer_UH hNS h13315 h1356two hH hab hhat
        hu) _).mp ((conjClosure S.V3 H).inv_mem hd.1)
    have e : d * u * d⁻¹ * u⁻¹ = d * (u * d⁻¹ * u⁻¹) := by group
    rw [e]
    exact (conjClosure S.V3 H).mul_mem hd.1 h3
  have h4 := C.V1g_inf_UH hab hna h1 h2
  rw [commutatorElement_def] at h4
  calc d * u = d * u * d⁻¹ * u⁻¹ * (u * d) := by group
    _ = u * d := by rw [h4, one_mul]

theorem comm_DHg_UH (hna : ¬ IsElemAbelian 2 (conjClosure V H))
    {x u : G} (hx : x ∈ conjSub (C.g : G)⁻¹ (conjClosure S.V3 H) ⊓ pCoreOf 2 H)
    (hu : u ∈ conjClosure S.V3 H) : x * u = u * x := by
  have hF := S.hypF91 hNS h13315 h1356two hH
  have hsq := C.g_sq_mem hhat
  have h2 := (hF.F96_2 C.g_mem C.g_mem rfl hsq).1
  rw [← h2, mem_conjSub, inv_inv] at hx
  have hgu : (C.g : G) * u * (C.g : G)⁻¹ ∈ conjSub (C.g : G)⁻¹ (conjClosure S.V3 H) := by
    rw [mem_conjSub, inv_inv]
    have hgg : (C.g : G) * C.g ∈ H := hF.L₁T_le_H hsq
    have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 H hgg) u).mp hu
    have e : (C.g : G) * ((C.g : G) * u * (C.g : G)⁻¹) * (C.g : G)⁻¹ =
        (C.g : G) * C.g * u * ((C.g : G) * C.g)⁻¹ := by group
    rw [e]
    exact this
  have h := C.comm_DH_UHg hNS h13315 h1356two hH hab hhat hna hx hgu
  have e1 : (C.g : G) * x * (C.g : G)⁻¹ * ((C.g : G) * u * (C.g : G)⁻¹) =
      (C.g : G) * (x * u) * (C.g : G)⁻¹ := by group
  have e2 : (C.g : G) * u * (C.g : G)⁻¹ * ((C.g : G) * x * (C.g : G)⁻¹) =
      (C.g : G) * (u * x) * (C.g : G)⁻¹ := by group
  rw [e1, e2] at h
  simpa using h

theorem DHg_le_ZI (hna : ¬ IsElemAbelian 2 (conjClosure V H)) :
    conjSub (C.g : G)⁻¹ (conjClosure S.V3 H) ⊓ pCoreOf 2 H ≤ C.ZI := by
  intro x hx
  have hxA := C.VHg_inf_QH_le_A hNS h13315 h1356two hH hab
    (C.UHg_le_VHg hx.1) hx.2
  have hxC : x ∈ Subgroup.centralizer (conjClosure S.V3 H : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (C.comm_DHg_UH hNS h13315 h1356two hH hab hhat hna hx hu).symm
  have h1 := S.comm_VH_HC hNS h13315 h1356two hH hx.2 hxC C.v_mem
  exact (C.dmod hNS h13315 h1356two hH hab hhat).fix_v_A hxA
    (C.V_le_ZI (((S.V1_le_V2.trans S.V2_le_V3).trans S.V3_le_V) h1))

theorem EHg_le_ZI (hna : ¬ IsElemAbelian 2 (conjClosure V H))
    (h13314 : Stmt13_3_14) : C.VHg ⊓ pCoreOf 2 H ≤ C.ZI := by
  intro x hx
  have hD := C.dmod hNS h13315 h1356two hH hab hhat
  have hxA := C.VHg_inf_QH_le_A hNS h13315 h1356two hH hab hx.1 hx.2
  have hu : (C.v : G) * x * (C.v : G)⁻¹ * x⁻¹ ∈ conjClosure S.V3 H := by
    rw [← S.comm_VH_QH_eq hNS h13315 h1356two hH h13314]
    exact Subgroup.commutator_mem_commutator C.v_mem hx.2
  have huW := C.UH_le_W hNS h13315 h1356two hH hab hu
  have hxu : ((C.v : G) * x * (C.v : G)⁻¹ * x⁻¹) * ((C.v : G) * x * (C.v : G)⁻¹ * x⁻¹)⁻¹ ∈
      C.ZI := by
    rw [mul_inv_cancel]; exact C.ZI.one_mem
  have h1 := hD.beta_eq huW hxA hxu
  set u := (C.v : G) * x * (C.v : G)⁻¹ * x⁻¹ with hu_def
  set d := ((C.v : G) * C.w * C.v)⁻¹ * u⁻¹ * ((C.v : G) * C.w * C.v) with hd_def
  have hdU : d ∈ conjSub (C.g : G)⁻¹ (conjClosure S.V3 H) := by
    rw [(C.F96_y hNS h13315 h1356two hH hab).2.2.1, mem_conjSub, inv_inv]
    have e : (C.y : G) * d * (C.y : G)⁻¹ = u⁻¹ := by rw [hd_def, y_coe]; group
    rw [e]
    exact (conjClosure S.V3 H).inv_mem hu
  have hdQ : d ∈ pCoreOf 2 H := by
    have e : d = (x * d⁻¹)⁻¹ * x := by group
    rw [e]
    exact (pCoreOf 2 H).mul_mem ((pCoreOf 2 H).inv_mem
      (S.VH_le_QH hNS h13315 h1356two hH hab (C.ZI_le_VH h1))) hx.2
  have hdZ := C.DHg_le_ZI hNS h13315 h1356two hH hab hhat hna ⟨hdU, hdQ⟩
  have e : x = (x * d⁻¹) * d := by group
  rw [e]
  exact C.ZI.mul_mem h1 hdZ

theorem A_inf_QH (hna : ¬ IsElemAbelian 2 (conjClosure V H))
    (h13314 : Stmt13_3_14) : C.A ⊓ pCoreOf 2 H = C.ZI := by
  refine le_antisymm (fun x hx => C.EHg_le_ZI hNS h13315 h1356two hH hab hhat hna h13314
    ⟨hx.1.1, hx.2⟩) (le_inf (C.ZI_le_A hNS h13315 h1356two hH hab) ?_)
  exact C.ZI_le_VH.trans (S.VH_le_QH hNS h13315 h1356two hH hab)

theorem A_eq : C.A = C.VHg ⊓ pCoreOf 2 (L ⊔ T) := by
  rw [← S.cT]
  apply le_antisymm
  · intro x hx
    exact ⟨hx.1, S.cLT_le_T hhat ⟨C.VHg_le_LT hNS h13315 h1356two hH hab hx.1, hx.2⟩, hx.2⟩
  · intro x hx
    exact ⟨hx.1, hx.2.2⟩

theorem exists_card_N : ∃ e : ℕ, Nat.card C.N = 2 ^ e := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsPGroup.iff_card.1 (C.isPGroup_N hNS h13315 h1356two hH hab hhat)

theorem rho_c3 : S.frame.ρ C.c3 = swap 4 5 * swap 3 4 := by
  obtain ⟨e, he⟩ := C.exists_card_N hNS h13315 h1356two hH hab hhat
  have h3 : (swap (4 : Fin 6) 5 * swap 3 4) ^ 3 = 1 := by decide
  rw [c3, map_pow, C.rho_r, pow_eq_pow_mod _ h3, he, two_pow_sq_mod_three, pow_one]

theorem c3_fix {x : G} (hx : x ∈ C.N)
    (hc : (C.c3 : G) * x * (C.c3 : G)⁻¹ * x⁻¹ ∈ C.ZI) : x ∈ C.ZI := by
  have hD := C.dmod hNS h13315 h1356two hH hab hhat
  obtain ⟨e, he⟩ := C.exists_card_N hNS h13315 h1356two hH hab hhat
  obtain ⟨m, hm⟩ : ∃ m, Nat.card C.N ^ 2 = 3 * m + 1 := by
    refine ⟨Nat.card C.N ^ 2 / 3, ?_⟩
    have := Nat.div_add_mod (Nat.card C.N ^ 2) 3
    rw [he, two_pow_sq_mod_three] at this
    rw [he]
    omega
  have hr3 : (C.r : G) ^ 3 ∈ C.N := C.r_cube_mem_N
  have hNF : ∀ n ∈ C.N, n ∈ DMod.fixMod C.ZI x := fun n hn =>
    ⟨C.N_le_normalizer_ZI hNS h13315 h1356two hH hab hhat hn, hD.comm n hn x hx⟩
  have hrZ : (C.r : G) ∈ Subgroup.normalizer (C.ZI : Set G) := by
    rw [r_coe]; exact Subgroup.mul_mem _ hD.vZ hD.wZ
  have hcF : (C.c3 : G) ∈ DMod.fixMod C.ZI x := by
    refine ⟨?_, hc⟩
    rw [c3_coe]
    exact Subgroup.pow_mem _ hrZ _
  have hrF : (C.r : G) ∈ DMod.fixMod C.ZI x := by
    have e1 : (C.r : G) = (((C.r : G) ^ 3) ^ m)⁻¹ * C.c3 := by
      rw [c3_coe, hm, ← pow_mul, pow_succ]
      group
    rw [e1]
    exact (DMod.fixMod C.ZI x).mul_mem
      ((DMod.fixMod C.ZI x).inv_mem (hNF _ (C.N.pow_mem hr3 m))) hcF
  exact hD.fix_r hx hrF.2

theorem nu_c3_ZI : nu (C.c3 : G) C.ZI = 4 := by
  have hVZ := C.V_le_ZI
  have hZV : C.ZI ≤ Subgroup.normalizer (V : Set G) :=
    C.ZI_le_VH.trans (S.VH_le_NV hNS h13315 h1356two hH hab)
  rw [nu_mul (C.c3 : G) hVZ (inf_le_left.trans hZV),
    relIndex_cfix_sup_eq_one (C.c3_cube) hVZ
      (by rw [S.card_V]; decide)
      (fun y hy => (Subgroup.mem_normalizer_iff.mp C.c3.2 y).mp hy)
      (fun x hx => C.c3_mod_V hNS h13315 h1356two hH hab hx),
    one_mul, nu_V C.c3 (C.rho_c3 hNS h13315 h1356two hH hab hhat)]

theorem nu_c3_N :
    nu (C.c3 : G) C.N = C.ZI.relIndex C.N * 4 := by
  have hZN : C.ZI ≤ C.N := (C.ZI_le_W hNS h13315 h1356two hH hab).trans C.W_le_N
  rw [nu_mul (C.c3 : G) hZN (inf_le_left.trans (C.N_le_normalizer_ZI hNS h13315 h1356two hH hab
    hhat)), cfix_sup_eq_of_fpf (fun x hx h => C.c3_fix hNS h13315 h1356two hH hab hhat hx h),
    C.nu_c3_ZI hNS h13315 h1356two hH hab hhat]

omit hab in
theorem cLT_le_normalizer_N :
    (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (C.N : Set G) := by
  refine A5.le_normalizer_of_forall_conj_mem fun q hq x hx => ⟨?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp
      (C.cLT_le_normalizer_I hNS h13315 h1356two hH hhat hq) x).mp hx.1
  · exact A5.conj_mem_centralizer_of_mem_normalizer (S.frame.T_le (S.cLT_le_T hhat hq)) hx.2

theorem nu_c3_Q_N :
    nu (C.c3 : G) ((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) = nu (C.c3 : G) C.N := by
  have hNQ := C.N_le_cLT hNS h13315 h1356two hH hab
  have hc3I := C.c3_mem_I
  have hcN : ∀ n ∈ C.N, (C.c3 : G) * n * (C.c3 : G)⁻¹ ∈ C.N := by
    intro n hn
    refine ⟨C.I.mul_mem (C.I.mul_mem hc3I hn.1) (C.I.inv_mem hc3I), ?_⟩
    exact A5.conj_mem_centralizer_of_mem_normalizer C.c3.2 hn.2
  have h3 : ¬ 3 ∣ Nat.card C.N := by
    obtain ⟨e, he⟩ := C.exists_card_N hNS h13315 h1356two hH hab hhat
    rw [he]
    intro h
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
    omega
  have hcX : ∀ q ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G),
      q⁻¹ * ((C.c3 : G) * q * (C.c3 : G)⁻¹) ∈ C.N := by
    intro q hq
    have hqI := C.cLT_le_normalizer_I hNS h13315 h1356two hH hhat
      (((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)).inv_mem hq)
    have h1 : q⁻¹ * C.c3 * q⁻¹⁻¹ ∈ C.I := (Subgroup.mem_normalizer_iff.mp hqI _).mp hc3I
    refine ⟨?_, ?_⟩
    · have e : q⁻¹ * ((C.c3 : G) * q * (C.c3 : G)⁻¹) = (q⁻¹ * C.c3 * q⁻¹⁻¹) * (C.c3 : G)⁻¹ := by
        group
      rw [e]
      exact C.I.mul_mem h1 (C.I.inv_mem hc3I)
    · exact (Subgroup.centralizer (V : Set G)).mul_mem
        ((Subgroup.centralizer (V : Set G)).inv_mem hq.2)
        (A5.conj_mem_centralizer_of_mem_normalizer C.c3.2 hq.2)
  rw [nu_mul (C.c3 : G) hNQ (inf_le_left.trans (C.cLT_le_normalizer_N hNS h13315 h1356two hH
    hhat)), relIndex_cfix_sup_eq_one (C.c3_cube) hNQ h3 hcN hcX,
    one_mul]

theorem A_eq_conj : C.A = conjSub (C.y : G)⁻¹ C.W := by
  have hD := C.dmod hNS h13315 h1356two hH hab hhat
  ext x
  rw [mem_conjSub, inv_inv]
  constructor
  · intro hx
    exact hD.yA x hx
  · intro hx
    have := hD.yW _ hx
    have e : ((C.v : G) * C.w * C.v)⁻¹ * ((C.y : G) * x * (C.y : G)⁻¹) * ((C.v : G) * C.w * C.v) =
        x := by rw [y_coe]; group
    rwa [e] at this

theorem relIndex_ZI_N :
    C.ZI.relIndex C.N = (C.ZI.relIndex C.A) ^ 2 := by
  have hD := C.dmod hNS h13315 h1356two hH hab hhat
  have hWA : C.W ⊓ C.A = C.ZI :=
    le_antisymm (fun x hx => hD.WA x hx.1 hx.2) (le_inf hD.ZW hD.ZA)
  have hcardWA : Nat.card C.W = Nat.card C.A := by
    rw [C.A_eq_conj hNS h13315 h1356two hH hab hhat, A5.card_conjSub']
  have hprod := card_sup_mul_card_inf' (C.W_le_normalizer_A hNS h13315 h1356two hH hab hhat)
  rw [← C.N_eq hNS h13315 h1356two hH hab hhat, hWA, hcardWA] at hprod
  have r1 := Subgroup.relIndex_mul_card C.ZI C.N
  have r2 := Subgroup.relIndex_mul_card C.ZI C.A
  rw [inf_eq_left.2 (hD.ZW.trans hD.WN)] at r1
  rw [inf_eq_left.2 hD.ZA] at r2
  have hpos : 0 < Nat.card C.ZI := Nat.card_pos
  have key : C.ZI.relIndex C.N * (Nat.card C.ZI * Nat.card C.ZI) =
      (C.ZI.relIndex C.A) ^ 2 * (Nat.card C.ZI * Nat.card C.ZI) := by
    calc C.ZI.relIndex C.N * (Nat.card C.ZI * Nat.card C.ZI)
        = (C.ZI.relIndex C.N * Nat.card C.ZI) * Nat.card C.ZI := by ring
      _ = Nat.card C.A * Nat.card C.A := by rw [r1, hprod]
      _ = (C.ZI.relIndex C.A * Nat.card C.ZI) * (C.ZI.relIndex C.A * Nat.card C.ZI) := by
          rw [r2]
      _ = (C.ZI.relIndex C.A) ^ 2 * (Nat.card C.ZI * Nat.card C.ZI) := by ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hpos hpos) key

theorem nu_cQ :
    nu (C.c3 : G) ((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) =
      4 * (C.ZI.relIndex C.A) ^ 2 := by
  rw [C.nu_c3_Q_N hNS h13315 h1356two hH hab hhat, C.nu_c3_N hNS h13315 h1356two hH hab hhat,
    C.relIndex_ZI_N hNS h13315 h1356two hH hab hhat, mul_comm]

omit hhat in
theorem c3_mem_L : (C.c3 : G) ∈ L := by
  have hcLT : (C.c3 : G) ∈ L ⊔ T := C.I_le_LT hNS h13315 h1356two hH hab C.c3_mem_I
  have hx : (C.c3 : G) ∈ ((L : Set G) * (T : Set G)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left L T S.T_le_NL]
    exact hcLT
  obtain ⟨l, hl, t, ht, hlt⟩ := Set.mem_mul.mp hx
  obtain ⟨a, ha⟩ := S.h13.sylow.1 ⟨t, ht⟩
  have hta : t ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
  obtain ⟨l', hl', he⟩ := A5.pow_mem_mul_of_normalizes hl (S.T_le_NL ht) (2 ^ a)
  rw [hta, mul_one, hlt] at he
  have h3 := C.c3_cube
  have h4 : (C.c3 : G) = ((C.c3 : G) ^ 2 ^ a) ^ 2 ^ a := by
    rw [← pow_mul, ← mul_pow, show (2 * 2 : ℕ) = 4 by norm_num, pow_eq_pow_mod _ h3,
      Nat.pow_mod]
    norm_num
  rw [h4, he]
  exact L.pow_mem hl' _

theorem exists_c1 :
    ∃ c₁ : ↥(Subgroup.normalizer (V : Set G)), (c₁ : G) ∈ S.L1 ∧ (c₁ : G) ^ 3 = 1 ∧
      S.frame.ρ c₁ = swap 0 1 * swap 1 2 ∧
      nu (c₁ : G) ((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) =
        nu (C.c3 : G) ((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) := by
  obtain ⟨l, hlL, hρl⟩ := (S.frame.image_L _).2 conj_354_012.1
  refine ⟨l * C.c3 * l⁻¹, ?_, ?_, ?_, ?_⟩
  ·
    have hρ : S.frame.ρ (l * C.c3 * l⁻¹) = swap 0 1 * swap 1 2 := by
      rw [map_mul, map_mul, map_inv, hρl, C.rho_c3 hNS h13315 h1356two hH hab hhat]
      exact conj_354_012.2
    have hc1L : ((l * C.c3 * l⁻¹ : ↥(Subgroup.normalizer (V : Set G))) : G) ∈ L := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact L.mul_mem (L.mul_mem hlL (C.c3_mem_L hNS h13315 h1356two hH hab)) (L.inv_mem hlL)
    have hfix := fix_e0123_of (S.frame.ρ (l * C.c3 * l⁻¹)) (by rw [hρ]; exact c012_fix45.1)
      (by rw [hρ]; exact c012_fix45.2)
    have hz : ((l * C.c3 * l⁻¹ : ↥(Subgroup.normalizer (V : Set G))) : G) * S.z *
        ((l * C.c3 * l⁻¹ : ↥(Subgroup.normalizer (V : Set G))) : G)⁻¹ = S.z := by
      refine (S.conj_eq_iff _ ⟨S.z, S.z_mem_V⟩).2 ?_
      rw [S.psi_z]
      exact Subtype.ext hfix
    have hN : ((l * C.c3 * l⁻¹ : ↥(Subgroup.normalizer (V : Set G))) : G) ∈
        Subgroup.normalizer (fsuV1 T V : Set G) := by
      rw [S.normalizer_V1, Subgroup.mem_centralizer_singleton_iff]
      calc ((l * C.c3 * l⁻¹ : ↥(Subgroup.normalizer (V : Set G))) : G) * S.z =
          ((l * C.c3 * l⁻¹ : ↥(Subgroup.normalizer (V : Set G))) : G) * S.z *
            ((l * C.c3 * l⁻¹ : ↥(Subgroup.normalizer (V : Set G))) : G)⁻¹ *
              ((l * C.c3 * l⁻¹ : ↥(Subgroup.normalizer (V : Set G))) : G) := by group
        _ = S.z * ((l * C.c3 * l⁻¹ : ↥(Subgroup.normalizer (V : Set G))) : G) := by rw [hz]
    refine Subgroup.subset_closure ⟨⟨hc1L, hN⟩, 3, by decide, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [conj_pow, C.c3_cube]
    group
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [conj_pow, C.c3_cube]
    group
  · rw [map_mul, map_mul, map_inv, hρl, C.rho_c3 hNS h13315 h1356two hH hab hhat]
    exact conj_354_012.2
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact nu_conj (S.le_normalizer_cLT (le_sup_left (a := L) hlL))

end Hat

end Conf

end NonAb

variable (S)

theorem rho_O2L1_mem_K4 {x : G} (hx : x ∈ pCoreOf 2 S.L1)
    (hxN : x ∈ Subgroup.normalizer (V : Set G)) : S.frame.ρ ⟨x, hxN⟩ ∈ K4L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h4, h5, hs⟩ := S.rho_L1 (g := ⟨x, hxN⟩) (pCoreOf_le 2 S.L1 hx)
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 S.L1 ⟨x, hx⟩
  have hk' : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hρk : S.frame.ρ ⟨x, hxN⟩ ^ 2 ^ k = 1 := by
    rw [← map_pow]
    have e : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (V : Set G))) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using hk')
    rw [e, map_one]
  exact mem_K4L _ h4 h5 hs (pow_four_of_pow_two_pow hρk)

@[expose] noncomputable def rhoO2L1 : ↥(pCoreOf 2 S.L1) →* Perm (Fin 6) :=
  S.frame.ρ.comp (Subgroup.inclusion
    ((pCoreOf_le 2 S.L1).trans (S.L1_le_L.trans S.frame.L_le)))

theorem relIndex_O2L1_eq :
    (pCoreOf 2 S.L1 ⊓ ((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G))).relIndex (pCoreOf 2 S.L1) =
      Nat.card S.rhoO2L1.range := by
  have hL1LT : S.L1 ≤ L ⊔ T := S.L1_le_L.trans le_sup_left
  have hker : (pCoreOf 2 S.L1 ⊓ ((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G))).subgroupOf
      (pCoreOf 2 S.L1) = S.rhoO2L1.ker := by
    ext x
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    constructor
    · intro hx
      exact (S.rho_eq_one_iff _).2 hx.2.2
    · intro hx
      exact ⟨x.2, hL1LT (pCoreOf_le 2 S.L1 x.2), (S.rho_eq_one_iff _).1 hx⟩
  have h1 : S.rhoO2L1.ker.index = Nat.card S.rhoO2L1.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange S.rhoO2L1).toEquiv
  rw [Subgroup.relIndex, hker, h1]

theorem relIndex_O2L1_le :
    (pCoreOf 2 S.L1 ⊓ ((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G))).relIndex (pCoreOf 2 S.L1) ≤
      4 := by
  have hrange : S.rhoO2L1.range ≤ K4sub := by
    intro y hy
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hy
    exact S.rho_O2L1_mem_K4 x.2 _
  rw [S.relIndex_O2L1_eq]
  exact (Subgroup.card_le_of_le hrange).trans card_K4sub.le

theorem nu_O2L1_eq_mul (hhat : ¬ IsHatA6 L)
    (c₁ : ↥(Subgroup.normalizer (V : Set G))) (hc₁ : (c₁ : G) ∈ S.L1) (h3 : (c₁ : G) ^ 3 = 1)
    (hρ : S.frame.ρ c₁ = swap 0 1 * swap 1 2) :
    nu (c₁ : G) (pCoreOf 2 S.L1) =
      (pCoreOf 2 S.L1 ⊓ ((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G))).relIndex
        (pCoreOf 2 S.L1) * nu (c₁ : G) ((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) with hQ
  set O := pCoreOf 2 S.L1 with hO
  have hOL1 : O ≤ S.L1 := pCoreOf_le 2 S.L1
  have hL1LT : S.L1 ≤ L ⊔ T := S.L1_le_L.trans le_sup_left
  have hON : O ≤ Subgroup.normalizer (V : Set G) := hOL1.trans (S.L1_le_L.trans S.frame.L_le)
  have hQT : Q ≤ T := S.cLT_le_T hhat
  have hQL1 : Q ≤ Subgroup.normalizer (S.L1 : Set G) := hQT.trans S.T_le_normalizer_L1
  have hQO : Q ≤ Subgroup.normalizer (O : Set G) :=
    hQL1.trans (normalizer_le_normalizer_pCoreOf 2 S.L1)
  have hc₁LT : (c₁ : G) ∈ L ⊔ T := hL1LT hc₁
  have hc₁Q : (c₁ : G) ∈ Subgroup.normalizer (Q : Set G) := S.le_normalizer_cLT hc₁LT
  have hc₁O : (c₁ : G) ∈ Subgroup.normalizer (O : Set G) := le_normalizer_pCoreOf 2 S.L1 hc₁
  have hL1Q : S.L1 ⊓ Q ≤ O := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
      (S.h13.sylow.1.to_le (inf_le_right.trans hQT))
    refine A5.le_normalizer_of_forall_conj_mem fun l hl x hx => ⟨?_, ?_⟩
    · exact S.L1.mul_mem (S.L1.mul_mem hl hx.1) (S.L1.inv_mem hl)
    · exact (Subgroup.mem_normalizer_iff.mp (S.le_normalizer_cLT (hL1LT hl)) x).mp hx.2
  set Y := O ⊓ Q with hY
  have hYO : Y ≤ O := inf_le_left
  have hYQ : Y ≤ Q := inf_le_right
  have hY2 : ¬ 3 ∣ Nat.card Y := by
    obtain ⟨e, he⟩ := IsPGroup.iff_card.1 (S.h13.sylow.1.to_le (hYQ.trans hQT))
    rw [he]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  have hcY : ∀ y ∈ Y, (c₁ : G) * y * (c₁ : G)⁻¹ ∈ Y := fun y hy =>
    ⟨(Subgroup.mem_normalizer_iff.mp hc₁O y).mp hy.1,
      (Subgroup.mem_normalizer_iff.mp hc₁Q y).mp hy.2⟩
  have hνQ : nu (c₁ : G) Q = nu (c₁ : G) Y := by
    have hN : cfix (c₁ : G) Q ≤ Subgroup.normalizer (Y : Set G) := by
      intro q hq
      have hq1 := hQO hq.1
      have hq2 : q ∈ Subgroup.normalizer (Q : Set G) := Subgroup.le_normalizer hq.1
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨(Subgroup.mem_normalizer_iff.mp hq1 y).mp h1,
          (Subgroup.mem_normalizer_iff.mp hq2 y).mp h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨(Subgroup.mem_normalizer_iff.mp hq1 y).mpr h1,
          (Subgroup.mem_normalizer_iff.mp hq2 y).mpr h2⟩
    have hcX : ∀ q ∈ Q, q⁻¹ * ((c₁ : G) * q * (c₁ : G)⁻¹) ∈ Y := by
      intro q hq
      have h1 : q⁻¹ * c₁ * q⁻¹⁻¹ ∈ S.L1 :=
        (Subgroup.mem_normalizer_iff.mp (hQL1 (Q.inv_mem hq)) _).mp hc₁
      have hmem : q⁻¹ * ((c₁ : G) * q * (c₁ : G)⁻¹) ∈ S.L1 ⊓ Q := by
        refine ⟨?_, Q.mul_mem (Q.inv_mem hq) ((Subgroup.mem_normalizer_iff.mp hc₁Q q).mp hq)⟩
        have e : q⁻¹ * ((c₁ : G) * q * (c₁ : G)⁻¹) = (q⁻¹ * c₁ * q⁻¹⁻¹) * (c₁ : G)⁻¹ := by group
        rw [e]
        exact S.L1.mul_mem h1 (S.L1.inv_mem hc₁)
      exact ⟨hL1Q hmem, hmem.2⟩
    rw [nu_mul (c₁ : G) hYQ hN, relIndex_cfix_sup_eq_one h3 hYQ hY2 hcY hcX, one_mul]
  have hN' : cfix (c₁ : G) O ≤ Subgroup.normalizer (Y : Set G) := by
    intro x hx
    have hx1 : x ∈ Subgroup.normalizer (O : Set G) := Subgroup.le_normalizer hx.1
    have hx2 : x ∈ Subgroup.normalizer (Q : Set G) := S.le_normalizer_cLT (hL1LT (hOL1 hx.1))
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp hx1 y).mp h1,
        (Subgroup.mem_normalizer_iff.mp hx2 y).mp h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp hx1 y).mpr h1,
        (Subgroup.mem_normalizer_iff.mp hx2 y).mpr h2⟩
  have hK : ∀ x (hx : x ∈ O), S.frame.ρ ⟨x, hON hx⟩ ∈ K4L := fun x hx =>
    S.rho_O2L1_mem_K4 hx (hON hx)
  have hfp : ∀ x ∈ O, (c₁ : G) * x * (c₁ : G)⁻¹ * x⁻¹ ∈ Y → x ∈ Y := by
    intro x hx h
    have hxN := hON hx
    have h1 : S.frame.ρ (c₁ * ⟨x, hxN⟩ * c₁⁻¹ * (⟨x, hxN⟩)⁻¹) = 1 := (S.rho_eq_one_iff _).2 h.2.2
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hρ] at h1
    have h2 : (swap 0 1 * swap 1 2) * S.frame.ρ ⟨x, hxN⟩ * (swap 0 1 * swap 1 2)⁻¹ =
        S.frame.ρ ⟨x, hxN⟩ := by
      calc (swap 0 1 * swap 1 2) * S.frame.ρ ⟨x, hxN⟩ * (swap 0 1 * swap 1 2)⁻¹ =
          (swap 0 1 * swap 1 2) * S.frame.ρ ⟨x, hxN⟩ * (swap 0 1 * swap 1 2)⁻¹ *
            (S.frame.ρ ⟨x, hxN⟩)⁻¹ * S.frame.ρ ⟨x, hxN⟩ := by group
        _ = S.frame.ρ ⟨x, hxN⟩ := by rw [h1, one_mul]
    have h3' := K4L_fix_012 _ (hK x hx) h2
    have hxC := (S.rho_eq_one_iff ⟨x, hxN⟩).1 h3'
    exact ⟨hx, hL1LT (hOL1 hx), hxC⟩
  rw [nu_mul (c₁ : G) hYO hN', cfix_sup_eq_of_fpf hfp, ← hνQ]

theorem nu_O2L1_le (hhat : ¬ IsHatA6 L)
    (c₁ : ↥(Subgroup.normalizer (V : Set G))) (hc₁ : (c₁ : G) ∈ S.L1) (h3 : (c₁ : G) ^ 3 = 1)
    (hρ : S.frame.ρ c₁ = swap 0 1 * swap 1 2) :
    nu (c₁ : G) (pCoreOf 2 S.L1) ≤
      4 * nu (c₁ : G) ((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) := by
  rw [S.nu_O2L1_eq_mul hhat c₁ hc₁ h3 hρ]
  exact Nat.mul_le_mul_right _ S.relIndex_O2L1_le

end Setting4

end CFSG.Quasithin.H13.A6
