module

public import CFSG.Quasithin.H13.L32ALevi7
public import CFSG.Quasithin.H13.A6S1372Mod
public import CFSG.Quasithin.H13.L32ALevi6

public section

namespace CFSG.Quasithin.H13.L32A.C.Levi

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Quasithin.H13.L32A.C.Alt6 (conjK conjK_apply)
open scoped IsMulCommutative

variable {G : Type} [Group G] {T L V H K V₁ : Subgroup G} {πK : ↥K →* Lin.SLn 4} {a c x : G}

namespace HSide

abbrev Q (V H V₁ : Subgroup G) [IsMulCommutative ↥(conjClosure V H)] : Type :=
  Sec (⊤ : Subgroup ↥(conjClosure V H)) (V₁.subgroupOf (conjClosure V H))

@[expose] noncomputable def cl [IsMulCommutative ↥(conjClosure V H)] (u : ↥(conjClosure V H)) :
    Q V H V₁ :=
  InternalSec.secMk (V₁.subgroupOf (conjClosure V H)) u

theorem cl_eq_iff [IsMulCommutative ↥(conjClosure V H)] (u u' : ↥(conjClosure V H)) :
    (cl u : Q V H V₁) = cl u' ↔ (u : G) * (u' : G)⁻¹ ∈ V₁ := by
  rw [cl, cl, ← mul_inv_eq_one, ← map_inv, ← map_mul, A6.A6Mod.secMk_eq_one_iff]
  rfl

variable (C : HSide T L V H K V₁ πK a c x) [IsMulCommutative ↥(conjClosure V H)]
include C

omit [IsMulCommutative ↥(conjClosure V H)] in
theorem hHUV₁ : H ≤ Subgroup.normalizer ((conjClosure V H ⊓ V₁ : Subgroup G) : Set G) := by
  rw [inf_eq_right.mpr C.hV₁U]
  exact C.hHV₁

@[expose] noncomputable def ρ : ↥H →* MulAut (Q V H V₁) :=
  A6.A6Mod.secAct (le_normalizer_conjClosure V H) C.hHUV₁

@[expose] noncomputable def aT : Q V H V₁ := cl ⟨a, C.ha⟩

@[expose] noncomputable def kK (g : Lin.SLn 4) : ↥K := Classical.choose (C.hπs g)

omit [IsMulCommutative ↥(conjClosure V H)] in
theorem piK_kK (g : Lin.SLn 4) : πK (C.kK g) = g := Classical.choose_spec (C.hπs g)

@[expose] noncomputable def kH (g : Lin.SLn 4) : ↥H := ⟨C.kK g, C.hKH (C.kK g).2⟩

@[expose] noncomputable def model : Model (Q V H V₁) ↥H := ⟨C.ρ, C.β, fun g => C.ρ (C.kH g) C.aT⟩

theorem ρ_cl (h : ↥H) (u : ↥(conjClosure V H)) :
    C.ρ h (cl u) = cl (V₁ := V₁) ⟨(h : G) * u * (h : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V H h.2) u).mp u.2⟩ := rfl

theorem ρ_eq_one {h : ↥H} (hh : (h : G) ∈ pCoreOf 2 H) : C.ρ h = 1 := by
  rw [ρ, A6.A6Mod.secAct_eq_one_iff]
  exact C.hO _ hh

theorem ρ_aT_iff (h : ↥H) : C.ρ h C.aT = C.aT ↔ (h : G) * a * (h : G)⁻¹ * a⁻¹ ∈ V₁ := by
  rw [aT, ρ_cl, cl_eq_iff]

theorem ρ_eq_of_piK {k k' : G} (hk : k ∈ K) (hk' : k' ∈ K) (he : πK ⟨k, hk⟩ = πK ⟨k', hk'⟩) :
    C.ρ ⟨k, C.hKH hk⟩ = C.ρ ⟨k', C.hKH hk'⟩ := by
  have h1 := C.ρ_eq_one (h := ⟨k', C.hKH hk'⟩⁻¹ * ⟨k, C.hKH hk⟩) (C.eq_of_piK hk hk' he)
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1.symm

theorem kH_mul (g w : Lin.SLn 4) : C.ρ (C.kH (g * w)) = C.ρ (C.kH g * C.kH w) := by
  have := C.ρ_eq_of_piK (C.kK (g * w)).2 (K.mul_mem (C.kK g).2 (C.kK w).2) (by
    show πK (C.kK (g * w)) = πK (C.kK g * C.kK w)
    rw [map_mul, C.piK_kK, C.piK_kK, C.piK_kK])
  exact this

theorem sq_Q (q : Q V H V₁) : q * q = 1 := by
  obtain ⟨u, rfl⟩ := InternalSec.secMk_surjective (V₁.subgroupOf (conjClosure V H)) q
  rw [← map_mul, A6.A6Mod.secMk_eq_one_iff]
  have h1 : (u : G) * u = 1 := by
    have := C.hU.2 u u.2
    rwa [pow_two] at this
  rw [Subgroup.coe_mul, h1]
  exact V₁.one_mem

theorem model_φ (g : Lin.SLn 4) : C.model.φ g = C.ρ (C.kH g) C.aT := rfl

theorem model_ρ : C.model.ρ = C.ρ := rfl

theorem model_β : C.model.β = C.β := rfl

theorem ρ_T_aT {t : G} (ht : t ∈ T) : C.ρ ⟨t, C.hTH ht⟩ C.aT = C.aT :=
  (C.ρ_aT_iff _).mpr (C.hTa t ht)

theorem ρ_kH_U {u : Lin.SLn 4} (hu : u ∈ unitriangular 4 (ZMod 2)) : C.ρ (C.kH u) C.aT = C.aT := by
  have hT : (C.kK u : G) ∈ T := C.fix_of_piK_mem (C.kK u).2 (by
    show πK (C.kK u) ∈ _
    rw [C.piK_kK]
    exact hu)
  exact C.ρ_T_aT hT

theorem model_right (g u : Lin.SLn 4) (hu : u ∈ unitriangular 4 (ZMod 2)) :
    C.model.φ (g * u) = C.model.φ g := by
  rw [model_φ, model_φ, C.kH_mul, map_mul, MulAut.mul_apply, C.ρ_kH_U hu]

theorem ρ_kH_eq {g : Lin.SLn 4} {k : G} (hk : k ∈ K) (he : πK ⟨k, hk⟩ = g) :
    C.ρ (C.kH g) = C.ρ ⟨k, C.hKH hk⟩ :=
  C.ρ_eq_of_piK (C.kK g).2 hk (by
    show πK (C.kK g) = _
    rw [C.piK_kK, he])

theorem ρ_x_aT : C.ρ ⟨x, C.hKH (C.hl1K C.hx)⟩ C.aT = cl ⟨c, C.hc⟩ := by
  rw [aT, ρ_cl]
  congr 1
  exact Subtype.ext C.hxa

theorem ρ_x2_aT : C.ρ ⟨x, C.hKH (C.hl1K C.hx)⟩ (cl ⟨c, C.hc⟩) =
    cl (V₁ := V₁) ⟨a * c, (conjClosure V H).mul_mem C.ha C.hc⟩ := by
  rw [ρ_cl]
  congr 1
  exact Subtype.ext C.hxc

theorem phi_lam : C.model.φ (πK ⟨x, C.hl1K C.hx⟩) = cl ⟨c, C.hc⟩ := by
  rw [model_φ, C.ρ_kH_eq (C.hl1K C.hx) rfl, ρ_x_aT]

theorem phi_lam2 : C.model.φ (πK ⟨x, C.hl1K C.hx⟩ ^ 2) =
    cl (V₁ := V₁) ⟨a * c, (conjClosure V H).mul_mem C.ha C.hc⟩ := by
  rw [model_φ, pow_two, C.kH_mul, map_mul, MulAut.mul_apply, C.ρ_kH_eq (C.hl1K C.hx) rfl,
    ρ_x_aT, ρ_x2_aT]

theorem line_aT : C.aT * cl ⟨c, C.hc⟩ *
    cl (V₁ := V₁) ⟨a * c, (conjClosure V H).mul_mem C.ha C.hc⟩ = 1 := by
  rw [aT, cl, cl, cl, ← map_mul, ← map_mul, A6.A6Mod.secMk_eq_one_iff]
  show a * c * (a * c) ∈ V₁
  have : a * c * (a * c) = 1 := by
    have := C.hU.2 (a * c) ((conjClosure V H).mul_mem C.ha C.hc)
    rwa [pow_two] at this
  rw [this]
  exact V₁.one_mem

theorem model_line (g : Lin.SLn 4) :
    C.model.φ g * C.model.φ (g * R2) * C.model.φ (g * M2) = 1 := by
  have hR : C.model.φ R2 * C.model.φ M2 =
      cl ⟨c, C.hc⟩ * cl (V₁ := V₁) ⟨a * c, (conjClosure V H).mul_mem C.ha C.hc⟩ := by
    rcases C.lam_cases with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [← phi_lam, ← phi_lam2, ← C.model_right R2 _ h1, ← C.model_right M2 _ h2,
        mul_inv_cancel_left, mul_inv_cancel_left]
    · rw [← phi_lam, ← phi_lam2, ← C.model_right R2 _ h2, ← C.model_right M2 _ h1,
        mul_inv_cancel_left, mul_inv_cancel_left, mul_comm]
  have e1 : ∀ w, C.model.φ (g * w) = C.ρ (C.kH g) (C.model.φ w) := fun w => by
    rw [model_φ, model_φ, C.kH_mul, map_mul, MulAut.mul_apply]
  rw [e1, e1, show C.model.φ g = C.ρ (C.kH g) C.aT from rfl, mul_assoc, ← map_mul, ← map_mul, hR,
    ← mul_assoc, line_aT, map_one]

theorem model_ne1 (g : Lin.SLn 4) : C.model.φ g ≠ 1 := by
  rw [model_φ]
  intro h
  rw [MulEquiv.map_eq_one_iff, aT, cl, A6.A6Mod.secMk_eq_one_iff] at h
  exact C.haV₁ h

theorem model_ker (h : ↥H) (hh : C.model.β h = 1) : C.model.ρ h = 1 :=
  C.ρ_eq_one (C.β_ker hh)

theorem model_inner (v : Lin.SLn 4) : ∃ γ, C.model.β γ = autOf v false := by
  refine ⟨C.kH v, ?_⟩
  rw [model_β, kH, C.β_K (C.kK v).2, show (⟨(C.kK v : G), (C.kK v).2⟩ : ↥K) = C.kK v from rfl,
    C.piK_kK]

theorem model_eqv (γ : ↥H) (v : Lin.SLn 4) (e : Bool) (hγ : C.model.β γ = autOf v e)
    (g : Lin.SLn 4) : C.model.ρ γ (C.model.φ g) = C.model.φ (mact v e g) := by
  rw [model_β] at hγ
  rw [model_ρ, model_φ]
  obtain ⟨k, hk, t, ht, hkt⟩ := C.hdec γ γ.2
  obtain ⟨u, hu, e', he'⟩ := C.β_T ht
  have hγ' : γ = ⟨k, C.hKH hk⟩ * ⟨t, C.hTH ht⟩ := Subtype.ext hkt
  have hβ' : C.β (⟨k, C.hKH hk⟩ * ⟨t, C.hTH ht⟩) = autOf (πK ⟨k, hk⟩ * u) e' := by
    rw [map_mul, C.β_K hk, he', autOf_mul, Bool.false_xor]
    rfl
  have hβ : C.β γ = autOf (πK ⟨k, hk⟩ * u) e' := hγ' ▸ hβ'
  obtain ⟨hv, rfl⟩ := autOf_inj (hγ.symm.trans hβ)
  have hmK : (γ : G) * (C.kK g : G) * (γ : G)⁻¹ * k ∈ K :=
    K.mul_mem (conjK (C.hKn γ.2) (C.kK g)).2 hk
  have hmγ : C.ρ (γ * C.kH g) C.aT = C.ρ ⟨_, C.hKH hmK⟩ C.aT := by
    have e1 : γ * C.kH g = ⟨_, C.hKH hmK⟩ * ⟨t, C.hTH ht⟩ := by
      apply Subtype.ext
      show (γ : G) * (C.kK g : G) = (γ : G) * (C.kK g : G) * (γ : G)⁻¹ * k * t
      rw [mul_assoc _ k t, ← hkt]
      group
    rw [e1, map_mul, MulAut.mul_apply, C.ρ_T_aT ht]
  have hπm : πK ⟨_, hmK⟩ = mact v e g * u⁻¹ := by
    have e2 : (⟨_, hmK⟩ : ↥K) = conjK (C.hKn γ.2) (C.kK g) * ⟨k, hk⟩ := Subtype.ext (by
      rw [Subgroup.coe_mul, conjK_apply])
    rw [e2, map_mul, ← C.β_apply, C.piK_kK, hγ, autOf_apply, mact_eq, hv]
    group
  rw [← MulAut.mul_apply, ← map_mul, hmγ, ← C.ρ_kH_eq hmK hπm, ← model_φ,
    C.model_right _ _ (inv_mem hu)]

theorem hyp (hbad : ∀ h ∈ H, h * a * h⁻¹ * a⁻¹ ∈ V₁ → h ∈ T) : C.model.Hyp where
  sq := C.sq_Q
  right := C.model_right
  inj := by
    intro g g' h
    rw [model_φ, model_φ] at h
    have h2 : C.ρ ((C.kH g)⁻¹ * C.kH g') C.aT = C.aT := by
      rw [map_mul, MulAut.mul_apply, ← h, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel,
        map_one, MulAut.one_apply]
    have hT := hbad _ ((C.kH g)⁻¹ * C.kH g').2 ((C.ρ_aT_iff _).mp h2)
    have hK : (((C.kH g)⁻¹ * C.kH g' : ↥H) : G) ∈ K :=
      K.mul_mem (K.inv_mem (C.kK g).2) (C.kK g').2
    have := C.mem_T_K hT hK
    have e : πK ⟨_, hK⟩ = g⁻¹ * g' := by
      show πK ((C.kK g)⁻¹ * C.kK g') = _
      rw [map_mul, map_inv, C.piK_kK, C.piK_kK]
    rwa [e] at this
  line := C.model_line
  eqv := C.model_eqv
  ne1 := C.model_ne1
  ker := C.model_ker
  inner := C.model_inner

end HSide

end CFSG.Quasithin.H13.L32A.C.Levi
