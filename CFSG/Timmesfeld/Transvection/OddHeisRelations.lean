module

public import CFSG.Timmesfeld.Transvection.OddHeisFrameBasics
public import CFSG.Timmesfeld.Transvection.RelBuildField
public import Certificates.Certificate43
public import Certificates.Certificate82
public import Certificates.Certificate83
public import Certificates.Certificate84
public import Certificates.Certificate85
public import Certificates.Certificate86
public import Certificates.Certificate87
public import Certificates.Certificate88
public import Certificates.Certificate89
public import Certificates.Certificate90
public import Certificates.Certificate91
public import Certificates.Certificate92
public import Certificates.Certificate93
public import Certificates.Certificate94
public import Certificates.Certificate95
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import CFSG.Timmesfeld.Transvection.OddTranslationsMeet
import CFSG.Timmesfeld.Transvection.OddNormalize
import CFSG.Timmesfeld.Transvection.OddPairsFrame
import CFSG.Timmesfeld.Transvection.OddBC2Comm
import CFSG.Timmesfeld.Transvection.OddModelShortTorus
import CFSG.Timmesfeld.Transvection.OddHeisAut
import CFSG.LinearAlgebra.LinearGroups.CoordinateData
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
import CFSG.Permutation.BurnsideSchur
import CFSG.Timmesfeld.Moufang.Three
import CFSG.Timmesfeld.Transvection.OddResidueBlock

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.Timmesfeld.Transvection.Pres CFSG.LocalAnalysis.UniquenessCase
open CFSG.LieType.Universal.Unitary.SUExtras (toStd_last_odd)
open CFSG.LieType.Universal.Symplectic.SpExtras (wt)
open scoped commutatorElement

section Algebra

variable {F : Type*} [Field F] {σ : F ≃+* F} {H : Type*} [Group H]

private abbrev HV (σ : F ≃+* F) (u v : F) : Prop := v + σ v + σ u * u = 0

private structure HeisAlg (σ : F ≃+* F) (X X' : F → F → H) : Prop where
  invol : ∀ c, σ (σ c) = c
  nonfix : ∃ a, σ a ≠ a
  X_mul : ∀ u v u' v', HV σ u v → HV σ u' v' →
    X u v * X u' v' = X (u + u') (v + v' + u * σ u')
  X'_mul : ∀ u v u' v', HV σ u v → HV σ u' v' →
    X' u v * X' u' v' = X' (u + u') (v + v' + u * σ u')
  X'_inj : ∀ u v u' v', HV σ u v → HV σ u' v' → X' u v = X' u' v' → u = u' ∧ v = v'

private structure HeisRel (σ : F ≃+* F) (X X' : F → F → H) (y z : F → H) : Prop where
  y_add : ∀ s t, y (s + t) = y s * y t
  z_add : ∀ s t, z (s + t) = z s * z t
  z_inj : ∀ s t, z s = z t → s = t
  trace : ∀ s t, ⁅y s, z t⁆ = X' 0 (s * σ t + σ s * t)
  shortLong : ∀ s c, σ c = c → ⁅y s, X 0 c⁆ = z (s * c) * X' 0 (σ s * s * c)

private structure HeisComm (σ : F ≃+* F) (X X' : F → F → H) (y z : F → H) : Prop where
  yX' : ∀ s a b, Commute (y s) (X' a b)
  zX' : ∀ w a b, Commute (z w) (X' a b)
  zX : ∀ w a b, Commute (z w) (X a b)
  lX' : ∀ c, σ c = c → ∀ a b, Commute (X 0 c) (X' a b)
  l'X : ∀ c, σ c = c → ∀ a b, Commute (X' 0 c) (X a b)

private structure HeisMem (σ : F ≃+* F) (X X' : F → F → H) (z : F → H) : Prop where
  comm_mem : ∀ u v u' v', HV σ u v → HV σ u' v' → ∃ w, ⁅X u v, X' u' v'⁆ = z w
  unique : ∀ a b a' b' w w', HV σ a b → HV σ a' b' →
    X' a b * z w = X' a' b' * z w' → X' a b = X' a' b'

private structure HeisCtx (σ : F ≃+* F) (X X' : F → F → H) (y z : F → H) : Prop
    extends HeisAlg σ X X', HeisRel σ X X' y z, HeisComm σ X X' y z, HeisMem σ X X' z

variable [CharP F 2]

private theorem HV.mul (hσ : ∀ c, σ (σ c) = c) {u v u' v' : F} (h : HV σ u v)
    (h' : HV σ u' v') : HV σ (u + u') (v + v' + u * σ u') := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  simp only [HV, map_add, map_mul, hσ] at h h' ⊢
  linear_combination h + h' + (u * σ u' + σ u * u') * h2

private theorem HV.add_fixed {a b c : F} (h : HV σ a b) (hc : σ c = c) : HV σ a (b + c) := by
  simp only [HV, map_add, hc] at h ⊢
  linear_combination h + CharTwo.add_self_eq_zero c

private theorem HV.fixed_add {a b b' : F} (h : HV σ a b) (h' : HV σ a b') :
    σ (b + b') = b + b' := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  simp only [HV] at h h'
  rw [map_add]
  linear_combination h + h' + (-b - b' - σ a * a) * h2

private theorem eq_of_trace_eq (hσ : ∀ c, σ (σ c) = c) (hne : ∃ a, σ a ≠ a) {a b : F}
    (h : ∀ s, s * σ a + σ s * a = s * σ b + σ s * b) : a = b := by
  have h0 : σ a - σ b = 0 := RelBuild.eq_zero_of_trace_mul hne fun x => by
    simp only [map_mul, map_sub, hσ]
    linear_combination h x
  exact σ.injective (sub_eq_zero.1 h0)

private theorem conj_aux {G : Type*} [Group G] {x x' zw zf : G} (h1 : x * x' * x⁻¹ = zf * x')
    (h2 : x * zw * x⁻¹ = zw) (c1 : x' * zw = zw * x') (c2 : x' * zf = zf * x')
    (c3 : zw * zf = zf * zw) (hsq : zw * zw = 1) :
    x' * zw * x * (x' * zw) * x⁻¹ = x' * x' * zf := by
  have e1 : x' * zw * x * (x' * zw) * x⁻¹ = x' * zw * ((x * x' * x⁻¹) * (x * zw * x⁻¹)) := by
    group
  rw [e1, h1, h2]
  have e2 : x' * zw * (zf * x' * zw) = x' * (zw * zf) * x' * zw := by group
  rw [e2, c3]
  have e3 : x' * (zf * zw) * x' * zw = x' * zf * (zw * x') * zw := by group
  rw [e3, ← c1]
  have e4 : x' * zf * (x' * zw) * zw = x' * zf * x' * (zw * zw) := by group
  rw [e4, hsq, mul_one, mul_assoc, ← c2, ← mul_assoc]

variable {X X' : F → F → H} {y z : F → H}

private theorem HeisCtx.z_zero (C : HeisCtx σ X X' y z) : z 0 = 1 := by
  have h := C.z_add 0 0
  rw [add_zero] at h
  exact (mul_eq_left.1 h.symm)

private theorem HeisCtx.z_mul_self (C : HeisCtx σ X X' y z) (w : F) : z w * z w = 1 := by
  rw [← C.z_add, CharTwo.add_self_eq_zero, C.z_zero]

private theorem HeisCtx.z_mul_comm (C : HeisCtx σ X X' y z) (a b : F) :
    z a * z b = z b * z a := by
  rw [← C.z_add, ← C.z_add, add_comm]

private theorem HeisCtx.l_mul_right (C : HeisCtx σ X X' y z) {c a b : F} (hc : σ c = c)
    (hab : HV σ a b) : X' a b * X' 0 c = X' a (b + c) := by
  rw [C.X'_mul _ _ _ _ hab (Pres.heis_zero_left_valid hc)]
  have e1 : a + 0 = a := add_zero a
  have e2 : b + c + a * σ 0 = b + c := by simp
  rw [e1, e2]

private theorem HeisCtx.comm_sq (C : HeisCtx σ X X' y z) {u v κ s w : F} (hV : HV σ u v)
    (hκ : σ κ * κ = σ s * s) (hw : ⁅y s, X u v⁆ = X' (κ * u) (σ s * s * v) * z w) :
    ⁅X u v, X' (κ * u) (σ s * s * v)⁆ = z (s * (σ u * u)) := by
  have hσ := C.invol
  have hV' : HV σ (κ * u) (σ s * s * v) := Pres.heis_smul_valid hσ hV hκ
  obtain ⟨f, hf⟩ := C.comm_mem u v _ _ hV hV'
  have hN : σ (σ u * u) = σ u * u := by rw [map_mul, hσ, mul_comm]
  have hxx : X u v * X u v = X 0 (σ u * u) := by
    rw [C.X_mul _ _ _ _ hV hV]
    have e2 : v + v + u * σ u = σ u * u := by
      rw [CharTwo.add_self_eq_zero, zero_add, mul_comm]
    rw [CharTwo.add_self_eq_zero u, e2]
  have hx'x' : X' (κ * u) (σ s * s * v) * X' (κ * u) (σ s * s * v) =
      X' 0 (σ s * s * (σ u * u)) := by
    rw [C.X'_mul _ _ _ _ hV' hV']
    have e2 : σ s * s * v + σ s * s * v + κ * u * σ (κ * u) = σ s * s * (σ u * u) := by
      rw [CharTwo.add_self_eq_zero, zero_add, map_mul]
      linear_combination (σ u * u) * hκ
    rw [CharTwo.add_self_eq_zero (κ * u), e2]
  have h1 := C.shortLong s (σ u * u) hN
  rw [← hxx, commutatorElement_mul_right_eq_mul_conj, hw] at h1
  have key := conj_aux (x := X u v) (x' := X' (κ * u) (σ s * s * v)) (zw := z w) (zf := z f)
    (by rw [commutatorElement_def] at hf; rwa [mul_inv_eq_iff_eq_mul] at hf)
    (by rw [mul_inv_eq_iff_eq_mul]; exact (C.zX w u v).symm.eq)
    (C.zX' w _ _).symm.eq (C.zX' f _ _).symm.eq (C.z_mul_comm w f) (C.z_mul_self w)
  rw [key, hx'x'] at h1
  have h3 := (C.zX' (s * (σ u * u)) 0 (σ s * s * (σ u * u))).eq
  rw [h3] at h1
  rw [hf]
  exact mul_left_cancel h1

private theorem HeisCtx.cocycle (C : HeisCtx σ X X' y z) {u v : F} (hV : HV σ u v)
    {κ : F → F} (hκ : ∀ s, σ (κ s) * κ s = σ s * s)
    {w : F → F} (hw : ∀ s, ⁅y s, X u v⁆ = X' (κ s * u) (σ s * s * v) * z (w s)) (s s' : F) :
    σ (s + s') * (s + s') * v = σ s' * s' * v + (s * σ (w s') + σ s * w s') + σ s * s * v +
      κ s' * u * σ (κ s * u) := by
  have hσ := C.invol
  set c₀ := s * σ (w s') + σ s * w s' with hc₀
  have hc₀σ : σ c₀ = c₀ := by
    rw [hc₀, map_add, map_mul, map_mul, hσ, hσ]; ring
  have hA : HV σ (κ s * u) (σ s * s * v) := Pres.heis_smul_valid hσ hV (hκ s)
  have hA' : HV σ (κ s' * u) (σ s' * s' * v) := Pres.heis_smul_valid hσ hV (hκ s')
  have hA'ℓ : HV σ (κ s' * u) (σ s' * s' * v + c₀) := HV.add_fixed hA' hc₀σ
  have hA₃ : HV σ (κ (s + s') * u) (σ (s + s') * (s + s') * v) :=
    Pres.heis_smul_valid hσ hV (hκ (s + s'))
  have hA₄ := HV.mul hσ hA'ℓ hA
  have hya : y s * X' (κ s' * u) (σ s' * s' * v) * (y s)⁻¹ = X' (κ s' * u) (σ s' * s' * v) := by
    rw [mul_inv_eq_iff_eq_mul]; exact (C.yX' s _ _).eq
  have hyz : y s * z (w s') * (y s)⁻¹ = X' 0 c₀ * z (w s') := by
    rw [← C.trace, commutatorElement_def]; group
  have e0 : ⁅y (s + s'), X u v⁆ = X' (κ s' * u + κ s * u)
      (σ s' * s' * v + c₀ + σ s * s * v + κ s' * u * σ (κ s * u)) * z (w s' + w s) := by
    rw [C.y_add, commutatorElement_mul_left_eq_conj_mul, hw s, hw s', C.z_add,
      ← C.X'_mul _ _ _ _ hA'ℓ hA, ← C.l_mul_right hc₀σ hA']
    calc y s * (X' (κ s' * u) (σ s' * s' * v) * z (w s')) * (y s)⁻¹ *
          (X' (κ s * u) (σ s * s * v) * z (w s)) =
        (y s * X' (κ s' * u) (σ s' * s' * v) * (y s)⁻¹) * (y s * z (w s') * (y s)⁻¹) *
          (X' (κ s * u) (σ s * s * v) * z (w s)) := by group
      _ = X' (κ s' * u) (σ s' * s' * v) * (X' 0 c₀ * z (w s')) *
          (X' (κ s * u) (σ s * s * v) * z (w s)) := by rw [hya, hyz]
      _ = X' (κ s' * u) (σ s' * s' * v) * X' 0 c₀ * (z (w s') * X' (κ s * u) (σ s * s * v)) *
          z (w s) := by group
      _ = X' (κ s' * u) (σ s' * s' * v) * X' 0 c₀ * (X' (κ s * u) (σ s * s * v) * z (w s')) *
          z (w s) := by rw [(C.zX' (w s') _ _).eq]
      _ = _ := by group
  have h := C.unique _ _ _ _ _ _ hA₃ hA₄ ((hw (s + s')).symm.trans e0)
  exact (C.X'_inj _ _ _ _ hA₃ hA₄ h).2

private theorem tw_identity (hσ : ∀ c, σ (σ c) = c) (e : Bool) {u v : F} (hV : HV σ u v)
    (s s' : F) :
    s * σ (s' * RelBuild.tw σ e (σ v)) + σ s * (s' * RelBuild.tw σ e (σ v)) =
      σ (s + s') * (s + s') * v + σ s' * s' * v + σ s * s * v +
        RelBuild.tw σ e s' * u * σ (RelBuild.tw σ e s * u) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  cases e
  · simp only [RelBuild.tw_false, map_mul, map_add, hσ] at hV ⊢
    linear_combination (-(σ s * s')) * hV +
      (σ s * s' * σ v - σ s * s * v - σ s' * s' * v) * h2
  · simp only [RelBuild.tw_true, map_mul, map_add, hσ] at hV ⊢
    linear_combination (-(σ s' * s)) * hV +
      (σ s' * s * σ v - σ s * s * v - σ s' * s' * v) * h2

private theorem tw_div_mul (hσ : ∀ c, σ (σ c) = c) (e : Bool) {u u' : F} (hu : u ≠ 0) :
    RelBuild.tw σ e (u' / u) * (σ u * u) = RelBuild.tw σ e (σ u * u') := by
  have hσu : σ u ≠ 0 := (map_ne_zero σ).2 hu
  cases e
  · simp only [RelBuild.tw_false]
    field_simp
  · simp only [RelBuild.tw_true, map_div₀, map_mul, hσ]
    field_simp

private theorem HeisCtx.w_eq (C : HeisCtx σ X X' y z) {u v : F} (hV : HV σ u v) (e : Bool)
    {w : F → F}
    (hw : ∀ s, ⁅y s, X u v⁆ = X' (RelBuild.tw σ e s * u) (σ s * s * v) * z (w s)) (s' : F) :
    w s' = s' * RelBuild.tw σ e (σ v) := by
  have hσ := C.invol
  have hc2 : (2 : F) = 0 := CharTwo.two_eq_zero
  refine eq_of_trace_eq hσ C.nonfix fun s => ?_
  have h1 := C.cocycle hV (κ := RelBuild.tw σ e) (fun s => RelBuild.norm_tw hσ e s) hw s s'
  have h2 := tw_identity hσ e hV s s'
  linear_combination (-1) * h1 + (-1) * h2 +
    (-(σ s' * s' * v + σ s * s * v + RelBuild.tw σ e s' * u * σ (RelBuild.tw σ e s * u))) * hc2

private theorem HeisCtx.first (C : HeisCtx σ X X' y z) (e : Bool)
    (hSM : ∀ s u v, HV σ u v →
      ∃ w, ⁅y s, X u v⁆ = X' (RelBuild.tw σ e s * u) (σ s * s * v) * z w)
    {u v u' v' : F} (hV : HV σ u v) (hV' : HV σ u' v') :
    ⁅X u v, X' u' v'⁆ = z (RelBuild.tw σ e (σ u * u')) := by
  have hσ := C.invol
  by_cases hu : u = 0
  · subst hu
    have hv : σ v = v := by
      have h : v + σ v = 0 := by simpa [HV] using hV
      exact (CharTwo.add_eq_zero.1 h).symm
    rw [(C.lX' v hv u' v').commutator_eq, map_zero, zero_mul, RelBuild.tw_zero, C.z_zero]
  · obtain ⟨w, hw⟩ := hSM (RelBuild.tw σ e (u' / u)) u v hV
    set s := RelBuild.tw σ e (u' / u) with hs
    have hκ : σ (RelBuild.tw σ e s) * RelBuild.tw σ e s = σ s * s := RelBuild.norm_tw hσ e s
    have hκu : RelBuild.tw σ e s * u = u' := by
      rw [hs, RelBuild.tw_tw_self hσ, div_mul_cancel₀ _ hu]
    have key := C.comm_sq hV hκ hw
    rw [hκu, hs, tw_div_mul hσ e hu] at key
    have hV'' : HV σ u' (σ s * s * v) := hκu ▸ Pres.heis_smul_valid hσ hV hκ
    have hd := HV.fixed_add hV'' hV'
    have hsplit : X' u' v' = X' u' (σ s * s * v) * X' 0 (σ s * s * v + v') := by
      rw [C.l_mul_right hd hV'', ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    rw [hsplit, commutatorElement_mul_right_eq_mul_conj, (C.l'X _ hd u v).symm.commutator_eq,
      key, mul_one, mul_inv_cancel_right]

private theorem HeisCtx.second (C : HeisCtx σ X X' y z) (e : Bool)
    (hSM : ∀ s u v, HV σ u v →
      ∃ w, ⁅y s, X u v⁆ = X' (RelBuild.tw σ e s * u) (σ s * s * v) * z w)
    {u v : F} (hV : HV σ u v) (s : F) :
    ⁅y s, X u v⁆ = X' (RelBuild.tw σ e s * u) (σ s * s * v) * z (s * RelBuild.tw σ e (σ v)) := by
  choose w hw using fun s => hSM s u v hV
  rw [hw s, C.w_eq hV e hw s]

end Algebra

section Frame

variable {H : Type} [Group H] {Δ : Set (Subgroup H)} {r : ℕ} {P Q : Fin r → Subgroup H}
  {k i : Fin r} {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
  (hFn : Nat.card F = (2 ^ n) ^ 2)

local notation "heis₃" => suHeis (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
  (Nat.not_even_iff_odd.mpr (Exists.intro 1 rfl)) (Sum.inl (0 : Fin (3 / 2)))

private theorem map_heis_zero_mem {c : F} (hc : unitaryInvolution F 2 n c = c)
    {θ : SU (unitaryInvolution F 2 n) 3 →* H} {A : Subgroup H}
    (hθt : (su3Top (unitaryInvolution F 2 n)).map θ = A) : θ (heis₃ 0 c) ∈ A := by
  rw [suHeis_zero_left (σ := unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
    (Nat.not_even_iff_odd.mpr ⟨1, rfl⟩) (Sum.inl (0 : Fin (3 / 2))) c, ← hθt]
  exact Subgroup.mem_map_of_mem θ ((mem_su3Top_iff (σ := unitaryInvolution F 2 n)).2 ⟨c, hc, rfl⟩)

private theorem heisAlg_of_odd {θ θ' : SU (unitaryInvolution F 2 n) 3 →* H}
    (hθ'o : Odd (Nat.card θ'.ker)) :
    HeisAlg (unitaryInvolution F 2 n) (fun u v => θ (heis₃ u v)) (fun u v => θ' (heis₃ u v)) := by
  refine ⟨unitaryInvolution_involutive hFn, exists_unitaryInvolution_ne hFn,
    fun u v u' v' h h' => ?_, fun u v u' v' h h' => ?_,
    fun u v u' v' h h' he => eq_and_eq_of_map_suHeis_eq hFn hθ'o h h' he⟩
  · rw [← map_mul, suHeis_mul (unitaryInvolution_involutive hFn)
      (Nat.not_even_iff_odd.mpr ⟨1, rfl⟩) h h', CharTwo.sub_eq_add]
  · rw [← map_mul, suHeis_mul (unitaryInvolution_involutive hFn)
      (Nat.not_even_iff_odd.mpr ⟨1, rfl⟩) h h', CharTwo.sub_eq_add]

private theorem heisRel_of_frame {R : SURelations r (unitaryInvolution F 2 n) H} (hik : i ≠ k)
    {θ θ' : SU (unitaryInvolution F 2 n) 3 →* H}
    (hξk : ∀ c, unitaryInvolution F 2 n c = c → R.ξL (Sum.inl k) c = θ (heis₃ 0 c))
    (hξi : ∀ c, unitaryInvolution F 2 n c = c → R.ξL (Sum.inl i) c = θ' (heis₃ 0 c))
    (hθ'o : Odd (Nat.card θ'.ker)) :
    HeisRel (unitaryInvolution F 2 n) (fun u v => θ (heis₃ u v)) (fun u v => θ' (heis₃ u v))
      (fun s => R.ξ (Sum.inl i) (Sum.inr k) s) (fun w => R.ξ (Sum.inl i) (Sum.inl k) w) := by
  have hσ := unitaryInvolution_involutive hFn
  have hfix : ∀ s t : F, unitaryInvolution F 2 n (s * unitaryInvolution F 2 n t +
      unitaryInvolution F 2 n s * t) = s * unitaryInvolution F 2 n t +
        unitaryInvolution F 2 n s * t := fun s t => by
    rw [map_add, map_mul, map_mul, hσ, hσ]; ring
  refine ⟨fun s t => R.add (Sum.inl i) (Sum.inr k) hik s t,
    fun s t => R.add (Sum.inl i) (Sum.inl k) hik s t, fun s t h => ?_,
    fun s t => ?_, fun s c hc => ?_⟩
  · refine R.eq_of_ξ_eq hσ (exists_unitaryInvolution_ne hFn) (a := Sum.inl i) (b := Sum.inl k) hik
      (fun c hc h1 => ?_) h
    rw [hξi c hc] at h1
    have h0 : θ' (heis₃ 0 c) = θ' (heis₃ 0 0) := by
      rw [h1, suHeis_zero_left (σ := unitaryInvolution F 2 n) hσ
        (Nat.not_even_iff_odd.mpr ⟨1, rfl⟩) (Sum.inl (0 : Fin (3 / 2))) 0, suLong_zero, map_one]
    exact (eq_and_eq_of_map_suHeis_eq hFn hθ'o (Pres.heis_zero_left_valid hc)
      (Pres.heis_zero_left_valid (map_zero _)) h0).2
  · exact (R.trace (Sum.inl i) (Sum.inr k) hik s t).trans (hξi _ (hfix s t))
  · have h := R.shortLong (Sum.inl i) (Sum.inr k) hik s c hc
    have e1 : R.ξL (Sum.swap (Sum.inr k)) c = θ (heis₃ 0 c) := hξk c hc
    have e2 : R.ξL (Sum.inl i) (unitaryInvolution F 2 n s * s * c) =
        θ' (heis₃ 0 (unitaryInvolution F 2 n s * s * c)) :=
      hξi _ (by rw [map_mul, map_mul, hσ, hc, mul_comm (unitaryInvolution F 2 n s) s])
    rw [e1, e2] at h
    exact h

private theorem heisComm_of_frame (h : TransvectionHyp H Δ) (hML : MeetsLines Δ)
    (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsFrame Δ P Q) (hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ n)
    {R : SURelations r (unitaryInvolution F 2 n) H} (hR : R.HasFrameImages Δ P Q) (hik : i ≠ k)
    {θ θ' : SU (unitaryInvolution F 2 n) 3 →* H} (hθr : θ.range = residueGroup Δ P Q k)
    (hθt : (su3Top (unitaryInvolution F 2 n)).map θ = P k)
    (hθb : (su3Bot (unitaryInvolution F 2 n)).map θ = Q k)
    (hθr' : θ'.range = residueGroup Δ P Q i)
    (hθt' : (su3Top (unitaryInvolution F 2 n)).map θ' = P i)
    (hθb' : (su3Bot (unitaryInvolution F 2 n)).map θ' = Q i) :
    HeisComm (unitaryInvolution F 2 n) (fun u v => θ (heis₃ u v)) (fun u v => θ' (heis₃ u v))
      (fun s => R.ξ (Sum.inl i) (Sum.inr k) s) (fun w => R.ξ (Sum.inl i) (Sum.inl k) w) := by
  have hθ' := hR.commute_map_suHeis_short h hML hq hF hFn hcard hθr' hθt' hθb' hik.symm
  have hθ := hR.commute_map_suHeis_short h hML hq hF hFn hcard hθr hθt hθb hik
  refine ⟨fun s a b => (hθ' a b s).1.symm, fun w a b => (hθ' a b w).2.1.symm,
    fun w a b => (hθ a b w).2.2.symm, fun c hc a b => ?_, fun c hc a b => ?_⟩
  · have hmem : θ' (heis₃ a b) ∈ residueGroup Δ P Q i := hθr' ▸ ⟨_, rfl⟩
    exact ((commuting_residueGroup (Δ := Δ) (P := P) (Q := Q) hik.symm) _ hmem _
      (Subgroup.mem_sup_left (map_heis_zero_mem hFn hc hθt))).symm
  · have hmem : θ (heis₃ a b) ∈ residueGroup Δ P Q k := hθr ▸ ⟨_, rfl⟩
    exact ((commuting_residueGroup (Δ := Δ) (P := P) (Q := Q) hik) _ hmem _
      (Subgroup.mem_sup_left (map_heis_zero_mem hFn hc hθt'))).symm

private theorem heisMem_of_frame (h : TransvectionHyp H Δ) (hML : MeetsLines Δ)
    (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsMaxFrame Δ P Q) (hns : ¬IsSmallFrame Δ P Q k)
    (hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ n)
    {R : SURelations r (unitaryInvolution F 2 n) H} (hR : R.HasFrameImages Δ P Q) (hik : i ≠ k)
    {θ θ' : SU (unitaryInvolution F 2 n) 3 →* H} (hθr : θ.range = residueGroup Δ P Q k)
    (hθo : Odd (Nat.card θ.ker)) (hθt : (su3Top (unitaryInvolution F 2 n)).map θ = P k)
    (hθb : (su3Bot (unitaryInvolution F 2 n)).map θ = Q k)
    (hθmem : ∀ X : Subgroup H, X ∈ frameResidue Δ P Q k ↔
      ∃ g, X = (conjSub (su3Top (unitaryInvolution F 2 n)) g).map θ)
    (hθr' : θ'.range = residueGroup Δ P Q i) (hθo' : Odd (Nat.card θ'.ker))
    (hθt' : (su3Top (unitaryInvolution F 2 n)).map θ' = P i)
    (hθb' : (su3Bot (unitaryInvolution F 2 n)).map θ' = Q i)
    (hθmem' : ∀ X : Subgroup H, X ∈ frameResidue Δ P Q i ↔
      ∃ g, X = (conjSub (su3Top (unitaryInvolution F 2 n)) g).map θ') :
    HeisMem (unitaryInvolution F 2 n) (fun u v => θ (heis₃ u v)) (fun u v => θ' (heis₃ u v))
      (fun w => R.ξ (Sum.inl i) (Sum.inl k) w) := by
  have hz : ∀ w, R.ξ (Sum.inl i) (Sum.inl k) w ∈ shortRootGroup Δ (P i) (Q i) (P k) (Q k) :=
    fun w => (hR.short (Sum.inl i) (Sum.inl k) hik _).2 ⟨w, rfl⟩
  have hbot := hF.residueGroup_inf_shortRootGroup_eq_bot h hML hq hns hFn hcard hθr hθo hθt hθb
    hθmem hik
  refine ⟨fun u v u' v' _ _ => ?_, fun a b a' b' w w' _ _ he => ?_⟩
  · have hb := Subgroup.mem_map_of_mem θ' (suHeis_three_mem_uc22pwsu3X hFn u' v')
    have hb' := Subgroup.mem_map_of_mem θ (suHeis_three_mem_uc22pwsu3X hFn u v)
    have hc := hF.commutatorElement_mem_map_heis_sup_inf h hML hq hns hFn hcard hθr hθo hθt hθb
      hθmem hik hθr' hθo' hθt' hθb' hθmem' hb hb'
    have hY := hF.map_heis_sup_inf_map_heis_sup_le (k := i) (i := k) h hML hq hFn hcard hθr' hθt'
      hθb' hik.symm hns hθr hθo hθt hθb hθmem ⟨hc.2, hc.1⟩
    have hY' : ⁅θ (heis₃ u v), θ' (heis₃ u' v')⁆ ∈ shortRootGroup Δ (P i) (Q i) (P k) (Q k) := by
      rw [← commutatorElement_inv]
      exact Subgroup.inv_mem _ hY
    obtain ⟨w, hw⟩ := (hR.short (Sum.inl i) (Sum.inl k) hik _).1 hY'
    exact ⟨w, hw.symm⟩
  · have he' : θ' (heis₃ a b) * R.ξ (Sum.inl i) (Sum.inl k) w =
        θ' (heis₃ a' b') * R.ξ (Sum.inl i) (Sum.inl k) w' := he
    have hmem : (θ' (heis₃ a' b'))⁻¹ * θ' (heis₃ a b) ∈ residueGroup Δ P Q i := by
      rw [← hθr', ← map_inv, ← map_mul]
      exact ⟨_, rfl⟩
    have hcomm : (θ' (heis₃ a' b'))⁻¹ * θ' (heis₃ a b) =
        R.ξ (Sum.inl i) (Sum.inl k) w' * (R.ξ (Sum.inl i) (Sum.inl k) w)⁻¹ := by
      calc (θ' (heis₃ a' b'))⁻¹ * θ' (heis₃ a b) =
          (θ' (heis₃ a' b'))⁻¹ * (θ' (heis₃ a b) * R.ξ (Sum.inl i) (Sum.inl k) w) *
            (R.ξ (Sum.inl i) (Sum.inl k) w)⁻¹ := by group
        _ = (θ' (heis₃ a' b'))⁻¹ * (θ' (heis₃ a' b') * R.ξ (Sum.inl i) (Sum.inl k) w') *
            (R.ξ (Sum.inl i) (Sum.inl k) w)⁻¹ := by rw [he']
        _ = _ := by group
    have hmem2 : (θ' (heis₃ a' b'))⁻¹ * θ' (heis₃ a b) ∈
        shortRootGroup Δ (P i) (Q i) (P k) (Q k) := by
      rw [hcomm]
      exact Subgroup.mul_mem _ (hz w') (Subgroup.inv_mem _ (hz w))
    have h1 : (θ' (heis₃ a' b'))⁻¹ * θ' (heis₃ a b) ∈ (⊥ : Subgroup H) :=
      hbot ▸ Subgroup.mem_inf.2 ⟨hmem, hmem2⟩
    exact (inv_mul_eq_one.1 (Subgroup.mem_bot.1 h1)).symm

end Frame

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ} (hFn : Nat.card F = (2 ^ n) ^ 2)
  {r : ℕ} (hr : 2 ≤ r) {H : Type} [Group H] {Δ : Set (Subgroup H)}
  {P Q : Fin (2 * r / 2) → Subgroup H} (hm : 4 ≤ 2 * r)

theorem IsMaxFrame.commutatorElement_suHeis_of_tw (h : TransvectionHyp H Δ)
    (hML : MeetsLines Δ) (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsMaxFrame Δ P Q)
    (hns : ¬IsSmallFrame Δ P Q (cLastIdx r hr)) (hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ n)
    {R : SURelations (2 * r / 2) (unitaryInvolution F 2 n) H} (hR : R.HasFrameImages Δ P Q)
    {θ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hθr : θ.range = residueGroup Δ P Q (cLastIdx r hr)) (hθo : Odd (Nat.card θ.ker))
    (hθc : θ.comp (su3Chord (unitaryInvolution F 2 n)) = R.lastBlock hFn (even_two_mul r) hm)
    (hθmem : ∀ X : Subgroup H, X ∈ frameResidue Δ P Q (cLastIdx r hr) ↔
      ∃ g, X = (conjSub (su3Top (unitaryInvolution F 2 n)) g).map θ)
    (hd : OddFrameCompatible hFn hr (R.toHom hFn (even_two_mul r) hm) θ) (e : Bool)
    (hSM : ∀ s u v : F, v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u = 0 →
      ∃ w : F, ⁅R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) s,
          θ (suHeis (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
            (Nat.not_even_iff_odd.mpr ⟨1, rfl⟩) (Sum.inl (0 : Fin (3 / 2))) u v)⁆ =
        oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) θ
            (suHeis (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
              (Nat.not_even_iff_odd.mpr ⟨1, rfl⟩) (Sum.inl (0 : Fin (3 / 2)))
              (RelBuild.tw (unitaryInvolution F 2 n) e s * u)
              (unitaryInvolution F 2 n s * s * v)) *
          R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inl (cLastIdx r hr)) w) :
    (∀ u v u' v' : F, v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u = 0 →
        v' + unitaryInvolution F 2 n v' + unitaryInvolution F 2 n u' * u' = 0 →
        ⁅θ (suHeis (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
              (Nat.not_even_iff_odd.mpr ⟨1, rfl⟩) (Sum.inl (0 : Fin (3 / 2))) u v),
          oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) θ
            (suHeis (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
              (Nat.not_even_iff_odd.mpr ⟨1, rfl⟩) (Sum.inl (0 : Fin (3 / 2))) u' v')⁆ =
          R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inl (cLastIdx r hr))
            (RelBuild.tw (unitaryInvolution F 2 n) e (unitaryInvolution F 2 n u * u'))) ∧
      ∀ s u v : F, v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u = 0 →
        ⁅R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) s,
          θ (suHeis (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
            (Nat.not_even_iff_odd.mpr ⟨1, rfl⟩) (Sum.inl (0 : Fin (3 / 2))) u v)⁆ =
        oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) θ
            (suHeis (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
              (Nat.not_even_iff_odd.mpr ⟨1, rfl⟩) (Sum.inl (0 : Fin (3 / 2)))
              (RelBuild.tw (unitaryInvolution F 2 n) e s * u)
              (unitaryInvolution F 2 n s * s * v)) *
          R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inl (cLastIdx r hr))
            (s * RelBuild.tw (unitaryInvolution F 2 n) e (unitaryInvolution F 2 n v)) := by
  obtain ⟨hθ'o, hθ't, hθ'b⟩ :=
    hF.oddPrevLift_normalized hFn hr hm h.cls.root hns hR hθr hθo hθc hθmem
  obtain ⟨hθ'r, -, hθ'mem, -⟩ :=
    IsMaxFrame.su3_residue_oddPrevLift hFn hr hm h.cls.root hF hns hR hθr hθc hθmem
  obtain ⟨hθt, hθb⟩ := hR.map_su3Top_su3Bot_of_comp hFn hr hm hθc
  have hne : cPrevIdx r hr ≠ cLastIdx r hr := cPrevIdx_ne_cLastIdx hr
  have C : HeisCtx (unitaryInvolution F 2 n)
      (fun u v => θ (suHeis (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
        (Nat.not_even_iff_odd.mpr ⟨1, rfl⟩) (Sum.inl (0 : Fin (3 / 2))) u v))
      (fun u v => oddPrevLift hFn hr (R.toHom hFn (even_two_mul r) hm) θ
        (suHeis (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
          (Nat.not_even_iff_odd.mpr ⟨1, rfl⟩) (Sum.inl (0 : Fin (3 / 2))) u v))
      (fun s => R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inr (cLastIdx r hr)) s)
      (fun w => R.ξ (Sum.inl (cPrevIdx r hr)) (Sum.inl (cLastIdx r hr)) w) :=
    ⟨heisAlg_of_odd hFn hθ'o,
      heisRel_of_frame hFn hne
        (fun c hc => (OddFrameCompatible.ξL_inl_eq_map_suHeis hFn hr hm hd hc).1)
        (fun c hc => (OddFrameCompatible.ξL_inl_eq_map_suHeis hFn hr hm hd hc).2) hθ'o,
      heisComm_of_frame hFn h hML hq hF.toIsFrame hcard hR hne hθr hθt hθb hθ'r hθ't hθ'b,
      heisMem_of_frame hFn h hML hq hF hns hcard hR hne hθr hθo hθt hθb hθmem hθ'r hθ'o hθ't
        hθ'b hθ'mem⟩
  exact ⟨fun u v u' v' hV hV' => C.first e hSM hV hV', fun s u v hV => C.second e hSM hV s⟩

end CFSG.Timmesfeld.Transvection
