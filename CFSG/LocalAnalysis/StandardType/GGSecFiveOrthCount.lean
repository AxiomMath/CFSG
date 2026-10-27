module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank
public import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.Isometry
public import Mathlib.LinearAlgebra.QuadraticForm.Prod
public import TauCeti.LinearAlgebra.QuadraticForm.Prod
public import TauCeti.LinearAlgebra.QuadraticForm.Radical

public section

namespace CFSG.StandardType.OrthF3

open TauCeti

private def ct_oc_Q {n : ℕ} (a : Fin n → ZMod 3) : QuadraticForm (ZMod 3) (Fin n → ZMod 3) :=
  QuadraticMap.weightedSumSquares (ZMod 3) a

private def ct_oc_tail {n : ℕ} (a : Fin (n+1) → ZMod 3) : Fin n → ZMod 3 :=
  fun i => a i.succ

private def ct_oc_e0 (n : ℕ) : Fin (n+1) → ZMod 3 := Fin.cons 1 (fun _ => 0)

private lemma ct_oc_Q_cons {n : ℕ} (a : Fin (n+1) → ZMod 3) (c : ZMod 3) (y : Fin n → ZMod 3) :
    ct_oc_Q a (Fin.cons c y) = a 0 * (c * c) + ct_oc_Q (ct_oc_tail a) y := by
  simp [ct_oc_Q, ct_oc_tail, QuadraticMap.weightedSumSquares_apply, Fin.sum_univ_succ]

private lemma ct_oc_Q_e0 {n : ℕ} (a : Fin (n+1) → ZMod 3) :
    ct_oc_Q a (ct_oc_e0 n) = a 0 := by
  rw [ct_oc_e0, ct_oc_Q_cons]
  simp [ct_oc_Q]

private lemma ct_oc_polar_e0 {n : ℕ} (a : Fin (n+1) → ZMod 3) (x : Fin (n+1) → ZMod 3) :
    QuadraticMap.polar (ct_oc_Q a) x (ct_oc_e0 n) = 2 * a 0 * x 0 := by
  have hxe : x + ct_oc_e0 n = Fin.cons (x 0 + 1) (Fin.tail x) := by
    rw [← Fin.cons_self_tail (x + ct_oc_e0 n), Fin.cons_inj]
    constructor
    · simp [ct_oc_e0]
    · funext i; simp [Fin.tail, ct_oc_e0, Pi.add_apply]
  have hxq : ct_oc_Q a x = a 0 * (x 0 * x 0) + ct_oc_Q (ct_oc_tail a) (Fin.tail x) := by
    conv_lhs => rw [← Fin.cons_self_tail x]
    rw [ct_oc_Q_cons]
  rw [QuadraticMap.polar, hxe, ct_oc_Q_cons, hxq, ct_oc_Q_e0]
  ring


private def ct_oc_consLinearEquiv (n : ℕ) :
    (ZMod 3 × (Fin n → ZMod 3)) ≃ₗ[ZMod 3] (Fin (n+1) → ZMod 3) where
  toFun p := Fin.cons p.1 p.2
  invFun x := (x 0, Fin.tail x)
  left_inv p := by ext <;> simp
  right_inv x := by rw [← Fin.cons_self_tail x]; simp
  map_add' p q := by
    funext i
    refine Fin.cases ?_ ?_ i <;> simp [Pi.add_apply]
  map_smul' c p := by
    funext i
    refine Fin.cases ?_ ?_ i <;> simp [Pi.smul_apply]

private lemma ct_oc_cons0_tail {n : ℕ} (x : Fin (n+1) → ZMod 3) (hx : x 0 = 0) :
    Fin.cons (0 : ZMod 3) (Fin.tail x) = x := by
  rw [← hx]
  exact Fin.cons_self_tail x

private lemma ct_oc_cons0_add {n : ℕ} (y y' : Fin n → ZMod 3) :
    Fin.cons (α := fun _ => ZMod 3) (0 : ZMod 3) (y + y') =
      Fin.cons (α := fun _ => ZMod 3) (0 : ZMod 3) y +
        Fin.cons (α := fun _ => ZMod 3) (0 : ZMod 3) y' := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp
  · intro j; simp

private lemma ct_oc_cons0_smul {n : ℕ} (c : ZMod 3) (y : Fin n → ZMod 3) :
    Fin.cons (α := fun _ => ZMod 3) (0 : ZMod 3) (c • y) =
      c • Fin.cons (α := fun _ => ZMod 3) (0 : ZMod 3) y := by
  funext i
  refine Fin.cases ?_ ?_ i
  · simp
  · intro j; simp

private lemma ct_oc_decomp {n : ℕ} (x : Fin (n+1) → ZMod 3) :
    x = (x 0) • ct_oc_e0 n + Fin.cons 0 (Fin.tail x) := by
  rw [← Fin.cons_self_tail x]
  funext i
  refine Fin.cases ?_ ?_ i <;> simp [ct_oc_e0, Fin.tail, Pi.add_apply, Pi.smul_apply]

private lemma ct_oc_coord_of_fixed {n : ℕ} {a : Fin (n+1) → ZMod 3} (ha : a 0 ≠ 0)
    (g : QuadraticMap.orthogonalGroup (ct_oc_Q a))
    (hg : (g : (Fin (n+1) → ZMod 3) ≃ₗ[ZMod 3] (Fin (n+1) → ZMod 3)) (ct_oc_e0 n) = ct_oc_e0 n)
    (x : Fin (n+1) → ZMod 3) :
    ((g : (Fin (n+1) → ZMod 3) ≃ₗ[ZMod 3] (Fin (n+1) → ZMod 3)) x) 0 = x 0 := by
  have hp := QuadraticMap.polar_apply_of_mem_orthogonalGroup g.2 x (ct_oc_e0 n)
  rw [hg, ct_oc_polar_e0, ct_oc_polar_e0] at hp
  have h2a : (2 * a 0 : ZMod 3) ≠ 0 := mul_ne_zero (by decide) ha
  exact mul_left_cancel₀ h2a hp

private lemma ct_oc_fixed_apply {n : ℕ} {a : Fin (n+1) → ZMod 3} (ha : a 0 ≠ 0)
    (g : QuadraticMap.orthogonalGroup (ct_oc_Q a))
    (hg : (g : (Fin (n+1) → ZMod 3) ≃ₗ[ZMod 3] (Fin (n+1) → ZMod 3)) (ct_oc_e0 n) = ct_oc_e0 n)
    (x : Fin (n+1) → ZMod 3) :
    (g : (Fin (n+1) → ZMod 3) ≃ₗ[ZMod 3] (Fin (n+1) → ZMod 3)) x =
      Fin.cons (x 0) (Fin.tail ((g : (Fin (n+1) → ZMod 3) ≃ₗ[ZMod 3]
        (Fin (n+1) → ZMod 3)) (Fin.cons 0 (Fin.tail x)))) := by
  have hcoord := ct_oc_coord_of_fixed ha g hg x
  funext i
  refine Fin.cases ?_ ?_ i
  · simpa using hcoord
  · intro j
    have hdec := ct_oc_decomp x
    conv_lhs => rw [hdec]
    rw [map_add, map_smul, hg]
    simp [ct_oc_e0, Fin.tail, Pi.add_apply, Pi.smul_apply]

private def ct_oc_stabForwardLinear {n : ℕ} (a : Fin (n+1) → ZMod 3)
    (g : MulAction.stabilizer (QuadraticMap.orthogonalGroup (ct_oc_Q a)) (ct_oc_e0 n)) :
    (Fin n → ZMod 3) →ₗ[ZMod 3] (Fin n → ZMod 3) where
  toFun y := Fin.tail ((g.1 : (Fin (n+1) → ZMod 3) ≃ₗ[ZMod 3] (Fin (n+1) → ZMod 3))
    (Fin.cons 0 y))
  map_add' y y' := by
    rw [ct_oc_cons0_add, map_add]
    funext i
    simp [Fin.tail, Pi.add_apply]
  map_smul' c y := by
    rw [ct_oc_cons0_smul, map_smul]
    funext i
    simp [Fin.tail, Pi.smul_apply]

private lemma ct_oc_stabForwardLinear_injective {n : ℕ} {a : Fin (n+1) → ZMod 3}
    (ha : a 0 ≠ 0)
    (g : MulAction.stabilizer (QuadraticMap.orthogonalGroup (ct_oc_Q a)) (ct_oc_e0 n)) :
    Function.Injective (ct_oc_stabForwardLinear a g) := by
  intro y y' h
  have hgfix : (g.1 : (Fin (n+1) → ZMod 3) ≃ₗ[ZMod 3] (Fin (n+1) → ZMod 3)) (ct_oc_e0 n)
      = ct_oc_e0 n := by
    simpa only [Subgroup.smul_def, LinearEquiv.smul_def, Subgroup.coe_mk] using MulAction.mem_stabilizer_iff.mp g.2
  have hcoord : ((g.1 : (Fin (n+1) → ZMod 3) ≃ₗ[ZMod 3] (Fin (n+1) → ZMod 3))
      (Fin.cons 0 y)) 0 = 0 := by
    rw [ct_oc_coord_of_fixed ha g.1 hgfix]
    simp
  have hcoord' : ((g.1 : (Fin (n+1) → ZMod 3) ≃ₗ[ZMod 3] (Fin (n+1) → ZMod 3))
      (Fin.cons 0 y')) 0 = 0 := by
    rw [ct_oc_coord_of_fixed ha g.1 hgfix]
    simp
  have h1 : (g.1 : (Fin (n+1) → ZMod 3) ≃ₗ[ZMod 3] (Fin (n+1) → ZMod 3))
      (Fin.cons 0 y) = (g.1 : (Fin (n+1) → ZMod 3) ≃ₗ[ZMod 3] (Fin (n+1) → ZMod 3))
        (Fin.cons 0 y') := by
    have h' : Fin.tail ((g.1 : (Fin (n+1) → ZMod 3) ≃ₗ[ZMod 3] (Fin (n+1) → ZMod 3))
        (Fin.cons 0 y)) = Fin.tail ((g.1 : (Fin (n+1) → ZMod 3) ≃ₗ[ZMod 3]
          (Fin (n+1) → ZMod 3)) (Fin.cons 0 y')) := h
    rw [← ct_oc_cons0_tail _ hcoord, ← ct_oc_cons0_tail _ hcoord', h']
  have h2 : Fin.cons 0 y = Fin.cons 0 y' := (g.1 : (Fin (n+1) → ZMod 3) ≃ₗ[ZMod 3]
    (Fin (n+1) → ZMod 3)).injective h1
  exact (Fin.cons_inj.mp h2).2

private noncomputable def ct_oc_stabForwardEquiv {n : ℕ} (a : Fin (n+1) → ZMod 3) (ha : a 0 ≠ 0)
    (g : MulAction.stabilizer (QuadraticMap.orthogonalGroup (ct_oc_Q a)) (ct_oc_e0 n)) :
    (Fin n → ZMod 3) ≃ₗ[ZMod 3] (Fin n → ZMod 3) :=
  LinearEquiv.ofInjectiveEndo (ct_oc_stabForwardLinear a g)
    (ct_oc_stabForwardLinear_injective ha g)

private lemma ct_oc_stabForwardEquiv_apply {n : ℕ} (a : Fin (n+1) → ZMod 3) (ha : a 0 ≠ 0)
    (g : MulAction.stabilizer (QuadraticMap.orthogonalGroup (ct_oc_Q a)) (ct_oc_e0 n))
    (y : Fin n → ZMod 3) :
    ct_oc_stabForwardEquiv a ha g y = Fin.tail ((g.1 : (Fin (n+1) → ZMod 3) ≃ₗ[ZMod 3]
      (Fin (n+1) → ZMod 3)) (Fin.cons 0 y)) := by
  rw [ct_oc_stabForwardEquiv, LinearEquiv.coe_ofInjectiveEndo]
  rfl

private noncomputable def ct_oc_stabForward {n : ℕ} (a : Fin (n+1) → ZMod 3) (ha : a 0 ≠ 0)
    (g : MulAction.stabilizer (QuadraticMap.orthogonalGroup (ct_oc_Q a)) (ct_oc_e0 n)) :
    QuadraticMap.orthogonalGroup (ct_oc_Q (ct_oc_tail a)) := by
  have hgfix : (g.1 : (Fin (n+1) → ZMod 3) ≃ₗ[ZMod 3] (Fin (n+1) → ZMod 3)) (ct_oc_e0 n)
      = ct_oc_e0 n := by
    simpa only [Subgroup.smul_def, LinearEquiv.smul_def, Subgroup.coe_mk] using
      MulAction.mem_stabilizer_iff.mp g.2
  refine ⟨ct_oc_stabForwardEquiv a ha g, ?_⟩
  rw [QuadraticMap.mem_orthogonalGroup_iff]
  intro y
  have hcoord : ((g.1 : (Fin (n+1) → ZMod 3) ≃ₗ[ZMod 3] (Fin (n+1) → ZMod 3))
      (Fin.cons 0 y)) 0 = 0 := by
    rw [ct_oc_coord_of_fixed ha g.1 hgfix]
    simp
  have hcons : (g.1 : (Fin (n+1) → ZMod 3) ≃ₗ[ZMod 3] (Fin (n+1) → ZMod 3))
      (Fin.cons 0 y) = Fin.cons (α := fun _ => ZMod 3) 0 (Fin.tail ((g.1 : (Fin (n+1) → ZMod 3) ≃ₗ[ZMod 3]
        (Fin (n+1) → ZMod 3)) (Fin.cons 0 y))) :=
    (ct_oc_cons0_tail _ hcoord).symm
  rw [ct_oc_stabForwardEquiv_apply]
  calc ct_oc_Q (ct_oc_tail a) (Fin.tail ((g.1 : (Fin (n+1) → ZMod 3) ≃ₗ[ZMod 3]
        (Fin (n+1) → ZMod 3)) (Fin.cons 0 y)))
      = ct_oc_Q a (Fin.cons 0 (Fin.tail ((g.1 : (Fin (n+1) → ZMod 3) ≃ₗ[ZMod 3]
          (Fin (n+1) → ZMod 3)) (Fin.cons 0 y)))) := by
        rw [ct_oc_Q_cons]; simp
    _ = ct_oc_Q a ((g.1 : (Fin (n+1) → ZMod 3) ≃ₗ[ZMod 3] (Fin (n+1) → ZMod 3))
          (Fin.cons 0 y)) := by rw [← hcons]
    _ = ct_oc_Q a (Fin.cons 0 y) :=
        QuadraticMap.map_app_of_mem_orthogonalGroup g.1.2 (Fin.cons 0 y)
    _ = ct_oc_Q (ct_oc_tail a) y := by rw [ct_oc_Q_cons]; simp

private def ct_oc_stabBackLinear {n : ℕ} {a : Fin (n+1) → ZMod 3}
    (h : QuadraticMap.orthogonalGroup (ct_oc_Q (ct_oc_tail a))) :
    (Fin (n+1) → ZMod 3) →ₗ[ZMod 3] (Fin (n+1) → ZMod 3) where
  toFun x := Fin.cons (x 0) (h.1 (Fin.tail x))
  map_add' x y := by
    have ht : Fin.tail (x + y) = Fin.tail x + Fin.tail y := by
      funext i; simp [Fin.tail, Pi.add_apply]
    funext i
    refine Fin.cases ?_ ?_ i
    · simp
    · intro j; simp [ht, map_add]
  map_smul' c x := by
    have ht : Fin.tail (c • x) = c • Fin.tail x := by
      funext i; simp [Fin.tail, Pi.smul_apply]
    funext i
    refine Fin.cases ?_ ?_ i
    · simp
    · intro j; simp [ht, map_smul]

private lemma ct_oc_stabBackLinear_injective {n : ℕ} {a : Fin (n+1) → ZMod 3}
    (h : QuadraticMap.orthogonalGroup (ct_oc_Q (ct_oc_tail a))) :
    Function.Injective (ct_oc_stabBackLinear (a := a) h) := by
  intro x y hxy
  have h0 : x 0 = y 0 := by
    simpa [ct_oc_stabBackLinear] using congrArg (fun z => z 0) hxy
  have htail : h.1 (Fin.tail x) = h.1 (Fin.tail y) := by
    have := congrArg Fin.tail hxy
    simpa [ct_oc_stabBackLinear, Fin.tail] using this
  have ht : Fin.tail x = Fin.tail y := h.1.injective htail
  calc x = Fin.cons (x 0) (Fin.tail x) := (Fin.cons_self_tail x).symm
    _ = Fin.cons (y 0) (Fin.tail y) := by rw [h0, ht]
    _ = y := Fin.cons_self_tail y

private noncomputable def ct_oc_stabBackEquiv {n : ℕ} (a : Fin (n+1) → ZMod 3)
    (h : QuadraticMap.orthogonalGroup (ct_oc_Q (ct_oc_tail a))) :
    (Fin (n+1) → ZMod 3) ≃ₗ[ZMod 3] (Fin (n+1) → ZMod 3) :=
  LinearEquiv.ofInjectiveEndo (ct_oc_stabBackLinear (a := a) h)
    (ct_oc_stabBackLinear_injective h)

private lemma ct_oc_stabBackEquiv_apply {n : ℕ} (a : Fin (n+1) → ZMod 3)
    (h : QuadraticMap.orthogonalGroup (ct_oc_Q (ct_oc_tail a))) (x : Fin (n+1) → ZMod 3) :
    ct_oc_stabBackEquiv a h x = Fin.cons (x 0) (h.1 (Fin.tail x)) := by
  rw [ct_oc_stabBackEquiv, LinearEquiv.coe_ofInjectiveEndo]
  rfl

private noncomputable def ct_oc_stabBack {n : ℕ} (a : Fin (n+1) → ZMod 3)
    (h : QuadraticMap.orthogonalGroup (ct_oc_Q (ct_oc_tail a))) :
    MulAction.stabilizer (QuadraticMap.orthogonalGroup (ct_oc_Q a)) (ct_oc_e0 n) := by
  refine ⟨⟨ct_oc_stabBackEquiv a h, ?_⟩, ?_⟩
  · rw [QuadraticMap.mem_orthogonalGroup_iff]
    intro x
    rw [ct_oc_stabBackEquiv_apply, ct_oc_Q_cons]
    have hxq : ct_oc_Q a x = a 0 * (x 0 * x 0) + ct_oc_Q (ct_oc_tail a) (Fin.tail x) := by
      conv_lhs => rw [← Fin.cons_self_tail x]
      rw [ct_oc_Q_cons]
    rw [hxq, QuadraticMap.map_app_of_mem_orthogonalGroup h.2 (Fin.tail x)]
  · rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def, LinearEquiv.smul_def,
      ct_oc_stabBackEquiv_apply]
    rw [ct_oc_e0, Fin.tail_cons]
    simp only [Fin.cons_zero]
    exact Fin.cons_inj.mpr ⟨rfl, map_zero (h.1 : (Fin n → ZMod 3) ≃ₗ[ZMod 3]
      (Fin n → ZMod 3))⟩

private noncomputable def ct_oc_stabilizerEquiv {n : ℕ} (a : Fin (n+1) → ZMod 3) (ha : a 0 ≠ 0) :
    MulAction.stabilizer (QuadraticMap.orthogonalGroup (ct_oc_Q a)) (ct_oc_e0 n) ≃
      QuadraticMap.orthogonalGroup (ct_oc_Q (ct_oc_tail a)) where
  toFun := ct_oc_stabForward a ha
  invFun := ct_oc_stabBack a
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    have hgfix : (g.1 : (Fin (n+1) → ZMod 3) ≃ₗ[ZMod 3] (Fin (n+1) → ZMod 3)) (ct_oc_e0 n)
        = ct_oc_e0 n := by
      simpa only [Subgroup.smul_def, LinearEquiv.smul_def, Subgroup.coe_mk] using
        MulAction.mem_stabilizer_iff.mp g.2
    change ct_oc_stabBackEquiv a (ct_oc_stabForward a ha g) x =
      (g.1 : (Fin (n+1) → ZMod 3) ≃ₗ[ZMod 3] (Fin (n+1) → ZMod 3)) x
    rw [ct_oc_stabBackEquiv_apply]
    change Fin.cons (x 0) (ct_oc_stabForwardEquiv a ha g (Fin.tail x)) =
      (g.1 : (Fin (n+1) → ZMod 3) ≃ₗ[ZMod 3] (Fin (n+1) → ZMod 3)) x
    rw [ct_oc_stabForwardEquiv_apply]
    exact (ct_oc_fixed_apply ha g.1 hgfix x).symm
  right_inv h := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro y
    change ct_oc_stabForwardEquiv a ha (ct_oc_stabBack a h) y =
      (h.1 : (Fin n → ZMod 3) ≃ₗ[ZMod 3] (Fin n → ZMod 3)) y
    rw [ct_oc_stabForwardEquiv_apply]
    change Fin.tail (ct_oc_stabBackEquiv a h (Fin.cons 0 y)) =
      (h.1 : (Fin n → ZMod 3) ≃ₗ[ZMod 3] (Fin n → ZMod 3)) y
    rw [ct_oc_stabBackEquiv_apply]
    simp


private def ct_oc_shellCard {n : ℕ} (a : Fin n → ZMod 3) (c : ZMod 3) : Nat :=
  (Finset.univ.filter (fun v : Fin n → ZMod 3 => ct_oc_Q a v = c)).card

private lemma ct_oc_shellCard_eq {n : ℕ} [NeZero n] (a : Fin n → ZMod 3) :
    Nat.card (↑{v : Fin n → ZMod 3 | ct_oc_Q a v = a 0}) = ct_oc_shellCard a (a 0) := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

private lemma ct_oc_stabilizer_card {n : ℕ} (a : Fin (n+1) → ZMod 3) (ha : a 0 ≠ 0) :
    Nat.card (MulAction.stabilizer (QuadraticMap.orthogonalGroup (ct_oc_Q a)) (ct_oc_e0 n)) =
      Nat.card (QuadraticMap.orthogonalGroup (ct_oc_Q (ct_oc_tail a))) :=
  Nat.card_congr (ct_oc_stabilizerEquiv a ha)

private lemma ct_oc_orbit_eq {n : ℕ} (a : Fin (n+1) → ZMod 3) (ha : a 0 ≠ 0) :
    MulAction.orbit (QuadraticMap.orthogonalGroup (ct_oc_Q a)) (ct_oc_e0 n)
      = {v : Fin (n+1) → ZMod 3 | ct_oc_Q a v = a 0} := by
  ext v
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, rfl⟩
    show ct_oc_Q a (g • ct_oc_e0 n) = a 0
    rw [Subgroup.smul_def, LinearEquiv.smul_def]
    rw [QuadraticMap.map_app_of_mem_orthogonalGroup g.2, ct_oc_Q_e0]
  · intro hv
    have hxy : ct_oc_Q a (ct_oc_e0 n) = ct_oc_Q a v := by rw [ct_oc_Q_e0, hv]
    have hy : ct_oc_Q a v ≠ 0 := by rw [hv]; exact ha
    have : NeZero (2 : ZMod 3) := ⟨by decide⟩
    obtain ⟨f, hf⟩ := QuadraticMap.exists_isometryEquiv_apply_eq_of_map_eq (Q := ct_oc_Q a) hxy hy
    refine ⟨(QuadraticMap.orthogonalGroupEquivIsometryEquiv (ct_oc_Q a)).symm f, ?_⟩
    rw [Subgroup.smul_def, LinearEquiv.smul_def]
    simpa using hf

private lemma ct_oc_card_succ {n : ℕ} (a : Fin (n+1) → ZMod 3) (ha : a 0 ≠ 0) :
    Nat.card (QuadraticMap.orthogonalGroup (ct_oc_Q a)) =
      ct_oc_shellCard a (a 0) *
        Nat.card (QuadraticMap.orthogonalGroup (ct_oc_Q (ct_oc_tail a))) := by
  let G := QuadraticMap.orthogonalGroup (ct_oc_Q a)
  have horb := ct_oc_orbit_eq a ha
  calc Nat.card G
      = Nat.card (MulAction.orbit G (ct_oc_e0 n) ×
          MulAction.stabilizer G (ct_oc_e0 n)) :=
        (Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (G := G)
          (b := ct_oc_e0 n))).symm
    _ = Nat.card (MulAction.orbit G (ct_oc_e0 n)) *
          Nat.card (MulAction.stabilizer G (ct_oc_e0 n)) := Nat.card_prod _ _
    _ = ct_oc_shellCard a (a 0) *
          Nat.card (MulAction.stabilizer G (ct_oc_e0 n)) := by
        rw [Nat.card_congr (Set.equivOfEq horb), ct_oc_shellCard_eq]
    _ = ct_oc_shellCard a (a 0) *
          Nat.card (QuadraticMap.orthogonalGroup (ct_oc_Q (ct_oc_tail a))) := by
        rw [ct_oc_stabilizer_card a ha]


private def ct_oc_count : (n : ℕ) → (Fin n → ZMod 3) → Nat
  | 0, _ => 1
  | 1, _ => 2
  | (n+2), a => ct_oc_shellCard a (a 0) * ct_oc_count (n+1) (ct_oc_tail a)

private lemma ct_oc_card_count (n : ℕ) : ∀ a : Fin n → ZMod 3, (∀ i, a i ≠ 0) →
    Nat.card (QuadraticMap.orthogonalGroup (ct_oc_Q a)) = ct_oc_count n a := by
  induction n with
  | zero =>
      intro a ha
      rw [ct_oc_count]
      refine Nat.card_eq_one_iff_exists.mpr ⟨1, fun g => ?_⟩
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      have hx : x = 0 := Subsingleton.elim x 0
      rw [hx, map_zero]
      rfl
  | succ n ih =>
      cases n with
      | zero =>
          intro a ha
          have : NeZero (2 : ZMod 3) := ⟨by decide⟩
          rw [ct_oc_count]
          have hQ : ct_oc_Q a ≠ 0 := by
            intro h
            have h0 : ct_oc_Q a (ct_oc_e0 0) = 0 := by rw [h]; rfl
            rw [ct_oc_Q_e0] at h0
            exact ha 0 h0
          have hfin : Module.finrank (ZMod 3) (Fin 1 → ZMod 3) = 1 := by
            simp
          exact QuadraticMap.card_orthogonalGroup_of_finrank_eq_one hQ hfin
      | succ n =>
          intro a ha
          rw [ct_oc_card_succ a (ha 0)]
          have htail : ∀ i, ct_oc_tail a i ≠ 0 := fun i => ha i.succ
          rw [ih (ct_oc_tail a) htail]
          rfl


private lemma ct_oc_plane_to_pair {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V)
    (h : ∃ W : Submodule (ZMod 3) V, Module.finrank (ZMod 3) W = 2 ∧ ∀ w ∈ W, Q w = 0) :
    ∃ u v : V, Q u = 0 ∧ Q v = 0 ∧ QuadraticMap.polar Q u v = 0 ∧
      u ≠ 0 ∧ v ≠ 0 ∧ v ≠ u ∧ v ≠ -u := by
  obtain ⟨W, hW, hWQ⟩ := h
  have hne : W ≠ ⊥ := by
    intro hbot
    have : Module.finrank (ZMod 3) W = 0 := by rw [hbot]; simp
    omega
  obtain ⟨u, huW, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hspan_fin : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) {u}) = 1 :=
    finrank_span_singleton hu0
  have hspan_le : Submodule.span (ZMod 3) {u} ≤ W :=
    Submodule.span_le.mpr (by simpa using huW)
  have hspan_ne : Submodule.span (ZMod 3) {u} ≠ W := by
    intro heq
    rw [heq, hW] at hspan_fin
    omega
  have hlt : Submodule.span (ZMod 3) {u} < W := lt_of_le_of_ne hspan_le hspan_ne
  obtain ⟨-, v, hvW, hvspan⟩ := SetLike.lt_iff_le_and_exists.mp hlt
  have hv0 : v ≠ 0 := by
    intro hv
    exact hvspan (hv ▸ Submodule.zero_mem _)
  have hvu : v ≠ u := by
    intro hv
    exact hvspan (by rw [hv]; exact Submodule.mem_span_singleton_self u)
  have hvn : v ≠ -u := by
    intro hv
    refine hvspan ?_
    rw [hv]
    exact Submodule.neg_mem (Submodule.span (ZMod 3) {u})
      (Submodule.mem_span_singleton_self u)
  have hsum : Q (u + v) = 0 := hWQ (u + v) (W.add_mem huW hvW)
  have hpolar : QuadraticMap.polar Q u v = 0 := by
    rw [QuadraticMap.polar, hsum, hWQ u huW, hWQ v hvW]
    abel
  exact ⟨u, v, hWQ u huW, hWQ v hvW, hpolar, hu0, hv0, hvu, hvn⟩

private lemma ct_oc_pair_to_plane {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V) {u v : V} (hu : Q u = 0) (hv : Q v = 0)
    (huv : QuadraticMap.polar Q u v = 0) (hu0 : u ≠ 0) (hv0 : v ≠ 0)
    (hvu : v ≠ u) (hvn : v ≠ -u) :
    ∃ W : Submodule (ZMod 3) V, Module.finrank (ZMod 3) W = 2 ∧ ∀ w ∈ W, Q w = 0 := by
  have hind : LinearIndependent (ZMod 3) ![u, v] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    constructor
    · by_contra hs
      have ht : t ≠ 0 := by
        intro ht0
        rw [ht0, zero_smul, add_zero] at hst
        exact hs ((smul_eq_zero.mp hst).resolve_right hu0)
      have hv' : v = (-(t⁻¹ * s)) • u := by
        have h1 : t • v = -(s • u) := by
          rw [eq_neg_iff_add_eq_zero, add_comm]
          exact hst
        calc v = (t⁻¹ * t) • v := by rw [inv_mul_cancel₀ ht, one_smul]
          _ = t⁻¹ • (t • v) := by rw [smul_smul]
          _ = t⁻¹ • (-(s • u)) := by rw [h1]
          _ = (-(t⁻¹ * s)) • u := by rw [smul_neg, smul_smul, neg_smul]
      have hcases : -(t⁻¹ * s) = 0 ∨ -(t⁻¹ * s) = 1 ∨ -(t⁻¹ * s) = -1 := by
        have h : ∀ d : ZMod 3, d = 0 ∨ d = 1 ∨ d = -1 := by decide
        exact h _
      rcases hcases with h0 | h1 | h1
      · rw [h0, zero_smul] at hv'; exact hv0 hv'
      · rw [h1, one_smul] at hv'; exact hvu hv'
      · rw [h1, neg_one_smul] at hv'; exact hvn hv'
    · by_contra ht
      have hs : s ≠ 0 := by
        intro hs0
        rw [hs0, zero_smul, zero_add] at hst
        exact ht ((smul_eq_zero.mp hst).resolve_right hv0)
      have hu' : u = (-(s⁻¹ * t)) • v := by
        have h1 : s • u = -(t • v) := by
          rw [eq_neg_iff_add_eq_zero]
          exact hst
        calc u = (s⁻¹ * s) • u := by rw [inv_mul_cancel₀ hs, one_smul]
          _ = s⁻¹ • (s • u) := by rw [smul_smul]
          _ = s⁻¹ • (-(t • v)) := by rw [h1]
          _ = (-(s⁻¹ * t)) • v := by rw [smul_neg, smul_smul, neg_smul]
      have hcases : -(s⁻¹ * t) = 0 ∨ -(s⁻¹ * t) = 1 ∨ -(s⁻¹ * t) = -1 := by
        have h : ∀ d : ZMod 3, d = 0 ∨ d = 1 ∨ d = -1 := by decide
        exact h _
      rcases hcases with h0 | h1 | h1
      · rw [h0, zero_smul] at hu'; exact hu0 hu'
      · rw [h1, one_smul] at hu'; exact hvu hu'.symm
      · rw [h1, neg_one_smul] at hu'
        exact hvn (by rw [hu']; simp)
  refine ⟨Submodule.span (ZMod 3) ({u, v} : Set V), ?_, ?_⟩
  · have hrange : Set.range ![u, v] = ({u, v} : Set V) := by
      ext x
      simp [or_comm]
    rw [← hrange, finrank_span_eq_card hind]
    simp
  · intro w hw
    rw [Submodule.mem_span_pair] at hw
    obtain ⟨a, b, rfl⟩ := hw
    calc Q (a • u + b • v)
        = Q (a • u) + Q (b • v) + QuadraticMap.polar Q (a • u) (b • v) :=
          QuadraticMap.map_add Q _ _
      _ = (a * a) • Q u + (b * b) • Q v + a * b • QuadraticMap.polar Q u v := by
          simp only [QuadraticMap.map_smul, QuadraticMap.polar_smul_left,
            QuadraticMap.polar_smul_right, smul_eq_mul]
          ring
      _ = 0 := by rw [hu, hv, huv]; simp


private def ct_oc_isoPair {n : ℕ} (a : Fin n → ZMod 3) : Prop :=
  ∃ u v : Fin n → ZMod 3, ct_oc_Q a u = 0 ∧ ct_oc_Q a v = 0 ∧
    QuadraticMap.polar (ct_oc_Q a) u v = 0 ∧
      u ≠ 0 ∧ v ≠ 0 ∧ v ≠ u ∧ v ≠ -u

private instance ct_oc_instDecidableIsoPair {n : ℕ} (a : Fin n → ZMod 3) :
    Decidable (ct_oc_isoPair a) := by
  dsimp only [ct_oc_isoPair]
  infer_instance

private lemma ct_oc_isoPair_iff_plane {n : ℕ} (a : Fin n → ZMod 3) :
    ct_oc_isoPair a ↔
      ∃ W : Submodule (ZMod 3) (Fin n → ZMod 3),
        Module.finrank (ZMod 3) W = 2 ∧ ∀ w ∈ W, ct_oc_Q a w = 0 := by
  constructor
  · rintro ⟨u, v, hu, hv, huv, hu0, hv0, hvu, hvn⟩
    exact ct_oc_pair_to_plane (ct_oc_Q a) hu hv huv hu0 hv0 hvu hvn
  · intro h
    exact ct_oc_plane_to_pair (ct_oc_Q a) h

private lemma ct_oc_count_four_of_pair :
    ∀ a : Fin 4 → ZMod 3, (∀ i, a i ≠ 0) → ct_oc_isoPair a → ct_oc_count 4 a = 1152 := by
  intro a ha hp
  by_contra hne
  have hmem : a ∈ Finset.univ.filter (fun b : Fin 4 → ZMod 3 =>
      (∀ i, b i ≠ 0) ∧ ct_oc_isoPair b ∧ ct_oc_count 4 b ≠ 1152) := by
    simp [ha, hp, hne]
  have hempty : (Finset.univ.filter (fun b : Fin 4 → ZMod 3 =>
      (∀ i, b i ≠ 0) ∧ ct_oc_isoPair b ∧ ct_oc_count 4 b ≠ 1152)) = ∅ :=
    Finset.card_eq_zero.mp (by decide +kernel)
  rw [hempty] at hmem
  simp at hmem

private lemma ct_oc_count_four_of_not_pair :
    ∀ a : Fin 4 → ZMod 3, (∀ i, a i ≠ 0) → ¬ ct_oc_isoPair a → ct_oc_count 4 a = 1440 := by
  intro a ha hp
  by_contra hne
  have hmem : a ∈ Finset.univ.filter (fun b : Fin 4 → ZMod 3 =>
      (∀ i, b i ≠ 0) ∧ ¬ ct_oc_isoPair b ∧ ct_oc_count 4 b ≠ 1440) := by
    simp [ha, hp, hne]
  have hempty : (Finset.univ.filter (fun b : Fin 4 → ZMod 3 =>
      (∀ i, b i ≠ 0) ∧ ¬ ct_oc_isoPair b ∧ ct_oc_count 4 b ≠ 1440)) = ∅ :=
    Finset.card_eq_zero.mp (by decide +kernel)
  rw [hempty] at hmem
  simp at hmem

private lemma ct_oc_count_five :
    ∀ a : Fin 5 → ZMod 3, (∀ i, a i ≠ 0) → ct_oc_count 5 a = 103680 := by
  intro a ha
  by_contra hne
  have hmem : a ∈ Finset.univ.filter (fun b : Fin 5 → ZMod 3 =>
      (∀ i, b i ≠ 0) ∧ ct_oc_count 5 b ≠ 103680) := by
    simp [ha, hne]
  have hempty : (Finset.univ.filter (fun b : Fin 5 → ZMod 3 =>
      (∀ i, b i ≠ 0) ∧ ct_oc_count 5 b ≠ 103680)) = ∅ :=
    Finset.card_eq_zero.mp (by decide +kernel)
  rw [hempty] at hmem
  simp at hmem


private lemma ct_oc_count_three :
    ∀ a : Fin 3 → ZMod 3, (∀ i, a i ≠ 0) → ct_oc_count 3 a = 48 := by
  intro a ha
  by_contra hne
  have hmem : a ∈ Finset.univ.filter (fun b : Fin 3 → ZMod 3 =>
      (∀ i, b i ≠ 0) ∧ ct_oc_count 3 b ≠ 48) := by
    simp [ha, hne]
  have hempty : (Finset.univ.filter (fun b : Fin 3 → ZMod 3 =>
      (∀ i, b i ≠ 0) ∧ ct_oc_count 3 b ≠ 48)) = ∅ :=
    Finset.card_eq_zero.mp (by decide +kernel)
  rw [hempty] at hmem
  simp at hmem


private lemma ct_oc_exists_diag {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] (Q : QuadraticForm (ZMod 3) V)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (n : ℕ)
    (hd : Module.finrank (ZMod 3) V = n) :
    ∃ a : Fin n → ZMod 3, (∀ i, a i ≠ 0) ∧ Nonempty (Q.IsometryEquiv (ct_oc_Q a)) := by
  have : Invertible (2 : ZMod 3) := invertibleOfNonzero (by decide)
  have hQnd : Q.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp hQ
  have hassoc : (QuadraticMap.associated Q).Nondegenerate :=
    QuadraticMap.nondegenerate_associated_iff.mpr hQnd
  have hsep : (QuadraticMap.associated Q).SeparatingLeft :=
    (QuadraticForm.associated_isSymm (ZMod 3) Q).isRefl.nondegenerate_iff_separatingLeft.mp hassoc
  obtain ⟨w, ⟨e⟩⟩ :=
    QuadraticForm.equivalent_weightedSumSquares_units_of_nondegenerate' Q hsep
  let efin : Fin n ≃ Fin (Module.finrank (ZMod 3) V) := (finCongr hd).symm
  let a : Fin n → ZMod 3 := fun i => (w (efin i) : ZMod 3)
  have ha : ∀ i, a i ≠ 0 := fun i => (w (efin i)).ne_zero
  have hreindex : (QuadraticMap.weightedSumSquares (ZMod 3) w).IsometryEquiv
      (QuadraticMap.weightedSumSquares (ZMod 3) (w ∘ efin)) :=
    QuadraticForm.isometryEquivWeightedSumSquaresReindex w efin
  have hdiag : ct_oc_Q a = QuadraticMap.weightedSumSquares (ZMod 3) (w ∘ efin) := by
    rw [ct_oc_Q, QuadraticMap.weightedSumSquares_units]
    rfl
  have hEq : Q.IsometryEquiv (QuadraticMap.weightedSumSquares (ZMod 3) (w ∘ efin)) =
      Q.IsometryEquiv (ct_oc_Q a) := by rw [hdiag]
  exact ⟨a, ha, ⟨hEq ▸ e.trans hreindex⟩⟩

private lemma ct_oc_card_congr {V W : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [AddCommGroup W] [Module (ZMod 3) W]
    {Q : QuadraticForm (ZMod 3) V} {Q' : QuadraticForm (ZMod 3) W}
    (e : Q.IsometryEquiv Q') :
    Nat.card (QuadraticMap.orthogonalGroup Q) = Nat.card (QuadraticMap.orthogonalGroup Q') :=
  Nat.card_congr (QuadraticMap.orthogonalGroupCongr e).toEquiv


private lemma ct_oc_plane_map {V V' : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [AddCommGroup V'] [Module (ZMod 3) V']
    {Q : QuadraticForm (ZMod 3) V} {Q' : QuadraticForm (ZMod 3) V'}
    (e : Q.IsometryEquiv Q') :
    (∃ W : Submodule (ZMod 3) V, Module.finrank (ZMod 3) W = 2 ∧ ∀ w ∈ W, Q w = 0) →
    ∃ W' : Submodule (ZMod 3) V', Module.finrank (ZMod 3) W' = 2 ∧ ∀ w ∈ W', Q' w = 0 := by
  rintro ⟨W, hW, hWQ⟩
  refine ⟨W.map (e.toLinearEquiv : V →ₗ[ZMod 3] V'), ?_, ?_⟩
  · rw [LinearEquiv.finrank_map_eq, hW]
  · intro w hw
    rw [Submodule.mem_map] at hw
    obtain ⟨v, hvW, rfl⟩ := hw
    exact (e.map_app' v).trans (hWQ v hvW)

private lemma ct_oc_prod_fst_coord_zero {M1 M2 : Type} [AddCommGroup M1] [Module (ZMod 3) M1]
    [AddCommGroup M2] [Module (ZMod 3) M2]
    {Q1 : QuadraticForm (ZMod 3) M1} {Q2 : QuadraticForm (ZMod 3) M2} {x : M1}
    (hspan : ∀ m1 : M1, ∃ a : ZMod 3, a • x = m1) (hx : Q1 x ≠ 0)
    (g : QuadraticMap.orthogonalGroup (Q1.prod Q2))
    (hg : (g.1 : (M1 × M2) ≃ₗ[ZMod 3] (M1 × M2)) (x, 0) = (x, 0)) (m2 : M2) :
    ((g.1 : (M1 × M2) ≃ₗ[ZMod 3] (M1 × M2)) (0, m2)).1 = 0 := by
  obtain ⟨a, ha⟩ := hspan ((g.1 : (M1 × M2) ≃ₗ[ZMod 3] (M1 × M2)) (0, m2)).1
  have hpolar := QuadraticMap.polar_apply_of_mem_orthogonalGroup g.2 (0, m2) (x, 0)
  rw [hg, QuadraticMap.polar_prod, QuadraticMap.polar_prod] at hpolar
  simp only [QuadraticMap.polar_zero_left, QuadraticMap.polar_zero_right, add_zero] at hpolar
  rw [← ha, QuadraticMap.polar_smul_left, QuadraticMap.polar_self] at hpolar
  have hne : (2 : ZMod 3) * Q1 x ≠ 0 := mul_ne_zero (by decide) hx
  have ha0 : a = 0 := by
    have : a * (2 * Q1 x) = 0 := by simpa [nsmul_eq_mul, mul_assoc] using hpolar
    exact (mul_eq_zero.mp this).resolve_right hne
  rw [← ha, ha0, zero_smul]

private lemma ct_oc_prod_fst_fix {M1 M2 : Type} [AddCommGroup M1] [Module (ZMod 3) M1]
    [AddCommGroup M2] [Module (ZMod 3) M2]
    {Q1 : QuadraticForm (ZMod 3) M1} {Q2 : QuadraticForm (ZMod 3) M2} {x : M1}
    (hspan : ∀ m1 : M1, ∃ a : ZMod 3, a • x = m1) (g : QuadraticMap.orthogonalGroup (Q1.prod Q2))
    (hg : (g.1 : (M1 × M2) ≃ₗ[ZMod 3] (M1 × M2)) (x, 0) = (x, 0)) (m1 : M1) :
    (g.1 : (M1 × M2) ≃ₗ[ZMod 3] (M1 × M2)) (m1, 0) = (m1, 0) := by
  obtain ⟨a, ha⟩ := hspan m1
  rw [← ha]
  have h : ((a • x : M1), (0 : M2)) = a • (x, (0 : M2)) := by ext <;> simp
  rw [h, map_smul, hg]

private def ct_oc_prodFirstLinear {M1 M2 : Type} [AddCommGroup M1] [Module (ZMod 3) M1]
    [AddCommGroup M2] [Module (ZMod 3) M2]
    (Q1 : QuadraticForm (ZMod 3) M1) (Q2 : QuadraticForm (ZMod 3) M2)
    (g : QuadraticMap.orthogonalGroup (Q1.prod Q2)) : M2 →ₗ[ZMod 3] M2 where
  toFun m2 := ((g.1 : (M1 × M2) ≃ₗ[ZMod 3] (M1 × M2)) (0, m2)).2
  map_add' a b := by
    have h : ((0 : M1), a + b) = (0, a) + (0, b) := by ext <;> simp
    rw [h, map_add]
    rfl
  map_smul' c a := by
    have h : ((0 : M1), c • a) = c • ((0 : M1), a) := by ext <;> simp
    rw [h, map_smul]
    rfl

private lemma ct_oc_prodFirstLinear_injective {M1 M2 : Type} [AddCommGroup M1]
    [Module (ZMod 3) M1] [AddCommGroup M2] [Module (ZMod 3) M2]
    {Q1 : QuadraticForm (ZMod 3) M1} {Q2 : QuadraticForm (ZMod 3) M2} {x : M1}
    (hspan : ∀ m1 : M1, ∃ a : ZMod 3, a • x = m1) (hx : Q1 x ≠ 0)
    (g : QuadraticMap.orthogonalGroup (Q1.prod Q2))
    (hg : (g.1 : (M1 × M2) ≃ₗ[ZMod 3] (M1 × M2)) (x, 0) = (x, 0)) :
    Function.Injective (ct_oc_prodFirstLinear Q1 Q2 g) := by
  intro a b hab
  have hsub : ((g.1 : (M1 × M2) ≃ₗ[ZMod 3] (M1 × M2)) ((0 : M1), a - b)).2 = 0 := by
    have h : ((0 : M1), a - b) = (0, a) - (0, b) := by ext <;> simp
    have hab' : ((g.1 : (M1 × M2) ≃ₗ[ZMod 3] (M1 × M2)) (0, a)).2 =
        ((g.1 : (M1 × M2) ≃ₗ[ZMod 3] (M1 × M2)) (0, b)).2 := hab
    rw [h, map_sub]
    simpa using sub_eq_zero.mpr hab'
  have hfst := ct_oc_prod_fst_coord_zero hspan hx g hg (a - b)
  have hzero : (g.1 : (M1 × M2) ≃ₗ[ZMod 3] (M1 × M2)) ((0 : M1), a - b) = 0 := by
    rw [← Prod.mk_zero_zero]
    exact Prod.ext hfst hsub
  have h2 := (g.1 : (M1 × M2) ≃ₗ[ZMod 3] (M1 × M2)).injective
    (hzero.trans (map_zero (g.1 : (M1 × M2) ≃ₗ[ZMod 3] (M1 × M2))).symm)
  have : a - b = 0 := by simpa using congrArg Prod.snd h2
  exact sub_eq_zero.mp this

private noncomputable def ct_oc_prodFirstEquiv {M1 M2 : Type} [AddCommGroup M1]
    [Module (ZMod 3) M1] [AddCommGroup M2] [Module (ZMod 3) M2]
    {Q1 : QuadraticForm (ZMod 3) M1} {Q2 : QuadraticForm (ZMod 3) M2} {x : M1}
    [FiniteDimensional (ZMod 3) M2]
    (hspan : ∀ m1 : M1, ∃ a : ZMod 3, a • x = m1) (hx : Q1 x ≠ 0)
    (g : QuadraticMap.orthogonalGroup (Q1.prod Q2))
    (hg : (g.1 : (M1 × M2) ≃ₗ[ZMod 3] (M1 × M2)) (x, 0) = (x, 0)) : M2 ≃ₗ[ZMod 3] M2 :=
  LinearEquiv.ofInjectiveEndo (ct_oc_prodFirstLinear Q1 Q2 g)
    (ct_oc_prodFirstLinear_injective hspan hx g hg)

private lemma ct_oc_prodFirstEquiv_apply {M1 M2 : Type} [AddCommGroup M1]
    [Module (ZMod 3) M1] [AddCommGroup M2] [Module (ZMod 3) M2]
    {Q1 : QuadraticForm (ZMod 3) M1} {Q2 : QuadraticForm (ZMod 3) M2} {x : M1}
    [FiniteDimensional (ZMod 3) M2]
    (hspan : ∀ m1 : M1, ∃ a : ZMod 3, a • x = m1) (hx : Q1 x ≠ 0)
    (g : QuadraticMap.orthogonalGroup (Q1.prod Q2))
    (hg : (g.1 : (M1 × M2) ≃ₗ[ZMod 3] (M1 × M2)) (x, 0) = (x, 0)) (m2 : M2) :
    ct_oc_prodFirstEquiv hspan hx g hg m2
      = ((g.1 : (M1 × M2) ≃ₗ[ZMod 3] (M1 × M2)) (0, m2)).2 := by
  rw [ct_oc_prodFirstEquiv, LinearEquiv.coe_ofInjectiveEndo]
  rfl

noncomputable def orthogonalGroupProdFirstStabilizer {M1 M2 : Type} [AddCommGroup M1]
    [Module (ZMod 3) M1] [AddCommGroup M2] [Module (ZMod 3) M2]
    [FiniteDimensional (ZMod 3) M2]
    (Q1 : QuadraticForm (ZMod 3) M1) (Q2 : QuadraticForm (ZMod 3) M2) (x : M1)
    (hspan : ∀ m1 : M1, ∃ a : ZMod 3, a • x = m1) (hx : Q1 x ≠ 0) :
    {g : QuadraticMap.orthogonalGroup (Q1.prod Q2) //
      (g.1 : (M1 × M2) ≃ₗ[ZMod 3] (M1 × M2)) (x, 0) = (x, 0)} ≃
      QuadraticMap.orthogonalGroup Q2 where
  toFun g := by
    refine ⟨ct_oc_prodFirstEquiv hspan hx g.1 g.2, ?_⟩
    rw [QuadraticMap.mem_orthogonalGroup_iff]
    intro m2
    rw [ct_oc_prodFirstEquiv_apply]
    have hfst := ct_oc_prod_fst_coord_zero hspan hx g.1 g.2 m2
    have hQ := QuadraticMap.map_app_of_mem_orthogonalGroup g.1.2 (0, m2)
    simpa [QuadraticMap.prod_apply, hfst] using hQ
  invFun f := ⟨QuadraticMap.orthogonalGroupProd Q1 Q2 (1, f), by
    rw [QuadraticMap.coe_orthogonalGroupProd]
    show (((x : M1), (f.1 : M2 ≃ₗ[ZMod 3] M2) 0) : M1 × M2) = (x, 0)
    simp⟩
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    apply LinearEquiv.ext
    intro p
    obtain ⟨m1, m2⟩ := p
    rw [QuadraticMap.coe_orthogonalGroupProd]
    change (((m1 : M1), (ct_oc_prodFirstEquiv hspan hx g.1 g.2) m2) : M1 × M2) =
      (g.1.1 : (M1 × M2) ≃ₗ[ZMod 3] (M1 × M2)) (m1, m2)
    have hsplit : ((m1, m2) : M1 × M2) = (m1, 0) + ((0 : M1), m2) := by ext <;> simp
    rw [hsplit, map_add, ct_oc_prod_fst_fix hspan g.1 g.2 m1, ct_oc_prodFirstEquiv_apply]
    refine Prod.ext ?_ ?_
    · change (m1 : M1) = m1 + ((g.1.1 : (M1 × M2) ≃ₗ[ZMod 3] (M1 × M2)) (0, m2)).1
      rw [ct_oc_prod_fst_coord_zero hspan hx g.1 g.2 m2, add_zero]
    · change (((g.1.1 : (M1 × M2) ≃ₗ[ZMod 3] (M1 × M2)) (0, m2)).2 : M2) =
        0 + ((g.1.1 : (M1 × M2) ≃ₗ[ZMod 3] (M1 × M2)) (0, m2)).2
      rw [zero_add]
  right_inv f := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro m2
    dsimp
    change (ct_oc_prodFirstEquiv hspan hx
        (QuadraticMap.orthogonalGroupProd Q1 Q2 (1, f)) _) m2 =
      (f.1 : M2 ≃ₗ[ZMod 3] M2) m2
    rw [ct_oc_prodFirstEquiv_apply, QuadraticMap.coe_orthogonalGroupProd]
    simp

noncomputable def orthogonalGroupStabilizerCongr {V V' : Type} [AddCommGroup V]
    [Module (ZMod 3) V] [AddCommGroup V'] [Module (ZMod 3) V']
    {Q : QuadraticForm (ZMod 3) V} {Q' : QuadraticForm (ZMod 3) V'}
    (e : Q.IsometryEquiv Q') (x : V) :
    {g : QuadraticMap.orthogonalGroup Q // (g : V ≃ₗ[ZMod 3] V) x = x} ≃
      {h : QuadraticMap.orthogonalGroup Q' //
        (h : V' ≃ₗ[ZMod 3] V') (e.toLinearEquiv x) = e.toLinearEquiv x} where
  toFun g := ⟨QuadraticMap.orthogonalGroupCongr e g.1, by
    rw [QuadraticMap.coe_orthogonalGroupCongr_apply, LinearEquiv.symm_apply_apply]
    exact congrArg e.toLinearEquiv g.2⟩
  invFun h := ⟨(QuadraticMap.orthogonalGroupCongr e).symm h.1, by
    rw [QuadraticMap.coe_orthogonalGroupCongr_symm_apply, h.2, LinearEquiv.symm_apply_apply]⟩
  left_inv g := Subtype.ext (by simp)
  right_inv h := Subtype.ext (by simp)

theorem card_orthogonalGroup_three {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : Module.finrank (ZMod 3) V = 3) :
    Nat.card (QuadraticMap.orthogonalGroup Q) = 48 := by
  obtain ⟨a, ha, ⟨e⟩⟩ := ct_oc_exists_diag Q hQ 3 hd
  rw [ct_oc_card_congr e, ct_oc_card_count 3 a ha]
  exact ct_oc_count_three a ha

theorem card_orthogonalGroup_four_plus {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : Module.finrank (ZMod 3) V = 4)
    (hplus : ∃ W : Submodule (ZMod 3) V, Module.finrank (ZMod 3) W = 2 ∧ ∀ w ∈ W, Q w = 0) :
    Nat.card (QuadraticMap.orthogonalGroup Q) = 1152 := by
  obtain ⟨a, ha, ⟨e⟩⟩ := ct_oc_exists_diag Q hQ 4 hd
  rw [ct_oc_card_congr e, ct_oc_card_count 4 a ha]
  exact ct_oc_count_four_of_pair a ha ((ct_oc_isoPair_iff_plane a).mpr (ct_oc_plane_map e hplus))

theorem card_orthogonalGroup_four_minus {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : Module.finrank (ZMod 3) V = 4)
    (hminus : ¬ ∃ W : Submodule (ZMod 3) V, Module.finrank (ZMod 3) W = 2 ∧ ∀ w ∈ W, Q w = 0) :
    Nat.card (QuadraticMap.orthogonalGroup Q) = 1440 := by
  obtain ⟨a, ha, ⟨e⟩⟩ := ct_oc_exists_diag Q hQ 4 hd
  rw [ct_oc_card_congr e, ct_oc_card_count 4 a ha]
  refine ct_oc_count_four_of_not_pair a ha (fun hp => hminus ?_)
  exact ct_oc_plane_map e.symm ((ct_oc_isoPair_iff_plane a).mp hp)

theorem card_orthogonalGroup_of_finrank_eq_five {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : Module.finrank (ZMod 3) V = 5) : Nat.card (QuadraticMap.orthogonalGroup Q) = 103680 := by
  obtain ⟨a, ha, ⟨e⟩⟩ := ct_oc_exists_diag Q hQ 5 hd
  rw [ct_oc_card_congr e, ct_oc_card_count 5 a ha]
  exact ct_oc_count_five a ha

theorem card_stabilizer_eq_perp_orthogonalGroup
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V)
    (x : V) (hx : Q x ≠ 0) :
    Nat.card {g : QuadraticMap.orthogonalGroup Q //
      (g : V ≃ₗ[ZMod 3] V) x = x} =
    Nat.card (QuadraticMap.orthogonalGroup
      (Q.restrict (LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q)
        (Submodule.span (ZMod 3) {x})))) := by
  have hByy : QuadraticMap.polarBilin Q x x ≠ 0 := by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self]
    simpa [nsmul_eq_mul] using mul_ne_zero (by decide : (2 : ZMod 3) ≠ 0) hx
  let W : Submodule (ZMod 3) V :=
    LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) (Submodule.span (ZMod 3) {x})
  have hcomp : IsCompl (Submodule.span (ZMod 3) {x}) W :=
    LinearMap.BilinForm.isCompl_span_singleton_orthogonal (B := QuadraticMap.polarBilin Q) hByy
  let e := QuadraticMap.IsometryEquiv.prodRestrictOrthogonal Q (Submodule.span (ZMod 3) {x}) hcomp
  let x1 : Submodule.span (ZMod 3) {x} := ⟨x, Submodule.mem_span_singleton_self x⟩
  have hx1 : (Q.restrict (Submodule.span (ZMod 3) {x})) x1 ≠ 0 := by
    simpa [x1, QuadraticMap.restrict_apply] using hx
  have hspan : ∀ m1 : Submodule.span (ZMod 3) {x}, ∃ a : ZMod 3, a • x1 = m1 := by
    intro m1
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp m1.2
    exact ⟨a, Subtype.ext ha⟩
  have hprod : Nat.card {g : QuadraticMap.orthogonalGroup
        ((Q.restrict (Submodule.span (ZMod 3) {x})).prod (Q.restrict W)) //
        (g : ((Submodule.span (ZMod 3) {x}) × W) ≃ₗ[ZMod 3]
          ((Submodule.span (ZMod 3) {x}) × W)) (x1, 0) = (x1, 0)} =
      Nat.card (QuadraticMap.orthogonalGroup (Q.restrict W)) :=
    Nat.card_congr (orthogonalGroupProdFirstStabilizer (Q.restrict (Submodule.span (ZMod 3) {x}))
      (Q.restrict W) x1 hspan hx1)
  have himage : e.toLinearEquiv (x1, (0 : W)) = x := by
    dsimp only [e]
    change (QuadraticMap.IsometryEquiv.prodRestrictOrthogonal Q (Submodule.span (ZMod 3) {x})
      hcomp) (x1, (0 : W)) = x
    rw [QuadraticMap.IsometryEquiv.prodRestrictOrthogonal_apply]
    simp [x1]
  have hconj : Nat.card {g : QuadraticMap.orthogonalGroup
        ((Q.restrict (Submodule.span (ZMod 3) {x})).prod (Q.restrict W)) //
        (g : ((Submodule.span (ZMod 3) {x}) × W) ≃ₗ[ZMod 3]
          ((Submodule.span (ZMod 3) {x}) × W)) (x1, 0) = (x1, 0)} =
      Nat.card {g : QuadraticMap.orthogonalGroup Q // (g : V ≃ₗ[ZMod 3] V) x = x} := by
    have h := Nat.card_congr (orthogonalGroupStabilizerCongr e (x1, (0 : W)))
    rwa [himage] at h
  exact hconj.symm.trans hprod

theorem card_stabilizer_five {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : Module.finrank (ZMod 3) V = 5) (x : V) (hx : Q x ≠ 0) :
    Nat.card {g : QuadraticMap.orthogonalGroup Q // (g : V ≃ₗ[ZMod 3] V) x = x} = 1152 ∨
      Nat.card {g : QuadraticMap.orthogonalGroup Q // (g : V ≃ₗ[ZMod 3] V) x = x} = 1440 := by
  have hx0 : x ≠ 0 := fun h => hx (by rw [h, QuadraticMap.map_zero])
  have hByy : QuadraticMap.polarBilin Q x x ≠ 0 := by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self]
    simpa [nsmul_eq_mul] using mul_ne_zero (by decide : (2 : ZMod 3) ≠ 0) hx
  let W : Submodule (ZMod 3) V :=
    LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) (Submodule.span (ZMod 3) {x})
  have hWfin : Module.finrank (ZMod 3) W = 4 := by
    have hspan_fin : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) {x}) = 1 :=
      finrank_span_singleton hx0
    have hfin := LinearMap.BilinForm.finrank_orthogonal (B := QuadraticMap.polarBilin Q) hQ
      (Submodule.span (ZMod 3) {x})
    dsimp only [W]
    rw [hfin, hd, hspan_fin]
  have hQ2nd : (QuadraticMap.polarBilin (Q.restrict W)).Nondegenerate := by
    rw [QuadraticMap.polarBilin_restrict]
    exact LinearMap.BilinForm.restrict_nondegenerate_orthogonal_spanSingleton
      (QuadraticMap.polarBilin Q) hQ (QuadraticMap.isSymm_polarBilin Q).isRefl hByy
  have hcard : Nat.card {g : QuadraticMap.orthogonalGroup Q //
      (g : V ≃ₗ[ZMod 3] V) x = x} =
      Nat.card (QuadraticMap.orthogonalGroup (Q.restrict W)) := by
    simpa only [W] using card_stabilizer_eq_perp_orthogonalGroup Q x hx
  obtain ⟨b, hb, ⟨e2⟩⟩ := ct_oc_exists_diag (Q.restrict W) hQ2nd 4 hWfin
  rw [hcard, ct_oc_card_congr e2, ct_oc_card_count 4 b hb]
  by_cases hp : ct_oc_isoPair b
  · left; exact ct_oc_count_four_of_pair b hb hp
  · right; exact ct_oc_count_four_of_not_pair b hb hp



theorem card_stabilizer_four {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : Module.finrank (ZMod 3) V = 4) (v : V) (hv : Q v ≠ 0) :
    Nat.card {g : QuadraticMap.orthogonalGroup Q //
      (g : V ≃ₗ[ZMod 3] V) v = v} = 48 := by
  have hv0 : v ≠ 0 := fun h => hv (by rw [h, QuadraticMap.map_zero])
  have hByy : QuadraticMap.polarBilin Q v v ≠ 0 := by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self]
    simpa [nsmul_eq_mul] using mul_ne_zero (by decide : (2 : ZMod 3) ≠ 0) hv
  let W : Submodule (ZMod 3) V :=
    LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) (Submodule.span (ZMod 3) {v})
  have hWfin : Module.finrank (ZMod 3) W = 3 := by
    have hspan_fin : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) {v}) = 1 :=
      finrank_span_singleton hv0
    have hfin := LinearMap.BilinForm.finrank_orthogonal (B := QuadraticMap.polarBilin Q) hQ
      (Submodule.span (ZMod 3) {v})
    dsimp only [W]
    rw [hfin, hd, hspan_fin]
  have hQ2nd : (QuadraticMap.polarBilin (Q.restrict W)).Nondegenerate := by
    rw [QuadraticMap.polarBilin_restrict]
    exact LinearMap.BilinForm.restrict_nondegenerate_orthogonal_spanSingleton
      (QuadraticMap.polarBilin Q) hQ (QuadraticMap.isSymm_polarBilin Q).isRefl hByy
  have hcard : Nat.card {g : QuadraticMap.orthogonalGroup Q //
      (g : V ≃ₗ[ZMod 3] V) v = v} =
      Nat.card (QuadraticMap.orthogonalGroup (Q.restrict W)) := by
    simpa only [W] using card_stabilizer_eq_perp_orthogonalGroup Q v hv
  rw [hcard]
  exact card_orthogonalGroup_three (Q.restrict W) hQ2nd hWfin

def fullVectorStabilizer {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V) (v : V) : Subgroup (V ≃ₗ[ZMod 3] V) where
  carrier := {g | g v = v ∧ g ∈ QuadraticMap.orthogonalGroup Q}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    refine ⟨?_, (QuadraticMap.orthogonalGroup Q).mul_mem hg.2 hh.2⟩
    rw [LinearEquiv.mul_apply, hh.1, hg.1]
  inv_mem' := by
    intro g hg
    refine ⟨?_, (QuadraticMap.orthogonalGroup Q).inv_mem hg.2⟩
    have h := congrArg (fun w => (g⁻¹ : V ≃ₗ[ZMod 3] V) w) hg.1
    simpa using h.symm

@[simp] theorem mem_fullVectorStabilizer_iff
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {Q : QuadraticForm (ZMod 3) V} {v : V} {g : V ≃ₗ[ZMod 3] V} :
    g ∈ fullVectorStabilizer Q v ↔ g v = v ∧ g ∈ QuadraticMap.orthogonalGroup Q :=
  Iff.rfl

noncomputable def fullVectorStabilizerEquiv {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] (Q : QuadraticForm (ZMod 3) V) (v : V) :
    fullVectorStabilizer Q v ≃
      {g : QuadraticMap.orthogonalGroup Q // (g : V ≃ₗ[ZMod 3] V) v = v} where
  toFun g := ⟨⟨g.1, g.2.2⟩, g.2.1⟩
  invFun g := ⟨g.1.1, ⟨g.2, g.1.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem natCard_fullVectorStabilizer {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : Module.finrank (ZMod 3) V = 4) (v : V) (hv : Q v ≠ 0) :
    Nat.card (fullVectorStabilizer Q v) = 48 := by
  have : Finite V := Module.finite_of_finite (ZMod 3)
  have : Finite (V ≃ₗ[ZMod 3] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod 3] V => (e : V → V))
      DFunLike.coe_injective
  rw [← card_stabilizer_four Q hQ hd v hv]
  exact Nat.card_congr (fullVectorStabilizerEquiv Q v)

theorem eq_fullVectorStabilizer_of_le_orthogonalGroup_of_card_eq {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : Module.finrank (ZMod 3) V = 4) (v : V) (hv : Q v ≠ 0)
    {H : Subgroup (V ≃ₗ[ZMod 3] V)} (hHO : H ≤ QuadraticMap.orthogonalGroup Q)
    (hfix : ∀ g ∈ H, g v = v) (hcard : Nat.card H = 48) :
    H = fullVectorStabilizer Q v := by
  have : Finite V := Module.finite_of_finite (ZMod 3)
  have : Finite (V ≃ₗ[ZMod 3] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod 3] V => (e : V → V))
      DFunLike.coe_injective
  have hle : H ≤ fullVectorStabilizer Q v := by
    intro g hg
    exact ⟨hfix g hg, hHO hg⟩
  have hstab : Nat.card (fullVectorStabilizer Q v) = 48 :=
    natCard_fullVectorStabilizer Q hQ hd v hv
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hstab, hcard])

theorem fullVectorStabilizer_le_of_le_orthogonalGroup_of_card_eq {V : Type}
    [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
    (Q : QuadraticForm (ZMod 3) V) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : Module.finrank (ZMod 3) V = 4) (v : V) (hv : Q v ≠ 0)
    {H : Subgroup (V ≃ₗ[ZMod 3] V)} (hHO : H ≤ QuadraticMap.orthogonalGroup Q)
    (hfix : ∀ g ∈ H, g v = v) (hcard : Nat.card H = 48) :
    fullVectorStabilizer Q v ≤ H := by
  rw [eq_fullVectorStabilizer_of_le_orthogonalGroup_of_card_eq Q hQ hd v hv hHO hfix hcard]


end CFSG.StandardType.OrthF3

end
