module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.StandardType.FrameRoute

section Rot

variable {K : Type} [Field K] [Algebra (ZMod 2) K] {V0 : Type} [AddCommGroup V0]
  [Module (ZMod 2) V0] {t : ℕ}

@[expose] noncomputable def P9rot (a : Fin t → Kˣ) :
    (V0 × (Fin t → K)) ≃ₗ[ZMod 2] (V0 × (Fin t → K)) where
  toFun v := (v.1, fun k => (a k : K) * v.2 k)
  invFun v := (v.1, fun k => ((a k)⁻¹ : Kˣ) * v.2 k)
  map_add' x y := by
    ext <;> simp [mul_add]
  map_smul' c x := by
    ext <;> simp [mul_smul_comm]
  left_inv v := by
    ext <;> simp
  right_inv v := by
    ext <;> simp

theorem P9rot_apply (a : Fin t → Kˣ) (v : V0 × (Fin t → K)) :
    P9rot a v = (v.1, fun k => (a k : K) * v.2 k) := rfl

@[expose] noncomputable def P9rotHom :
    (Fin t → Kˣ) →* ((V0 × (Fin t → K)) ≃ₗ[ZMod 2] (V0 × (Fin t → K))) where
  toFun := P9rot
  map_one' := by
    ext <;> simp [P9rot_apply]
  map_mul' a b := by
    ext <;> simp [P9rot_apply, mul_assoc]

private lemma P9C_add_self {M : Type} [AddCommGroup M] [Module (ZMod 2) M] (x : M) :
    x + x = 0 := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  calc x + x = (1 + 1 : ZMod 2) • x := by rw [add_smul, one_smul]
    _ = (2 : ZMod 2) • x := by rw [show (1 + 1 : ZMod 2) = 2 by norm_num]
    _ = 0 := by rw [h2, zero_smul]

private lemma P9C_rot_single (k : Fin t) (ω : Kˣ) (c : K) :
    P9rot (V0 := V0) (Function.update (1 : Fin t → Kˣ) k ω) (0, Pi.single k c) =
      (0, Pi.single k ((ω : K) * c)) := by
  rw [P9rot_apply]
  congr 1
  funext j
  by_cases hjk : j = k
  · rw [hjk]
    simp
  · simp [Function.update_of_ne hjk, Pi.single_eq_of_ne hjk]

private lemma P9C_rot_proj (k : Fin t) (ω : Kˣ) (hωω : (ω : K) + (ω : K) ^ 2 = 1)
    (u : V0 × (Fin t → K)) :
    P9rot (V0 := V0) (Function.update (1 : Fin t → Kˣ) k ω) u
        + P9rot (V0 := V0) (Function.update (1 : Fin t → Kˣ) k ω)
            (P9rot (V0 := V0) (Function.update (1 : Fin t → Kˣ) k ω) u)
      = (0, Pi.single k (u.2 k)) := by
  refine Prod.ext ?_ ?_
  · simp [P9rot_apply, P9C_add_self]
  · funext j
    by_cases hjk : j = k
    · rw [hjk]
      rw [P9rot_apply, P9rot_apply]
      simp only [Function.update_self, Pi.single_eq_same, Prod.mk_add_mk, Pi.add_apply]
      rw [show (ω : K) * u.2 k + (ω : K) * ((ω : K) * u.2 k)
            = ((ω : K) + (ω : K) ^ 2) * u.2 k by ring, hωω, one_mul]
    · rw [P9rot_apply, P9rot_apply]
      simp [Function.update_of_ne hjk, Pi.single_eq_of_ne hjk, P9C_add_self]

private lemma P9C_sum_pi (y : Fin t → K) :
    (∑ k, ((0 : V0), (Pi.single k (y k) : Fin t → K))) = (0, y) := by
  refine Prod.ext ?_ ?_
  · have h := map_sum (LinearMap.fst (ZMod 2) V0 (Fin t → K))
        (fun k => (0, Pi.single k (y k))) Finset.univ
    rw [LinearMap.fst_apply] at h
    simpa using h
  · have h := map_sum (LinearMap.snd (ZMod 2) V0 (Fin t → K))
        (fun k => (0, Pi.single k (y k))) Finset.univ
    simp only [LinearMap.snd_apply, Finset.univ_sum_single] at h
    simpa using h

theorem P9rotHom_injective :
    Function.Injective (P9rotHom (K := K) (V0 := V0) (t := t)) := by
  change Function.Injective (P9rot (K := K) (V0 := V0) (t := t))
  intro a b hab
  funext k
  apply Units.ext
  have h := congrArg (fun e : (V0 × (Fin t → K)) ≃ₗ[ZMod 2] (V0 × (Fin t → K)) =>
    (e (0, Pi.single k 1)).2 k) hab
  simpa [P9rot_apply] using h

theorem P9rot_comm (a b : Fin t → Kˣ) :
    P9rot (V0 := V0) a * P9rot b = P9rot b * P9rot a := by
  apply LinearEquiv.ext
  intro v
  simp only [LinearEquiv.mul_apply, P9rot_apply]
  apply Prod.ext
  · rfl
  · funext k
    ring

theorem P9rot_apply_inl (a : Fin t → Kˣ) (v : V0) :
    P9rot a (v, 0) = (v, 0) := by
  rw [P9rot_apply]
  ext <;> simp

section Four

variable [Finite K] (hK : Nat.card K = 4)

private lemma P9C_four_cover (hK : Nat.card K = 4) {ω : K} (hω3 : ω ^ 3 = 1) (hωne1 : ω ≠ 1)
    (hωne0 : ω ≠ 0) :
    ∀ c : K, c = 0 ∨ c = 1 ∨ c = ω ∨ c = ω ^ 2 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card, hK]
  have hω2ne1 : ω ^ 2 ≠ 1 := by
    intro h
    apply hωne1
    have h3 : ω ^ 3 = ω := by rw [show ω ^ 3 = ω * ω ^ 2 by ring, h, mul_one]
    rw [hω3] at h3
    exact h3.symm
  have hω2neω : ω ^ 2 ≠ ω := by
    intro h
    apply hωne1
    have h' : ω * ω = ω * 1 := by rw [mul_one, ← pow_two]; exact h
    exact mul_left_cancel₀ hωne0 h'
  let s : Finset K := {0, 1, ω, ω ^ 2}
  have hs : s.card = Fintype.card K := by
    rw [hcard]
    have h01 : (0 : K) ≠ 1 := zero_ne_one
    have h0ω : (0 : K) ≠ ω := hωne0.symm
    have h0ω2 : (0 : K) ≠ ω ^ 2 := (pow_ne_zero 2 hωne0).symm
    have h1ω : (1 : K) ≠ ω := hωne1.symm
    have h1ω2 : (1 : K) ≠ ω ^ 2 := hω2ne1.symm
    have hωω2 : ω ≠ ω ^ 2 := hω2neω.symm
    simp only [s]
    rw [Finset.card_insert_of_notMem (by simp [h01, h0ω, h0ω2]),
      Finset.card_insert_of_notMem (by simp [h1ω, h1ω2]),
      Finset.card_insert_of_notMem (by simp [hωω2]), Finset.card_singleton]
  have huniv : s = Finset.univ := Finset.eq_univ_of_card s hs
  intro c
  have hc : c ∈ s := by rw [huniv]; exact Finset.mem_univ c
  simpa only [s, Finset.mem_insert, Finset.mem_singleton] using hc

include hK in
theorem P9_card_units : Nat.card Kˣ = 3 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK]

include hK in
theorem P9rot_pow_three (a : Fin t → Kˣ) : P9rot (V0 := V0) a ^ 3 = 1 := by
  have ha : a ^ 3 = 1 := by
    funext k
    have h := pow_card_eq_one' (x := a k)
    rw [P9_card_units hK] at h
    simpa using h
  change (P9rotHom (K := K) (V0 := V0) (t := t) a) ^ 3 = 1
  rw [← map_pow P9rotHom a 3, ha, map_one P9rotHom]

include hK in
theorem P9_centralizer_rot (g : (V0 × (Fin t → K)) ≃ₗ[ZMod 2] (V0 × (Fin t → K)))
    (hg : ∀ a : Fin t → Kˣ, g * P9rot a = P9rot a * g) :
    ∃ (g0 : V0 ≃ₗ[ZMod 2] V0) (u : Fin t → Kˣ),
      ∀ v : V0 × (Fin t → K), g v = (g0 v.1, fun k => (u k : K) * v.2 k) := by
  have hcard_units : Nat.card Kˣ = 3 := P9_card_units hK
  haveI : Fintype Kˣ := Fintype.ofFinite Kˣ
  obtain ⟨ω, hωne1⟩ : ∃ ω : Kˣ, ω ≠ 1 := by
    refine Fintype.exists_ne_of_one_lt_card ?_ (1 : Kˣ)
    rw [← Nat.card_eq_fintype_card, hcard_units]
    norm_num
  have hω3 : ω ^ 3 = 1 := by
    have h := pow_card_eq_one' (x := ω)
    rwa [hcard_units] at h
  have hω3K : (ω : K) ^ 3 = 1 := by
    have h := congrArg (fun u : Kˣ => (u : K)) hω3
    simpa using h
  have hωne1K : (ω : K) ≠ 1 := fun h => hωne1 (Units.ext h)
  have hωne0K : (ω : K) ≠ 0 := Units.ne_zero ω
  have h11 : (1 : K) + 1 = 0 := P9C_add_self 1
  have hneg1 : (-1 : K) = 1 := (eq_neg_of_add_eq_zero_left h11).symm
  have hωpoly : (ω : K) ^ 2 + (ω : K) + 1 = 0 := by
    have hprod : ((ω : K) - 1) * ((ω : K) ^ 2 + (ω : K) + 1) = 0 := by
      rw [show ((ω : K) - 1) * ((ω : K) ^ 2 + (ω : K) + 1) = (ω : K) ^ 3 - 1 by ring,
        hω3K, sub_self]
    exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hωne1K)
  have hωω : (ω : K) + (ω : K) ^ 2 = 1 := by
    have h' : (ω : K) ^ 2 + (ω : K) = -1 := (eq_neg_iff_add_eq_zero).2 hωpoly
    rw [add_comm (ω : K) ((ω : K) ^ 2), h', hneg1]
  have hcover := P9C_four_cover (K := K) hK hω3K hωne1K hωne0K
  have hg_apply : ∀ (a : Fin t → Kˣ) (v : V0 × (Fin t → K)), g (P9rot a v) = P9rot a (g v) := by
    intro a v
    have h := congrArg (fun e : (V0 × (Fin t → K)) ≃ₗ[ZMod 2] (V0 × (Fin t → K)) => e v)
      (hg a)
    simpa only [LinearEquiv.mul_apply] using h
  have hproj : ∀ (k : Fin t) (u : V0 × (Fin t → K)),
      P9rot (V0 := V0) (Function.update (1 : Fin t → Kˣ) k ω) u
          + P9rot (V0 := V0) (Function.update (1 : Fin t → Kˣ) k ω)
              (P9rot (V0 := V0) (Function.update (1 : Fin t → Kˣ) k ω) u)
        = (0, Pi.single k (u.2 k)) :=
    fun k u => P9C_rot_proj k ω hωω u
  have hline : ∀ (k : Fin t) (c : K),
      g (0, Pi.single k c) = (0, Pi.single k ((g (0, Pi.single k c)).2 k)) := by
    intro k c
    have hw : (0, Pi.single k c) =
        P9rot (V0 := V0) (Function.update (1 : Fin t → Kˣ) k ω) (0, Pi.single k c)
          + P9rot (V0 := V0) (Function.update (1 : Fin t → Kˣ) k ω)
              (P9rot (V0 := V0) (Function.update (1 : Fin t → Kˣ) k ω) (0, Pi.single k c)) := by
      rw [hproj k (0, Pi.single k c)]
      simp
    calc g (0, Pi.single k c)
        = g (P9rot (V0 := V0) (Function.update (1 : Fin t → Kˣ) k ω) (0, Pi.single k c)
            + P9rot (V0 := V0) (Function.update (1 : Fin t → Kˣ) k ω)
                (P9rot (V0 := V0) (Function.update (1 : Fin t → Kˣ) k ω)
                  (0, Pi.single k c))) := congrArg g hw
      _ = P9rot (V0 := V0) (Function.update (1 : Fin t → Kˣ) k ω) (g (0, Pi.single k c))
            + P9rot (V0 := V0) (Function.update (1 : Fin t → Kˣ) k ω)
                (P9rot (V0 := V0) (Function.update (1 : Fin t → Kˣ) k ω)
                  (g (0, Pi.single k c))) := by
            rw [map_add, hg_apply, hg_apply, hg_apply]
      _ = (0, Pi.single k ((g (0, Pi.single k c)).2 k)) := hproj k (g (0, Pi.single k c))
  let γ : Fin t → K → K := fun k c => (g (0, Pi.single k c)).2 k
  have hline' : ∀ (k : Fin t) (c : K), g (0, Pi.single k c) = (0, Pi.single k (γ k c)) :=
    fun k c => hline k c
  have hγ_omega : ∀ (k : Fin t) (c : K), γ k ((ω : K) * c) = (ω : K) * γ k c := by
    intro k c
    have h1 : g (P9rot (V0 := V0) (Function.update (1 : Fin t → Kˣ) k ω) (0, Pi.single k c)) =
        P9rot (V0 := V0) (Function.update (1 : Fin t → Kˣ) k ω) (g (0, Pi.single k c)) :=
      hg_apply _ _
    rw [P9C_rot_single k ω c] at h1
    rw [hline' k ((ω : K) * c), hline' k c, P9C_rot_single k ω (γ k c)] at h1
    have := congrArg (fun w : V0 × (Fin t → K) => w.2 k) h1
    simpa using this
  have hγ0 : ∀ k : Fin t, γ k 0 = 0 := by
    intro k
    have hzero : ((0 : V0), (Pi.single k (γ k 0) : Fin t → K)) = 0 := by
      rw [← hline' k 0]
      simp
    have := congrArg (fun w : V0 × (Fin t → K) => w.2 k) hzero
    simpa using this
  have hγ_eq : ∀ (k : Fin t) (c : K), γ k c = γ k 1 * c := by
    intro k c
    rcases hcover c with rfl | rfl | rfl | rfl
    · rw [hγ0, mul_zero]
    · rw [mul_one]
    · have h := hγ_omega k 1
      simpa [mul_comm] using h
    · have h2 : γ k ((ω : K) ^ 2) = (ω : K) * γ k (ω : K) := by
        simpa [pow_two] using hγ_omega k (ω : K)
      have h1 : γ k (ω : K) = (ω : K) * γ k 1 := by
        simpa using hγ_omega k 1
      rw [h2, h1]
      ring
  have hγ1_ne : ∀ k : Fin t, γ k 1 ≠ 0 := by
    intro k h
    have h0 : g (0, Pi.single k 1) = 0 := by
      have h1 := hline' k 1
      rw [h] at h1
      rw [h1]
      simp
    have hz : ((0 : V0), (Pi.single k 1 : Fin t → K)) = 0 :=
      g.injective (h0.trans (map_zero g).symm)
    have hcontra : (1 : K) = 0 := by
      have := congrArg (fun w : V0 × (Fin t → K) => w.2 k) hz
      simpa using this
    exact one_ne_zero hcontra
  have fixed_part : ∀ (e : (V0 × (Fin t → K)) ≃ₗ[ZMod 2] (V0 × (Fin t → K))),
      (∀ a : Fin t → Kˣ, e * P9rot a = P9rot a * e) →
        ∀ x : V0 × (Fin t → K), e (x.1, 0) = ((e x).1, 0) := by
    intro e he x
    have he_apply : ∀ (a : Fin t → Kˣ) (v : V0 × (Fin t → K)), e (P9rot a v) = P9rot a (e v) := by
      intro a v
      have h := congrArg (fun f : (V0 × (Fin t → K)) ≃ₗ[ZMod 2] (V0 × (Fin t → K)) => f v)
        (he a)
      simpa only [LinearEquiv.mul_apply] using h
    have heproj : ∀ (k : Fin t) (u : V0 × (Fin t → K)),
        e (0, Pi.single k (u.2 k)) = (0, Pi.single k ((e u).2 k)) := by
      intro k u
      have h2 : e (P9rot (V0 := V0) (Function.update (1 : Fin t → Kˣ) k ω) u
            + P9rot (V0 := V0) (Function.update (1 : Fin t → Kˣ) k ω)
                (P9rot (V0 := V0) (Function.update (1 : Fin t → Kˣ) k ω) u))
          = P9rot (V0 := V0) (Function.update (1 : Fin t → Kˣ) k ω) (e u)
            + P9rot (V0 := V0) (Function.update (1 : Fin t → Kˣ) k ω)
                (P9rot (V0 := V0) (Function.update (1 : Fin t → Kˣ) k ω) (e u)) := by
        rw [map_add, he_apply, he_apply, he_apply]
      rwa [hproj k u, hproj k (e u)] at h2
    have hx0 : x + ∑ k, ((0 : V0), (Pi.single k (x.2 k) : Fin t → K)) = (x.1, 0) := by
      rw [P9C_sum_pi x.2]
      ext <;> simp [P9C_add_self]
    calc e (x.1, 0)
        = e (x + ∑ k, (0, Pi.single k (x.2 k))) := congrArg e hx0.symm
      _ = e x + ∑ k, e (0, Pi.single k (x.2 k)) := by
            rw [map_add]
            congr 1
            exact map_sum (e : V0 × (Fin t → K) →ₗ[ZMod 2] (V0 × (Fin t → K)))
              (fun k => (0, Pi.single k (x.2 k))) Finset.univ
      _ = e x + ∑ k, (0, Pi.single k ((e x).2 k)) := by
            congr 1
            exact Finset.sum_congr rfl fun k _ => heproj k x
      _ = e x + (0, (e x).2) := by
            congr 1
            simpa using P9C_sum_pi (e x).2
      _ = ((e x).1, 0) := by ext <;> simp [P9C_add_self]
  have hg_inv : ∀ a : Fin t → Kˣ, g.symm * P9rot a = P9rot a * g.symm :=
    fun a => Commute.inv_left (hg a)
  let g0 : V0 →ₗ[ZMod 2] V0 :=
    { toFun := fun v0 => (g (v0, 0)).1
      map_add' := by
        intro a b
        have h := congrArg (fun w : V0 × (Fin t → K) => w.1) (map_add g (a, 0) (b, 0))
        simpa using h
      map_smul' := by
        intro c a
        have h := congrArg (fun w : V0 × (Fin t → K) => w.1) (map_smul g c (a, 0))
        simpa using h }
  let g0' : V0 →ₗ[ZMod 2] V0 :=
    { toFun := fun v0 => (g.symm (v0, 0)).1
      map_add' := by
        intro a b
        have h := congrArg (fun w : V0 × (Fin t → K) => w.1) (map_add g.symm (a, 0) (b, 0))
        simpa using h
      map_smul' := by
        intro c a
        have h := congrArg (fun w : V0 × (Fin t → K) => w.1) (map_smul g.symm c (a, 0))
        simpa using h }
  have hg0 : ∀ v0 : V0, g (v0, 0) = (g0 v0, 0) := fun v0 => fixed_part g hg (v0, 0)
  have hg0' : ∀ v0 : V0, g.symm (v0, 0) = (g0' v0, 0) := fun v0 => fixed_part g.symm hg_inv (v0, 0)
  have hg0'_left : ∀ v0 : V0, g0' (g0 v0) = v0 := by
    intro v0
    have h1 : g.symm (g0 v0, 0) = (v0, 0) := by rw [← hg0 v0, LinearEquiv.symm_apply_apply]
    change (g.symm (g0 v0, 0)).1 = v0
    rw [h1]
  have hg0_left : ∀ v0 : V0, g0 (g0' v0) = v0 := by
    intro v0
    have h1 : g (g0' v0, 0) = (v0, 0) := by rw [← hg0' v0, LinearEquiv.apply_symm_apply]
    change (g (g0' v0, 0)).1 = v0
    rw [h1]
  have hcomp1 : g0.comp g0' = 1 := by ext v0; simpa using hg0_left v0
  have hcomp2 : g0'.comp g0 = 1 := by ext v0; simpa using hg0'_left v0
  refine ⟨LinearEquiv.ofLinearMap g0 g0' hcomp1 hcomp2, fun k => Units.mk0 (γ k 1) (hγ1_ne k), ?_⟩
  intro v
  have hv : (v.1, 0) + ∑ k, ((0 : V0), (Pi.single k (v.2 k) : Fin t → K)) = v := by
    rw [P9C_sum_pi v.2]
    ext <;> simp [P9C_add_self]
  calc g v
      = g ((v.1, 0) + ∑ k, ((0 : V0), (Pi.single k (v.2 k) : Fin t → K))) :=
          congrArg g hv.symm
    _ = g (v.1, 0) + ∑ k, g ((0 : V0), (Pi.single k (v.2 k) : Fin t → K)) := by
          rw [map_add]
          congr 1
          exact map_sum (g : V0 × (Fin t → K) →ₗ[ZMod 2] (V0 × (Fin t → K)))
            (fun k => ((0 : V0), (Pi.single k (v.2 k) : Fin t → K))) Finset.univ
    _ = (g0 v.1, 0) + ∑ k, ((0 : V0), (Pi.single k (γ k (v.2 k)) : Fin t → K)) := by
          rw [hg0 v.1]
          congr 1
          exact Finset.sum_congr rfl fun k _ => hline' k (v.2 k)
    _ = (g0 v.1, 0) + (0, fun k => γ k (v.2 k)) := by
          congr 1
          simpa using P9C_sum_pi (fun k => γ k (v.2 k))
    _ = (g0 v.1, fun k => (Units.mk0 (γ k 1) (hγ1_ne k) : K) * v.2 k) := by
          refine Prod.ext ?_ ?_
          · simp
          · funext j
            simp [hγ_eq j (v.2 j)]

end Four

end Rot

theorem P9_exists_order_three {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [Module.Finite (ZMod 2) W] (hW : 2 ≤ Module.finrank (ZMod 2) W) :
    ∃ g : W ≃ₗ[ZMod 2] W, g ^ 3 = 1 ∧ g ≠ 1 := by
  let b : Module.Basis (Fin (Module.finrank (ZMod 2) W)) (ZMod 2) W :=
    Module.finBasis (ZMod 2) W
  let i0 : Fin (Module.finrank (ZMod 2) W) := ⟨0, by omega⟩
  let i1 : Fin (Module.finrank (ZMod 2) W) := ⟨1, by omega⟩
  have hi10 : i1 ≠ i0 := by
    intro h
    have := congrArg Fin.val h
    simp [i0, i1] at this
  let f : Fin (Module.finrank (ZMod 2) W) → W := fun i =>
    if i = i0 then b i1 else if i = i1 then b i0 + b i1 else b i
  let φ : Module.End (ZMod 2) W := b.constr (ZMod 2) f
  have hφ0 : φ (b i0) = b i1 := by
    have h : φ (b i0) = f i0 := by
      change (b.constr (ZMod 2) f) (b i0) = f i0
      rw [Module.Basis.constr_basis]
    rw [h]
    simp [f]
  have hφ1 : φ (b i1) = b i0 + b i1 := by
    have h : φ (b i1) = f i1 := by
      change (b.constr (ZMod 2) f) (b i1) = f i1
      rw [Module.Basis.constr_basis]
    rw [h]
    simp [f, hi10]
  have hφv1 : φ (b i0 + b i1) = b i0 := by
    rw [map_add, hφ0, hφ1]
    rw [show b i1 + (b i0 + b i1) = b i0 by
      rw [← add_assoc, add_comm (b i1) (b i0), add_assoc, P9C_add_self, add_zero]]
  have hφi : ∀ i, i ≠ i0 → i ≠ i1 → φ (b i) = b i := by
    intro i hi0 hi1
    have h : φ (b i) = f i := by
      change (b.constr (ZMod 2) f) (b i) = f i
      rw [Module.Basis.constr_basis]
    rw [h]
    simp [f, hi0, hi1]
  have hφ3 : φ ^ 3 = 1 := by
    refine b.ext fun i => ?_
    change φ (φ (φ (b i))) = b i
    rcases eq_or_ne i i0 with rfl | hi0
    · rw [hφ0, hφ1, hφv1]
    · rcases eq_or_ne i i1 with rfl | hi1
      · rw [hφ1, hφv1, hφ0]
      · simp only [hφi i hi0 hi1]
  have hcomp1 : φ.comp (φ ^ 2) = 1 := by
    have h : φ * φ ^ 2 = φ ^ 3 := by simpa using (pow_succ' φ 2).symm
    rw [show φ.comp (φ ^ 2) = φ * φ ^ 2 from rfl, h, hφ3]
  have hcomp2 : (φ ^ 2).comp φ = 1 := by
    have h : φ ^ 2 * φ = φ ^ 3 := by simpa using (pow_succ φ 2).symm
    rw [show (φ ^ 2).comp φ = φ ^ 2 * φ from rfl, h, hφ3]
  let g : W ≃ₗ[ZMod 2] W := LinearEquiv.ofLinearMap φ (φ ^ 2) hcomp1 hcomp2
  refine ⟨g, ?_, ?_⟩
  · have hcoe : ((g ^ 3 : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W) = φ ^ 3 := by
      change LinearEquiv.automorphismGroup.toLinearMapMonoidHom (g ^ 3) = φ ^ 3
      rw [map_pow]
      rfl
    ext x
    have hx : (((g ^ 3 : W ≃ₗ[ZMod 2] W) : W →ₗ[ZMod 2] W)) x = x := by
      rw [hcoe]
      have := congrArg (fun e : Module.End (ZMod 2) W => e x) hφ3
      simpa using this
    simpa using hx
  · intro h
    have hb1 : g (b i0) = b i1 := by
      change φ (b i0) = b i1
      exact hφ0
    have hb' : b i1 = b i0 := by
      have h2 := congrArg (fun e : W ≃ₗ[ZMod 2] W => e (b i0)) h
      rw [hb1] at h2
      simpa using h2
    exact hi10 (b.injective hb')

end CFSG.StandardType.FrameRoute
