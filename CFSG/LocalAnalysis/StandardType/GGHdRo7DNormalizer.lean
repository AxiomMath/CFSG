module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7DDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthSPerm
import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ExtensionPCore

public section

namespace CFSG.StandardType.HdRo7D

open CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma hdRo7DNormAux_sq_pm (a : ZMod 3) (h : a = 1 ∨ a = -1) : a * a = 1 := by
  rcases h with h | h <;> rw [h] <;> decide

private lemma hdRo7DNormAux_char3 {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (x : V) :
    -x - x = x := by
  have h : (-1 : ZMod 3) + (-1 : ZMod 3) = 1 := by decide
  calc -x - x = (-1 : ZMod 3) • x + (-1 : ZMod 3) • x := by rw [sub_eq_add_neg, neg_one_smul]
    _ = ((-1 : ZMod 3) + (-1 : ZMod 3)) • x := by rw [add_smul]
    _ = (1 : ZMod 3) • x := by rw [h]
    _ = x := by rw [one_smul]

private lemma hdRo7DNormAux_coord_smul_basis {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (k i : Fin (n + 1)) (c : ZMod 3) :
    b.coord k (c • b i) = c * (if i = k then 1 else 0) := by
  rw [map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply,
    smul_eq_mul]

private lemma hdRo7DNormAux_prod_sign {n : ℕ} (F : Finset (Fin (n + 1))) :
    ∏ i : Fin (n + 1), (if i ∈ F then (-1 : ZMod 3) else 1) = (-1) ^ F.card := by
  rw [← Finset.prod_filter (s := Finset.univ) (p := fun i => i ∈ F) (f := fun _ => (-1 : ZMod 3))]
  rw [Finset.filter_univ_mem, Finset.prod_const]

private noncomputable def hdRo7DNormAux_P {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) : Subgroup (V ≃ₗ[ZMod 3] V) where
  carrier := {s | DSP 3 b s}
  mul_mem' := by
    intro s t hs ht
    obtain ⟨σ, c, hσ0, hc0, hc, hprod, hs⟩ := hs
    obtain ⟨τ, d, hτ0, hd0, hd, hprod', ht⟩ := ht
    refine ⟨σ * τ, fun i => d i * c (τ i), ?_, ?_, ?_, ?_, ?_⟩
    · rw [Equiv.Perm.mul_apply, hτ0, hσ0]
    · show d 0 * c (τ 0) = 1; rw [hd0, hτ0, hc0, mul_one]
    · intro i
      change d i * c (τ i) = 1 ∨ d i * c (τ i) = -1
      rcases hd i with h | h <;> rcases hc (τ i) with h' | h' <;> rw [h, h'] <;> decide
    · calc ∏ i, d i * c (τ i) = (∏ i, d i) * ∏ i, c (τ i) := Finset.prod_mul_distrib
        _ = (∏ i, d i) * (∏ i, c i) := by rw [Equiv.prod_comp τ c]
        _ = 1 := by rw [hprod', hprod, mul_one]
    · intro i
      calc (s * t) (b i) = s (t (b i)) := LinearEquiv.mul_apply s t (b i)
        _ = s (d i • b (τ i)) := by rw [ht i]
        _ = d i • s (b (τ i)) := by rw [map_smul]
        _ = d i • (c (τ i) • b (σ (τ i))) := by rw [hs (τ i)]
        _ = (d i * c (τ i)) • b ((σ * τ) i) := by rw [← mul_smul, Equiv.Perm.mul_apply]
  one_mem' := ⟨1, fun _ => 1, rfl, rfl, fun _ => Or.inl rfl, by simp, fun i => by simp⟩
  inv_mem' := by
    intro s hs
    obtain ⟨σ, c, hσ0, hc0, hc, hprod, hs⟩ := hs
    have hσinv0 : σ.symm 0 = 0 := (Equiv.symm_apply_eq σ).mpr hσ0.symm
    refine ⟨σ.symm, fun j => c (σ.symm j), hσinv0, ?_, ?_, ?_, ?_⟩
    · change c (σ.symm 0) = 1; rw [hσinv0]; exact hc0
    · intro j; exact hc (σ.symm j)
    · calc ∏ j, c (σ.symm j) = ∏ j, c j := Equiv.prod_comp σ.symm c
        _ = 1 := hprod
    · intro j
      change s.symm (b j) = c (σ.symm j) • b (σ.symm j)
      rw [LinearEquiv.symm_apply_eq]
      calc b j = (c (σ.symm j) * c (σ.symm j)) • b j := by
              rw [hdRo7DNormAux_sq_pm (c (σ.symm j)) (hc (σ.symm j)), one_smul]
        _ = c (σ.symm j) • (c (σ.symm j) • b (σ (σ.symm j))) := by
              rw [← mul_smul, Equiv.apply_symm_apply σ j]
        _ = c (σ.symm j) • s (b (σ.symm j)) := by rw [hs]
        _ = s (c (σ.symm j) • b (σ.symm j)) := by rw [map_smul]

private noncomputable def hdRo7DNormAux_sigma {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (s : hdRo7DNormAux_P b) :
    Equiv.Perm (Fin (n + 1)) := Classical.choose s.2

private noncomputable def hdRo7DNormAux_sign {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (s : hdRo7DNormAux_P b) :
    Fin (n + 1) → ZMod 3 := Classical.choose (Classical.choose_spec s.2)

private lemma hdRo7DNormAux_sigma_zero {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (s : hdRo7DNormAux_P b) :
    hdRo7DNormAux_sigma b s 0 = 0 :=
  (Classical.choose_spec (Classical.choose_spec s.2)).1

private lemma hdRo7DNormAux_sign_zero {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (s : hdRo7DNormAux_P b) :
    hdRo7DNormAux_sign b s 0 = 1 :=
  (Classical.choose_spec (Classical.choose_spec s.2)).2.1

private lemma hdRo7DNormAux_sign_pm {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (s : hdRo7DNormAux_P b) :
    ∀ i, hdRo7DNormAux_sign b s i = 1 ∨ hdRo7DNormAux_sign b s i = -1 :=
  (Classical.choose_spec (Classical.choose_spec s.2)).2.2.1

private lemma hdRo7DNormAux_sigma_spec {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (s : hdRo7DNormAux_P b) :
    ∀ i, s.1 (b i) = hdRo7DNormAux_sign b s i • b (hdRo7DNormAux_sigma b s i) :=
  (Classical.choose_spec (Classical.choose_spec s.2)).2.2.2.2

private lemma hdRo7DNormAux_unique {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (s : hdRo7DNormAux_P b)
    {σ : Equiv.Perm (Fin (n + 1))} {c : Fin (n + 1) → ZMod 3}
    (h : ∀ i, s.1 (b i) = c i • b (σ i)) :
    σ = hdRo7DNormAux_sigma b s ∧ c = hdRo7DNormAux_sign b s := by
  have hσc : ∀ i, hdRo7DNormAux_sigma b s i = σ i ∧ hdRo7DNormAux_sign b s i = c i := by
    intro i
    have heq : hdRo7DNormAux_sign b s i • b (hdRo7DNormAux_sigma b s i) = c i • b (σ i) := by
      rw [← hdRo7DNormAux_sigma_spec b s i, h i]
    have hcoord := congrArg (fun v => b.coord (hdRo7DNormAux_sigma b s i) v) heq
    rw [hdRo7DNormAux_coord_smul_basis, hdRo7DNormAux_coord_smul_basis] at hcoord
    rw [if_pos rfl, mul_one] at hcoord
    by_cases hsi : σ i = hdRo7DNormAux_sigma b s i
    · rw [if_pos hsi, mul_one] at hcoord
      exact ⟨hsi.symm, hcoord⟩
    · rw [if_neg hsi, mul_zero] at hcoord
      exfalso
      rcases hdRo7DNormAux_sign_pm b s i with h1 | h1 <;> rw [h1] at hcoord <;>
        exact absurd hcoord (by decide)
  refine ⟨Equiv.ext fun i => (hσc i).1.symm, funext fun i => (hσc i).2.symm⟩

private lemma hdRo7DNormAux_sigma_mul {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (s t : hdRo7DNormAux_P b) :
    hdRo7DNormAux_sigma b (s * t) = hdRo7DNormAux_sigma b s * hdRo7DNormAux_sigma b t := by
  have h : ∀ i, (s * t).1 (b i) =
      (hdRo7DNormAux_sign b t i * hdRo7DNormAux_sign b s (hdRo7DNormAux_sigma b t i)) •
        b ((hdRo7DNormAux_sigma b s * hdRo7DNormAux_sigma b t) i) := by
    intro i
    calc (s * t).1 (b i) = s.1 (t.1 (b i)) := LinearEquiv.mul_apply s.1 t.1 (b i)
      _ = s.1 (hdRo7DNormAux_sign b t i • b (hdRo7DNormAux_sigma b t i)) := by
            rw [hdRo7DNormAux_sigma_spec b t i]
      _ = hdRo7DNormAux_sign b t i • s.1 (b (hdRo7DNormAux_sigma b t i)) := by rw [map_smul]
      _ = hdRo7DNormAux_sign b t i •
            (hdRo7DNormAux_sign b s (hdRo7DNormAux_sigma b t i) •
              b (hdRo7DNormAux_sigma b s (hdRo7DNormAux_sigma b t i))) := by
            rw [hdRo7DNormAux_sigma_spec b s]
      _ = (hdRo7DNormAux_sign b t i * hdRo7DNormAux_sign b s (hdRo7DNormAux_sigma b t i)) •
            b ((hdRo7DNormAux_sigma b s * hdRo7DNormAux_sigma b t) i) := by
            rw [← mul_smul, Equiv.Perm.mul_apply]
  exact (hdRo7DNormAux_unique b (s * t)
    (σ := hdRo7DNormAux_sigma b s * hdRo7DNormAux_sigma b t)
    (c := fun i => hdRo7DNormAux_sign b t i * hdRo7DNormAux_sign b s (hdRo7DNormAux_sigma b t i))
    h).1.symm

private lemma hdRo7DNormAux_subtypePerm_cond {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (s : hdRo7DNormAux_P b) :
    ∀ i : Fin (n + 1), (hdRo7DNormAux_sigma b s i ≠ 0) ↔ (i ≠ 0) := by
  intro i
  constructor
  · intro hi h
    exact hi (by rw [h]; exact hdRo7DNormAux_sigma_zero b s)
  · intro hi h
    exact hi ((hdRo7DNormAux_sigma b s).injective (h.trans (hdRo7DNormAux_sigma_zero b s).symm))

private noncomputable def hdRo7DNormAux_pi {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) :
    hdRo7DNormAux_P b →* Equiv.Perm {i : Fin (n + 1) // i ≠ 0} where
  toFun s := (hdRo7DNormAux_sigma b s).subtypePerm (hdRo7DNormAux_subtypePerm_cond b s)
  map_one' := by
    have h1 : hdRo7DNormAux_sigma b (1 : hdRo7DNormAux_P b) = 1 :=
      (hdRo7DNormAux_unique b (1 : hdRo7DNormAux_P b) (σ := 1) (c := fun _ => 1)
        (fun i => by simp)).1.symm
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change (hdRo7DNormAux_sigma b (1 : hdRo7DNormAux_P b)) x.1 = x.1
    rw [h1]
    rfl
  map_mul' s t := by
    ext x
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.subtypePerm_apply]
    rw [hdRo7DNormAux_sigma_mul]
    rfl

private lemma hdRo7DNormAux_sigma_eq_one_of_pi_eq_one {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    (s : hdRo7DNormAux_P b) (hs : hdRo7DNormAux_pi b s = 1) :
    hdRo7DNormAux_sigma b s = 1 := by
  apply Equiv.ext
  intro i
  by_cases hi : i = 0
  · subst hi; exact hdRo7DNormAux_sigma_zero b s
  · have hx := congrArg (fun e : Equiv.Perm {i : Fin (n + 1) // i ≠ 0} => e ⟨i, hi⟩) hs
    have hxv := congrArg Subtype.val hx
    simpa [hdRo7DNormAux_pi, Equiv.Perm.subtypePerm_apply] using hxv

private noncomputable def hdRo7DNormAux_D {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) : Subgroup (hdRo7DNormAux_P b) :=
  (hdRo7DNormAux_pi b).ker

private lemma hdRo7DNormAux_D_sq {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (s : hdRo7DNormAux_P b)
    (hs : s ∈ hdRo7DNormAux_D b) : s ^ 2 = 1 := by
  have hsσ : hdRo7DNormAux_sigma b s = 1 :=
    hdRo7DNormAux_sigma_eq_one_of_pi_eq_one b s (show hdRo7DNormAux_pi b s = 1 from hs)
  have hbasis : ∀ i, s.1 (s.1 (b i)) = b i := by
    intro i
    have h2 : s.1 (b i) = hdRo7DNormAux_sign b s i • b i := by
      rw [hdRo7DNormAux_sigma_spec b s i, hsσ]; simp
    calc s.1 (s.1 (b i)) = s.1 (hdRo7DNormAux_sign b s i • b i) := by rw [h2]
      _ = hdRo7DNormAux_sign b s i • s.1 (b i) := by rw [map_smul]
      _ = hdRo7DNormAux_sign b s i • (hdRo7DNormAux_sign b s i • b i) := by rw [h2]
      _ = b i := by
            rw [← mul_smul, hdRo7DNormAux_sq_pm _ (hdRo7DNormAux_sign_pm b s i), one_smul]
  have hmap : (s.1 : V →ₗ[ZMod 3] V) * (s.1 : V →ₗ[ZMod 3] V) = 1 := by
    apply b.ext
    intro i
    show s.1 (s.1 (b i)) = b i
    exact hbasis i
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  simpa [pow_two, LinearEquiv.mul_apply] using
    congrArg (fun f : V →ₗ[ZMod 3] V => f x) hmap

private lemma hdRo7DNormAux_finite_P {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) : Finite (hdRo7DNormAux_P b) := by
  have hV : Finite V := Finite.of_equiv _ b.repr.toEquiv.symm
  have hV' : Fintype V := Fintype.ofFinite V
  have hFV : Fintype (Fin (n + 1) → V) := inferInstance
  exact Finite.of_injective (fun s : hdRo7DNormAux_P b => fun i => s.1 (b i)) (by
    intro s t h
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    have hmap : (s.1 : V →ₗ[ZMod 3] V) = (t.1 : V →ₗ[ZMod 3] V) := by
      apply b.ext
      intro i
      exact congrFun h i
    exact congrArg (fun f : V →ₗ[ZMod 3] V => f x) hmap)

private noncomputable def hdRo7DNormAux_conj {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (a : V ≃ₗ[ZMod 3] V)
    (hnorm : ∀ s, DSP 3 b s → DSP 3 b (a * s * a⁻¹)) :
    hdRo7DNormAux_P b →* hdRo7DNormAux_P b where
  toFun s := ⟨a * s.1 * a⁻¹, hnorm s.1 s.2⟩
  map_one' := by apply Subtype.ext; simp only [Subgroup.coe_one]; group
  map_mul' s t := by apply Subtype.ext; simp only [Subgroup.coe_mul]; group

private lemma hdRo7DNormAux_conj_injective {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (a : V ≃ₗ[ZMod 3] V)
    (hnorm : ∀ s, DSP 3 b s → DSP 3 b (a * s * a⁻¹)) :
    Function.Injective (hdRo7DNormAux_conj b a hnorm) := by
  intro s t h
  apply Subtype.ext
  have h' := congrArg Subtype.val h
  exact mul_right_cancel (mul_left_cancel h')

private lemma hdRo7DNormAux_conj_surjective {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (a : V ≃ₗ[ZMod 3] V)
    (hnorm : ∀ s, DSP 3 b s → DSP 3 b (a * s * a⁻¹)) :
    Function.Surjective (hdRo7DNormAux_conj b a hnorm) := by
  exact @Finite.surjective_of_injective _ (hdRo7DNormAux_finite_P b)
    (hdRo7DNormAux_conj b a hnorm) (hdRo7DNormAux_conj_injective b a hnorm)

private lemma hdRo7DNormAux_D_isPGroup {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) : IsPGroup 2 (hdRo7DNormAux_D b) := by
  intro g
  refine ⟨1, ?_⟩
  rw [show (2 : ℕ) ^ 1 = 2 from rfl]
  apply Subtype.ext
  simpa using hdRo7DNormAux_D_sq b g.1 g.2

private noncomputable def hdRo7DNormAux_alphaEquiv (n : ℕ) :
    {i : Fin (n + 1) // i ≠ 0} ≃ Fin n where
  toFun x := Fin.pred x.1 x.2
  invFun j := ⟨j.succ, Fin.succ_ne_zero j⟩
  left_inv x := by apply Subtype.ext; exact Fin.succ_pred x.1 x.2
  right_inv j := by simp [Fin.pred_succ]

private lemma hdRo7DNormAux_pi_surjective {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) : Function.Surjective (hdRo7DNormAux_pi b) := by
  intro ρ
  let φ := hdRo7DNormAux_alphaEquiv n
  let τ : Equiv.Perm (Fin n) := φ.symm.trans (ρ.trans φ)
  let σ : Equiv.Perm (Fin (n + 1)) := Equiv.Perm.decomposeFin.symm (0, τ)
  have hσ0 : σ 0 = 0 := Equiv.Perm.decomposeFin_symm_apply_zero 0 τ
  have hσsucc : ∀ j : Fin n, σ j.succ = (ρ (φ.symm j)).1 := by
    intro j
    change (Equiv.Perm.decomposeFin.symm (0, τ)) j.succ = (ρ (φ.symm j)).1
    rw [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self]
    exact Fin.succ_pred (ρ (φ.symm j)).1 (ρ (φ.symm j)).2
  have hP : b.equiv b σ ∈ hdRo7DNormAux_P b :=
    ⟨σ, fun _ => 1, hσ0, rfl, fun _ => Or.inl rfl, by simp,
      fun i => by rw [Module.Basis.equiv_apply]; simp⟩
  refine ⟨⟨b.equiv b σ, hP⟩, ?_⟩
  have hsig : hdRo7DNormAux_sigma b ⟨b.equiv b σ, hP⟩ = σ :=
    (hdRo7DNormAux_unique b ⟨b.equiv b σ, hP⟩ (σ := σ) (c := fun _ => 1)
      (fun i => by rw [Module.Basis.equiv_apply]; simp)).1.symm
  apply Equiv.ext
  intro x
  change ↑(((hdRo7DNormAux_sigma b ⟨b.equiv b σ, hP⟩).subtypePerm
    (hdRo7DNormAux_subtypePerm_cond b ⟨b.equiv b σ, hP⟩)) x) = ↑(ρ x)
  simp only [hsig]
  simp only [Equiv.Perm.subtypePerm_apply]
  apply Subtype.ext
  have hx : x.1 = (φ x).succ := (Fin.succ_pred x.1 x.2).symm
  simp only [hx, hσsucc]
  simp [φ]

private lemma hdRo7DNormAux_D_conj_le {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (a : V ≃ₗ[ZMod 3] V)
    (hnorm : ∀ s, DSP 3 b s → DSP 3 b (a * s * a⁻¹)) (hn : 5 ≤ n) :
    (hdRo7DNormAux_D b).map (hdRo7DNormAux_conj b a hnorm) ≤ hdRo7DNormAux_D b := by
  have hsurj := hdRo7DNormAux_conj_surjective b a hnorm
  have hD'normal : ((hdRo7DNormAux_D b).map (hdRo7DNormAux_conj b a hnorm)).Normal :=
    (show (hdRo7DNormAux_D b).Normal from by
      change ((hdRo7DNormAux_pi b).ker).Normal; infer_instance).map _ hsurj
  have hD'p : IsPGroup 2 ((hdRo7DNormAux_D b).map (hdRo7DNormAux_conj b a hnorm)) :=
    (hdRo7DNormAux_D_isPGroup b).map _
  have hQnormal : (((hdRo7DNormAux_D b).map (hdRo7DNormAux_conj b a hnorm)).map
      (hdRo7DNormAux_pi b)).Normal :=
    hD'normal.map _ (hdRo7DNormAux_pi_surjective b)
  have hQp : IsPGroup 2 (((hdRo7DNormAux_D b).map (hdRo7DNormAux_conj b a hnorm)).map
      (hdRo7DNormAux_pi b)) := hD'p.map _
  have hQbot : (((hdRo7DNormAux_D b).map (hdRo7DNormAux_conj b a hnorm)).map
      (hdRo7DNormAux_pi b)) = ⊥ := by
    refine CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.normal_isPGroup_perm_eq_bot
      (α := {i : Fin (n + 1) // i ≠ 0}) ?_ _ hQp
    rw [Fintype.card_congr (hdRo7DNormAux_alphaEquiv n), Fintype.card_fin]
    exact hn
  have hle := (Subgroup.map_eq_bot_iff _ (f := hdRo7DNormAux_pi b)).mp hQbot
  simpa [hdRo7DNormAux_D] using hle

private lemma hdRo7DNormAux_double_apply {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) {j k : Fin (n + 1)} (hjk : j ≠ k)
    (i : Fin (n + 1)) :
    (CFSG.StandardType.OrthF3.ggOrthSignChange b j *
      CFSG.StandardType.OrthF3.ggOrthSignChange b k) (b i) =
      (if i ∈ ({j, k} : Finset (Fin (n + 1))) then (-1 : ZMod 3) else 1) • b i := by
  by_cases hij : i = j
  · subst i
    rw [LinearEquiv.mul_apply,
      CFSG.StandardType.OrthF3.ggOrthSignChange_apply_of_ne (f := b) (i := k) (j := j) hjk,
      CFSG.StandardType.OrthF3.ggOrthSignChange_apply_self]
    simp
  · by_cases hik : i = k
    · subst i
      rw [LinearEquiv.mul_apply,
        CFSG.StandardType.OrthF3.ggOrthSignChange_apply_self, map_neg,
        CFSG.StandardType.OrthF3.ggOrthSignChange_apply_of_ne (f := b) (i := j) (j := k) hjk.symm]
      simp
    · rw [LinearEquiv.mul_apply,
        CFSG.StandardType.OrthF3.ggOrthSignChange_apply_of_ne (f := b) (i := k) (j := i) hik,
        CFSG.StandardType.OrthF3.ggOrthSignChange_apply_of_ne (f := b) (i := j) (j := i) hij]
      rw [if_neg]
      · simp
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hij, hik⟩

private lemma hdRo7DNormAux_double_mem_P {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) {j k : Fin (n + 1)}
    (hj : j ≠ 0) (hk : k ≠ 0) (hjk : j ≠ k) :
    DSP 3 b (CFSG.StandardType.OrthF3.ggOrthSignChange b j *
      CFSG.StandardType.OrthF3.ggOrthSignChange b k) := by
  refine ⟨1, fun i => if i ∈ ({j, k} : Finset (Fin (n + 1))) then (-1 : ZMod 3) else 1,
    rfl, ?_, ?_, ?_, ?_⟩
  · change (if (0 : Fin (n + 1)) ∈ ({j, k} : Finset (Fin (n + 1))) then
      (-1 : ZMod 3) else 1) = 1
    rw [if_neg (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hj, Ne.symm hk⟩)]
  · intro i
    dsimp only
    by_cases hi : i ∈ ({j, k} : Finset (Fin (n + 1))) <;> simp [hi]
  · calc ∏ i : Fin (n + 1),
        (if i ∈ ({j, k} : Finset (Fin (n + 1))) then (-1 : ZMod 3) else 1)
        = (-1) ^ ({j, k} : Finset (Fin (n + 1))).card := hdRo7DNormAux_prod_sign _
      _ = 1 := by rw [Finset.card_pair hjk]; decide
  · intro i
    simpa [Equiv.Perm.one_apply] using hdRo7DNormAux_double_apply b hjk i

private lemma hdRo7DNormAux_pi_eq_one_of_sigma_eq_one {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    (s : hdRo7DNormAux_P b) (h : hdRo7DNormAux_sigma b s = 1) :
    hdRo7DNormAux_pi b s = 1 := by
  change (hdRo7DNormAux_sigma b s).subtypePerm (hdRo7DNormAux_subtypePerm_cond b s) = 1
  simp only [h]
  exact Equiv.Perm.subtypePerm_one _

private lemma hdRo7DNormAux_double_mem_D {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) {j k : Fin (n + 1)}
    (hj : j ≠ 0) (hk : k ≠ 0) (hjk : j ≠ k) :
    (⟨CFSG.StandardType.OrthF3.ggOrthSignChange b j *
        CFSG.StandardType.OrthF3.ggOrthSignChange b k,
      show DSP 3 b (CFSG.StandardType.OrthF3.ggOrthSignChange b j *
        CFSG.StandardType.OrthF3.ggOrthSignChange b k) from
        hdRo7DNormAux_double_mem_P b hj hk hjk⟩ : hdRo7DNormAux_P b) ∈
      hdRo7DNormAux_D b := by
  have hσ : hdRo7DNormAux_sigma b
      (⟨CFSG.StandardType.OrthF3.ggOrthSignChange b j *
        CFSG.StandardType.OrthF3.ggOrthSignChange b k,
        show DSP 3 b (CFSG.StandardType.OrthF3.ggOrthSignChange b j *
          CFSG.StandardType.OrthF3.ggOrthSignChange b k) from
          hdRo7DNormAux_double_mem_P b hj hk hjk⟩ : hdRo7DNormAux_P b) = 1 := by
    refine (hdRo7DNormAux_unique b _ (σ := 1)
      (c := fun i => if i ∈ ({j, k} : Finset (Fin (n + 1))) then -1 else 1) ?_).1.symm
    intro i
    exact hdRo7DNormAux_double_apply b hjk i
  change hdRo7DNormAux_pi b _ = 1
  exact hdRo7DNormAux_pi_eq_one_of_sigma_eq_one b _ hσ

private lemma hdRo7DNormAux_range_conj {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (_b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (a r : V ≃ₗ[ZMod 3] V) :
    LinearMap.range (((a * r * a⁻¹ : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V) - LinearMap.id) =
      Submodule.map (a : V →ₗ[ZMod 3] V)
        (LinearMap.range ((r : V →ₗ[ZMod 3] V) - LinearMap.id)) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨(r : V →ₗ[ZMod 3] V) (a⁻¹ y) - a⁻¹ y, ⟨a⁻¹ y, rfl⟩, ?_⟩
    show a ((r : V →ₗ[ZMod 3] V) (a⁻¹ y) - a⁻¹ y) = (a * r * a⁻¹) y - y
    rw [map_sub, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    rw [show a (a⁻¹ y) = y from LinearEquiv.apply_symm_apply a y]
    rfl
  · rintro ⟨z, ⟨y, rfl⟩, rfl⟩
    refine ⟨a y, ?_⟩
    show (a * r * a⁻¹) (a y) - a y = a ((r : V →ₗ[ZMod 3] V) y - y)
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    rw [show a⁻¹ (a y) = y from LinearEquiv.symm_apply_apply a y]
    rw [map_sub]
    rfl

private lemma hdRo7DNormAux_double_range {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) {j k : Fin (n + 1)} (hjk : j ≠ k) :
    LinearMap.range
      (((CFSG.StandardType.OrthF3.ggOrthSignChange b j *
        CFSG.StandardType.OrthF3.ggOrthSignChange b k : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V) -
          LinearMap.id) =
      Submodule.span (ZMod 3) ({b j, b k} : Set V) := by
  have hT : ((CFSG.StandardType.OrthF3.ggOrthSignChange b j *
        CFSG.StandardType.OrthF3.ggOrthSignChange b k : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V) -
          LinearMap.id =
      b.constr (ZMod 3) (fun i =>
        (if i ∈ ({j, k} : Finset (Fin (n + 1))) then (1 : ZMod 3) else 0) • b i) := by
    apply b.ext
    intro i
    rw [Module.Basis.constr_basis, LinearMap.sub_apply, LinearMap.id_apply,
      LinearEquiv.coe_toLinearMap, hdRo7DNormAux_double_apply b hjk i]
    by_cases hi : i ∈ ({j, k} : Finset (Fin (n + 1)))
    · rw [if_pos hi, if_pos hi, neg_one_smul, one_smul]
      exact hdRo7DNormAux_char3 (b i)
    · rw [if_neg hi, if_neg hi]
      simp
  rw [hT, Module.Basis.constr_range]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    by_cases hi : i ∈ ({j, k} : Finset (Fin (n + 1)))
    · change (if i ∈ ({j, k} : Finset (Fin (n + 1))) then (1 : ZMod 3) else 0) • b i ∈
        Submodule.span (ZMod 3) ({b j, b k} : Set V)
      rw [if_pos hi, one_smul]
      rw [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · exact Submodule.subset_span (by simp)
      · exact Submodule.subset_span (by simp)
    · change (if i ∈ ({j, k} : Finset (Fin (n + 1))) then (1 : ZMod 3) else 0) • b i ∈
        Submodule.span (ZMod 3) ({b j, b k} : Set V)
      rw [if_neg hi, zero_smul]
      exact Submodule.zero_mem _
  · rw [Submodule.span_le]
    intro x hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · refine Submodule.subset_span ⟨j, ?_⟩
      change (if j ∈ ({j, k} : Finset (Fin (n + 1))) then (1 : ZMod 3) else 0) • b j = b j
      rw [if_pos (by simp), one_smul]
    · refine Submodule.subset_span ⟨k, ?_⟩
      change (if k ∈ ({j, k} : Finset (Fin (n + 1))) then (1 : ZMod 3) else 0) • b k = b k
      rw [if_pos (by simp), one_smul]

private lemma hdRo7DNormAux_finrank_span_pair {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) {j k : Fin (n + 1)} (hjk : j ≠ k) :
    Module.finrank (ZMod 3) (Submodule.span (ZMod 3) ({b j, b k} : Set V)) = 2 := by
  have hli : LinearIndependent (ZMod 3) (![b j, b k] : Fin 2 → V) := by
    have hinj : Function.Injective (![j, k] : Fin 2 → Fin (n + 1)) := by
      intro x y hxy
      fin_cases x <;> fin_cases y <;> simp_all
    have h := b.linearIndependent.comp (![j, k] : Fin 2 → Fin (n + 1)) hinj
    have h' : (![b j, b k] : Fin 2 → V) = (fun x => b (![j, k] x)) := by
      funext x
      fin_cases x <;> simp
    rw [h']
    exact h
  have h := finrank_span_eq_card hli
  rw [show Set.range (![b j, b k] : Fin 2 → V) = ({b j, b k} : Set V) by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hx
      rcases hx with rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩] at h
  simpa using h

private lemma hdRo7DNormAux_finrank_span_image_b {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    (F : Finset (Fin (n + 1))) :
    Module.finrank (ZMod 3) (Submodule.span (ZMod 3) (b '' (F : Set (Fin (n + 1))))) =
      F.card := by
  have hrange : Set.range (fun i : F => b i.1) = b '' (F : Set (Fin (n + 1))) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.1, i.2, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  have hli : LinearIndependent (ZMod 3) (fun i : F => b i.1) :=
    b.linearIndependent.comp (fun i : F => i.1) (fun x y h => Subtype.ext h)
  rw [← hrange, finrank_span_eq_card hli]
  simp

private lemma hdRo7DNormAux_range_diag {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (r : V ≃ₗ[ZMod 3] V)
    (s : Fin (n + 1) → ZMod 3) (hpm : ∀ i, s i = 1 ∨ s i = -1)
    (hact : ∀ i, r (b i) = s i • b i) :
    LinearMap.range ((r : V →ₗ[ZMod 3] V) - LinearMap.id) =
      Submodule.span (ZMod 3) (b '' {i | s i = -1}) := by
  have hT : ((r : V →ₗ[ZMod 3] V) - LinearMap.id) =
      b.constr (ZMod 3) (fun i => (s i - 1) • b i) := by
    apply b.ext
    intro i
    rw [Module.Basis.constr_basis, LinearMap.sub_apply, LinearMap.id_apply,
      LinearEquiv.coe_toLinearMap, hact i]
    rw [sub_smul, one_smul]
  rw [hT, Module.Basis.constr_range]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    by_cases hi : s i = -1
    · change (s i - 1) • b i ∈ Submodule.span (ZMod 3) (b '' {i | s i = -1})
      have hc : ((-1 : ZMod 3) - 1) = 1 := by decide
      rw [hi, hc, one_smul]
      exact Submodule.subset_span ⟨i, hi, rfl⟩
    · change (s i - 1) • b i ∈ Submodule.span (ZMod 3) (b '' {i | s i = -1})
      have h1 : s i = 1 := (hpm i).resolve_right hi
      rw [h1, sub_self, zero_smul]
      exact Submodule.zero_mem _
  · rw [Submodule.span_le]
    rintro x ⟨i, hi, rfl⟩
    refine Submodule.subset_span ⟨i, ?_⟩
    show (s i - 1) • b i = b i
    rw [hi]
    have hc : ((-1 : ZMod 3) - 1) = 1 := by decide
    rw [hc, one_smul]

private lemma hdRo7DNormAux_range_flip_pair {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (r : V ≃ₗ[ZMod 3] V)
    (s : Fin (n + 1) → ZMod 3) (hpm : ∀ i, s i = 1 ∨ s i = -1)
    (hact : ∀ i, r (b i) = s i • b i) (hs0 : s 0 = 1)
    (h2 : Module.finrank (ZMod 3)
      (LinearMap.range ((r : V →ₗ[ZMod 3] V) - LinearMap.id)) = 2) :
    ∃ p q : Fin (n + 1), p ≠ 0 ∧ q ≠ 0 ∧ p ≠ q ∧ s p = -1 ∧ s q = -1 ∧
      (∀ l, l ∉ ({p, q} : Finset (Fin (n + 1))) → s l = 1) ∧
      LinearMap.range ((r : V →ₗ[ZMod 3] V) - LinearMap.id) =
        Submodule.span (ZMod 3) ({b p, b q} : Set V) := by
  let F : Finset (Fin (n + 1)) := Finset.univ.filter (fun i => s i = -1)
  have hFset : (F : Set (Fin (n + 1))) = {i | s i = -1} := by
    ext i
    simp [F]
  have hrange : LinearMap.range ((r : V →ₗ[ZMod 3] V) - LinearMap.id) =
      Submodule.span (ZMod 3) (b '' (F : Set (Fin (n + 1)))) := by
    rw [hdRo7DNormAux_range_diag b r s hpm hact, hFset]
  have hcard : F.card = 2 := by
    have h := hdRo7DNormAux_finrank_span_image_b b F
    rw [← hrange, h2] at h
    exact h.symm
  obtain ⟨p, q, hpq, hF⟩ := Finset.card_eq_two.mp hcard
  have h0F : (0 : Fin (n + 1)) ∉ F := by
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hs0]
    decide
  have hp0 : p ≠ 0 := by
    intro h
    exact h0F (by rw [hF, h]; simp)
  have hq0 : q ≠ 0 := by
    intro h
    exact h0F (by rw [hF, h]; simp)
  have hp : s p = -1 := by
    have : p ∈ F := by rw [hF]; simp
    simpa [F] using this
  have hq : s q = -1 := by
    have : q ∈ F := by rw [hF]; simp
    simpa [F] using this
  have hone : ∀ l, l ∉ ({p, q} : Finset (Fin (n + 1))) → s l = 1 := by
    intro l hl
    have hnot : l ∉ F := by
      rw [hF]
      simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using hl
    have hne : ¬ s l = -1 := by
      intro h
      exact hnot (by simp [F, h])
    exact (hpm l).resolve_right hne
  refine ⟨p, q, hp0, hq0, hpq, hp, hq, hone, ?_⟩
  rw [hrange, hF]
  congr 1
  ext x
  simp

private lemma hdRo7DNormAux_coord_diag {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (r : V ≃ₗ[ZMod 3] V)
    (s : Fin (n + 1) → ZMod 3) (hact : ∀ i, r (b i) = s i • b i) (m : Fin (n + 1))
    (x : V) : b.coord m (r x) = s m * b.coord m x := by
  have h : r x = ∑ i, (b.coord i x * s i) • b i := by
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, hact i, smul_smul]
    simp only [Module.Basis.coord_apply]
  rw [h, map_sum]
  rw [Finset.sum_eq_single m]
  · rw [hdRo7DNormAux_coord_smul_basis, if_pos rfl, mul_one, mul_comm]
  · intro i _ him
    rw [hdRo7DNormAux_coord_smul_basis, if_neg him, mul_zero]
  · intro hm
    exact absurd (Finset.mem_univ m) hm

private lemma hdRo7DNormAux_coord_line {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (a : V ≃ₗ[ZMod 3] V)
    (hnorm : ∀ s, DSP 3 b s → DSP 3 b (a * s * a⁻¹)) (hn : 5 ≤ n) (i : Fin n) :
    ∃ (i' : Fin n) (c : ZMod 3), c ≠ 0 ∧ a (b i.succ) = c • b i'.succ := by
  have hcard : 1 < ((Finset.univ : Finset (Fin n)).erase i).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨j₁, hj₁, j₂, hj₂, hj₁₂⟩ := Finset.one_lt_card.mp hcard
  rw [Finset.mem_erase] at hj₁ hj₂
  obtain ⟨hj₁i, -⟩ := hj₁
  obtain ⟨hj₂i, -⟩ := hj₂
  set v : V := a (b i.succ) with hv
  have hv_ne : v ≠ 0 := by
    rw [hv]
    exact fun h => b.ne_zero i.succ (a.injective (by simpa using h))
  have hsucc_ne : i.succ ≠ j₁.succ := fun h => hj₁i (Fin.succ_injective n h).symm
  have hsucc_ne₂ : i.succ ≠ j₂.succ := fun h => hj₂i (Fin.succ_injective n h).symm
  let ε₁ : V ≃ₗ[ZMod 3] V :=
    CFSG.StandardType.OrthF3.ggOrthSignChange b i.succ *
      CFSG.StandardType.OrthF3.ggOrthSignChange b j₁.succ
  have hε₁P : DSP 3 b ε₁ :=
    hdRo7DNormAux_double_mem_P b (Fin.succ_ne_zero i) (Fin.succ_ne_zero j₁) hsucc_ne
  have hε₁D : (⟨ε₁, hε₁P⟩ : hdRo7DNormAux_P b) ∈ hdRo7DNormAux_D b :=
    hdRo7DNormAux_double_mem_D b (Fin.succ_ne_zero i) (Fin.succ_ne_zero j₁) hsucc_ne
  have hρ₁C : DSP 3 b (a * ε₁ * a⁻¹) := hnorm _ hε₁P
  let d₁ : hdRo7DNormAux_P b := ⟨a * ε₁ * a⁻¹, hρ₁C⟩
  have hd₁D' : d₁ ∈ (hdRo7DNormAux_D b).map (hdRo7DNormAux_conj b a hnorm) := by
    refine Subgroup.mem_map.mpr ⟨⟨ε₁, hε₁P⟩, hε₁D, ?_⟩
    apply Subtype.ext
    rfl
  have hd₁D : d₁ ∈ hdRo7DNormAux_D b := hdRo7DNormAux_D_conj_le b a hnorm hn hd₁D'
  have hσ₁ : hdRo7DNormAux_sigma b d₁ = 1 :=
    hdRo7DNormAux_sigma_eq_one_of_pi_eq_one b d₁
      (show hdRo7DNormAux_pi b d₁ = 1 from hd₁D)
  have hdiag₁ : ∀ m, d₁.1 (b m) = hdRo7DNormAux_sign b d₁ m • b m := by
    intro m
    rw [hdRo7DNormAux_sigma_spec b d₁ m, hσ₁]
    simp
  have hrange₁ : LinearMap.range ((d₁.1 : V →ₗ[ZMod 3] V) - LinearMap.id) =
      Submodule.map (a : V →ₗ[ZMod 3] V)
        (Submodule.span (ZMod 3) ({b i.succ, b j₁.succ} : Set V)) := by
    rw [hdRo7DNormAux_range_conj b a ε₁, hdRo7DNormAux_double_range b hsucc_ne]
  have hfin₁ : Module.finrank (ZMod 3)
      (LinearMap.range ((d₁.1 : V →ₗ[ZMod 3] V) - LinearMap.id)) = 2 := by
    rw [hdRo7DNormAux_range_conj b a ε₁, hdRo7DNormAux_double_range b hsucc_ne,
      LinearEquiv.finrank_map_eq]
    exact hdRo7DNormAux_finrank_span_pair b hsucc_ne
  obtain ⟨P₁, Q₁, hP₁0, hQ₁0, hP₁Q₁, hsP₁, hsQ₁, hsone₁, hrangeD₁⟩ :=
    hdRo7DNormAux_range_flip_pair b d₁.1 (hdRo7DNormAux_sign b d₁)
      (hdRo7DNormAux_sign_pm b d₁) hdiag₁ (hdRo7DNormAux_sign_zero b d₁) hfin₁
  have hdv₁ : d₁.1 v = -v := by
    have hε : ε₁ (b i.succ) = -b i.succ := by
      rw [hdRo7DNormAux_double_apply b hsucc_ne i.succ]
      rw [if_pos (by simp)]
      simp
    rw [hv]
    show (a * ε₁ * a⁻¹) (a (b i.succ)) = -a (b i.succ)
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      show a⁻¹ (a (b i.succ)) = b i.succ from LinearEquiv.symm_apply_apply a (b i.succ),
      hε, map_neg]
  have hsupp₁ : ∀ m, m ∉ ({P₁, Q₁} : Finset (Fin (n + 1))) → b.coord m v = 0 := by
    intro m hm
    have h1 := hdRo7DNormAux_coord_diag b d₁.1 (hdRo7DNormAux_sign b d₁) hdiag₁ m v
    rw [hdv₁, map_neg, hsone₁ m hm, one_mul] at h1
    have h2 : b.coord m v + b.coord m v = 0 := by
      nth_rewrite 1 [← h1]
      exact neg_add_cancel _
    have h3 : (2 : ZMod 3) * b.coord m v = 0 := by
      rw [two_mul]
      exact h2
    exact (mul_eq_zero.mp h3).resolve_left (by decide)
  let ε₂ : V ≃ₗ[ZMod 3] V :=
    CFSG.StandardType.OrthF3.ggOrthSignChange b i.succ *
      CFSG.StandardType.OrthF3.ggOrthSignChange b j₂.succ
  have hε₂P : DSP 3 b ε₂ :=
    hdRo7DNormAux_double_mem_P b (Fin.succ_ne_zero i) (Fin.succ_ne_zero j₂) hsucc_ne₂
  have hε₂D : (⟨ε₂, hε₂P⟩ : hdRo7DNormAux_P b) ∈ hdRo7DNormAux_D b :=
    hdRo7DNormAux_double_mem_D b (Fin.succ_ne_zero i) (Fin.succ_ne_zero j₂) hsucc_ne₂
  have hρ₂C : DSP 3 b (a * ε₂ * a⁻¹) := hnorm _ hε₂P
  let d₂ : hdRo7DNormAux_P b := ⟨a * ε₂ * a⁻¹, hρ₂C⟩
  have hd₂D' : d₂ ∈ (hdRo7DNormAux_D b).map (hdRo7DNormAux_conj b a hnorm) := by
    refine Subgroup.mem_map.mpr ⟨⟨ε₂, hε₂P⟩, hε₂D, ?_⟩
    apply Subtype.ext
    rfl
  have hd₂D : d₂ ∈ hdRo7DNormAux_D b := hdRo7DNormAux_D_conj_le b a hnorm hn hd₂D'
  have hσ₂ : hdRo7DNormAux_sigma b d₂ = 1 :=
    hdRo7DNormAux_sigma_eq_one_of_pi_eq_one b d₂
      (show hdRo7DNormAux_pi b d₂ = 1 from hd₂D)
  have hdiag₂ : ∀ m, d₂.1 (b m) = hdRo7DNormAux_sign b d₂ m • b m := by
    intro m
    rw [hdRo7DNormAux_sigma_spec b d₂ m, hσ₂]
    simp
  have hfin₂ : Module.finrank (ZMod 3)
      (LinearMap.range ((d₂.1 : V →ₗ[ZMod 3] V) - LinearMap.id)) = 2 := by
    rw [hdRo7DNormAux_range_conj b a ε₂, hdRo7DNormAux_double_range b hsucc_ne₂,
      LinearEquiv.finrank_map_eq]
    exact hdRo7DNormAux_finrank_span_pair b hsucc_ne₂
  obtain ⟨P₂, Q₂, hP₂0, hQ₂0, hP₂Q₂, hsP₂, hsQ₂, hsone₂, hrangeD₂⟩ :=
    hdRo7DNormAux_range_flip_pair b d₂.1 (hdRo7DNormAux_sign b d₂)
      (hdRo7DNormAux_sign_pm b d₂) hdiag₂ (hdRo7DNormAux_sign_zero b d₂) hfin₂
  have hdv₂ : d₂.1 v = -v := by
    have hε : ε₂ (b i.succ) = -b i.succ := by
      rw [hdRo7DNormAux_double_apply b hsucc_ne₂ i.succ]
      rw [if_pos (by simp)]
      simp
    rw [hv]
    show (a * ε₂ * a⁻¹) (a (b i.succ)) = -a (b i.succ)
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      show a⁻¹ (a (b i.succ)) = b i.succ from LinearEquiv.symm_apply_apply a (b i.succ),
      hε, map_neg]
  have hsupp₂ : ∀ m, m ∉ ({P₂, Q₂} : Finset (Fin (n + 1))) → b.coord m v = 0 := by
    intro m hm
    have h1 := hdRo7DNormAux_coord_diag b d₂.1 (hdRo7DNormAux_sign b d₂) hdiag₂ m v
    rw [hdv₂, map_neg, hsone₂ m hm, one_mul] at h1
    have h2 : b.coord m v + b.coord m v = 0 := by
      nth_rewrite 1 [← h1]
      exact neg_add_cancel _
    have h3 : (2 : ZMod 3) * b.coord m v = 0 := by
      rw [two_mul]
      exact h2
    exact (mul_eq_zero.mp h3).resolve_left (by decide)
  have hex : ∃ m, b.coord m v ≠ 0 := by
    by_contra h
    push Not at h
    have hv0 : v = 0 := by
      conv_lhs => rw [← b.sum_repr v]
      apply Finset.sum_eq_zero
      intro i _
      rw [show b.repr v i = b.coord i v from rfl, h i, zero_smul]
    exact hv_ne hv0
  obtain ⟨m, hmne⟩ := hex
  have hm0 : m ≠ 0 := by
    intro hm0
    apply hmne
    apply hsupp₁
    rw [hm0]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hP₁0, Ne.symm hQ₁0⟩
  have huniq : ∀ l, l ≠ m → b.coord l v = 0 := by
    intro l hl
    by_contra hlne
    have hl0 : l ≠ 0 := by
      intro hl0
      apply hlne
      apply hsupp₁
      rw [hl0]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hP₁0, Ne.symm hQ₁0⟩
    have hmP₁ : m ∈ ({P₁, Q₁} : Finset (Fin (n + 1))) := by
      by_contra h
      exact hmne (hsupp₁ m h)
    have hlP₁ : l ∈ ({P₁, Q₁} : Finset (Fin (n + 1))) := by
      by_contra h
      exact hlne (hsupp₁ l h)
    have hmP₂ : m ∈ ({P₂, Q₂} : Finset (Fin (n + 1))) := by
      by_contra h
      exact hmne (hsupp₂ m h)
    have hlP₂ : l ∈ ({P₂, Q₂} : Finset (Fin (n + 1))) := by
      by_contra h
      exact hlne (hsupp₂ l h)
    have hpair₁ : ({P₁, Q₁} : Finset (Fin (n + 1))) = {m, l} := by
      apply (Finset.eq_of_subset_of_card_le ?_ ?_).symm
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        rcases hx with rfl | rfl
        · simpa only [Finset.mem_insert, Finset.mem_singleton] using hmP₁
        · simpa only [Finset.mem_insert, Finset.mem_singleton] using hlP₁
      · rw [Finset.card_pair hP₁Q₁, Finset.card_pair (Ne.symm hl)]
    have hpair₂ : ({P₂, Q₂} : Finset (Fin (n + 1))) = {m, l} := by
      apply (Finset.eq_of_subset_of_card_le ?_ ?_).symm
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        rcases hx with rfl | rfl
        · simpa only [Finset.mem_insert, Finset.mem_singleton] using hmP₂
        · simpa only [Finset.mem_insert, Finset.mem_singleton] using hlP₂
      · rw [Finset.card_pair hP₂Q₂, Finset.card_pair (Ne.symm hl)]
    have hpair_eq : ({P₁, Q₁} : Finset (Fin (n + 1))) = {P₂, Q₂} := hpair₁.trans hpair₂.symm
    have hd_eq : d₁.1 = d₂.1 := by
      apply LinearEquiv.toLinearMap_inj.mp
      apply b.ext
      intro x
      by_cases hx : x ∈ ({P₁, Q₁} : Finset (Fin (n + 1)))
      · have hx2 : x ∈ ({P₂, Q₂} : Finset (Fin (n + 1))) := by
          rw [← hpair_eq]; exact hx
        have h1 : hdRo7DNormAux_sign b d₁ x = -1 := by
          rcases Finset.mem_insert.mp hx with rfl | hx'
          · exact hsP₁
          · rw [Finset.mem_singleton.mp hx']; exact hsQ₁
        have h2 : hdRo7DNormAux_sign b d₂ x = -1 := by
          rcases Finset.mem_insert.mp hx2 with rfl | hx'
          · exact hsP₂
          · rw [Finset.mem_singleton.mp hx']; exact hsQ₂
        change d₁.1 (b x) = d₂.1 (b x)
        rw [hdiag₁ x, hdiag₂ x, h1, h2]
      · have hx2 : x ∉ ({P₂, Q₂} : Finset (Fin (n + 1))) := by
          rw [← hpair_eq]; exact hx
        change d₁.1 (b x) = d₂.1 (b x)
        rw [hdiag₁ x, hdiag₂ x, hsone₁ x hx, hsone₂ x hx2]
    have hε_eq : ε₁ = ε₂ := by
      calc ε₁ = a⁻¹ * d₁.1 * a := by dsimp [d₁, ε₁]; group
        _ = a⁻¹ * d₂.1 * a := by rw [hd_eq]
        _ = ε₂ := by dsimp [d₂, ε₂]; group
    have hne_basis : b j₁.succ ≠ -b j₁.succ := by
      intro h
      have hc := congrArg (b.coord j₁.succ) h
      rw [map_neg, show b.coord j₁.succ (b j₁.succ) = 1 from by
        simp] at hc
      exact absurd hc (by decide)
    have hmem : j₁.succ ∈ ({i.succ, j₂.succ} : Finset (Fin (n + 1))) := by
      by_contra h
      have hval : ε₂ (b j₁.succ) = b j₁.succ := by
        rw [show ε₂ = CFSG.StandardType.OrthF3.ggOrthSignChange b i.succ *
          CFSG.StandardType.OrthF3.ggOrthSignChange b j₂.succ from rfl]
        rw [hdRo7DNormAux_double_apply b hsucc_ne₂ j₁.succ, if_neg h]
        simp
      have hval₁ : ε₁ (b j₁.succ) = -b j₁.succ := by
        rw [show ε₁ = CFSG.StandardType.OrthF3.ggOrthSignChange b i.succ *
          CFSG.StandardType.OrthF3.ggOrthSignChange b j₁.succ from rfl]
        rw [hdRo7DNormAux_double_apply b hsucc_ne j₁.succ, if_pos (by simp)]
        simp
      rw [← hε_eq, hval₁] at hval
      exact hne_basis hval.symm
    have hjs : j₁.succ = j₂.succ := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      rcases hmem with h | h
      · exact absurd h.symm hsucc_ne
      · exact h
    exact hj₁₂ (Fin.succ_injective n hjs)
  refine ⟨Fin.pred m hm0, b.coord m v, hmne, ?_⟩
  have hsucc : (Fin.pred m hm0).succ = m := Fin.succ_pred m hm0
  rw [hsucc]
  conv_lhs => rw [← b.sum_repr v]
  rw [Finset.sum_eq_single m]
  · simp
  · intro l _ hl
    change b.coord l v • b l = 0
    rw [huniq l hl, zero_smul]
  · intro hm
    exact absurd (Finset.mem_univ m) hm

theorem d_normalizer_holds : DNormalizerLeaf := by
  intro p _ hp n hn V _ _ b a hnorm hfix
  subst hp
  choose τ lam hlam using fun j : Fin n => hdRo7DNormAux_coord_line b a hnorm hn j
  have hτinj : Function.Injective τ := by
    intro j j' hjj
    by_contra hne
    have h1 := (hlam j).2
    have h2 := (hlam j').2
    rw [hjj] at h1
    have h3 : b j.succ = (lam j * (lam j')⁻¹) • b j'.succ := by
      apply a.injective
      rw [h1, map_smul, h2]
      rw [← smul_smul]
      congr 1
      exact (inv_smul_smul₀ (hlam j').1 (b (τ j').succ)).symm
    have h4 := congrArg (fun v => b.coord j.succ v) h3
    rw [show b.coord j.succ (b j.succ) = 1 from by
      simp,
      hdRo7DNormAux_coord_smul_basis] at h4
    rw [if_neg (fun hh => hne (Fin.succ_injective n hh).symm), mul_zero] at h4
    exact one_ne_zero h4
  let τe : Equiv.Perm (Fin n) := Equiv.ofBijective τ ⟨hτinj, Finite.surjective_of_injective hτinj⟩
  let σ : Equiv.Perm (Fin (n + 1)) := Equiv.Perm.decomposeFin.symm (0, τe)
  have hσ0 : σ 0 = 0 := Equiv.Perm.decomposeFin_symm_apply_zero 0 τe
  have hσsucc : ∀ j : Fin n, σ j.succ = (τ j).succ := by
    intro j
    change (Equiv.Perm.decomposeFin.symm (0, τe)) j.succ = (τ j).succ
    rw [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self]
    rfl
  refine ⟨σ, fun i => if h : i = 0 then 1 else lam (Fin.pred i h), hσ0, ?_, ?_, ?_⟩
  · dsimp only
    rw [dif_pos rfl]
  · intro i
    dsimp only
    by_cases hi : i = 0
    · subst hi; rw [dif_pos rfl]; exact Or.inl rfl
    · rw [dif_neg hi]
      have hpm : ∀ x : ZMod 3, x ≠ 0 → x = 1 ∨ x = -1 := by
        intro x hx
        fin_cases x
        · exact absurd rfl hx
        · exact Or.inl rfl
        · exact Or.inr rfl
      exact hpm (lam (Fin.pred i hi)) (hlam (Fin.pred i hi)).1
  · intro i
    dsimp only
    by_cases hi : i = 0
    · subst hi
      rw [dif_pos rfl, hfix, hσ0]
      simp
    · rw [dif_neg hi]
      have hτ : (Fin.pred i hi).succ = i := Fin.succ_pred i hi
      have hσi : σ i = (τ (Fin.pred i hi)).succ := by
        conv_lhs => rw [show i = (Fin.pred i hi).succ from hτ.symm]
        exact hσsucc (Fin.pred i hi)
      rw [hσi]
      conv_lhs => rw [show i = (Fin.pred i hi).succ from hτ.symm]
      exact (hlam (Fin.pred i hi)).2

end CFSG.StandardType.HdRo7D
