module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CDefs
import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthSPerm
import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ExtensionPCore

public section

namespace CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma hdRo7CNormAux_sq_pm (a : ZMod 3) (h : a = 1 ∨ a = -1) : a * a = 1 := by
  rcases h with h | h <;> rw [h] <;> decide
private lemma hdRo7CNormAux_char3 {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (x : V) : -x - x = x := by
  have h : (-1 : ZMod 3) + (-1 : ZMod 3) = 1 := by decide
  calc -x - x = (-1 : ZMod 3) • x + (-1 : ZMod 3) • x := by rw [sub_eq_add_neg, neg_one_smul]
    _ = ((-1 : ZMod 3) + (-1 : ZMod 3)) • x := by rw [add_smul]
    _ = (1 : ZMod 3) • x := by rw [h]
    _ = x := by rw [one_smul]
private lemma hdRo7CNormAux_coord_smul_basis {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (k i : Fin (n + 1)) (c : ZMod 3) : b.coord k (c • b i) = c * (if i = k then 1 else 0) := by
  rw [map_smul, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul]
private noncomputable def hdRo7CNormAux_P {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) : Subgroup (V ≃ₗ[ZMod 3] V) where
  carrier := {s | C2SP 3 b s}
  mul_mem' := by
    intro s t hs ht
    obtain ⟨σ, c, hσ0, hc0, hc, hs⟩ := hs
    obtain ⟨τ, d, hτ0, hd0, hd, ht⟩ := ht
    refine ⟨σ * τ, fun i => d i * c (τ i), ?_, ?_, ?_, ?_⟩
    · rw [Equiv.Perm.mul_apply, hτ0, hσ0]
    · show d 0 * c (τ 0) = 1; rw [hd0, hτ0, hc0, mul_one]
    · intro i
      change d i * c (τ i) = 1 ∨ d i * c (τ i) = -1
      rcases hd i with h | h <;> rcases hc (τ i) with h' | h' <;> rw [h, h'] <;> decide
    · intro i
      calc (s * t) (b i) = s (t (b i)) := LinearEquiv.mul_apply s t (b i)
        _ = s (d i • b (τ i)) := by rw [ht i]
        _ = d i • s (b (τ i)) := by rw [map_smul]
        _ = d i • (c (τ i) • b (σ (τ i))) := by rw [hs (τ i)]
        _ = (d i * c (τ i)) • b ((σ * τ) i) := by rw [← mul_smul, Equiv.Perm.mul_apply]
  one_mem' := ⟨1, fun _ => 1, rfl, rfl, fun _ => Or.inl rfl, fun i => by simp⟩
  inv_mem' := by
    intro s hs
    obtain ⟨σ, c, hσ0, hc0, hc, hs⟩ := hs
    have hσinv0 : σ.symm 0 = 0 := (Equiv.symm_apply_eq σ).mpr hσ0.symm
    refine ⟨σ.symm, fun j => c (σ.symm j), hσinv0, ?_, ?_, ?_⟩
    · change c (σ.symm 0) = 1; rw [hσinv0]; exact hc0
    · intro j; exact hc (σ.symm j)
    · intro j
      change s.symm (b j) = c (σ.symm j) • b (σ.symm j)
      rw [LinearEquiv.symm_apply_eq]
      calc b j = (c (σ.symm j) * c (σ.symm j)) • b j := by
              rw [hdRo7CNormAux_sq_pm (c (σ.symm j)) (hc (σ.symm j)), one_smul]
        _ = c (σ.symm j) • (c (σ.symm j) • b (σ (σ.symm j))) := by
              rw [← mul_smul, Equiv.apply_symm_apply σ j]
        _ = c (σ.symm j) • s (b (σ.symm j)) := by rw [hs]
        _ = s (c (σ.symm j) • b (σ.symm j)) := by rw [map_smul]
private noncomputable def hdRo7CNormAux_sigma {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (s : hdRo7CNormAux_P b) : Equiv.Perm (Fin (n + 1)) := Classical.choose s.2
private noncomputable def hdRo7CNormAux_sign {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (s : hdRo7CNormAux_P b) :
    Fin (n + 1) → ZMod 3 := Classical.choose (Classical.choose_spec s.2)
private lemma hdRo7CNormAux_sigma_zero {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (s : hdRo7CNormAux_P b) : hdRo7CNormAux_sigma b s 0 = 0 :=
  (Classical.choose_spec (Classical.choose_spec s.2)).1
private lemma hdRo7CNormAux_sign_zero {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (s : hdRo7CNormAux_P b) : hdRo7CNormAux_sign b s 0 = 1 :=
  (Classical.choose_spec (Classical.choose_spec s.2)).2.1
private lemma hdRo7CNormAux_sign_pm {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (s : hdRo7CNormAux_P b) :
    ∀ i, hdRo7CNormAux_sign b s i = 1 ∨ hdRo7CNormAux_sign b s i = -1 :=
  (Classical.choose_spec (Classical.choose_spec s.2)).2.2.1
private lemma hdRo7CNormAux_sigma_spec {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (s : hdRo7CNormAux_P b) :
    ∀ i, s.1 (b i) = hdRo7CNormAux_sign b s i • b (hdRo7CNormAux_sigma b s i) :=
  (Classical.choose_spec (Classical.choose_spec s.2)).2.2.2
private lemma hdRo7CNormAux_unique {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (s : hdRo7CNormAux_P b)
    {σ : Equiv.Perm (Fin (n + 1))} {c : Fin (n + 1) → ZMod 3}
    (hc : ∀ i, c i = 1 ∨ c i = -1)
    (h : ∀ i, s.1 (b i) = c i • b (σ i)) : σ = hdRo7CNormAux_sigma b s ∧ c = hdRo7CNormAux_sign b s := by
  have hσc : ∀ i, hdRo7CNormAux_sigma b s i = σ i ∧ hdRo7CNormAux_sign b s i = c i := by
    intro i
    have heq : hdRo7CNormAux_sign b s i • b (hdRo7CNormAux_sigma b s i) = c i • b (σ i) := by
      rw [← hdRo7CNormAux_sigma_spec b s i, h i]
    have hcoord := congrArg (fun v => b.coord (hdRo7CNormAux_sigma b s i) v) heq
    rw [hdRo7CNormAux_coord_smul_basis, hdRo7CNormAux_coord_smul_basis] at hcoord
    rw [if_pos rfl, mul_one] at hcoord
    by_cases hsi : σ i = hdRo7CNormAux_sigma b s i
    · rw [if_pos hsi, mul_one] at hcoord
      exact ⟨hsi.symm, hcoord⟩
    · rw [if_neg hsi, mul_zero] at hcoord
      exfalso
      rcases hdRo7CNormAux_sign_pm b s i with h1 | h1 <;> rw [h1] at hcoord <;>
        exact absurd hcoord (by decide)
  refine ⟨Equiv.ext fun i => (hσc i).1.symm, funext fun i => (hσc i).2.symm⟩
private lemma hdRo7CNormAux_sigma_mul {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (s t : hdRo7CNormAux_P b) :
    hdRo7CNormAux_sigma b (s * t) = hdRo7CNormAux_sigma b s * hdRo7CNormAux_sigma b t := by
  have h : ∀ i, (s * t).1 (b i) =
      (hdRo7CNormAux_sign b t i * hdRo7CNormAux_sign b s (hdRo7CNormAux_sigma b t i)) •
        b ((hdRo7CNormAux_sigma b s * hdRo7CNormAux_sigma b t) i) := by
    intro i
    calc (s * t).1 (b i) = s.1 (t.1 (b i)) := LinearEquiv.mul_apply s.1 t.1 (b i)
      _ = s.1 (hdRo7CNormAux_sign b t i • b (hdRo7CNormAux_sigma b t i)) := by
            rw [hdRo7CNormAux_sigma_spec b t i]
      _ = hdRo7CNormAux_sign b t i • s.1 (b (hdRo7CNormAux_sigma b t i)) := by rw [map_smul]
      _ = hdRo7CNormAux_sign b t i •
            (hdRo7CNormAux_sign b s (hdRo7CNormAux_sigma b t i) •
              b (hdRo7CNormAux_sigma b s (hdRo7CNormAux_sigma b t i))) := by
            rw [hdRo7CNormAux_sigma_spec b s]
      _ = (hdRo7CNormAux_sign b t i * hdRo7CNormAux_sign b s (hdRo7CNormAux_sigma b t i)) •
            b ((hdRo7CNormAux_sigma b s * hdRo7CNormAux_sigma b t) i) := by
            rw [← mul_smul, Equiv.Perm.mul_apply]
  exact (hdRo7CNormAux_unique b (s * t)
    (σ := hdRo7CNormAux_sigma b s * hdRo7CNormAux_sigma b t)
    (c := fun i => hdRo7CNormAux_sign b t i * hdRo7CNormAux_sign b s (hdRo7CNormAux_sigma b t i))
    (fun i => by
      rcases hdRo7CNormAux_sign_pm b t i with h1 | h1 <;>
        rcases hdRo7CNormAux_sign_pm b s (hdRo7CNormAux_sigma b t i) with h2 | h2 <;>
        rw [h1, h2] <;> decide)
    h).1.symm
private lemma hdRo7CNormAux_subtypePerm_cond {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (s : hdRo7CNormAux_P b) :
    ∀ i : Fin (n + 1), (hdRo7CNormAux_sigma b s i ≠ 0) ↔ (i ≠ 0) := by
  intro i
  constructor
  · intro hi h
    exact hi (by rw [h]; exact hdRo7CNormAux_sigma_zero b s)
  · intro hi h
    exact hi ((hdRo7CNormAux_sigma b s).injective (h.trans (hdRo7CNormAux_sigma_zero b s).symm))
private noncomputable def hdRo7CNormAux_pi {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) : hdRo7CNormAux_P b →* Equiv.Perm {i : Fin (n + 1) // i ≠ 0} where
  toFun s := (hdRo7CNormAux_sigma b s).subtypePerm (hdRo7CNormAux_subtypePerm_cond b s)
  map_one' := by
    have h1 : hdRo7CNormAux_sigma b (1 : hdRo7CNormAux_P b) = 1 :=
      (hdRo7CNormAux_unique b (1 : hdRo7CNormAux_P b) (σ := 1) (c := fun _ => 1)
        (fun _ => Or.inl rfl) (fun i => by simp)).1.symm
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change (hdRo7CNormAux_sigma b (1 : hdRo7CNormAux_P b)) x.1 = x.1
    rw [h1]
    rfl
  map_mul' s t := by
    ext x
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.subtypePerm_apply]
    rw [hdRo7CNormAux_sigma_mul]
    rfl
private lemma hdRo7CNormAux_sigma_eq_one_of_pi_eq_one {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod 3) V)
    (s : hdRo7CNormAux_P b) (hs : hdRo7CNormAux_pi b s = 1) : hdRo7CNormAux_sigma b s = 1 := by
  apply Equiv.ext
  intro i
  by_cases hi : i = 0
  · subst hi; exact hdRo7CNormAux_sigma_zero b s
  · have hx := congrArg (fun e : Equiv.Perm {i : Fin (n + 1) // i ≠ 0} => e ⟨i, hi⟩) hs
    have hxv := congrArg Subtype.val hx
    simpa [hdRo7CNormAux_pi, Equiv.Perm.subtypePerm_apply] using hxv
private noncomputable def hdRo7CNormAux_D {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) : Subgroup (hdRo7CNormAux_P b) :=
  (hdRo7CNormAux_pi b).ker
private lemma hdRo7CNormAux_D_sq {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (s : hdRo7CNormAux_P b)
    (hs : s ∈ hdRo7CNormAux_D b) : s ^ 2 = 1 := by
  have hsσ : hdRo7CNormAux_sigma b s = 1 :=
    hdRo7CNormAux_sigma_eq_one_of_pi_eq_one b s (show hdRo7CNormAux_pi b s = 1 from hs)
  have hbasis : ∀ i, s.1 (s.1 (b i)) = b i := by
    intro i
    have h2 : s.1 (b i) = hdRo7CNormAux_sign b s i • b i := by
      rw [hdRo7CNormAux_sigma_spec b s i, hsσ]; simp
    calc s.1 (s.1 (b i)) = s.1 (hdRo7CNormAux_sign b s i • b i) := by rw [h2]
      _ = hdRo7CNormAux_sign b s i • s.1 (b i) := by rw [map_smul]
      _ = hdRo7CNormAux_sign b s i • (hdRo7CNormAux_sign b s i • b i) := by rw [h2]
      _ = b i := by
            rw [← mul_smul, hdRo7CNormAux_sq_pm _ (hdRo7CNormAux_sign_pm b s i), one_smul]
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
private lemma hdRo7CNormAux_finite_P {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) : Finite (hdRo7CNormAux_P b) := by
  haveI : Finite V := Finite.of_equiv _ b.repr.toEquiv.symm
  haveI : Fintype V := Fintype.ofFinite V
  haveI : Fintype (Fin (n + 1) → V) := inferInstance
  exact Finite.of_injective (fun s : hdRo7CNormAux_P b => fun i => s.1 (b i)) (by
    intro s t h
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    have hmap : (s.1 : V →ₗ[ZMod 3] V) = (t.1 : V →ₗ[ZMod 3] V) := by
      apply b.ext
      intro i
      exact congrFun h i
    exact congrArg (fun f : V →ₗ[ZMod 3] V => f x) hmap)
private noncomputable def hdRo7CNormAux_conj {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (a : V ≃ₗ[ZMod 3] V)
    (hnorm : ∀ s, C2SP 3 b s → C2SP 3 b (a * s * a⁻¹)) : hdRo7CNormAux_P b →* hdRo7CNormAux_P b where
  toFun s := ⟨a * s.1 * a⁻¹, hnorm s.1 s.2⟩
  map_one' := by apply Subtype.ext; simp only [Subgroup.coe_mul, Subgroup.coe_one]; group
  map_mul' s t := by apply Subtype.ext; simp only [Subgroup.coe_mul, Subgroup.coe_one]; group
private lemma hdRo7CNormAux_conj_injective {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (a : V ≃ₗ[ZMod 3] V)
    (hnorm : ∀ s, C2SP 3 b s → C2SP 3 b (a * s * a⁻¹)) : Function.Injective (hdRo7CNormAux_conj b a hnorm) := by
  intro s t h
  apply Subtype.ext
  have h' := congrArg Subtype.val h
  exact mul_right_cancel (mul_left_cancel h')
private lemma hdRo7CNormAux_conj_surjective {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (a : V ≃ₗ[ZMod 3] V)
    (hnorm : ∀ s, C2SP 3 b s → C2SP 3 b (a * s * a⁻¹)) : Function.Surjective (hdRo7CNormAux_conj b a hnorm) := by
  haveI := hdRo7CNormAux_finite_P b
  exact Finite.surjective_of_injective (hdRo7CNormAux_conj_injective b a hnorm)
private lemma hdRo7CNormAux_D_isPGroup {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) : IsPGroup 2 (hdRo7CNormAux_D b) := by
  intro g
  refine ⟨1, ?_⟩
  rw [show (2 : ℕ) ^ 1 = 2 from rfl]
  apply Subtype.ext
  simpa using hdRo7CNormAux_D_sq b g.1 g.2
private noncomputable def hdRo7CNormAux_alphaEquiv (n : ℕ) : {i : Fin (n + 1) // i ≠ 0} ≃ Fin n where
  toFun x := Fin.pred x.1 x.2
  invFun j := ⟨j.succ, Fin.succ_ne_zero j⟩
  left_inv x := by apply Subtype.ext; exact Fin.succ_pred x.1 x.2
  right_inv j := by simp [Fin.pred_succ]
private lemma hdRo7CNormAux_pi_surjective {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) : Function.Surjective (hdRo7CNormAux_pi b) := by
  intro ρ
  let φ := hdRo7CNormAux_alphaEquiv n
  let τ : Equiv.Perm (Fin n) := φ.symm.trans (ρ.trans φ)
  let σ : Equiv.Perm (Fin (n + 1)) := Equiv.Perm.decomposeFin.symm (0, τ)
  have hσ0 : σ 0 = 0 := Equiv.Perm.decomposeFin_symm_apply_zero 0 τ
  have hσsucc : ∀ j : Fin n, σ j.succ = (ρ (φ.symm j)).1 := by
    intro j
    change (Equiv.Perm.decomposeFin.symm (0, τ)) j.succ = (ρ (φ.symm j)).1
    rw [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self]
    exact Fin.succ_pred (ρ (φ.symm j)).1 (ρ (φ.symm j)).2
  have hP : b.equiv b σ ∈ hdRo7CNormAux_P b :=
    ⟨σ, fun _ => 1, hσ0, rfl, fun _ => Or.inl rfl, by
      intro i; rw [Module.Basis.equiv_apply]; simp⟩
  refine ⟨⟨b.equiv b σ, hP⟩, ?_⟩
  have hsig : hdRo7CNormAux_sigma b ⟨b.equiv b σ, hP⟩ = σ :=
    (hdRo7CNormAux_unique b ⟨b.equiv b σ, hP⟩ (σ := σ) (c := fun _ => 1)
      (fun _ => Or.inl rfl) (fun i => by rw [Module.Basis.equiv_apply]; simp)).1.symm
  apply Equiv.ext
  intro x
  change ↑(((hdRo7CNormAux_sigma b ⟨b.equiv b σ, hP⟩).subtypePerm
    (hdRo7CNormAux_subtypePerm_cond b ⟨b.equiv b σ, hP⟩)) x) = ↑(ρ x)
  simp only [hsig]
  simp only [Equiv.Perm.subtypePerm_apply]
  apply Subtype.ext
  have hx : x.1 = (φ x).succ := (Fin.succ_pred x.1 x.2).symm
  simp only [hx, hσsucc]
  simp [φ]
private lemma hdRo7CNormAux_D_conj_le {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (a : V ≃ₗ[ZMod 3] V)
    (hnorm : ∀ s, C2SP 3 b s → C2SP 3 b (a * s * a⁻¹)) (hn : 5 ≤ n) :
    (hdRo7CNormAux_D b).map (hdRo7CNormAux_conj b a hnorm) ≤ hdRo7CNormAux_D b := by
  have hsurj := hdRo7CNormAux_conj_surjective b a hnorm
  have hD'normal : ((hdRo7CNormAux_D b).map (hdRo7CNormAux_conj b a hnorm)).Normal :=
    (show (hdRo7CNormAux_D b).Normal from by
      change ((hdRo7CNormAux_pi b).ker).Normal; infer_instance).map _ hsurj
  have hD'p : IsPGroup 2 ((hdRo7CNormAux_D b).map (hdRo7CNormAux_conj b a hnorm)) :=
    (hdRo7CNormAux_D_isPGroup b).map _
  have hQnormal : (((hdRo7CNormAux_D b).map (hdRo7CNormAux_conj b a hnorm)).map
      (hdRo7CNormAux_pi b)).Normal :=
    hD'normal.map _ (hdRo7CNormAux_pi_surjective b)
  have hQp : IsPGroup 2 (((hdRo7CNormAux_D b).map (hdRo7CNormAux_conj b a hnorm)).map
      (hdRo7CNormAux_pi b)) := hD'p.map _
  have hQbot : (((hdRo7CNormAux_D b).map (hdRo7CNormAux_conj b a hnorm)).map
      (hdRo7CNormAux_pi b)) = ⊥ := by
    refine CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.normal_isPGroup_perm_eq_bot
      (α := {i : Fin (n + 1) // i ≠ 0}) ?_ _ hQp
    rw [Fintype.card_congr (hdRo7CNormAux_alphaEquiv n), Fintype.card_fin]
    exact hn
  have hle := (Subgroup.map_eq_bot_iff _ (f := hdRo7CNormAux_pi b)).mp hQbot
  simpa [hdRo7CNormAux_D] using hle
private lemma hdRo7CNormAux_signChange_mem_P {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (j : Fin n) : CFSG.StandardType.OrthF3.ggOrthSignChange b j.succ ∈ hdRo7CNormAux_P b := by
  refine ⟨1, fun k => if k = j.succ then -1 else 1, rfl, ?_, ?_, ?_⟩
  · show (if (0 : Fin (n + 1)) = j.succ then (-1 : ZMod 3) else 1) = 1
    rw [if_neg (fun h => Fin.succ_ne_zero j h.symm)]
  · intro k
    dsimp only
    by_cases hk : k = j.succ
    · rw [if_pos hk]; exact Or.inr rfl
    · rw [if_neg hk]; exact Or.inl rfl
  · intro k
    by_cases hk : k = j.succ
    · subst hk; simp [CFSG.StandardType.OrthF3.ggOrthSignChange_apply_self]
    · simp [CFSG.StandardType.OrthF3.ggOrthSignChange_apply_of_ne b hk, hk]
private lemma hdRo7CNormAux_signChange_mem_D {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {n : ℕ} (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (j : Fin n) :
    (⟨CFSG.StandardType.OrthF3.ggOrthSignChange b j.succ, hdRo7CNormAux_signChange_mem_P b j⟩ : hdRo7CNormAux_P b) ∈
      hdRo7CNormAux_D b := by
  change (hdRo7CNormAux_sigma b
    ⟨CFSG.StandardType.OrthF3.ggOrthSignChange b j.succ, hdRo7CNormAux_signChange_mem_P b j⟩).subtypePerm
      (hdRo7CNormAux_subtypePerm_cond b
        ⟨CFSG.StandardType.OrthF3.ggOrthSignChange b j.succ, hdRo7CNormAux_signChange_mem_P b j⟩) = 1
  have hσ : hdRo7CNormAux_sigma b
      ⟨CFSG.StandardType.OrthF3.ggOrthSignChange b j.succ, hdRo7CNormAux_signChange_mem_P b j⟩ = 1 :=
    (hdRo7CNormAux_unique b _
      (σ := 1) (c := fun k => if k = j.succ then -1 else 1)
      (fun k => by by_cases hk : k = j.succ <;> simp [hk])
      (fun k => by
        by_cases hk : k = j.succ
        · subst hk; simp [CFSG.StandardType.OrthF3.ggOrthSignChange_apply_self]
        · simp [CFSG.StandardType.OrthF3.ggOrthSignChange_apply_of_ne b hk, hk])).1.symm
  simp only [hσ]
  exact Equiv.Perm.subtypePerm_one _
private lemma hdRo7CNormAux_range_conj {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (a : V ≃ₗ[ZMod 3] V) (j : Fin n) :
    LinearMap.range (((a * CFSG.StandardType.OrthF3.ggOrthSignChange b j.succ * a⁻¹ : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V)
        - LinearMap.id) =
      Submodule.map (a : V →ₗ[ZMod 3] V)
        (LinearMap.range (((CFSG.StandardType.OrthF3.ggOrthSignChange b j.succ : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V)
          - LinearMap.id)) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨((CFSG.StandardType.OrthF3.ggOrthSignChange b j.succ : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V) (a⁻¹ y) - a⁻¹ y, ⟨a⁻¹ y, rfl⟩, ?_⟩
    show a (((CFSG.StandardType.OrthF3.ggOrthSignChange b j.succ : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V) (a⁻¹ y) - a⁻¹ y) =
      (a * CFSG.StandardType.OrthF3.ggOrthSignChange b j.succ * a⁻¹) y - y
    rw [map_sub, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    rw [show a (a⁻¹ y) = y from LinearEquiv.apply_symm_apply a y]
    rfl
  · rintro ⟨z, ⟨y, rfl⟩, rfl⟩
    refine ⟨a y, ?_⟩
    show (a * CFSG.StandardType.OrthF3.ggOrthSignChange b j.succ * a⁻¹) (a y) - a y =
      a (((CFSG.StandardType.OrthF3.ggOrthSignChange b j.succ : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V) y - y)
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    rw [show a⁻¹ (a y) = y from LinearEquiv.symm_apply_apply a y]
    rw [map_sub]
    rfl
private lemma hdRo7CNormAux_rank {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (a : V ≃ₗ[ZMod 3] V) (j : Fin n) :
    Module.finrank (ZMod 3) (LinearMap.range (((a * CFSG.StandardType.OrthF3.ggOrthSignChange b j.succ * a⁻¹ :
      V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V) - LinearMap.id)) = 1 := by
  rw [hdRo7CNormAux_range_conj b a j, LinearEquiv.finrank_map_eq]
  exact (CFSG.StandardType.OrthF3.ggOrthSignChange_isRefl b j.succ).2
private lemma hdRo7CNormAux_coord_line {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod 3) V) (a : V ≃ₗ[ZMod 3] V)
    (hnorm : ∀ s, C2SP 3 b s → C2SP 3 b (a * s * a⁻¹)) (hn : 5 ≤ n) (j : Fin n) :
    ∃ (k : Fin n) (lam : ZMod 3), lam ≠ 0 ∧ a (b j.succ) = lam • b k.succ := by
  haveI : Module.Finite (ZMod 3) V := Module.Finite.of_basis b
  have hepsP : CFSG.StandardType.OrthF3.ggOrthSignChange b j.succ ∈ hdRo7CNormAux_P b := hdRo7CNormAux_signChange_mem_P b j
  have hepsD : (⟨CFSG.StandardType.OrthF3.ggOrthSignChange b j.succ, hepsP⟩ : hdRo7CNormAux_P b) ∈ hdRo7CNormAux_D b :=
    hdRo7CNormAux_signChange_mem_D b j
  have hrC : C2SP 3 b (a * CFSG.StandardType.OrthF3.ggOrthSignChange b j.succ * a⁻¹) := hnorm _ hepsP
  let rP : hdRo7CNormAux_P b := ⟨a * CFSG.StandardType.OrthF3.ggOrthSignChange b j.succ * a⁻¹, hrC⟩
  have hrD' : rP ∈ (hdRo7CNormAux_D b).map (hdRo7CNormAux_conj b a hnorm) := by
    refine Subgroup.mem_map.mpr ⟨⟨CFSG.StandardType.OrthF3.ggOrthSignChange b j.succ, hepsP⟩, hepsD, ?_⟩
    apply Subtype.ext
    rfl
  have hrD : rP ∈ hdRo7CNormAux_D b := hdRo7CNormAux_D_conj_le b a hnorm hn hrD'
  have hsσ : hdRo7CNormAux_sigma b rP = 1 :=
    hdRo7CNormAux_sigma_eq_one_of_pi_eq_one b rP (show hdRo7CNormAux_pi b rP = 1 from hrD)
  have hdiag : ∀ k, rP.1 (b k) = hdRo7CNormAux_sign b rP k • b k := by
    intro k
    rw [hdRo7CNormAux_sigma_spec b rP k, hsσ]
    simp
  have hrank : Module.finrank (ZMod 3)
      (LinearMap.range ((rP.1 : V →ₗ[ZMod 3] V) - LinearMap.id)) = 1 :=
    hdRo7CNormAux_rank b a j
  have hex : ∃ k, hdRo7CNormAux_sign b rP k = -1 := by
    by_contra h
    push Not at h
    have hall : ∀ k, hdRo7CNormAux_sign b rP k = 1 := by
      intro k
      rcases hdRo7CNormAux_sign_pm b rP k with h1 | h1
      · exact h1
      · exact absurd h1 (h k)
    have hr1 : rP.1 = 1 := by
      apply b.ext'
      intro k
      rw [hdiag k, hall k]
      simp
    have hzero : (rP.1 : V →ₗ[ZMod 3] V) - LinearMap.id = 0 := by
      rw [hr1]; simp
    rw [hzero, LinearMap.range_zero, finrank_bot] at hrank
    exact one_ne_zero hrank.symm
  obtain ⟨k, hk⟩ := hex
  have hk0 : k ≠ 0 := by
    intro hk0
    rw [hk0] at hk
    rw [hdRo7CNormAux_sign_zero b rP] at hk
    exact absurd hk (by decide)
  have hbk_mem : b k ∈ LinearMap.range ((rP.1 : V →ₗ[ZMod 3] V) - LinearMap.id) := by
    refine ⟨b k, ?_⟩
    change rP.1 (b k) - b k = b k
    rw [hdiag k, hk, neg_one_smul]
    exact hdRo7CNormAux_char3 (b k)
  have hspan_le : Submodule.span (ZMod 3) ({b k} : Set V) ≤
      LinearMap.range ((rP.1 : V →ₗ[ZMod 3] V) - LinearMap.id) := by
    rw [Submodule.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact hbk_mem
  have hfin : Module.finrank (ZMod 3) (Submodule.span (ZMod 3) ({b k} : Set V)) = 1 :=
    finrank_span_singleton (b.ne_zero k)
  have hrange_eq : LinearMap.range ((rP.1 : V →ₗ[ZMod 3] V) - LinearMap.id) =
      Submodule.span (ZMod 3) ({b k} : Set V) :=
    (Submodule.eq_of_le_of_finrank_eq hspan_le (by rw [hrank, hfin])).symm
  have ha_mem : a (b j.succ) ∈ LinearMap.range ((rP.1 : V →ₗ[ZMod 3] V) - LinearMap.id) := by
    refine ⟨a (b j.succ), ?_⟩
    change rP.1 (a (b j.succ)) - a (b j.succ) = a (b j.succ)
    have hr : rP.1 (a (b j.succ)) = -a (b j.succ) := by
      show (a * CFSG.StandardType.OrthF3.ggOrthSignChange b j.succ * a⁻¹) (a (b j.succ)) = -a (b j.succ)
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
      rw [show a⁻¹ (a (b j.succ)) = b j.succ from LinearEquiv.symm_apply_apply a (b j.succ)]
      rw [CFSG.StandardType.OrthF3.ggOrthSignChange_apply_self, map_neg]
    rw [hr]
    exact hdRo7CNormAux_char3 (a (b j.succ))
  rw [hrange_eq, Submodule.mem_span_singleton] at ha_mem
  obtain ⟨lam, hlam⟩ := ha_mem
  refine ⟨Fin.pred k hk0, lam, ?_, ?_⟩
  · intro hlam0
    have h0 : a (b j.succ) = a 0 := by rw [← hlam, hlam0, zero_smul, map_zero]
    exact (b.ne_zero j.succ) (a.injective h0)
  · rw [Fin.succ_pred k hk0]; exact hlam.symm
theorem c2_normalizer_holds : C2NormalizerLeaf := by
  intro p _ hp n hn V _ _ b a hnorm hfix
  subst hp
  choose τ lam hlam using fun j : Fin n => hdRo7CNormAux_coord_line b a hnorm hn j
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
      simpa using hdRo7CNormAux_coord_smul_basis b j.succ j.succ 1,
      hdRo7CNormAux_coord_smul_basis] at h4
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
end CFSG.StandardType.HdRo7C
