module

public import CFSG.Quasithin.Recognition.G112A2D6ZornFin

public section

namespace CFSG.Quasithin.G112A2

open CFSG.Open
open scoped commutatorElement

@[expose] def z6Aut (g : z6O ≃ₗ[ZMod 2] z6O) : Prop :=
  ∀ x y, g (quasithinZornMul x y) = quasithinZornMul (g x) (g y)

theorem z6_mem_of_aut {g : z6O ≃ₗ[ZMod 2] z6O} (hg : z6Aut g) :
    g ∈ quasithinG2 (ZMod 2) :=
  Subgroup.subset_closure (show g ∈ {g : z6O ≃ₗ[ZMod 2] z6O |
    ∀ x y, g (quasithinZornMul x y) = quasithinZornMul (g x) (g y)} from hg)

theorem z6_aut_of_mem {g : z6O ≃ₗ[ZMod 2] z6O} (hg : g ∈ quasithinG2 (ZMod 2)) : z6Aut g := by
  induction hg using Subgroup.closure_induction with
  | mem g hg => exact hg
  | one => intro x y; rfl
  | mul g h _ _ hg hh =>
    intro x y
    show g (h (quasithinZornMul x y)) = quasithinZornMul (g (h x)) (g (h y))
    rw [hh, hg]
  | inv g _ hg =>
    intro x y
    have h1 := hg (g⁻¹ x) (g⁻¹ y)
    have e1 : g (g⁻¹ x) = x := LinearEquiv.apply_symm_apply g x
    have e2 : g (g⁻¹ y) = y := LinearEquiv.apply_symm_apply g y
    rw [e1, e2] at h1
    show g.symm (quasithinZornMul x y) = quasithinZornMul (g.symm x) (g.symm y)
    rw [← h1]
    exact LinearEquiv.symm_apply_apply g _

theorem z6_commutator_le_G2 :
    ⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆ ≤ quasithinG2 (ZMod 2) := by
  refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
  rw [commutatorElement_def]
  exact (quasithinG2 (ZMod 2)).mul_mem
    ((quasithinG2 (ZMod 2)).mul_mem ((quasithinG2 (ZMod 2)).mul_mem ha hb)
      ((quasithinG2 (ZMod 2)).inv_mem ha)) ((quasithinG2 (ZMod 2)).inv_mem hb)

theorem z6_neg_eq (c : ZMod 2) : -c = c := by
  revert c
  decide

theorem z6_aut_one {g : z6O ≃ₗ[ZMod 2] z6O} (hg : z6Aut g) : g z6One = z6One := by
  have hL : ∀ w, quasithinZornMul (g z6One) w = w := by
    intro w
    have h := hg z6One (g.symm w)
    rw [z6_mul_one_left, LinearEquiv.apply_symm_apply] at h
    exact h.symm
  have h1 := hL z6One
  rw [z6_mul_one_right] at h1
  exact h1

theorem z6_sq' (x : z6O) :
    quasithinZornMul x x = z6Tr x • x + z6Nrm x • z6One := by
  rw [z6_sq]
  obtain ⟨a, u, v, b⟩ := x
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · simp [z6One, z6Tr, z6Nrm]
  · funext i
    simp [z6One, z6Tr]
  · funext i
    simp [z6One, z6Tr]
  · simp [z6One, z6Tr, z6Nrm]

theorem z6_bar_eq (w : z6O) : z6Bar w = z6Tr w • z6One - w := by
  obtain ⟨a, u, v, b⟩ := w
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · simp [z6Bar, z6Tr, z6One] <;> ring
  · funext i
    simp [z6Bar, z6Tr, z6One, z6_neg_eq]
  · funext i
    simp [z6Bar, z6Tr, z6One, z6_neg_eq]
  · simp [z6Bar, z6Tr, z6One] <;> ring

theorem z6_smul_one (c : ZMod 2) : c • z6One = (c, 0, 0, c) := by
  simp [z6One]

theorem z6_tr_sub_smul_one (c d : ZMod 2) : z6Tr (c • z6One - d • z6One) = 0 := by
  rw [z6_smul_one, z6_smul_one]
  revert c d
  decide

theorem z6_aut_tr_nrm {g : z6O ≃ₗ[ZMod 2] z6O} (hg : z6Aut g) (x : z6O) :
    z6Tr (g x) = z6Tr x ∧ z6Nrm (g x) = z6Nrm x := by
  have hg1 : g z6One = z6One := z6_aut_one hg
  have hg1' : g.symm z6One = z6One := by
    rw [LinearEquiv.symm_apply_eq]
    exact hg1.symm
  have hx := hg x x
  rw [z6_sq', map_add, map_smul, map_smul, hg1, z6_sq'] at hx
  generalize hy : g x = y at hx ⊢
  rcases z6_zmod2 (z6Tr x) with ht | ht <;> rcases z6_zmod2 (z6Tr y) with ht' | ht'
  ·
    rw [ht, ht'] at hx
    simp only [zero_smul, zero_add] at hx
    rw [z6_smul_one, z6_smul_one, Prod.mk.injEq] at hx
    exact ⟨ht'.trans ht.symm, hx.1.symm⟩
  ·
    exfalso
    rw [ht, ht'] at hx
    simp only [zero_smul, one_smul, zero_add] at hx
    have hy' : y = z6Nrm x • z6One - z6Nrm y • z6One := by
      rw [eq_sub_iff_add_eq]
      exact hx.symm
    rw [hy', z6_tr_sub_smul_one] at ht'
    exact zero_ne_one ht'
  ·
    exfalso
    rw [ht, ht'] at hx
    simp only [zero_smul, one_smul, zero_add] at hx
    have hy' : y = z6Nrm y • z6One - z6Nrm x • z6One := by
      rw [eq_sub_iff_add_eq]
      exact hx
    have hxx : x = z6Nrm y • z6One - z6Nrm x • z6One := by
      calc x = g.symm (g x) := (g.symm_apply_apply x).symm
        _ = g.symm y := by rw [hy]
        _ = g.symm (z6Nrm y • z6One - z6Nrm x • z6One) := by rw [← hy']
        _ = z6Nrm y • z6One - z6Nrm x • z6One := by
          rw [map_sub, map_smul, map_smul, hg1']
          rfl
    rw [hxx, z6_tr_sub_smul_one] at ht
    exact zero_ne_one ht
  ·
    rw [ht, ht'] at hx
    simp only [one_smul] at hx
    have h2 := add_left_cancel hx
    rw [z6_smul_one, z6_smul_one, Prod.mk.injEq] at h2
    exact ⟨ht'.trans ht.symm, h2.1.symm⟩

theorem z6_linear_id (f : z6O →ₗ[ZMod 2] z6O) (h : ∀ i, f (z6E i) = z6E i) : f = LinearMap.id :=
  z6_linear_ext f LinearMap.id h

theorem z6_cU_mul {u : z6O} (h1 : z6Tr u = 1) (h2 : z6Nrm u = 1) (x y : z6O) :
    z6cU u (quasithinZornMul x y) = quasithinZornMul (z6cU u x) (z6cU u y) :=
  z6_mul_check (z6cUL u) (fun i j => z6_F1 u h1 h2 i j) x y

theorem z6_F3_all {u : z6O} (h1 : z6Tr u = 1) (h2 : z6Nrm u = 1) (x : z6O) :
    z6cU (z6Bar u) x = z6cU u (z6cU u x) := by
  have h := z6_linear_ext (z6cUL (z6Bar u)) ((z6cUL u).comp (z6cUL u))
    (fun i => z6_F3 u h1 h2 i)
  exact LinearMap.congr_fun h x

@[expose] def z6cUE {u : z6O} (h1 : z6Tr u = 1) (h2 : z6Nrm u = 1) : z6O ≃ₗ[ZMod 2] z6O :=
  LinearEquiv.ofLinear (z6cUL u) ((z6cUL u).comp (z6cUL u))
    (z6_linear_id _ fun i => z6_F2 u h1 h2 i) (z6_linear_id _ fun i => z6_F2 u h1 h2 i)

theorem z6cUE_apply {u : z6O} (h1 : z6Tr u = 1) (h2 : z6Nrm u = 1) (x : z6O) :
    z6cUE h1 h2 x = z6cU u x :=
  rfl

theorem z6cUE_aut {u : z6O} (h1 : z6Tr u = 1) (h2 : z6Nrm u = 1) : z6Aut (z6cUE h1 h2) :=
  fun x y => z6_cU_mul h1 h2 x y

theorem z6_SL_invol {p : (Fin 3 → Fin 3 → ZMod 2) × (Fin 3 → Fin 3 → ZMod 2)} (hp : p ∈ z6Ms) :
    (z6SL p.1 p.2).comp (z6SL p.1 p.2) = LinearMap.id :=
  z6_linear_id _ fun i => z6_S2 p hp i

@[expose] def z6SE (p : (Fin 3 → Fin 3 → ZMod 2) × (Fin 3 → Fin 3 → ZMod 2)) (hp : p ∈ z6Ms) :
    z6O ≃ₗ[ZMod 2] z6O :=
  LinearEquiv.ofInvolutive (z6SL p.1 p.2) (fun x => LinearMap.congr_fun (z6_SL_invol hp) x)



theorem z6SE_aut (p : (Fin 3 → Fin 3 → ZMod 2) × (Fin 3 → Fin 3 → ZMod 2)) (hp : p ∈ z6Ms) :
    z6Aut (z6SE p hp) :=
  fun x y => z6_mul_check (z6SL p.1 p.2) (fun i j => z6_S1 p hp i j) x y

theorem z6_conj {s : z6O ≃ₗ[ZMod 2] z6O} (hs : z6Aut s) (u y : z6O) :
    s (z6cU u y) = z6cU (s u) (s y) := by
  have hs1 := z6_aut_one hs
  have hst : ∀ x, z6Tr (s x) = z6Tr x := fun x => (z6_aut_tr_nrm hs x).1
  have hbar : s (z6Bar u) = z6Bar (s u) := by
    rw [z6_bar_eq, z6_bar_eq, map_sub, map_smul, hs1, hst]
    rfl
  unfold z6cU
  rw [hs (quasithinZornMul u y) (z6Bar u), hs u y, hbar]

theorem z6_conj_cUE {u : z6O} (h1 : z6Tr u = 1) (h2 : z6Nrm u = 1)
    (s : z6O ≃ₗ[ZMod 2] z6O) (hs : z6Aut s) (hsu : s u = z6Bar u) :
    s * z6cUE h1 h2 * s⁻¹ = z6cUE h1 h2 * z6cUE h1 h2 := by
  refine LinearEquiv.ext fun x => ?_
  show s (z6cU u (s.symm x)) = z6cU u (z6cU u x)
  have h := z6_conj hs u (s.symm x)
  rw [LinearEquiv.apply_symm_apply, hsu] at h
  rw [h, z6_F3_all h1 h2 x]

theorem z6_comm_cUE {u : z6O} (h1 : z6Tr u = 1) (h2 : z6Nrm u = 1)
    (s : z6O ≃ₗ[ZMod 2] z6O) (hs : z6Aut s) (hsu : s u = z6Bar u) :
    ⁅s, z6cUE h1 h2⁆ = z6cUE h1 h2 := by
  rw [commutatorElement_def, z6_conj_cUE h1 h2 s hs hsu, mul_inv_cancel_right]

theorem z6_comm_fix {u : z6O} (h1 : z6Tr u = 1) (h2 : z6Nrm u = 1)
    (g : z6O ≃ₗ[ZMod 2] z6O) (hg : z6Aut g) (hgu : g u = u) :
    g * z6cUE h1 h2 = z6cUE h1 h2 * g := by
  refine LinearEquiv.ext fun x => ?_
  show g (z6cU u x) = z6cU u (g x)
  have h := z6_conj hg u x
  rw [hgu] at h
  exact h

theorem z6cUE_mem_G2 {u : z6O} (h1 : z6Tr u = 1) (h2 : z6Nrm u = 1) :
    z6cUE h1 h2 ∈ quasithinG2 (ZMod 2) :=
  z6_mem_of_aut (z6cUE_aut h1 h2)

theorem z6cUE_mem_comm {u : z6O} (h1 : z6Tr u = 1) (h2 : z6Nrm u = 1)
    {p : (Fin 3 → Fin 3 → ZMod 2) × (Fin 3 → Fin 3 → ZMod 2)} (hp : p ∈ z6Ms)
    (hsu : z6S p.1 p.2 u = z6Bar u) :
    z6cUE h1 h2 ∈ ⁅quasithinG2 (ZMod 2), quasithinG2 (ZMod 2)⁆ := by
  have hs : z6Aut (z6SE p hp) := z6SE_aut p hp
  have hsu' : z6SE p hp u = z6Bar u := hsu
  have h := Subgroup.commutator_mem_commutator (z6_mem_of_aut hs) (z6cUE_mem_G2 h1 h2)
  rwa [z6_comm_cUE h1 h2 (z6SE p hp) hs hsu'] at h

