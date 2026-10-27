module

public import CFSG.LocalAnalysis.StandardType.GGQ2ClassicalNormalizers
import CFSG.Mathlib.Perm.ChainSwap

public section

namespace CFSG.StandardType.GGQ2Frame.PlaneRaw

open CFSG Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

@[expose] def forkTwist (t : ℕ) (e : V t) (i j : Fin t) : V t ≃ₗ[F] V t :=
  negEquiv t i * negEquiv t j * swapTwist t e i j

private theorem pcg_sq_all : ∀ x : ZMod 3, x ≠ 0 → x * x = 1 := by decide

private theorem pcg_sq {x : ZMod 3} (hx : x ≠ 0) : x * x = 1 := pcg_sq_all x hx

private theorem pcg_sq_pow {x : ZMod 3} (hx : x ≠ 0) : x ^ 2 = 1 := by
  rw [pow_two]; exact pcg_sq hx

private theorem pcg_orientCoeff_all : ∀ x : ZMod 3, x ≠ 0 →
    (if x = -1 then (-1 : ZMod 3) else 1) = x := by decide

private theorem pcg_orientCoeff {x : ZMod 3} (hx : x ≠ 0) :
    (if x = -1 then (-1 : ZMod 3) else 1) = x := pcg_orientCoeff_all x hx

private theorem pcg_neg_all : ∀ x y : ZMod 3, x ≠ 0 → y ≠ 0 → x ≠ y → x * y = -1 := by decide

private theorem pcg_neg {x y : ZMod 3} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y) :
    x * y = -1 := pcg_neg_all x y hx hy hxy

private theorem pcg_add_self_all : ∀ x : ZMod 3, x + x = 0 → x = 0 := by decide

theorem negEquiv_apply (t : ℕ) (i : Fin t) (v : V t) (k : Fin t) :
    negEquiv t i v k = if k = i then - v k else v k := by
  simp only [negEquiv, LinearEquiv.piCongrRight_apply]
  by_cases hk : k = i
  · rw [if_pos hk, if_pos hk]
    rfl
  · rw [if_neg hk, if_neg hk]
    rfl

private theorem pcg_orientEquiv_apply (t : ℕ) (e : V t) (v : V t) (k : Fin t) :
    orientEquiv t e v k = (if e k = -1 then (-1 : ZMod 3) else 1) * v k := by
  simp only [orientEquiv, LinearEquiv.piCongrRight_apply]
  split_ifs with hk
  · simp
  · simp

private theorem pcg_orientEquiv_symm_apply (t : ℕ) (e : V t) (w : V t) (k : Fin t) :
    (orientEquiv t e).symm w k = (if e k = -1 then (-1 : ZMod 3) else 1) * w k := by
  have h : orientEquiv t e (fun k => (if e k = -1 then (-1 : ZMod 3) else 1) * w k) = w := by
    ext k
    rw [pcg_orientEquiv_apply]
    split_ifs with hk <;> ring_nf
  have h2 := LinearEquiv.symm_apply_apply (orientEquiv t e)
    (fun k => (if e k = -1 then (-1 : ZMod 3) else 1) * w k)
  rw [h] at h2
  exact congrFun h2 k

theorem swapEquiv_apply (t : ℕ) (i j : Fin t) (v : V t) (k : Fin t) :
    swapEquiv t i j v k = v (Equiv.swap i j k) := by
  simp [swapEquiv, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]

private theorem pcg_funCongrLeft_mul (t : ℕ) (σ τ : Equiv.Perm (Fin t)) :
    LinearEquiv.funCongrLeft F F (σ * τ) =
      LinearEquiv.funCongrLeft F F τ * LinearEquiv.funCongrLeft F F σ := by
  ext v i
  simp [LinearEquiv.mul_apply, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]

theorem swapTwist_apply {t : ℕ} {e : V t} {i j : Fin t} (hi : e i ≠ 0) (hj : e j ≠ 0)
    (v : V t) (k : Fin t) :
    swapTwist t e i j v k =
      if k = i then e i * e j * v j else if k = j then e i * e j * v i else v k := by
  rw [swapTwist, LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.coe_inv]
  rw [pcg_orientEquiv_symm_apply, swapEquiv_apply, pcg_orientEquiv_apply]
  by_cases hki : k = i
  · subst k
    rw [Equiv.swap_apply_left, pcg_orientCoeff hi, pcg_orientCoeff hj, if_pos rfl]
    ring
  · by_cases hkj : k = j
    · subst k
      rw [Equiv.swap_apply_right, pcg_orientCoeff hi, pcg_orientCoeff hj, if_neg hki,
        if_pos rfl]
      ring
    · rw [Equiv.swap_apply_of_ne_of_ne hki hkj, if_neg hki, if_neg hkj]
      by_cases hek : e k = 0
      · rw [hek]
        have h0 : (0 : ZMod 3) ≠ -1 := by decide
        rw [if_neg h0]
        ring
      · rw [pcg_orientCoeff hek, ← mul_assoc, pcg_sq hek, one_mul]

theorem forkTwist_apply {t : ℕ} {e : V t} {i j : Fin t} (hi : e i ≠ 0) (hj : e j ≠ 0)
    (hij : i ≠ j) (v : V t) (k : Fin t) :
    forkTwist t e i j v k =
      if k = i then -(e i * e j * v j) else if k = j then -(e i * e j * v i) else v k := by
  simp only [forkTwist, LinearEquiv.mul_apply, negEquiv_apply, swapTwist_apply hi hj]
  by_cases hki : k = i
  · subst k
    simp [hij]
  · by_cases hkj : k = j
    · subst k
      simp [hki]
    · simp [hki, hkj]

private theorem pcg_swapTwist_eq {t : ℕ} {e : V t} {i j : Fin t} (hi : e i ≠ 0) (hj : e j ≠ 0)
    (hij : i ≠ j) :
    swapTwist t e i j =
      if e i = e j then swapEquiv t i j else negEquiv t i * negEquiv t j * swapEquiv t i j := by
  by_cases h : e i = e j
  · rw [if_pos h]
    ext v r
    simp only [swapTwist_apply hi hj, swapEquiv_apply]
    by_cases hri : r = i
    · subst r
      rw [if_pos rfl, Equiv.swap_apply_left, ← h, pcg_sq hi, one_mul]
    · by_cases hrj : r = j
      · subst r
        rw [if_neg hri, if_pos rfl, Equiv.swap_apply_right, h, pcg_sq hj, one_mul]
      · rw [if_neg hri, if_neg hrj, Equiv.swap_apply_of_ne_of_ne hri hrj]
  · rw [if_neg h]
    ext v r
    simp only [LinearEquiv.mul_apply, negEquiv_apply, swapTwist_apply hi hj,
      swapEquiv_apply]
    by_cases hri : r = i
    · subst r
      simp [hij]
      rw [pcg_neg hi hj h]
      ring
    · by_cases hrj : r = j
      · subst r
        simp [hri]
        rw [pcg_neg hi hj h]
        ring
      · simp [hri, hrj, Equiv.swap_apply_of_ne_of_ne hri hrj]

theorem swapTwist_one (t : ℕ) (i j : Fin t) : swapTwist t 1 i j = swapEquiv t i j := by
  have h : orientEquiv t (1 : V t) = 1 := by
    ext v k
    rw [pcg_orientEquiv_apply]
    have h1 : ¬ ((1 : V t) k = -1) := by
      rw [Pi.one_apply]; decide
    rw [if_neg h1, one_mul]
    rfl
  simp [swapTwist, h]

theorem swapTwist_update_of_ne {t : ℕ} {e : V t} {i j k : Fin t} (hi : e i ≠ 0) (hj : e j ≠ 0)
    (hki : k ≠ i) (hkj : k ≠ j) (x : F) :
    swapTwist t (Function.update e k x) i j = swapTwist t e i j := by
  have hi' : Function.update e k x i ≠ 0 := by
    rw [Function.update_of_ne (Ne.symm hki) x e]; exact hi
  have hj' : Function.update e k x j ≠ 0 := by
    rw [Function.update_of_ne (Ne.symm hkj) x e]; exact hj
  ext v r
  rw [swapTwist_apply hi' hj', swapTwist_apply hi hj]
  by_cases hri : r = i
  · subst r
    simp [Function.update_of_ne (Ne.symm hki) x e, Function.update_of_ne (Ne.symm hkj) x e]
  · by_cases hrj : r = j
    · subst r
      simp [hri, Function.update_of_ne (Ne.symm hki) x e,
        Function.update_of_ne (Ne.symm hkj) x e]
    · simp [hri, hrj]

theorem forkTwist_eq_swapTwist_update {t : ℕ} {e : V t} {i j : Fin t} (hi : e i ≠ 0)
    (hj : e j ≠ 0) (hij : i ≠ j) :
    forkTwist t e i j = swapTwist t (Function.update e j (-e j)) i j := by
  have hi' : Function.update e j (-e j) i ≠ 0 := by
    rw [Function.update_of_ne hij (-e j) e]; exact hi
  have hj' : Function.update e j (-e j) j ≠ 0 := by
    rw [Function.update_apply, if_pos rfl]
    exact neg_ne_zero.mpr hj
  ext v r
  rw [forkTwist_apply hi hj hij, swapTwist_apply hi' hj']
  by_cases hri : r = i
  · subst r
    simp [Function.update_of_ne hij (-e j) e]
  · by_cases hrj : r = j
    · subst r
      simp [hri, Function.update_of_ne hij (-e j) e]
    · simp [hri, hrj]

private theorem pcg_neg_mul_neg_comm (t : ℕ) (i j : Fin t) :
    negEquiv t i * negEquiv t j = negEquiv t j * negEquiv t i := by
  ext v r
  simp only [LinearEquiv.mul_apply, negEquiv_apply]
  by_cases hri : r = i
  · subst r
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
  · by_cases hrj : r = j
    · subst r
      by_cases hij : i = j
      · subst j
        simp
      · simp [Ne.symm hij]
    · simp [hri, hrj]

theorem negEquiv_mul_self (t : ℕ) (i : Fin t) :
    negEquiv t i * negEquiv t i = 1 := by
  ext v r
  simp only [LinearEquiv.mul_apply, negEquiv_apply]
  by_cases hri : r = i <;> simp [*]

private theorem pcg_neg_pairs_mul (t : ℕ) (p q r : Fin t) :
    (negEquiv t p * negEquiv t r) * (negEquiv t q * negEquiv t r) =
      negEquiv t p * negEquiv t q := by
  calc (negEquiv t p * negEquiv t r) * (negEquiv t q * negEquiv t r)
      = negEquiv t p * (negEquiv t r * negEquiv t q) * negEquiv t r := by group
    _ = negEquiv t p * (negEquiv t q * negEquiv t r) * negEquiv t r := by
        rw [pcg_neg_mul_neg_comm]
    _ = negEquiv t p * negEquiv t q * (negEquiv t r * negEquiv t r) := by group
    _ = negEquiv t p * negEquiv t q := by rw [negEquiv_mul_self, mul_one]

private theorem pcg_swapTwist_mul_neg_mul {t : ℕ} {e : V t} {i j : Fin t}
    (hi : e i ≠ 0) (hj : e j ≠ 0) (hij : i ≠ j) :
    swapTwist t e i j * negEquiv t j * swapTwist t e i j = negEquiv t i := by
  ext v r
  simp only [LinearEquiv.mul_apply, negEquiv_apply, swapTwist_apply hi hj]
  by_cases hri : r = i
  · subst r
    simp [Ne.symm hij]
    ring_nf
    rw [pcg_sq_pow hi, pcg_sq_pow hj]
    ring
  · by_cases hrj : r = j
    · subst r
      simp [hij, hri]
      ring_nf
      rw [pcg_sq_pow hi, pcg_sq_pow hj]
      ring
    · simp [hri, hrj]

private theorem pcg_swapTwist_comm_neg {t : ℕ} {e : V t} {i j k : Fin t}
    (hi : e i ≠ 0) (hj : e j ≠ 0) (_hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) :
    swapTwist t e i j * negEquiv t k = negEquiv t k * swapTwist t e i j := by
  ext v r
  simp only [LinearEquiv.mul_apply, negEquiv_apply, swapTwist_apply hi hj]
  by_cases hri : r = i
  · subst r
    simp [Ne.symm hki, Ne.symm hkj]
  · by_cases hrj : r = j
    · subst r
      simp [Ne.symm hki, Ne.symm hkj]
    · by_cases hrk : r = k
      · subst r
        simp [hri, hrj]
      · simp [hri, hrj, hrk]

private theorem pcg_swapTwist_mul_neg_mul_neg {t : ℕ} {e : V t} {i j k : Fin t}
    (hi : e i ≠ 0) (hj : e j ≠ 0) (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) :
    swapTwist t e i j * (negEquiv t j * negEquiv t k) * swapTwist t e i j =
      negEquiv t i * negEquiv t k := by
  have hcomm := pcg_swapTwist_comm_neg (e := e) hi hj hij hki hkj
  have hsingle := pcg_swapTwist_mul_neg_mul (e := e) hi hj hij
  calc swapTwist t e i j * (negEquiv t j * negEquiv t k) * swapTwist t e i j
      = swapTwist t e i j * negEquiv t j * (swapTwist t e i j * negEquiv t k) := by
        rw [hcomm]; group
    _ = (swapTwist t e i j * negEquiv t j * swapTwist t e i j) * negEquiv t k := by group
    _ = negEquiv t i * negEquiv t k := by rw [hsingle]

theorem swapEquiv_self (t : ℕ) (i : Fin t) : swapEquiv t i i = 1 := by
  ext v k
  rw [swapEquiv_apply]
  simp

private def pcg_permHom (t : ℕ) (e : V t) : Equiv.Perm (Fin t) →* (V t ≃ₗ[F] V t) where
  toFun σ := (orientEquiv t e)⁻¹ * LinearEquiv.funCongrLeft F F σ⁻¹ * orientEquiv t e
  map_one' := by
    rw [inv_one]
    show (orientEquiv t e)⁻¹ * LinearEquiv.funCongrLeft F F (1 : Equiv.Perm (Fin t)) *
      orientEquiv t e = 1
    rw [show (1 : Equiv.Perm (Fin t)) = Equiv.refl (Fin t) from rfl,
      LinearEquiv.funCongrLeft_id]
    rw [show LinearEquiv.refl F (Fin t → F) = 1 from rfl, mul_one, inv_mul_cancel]
  map_mul' σ τ := by
    rw [show (σ * τ)⁻¹ = τ⁻¹ * σ⁻¹ from mul_inv_rev σ τ]
    rw [pcg_funCongrLeft_mul]
    group

private theorem pcg_permHom_swap (t : ℕ) (e : V t) (i j : Fin t) :
    pcg_permHom t e (Equiv.swap i j) = swapTwist t e i j := by
  simp [pcg_permHom, swapTwist, swapEquiv, Equiv.swap_inv]

private theorem pcg_castSucc_ne_succ {n : ℕ} (i : Fin n) : i.castSucc ≠ i.succ := by
  intro h
  have h' := congrArg Fin.val h
  simp only [Fin.val_castSucc, Fin.val_succ] at h'
  omega

private theorem pcg_chain_const {m : ℕ} {α : Type*} {d : Fin (m + 1) → α} {w : α → F}
    (h : ∀ κ : Fin m, w (d κ.castSucc) = w (d κ.succ)) (p q : Fin (m + 1)) :
    w (d p) = w (d q) := by
  have key : ∀ (a n : ℕ) (ha : a < m + 1) (han : a + n < m + 1),
      w (d ⟨a, ha⟩) = w (d ⟨a + n, han⟩) := by
    intro a n
    induction n with
    | zero =>
      intro ha han
      rw [show (⟨a, ha⟩ : Fin (m + 1)) = ⟨a + 0, han⟩ from Fin.ext (by simp)]
    | succ n ih =>
      intro ha han
      have hstep : w (d ⟨a + n, by omega⟩) = w (d ⟨a + n + 1, han⟩) := by
        have := h ⟨a + n, by omega⟩
        simpa using this
      rw [ih ha (by omega), hstep]
      rw [show (⟨a + n + 1, han⟩ : Fin (m + 1)) = ⟨a + (n + 1), han⟩ from
        Fin.ext (by simp; omega)]
  rcases le_total (p : ℕ) (q : ℕ) with hpq | hpq
  · have hq : (⟨(p : ℕ) + ((q : ℕ) - (p : ℕ)), by omega⟩ : Fin (m + 1)) = q :=
      Fin.ext (by simp; omega)
    have := key (p : ℕ) ((q : ℕ) - (p : ℕ)) p.isLt (by omega)
    rwa [hq] at this
  · have hp : (⟨(q : ℕ) + ((p : ℕ) - (q : ℕ)), by omega⟩ : Fin (m + 1)) = p :=
      Fin.ext (by simp; omega)
    have := key (q : ℕ) ((p : ℕ) - (q : ℕ)) q.isLt (by omega)
    rw [hp] at this
    exact this.symm

theorem closure_chainTwist {t m : ℕ} {e : V t} (he : ∀ i, e i ≠ 0) (d : Fin (m + 1) ≃ Fin t) :
    Subgroup.closure (Set.range fun κ : Fin m => swapTwist t e (d κ.castSucc) (d κ.succ)) =
      twistedPermGroupOn t e := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨κ, rfl⟩
    exact Subgroup.subset_closure ⟨d κ.castSucc, d κ.succ, he _, he _, rfl⟩
  · rw [twistedPermGroupOn, Subgroup.closure_le]
    rintro _ ⟨i, j, hi, hj, rfl⟩
    have hmem := CFSG.Perm.map_swap_mem_closure_chainSwap (pcg_permHom t e) d.injective
      (d.symm i) (d.symm j)
    simp only [Equiv.apply_symm_apply] at hmem
    simpa [pcg_permHom_swap] using hmem

theorem closure_chainTwist_neg {t m : ℕ} {e : V t} (c : Fin (m + 1) → Fin t)
    (hc : Function.Injective c) (he : ∀ κ, e (c κ) ≠ 0) :
    Subgroup.closure (Set.range (fun κ : Fin m => swapTwist t e (c κ.castSucc) (c κ.succ)) ∪
      {negEquiv t (c (Fin.last m))}) = signedPermGroupOn t (Finset.univ.image c) := by
  have hS : ∀ a : Fin (m + 1), c a ∈ Finset.univ.image c := fun a =>
    Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
  have hswap (κ : Fin m) :
      swapTwist t e (c κ.castSucc) (c κ.succ) ∈ signedPermGroupOn t (Finset.univ.image c) := by
    have hij : c κ.castSucc ≠ c κ.succ := hc.ne (pcg_castSucc_ne_succ κ)
    have heq := pcg_swapTwist_eq (e := e) (he κ.castSucc) (he κ.succ) hij
    by_cases h : e (c κ.castSucc) = e (c κ.succ)
    · rw [if_pos h] at heq
      rw [heq]
      exact Subgroup.subset_closure (Or.inl ⟨_, hS _, _, hS _, rfl⟩)
    · rw [if_neg h] at heq
      rw [heq]
      exact Subgroup.mul_mem _
        (Subgroup.mul_mem _
          (Subgroup.subset_closure (Or.inr ⟨_, hS _, rfl⟩))
          (Subgroup.subset_closure (Or.inr ⟨_, hS _, rfl⟩)))
        (Subgroup.subset_closure (Or.inl ⟨_, hS _, _, hS _, rfl⟩))
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x (⟨κ, rfl⟩ | hx)
    · exact hswap κ
    · have hx' : x = negEquiv t (c (Fin.last m)) := by simpa using hx
      rw [hx']
      exact Subgroup.subset_closure (Or.inr ⟨_, hS _, rfl⟩)
  · rw [signedPermGroupOn, Subgroup.closure_le]
    have hneg : ∀ κ : Fin (m + 1), negEquiv t (c κ) ∈
        Subgroup.closure (Set.range (fun κ : Fin m =>
          swapTwist t e (c κ.castSucc) (c κ.succ)) ∪ {negEquiv t (c (Fin.last m))}) := by
      intro κ
      induction κ using Fin.reverseInduction with
      | last => exact Subgroup.subset_closure (Or.inr rfl)
      | cast κ ih =>
        have hT : swapTwist t e (c κ.castSucc) (c κ.succ) ∈
            Subgroup.closure (Set.range (fun κ : Fin m =>
              swapTwist t e (c κ.castSucc) (c κ.succ)) ∪
                {negEquiv t (c (Fin.last m))}) :=
          Subgroup.subset_closure (Or.inl ⟨κ, rfl⟩)
        have hconj := pcg_swapTwist_mul_neg_mul (e := e) (he κ.castSucc) (he κ.succ)
          (hc.ne (pcg_castSucc_ne_succ κ))
        rw [← hconj]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hT ih) hT
    rintro _ (⟨i, hiS, j, hjS, rfl⟩ | ⟨i, hiS, rfl⟩)
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hiS
      obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hjS
      by_cases hab : a = b
      · subst b
        rw [swapEquiv_self]
        exact Subgroup.one_mem _
      · have hT : swapTwist t e (c a) (c b) ∈
            Subgroup.closure (Set.range (fun κ : Fin m =>
              swapTwist t e (c κ.castSucc) (c κ.succ)) ∪
                {negEquiv t (c (Fin.last m))}) := by
          have h := CFSG.Perm.map_swap_mem_closure_chainSwap (pcg_permHom t e) hc a b
          have h' : swapTwist t e (c a) (c b) ∈ Subgroup.closure
              (Set.range fun κ : Fin m => swapTwist t e (c κ.castSucc) (c κ.succ)) := by
            simpa [pcg_permHom_swap] using h
          exact Subgroup.closure_mono (Set.subset_union_left) h'
        have heq := pcg_swapTwist_eq (e := e) (he a) (he b) (hc.ne hab)
        by_cases h : e (c a) = e (c b)
        · rw [if_pos h] at heq
          rw [← heq]
          exact hT
        · rw [if_neg h] at heq
          have hS' : swapEquiv t (c a) (c b) =
              (negEquiv t (c a) * negEquiv t (c b))⁻¹ * swapTwist t e (c a) (c b) := by
            rw [heq]; group
          rw [hS']
          exact Subgroup.mul_mem _
            (Subgroup.inv_mem _ (Subgroup.mul_mem _ (hneg a) (hneg b))) hT
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hiS
      exact hneg a

theorem closure_chainTwist_fork {t m : ℕ} {e : V t} (c : Fin (m + 2) → Fin t)
    (hc : Function.Injective c) (he : ∀ κ, e (c κ) ≠ 0) :
    Subgroup.closure (Set.range (fun κ : Fin (m + 1) => swapTwist t e (c κ.castSucc) (c κ.succ)) ∪
      {forkTwist t e (c (Fin.last m).castSucc) (c (Fin.last (m + 1)))}) =
      evenSignedPermGroupOn t (Finset.univ.image c) := by
  let iprev : Fin (m + 2) := (Fin.last m).castSucc
  let ilast : Fin (m + 2) := Fin.last (m + 1)
  have hS : ∀ a : Fin (m + 2), c a ∈ Finset.univ.image c := fun a =>
    Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
  have hprevne : iprev ≠ ilast := by
    simp [iprev, ilast]
  have hsucc : (Fin.last m).succ = ilast := by
    apply Fin.ext
    simp [ilast, Fin.val_last]
  have hT (κ : Fin (m + 1)) : swapTwist t e (c κ.castSucc) (c κ.succ) ∈
      Subgroup.closure (Set.range (fun κ : Fin (m + 1) =>
        swapTwist t e (c κ.castSucc) (c κ.succ)) ∪
          {forkTwist t e (c (Fin.last m).castSucc) (c (Fin.last (m + 1)))}) :=
    Subgroup.subset_closure (Or.inl ⟨κ, rfl⟩)
  have hfork : forkTwist t e (c (Fin.last m).castSucc) (c (Fin.last (m + 1))) ∈
      Subgroup.closure (Set.range (fun κ : Fin (m + 1) =>
        swapTwist t e (c κ.castSucc) (c κ.succ)) ∪
          {forkTwist t e (c (Fin.last m).castSucc) (c (Fin.last (m + 1)))}) :=
    Subgroup.subset_closure (Or.inr rfl)
  have hswap (κ : Fin (m + 1)) :
      swapTwist t e (c κ.castSucc) (c κ.succ) ∈ evenSignedPermGroupOn t (Finset.univ.image c) := by
    have hij : c κ.castSucc ≠ c κ.succ := hc.ne (pcg_castSucc_ne_succ κ)
    have heq := pcg_swapTwist_eq (e := e) (he κ.castSucc) (he κ.succ) hij
    by_cases h : e (c κ.castSucc) = e (c κ.succ)
    · rw [if_pos h] at heq
      rw [heq]
      exact Subgroup.subset_closure (Or.inl ⟨_, hS _, _, hS _, rfl⟩)
    · rw [if_neg h] at heq
      rw [heq]
      exact Subgroup.mul_mem _
        (Subgroup.subset_closure (Or.inr ⟨_, hS _, _, hS _, hij, rfl⟩))
        (Subgroup.subset_closure (Or.inl ⟨_, hS _, _, hS _, rfl⟩))
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x (⟨κ, rfl⟩ | hx)
    · dsimp only
      exact hswap κ
    · have hx' : x = forkTwist t e (c (Fin.last m).castSucc) (c (Fin.last (m + 1))) := by
        simpa using hx
      rw [hx']
      have hgen : negEquiv t (c iprev) * negEquiv t (c ilast) ∈
          evenSignedPermGroupOn t (Finset.univ.image c) :=
        Subgroup.subset_closure (Or.inr ⟨c iprev, hS iprev, c ilast, hS ilast,
          hc.ne hprevne, rfl⟩)
      have hlast : swapTwist t e (c iprev) (c ilast) ∈
          evenSignedPermGroupOn t (Finset.univ.image c) := by
        simpa [iprev, hsucc] using hswap (Fin.last m)
      have hfac : forkTwist t e (c (Fin.last m).castSucc) (c (Fin.last (m + 1))) =
          negEquiv t (c iprev) * negEquiv t (c ilast) * swapTwist t e (c iprev) (c ilast) := by
        simp only [forkTwist, iprev, ilast]
      rw [hfac]
      exact Subgroup.mul_mem _ hgen hlast
  · rw [evenSignedPermGroupOn, Subgroup.closure_le]
    have hNmem : negEquiv t (c iprev) * negEquiv t (c ilast) ∈
        Subgroup.closure (Set.range (fun κ : Fin (m + 1) =>
          swapTwist t e (c κ.castSucc) (c κ.succ)) ∪
            {forkTwist t e (c (Fin.last m).castSucc) (c (Fin.last (m + 1)))}) := by
      have hN : negEquiv t (c iprev) * negEquiv t (c ilast) =
          forkTwist t e (c iprev) (c ilast) * (swapTwist t e (c iprev) (c ilast))⁻¹ := by
        simp only [forkTwist]; group
      rw [hN]
      have hTlast : swapTwist t e (c iprev) (c ilast) ∈
          Subgroup.closure (Set.range (fun κ : Fin (m + 1) =>
            swapTwist t e (c κ.castSucc) (c κ.succ)) ∪
              {forkTwist t e (c (Fin.last m).castSucc) (c (Fin.last (m + 1)))}) := by
        simpa [iprev, hsucc] using hT (Fin.last m)
      exact Subgroup.mul_mem _ hfork (Subgroup.inv_mem _ hTlast)
    have hpair_last : ∀ a : Fin (m + 2), a ≠ ilast →
        negEquiv t (c a) * negEquiv t (c ilast) ∈
          Subgroup.closure (Set.range (fun κ : Fin (m + 1) =>
            swapTwist t e (c κ.castSucc) (c κ.succ)) ∪
              {forkTwist t e (c (Fin.last m).castSucc) (c (Fin.last (m + 1)))}) := by
      intro a ha
      by_cases haprev : a = iprev
      · rw [haprev]; exact hNmem
      · have hT' : swapTwist t e (c a) (c iprev) ∈
            Subgroup.closure (Set.range (fun κ : Fin (m + 1) =>
              swapTwist t e (c κ.castSucc) (c κ.succ)) ∪
                {forkTwist t e (c (Fin.last m).castSucc) (c (Fin.last (m + 1)))}) := by
          have h := CFSG.Perm.map_swap_mem_closure_chainSwap (pcg_permHom t e) hc a iprev
          have h' : swapTwist t e (c a) (c iprev) ∈ Subgroup.closure
              (Set.range fun κ : Fin (m + 1) =>
                swapTwist t e (c κ.castSucc) (c κ.succ)) := by
            simpa [pcg_permHom_swap] using h
          exact Subgroup.closure_mono (Set.subset_union_left) h'
        have hconj := pcg_swapTwist_mul_neg_mul_neg (e := e) (i := c a) (j := c iprev)
          (k := c ilast) (he a) (he iprev) (hc.ne haprev) (hc.ne (Ne.symm ha))
          (hc.ne hprevne.symm)
        rw [← hconj]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hT' hNmem) hT'
    have hpair : ∀ a b : Fin (m + 2), a ≠ b →
        negEquiv t (c a) * negEquiv t (c b) ∈
          Subgroup.closure (Set.range (fun κ : Fin (m + 1) =>
            swapTwist t e (c κ.castSucc) (c κ.succ)) ∪
              {forkTwist t e (c (Fin.last m).castSucc) (c (Fin.last (m + 1)))}) := by
      intro a b hab
      by_cases hb : b = ilast
      · subst b; exact hpair_last a hab
      · by_cases ha : a = ilast
        · subst a
          rw [pcg_neg_mul_neg_comm]
          exact hpair_last b hb
        · rw [← pcg_neg_pairs_mul (p := c a) (q := c b) (r := c ilast)]
          exact Subgroup.mul_mem _ (hpair_last a ha) (hpair_last b hb)
    rintro _ (⟨i, hiS, j, hjS, rfl⟩ | ⟨i, hiS, j, hjS, hij, rfl⟩)
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hiS
      obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hjS
      by_cases hab : a = b
      · subst b
        rw [swapEquiv_self]
        exact Subgroup.one_mem _
      · have hTab : swapTwist t e (c a) (c b) ∈
            Subgroup.closure (Set.range (fun κ : Fin (m + 1) =>
              swapTwist t e (c κ.castSucc) (c κ.succ)) ∪
                {forkTwist t e (c (Fin.last m).castSucc) (c (Fin.last (m + 1)))}) := by
          have h := CFSG.Perm.map_swap_mem_closure_chainSwap (pcg_permHom t e) hc a b
          have h' : swapTwist t e (c a) (c b) ∈ Subgroup.closure
              (Set.range fun κ : Fin (m + 1) =>
                swapTwist t e (c κ.castSucc) (c κ.succ)) := by
            simpa [pcg_permHom_swap] using h
          exact Subgroup.closure_mono (Set.subset_union_left) h'
        have heq := pcg_swapTwist_eq (e := e) (he a) (he b) (hc.ne hab)
        by_cases h : e (c a) = e (c b)
        · rw [if_pos h] at heq
          rw [← heq]
          exact hTab
        · rw [if_neg h] at heq
          have hS' : swapEquiv t (c a) (c b) =
              (negEquiv t (c a) * negEquiv t (c b))⁻¹ * swapTwist t e (c a) (c b) := by
            rw [heq]; group
          rw [hS']
          exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hpair a b hab)) hTab
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hiS
      obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hjS
      exact hpair a b (fun h => hij (by rw [h]))

theorem chain_kernel_twisted {t m : ℕ} {e : V t} (he : ∀ i, e i ≠ 0) (d : Fin (m + 1) ≃ Fin t)
    (v : V t) :
    (∀ κ : Fin m, e (d κ.castSucc) * v (d κ.castSucc) = e (d κ.succ) * v (d κ.succ)) ↔
      v ∈ Submodule.span F {e} := by
  constructor
  · intro h
    have hconst : ∀ p q : Fin (m + 1),
        e (d p) * v (d p) = e (d q) * v (d q) :=
      pcg_chain_const (d := d) (w := fun i => e i * v i) h
    refine Submodule.mem_span_singleton.mpr ⟨e (d 0) * v (d 0), ?_⟩
    ext i
    have hi := hconst (d.symm i) 0
    rw [Equiv.apply_symm_apply] at hi
    simp only [Pi.smul_apply, smul_eq_mul]
    calc (e (d 0) * v (d 0)) * e i = e i * (e (d 0) * v (d 0)) := by ring
      _ = e i * (e i * v i) := by rw [hi]
      _ = (e i * e i) * v i := by ring
      _ = v i := by rw [pcg_sq (he i), one_mul]
  · intro hv
    rw [Submodule.mem_span_singleton] at hv
    obtain ⟨s, rfl⟩ := hv
    intro κ
    simp only [Pi.smul_apply, smul_eq_mul]
    have ha := pcg_sq (he (d κ.castSucc))
    have hb := pcg_sq (he (d κ.succ))
    calc e (d κ.castSucc) * (s * e (d κ.castSucc))
        = s * (e (d κ.castSucc) * e (d κ.castSucc)) := by ring
      _ = s := by rw [ha, mul_one]
      _ = s * (e (d κ.succ) * e (d κ.succ)) := by rw [hb, mul_one]
      _ = e (d κ.succ) * (s * e (d κ.succ)) := by ring

theorem chain_kernel_neg {t m : ℕ} {e : V t} (c : Fin (m + 1) → Fin t) (he : ∀ κ, e (c κ) ≠ 0)
    (v : V t) :
    ((∀ κ : Fin m, e (c κ.castSucc) * v (c κ.castSucc) = e (c κ.succ) * v (c κ.succ)) ∧
        e (c (Fin.last m)) * v (c (Fin.last m)) = 0) ↔ ∀ κ, v (c κ) = 0 := by
  constructor
  · rintro ⟨h, hlast⟩ κ
    have hconst : ∀ p q : Fin (m + 1),
        e (c p) * v (c p) = e (c q) * v (c q) :=
      pcg_chain_const (d := c) (w := fun i => e i * v i) h
    have hw : e (c κ) * v (c κ) = 0 := by
      rw [hconst κ (Fin.last m), hlast]
    exact (mul_eq_zero.mp hw).resolve_left (he κ)
  · intro h
    refine ⟨?_, ?_⟩
    · intro κ
      simp [h κ.castSucc, h κ.succ]
    · simp [h (Fin.last m)]

theorem chain_kernel_fork {t m : ℕ} {e : V t} (c : Fin (m + 2) → Fin t) (he : ∀ κ, e (c κ) ≠ 0)
    (v : V t) :
    ((∀ κ : Fin (m + 1), e (c κ.castSucc) * v (c κ.castSucc) = e (c κ.succ) * v (c κ.succ)) ∧
        e (c (Fin.last m).castSucc) * v (c (Fin.last m).castSucc) +
          e (c (Fin.last (m + 1))) * v (c (Fin.last (m + 1))) = 0) ↔ ∀ κ, v (c κ) = 0 := by
  constructor
  · rintro ⟨h, hsum⟩ κ
    have hconst : ∀ p q : Fin (m + 2),
        e (c p) * v (c p) = e (c q) * v (c q) :=
      pcg_chain_const (d := c) (w := fun i => e i * v i) h
    have hab : e (c (Fin.last m).castSucc) * v (c (Fin.last m).castSucc) =
        e (c (Fin.last (m + 1))) * v (c (Fin.last (m + 1))) := hconst _ _
    have haa : e (c (Fin.last m).castSucc) * v (c (Fin.last m).castSucc) +
        e (c (Fin.last m).castSucc) * v (c (Fin.last m).castSucc) = 0 := by
      rw [← hab] at hsum
      exact hsum
    have ha0 : e (c (Fin.last m).castSucc) * v (c (Fin.last m).castSucc) = 0 :=
      pcg_add_self_all _ haa
    have hw : e (c κ) * v (c κ) = 0 := by
      rw [hconst κ (Fin.last m).castSucc, ha0]
    exact (mul_eq_zero.mp hw).resolve_left (he κ)
  · intro h
    refine ⟨?_, ?_⟩
    · intro κ
      simp [h κ.castSucc, h κ.succ]
    · rw [h (Fin.last m).castSucc, h (Fin.last (m + 1)), mul_zero, mul_zero, add_zero]

end

end CFSG.StandardType.GGQ2Frame.PlaneRaw

end
