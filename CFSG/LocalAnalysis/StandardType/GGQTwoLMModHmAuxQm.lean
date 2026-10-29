module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMModHmAux

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord CFSG.StandardType.SpCoord
open Multiplicative
open Subgroup

theorem qTwoLMH_mem_zpowers_perm {m : ℕ} (w : Fin m → Multiplicative (ZMod 3)) :
    w ∈ Subgroup.zpowers (fun _ : Fin m => ofAdd (1 : ZMod 3)) ↔ ∀ i j, w i = w j := by
  constructor
  · intro hw
    rw [mem_zpowers_iff_mem_range_orderOf] at hw
    obtain ⟨n, -, hn⟩ := Finset.mem_image.mp hw
    rw [← hn]
    intro i j
    simp only [Pi.pow_apply, qTwoLMH_ofAdd_one_pow]
  · intro hw
    by_cases hm : m = 0
    · subst hm
      have : Subsingleton (Fin 0 → Multiplicative (ZMod 3)) := inferInstance
      rw [Subsingleton.elim w 1]
      exact Subgroup.one_mem _
    · have hm' : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
      have h0 : w = (fun _ : Fin m => ofAdd (1 : ZMod 3)) ^ (toAdd (w ⟨0, hm'⟩)).val := by
        funext i
        rw [Pi.pow_apply, qTwoLMH_ofAdd_one_pow, ZMod.natCast_zmod_val]
        rw [hw i ⟨0, hm'⟩, ofAdd_toAdd]
      rw [h0]
      exact Subgroup.mem_zpowers_iff.mpr
        ⟨((toAdd (w ⟨0, hm'⟩)).val : ℤ), by rw [zpow_natCast]⟩

theorem qTwoLMH_card_zpowers_perm {m : ℕ} (hm : 1 ≤ m) :
    Nat.card (Subgroup.zpowers (fun _ : Fin m => ofAdd (1 : ZMod 3))) = 3 := by
  rw [Nat.card_zpowers]
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  apply orderOf_eq_prime
  · funext i
    rw [Pi.pow_apply, qTwoLMH_ofAdd_one_pow, ZMod.natCast_self, Pi.one_apply]
    rfl
  · intro h
    have hc := congrFun h ⟨0, hm⟩
    have h2 := congrArg toAdd hc
    simp only [Pi.one_apply, toAdd_ofAdd, toAdd_one] at h2
    exact one_ne_zero h2

theorem qTwoLMH_card_of_qmodel {m : ℕ} {V : Type} [Group V]
    {ρ : Equiv.Perm (Fin m) →* MulAut V} (h : IsQmModel m V ρ) :
    Nat.card V = 3 ^ (m - 1) := by
  obtain ⟨π, hsurj, hker, -⟩ := h.ex
  by_cases hm : m = 0
  · subst hm
    haveI : Subsingleton V := ⟨fun a b => by
      obtain ⟨x, rfl⟩ := hsurj a
      obtain ⟨y, rfl⟩ := hsurj b
      rw [Subsingleton.elim x y]⟩
    rw [Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩]
    norm_num
  · have hm' : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    have hcardV : Nat.card V * 3 = Nat.card (Fin m → Multiplicative (ZMod 3)) := by
      have h := qTwoLMH_card_of_surjective_ker (fun _ : Fin m => ofAdd (1 : ZMod 3)) π hsurj hker
      rwa [qTwoLMH_card_zpowers_perm hm'] at h
    have hpow : 3 ^ m = 3 ^ (m - 1) * 3 := by
      rw [← pow_succ]
      congr 1
      omega
    have hEq : Nat.card V * 3 = 3 ^ (m - 1) * 3 := by
      rw [hcardV, qTwoLMH_card_perm m, hpow]
    exact Nat.mul_right_cancel (by norm_num : 0 < 3) hEq

theorem qTwoLMH_fixed_qmodel {m : ℕ} {V : Type} [Group V]
    {ρ : Equiv.Perm (Fin m) →* MulAut V} (h : IsQmModel m V ρ) (h3 : 3 ∣ m) (hm : 5 ≤ m) :
    ∀ v : V, (∀ σ, ρ σ v = v) → v = 1 := by
  obtain ⟨π, hsurj, hker, heq⟩ := h.ex
  intro v hv
  obtain ⟨w, rfl⟩ := hsurj v
  rw [hker w, qTwoLMH_mem_zpowers_perm w]
  intro i j
  by_cases hij : i = j
  · rw [hij]
  · have hx : (fun k => w ((Equiv.swap i j)⁻¹ k)) * w⁻¹ ∈
        Subgroup.zpowers (fun _ : Fin m => ofAdd (1 : ZMod 3)) := by
      have h1 : π (fun k => w ((Equiv.swap i j)⁻¹ k)) = ρ (Equiv.swap i j) (π w) :=
        heq (Equiv.swap i j) w
      rw [← hker, map_mul, h1, hv (Equiv.swap i j), ← map_mul,
        show w * w⁻¹ = 1 from mul_inv_cancel w, map_one]
    have hconst := (qTwoLMH_mem_zpowers_perm _).mp hx
    have h1 : toAdd (((fun k => w ((Equiv.swap i j)⁻¹ k)) * w⁻¹) i) =
        toAdd (w j) - toAdd (w i) := by
      rw [Pi.mul_apply, Pi.inv_apply, Equiv.swap_inv, Equiv.swap_apply_left, toAdd_mul,
        toAdd_inv]
      exact (sub_eq_add_neg (toAdd (w j)) (toAdd (w i))).symm
    have h2 : toAdd (((fun k => w ((Equiv.swap i j)⁻¹ k)) * w⁻¹) j) =
        toAdd (w i) - toAdd (w j) := by
      rw [Pi.mul_apply, Pi.inv_apply, Equiv.swap_inv, Equiv.swap_apply_right, toAdd_mul,
        toAdd_inv]
      exact (sub_eq_add_neg (toAdd (w i)) (toAdd (w j))).symm
    have h3 : toAdd (w j) - toAdd (w i) = -(toAdd (w j) - toAdd (w i)) := by
      calc toAdd (w j) - toAdd (w i)
          = toAdd (((fun k => w ((Equiv.swap i j)⁻¹ k)) * w⁻¹) i) := h1.symm
        _ = toAdd (((fun k => w ((Equiv.swap i j)⁻¹ k)) * w⁻¹) j) := hconst i j
        _ = toAdd (w i) - toAdd (w j) := h2
        _ = -(toAdd (w j) - toAdd (w i)) :=
          (neg_sub (toAdd (w j)) (toAdd (w i))).symm
    have h4 : toAdd (w j) - toAdd (w i) = 0 :=
      coord_eq_zero_of_eq_neg (p := 3) (by norm_num) (by norm_num) h3
    exact (toAdd.injective (sub_eq_zero.mp h4)).symm

theorem qTwoLMH_faithful_qmodel {m : ℕ} {V : Type} [Group V]
    {ρ : Equiv.Perm (Fin m) →* MulAut V} (h : IsQmModel m V ρ) (hm : 5 ≤ m) :
    ∀ σ, (∀ v, ρ σ v = v) → σ = 1 := by
  obtain ⟨π, hsurj, hker, heq⟩ := h.ex
  intro σ hσ
  by_contra hne
  obtain ⟨a, ha⟩ : ∃ a, σ a ≠ a := by
    by_contra hcon
    push Not at hcon
    exact hne (Equiv.ext hcon)
  obtain ⟨c, hca, hcσa, hcσia⟩ := qTwoLMH_exists_ne_three (by omega : 4 ≤ m) a (σ a) (σ⁻¹ a)
  have hσia : σ⁻¹ a ≠ a := by
    intro hcon
    exact ha (by
      calc σ a = σ (σ⁻¹ a) := by rw [hcon]
        _ = a := Equiv.apply_symm_apply σ a)
  let w : Fin m → Multiplicative (ZMod 3) :=
    Pi.mulSingle (M := fun _ : Fin m => Multiplicative (ZMod 3)) a (ofAdd (1 : ZMod 3)) *
      Pi.mulSingle (M := fun _ : Fin m => Multiplicative (ZMod 3)) c (ofAdd (-1 : ZMod 3))
  have hwa : toAdd (w a) = 1 := by
    show toAdd (Pi.mulSingle (M := fun _ : Fin m => Multiplicative (ZMod 3)) a
        (ofAdd (1 : ZMod 3)) a *
      Pi.mulSingle (M := fun _ : Fin m => Multiplicative (ZMod 3)) c
        (ofAdd (-1 : ZMod 3)) a) = 1
    rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (Ne.symm hca), toAdd_mul, toAdd_ofAdd]
    simp
  have hwc : toAdd (w c) = -1 := by
    show toAdd (Pi.mulSingle (M := fun _ : Fin m => Multiplicative (ZMod 3)) a
        (ofAdd (1 : ZMod 3)) c *
      Pi.mulSingle (M := fun _ : Fin m => Multiplicative (ZMod 3)) c
        (ofAdd (-1 : ZMod 3)) c) = -1
    rw [Pi.mulSingle_eq_of_ne hca, Pi.mulSingle_eq_same, toAdd_mul, toAdd_ofAdd]
    simp
  have hwσa : toAdd (w (σ a)) = 0 := by
    show toAdd (Pi.mulSingle (M := fun _ : Fin m => Multiplicative (ZMod 3)) a
        (ofAdd (1 : ZMod 3)) (σ a) *
      Pi.mulSingle (M := fun _ : Fin m => Multiplicative (ZMod 3)) c
        (ofAdd (-1 : ZMod 3)) (σ a)) = 0
    rw [Pi.mulSingle_eq_of_ne ha, Pi.mulSingle_eq_of_ne hcσa.symm]
    simp
  have hwσia : toAdd (w (σ⁻¹ a)) = 0 := by
    show toAdd (Pi.mulSingle (M := fun _ : Fin m => Multiplicative (ZMod 3)) a
        (ofAdd (1 : ZMod 3)) (σ⁻¹ a) *
      Pi.mulSingle (M := fun _ : Fin m => Multiplicative (ZMod 3)) c
        (ofAdd (-1 : ZMod 3)) (σ⁻¹ a)) = 0
    rw [Pi.mulSingle_eq_of_ne hσia, Pi.mulSingle_eq_of_ne hcσia.symm]
    simp
  have hσa : (σ⁻¹ : Equiv.Perm (Fin m)) (σ a) = a := σ.symm_apply_apply a
  have hx : (fun i => w (σ⁻¹ i)) * w⁻¹ ∈
      Subgroup.zpowers (fun _ : Fin m => ofAdd (1 : ZMod 3)) := by
    rw [← hker, map_mul, heq σ w, hσ (π w), ← map_mul,
      show w * w⁻¹ = 1 from mul_inv_cancel w, map_one]
  have hconst := (qTwoLMH_mem_zpowers_perm _).mp hx
  have h1 : toAdd (((fun i => w (σ⁻¹ i)) * w⁻¹) (σ a)) = 1 := by
    rw [Pi.mul_apply, Pi.inv_apply, hσa, toAdd_mul, toAdd_inv, hwa, hwσa]
    decide
  have h2 : toAdd (((fun i => w (σ⁻¹ i)) * w⁻¹) a) = -1 := by
    rw [Pi.mul_apply, Pi.inv_apply, toAdd_mul, toAdd_inv, hwσia, hwa]
    decide
  have h3 := congrArg toAdd (hconst (σ a) a)
  rw [h1, h2] at h3
  exact (by decide : ¬ (1 : ZMod 3) = -1) h3

theorem qTwoLMH_fix_swap_card_qmodel {m : ℕ} {V : Type} [Group V]
    {ρ : Equiv.Perm (Fin m) →* MulAut V} (h : IsQmModel m V ρ)
    (a b : Fin m) (hab : a ≠ b) :
    Nat.card {v : V // ρ (Equiv.swap a b) v = v} * 3 = Nat.card V := by
  obtain ⟨π, hsurj, hker, heq⟩ := h.ex
  let ψ : (Fin m → Multiplicative (ZMod 3)) →* Multiplicative (ZMod 3) :=
    { toFun := fun w => ofAdd (toAdd (w a) - toAdd (w b))
      map_one' := by simp
      map_mul' := by
        intro f g
        rw [Pi.mul_apply, Pi.mul_apply, toAdd_mul, toAdd_mul, ← ofAdd_add]
        congr 1
        ring }
  have hψsurj : Function.Surjective ψ := by
    intro y
    refine ⟨Pi.mulSingle (M := fun _ : Fin m => Multiplicative (ZMod 3)) a (ofAdd (toAdd y)), ?_⟩
    show ofAdd (toAdd ((Pi.mulSingle (M := fun _ : Fin m => Multiplicative (ZMod 3)) a
      (ofAdd (toAdd y))) a) -
      toAdd ((Pi.mulSingle (M := fun _ : Fin m => Multiplicative (ZMod 3)) a
      (ofAdd (toAdd y))) b)) = y
    rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (Ne.symm hab), toAdd_ofAdd]
    simp
  have hBidx : Nat.card ψ.ker * 3 = Nat.card (Fin m → Multiplicative (ZMod 3)) :=
    qTwoLMH_card_ker_of_surjective_zmod3 ψ hψsurj
  have hBk : Subgroup.zpowers (fun _ : Fin m => ofAdd (1 : ZMod 3)) ≤ ψ.ker := by
    intro w hw
    rw [MonoidHom.mem_ker]
    have hconst := (qTwoLMH_mem_zpowers_perm w).mp hw
    show ofAdd (toAdd (w a) - toAdd (w b)) = 1
    rw [hconst a b, sub_self]
    rfl
  have hBfix : ∀ w, w ∈ ψ.ker ↔ ρ (Equiv.swap a b) (π w) = π w := by
    intro w
    rw [MonoidHom.mem_ker]
    constructor
    · intro hw
      have hw' : toAdd (w a) - toAdd (w b) = 0 := by
        have h : toAdd (ψ w) = 0 := by rw [congrArg toAdd hw, toAdd_one]
        rwa [show ψ w = ofAdd (toAdd (w a) - toAdd (w b)) from rfl, toAdd_ofAdd] at h
      have hab' : w a = w b := toAdd.injective (sub_eq_zero.mp hw')
      have hx : (fun k => w ((Equiv.swap a b)⁻¹ k)) = w := by
        funext k
        rw [Equiv.swap_inv]
        by_cases hka : k = a
        · rw [hka, Equiv.swap_apply_left, hab']
        · by_cases hkb : k = b
          · rw [hkb, Equiv.swap_apply_right, hab']
          · rw [Equiv.swap_apply_of_ne_of_ne hka hkb]
      rw [← heq, hx]
    · intro hfix
      have hx : (fun k => w ((Equiv.swap a b)⁻¹ k)) * w⁻¹ ∈
          Subgroup.zpowers (fun _ : Fin m => ofAdd (1 : ZMod 3)) := by
        have h1 : π (fun k => w ((Equiv.swap a b)⁻¹ k)) = ρ (Equiv.swap a b) (π w) :=
          heq (Equiv.swap a b) w
        rw [← hker, map_mul, h1, hfix, ← map_mul,
          show w * w⁻¹ = 1 from mul_inv_cancel w, map_one]
      have hconst := (qTwoLMH_mem_zpowers_perm _).mp hx
      have h1 : toAdd (((fun k => w ((Equiv.swap a b)⁻¹ k)) * w⁻¹) a) =
          toAdd (w b) - toAdd (w a) := by
        rw [Pi.mul_apply, Pi.inv_apply, Equiv.swap_inv, Equiv.swap_apply_left, toAdd_mul,
          toAdd_inv]
        exact (sub_eq_add_neg (toAdd (w b)) (toAdd (w a))).symm
      have h2 : toAdd (((fun k => w ((Equiv.swap a b)⁻¹ k)) * w⁻¹) b) =
          toAdd (w a) - toAdd (w b) := by
        rw [Pi.mul_apply, Pi.inv_apply, Equiv.swap_inv, Equiv.swap_apply_right, toAdd_mul,
          toAdd_inv]
        exact (sub_eq_add_neg (toAdd (w a)) (toAdd (w b))).symm
      have h3 : toAdd (w b) - toAdd (w a) = -(toAdd (w b) - toAdd (w a)) := by
        calc toAdd (w b) - toAdd (w a)
            = toAdd (((fun k => w ((Equiv.swap a b)⁻¹ k)) * w⁻¹) a) := h1.symm
          _ = toAdd (((fun k => w ((Equiv.swap a b)⁻¹ k)) * w⁻¹) b) := hconst a b
          _ = toAdd (w a) - toAdd (w b) := h2
          _ = -(toAdd (w b) - toAdd (w a)) :=
            (neg_sub (toAdd (w b)) (toAdd (w a))).symm
      have h4 : toAdd (w b) - toAdd (w a) = 0 :=
        coord_eq_zero_of_eq_neg (p := 3) (by norm_num) (by norm_num) h3
      have hab' : toAdd (w b) = toAdd (w a) := sub_eq_zero.mp h4
      show ofAdd (toAdd (w a) - toAdd (w b)) = 1
      rw [← hab', sub_self]
      rfl
  exact qTwoLMH_card_fix_of_index_three π hsurj hker (Equiv.swap a b) ρ ψ.ker hBk hBidx hBfix

end CFSG.StandardType.QTwo

end
