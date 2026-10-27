module

public import CFSG.Quasithin.Background.B5FinSpCore
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.Quasithin.MS93.A6F

open CFSG.Quasithin B5FinSp Equiv

@[expose] def actChi (σ : Perm (Fin 6)) (w : Fin 4 → ZMod 2) : Fin 4 → ZMod 2 :=
  chi (fun i => phi w (σ⁻¹ i))

theorem phi_add : ∀ v w : Fin 4 → ZMod 2, ∃ c : ZMod 2,
    phi (v + w) = phi v + phi w + fun _ => c := by
  decide +kernel

theorem chi_perm (σ : Perm (Fin 6)) {x : Fin 6 → ZMod 2} (hx : ∑ i, x i = 0) :
    chi (fun i => x (σ⁻¹ i)) = actChi σ (chi x) := by
  obtain ⟨v, c, rfl⟩ := exists_phi_of_sum_zero x hx
  have h1 : (fun i => (phi v + fun _ => c : Fin 6 → ZMod 2) (σ⁻¹ i)) =
      (fun i => phi v (σ⁻¹ i)) + fun _ => c := by
    funext i
    rfl
  rw [h1, chi_add, chi_const, add_zero, chi_add, chi_phi, chi_const, add_zero]
  rfl

theorem sum_perm_phi (σ : Perm (Fin 6)) (w : Fin 4 → ZMod 2) : ∑ i, phi w (σ⁻¹ i) = 0 := by
  rw [Equiv.sum_comp σ⁻¹ (phi w)]
  exact sum_phi w

theorem actChi_mul (σ τ : Perm (Fin 6)) (w : Fin 4 → ZMod 2) :
    actChi (σ * τ) w = actChi σ (actChi τ w) := by
  show actChi (σ * τ) w = actChi σ (chi (fun i => phi w (τ⁻¹ i)))
  rw [← chi_perm σ (sum_perm_phi τ w)]
  show chi (fun i => phi w ((σ * τ)⁻¹ i)) = chi (fun i => phi w (τ⁻¹ (σ⁻¹ i)))
  rw [_root_.mul_inv_rev]
  rfl

theorem actChi_one (w : Fin 4 → ZMod 2) : actChi 1 w = w := by
  show chi (fun i => phi w ((1 : Perm (Fin 6))⁻¹ i)) = w
  rw [inv_one]
  exact chi_phi w

theorem actChi_add (σ : Perm (Fin 6)) (v w : Fin 4 → ZMod 2) :
    actChi σ (v + w) = actChi σ v + actChi σ w := by
  obtain ⟨c, hc⟩ := phi_add v w
  show chi (fun i => phi (v + w) (σ⁻¹ i)) =
    chi (fun i => phi v (σ⁻¹ i)) + chi (fun i => phi w (σ⁻¹ i))
  rw [hc]
  have h1 : (fun i => (phi v + phi w + fun _ => c : Fin 6 → ZMod 2) (σ⁻¹ i)) =
      (fun i => phi v (σ⁻¹ i)) + (fun i => phi w (σ⁻¹ i)) + fun _ => c := by
    funext i
    rfl
  rw [h1, chi_add, chi_add, chi_const, add_zero]

theorem actChi_inv_apply (σ : Perm (Fin 6)) (w : Fin 4 → ZMod 2) :
    actChi σ⁻¹ (actChi σ w) = w := by
  rw [← actChi_mul, inv_mul_cancel, actChi_one]

theorem actChi_apply_inv (σ : Perm (Fin 6)) (w : Fin 4 → ZMod 2) :
    actChi σ (actChi σ⁻¹ w) = w := by
  rw [← actChi_mul, mul_inv_cancel, actChi_one]

theorem eq_one_of_actChi : ∀ σ : Perm (Fin 6), (∀ w, actChi σ w = w) → σ = 1 := by
  decide +kernel

theorem eq_of_actChi {σ τ : Perm (Fin 6)} (h : ∀ w, actChi σ w = actChi τ w) : σ = τ := by
  have := eq_one_of_actChi (τ⁻¹ * σ) fun w => by rw [actChi_mul, h, actChi_inv_apply]
  rw [inv_mul_eq_one] at this
  exact this.symm

@[expose] def aP : Perm (Fin 6) := swap 0 3 * swap 0 2 * swap 0 1

@[expose] def d8List : List (Perm (Fin 6)) :=
  [1, aP, aP * aP, aP * aP * aP, swap 0 2, aP * swap 0 2, aP * aP * swap 0 2,
    aP * aP * aP * swap 0 2]

@[expose] def s1List : List (Perm (Fin 6)) := d8List ++ d8List.map (· * swap 4 5)

theorem s1_one : (1 : Perm (Fin 6)) ∈ s1List := by decide

theorem s1_mul : ∀ a ∈ s1List, ∀ b ∈ s1List, a * b ∈ s1List := by decide +kernel

theorem s1_inv : ∀ a ∈ s1List, a⁻¹ ∈ s1List := by decide +kernel

@[expose] def sylowS : Subgroup (Perm (Fin 6)) where
  carrier := {σ | σ ∈ s1List}
  mul_mem' {a b} ha hb := s1_mul a ha b hb
  one_mem' := s1_one
  inv_mem' {a} ha := s1_inv a ha

theorem card_s1 : (Finset.univ.filter fun σ : Perm (Fin 6) => σ ∈ s1List).card = 16 := by
  decide +kernel

theorem card_sylowS : Nat.card sylowS = 16 := by
  have e : Nat.card sylowS = Nat.card {σ : Perm (Fin 6) // σ ∈ s1List} := rfl
  rw [e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact card_s1

theorem isPGroup_sylowS : IsPGroup 2 sylowS := IsPGroup.of_card (n := 4) card_sylowS

theorem exists_sylow_S : ∃ U : Sylow 2 (Perm (Fin 6)), (U : Subgroup (Perm (Fin 6))) = sylowS := by
  have h := Subgroup.card_mul_index sylowS
  rw [card_sylowS, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at h
  have hidx : sylowS.index = 45 := by
    have : Nat.factorial 6 = 720 := by decide
    omega
  exact ⟨isPGroup_sylowS.toSylow (by rw [hidx]; norm_num), rfl⟩

open scoped Pointwise in
theorem exists_conj_mem_sylowS {P : Subgroup (Perm (Fin 6))} (hP : IsPGroup 2 P) :
    ∃ g : Perm (Fin 6), ∀ x ∈ P, g⁻¹ * x * g ∈ s1List := by
  obtain ⟨U, hU⟩ := exists_sylow_S
  obtain ⟨S, hS⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Perm (Fin 6)) U S
  refine ⟨g, fun x hx => ?_⟩
  have h1 : x ∈ (S : Subgroup (Perm (Fin 6))) := hS hx
  rw [← hg] at h1
  have h2 : x ∈ MulAut.conj g • (U : Subgroup (Perm (Fin 6))) := h1
  rw [Subgroup.mem_smul_pointwise_iff_exists] at h2
  obtain ⟨u, hu, rfl⟩ := h2
  have : g⁻¹ * (MulAut.conj g • u) * g = u := by
    simp [MulAut.smul_def, MulAut.conj_apply, mul_assoc]
  rw [this]
  have hu' : u ∈ sylowS := hU ▸ hu
  exact hu'

@[expose] def invList : List (Perm (Fin 6)) :=
  [aP * aP, swap 0 2 * swap 4 5, aP * swap 0 2, aP * aP * swap 0 2 * swap 4 5,
    aP * aP * aP * swap 0 2]

theorem mem_invList : ∀ s ∈ s1List, Perm.sign s = 1 → s * s = 1 → s ≠ 1 → s ∈ invList := by
  decide +kernel

theorem card_fix_invList : ∀ s ∈ invList,
    (Finset.univ.filter fun w => actChi s w = w).card = 4 := by
  decide +kernel

theorem card_fix_two_invList : ∀ s₁ ∈ invList, ∀ s₂ ∈ invList, s₁ * s₂ = s₂ * s₁ →
    (∃ w, ¬ (actChi s₁ w = w ↔ actChi s₂ w = w)) →
    (Finset.univ.filter fun w => actChi s₁ w = w ∧ actChi s₂ w = w).card ≤ 2 := by
  decide +kernel

@[expose] def sameFixB (s₁ s₂ : Perm (Fin 6)) : Bool :=
  decide (∀ w : Fin 4 → ZMod 2, actChi s₁ w = w ↔ actChi s₂ w = w)

theorem sameFixB_iff {s₁ s₂ : Perm (Fin 6)} :
    sameFixB s₁ s₂ = true ↔ ∀ w, actChi s₁ w = w ↔ actChi s₂ w = w :=
  decide_eq_true_iff

theorem uniq_invList' : ∀ s₁ ∈ invList, ∀ s₂ ∈ invList, ∀ s₁' ∈ invList, ∀ s₂' ∈ invList,
    s₁ ≠ s₂ → s₁ * s₂ = s₂ * s₁ → sameFixB s₁ s₂ = true →
    s₁' ≠ s₂' → s₁' * s₂' = s₂' * s₁' → sameFixB s₁' s₂' = true →
    (s₁' = s₁ ∨ s₁' = s₂ ∨ s₁' = s₁ * s₂) := by
  decide +kernel

theorem uniq_invList : ∀ s₁ ∈ invList, ∀ s₂ ∈ invList, ∀ s₁' ∈ invList, ∀ s₂' ∈ invList,
    s₁ ≠ s₂ → s₁ * s₂ = s₂ * s₁ → (∀ w, actChi s₁ w = w ↔ actChi s₂ w = w) →
    s₁' ≠ s₂' → s₁' * s₂' = s₂' * s₁' → (∀ w, actChi s₁' w = w ↔ actChi s₂' w = w) →
    (s₁' = s₁ ∨ s₁' = s₂ ∨ s₁' = s₁ * s₂) :=
  fun s₁ h₁ s₂ h₂ s₁' h₁' s₂' h₂' hne hc hf hne' hc' hf' =>
    uniq_invList' s₁ h₁ s₂ h₂ s₁' h₁' s₂' h₂' hne hc (sameFixB_iff.mpr hf) hne' hc'
      (sameFixB_iff.mpr hf')

@[expose] def s0List : List (Perm (Fin 6)) :=
  1 :: invList ++ [aP * swap 4 5, aP * aP * aP * swap 4 5]

theorem mem_s0List : ∀ y ∈ s1List, Perm.sign y = 1 → y ∈ s0List := by
  decide +kernel

@[expose] def centB (s₁ s₂ : Perm (Fin 6)) : Bool :=
  s0List.all fun y => !(decide (y * s₁ = s₁ * y) && decide (y * s₂ = s₂ * y)) ||
    decide (y = 1) || decide (y = s₁) || decide (y = s₂) || decide (y = s₁ * s₂)

theorem centB_invList : ∀ s₁ ∈ invList, ∀ s₂ ∈ invList, s₁ ≠ s₂ → s₁ * s₂ = s₂ * s₁ →
    centB s₁ s₂ = true := by
  decide +kernel

theorem cent_s0List {s₁ s₂ : Perm (Fin 6)} (h₁ : s₁ ∈ invList) (h₂ : s₂ ∈ invList)
    (hne : s₁ ≠ s₂) (hc : s₁ * s₂ = s₂ * s₁) {y : Perm (Fin 6)} (hy : y ∈ s0List)
    (hy₁ : y * s₁ = s₁ * y) (hy₂ : y * s₂ = s₂ * y) :
    y = 1 ∨ y = s₁ ∨ y = s₂ ∨ y = s₁ * s₂ := by
  have h := centB_invList s₁ h₁ s₂ h₂ hne hc
  rw [centB, List.all_eq_true] at h
  have := h y hy
  simp only [hy₁, hy₂, decide_true, Bool.and_self, Bool.not_true, Bool.false_or,
    Bool.or_eq_true, decide_eq_true_eq] at this
  rcases this with ((h1 | h1) | h1) | h1
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Or.inl h1))
  · exact Or.inr (Or.inr (Or.inr h1))

theorem actChi_conj (g σ : Perm (Fin 6)) (w : Fin 4 → ZMod 2) :
    actChi (g⁻¹ * σ * g) w = actChi g⁻¹ (actChi σ (actChi g w)) := by
  rw [actChi_mul, actChi_mul]

theorem fix_conj_iff (g σ : Perm (Fin 6)) (w : Fin 4 → ZMod 2) :
    actChi (g⁻¹ * σ * g) w = w ↔ actChi σ (actChi g w) = actChi g w := by
  rw [actChi_conj]
  constructor
  · intro h
    have := congrArg (actChi g) h
    rwa [actChi_apply_inv] at this
  · intro h
    rw [h, actChi_inv_apply]

theorem card_fix_conj (g σ : Perm (Fin 6)) :
    (Finset.univ.filter fun w => actChi (g⁻¹ * σ * g) w = w).card =
      (Finset.univ.filter fun w => actChi σ w = w).card := by
  refine Finset.card_bij (fun w _ => actChi g w) (fun w hw => ?_) (fun w _ w' _ h => ?_)
    (fun w hw => ⟨actChi g⁻¹ w, ?_, actChi_apply_inv g w⟩)
  · rw [Finset.mem_filter] at hw ⊢
    exact ⟨Finset.mem_univ _, (fix_conj_iff g σ w).mp hw.2⟩
  · have := congrArg (actChi g⁻¹) h
    rwa [actChi_inv_apply, actChi_inv_apply] at this
  · rw [Finset.mem_filter] at hw ⊢
    refine ⟨Finset.mem_univ _, (fix_conj_iff g σ _).mpr ?_⟩
    rw [actChi_apply_inv]
    exact hw.2

theorem card_fix_two_conj (g σ τ : Perm (Fin 6)) :
    (Finset.univ.filter fun w => actChi (g⁻¹ * σ * g) w = w ∧ actChi (g⁻¹ * τ * g) w = w).card =
      (Finset.univ.filter fun w => actChi σ w = w ∧ actChi τ w = w).card := by
  refine Finset.card_bij (fun w _ => actChi g w) (fun w hw => ?_) (fun w _ w' _ h => ?_)
    (fun w hw => ⟨actChi g⁻¹ w, ?_, actChi_apply_inv g w⟩)
  · rw [Finset.mem_filter] at hw ⊢
    exact ⟨Finset.mem_univ _, (fix_conj_iff g σ w).mp hw.2.1, (fix_conj_iff g τ w).mp hw.2.2⟩
  · have := congrArg (actChi g⁻¹) h
    rwa [actChi_inv_apply, actChi_inv_apply] at this
  · rw [Finset.mem_filter] at hw ⊢
    refine ⟨Finset.mem_univ _, (fix_conj_iff g σ _).mpr ?_, (fix_conj_iff g τ _).mpr ?_⟩
    · rw [actChi_apply_inv]
      exact hw.2.1
    · rw [actChi_apply_inv]
      exact hw.2.2

theorem sameFix_conj {g σ τ : Perm (Fin 6)} (h : ∀ w, actChi σ w = w ↔ actChi τ w = w) :
    ∀ w, actChi (g⁻¹ * σ * g) w = w ↔ actChi (g⁻¹ * τ * g) w = w := fun w => by
  rw [fix_conj_iff, fix_conj_iff]
  exact h _

theorem conj_mul_conj (g x y : Perm (Fin 6)) :
    (g⁻¹ * x * g) * (g⁻¹ * y * g) = g⁻¹ * (x * y) * g := by group

theorem conj_inj {g x y : Perm (Fin 6)} (h : g⁻¹ * x * g = g⁻¹ * y * g) : x = y := by
  calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    _ = g * (g⁻¹ * y * g) * g⁻¹ := by rw [h]
    _ = y := by group

theorem conj_comm {g x y : Perm (Fin 6)} (h : x * y = y * x) :
    (g⁻¹ * x * g) * (g⁻¹ * y * g) = (g⁻¹ * y * g) * (g⁻¹ * x * g) := by
  rw [conj_mul_conj, conj_mul_conj, h]

theorem conj_sq {g x : Perm (Fin 6)} (h : x * x = 1) : (g⁻¹ * x * g) * (g⁻¹ * x * g) = 1 := by
  rw [conj_mul_conj, h]
  group

theorem conj_ne_one {g x : Perm (Fin 6)} (h : x ≠ 1) : g⁻¹ * x * g ≠ 1 := fun he =>
  h (conj_inj (he.trans (by group)))

theorem sign_conj (g x : Perm (Fin 6)) : Perm.sign (g⁻¹ * x * g) = Perm.sign x := by
  rw [Perm.sign_mul, Perm.sign_mul, Perm.sign_inv, mul_comm (Perm.sign g) (Perm.sign x),
    mul_assoc, Int.units_mul_self, mul_one]

variable {P : Subgroup (Perm (Fin 6))}

theorem conj_mem_invList {g : Perm (Fin 6)} (hg : ∀ x ∈ P, g⁻¹ * x * g ∈ s1List)
    (hPA : ∀ x ∈ P, Perm.sign x = 1) {s : Perm (Fin 6)} (hs : s ∈ P) (hs2 : s * s = 1)
    (hs1 : s ≠ 1) : g⁻¹ * s * g ∈ invList :=
  mem_invList _ (hg s hs) (by rw [sign_conj]; exact hPA s hs) (conj_sq hs2) (conj_ne_one hs1)

theorem card_fix_of_mem (hP : IsPGroup 2 P) (hPA : ∀ x ∈ P, Perm.sign x = 1)
    {s : Perm (Fin 6)} (hs : s ∈ P) (hs2 : s * s = 1) (hs1 : s ≠ 1) :
    (Finset.univ.filter fun w => actChi s w = w).card = 4 := by
  obtain ⟨g, hg⟩ := exists_conj_mem_sylowS hP
  rw [← card_fix_conj g s]
  exact card_fix_invList _ (conj_mem_invList hg hPA hs hs2 hs1)

theorem card_fix_two_of_mem (hP : IsPGroup 2 P) (hPA : ∀ x ∈ P, Perm.sign x = 1)
    {s₁ s₂ : Perm (Fin 6)} (h₁ : s₁ ∈ P) (h₂ : s₂ ∈ P) (hs₁ : s₁ * s₁ = 1) (hs₂ : s₂ * s₂ = 1)
    (hn₁ : s₁ ≠ 1) (hn₂ : s₂ ≠ 1) (hc : s₁ * s₂ = s₂ * s₁)
    (hw : ∃ w, ¬ (actChi s₁ w = w ↔ actChi s₂ w = w)) :
    (Finset.univ.filter fun w => actChi s₁ w = w ∧ actChi s₂ w = w).card ≤ 2 := by
  obtain ⟨g, hg⟩ := exists_conj_mem_sylowS hP
  rw [← card_fix_two_conj g s₁ s₂]
  refine card_fix_two_invList _ (conj_mem_invList hg hPA h₁ hs₁ hn₁) _
    (conj_mem_invList hg hPA h₂ hs₂ hn₂) (conj_comm hc) ?_
  obtain ⟨w, hw⟩ := hw
  refine ⟨actChi g⁻¹ w, fun h => hw ?_⟩
  have := h
  rw [fix_conj_iff, fix_conj_iff, actChi_apply_inv] at this
  exact this

theorem eq_of_fix_four (hP : IsPGroup 2 P) (hPA : ∀ x ∈ P, Perm.sign x = 1)
    {s₁ s₂ s₁' s₂' : Perm (Fin 6)} (h₁ : s₁ ∈ P) (h₂ : s₂ ∈ P) (h₁' : s₁' ∈ P) (h₂' : s₂' ∈ P)
    (hs₁ : s₁ * s₁ = 1) (hs₂ : s₂ * s₂ = 1) (hs₁' : s₁' * s₁' = 1) (hs₂' : s₂' * s₂' = 1)
    (hn₁ : s₁ ≠ 1) (hn₂ : s₂ ≠ 1) (hn₁' : s₁' ≠ 1) (hn₂' : s₂' ≠ 1)
    (hne : s₁ ≠ s₂) (hc : s₁ * s₂ = s₂ * s₁) (hf : ∀ w, actChi s₁ w = w ↔ actChi s₂ w = w)
    (hne' : s₁' ≠ s₂') (hc' : s₁' * s₂' = s₂' * s₁')
    (hf' : ∀ w, actChi s₁' w = w ↔ actChi s₂' w = w) :
    s₁' = s₁ ∨ s₁' = s₂ ∨ s₁' = s₁ * s₂ := by
  obtain ⟨g, hg⟩ := exists_conj_mem_sylowS hP
  rcases uniq_invList _ (conj_mem_invList hg hPA h₁ hs₁ hn₁) _
      (conj_mem_invList hg hPA h₂ hs₂ hn₂) _ (conj_mem_invList hg hPA h₁' hs₁' hn₁') _
      (conj_mem_invList hg hPA h₂' hs₂' hn₂') (fun h => hne (conj_inj h)) (conj_comm hc)
      (sameFix_conj hf) (fun h => hne' (conj_inj h)) (conj_comm hc') (sameFix_conj hf') with
    e | e | e
  · exact Or.inl (conj_inj e)
  · exact Or.inr (Or.inl (conj_inj e))
  · right; right
    rw [conj_mul_conj] at e
    exact conj_inj e

theorem mem_of_comm_four (hP : IsPGroup 2 P) (hPA : ∀ x ∈ P, Perm.sign x = 1)
    {s₁ s₂ y : Perm (Fin 6)} (h₁ : s₁ ∈ P) (h₂ : s₂ ∈ P) (hy : y ∈ P)
    (hs₁ : s₁ * s₁ = 1) (hs₂ : s₂ * s₂ = 1) (hn₁ : s₁ ≠ 1) (hn₂ : s₂ ≠ 1)
    (hne : s₁ ≠ s₂) (hc : s₁ * s₂ = s₂ * s₁) (hy₁ : y * s₁ = s₁ * y) (hy₂ : y * s₂ = s₂ * y) :
    y = 1 ∨ y = s₁ ∨ y = s₂ ∨ y = s₁ * s₂ := by
  obtain ⟨g, hg⟩ := exists_conj_mem_sylowS hP
  have hy0 : g⁻¹ * y * g ∈ s0List :=
    mem_s0List _ (hg y hy) (by rw [sign_conj]; exact hPA y hy)
  rcases cent_s0List (conj_mem_invList hg hPA h₁ hs₁ hn₁) (conj_mem_invList hg hPA h₂ hs₂ hn₂)
      (fun h => hne (conj_inj h)) (conj_comm hc) hy0 (conj_comm hy₁) (conj_comm hy₂) with
    e | e | e | e
  · left
    exact conj_inj (e.trans (by group))
  · exact Or.inr (Or.inl (conj_inj e))
  · exact Or.inr (Or.inr (Or.inl (conj_inj e)))
  · right; right; right
    rw [conj_mul_conj] at e
    exact conj_inj e

end CFSG.Quasithin.MS93.A6F
