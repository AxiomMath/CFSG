module

public import CFSG.RankThree.PartOne.S13K.Sp6Refl
public import CFSG.RankThree.PartOne.S13K.Sp6Reps

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartOne.S13K

open CFSG CFSG.RankThree.PartOne.KFQ

variable {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}

@[expose] noncomputable def sg10 (π : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) : ↥(M10 K) :=
  ⟨sgnPerm π s, sgnPerm_mem_M10 π s⟩

theorem sg10_apply (π : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) (v : QV K (Fin 3)) (i : Fin 3) :
    (sg10 π s : ↥(M10 K)).1 v i =
      if s (π.symm i) then frobQ K (v (π.symm i)) else v (π.symm i) :=
  sgnPerm_apply π s v i

theorem sg10_conj_perm (σ π : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) :
    sg10 σ (fun _ => false) * sg10 π s * (sg10 σ (fun _ => false))⁻¹ =
      (sg10 (σ * π * σ⁻¹) (fun j => s (σ.symm j)) : ↥(M10 K)) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  refine LinearEquiv.ext fun v => ?_
  funext i
  change (sg10 σ (fun _ => false) : ↥(M10 K)).1 ((sg10 π s : ↥(M10 K)).1 v) i =
    (sg10 (σ * π * σ⁻¹) (fun j => s (σ.symm j)) : ↥(M10 K)).1
      ((sg10 σ (fun _ => false) : ↥(M10 K)).1 v) i
  simp only [sg10_apply, Equiv.Perm.mul_def, Equiv.Perm.inv_def, Equiv.symm_trans_apply,
    Equiv.symm_symm, Equiv.symm_apply_apply, Bool.false_eq_true, ite_false]

theorem sg10_conj_sign {a b : Fin 3} (hab : a ≠ b) :
    sg10 1 (fun j => decide (j = b)) * sg10 (Equiv.swap a b) (fun _ => false) *
        (sg10 1 (fun j => decide (j = b)))⁻¹ =
      (sg10 (Equiv.swap a b) (fun j => decide (j = a ∨ j = b)) : ↥(M10 K)) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  refine LinearEquiv.ext fun v => ?_
  funext i
  change (sg10 1 (fun j => decide (j = b)) : ↥(M10 K)).1
      ((sg10 (Equiv.swap a b) (fun _ => false) : ↥(M10 K)).1 v) i =
    (sg10 (Equiv.swap a b) (fun j => decide (j = a ∨ j = b)) : ↥(M10 K)).1
      ((sg10 1 (fun j => decide (j = b)) : ↥(M10 K)).1 v) i
  by_cases hia : i = a
  · subst hia
    simp [sg10_apply, hab, frobQ_frobQ]
  · by_cases hib : i = b
    · subst hib
      simp [sg10_apply, hab]
    · simp [sg10_apply, hia, hib, Equiv.swap_apply_of_ne_of_ne hia hib]

theorem sact_pow {π : Equiv.Perm (Fin 3)} {ε : Fin 3 → Bool} {x : Fin 3 → (Qext K)ˣ}
    (hx : ∀ i, x i ^ p = 1) : ∀ j, sact π ε x j ^ p = 1 := by
  intro j
  rw [sact_apply]
  split_ifs
  · rw [inv_pow, hx, inv_one]
  · exact hx _

theorem sg10_hg1 (hpq : p ∣ Nat.card K + 1) (π : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool) :
    ∀ x : ↥(M10 K), IsTor p x → IsTor p (sg10 π s * x * (sg10 π s)⁻¹) := by
  rintro x ⟨a, ha, hxa⟩
  refine ⟨sact π s a, sact_pow ha, ?_⟩
  change sgnPerm π s * x.1 * (sgnPerm π s)⁻¹ = _
  rw [hxa]
  exact sgnPerm_conj hpq π s a (sact π s a) ha (fun i => rfl)

theorem exists_perm_of_ne : ∀ a b : Fin 3, a ≠ b →
    ∃ σ : Equiv.Perm (Fin 3), σ 0 = a ∧ σ 1 = b := by decide +kernel

theorem eq_or_eq_or_eq : ∀ a b c : Fin 3, a ≠ b → c ≠ a → c ≠ b →
    ∀ j : Fin 3, j = a ∨ j = b ∨ j = c := by decide +kernel

theorem sact_fun_swap : ∀ i : Fin 3, (fun j => (![true, false, false] : Fin 3 → Bool)
    ((Equiv.swap 0 i).symm j)) = fun j => decide (j = i) := by decide +kernel

namespace Sp6Ctx

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L E : Subgroup G}
  {f : ℕ} (C : Sp6Ctx p A c L E f K)

include C in
theorem hg2_of_hg1 {g : ↥(M10 K)} (hg1 : ∀ x, IsTor p x → IsTor p (g * x * g⁻¹)) :
    ∀ x, IsTor p x → IsTor p (g⁻¹ * x * g) := by
  have hfin : Finite ↥(M10 K) := Finite.of_equiv ↥L C.ψ.symm.toEquiv
  let cj : {y : ↥(M10 K) // IsTor p y} → {y : ↥(M10 K) // IsTor p y} :=
    fun x => ⟨g * x.1 * g⁻¹, hg1 x.1 x.2⟩
  have hinj : Function.Injective cj := by
    intro x y hxy
    have h1 : g * x.1 * g⁻¹ = g * y.1 * g⁻¹ := congrArg Subtype.val hxy
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  intro x hx
  obtain ⟨x', hx'⟩ := Finite.injective_iff_surjective.mp hinj ⟨x, hx⟩
  have h2 : g * x'.1 * g⁻¹ = x := congrArg Subtype.val hx'
  have h3 : g⁻¹ * x * g = x'.1 := by rw [← h2]; group
  rw [h3]
  exact x'.2

theorem kfAt_conj_of_mul {m g g' : ↥(M10 K)}
    (hm1 : ∀ x, IsTor p x → IsTor p (m * x * m⁻¹))
    (hm2 : ∀ x, IsTor p x → IsTor p (m⁻¹ * x * m))
    (hg1 : ∀ x, IsTor p x → IsTor p (g * x * g⁻¹))
    (hg2 : ∀ x, IsTor p x → IsTor p (g⁻¹ * x * g))
    (hg1' : ∀ x, IsTor p x → IsTor p (g' * x * g'⁻¹))
    (hg2' : ∀ x, IsTor p x → IsTor p (g'⁻¹ * x * g'))
    (hconj : m * g' * m⁻¹ = g)
    (h : KFAt p E f (E.normalizerMonoidHom ⟨C.phi g', C.mem_normalizer hg1' hg2'⟩)) :
    KFAt p E f (E.normalizerMonoidHom ⟨C.phi g, C.mem_normalizer hg1 hg2⟩) := by
  have h2 := h.conj (C.mem_normalizer hm1 hm2)
  convert h2 using 1
  unfold conjAut
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  change C.phi g = C.phi m * C.phi g' * (C.phi m)⁻¹
  rw [← hconj, map_mul, map_mul, map_inv]

@[expose] noncomputable def tSgn (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool) : MulAut E :=
  E.normalizerMonoidHom ⟨C.phi (sg10 π ε),
    C.mem_normalizer (sg10_hg1 C.hpq' π ε) (C.hg2_of_hg1 (sg10_hg1 C.hpq' π ε))⟩

theorem kfAt_tSgn_conj (σ : Equiv.Perm (Fin 3)) (τ : Fin 3 → Bool)
    {π π' : Equiv.Perm (Fin 3)} {s s' : Fin 3 → Bool}
    (hconj : sg10 σ τ * sg10 π' s' * (sg10 σ τ)⁻¹ = (sg10 π s : ↥(M10 K)))
    (h : KFAt p E f (C.tSgn π' s')) : KFAt p E f (C.tSgn π s) :=
  C.kfAt_conj_of_mul (sg10_hg1 C.hpq' σ τ) (C.hg2_of_hg1 (sg10_hg1 C.hpq' σ τ))
    (sg10_hg1 C.hpq' π s) (C.hg2_of_hg1 (sg10_hg1 C.hpq' π s))
    (sg10_hg1 C.hpq' π' s') (C.hg2_of_hg1 (sg10_hg1 C.hpq' π' s')) hconj h

theorem kfAt_tSgn_S (i : Fin 3) : KFAt p E f (C.tSgn 1 (fun j => decide (j = i))) := by
  have h0 : KFAt p E f (C.tSgn 1 ![true, false, false]) := C.kfAt_gS
  refine C.kfAt_tSgn_conj (Equiv.swap 0 i) (fun _ => false) ?_ h0
  rw [sg10_conj_perm, sact_fun_swap i]
  congr 1
  simp

theorem kfAt_tSgn_D0 {a b : Fin 3} (hab : a ≠ b) :
    KFAt p E f (C.tSgn (Equiv.swap a b) (fun _ => false)) := by
  obtain ⟨σ, h0, h1⟩ := exists_perm_of_ne a b hab
  have h : KFAt p E f (C.tSgn (Equiv.swap 0 1) ![false, false, false]) := C.kfAt_gD
  refine C.kfAt_tSgn_conj σ (fun _ => false) ?_ h
  rw [sg10_conj_perm]
  have hperm : σ * Equiv.swap 0 1 * σ⁻¹ = Equiv.swap a b := by
    rw [Equiv.mul_swap_eq_swap_mul, mul_inv_cancel_right, h0, h1]
  have hfun : (fun j => (![false, false, false] : Fin 3 → Bool) (σ.symm j)) = fun _ => false := by
    funext j
    exact bool_false_vec _
  rw [hperm, hfun]

theorem kfAt_tSgn_D1 {a b : Fin 3} (hab : a ≠ b) :
    KFAt p E f (C.tSgn (Equiv.swap a b) (fun j => decide (j = a ∨ j = b))) :=
  C.kfAt_tSgn_conj 1 (fun j => decide (j = b)) (sg10_conj_sign hab) (C.kfAt_tSgn_D0 hab)

theorem kfAt_tSgn_of_shape {π : Equiv.Perm (Fin 3)} {ε : Fin 3 → Bool} (hs : ReflShape π ε) :
    KFAt p E f (C.tSgn π ε) := by
  rcases hs with ⟨rfl, i, hi, hj⟩ | ⟨a, b, c', hab, hca, hcb, rfl, hεab, hεc⟩
  · have : ε = fun j => decide (j = i) := by
      funext j
      by_cases h : j = i
      · subst h
        simp [hi]
      · simp [h, hj j h]
    rw [this]
    exact C.kfAt_tSgn_S i
  · have hall := eq_or_eq_or_eq a b c' hab hca hcb
    cases hεa : ε a
    · have : ε = fun _ => false := by
        funext j
        rcases hall j with rfl | rfl | rfl
        · exact hεa
        · rw [← hεab, hεa]
        · exact hεc
      rw [this]
      exact C.kfAt_tSgn_D0 hab
    · have : ε = fun j => decide (j = a ∨ j = b) := by
        funext j
        rcases hall j with rfl | rfl | rfl
        · simp [hεa]
        · simp [← hεab, hεa]
        · simp [hεc, hca, hcb]
      rw [this]
      exact C.kfAt_tSgn_D1 hab

end Sp6Ctx

end CFSG.RankThree.PartOne.S13K
