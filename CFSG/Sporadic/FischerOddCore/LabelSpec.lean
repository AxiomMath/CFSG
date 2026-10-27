module

public import Certificates.Data.CFSGNative.FischerOddCore.Checks
public import CFSG.Monster.B.Co2.PermArr
public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Group

public noncomputable section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.FischerOddCore.Native

variable {m : ℕ}

theorem rep_conjArr {g gi a : Array ℕ} {G A : Equiv.Perm (Fin m)} (hg : Rep m g G)
    (hgi : Rep m gi G⁻¹) (ha : Rep m a A) : Rep m (conjArr m g gi a) (G * A * G⁻¹) := by
  rw [conjArr, mul_assoc]
  exact rep_compA hg (rep_compA ha hgi)

theorem isInvArr_iff {a : Array ℕ} {A : Equiv.Perm (Fin m)} (ha : Rep m a A) :
    isInvArr m a = true ↔ A ≠ 1 ∧ A * A = 1 := by
  rw [isInvArr, Bool.and_eq_true, Bool.not_eq_true', ← eqA_iff (rep_compA ha ha) rep_idA]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun h => ?_, h2⟩
    rw [(eqA_iff ha rep_idA).2 h] at h1
    exact absurd h1 (by decide)
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    cases h : eqA m a (idA m)
    · rfl
    · exact absurd ((eqA_iff ha rep_idA).1 h) h1

theorem orderOf_eq_two_iff' {G : Type*} [Group G] (x : G) : orderOf x = 2 ↔ x ≠ 1 ∧ x * x = 1 := by
  rw [orderOf_eq_prime_iff, pow_two, and_comm]

theorem card_fin_subtype_eq_countP (sz : ℕ) (q : ℕ → Bool) :
    Nat.card {I : Fin sz // q I = true} = (List.range sz).countP q := by
  induction sz with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.countP_append, ← ih]
    have e : {I : Fin (n + 1) // q I = true} ≃
        {I : Fin n // q I = true} ⊕ {u : Unit // q n = true} :=
      { toFun := fun I => if h : (I : ℕ) < n then Sum.inl ⟨⟨I, h⟩, I.2⟩
          else Sum.inr ⟨(), by
            have : (I : ℕ) = n := by have := I.1.2; omega
            rw [← this]; exact I.2⟩
        invFun := fun x => match x with
          | Sum.inl I => ⟨Fin.castSucc I.1, I.2⟩
          | Sum.inr u => ⟨Fin.last n, u.2⟩
        left_inv := fun I => by
          by_cases h : (I : ℕ) < n
          · simp [h]
          · simp only [h, dite_false]
            apply Subtype.ext
            apply Fin.ext
            simp only [Fin.val_last]
            have := I.1.2
            omega
        right_inv := fun x => by
          rcases x with I | u
          · simp [I.1.2]
          · simp }
    rw [Nat.card_congr e, Nat.card_sum]
    congr 1
    by_cases hq : q n = true
    · simp [hq]
    · simp [hq]

section Labels

variable {S : Type*} [Group S] {ρ : S →* Equiv.Perm (Fin m)} {sz : ℕ} {res : ℕ → Array ℕ}
  {E : ℕ → S} {steps stepsInv : Array (Array ℕ)} {gs : ℕ → S} {roots : Array ℕ} {C : LabelCert}

section Facts

variable (hρ : Function.Injective ρ) (hE : ∀ I < sz, Rep m (res I) (ρ (E I)))
  (hgs : ∀ s < steps.size, Rep m steps[s]! (ρ (gs s)) ∧ Rep m stepsInv[s]! (ρ (gs s))⁻¹)
  (hok : ∀ I < sz, labelOKAt m sz res steps stepsInv roots C I = true)
include hρ hE hok

omit hok in
theorem isInvArr_res_iff {I : ℕ} (hI : I < sz) :
    isInvArr m (res I) = true ↔ orderOf (E I) = 2 := by
  rw [isInvArr_iff (hE I hI), orderOf_eq_two_iff', ← map_mul, Ne, ← map_one ρ,
    hρ.eq_iff, hρ.eq_iff]

theorem orderOf_eq_two_iff_lab_lt {I : ℕ} (hI : I < sz) :
    orderOf (E I) = 2 ↔ C.lab[I]! < roots.size := by
  have h := hok I hI
  rw [← isInvArr_res_iff hρ hE hI]
  unfold labelOKAt at h
  by_cases hinv : isInvArr m (res I) = true
  · rw [ite_eq_left hinv, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨fun _ => h.1.1, fun _ => hinv⟩
  · rw [ite_eq_right hinv, beq_iff_eq] at h
    simp [hinv, h]

theorem labelOKAt_inv {I : ℕ} (hI : I < sz) (hl : C.lab[I]! < roots.size) :
    (if C.dep[I]! = 0 then I = roots[C.lab[I]!]!
      else C.par[I]! < sz ∧ C.dep[C.par[I]!]! < C.dep[I]! ∧ C.lab[C.par[I]!]! = C.lab[I]! ∧
        C.gen[I]! < steps.size ∧ eqA m (res I) (conjArr m steps[C.gen[I]!]!
          stepsInv[C.gen[I]!]! (res C.par[I]!)) = true) ∧
      ∀ s < steps.size, C.nb[I * steps.size + s]! < sz ∧
        C.lab[C.nb[I * steps.size + s]!]! = C.lab[I]! ∧
        eqA m (res C.nb[I * steps.size + s]!) (conjArr m steps[s]! stepsInv[s]! (res I)) =
          true := by
  have hinv : isInvArr m (res I) = true :=
    (isInvArr_res_iff hρ hE hI).2 ((orderOf_eq_two_iff_lab_lt hρ hE hok hI).2 hl)
  have h := hok I hI
  unfold labelOKAt at h
  rw [ite_eq_left hinv] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨-, h1⟩, h2⟩ := h
  refine ⟨?_, fun s hs => ?_⟩
  · by_cases hd : C.dep[I]! = 0
    · rw [ite_eq_left hd]
      rw [ite_eq_left (by simpa using hd), beq_iff_eq] at h1
      exact h1
    · rw [ite_eq_right hd]
      rw [ite_eq_right (by simpa using hd)] at h1
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h1
      obtain ⟨⟨⟨⟨ha, hb⟩, hc⟩, hd'⟩, he⟩ := h1
      exact ⟨ha, hb, hc, hd', he⟩
  · have := allLt_spec h2 hs
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩

include hgs in
theorem exists_conj_root {I : ℕ} (hI : I < sz) (hl : C.lab[I]! < roots.size) :
    ∃ g : S, g * E roots[C.lab[I]!]! * g⁻¹ = E I := by
  induction hd : C.dep[I]! using Nat.strong_induction_on generalizing I with
  | _ d ih =>
    obtain ⟨h1, -⟩ := labelOKAt_inv hρ hE hok hI hl
    by_cases hd0 : C.dep[I]! = 0
    · rw [ite_eq_left hd0] at h1
      refine ⟨1, ?_⟩
      rw [one_mul, inv_one, mul_one, ← h1]
    · rw [ite_eq_right hd0] at h1
      obtain ⟨hJ, hdep, hlab, hs, heq⟩ := h1
      have hlJ : C.lab[C.par[I]!]! < roots.size := hlab ▸ hl
      obtain ⟨g, hg⟩ := ih _ (hd ▸ hdep) hJ hlJ rfl
      rw [hlab] at hg
      have hEI : E I = gs C.gen[I]! * E C.par[I]! * (gs C.gen[I]!)⁻¹ := by
        apply hρ
        have := eq_of_eqA (hE I hI) (rep_conjArr (hgs _ hs).1 (hgs _ hs).2 (hE _ hJ)) heq
        rw [this, map_mul, map_mul, map_inv]
      refine ⟨gs C.gen[I]! * g, ?_⟩
      rw [hEI, ← hg]
      group

include hgs in
theorem exists_conj_step {I : ℕ} (hI : I < sz) (hl : C.lab[I]! < roots.size) {s : ℕ}
    (hs : s < steps.size) :
    ∃ J < sz, C.lab[J]! = C.lab[I]! ∧ E J = gs s * E I * (gs s)⁻¹ := by
  obtain ⟨-, h2⟩ := labelOKAt_inv hρ hE hok hI hl
  obtain ⟨hJ, hlab, heq⟩ := h2 s hs
  refine ⟨_, hJ, hlab, hρ ?_⟩
  rw [eq_of_eqA (hE _ hJ) (rep_conjArr (hgs _ hs).1 (hgs _ hs).2 (hE I hI)) heq, map_mul, map_mul,
    map_inv]

include hgs in
theorem exists_conj_all [Finite S]
    (hgen : Subgroup.closure {x | ∃ s < steps.size, gs s = x} = ⊤) (g : S) {I : ℕ} (hI : I < sz)
    (hl : C.lab[I]! < roots.size) :
    ∃ J < sz, C.lab[J]! = C.lab[I]! ∧ E J = g * E I * g⁻¹ := by
  let P : S → Prop := fun g => ∀ I < sz, C.lab[I]! < roots.size →
    ∃ J < sz, C.lab[J]! = C.lab[I]! ∧ E J = g * E I * g⁻¹
  have hmul : ∀ x y, P x → P y → P (x * y) := by
    intro x y hx hy I hI hl
    obtain ⟨J, hJ, hlJ, hJe⟩ := hy I hI hl
    obtain ⟨K, hK, hlK, hKe⟩ := hx J hJ (hlJ ▸ hl)
    refine ⟨K, hK, hlK.trans hlJ, ?_⟩
    rw [hKe, hJe]
    group
  have hone : P 1 := fun I hI _ => ⟨I, hI, rfl, by group⟩
  have hpow : ∀ x, P x → ∀ k : ℕ, P (x ^ k) := by
    intro x hx k
    induction k with
    | zero => rw [pow_zero]; exact hone
    | succ k ih => rw [pow_succ]; exact hmul _ _ ih hx
  have hg : g ∈ Subgroup.closure {x | ∃ s < steps.size, gs s = x} := by rw [hgen]; trivial
  refine (Subgroup.closure_induction (p := fun x _ => P x) ?_ hone
    (fun x y _ _ hx hy => hmul x y hx hy)
    ?_ hg) I hI hl
  · rintro _ ⟨s, hs, rfl⟩ I hI hl
    exact exists_conj_step hρ hE hgs hok hI hl hs
  · intro x _ hx
    have hinv : x ^ (orderOf x - 1) = x⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← pow_succ, Nat.sub_add_cancel (orderOf_pos x),
        pow_orderOf_eq_one]
    rw [← hinv]
    exact hpow x hx _

end Facts

theorem labelOK_spec [Finite S] (hρ : Function.Injective ρ)
    (hE : ∀ I < sz, Rep m (res I) (ρ (E I)))
    (hgs : ∀ s < steps.size, Rep m steps[s]! (ρ (gs s)) ∧ Rep m stepsInv[s]! (ρ (gs s))⁻¹)
    (hgen : Subgroup.closure {x | ∃ s < steps.size, gs s = x} = ⊤)
    (hok : ∀ I < sz, labelOKAt m sz res steps stepsInv roots C I = true)
    (hroots : ∀ j < roots.size, roots[j]! < sz ∧ C.lab[roots[j]!]! = j)
    (hsurj : ∀ x : S, ∃ I < sz, E I = x) (hinj : ∀ I < sz, ∀ J < sz, E I = E J → I = J) :
    (∀ x : S, orderOf x = 2 → ∃ j < roots.size, ∃ g : S, g * E roots[j]! * g⁻¹ = x) ∧
    (∀ j < roots.size, ∀ j' < roots.size,
      (∃ g : S, g * E roots[j]! * g⁻¹ = E roots[j']!) → j = j') ∧
    (∀ j < roots.size, orderOf (E roots[j]!) = 2) ∧
    (∀ j < roots.size, Nat.card {x : S // ∃ g : S, g * E roots[j]! * g⁻¹ = x} =
      labCount C.lab sz j) := by
  have hlab : ∀ j < roots.size, C.lab[roots[j]!]! < roots.size := fun j hj => by
    rw [(hroots j hj).2]
    exact hj
  have hclass : ∀ j < roots.size, ∀ I < sz, (∃ g : S, g * E roots[j]! * g⁻¹ = E I) →
      C.lab[I]! = j := by
    rintro j hj I hI ⟨g, hg⟩
    obtain ⟨J, hJ, hlJ, hJe⟩ :=
      exists_conj_all hρ hE hgs hok hgen g (hroots j hj).1 (hlab j hj)
    rw [hinj I hI J hJ (hg.symm.trans hJe.symm), hlJ, (hroots j hj).2]
  refine ⟨fun x hx => ?_, fun j hj j' hj' h => ?_, fun j hj => ?_, fun j hj => ?_⟩
  · obtain ⟨I, hI, rfl⟩ := hsurj x
    have hl := (orderOf_eq_two_iff_lab_lt hρ hE hok hI).1 hx
    exact ⟨_, hl, exists_conj_root hρ hE hgs hok hI hl⟩
  · have := hclass j hj _ (hroots j' hj').1 h
    rw [(hroots j' hj').2] at this
    exact this.symm
  · exact (orderOf_eq_two_iff_lab_lt hρ hE hok (hroots j hj).1).2 (hlab j hj)
  · rw [labCount, ← card_fin_subtype_eq_countP]
    symm
    refine Nat.card_congr
      { toFun := fun I => ⟨E I, ?_⟩
        invFun := fun x => ⟨⟨_, (hsurj x).choose_spec.1⟩, ?_⟩
        left_inv := fun I => ?_
        right_inv := fun x => ?_ }
    · have hl : C.lab[(I : ℕ)]! = j := by simpa using I.2
      have := exists_conj_root hρ hE hgs hok I.1.2 (by rw [hl]; exact hj)
      rwa [hl] at this
    · obtain ⟨hI, hx⟩ := (hsurj x).choose_spec
      have := x.2
      rw [← hx] at this
      simpa using hclass j hj _ hI this
    · apply Subtype.ext
      apply Fin.ext
      exact hinj _ (hsurj _).choose_spec.1 _ I.1.2 (hsurj _).choose_spec.2
    · exact Subtype.ext (hsurj x).choose_spec.2

end Labels

end CFSG.Sporadic.FischerOddCore
