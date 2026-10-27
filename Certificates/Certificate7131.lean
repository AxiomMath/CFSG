module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115AltSixInputs

public section

open CFSG.QuasithinUnique.Ch1.AltSix
open Equiv Equiv.Perm

namespace CertificateChecks.Batch7131

open CFSG.QuasithinUnique.Ch1.AltSix
open Equiv Equiv.Perm

theorem permKey_lt (σ : Perm (Fin 6)) : permKey σ < 46656 := by
  unfold permKey
  have h0 := (σ 0).isLt
  have h1 := (σ 1).isLt
  have h2 := (σ 2).isLt
  have h3 := (σ 3).isLt
  have h4 := (σ 4).isLt
  have h5 := (σ 5).isLt
  omega

theorem fin6_cases (j : Fin 6) : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by
  fin_cases j <;> simp

theorem permKey_inj {σ τ : Perm (Fin 6)} (h : permKey σ = permKey τ) : σ = τ := by
  unfold permKey at h
  have h0 := (σ 0).isLt
  have h1 := (σ 1).isLt
  have h2 := (σ 2).isLt
  have h3 := (σ 3).isLt
  have h4 := (σ 4).isLt
  have h5 := (σ 5).isLt
  have k0 := (τ 0).isLt
  have k1 := (τ 1).isLt
  have k2 := (τ 2).isLt
  have k3 := (τ 3).isLt
  have k4 := (τ 4).isLt
  have k5 := (τ 5).isLt
  refine Equiv.ext fun j => Fin.ext ?_
  rcases fin6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;> omega

theorem foldl_set_other (f : Perm (Fin 6) → Perm (Fin 6)) :
    ∀ (L : List (Perm (Fin 6))) (t : Array (Perm (Fin 6))) (k : ℕ), (∀ a ∈ L, permKey a ≠ k) →
      (L.foldl (fun t a => t.set! (permKey a) (f a)) t)[k]? = t[k]? := by
  intro L
  induction L with
  | nil => intro t k _; rfl
  | cons c L ih =>
    intro t k hk
    rw [List.foldl_cons, ih _ _ fun a ha => hk a (List.mem_cons_of_mem _ ha)]
    simp [Array.set!, Array.getElem?_setIfInBounds, hk c List.mem_cons_self]

theorem foldl_set_mem (f : Perm (Fin 6) → Perm (Fin 6)) :
    ∀ (L : List (Perm (Fin 6))) (t : Array (Perm (Fin 6))), t.size = 46656 →
      ∀ a ∈ L, (L.foldl (fun t a => t.set! (permKey a) (f a)) t)[permKey a]? = some (f a) := by
  intro L
  induction L with
  | nil => intro t _ a ha; simp at ha
  | cons c L ih =>
    intro t ht a ha
    rw [List.foldl_cons]
    by_cases haL : a ∈ L
    · exact ih _ (by simp [Array.set!, ht]) a haL
    · have hac : a = c := by
        rcases List.mem_cons.mp ha with h | h
        · exact h
        · exact absurd h haL
      subst hac
      rw [foldl_set_other f L _ _ fun b hb hba => haL (by rwa [← permKey_inj hba])]
      simp [Array.set!, Array.getElem?_setIfInBounds, ht, permKey_lt]

theorem flat_apply (p : Perm (Fin 6)) (i : Fin 6) : flat p i = p i := tabOf_getD p i

theorem mem_perms6 (a : Perm (Fin 6)) : a ∈ permsOfList (List.finRange 6) :=
  mem_permsOfList_of_mem fun x _ => List.mem_finRange x

theorem epsTable_get (a : Perm (Fin 6)) :
    ((permsOfList (List.finRange 6)).foldl (fun t a => t.set! (permKey a) (flat (epsPerm a)))
      (Array.replicate 46656 1))[permKey a]? = some (flat (epsPerm a)) :=
  foldl_set_mem (fun a => flat (epsPerm a)) _ _ Array.size_replicate a (mem_perms6 a)

theorem epsFast_eq (a : Perm (Fin 6)) :
    epsFast a = ((permsOfList (List.finRange 6)).foldl
      (fun t a => t.set! (permKey a) (flat (epsPerm a))) (Array.replicate 46656 1)).getD
        (permKey a) 1 := by
  rw [epsFast, epsTable]

theorem epsPerm_apply (a : Perm (Fin 6)) (i : Fin 6) :
    epsPerm a i = epsFun a i := by
  rw [epsPerm, MonoidHom.coe_mk, OneHom.coe_mk, epsEquiv_apply]

theorem epsFast_apply (a : Perm (Fin 6)) (i : Fin 6) :
    epsFast a i = epsFun a i := by
  rw [epsFast_eq, Array.getD_eq_getD_getElem?, epsTable_get, Option.getD_some, flat_apply,
    epsPerm_apply]

theorem conj_apply {σ a b : Perm (Fin 6)} (h : σ * a * σ⁻¹ = b) (j : Fin 6) :
    σ (a j) = b (σ j) := by
  have := congrArg (fun p : Perm (Fin 6) => p (σ j)) h
  simpa [Perm.mul_apply] using this

theorem epsFun_of (g : Perm (Fin 6)) (i j : Fin 6)
    (h : act (swap 0 j * g * swap 0 i) totalZero = totalZero) : epsFun g i = j := by
  apply total_injective
  rw [← act_total_epsFun, total, total, ← act_mul]
  have e : g * swap 0 i = swap 0 j * (swap 0 j * g * swap 0 i) := by
    rw [← mul_assoc, ← mul_assoc, swap_mul_self, one_mul]
  rw [e, act_mul, h]

theorem ex0 : act (swap 0 2 * (swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5) * swap 0 0) totalZero =
    totalZero := by decide +kernel

theorem ex2 : act (swap 0 3 * (swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5) * swap 0 2) totalZero =
    totalZero := by decide +kernel

theorem ey0 : act (swap 0 3 * (swap 0 1 * swap 2 3) * swap 0 0) totalZero = totalZero := by
  decide +kernel

theorem ey2 : act (swap 0 2 * (swap 0 1 * swap 2 3) * swap 0 2) totalZero = totalZero := by
  decide +kernel

theorem key_true : ∀ p : Fin 6,
    (swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5 : Perm (Fin 6))
        ((swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5 : Perm (Fin 6)) p) =
      (swap 0 1 * swap 2 3 : Perm (Fin 6)) p →
    (swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5 : Perm (Fin 6)) p =
      (swap 0 1 * swap 2 3 : Perm (Fin 6)) ((swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5 : Perm (Fin 6)) p) →
    p ≠ (swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5 : Perm (Fin 6))
        ((swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5 : Perm (Fin 6)) p) → False := by
  decide +kernel

theorem key_choice : ∀ p q : Fin 6,
    (swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5 : Perm (Fin 6)) p = (swap 0 1 * swap 2 3 : Perm (Fin 6)) p →
      p ≠ (swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5 : Perm (Fin 6))
        ((swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5 : Perm (Fin 6)) p) →
      q = (swap 0 1 * swap 2 3 : Perm (Fin 6)) q → (p = 0 ∨ p = 2) ∧ (q = 4 ∨ q = 5) := by
  decide +kernel

theorem fix_check (σ : Perm (Fin 6)) (b : Bool) :
    phi σ b (swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5) =
        swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5 →
      phi σ b (swap 0 1 * swap 2 3) = swap 0 1 * swap 2 3 →
        b = false ∧ (σ = 1 ∨ σ = swap 0 2 * swap 1 3 ∨ σ = swap 4 5 ∨
          σ = swap 0 2 * swap 1 3 * swap 4 5) := by
  set x : Perm (Fin 6) := swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5 with hxdef
  set y : Perm (Fin 6) := swap 0 1 * swap 2 3 with hydef
  intro hx hy
  cases b with
  | true =>
    exfalso
    have hx' : σ * epsFast x * σ⁻¹ = x := hx
    have hy' : σ * epsFast y * σ⁻¹ = y := hy
    have e0 : epsFast x 0 = 2 := by rw [epsFast_apply]; exact epsFun_of _ _ _ ex0
    have e2 : epsFast x 2 = 3 := by rw [epsFast_apply]; exact epsFun_of _ _ _ ex2
    have f0 : epsFast y 0 = 3 := by rw [epsFast_apply]; exact epsFun_of _ _ _ ey0
    have f2 : epsFast y 2 = 2 := by rw [epsFast_apply]; exact epsFun_of _ _ _ ey2
    have h2 : σ 2 = x (σ 0) := by rw [← e0, conj_apply hx']
    have h3 : σ 3 = x (σ 2) := by rw [← e2, conj_apply hx']
    have c1 : x (x (σ 0)) = y (σ 0) := by rw [← h2, ← h3, ← f0, conj_apply hy']
    have c3 : x (σ 0) = y (x (σ 0)) := by
      rw [← h2]
      have := conj_apply hy' 2
      rwa [f2] at this
    have c4 : σ 0 ≠ x (x (σ 0)) := by
      rw [← h2, ← h3]
      intro h
      exact absurd (σ.injective h) (by decide)
    exact key_true (σ 0) c1 c3 c4
  | false =>
    refine ⟨rfl, ?_⟩
    have hx' : σ * x * σ⁻¹ = x := hx
    have hy' : σ * y * σ⁻¹ = y := hy
    have hx0 : x 0 = 1 := by rw [hxdef]; decide
    have hx1 : x 1 = 2 := by rw [hxdef]; decide
    have hx2 : x 2 = 3 := by rw [hxdef]; decide
    have hx4 : x 4 = 5 := by rw [hxdef]; decide
    have hy0 : y 0 = 1 := by rw [hydef]; decide
    have hy4 : y 4 = 4 := by rw [hydef]; decide
    have h1 : σ 1 = x (σ 0) := by rw [← hx0, conj_apply hx']
    have h2 : σ 2 = x (σ 1) := by rw [← hx1, conj_apply hx']
    have h3 : σ 3 = x (σ 2) := by rw [← hx2, conj_apply hx']
    have h5 : σ 5 = x (σ 4) := by rw [← hx4, conj_apply hx']
    have hp1 : x (σ 0) = y (σ 0) := by rw [← h1, ← hy0, conj_apply hy']
    have hq : σ 4 = y (σ 4) := by
      have := conj_apply hy' 4
      rwa [hy4] at this
    have hp2 : σ 0 ≠ x (x (σ 0)) := by
      rw [← h1, ← h2]
      intro h
      exact absurd (σ.injective h) (by decide)
    obtain ⟨hp, hq'⟩ := key_choice (σ 0) (σ 4) hp1 hp2 hq
    have hval : ∀ τ : Perm (Fin 6), (∀ j : Fin 6, σ j = τ j) → σ = τ := fun τ h => Equiv.ext h
    rcases hp with h0 | h0 <;> rcases hq' with h4 | h4
    · left
      refine hval _ fun j => ?_
      rcases fin6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [h5, h3, h2, h1, h0, h4, hxdef] <;> decide
    · right; right; left
      refine hval _ fun j => ?_
      rcases fin6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [h5, h3, h2, h1, h0, h4, hxdef] <;> decide
    · right; left
      refine hval _ fun j => ?_
      rcases fin6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [h5, h3, h2, h1, h0, h4, hxdef] <;> decide
    · right; right; right
      refine hval _ fun j => ?_
      rcases fin6_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [h5, h3, h2, h1, h0, h4, hxdef] <;> decide

end CertificateChecks.Batch7131

namespace Certificates

open CertificateChecks

open CFSG.QuasithinUnique.Ch1.AltSix in
open Equiv Equiv.Perm in
theorem certificate7131 :
    ∀ (σ : Perm (Fin 6)) (b : Bool),
      phi σ b (swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5) =
          swap 0 1 * swap 1 2 * swap 2 3 * swap 4 5 →
        phi σ b (swap 0 1 * swap 2 3) = swap 0 1 * swap 2 3 →
          b = false ∧ (σ = 1 ∨ σ = swap 0 2 * swap 1 3 ∨ σ = swap 4 5 ∨
            σ = swap 0 2 * swap 1 3 * swap 4 5) := by
  exact CertificateChecks.Batch7131.fix_check

end Certificates
