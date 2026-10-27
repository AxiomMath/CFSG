module

public import CFSG.LocalAnalysis.StandardType.PhanEDMCoxeter

public section

namespace CoxeterSystem

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

@[expose] def conjInter (J K : Set B) (w₁ : W) : Set B :=
  {i | i ∈ J ∧ ∃ k ∈ K, cs.simple i * w₁ = w₁ * cs.simple k}

theorem conjInter_subset (J K : Set B) (w₁ : W) : cs.conjInter J K w₁ ⊆ J :=
  fun _ hi => hi.1

theorem exists_mul_eq_mul_of_mem_parabolic_conjInter {J K : Set B} {w₁ h : W}
    (hh : h ∈ cs.parabolic (cs.conjInter J K w₁)) :
    ∃ k ∈ cs.parabolic K, h * w₁ = w₁ * k := by
  let H : Subgroup W :=
    { carrier := {h : W | ∃ k ∈ cs.parabolic K, h * w₁ = w₁ * k}
      one_mem' := ⟨1, one_mem _, by simp⟩
      mul_mem' := by
        rintro h h' ⟨k, hk, hk_eq⟩ ⟨k', hk', hk'_eq⟩
        exact ⟨k * k', mul_mem hk hk',
          by rw [mul_assoc, hk'_eq, ← mul_assoc, hk_eq, mul_assoc]⟩
      inv_mem' := by
        rintro h ⟨k, hk, hk_eq⟩
        refine ⟨k⁻¹, inv_mem hk, ?_⟩
        have h1 : w₁ = h⁻¹ * w₁ * k := by
          rw [mul_assoc, ← hk_eq, ← mul_assoc, inv_mul_cancel, one_mul]
        calc h⁻¹ * w₁ = h⁻¹ * w₁ * k * k⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]
          _ = w₁ * k⁻¹ := by rw [← h1] }
  have hle : cs.parabolic (cs.conjInter J K w₁) ≤ H := by
    rw [cs.parabolic_le_iff]
    intro i hi
    obtain ⟨-, k, hk, hik⟩ := hi
    exact ⟨cs.simple k, cs.simple_mem_parabolic hk, hik⟩
  exact hle hh

theorem mem_parabolic_conjInter_of_mul_eq_mul {J K : Set B} {w₁ : W}
    (hw₁ : cs.IsMinimalDoubleCosetRep J K w₁) {h k : W} (hh : h ∈ cs.parabolic J)
    (hk : k ∈ cs.parabolic K) (hmul : h * w₁ = w₁ * k) :
    h ∈ cs.parabolic (cs.conjInter J K w₁) := by
  obtain ⟨hR, hL⟩ := (cs.isMinimalDoubleCosetRep_iff (K := J) (J := K)).mp hw₁
  have hlen_a : ∀ x : W, x ∈ cs.parabolic J →
      cs.length (x * w₁) = cs.length x + cs.length w₁ :=
    fun x hx => cs.length_mul_of_forall_not_isLeftDescent hx hL
  have hmin : cs.IsMinimalCosetRep K w₁ := (cs.isMinimalCosetRep_iff (J := K)).mpr hR
  have hlen_b : ∀ y : W, y ∈ cs.parabolic K →
      cs.length (w₁ * y) = cs.length w₁ + cs.length y :=
    fun y hy => cs.length_mul_of_isMinimalCosetRep hmin hy
  suffices main : ∀ n : ℕ, ∀ h k : W, cs.length h = n → h ∈ cs.parabolic J →
      k ∈ cs.parabolic K → h * w₁ = w₁ * k → h ∈ cs.parabolic (cs.conjInter J K w₁) by
    exact main _ h k rfl hh hk hmul
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro h k hlen hh hk hmul
    rcases eq_or_ne h 1 with rfl | hne
    · exact one_mem _
    obtain ⟨i, hiJ, hdesc_inv⟩ :=
      cs.exists_rightDescent_mem_of_mem_parabolic_of_ne_one (inv_mem hh) (inv_ne_one.mpr hne)
    have hdesc : cs.IsLeftDescent h i := cs.isRightDescent_inv_iff.mp hdesc_inv
    obtain ⟨α, hαred, hα⟩ := cs.exists_isReduced w₁
    obtain ⟨β, hβred, hβK, hβ⟩ := cs.exists_isReduced_wordProd_eq_of_mem_parabolic hk
    have hαlen : α.length = cs.length w₁ := ((congrArg cs.length hα).trans hαred.eq).symm
    have hβlen : β.length = cs.length k :=
      (hβred.eq.symm).trans (congrArg cs.length hβ)
    have hcat_red : cs.IsReduced (α ++ β) := by
      show cs.length (cs.wordProd (α ++ β)) = (α ++ β).length
      rw [cs.wordProd_append, ← hα, hβ, hlen_b k hk, List.length_append, hαlen, hβlen]
    have hdesccat : cs.IsLeftDescent (cs.wordProd (α ++ β)) i := by
      show cs.length (cs.simple i * cs.wordProd (α ++ β)) <
        cs.length (cs.wordProd (α ++ β))
      rw [cs.wordProd_append, ← hα, hβ, ← hmul, ← mul_assoc]
      have hh' : cs.simple i * h ∈ cs.parabolic J :=
        mul_mem (s := cs.parabolic J) (a := cs.simple i) (b := h)
          (cs.simple_mem_parabolic hiJ) hh
      rw [hlen_a (cs.simple i * h) hh', hlen_a h hh]
      have := cs.isLeftDescent_iff.mp hdesc
      omega
    obtain ⟨j, hj, hje, -⟩ := cs.exchangeCondition hcat_red hdesccat
    rcases Nat.lt_or_ge j α.length with hjα | hjα
    ·
      exfalso
      have hsiw1 : cs.simple i * w₁ = cs.wordProd (α.eraseIdx j) := by
        have hLHS : cs.simple i * cs.wordProd (α ++ β) = cs.simple i * w₁ * k := by
          rw [cs.wordProd_append, ← hα, hβ, mul_assoc]
        have hRHS : cs.wordProd ((α ++ β).eraseIdx j) = cs.wordProd (α.eraseIdx j) * k := by
          rw [List.eraseIdx_append_of_lt_length hjα β, cs.wordProd_append, hβ]
        have hsik : cs.simple i * w₁ * k = cs.wordProd (α.eraseIdx j) * k := by
          rw [← hLHS, hje, hRHS]
        exact mul_right_cancel hsik
      have hnot : cs.length (cs.simple i * w₁) = cs.length w₁ + 1 :=
        cs.not_isLeftDescent_iff.mp (hL i hiJ)
      have hle : cs.length (cs.simple i * w₁) ≤ α.length - 1 := by
        rw [hsiw1]
        calc cs.length (cs.wordProd (α.eraseIdx j)) ≤ (α.eraseIdx j).length :=
              cs.length_wordProd_le _
          _ = α.length - 1 := List.length_eraseIdx_of_lt hjα
      omega
    ·
      set k' : W := cs.wordProd (β.eraseIdx (j - α.length)) with hk'def
      have hLHS : cs.simple i * cs.wordProd (α ++ β) = cs.simple i * w₁ * k := by
        rw [cs.wordProd_append, ← hα, hβ, mul_assoc]
      have hRHS : cs.wordProd ((α ++ β).eraseIdx j) = w₁ * k' := by
        rw [List.eraseIdx_append_of_length_le hjα β, cs.wordProd_append, ← hα, ← hk'def]
      have hsik : cs.simple i * w₁ * k = w₁ * k' := by
        rw [← hLHS, hje, hRHS]
      have hk'mem : k' ∈ cs.parabolic K := by
        rw [hk'def]
        exact cs.wordProd_mem_parabolic
          (fun a ha => hβK a ((List.eraseIdx_sublist β (j - α.length)).subset ha))
      have hk''mem : k' * k⁻¹ ∈ cs.parabolic K := mul_mem hk'mem (inv_mem hk)
      have hkey : cs.simple i * w₁ = w₁ * (k' * k⁻¹) := by
        have h₁ : (cs.simple i * w₁) * k = (w₁ * (k' * k⁻¹)) * k := by
          rw [hsik]; group
        exact mul_right_cancel h₁
      have hsix : cs.length (cs.simple i * w₁) = cs.length w₁ + 1 :=
        cs.not_isLeftDescent_iff.mp (hL i hiJ)
      have hk''len : cs.length (k' * k⁻¹) = 1 := by
        have hlenb := hlen_b (k' * k⁻¹) hk''mem
        rw [← hkey, hsix] at hlenb
        omega
      obtain ⟨j', hj'K, hsj'⟩ : ∃ j' ∈ K, k' * k⁻¹ = cs.simple j' := by
        obtain ⟨ω, hωred, hωK, hωprod⟩ :=
          cs.exists_isReduced_wordProd_eq_of_mem_parabolic hk''mem
        have hωlen : ω.length = 1 := by
          rw [← hωred.eq, hωprod, hk''len]
        rcases List.length_eq_one_iff.mp hωlen with ⟨j', rfl⟩
        exact ⟨j', hωK j' (by simp), by rw [← hωprod, cs.wordProd_singleton]⟩
      have hconj : cs.simple i * w₁ = w₁ * cs.simple j' := by
        rw [← hsj']; exact hkey
      have hiConj : i ∈ cs.conjInter J K w₁ := ⟨hiJ, j', hj'K, hconj⟩
      have hh' : cs.simple i * h ∈ cs.parabolic J :=
        mul_mem (s := cs.parabolic J) (a := cs.simple i) (b := h)
          (cs.simple_mem_parabolic hiJ) hh
      have hknew : cs.simple j' * k ∈ cs.parabolic K :=
        mul_mem (s := cs.parabolic K) (a := cs.simple j') (b := k)
          (cs.simple_mem_parabolic hj'K) hk
      have hmul' : (cs.simple i * h) * w₁ = w₁ * (cs.simple j' * k) := by
        rw [mul_assoc, hmul, ← mul_assoc, hconj, mul_assoc]
      have hlt : cs.length (cs.simple i * h) < n := by
        have := cs.isLeftDescent_iff.mp hdesc
        rw [hlen] at this
        omega
      have ih' := ih (cs.length (cs.simple i * h)) hlt (cs.simple i * h) (cs.simple j' * k)
        rfl hh' hknew hmul'
      have hdecomp : h = cs.simple i * (cs.simple i * h) :=
        (cs.simple_mul_simple_cancel_left (w := h) i).symm
      rw [hdecomp]
      exact mul_mem (cs.simple_mem_parabolic hiConj) ih'

end CoxeterSystem

end
