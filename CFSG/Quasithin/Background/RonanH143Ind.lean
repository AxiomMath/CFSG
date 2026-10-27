module

public import CFSG.Quasithin.Background.RonanH143QL2

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH143

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf CFSG.Quasithin

def indwG1 : List ℕ :=
  [0, 4, 8, 12, 9, 13, 1, 5, 14, 10, 6, 2, 7, 3, 15, 11,
    28, 24, 20, 16, 21, 17, 29, 25, 18, 22, 26, 30, 27, 31, 19, 23]

def indwG2 : List ℕ :=
  [0, 2, 1, 3, 12, 14, 13, 15, 8, 10, 9, 11, 4, 6, 5, 7,
    16, 18, 17, 19, 28, 30, 29, 31, 24, 26, 25, 27, 20, 22, 21, 23]

def indwTab (F : List ℕ) (u : Fin 32) : Fin 32 :=
  ⟨(F.getD (u : ℕ) 0) % 32, Nat.mod_lt _ (by norm_num)⟩

theorem indw_conj_g1 :
    ∀ u : Fin 32, g1Perm * nq2Perm u * g1Perm⁻¹ = nq2Perm (indwTab indwG1 u) := by
  decide +kernel

theorem indw_conj_g2 :
    ∀ u : Fin 32, g2Perm * nq2Perm u * g2Perm⁻¹ = nq2Perm (indwTab indwG2 u) := by
  decide +kernel

def indwAdd (S : List (Fin 32)) (v : Fin 32) : List (Fin 32) :=
  if v ∈ S then S else S ++ S.map (fun s => xor32 s v)

def indwClos : ℕ → List (Fin 32) → List (Fin 32) → List (Fin 32)
  | 0, S, _ => S
  | _ + 1, S, [] => S
  | n + 1, S, v :: Q =>
    if v ∈ S then indwClos n S Q
    else indwClos n (indwAdd S v) (Q ++ [indwTab indwG1 v, indwTab indwG2 v])

theorem indwAdd_sound {P : Fin 32 → Prop} (hx : ∀ s t, P s → P t → P (xor32 s t))
    {S : List (Fin 32)} {v : Fin 32} (hS : ∀ s ∈ S, P s) (hv : P v) :
    ∀ x ∈ indwAdd S v, P x := by
  intro x hxS
  unfold indwAdd at hxS
  split_ifs at hxS with h
  · exact hS x hxS
  · rcases List.mem_append.1 hxS with h1 | h2
    · exact hS x h1
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.1 h2
      exact hx s v (hS s hs) hv

theorem indwClos_sound {P : Fin 32 → Prop} (hx : ∀ s t, P s → P t → P (xor32 s t))
    (h1 : ∀ u, P u → P (indwTab indwG1 u)) (h2 : ∀ u, P u → P (indwTab indwG2 u))
    (n : ℕ) :
    ∀ (S Q : List (Fin 32)), (∀ s ∈ S, P s) → (∀ v ∈ Q, P v) →
      ∀ x ∈ indwClos n S Q, P x := by
  induction n with
  | zero =>
    intro S Q hS _ x hxS
    exact hS x (by simpa [indwClos] using hxS)
  | succ n ih =>
    intro S Q hS hQ x hxS
    cases Q with
    | nil => exact hS x (by simpa [indwClos] using hxS)
    | cons v Q =>
      have hv : P v := hQ v (by simp)
      have hQ' : ∀ w ∈ Q, P w := fun w hw => hQ w (by simp [hw])
      simp only [indwClos] at hxS
      split_ifs at hxS with h
      · exact ih S Q hS hQ' x hxS
      · refine ih _ _ (indwAdd_sound hx hS hv) ?_ x hxS
        intro w hw
        rcases List.mem_append.1 hw with hw | hw
        · exact hQ' w hw
        · rcases List.mem_cons.1 hw with rfl | hw
          · exact h1 v hv
          · rw [List.mem_singleton.1 hw]
            exact h2 v hv

theorem indw_one_mem : ∀ u : Fin 32, u ≠ 0 → (1 : Fin 32) ∈ indwClos 16 [0] [u] := by
  decide +kernel

theorem indw_nq2_one_ne : nq2Perm 1 ≠ 1 := by
  intro h
  exact absurd (nq2Perm_injective (h.trans nq2Perm_zero.symm)) (by decide)

theorem indw_conj_mem {W : Subgroup P24} {c : P24} (h : conjSubg c W = W) {x : P24}
    (hx : x ∈ W) : c * x * c⁻¹ ∈ W := by
  have hmem : (MulAut.conj c).toMonoidHom x ∈ conjSubg c W := Subgroup.mem_map_of_mem _ hx
  rw [h] at hmem
  exact hmem

theorem indw_key {W : Subgroup P24} (hW : W ≤ NQ2)
    (hinv : ∀ g ∈ MY mog22plus Qstd, conjSubg g W = W) (hne : W ≠ ⊥) :
    nq2Perm 1 ∈ W := by
  obtain ⟨x, hxW, hx1⟩ := (Subgroup.bot_or_exists_ne_one W).resolve_left hne
  obtain ⟨u, rfl⟩ := mem_NQ2_iff.1 (hW hxW)
  have hu : u ≠ 0 := by
    rintro rfl
    exact hx1 nq2Perm_zero
  have hg1 : g1Perm ∈ MY mog22plus Qstd := g1Perm_mem_MY g1Perm_mem_mog22plus
  have hg2 : g2Perm ∈ MY mog22plus Qstd := g2Perm_mem_MY g2Perm_mem_mog22plus
  have hx : ∀ s t : Fin 32, nq2Perm s ∈ W → nq2Perm t ∈ W → nq2Perm (xor32 s t) ∈ W := by
    intro s t hs ht
    rw [← nq2Perm_mul s t]
    exact W.mul_mem hs ht
  have h1 : ∀ v : Fin 32, nq2Perm v ∈ W → nq2Perm (indwTab indwG1 v) ∈ W := by
    intro v hv
    rw [← indw_conj_g1 v]
    exact indw_conj_mem (hinv g1Perm hg1) hv
  have h2 : ∀ v : Fin 32, nq2Perm v ∈ W → nq2Perm (indwTab indwG2 v) ∈ W := by
    intro v hv
    rw [← indw_conj_g2 v]
    exact indw_conj_mem (hinv g2Perm hg2) hv
  have hS : ∀ s ∈ [(0 : Fin 32)], nq2Perm s ∈ W := by
    intro s hs
    rw [List.mem_singleton.1 hs, nq2Perm_zero]
    exact W.one_mem
  have hQ : ∀ v ∈ [u], nq2Perm v ∈ W := by
    intro v hv
    rw [List.mem_singleton.1 hv]
    exact hxW
  exact indwClos_sound (P := fun v => nq2Perm v ∈ W) hx h1 h2 16 [0] [u] hS hQ 1
    (indw_one_mem u hu)

theorem indecomposable_Q_L2 :
    ∀ W₁ W₂ : Subgroup P24, W₁ ≤ KY mog22plus Qstd → W₂ ≤ KY mog22plus Qstd →
      (∀ g ∈ MY mog22plus Qstd, conjSubg g W₁ = W₁) →
      (∀ g ∈ MY mog22plus Qstd, conjSubg g W₂ = W₂) →
      W₁ ⊔ W₂ = KY mog22plus Qstd → W₁ ⊓ W₂ = ⊥ → W₁ = ⊥ ∨ W₂ = ⊥ := by
  intro W₁ W₂ h₁ h₂ i₁ i₂ _ hmeet
  rw [KY_Q_L2] at h₁ h₂
  by_contra hcon
  rw [not_or] at hcon
  have hm : nq2Perm 1 ∈ W₁ ⊓ W₂ :=
    ⟨indw_key h₁ i₁ hcon.1, indw_key h₂ i₂ hcon.2⟩
  rw [hmeet, Subgroup.mem_bot] at hm
  exact indw_nq2_one_ne hm

end CFSG.Quasithin.RonanH143
