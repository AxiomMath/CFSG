module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin5

public section

namespace CFSG.Quasithin.F53.Stellmacher.S35.F2a

open Equiv CFSG.Quasithin CFSG.Quasithin.F53Mod CFSG.Quasithin.F53.Stellmacher.S35.Fin

theorem cj_mul (g h : Perm (Fin 5)) (B : Subgroup (Perm (Fin 5))) :
    cj (g * h) B = cj g (cj h B) := by
  ext σ
  simp only [mem_cj]
  have : (h⁻¹ * (g⁻¹ * σ * g) * h) = (g * h)⁻¹ * σ * (g * h) := by group
  rw [this]

theorem cj_one (B : Subgroup (Perm (Fin 5))) : cj 1 B = B := by
  ext σ; simp

theorem cj_inv_cj (g : Perm (Fin 5)) (B : Subgroup (Perm (Fin 5))) : cj g⁻¹ (cj g B) = B := by
  rw [← cj_mul, inv_mul_cancel, cj_one]

theorem cj_injective (g : Perm (Fin 5)) : Function.Injective (cj g) := fun A B h => by
  have := congrArg (cj g⁻¹) h
  rwa [cj_inv_cj, cj_inv_cj] at this

theorem cj_sup (g : Perm (Fin 5)) (A B : Subgroup (Perm (Fin 5))) :
    cj g (A ⊔ B) = cj g A ⊔ cj g B :=
  Subgroup.map_sup A B _

theorem cj_top (g : Perm (Fin 5)) : cj g (⊤ : Subgroup (Perm (Fin 5))) = ⊤ := by
  ext σ
  exact ⟨fun _ => trivial, fun _ => mem_cj.mpr trivial⟩

theorem cj_le_cj_iff (g : Perm (Fin 5)) {A B : Subgroup (Perm (Fin 5))} :
    cj g A ≤ cj g B ↔ A ≤ B := by
  constructor
  · intro h x hx
    exact mem_cj_conj.mp (h (mem_cj_conj.mpr hx))
  · intro h σ hσ
    rw [mem_cj] at hσ ⊢
    exact h hσ

theorem cj_ptStab (g : Perm (Fin 5)) (p : Fin 5) : cj g (ptStab p) = ptStab (g p) := by
  ext σ
  rw [mem_cj, mem_ptStab, mem_ptStab]
  simp only [Perm.mul_apply]
  constructor
  · intro h
    have h2 : g (g⁻¹ (σ (g p))) = g p := congrArg g (by simpa using h)
    simpa using h2
  · intro h
    simp [h]

theorem fixPt_cj {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) (g : Perm (Fin 5)) :
    fixPt (cj g D) = g (fixPt D) := by
  apply fixPt_eq (by rw [card_cj]; exact hD)
  rw [isFixPt_cj_iff]
  simpa using isFixPt_fixPt hD

theorem zc_cj {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) (g : Perm (Fin 5)) :
    zc (cj g D) = g * zc D * g⁻¹ := by
  apply zc_eq (by rw [card_cj]; exact hD)
  rw [isCentInv_cj_iff]
  have : g⁻¹ * (g * zc D * g⁻¹) * g = zc D := by group
  rw [this]; exact isCentInv_zc hD

theorem fixPt_std : fixPt S5Syl = 4 :=
  fixPt_eq card_S5Syl ((isFixPt_std_iff 4).mpr rfl)

theorem zc_std : zc S5Syl = zStd := zc_eq card_S5Syl ((isCentInv_std_iff zStd).mpr rfl)

theorem card_ptStab (p : Fin 5) : Nat.card (ptStab p) = 24 := by
  have h := Subgroup.card_mul_index (ptStab p)
  unfold ptStab at h
  rw [MulAction.index_stabilizer_of_transitive] at h
  have e : Nat.card (Perm (Fin 5)) = 120 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]; simp [Nat.factorial]
  have e5 : Nat.card (Fin 5) = 5 := by simp
  rw [e, e5] at h
  unfold ptStab
  omega

theorem le_ptStab_fixPt {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) :
    D ≤ ptStab (fixPt D) := le_ptStab (isFixPt_fixPt hD)

@[expose] def evalW (T : List (Perm (Fin 5))) (w : List ℕ) : Perm (Fin 5) :=
  (w.map fun i => T.getD i 1).prod

theorem evalW_mem (P : Subgroup (Perm (Fin 5))) {T : List (Perm (Fin 5))}
    (hT : ∀ t ∈ T, t ∈ P) (w : List ℕ) : evalW T w ∈ P := by
  unfold evalW
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
  by_cases hi : i < T.length
  · rw [List.getD_eq_getElem _ _ hi]; exact hT _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]; exact P.one_mem

theorem eq_top_of_adj (H : Subgroup (Perm (Fin 5))) (h0 : swap 0 1 ∈ H) (h1 : swap 1 2 ∈ H)
    (h2 : swap 2 3 ∈ H) (h3 : swap 3 4 ∈ H) : H = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hle : Submonoid.closure (Set.range fun i : Fin 4 => swap i.castSucc i.succ) ≤
      H.toSubmonoid := by
    rw [Submonoid.closure_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  have hx : x ∈ Submonoid.closure (Set.range fun i : Fin 4 => swap i.castSucc i.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]
    exact Submonoid.mem_top x
  exact hle hx

theorem eq_top_of_words (P : Subgroup (Perm (Fin 5))) {T : List (Perm (Fin 5))}
    (hT : ∀ t ∈ T, t ∈ P) (w0 w1 w2 w3 : List ℕ) (h0 : evalW T w0 = swap 0 1)
    (h1 : evalW T w1 = swap 1 2) (h2 : evalW T w2 = swap 2 3) (h3 : evalW T w3 = swap 3 4) :
    P = ⊤ :=
  eq_top_of_adj P (h0 ▸ evalW_mem P hT w0) (h1 ▸ evalW_mem P hT w1) (h2 ▸ evalW_mem P hT w2)
    (h3 ▸ evalW_mem P hT w3)

@[expose] def stepF (T X : Finset (Perm (Fin 5))) : Finset (Perm (Fin 5)) :=
  X ∪ X.biUnion fun x => T.image fun t => x * t

@[expose] def ballF (T : Finset (Perm (Fin 5))) : ℕ → Finset (Perm (Fin 5))
  | 0 => {1}
  | n + 1 => stepF T (ballF T n)

theorem ballF_subset (T : Finset (Perm (Fin 5))) (P : Subgroup (Perm (Fin 5)))
    (hT : ∀ t ∈ T, t ∈ P) (n : ℕ) : ∀ x ∈ ballF T n, x ∈ P := by
  induction n with
  | zero => intro x hx; simp only [ballF, Finset.mem_singleton] at hx; rw [hx]; exact P.one_mem
  | succ n ih =>
    intro x hx
    simp only [ballF, stepF, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image] at hx
    rcases hx with hx | ⟨y, hy, t, ht, rfl⟩
    · exact ih x hx
    · exact P.mul_mem (ih y hy) (hT t ht)

theorem closure_eq_ballF (T : Finset (Perm (Fin 5))) (n : ℕ) (hinv : ∀ t ∈ T, t⁻¹ ∈ T)
    (hfix : ∀ x ∈ ballF T n, ∀ t ∈ T, x * t ∈ ballF T n) :
    ((Subgroup.closure (T : Set (Perm (Fin 5))) : Subgroup (Perm (Fin 5))) :
      Set (Perm (Fin 5))) = (ballF T n : Set (Perm (Fin 5))) := by
  ext x
  constructor
  · intro hx
    have h : x ∈ ballF T n := by
      induction hx using Subgroup.closure_induction_right with
      | one =>
        clear hfix hinv
        induction n with
        | zero => simp [ballF]
        | succ n ih => simp only [ballF, stepF, Finset.mem_union]; exact Or.inl ih
      | mul_right x hx y hy ih => exact hfix x ih y hy
      | mul_inv_cancel x hx y hy ih => exact hfix x ih _ (hinv y hy)
    exact h
  · intro hx
    exact (Subgroup.closure_le _ |>.mpr fun t ht => Subgroup.subset_closure ht)
      (show x ∈ _ from by
        have := ballF_subset T (Subgroup.closure (T : Set (Perm (Fin 5))))
          (fun t ht => Subgroup.subset_closure ht) n x hx
        exact this)

theorem doubleCoset_cover : ∀ k : Perm (Fin 5), ∃ s ∈ S5SylF, ∃ t ∈ S5SylF,
    k = s * t ∨ k = s * swap 2 3 * t ∨ k = s * swap 3 4 * t ∨
      k = s * (swap 2 3 * swap 3 4) * t := by
  decide +kernel

theorem mem_S5SylF_of_conj : ∀ k : Perm (Fin 5), (∀ x ∈ S5SylF, k * x * k⁻¹ ∈ S5SylF) →
    k ∈ S5SylF := by
  decide +kernel

theorem cj_S5Syl_of_mem {k : Perm (Fin 5)} (hk : k ∈ S5Syl) : cj k S5Syl = S5Syl := by
  ext σ
  rw [mem_cj]
  constructor
  · intro h
    have := S5Syl.mul_mem (S5Syl.mul_mem hk h) (S5Syl.inv_mem hk)
    simpa [mul_assoc] using this
  · intro h
    exact S5Syl.mul_mem (S5Syl.mul_mem (S5Syl.inv_mem hk) h) hk

theorem cj_S5Syl_eq_iff {k : Perm (Fin 5)} : cj k S5Syl = S5Syl ↔ k ∈ S5Syl := by
  constructor
  · intro h
    rw [mem_S5Syl_iff]
    apply mem_S5SylF_of_conj
    intro x hx
    have h1 : k * x * k⁻¹ ∈ cj k S5Syl := mem_cj_conj.mpr ((mem_S5Syl_iff x).mpr hx)
    rw [h] at h1
    exact (mem_S5Syl_iff _).mp h1
  · exact cj_S5Syl_of_mem

@[expose] def r2 : Perm (Fin 5) := swap 2 3

@[expose] def r4 : Perm (Fin 5) := swap 3 4

@[expose] def r8 : Perm (Fin 5) := swap 2 3 * swap 3 4

theorem cj_dc (s t r : Perm (Fin 5)) (ht : t ∈ S5Syl) :
    cj (s * r * t) S5Syl = cj s (cj r S5Syl) := by
  rw [cj_mul, cj_mul, cj_S5Syl_of_mem ht]

theorem sylPair_cases {D E : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8)
    (hE : Nat.card E = 8) :
    ∃ g : Perm (Fin 5), D = cj g S5Syl ∧
      (E = cj g S5Syl ∨ E = cj g (cj r2 S5Syl) ∨ E = cj g (cj r4 S5Syl) ∨
        E = cj g (cj r8 S5Syl)) := by
  obtain ⟨g, rfl⟩ := exists_cj hD
  obtain ⟨h, rfl⟩ := exists_cj hE
  obtain ⟨s, hs, t, ht, hk⟩ := doubleCoset_cover (g⁻¹ * h)
  have hs' : s ∈ S5Syl := (mem_S5Syl_iff s).mpr hs
  have ht' : t ∈ S5Syl := (mem_S5Syl_iff t).mpr ht
  have hh : ∀ r : Perm (Fin 5), g⁻¹ * h = s * r * t → cj h S5Syl = cj (g * s) (cj r S5Syl) := by
    intro r hr
    have : h = g * (s * r * t) := by rw [← hr]; group
    rw [this, cj_mul g, cj_dc s t r ht', ← cj_mul]
  refine ⟨g * s, ?_, ?_⟩
  · rw [cj_mul, cj_S5Syl_of_mem hs']
  · rcases hk with hk | hk | hk | hk
    · left; rw [hh 1 (by rw [hk]; group), cj_one]
    · right; left; exact hh r2 (by rw [hk]; rfl)
    · right; right; left; exact hh r4 (by rw [hk]; rfl)
    · right; right; right; exact hh r8 (by rw [hk]; rfl)

end CFSG.Quasithin.F53.Stellmacher.S35.F2a
