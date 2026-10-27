module

public import CFSG.Sporadic.Recognition.LyonsLocalNormalizerE

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Equiv Equiv.Perm Subgroup

@[expose] def A3 {G : Type*} [Group G] (a b c : G) : Subgroup G :=
  Subgroup.closure ({a, b, c} : Set G)

@[expose] def Q3 {G : Type*} [Group G] (a b c : G) : Subgroup G := centralizer ({a, b, c} : Set G)

theorem mem_Q3 {G : Type*} [Group G] {a b c g : G} :
    g ∈ Q3 a b c ↔ a * g = g * a ∧ b * g = g * b ∧ c * g = g * c := by
  simp [Q3, mem_centralizer_iff]

theorem Q3_le_normalizer_A3 {G : Type*} [Group G] (a b c : G) :
    Q3 a b c ≤ normalizer (A3 a b c : Set G) := by
  have h : Q3 a b c = centralizer ((A3 a b c : Subgroup G) : Set G) := by
    rw [A3, Subgroup.centralizer_closure]; rfl
  rw [h]
  exact Subgroup.centralizer_le_normalizer _

section Lift

variable {G : Type} [Group G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}

@[expose] def e6H (x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))) :
    Fin 6 → ↥(centralizer ({t} : Set G)) := ![x₁, x₁⁻¹, x₂, x₂⁻¹, x₃, x₃⁻¹]

theorem rho_e6H (S : LyStd ρ x₁ x₂ x₃) (i : Fin 6) : ρ (e6H x₁ x₂ x₃ i) = e6p i := by
  fin_cases i <;> simp [e6H, e6p, S.rho₁, S.rho₂, S.rho₃]

theorem pow_e6H (S : LyStd ρ x₁ x₂ x₃) (i : Fin 6) : (e6H x₁ x₂ x₃ i) ^ 3 = 1 := by
  fin_cases i
  · exact S.pow₁
  · simp [e6H, inv_pow, S.pow₁]
  · exact S.pow₂
  · simp [e6H, inv_pow, S.pow₂]
  · exact S.pow₃
  · simp [e6H, inv_pow, S.pow₃]

theorem e6p_injective : Function.Injective e6p := by decide

theorem e6H_injective (S : LyStd ρ x₁ x₂ x₃) : Function.Injective (e6H x₁ x₂ x₃) := by
  intro i j h
  apply e6p_injective
  rw [← rho_e6H S, ← rho_e6H S, h]

theorem e6H_axis (i j : Fin 6) (h : i.val / 2 = j.val / 2) (a b c : ↥(centralizer ({t} : Set G))) :
    e6H a b c j = e6H a b c i ∨ e6H a b c j = (e6H a b c i)⁻¹ := by
  fin_cases i <;> fin_cases j <;> simp [e6H] at h ⊢

theorem e6H_mem_A3 (i : Fin 6) : (e6H x₁ x₂ x₃ i : G) ∈ A3 (x₁ : G) (x₂ : G) (x₃ : G) := by
  fin_cases i
  · exact Subgroup.subset_closure (by simp [e6H])
  · exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))
  · exact Subgroup.subset_closure (by simp [e6H])
  · exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))
  · exact Subgroup.subset_closure (by simp [e6H])
  · exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))

theorem exists_e6H_of_six {u : G}
    (h : u = (x₁ : G) ∨ u = (x₁ : G)⁻¹ ∨ u = (x₂ : G) ∨ u = (x₂ : G)⁻¹ ∨ u = (x₃ : G) ∨
      u = (x₃ : G)⁻¹) : ∃ i : Fin 6, u = (e6H x₁ x₂ x₃ i : G) := by
  rcases h with h | h | h | h | h | h
  · exact ⟨0, by simp [e6H, h]⟩
  · exact ⟨1, by simp [e6H, h]⟩
  · exact ⟨2, by simp [e6H, h]⟩
  · exact ⟨3, by simp [e6H, h]⟩
  · exact ⟨4, by simp [e6H, h]⟩
  · exact ⟨5, by simp [e6H, h]⟩

theorem ne_of_e6H (S : LyStd ρ x₁ x₂ x₃) :
    (x₂ : G) ≠ (x₁ : G) ∧ (x₂ : G) ≠ (x₁ : G)⁻¹ ∧ (x₃ : G) ≠ (x₁ : G) ∧
      (x₃ : G) ≠ (x₁ : G)⁻¹ ∧ (x₃ : G) ≠ (x₂ : G) ∧ (x₃ : G) ≠ (x₂ : G)⁻¹ := by
  have hinj := fun i j (h : (e6H x₁ x₂ x₃ i : G) = e6H x₁ x₂ x₃ j) =>
    e6H_injective S (Subtype.val_injective h)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; exact absurd (hinj 2 0 h) (by decide)
  · intro h; exact absurd (hinj 2 1 h) (by decide)
  · intro h; exact absurd (hinj 4 0 h) (by decide)
  · intro h; exact absurd (hinj 4 1 h) (by decide)
  · intro h; exact absurd (hinj 4 2 h) (by decide)
  · intro h; exact absurd (hinj 4 3 h) (by decide)

namespace LyData

variable [Finite G]

theorem exists_lift_pA (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) (m : Fin 48) :
    ∃ w : ↥(centralizer ({t} : Set G)),
      (w : G) ∈ normalizer (A3 (x₁ : G) (x₂ : G) (x₃ : G) : Set G) ∧
      (w : G) * (x₁ : G) * (w : G)⁻¹ = (e6H x₁ x₂ x₃ (iA m).1 : G) ∧
      (w : G) * (x₂ : G) * (w : G)⁻¹ = (e6H x₁ x₂ x₃ (iA m).2.1 : G) ∧
      (w : G) * (x₃ : G) * (w : G)⁻¹ = (e6H x₁ x₂ x₃ (iA m).2.2 : G) := by
  obtain ⟨w, hw⟩ := D.cover.exists_lift (sign_pA m)
  have hc := pA_conj m
  have h1 := D.conj_eq_of_rho S.pow₁ (pow_e6H S _) (by rw [hw, S.rho₁, rho_e6H S]; exact hc.1)
  have h2 := D.conj_eq_of_rho S.pow₂ (pow_e6H S _) (by rw [hw, S.rho₂, rho_e6H S]; exact hc.2.1)
  have h3 := D.conj_eq_of_rho S.pow₃ (pow_e6H S _) (by rw [hw, S.rho₃, rho_e6H S]; exact hc.2.2)
  have h1G : (w : G) * (x₁ : G) * (w : G)⁻¹ = (e6H x₁ x₂ x₃ (iA m).1 : G) := by
    have := congrArg Subtype.val h1; simpa using this
  have h2G : (w : G) * (x₂ : G) * (w : G)⁻¹ = (e6H x₁ x₂ x₃ (iA m).2.1 : G) := by
    have := congrArg Subtype.val h2; simpa using this
  have h3G : (w : G) * (x₃ : G) * (w : G)⁻¹ = (e6H x₁ x₂ x₃ (iA m).2.2 : G) := by
    have := congrArg Subtype.val h3; simpa using this
  refine ⟨w, ?_, h1G, h2G, h3G⟩
  refine McLAS.mem_normalizer_closure (S := ({(x₁ : G), (x₂ : G), (x₃ : G)} : Set G)) ?_
  intro g hg
  have hg' : g = (x₁ : G) ∨ g = (x₂ : G) ∨ g = (x₃ : G) := by simpa using hg
  rcases hg' with rfl | rfl | rfl
  · rw [h1G]; exact e6H_mem_A3 _
  · rw [h2G]; exact e6H_mem_A3 _
  · rw [h3G]; exact e6H_mem_A3 _

omit [Finite G] in
theorem isConj_x₂_x₃ (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) : IsConj (x₂ : G) (x₃ : G) := by
  obtain ⟨u, hu₂, -, -, -⟩ := D.exists_swap23 S
  refine isConj_iff.2 ⟨(u : G), ?_⟩
  have := congrArg Subtype.val hu₂
  simpa using this

theorem exists_pA_of_mem_normalizer (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) {n : G}
    (hn : n ∈ normalizer (A3 (x₁ : G) (x₂ : G) (x₃ : G) : Set G)) :
    ∃ m : Fin 48, n * (x₁ : G) * n⁻¹ = (e6H x₁ x₂ x₃ (iA m).1 : G) ∧
      n * (x₂ : G) * n⁻¹ = (e6H x₁ x₂ x₃ (iA m).2.1 : G) ∧
      n * (x₃ : G) * n⁻¹ = (e6H x₁ x₂ x₃ (iA m).2.2 : G) := by
  have hmem : ∀ y, y ∈ ({(x₁ : G), (x₂ : G), (x₃ : G)} : Set G) →
      n * y * n⁻¹ ∈ A3 (x₁ : G) (x₂ : G) (x₃ : G) := fun y hy =>
    (mem_normalizer_iff.1 hn y).1 (Subgroup.subset_closure hy)
  have h12 := D.isConj_x₁_x₂ S
  have h23 := D.isConj_x₂_x₃ S
  obtain ⟨i, hi⟩ := exists_e6H_of_six (D.eq_of_isConj_mem_closure_three S
    (hmem _ (by simp)) (isConj_iff.2 ⟨n, rfl⟩))
  obtain ⟨j, hj⟩ := exists_e6H_of_six (D.eq_of_isConj_mem_closure_three S
    (hmem _ (by simp)) (h12.trans (isConj_iff.2 ⟨n, rfl⟩)))
  obtain ⟨k, hk⟩ := exists_e6H_of_six (D.eq_of_isConj_mem_closure_three S
    (hmem _ (by simp)) ((h12.trans h23).trans (isConj_iff.2 ⟨n, rfl⟩)))
  have hne := ne_of_e6H S
  have hconj_ne : ∀ y z : G, z ≠ y → z ≠ y⁻¹ →
      n * z * n⁻¹ ≠ n * y * n⁻¹ ∧ n * z * n⁻¹ ≠ (n * y * n⁻¹)⁻¹ := by
    intro y z h1 h2
    refine ⟨fun h => h1 (mul_left_cancel (mul_right_cancel h)), fun h => h2 ?_⟩
    have h' : n * z * n⁻¹ = n * y⁻¹ * n⁻¹ := by rw [h]; group
    exact mul_left_cancel (mul_right_cancel h')
  have hax : ∀ (a b : Fin 6), (e6H x₁ x₂ x₃ b : G) ≠ (e6H x₁ x₂ x₃ a : G) →
      (e6H x₁ x₂ x₃ b : G) ≠ ((e6H x₁ x₂ x₃ a : G))⁻¹ → a.val / 2 ≠ b.val / 2 := by
    intro a b h1 h2 hab
    rcases e6H_axis a b hab x₁ x₂ x₃ with h | h
    · exact h1 (by rw [h])
    · exact h2 (by rw [h]; simp)
  have hij : i.val / 2 ≠ j.val / 2 := by
    apply hax
    · rw [← hi, ← hj]; exact (hconj_ne _ _ hne.1 hne.2.1).1
    · rw [← hi, ← hj]; exact (hconj_ne _ _ hne.1 hne.2.1).2
  have hik : i.val / 2 ≠ k.val / 2 := by
    apply hax
    · rw [← hi, ← hk]; exact (hconj_ne _ _ hne.2.2.1 hne.2.2.2.1).1
    · rw [← hi, ← hk]; exact (hconj_ne _ _ hne.2.2.1 hne.2.2.2.1).2
  have hjk : j.val / 2 ≠ k.val / 2 := by
    apply hax
    · rw [← hj, ← hk]; exact (hconj_ne _ _ hne.2.2.2.2.1 hne.2.2.2.2.2).1
    · rw [← hj, ← hk]; exact (hconj_ne _ _ hne.2.2.2.2.1 hne.2.2.2.2.2).2
  obtain ⟨m, hm⟩ := iA_surjective i j k hij hik hjk
  refine ⟨m, ?_, ?_, ?_⟩
  · rw [hm]; exact hi
  · rw [hm]; exact hj
  · rw [hm]; exact hk

theorem normalizer_A3_eq_mul (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    ∀ n ∈ normalizer (A3 (x₁ : G) (x₂ : G) (x₃ : G) : Set G),
      ∃ h ∈ normalizer (A3 (x₁ : G) (x₂ : G) (x₃ : G) : Set G) ⊓ centralizer ({t} : Set G),
        ∃ q ∈ Q3 (x₁ : G) (x₂ : G) (x₃ : G), n = h * q := by
  intro n hn
  obtain ⟨m, hm1, hm2, hm3⟩ := D.exists_pA_of_mem_normalizer S hn
  obtain ⟨w, hwN, hw1, hw2, hw3⟩ := D.exists_lift_pA S m
  have key : ∀ a b : G, n * a * n⁻¹ = b → (w : G) * a * (w : G)⁻¹ = b →
      a * ((w : G)⁻¹ * n) = ((w : G)⁻¹ * n) * a := by
    intro a b h1 h2
    have h3 : (w : G)⁻¹ * n * a * ((w : G)⁻¹ * n)⁻¹ = a := by
      calc (w : G)⁻¹ * n * a * ((w : G)⁻¹ * n)⁻¹ = (w : G)⁻¹ * (n * a * n⁻¹) * (w : G) := by
            group
        _ = (w : G)⁻¹ * ((w : G) * a * (w : G)⁻¹) * (w : G) := by rw [h1, h2]
        _ = a := by group
    exact (mul_inv_eq_iff_eq_mul.1 h3).symm
  refine ⟨(w : G), ⟨hwN, w.2⟩, (w : G)⁻¹ * n, ?_, by group⟩
  rw [mem_Q3]
  exact ⟨key _ _ hm1 hw1, key _ _ hm2 hw2, key _ _ hm3 hw3⟩

theorem card_normalizer_A3 (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    Nat.card ↥(normalizer (A3 (x₁ : G) (x₂ : G) (x₃ : G) : Set G)) =
      48 * Nat.card ↥(Q3 (x₁ : G) (x₂ : G) (x₃ : G)) := by
  classical
  let a : Fin 3 → G := ![(x₁ : G), (x₂ : G), (x₃ : G)]
  have hrange : Set.range a = {(x₁ : G), (x₂ : G), (x₃ : G)} := by
    ext g
    simp [a, or_comm, or_left_comm]
  let gT : Fin 48 → (Fin 3 → G) := fun m =>
    ![(e6H x₁ x₂ x₃ (iA m).1 : G), (e6H x₁ x₂ x₃ (iA m).2.1 : G),
      (e6H x₁ x₂ x₃ (iA m).2.2 : G)]
  have hgT : Function.Injective gT := by
    intro m m' h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp only [gT, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
    apply iA_injective
    exact Prod.ext (e6H_injective S (Subtype.val_injective h0))
      (Prod.ext (e6H_injective S (Subtype.val_injective h1))
        (e6H_injective S (Subtype.val_injective h2)))
  let T : Finset (Fin 3 → G) := Finset.univ.image gT
  have hTcard : T.card = 48 := by
    rw [Finset.card_image_of_injective _ hgT]; simp
  choose w hwN hw using fun m => D.exists_lift_pA S m
  have hconj : ∀ m, (fun i => (w m : G) * a i * (w m : G)⁻¹) = gT m := by
    intro m
    funext i
    fin_cases i
    · exact (hw m).1
    · exact (hw m).2.1
    · exact (hw m).2.2
  have hT : ∀ n ∈ normalizer (A3 (x₁ : G) (x₂ : G) (x₃ : G) : Set G),
      (fun i => n * a i * n⁻¹) ∈ T := by
    intro n hn
    obtain ⟨m, hm1, hm2, hm3⟩ := D.exists_pA_of_mem_normalizer S hn
    refine Finset.mem_image.2 ⟨m, Finset.mem_univ _, ?_⟩
    funext k
    fin_cases k
    · exact hm1.symm
    · exact hm2.symm
    · exact hm3.symm
  have hmain := card_eq_mul_card_of_conj_tuples
    (normalizer (A3 (x₁ : G) (x₂ : G) (x₃ : G) : Set G)) a T hT hTcard (fun m => (w m : G)) hwN
    (by
      intro m m' h
      apply hgT
      rw [← hconj m, ← hconj m']
      exact h)
  have hinf : normalizer (A3 (x₁ : G) (x₂ : G) (x₃ : G) : Set G) ⊓
      centralizer ({(x₁ : G), (x₂ : G), (x₃ : G)} : Set G) = Q3 (x₁ : G) (x₂ : G) (x₃ : G) :=
    inf_eq_right.2 (Q3_le_normalizer_A3 _ _ _)
  rw [hmain, hrange, hinf]

end LyData

end Lift

end CFSG.Sporadic.Recognition.LyonsSims
