module

public import CFSG.Sporadic.Recognition.LyonsLocalCentralizerE
public import CFSG.Sporadic.Recognition.LyonsLocalMonomial
public import CFSG.Sporadic.Recognition.LyonsLocalOrbit
public import CFSG.Sporadic.Recognition.LyonsLocalTorus

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Equiv Equiv.Perm Subgroup

section Lift

variable {G : Type} [Group G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}

@[expose] def e4H (x₁ x₂ : ↥(centralizer ({t} : Set G))) : Fin 4 → ↥(centralizer ({t} : Set G)) :=
  ![x₁, x₁⁻¹, x₂, x₂⁻¹]

theorem rho_e4H (S : LyStd ρ x₁ x₂ x₃) (i : Fin 4) : ρ (e4H x₁ x₂ i) = e4p i := by
  fin_cases i <;> simp [e4H, e4p, S.rho₁, S.rho₂]

theorem pow_e4H (S : LyStd ρ x₁ x₂ x₃) (i : Fin 4) : (e4H x₁ x₂ i) ^ 3 = 1 := by
  fin_cases i
  · exact S.pow₁
  · simp [e4H, inv_pow, S.pow₁]
  · exact S.pow₂
  · simp [e4H, inv_pow, S.pow₂]

theorem e4p_injective : Function.Injective e4p := by decide

theorem e4H_injective (S : LyStd ρ x₁ x₂ x₃) : Function.Injective (e4H x₁ x₂) := by
  intro i j h
  apply e4p_injective
  rw [← rho_e4H S, ← rho_e4H S, h]

omit [Group G] in
theorem e4p_axis (i j : Fin 4) (h : i.val / 2 = j.val / 2) :
    e4p j = e4p i ∨ e4p j = (e4p i)⁻¹ := by
  revert h
  revert i j
  decide

namespace LyData

theorem exists_lift_pE (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) (m : Fin 8) :
    ∃ w : ↥(centralizer ({t} : Set G)), w * x₁ * w⁻¹ = e4H x₁ x₂ (iE m).1 ∧
      w * x₂ * w⁻¹ = e4H x₁ x₂ (iE m).2 := by
  obtain ⟨w, hw⟩ := D.cover.exists_lift (sign_pE m)
  refine ⟨w, D.conj_eq_of_rho S.pow₁ (pow_e4H S _) ?_, D.conj_eq_of_rho S.pow₂ (pow_e4H S _) ?_⟩
  · rw [hw, S.rho₁, rho_e4H S]; exact (pE_conj m).1
  · rw [hw, S.rho₂, rho_e4H S]; exact (pE_conj m).2

end LyData

end Lift

@[expose] def EE {G : Type*} [Group G] (a b : G) : Subgroup G := Subgroup.closure ({a, b} : Set G)

theorem QE_le_normalizer_EE {G : Type*} [Group G] (a b : G) :
    QE a b ≤ normalizer (EE a b : Set G) := by
  have h : QE a b = centralizer ((EE a b : Subgroup G) : Set G) := by
    rw [EE, Subgroup.centralizer_closure]; rfl
  rw [h]
  exact Subgroup.centralizer_le_normalizer _

section Count

variable {G : Type} [Group G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}

theorem e4H_axis (i j : Fin 4) (h : i.val / 2 = j.val / 2) (a b : ↥(centralizer ({t} : Set G))) :
    e4H a b j = e4H a b i ∨ e4H a b j = (e4H a b i)⁻¹ := by
  fin_cases i <;> fin_cases j <;> simp [e4H] at h ⊢

theorem e4H_mem_EE (i : Fin 4) :
    (e4H x₁ x₂ i : G) ∈ EE (x₁ : G) (x₂ : G) := by
  fin_cases i
  · exact Subgroup.subset_closure (by simp [e4H])
  · exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))
  · exact Subgroup.subset_closure (by simp [e4H])
  · exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))

theorem exists_e4H_of_four {u : G}
    (h : u = (x₁ : G) ∨ u = (x₁ : G)⁻¹ ∨ u = (x₂ : G) ∨ u = (x₂ : G)⁻¹) :
    ∃ i : Fin 4, u = (e4H x₁ x₂ i : G) := by
  rcases h with h | h | h | h
  · exact ⟨0, by simp [e4H, h]⟩
  · exact ⟨1, by simp [e4H, h]⟩
  · exact ⟨2, by simp [e4H, h]⟩
  · exact ⟨3, by simp [e4H, h]⟩

theorem ne_of_e4H (S : LyStd ρ x₁ x₂ x₃) :
    (x₂ : G) ≠ (x₁ : G) ∧ (x₂ : G) ≠ (x₁ : G)⁻¹ := by
  constructor
  · intro h
    have := e4H_injective S (Subtype.val_injective (show (e4H x₁ x₂ 2 : G) = e4H x₁ x₂ 0 from h))
    exact absurd this (by decide)
  · intro h
    have := e4H_injective S (Subtype.val_injective (show (e4H x₁ x₂ 2 : G) = e4H x₁ x₂ 1 from h))
    exact absurd this (by decide)

variable [Finite G]

omit [Finite G] in
theorem LyData.isConj_x₁_x₂ (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    IsConj (x₁ : G) (x₂ : G) := by
  obtain ⟨s, hs₁, -, -, -⟩ := D.exists_swap S
  refine isConj_iff.2 ⟨(s : G), ?_⟩
  have := congrArg Subtype.val hs₁
  simpa using this

theorem LyData.exists_lift_pE_normalizer (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) (m : Fin 8) :
    ∃ w : ↥(centralizer ({t} : Set G)), (w : G) ∈ normalizer (EE (x₁ : G) (x₂ : G) : Set G) ∧
      (w : G) * (x₁ : G) * (w : G)⁻¹ = (e4H x₁ x₂ (iE m).1 : G) ∧
      (w : G) * (x₂ : G) * (w : G)⁻¹ = (e4H x₁ x₂ (iE m).2 : G) := by
  obtain ⟨w, hw1, hw2⟩ := D.exists_lift_pE S m
  have h1 : (w : G) * (x₁ : G) * (w : G)⁻¹ = (e4H x₁ x₂ (iE m).1 : G) := by
    have := congrArg Subtype.val hw1; simpa using this
  have h2 : (w : G) * (x₂ : G) * (w : G)⁻¹ = (e4H x₁ x₂ (iE m).2 : G) := by
    have := congrArg Subtype.val hw2; simpa using this
  refine ⟨w, ?_, h1, h2⟩
  refine McLAS.mem_normalizer_closure (S := ({(x₁ : G), (x₂ : G)} : Set G)) ?_
  intro g hg
  have hg' : g = (x₁ : G) ∨ g = (x₂ : G) := by simpa using hg
  rcases hg' with rfl | rfl
  · rw [h1]; exact e4H_mem_EE _
  · rw [h2]; exact e4H_mem_EE _

theorem LyData.exists_pE_of_mem_normalizer (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) {n : G}
    (hn : n ∈ normalizer (EE (x₁ : G) (x₂ : G) : Set G)) :
    ∃ m : Fin 8, n * (x₁ : G) * n⁻¹ = (e4H x₁ x₂ (iE m).1 : G) ∧
      n * (x₂ : G) * n⁻¹ = (e4H x₁ x₂ (iE m).2 : G) := by
  have hX₁E : (x₁ : G) ∈ EE (x₁ : G) (x₂ : G) := Subgroup.subset_closure (by simp)
  have hX₂E : (x₂ : G) ∈ EE (x₁ : G) (x₂ : G) := Subgroup.subset_closure (by simp)
  have huE : n * (x₁ : G) * n⁻¹ ∈ EE (x₁ : G) (x₂ : G) := (mem_normalizer_iff.1 hn _).1 hX₁E
  have hvE : n * (x₂ : G) * n⁻¹ ∈ EE (x₁ : G) (x₂ : G) := (mem_normalizer_iff.1 hn _).1 hX₂E
  have hu : IsConj (x₁ : G) (n * (x₁ : G) * n⁻¹) := isConj_iff.2 ⟨n, rfl⟩
  have hv : IsConj (x₁ : G) (n * (x₂ : G) * n⁻¹) :=
    (D.isConj_x₁_x₂ S).trans (isConj_iff.2 ⟨n, rfl⟩)
  obtain ⟨i, hi⟩ := exists_e4H_of_four (D.eq_of_isConj_mem_closure_two S huE hu)
  obtain ⟨j, hj⟩ := exists_e4H_of_four (D.eq_of_isConj_mem_closure_two S hvE hv)
  have hne := ne_of_e4H S
  have hax : i.val / 2 ≠ j.val / 2 := by
    intro hij
    rcases e4H_axis i j hij x₁ x₂ with h | h
    · have h' : n * (x₂ : G) * n⁻¹ = n * (x₁ : G) * n⁻¹ := by
        rw [hj, hi, h]
      exact hne.1 (mul_left_cancel (mul_right_cancel h'))
    · have h' : n * (x₂ : G) * n⁻¹ = n * (x₁ : G)⁻¹ * n⁻¹ := by
        rw [hj]
        have : (e4H x₁ x₂ j : G) = ((e4H x₁ x₂ i : G))⁻¹ := by rw [h]; simp
        rw [this, ← hi]; group
      exact hne.2 (mul_left_cancel (mul_right_cancel h'))
  obtain ⟨m, hm⟩ := iE_surjective i j hax
  exact ⟨m, by rw [hm]; exact hi, by rw [hm]; exact hj⟩

theorem LyData.card_normalizer_EE (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    Nat.card ↥(normalizer (EE (x₁ : G) (x₂ : G) : Set G)) =
      8 * Nat.card ↥(QE (x₁ : G) (x₂ : G)) := by
  classical
  let a : Fin 2 → G := ![(x₁ : G), (x₂ : G)]
  have hrange : Set.range a = {(x₁ : G), (x₂ : G)} := by
    ext g
    simp [a, or_comm]
  let gT : Fin 8 → (Fin 2 → G) := fun m =>
    ![(e4H x₁ x₂ (iE m).1 : G), (e4H x₁ x₂ (iE m).2 : G)]
  have hgT : Function.Injective gT := by
    intro m m' h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [gT, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    apply iE_injective
    exact Prod.ext (e4H_injective S (Subtype.val_injective h0))
      (e4H_injective S (Subtype.val_injective h1))
  let T : Finset (Fin 2 → G) := Finset.univ.image gT
  have hTcard : T.card = 8 := by
    rw [Finset.card_image_of_injective _ hgT]; simp
  choose w hwN hw using fun m => D.exists_lift_pE_normalizer S m
  have hconj : ∀ m, (fun i => (w m : G) * a i * (w m : G)⁻¹) = gT m := by
    intro m
    funext i
    fin_cases i
    · exact (hw m).1
    · exact (hw m).2
  have hT : ∀ n ∈ normalizer (EE (x₁ : G) (x₂ : G) : Set G),
      (fun i => n * a i * n⁻¹) ∈ T := by
    intro n hn
    obtain ⟨m, hm1, hm2⟩ := D.exists_pE_of_mem_normalizer S hn
    refine Finset.mem_image.2 ⟨m, Finset.mem_univ _, ?_⟩
    funext k
    fin_cases k
    · exact hm1.symm
    · exact hm2.symm
  have hmain := card_eq_mul_card_of_conj_tuples (normalizer (EE (x₁ : G) (x₂ : G) : Set G)) a T hT
    hTcard (fun m => (w m : G)) hwN
    (by
      intro m m' h
      apply hgT
      rw [← hconj m, ← hconj m']
      exact h)
  have hinf : normalizer (EE (x₁ : G) (x₂ : G) : Set G) ⊓
      centralizer ({(x₁ : G), (x₂ : G)} : Set G) = QE (x₁ : G) (x₂ : G) :=
    inf_eq_right.2 (QE_le_normalizer_EE _ _)
  rw [hmain, hrange, hinf]

end Count

section Normal

variable {G : Type*} [Group G]

theorem conj_mem_QE {a b n q : G} (hn : n ∈ normalizer (EE a b : Set G)) (hq : q ∈ QE a b) :
    n * q * n⁻¹ ∈ QE a b := by
  have hQ : QE a b = centralizer ((EE a b : Subgroup G) : Set G) := by
    rw [EE, Subgroup.centralizer_closure]; rfl
  rw [hQ] at hq ⊢
  rw [mem_centralizer_iff] at hq ⊢
  intro e he
  have he' : n⁻¹ * e * n ∈ (EE a b : Subgroup G) := (mem_normalizer_iff''.1 hn e).1 he
  have h1 := hq _ he'
  calc e * (n * q * n⁻¹) = n * ((n⁻¹ * e * n) * q) * n⁻¹ := by group
    _ = n * (q * (n⁻¹ * e * n)) * n⁻¹ := by rw [h1]
    _ = n * q * n⁻¹ * e := by group

theorem normal_threeCoreE_normalizer {a b : G} {R : Subgroup G} (hR : ThreeCoreE a b R) :
    ∀ n ∈ normalizer (EE a b : Set G), ∀ r ∈ R, n * r * n⁻¹ ∈ R := by
  intro n hn r hr
  have hJ : R.map (MulAut.conj n).toMonoidHom ≤ R := by
    refine hR.max _ ?_ ?_ (hR.isPGroup.map _)
    · rintro _ ⟨r', hr', rfl⟩
      exact conj_mem_QE hn (hR.le hr')
    · rintro g hg _ ⟨r', hr', rfl⟩
      have hg' : n⁻¹ * g * n ∈ QE a b := by
        have := conj_mem_QE (Subgroup.inv_mem _ hn) hg
        simpa using this
      refine ⟨(n⁻¹ * g * n) * r' * (n⁻¹ * g * n)⁻¹, hR.normal _ hg' _ hr', ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  exact hJ ⟨r, hr, rfl⟩

end Normal

section Cert

variable {G : Type} [Group G] [Finite G] {t : G}
  {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}

namespace LyData

theorem card_normalizer_EE' (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    Nat.card ↥(normalizer (EE (x₁ : G) (x₂ : G) : Set G)) = 699840 := by
  rw [D.card_normalizer_EE S, D.card_QE S]

theorem normalizer_EE_eq_mul (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) {R : Subgroup G}
    (hR : ThreeCoreE (x₁ : G) (x₂ : G) R) :
    ∀ n ∈ normalizer (EE (x₁ : G) (x₂ : G) : Set G), ∃ r ∈ R,
      ∃ h ∈ normalizer (EE (x₁ : G) (x₂ : G) : Set G) ⊓ centralizer ({t} : Set G), n = r * h := by
  intro n hn
  obtain ⟨m, hm1, hm2⟩ := D.exists_pE_of_mem_normalizer S hn
  obtain ⟨w, hwN, hw1, hw2⟩ := D.exists_lift_pE_normalizer S m
  have hq : (w : G)⁻¹ * n ∈ QE (x₁ : G) (x₂ : G) := by
    rw [mem_QE]
    constructor
    · have h1 : (w : G)⁻¹ * n * (x₁ : G) * ((w : G)⁻¹ * n)⁻¹ = (x₁ : G) := by
        calc (w : G)⁻¹ * n * (x₁ : G) * ((w : G)⁻¹ * n)⁻¹
            = (w : G)⁻¹ * (n * (x₁ : G) * n⁻¹) * (w : G) := by group
          _ = (w : G)⁻¹ * ((w : G) * (x₁ : G) * (w : G)⁻¹) * (w : G) := by rw [hm1, hw1]
          _ = (x₁ : G) := by group
      exact (mul_inv_eq_iff_eq_mul.1 h1).symm
    · have h1 : (w : G)⁻¹ * n * (x₂ : G) * ((w : G)⁻¹ * n)⁻¹ = (x₂ : G) := by
        calc (w : G)⁻¹ * n * (x₂ : G) * ((w : G)⁻¹ * n)⁻¹
            = (w : G)⁻¹ * (n * (x₂ : G) * n⁻¹) * (w : G) := by group
          _ = (w : G)⁻¹ * ((w : G) * (x₂ : G) * (w : G)⁻¹) * (w : G) := by rw [hm2, hw2]
          _ = (x₂ : G) := by group
      exact (mul_inv_eq_iff_eq_mul.1 h1).symm
  obtain ⟨r, hr, s, hs, hrs⟩ := D.QE_eq_mul_SL5 S hR _ hq
  have hsQ := D.SL5_le_QE S hs
  have hsH : s ∈ centralizer ({t} : Set G) := by
    obtain ⟨a, -, rfl⟩ := hs
    exact a.2
  refine ⟨(w : G) * r * (w : G)⁻¹, normal_threeCoreE_normalizer hR _ hwN _ hr, (w : G) * s, ?_, ?_⟩
  · exact ⟨Subgroup.mul_mem _ hwN (QE_le_normalizer_EE _ _ hsQ),
      Subgroup.mul_mem _ w.2 hsH⟩
  · calc n = (w : G) * ((w : G)⁻¹ * n) := by group
      _ = (w : G) * (r * s) := by rw [hrs]
      _ = (w : G) * r * (w : G)⁻¹ * ((w : G) * s) := by group

end LyData

end Cert

end CFSG.Sporadic.Recognition.LyonsSims
