module

public import CFSG.LieType.Chevalley.WeylRoots
public import CFSG.LieType.Steinberg.Adjoint.Pairs

public section

namespace CFSG.StandardType

namespace ExcFramesHalf

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

section NormTwo

variable {τ : Tag}

theorem cartan_diag (hτ : τ = .E7 ∨ τ = .E8) (i : Fin τ.rank) : τ.cartan i i = 2 := by
  rcases hτ with rfl | rfl <;> revert i <;> decide

theorem cartan_offDiag (hτ : τ = .E7 ∨ τ = .E8) (i j : Fin τ.rank) (h : i ≠ j) :
    τ.cartan i j ≤ 0 := by
  have key : ∀ p : Fin τ.rank × Fin τ.rank, p.1 ≠ p.2 → τ.cartan p.1 p.2 ≤ 0 := by
    rcases hτ with rfl | rfl <;> decide
  exact key (i, j) h

theorem symmetrizer_diag (hτ : τ = .E7 ∨ τ = .E8) (i : Fin τ.rank) : τ.symmetrizer i i = 1 := by
  rcases hτ with rfl | rfl <;> revert i <;> decide

theorem symmetrizedCartan_eq (hτ : τ = .E7 ∨ τ = .E8) (i j : Fin τ.rank) :
    τ.symmetrizedCartan i j = τ.cartan i j := by
  rcases hτ with rfl | rfl <;> simp [Tag.symmetrizedCartan, Tag.symmetrizer]

theorem iform_single_left_eq (hτ : τ = .E7 ∨ τ = .E8) (i : Fin τ.rank)
    (u : Fin τ.rank → ℤ) :
    iform (Pi.single i 1 : Fin τ.rank → ℤ) u = ∑ j, τ.cartan i j * u j := by
  rw [iform_single_left, symmetrizer_diag hτ, one_mul]

theorem iform_single_single_eq (hτ : τ = .E7 ∨ τ = .E8) (i : Fin τ.rank) :
    iform (Pi.single i 1 : Fin τ.rank → ℤ) (Pi.single i 1) = 2 := by
  rw [iform_single_single, symmetrizer_diag hτ]
  ring

theorem iform_self_eq_sum (hτ : τ = .E7 ∨ τ = .E8) (u : Fin τ.rank → ℤ) :
    iform u u = ∑ i, u i * ∑ j, τ.cartan i j * u j := by
  simp only [iform, symmetrizedCartan_eq hτ, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem iform_self_nonneg (x : Fin τ.rank → ℤ) : 0 ≤ iform x x := by
  by_cases hx : x = 0
  · subst hx
    simp [iform]
  · exact (iform_self_pos hx).le

theorem even_iform_self (hτ : τ = .E7 ∨ τ = .E8) (v : Fin τ.rank → ℤ) : Even (iform v v) := by
  classical
  have key : ∀ S : Finset (Fin τ.rank),
      Even (iform (∑ i ∈ S, v i • (Pi.single i 1 : Fin τ.rank → ℤ))
        (∑ i ∈ S, v i • (Pi.single i 1 : Fin τ.rank → ℤ))) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp [iform]
    | insert a S ha ih =>
      rw [Finset.sum_insert ha]
      set x : Fin τ.rank → ℤ := ∑ i ∈ S, v i • (Pi.single i 1 : Fin τ.rank → ℤ) with hx
      set y : Fin τ.rank → ℤ := v a • (Pi.single a 1 : Fin τ.rank → ℤ) with hy
      have h1 : iform (y + x) (y + x) = iform y y + 2 * iform y x + iform x x := by
        rw [iform_add_left, iform_add_right, iform_add_right, iform_comm x y]
        ring
      have h2 : iform y y = 2 * (v a * v a) := by
        rw [hy, iform_smul_left, iform_smul_right, iform_single_single_eq hτ]
        ring
      rw [h1, h2]
      exact ((even_two_mul _).add (even_two_mul _)).add ih
  have hv : ∑ i ∈ (Finset.univ : Finset (Fin τ.rank)),
      v i • (Pi.single i 1 : Fin τ.rank → ℤ) = v := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have := key Finset.univ
  rwa [hv] at this

theorem isRoot_of_nonneg_iform_eq_two (hτ : τ = .E7 ∨ τ = .E8) :
    ∀ (n : ℕ) (u : Fin τ.rank → ℤ), (∀ i, 0 ≤ u i) → iform u u = 2 → ∑ i, u i = n →
      IsRoot τ u := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro u hu0 hu2 hun
    classical
    have hsum : ∑ i, u i * ∑ j, τ.cartan i j * u j = 2 := by
      rw [← iform_self_eq_sum hτ u]
      exact hu2
    obtain ⟨i, hi⟩ : ∃ i, 0 < u i * ∑ j, τ.cartan i j * u j := by
      by_contra h
      push Not at h
      have := Finset.sum_nonpos (fun i (_ : i ∈ Finset.univ) => h i)
      omega
    have hui : 0 < u i := by
      rcases (hu0 i).lt_or_eq with h | h
      · exact h
      · rw [← h] at hi
        simp at hi
    have hk : 0 < ∑ j, τ.cartan i j * u j := by
      by_contra h
      push Not at h
      have := mul_nonpos_of_nonneg_of_nonpos (hu0 i) h
      omega
    set k : ℤ := ∑ j, τ.cartan i j * u j with hkdef
    have hpair : iform (Pi.single i 1 : Fin τ.rank → ℤ) u = k := iform_single_left_eq hτ i u
    have hrefl : reflect τ i u = u - k • (Pi.single i 1 : Fin τ.rank → ℤ) := rfl
    by_cases hcase : k ≤ u i
    · have hv0 : ∀ j, 0 ≤ reflect τ i u j := by
        intro j
        rw [hrefl]
        by_cases hj : j = i
        · subst hj
          simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_apply, if_true, smul_eq_mul, mul_one]
          omega
        · simp [Pi.single_apply, hj, hu0 j]
      have hv2 : iform (reflect τ i u) (reflect τ i u) = 2 := by
        rw [iform_reflect, hu2]
      have hvsum : ∑ j, reflect τ i u j = (n : ℤ) - k := by
        rw [hrefl]
        simp [Finset.sum_sub_distrib, hun, Pi.single_apply]
      have hvnn : 0 ≤ ∑ j, reflect τ i u j := Finset.sum_nonneg fun j _ => hv0 j
      have hlt : (∑ j, reflect τ i u j).toNat < n := by omega
      have hroot := ih _ hlt (reflect τ i u) hv0 hv2 (Int.toNat_of_nonneg hvnn).symm
      have := IsRoot.reflect i hroot
      rwa [reflect_reflect] at this
    · push Not at hcase
      have hk2 : 2 ≤ k := by omega
      set w : Fin τ.rank → ℤ := u - (Pi.single i 1 : Fin τ.rank → ℤ) with hw
      have hww : iform w w = 4 - 2 * k := by
        rw [hw, iform_sub_left, iform_sub_right, iform_sub_right, iform_comm u (Pi.single i 1),
          hpair, hu2, iform_single_single_eq hτ]
        ring
      have hnn := iform_self_nonneg w
      have hk2' : k = 2 := by omega
      have hw0 : w = 0 := by
        by_contra hne
        have := iform_self_pos hne
        omega
      have : u = Pi.single i 1 := by
        rw [hw] at hw0
        exact sub_eq_zero.1 hw0
      rw [this]
      exact IsRoot.basis i

theorem isRoot_of_iform_self_eq_two (hτ : τ = .E7 ∨ τ = .E8) {u : Fin τ.rank → ℤ}
    (hu : iform u u = 2) : IsRoot τ u := by
  classical
  obtain ⟨up, um, hu_eq, hup0, hum0, hdisj⟩ : ∃ up um : Fin τ.rank → ℤ, u = up - um ∧
      (∀ i, 0 ≤ up i) ∧ (∀ i, 0 ≤ um i) ∧ ∀ i, up i * um i = 0 := by
    refine ⟨fun i => ((u i).toNat : ℤ), fun i => ((-u i).toNat : ℤ), ?_, fun i => by simp,
      fun i => by simp, fun i => ?_⟩
    · ext i
      simp only [Pi.sub_apply]
      omega
    · rcases le_total 0 (u i) with h | h
      · have : (-u i).toNat = 0 := by omega
        simp [this]
      · have : (u i).toNat = 0 := by omega
        simp [this]
  subst hu_eq
  have hcross : iform up um ≤ 0 := by
    unfold iform
    refine Finset.sum_nonpos fun i _ => Finset.sum_nonpos fun j _ => ?_
    rw [symmetrizedCartan_eq hτ]
    by_cases hij : i = j
    · subst hij
      rw [cartan_diag hτ]
      have := hdisj i
      nlinarith
    · have h1 : 0 ≤ up i * um j := mul_nonneg (hup0 i) (hum0 j)
      have h2 := cartan_offDiag hτ i j hij
      nlinarith
  have hexp : iform (up - um) (up - um) = iform up up + iform um um - 2 * iform up um := by
    rw [iform_sub_left, iform_sub_right, iform_sub_right, iform_comm um up]
    ring
  rw [hexp] at hu
  have hor : up = 0 ∨ um = 0 := by
    by_contra h
    push Not at h
    have h1 := iform_self_pos h.1
    have h2 := iform_self_pos h.2
    obtain ⟨a, ha⟩ := even_iform_self hτ up
    obtain ⟨b, hb⟩ := even_iform_self hτ um
    omega
  rcases hor with h | h
  · subst h
    have hn : iform um um = 2 := by
      have : iform (0 : Fin τ.rank → ℤ) 0 = 0 := by simp [iform]
      have h0 : iform (0 : Fin τ.rank → ℤ) um = 0 := by simp [iform]
      rw [this, h0] at hu
      linarith
    have := isRoot_of_nonneg_iform_eq_two hτ (∑ i, um i).toNat um hum0 hn
      (Int.toNat_of_nonneg (Finset.sum_nonneg fun i _ => hum0 i)).symm
    have h2 := IsRoot.neg this
    simpa using h2
  · subst h
    have hn : iform up up = 2 := by
      have : iform (0 : Fin τ.rank → ℤ) 0 = 0 := by simp [iform]
      have h0 : iform up (0 : Fin τ.rank → ℤ) = 0 := by simp [iform]
      rw [this, h0] at hu
      linarith
    have := isRoot_of_nonneg_iform_eq_two hτ (∑ i, up i).toNat up hup0 hn
      (Int.toNat_of_nonneg (Finset.sum_nonneg fun i _ => hup0 i)).symm
    simpa using this

end NormTwo

end ExcFramesHalf

end CFSG.StandardType
