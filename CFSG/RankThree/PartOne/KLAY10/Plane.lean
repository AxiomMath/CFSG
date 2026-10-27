module

public import CFSG.RankThree.PartOne.KF.SpQuad
public import CFSG.RankThree.PartOne.KF.R8Levi

public section

namespace CFSG.RankThree.PartOne.KLAY10

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KFQ

section Fixed

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_nonzero_fixed10 {V : Type} [AddCommGroup V] [Module K V] [Finite V]
    (S : Subgroup (V ≃ₗ[K] V)) (hS2 : IsPGroup 2 S) (X : Submodule K V) (hX : X ≠ ⊥)
    (hXS : ∀ s ∈ S, ∀ x ∈ X, s x ∈ X) :
    ∃ x ∈ X, x ≠ 0 ∧ ∀ s ∈ S, s x = x := by
  classical
  let _ : MulAction S X :=
    { smul := fun s x => ⟨(s : V ≃ₗ[K] V) x, hXS s s.2 x x.2⟩
      one_smul := fun x => Subtype.ext (by
        show (((1 : S) : V ≃ₗ[K] V)) x = x
        rfl)
      mul_smul := fun s t x => Subtype.ext (by
        show (((s * t : S) : V ≃ₗ[K] V)) x = (s : V ≃ₗ[K] V) ((t : V ≃ₗ[K] V) x)
        rfl) }
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : 2 ∣ Nat.card X := by
    have hfin : Module.finrank K X ≠ 0 := by
      have : Nontrivial X := (Submodule.nontrivial_iff_ne_bot).2 hX
      exact (Module.finrank_pos_iff.mpr inferInstance).ne'
    have := Fintype.ofFinite K
    have := Fintype.ofFinite X
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := K) (V := X)]
    have h2 : 2 ∣ Fintype.card K := by
      obtain ⟨m, hm, hmK⟩ := FiniteField.card K 2
      rw [hmK]
      exact dvd_pow_self 2 m.ne_zero
    exact h2.trans (dvd_pow_self _ hfin)
  obtain ⟨b, hb, hne⟩ := hS2.exists_fixed_point_of_prime_dvd_card_of_fixed_point (α := X) hdvd
    (a := 0) (by
      intro s
      apply Subtype.ext
      show (s : V ≃ₗ[K] V) 0 = 0
      exact map_zero _)
  refine ⟨b, b.2, fun h0 => hne ?_, fun s hs => ?_⟩
  · apply Subtype.ext
    exact h0.symm
  · have := hb ⟨s, hs⟩
    exact congrArg Subtype.val this

end Fixed

section Plane

variable {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}

@[expose] def fixSub (S : Subgroup (QV K (Fin 3) ≃ₗ[K] QV K (Fin 3))) :
    Submodule K (QV K (Fin 3)) where
  carrier := {v | ∀ s ∈ S, s v = v}
  add_mem' := fun {a b} ha hb s hs => by rw [map_add, ha s hs, hb s hs]
  zero_mem' := fun s _ => map_zero _
  smul_mem' := fun c v hv s hs => by rw [map_smul, hv s hs]

theorem not_mem_range_of_ne_one (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1)
    {x : (Qext K)ˣ} (hxp : x ^ p = 1) (hx1 : x ≠ 1) :
    (x : Qext K) ∉ Set.range (algebraMap K (Qext K)) := by
  rintro ⟨k, hk⟩
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp only [map_zero] at hk
    exact x.ne_zero hk.symm
  have h1 : k ^ (Nat.card K - 1) = 1 := by
    have := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one k hk0
  have h2 : x ^ (Nat.card K - 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, ← hk, ← map_pow, h1, map_one, Units.val_one]
  have h3 : x ^ Nat.gcd p (Nat.card K - 1) = 1 := pow_gcd_eq_one.2 ⟨hxp, h2⟩
  have hcop : Nat.Coprime p (Nat.card K - 1) := by
    refine (Nat.Prime.coprime_iff_not_dvd hp).2 fun hd => ?_
    have hq1 : 1 < Nat.card K := Finite.one_lt_card
    have h4 : p ∣ (Nat.card K + 1) - (Nat.card K - 1) := Nat.dvd_sub hpq hd
    have h5 : (Nat.card K + 1) - (Nat.card K - 1) = 2 := by omega
    rw [h5] at h4
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h4)
  rw [hcop, pow_one] at h3
  exact hx1 h3

variable (P : Subgroup (Fin 3 → (Qext K)ˣ))

omit [Finite K] in
theorem exists_separating (hp2 : p ≠ 2) (hp : p.Prime) (hPe : ∀ x ∈ P, ∀ i, x i ^ p = 1)
    {i j : Fin 3} (h2 : ∃ x ∈ P, x i ≠ x j) (h3 : ∃ x ∈ P, x i ≠ (x j)⁻¹) :
    ∃ x ∈ P, x i ≠ x j ∧ x i ≠ (x j)⁻¹ := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨x₂, hx₂, hij₂⟩ := h2
  obtain ⟨x₃, hx₃, hij₃⟩ := h3
  by_cases hA : x₂ i ≠ (x₂ j)⁻¹
  · exact ⟨x₂, hx₂, hij₂, hA⟩
  by_cases hB : x₃ i ≠ x₃ j
  · exact ⟨x₃, hx₃, hB, hij₃⟩
  push Not at hA hB
  refine ⟨x₂ * x₃, P.mul_mem hx₂ hx₃, ?_, ?_⟩
  · intro h
    apply hij₂
    have e : ((x₂ j)⁻¹ * x₃ j) = x₂ j * x₃ j := by
      simpa [Pi.mul_apply, hA, hB] using h
    have e2 : (x₂ j)⁻¹ = x₂ j := mul_right_cancel e
    have e3 : x₂ j = 1 := by
      apply eq_one_of_mul_self_of_pow hpodd _ (hPe x₂ hx₂ j)
      calc x₂ j * x₂ j = (x₂ j)⁻¹ * x₂ j := by rw [e2]
        _ = 1 := inv_mul_cancel _
    rw [hA, e3, inv_one]
  · intro h
    apply hij₃
    have e : ((x₂ j)⁻¹ * x₃ j) = (x₂ j)⁻¹ * (x₃ j)⁻¹ := by
      simpa [Pi.mul_apply, hA, hB, mul_inv_rev, mul_comm] using h
    have e2 : x₃ j = (x₃ j)⁻¹ := mul_left_cancel e
    have e3 : x₃ j = 1 := by
      apply eq_one_of_mul_self_of_pow hpodd _ (hPe x₃ hx₃ j)
      calc x₃ j * x₃ j = x₃ j * (x₃ j)⁻¹ := by rw [← e2]
        _ = 1 := mul_inv_cancel _
    rw [hB, e3, inv_one]

theorem sum_qForm_single (x : QV K (Fin 3)) (i : Fin 3) (u : Qext K) :
    ∑ k, qForm (x k) ((Pi.single i u : QV K (Fin 3)) k) = qForm (x i) u := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hk
    simp [Pi.single_eq_of_ne hk]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem frobQ_unit_eq_inv (hpq : p ∣ Nat.card K + 1) {y : (Qext K)ˣ} (hy : y ^ p = 1) :
    frobQ K (y : Qext K) = (y : Qext K)⁻¹ :=
  eq_inv_of_mul_eq_one_right (unit_mul_frob_eq_one hpq hy)

theorem exists_single_of_invariant (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1)
    (hPe : ∀ x ∈ P, ∀ i, x i ^ p = 1)
    (h2 : ∀ i j : Fin 3, i ≠ j → ∃ x ∈ P, x i ≠ x j)
    (h3 : ∀ i j : Fin 3, i ≠ j → ∃ x ∈ P, x i ≠ (x j)⁻¹)
    (N : Submodule K (QV K (Fin 3))) (hN : ∀ x ∈ P, ∀ v ∈ N, torusEquiv x v ∈ N) :
    ∀ v ∈ N, ∀ i, v i ≠ 0 → ∃ a : Qext K, a ≠ 0 ∧ (Pi.single i a : QV K (Fin 3)) ∈ N := by
  classical
  suffices hk : ∀ m : ℕ, ∀ v ∈ N, (Finset.univ.filter fun k => v k ≠ 0).card ≤ m →
      ∀ i, v i ≠ 0 → ∃ a : Qext K, a ≠ 0 ∧ (Pi.single i a : QV K (Fin 3)) ∈ N from
    fun v hv i hvi => hk _ v hv le_rfl i hvi
  intro m
  induction m with
  | zero =>
    intro v hv hcard i hvi
    exfalso
    have hmem : i ∈ Finset.univ.filter fun k => v k ≠ 0 := by simp [hvi]
    have := Finset.card_pos.mpr ⟨i, hmem⟩
    omega
  | succ m ih =>
    intro v hv hcard i hvi
    by_cases hall : ∀ j, j ≠ i → v j = 0
    · refine ⟨v i, hvi, ?_⟩
      have : v = Pi.single i (v i) := by
        funext k
        by_cases hk : k = i
        · subst hk
          simp
        · simp [Pi.single_eq_of_ne hk, hall k hk]
      rw [← this]
      exact hv
    · push Not at hall
      obtain ⟨j, hji, hvj⟩ := hall
      obtain ⟨x, hxP, hne1, hne2⟩ := exists_separating P hp2 hp hPe (h2 i j hji.symm)
        (h3 i j hji.symm)
      set y : (Qext K)ˣ := x j with hy
      have hyp : y ^ p = 1 := hPe x hxP j
      have hyy : (y : Qext K) * (y : Qext K)⁻¹ = 1 := mul_inv_cancel₀ y.ne_zero
      set v1 : QV K (Fin 3) := torusEquiv x v with hv1
      have hv1N : v1 ∈ N := hN x hxP v hv
      set v' : QV K (Fin 3) := torusEquiv x v1 + (trQ (y : Qext K)) • v1 + v with hv'
      have hv'N : v' ∈ N := N.add_mem (N.add_mem (hN x hxP v1 hv1N) (N.smul_mem _ hv1N)) hv
      have hσ : frobQ K (y : Qext K) = (y : Qext K)⁻¹ := frobQ_unit_eq_inv hpq hyp
      have hv'k : ∀ k, v' k = ((x k : Qext K) ^ 2 +
          ((y : Qext K) + (y : Qext K)⁻¹) * (x k : Qext K) + 1) * v k := by
        intro k
        simp only [hv', hv1, Pi.add_apply, Pi.smul_apply]
        simp only [Algebra.smul_def, torusEquiv_apply, algebraMap_trQ, hσ]
        ring
      have hv'j : v' j = 0 := by
        rw [hv'k j]
        have : (x j : Qext K) ^ 2 + ((y : Qext K) + (y : Qext K)⁻¹) * (x j : Qext K) + 1 = 0 := by
          rw [← hy]
          linear_combination ((y : Qext K) ^ 2 + 1) * (two_eq_zero_qext (K := K)) + hyy
        rw [this, zero_mul]
      have hm : ∀ k, (x k : Qext K) ^ 2 + ((y : Qext K) + (y : Qext K)⁻¹) * (x k : Qext K) + 1 =
          ((x k : Qext K) - y) * ((x k : Qext K) - (y : Qext K)⁻¹) := by
        intro k
        linear_combination (((y : Qext K) + (y : Qext K)⁻¹) * (x k : Qext K)) *
          (two_eq_zero_qext (K := K)) - hyy
      have hv'i : v' i ≠ 0 := by
        rw [hv'k i, hm i]
        refine mul_ne_zero (mul_ne_zero ?_ ?_) hvi
        · intro h
          exact hne1 (Units.ext (sub_eq_zero.1 h))
        · intro h
          apply hne2
          apply Units.ext
          rw [Units.val_inv_eq_inv_val]
          exact sub_eq_zero.1 h
      have hcard' : (Finset.univ.filter fun k => v' k ≠ 0).card ≤ m := by
        have hsub : (Finset.univ.filter fun k => v' k ≠ 0) ⊆
            (Finset.univ.filter fun k => v k ≠ 0).erase j := by
          intro k hk
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at hk ⊢
          refine ⟨?_, ?_⟩
          · rintro rfl
            exact hk hv'j
          · intro hvk
            apply hk
            rw [hv'k k, hvk, mul_zero]
        have hjmem : j ∈ Finset.univ.filter fun k => v k ≠ 0 := by simp [hvj]
        calc _ ≤ ((Finset.univ.filter fun k => v k ≠ 0).erase j).card := Finset.card_le_card hsub
          _ = (Finset.univ.filter fun k => v k ≠ 0).card - 1 := Finset.card_erase_of_mem hjmem
          _ ≤ m := by omega
      exact ih v' hv'N hcard' i hv'i

theorem single_all_of_single (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1)
    (hPe : ∀ x ∈ P, ∀ i, x i ^ p = 1) (h1 : ∀ i, ∃ x ∈ P, x i ≠ 1)
    (N : Submodule K (QV K (Fin 3))) (hN : ∀ x ∈ P, ∀ v ∈ N, torusEquiv x v ∈ N)
    (i : Fin 3) (a : Qext K) (ha : a ≠ 0) (haN : (Pi.single i a : QV K (Fin 3)) ∈ N)
    (u : Qext K) : (Pi.single i u : QV K (Fin 3)) ∈ N := by
  obtain ⟨x, hxP, hx1⟩ := h1 i
  have hz := not_mem_range_of_ne_one hp hp2 hpq (hPe x hxP i) hx1
  obtain ⟨s, t, hst⟩ := span_one_z hz (u * a⁻¹)
  have hu : u = (algebraMap K (Qext K) s + algebraMap K (Qext K) t * (x i : Qext K)) * a := by
    have : u = (u * a⁻¹) * a := by field_simp
    rw [this, hst]
    simp only [Algebra.smul_def, mul_one]
  have hvec : (Pi.single i u : QV K (Fin 3)) =
      s • (Pi.single i a : QV K (Fin 3)) + t • torusEquiv x (Pi.single i a : QV K (Fin 3)) := by
    funext k
    by_cases hk : k = i
    · subst hk
      simp only [Pi.add_apply, Pi.smul_apply]
      simp only [Algebra.smul_def, torusEquiv_apply, Pi.single_eq_same]
      rw [hu]
      ring
    · simp [Pi.single_eq_of_ne hk, torusEquiv_apply]
  rw [hvec]
  exact N.add_mem (N.smul_mem s haN) (N.smul_mem t (hN x hxP _ haN))

theorem eq_bot_of_separated (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1)
    (hPe : ∀ x ∈ P, ∀ i, x i ^ p = 1)
    (S : Subgroup (QV K (Fin 3) ≃ₗ[K] QV K (Fin 3))) (hSM : S ≤ M10 K) (hS2 : IsPGroup 2 S)
    (hPS : ∀ x ∈ P, ∀ s ∈ S, torusEquiv x * s * (torusEquiv x)⁻¹ ∈ S)
    (h1 : ∀ i, ∃ x ∈ P, x i ≠ 1)
    (h2 : ∀ i j : Fin 3, i ≠ j → ∃ x ∈ P, x i ≠ x j)
    (h3 : ∀ i j : Fin 3, i ≠ j → ∃ x ∈ P, x i ≠ (x j)⁻¹) : S = ⊥ := by
  classical
  have hWD : ∀ x ∈ P, ∀ v ∈ fixSub S, torusEquiv x v ∈ fixSub S := by
    intro x hx v hv s hs
    have hs' : (torusEquiv x)⁻¹ * s * ((torusEquiv x)⁻¹)⁻¹ ∈ S := by
      have := hPS x⁻¹ (P.inv_mem hx) s hs
      have hinv : torusEquiv x⁻¹ = (torusEquiv x)⁻¹ := map_inv torusHom x
      rwa [hinv] at this
    have h1' := hv _ hs'
    rw [inv_inv] at h1'
    have h2' : (torusEquiv x).symm (s (torusEquiv x v)) = v := h1'
    calc s (torusEquiv x v) = torusEquiv x ((torusEquiv x).symm (s (torusEquiv x v))) := by simp
      _ = torusEquiv x v := by rw [h2']
  have hWsupp : ∀ v ∈ fixSub S, ∀ i, v i ≠ 0 → ∀ u, (Pi.single i u : QV K (Fin 3)) ∈ fixSub S := by
    intro v hv i hvi u
    obtain ⟨a, ha, haW⟩ := exists_single_of_invariant P hp hp2 hpq hPe h2 h3 (fixSub S) hWD v hv i
      hvi
    exact single_all_of_single P hp hp2 hpq hPe h1 (fixSub S) hWD i a ha haW u
  by_cases hI : ∀ i : Fin 3, ∀ u : Qext K, (Pi.single i u : QV K (Fin 3)) ∈ fixSub S
  · rw [eq_bot_iff]
    intro s hs
    rw [Subgroup.mem_bot]
    refine LinearEquiv.ext fun v => ?_
    have hv : v = ∑ k, (Pi.single k (v k) : QV K (Fin 3)) := (Finset.univ_sum_single v).symm
    conv_lhs => rw [hv]
    rw [map_sum]
    refine (Finset.sum_congr rfl fun k _ => hI k (v k) s hs).trans ?_
    exact hv.symm
  · exfalso
    push Not at hI
    obtain ⟨j, uj, hjW⟩ := hI
    let Y : Submodule K (QV K (Fin 3)) :=
      { carrier := {y | ∀ i, (∀ u : Qext K, (Pi.single i u : QV K (Fin 3)) ∈ fixSub S) → y i = 0}
        add_mem' := fun {a b} ha hb i hi => by simp [ha i hi, hb i hi]
        zero_mem' := fun i hi => rfl
        smul_mem' := fun c y hy i hi => by simp [hy i hi] }
    have hYne : Y ≠ ⊥ := by
      intro hbot
      have hmem : (Pi.single j 1 : QV K (Fin 3)) ∈ Y := by
        intro i hi
        have hij : i ≠ j := fun hij => hjW (hij ▸ hi uj)
        simp [Pi.single_eq_of_ne hij]
      rw [hbot] at hmem
      have := congrFun ((Submodule.mem_bot K).1 hmem) j
      simp at this
    have hYS : ∀ s ∈ S, ∀ y ∈ Y, s y ∈ Y := by
      intro s hs y hy i hi
      have hsM := (mem_M10_iff s).1 (hSM hs)
      apply qForm_nondegenerate.1
      intro u
      have e1 : ∑ k, qForm (s y k) ((Pi.single i u : QV K (Fin 3)) k) = qForm (s y i) u :=
        sum_qForm_single _ i u
      have e2 : ∑ k, qForm (y k) ((Pi.single i u : QV K (Fin 3)) k) = qForm (y i) u :=
        sum_qForm_single _ i u
      rw [← e1]
      calc ∑ k, qForm (s y k) ((Pi.single i u : QV K (Fin 3)) k)
          = ∑ k, qForm (s y k) (s (Pi.single i u : QV K (Fin 3)) k) := by
            rw [hi u s hs]
        _ = ∑ k, qForm (y k) ((Pi.single i u : QV K (Fin 3)) k) := hsM y _
        _ = 0 := by rw [e2, hy i hi]; simp
    obtain ⟨y, hyY, hy0, hyfix⟩ := exists_nonzero_fixed10 S hS2 Y hYne hYS
    have hyW : y ∈ fixSub S := fun s hs => hyfix s hs
    apply hy0
    funext i
    by_cases hi : ∀ u : Qext K, (Pi.single i u : QV K (Fin 3)) ∈ fixSub S
    · exact hyY i hi
    · by_contra hyi
      exact hi (hWsupp y hyW i hyi)

end Plane

end CFSG.RankThree.PartOne.KLAY10
