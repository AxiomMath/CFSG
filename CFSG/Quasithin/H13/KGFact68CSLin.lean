module

public import CFSG.Quasithin.H13.KGFact68CSTrans
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyLinearBinary

public section

namespace CFSG.Quasithin.H13.KG68

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Center

variable {n : ℕ} {K : Type} [Field K]

theorem transvection_mem_unitriangular {i j : Fin n} (hij : i < j) (c : K) :
    Matrix.SpecialLinearGroup.transvection (ne_of_lt hij) c ∈ unitriangular n K := by
  rw [mem_unitriangular]
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_apply, one_apply_ne (ne_of_gt hab),
      single_apply]
    have : ¬ (i = a ∧ j = b) := fun h => by
      rw [← h.1, ← h.2] at hab
      exact absurd (hab.trans hij) (lt_irrefl _)
    simp [this]
  · rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_apply, one_apply_eq, single_apply]
    have : ¬ (i = a ∧ j = a) := fun h => (ne_of_lt hij) (h.1.trans h.2.symm)
    simp [this]

theorem unitriangular_center_entry {A : SpecialLinearGroup (Fin n) K}
    (hc : ∀ B ∈ unitriangular n K, A * B = B * A) {i j : Fin n} (hij : i < j)
    (h0 : ¬ (i.val = 0 ∧ j.val + 1 = n)) : (A : Matrix (Fin n) (Fin n) K) i j = 0 := by
  by_cases hj : j.val + 1 < n
  · let j' : Fin n := ⟨j.val + 1, hj⟩
    have hjj' : j < j' := by
      rw [Fin.lt_def]
      exact Nat.lt_succ_self _
    have h1 := congrArg (fun B : SpecialLinearGroup (Fin n) K =>
      (B : Matrix (Fin n) (Fin n) K) i j') (hc _ (transvection_mem_unitriangular hjj' 1))
    simp [Matrix.SpecialLinearGroup.transvection_coe, mul_add, add_mul, ne_of_lt hij] at h1
    exact h1
  · have hjn : j.val + 1 = n := by omega
    have hi : 0 < i.val := by
      by_contra hi0
      exact h0 ⟨by omega, hjn⟩
    let i' : Fin n := ⟨i.val - 1, by omega⟩
    have hi'i : i' < i := by
      rw [Fin.lt_def]
      show i.val - 1 < i.val
      omega
    have h1 := congrArg (fun B : SpecialLinearGroup (Fin n) K =>
      (B : Matrix (Fin n) (Fin n) K) i' j) (hc _ (transvection_mem_unitriangular hi'i 1))
    simp [Matrix.SpecialLinearGroup.transvection_coe, mul_add, add_mul, ne_of_gt hij] at h1
    exact h1

theorem card_center_unitriangular_le [Finite K] (hn : 1 ≤ n) :
    Nat.card (Subgroup.center ↥(unitriangular n K)) ≤ Nat.card K := by
  let i0 : Fin n := ⟨0, by omega⟩
  let jn : Fin n := ⟨n - 1, by omega⟩
  let f : Subgroup.center ↥(unitriangular n K) → K := fun A =>
    (((A : ↥(unitriangular n K)) : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) i0 jn
  refine Nat.card_le_card_of_injective f fun A B hAB => ?_
  have hcen : ∀ C : Subgroup.center ↥(unitriangular n K), ∀ D ∈ unitriangular n K,
      ((C : ↥(unitriangular n K)) : SpecialLinearGroup (Fin n) K) * D =
        D * ((C : ↥(unitriangular n K)) : SpecialLinearGroup (Fin n) K) := by
    intro C D hD
    have := Subgroup.mem_center_iff.mp C.2 ⟨D, hD⟩
    exact (congrArg Subtype.val this).symm
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  have hA := ((A : ↥(unitriangular n K))).2
  have hB := ((B : ↥(unitriangular n K))).2
  rw [mem_unitriangular] at hA hB
  rcases lt_trichotomy i j with hij | rfl | hij
  · by_cases h0 : i.val = 0 ∧ j.val + 1 = n
    · have hi : i = i0 := Fin.ext h0.1
      have hj : j = jn := Fin.ext (by show j.val = n - 1; omega)
      rw [hi, hj]
      exact hAB
    · rw [unitriangular_center_entry (hcen A) hij h0, unitriangular_center_entry (hcen B) hij h0]
  · rw [hA.2, hB.2]
  · rw [hA.1 _ _ hij, hB.1 _ _ hij]

end Center

section Binary

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem eq_one_of_card_two (hK : Nat.card K = 2) {r : K} (hr : r ≠ 0) : r = 1 := by
  have hcard : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK]
  have : Subsingleton Kˣ := (Nat.card_eq_one_iff_unique.1 hcard).1
  exact congrArg Units.val (Subsingleton.elim (Units.mk0 r hr) 1)

omit [Finite K] in
theorem center_sl_eq_bot_of_card_two {n : ℕ} (hK : Nat.card K = 2) :
    Subgroup.center (SpecialLinearGroup (Fin n) K) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Subgroup.mem_bot]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · apply Subtype.ext
    ext i
    exact i.elim0
  · have hr0 : r ≠ 0 := by
      rintro rfl
      rw [Fintype.card_fin, zero_pow (by omega)] at hr
      exact zero_ne_one hr
    apply Subtype.ext
    rw [← hrA, eq_one_of_card_two hK hr0]
    simp

theorem factorization_two_pow_mul {m k : ℕ} (hk : ¬ 2 ∣ k) : (2 ^ m * k).factorization 2 = m := by
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hk (dvd_zero 2)
  rw [Nat.factorization_mul (by positivity) hk0, Finsupp.add_apply, Nat.factorization_pow,
    Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd hk]
  simp

theorem card_unitriangular_binary {n : ℕ} (hn : n = 3 ∨ n = 4 ∨ n = 5) (hK : Nat.card K = 2) :
    Nat.card (unitriangular n K) =
      2 ^ (Nat.card (SpecialLinearGroup (Fin n) K)).factorization 2 := by
  have : Fintype K := Fintype.ofFinite K
  have hq : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  rw [card_unitriangular, hK]
  rcases hn with rfl | rfl | rfl
  · rw [Matrix.card_SL_field, hq, show (∏ i : Fin 3, (2 ^ 3 - 2 ^ (i : ℕ))) / (2 - 1) = 2 ^ 3 * 21
      by norm_num [Fin.prod_univ_succ], factorization_two_pow_mul (by norm_num)]
  · rw [Matrix.card_SL_field, hq, show (∏ i : Fin 4, (2 ^ 4 - 2 ^ (i : ℕ))) / (2 - 1) = 2 ^ 6 * 315
      by norm_num [Fin.prod_univ_succ], factorization_two_pow_mul (by norm_num)]
  · rw [Matrix.card_SL_field, hq, show (∏ i : Fin 5, (2 ^ 5 - 2 ^ (i : ℕ))) / (2 - 1) =
      2 ^ 10 * 9765 by norm_num [Fin.prod_univ_succ], factorization_two_pow_mul (by norm_num)]

theorem cartanSingerCover_sl_binary {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2)
    (hsyl : Nat.card (unitriangular n K) =
      2 ^ (Nat.card (SpecialLinearGroup (Fin n) K)).factorization 2) :
    CartanSingerCover (SpecialLinearGroup (Fin n) K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine cartanSingerCover_of_sylow (Sylow.ofCard (unitriangular n K) hsyl) fun 𝓡 G hG => ?_
  exfalso
  rw [Sylow.coe_ofCard] at hG
  have h1 : Nat.card G ≤ Nat.card (Subgroup.center ↥(unitriangular n K)) := by
    refine Nat.card_le_card_of_injective (fun g : G => ⟨⟨g, (hG.le g g.2).1⟩,
      Subgroup.mem_center_iff.mpr fun y => Subtype.ext ((hG.le g g.2).2 y y.2).symm⟩) ?_
    intro a b hab
    have := congrArg (fun w : Subgroup.center ↥(unitriangular n K) =>
      ((w : ↥(unitriangular n K)) : SpecialLinearGroup (Fin n) K)) hab
    exact Subtype.ext this
  have h2 := card_center_unitriangular_le (K := K) hn
  have h3 := hG.four_le
  rw [hK] at h2
  omega

end Binary

theorem cartanSingerCover_of_stated_psl_binary {X : Type} [Group X] [Finite X] {n : ℕ}
    (hn : n = 3 ∨ n = 4 ∨ n = 5)
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL n 2 1) : CartanSingerCover X := by
  obtain ⟨-, K, _, hfin, hcard, ⟨e⟩⟩ := h
  have hK : Nat.card K = 2 := by rw [hcard, pow_one]
  have hZ := center_sl_eq_bot_of_card_two (n := n) hK
  have hn1 : 1 ≤ n := by omega
  exact CartanSingerCover.of_mulEquiv
    ((e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n K).symm).trans
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot))
    (cartanSingerCover_sl_binary hn1 hK (card_unitriangular_binary hn hK))

section CyclicCenter

theorem isCyclic_of_card_le_two {α : Type*} [Group α] [Finite α] (h : Nat.card α ≤ 2) :
    IsCyclic α := by
  rcases Nat.lt_or_ge (Nat.card α) 2 with h1 | h1
  · have h2 : Nat.card α = 1 := by
      have := Nat.card_pos (α := α)
      omega
    exact @isCyclic_of_subsingleton α _ (Nat.card_eq_one_iff_unique.mp h2).1
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact isCyclic_of_prime_card (p := 2) (by omega)

theorem isCyclic_center_sylow {S : Type} [Group S] [Finite S] (U : Sylow 2 S)
    (hU : Nat.card (Subgroup.center ↥(U : Subgroup S)) ≤ 2) (T : Sylow 2 S) :
    IsCyclic (Subgroup.center ↥(T : Subgroup S)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S T U
  let e : ↥(T : Subgroup S) ≃* ↥(U : Subgroup S) :=
    (T.equivSMul g).trans (MulEquiv.subgroupCongr (by rw [hg]))
  have hc : Nat.card (Subgroup.center ↥(T : Subgroup S)) =
      Nat.card (Subgroup.center ↥(U : Subgroup S)) := by
    rw [← Subgroup.map_center_eq e, Subgroup.card_map_of_injective e.injective]
  exact isCyclic_of_card_le_two (hc ▸ hU)

theorem isCyclic_center_sylow_of_mulEquiv {X S : Type} [Group X] [Group S] [Finite X]
    (e : X ≃* S) (h : ∀ T : Sylow 2 S, IsCyclic (Subgroup.center ↥(T : Subgroup S)))
    (T : Sylow 2 X) : IsCyclic (Subgroup.center ↥(T : Subgroup X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := h (T.mapSurjective (f := e.toMonoidHom) e.surjective)
  let e' : ↥(T : Subgroup X) ≃* ↥((T.mapSurjective (f := e.toMonoidHom) e.surjective :
      Sylow 2 S) : Subgroup S) :=
    (T : Subgroup X).equivMapOfInjective e.toMonoidHom e.injective
  have := h1
  let hc := ((Subgroup.center ↥(T : Subgroup X)).equivMapOfInjective e'.toMonoidHom
    e'.injective).trans (MulEquiv.subgroupCongr (Subgroup.map_center_eq e'))
  exact isCyclic_of_surjective hc.symm.toMonoidHom hc.symm.surjective

variable {K : Type} [Field K] [Finite K]

theorem isCyclic_center_sylow_sl_binary {n : ℕ} (hn : n = 3 ∨ n = 4 ∨ n = 5)
    (hK : Nat.card K = 2) (T : Sylow 2 (SpecialLinearGroup (Fin n) K)) :
    IsCyclic (Subgroup.center ↥(T : Subgroup (SpecialLinearGroup (Fin n) K))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let U : Sylow 2 (SpecialLinearGroup (Fin n) K) :=
    Sylow.ofCard (unitriangular n K) (card_unitriangular_binary hn hK)
  refine isCyclic_center_sylow U ?_ T
  have h1 := card_center_unitriangular_le (n := n) (K := K) (by omega)
  rw [hK] at h1
  have hU : (U : Subgroup (SpecialLinearGroup (Fin n) K)) = unitriangular n K :=
    Sylow.coe_ofCard _ _
  rw [hU]
  exact h1

end CyclicCenter

theorem isCyclic_center_sylow_of_stated_psl_binary {X : Type} [Group X] [Finite X] {n : ℕ}
    (hn : n = 3 ∨ n = 4 ∨ n = 5)
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL n 2 1) (T : Sylow 2 X) :
    IsCyclic (Subgroup.center ↥(T : Subgroup X)) := by
  obtain ⟨-, K, _, hfin, hcard, ⟨e⟩⟩ := h
  have hK : Nat.card K = 2 := by rw [hcard, pow_one]
  have hZ := center_sl_eq_bot_of_card_two (n := n) hK
  exact isCyclic_center_sylow_of_mulEquiv
    ((e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj n K).symm).trans
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot))
    (isCyclic_center_sylow_sl_binary hn hK) T

theorem isCyclic_center_sylow_alt8 (T : Sylow 2 (alternatingGroup (Fin 8))) :
    IsCyclic (Subgroup.center ↥(T : Subgroup (alternatingGroup (Fin 8)))) :=
  isCyclic_center_sylow_of_mulEquiv
    (CFSG.GH74.Exceptional.alternatingEightEquivGLFourTwo.trans
      (CFSG.QuasithinUnique.Setup.Family.slEquivGL 4).symm)
    (isCyclic_center_sylow_sl_binary (Or.inr (Or.inl rfl)) (by rw [Nat.card_zmod])) T

end CFSG.Quasithin.H13.KG68
