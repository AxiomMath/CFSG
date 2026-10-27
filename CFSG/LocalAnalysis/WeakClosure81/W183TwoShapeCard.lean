module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5SOS

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2 IsL3 IsU3 IsSp4 IsAlt)
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput lieOrderNumerator
  lieOrderDivisor lieSylowExponent)

private theorem w183b5_card_PSL_2_2_2 {T : Type} [Group T] (hO : LieOrderFormulasInput)
    (h : LieModel T .PSL 2 2 2) : Nat.card T = 60 := by
  obtain ⟨-, hM, -⟩ := hO T .PSL 2 2 2 h.admissible h
  have hd : lieOrderDivisor .PSL 2 (2 ^ 2) = 1 := by decide
  rw [hd, mul_one] at hM
  rw [hM]
  simp [lieOrderNumerator, show Finset.Icc 2 2 = {2} by decide]

private theorem w183b5_card_PSU_3_2_2 {T : Type} [Group T] (hO : LieOrderFormulasInput)
    (h : LieModel T .PSU 3 2 2) : Nat.card T = 62400 := by
  obtain ⟨-, hM, -⟩ := hO T .PSU 3 2 2 h.admissible h
  have hd : lieOrderDivisor .PSU 3 (2 ^ 2) = 1 := by decide
  rw [hd, mul_one] at hM
  rw [hM]
  have h2 : Even (2 : ℕ) := by decide
  have h3 : ¬ Even (3 : ℕ) := by decide
  simp [lieOrderNumerator, show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair, h2, h3]

private theorem w183b5_card_PSL_3_2_1 {T : Type} [Group T] (hO : LieOrderFormulasInput)
    (h : LieModel T .PSL 3 2 1) : Nat.card T = 168 := by
  obtain ⟨-, hM, -⟩ := hO T .PSL 3 2 1 h.admissible h
  have hd : lieOrderDivisor .PSL 3 (2 ^ 1) = 1 := by decide
  rw [hd, mul_one] at hM
  rw [hM]
  simp [lieOrderNumerator, show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair]

private theorem w183b5_card_PSL_3_2_2 {T : Type} [Group T] (hO : LieOrderFormulasInput)
    (h : LieModel T .PSL 3 2 2) : Nat.card T = 20160 := by
  obtain ⟨-, hM, -⟩ := hO T .PSL 3 2 2 h.admissible h
  have hd : lieOrderDivisor .PSL 3 (2 ^ 2) = 3 := by decide
  rw [hd] at hM
  have hnum : lieOrderNumerator .PSL 3 (2 ^ 2) = 60480 := by
    simp [lieOrderNumerator, show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair]
  rw [hnum] at hM
  omega

private theorem w183b5_card_PSp_2_2_2 {T : Type} [Group T] (hO : LieOrderFormulasInput)
    (h : LieModel T .PSp 2 2 2) : Nat.card T = 979200 := by
  obtain ⟨-, hM, -⟩ := hO T .PSp 2 2 2 h.admissible h
  have hd : lieOrderDivisor .PSp 2 (2 ^ 2) = 1 := by decide
  rw [hd, mul_one] at hM
  rw [hM]
  simp [lieOrderNumerator, show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair]

private theorem w183b5_card_PSL_2_5_2 {T : Type} [Group T] (hO : LieOrderFormulasInput)
    (h : LieModel T .PSL 2 5 2) : Nat.card T = 7800 := by
  obtain ⟨-, hM, -⟩ := hO T .PSL 2 5 2 h.admissible h
  have hd : lieOrderDivisor .PSL 2 (5 ^ 2) = 2 := by decide
  have hn : lieOrderNumerator .PSL 2 (5 ^ 2) = 15600 := by
    simp [lieOrderNumerator, show Finset.Icc 2 2 = {2} by decide]
  rw [hd, hn] at hM
  omega

private theorem w183b5_card_PSp_2_5_1 {T : Type} [Group T] (hO : LieOrderFormulasInput)
    (h : LieModel T .PSp 2 5 1) : Nat.card T = 4680000 := by
  obtain ⟨-, hM, -⟩ := hO T .PSp 2 5 1 h.admissible h
  have hd : lieOrderDivisor .PSp 2 (5 ^ 1) = 2 := by decide
  have hn : lieOrderNumerator .PSp 2 (5 ^ 1) = 9360000 := by
    simp [lieOrderNumerator, show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair]
  rw [hd, hn] at hM
  omega

private theorem w183b5_card_PSp_2_3_1 {T : Type} [Group T] (hO : LieOrderFormulasInput)
    (h : LieModel T .PSp 2 3 1) : Nat.card T = 25920 := by
  obtain ⟨-, hM, -⟩ := hO T .PSp 2 3 1 h.admissible h
  have hd : lieOrderDivisor .PSp 2 (3 ^ 1) = 2 := by decide
  have hn : lieOrderNumerator .PSp 2 (3 ^ 1) = 51840 := by
    simp [lieOrderNumerator, show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair]
  rw [hd, hn] at hM
  omega

private theorem w183b5_card_alt6 {X : Type} [Group X]
    (h : Nonempty (X ≃* alternatingGroup (Fin 6))) : Nat.card X = 360 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  norm_num

private theorem w183b5_nonab_of_simple_of_not_prime {X : Type} [Group X] (hs : IsSimpleGroup X)
    (hn : ¬ (Nat.card X).Prime) : ∃ a b : X, a * b ≠ b * a := by
  by_contra hnab
  have hcomm : ∀ a b : X, a * b = b * a := fun a b => by
    by_contra hab
    exact hnab ⟨a, b, hab⟩
  letI : CommGroup X := { ‹Group X› with mul_comm := hcomm }
  haveI : IsSimpleGroup X := hs
  exact hn (IsSimpleGroup.prime_card (α := X))

private theorem w183b5_nonab_of_card {X : Type} [Group X] (hs : IsSimpleGroup X) {m : ℕ}
    (hcard : Nat.card X = m) (hm : ¬ m.Prime) : ∃ a b : X, a * b ≠ b * a :=
  w183b5_nonab_of_simple_of_not_prime hs (hcard.symm ▸ hm)

private theorem w183b5_triple_of_LieModel {X : Type} [Group X] {t : StatedLieTag} {n p f m : ℕ}
    (h : LieModel X t n p f) (ht : t ∈ CFSG.Blueprint.classicalTags) (hcard : Nat.card X = m)
    (hm : ¬ m.Prime) : Finite X ∧ IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a := by
  have hs : IsSimpleGroup X := CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags ht h
  exact ⟨CFSG.LieType.Simplicity.finite_of_statedClassicalModel (h.statedClassicalModel ht), hs,
    w183b5_nonab_of_card hs hcard hm⟩

private theorem w183b5_triple_of_L2_odd {X : Type} [Group X] {p e : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h3 : 3 < p ^ e) (h : CFSG.Quasithin.F6.IsL2 p e X) :
    Finite X ∧ IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a := by
  have hfin : Finite X := CFSG.LieType.Simplicity.finite_of_statedClassicalModel h
  haveI : Finite X := hfin
  obtain ⟨hs, hnab, -⟩ := asch5_simpOutSolv_holds X (Or.inl ⟨p, e, hp, hp2, h3, h⟩)
  exact ⟨hfin, hs, hnab⟩

private theorem w183b5_triple_of_L3_odd {X : Type} [Group X] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : LieModel X .PSL 3 p 1 ∨ LieModel X .PSU 3 p 1) :
    Finite X ∧ IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a := by
  have hfin : Finite X := by
    rcases h with h | h
    · exact CFSG.LieType.Simplicity.finite_of_statedClassicalModel
        (h.statedClassicalModel (by decide))
    · exact CFSG.LieType.Simplicity.finite_of_statedClassicalModel
        (h.statedClassicalModel (by decide))
  haveI : Finite X := hfin
  obtain ⟨hs, hnab, -⟩ := asch5_simpOutSolv_holds X (Or.inr ⟨p, 1, hp, hp2, h⟩)
  exact ⟨hfin, hs, hnab⟩

private theorem w183b5_not_prime_card_PSp_two {X : Type} [Group X] (hO : LieOrderFormulasInput)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : LieModel X .PSp 2 p 1) :
    ¬ (Nat.card X).Prime := by
  obtain ⟨hfin, -, hfac⟩ := hO X .PSp 2 p 1 h.admissible h
  have hfac' : (Nat.card X).factorization p = 4 := by
    rw [hfac]
    decide
  haveI : Finite X := hfin
  haveI : Nonempty X := ⟨1⟩
  have hne : Nat.card X ≠ 0 := Nat.card_ne_zero.mpr ⟨inferInstance, hfin⟩
  have hdvd : p ^ 4 ∣ Nat.card X :=
    (hp.pow_dvd_iff_le_factorization hne).2 (le_of_eq hfac'.symm)
  have hle : p ^ 4 ≤ Nat.card X := Nat.le_of_dvd Nat.card_pos hdvd
  have hlt : p < Nat.card X := by
    have hp4 : p < p ^ 4 := by
      simpa using (Nat.pow_lt_pow_iff_right hp.one_lt).2 (by norm_num : 1 < 4)
    exact lt_of_lt_of_le hp4 hle
  intro hprime
  have heq : p = Nat.card X :=
    (Nat.prime_dvd_prime_iff_eq hp hprime).mp (dvd_trans (by norm_num : p ∣ p ^ 4) hdvd)
  exact (lt_irrefl p) (heq.symm ▸ hlt)

private theorem w183b5_triple_of_PSp_two_odd {X : Type} [Group X] (hO : LieOrderFormulasInput)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : LieModel X .PSp 2 p 1) :
    Finite X ∧ IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a := by
  have hst : StatedClassicalModel X .PSp 2 p 1 := h.statedClassicalModel (by decide)
  have hs : IsSimpleGroup X :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp X 2 p 1 hst
  exact ⟨CFSG.LieType.Simplicity.finite_of_statedClassicalModel hst, hs,
    w183b5_nonab_of_simple_of_not_prime hs (w183b5_not_prime_card_PSp_two hO hp hp2 h)⟩

theorem isSimple_nonab_of_shape (hO : LieOrderFormulasInput) {X : Type} [Group X]
    (hX : IsL2 X 2 ∨ IsU3 X 2 ∨ IsAlt X 6 ∨ IsL3 X 1 ∨ IsL3 X 2 ∨ IsSp4 X 2 ∨
      (∃ p e : ℕ, p.Prime ∧ p ≠ 2 ∧ 9 < p ^ e ∧ CFSG.Quasithin.F6.IsL2 p e X) ∨
      (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
        (LieModel X .PSL 3 p 1 ∨ LieModel X .PSU 3 p 1 ∨ LieModel X .PSp 2 p 1))) :
    Finite X ∧ IsSimpleGroup X ∧ ∃ u v : X, u * v ≠ v * u := by
  rcases hX with hL24 | hU34 | hA6 | hL32 | hL34 | hSp44 | hOddL2 | hOddLie
  · exact w183b5_triple_of_LieModel hL24 (by decide) (w183b5_card_PSL_2_2_2 hO hL24)
      (by norm_num)
  · exact w183b5_triple_of_LieModel hU34 (by decide) (w183b5_card_PSU_3_2_2 hO hU34)
      (by norm_num)
  · obtain ⟨e⟩ := hA6
    have hcard : Nat.card X = 360 := w183b5_card_alt6 ⟨e⟩
    have hs : IsSimpleGroup X :=
      (MulEquiv.isSimpleGroup_congr e).mpr (alternatingGroup.isSimpleGroup (by simp))
    exact ⟨Finite.of_injective (e : X → alternatingGroup (Fin 6)) e.injective, hs,
      w183b5_nonab_of_card hs hcard (by norm_num)⟩
  · exact w183b5_triple_of_LieModel hL32 (by decide) (w183b5_card_PSL_3_2_1 hO hL32)
      (by norm_num)
  · exact w183b5_triple_of_LieModel hL34 (by decide) (w183b5_card_PSL_3_2_2 hO hL34)
      (by norm_num)
  · exact w183b5_triple_of_LieModel hSp44 (by decide) (w183b5_card_PSp_2_2_2 hO hSp44)
      (by norm_num)
  · obtain ⟨p, e, hp, hp2, h9, hL2⟩ := hOddL2
    exact w183b5_triple_of_L2_odd hp hp2 (by omega) hL2
  · obtain ⟨p, hp, hp2, hrest⟩ := hOddLie
    rcases hrest with hPSL3 | hPSU3 | hPSp4
    · exact w183b5_triple_of_L3_odd hp hp2 (Or.inl hPSL3)
    · exact w183b5_triple_of_L3_odd hp hp2 (Or.inr hPSU3)
    · exact w183b5_triple_of_PSp_two_odd hO hp hp2 hPSp4

@[expose] def Tail1812Orders (n : ℕ) : Prop :=
  n = 60 ∨ n = 62400 ∨ n = 360 ∨ n = 979200 ∨ n = 7800 ∨ n = 4680000 ∨ n = 25920

theorem card_mem_of_tail1812Shape (hO : LieOrderFormulasInput) {X : Type} [Group X]
    (hX : CFSG.Quasithin.F6.IsL2 2 2 X ∨ LieModel X .PSU 3 2 2 ∨
      Nonempty (X ≃* alternatingGroup (Fin 6)) ∨ LieModel X .PSp 2 2 2 ∨
      CFSG.Quasithin.F6.IsL2 5 2 X ∨ LieModel X .PSp 2 5 1 ∨ LieModel X .PSp 2 3 1) :
    Tail1812Orders (Nat.card X) := by
  rcases hX with hL24 | hU34 | hA6 | hSp44 | hL25 | hPSp45 | hPSp43
  · exact Or.inl (w183b5_card_PSL_2_2_2 hO (Or.inl ⟨by decide, hL24⟩))
  · exact Or.inr (Or.inl (w183b5_card_PSU_3_2_2 hO hU34))
  · exact Or.inr (Or.inr (Or.inl (w183b5_card_alt6 hA6)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (w183b5_card_PSp_2_2_2 hO hSp44))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (w183b5_card_PSL_2_5_2 hO (Or.inl ⟨by decide, hL25⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (w183b5_card_PSp_2_5_1 hO hPSp45))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (w183b5_card_PSp_2_3_1 hO hPSp43))))))

end CFSG.LocalAnalysis.WeakClosure81

end
