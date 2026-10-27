module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestBasic
public import CFSG.Quasithin.Background.G2UGroups
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineGroups
public import CFSG.ClassicalGroups.Unitary.Simple

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.Quasithin.G2U

namespace TableBExcSmallRest

@[expose] def su3xc : List ℕ := [0, 1, 0, 0, 0, 1, 1, 0, 0]

@[expose] def su3xic : List ℕ := [0, 0, 1, 1, 0, 0, 0, 1, 0]

@[expose] def su3yc : List ℕ := [0, 5, 8, 5, 6, 2, 8, 2, 3]

@[expose] def su3yic : List ℕ := [0, 8, 5, 8, 3, 2, 5, 2, 6]

@[expose] def su3Codes : List (List ℕ) :=
  [[0, 0, 1, 1, 0, 0, 0, 1, 0], [0, 1, 0, 0, 0, 1, 1, 0, 0], [0, 5, 8, 5, 6, 2, 8, 2, 3],
    [0, 8, 5, 8, 3, 2, 5, 2, 6], [1, 0, 0, 0, 1, 0, 0, 0, 1], [2, 3, 8, 5, 8, 0, 6, 2, 5],
    [2, 5, 6, 3, 8, 2, 8, 0, 5], [2, 6, 5, 8, 5, 0, 3, 2, 8], [2, 8, 3, 6, 5, 2, 5, 0, 8],
    [3, 2, 8, 2, 6, 5, 8, 5, 0], [3, 3, 4, 4, 3, 3, 3, 4, 3], [3, 4, 3, 3, 3, 4, 4, 3, 3],
    [3, 8, 2, 8, 0, 5, 2, 5, 6], [4, 3, 3, 3, 4, 3, 3, 3, 4], [5, 0, 8, 2, 8, 3, 6, 5, 2],
    [5, 2, 6, 0, 8, 5, 8, 3, 2], [5, 6, 2, 8, 2, 3, 0, 5, 8], [5, 8, 0, 6, 2, 5, 2, 3, 8],
    [6, 2, 5, 2, 3, 8, 5, 8, 0], [6, 5, 2, 5, 0, 8, 2, 8, 3], [6, 6, 7, 7, 6, 6, 6, 7, 6],
    [6, 7, 6, 6, 6, 7, 7, 6, 6], [7, 6, 6, 6, 7, 6, 6, 6, 7], [8, 0, 5, 2, 5, 6, 3, 8, 2],
    [8, 2, 3, 0, 5, 8, 5, 6, 2], [8, 3, 2, 5, 2, 6, 0, 8, 5], [8, 5, 0, 3, 2, 8, 2, 6, 5]]

theorem su3Codes_closed : (su3Codes.all fun m =>
    [su3xc, su3yc, su3xic, su3yic].all fun s => su3Codes.contains (mul3 m s)) = true := by
  decide

theorem su3Codes_cube : (su3Codes.all fun m => mul3 (mul3 m m) m == id3) = true := by
  decide

@[expose] def su3X : GL (Fin 3) F9 :=
  unit3 su3xc su3xic (by decide) (by decide)

@[expose] def su3Y : GL (Fin 3) F9 :=
  unit3 su3yc su3yic (by decide) (by decide)

theorem su3X_mem : su3X ∈ StatedSU 3 3 F9 := by
  rw [← SetLike.mem_coe, CFSG.LinearGroups.UnitaryThreeOverNine.coe_statedSU card_F9]
  exact (by rw [Matrix.det_fin_three]; decide :
    Matrix.transpose ((dec3 su3xc).map (· ^ 3)) * dec3 su3xc = 1 ∧ (dec3 su3xc).det = 1)

theorem su3Y_mem : su3Y ∈ StatedSU 3 3 F9 := by
  rw [← SetLike.mem_coe, CFSG.LinearGroups.UnitaryThreeOverNine.coe_statedSU card_F9]
  exact (by rw [Matrix.det_fin_three]; decide :
    Matrix.transpose ((dec3 su3yc).map (· ^ 3)) * dec3 su3yc = 1 ∧ (dec3 su3yc).det = 1)

theorem su3X_mul_su3Y_ne : su3X * su3Y ≠ su3Y * su3X := by
  intro h
  have h1 := congrArg (fun g : GL (Fin 3) F9 => (g : Matrix (Fin 3) (Fin 3) F9)) h
  simp only [Units.val_mul, su3X, su3Y, unit3] at h1
  rw [← dec3_mul3, ← dec3_mul3] at h1
  exact absurd h1 (by decide)

@[expose] def su3P : Subgroup (StatedSU 3 3 F9) :=
  Subgroup.closure {⟨su3X, su3X_mem⟩, ⟨su3Y, su3Y_mem⟩}

theorem mem_su3Codes_mul {m s : List ℕ} (hm : m ∈ su3Codes)
    (hs : s = su3xc ∨ s = su3yc ∨ s = su3xic ∨ s = su3yic) : mul3 m s ∈ su3Codes := by
  have h := List.all_eq_true.mp su3Codes_closed m hm
  have h' := List.all_eq_true.mp h s (by rcases hs with rfl | rfl | rfl | rfl <;> simp)
  simpa using h'

theorem exists_code_of_mem_su3P {g : StatedSU 3 3 F9} (hg : g ∈ su3P) :
    ∃ m ∈ su3Codes, ((g : GL (Fin 3) F9) : Matrix (Fin 3) (Fin 3) F9) = dec3 m := by
  induction hg using Subgroup.closure_induction_right with
  | one => exact ⟨id3, by decide, by rw [dec3_id3]; rfl⟩
  | mul_right g _ s hs ih =>
    obtain ⟨m, hm, hgm⟩ := ih
    rcases hs with rfl | rfl
    · refine ⟨mul3 m su3xc, mem_su3Codes_mul hm (Or.inl rfl), ?_⟩
      simp only [Subgroup.coe_mul, Units.val_mul, hgm, dec3_mul3]
      rfl
    · refine ⟨mul3 m su3yc, mem_su3Codes_mul hm (Or.inr (Or.inl rfl)), ?_⟩
      simp only [Subgroup.coe_mul, Units.val_mul, hgm, dec3_mul3]
      rfl
  | mul_inv_cancel g _ s hs ih =>
    obtain ⟨m, hm, hgm⟩ := ih
    rcases hs with rfl | rfl
    · refine ⟨mul3 m su3xic, mem_su3Codes_mul hm (Or.inr (Or.inr (Or.inl rfl))), ?_⟩
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, hgm, dec3_mul3]
      rfl
    · refine ⟨mul3 m su3yic, mem_su3Codes_mul hm (Or.inr (Or.inr (Or.inr rfl))), ?_⟩
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, hgm, dec3_mul3]
      rfl

theorem isPGroup_su3P : IsPGroup 3 su3P := by
  intro g
  refine ⟨1, ?_⟩
  obtain ⟨m, hm, hgm⟩ := exists_code_of_mem_su3P g.2
  have hc : mul3 (mul3 m m) m = id3 := by
    simpa using List.all_eq_true.mp su3Codes_cube m hm
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  simp only [pow_one, Subgroup.coe_pow, Units.val_pow_eq_pow_val, Subgroup.coe_one,
    Units.val_one]
  rw [hgm, pow_succ, pow_succ, pow_one, ← dec3_mul3, ← dec3_mul3, hc, dec3_id3]

theorem card_lt_of_isElemAbelian_su3 {E : Subgroup (StatedSU 3 3 F9)} (hE : IsElemAbelian 3 E) :
    Nat.card E < 3 ^ 3 := by
  refine card_lt_of_nonabelian_isPGroup Nat.prime_three ?_ isPGroup_su3P
    (x := ⟨su3X, su3X_mem⟩) (y := ⟨su3Y, su3Y_mem⟩)
    (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)) ?_ hE
  · rw [CFSG.LinearGroups.UnitaryThreeOverNine.card_statedSU card_F9]
    norm_num
  · intro h
    exact su3X_mul_su3Y_ne (congrArg Subtype.val h)

theorem center_su3_eq_bot : Subgroup.center (StatedSU 3 3 F9) = ⊥ := by
  have hs := (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 3 3 1
    (CFSG.LinearGroups.UnitaryThreeOverNine.classicalModel_statedSU card_F9)).2
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center (StatedSU 3 3 F9)) with h | h
  · exact h
  · exfalso
    have hx : (⟨su3X, su3X_mem⟩ : StatedSU 3 3 F9) ∈ Subgroup.center (StatedSU 3 3 F9) := by
      rw [h]
      exact Subgroup.mem_top _
    have hc := Subgroup.mem_center_iff.mp hx ⟨su3Y, su3Y_mem⟩
    exact su3X_mul_su3Y_ne (congrArg Subtype.val hc).symm

theorem nonempty_g2der_equiv_su3
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2) :
    Nonempty (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K true) ≃*
      StatedSU 3 3 F9) := by
  obtain ⟨e₁⟩ := centerQuot_commutator_chevGroup_equiv K .G2
  have := Fintype.ofFinite K
  have hc : Fintype.card K = Fintype.card (ZMod 2) := by
    rw [← Nat.card_eq_fintype_card, hK, ZMod.card]
  let e := (commutatorAdjointEquiv (FiniteField.ringEquivOfCardEq hc)).trans
    commutatorRootGroupEquiv
  have hZ := center_eq_bot_of_mulEquiv e center_su3_eq_bot
  exact ⟨e₁.trans (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans
    e)⟩

theorem eq_three_of_largeEvenSplit_G2der {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (ht : lab.tag = .G2der) (hlab : LargeEvenInLambda2 lab) (hs : LargeEvenSplit p lab) :
    p = 3 := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hlab hs ⊢
  subst ht
  have hn : n = 1 := hlab.2.2
  subst hn
  rcases hs with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
  · exact absurd (Nat.dvd_one.mp h) hp.one_lt.ne'
  · exact absurd trivial h
  · rcases h with h | h <;> cases h
  · exact h

theorem largeEvenLabelAll_card_lt_G2der
    {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .G2der) (hs : LargeEvenSplit p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ X : Subgroup (MulAut R),
      (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X → Nat.card X < p ^ 3 := by
  have hp3 := eq_three_of_largeEvenSplit_G2der hp ht hlab hs
  subst hp3
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht
  subst ht
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hq⟩ := hQ
  refine ⟨K, i1, i2, hK, hq, fun X hXI hX => ?_⟩
  obtain ⟨e⟩ := nonempty_g2der_equiv_su3 K hK
  have : Finite (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K true)) :=
    Finite.of_equiv _ e.symm.toEquiv
  have := CFSG.Monster.Existence.Compat.subsingleton_units_of_card_two hK
  have hI := chevIDImage_subset_inn_of_subsingleton (A := LargeEvenCartanG2)
    (LargeEvenChevH LargeEvenCartanG2 K true)
  refine card_lt_of_subset_inn (center_eq_bot_of_mulEquiv e center_su3_eq_bot)
    (fun A hA => card_lt_of_mulEquiv e (fun E hE => card_lt_of_isElemAbelian_su3 hE) hA)
    (fun φ hφ => ?_) hX
  obtain ⟨r, hr⟩ := hI (hXI hφ)
  exact ⟨r, hr⟩

end TableBExcSmallRest

end CFSG.StandardType
