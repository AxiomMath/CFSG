module

public import CFSG.Quasithin.Background.SmithB45MatRep
public import CFSG.Quasithin.Background.HMathieuNorm
public import Certificates.Certificate260402

public section

namespace CFSG.Quasithin.B45Mat.M22

open CFSG.CharacterTheory.SteinbergBY CFSG.QuasithinUnique.Setup.X1 CFSG.Sporadic.Mathieu
  CFSG.Blueprint CFSG.Monster.B.TwoA CFSG.Quasithin.H.Mathieu FieldFour Matrix
open CFSG.Monster.Code (bvec bvec_apply)
open scoped Kronecker

theorem m22_module_checks :
    subOK (kronBB m22a) (kronBB m22b) B34 P34 = true ∧
    subOK (kronAB m22a) (kronAB m22b) B99 P99 = true ∧
    quotOK (tab99 m22a) (tab99 m22b) B98 P98 = true ∧
    subOK (tab340 m22a) (tab340 m22b) B70a P70a = true ∧
    subOK (tab340 m22a) (tab340 m22b) B70b P70b = true ∧
    c10a.check (tab10a m22a) (tab10a m22b) = true ∧
    c10b.check (tab10b m22a) (tab10b m22b) = true ∧
    c34.check (tab34 m22a) (tab34 m22b) = true ∧
    c98.check (tab98 m22a) (tab98 m22b) = true ∧
    c70a.check (tab70a m22a) (tab70a m22b) = true ∧
    c70b.check (tab70b m22a) (tab70b m22b) = true ∧
    Matrix.trace (untab (tab10a g7)) = 0 ∧ Matrix.trace (untab (tab10b g7)) = 1 ∧
    Matrix.trace (untab (tab70a g11)) = ω ∧ Matrix.trace (untab (tab70b g11)) = ω₂ :=
  Certificates.certificate260402

theorem jCat_arr : ∀ k : Fin 22, (jCat k : ℕ) = jCatArr[(k : ℕ)]! := by
  decide

theorem jInv_arr : ∀ m : Fin 24, ¬ (m : ℕ) < 2 →
    ∃ i : Fin 22, jCat i = m ∧ jInvArr[(m : ℕ)]! = (i : ℕ) := by
  decide

theorem psiArr_get (g : Equiv.Perm (Fin 22)) (m : Fin 24) :
    (psiArr g)[(m : ℕ)]! = if (m : ℕ) < 2 then (m : ℕ) else
      jCatArr[(Array.ofFn fun i : Fin 22 => (g i : ℕ))[jInvArr[(m : ℕ)]!]!]! := by
  unfold psiArr
  rw [getElem!_pos _ _ (by simp), Array.getElem_ofFn]

theorem hasArr_psiArr (g : Equiv.Perm (Fin 22)) : HasArr (psiHom g) (psiArr g) := by
  intro m
  rw [psiArr_get]
  split_ifs with h
  · have hm01 : m = 0 ∨ m = 1 := by
      rcases m with ⟨_ | _ | m, hm⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
      · simp at h
    rcases hm01 with rfl | rfl
    · rw [psiHom_zero]
    · rw [psiHom_one]
  · obtain ⟨i, hi, hiv⟩ := jInv_arr m h
    rw [hiv, ← hi, psiHom_jCat]
    have hga : (Array.ofFn fun k : Fin 22 => (g k : ℕ))[(i : ℕ)]! = (g i : ℕ) := by
      rw [getElem!_pos _ _ (by simp), Array.getElem_ofFn]
    rw [hga]
    exact jCat_arr (g i)

noncomputable abbrev psiS22 :
    G22 →* ↥mog22 :=
  mog22EquivM22.symm.toMonoidHom

theorem coe_psiS22 (g : G22) :
    ((psiS22 g : ↥mog22) : Equiv.Perm (Fin 24)) = psiHom (g : Equiv.Perm (Fin 22)) :=
  rfl

theorem bvec_two_pow (n : ℕ) (j : Fin n) : bvec n (2 ^ (j : ℕ)) = Pi.single j 1 := by
  funext i
  rw [bvec_apply, Nat.testBit_two_pow, Pi.single_apply]
  by_cases h : i = j
  · subst h
    simp
  · have : (j : ℕ) ≠ i := fun h' => h (Fin.ext h'.symm)
    simp [h, this]

noncomputable def rep10a :
    G22 →* Matrix (Fin 10) (Fin 10) (ZMod 2) :=
  (mulAutMat 10).comp ((rho10 mog22 mog22_le_mog22plus).comp psiS22)

noncomputable def rep10b :
    G22 →* Matrix (Fin 10) (Fin 10) (ZMod 2) :=
  (mulAutMat 10).comp ((rhoC10 mog22 mog22_le_mog22plus).comp psiS22)

theorem rep10a_apply (g : G22) :
    rep10a g = mulAutMat 10 (rho10 mog22 mog22_le_mog22plus (psiS22 g)) := by
  rw [rep10a, MonoidHom.comp_apply, MonoidHom.comp_apply]

theorem rep10b_apply (g : G22) :
    rep10b g = mulAutMat 10 (rhoC10 mog22 mog22_le_mog22plus (psiS22 g)) := by
  rw [rep10b, MonoidHom.comp_apply, MonoidHom.comp_apply]

theorem untab_tab10a (g : G22) :
    untab (tab10a g) = rep10a g := by
  ext i j
  rw [untab_apply, rep10a, MonoidHom.comp_apply, MonoidHom.comp_apply, mulAutMat_apply]
  have h1 : (Multiplicative.ofAdd (Pi.single j 1 : Fin 10 → ZMod 2)) = toW 10 (2 ^ (j : ℕ)) := by
    rw [toW, bvec_two_pow]
  have ha : HasArr ((psiS22 g : ↥mog22) : Equiv.Perm (Fin 24)) (psiArr g) := by
    rw [coe_psiS22]
    exact hasArr_psiArr _
  rw [h1, rho10_toW _ _ _ ha, toAdd_toW, bvec_apply]
  simp [tab10a, maskTab]

theorem untab_tab10b (g : G22) :
    untab (tab10b g) = rep10b g := by
  ext i j
  rw [untab_apply, rep10b, MonoidHom.comp_apply, MonoidHom.comp_apply, mulAutMat_apply]
  have h1 : (Multiplicative.ofAdd (Pi.single j 1 : Fin 10 → ZMod 2)) = toW 10 (2 ^ (j : ℕ)) := by
    rw [toW, bvec_two_pow]
  have ha : HasArr ((psiS22 g : ↥mog22) : Equiv.Perm (Fin 24)) (psiArr g) := by
    rw [coe_psiS22]
    exact hasArr_psiArr _
  rw [h1, rhoC10_toW _ _ _ ha, toAdd_toW, bvec_apply]
  simp [tab10b, maskTab]

theorem closure_m22ab : Subgroup.closure ({m22a, m22b} : Set G22) = ⊤ :=
  closure_pair_eq_top m22_eq _ _

theorem forall_gens {F : Type*} {n : ℕ} {R : G22 → Prop} {Ka Kb : Vector (Vector F n) n}
    {p : Vector (Vector F n) n → Prop} (h : ∀ K ∈ [Ka, Kb], p K) (ha : p Ka → R m22a)
    (hb : p Kb → R m22b) : ∀ s ∈ ({m22a, m22b} : Set G22), R s := by
  rintro s (rfl | rfl)
  · exact ha (h Ka (by simp))
  · exact hb (h Kb (by simp))

section Kron


noncomputable abbrev repBB : G22 →* Matrix (Fin (10 * 10)) (Fin (10 * 10)) (ZMod 2) :=
  kronRep rep10b rep10b

noncomputable abbrev repAB : G22 →* Matrix (Fin (10 * 10)) (Fin (10 * 10)) (ZMod 2) :=
  kronRep rep10a rep10b

theorem untab_kronBB (g : G22) : untab (kronBB g) = repBB g := by
  rw [kronBB, untab_kronTab, untab_tab10b, kronRep_apply]

theorem untab_kronAB (g : G22) : untab (kronAB g) = repAB g := by
  rw [kronAB, untab_kronTab, untab_tab10a, untab_tab10b, kronRep_apply]

end Kron

section Reps


theorem inv34 : untab P34 * untab B34 = 1 ∧
    ∀ g, repBB g * untab B34 = untab B34 * (untab P34 * repBB g * untab B34) := by
  obtain ⟨hPB, hgen⟩ := subOK_spec m22_module_checks.1
  refine ⟨hPB, subInv_of_closure closure_m22ab _ _ _ hPB (forall_gens hgen ?_ ?_)⟩ <;>
    · intro h
      simpa only [untab_kronBB] using h

noncomputable def rep34 : G22 →* Matrix (Fin 34) (Fin 34) (ZMod 2) :=
  subRep repBB (untab B34) (untab P34) inv34.1 inv34.2

theorem untab_tab34 (g : G22) : untab (tab34 g) = rep34 g := by
  rw [tab34, untab_mulT, untab_mulT, untab_kronBB, rep34, subRep_apply]

theorem inv99 : untab P99 * untab B99 = 1 ∧
    ∀ g, repAB g * untab B99 = untab B99 * (untab P99 * repAB g * untab B99) := by
  obtain ⟨hPB, hgen⟩ := subOK_spec m22_module_checks.2.1
  refine ⟨hPB, subInv_of_closure closure_m22ab _ _ _ hPB (forall_gens hgen ?_ ?_)⟩ <;>
    · intro h
      simpa only [untab_kronAB] using h

noncomputable def rep99 : G22 →* Matrix (Fin 99) (Fin 99) (ZMod 2) :=
  subRep repAB (untab B99) (untab P99) inv99.1 inv99.2

theorem untab_tab99 (g : G22) : untab (tab99 g) = rep99 g := by
  rw [tab99, untab_mulT, untab_mulT, untab_kronAB, rep99, subRep_apply]

theorem inv98 : untab P98 * untab B98 = 1 ∧
    ∀ g, untab P98 * rep99 g = untab P98 * rep99 g * untab B98 * untab P98 := by
  obtain ⟨hPB, hgen⟩ := quotOK_spec m22_module_checks.2.2.1
  refine ⟨hPB, quotInv_of_closure closure_m22ab _ _ _ hPB (forall_gens hgen ?_ ?_)⟩ <;>
    · intro h
      simpa only [untab_tab99] using h

noncomputable def rep98 : G22 →* Matrix (Fin 98) (Fin 98) (ZMod 2) :=
  quotRep rep99 (untab B98) (untab P98) inv98.1 inv98.2

theorem untab_tab98 (g : G22) : untab (tab98 g) = rep98 g := by
  rw [tab98, untab_mulT, untab_mulT, untab_tab99, rep98, quotRep_apply]

noncomputable abbrev rep10bF : G22 →* Matrix (Fin 10) (Fin 10) FieldFour :=
  (ofPrime.mapMatrix : Matrix (Fin 10) (Fin 10) (ZMod 2) →+* _).toMonoidHom.comp rep10b

noncomputable abbrev rep34F : G22 →* Matrix (Fin 34) (Fin 34) FieldFour :=
  (ofPrime.mapMatrix : Matrix (Fin 34) (Fin 34) (ZMod 2) →+* _).toMonoidHom.comp rep34

noncomputable abbrev rep340 : G22 →* Matrix (Fin (10 * 34)) (Fin (10 * 34)) FieldFour :=
  kronRep rep10bF rep34F

theorem untab_tab340 (g : G22) : untab (tab340 g) = rep340 g := by
  rw [tab340, untab_kronTab, untab_mapTab, untab_mapTab, untab_tab10b, untab_tab34,
    kronRep_apply]
  rfl

theorem inv70a : untab P70a * untab B70a = 1 ∧
    ∀ g, rep340 g * untab B70a = untab B70a * (untab P70a * rep340 g * untab B70a) := by
  obtain ⟨hPB, hgen⟩ := subOK_spec m22_module_checks.2.2.2.1
  refine ⟨hPB, subInv_of_closure closure_m22ab _ _ _ hPB (forall_gens hgen ?_ ?_)⟩ <;>
    · intro h
      simpa only [untab_tab340] using h

theorem inv70b : untab P70b * untab B70b = 1 ∧
    ∀ g, rep340 g * untab B70b = untab B70b * (untab P70b * rep340 g * untab B70b) := by
  obtain ⟨hPB, hgen⟩ := subOK_spec m22_module_checks.2.2.2.2.1
  refine ⟨hPB, subInv_of_closure closure_m22ab _ _ _ hPB (forall_gens hgen ?_ ?_)⟩ <;>
    · intro h
      simpa only [untab_tab340] using h

noncomputable def rep70a : G22 →* Matrix (Fin 70) (Fin 70) FieldFour :=
  subRep rep340 (untab B70a) (untab P70a) inv70a.1 inv70a.2

noncomputable def rep70b : G22 →* Matrix (Fin 70) (Fin 70) FieldFour :=
  subRep rep340 (untab B70b) (untab P70b) inv70b.1 inv70b.2

theorem untab_tab70a (g : G22) : untab (tab70a g) = rep70a g := by
  rw [tab70a, untab_mulT, untab_mulT, untab_tab340, rep70a, subRep_apply]

theorem untab_tab70b (g : G22) : untab (tab70b g) = rep70b g := by
  rw [tab70b, untab_mulT, untab_mulT, untab_tab340, rep70b, subRep_apply]

variable {K : Type*} [Field K]

theorem isIrreducible_rep10a (φ : ZMod 2 →+* K) : (matrixBaseChange φ rep10a).IsIrreducible :=
  c10a.isIrreducible_of_check φ rep10a (untab_tab10a m22a) (untab_tab10a m22b)
    m22_module_checks.2.2.2.2.2.1

theorem isIrreducible_rep10b (φ : ZMod 2 →+* K) : (matrixBaseChange φ rep10b).IsIrreducible :=
  c10b.isIrreducible_of_check φ rep10b (untab_tab10b m22a) (untab_tab10b m22b)
    m22_module_checks.2.2.2.2.2.2.1

theorem isIrreducible_rep34 (φ : ZMod 2 →+* K) : (matrixBaseChange φ rep34).IsIrreducible :=
  c34.isIrreducible_of_check φ rep34 (untab_tab34 m22a) (untab_tab34 m22b)
    m22_module_checks.2.2.2.2.2.2.2.1

theorem isIrreducible_rep98 (φ : ZMod 2 →+* K) : (matrixBaseChange φ rep98).IsIrreducible :=
  c98.isIrreducible_of_check φ rep98 (untab_tab98 m22a) (untab_tab98 m22b)
    m22_module_checks.2.2.2.2.2.2.2.2.1

theorem isIrreducible_rep70a (φ : FieldFour →+* K) : (matrixBaseChange φ rep70a).IsIrreducible :=
  c70a.isIrreducible_of_check φ rep70a (untab_tab70a m22a) (untab_tab70a m22b)
    m22_module_checks.2.2.2.2.2.2.2.2.2.1

theorem isIrreducible_rep70b (φ : FieldFour →+* K) : (matrixBaseChange φ rep70b).IsIrreducible :=
  c70b.isIrreducible_of_check φ rep70b (untab_tab70b m22a) (untab_tab70b m22b)
    m22_module_checks.2.2.2.2.2.2.2.2.2.2.1

theorem trace_rep10a_g7 : Matrix.trace (rep10a g7) = 0 := by
  rw [← untab_tab10a]
  exact m22_module_checks.2.2.2.2.2.2.2.2.2.2.2.1

theorem trace_rep10b_g7 : Matrix.trace (rep10b g7) = 1 := by
  rw [← untab_tab10b]
  exact m22_module_checks.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem trace_rep70a_g11 : Matrix.trace (rep70a g11) = ω := by
  rw [← untab_tab70a]
  exact m22_module_checks.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem trace_rep70b_g11 : Matrix.trace (rep70b g11) = ω₂ := by
  rw [← untab_tab70b]
  exact m22_module_checks.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end Reps

end CFSG.Quasithin.B45Mat.M22
