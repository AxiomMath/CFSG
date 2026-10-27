module

public import CFSG.Sporadic.HeldB.InnerCheck
public import CFSG.Sporadic.HeldB.Common
public import CFSG.Sporadic.HeldB.CertPChain
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import Certificates.Certificate2112
public import Certificates.Certificate2114

public noncomputable section

namespace CFSG.Sporadic.HeldB

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native Pointwise

section General

variable {N m : ℕ} {P : Subgroup (Equiv.Perm (Fin N))} {t : Equiv.Perm (Fin N)}
  {C : Subgroup (Equiv.Perm (Fin N))} {δ : Fin m → Fin N}

theorem eq_bot_of_le_ker_two {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hker : Nat.card f.ker = 2) (K : Subgroup G) (hK : K ≤ f.ker) (hodd : Odd (Nat.card K)) :
    K = ⊥ := by
  have hdvd : Nat.card K ∣ 2 := hker ▸ Subgroup.card_dvd_of_le hK
  have h1 : Nat.card K = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact h
    · rw [h] at hodd
      exact absurd hodd (by decide)
  exact Subgroup.card_eq_one.1 h1

theorem oddCore_eq_bot_of_restrict (hCle : C ≤ centralizerIn P t) (htC : t ∈ C) (ht1 : t ≠ 1)
    (hδ : Function.Injective δ)
    (hstab : C ≤ MulAction.stabilizer (Equiv.Perm (Fin N)) (Set.range δ))
    (htfix : ∀ k, t (δ k) = δ k) {X : Subgroup (Equiv.Perm (Fin m))}
    (hrange : (restrictHom hδ C hstab).range = X) {mo v : ℕ} (hX : Nat.card X = 2 ^ v * mo)
    (hw : OddWitness X mo) (hcard : Nat.card (centralizerIn P t) = 2 * Nat.card X) :
    C = centralizerIn P t ∧ CFSG.oddCore C = ⊥ := by
  set ψ := restrictHom hδ C hstab
  have hfin : Finite C := inferInstance
  have hkt : (⟨t, htC⟩ : C) ∈ ψ.ker := by
    rw [MonoidHom.mem_ker]
    exact (restrictHom_eq_one_iff hδ hstab _).2 htfix
  have hker2 : 2 ≤ Nat.card ψ.ker := by
    have hne : (⟨t, htC⟩ : C) ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
    have hnt : Nontrivial ψ.ker := ⟨⟨⟨_, hkt⟩, 1, fun h => hne (congrArg Subtype.val h)⟩⟩
    exact Finite.one_lt_card_iff_nontrivial.2 hnt
  have hCcard : Nat.card C = Nat.card ψ.ker * Nat.card X := by
    rw [← hrange, ← Subgroup.index_ker, Subgroup.card_mul_index]
  have hle : Nat.card (centralizerIn P t) ≤ Nat.card C := by
    rw [hcard, hCcard]
    exact Nat.mul_le_mul_right _ hker2
  have hCeq : C = centralizerIn P t := Subgroup.eq_of_le_of_card_ge hCle hle
  have hXpos : 0 < Nat.card X := Nat.card_pos
  have hker : Nat.card ψ.ker = 2 := by
    have h1 : Nat.card C = 2 * Nat.card X := by rw [hCeq, hcard]
    rw [hCcard] at h1
    exact Nat.eq_of_mul_eq_mul_right hXpos h1
  refine ⟨hCeq, sSup_eq_bot.2 fun K hK => ?_⟩
  obtain ⟨hKn, hKodd⟩ := hK
  set f : C →* X := (MulEquiv.subgroupCongr hrange).toMonoidHom.comp ψ.rangeRestrict
  have hfs : Function.Surjective f :=
    (MulEquiv.subgroupCongr hrange).surjective.comp ψ.rangeRestrict_surjective
  have hKmap : K.map f = ⊥ := by
    have : (K.map f).Normal := hKn.map f hfs
    exact normal_eq_bot_of_oddWitness hX hw (K.map f)
      (Odd.of_dvd_nat hKodd (Subgroup.card_map_dvd K f))
  have hKker : K ≤ ψ.ker := by
    intro k hk
    have : f k ∈ K.map f := Subgroup.mem_map_of_mem f hk
    rw [hKmap, Subgroup.mem_bot] at this
    rw [MonoidHom.mem_ker]
    have h2 := congrArg Subtype.val this
    simpa [f] using h2
  exact eq_bot_of_le_ker_two ψ hker K hKker hKodd

end General

@[expose, irreducible] def heT1P : Equiv.Perm (Fin 8330) :=
  evalSignedWord [heGenPerm 0, heGenPerm 1] heT1Word

theorem rep_heAB
    (h : ℕ) (hh : h < [heGenPerm 0, heGenPerm 1].length) :
    Rep 8330 heABArrs[h]! ([heGenPerm 0, heGenPerm 1].getD h 1) ∧
      Rep 8330 (heABArrs.map (invCand 8330))[h]! ([heGenPerm 0, heGenPerm 1].getD h 1)⁻¹ := by
  have hh' : h < 2 := hh
  rw [heABArrs]
  interval_cases h
  · rw [arr2_get0, arr2_map_get0, list2_getD0]
    exact ⟨rep_heGen (by norm_num), rep_heGen_inv (k := 0) (by norm_num)⟩
  · rw [arr2_get1, arr2_map_get1, list2_getD1]
    exact ⟨rep_heGen (by norm_num), rep_heGen_inv (k := 1) (by norm_num)⟩

theorem rep_heT1 :
    Rep 8330 heT1Arr heT1P := by
  rw [heT1Arr, heT1P]
  exact rep_wordA_evalSignedWord (fun h hh => (rep_heAB h hh).1) (fun h hh => (rep_heAB h hh).2)
    heInner_big.1

theorem rep_heT1_inv :
    Rep 8330 (invCand 8330 heT1Arr) heT1P⁻¹ := by
  have h := permChk_spec heInner_big.2.1
  rw [h.1.unique rep_heT1] at h
  exact h.2

theorem heT1P_mem : heT1P ∈ heP := by
  rw [heT1P]
  refine evalSignedWord_mem heP (fun g hg => ?_) _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h <;> rw [h]
  · exact heGenPerm_mem (by norm_num)
  · exact heGenPerm_mem (by norm_num)

theorem heT1P_ne_one : heT1P ≠ 1 := by
  intro h
  have h' := (eqA_iff rep_heT1 rep_idA).2 h
  rw [heInner_big.2.2.2.1] at h'
  exact absurd h' (by decide)

theorem orderOf_heT1P :
    orderOf heT1P = 2 := by
  refine orderOf_eq_prime ?_ heT1P_ne_one
  rw [sq]
  exact eq_of_eqA (rep_compA rep_heT1 rep_heT1) rep_idA heInner_big.2.2.1

theorem heA0_ne_one :
    heGenPerm 0 ≠ 1 := by
  intro h
  have h' := (eqA_iff (rep_heGen (k := 0) (by norm_num)) rep_idA).2 h
  rw [heInner_big.2.2.2.2.2.1] at h'
  exact absurd h' (by decide)

theorem orderOf_heA0 :
    orderOf (heGenPerm 0) = 2 := by
  refine orderOf_eq_prime ?_ heA0_ne_one
  rw [sq]
  exact eq_of_eqA (rep_compA (rep_heGen (by norm_num)) (rep_heGen (by norm_num))) rep_idA
    heInner_big.2.2.2.2.1

@[expose] def heInnerLettersP0 : List (Equiv.Perm (Fin 8330)) :=
  [heGenPerm 0, heGenPerm 1, heGenPerm 0]

@[expose] def heInnerLettersP1 : List (Equiv.Perm (Fin 8330)) := [heGenPerm 0, heGenPerm 1, heT1P]

theorem rep_heInnerLetter0
    (h : ℕ) (hh : h < heInnerLettersP0.length) :
    Rep 8330 heInnerLetters0[h]! (heInnerLettersP0.getD h 1) ∧
      Rep 8330 (heInnerLetters0.map (invCand 8330))[h]! (heInnerLettersP0.getD h 1)⁻¹ := by
  have hh' : h < 3 := hh
  rw [heInnerLetters0, heInnerLettersP0]
  interval_cases h
  · rw [arr3_get0, arr3_map_get0, list3_getD0]
    exact ⟨rep_heGen (by norm_num), rep_heGen_inv (k := 0) (by norm_num)⟩
  · rw [arr3_get1, arr3_map_get1, list3_getD1]
    exact ⟨rep_heGen (by norm_num), rep_heGen_inv (k := 1) (by norm_num)⟩
  · rw [arr3_get2, arr3_map_get2, list3_getD2]
    exact ⟨rep_heGen (by norm_num), rep_heGen_inv (k := 0) (by norm_num)⟩

theorem rep_heInnerLetter1
    (h : ℕ) (hh : h < heInnerLettersP1.length) :
    Rep 8330 heInnerLetters1[h]! (heInnerLettersP1.getD h 1) ∧
      Rep 8330 (heInnerLetters1.map (invCand 8330))[h]! (heInnerLettersP1.getD h 1)⁻¹ := by
  have hh' : h < 3 := hh
  rw [heInnerLetters1, heInnerLettersP1]
  interval_cases h
  · rw [arr3_get0, arr3_map_get0, list3_getD0]
    exact ⟨rep_heGen (by norm_num), rep_heGen_inv (k := 0) (by norm_num)⟩
  · rw [arr3_get1, arr3_map_get1, list3_getD1]
    exact ⟨rep_heGen (by norm_num), rep_heGen_inv (k := 1) (by norm_num)⟩
  · rw [arr3_get2, arr3_map_get2, list3_getD2]
    exact ⟨rep_heT1, rep_heT1_inv⟩

@[expose, irreducible] def heInnerCP0 (j : ℕ) : Equiv.Perm (Fin 8330) :=
  evalSignedWord heInnerLettersP0 (heInnerWords0.getD j [])

@[expose, irreducible] def heInnerCP1 (j : ℕ) : Equiv.Perm (Fin 8330) :=
  evalSignedWord heInnerLettersP1 (heInnerWords1.getD j [])

theorem rep_heInnerC0
    {j : ℕ} (hj : j < 9) : Rep 8330 (heInnerC0 j) (heInnerCP0 j) := by
  rw [heInnerC0, heInnerCP0]
  exact rep_wordA_evalSignedWord (fun h hh => (rep_heInnerLetter0 h hh).1)
    (fun h hh => (rep_heInnerLetter0 h hh).2) (heInner_big.2.2.2.2.2.2.2.2.1 j hj).1

theorem rep_heInnerC1
    {j : ℕ} (hj : j < 9) : Rep 8330 (heInnerC1 j) (heInnerCP1 j) := by
  rw [heInnerC1, heInnerCP1]
  exact rep_wordA_evalSignedWord (fun h hh => (rep_heInnerLetter1 h hh).1)
    (fun h hh => (rep_heInnerLetter1 h hh).2) (heInner_big.2.2.2.2.2.2.2.2.2.1 j hj).1

theorem heInnerCP0_mem (j : ℕ) : heInnerCP0 j ∈ heP := by
  rw [heInnerCP0]
  refine evalSignedWord_mem heP (fun g hg => ?_) _
  simp only [heInnerLettersP0, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h <;> rw [h]
  · exact heGenPerm_mem (by norm_num)
  · exact heGenPerm_mem (by norm_num)
  · exact heGenPerm_mem (by norm_num)

theorem heInnerCP1_mem (j : ℕ) : heInnerCP1 j ∈ heP := by
  rw [heInnerCP1]
  refine evalSignedWord_mem heP (fun g hg => ?_) _
  simp only [heInnerLettersP1, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with h | h | h <;> rw [h]
  · exact heGenPerm_mem (by norm_num)
  · exact heGenPerm_mem (by norm_num)
  · exact heT1P_mem

theorem heInnerCP0_comm
    {j : ℕ} (hj : j < 9) :
    heInnerCP0 j * heGenPerm 0 = heGenPerm 0 * heInnerCP0 j :=
  eq_of_eqA (rep_compA (rep_heInnerC0 hj) (rep_heGen (by norm_num)))
    (rep_compA (rep_heGen (by norm_num)) (rep_heInnerC0 hj))
    (heInner_big.2.2.2.2.2.2.2.2.1 j hj).2.2.1

theorem heInnerCP1_comm
    {j : ℕ} (hj : j < 9) : heInnerCP1 j * heT1P = heT1P * heInnerCP1 j :=
  eq_of_eqA (rep_compA (rep_heInnerC1 hj) rep_heT1) (rep_compA rep_heT1 (rep_heInnerC1 hj))
    (heInner_big.2.2.2.2.2.2.2.2.2.1 j hj).2.2.1

theorem heInnerCP0_zero :
    heInnerCP0 0 = heGenPerm 0 :=
  eq_of_eqA (rep_heInnerC0 (by norm_num)) (rep_heGen (by norm_num))
    heInner_big.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem heInnerCP1_zero :
    heInnerCP1 0 = heT1P :=
  eq_of_eqA (rep_heInnerC1 (by norm_num)) rep_heT1 heInner_big.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

@[expose] def heInnerGrp0 : Subgroup (Equiv.Perm (Fin 8330)) :=
  Subgroup.closure {g | ∃ j < 9, heInnerCP0 j = g}

@[expose] def heInnerGrp1 : Subgroup (Equiv.Perm (Fin 8330)) :=
  Subgroup.closure {g | ∃ j < 9, heInnerCP1 j = g}

theorem heInnerGrp0_le :
    heInnerGrp0 ≤ centralizerIn heP (heGenPerm 0) := by
  rw [heInnerGrp0, Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  exact mem_centralizerIn.2 ⟨heInnerCP0_mem j, heInnerCP0_comm hj⟩

theorem heInnerGrp1_le :
    heInnerGrp1 ≤ centralizerIn heP heT1P := by
  rw [heInnerGrp1, Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  exact mem_centralizerIn.2 ⟨heInnerCP1_mem j, heInnerCP1_comm hj⟩

theorem heA0_mem_grp0 :
    heGenPerm 0 ∈ heInnerGrp0 :=
  Subgroup.subset_closure ⟨0, by norm_num, heInnerCP0_zero⟩

theorem heT1P_mem_grp1 :
    heT1P ∈ heInnerGrp1 :=
  Subgroup.subset_closure ⟨0, by norm_num, heInnerCP1_zero⟩

theorem heDelta0_lt : ∀ k < 240, heDelta0[k]! < 8330 := by
  have h := heInner_big.2.2.2.2.2.2.2.2.2.2.1
  simp only [incListOK, Bool.and_eq_true, allLt_iff, decide_eq_true_eq] at h
  exact h.1.2

theorem heDelta1_lt : ∀ k < 42, heDelta1[k]! < 8330 := by
  have h := heInner_big.2.2.2.2.2.2.2.2.2.2.2.2.1
  simp only [incListOK, Bool.and_eq_true, allLt_iff, decide_eq_true_eq] at h
  exact h.1.2

theorem heDelta0_injective :
    Function.Injective (listPt 8330 heDelta0 (m := 240)) := by
  have h := heInner_big.2.2.2.2.2.2.2.2.2.2.1
  simp only [incListOK, Bool.and_eq_true, allLt_iff, decide_eq_true_eq] at h
  exact listPt_injective_of_inc h.1.2 h.2

theorem heDelta1_injective :
    Function.Injective (listPt 8330 heDelta1 (m := 42)) := by
  have h := heInner_big.2.2.2.2.2.2.2.2.2.2.2.2.1
  simp only [incListOK, Bool.and_eq_true, allLt_iff, decide_eq_true_eq] at h
  exact listPt_injective_of_inc h.1.2 h.2

@[expose] def heInnerSigmaP0 (j : ℕ) : Equiv.Perm (Fin 240) :=
  permOrId 240 (heInnerSigma0.getD j #[])

@[expose] def heInnerSigmaP1 (j : ℕ) : Equiv.Perm (Fin 42) :=
  permOrId 42 (heInnerSigma1.getD j #[])

theorem heInnerCP0_agree
    {j : ℕ} (hj : j < 9) (k : Fin 240) :
    heInnerCP0 j (listPt 8330 heDelta0 k) = listPt 8330 heDelta0 (heInnerSigmaP0 j k) :=
  agreeOK_spec_of_lt heDelta0_lt (rep_heInnerC0 hj)
    (permChk_spec (heInner_big.2.2.2.2.2.2.2.2.1 j hj).2.2.2.1).1
    (heInner_big.2.2.2.2.2.2.2.2.1 j hj).2.2.2.2 k

theorem heInnerCP1_agree
    {j : ℕ} (hj : j < 9) (k : Fin 42) :
    heInnerCP1 j (listPt 8330 heDelta1 k) = listPt 8330 heDelta1 (heInnerSigmaP1 j k) :=
  agreeOK_spec_of_lt heDelta1_lt (rep_heInnerC1 hj)
    (permChk_spec (heInner_big.2.2.2.2.2.2.2.2.2.1 j hj).2.2.2.1).1
    (heInner_big.2.2.2.2.2.2.2.2.2.1 j hj).2.2.2.2 k

theorem heInnerGrp0_stab :
    heInnerGrp0 ≤ MulAction.stabilizer (Equiv.Perm (Fin 8330))
      (Set.range (listPt 8330 heDelta0 (m := 240))) := by
  rw [heInnerGrp0, Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  exact mem_stabilizer_of_agree (heInnerCP0_agree hj)

theorem heInnerGrp1_stab :
    heInnerGrp1 ≤ MulAction.stabilizer (Equiv.Perm (Fin 8330))
      (Set.range (listPt 8330 heDelta1 (m := 42))) := by
  rw [heInnerGrp1, Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  exact mem_stabilizer_of_agree (heInnerCP1_agree hj)

theorem heA0_fix (k : Fin 240) :
    heGenPerm 0 (listPt 8330 heDelta0 k) = listPt 8330 heDelta0 k := by
  apply Fin.ext
  have h := heInner_big.2.2.2.2.2.2.2.2.2.2.2.1
  simp only [fixesOK, allLt_iff, beq_iff_eq] at h
  rw [← rep_heGen (k := 0) (by norm_num), listPt_val_of_lt heDelta0_lt]
  exact h k k.2

theorem heT1P_fix
    (k : Fin 42) : heT1P (listPt 8330 heDelta1 k) = listPt 8330 heDelta1 k := by
  apply Fin.ext
  have h := heInner_big.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  simp only [fixesOK, allLt_iff, beq_iff_eq] at h
  rw [← rep_heT1, listPt_val_of_lt heDelta1_lt]
  exact h k k.2

theorem heInnerSigma0_length : heInnerSigma0.length = 9 := rfl

theorem heX0_eq :
    heX0.originalSubgroup = Subgroup.closure {g | ∃ j < 9, heInnerSigmaP0 j = g} := by
  rw [heX0, certificate_originalSubgroup]
  congr 1
  ext g
  simp only [List.mem_map, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
    refine ⟨j, heInnerSigma0_length ▸ hj, ?_⟩
    rw [heInnerSigmaP0, List.getD_eq_getElem _ _ hj]
  · rintro ⟨j, hj, rfl⟩
    have hj' : j < heInnerSigma0.length := heInnerSigma0_length ▸ hj
    exact ⟨_, List.getElem_mem hj', by rw [heInnerSigmaP0, List.getD_eq_getElem _ _ hj']⟩

theorem heInnerSigma1_length : heInnerSigma1.length = 9 := rfl

theorem heX1_eq :
    heX1.originalSubgroup = Subgroup.closure {g | ∃ j < 9, heInnerSigmaP1 j = g} := by
  rw [heX1, certificate_originalSubgroup]
  congr 1
  ext g
  simp only [List.mem_map, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
    refine ⟨j, heInnerSigma1_length ▸ hj, ?_⟩
    rw [heInnerSigmaP1, List.getD_eq_getElem _ _ hj]
  · rintro ⟨j, hj, rfl⟩
    have hj' : j < heInnerSigma1.length := heInnerSigma1_length ▸ hj
    exact ⟨_, List.getElem_mem hj', by rw [heInnerSigmaP1, List.getD_eq_getElem _ _ hj']⟩

theorem heInnerRes0_range :
    (restrictHom heDelta0_injective heInnerGrp0 heInnerGrp0_stab).range =
      heX0.originalSubgroup := by
  rw [restrictHom_range heDelta0_injective heInnerGrp0_stab rfl, heX0_eq]
  congr 1
  ext g
  constructor
  · rintro ⟨h, ⟨j, hj, hjh⟩, rfl⟩
    exact ⟨j, hj, (restrictHom_eq_of_agree heDelta0_injective heInnerGrp0_stab h
      (by rw [← hjh]; exact heInnerCP0_agree hj)).symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨heInnerCP0 j, Subgroup.subset_closure ⟨j, hj, rfl⟩⟩, ⟨j, hj, rfl⟩,
      restrictHom_eq_of_agree heDelta0_injective heInnerGrp0_stab _ (heInnerCP0_agree hj)⟩

theorem heInnerRes1_range :
    (restrictHom heDelta1_injective heInnerGrp1 heInnerGrp1_stab).range =
      heX1.originalSubgroup := by
  rw [restrictHom_range heDelta1_injective heInnerGrp1_stab rfl, heX1_eq]
  congr 1
  ext g
  constructor
  · rintro ⟨h, ⟨j, hj, hjh⟩, rfl⟩
    exact ⟨j, hj, (restrictHom_eq_of_agree heDelta1_injective heInnerGrp1_stab h
      (by rw [← hjh]; exact heInnerCP1_agree hj)).symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨heInnerCP1 j, Subgroup.subset_closure ⟨j, hj, rfl⟩⟩, ⟨j, hj, rfl⟩,
      restrictHom_eq_of_agree heDelta1_injective heInnerGrp1_stab _ (heInnerCP1_agree hj)⟩

theorem card_heX0 : Nat.card heX0.originalSubgroup = 80640 := by
  rw [← heX0.orderCertificate_eq_card heInner_X0.1, heInner_X0.2.1]

theorem card_heX1 : Nat.card heX1.originalSubgroup = 10752 := by
  rw [← heX1.orderCertificate_eq_card heInner_X1.1, heInner_X1.2.1]

theorem oddWitness_heX0 : OddWitness heX0.originalSubgroup 315 :=
  oddWitness_of_oddWitnessOK (by norm_num) heX0 heInner_X0.1 heInner_X0.2.2

theorem oddWitness_heX1 : OddWitness heX1.originalSubgroup 21 :=
  oddWitness_of_oddWitnessOK (by norm_num) heX1 heInner_X1.1 heInner_X1.2.2

theorem heInner0_oddCore
    (hcard : Nat.card (centralizerIn heP (heGenPerm 0)) = 161280) :
    CFSG.oddCore (centralizerIn heP (heGenPerm 0)) = ⊥ := by
  obtain ⟨hC, hcore⟩ := oddCore_eq_bot_of_restrict heInnerGrp0_le heA0_mem_grp0 heA0_ne_one
    heDelta0_injective heInnerGrp0_stab heA0_fix heInnerRes0_range (v := 8)
    (by rw [card_heX0]; norm_num) oddWitness_heX0 (by rw [hcard, card_heX0])
  rw [← hC]
  exact hcore

theorem heInner1_oddCore
    (hcard : Nat.card (centralizerIn heP heT1P) = 21504) :
    CFSG.oddCore (centralizerIn heP heT1P) = ⊥ := by
  obtain ⟨hC, hcore⟩ := oddCore_eq_bot_of_restrict heInnerGrp1_le heT1P_mem_grp1 heT1P_ne_one
    heDelta1_injective heInnerGrp1_stab heT1P_fix heInnerRes1_range (v := 9)
    (by rw [card_heX1]; norm_num) oddWitness_heX1 (by rw [hcard, card_heX1])
  rw [← hC]
  exact hcore

end CFSG.Sporadic.HeldB
