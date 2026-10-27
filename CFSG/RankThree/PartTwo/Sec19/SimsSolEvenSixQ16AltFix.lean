module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenLen4

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.CGT.PushingUpLit.SolK CFSG.CGT.PushingUpLit.BHS Equiv Equiv.Perm

namespace Q16Alt

@[expose] def b1 : Perm (Fin 6) := swap 0 1 * swap 2 3

@[expose] def b2 : Perm (Fin 6) := swap 0 2 * swap 1 3

@[expose] def g3 : Perm (Fin 6) := swap 0 1 * swap 4 5

@[expose] def c3 : Perm (Fin 6) := swap 1 2 * swap 2 3

@[expose] def dZero : Subgroup (Perm (Fin 6)) := Subgroup.closure {b1, b2, g3}

@[expose] noncomputable def zBar : permBar 6 := barInd ({4, 5} : Finset (Fin 6))

@[expose] noncomputable def zPerp : Set (permBar 6) :=
  {v | ∃ I : Finset (Fin 6), I ⊆ {0, 1, 2, 3} ∧ Even I.card ∧ v = barInd I}

theorem compl_45 : ({4, 5} : Finset (Fin 6))ᶜ = {0, 1, 2, 3} := by
  decide

private theorem card_compl_45 : (({4, 5} : Finset (Fin 6))ᶜ).card = 4 := by
  decide

private theorem sign_b1 : sign b1 = 1 := by
  decide

private theorem sign_b2 : sign b2 = 1 := by
  decide

private theorem sign_g3 : sign g3 = 1 := by
  decide

private theorem sign_c3 : sign c3 = 1 := by
  decide

private theorem invol_cases : ∀ σ : Perm (Fin 6), σ 4 = 4 → σ 5 = 5 → σ * σ = 1 →
    σ ∈ ({1, swap 0 1, swap 0 2, swap 0 3, swap 1 2, swap 1 3, swap 2 3, b1, b2, b1 * b2} :
      Finset (Perm (Fin 6))) := by
  decide +kernel

theorem mem_klein4_45_iff {σ : Perm (Fin 6)} :
    σ ∈ klein4 ({4, 5} : Finset (Fin 6))ᶜ ↔ σ = 1 ∨ σ = b1 ∨ σ = b2 ∨ σ = b1 * b2 := by
  rw [mem_klein4_iff card_compl_45, mem_altOn]
  constructor
  · rintro ⟨⟨hfix, hsign⟩, hsq⟩
    have hmem := invol_cases σ (hfix 4 (by decide)) (hfix 5 (by decide)) hsq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    have hodd : ∀ {x y : Fin 6}, x ≠ y → σ = swap x y → False := fun hxy h => by
      rw [h, sign_swap hxy] at hsign
      exact absurd hsign (by decide)
    rcases hmem with h | h | h | h | h | h | h | h | h | h
    · exact Or.inl h
    · exact (hodd (by decide) h).elim
    · exact (hodd (by decide) h).elim
    · exact (hodd (by decide) h).elim
    · exact (hodd (by decide) h).elim
    · exact (hodd (by decide) h).elim
    · exact (hodd (by decide) h).elim
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨⟨fun x _ => rfl, sign_one⟩, mul_one 1⟩
    · exact ⟨⟨by decide, sign_b1⟩, by decide⟩
    · exact ⟨⟨by decide, sign_b2⟩, by decide⟩
    · exact ⟨⟨by decide, by rw [map_mul, sign_b1, sign_b2]; rfl⟩, by decide⟩

theorem b1_mul_b2 : b1 * b2 = b2 * b1 := by
  decide

theorem c3_mem_altOn : c3 ∈ altOn ({4, 5} : Finset (Fin 6))ᶜ :=
  mem_altOn.2 ⟨by decide, sign_c3⟩

theorem c3_conj_b1 : c3 * b1 * c3⁻¹ = b2 := by
  decide

theorem c3_conj_b2 : c3 * b2 * c3⁻¹ = b1 * b2 := by
  decide

theorem b1_mem_dZero : b1 ∈ dZero :=
  Subgroup.subset_closure (by simp)

theorem b2_mem_dZero : b2 ∈ dZero :=
  Subgroup.subset_closure (by simp)

theorem g3_mem_dZero : g3 ∈ dZero :=
  Subgroup.subset_closure (by simp)

private def dZeroSet : Finset (Perm (Fin 6)) :=
  {1, b1, b2, b1 * b2, g3, g3 * b1, g3 * b2, g3 * b1 * b2}

private def dZeroSub : Subgroup (Perm (Fin 6)) where
  carrier := ↑dZeroSet
  mul_mem' := fun {a b} ha hb => by
    have key : ∀ a ∈ dZeroSet, ∀ b ∈ dZeroSet, a * b ∈ dZeroSet := by decide +kernel
    exact key a ha b hb
  one_mem' := by
    show (1 : Perm (Fin 6)) ∈ dZeroSet
    decide
  inv_mem' := fun {a} ha => by
    have key : ∀ a ∈ dZeroSet, a⁻¹ ∈ dZeroSet := by decide +kernel
    exact key a ha

private theorem dZero_eq_dZeroSub : dZero = dZeroSub := by
  refine le_antisymm ((Subgroup.closure_le _).2 fun x hx => ?_) fun x hx => ?_
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · show b1 ∈ dZeroSet
      decide
    · show b2 ∈ dZeroSet
      decide
    · show g3 ∈ dZeroSet
      decide
  · have hx' : x ∈ dZeroSet := hx
    simp only [dZeroSet, Finset.mem_insert, Finset.mem_singleton] at hx'
    rcases hx' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact dZero.one_mem
    · exact b1_mem_dZero
    · exact b2_mem_dZero
    · exact dZero.mul_mem b1_mem_dZero b2_mem_dZero
    · exact g3_mem_dZero
    · exact dZero.mul_mem g3_mem_dZero b1_mem_dZero
    · exact dZero.mul_mem g3_mem_dZero b2_mem_dZero
    · exact dZero.mul_mem (dZero.mul_mem g3_mem_dZero b1_mem_dZero) b2_mem_dZero

theorem card_dZero : Nat.card dZero = 8 := by
  rw [dZero_eq_dZeroSub]
  show Nat.card ↥(↑dZeroSet : Set (Perm (Fin 6))) = 8
  rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
  decide

theorem dZero_le_alternatingGroup : dZero ≤ alternatingGroup (Fin 6) := by
  refine (Subgroup.closure_le _).2 fun x hx => ?_
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact mem_alternatingGroup.2 sign_b1
  · exact mem_alternatingGroup.2 sign_b2
  · exact mem_alternatingGroup.2 sign_g3

theorem klein4_le_dZero : klein4 ({4, 5} : Finset (Fin 6))ᶜ ≤ dZero := by
  intro σ hσ
  rcases mem_klein4_45_iff.1 hσ with rfl | rfl | rfl | rfl
  · exact dZero.one_mem
  · exact b1_mem_dZero
  · exact b2_mem_dZero
  · exact dZero.mul_mem b1_mem_dZero b2_mem_dZero

private theorem barInd_add_barInd_aux {n : ℕ} (A B : Finset (Fin n)) :
    barInd A + barInd B = barInd (symmDiff A B) := by
  unfold barInd
  rw [← QuotientAddGroup.mk_add]
  congr 1
  funext i
  simp only [Pi.add_apply, indVec, Finset.mem_symmDiff]
  by_cases hA : i ∈ A <;> by_cases hB : i ∈ B <;> simp [hA, hB]
  rfl

private theorem barInd_sub_barInd_aux {n : ℕ} (A B : Finset (Fin n)) :
    barInd A - barInd B = barInd (symmDiff A B) := by
  have h : barInd B + barInd B = 0 := by
    rw [barInd_add_barInd_aux, symmDiff_self, Finset.bot_eq_empty, barInd_empty]
  rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_right h, barInd_add_barInd_aux]

private theorem barInd_eq_zero_iff_aux {I : Finset (Fin 6)} :
    barInd I = 0 ↔ I = ∅ ∨ I = Finset.univ := by
  rw [← barInd_empty (n := 6), barInd_eq_barInd_iff, Finset.compl_empty]

private theorem barInd_eq_zBar_iff_aux {I : Finset (Fin 6)} :
    barInd I = zBar ↔ I = {4, 5} ∨ I = {0, 1, 2, 3} := by
  rw [zBar, barInd_eq_barInd_iff, compl_45]

private theorem exists_barInd_of_mem_range_aux {v : permBar 6}
    (hv : v ∈ Set.range (heartToBar (n := 6))) :
    ∃ I : Finset (Fin 6), Even I.card ∧ v = barInd I := by
  obtain ⟨a, rfl⟩ := hv
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective a
  rw [heartToBar_mk]
  have hsum : ∑ i, (x : Fin 6 → ZMod 2) i = 0 := by
    simpa [evenWeight, AddMonoidHom.mem_ker] using x.2
  obtain ⟨I, hIc, hI⟩ := exists_supp_of_len ((x : Fin 6 → ZMod 2) : permBar 6)
  refine ⟨I, ?_, hI⟩
  obtain ⟨k, hk⟩ := even_vecWt_of_sum_eq_zero hsum
  have hle := vecWt_le (x : Fin 6 → ZMod 2)
  rw [barLen_mk] at hIc
  rw [Nat.even_iff]
  omega

private theorem barInd_mem_range_aux {I : Finset (Fin 6)} (hI : Even I.card) :
    barInd I ∈ Set.range (heartToBar (n := 6)) := by
  have key : ∀ I : Finset (Fin 6), Even I.card → ∑ i, indVec I i = 0 := by decide +kernel
  have hx : indVec I ∈ evenWeight 6 := by
    simpa [evenWeight, AddMonoidHom.mem_ker] using key I hI
  exact ⟨((⟨indVec I, hx⟩ : evenWeight 6) : altHeart 6), rfl⟩

theorem fix_dZero {v : permBar 6} (hv : v ∈ Set.range (heartToBar (n := 6)))
    (h1 : barAct b1 v = v) (h2 : barAct b2 v = v) (h3 : barAct g3 v = v) : v = 0 ∨ v = zBar := by
  obtain ⟨I, hIe, rfl⟩ := exists_barInd_of_mem_range_aux hv
  rw [barAct_barInd, barInd_eq_barInd_iff] at h1 h2 h3
  have key : ∀ I : Finset (Fin 6), Even I.card →
      (I.image b1 = I ∨ I.image b1 = Iᶜ) → (I.image b2 = I ∨ I.image b2 = Iᶜ) →
      (I.image g3 = I ∨ I.image g3 = Iᶜ) →
      (I = ∅ ∨ I = Finset.univ) ∨ (I = {4, 5} ∨ I = {0, 1, 2, 3}) := by
    decide +kernel
  rcases key I hIe h1 h2 h3 with h | h
  · exact Or.inl (barInd_eq_zero_iff_aux.2 h)
  · exact Or.inr (barInd_eq_zBar_iff_aux.2 h)

theorem zBar_ne_zero : zBar ≠ 0 := by
  intro h
  have h' : ({4, 5} : Finset (Fin 6)) = ∅ ∨ ({4, 5} : Finset (Fin 6)) = Finset.univ :=
    barInd_eq_zero_iff_aux.1 h
  exact absurd h' (by decide)

theorem zBar_mem_zPerp : zBar ∈ zPerp :=
  ⟨{0, 1, 2, 3}, by decide, by decide, (barInd_eq_zBar_iff_aux.2 (Or.inr rfl)).symm⟩

theorem zPerp_subset_range : zPerp ⊆ Set.range (heartToBar (n := 6)) := by
  rintro _ ⟨I, -, hI, rfl⟩
  exact barInd_mem_range_aux hI

theorem ncard_zPerp : zPerp.ncard = 8 := by
  have hinj : Set.InjOn barInd (↑(Finset.univ.filter fun I : Finset (Fin 6) =>
      I ⊆ {0, 1, 2, 3} ∧ Even I.card) : Set (Finset (Fin 6))) := by
    intro I hI J hJ h
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hI hJ
    rcases barInd_eq_barInd_iff.1 h with h1 | h1
    · exact h1
    · exfalso
      have h4J : (4 : Fin 6) ∉ J := fun h4 => by simpa using hJ.1 h4
      have h4I : (4 : Fin 6) ∈ I := by
        rw [h1]
        simpa using h4J
      simpa using hI.1 h4I
  have hzP : zPerp = barInd '' (↑(Finset.univ.filter fun I : Finset (Fin 6) =>
      I ⊆ {0, 1, 2, 3} ∧ Even I.card) : Set (Finset (Fin 6))) := by
    ext v
    simp only [zPerp, Set.mem_setOf_eq, Set.mem_image, Finset.coe_filter, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨I, h1, h2, rfl⟩
      exact ⟨I, ⟨h1, h2⟩, rfl⟩
    · rintro ⟨I, ⟨h1, h2⟩, rfl⟩
      exact ⟨I, h1, h2, rfl⟩
  rw [hzP, hinj.ncard_image, Set.ncard_coe_finset]
  decide

theorem exists_eq_sub_of_mem_zPerp {w : permBar 6} (hw : w ∈ zPerp) :
    ∃ σ ∈ klein4 ({4, 5} : Finset (Fin 6))ᶜ, ∃ u ∈ Set.range (heartToBar (n := 6)),
      w = barAct σ u - u := by
  obtain ⟨I, hIs, hIe, rfl⟩ := hw
  have key : ∀ I : Finset (Fin 6), I ⊆ {0, 1, 2, 3} → Even I.card →
      ∃ σ ∈ ({1, b1, b2, b1 * b2} : Finset (Perm (Fin 6))), ∃ J : Finset (Fin 6), Even J.card ∧
        (symmDiff (J.image σ) J = I ∨ symmDiff (J.image σ) J = Iᶜ) := by
    decide +kernel
  obtain ⟨σ, hσ, J, hJe, hJ⟩ := key I hIs hIe
  refine ⟨σ, ?_, barInd J, barInd_mem_range_aux hJe, ?_⟩
  · rw [mem_klein4_45_iff]
    simpa using hσ
  · rw [barAct_barInd, barInd_sub_barInd_aux]
    exact (barInd_eq_barInd_iff.2 hJ).symm

theorem barAct_sub_mem_zPerp {σ : Perm (Fin 6)} (hσ : σ ∈ klein4 ({4, 5} : Finset (Fin 6))ᶜ)
    {w : permBar 6} (hw : w ∈ zPerp) : barAct σ w - w = 0 ∨ barAct σ w - w = zBar := by
  rw [mem_klein4_45_iff] at hσ
  obtain ⟨I, hIs, hIe, rfl⟩ := hw
  have key : ∀ σ ∈ ({1, b1, b2, b1 * b2} : Finset (Perm (Fin 6))), ∀ I : Finset (Fin 6),
      I ⊆ {0, 1, 2, 3} → Even I.card →
      (symmDiff (I.image σ) I = ∅ ∨ symmDiff (I.image σ) I = Finset.univ) ∨
        (symmDiff (I.image σ) I = {4, 5} ∨ symmDiff (I.image σ) I = {0, 1, 2, 3}) := by
    decide +kernel
  rw [barAct_barInd, barInd_sub_barInd_aux]
  rcases key σ (by simpa using hσ) I hIs hIe with h | h
  · exact Or.inl (barInd_eq_zero_iff_aux.2 h)
  · exact Or.inr (barInd_eq_zBar_iff_aux.2 h)

theorem eq_of_fix_b1_b2 {w : permBar 6} (hw : w ∈ zPerp) (h1 : barAct b1 w = w)
    (h2 : barAct b2 w = w) : w = 0 ∨ w = zBar := by
  obtain ⟨I, hIs, hIe, rfl⟩ := hw
  rw [barAct_barInd, barInd_eq_barInd_iff] at h1 h2
  have key : ∀ I : Finset (Fin 6), (I ⊆ {0, 1, 2, 3} ∧ Even I.card) →
      (I.image b1 = I ∨ I.image b1 = Iᶜ) → (I.image b2 = I ∨ I.image b2 = Iᶜ) →
      (I = ∅ ∨ I = Finset.univ) ∨ (I = {4, 5} ∨ I = {0, 1, 2, 3}) := by
    decide +kernel
  rcases key I ⟨hIs, hIe⟩ h1 h2 with h | h
  · exact Or.inl (barInd_eq_zero_iff_aux.2 h)
  · exact Or.inr (barInd_eq_zBar_iff_aux.2 h)

theorem exists_not_fix_zPerp {σ : Perm (Fin 6)} (hσ : σ ∈ klein4 ({4, 5} : Finset (Fin 6))ᶜ)
    (h1 : σ ≠ 1) : ∃ w ∈ zPerp, barAct σ w ≠ w := by
  have key : ∀ σ ∈ ({b1, b2, b1 * b2} : Finset (Perm (Fin 6))), ∃ I : Finset (Fin 6),
      I ⊆ {0, 1, 2, 3} ∧ Even I.card ∧ I.image σ ≠ I ∧ I.image σ ≠ Iᶜ := by
    decide +kernel
  have hσ' : σ ∈ ({b1, b2, b1 * b2} : Finset (Perm (Fin 6))) := by
    rcases mem_klein4_45_iff.1 hσ with h | h | h | h
    · exact absurd h h1
    · simp [h]
    · simp [h]
    · simp [h]
  obtain ⟨I, hIs, hIe, hne1, hne2⟩ := key σ hσ'
  refine ⟨barInd I, ⟨I, hIs, hIe, rfl⟩, ?_⟩
  rw [barAct_barInd, Ne, barInd_eq_barInd_iff]
  exact not_or.2 ⟨hne1, hne2⟩

theorem eq_of_c3_sub {w : permBar 6} (hw : w ∈ zPerp)
    (h : barAct c3 w - w = 0 ∨ barAct c3 w - w = zBar) : w = 0 ∨ w = zBar := by
  obtain ⟨I, hIs, hIe, rfl⟩ := hw
  rw [barAct_barInd, barInd_sub_barInd_aux, barInd_eq_zero_iff_aux, barInd_eq_zBar_iff_aux] at h
  have key : ∀ I : Finset (Fin 6), I ⊆ {0, 1, 2, 3} → Even I.card →
      ((symmDiff (I.image c3) I = ∅ ∨ symmDiff (I.image c3) I = Finset.univ) ∨
        (symmDiff (I.image c3) I = {4, 5} ∨ symmDiff (I.image c3) I = {0, 1, 2, 3})) →
      (I = ∅ ∨ I = Finset.univ) ∨ (I = {4, 5} ∨ I = {0, 1, 2, 3}) := by
    decide +kernel
  rcases key I hIs hIe h with h' | h'
  · exact Or.inl (barInd_eq_zero_iff_aux.2 h')
  · exact Or.inr (barInd_eq_zBar_iff_aux.2 h')

end Q16Alt

end CFSG.RankThree.PartTwo.Sec19.SolEven
