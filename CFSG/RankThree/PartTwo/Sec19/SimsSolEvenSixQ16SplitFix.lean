module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixQ16AltFix
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixQ16Mod

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.CGT.PushingUpLit.SolK CFSG.CGT.PushingUpLit.BHS Equiv Equiv.Perm

namespace Q16Split

@[expose] def t45 : Perm (Fin 6) := swap 4 5

@[expose] def d16 : Subgroup (Perm (Fin 6)) :=
  Subgroup.closure {swap 0 1, swap 0 2 * swap 1 3, swap 4 5}

@[expose] def b8 : Subgroup (Perm (Fin 6)) := Subgroup.closure {swap 0 1, swap 2 3, swap 4 5}

@[expose] noncomputable def y4 : Set (permBar 6) :=
  {0, barInd ({0, 1} : Finset (Fin 6)), barInd ({2, 3} : Finset (Fin 6)), Q16Alt.zBar}

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
    barInd I = Q16Alt.zBar ↔ I = {4, 5} ∨ I = {0, 1, 2, 3} := by
  rw [Q16Alt.zBar, barInd_eq_barInd_iff, Q16Alt.compl_45]

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

private theorem card_fixU_le_of_cover (σ : Perm (Fin 6)) (S : Finset (Finset (Fin 6)))
    (h : ∀ I : Finset (Fin 6), Even I.card → (I.image σ = I ∨ I.image σ = Iᶜ) →
      ∃ J ∈ S, I = J ∨ I = Jᶜ) : Nat.card ↥(Q16Mod.fixU σ) ≤ S.card := by
  have hsub : Q16Mod.fixU σ ⊆ Set.range (fun J : S => barInd (J : Finset (Fin 6))) := by
    intro v hv
    obtain ⟨hvU, hv⟩ := Q16Mod.mem_fixU.1 hv
    obtain ⟨I, hIe, rfl⟩ := exists_barInd_of_mem_range_aux hvU
    rw [barAct_barInd, barInd_eq_barInd_iff] at hv
    obtain ⟨J, hJ, hIJ⟩ := h I hIe hv
    exact ⟨⟨J, hJ⟩, (barInd_eq_barInd_iff.2 hIJ).symm⟩
  calc Nat.card ↥(Q16Mod.fixU σ)
      ≤ Nat.card ↥(Set.range (fun J : S => barInd (J : Finset (Fin 6)))) :=
        Nat.card_mono (Set.finite_range _) hsub
    _ ≤ Nat.card S := Nat.card_le_card_of_surjective _ Set.rangeFactorization_surjective
    _ = S.card := by simp

private def d16Set : Finset (Perm (Fin 6)) :=
  {1, swap 0 1, swap 0 2 * swap 1 3, swap 0 1 * (swap 0 2 * swap 1 3),
    (swap 0 2 * swap 1 3) * swap 0 1, swap 0 1 * (swap 0 2 * swap 1 3) * swap 0 1,
    (swap 0 2 * swap 1 3) * swap 0 1 * (swap 0 2 * swap 1 3),
    swap 0 1 * (swap 0 2 * swap 1 3) * swap 0 1 * (swap 0 2 * swap 1 3),
    swap 4 5, swap 0 1 * swap 4 5, (swap 0 2 * swap 1 3) * swap 4 5,
    swap 0 1 * (swap 0 2 * swap 1 3) * swap 4 5, (swap 0 2 * swap 1 3) * swap 0 1 * swap 4 5,
    swap 0 1 * (swap 0 2 * swap 1 3) * swap 0 1 * swap 4 5,
    (swap 0 2 * swap 1 3) * swap 0 1 * (swap 0 2 * swap 1 3) * swap 4 5,
    swap 0 1 * (swap 0 2 * swap 1 3) * swap 0 1 * (swap 0 2 * swap 1 3) * swap 4 5}

private def b8Set : Finset (Perm (Fin 6)) :=
  {1, swap 0 1, swap 2 3, swap 4 5, swap 0 1 * swap 2 3, swap 0 1 * swap 4 5, swap 2 3 * swap 4 5,
    swap 0 1 * swap 2 3 * swap 4 5}

private def d16Sub : Subgroup (Perm (Fin 6)) where
  carrier := ↑d16Set
  mul_mem' := fun {a b} ha hb => by
    have key : ∀ a ∈ d16Set, ∀ b ∈ d16Set, a * b ∈ d16Set := by decide +kernel
    exact key a ha b hb
  one_mem' := by
    show (1 : Perm (Fin 6)) ∈ d16Set
    decide
  inv_mem' := fun {a} ha => by
    have key : ∀ a ∈ d16Set, a⁻¹ ∈ d16Set := by decide +kernel
    exact key a ha

private def b8Sub : Subgroup (Perm (Fin 6)) where
  carrier := ↑b8Set
  mul_mem' := fun {a b} ha hb => by
    have key : ∀ a ∈ b8Set, ∀ b ∈ b8Set, a * b ∈ b8Set := by decide +kernel
    exact key a ha b hb
  one_mem' := by
    show (1 : Perm (Fin 6)) ∈ b8Set
    decide
  inv_mem' := fun {a} ha => by
    have key : ∀ a ∈ b8Set, a⁻¹ ∈ b8Set := by decide +kernel
    exact key a ha

private theorem s01_mem_d16 : swap 0 1 ∈ d16 :=
  Subgroup.subset_closure (by simp)

private theorem r_mem_d16 : swap 0 2 * swap 1 3 ∈ d16 :=
  Subgroup.subset_closure (by simp)

private theorem t_mem_d16 : swap 4 5 ∈ d16 :=
  Subgroup.subset_closure (by simp)

private theorem d16_eq_d16Sub : d16 = d16Sub := by
  refine le_antisymm ((Subgroup.closure_le _).2 fun x hx => ?_) fun x hx => ?_
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · show swap 0 1 ∈ d16Set
      decide
    · show swap 0 2 * swap 1 3 ∈ d16Set
      decide
    · show swap 4 5 ∈ d16Set
      decide
  · have hx' : x ∈ d16Set := hx
    simp only [d16Set, Finset.mem_insert, Finset.mem_singleton] at hx'
    rcases hx' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
    · exact d16.one_mem
    · exact s01_mem_d16
    · exact r_mem_d16
    · exact d16.mul_mem s01_mem_d16 r_mem_d16
    · exact d16.mul_mem r_mem_d16 s01_mem_d16
    · exact d16.mul_mem (d16.mul_mem s01_mem_d16 r_mem_d16) s01_mem_d16
    · exact d16.mul_mem (d16.mul_mem r_mem_d16 s01_mem_d16) r_mem_d16
    · exact d16.mul_mem (d16.mul_mem (d16.mul_mem s01_mem_d16 r_mem_d16) s01_mem_d16) r_mem_d16
    · exact t_mem_d16
    · exact d16.mul_mem s01_mem_d16 t_mem_d16
    · exact d16.mul_mem r_mem_d16 t_mem_d16
    · exact d16.mul_mem (d16.mul_mem s01_mem_d16 r_mem_d16) t_mem_d16
    · exact d16.mul_mem (d16.mul_mem r_mem_d16 s01_mem_d16) t_mem_d16
    · exact d16.mul_mem (d16.mul_mem (d16.mul_mem s01_mem_d16 r_mem_d16) s01_mem_d16) t_mem_d16
    · exact d16.mul_mem (d16.mul_mem (d16.mul_mem r_mem_d16 s01_mem_d16) r_mem_d16) t_mem_d16
    · exact d16.mul_mem (d16.mul_mem (d16.mul_mem (d16.mul_mem s01_mem_d16 r_mem_d16)
        s01_mem_d16) r_mem_d16) t_mem_d16

private theorem s01_mem_b8 : swap 0 1 ∈ b8 :=
  Subgroup.subset_closure (by simp)

private theorem s23_mem_b8 : swap 2 3 ∈ b8 :=
  Subgroup.subset_closure (by simp)

private theorem s45_mem_b8 : swap 4 5 ∈ b8 :=
  Subgroup.subset_closure (by simp)

private theorem b8_eq_b8Sub : b8 = b8Sub := by
  refine le_antisymm ((Subgroup.closure_le _).2 fun x hx => ?_) fun x hx => ?_
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · show swap 0 1 ∈ b8Set
      decide
    · show swap 2 3 ∈ b8Set
      decide
    · show swap 4 5 ∈ b8Set
      decide
  · have hx' : x ∈ b8Set := hx
    simp only [b8Set, Finset.mem_insert, Finset.mem_singleton] at hx'
    rcases hx' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact b8.one_mem
    · exact s01_mem_b8
    · exact s23_mem_b8
    · exact s45_mem_b8
    · exact b8.mul_mem s01_mem_b8 s23_mem_b8
    · exact b8.mul_mem s01_mem_b8 s45_mem_b8
    · exact b8.mul_mem s23_mem_b8 s45_mem_b8
    · exact b8.mul_mem (b8.mul_mem s01_mem_b8 s23_mem_b8) s45_mem_b8

private theorem mem_d16Set {x : Perm (Fin 6)} (hx : x ∈ d16) : x ∈ d16Set := by
  rw [d16_eq_d16Sub] at hx
  exact hx

private theorem mem_d16_of_mem_d16Set {x : Perm (Fin 6)} (hx : x ∈ d16Set) : x ∈ d16 := by
  rw [d16_eq_d16Sub]
  exact hx

private theorem mem_b8Set {x : Perm (Fin 6)} (hx : x ∈ b8) : x ∈ b8Set := by
  rw [b8_eq_b8Sub] at hx
  exact hx

private theorem mem_b8_of_mem_b8Set {x : Perm (Fin 6)} (hx : x ∈ b8Set) : x ∈ b8 := by
  rw [b8_eq_b8Sub]
  exact hx

theorem card_d16 : Nat.card d16 = 16 := by
  rw [d16_eq_d16Sub]
  show Nat.card ↥(↑d16Set : Set (Perm (Fin 6))) = 16
  rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
  decide +kernel

theorem t45_mem_d16 : t45 ∈ d16 :=
  t_mem_d16

theorem b8_le_d16 : b8 ≤ d16 := by
  intro x hx
  have key : ∀ x ∈ b8Set, x ∈ d16Set := by decide +kernel
  exact mem_d16_of_mem_d16Set (key x (mem_b8Set hx))

theorem b8_comm {x y : Perm (Fin 6)} (hx : x ∈ b8) (hy : y ∈ b8) : x * y = y * x := by
  have key : ∀ x ∈ b8Set, ∀ y ∈ b8Set, x * y = y * x := by decide +kernel
  exact key x (mem_b8Set hx) y (mem_b8Set hy)

theorem t45_comm {d : Perm (Fin 6)} (hd : d ∈ d16) : d * t45 = t45 * d := by
  have key : ∀ d ∈ d16Set, d * t45 = t45 * d := by decide +kernel
  exact key d (mem_d16Set hd)

theorem barAct_zBar_of_mem_d16 {d : Perm (Fin 6)} (hd : d ∈ d16) :
    barAct d Q16Alt.zBar = Q16Alt.zBar := by
  have key : ∀ d ∈ d16Set, ({4, 5} : Finset (Fin 6)).image d = {4, 5} := by decide +kernel
  rw [Q16Alt.zBar, barAct_barInd, key d (mem_d16Set hd)]

theorem fix_d16 {v : permBar 6} (hv : v ∈ Set.range (heartToBar (n := 6)))
    (h : ∀ d ∈ d16, barAct d v = v) : v = 0 ∨ v = Q16Alt.zBar := by
  obtain ⟨I, hIe, rfl⟩ := exists_barInd_of_mem_range_aux hv
  have h1 := h (swap 0 1) s01_mem_d16
  have h2 := h (swap 0 2 * swap 1 3) r_mem_d16
  have h3 := h (swap 4 5) t_mem_d16
  rw [barAct_barInd, barInd_eq_barInd_iff] at h1 h2 h3
  have key : ∀ I : Finset (Fin 6), Even I.card →
      (I.image (swap 0 1) = I ∨ I.image (swap 0 1) = Iᶜ) →
      (I.image (swap 0 2 * swap 1 3 : Perm (Fin 6)) = I ∨
        I.image (swap 0 2 * swap 1 3 : Perm (Fin 6)) = Iᶜ) →
      (I.image (swap 4 5) = I ∨ I.image (swap 4 5) = Iᶜ) →
      (I = ∅ ∨ I = Finset.univ) ∨ (I = {4, 5} ∨ I = {0, 1, 2, 3}) := by
    decide +kernel
  rcases key I hIe h1 h2 h3 with h | h
  · exact Or.inl (barInd_eq_zero_iff_aux.2 h)
  · exact Or.inr (barInd_eq_zBar_iff_aux.2 h)

theorem eq_one_or_t45 {b : Perm (Fin 6)} (hb : b ∈ d16)
    (h : ∀ v ∈ Set.range (heartToBar (n := 6)),
      barAct b v - v = 0 ∨ barAct b v - v = Q16Alt.zBar) : b = 1 ∨ b = t45 := by
  have key : ∀ b ∈ d16Set, (∀ I : Finset (Fin 6), Even I.card →
      (symmDiff (I.image b) I = ∅ ∨ symmDiff (I.image b) I = Finset.univ) ∨
        (symmDiff (I.image b) I = {4, 5} ∨ symmDiff (I.image b) I = {0, 1, 2, 3})) →
      b = 1 ∨ b = t45 := by
    decide +kernel
  refine key b (mem_d16Set hb) fun I hI => ?_
  have hI' := h (barInd I) (barInd_mem_range_aux hI)
  rw [barAct_barInd, barInd_sub_barInd_aux] at hI'
  rcases hI' with h0 | hz
  · exact Or.inl (barInd_eq_zero_iff_aux.1 h0)
  · exact Or.inr (barInd_eq_zBar_iff_aux.1 hz)

theorem barAct_t45_sub {v : permBar 6} (hv : v ∈ Set.range (heartToBar (n := 6))) :
    barAct t45 v - v = 0 ∨ barAct t45 v - v = Q16Alt.zBar := by
  obtain ⟨I, -, rfl⟩ := exists_barInd_of_mem_range_aux hv
  have key : ∀ I : Finset (Fin 6),
      (symmDiff (I.image t45) I = ∅ ∨ symmDiff (I.image t45) I = Finset.univ) ∨
        (symmDiff (I.image t45) I = {4, 5} ∨ symmDiff (I.image t45) I = {0, 1, 2, 3}) := by
    decide +kernel
  rw [barAct_barInd, barInd_sub_barInd_aux]
  rcases key I with h | h
  · exact Or.inl (barInd_eq_zero_iff_aux.2 h)
  · exact Or.inr (barInd_eq_zBar_iff_aux.2 h)

theorem card_fixU_t45_le : Nat.card ↥(Q16Mod.fixU t45) ≤ 8 := by
  refine (card_fixU_le_of_cover t45
    (Finset.univ.filter fun J : Finset (Fin 6) => J ⊆ {0, 1, 2, 3} ∧ Even J.card) ?_).trans
    (by decide +kernel)
  decide +kernel

private theorem central_cases : ∀ b ∈ d16Set, b ≠ 1 → b ≠ t45 → (∀ d ∈ d16Set, d * b = b * d) →
    b = swap 0 1 * swap 2 3 ∨ b = swap 0 1 * swap 2 3 * swap 4 5 := by
  decide +kernel

theorem card_fixU_le_four_of_central {b : Perm (Fin 6)} (hb : b ∈ d16) (h1 : b ≠ 1)
    (h2 : b ≠ t45) (hc : ∀ d ∈ d16, d * b = b * d) : Nat.card ↥(Q16Mod.fixU b) ≤ 4 := by
  rcases central_cases b (mem_d16Set hb) h1 h2 (fun d hd => hc d (mem_d16_of_mem_d16Set hd))
    with rfl | rfl
  · exact Q16Mod.card_fixU_std_le
  · refine (card_fixU_le_of_cover _
      ({∅, {0, 1}, {2, 3}, {4, 5}} : Finset (Finset (Fin 6))) ?_).trans (by decide +kernel)
    decide +kernel

private def y4Sets : Finset (Finset (Fin 6)) := {∅, {0, 1}, {2, 3}, {4, 5}}

private theorem mem_y4_iff_aux {v : permBar 6} : v ∈ y4 ↔ ∃ J ∈ y4Sets, barInd J = v := by
  simp only [y4, y4Sets, Set.mem_insert_iff, Set.mem_singleton_iff, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨∅, Or.inl rfl, barInd_empty⟩
    · exact ⟨{0, 1}, Or.inr (Or.inl rfl), rfl⟩
    · exact ⟨{2, 3}, Or.inr (Or.inr (Or.inl rfl)), rfl⟩
    · exact ⟨{4, 5}, Or.inr (Or.inr (Or.inr rfl)), rfl⟩
  · rintro ⟨J, hJ, rfl⟩
    rcases hJ with rfl | rfl | rfl | rfl
    · exact Or.inl barInd_empty
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))

theorem y4_subset_range : y4 ⊆ Set.range (heartToBar (n := 6)) := by
  intro v hv
  obtain ⟨J, hJ, rfl⟩ := mem_y4_iff_aux.1 hv
  have key : ∀ J ∈ y4Sets, Even J.card := by decide +kernel
  exact barInd_mem_range_aux (key J hJ)

theorem ncard_y4 : y4.ncard = 4 := by
  have hy : y4 = barInd '' (↑y4Sets : Set (Finset (Fin 6))) := by
    ext v
    rw [mem_y4_iff_aux]
    simp
  have hinj : Set.InjOn barInd (↑y4Sets : Set (Finset (Fin 6))) := by
    intro I hI J hJ h
    rcases barInd_eq_barInd_iff.1 h with h1 | h1
    · exact h1
    · have key : ∀ I ∈ y4Sets, ∀ J ∈ y4Sets, I = Jᶜ → I = J := by decide +kernel
      exact key I hI J hJ h1
  rw [hy, hinj.ncard_image, Set.ncard_coe_finset]
  decide +kernel

theorem mem_y4_iff {v : permBar 6} (hv : v ∈ Set.range (heartToBar (n := 6))) :
    v ∈ y4 ↔ ∀ d ∈ d16, barAct d v - v = 0 ∨ barAct d v - v = Q16Alt.zBar := by
  obtain ⟨I, hIe, rfl⟩ := exists_barInd_of_mem_range_aux hv
  constructor
  · intro hy d hd
    obtain ⟨J, hJ, hJI⟩ := mem_y4_iff_aux.1 hy
    rw [← hJI, barAct_barInd, barInd_sub_barInd_aux]
    have key : ∀ d ∈ d16Set, ∀ J ∈ y4Sets,
        (symmDiff (J.image d) J = ∅ ∨ symmDiff (J.image d) J = Finset.univ) ∨
          (symmDiff (J.image d) J = {4, 5} ∨ symmDiff (J.image d) J = {0, 1, 2, 3}) := by
      decide +kernel
    rcases key d (mem_d16Set hd) J hJ with h | h
    · exact Or.inl (barInd_eq_zero_iff_aux.2 h)
    · exact Or.inr (barInd_eq_zBar_iff_aux.2 h)
  · intro h
    have key : ∀ I : Finset (Fin 6), Even I.card → (∀ d ∈ d16Set,
        (symmDiff (I.image d) I = ∅ ∨ symmDiff (I.image d) I = Finset.univ) ∨
          (symmDiff (I.image d) I = {4, 5} ∨ symmDiff (I.image d) I = {0, 1, 2, 3})) →
        ∃ J ∈ y4Sets, I = J ∨ I = Jᶜ := by
      decide +kernel
    obtain ⟨J, hJ, hIJ⟩ := key I hIe fun d hd => by
      have hd' := h d (mem_d16_of_mem_d16Set hd)
      rw [barAct_barInd, barInd_sub_barInd_aux] at hd'
      rcases hd' with h0 | hz
      · exact Or.inl (barInd_eq_zero_iff_aux.1 h0)
      · exact Or.inr (barInd_eq_zBar_iff_aux.1 hz)
    exact mem_y4_iff_aux.2 ⟨J, hJ, (barInd_eq_barInd_iff.2 hIJ).symm⟩

theorem barAct_t45_of_mem_y4 {v : permBar 6} (hv : v ∈ y4) : barAct t45 v = v := by
  obtain ⟨J, hJ, rfl⟩ := mem_y4_iff_aux.1 hv
  have key : ∀ J ∈ y4Sets, J.image t45 = J := by decide +kernel
  rw [barAct_barInd, key J hJ]

theorem mem_b8_of_fix_y4 {b : Perm (Fin 6)} (hb : b ∈ d16) (h : ∀ v ∈ y4, barAct b v = v) :
    b ∈ b8 := by
  have key : ∀ b ∈ d16Set, (∀ J ∈ y4Sets, J.image b = J ∨ J.image b = Jᶜ) → b ∈ b8Set := by
    decide +kernel
  refine mem_b8_of_mem_b8Set (key b (mem_d16Set hb) fun J hJ => ?_)
  have hJ' := h (barInd J) (mem_y4_iff_aux.2 ⟨J, hJ, rfl⟩)
  rw [barAct_barInd, barInd_eq_barInd_iff] at hJ'
  exact hJ'

theorem barAct_of_mem_b8_of_mem_y4 {b : Perm (Fin 6)} (hb : b ∈ b8) {v : permBar 6}
    (hv : v ∈ y4) : barAct b v = v := by
  obtain ⟨J, hJ, rfl⟩ := mem_y4_iff_aux.1 hv
  have key : ∀ b ∈ b8Set, ∀ J ∈ y4Sets, J.image b = J := by decide +kernel
  rw [barAct_barInd, key b (mem_b8Set hb) J hJ]

set_option synthInstance.maxSize 1024 in
private theorem centralizing_key : ∀ b₁ ∈ b8Set, ∀ b₂ ∈ b8Set, b₁ ≠ 1 → b₂ ≠ 1 → b₁ ≠ b₂ →
    ∀ I₁ : Finset (Fin 6), Even I₁.card → (I₁.image b₁ = I₁ ∨ I₁.image b₁ = I₁ᶜ) →
    ∀ I₂ : Finset (Fin 6), Even I₂.card → (I₂.image b₂ = I₂ ∨ I₂.image b₂ = I₂ᶜ) →
    (symmDiff I₁ (I₂.image b₁) = symmDiff I₂ (I₁.image b₂) ∨
      symmDiff I₁ (I₂.image b₁) = (symmDiff I₂ (I₁.image b₂))ᶜ) →
    ∃ c ∈ b8Set, c ≠ 1 ∧ c ≠ b₁ ∧ c ≠ b₂ ∧ c ≠ b₁ * b₂ ∧ ∃ K : Finset (Fin 6), Even K.card ∧
      (symmDiff K (I₁.image c) = symmDiff I₁ (K.image b₁) ∨
        symmDiff K (I₁.image c) = (symmDiff I₁ (K.image b₁))ᶜ) ∧
      (symmDiff K (I₂.image c) = symmDiff I₂ (K.image b₂) ∨
        symmDiff K (I₂.image c) = (symmDiff I₂ (K.image b₂))ᶜ) := by
  decide +kernel

theorem exists_centralizing {b₁ b₂ : Perm (Fin 6)} (hb₁ : b₁ ∈ b8) (hb₂ : b₂ ∈ b8)
    (h₁ : b₁ ≠ 1) (h₂ : b₂ ≠ 1) (h₁₂ : b₁ ≠ b₂) {v₁ v₂ : permBar 6}
    (hv₁ : v₁ ∈ Set.range (heartToBar (n := 6))) (hv₂ : v₂ ∈ Set.range (heartToBar (n := 6)))
    (e₁ : barAct b₁ v₁ = v₁) (e₂ : barAct b₂ v₂ = v₂)
    (e : v₁ + barAct b₁ v₂ = v₂ + barAct b₂ v₁) :
    ∃ c ∈ b8, c ≠ 1 ∧ c ≠ b₁ ∧ c ≠ b₂ ∧ c ≠ b₁ * b₂ ∧
      ∃ u ∈ Set.range (heartToBar (n := 6)),
        u + barAct c v₁ = v₁ + barAct b₁ u ∧ u + barAct c v₂ = v₂ + barAct b₂ u := by
  obtain ⟨I₁, hI₁e, rfl⟩ := exists_barInd_of_mem_range_aux hv₁
  obtain ⟨I₂, hI₂e, rfl⟩ := exists_barInd_of_mem_range_aux hv₂
  rw [barAct_barInd, barInd_eq_barInd_iff] at e₁ e₂
  rw [barAct_barInd, barAct_barInd, barInd_add_barInd_aux, barInd_add_barInd_aux,
    barInd_eq_barInd_iff] at e
  obtain ⟨c, hc, hc1, hc2, hc3, hc4, K, hKe, hK1, hK2⟩ :=
    centralizing_key b₁ (mem_b8Set hb₁) b₂ (mem_b8Set hb₂) h₁ h₂ h₁₂ I₁ hI₁e e₁ I₂ hI₂e e₂ e
  refine ⟨c, mem_b8_of_mem_b8Set hc, hc1, hc2, hc3, hc4, barInd K, barInd_mem_range_aux hKe,
    ?_, ?_⟩
  · rw [barAct_barInd, barAct_barInd, barInd_add_barInd_aux, barInd_add_barInd_aux,
      barInd_eq_barInd_iff]
    exact hK1
  · rw [barAct_barInd, barAct_barInd, barInd_add_barInd_aux, barInd_add_barInd_aux,
      barInd_eq_barInd_iff]
    exact hK2

end Q16Split

end CFSG.RankThree.PartTwo.Sec19.SolEven
