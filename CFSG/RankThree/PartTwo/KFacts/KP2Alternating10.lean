module

public import CFSG.RankThree.PartTwo.KFacts.KP2Alternating7

public section

namespace CFSG.RankThree.PartTwo.KFacts.KP2

open Equiv Subgroup

abbrev swTen (a b : Fin 10) : Perm (Fin 10) := swap a b

@[expose] def finSevenEquiv : Fin 7 ≃ {x : Fin 10 // x.val < 7} where
  toFun i := ⟨⟨i.val, by omega⟩, i.isLt⟩
  invFun x := ⟨x.1.val, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[expose] def embedSeven : Perm (Fin 7) →* Perm (Fin 10) := Perm.extendDomainHom finSevenEquiv

theorem embedSeven_injective : Function.Injective embedSeven :=
  Perm.extendDomainHom_injective finSevenEquiv

theorem embedSeven_apply_of_lt (σ : Perm (Fin 7)) {x : Fin 10} (hx : x.val < 7) :
    embedSeven σ x = ⟨(σ ⟨x.val, hx⟩).val, by omega⟩ := by
  change Perm.extendDomain σ finSevenEquiv x = _
  rw [Perm.extendDomain_apply_subtype σ finSevenEquiv hx]
  rfl

theorem embedSeven_apply_of_ge (σ : Perm (Fin 7)) {x : Fin 10} (hx : ¬ x.val < 7) :
    embedSeven σ x = x :=
  Perm.extendDomain_apply_not_subtype σ finSevenEquiv hx

theorem sign_embedSeven (σ : Perm (Fin 7)) : Perm.sign (embedSeven σ) = Perm.sign σ :=
  Perm.sign_extendDomain σ finSevenEquiv

@[expose] def dThree : Perm (Fin 10) := swTen 7 8 * swTen 8 9

theorem dThree_apply_of_lt {x : Fin 10} (hx : x.val < 7) : dThree x = x := by
  have h7 : x ≠ 7 := fun h => by simp [h] at hx
  have h8 : x ≠ 8 := fun h => by simp [h] at hx
  have h9 : x ≠ 9 := fun h => by simp [h] at hx
  simp [dThree, Perm.mul_apply, swap_apply_of_ne_of_ne h8 h9, swap_apply_of_ne_of_ne h7 h8]

theorem dThree_apply_ge {x : Fin 10} (hx : ¬ x.val < 7) : ¬ (dThree x).val < 7 := by
  revert x
  decide

theorem embedSeven_commute (σ : Perm (Fin 7)) : embedSeven σ * dThree = dThree * embedSeven σ := by
  ext x
  simp only [Perm.mul_apply]
  by_cases hx : x.val < 7
  · rw [dThree_apply_of_lt hx, dThree_apply_of_lt]
    rw [embedSeven_apply_of_lt σ hx]
    exact (σ ⟨x.val, hx⟩).isLt
  · rw [embedSeven_apply_of_ge σ hx, embedSeven_apply_of_ge σ (dThree_apply_ge hx)]

theorem dThree_pow_seven : ∀ y : Fin 10, ¬ y.val < 7 →
    ∃ i : Fin 3, (dThree ^ (i : ℕ)) 7 = y := by
  decide

theorem dThree_mem_alternatingGroup : dThree ∈ alternatingGroup (Fin 10) := by
  rw [Perm.mem_alternatingGroup]
  decide

theorem exists_eq_of_commute_dThree {x : Perm (Fin 10)} (hx : x * dThree = dThree * x) :
    ∃ i : Fin 3, ∃ σ : Perm (Fin 7), x = dThree ^ (i : ℕ) * embedSeven σ := by
  classical
  have hcomm : ∀ z, x (dThree z) = dThree (x z) := fun z => by
    have := congrArg (fun π : Perm (Fin 10) => π z) hx
    simpa [Perm.mul_apply] using this
  have h7 : ¬ (x 7).val < 7 := by
    intro hlt
    have h1 := hcomm 7
    rw [dThree_apply_of_lt hlt] at h1
    have : dThree 7 = 7 := x.injective h1
    revert this
    decide
  obtain ⟨i, hi⟩ := dThree_pow_seven (x 7) h7
  set y := (dThree ^ (i : ℕ))⁻¹ * x with hy
  have hycomm : ∀ z, y (dThree z) = dThree (y z) := fun z => by
    simp only [hy, Perm.mul_apply, hcomm]
    rw [← Perm.mul_apply ((dThree ^ (i : ℕ))⁻¹) dThree, ← Perm.mul_apply dThree,
      show (dThree ^ (i : ℕ))⁻¹ * dThree = dThree * (dThree ^ (i : ℕ))⁻¹ by group]
  have hy7 : y 7 = 7 := by
    rw [hy, Perm.mul_apply, ← hi, ← Perm.mul_apply, inv_mul_cancel, Perm.one_apply]
  have hy8 : y 8 = 8 := by
    have := hycomm 7
    rw [hy7] at this
    have h78 : dThree 7 = 8 := by decide
    rwa [h78] at this
  have hy9 : y 9 = 9 := by
    have := hycomm 8
    rw [hy8] at this
    have h89 : dThree 8 = 9 := by decide
    rwa [h89] at this
  have hyge : ∀ z : Fin 10, ¬ z.val < 7 → y z = z := by
    intro z hz
    have : z = 7 ∨ z = 8 ∨ z = 9 := by omega
    rcases this with rfl | rfl | rfl
    · exact hy7
    · exact hy8
    · exact hy9
  have hylt : ∀ z : Fin 10, z.val < 7 ↔ (y z).val < 7 := by
    intro z
    constructor
    · intro hz
      by_contra hyz
      have h1 := hyge (y z) hyz
      have : z = y z := y.injective h1.symm
      rw [← this] at hyz
      exact hyz hz
    · intro hyz
      by_contra hz
      exact (by rw [hyge z hz] at hyz; exact hz hyz)
  refine ⟨i, finSevenEquiv.symm.permCongr (y.subtypePerm fun z => (hylt z).symm), ?_⟩
  rw [show x = dThree ^ (i : ℕ) * y by rw [hy]; group]
  congr 1
  ext z
  by_cases hz : z.val < 7
  · rw [embedSeven_apply_of_lt _ hz]
    simp [Equiv.permCongr_apply, finSevenEquiv]
  · rw [embedSeven_apply_of_ge _ hz, hyge z hz]

theorem exists_eq_of_commute_dThree_of_mem {x : Perm (Fin 10)} (hx : x * dThree = dThree * x)
    (hA : x ∈ alternatingGroup (Fin 10)) :
    ∃ i : Fin 3, ∃ σ ∈ alternatingGroup (Fin 7), x = dThree ^ (i : ℕ) * embedSeven σ := by
  obtain ⟨i, σ, rfl⟩ := exists_eq_of_commute_dThree hx
  refine ⟨i, σ, ?_, rfl⟩
  have h := hA
  rw [Perm.mem_alternatingGroup, map_mul, map_pow,
    Perm.mem_alternatingGroup.1 dThree_mem_alternatingGroup, one_pow, one_mul,
    sign_embedSeven] at h
  exact h

@[expose] def dOne : Perm (Fin 10) := swTen 0 1 * swTen 1 2

@[expose] def dTwo : Perm (Fin 10) := swTen 3 4 * swTen 4 5

@[expose] def eTwentySevenF (i j k : Fin 3) : Perm (Fin 10) :=
  dOne ^ (i : ℕ) * dTwo ^ (j : ℕ) * dThree ^ (k : ℕ)

theorem eTwentySevenF_mul : ∀ i j k i' j' k' : Fin 3, ∃ a b c : Fin 3,
    eTwentySevenF i j k * eTwentySevenF i' j' k' = eTwentySevenF a b c := by
  decide +kernel

theorem eTwentySevenF_inv : ∀ i j k : Fin 3, ∃ a b c : Fin 3,
    (eTwentySevenF i j k)⁻¹ = eTwentySevenF a b c := by
  decide +kernel

@[expose] def eTwentySeven : Subgroup (Perm (Fin 10)) where
  carrier := {x | ∃ i j k, x = eTwentySevenF i j k}
  mul_mem' := by
    rintro _ _ ⟨i, j, k, rfl⟩ ⟨i', j', k', rfl⟩
    exact eTwentySevenF_mul i j k i' j' k'
  one_mem' := ⟨0, 0, 0, by decide +kernel⟩
  inv_mem' := by
    rintro _ ⟨i, j, k, rfl⟩
    exact eTwentySevenF_inv i j k

theorem embedSeven_eq_of (σ : Perm (Fin 7)) (τ : Perm (Fin 10))
    (h1 : ∀ x : Fin 10, ∀ hx : x.val < 7, (σ ⟨x.val, hx⟩).val = (τ x).val)
    (h2 : ∀ x : Fin 10, ¬ x.val < 7 → τ x = x) : embedSeven σ = τ := by
  ext x
  by_cases hx : x.val < 7
  · rw [embedSeven_apply_of_lt σ hx]
    exact h1 x hx
  · rw [embedSeven_apply_of_ge σ hx, h2 x hx]

theorem embedSeven_cOne_cTwo : embedSeven cOne = dOne ∧ embedSeven cTwo = dTwo := by
  refine ⟨embedSeven_eq_of _ _ ?_ ?_, embedSeven_eq_of _ _ ?_ ?_⟩ <;> decide +kernel

theorem mem_eTwentySeven_of_commute {x : Perm (Fin 10)} (h1 : x * dOne = dOne * x)
    (h2 : x * dTwo = dTwo * x) (h3 : x * dThree = dThree * x) : x ∈ eTwentySeven := by
  obtain ⟨k, σ, rfl⟩ := exists_eq_of_commute_dThree h3
  obtain ⟨hd1, hd2⟩ := embedSeven_cOne_cTwo
  have hc : ∀ c : Perm (Fin 7), embedSeven c * dThree = dThree * embedSeven c :=
    embedSeven_commute
  have hσ : ∀ c : Perm (Fin 7), (dThree ^ (k : ℕ) * embedSeven σ) * embedSeven c =
      embedSeven c * (dThree ^ (k : ℕ) * embedSeven σ) → σ * c = c * σ := by
    intro c h
    have hcomm : Commute (dThree ^ (k : ℕ)) (embedSeven c) :=
      ((show Commute (embedSeven c) dThree from hc c).pow_right (k : ℕ)).symm
    apply embedSeven_injective
    rw [map_mul, map_mul]
    rw [mul_assoc, ← mul_assoc (embedSeven c), ← hcomm.eq, mul_assoc] at h
    exact mul_left_cancel h
  have hσ1 := hσ cOne (by rw [hd1]; exact h1)
  have hσ2 := hσ cTwo (by rw [hd2]; exact h2)
  obtain ⟨a, b, hab⟩ : ∃ a b : Fin 3, σ = eNineF a b := by
    by_contra hne
    exact forall_not_of_card_filter_eq_zero card_filter_centralizer_eNine σ ⟨hσ1, hσ2, hne⟩
  refine ⟨a, b, k, ?_⟩
  rw [hab, eNineF, map_mul, map_pow, map_pow, hd1, hd2, eTwentySevenF]
  have h13 : Commute (dOne ^ (a : ℕ) * dTwo ^ (b : ℕ)) (dThree ^ (k : ℕ)) := by
    refine Commute.mul_left ?_ ?_
    · exact Commute.pow_pow (show Commute dOne dThree from hd1 ▸ hc cOne) _ _
    · exact Commute.pow_pow (show Commute dTwo dThree from hd2 ▸ hc cTwo) _ _
  exact h13.eq.symm

theorem eTwentySevenF_sign : ∀ i j k : Fin 3, Perm.sign (eTwentySevenF i j k) = 1 := by
  decide +kernel

theorem eTwentySeven_le_alternatingGroup : eTwentySeven ≤ alternatingGroup (Fin 10) := by
  rintro _ ⟨i, j, k, rfl⟩
  exact eTwentySevenF_sign i j k

theorem dOne_mem : dOne ∈ eTwentySeven := ⟨1, 0, 0, by decide +kernel⟩

theorem dTwo_mem : dTwo ∈ eTwentySeven := ⟨0, 1, 0, by decide +kernel⟩

theorem dThree_mem : dThree ∈ eTwentySeven := ⟨0, 0, 1, by decide +kernel⟩

@[expose] def wCycle : Perm (Fin 10) :=
  swTen 0 3 * swTen 3 7 * swTen 1 4 * swTen 4 8 * swTen 2 5 * swTen 5 9

@[expose] def rFourTen : Perm (Fin 10) := swTen 0 3 * swTen 1 4 * swTen 2 5 * swTen 4 5

@[expose] def normTen : Subgroup (Perm (Fin 10)) := normalizer (eTwentySeven : Set (Perm (Fin 10)))

@[expose] def normAlt : Subgroup (Perm (Fin 10)) := normTen ⊓ alternatingGroup (Fin 10)

@[expose] def axisGen : Fin 3 → Perm (Fin 10) := ![dOne, dTwo, dThree]

@[expose] def axisElt : Fin 6 → Perm (Fin 10) := ![dOne, dOne⁻¹, dTwo, dTwo⁻¹, dThree, dThree⁻¹]

@[expose] def blockPerm : Fin 6 → Perm (Fin 10) :=
  ![1, swTen 0 3 * swTen 1 4 * swTen 2 5, swTen 3 7 * swTen 4 8 * swTen 5 9,
    swTen 0 7 * swTen 1 8 * swTen 2 9, wCycle, wCycle * wCycle]

@[expose] def flipRep : Fin 8 → Perm (Fin 10) :=
  ![1, swTen 1 2, swTen 4 5, swTen 1 2 * swTen 4 5, swTen 8 9, swTen 1 2 * swTen 8 9,
    swTen 4 5 * swTen 8 9, swTen 1 2 * swTen 4 5 * swTen 8 9]

@[expose] def monoRep (π : Fin 6) (ε : Fin 8) : Perm (Fin 10) := blockPerm π * flipRep ε

@[expose] def imgTable : Fin 6 → Fin 8 → Fin 3 → Fin 6 :=
  ![![![0, 2, 4], ![1, 2, 4], ![0, 3, 4], ![1, 3, 4],
      ![0, 2, 5], ![1, 2, 5], ![0, 3, 5], ![1, 3, 5]],
    ![![2, 0, 4], ![3, 0, 4], ![2, 1, 4], ![3, 1, 4],
      ![2, 0, 5], ![3, 0, 5], ![2, 1, 5], ![3, 1, 5]],
    ![![0, 4, 2], ![1, 4, 2], ![0, 5, 2], ![1, 5, 2],
      ![0, 4, 3], ![1, 4, 3], ![0, 5, 3], ![1, 5, 3]],
    ![![4, 2, 0], ![5, 2, 0], ![4, 3, 0], ![5, 3, 0],
      ![4, 2, 1], ![5, 2, 1], ![4, 3, 1], ![5, 3, 1]],
    ![![2, 4, 0], ![3, 4, 0], ![2, 5, 0], ![3, 5, 0],
      ![2, 4, 1], ![3, 4, 1], ![2, 5, 1], ![3, 5, 1]],
    ![![4, 0, 2], ![5, 0, 2], ![4, 1, 2], ![5, 1, 2],
      ![4, 0, 3], ![5, 0, 3], ![4, 1, 3], ![5, 1, 3]]]

@[expose] def evenTable : Fin 6 → Fin 8 → Bool :=
  ![![true, false, false, true, false, true, true, false],
    ![false, true, true, false, true, false, false, true],
    ![false, true, true, false, true, false, false, true],
    ![false, true, true, false, true, false, false, true],
    ![true, false, false, true, false, true, true, false],
    ![true, false, false, true, false, true, true, false]]

theorem monoRep_conj : ∀ (π : Fin 6) (ε : Fin 8) (a : Fin 3),
    monoRep π ε * axisGen a * (monoRep π ε)⁻¹ = axisElt (imgTable π ε a) := by
  decide +kernel

theorem monoRep_inv_conj : ∀ (π : Fin 6) (ε : Fin 8) (a : Fin 3),
    ∃ b : Fin 6, (monoRep π ε)⁻¹ * axisGen a * monoRep π ε = axisElt b := by
  decide +kernel

theorem sign_monoRep : ∀ (π : Fin 6) (ε : Fin 8),
    Perm.sign (monoRep π ε) = if evenTable π ε then 1 else -1 := by
  decide +kernel

theorem imgTable_surj : ∀ a b c : Fin 6, a.val / 2 ≠ b.val / 2 → a.val / 2 ≠ c.val / 2 →
    b.val / 2 ≠ c.val / 2 →
    ∃ (π : Fin 6) (ε : Fin 8), imgTable π ε 0 = a ∧ imgTable π ε 1 = b ∧ imgTable π ε 2 = c := by
  decide +kernel

theorem axisElt_mem : ∀ a : Fin 6, ∃ i j k : Fin 3, axisElt a = eTwentySevenF i j k := by
  decide +kernel

theorem axisElt_of_support_card : ∀ i j k : Fin 3, (eTwentySevenF i j k).support.card = 3 →
    ∃ a : Fin 6, eTwentySevenF i j k = axisElt a := by
  decide +kernel

theorem axisElt_same_axis : ∀ a b : Fin 6, a.val / 2 = b.val / 2 →
    axisElt b = axisElt a ∨ axisElt b = (axisElt a)⁻¹ := by
  decide +kernel

theorem axisGen_ne : ∀ a b : Fin 3, a ≠ b → axisGen b ≠ axisGen a ∧ axisGen b ≠ (axisGen a)⁻¹ := by
  decide +kernel

theorem axisGen_support_card : ∀ a : Fin 3, (axisGen a).support.card = 3 := by
  decide +kernel

theorem axisGen_mem (a : Fin 3) : axisGen a ∈ eTwentySeven := by
  fin_cases a
  · exact dOne_mem
  · exact dTwo_mem
  · exact dThree_mem

theorem eTwentySevenF_comm : ∀ i j k i' j' k' : Fin 3,
    eTwentySevenF i j k * eTwentySevenF i' j' k' =
      eTwentySevenF i' j' k' * eTwentySevenF i j k := by
  decide +kernel

theorem centralizer_eTwentySeven :
    centralizer (eTwentySeven : Set (Perm (Fin 10))) = eTwentySeven := by
  apply le_antisymm
  · intro x hx
    rw [mem_centralizer_iff] at hx
    exact mem_eTwentySeven_of_commute (hx _ dOne_mem).symm (hx _ dTwo_mem).symm
      (hx _ dThree_mem).symm
  · rintro _ ⟨i, j, k, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨i', j', k', rfl⟩
    exact eTwentySevenF_comm i' j' k' i j k

theorem conj_mem_of_axisGen {g : Perm (Fin 10)}
    (h : ∀ a : Fin 3, g * axisGen a * g⁻¹ ∈ eTwentySeven)
    {x : Perm (Fin 10)} (hx : x ∈ eTwentySeven) : g * x * g⁻¹ ∈ eTwentySeven := by
  obtain ⟨i, j, k, rfl⟩ := hx
  have e : g * eTwentySevenF i j k * g⁻¹ = (g * dOne * g⁻¹) ^ (i : ℕ) *
      (g * dTwo * g⁻¹) ^ (j : ℕ) * (g * dThree * g⁻¹) ^ (k : ℕ) := by
    rw [eTwentySevenF, conj_pow, conj_pow, conj_pow]
    group
  rw [e]
  exact mul_mem (mul_mem (pow_mem (h 0) _) (pow_mem (h 1) _)) (pow_mem (h 2) _)

theorem mem_normTen_of_axisGen {g : Perm (Fin 10)}
    (h : ∀ a : Fin 3, g * axisGen a * g⁻¹ ∈ eTwentySeven)
    (h' : ∀ a : Fin 3, g⁻¹ * axisGen a * g ∈ eTwentySeven) : g ∈ normTen := by
  refine mem_normalizer_iff.2 fun x => ⟨fun hx => conj_mem_of_axisGen h hx, fun hx => ?_⟩
  have h'' : ∀ a : Fin 3, g⁻¹ * axisGen a * g⁻¹⁻¹ ∈ eTwentySeven := by
    simpa only [inv_inv] using h'
  have := conj_mem_of_axisGen h'' hx
  rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this

theorem monoRep_mem (π : Fin 6) (ε : Fin 8) : monoRep π ε ∈ normTen := by
  refine mem_normTen_of_axisGen (fun a => ?_) (fun a => ?_)
  · rw [monoRep_conj]
    obtain ⟨i, j, k, h⟩ := axisElt_mem (imgTable π ε a)
    exact ⟨i, j, k, h⟩
  · obtain ⟨b, hb⟩ := monoRep_inv_conj π ε a
    rw [hb]
    obtain ⟨i, j, k, h⟩ := axisElt_mem b
    exact ⟨i, j, k, h⟩

theorem exists_axisElt_of_mem_normTen {g : Perm (Fin 10)} (hg : g ∈ normTen) (a : Fin 3) :
    ∃ b : Fin 6, g * axisGen a * g⁻¹ = axisElt b := by
  obtain ⟨i, j, k, hijk⟩ := (mem_normalizer_iff.1 hg (axisGen a)).1 (axisGen_mem a)
  obtain ⟨b, hb⟩ := axisElt_of_support_card i j k (by
    rw [← hijk, Perm.card_support_conj]
    exact axisGen_support_card a)
  exact ⟨b, hijk.trans hb⟩

theorem exists_monoRep_of_mem_normTen {g : Perm (Fin 10)} (hg : g ∈ normTen) :
    ∃ (π : Fin 6) (ε : Fin 8) (i j k : Fin 3), g = monoRep π ε * eTwentySevenF i j k := by
  obtain ⟨a, ha⟩ := exists_axisElt_of_mem_normTen hg 0
  obtain ⟨b, hb⟩ := exists_axisElt_of_mem_normTen hg 1
  obtain ⟨c, hc⟩ := exists_axisElt_of_mem_normTen hg 2
  have hdist : ∀ (x y : Fin 3) (u v : Fin 6), x ≠ y → g * axisGen x * g⁻¹ = axisElt u →
      g * axisGen y * g⁻¹ = axisElt v → u.val / 2 ≠ v.val / 2 := by
    intro x y u v hxy hu hv huv
    obtain ⟨h1, h2⟩ := axisGen_ne x y hxy
    rcases axisElt_same_axis u v huv with h | h
    · apply h1
      have : g * axisGen y * g⁻¹ = g * axisGen x * g⁻¹ := by rw [hv, h, hu]
      simpa using this
    · apply h2
      have : g * axisGen y * g⁻¹ = g * (axisGen x)⁻¹ * g⁻¹ := by
        rw [hv, h, ← hu]
        group
      simpa using this
  obtain ⟨π, ε, h0, h1, h2⟩ := imgTable_surj a b c (hdist 0 1 a b (by decide) ha hb)
    (hdist 0 2 a c (by decide) ha hc) (hdist 1 2 b c (by decide) hb hc)
  have hcomm : ∀ (x : Fin 3) (u : Fin 6), imgTable π ε x = u → g * axisGen x * g⁻¹ = axisElt u →
      ((monoRep π ε)⁻¹ * g) * axisGen x = axisGen x * ((monoRep π ε)⁻¹ * g) := by
    intro x u hxu hgx
    have hm := monoRep_conj π ε x
    rw [hxu, ← hgx] at hm
    calc (monoRep π ε)⁻¹ * g * axisGen x
        = (monoRep π ε)⁻¹ * (g * axisGen x * g⁻¹) * g := by group
      _ = (monoRep π ε)⁻¹ * (monoRep π ε * axisGen x * (monoRep π ε)⁻¹) * g := by rw [hm]
      _ = axisGen x * ((monoRep π ε)⁻¹ * g) := by group
  obtain ⟨i, j, k, hijk⟩ :=
    mem_eTwentySeven_of_commute (hcomm 0 a h0 ha) (hcomm 1 b h1 hb) (hcomm 2 c h2 hc)
  exact ⟨π, ε, i, j, k, by rw [← hijk]; group⟩

@[expose] def diag : Fin 4 → Perm (Fin 10) :=
  ![eTwentySevenF 1 1 1, eTwentySevenF 1 1 2, eTwentySevenF 1 2 1, eTwentySevenF 2 1 1]

instance : (eTwentySeven.subgroupOf normAlt).Normal :=
  normal_subgroupOf_of_le_normalizer inf_le_left

instance : (eTwentySeven.subgroupOf normTen).Normal :=
  normal_subgroupOf_of_le_normalizer le_rfl

theorem monoRep_mem_normAlt {π : Fin 6} {ε : Fin 8} (h : evenTable π ε = true) :
    monoRep π ε ∈ normAlt :=
  mem_inf.2 ⟨monoRep_mem π ε, by rw [Perm.mem_alternatingGroup, sign_monoRep, h]; rfl⟩

theorem monoRep_four_zero : monoRep 4 0 = wCycle := by
  decide +kernel

theorem wCycle_mem_normAlt : wCycle ∈ normAlt :=
  monoRep_four_zero ▸ monoRep_mem_normAlt rfl

theorem wCycle_pow_conj : ∀ a b : Fin 3, ∃ n : Fin 3,
    wCycle ^ (n : ℕ) * axisGen a * (wCycle ^ (n : ℕ))⁻¹ = axisGen b := by
  decide +kernel

theorem exists_conj_axisGen (a b : Fin 3) : ∃ g ∈ normAlt, g * axisGen a * g⁻¹ = axisGen b := by
  obtain ⟨n, hn⟩ := wCycle_pow_conj a b
  exact ⟨_, pow_mem wCycle_mem_normAlt n, hn⟩

theorem coord_spec : ∀ i j k : Fin 3,
    eTwentySevenF i j k * (monoRep 0 3 * eTwentySevenF i j k * (monoRep 0 3)⁻¹) =
      dThree ^ (2 * (k : ℕ)) ∧
    eTwentySevenF i j k * (monoRep 0 5 * eTwentySevenF i j k * (monoRep 0 5)⁻¹) =
      dTwo ^ (2 * (j : ℕ)) ∧
    eTwentySevenF i j k * (monoRep 0 6 * eTwentySevenF i j k * (monoRep 0 6)⁻¹) =
      dOne ^ (2 * (i : ℕ)) := by
  decide +kernel

theorem axisGen_pow : ∀ m c : Fin 3, c ≠ 0 →
    (axisGen m ^ (2 * (c : ℕ))) ^ (2 * (c : ℕ)) = axisGen m := by
  decide +kernel

theorem eTwentySevenF_zero : eTwentySevenF 0 0 0 = 1 := by
  decide +kernel

theorem eq_bot_or_eq_eTwentySeven {U : Subgroup (Perm (Fin 10))} (hU : U ≤ eTwentySeven)
    (hN : normAlt ≤ normalizer (U : Set (Perm (Fin 10)))) : U = ⊥ ∨ U = eTwentySeven := by
  rcases U.bot_or_exists_ne_one with hbot | ⟨x, hxU, hx1⟩
  · exact Or.inl hbot
  right
  have hconj : ∀ g ∈ normAlt, ∀ y ∈ U, g * y * g⁻¹ ∈ U := fun g hg y hy =>
    (mem_normalizer_iff.1 (hN hg) y).1 hy
  obtain ⟨i, j, k, rfl⟩ := hU hxU
  obtain ⟨h3, h2, h1⟩ := coord_spec i j k
  have hc3 : dThree ^ (2 * (k : ℕ)) ∈ U :=
    h3 ▸ mul_mem hxU (hconj _ (monoRep_mem_normAlt rfl) _ hxU)
  have hc2 : dTwo ^ (2 * (j : ℕ)) ∈ U :=
    h2 ▸ mul_mem hxU (hconj _ (monoRep_mem_normAlt rfl) _ hxU)
  have hc1 : dOne ^ (2 * (i : ℕ)) ∈ U :=
    h1 ▸ mul_mem hxU (hconj _ (monoRep_mem_normAlt rfl) _ hxU)
  have hm : ∃ m : Fin 3, axisGen m ∈ U := by
    by_cases hk : k = 0
    · by_cases hj : j = 0
      · by_cases hi : i = 0
        · subst hi hj hk
          exact absurd eTwentySevenF_zero hx1
        · exact ⟨0, axisGen_pow 0 i hi ▸ pow_mem hc1 _⟩
      · exact ⟨1, axisGen_pow 1 j hj ▸ pow_mem hc2 _⟩
    · exact ⟨2, axisGen_pow 2 k hk ▸ pow_mem hc3 _⟩
  obtain ⟨m, hmU⟩ := hm
  have hall : ∀ b : Fin 3, axisGen b ∈ U := fun b => by
    obtain ⟨g, hg, hgb⟩ := exists_conj_axisGen m b
    rw [← hgb]
    exact hconj g hg _ hmU
  refine le_antisymm hU ?_
  rintro _ ⟨i', j', k', rfl⟩
  exact mul_mem (mul_mem (pow_mem (hall 0) _) (pow_mem (hall 1) _)) (pow_mem (hall 2) _)

@[expose] def sTen : Perm (Fin 10) := swTen 1 2 * swTen 8 9

theorem sTen_spec : monoRep 0 5 = sTen ∧ sTen * dThree * sTen⁻¹ = dThree⁻¹ ∧
    sTen * dOne * sTen⁻¹ = dOne⁻¹ ∧ sTen * dTwo * sTen⁻¹ = dTwo ∧
    sTen * rFourTen * sTen⁻¹ = rFourTen⁻¹ ∧ rFourTen ^ 2 = swTen 1 2 * swTen 4 5 ∧
    sTen * (swTen 1 2 * swTen 4 5) = swTen 1 2 * swTen 4 5 * sTen := by
  decide +kernel

theorem sTen_mem_normAlt : sTen ∈ normAlt :=
  sTen_spec.1 ▸ monoRep_mem_normAlt rfl

@[expose] def kOneF : Fin 4 → Perm (Fin 10) :=
  ![1, swTen 0 1 * swTen 2 6, swTen 0 2 * swTen 1 6, swTen 0 6 * swTen 1 2]

@[expose] def kTwoF : Fin 4 → Perm (Fin 10) :=
  ![1, swTen 3 4 * swTen 5 6, swTen 3 5 * swTen 4 6, swTen 3 6 * swTen 4 5]

@[expose] def kThreeF : Fin 4 → Perm (Fin 10) :=
  ![1, swTen 6 7 * swTen 8 9, swTen 6 8 * swTen 7 9, swTen 6 9 * swTen 7 8]

theorem kF_mul : (∀ m n : Fin 4, ∃ r : Fin 4, kOneF m * kOneF n = kOneF r) ∧
    (∀ m n : Fin 4, ∃ r : Fin 4, kTwoF m * kTwoF n = kTwoF r) ∧
    (∀ m n : Fin 4, ∃ r : Fin 4, kThreeF m * kThreeF n = kThreeF r) := by
  decide +kernel

theorem kF_sq : ∀ m : Fin 4,
    kOneF m * kOneF m = 1 ∧ kTwoF m * kTwoF m = 1 ∧ kThreeF m * kThreeF m = 1 := by
  decide +kernel

@[expose] def kOne : Subgroup (Perm (Fin 10)) where
  carrier := {x | ∃ m, x = kOneF m}
  mul_mem' := by
    rintro _ _ ⟨m, rfl⟩ ⟨n, rfl⟩
    exact kF_mul.1 m n
  one_mem' := ⟨0, rfl⟩
  inv_mem' := by
    rintro _ ⟨m, rfl⟩
    exact ⟨m, inv_eq_of_mul_eq_one_right (kF_sq m).1⟩

@[expose] def kTwo : Subgroup (Perm (Fin 10)) where
  carrier := {x | ∃ m, x = kTwoF m}
  mul_mem' := by
    rintro _ _ ⟨m, rfl⟩ ⟨n, rfl⟩
    exact kF_mul.2.1 m n
  one_mem' := ⟨0, rfl⟩
  inv_mem' := by
    rintro _ ⟨m, rfl⟩
    exact ⟨m, inv_eq_of_mul_eq_one_right (kF_sq m).2.1⟩

@[expose] def kThree : Subgroup (Perm (Fin 10)) where
  carrier := {x | ∃ m, x = kThreeF m}
  mul_mem' := by
    rintro _ _ ⟨m, rfl⟩ ⟨n, rfl⟩
    exact kF_mul.2.2 m n
  one_mem' := ⟨0, rfl⟩
  inv_mem' := by
    rintro _ ⟨m, rfl⟩
    exact ⟨m, inv_eq_of_mul_eq_one_right (kF_sq m).2.2⟩

theorem embedSeven_vOneF (m : Fin 4) : embedSeven (vOneF m) = kTwoF m := by
  fin_cases m <;> exact embedSeven_eq_of _ _ (by decide +kernel) (by decide +kernel)

theorem embedSeven_vTwoF (m : Fin 4) : embedSeven (vTwoF m) = kOneF m := by
  fin_cases m <;> exact embedSeven_eq_of _ _ (by decide +kernel) (by decide +kernel)

theorem le_normalizer_of_conj {G : Type*} [Group G] {A K : Subgroup G}
    (h : ∀ b ∈ A, ∀ y ∈ K, b * y * b⁻¹ ∈ K) : A ≤ normalizer (K : Set G) := by
  intro b hb
  refine mem_normalizer_iff.2 fun y => ⟨h b hb y, fun hy => ?_⟩
  have := h b⁻¹ (inv_mem hb) _ hy
  rwa [show b⁻¹ * (b * y * b⁻¹) * b⁻¹⁻¹ = y by group] at this

theorem eq_one_of_pow_three {G : Type*} [Group G] [Finite G] {Q : Subgroup G}
    (h3 : ¬ 3 ∣ Nat.card Q) {y : G} (hy : y ∈ Q) (h : y ^ 3 = 1) : y = 1 := by
  have h1 : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one h
  rcases (Nat.dvd_prime Nat.prime_three).1 h1 with h1 | h1
  · exact orderOf_eq_one_iff.1 h1
  · exact absurd (h1 ▸ Subgroup.orderOf_dvd_natCard Q hy) h3

theorem dThree_pow_three : dThree ^ 3 = 1 := by
  decide +kernel

theorem dThree_pow_apply_seven : ∀ r : ℕ, r < 3 → (dThree ^ r) 7 = 7 → r = 0 := by
  decide +kernel

theorem exists_embedSeven_of_mem {Q : Subgroup (Perm (Fin 10))} (h3 : ¬ 3 ∣ Nat.card Q)
    {x : Perm (Fin 10)} (hx : x ∈ Q) (hc : x * dThree = dThree * x) :
    ∃ σ, x = embedSeven σ := by
  obtain ⟨i, σ, rfl⟩ := exists_eq_of_commute_dThree hc
  refine ⟨σ, ?_⟩
  have hpow : (dThree ^ (i : ℕ) * embedSeven σ) ^ Nat.card Q = 1 :=
    congrArg Subtype.val (pow_card_eq_one' (x := (⟨_, hx⟩ : Q)))
  have hcomm : Commute (dThree ^ (i : ℕ)) (embedSeven σ) :=
    ((show Commute (embedSeven σ) dThree from embedSeven_commute σ).pow_right _).symm
  rw [hcomm.mul_pow, ← pow_mul, ← map_pow] at hpow
  have h7 := congrArg (fun π : Perm (Fin 10) => π 7) hpow
  simp only [Perm.mul_apply, Perm.one_apply] at h7
  rw [embedSeven_apply_of_ge _ (show ¬ (7 : Fin 10).val < 7 by decide),
    pow_eq_pow_mod _ dThree_pow_three] at h7
  have h0 := dThree_pow_apply_seven _ (Nat.mod_lt _ (by norm_num)) h7
  have hi : (i : ℕ) = 0 := by
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 (Nat.dvd_of_mod_eq_zero h0) with h | h
    · have := i.isLt
      omega
    · exact absurd h h3
  rw [hi, pow_zero, one_mul]

theorem cent_dThree_le {Q : Subgroup (Perm (Fin 10))} (h3 : ¬ 3 ∣ Nat.card Q)
    (hE : eTwentySeven ≤ normalizer (Q : Set (Perm (Fin 10)))) :
    Q ⊓ centralizer {dThree} ≤ kOne ∨ Q ⊓ centralizer {dThree} ≤ kTwo := by
  set R := Q ⊓ centralizer ({dThree} : Set (Perm (Fin 10))) with hR
  have hRc : ∀ x ∈ R, Commute x dThree := fun x hx =>
    mem_centralizer_singleton_iff.1 (mem_inf.1 hx).2
  have hconjR : ∀ g ∈ eTwentySeven, Commute g dThree → ∀ y ∈ R, g * y * g⁻¹ ∈ R := by
    intro g hg hg3 y hy
    refine mem_inf.2 ⟨(mem_normalizer_iff.1 (hE hg) y).1 (mem_inf.1 hy).1, ?_⟩
    exact mem_centralizer_singleton_iff.2 ((hg3.mul_left (hRc y hy)).mul_left hg3.inv_left)
  set P : Subgroup (Perm (Fin 7)) := R.comap embedSeven with hP
  have hPcard : ¬ 3 ∣ Nat.card P := by
    intro h
    apply h3
    have h1 : Nat.card (P.map embedSeven) = Nat.card P :=
      Subgroup.card_map_of_injective embedSeven_injective
    have h2 : P.map embedSeven ≤ Q := by
      rintro _ ⟨σ, hσ, rfl⟩
      exact (mem_inf.1 hσ).1
    have h4 : 3 ∣ Nat.card (P.map embedSeven) := by
      rw [h1]
      exact h
    exact h4.trans (Subgroup.card_dvd_of_le h2)
  have hPn : ∀ c : Perm (Fin 7), embedSeven c ∈ eTwentySeven →
      c ∈ normalizer (P : Set (Perm (Fin 7))) := by
    intro c hc
    refine mem_normalizer_iff.2 fun σ => ⟨fun hσ => ?_, fun hσ => ?_⟩
    · change embedSeven (c * σ * c⁻¹) ∈ R
      rw [map_mul, map_mul, map_inv]
      exact hconjR _ hc (embedSeven_commute c) _ hσ
    · change embedSeven σ ∈ R
      have hc' : embedSeven c⁻¹ ∈ eTwentySeven := by
        rw [map_inv]
        exact inv_mem hc
      have e : embedSeven σ =
          embedSeven c⁻¹ * embedSeven (c * σ * c⁻¹) * (embedSeven c⁻¹)⁻¹ := by
        simp only [map_mul, map_inv]
        group
      rw [e]
      exact hconjR _ hc' (embedSeven_commute c⁻¹) _ hσ
  have h1 : embedSeven cOne ∈ eTwentySeven := by
    rw [embedSeven_cOne_cTwo.1]
    exact dOne_mem
  have h2 : embedSeven cTwo ∈ eTwentySeven := by
    rw [embedSeven_cOne_cTwo.2]
    exact dTwo_mem
  rcases le_vOne_or_le_vTwo hPcard (hPn cOne h1) (hPn cTwo h2) with hle | hle
  · right
    intro x hx
    obtain ⟨σ, rfl⟩ := exists_embedSeven_of_mem h3 (mem_inf.1 hx).1 (hRc x hx)
    obtain ⟨m, hm⟩ := hle (show σ ∈ P from hx)
    rw [hm, embedSeven_vOneF]
    exact ⟨m, rfl⟩
  · left
    intro x hx
    obtain ⟨σ, rfl⟩ := exists_embedSeven_of_mem h3 (mem_inf.1 hx).1 (hRc x hx)
    obtain ⟨m, hm⟩ := hle (show σ ∈ P from hx)
    rw [hm, embedSeven_vTwoF]
    exact ⟨m, rfl⟩

theorem cent_le_of_conj {Q : Subgroup (Perm (Fin 10))} (h3 : ¬ 3 ∣ Nat.card Q)
    (hE : eTwentySeven ≤ normalizer (Q : Set (Perm (Fin 10)))) {g d : Perm (Fin 10)}
    (hg : g ∈ normTen) (hd : g * d * g⁻¹ = dThree) {K₁ K₂ : Subgroup (Perm (Fin 10))}
    (hK₁ : ∀ x ∈ kOne, g⁻¹ * x * g ∈ K₁) (hK₂ : ∀ x ∈ kTwo, g⁻¹ * x * g ∈ K₂) :
    Q ⊓ centralizer {d} ≤ K₁ ∨ Q ⊓ centralizer {d} ≤ K₂ := by
  set Q' := Q.map (MulAut.conj g).toMonoidHom with hQ'
  have hmemQ' : ∀ y ∈ Q, g * y * g⁻¹ ∈ Q' := fun y hy => ⟨y, hy, rfl⟩
  have hcard : Nat.card Q' = Nat.card Q :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hE' : eTwentySeven ≤ normalizer (Q' : Set (Perm (Fin 10))) := by
    intro e he
    have he' : g⁻¹ * e * g ∈ eTwentySeven := by
      have := (mem_normalizer_iff.1 (inv_mem hg) e).1 he
      rwa [inv_inv] at this
    have h2 := Subgroup.le_normalizer_map (MulAut.conj g).toMonoidHom ⟨_, hE he', rfl⟩
    have e_eq : (MulAut.conj g).toMonoidHom (g⁻¹ * e * g) = e := by
      show g * (g⁻¹ * e * g) * g⁻¹ = e
      group
    rwa [e_eq] at h2
  have h3' : ¬ 3 ∣ Nat.card Q' := by
    rw [hcard]
    exact h3
  have hy' : ∀ y ∈ Q ⊓ centralizer {d}, g * y * g⁻¹ ∈ Q' ⊓ centralizer {dThree} := by
    intro y hy
    refine mem_inf.2 ⟨hmemQ' y (mem_inf.1 hy).1, mem_centralizer_singleton_iff.2 ?_⟩
    have hyd : y * d = d * y := mem_centralizer_singleton_iff.1 (mem_inf.1 hy).2
    rw [← hd]
    calc g * y * g⁻¹ * (g * d * g⁻¹) = g * (y * d) * g⁻¹ := by group
      _ = g * (d * y) * g⁻¹ := by rw [hyd]
      _ = g * d * g⁻¹ * (g * y * g⁻¹) := by group
  rcases cent_dThree_le h3' hE' with hle | hle
  · left
    intro y hy
    have := hK₁ _ (hle (hy' y hy))
    rwa [show g⁻¹ * (g * y * g⁻¹) * g = y by group] at this
  · right
    intro y hy
    have := hK₂ _ (hle (hy' y hy))
    rwa [show g⁻¹ * (g * y * g⁻¹) * g = y by group] at this

theorem le_of_forall_commute {G : Type} [Group G] [Finite G] {A Q W : Subgroup G}
    [CFSG.IsElementaryAbelian 3 A] (hA : 9 ≤ Nat.card A) (h3 : ¬ 3 ∣ Nat.card Q)
    (hAQ : A ≤ normalizer (Q : Set G))
    (hW : ∀ a ∈ A, a ≠ 1 → ∀ x ∈ Q, x * a = a * x → x ∈ W) : Q ≤ W := by
  let φ : A →* MulAut Q := Q.normalizerMonoidHom.comp (Subgroup.inclusion hAQ)
  let _ : MulDistribMulAction A Q := MulDistribMulAction.compHom Q φ
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (A := A) (H := Q) (p := 3)
    (by norm_num; exact hA) h3
  have hfix : ∀ (a : A) (x : Q), x ∈ CFSG.fixedPointSubgroup (Subgroup.zpowers a) Q →
      (x : G) * a = a * x := by
    intro a x hx
    rw [CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff] at hx
    have h := congrArg Subtype.val hx
    change (a : G) * x * (a : G)⁻¹ = x at h
    nth_rewrite 1 [← h]
    group
  intro y hy
  have htop : (⊤ : Subgroup Q) ≤ W.comap Q.subtype := by
    rw [← hgen]
    exact iSup₂_le fun a ha x hx =>
      hW a a.2 (fun h => ha (Subtype.ext h)) x x.2 (hfix a x hx)
  exact htop (Subgroup.mem_top ⟨y, hy⟩)

theorem plane_mul : (∀ i j i' j' : Fin 3, ∃ a b : Fin 3,
      eTwentySevenF i j 0 * eTwentySevenF i' j' 0 = eTwentySevenF a b 0) ∧
    (∀ j k j' k' : Fin 3, ∃ a b : Fin 3,
      eTwentySevenF 0 j k * eTwentySevenF 0 j' k' = eTwentySevenF 0 a b) := by
  decide +kernel

theorem plane_inv : (∀ i j : Fin 3, ∃ a b : Fin 3, (eTwentySevenF i j 0)⁻¹ = eTwentySevenF a b 0) ∧
    (∀ j k : Fin 3, ∃ a b : Fin 3, (eTwentySevenF 0 j k)⁻¹ = eTwentySevenF 0 a b) := by
  decide +kernel

theorem plane_injective : (∀ p q : Fin 3 × Fin 3,
      eTwentySevenF p.1 p.2 0 = eTwentySevenF q.1 q.2 0 → p = q) ∧
    (∀ p q : Fin 3 × Fin 3, eTwentySevenF 0 p.1 p.2 = eTwentySevenF 0 q.1 q.2 → p = q) := by
  decide +kernel

theorem eTwentySevenF_pow_three : ∀ i j k : Fin 3, eTwentySevenF i j k ^ 3 = 1 := by
  decide +kernel

@[expose] def planeOne : Subgroup (Perm (Fin 10)) where
  carrier := {x | ∃ i j : Fin 3, x = eTwentySevenF i j 0}
  mul_mem' := by
    rintro _ _ ⟨i, j, rfl⟩ ⟨i', j', rfl⟩
    exact plane_mul.1 i j i' j'
  one_mem' := ⟨0, 0, eTwentySevenF_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨i, j, rfl⟩
    exact plane_inv.1 i j

@[expose] def planeTwo : Subgroup (Perm (Fin 10)) where
  carrier := {x | ∃ j k : Fin 3, x = eTwentySevenF 0 j k}
  mul_mem' := by
    rintro _ _ ⟨j, k, rfl⟩ ⟨j', k', rfl⟩
    exact plane_mul.2 j k j' k'
  one_mem' := ⟨0, 0, eTwentySevenF_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨j, k, rfl⟩
    exact plane_inv.2 j k

theorem card_planeOne : Nat.card planeOne = 9 := by
  have : (planeOne : Set (Perm (Fin 10))) =
      Set.range (fun p : Fin 3 × Fin 3 => eTwentySevenF p.1 p.2 0) := by
    ext x
    exact ⟨fun ⟨i, j, h⟩ => ⟨(i, j), h.symm⟩, fun ⟨p, h⟩ => ⟨p.1, p.2, h.symm⟩⟩
  rw [← SetLike.coe_sort_coe, this,
    Nat.card_range_of_injective (fun p q h => plane_injective.1 p q h)]
  simp

theorem card_planeTwo : Nat.card planeTwo = 9 := by
  have : (planeTwo : Set (Perm (Fin 10))) =
      Set.range (fun p : Fin 3 × Fin 3 => eTwentySevenF 0 p.1 p.2) := by
    ext x
    exact ⟨fun ⟨j, k, h⟩ => ⟨(j, k), h.symm⟩, fun ⟨p, h⟩ => ⟨p.1, p.2, h.symm⟩⟩
  rw [← SetLike.coe_sort_coe, this,
    Nat.card_range_of_injective (fun p q h => plane_injective.2 p q h)]
  simp

instance : CFSG.IsElementaryAbelian 3 planeOne where
  is_comm := ⟨fun ⟨x, hx⟩ ⟨y, hy⟩ => by
    obtain ⟨i, j, rfl⟩ := hx
    obtain ⟨k, l, rfl⟩ := hy
    exact Subtype.ext (eTwentySevenF_comm i j 0 k l 0)⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun ⟨x, hx⟩ => by
    obtain ⟨i, j, rfl⟩ := hx
    exact Subtype.ext (eTwentySevenF_pow_three i j 0)

instance : CFSG.IsElementaryAbelian 3 planeTwo where
  is_comm := ⟨fun ⟨x, hx⟩ ⟨y, hy⟩ => by
    obtain ⟨j, k, rfl⟩ := hx
    obtain ⟨l, m, rfl⟩ := hy
    exact Subtype.ext (eTwentySevenF_comm 0 j k 0 l m)⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun ⟨x, hx⟩ => by
    obtain ⟨j, k, rfl⟩ := hx
    exact Subtype.ext (eTwentySevenF_pow_three 0 j k)

theorem planeOne_le : planeOne ≤ eTwentySeven := by
  rintro _ ⟨i, j, rfl⟩
  exact ⟨i, j, 0, rfl⟩

theorem planeTwo_le : planeTwo ≤ eTwentySeven := by
  rintro _ ⟨j, k, rfl⟩
  exact ⟨0, j, k, rfl⟩

theorem diagFree_fix : ∀ i j k l : Fin 3, i ≠ 0 → j ≠ 0 → k ≠ 0 → l ≠ 0 →
    ∀ p : Fin 10, eTwentySevenF i j 0 p = p → eTwentySevenF 0 k l p = p → p = 6 := by
  decide +kernel

theorem diagFree_fixOne : ∀ k l : Fin 3, k ≠ 0 → l ≠ 0 →
    ∀ p : Fin 10, eTwentySevenF 0 k l p = p → p ≠ 6 → ∃ a : Fin 3, p = (dOne ^ (a : ℕ)) 0 := by
  decide +kernel

theorem diagFree_fixThree : ∀ i j : Fin 3, i ≠ 0 → j ≠ 0 →
    ∀ p : Fin 10, eTwentySevenF i j 0 p = p → p ≠ 6 → ∃ c : Fin 3, p = (dThree ^ (c : ℕ)) 7 := by
  decide +kernel

theorem diagFree_moved : ∀ i j k l : Fin 3, i ≠ 0 → j ≠ 0 → k ≠ 0 → l ≠ 0 →
    ∀ p : Fin 10, eTwentySevenF i j 0 p ≠ p → eTwentySevenF 0 k l p ≠ p →
      ∃ b : Fin 3, p = (dTwo ^ (b : ℕ)) 3 := by
  decide +kernel

theorem diagFree_cover : (∀ i j : Fin 3, i ≠ 0 → ∀ q : Fin 10, q.val < 3 →
      ∃ n : Fin 3, q = (eTwentySevenF i j 0 ^ (n : ℕ)) 0) ∧
    (∀ i j : Fin 3, j ≠ 0 → ∀ q : Fin 10, 3 ≤ q.val → q.val < 6 →
      ∃ n : Fin 3, q = (eTwentySevenF i j 0 ^ (n : ℕ)) 3) ∧
    (∀ k l : Fin 3, l ≠ 0 → ∀ q : Fin 10, 7 ≤ q.val →
      ∃ n : Fin 3, q = (eTwentySevenF 0 k l ^ (n : ℕ)) 7) := by
  decide +kernel

theorem diagFree_points : ∀ i j k l : Fin 3, j ≠ 0 → k ≠ 0 →
    eTwentySevenF i j 0 6 = 6 ∧ eTwentySevenF 0 k l 6 = 6 ∧ eTwentySevenF 0 k l 0 = 0 ∧
    eTwentySevenF i j 0 3 ≠ 3 ∧ eTwentySevenF 0 k l 3 ≠ 3 ∧ eTwentySevenF i j 0 7 = 7 := by
  decide +kernel

theorem eTwentySevenF_apply : ∀ a b c : Fin 3, eTwentySevenF a b c 0 = (dOne ^ (a : ℕ)) 0 ∧
    eTwentySevenF a b c 3 = (dTwo ^ (b : ℕ)) 3 ∧ eTwentySevenF a b c 7 = (dThree ^ (c : ℕ)) 7 ∧
    eTwentySevenF a b c 6 = 6 := by
  decide +kernel

theorem mem_eTwentySeven_of_commute_diagFree {x : Perm (Fin 10)} {i j k l : Fin 3} (hi : i ≠ 0)
    (hj : j ≠ 0) (hk : k ≠ 0) (hl : l ≠ 0)
    (hu : x * eTwentySevenF i j 0 = eTwentySevenF i j 0 * x)
    (hv : x * eTwentySevenF 0 k l = eTwentySevenF 0 k l * x) : x ∈ eTwentySeven := by
  have K1 := diagFree_fix i j k l hi hj hk hl
  have K2 := diagFree_fixOne k l hk hl
  have K3 := diagFree_moved i j k l hi hj hk hl
  have K4 := diagFree_fixThree i j hi hj
  obtain ⟨K5a, K5b, K5c⟩ := diagFree_cover
  obtain ⟨hu6, hv6, hv0, hu3, hv3, hu7⟩ := diagFree_points i j k l hj hk
  have cu : ∀ p, x (eTwentySevenF i j 0 p) = eTwentySevenF i j 0 (x p) := fun p => by
    have := congrArg (fun σ : Perm (Fin 10) => σ p) hu
    simpa [Perm.mul_apply] using this
  have cv : ∀ p, x (eTwentySevenF 0 k l p) = eTwentySevenF 0 k l (x p) := fun p => by
    have := congrArg (fun σ : Perm (Fin 10) => σ p) hv
    simpa [Perm.mul_apply] using this
  have hx6 : x 6 = 6 := K1 _ (by rw [← cu, hu6]) (by rw [← cv, hv6])
  have hne6 : ∀ p : Fin 10, p ≠ 6 → x p ≠ 6 := fun p hp h =>
    hp (x.injective (h.trans hx6.symm))
  obtain ⟨a, ha⟩ := K2 (x 0) (by rw [← cv, hv0]) (hne6 0 (by decide))
  obtain ⟨b, hb⟩ := K3 (x 3) (fun h => hu3 (x.injective (by rw [cu, h])))
    (fun h => hv3 (x.injective (by rw [cv, h])))
  obtain ⟨c, hc⟩ := K4 (x 7) (by rw [← cu, hu7]) (hne6 7 (by decide))
  obtain ⟨e0, e3, e7, e6⟩ := eTwentySevenF_apply a b c
  set y := (eTwentySevenF a b c)⁻¹ * x with hy
  have hyu : Commute y (eTwentySevenF i j 0) :=
    (show Commute (eTwentySevenF a b c) (eTwentySevenF i j 0) from
      eTwentySevenF_comm a b c i j 0).inv_left.mul_left hu
  have hyv : Commute y (eTwentySevenF 0 k l) :=
    (show Commute (eTwentySevenF a b c) (eTwentySevenF 0 k l) from
      eTwentySevenF_comm a b c 0 k l).inv_left.mul_left hv
  have hfix : ∀ p, x p = eTwentySevenF a b c p → y p = p := fun p h => by
    rw [hy, Perm.mul_apply, h]
    exact Equiv.symm_apply_apply _ p
  have hy0 : y 0 = 0 := hfix 0 (ha.trans e0.symm)
  have hy3 : y 3 = 3 := hfix 3 (hb.trans e3.symm)
  have hy7 : y 7 = 7 := hfix 7 (hc.trans e7.symm)
  have hy6 : y 6 = 6 := hfix 6 (hx6.trans e6.symm)
  have hpow : ∀ (z : Perm (Fin 10)) (n : ℕ) (p : Fin 10), Commute y z → y p = p →
      y ((z ^ n) p) = (z ^ n) p := fun z n p hz hp => by
    have := congrArg (fun σ : Perm (Fin 10) => σ p) (hz.pow_right n).eq
    simp only [Perm.mul_apply] at this
    rw [this, hp]
  have hy1 : y = 1 := by
    refine Perm.ext fun q => ?_
    rw [Perm.one_apply]
    by_cases h0 : q.val < 3
    · obtain ⟨n, rfl⟩ := K5a i j hi q h0
      exact hpow _ _ _ hyu hy0
    by_cases h1 : q.val < 6
    · obtain ⟨n, rfl⟩ := K5b i j hj q (by omega) h1
      exact hpow _ _ _ hyu hy3
    by_cases h2 : q.val = 6
    · rw [show q = 6 from Fin.ext h2]
      exact hy6
    · obtain ⟨n, rfl⟩ := K5c k l hl q (by omega)
      exact hpow _ _ _ hyv hy7
  have : x = eTwentySevenF a b c := by
    rw [← mul_inv_cancel_left (eTwentySevenF a b c) x, ← hy, hy1, mul_one]
  exact ⟨a, b, c, this⟩

theorem axis_pow : ∀ i : Fin 3, i ≠ 0 → eTwentySevenF i 0 0 ^ (i : ℕ) = dOne ∧
    eTwentySevenF 0 i 0 ^ (i : ℕ) = dTwo ∧ eTwentySevenF 0 0 i ^ (i : ℕ) = dThree := by
  decide +kernel

theorem mem_centralizer_of_pow {x z w : Perm (Fin 10)} {n : ℕ} (hw : z ^ n = w)
    (h : x * z = z * x) : x ∈ centralizer {w} := by
  rw [mem_centralizer_singleton_iff, ← hw]
  exact ((show Commute x z from h).pow_right n).eq

theorem le_of_cent_le {Q W : Subgroup (Perm (Fin 10))} (h3 : ¬ 3 ∣ Nat.card Q)
    (hE : eTwentySeven ≤ normalizer (Q : Set (Perm (Fin 10))))
    (h1 : Q ⊓ centralizer {dOne} ≤ W) (h2 : Q ⊓ centralizer {dTwo} ≤ W)
    (h3' : Q ⊓ centralizer {dThree} ≤ W) : Q ≤ W := by
  refine le_of_forall_commute (A := planeOne) (by rw [card_planeOne]) h3 (planeOne_le.trans hE) ?_
  rintro a ⟨i, j, rfl⟩ ha x hxQ hxa
  by_cases hj : j = 0
  · subst hj
    have hi : i ≠ 0 := by
      rintro rfl
      exact ha eTwentySevenF_zero
    exact h1 (mem_inf.2 ⟨hxQ, mem_centralizer_of_pow (axis_pow i hi).1 hxa⟩)
  by_cases hi : i = 0
  · subst hi
    exact h2 (mem_inf.2 ⟨hxQ, mem_centralizer_of_pow (axis_pow j hj).2.1 hxa⟩)
  set R := Q ⊓ centralizer ({eTwentySevenF i j 0} : Set (Perm (Fin 10))) with hR
  have hR3 : ¬ 3 ∣ Nat.card R := fun h => h3 (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hRn : planeTwo ≤ normalizer (R : Set (Perm (Fin 10))) := by
    refine le_normalizer_of_conj fun b hb y hy => mem_inf.2 ⟨?_, ?_⟩
    · exact (mem_normalizer_iff.1 (hE (planeTwo_le hb)) y).1 (mem_inf.1 hy).1
    · obtain ⟨k, l, rfl⟩ := hb
      have hb' : Commute (eTwentySevenF 0 k l) (eTwentySevenF i j 0) :=
        eTwentySevenF_comm 0 k l i j 0
      exact mem_centralizer_singleton_iff.2 ((hb'.mul_left
        (mem_centralizer_singleton_iff.1 (mem_inf.1 hy).2)).mul_left hb'.inv_left)
  have hxR : x ∈ R := mem_inf.2 ⟨hxQ, mem_centralizer_singleton_iff.2 hxa⟩
  refine le_of_forall_commute (A := planeTwo) (W := W) (by rw [card_planeTwo]) hR3 hRn ?_ hxR
  rintro b ⟨k, l, rfl⟩ hb y hyR hyb
  have hyQ : y ∈ Q := (mem_inf.1 hyR).1
  by_cases hl : l = 0
  · subst hl
    have hk : k ≠ 0 := by
      rintro rfl
      exact hb eTwentySevenF_zero
    exact h2 (mem_inf.2 ⟨hyQ, mem_centralizer_of_pow (axis_pow k hk).2.1 hyb⟩)
  by_cases hk : k = 0
  · subst hk
    exact h3' (mem_inf.2 ⟨hyQ, mem_centralizer_of_pow (axis_pow l hl).2.2 hyb⟩)
  obtain ⟨a, b', c, hyE⟩ := mem_eTwentySeven_of_commute_diagFree hi hj hk hl
    (mem_centralizer_singleton_iff.1 (mem_inf.1 hyR).2) hyb
  have hy1 : y = 1 := eq_one_of_pow_three h3 hyQ (by rw [hyE]; exact eTwentySevenF_pow_three a b' c)
  rw [hy1]
  exact one_mem W

theorem kF_prod_check : ∀ m n : Fin 4, m ≠ 0 → n ≠ 0 →
    ((kOneF m * kTwoF n) ^ 6 = 1 ∧ (kOneF m * kTwoF n) ^ 2 ≠ 1) ∧
    ((kOneF m * kThreeF n) ^ 6 = 1 ∧ (kOneF m * kThreeF n) ^ 2 ≠ 1) ∧
    ((kTwoF m * kThreeF n) ^ 6 = 1 ∧ (kTwoF m * kThreeF n) ^ 2 ≠ 1) := by
  decide +kernel

theorem kF_transport : ∀ m : Fin 4,
    (∃ n : Fin 4, wCycle⁻¹ * kOneF m * wCycle = kThreeF n) ∧
    (∃ n : Fin 4, wCycle⁻¹ * kTwoF m * wCycle = kOneF n) ∧
    (∃ n : Fin 4, (wCycle * wCycle)⁻¹ * kOneF m * (wCycle * wCycle) = kTwoF n) ∧
    (∃ n : Fin 4, (wCycle * wCycle)⁻¹ * kTwoF m * (wCycle * wCycle) = kThreeF n) := by
  decide +kernel

theorem wCycle_conj_spec : wCycle * dTwo * wCycle⁻¹ = dThree ∧
    wCycle * wCycle * dOne * (wCycle * wCycle)⁻¹ = dThree := by
  decide +kernel

theorem false_of_mem_of_mem {Q : Subgroup (Perm (Fin 10))} (h3 : ¬ 3 ∣ Nat.card Q)
    {x y : Perm (Fin 10)} (hx : x ∈ Q) (hy : y ∈ Q) (h6 : (x * y) ^ 6 = 1)
    (h2 : (x * y) ^ 2 ≠ 1) : False :=
  h3 ((three_dvd_orderOf_of_pow (m := 2) h6 h2).trans
    (Subgroup.orderOf_dvd_natCard Q (mul_mem hx hy)))

theorem le_kOne_or_le_kTwo_or_le_kThree {Q : Subgroup (Perm (Fin 10))} (h3 : ¬ 3 ∣ Nat.card Q)
    (hE : eTwentySeven ≤ normalizer (Q : Set (Perm (Fin 10)))) :
    Q ≤ kOne ∨ Q ≤ kTwo ∨ Q ≤ kThree := by
  have hw : wCycle ∈ normTen := (mem_inf.1 wCycle_mem_normAlt).1
  have hc3 := cent_dThree_le h3 hE
  have hc2 := cent_le_of_conj h3 hE hw wCycle_conj_spec.1 (K₁ := kThree) (K₂ := kOne)
    (fun _ ⟨m, hm⟩ => by
      obtain ⟨n, hn⟩ := (kF_transport m).1
      exact ⟨n, by rw [hm, hn]⟩)
    (fun _ ⟨m, hm⟩ => by
      obtain ⟨n, hn⟩ := (kF_transport m).2.1
      exact ⟨n, by rw [hm, hn]⟩)
  have hc1 := cent_le_of_conj h3 hE (mul_mem hw hw) wCycle_conj_spec.2 (K₁ := kTwo) (K₂ := kThree)
    (fun _ ⟨m, hm⟩ => by
      obtain ⟨n, hn⟩ := (kF_transport m).2.2.1
      exact ⟨n, by rw [hm, hn]⟩)
    (fun _ ⟨m, hm⟩ => by
      obtain ⟨n, hn⟩ := (kF_transport m).2.2.2
      exact ⟨n, by rw [hm, hn]⟩)
  let meets : Subgroup (Perm (Fin 10)) → Prop := fun K => ∃ z ∈ Q, z ∈ K ∧ z ≠ 1
  have key : ∀ W : Subgroup (Perm (Fin 10)), (W = kOne ∨ ¬ meets kOne) →
      (W = kTwo ∨ ¬ meets kTwo) → (W = kThree ∨ ¬ meets kThree) → Q ≤ W := by
    intro W m1 m2 m3
    have piece : ∀ P : Subgroup (Perm (Fin 10)), P ≤ Q → ∀ K, (W = K ∨ ¬ meets K) → P ≤ K →
        P ≤ W := by
      intro P hPQ K hK hPK
      rcases hK with rfl | hK
      · exact hPK
      · intro x hx
        by_cases hx1 : x = 1
        · rw [hx1]
          exact one_mem W
        · exact absurd ⟨x, hPQ hx, hPK hx, hx1⟩ hK
    apply le_of_cent_le h3 hE
    · rcases hc1 with h | h
      · exact piece _ inf_le_left kTwo m2 h
      · exact piece _ inf_le_left kThree m3 h
    · rcases hc2 with h | h
      · exact piece _ inf_le_left kThree m3 h
      · exact piece _ inf_le_left kOne m1 h
    · rcases hc3 with h | h
      · exact piece _ inf_le_left kOne m1 h
      · exact piece _ inf_le_left kTwo m2 h
  have ne0 : ∀ (F : Fin 4 → Perm (Fin 10)) (z : Perm (Fin 10)) (m : Fin 4), F 0 = 1 → z = F m →
      z ≠ 1 → m ≠ 0 := by
    rintro F z m h0 rfl hz rfl
    exact hz h0
  by_cases m1 : meets kOne
  · obtain ⟨z, hzQ, ⟨m, hm⟩, hz1⟩ := m1
    have hm0 := ne0 kOneF z m rfl hm hz1
    refine Or.inl (key kOne (Or.inl rfl) (Or.inr ?_) (Or.inr ?_))
    · rintro ⟨z', hz'Q, ⟨n, hn⟩, hz'1⟩
      have h := (kF_prod_check m n hm0 (ne0 kTwoF z' n rfl hn hz'1)).1
      rw [← hm, ← hn] at h
      exact false_of_mem_of_mem h3 hzQ hz'Q h.1 h.2
    · rintro ⟨z', hz'Q, ⟨n, hn⟩, hz'1⟩
      have h := (kF_prod_check m n hm0 (ne0 kThreeF z' n rfl hn hz'1)).2.1
      rw [← hm, ← hn] at h
      exact false_of_mem_of_mem h3 hzQ hz'Q h.1 h.2
  by_cases m2 : meets kTwo
  · obtain ⟨z, hzQ, ⟨m, hm⟩, hz1⟩ := m2
    have hm0 := ne0 kTwoF z m rfl hm hz1
    refine Or.inr (Or.inl (key kTwo (Or.inr m1) (Or.inl rfl) (Or.inr ?_)))
    rintro ⟨z', hz'Q, ⟨n, hn⟩, hz'1⟩
    have h := (kF_prod_check m n hm0 (ne0 kThreeF z' n rfl hn hz'1)).2.2
    rw [← hm, ← hn] at h
    exact false_of_mem_of_mem h3 hzQ hz'Q h.1 h.2
  · exact Or.inr (Or.inr (key kThree (Or.inr m1) (Or.inr m2) (Or.inl rfl)))

theorem kF_conj : ∀ (i j k : Fin 3) (m : Fin 4),
    (∃ n : Fin 4, eTwentySevenF i j k * kOneF m * (eTwentySevenF i j k)⁻¹ = kOneF n) ∧
    (∃ n : Fin 4, eTwentySevenF i j k * kTwoF m * (eTwentySevenF i j k)⁻¹ = kTwoF n) ∧
    (∃ n : Fin 4, eTwentySevenF i j k * kThreeF m * (eTwentySevenF i j k)⁻¹ = kThreeF n) := by
  decide +kernel

theorem eTwentySeven_le_normalizer_k :
    eTwentySeven ≤ normalizer (kOne : Set (Perm (Fin 10))) ∧
    eTwentySeven ≤ normalizer (kTwo : Set (Perm (Fin 10))) ∧
    eTwentySeven ≤ normalizer (kThree : Set (Perm (Fin 10))) := by
  refine ⟨le_normalizer_of_conj ?_, le_normalizer_of_conj ?_, le_normalizer_of_conj ?_⟩ <;>
  · rintro _ ⟨i, j, k, rfl⟩ _ ⟨m, rfl⟩
    first
    | exact (kF_conj i j k m).1
    | exact (kF_conj i j k m).2.1
    | exact (kF_conj i j k m).2.2

theorem kThreeF_spec : ∀ (i j : Fin 3) (m : Fin 4),
    kThreeF m * eTwentySevenF i j 0 = eTwentySevenF i j 0 * kThreeF m ∧
      Perm.sign (kThreeF m) = 1 := by
  decide +kernel

@[expose] def finFourEquiv : Fin 4 ≃ {x : Fin 10 // 6 ≤ x.val} where
  toFun i := ⟨⟨i.val + 6, by omega⟩, by simp⟩
  invFun x := ⟨x.1.val - 6, by have := x.1.isLt; omega⟩
  left_inv i := Fin.ext (by change i.val + 6 - 6 = i.val; omega)
  right_inv x := by
    obtain ⟨⟨v, hv⟩, h6⟩ := x
    change 6 ≤ v at h6
    apply Subtype.ext
    apply Fin.ext
    change v - 6 + 6 = v
    omega

@[expose] def embedFour : Perm (Fin 4) →* Perm (Fin 10) := Perm.extendDomainHom finFourEquiv

theorem embedFour_injective : Function.Injective embedFour :=
  Perm.extendDomainHom_injective finFourEquiv

theorem sign_embedFour (σ : Perm (Fin 4)) : Perm.sign (embedFour σ) = Perm.sign σ :=
  Perm.sign_extendDomain σ finFourEquiv

theorem embedFour_apply_of_lt (σ : Perm (Fin 4)) {x : Fin 10} (hx : ¬ 6 ≤ x.val) :
    embedFour σ x = x :=
  Perm.extendDomain_apply_not_subtype σ finFourEquiv hx

theorem embedFour_apply_of_ge (σ : Perm (Fin 4)) {x : Fin 10} (hx : 6 ≤ x.val) :
    (embedFour σ x).val = (σ ⟨x.val - 6, by have := x.isLt; omega⟩).val + 6 := by
  change (Perm.extendDomain σ finFourEquiv x).val = _
  rw [Perm.extendDomain_apply_subtype σ finFourEquiv hx]
  rfl

theorem finFourEquiv_apply (i : Fin 4) : ((finFourEquiv i : Fin 10)).val = i.val + 6 := rfl

theorem finFourEquiv_symm_apply (x : {x : Fin 10 // 6 ≤ x.val}) :
    (finFourEquiv.symm x).val = x.1.val - 6 := rfl

theorem embedFour_eq_of (σ : Perm (Fin 4)) (τ : Perm (Fin 10))
    (h1 : ∀ y : Fin 4, (τ (finFourEquiv y)).val = (σ y).val + 6)
    (h2 : ∀ x : Fin 10, ¬ 6 ≤ x.val → τ x = x) : embedFour σ = τ := by
  ext x
  by_cases hx : 6 ≤ x.val
  · rw [embedFour_apply_of_ge _ hx]
    have e : (finFourEquiv ⟨x.val - 6, by have := x.isLt; omega⟩ : Fin 10) = x :=
      Fin.ext (by rw [finFourEquiv_apply]; show x.val - 6 + 6 = x.val; omega)
    rw [← h1, e]
  · rw [embedFour_apply_of_lt _ hx, h2 x hx]

theorem exists_embedFour {τ : Perm (Fin 10)} (h : ∀ p : Fin 10, p.val < 6 → τ p = p) :
    ∃ σ : Perm (Fin 4), τ = embedFour σ := by
  have hτ : ∀ z : Fin 10, 6 ≤ (τ z).val ↔ 6 ≤ z.val := by
    intro z
    constructor
    · intro hτz
      by_contra hz
      rw [h z (by omega)] at hτz
      exact hz hτz
    · intro hz
      by_contra hτz
      have h1 : τ (τ z) = τ z := h (τ z) (by omega)
      have h2 : τ z = z := τ.injective h1
      rw [h2] at hτz
      exact hτz hz
  refine ⟨finFourEquiv.symm.permCongr (τ.subtypePerm hτ), ?_⟩
  symm
  refine embedFour_eq_of _ _ (fun y => ?_) (fun x hx => h x (by omega))
  rw [Equiv.permCongr_apply, finFourEquiv_symm_apply, Equiv.symm_symm, Perm.subtypePerm_apply]
  have := (hτ (finFourEquiv y)).2 (finFourEquiv y).2
  show (τ (finFourEquiv y)).val = (τ (finFourEquiv y)).val - 6 + 6
  omega

theorem sq_eq_one_cases : ∀ σ : Perm (Fin 4), Perm.sign σ = 1 → σ ^ 2 = 1 →
    σ = 1 ∨ σ = swap 0 1 * swap 2 3 ∨ σ = swap 0 2 * swap 1 3 ∨ σ = swap 0 3 * swap 1 2 := by
  decide +kernel

theorem embedFour_kThreeF : embedFour (swap 0 1 * swap 2 3) = kThreeF 1 ∧
    embedFour (swap 0 2 * swap 1 3) = kThreeF 2 ∧ embedFour (swap 0 3 * swap 1 2) = kThreeF 3 :=
  ⟨embedFour_eq_of _ _ (by decide +kernel) (by decide +kernel),
    embedFour_eq_of _ _ (by decide +kernel) (by decide +kernel),
    embedFour_eq_of _ _ (by decide +kernel) (by decide +kernel)⟩

theorem mem_kThree_of {τ : Perm (Fin 10)} (h : ∀ p : Fin 10, p.val < 6 → τ p = p)
    (hs : Perm.sign τ = 1) (h2 : τ ^ 2 = 1) : τ ∈ kThree := by
  obtain ⟨σ, rfl⟩ := exists_embedFour h
  rw [sign_embedFour] at hs
  have h2' : σ ^ 2 = 1 := embedFour_injective (by rw [map_pow, h2, map_one])
  rcases sq_eq_one_cases σ hs h2' with rfl | rfl | rfl | rfl
  · exact ⟨0, map_one _⟩
  · exact ⟨1, embedFour_kThreeF.1⟩
  · exact ⟨2, embedFour_kThreeF.2.1⟩
  · exact ⟨3, embedFour_kThreeF.2.2⟩

@[expose] def centTen : Subgroup (Perm (Fin 10)) :=
  centralizer {dOne * dTwo} ⊓ alternatingGroup (Fin 10)

theorem fix_dOne_dTwo : ∀ p : Fin 10, p.val < 6 ↔ (dOne * dTwo) p ≠ p := by
  decide +kernel

theorem kThreeF_fix : ∀ (m : Fin 4) (p : Fin 10), p.val < 6 → kThreeF m p = p := by
  decide +kernel

instance kThree_normal : (kThree.subgroupOf centTen).Normal where
  conj_mem := by
    rintro ⟨v, hv⟩ hvK ⟨g, hg⟩
    obtain ⟨m, rfl⟩ : ∃ m, v = kThreeF m := hvK
    change g * kThreeF m * g⁻¹ ∈ kThree
    have hgc : g * (dOne * dTwo) = dOne * dTwo * g :=
      mem_centralizer_singleton_iff.1 (mem_inf.1 hg).1
    have hcomm : ∀ q, g ((dOne * dTwo) q) = (dOne * dTwo) (g q) := fun q => by
      have := congrArg (fun σ : Perm (Fin 10) => σ q) hgc
      simpa only [Perm.mul_apply] using this
    refine mem_kThree_of (fun p hp => ?_) ?_ ?_
    · have hq : (g⁻¹ p).val < 6 := by
        by_contra hq
        have h1 : (dOne * dTwo) (g⁻¹ p) = g⁻¹ p := by
          by_contra h1
          exact hq ((fix_dOne_dTwo _).2 h1)
        have h2 : (dOne * dTwo) p = p := by
          have := hcomm (g⁻¹ p)
          have hgg : g (g⁻¹ p) = p := by simp
          rw [h1, hgg] at this
          exact this.symm
        exact (fix_dOne_dTwo p).1 hp h2
      have hgg : g (g⁻¹ p) = p := by simp
      rw [Perm.mul_apply, Perm.mul_apply, kThreeF_fix m _ hq, hgg]
    · rw [map_mul, map_mul, map_inv, (kThreeF_spec 0 0 m).2, mul_one, mul_inv_cancel]
    · rw [conj_pow, pow_two, (kF_sq m).2.2, mul_one, mul_inv_cancel]

end CFSG.RankThree.PartTwo.KFacts.KP2
