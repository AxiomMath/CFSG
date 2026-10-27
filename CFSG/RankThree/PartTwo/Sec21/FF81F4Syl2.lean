
module

public import CFSG.RankThree.PartTwo.Sec21.FF81F4Easy
public import CFSG.RankThree.PartTwo.Sec21.FF81F4Roots
public import CFSG.RankThree.PartTwo.Sec21.FF81F4Cls
public import CFSG.RankThree.PartTwo.Sec21.FF81F4Enum
public import CFSG.Sporadic.Schreier.TitsIso

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.F4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79
  CFSG.RankThree.PartTwo.Sec21.FF79.L41 CFSG.RankThree.PartTwo.Sec21.FF81
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.ComponentClassification.RankTwoExceptional.F4Sec8
open CFSG.LieType.Chevalley.RootOps CFSG.LieType.Simplicity.TitsBits

section Q0

@[expose] noncomputable def Q₀ : Subgroup F42C :=
  (posUnipotent ReeTag.F4.tag (ZMod 2)).subgroupOf (adjointGroup ReeTag.F4.tag (ZMod 2))

noncomputable abbrev rootElt (i : Fin 24) : F42C := f4Rep (ZMod 2) [24 + i]

theorem card_Q₀ : Nat.card ↥Q₀ = 2 ^ 24 :=
  (Nat.card_congr (Subgroup.subgroupOfEquivOfLe posUnipotent_le_adjointGroup).toEquiv).trans
    CFSG.Monster.B.GSide.natCard_posUnipotent_F4_zmod_two

theorem rootElt_mem (i : Fin 24) : rootElt i ∈ Q₀ := by
  have h := f4x_mem_posUnipotent (K := ZMod 2) (i := 24 + (i : ℕ)) ⟨by omega, by omega⟩ 1
  rw [← coe_f4Rep_singleton] at h
  exact h

theorem isSylowOf_Q₀ : IsSylowOf 2 Q₀ (⊤ : Subgroup F42C) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine isSylowOf_of_card_p le_top ?_
  rw [card_Q₀, Subgroup.card_top, card_F42C, factorization_two_card]

theorem Q₀_le_closure : Q₀ ≤ Subgroup.closure (Set.range rootElt) := by
  intro z hz
  obtain ⟨c, hc⟩ := exists_f4_coords (K := ZMod 2) (z := z.1) hz
  let y : ℕ → F42C := fun i => ⟨f4x (ZMod 2) i (c i), pinnedX_mem_adjointGroup _ _⟩
  have hy : ∀ i ∈ f4PosList, y i ∈ Subgroup.closure (Set.range rootElt) := by
    intro i hi
    obtain ⟨j, rfl⟩ : ∃ j : Fin 24, i = 24 + j := by
      rw [f4PosList, List.mem_ofFn] at hi
      obtain ⟨j, rfl⟩ := hi
      exact ⟨j, rfl⟩
    rcases card_two_cases (K := ZMod 2) (by simp) (c (24 + j)) with h0 | h1
    · have : y (24 + j) = 1 := Subtype.ext (by
        show f4x (ZMod 2) (24 + j) (c (24 + j)) = 1
        rw [h0, f4x_zero])
      rw [this]; exact Subgroup.one_mem _
    · have : y (24 + j) = rootElt j := Subtype.ext (by
        show f4x (ZMod 2) (24 + j) (c (24 + j)) = _
        rw [h1]; exact (coe_f4Rep_singleton (24 + (j : ℕ))).symm)
      rw [this]; exact Subgroup.subset_closure ⟨j, rfl⟩
  have hz' : z = (f4PosList.map y).prod := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_list_prod, List.map_map]
    exact hc
  rw [hz']
  exact Subgroup.list_prod_mem _ (fun x hx => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    exact hy i hi)

set_option maxRecDepth 100000 in
theorem rb_44_ne_rb_43 : rb 44 % 2 ^ 2704 ≠ rb 43 % 2 ^ 2704 := by decide +kernel

set_option maxRecDepth 100000 in
theorem rb_44_ne_one : rb 44 % 2 ^ 2704 ≠ oneBits % 2 ^ 2704 := by decide +kernel

set_option maxRecDepth 100000 in
theorem rb_43_ne_one : rb 43 % 2 ^ 2704 ≠ oneBits % 2 ^ 2704 := by decide +kernel

theorem four_le_card_of_ne {G : Type*} [Finite G] {x y z w : G} (h1 : x ≠ y) (h2 : x ≠ z)
    (h3 : x ≠ w) (h4 : y ≠ z) (h5 : y ≠ w) (h6 : z ≠ w) : 4 ≤ Nat.card G := by
  have hinj : Function.Injective (![x, y, z, w] : Fin 4 → G) := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [Ne.symm]
  have := Nat.card_le_card_of_injective _ hinj
  simpa using this

noncomputable abbrev zA : F42C := f4Rep (ZMod 2) [44]

noncomputable abbrev zB' : F42C := f4Rep (ZMod 2) [47]

theorem zA_mem : zA ∈ Q₀ := rootElt_mem ⟨20, by norm_num⟩

theorem zB'_mem : zB' ∈ Q₀ := rootElt_mem ⟨23, by norm_num⟩

theorem zA_central {q : F42C} (hq : q ∈ Q₀) : q * zA = zA * q := by
  have h := f4x_central (K := ZMod 2) (k := 44) (Or.inl rfl) 1 (u := q.1) hq
  rw [← coe_f4Rep_singleton] at h
  exact Subtype.ext h

theorem zB'_central {q : F42C} (hq : q ∈ Q₀) : q * zB' = zB' * q := by
  have h := f4x_central (K := ZMod 2) (k := 47) (Or.inr rfl) 1 (u := q.1) hq
  rw [← coe_f4Rep_singleton] at h
  exact Subtype.ext h

theorem zB'_sq : zB' * zB' = 1 := by
  apply Subtype.ext
  show (f4Rep (ZMod 2) [47]).1 * (f4Rep (ZMod 2) [47]).1 = 1
  rw [coe_f4Rep_singleton, f4x, ← pinnedX_add]
  have : (1 : ZMod 2) + 1 = 0 := by decide
  rw [this, pinnedX_zero]

theorem zA_ne_zB' : zA ≠ zB' := by
  intro h
  have h1 := (hasBits_f4Rep_single (K := ZMod 2) 44 ⟨by norm_num, by norm_num⟩).eq_iff
    (hasBits_f4Rep_single (K := ZMod 2) 47 ⟨by norm_num, by norm_num⟩)
  have c44 : certPos 44 = 44 := rfl
  have c47 : certPos 47 = 43 := rfl
  rw [c44, c47] at h1
  exact rb_44_ne_rb_43 (h1.1 h)

theorem zA_ne_one : zA ≠ 1 := by
  intro h
  have h1 := (hasBits_f4Rep_single (K := ZMod 2) 44 ⟨by norm_num, by norm_num⟩).eq_iff
    (hasBits_one (K := ZMod 2))
  have c44 : certPos 44 = 44 := rfl
  rw [c44] at h1
  exact rb_44_ne_one (h1.1 h)

theorem zB'_ne_one : zB' ≠ 1 := by
  intro h
  have h1 := (hasBits_f4Rep_single (K := ZMod 2) 47 ⟨by norm_num, by norm_num⟩).eq_iff
    (hasBits_one (K := ZMod 2))
  have c47 : certPos 47 = 43 := rfl
  rw [c47] at h1
  exact rb_43_ne_one (h1.1 h)

noncomputable def aQ : ↥Q₀ := ⟨zA, zA_mem⟩

noncomputable def bQ : ↥Q₀ := ⟨zB', zB'_mem⟩

theorem aQ_central : aQ ∈ Subgroup.center ↥Q₀ := by
  rw [Subgroup.mem_center_iff]
  intro y
  exact Subtype.ext (zA_central y.2)

theorem bQ_central : bQ ∈ Subgroup.center ↥Q₀ := by
  rw [Subgroup.mem_center_iff]
  intro y
  exact Subtype.ext (zB'_central y.2)

theorem card_center_Q₀ : Nat.card (Subgroup.center ↥Q₀) = 4 := by
  haveI : Finite F42C := finite_adjF
  have hle := (CFSG.Monster.B.GSide.sylow_facts_of_mulEquiv_F4
    (MulEquiv.refl F42C) card_Q₀).1
  refine le_antisymm hle ?_
  have hval : ∀ x y : ↥(Subgroup.center ↥Q₀), x = y → (x : ↥Q₀).1 = (y : ↥Q₀).1 :=
    fun x y h => by rw [h]
  have hsq : zB' * zB' = 1 := zB'_sq
  refine four_le_card_of_ne (x := (1 : ↥(Subgroup.center ↥Q₀)))
    (y := ⟨aQ, aQ_central⟩) (z := ⟨bQ, bQ_central⟩)
    (w := ⟨aQ * bQ, mul_mem aQ_central bQ_central⟩) ?_ ?_ ?_ ?_ ?_ ?_
  · intro h
    have h1 := hval _ _ h
    exact zA_ne_one h1.symm
  · intro h
    have h1 := hval _ _ h
    exact zB'_ne_one h1.symm
  · intro h
    have h1 := hval _ _ h
    have h'' : (1 : F42C) = zA * zB' := h1
    apply zA_ne_zB'
    calc zA = zA * (zB' * zB') := by rw [hsq, mul_one]
      _ = (zA * zB') * zB' := by rw [mul_assoc]
      _ = 1 * zB' := by rw [← h'']
      _ = zB' := one_mul _
  · intro h
    have h1 := hval _ _ h
    exact zA_ne_zB' h1
  · intro h
    have h1 := hval _ _ h
    have h' : zA = zA * zB' := h1
    exact zB'_ne_one (by simpa using h')
  · intro h
    have h1 := hval _ _ h
    have h' : zB' = zA * zB' := h1
    exact zA_ne_one (by simpa using h'.symm)

end Q0

end CFSG.RankThree.PartTwo.Sec21.FF81.F4
