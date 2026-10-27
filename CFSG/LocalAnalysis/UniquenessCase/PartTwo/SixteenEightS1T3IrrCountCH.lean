module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3IrrCountCB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.SmithD39Two

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

private lemma s16t3_no_class_two (r : Fin 3 → Fin 3 → Prop)
    (hrefl : ∀ i, r i i)
    (hsymm : ∀ i j, r i j → r j i)
    (hcard : ∀ i, Nat.card {k : Fin 3 // r k i} = 2) : False := by
  classical
  let T : Fin 3 → Finset (Fin 3) := fun i => Finset.univ.filter (fun k => r k i)
  have hT : ∀ i, (T i).card = 2 := by
    intro i
    have h : (T i).card = Nat.card {k : Fin 3 // r k i} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [h, hcard i]
  have h0T : (0 : Fin 3) ∈ T 0 := by
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hrefl 0
  have hErase : ((T 0).erase 0).card = 1 := by
    rw [Finset.card_erase_of_mem h0T, hT 0]
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hErase
  have hT0 : T 0 = {0, y} := by
    rw [← Finset.insert_erase h0T, hy]
  have hy0 : y ≠ 0 := by
    have hmem : y ∈ (T 0).erase 0 := by rw [hy]; exact Finset.mem_singleton_self y
    exact (Finset.mem_erase.mp hmem).1
  have hyr : r y 0 := by
    have hmem : y ∈ T 0 := by
      rw [hT0]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self y)
    simpa only [T, Finset.mem_filter, Finset.mem_univ, true_and] using hmem
  have hcard_pair : ({0, y} : Finset (Fin 3)).card = 2 := Finset.card_pair (Ne.symm hy0)
  have hTy : T y = {0, y} := by
    have hsub : ({0, y} : Finset (Fin 3)) ⊆ T y := by
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hsymm y 0 hyr
      · rw [Finset.mem_singleton] at hk
        rw [hk]
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hrefl y
    exact (Finset.eq_of_subset_of_card_le hsub (by rw [hT y, hcard_pair])).symm
  obtain ⟨z, _, hz⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := ({0, y} : Finset (Fin 3)))
    (t := Finset.univ) (by rw [hcard_pair]; simp)
  have hz0 : z ≠ 0 := by rintro rfl; exact hz (by simp)
  have hzy : z ≠ y := by rintro rfl; exact hz (by simp)
  have hzT0 : z ∉ T 0 := by rw [hT0]; exact hz
  have hzTy : z ∉ T y := by rw [hTy]; exact hz
  have hzall : ({0, y, z} : Finset (Fin 3)) = Finset.univ := by
    have hcard3 : ({0, y, z} : Finset (Fin 3)).card = 3 := by
      rw [Finset.card_eq_three]
      exact ⟨0, y, z, Ne.symm hy0, Ne.symm hz0, Ne.symm hzy, rfl⟩
    apply Finset.eq_of_subset_of_card_le
    · intro k _; exact Finset.mem_univ k
    · rw [Finset.card_univ, Fintype.card_fin]
      exact hcard3.ge
  have hsubz : T z ⊆ {z} := by
    intro k hk
    by_contra hkz
    have hkrz : r k z := by
      simpa only [T, Finset.mem_filter, Finset.mem_univ, true_and] using hk
    have hkz' : k ≠ z := fun h => hkz (Finset.mem_singleton.mpr h)
    have hk' : k = 0 ∨ k = y := by
      have hkmem : k ∈ ({0, y, z} : Finset (Fin 3)) := by rw [hzall]; exact Finset.mem_univ k
      rcases Finset.mem_insert.mp hkmem with h0 | hkmem
      · exact Or.inl h0
      rcases Finset.mem_insert.mp hkmem with hy' | hz'
      · exact Or.inr hy'
      · exact absurd (Finset.mem_singleton.mp hz') hkz'
    rcases hk' with hk0 | hky
    · rw [hk0] at hkrz
      exact hzT0 (by
        simpa only [T, Finset.mem_filter, Finset.mem_univ, true_and] using hsymm 0 z hkrz)
    · rw [hky] at hkrz
      exact hzTy (by
        simpa only [T, Finset.mem_filter, Finset.mem_univ, true_and] using hsymm y z hkrz)
  have hcardz : (T z).card ≤ 1 := by
    calc (T z).card ≤ ({z} : Finset (Fin 3)).card := Finset.card_le_card hsubz
      _ = 1 := Finset.card_singleton z
  exact absurd hcardz (by rw [hT z]; norm_num)

theorem s16t3_card_irr_three_or_seven [Finite Q] (hQ : ∀ q : Q, q ^ 2 = 1)
    {Λ : Subgroup Γ} {S : Fin 3 → Subgroup Q} (hS : ∀ i, XMod.IsIrr ↥Λ (S i))
    (htop : (⨆ i, S i) = ⊤)
    (hlen : ∀ i, IsotypicOfLength ↥Λ (isoComp ↥Λ (S i)) (S i)
      (Nat.card {k : Fin 3 // XMod.Iso ↥Λ (S k) (S i)}))
    (hE : ∀ i, Nat.card (Module.End ↥(XMod.opRing ↥Λ Q) ↥(XMod.toSubmod (hS i).1)) = 2)
    (hconst : ∀ i j, Nat.card {J : Subgroup Q // XMod.IsIrr ↥Λ J ∧ XMod.Iso ↥Λ J (S i)} =
      Nat.card {J : Subgroup Q // XMod.IsIrr ↥Λ J ∧ XMod.Iso ↥Λ J (S j)}) :
    Nat.card {Y : Subgroup Q // XMod.IsIrr ↥Λ Y} = 3 ∨
      Nat.card {Y : Subgroup Q // XMod.IsIrr ↥Λ Y} = 7 := by
  classical
  let c : Fin 3 → ℕ := fun i => Nat.card {k : Fin 3 // XMod.Iso ↥Λ (S k) (S i)}
  let n : Fin 3 → ℕ :=
    fun i => Nat.card {J : Subgroup Q // XMod.IsIrr ↥Λ J ∧ XMod.Iso ↥Λ J (S i)}
  have hn : ∀ i, n i = 2 ^ c i - 1 := fun i =>
    s16t3_card_iso_type hQ (hS i) (hlen i) (hE i)
  have hcpos : ∀ i, 1 ≤ c i := by
    intro i
    haveI : Nonempty {k : Fin 3 // XMod.Iso ↥Λ (S k) (S i)} := ⟨⟨i, XMod.Iso.refl (S i)⟩⟩
    show 0 < c i
    exact Finite.card_pos
  have hcle : ∀ i, c i ≤ 3 := by
    intro i
    have h : c i ≤ Nat.card (Fin 3) :=
      Finite.card_subtype_le (fun k : Fin 3 => XMod.Iso ↥Λ (S k) (S i))
    have h3 : Nat.card (Fin 3) = 3 := by simp
    omega
  have hcconst : ∀ i, c i = c 0 := by
    intro i
    have h1 : 2 ^ c i - 1 = 2 ^ c 0 - 1 := by
      rw [← hn i, ← hn 0]
      exact hconst i 0
    have h2 : 1 ≤ 2 ^ c i := Nat.one_le_two_pow
    have h3 : 1 ≤ 2 ^ c 0 := Nat.one_le_two_pow
    have h4 : (2 ^ c i - 1) + 1 = (2 ^ c 0 - 1) + 1 := by rw [h1]
    rw [Nat.sub_add_cancel h2, Nat.sub_add_cancel h3] at h4
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) h4
  have hex : ∀ Y : Subgroup Q, XMod.IsIrr ↥Λ Y → ∃ i, XMod.Iso ↥Λ Y (S i) := by
    intro Y hY
    exact CFSG.Quasithin.SmithD391.exists_iso_of_le_iSup (A := ↥Λ) (S := S) hS hY
      (by rw [htop]; exact le_top)
  have hc0 : c 0 = 1 ∨ c 0 = 2 ∨ c 0 = 3 := by
    have h1 := hcpos 0
    have h3 := hcle 0
    omega
  rcases hc0 with h1 | h2 | h3
  · left
    have hci : ∀ i, c i = 1 := fun i => by rw [hcconst i, h1]
    have hni : ∀ i, n i = 1 := by
      intro i
      rw [hn i, hci i]
      norm_num
    have huniq : ∀ i k, XMod.Iso ↥Λ (S k) (S i) → k = i := by
      intro i k hk
      have hcard : Nat.card {k' : Fin 3 // XMod.Iso ↥Λ (S k') (S i)} = 1 := hci i
      haveI : Subsingleton {k' : Fin 3 // XMod.Iso ↥Λ (S k') (S i)} :=
        (Nat.card_eq_one_iff_unique.mp hcard).1
      have hEq : (⟨k, hk⟩ : {k' : Fin 3 // XMod.Iso ↥Λ (S k') (S i)}) =
          ⟨i, XMod.Iso.refl (S i)⟩ := Subsingleton.elim _ _
      exact congrArg Subtype.val hEq
    have huniqJ : ∀ i J, XMod.IsIrr ↥Λ J → XMod.Iso ↥Λ J (S i) → J = S i := by
      intro i J hJ hJi
      have hcard : Nat.card
          {J' : Subgroup Q // XMod.IsIrr ↥Λ J' ∧ XMod.Iso ↥Λ J' (S i)} = 1 := hni i
      haveI : Subsingleton
          {J' : Subgroup Q // XMod.IsIrr ↥Λ J' ∧ XMod.Iso ↥Λ J' (S i)} :=
        (Nat.card_eq_one_iff_unique.mp hcard).1
      have hEq : (⟨J, hJ, hJi⟩ :
            {J' : Subgroup Q // XMod.IsIrr ↥Λ J' ∧ XMod.Iso ↥Λ J' (S i)}) =
          ⟨S i, hS i, XMod.Iso.refl (S i)⟩ := Subsingleton.elim _ _
      exact congrArg Subtype.val hEq
    let e : {Y : Subgroup Q // XMod.IsIrr ↥Λ Y} ≃ Fin 3 :=
      { toFun := fun Y => Classical.choose (hex Y.1 Y.2)
        invFun := fun i => ⟨S i, hS i⟩
        left_inv := fun Y => by
          have hspec := Classical.choose_spec (hex Y.1 Y.2)
          exact Subtype.ext
            (huniqJ (Classical.choose (hex Y.1 Y.2)) Y.1 Y.2 hspec).symm
        right_inv := fun i => by
          have hspec := Classical.choose_spec (hex (S i) (hS i))
          exact huniq i (Classical.choose (hex (S i) (hS i)))
            (XMod.Iso.symm (hS i).1 hspec) }
    rw [Nat.card_congr e]
    simp
  · exfalso
    have hci : ∀ i, c i = 2 := fun i => by rw [hcconst i, h2]
    exact s16t3_no_class_two (fun i j => XMod.Iso ↥Λ (S i) (S j))
      (fun i => XMod.Iso.refl (S i))
      (fun i j h => XMod.Iso.symm (hS i).1 h)
      (fun i => hci i)
  · right
    have hci : ∀ i, c i = 3 := fun i => by rw [hcconst i, h3]
    have hcard0 : Nat.card {k : Fin 3 // XMod.Iso ↥Λ (S k) (S 0)} = 3 := hci 0
    have hiso0 : ∀ k, XMod.Iso ↥Λ (S k) (S 0) := by
      intro k
      by_contra hk
      have hlt := Finite.card_subtype_lt
        (p := fun k : Fin 3 => XMod.Iso ↥Λ (S k) (S 0)) hk
      have h3' : Nat.card (Fin 3) = 3 := by simp
      omega
    let e : {Y : Subgroup Q // XMod.IsIrr ↥Λ Y} ≃
        {J : Subgroup Q // XMod.IsIrr ↥Λ J ∧ XMod.Iso ↥Λ J (S 0)} :=
      { toFun := fun Y => ⟨Y.1, Y.2, (hex Y.1 Y.2).elim (fun i hi => hi.trans (hiso0 i))⟩
        invFun := fun J => ⟨J.1, J.2.1⟩
        left_inv := fun Y => Subtype.ext rfl
        right_inv := fun J => Subtype.ext rfl }
    calc Nat.card {Y : Subgroup Q // XMod.IsIrr ↥Λ Y}
        = Nat.card {J : Subgroup Q // XMod.IsIrr ↥Λ J ∧ XMod.Iso ↥Λ J (S 0)} :=
          Nat.card_congr e
      _ = n 0 := rfl
      _ = 2 ^ c 0 - 1 := hn 0
      _ = 7 := by rw [h3]; norm_num

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
