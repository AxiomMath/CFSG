module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitWeylGen

public section

namespace CFSG.StandardType.QTwo

private theorem qtwoDB37_dPerm_inv_apply {m : ℕ} (σ : Equiv.Perm (Fin m)) (j : Fin m) :
    (dPerm m σ)⁻¹ (dBasis m j) = dBasis m (σ.symm j) := by
  have hinv : (dPerm m σ)⁻¹ = dPerm m σ⁻¹ := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← dPerm_mul, mul_inv_cancel, dPerm_one]
  rw [hinv, dPerm_apply]
  rfl

theorem qtwoDB37_dSign_comm {m : ℕ} (x y : Fin m) : dSign m x y = dSign m y x := by
  refine (dBasis m).ext' fun k => ?_
  rw [dSign_apply, dSign_apply]
  congr 1
  by_cases hx : k = x
  · subst hx; simp
  · by_cases hy : k = y
    · subst hy; simp [hx]
    · simp [hx, hy]

theorem qtwoDB37_dSign_double {m : ℕ} (a b : Fin m) :
    dSign m a b * dSign m a b = 1 := by
  refine (dBasis m).ext' fun k => ?_
  rw [LinearEquiv.mul_apply, dSign_apply, map_smul, dSign_apply, smul_smul]
  by_cases hk : k = a ∨ k = b <;> simp [hk]

private lemma qtwoDB37_scalar_mul {m : ℕ} {a i j k : Fin m} (hia : i ≠ a) (hja : j ≠ a)
    (hij : i ≠ j) :
    (if k = a ∨ k = j then (-1 : ZMod 3) else 1) *
        (if k = a ∨ k = i then (-1 : ZMod 3) else 1) =
      (if k = i ∨ k = j then (-1 : ZMod 3) else 1) := by
  rcases eq_or_ne k a with hka | hka
  · have hki : ¬(k = i) := fun h => hia (h.symm.trans hka)
    have hkj : ¬(k = j) := fun h => hja (h.symm.trans hka)
    rw [if_pos (Or.inl hka), if_pos (Or.inl hka), if_neg (fun h => h.elim hki hkj)]
    decide
  · rcases eq_or_ne k i with hki | hki
    · have hkj : ¬(k = j) := fun h => hij (hki.symm.trans h)
      rw [if_neg (fun h => h.elim hka hkj), if_pos (Or.inr hki), if_pos (Or.inl hki)]
      decide
    · rcases eq_or_ne k j with hkj | hkj
      · rw [if_pos (Or.inr hkj), if_neg (fun h => h.elim hka hki), if_pos (Or.inr hkj)]
        decide
      · rw [if_neg (fun h => h.elim hka hkj), if_neg (fun h => h.elim hka hki),
          if_neg (fun h => h.elim hki hkj)]
        decide

private theorem qtwoDB37_dSign_mul {m : ℕ} {a i j : Fin m} (hia : i ≠ a) (hja : j ≠ a)
    (hij : i ≠ j) : dSign m i j = dSign m a i * dSign m a j := by
  refine (dBasis m).ext' fun k => ?_
  rw [LinearEquiv.mul_apply, dSign_apply, dSign_apply, map_smul, dSign_apply, smul_smul]
  congr 1
  exact (qtwoDB37_scalar_mul hia hja hij).symm

private lemma qtwoDB37_scalar_ab {m : ℕ} {a b k i : Fin m} (hab : a ≠ b) (hka : k ≠ a)
    (hkb : k ≠ b) :
    (if i = b ∨ i = k then (-1 : ZMod 3) else 1) *
        (if i = a ∨ i = k then (-1 : ZMod 3) else 1) =
      (if i = a ∨ i = b then (-1 : ZMod 3) else 1) := by
  rcases eq_or_ne i a with hia | hia
  · have hib : ¬(i = b) := fun h => hab (hia.symm.trans h)
    have hik : ¬(i = k) := fun h => hka (h.symm.trans hia)
    rw [if_neg (fun h => h.elim hib hik), if_pos (Or.inl hia), if_pos (Or.inl hia)]
    decide
  · rcases eq_or_ne i b with hib | hib
    · have hik : ¬(i = k) := fun h => hkb (h.symm.trans hib)
      rw [if_pos (Or.inl hib), if_neg (fun h => h.elim hia hik), if_pos (Or.inr hib)]
      decide
    · rcases eq_or_ne i k with hik | hik
      · rw [if_pos (Or.inr hik), if_pos (Or.inr hik), if_neg (fun h => h.elim hia hib)]
        decide
      · rw [if_neg (fun h => h.elim hib hik), if_neg (fun h => h.elim hia hik),
          if_neg (fun h => h.elim hia hib)]
        decide

private theorem qtwoDB37_dSign_ab {m : ℕ} {a b k : Fin m} (hab : a ≠ b) (hka : k ≠ a)
    (hkb : k ≠ b) : dSign m a b = dSign m a k * dSign m b k := by
  refine (dBasis m).ext' fun i => ?_
  rw [LinearEquiv.mul_apply, dSign_apply, dSign_apply, map_smul, dSign_apply, smul_smul]
  congr 1
  exact (qtwoDB37_scalar_ab hab hka hkb).symm

private lemma qtwoDB37_scalar_pair {m : ℕ} {T : Finset (Fin m)} {i j k : Fin m}
    (hi : i ∈ T) (hj : j ∈ T.erase i) :
    (if k ∈ T then (-1 : ZMod 3) else 1) * (if k = i ∨ k = j then (-1 : ZMod 3) else 1) =
      (if k ∈ (T.erase i).erase j then (-1 : ZMod 3) else 1) := by
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  have hjT : j ∈ T := (Finset.mem_erase.mp hj).2
  have hmem : k ∈ (T.erase i).erase j ↔ k ≠ j ∧ k ≠ i ∧ k ∈ T := by
    simp only [Finset.mem_erase, and_assoc]
  by_cases hkT : k ∈ T
  · by_cases hki : k = i
    · have hnot : k ∉ (T.erase i).erase j := by rw [hmem]; tauto
      rw [if_pos hkT, if_pos (Or.inl hki), if_neg hnot]
      decide
    · by_cases hkj : k = j
      · have hnot : k ∉ (T.erase i).erase j := by rw [hmem]; tauto
        rw [if_pos hkT, if_pos (Or.inr hkj), if_neg hnot]
        decide
      · have hmem' : k ∈ (T.erase i).erase j := by rw [hmem]; tauto
        rw [if_pos hkT, if_neg (fun h => h.elim hki hkj), if_pos hmem']
        decide
  · have hnot : k ∉ (T.erase i).erase j := by rw [hmem]; tauto
    rw [if_neg hkT,
      if_neg (fun h => h.elim (fun hki' => hkT (hki' ▸ hi)) (fun hkj' => hkT (hkj' ▸ hjT))),
      if_neg hnot]
    decide

theorem ggQTwoDUnit_dEven_fix_mem {m : ℕ} (hm : 4 ≤ m) {a b c : Fin m} (hab : a ≠ b)
    (hca : c ≠ a) (hcb : c ≠ b) (H : Subgroup (DVec m ≃ₗ[ZMod 3] DVec m))
    (hperm : ∀ σ : Equiv.Perm (Fin m), σ c = c → dPerm m σ ∈ H)
    (hsa : ∀ k : Fin m, k ≠ a → k ≠ b → k ≠ c → dSign m a k ∈ H)
    (hsb : ∀ k : Fin m, k ≠ a → k ≠ b → k ≠ c → dSign m b k ∈ H)
    {w : DVec m ≃ₗ[ZMod 3] DVec m} (hw : w ∈ dEven m) (hwc : w (Pi.single c 1) = Pi.single c 1) :
    w ∈ H := by
  classical
  have hcard : ({a, b, c} : Finset (Fin m)).card < (Finset.univ : Finset (Fin m)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    have h3 : ({a, b, c} : Finset (Fin m)).card ≤ 3 := by
      have h1 : ({a, b, c} : Finset (Fin m)).card ≤ ({b, c} : Finset (Fin m)).card + 1 :=
        Finset.card_insert_le a ({b, c} : Finset (Fin m))
      have h2 : ({b, c} : Finset (Fin m)).card ≤ ({c} : Finset (Fin m)).card + 1 :=
        Finset.card_insert_le b ({c} : Finset (Fin m))
      have h4 : ({c} : Finset (Fin m)).card ≤ 1 := by simp
      omega
    omega
  obtain ⟨k₀, -, hk₀⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk₀
  obtain ⟨hk₀a, hk₀b, hk₀c⟩ := hk₀
  have hsign_ab : dSign m a b ∈ H := by
    rw [qtwoDB37_dSign_ab hab hk₀a hk₀b]
    exact H.mul_mem (hsa k₀ hk₀a hk₀b hk₀c) (hsb k₀ hk₀a hk₀b hk₀c)
  have hsign_a : ∀ k : Fin m, k ≠ a → k ≠ c → dSign m a k ∈ H := by
    intro k hka hkc
    by_cases hkb : k = b
    · subst hkb; exact hsign_ab
    · exact hsa k hka hkb hkc
  have hsign_ij : ∀ i j : Fin m, i ≠ c → j ≠ c → i ≠ j → dSign m i j ∈ H := by
    intro i j hic hjc hij
    by_cases hia : i = a
    · rw [hia]
      exact hsign_a j (fun h => hij (hia.trans h.symm)) hjc
    · by_cases hja : j = a
      · rw [hja, qtwoDB37_dSign_comm i a]
        exact hsign_a i hia hic
      · rw [qtwoDB37_dSign_mul hia hja hij]
        exact H.mul_mem (hsign_a i hia hic) (hsign_a j hja hjc)
  obtain ⟨σ, T, hσc, hcT, hTeven, hact⟩ := ggQTwoDUnit_dEven_fix_decomp hw hwc
  have hind : ∀ T : Finset (Fin m), c ∉ T → Even T.card →
      ∀ u : DVec m ≃ₗ[ZMod 3] DVec m,
        (∀ j, u (dBasis m j) = (if j ∈ T then (-1 : ZMod 3) else 1) • dBasis m j) → u ∈ H := by
    suffices key : ∀ n : ℕ, ∀ T : Finset (Fin m), T.card = n → c ∉ T → Even T.card →
        ∀ u : DVec m ≃ₗ[ZMod 3] DVec m,
          (∀ j, u (dBasis m j) = (if j ∈ T then (-1 : ZMod 3) else 1) • dBasis m j) → u ∈ H by
      intro T hcT hEven u hu
      exact key T.card T rfl hcT hEven u hu
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro T hTn hcT hEven u hu
      rcases Finset.eq_empty_or_nonempty T with hT | hT
      · subst hT
        have hueq : u = 1 := by
          refine (dBasis m).ext' fun t => ?_
          rw [hu t]; simp
        rw [hueq]; exact H.one_mem
      · obtain ⟨i, hiT⟩ := hT
        rcases hEven with ⟨r, hr⟩
        have hTcard : 2 ≤ T.card := by
          have hpos : 0 < T.card := Finset.card_pos.mpr ⟨i, hiT⟩
          omega
        have hne : (T.erase i).Nonempty := by
          rw [Finset.nonempty_iff_ne_empty]
          intro hempty
          have hcard0 : (T.erase i).card = 0 := by rw [hempty]; simp
          rw [Finset.card_erase_of_mem hiT] at hcard0
          omega
        obtain ⟨j, hjE⟩ := hne
        have hcT' : c ∉ (T.erase i).erase j := fun h =>
          hcT (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))
        have hEven' : Even ((T.erase i).erase j).card := by
          have h1 : ((T.erase i).erase j).card = (T.erase i).card - 1 :=
            Finset.card_erase_of_mem hjE
          have h2 : (T.erase i).card = T.card - 1 := Finset.card_erase_of_mem hiT
          rw [h1, h2]
          exact ⟨r - 1, by omega⟩
        have hlt : ((T.erase i).erase j).card < n := by
          rw [← hTn]
          have h1 : ((T.erase i).erase j).card = (T.erase i).card - 1 :=
            Finset.card_erase_of_mem hjE
          have h2 : (T.erase i).card = T.card - 1 := Finset.card_erase_of_mem hiT
          rw [h1, h2]
          omega
        have hu' : ∀ t, (dSign m i j * u) (dBasis m t) =
            (if t ∈ (T.erase i).erase j then (-1 : ZMod 3) else 1) • dBasis m t := by
          intro t
          rw [LinearEquiv.mul_apply, hu t, map_smul, dSign_apply, smul_smul]
          congr 1
          exact qtwoDB37_scalar_pair hiT hjE
        have hmem' : dSign m i j * u ∈ H :=
          ih ((T.erase i).erase j).card hlt ((T.erase i).erase j) rfl hcT' hEven'
            (dSign m i j * u) hu'
        have hic : i ≠ c := fun h => hcT (h ▸ hiT)
        have hjc : j ≠ c := fun h => hcT (h ▸ (Finset.mem_erase.mp hjE).2)
        have hij : i ≠ j := Ne.symm (Finset.mem_erase.mp hjE).1
        have hdij : dSign m i j ∈ H := hsign_ij i j hic hjc hij
        have heq : u = (dSign m i j)⁻¹ * (dSign m i j * u) := by group
        rw [heq]
        exact H.mul_mem (H.inv_mem hdij) hmem'
  let u : DVec m ≃ₗ[ZMod 3] DVec m := w * (dPerm m σ)⁻¹
  have hu : ∀ t, u (dBasis m t) = (if t ∈ T then (-1 : ZMod 3) else 1) • dBasis m t := by
    intro t
    show (w * (dPerm m σ)⁻¹) (dBasis m t) = _
    rw [LinearEquiv.mul_apply, qtwoDB37_dPerm_inv_apply, hact (σ.symm t)]
    simp only [Equiv.apply_symm_apply]
  have huH : u ∈ H := hind T hcT hTeven u hu
  have hw_eq : w = u * dPerm m σ := by
    show w = w * (dPerm m σ)⁻¹ * dPerm m σ
    rw [mul_assoc, inv_mul_cancel, mul_one]
  rw [hw_eq]
  exact H.mul_mem huH (hperm σ hσc)

end CFSG.StandardType.QTwo

end
