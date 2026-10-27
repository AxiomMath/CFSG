module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.RankThree.GF2n.Stroth78.Sec4SevenS6

open Equiv Equiv.Perm

private def d8List : List (Perm (Fin 6)) :=
  [1, swap 0 1, swap 2 3, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2,
    swap 0 1 * (swap 0 2 * swap 1 3), swap 0 2 * swap 1 3 * swap 0 1]

private theorem d8List_mul : ∀ x ∈ d8List, ∀ y ∈ d8List, x * y ∈ d8List := by
  decide +kernel

private theorem d8List_inv : ∀ x ∈ d8List, x⁻¹ ∈ d8List := by
  decide +kernel

private theorem d8List_nodup : d8List.Nodup := by decide +kernel

private def d8 : Subgroup (Perm (Fin 6)) where
  carrier := {x | x ∈ d8List}
  mul_mem' := fun hx hy => d8List_mul _ hx _ hy
  one_mem' := by decide +kernel
  inv_mem' := fun hx => d8List_inv _ hx

private theorem card_d8 : Nat.card d8 = 2 ^ 3 := by
  have h : (d8 : Set (Perm (Fin 6))) = ↑d8List.toFinset := by
    ext x
    simp [d8]
  rw [show Nat.card d8 = Nat.card (d8 : Set (Perm (Fin 6))) from rfl, Nat.card_coe_set_eq, h,
    Set.ncard_coe_finset, List.toFinset_card_of_nodup d8List_nodup]
  rfl

private theorem d8_noncomm : swap (0 : Fin 6) 1 * (swap 0 2 * swap 1 3) ≠
    (swap 0 2 * swap 1 3) * swap 0 1 := by decide +kernel

private theorem swap01_mem : swap (0 : Fin 6) 1 ∈ d8 := by
  show swap (0 : Fin 6) 1 ∈ d8List
  decide +kernel

private theorem swap02_mem : swap (0 : Fin 6) 2 * swap 1 3 ∈ d8 := by
  show swap (0 : Fin 6) 2 * swap 1 3 ∈ d8List
  decide +kernel

private theorem card_perm_six : Nat.card (Perm (Fin 6)) = 720 := by
  rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 6), Fintype.card_fin]
  rfl

private theorem le_four_of_pow_dvd (m : ℕ) (hm : 2 ^ m ∣ 720) : m ≤ 4 := by
  by_contra hm5
  push Not at hm5
  have h32 : 2 ^ 5 ∣ 2 ^ m := Nat.pow_dvd_pow 2 hm5
  have := h32.trans hm
  omega

theorem card_le_eight_of_elemAbelian (L : Subgroup (Perm (Fin 6)))
    (hsq : ∀ x ∈ L, x * x = 1) (hcomm : ∀ x ∈ L, ∀ y ∈ L, x * y = y * x) :
    Nat.card L ≤ 8 := by
  by_contra hlt
  push Not at hlt
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL2 : IsPGroup 2 L := by
    intro x
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simpa [pow_two] using hsq x.1 x.2
  obtain ⟨n, hn⟩ := hL2.exists_card_eq
  obtain ⟨P, hLP⟩ := hL2.exists_le_sylow
  obtain ⟨m, hm⟩ := P.isPGroup'.exists_card_eq
  have hdn : 2 ^ n ∣ 720 := by
    rw [← hn, ← card_perm_six]
    exact L.card_subgroup_dvd_card
  have hdm : 2 ^ m ∣ 720 := by
    rw [← hm, ← card_perm_six]
    exact (P : Subgroup (Perm (Fin 6))).card_subgroup_dvd_card
  have hn4 : n ≤ 4 := le_four_of_pow_dvd n hdn
  have hm4 : m ≤ 4 := le_four_of_pow_dvd m hdm
  have hn4' : n = 4 := by
    by_contra hne
    have h3 : n ≤ 3 := by omega
    have : 2 ^ n ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) h3
    omega
  have hm4' : m = 4 := by
    have hle : Nat.card L ≤ Nat.card P := Subgroup.card_le_of_le hLP
    rw [hn, hm, hn4'] at hle
    have : 2 ^ 4 ≤ 2 ^ m := hle
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp this
    omega
  have hLeq : L = (P : Subgroup (Perm (Fin 6))) := by
    refine Subgroup.eq_of_le_of_card_ge hLP ?_
    rw [hm, hn, hn4', hm4']
  have hPabel : ∀ x ∈ (P : Subgroup (Perm (Fin 6))), ∀ y ∈ (P : Subgroup (Perm (Fin 6))),
      x * y = y * x := by
    rw [← hLeq]
    exact hcomm
  obtain ⟨Q, hdQ⟩ := (IsPGroup.of_card card_d8 : IsPGroup 2 d8).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Perm (Fin 6)) P Q
  have hQabel : ∀ x ∈ (Q : Subgroup (Perm (Fin 6))), ∀ y ∈ (Q : Subgroup (Perm (Fin 6))),
      x * y = y * x := by
    intro x hx y hy
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    rw [MulAut.smul_def, MulAut.smul_def, ← map_mul, ← map_mul, hPabel x' hx' y' hy']
  exact d8_noncomm (hQabel _ (hdQ swap01_mem) _ (hdQ swap02_mem))


theorem exists_swap_separating {e e' : Perm (Fin 6)} (he : e.IsSwap) (he' : e'.IsSwap)
    (hne : e ≠ e') : ∃ x : Perm (Fin 6), x.IsSwap ∧ x * e ≠ e * x ∧ x * e' = e' * x := by
  obtain ⟨a, b, hab, rfl⟩ := he
  obtain ⟨c, d, hcd, rfl⟩ := he'
  have key : ∀ a b c d : Fin 6, a ≠ b → c ≠ d → swap a b ≠ swap c d →
      ∃ p q : Fin 6, p ≠ q ∧ swap p q * swap a b ≠ swap a b * swap p q ∧
        swap p q * swap c d = swap c d * swap p q := by
    decide +kernel
  obtain ⟨p, q, hpq, h1, h2⟩ := key a b c d hab hcd hne
  exact ⟨swap p q, ⟨p, q, hpq, rfl⟩, h1, h2⟩

theorem eq_one_or_eq_swap_of_commute (x : Perm (Fin 6))
    (hx : ∀ i j : Fin 6, 2 ≤ i.val → 2 ≤ j.val → i ≠ j → x * swap i j = swap i j * x)
    (h01 : x * swap 0 1 = swap 0 1 * x) : x = 1 ∨ x = swap 0 1 := by
  revert x
  decide +kernel

private def cyc3 (x y z : Fin 6) : Perm (Fin 6) := swap x z * swap x y

private theorem caseB_aux1 : ∀ a b : Fin 6, a ≠ b → swap a b ≠ swap 0 1 →
    swap a b * swap 0 1 = swap 0 1 * swap a b →
    ∃ c d : Fin 6, c ≠ d ∧ swap c d ≠ swap 0 1 ∧ swap c d ≠ swap a b ∧
      swap c d * swap 0 1 = swap 0 1 * swap c d ∧ swap c d * swap a b = swap a b * swap c d ∧
      (cyc3 0 a c * cyc3 1 b d) * swap 0 1 * (cyc3 0 a c * cyc3 1 b d)⁻¹ = swap a b ∧
      (cyc3 0 a c * cyc3 1 b d) * swap a b * (cyc3 0 a c * cyc3 1 b d)⁻¹ = swap c d ∧
      (cyc3 0 a c * cyc3 1 b d) * swap c d * (cyc3 0 a c * cyc3 1 b d)⁻¹ = swap 0 1 ∧
      (cyc3 0 a c * cyc3 1 b d) ^ 3 = 1 ∧ sign (cyc3 0 a c * cyc3 1 b d) = 1 := by
  decide +kernel

private theorem caseB_aux2 : ∀ q ∈ (Finset.univ.filter fun q : Fin 6 × Fin 6 × Fin 6 × Fin 6 =>
      q.1 ≠ q.2.1 ∧ q.2.2.1 ≠ q.2.2.2 ∧ swap q.1 q.2.1 ≠ swap 0 1 ∧
      swap q.2.2.1 q.2.2.2 ≠ swap 0 1 ∧ swap q.2.2.1 q.2.2.2 ≠ swap q.1 q.2.1 ∧
      swap q.1 q.2.1 * swap 0 1 = swap 0 1 * swap q.1 q.2.1 ∧
      swap q.2.2.1 q.2.2.2 * swap 0 1 = swap 0 1 * swap q.2.2.1 q.2.2.2 ∧
      swap q.2.2.1 q.2.2.2 * swap q.1 q.2.1 = swap q.1 q.2.1 * swap q.2.2.1 q.2.2.2),
    ∀ x : Perm (Fin 6), x * x = 1 → x * swap 0 1 = swap 0 1 * x →
      x * swap q.1 q.2.1 = swap q.1 q.2.1 * x →
      ∃ i j k : Fin 2, x = swap 0 1 ^ (i : ℕ) * swap q.1 q.2.1 ^ (j : ℕ) *
        swap q.2.2.1 q.2.2.2 ^ (k : ℕ) := by
  decide +kernel

private theorem caseA_aux : ∀ x : Perm (Fin 6), x * x = 1 → x * swap 0 1 = swap 0 1 * x →
    (∀ a b : Fin 6, a ≠ b → x = swap a b → x = swap 0 1) →
    (∀ a b : Fin 6, a ≠ b → swap 0 1 * x = swap a b → swap 0 1 * x = swap 0 1) →
    ∃ i j k : Fin 2, x = swap 0 1 ^ (i : ℕ) * (swap 2 3 * swap 4 5) ^ (j : ℕ) *
      (swap 2 4 * swap 3 5) ^ (k : ℕ) := by
  decide +kernel

private theorem caseA_conj : ∀ i j k : Fin 2,
    (swap (2 : Fin 6) 4 * swap 2 3) * (swap (0 : Fin 6) 1 ^ (i : ℕ) *
      (swap (2 : Fin 6) 3 * swap 4 5) ^ (j : ℕ) * (swap (2 : Fin 6) 4 * swap 3 5) ^ (k : ℕ)) *
      (swap (2 : Fin 6) 4 * swap 2 3)⁻¹ ∈
    (Finset.univ.image fun p : Fin 2 × Fin 2 × Fin 2 =>
      swap (0 : Fin 6) 1 ^ (p.1 : ℕ) * (swap (2 : Fin 6) 3 * swap 4 5) ^ (p.2.1 : ℕ) *
        (swap (2 : Fin 6) 4 * swap 3 5) ^ (p.2.2 : ℕ)) := by
  decide +kernel

private theorem caseA_facts :
    sign (swap (2 : Fin 6) 4 * swap 2 3) = 1 ∧ (swap (2 : Fin 6) 4 * swap 2 3) ^ 3 = 1 ∧
    (swap (2 : Fin 6) 4 * swap 2 3) * swap 0 1 = swap 0 1 * (swap 2 4 * swap 2 3) ∧
    (swap (2 : Fin 6) 4 * swap 2 3) * (swap 2 3 * swap 4 5) * (swap 2 4 * swap 2 3)⁻¹ *
      (swap 2 3 * swap 4 5)⁻¹ = swap 2 4 * swap 3 5 ∧
    (swap (2 : Fin 6) 4 * swap 2 3) * (swap 2 4 * swap 3 5) * (swap 2 4 * swap 2 3)⁻¹ *
      (swap 2 4 * swap 3 5)⁻¹ = (swap 2 3 * swap 4 5) * (swap 2 4 * swap 3 5) := by
  decide +kernel

private theorem mem_of_subset_of_card {L : Subgroup (Perm (Fin 6))} {F : Finset (Perm (Fin 6))}
    (hF : F.card ≤ 8) (h8 : 8 ≤ Nat.card L) (hLF : ∀ x ∈ L, x ∈ F) : ∀ x ∈ F, x ∈ L := by
  have hsub : (L : Set (Perm (Fin 6))) ⊆ (F : Set (Perm (Fin 6))) := fun x hx => hLF x hx
  have hL : (L : Set (Perm (Fin 6))).ncard = Nat.card L :=
    (Nat.card_coe_set_eq (L : Set (Perm (Fin 6)))).symm
  have hcard : (F : Set (Perm (Fin 6))).ncard ≤ (L : Set (Perm (Fin 6))).ncard := by
    rw [Set.ncard_coe_finset, hL]
    omega
  have heq := Set.eq_of_subset_of_ncard_le hsub hcard (Set.toFinite _)
  intro x hx
  have : x ∈ (L : Set (Perm (Fin 6))) := heq ▸ Finset.mem_coe.mpr hx
  exact this

theorem exists_threeElement_of_elemAbelian (L : Subgroup (Perm (Fin 6)))
    (hs : swap 0 1 ∈ L) (hsq : ∀ x ∈ L, x * x = 1) (hcomm : ∀ x ∈ L, ∀ y ∈ L, x * y = y * x)
    (h8 : 8 ≤ Nat.card L) :
    ∃ g : Perm (Fin 6), g ∈ alternatingGroup (Fin 6) ∧ g ^ 3 = 1 ∧
      (∀ ℓ ∈ L, g * ℓ * g⁻¹ ∈ L) ∧
      (g * swap 0 1 ≠ swap 0 1 * g ∨
        (g * swap 0 1 = swap 0 1 * g ∧
          ∀ K : Subgroup (Perm (Fin 6)), K ≤ L → swap 0 1 ∈ K →
            (∀ ℓ ∈ L, g * ℓ * g⁻¹ * ℓ⁻¹ ∈ K) → K = L)) := by
  by_cases hB : ∃ t ∈ L, t.IsSwap ∧ t ≠ swap 0 1
  · obtain ⟨t, htL, ⟨a, b, hab, rfl⟩, hts⟩ := hB
    have htc : swap a b * swap 0 1 = swap 0 1 * swap a b := hcomm _ htL _ hs
    obtain ⟨c, d, hcd, hus, hut, huc_s, huc_t, h1, h2, h3, hg3, hgsign⟩ :=
      caseB_aux1 a b hab hts htc
    set g := cyc3 0 a c * cyc3 1 b d with hg
    have hq : (a, b, c, d) ∈ (Finset.univ.filter fun q : Fin 6 × Fin 6 × Fin 6 × Fin 6 =>
      q.1 ≠ q.2.1 ∧ q.2.2.1 ≠ q.2.2.2 ∧ swap q.1 q.2.1 ≠ swap 0 1 ∧
      swap q.2.2.1 q.2.2.2 ≠ swap 0 1 ∧ swap q.2.2.1 q.2.2.2 ≠ swap q.1 q.2.1 ∧
      swap q.1 q.2.1 * swap 0 1 = swap 0 1 * swap q.1 q.2.1 ∧
      swap q.2.2.1 q.2.2.2 * swap 0 1 = swap 0 1 * swap q.2.2.1 q.2.2.2 ∧
      swap q.2.2.1 q.2.2.2 * swap q.1 q.2.1 = swap q.1 q.2.1 * swap q.2.2.1 q.2.2.2) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hab, hcd, hts, hus, hut, htc, huc_s, huc_t⟩
    have hcls := caseB_aux2 _ hq
    let F : Finset (Perm (Fin 6)) := Finset.univ.image fun p : Fin 2 × Fin 2 × Fin 2 =>
      swap 0 1 ^ (p.1 : ℕ) * swap a b ^ (p.2.1 : ℕ) * swap c d ^ (p.2.2 : ℕ)
    have hFcard : F.card ≤ 8 := by
      calc F.card ≤ (Finset.univ : Finset (Fin 2 × Fin 2 × Fin 2)).card :=
            Finset.card_image_le
        _ = 8 := by simp
    have hLF : ∀ x ∈ L, x ∈ F := by
      intro x hx
      obtain ⟨i, j, k, hijk⟩ := hcls x (hsq x hx) (hcomm x hx _ hs) (hcomm x hx _ htL)
      exact Finset.mem_image.mpr ⟨(i, j, k), Finset.mem_univ _, hijk.symm⟩
    have hFL := mem_of_subset_of_card hFcard h8 hLF
    have hu : swap c d ∈ L := hFL _ (Finset.mem_image.mpr ⟨(0, 0, 1), Finset.mem_univ _, by simp⟩)
    refine ⟨g, mem_alternatingGroup.mpr hgsign, hg3, ?_, Or.inl ?_⟩
    · intro ℓ hℓ
      obtain ⟨i, j, k, rfl⟩ := hcls ℓ (hsq ℓ hℓ) (hcomm ℓ hℓ _ hs) (hcomm ℓ hℓ _ htL)
      have e : g * (swap 0 1 ^ (i : ℕ) * swap a b ^ (j : ℕ) * swap c d ^ (k : ℕ)) * g⁻¹ =
          (g * swap 0 1 * g⁻¹) ^ (i : ℕ) * (g * swap a b * g⁻¹) ^ (j : ℕ) *
            (g * swap c d * g⁻¹) ^ (k : ℕ) := by
        rw [conj_pow, conj_pow, conj_pow]
        group
      rw [e, h1, h2, h3]
      exact mul_mem (mul_mem (pow_mem htL _) (pow_mem hu _)) (pow_mem hs _)
    · intro hcm
      apply hts
      have := congrArg (fun y => y * g⁻¹) hcm
      simp only [mul_assoc, mul_inv_cancel, mul_one] at this
      rw [← h1, hcm]
      group
  · push Not at hB
    have hcls := caseA_aux
    let F : Finset (Perm (Fin 6)) := Finset.univ.image fun p : Fin 2 × Fin 2 × Fin 2 =>
      swap 0 1 ^ (p.1 : ℕ) * (swap 2 3 * swap 4 5) ^ (p.2.1 : ℕ) *
        (swap 2 4 * swap 3 5) ^ (p.2.2 : ℕ)
    have hFcard : F.card ≤ 8 := by
      calc F.card ≤ (Finset.univ : Finset (Fin 2 × Fin 2 × Fin 2)).card :=
            Finset.card_image_le
        _ = 8 := by simp
    have hLF : ∀ x ∈ L, x ∈ F := by
      intro x hx
      obtain ⟨i, j, k, hijk⟩ := hcls x (hsq x hx) (hcomm x hx _ hs)
        (fun a b hab hxab => hB x hx ⟨a, b, hab, hxab⟩)
        (fun a b hab hxab => hB _ (mul_mem hs hx) ⟨a, b, hab, hxab⟩)
      exact Finset.mem_image.mpr ⟨(i, j, k), Finset.mem_univ _, hijk.symm⟩
    have hFL := mem_of_subset_of_card hFcard h8 hLF
    have hv₁ : swap 2 3 * swap 4 5 ∈ L :=
      hFL _ (Finset.mem_image.mpr ⟨(0, 1, 0), Finset.mem_univ _, by simp⟩)
    have hv₂ : swap 2 4 * swap 3 5 ∈ L :=
      hFL _ (Finset.mem_image.mpr ⟨(0, 0, 1), Finset.mem_univ _, by simp⟩)
    obtain ⟨hsg, hg3, hgs, hc1, hc2⟩ := caseA_facts
    refine ⟨swap 2 4 * swap 2 3, mem_alternatingGroup.mpr hsg, hg3, ?_, Or.inr ⟨hgs, ?_⟩⟩
    · intro ℓ hℓ
      obtain ⟨i, j, k, rfl⟩ := hcls ℓ (hsq ℓ hℓ) (hcomm ℓ hℓ _ hs)
        (fun a b hab hxab => hB ℓ hℓ ⟨a, b, hab, hxab⟩)
        (fun a b hab hxab => hB _ (mul_mem hs hℓ) ⟨a, b, hab, hxab⟩)
      obtain ⟨⟨i', j', k'⟩, -, he⟩ := Finset.mem_image.mp (caseA_conj i j k)
      rw [← he]
      exact mul_mem (mul_mem (pow_mem hs _) (pow_mem hv₁ _)) (pow_mem hv₂ _)
    · intro K hKL hsK hK
      have h2K : swap 2 4 * swap 3 5 ∈ K := by
        have := hK _ hv₁
        rwa [hc1] at this
      have h3K : (swap 2 3 * swap 4 5) * (swap 2 4 * swap 3 5) ∈ K := by
        have := hK _ hv₂
        rwa [hc2] at this
      have h1K : swap 2 3 * swap 4 5 ∈ K := by
        have := mul_mem h3K (inv_mem h2K)
        simpa [mul_assoc] using this
      refine le_antisymm hKL (fun x hx => ?_)
      obtain ⟨⟨i, j, k⟩, -, hijk⟩ := Finset.mem_image.mp (hLF x hx)
      rw [← hijk]
      exact mul_mem (mul_mem (pow_mem hsK _) (pow_mem h1K _)) (pow_mem h2K _)

end CFSG.RankThree.GF2n.Stroth78.Sec4SevenS6
