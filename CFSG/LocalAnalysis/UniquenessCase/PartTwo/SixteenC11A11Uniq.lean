module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11A11Order

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Equiv

private lemma s16c11a11_uniq_mem_stab_iff {σ : Perm (Fin 11)} {p : Fin 11} :
    σ ∈ MulAction.stabilizer (Perm (Fin 11)) p ↔ σ p = p := by
  rw [MulAction.mem_stabilizer_iff, Perm.smul_def]

private lemma s16c11a11_uniq_mem_low_iff {g : Perm (Fin 11)} :
    g ∈ s16c11A11Low ↔ g 8 = 8 ∧ g 9 = 9 ∧ g 10 = 10 := by
  simp only [s16c11A11Low, Subgroup.mem_inf, s16c11a11_uniq_mem_stab_iff]
  tauto

private lemma s16c11a11_uniq_mem_set3 {x : Fin 11} :
    x ∈ s16c11A11Set3 ↔ x = 8 ∨ x = 9 ∨ x = 10 := by
  simp [s16c11A11Set3]

private lemma s16c11a11_uniq_ge8_mem3 {x : Fin 11} (hx : ¬ (x : ℕ) < 8) :
    x ∈ s16c11A11Set3 := by
  rw [s16c11a11_uniq_mem_set3]
  revert hx
  revert x
  decide

private lemma s16c11a11_uniq_pres_apply_mem3 {g : Perm (Fin 11)} (hg : g ∈ s16c11A11Pres)
    {p : Fin 11} (hp : p ∈ s16c11A11Set3) : g p ∈ s16c11A11Set3 := by
  have hp' : ¬ (p : ℕ) < 8 := by
    rw [s16c11a11_uniq_mem_set3] at hp
    rcases hp with rfl | rfl | rfl <;> decide
  exact s16c11a11_uniq_ge8_mem3 fun h => hp' ((s16c11A11_mem_pres_iff.1 hg p).1 h)

private lemma s16c11a11_uniq_eight_mem3 : (8 : Fin 11) ∈ s16c11A11Set3 := by
  rw [s16c11a11_uniq_mem_set3]
  exact Or.inl rfl

private lemma s16c11a11_uniq_nine_mem3 : (9 : Fin 11) ∈ s16c11A11Set3 := by
  rw [s16c11a11_uniq_mem_set3]
  exact Or.inr (Or.inl rfl)

private lemma s16c11a11_uniq_ten_mem3 : (10 : Fin 11) ∈ s16c11A11Set3 := by
  rw [s16c11a11_uniq_mem_set3]
  exact Or.inr (Or.inr rfl)

private lemma s16c11a11_uniq_u_apply :
    s16c11A11u 8 = 9 ∧ s16c11A11u 9 = 8 ∧ s16c11A11u 10 = 10 := by
  decide

private lemma s16c11a11_uniq_orbit_eight_nine {X : Subgroup (Perm (Fin 11))}
    (hXP : X ≤ s16c11A11Pres) (hT : s16c11A11T ≤ X)
    (hmov : ∃ g ∈ X, g 10 ≠ 10) :
    (∃ h ∈ X, h 10 = 8) ∧ (∃ h ∈ X, h 10 = 9) := by
  obtain ⟨g, hgX, hg10⟩ := hmov
  have hmem : g 10 ∈ s16c11A11Set3 :=
    s16c11a11_uniq_pres_apply_mem3 (hXP hgX) s16c11a11_uniq_ten_mem3
  rw [s16c11a11_uniq_mem_set3] at hmem
  have huX : s16c11A11u ∈ X := hT s16c11A11_u_mem_T
  rcases hmem with h8 | h9 | h10
  · refine ⟨⟨g, hgX, h8⟩, ⟨s16c11A11u * g, X.mul_mem huX hgX, ?_⟩⟩
    rw [Equiv.Perm.mul_apply, h8]
    exact s16c11a11_uniq_u_apply.1
  · refine ⟨⟨s16c11A11u * g, X.mul_mem huX hgX, ?_⟩, ⟨g, hgX, h9⟩⟩
    rw [Equiv.Perm.mul_apply, h9]
    exact s16c11a11_uniq_u_apply.2.1
  · exact absurd h10 hg10

theorem s16c11_a11_conj_low_mem {g k : Perm (Fin 11)} (hg : g ∈ s16c11A11Pres)
    (hk : k ∈ s16c11A11Low) : g * k * g⁻¹ ∈ s16c11A11Low := by
  rw [s16c11a11_uniq_mem_low_iff]
  have hfix : ∀ p : Fin 11, p ∈ s16c11A11Set3 → k p = p := by
    intro p hp
    rcases s16c11a11_uniq_mem_set3.1 hp with rfl | rfl | rfl
    · exact (s16c11a11_uniq_mem_low_iff.1 hk).1
    · exact (s16c11a11_uniq_mem_low_iff.1 hk).2.1
    · exact (s16c11a11_uniq_mem_low_iff.1 hk).2.2
  have hinv : ∀ p : Fin 11, p ∈ s16c11A11Set3 → g⁻¹ p ∈ s16c11A11Set3 :=
    fun p hp => s16c11a11_uniq_pres_apply_mem3 (s16c11A11Pres.inv_mem hg) hp
  refine ⟨?_, ?_, ?_⟩
  · change g (k (g⁻¹ 8)) = 8
    rw [hfix (g⁻¹ 8) (hinv 8 s16c11a11_uniq_eight_mem3)]
    exact Equiv.apply_symm_apply g 8
  · change g (k (g⁻¹ 9)) = 9
    rw [hfix (g⁻¹ 9) (hinv 9 s16c11a11_uniq_nine_mem3)]
    exact Equiv.apply_symm_apply g 9
  · change g (k (g⁻¹ 10)) = 10
    rw [hfix (g⁻¹ 10) (hinv 10 s16c11a11_uniq_ten_mem3)]
    exact Equiv.apply_symm_apply g 10

theorem s16c11_a11_card_X {X : Subgroup (Perm (Fin 11))} (hT : s16c11A11T ≤ X)
    (h3 : s16c11A11T.relIndex X = 3) : Nat.card ↥X = 384 := by
  have h := Subgroup.relIndex_mul_card (H := s16c11A11T) (K := X)
  rw [show s16c11A11T ⊓ X = s16c11A11T from inf_eq_left.2 hT, s16c11_a11_card_T,
    h3] at h
  omega

theorem s16c11_a11_orbit_ten {X : Subgroup (Perm (Fin 11))} (hXP : X ≤ s16c11A11Pres)
    (hT : s16c11A11T ≤ X) (hmov : ∃ g ∈ X, g 10 ≠ 10) :
    {q : Fin 11 | ∃ h ∈ X, h 10 = q} = {8, 9, 10} := by
  have h89 := s16c11a11_uniq_orbit_eight_nine hXP hT hmov
  ext q
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact s16c11a11_uniq_pres_apply_mem3 (hXP hh) s16c11a11_uniq_ten_mem3
  · intro hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl
    · exact h89.1
    · exact h89.2
    · exact ⟨1, X.one_mem, by simp⟩

theorem s16c11_a11_card_X_inf_Low {X : Subgroup (Perm (Fin 11))} (hXP : X ≤ s16c11A11Pres)
    (hT : s16c11A11T ≤ X) (hmov : ∃ g ∈ X, g 10 ≠ 10) (hcard : Nat.card ↥X = 384) :
    Nat.card ↥(X ⊓ s16c11A11Low) = 64 := by
  have hcard3 : ({8, 9, 10} : Set (Fin 11)).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by decide : (8 : Fin 11) ∉ ({9, 10} : Set (Fin 11))),
      Set.ncard_insert_of_notMem (by decide : (9 : Fin 11) ∉ ({10} : Set (Fin 11))),
      Set.ncard_singleton]
  have hcard2 : ({8, 9} : Set (Fin 11)).ncard = 2 := Set.ncard_pair (by decide)
  have hOS1 := s16c11_a11_card_orbit_mul X 10
  rw [s16c11_a11_orbit_ten hXP hT hmov, hcard3, hcard] at hOS1
  have hX1 : Nat.card ↥(X ⊓ MulAction.stabilizer (Perm (Fin 11)) (10 : Fin 11)) = 128 := by
    omega
  have hOS2 := s16c11_a11_card_orbit_mul
    (X ⊓ MulAction.stabilizer (Perm (Fin 11)) (10 : Fin 11)) 8
  have horbit8 : {q : Fin 11 | ∃ h ∈ X ⊓ MulAction.stabilizer (Perm (Fin 11)) (10 : Fin 11),
      h 8 = q} = {8, 9} := by
    ext q
    constructor
    · rintro ⟨h, hh, rfl⟩
      obtain ⟨hhX, hh10⟩ := Subgroup.mem_inf.1 hh
      have hmem : h 8 ∈ s16c11A11Set3 :=
        s16c11a11_uniq_pres_apply_mem3 (hXP hhX) s16c11a11_uniq_eight_mem3
      rw [s16c11a11_uniq_mem_set3] at hmem
      have h10 : h 10 = 10 := s16c11a11_uniq_mem_stab_iff.1 hh10
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases hmem with h8 | h9 | h8
      · exact Or.inl h8
      · exact Or.inr h9
      · exfalso
        have hh8 : h 8 = h 10 := by rw [h8, h10]
        exact (by decide : (8 : Fin 11) ≠ 10) (h.injective hh8)
    · intro hq
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
      rcases hq with rfl | rfl
      · exact ⟨1, ⟨X.one_mem, s16c11a11_uniq_mem_stab_iff.2 (by simp)⟩, by simp⟩
      · exact ⟨s16c11A11u, ⟨hT s16c11A11_u_mem_T,
          s16c11a11_uniq_mem_stab_iff.2 s16c11a11_uniq_u_apply.2.2⟩,
          s16c11a11_uniq_u_apply.1⟩
  rw [horbit8, hcard2] at hOS2
  have hstab : (X ⊓ MulAction.stabilizer (Perm (Fin 11)) (10 : Fin 11)) ⊓
      MulAction.stabilizer (Perm (Fin 11)) (8 : Fin 11) = X ⊓ s16c11A11Low := by
    apply le_antisymm
    · intro σ hσ
      obtain ⟨⟨hσX, hσ10⟩, hσ8⟩ := Subgroup.mem_inf.1 hσ
      have hσ10' : σ 10 = 10 := s16c11a11_uniq_mem_stab_iff.1 hσ10
      have hσ8' : σ 8 = 8 := s16c11a11_uniq_mem_stab_iff.1 hσ8
      refine Subgroup.mem_inf.2 ⟨hσX, ?_⟩
      rw [s16c11a11_uniq_mem_low_iff]
      refine ⟨hσ8', ?_, hσ10'⟩
      have hmem : σ 9 ∈ s16c11A11Set3 :=
        s16c11a11_uniq_pres_apply_mem3 (hXP hσX) s16c11a11_uniq_nine_mem3
      rw [s16c11a11_uniq_mem_set3] at hmem
      rcases hmem with h9 | h9 | h9
      · exfalso
        have hh9 : σ 9 = σ 8 := by rw [h9, hσ8']
        exact (by decide : (9 : Fin 11) ≠ 8) (σ.injective hh9)
      · exact h9
      · exfalso
        have hh9 : σ 9 = σ 10 := by rw [h9, hσ10']
        exact (by decide : (9 : Fin 11) ≠ 10) (σ.injective hh9)
    · intro σ hσ
      obtain ⟨hσX, hσL⟩ := Subgroup.mem_inf.1 hσ
      have hσL' := s16c11a11_uniq_mem_low_iff.1 hσL
      exact Subgroup.mem_inf.2
        ⟨Subgroup.mem_inf.2 ⟨hσX, s16c11a11_uniq_mem_stab_iff.2 hσL'.2.2⟩,
          s16c11a11_uniq_mem_stab_iff.2 hσL'.1⟩
  have hcard64 : Nat.card ↥((X ⊓ MulAction.stabilizer (Perm (Fin 11)) (10 : Fin 11)) ⊓
      MulAction.stabilizer (Perm (Fin 11)) (8 : Fin 11)) = 64 := by
    rw [hX1] at hOS2
    omega
  rw [← hstab]
  exact hcard64

theorem s16c11_a11_inf_Low_eq_K {X : Subgroup (Perm (Fin 11))} (hXP : X ≤ s16c11A11Pres)
    (hT : s16c11A11T ≤ X) (hmov : ∃ g ∈ X, g 10 ≠ 10) (hcard : Nat.card ↥X = 384) :
    X ⊓ s16c11A11Low = s16c11A11K := by
  have hKX : s16c11A11K ≤ X := s16c11A11_K_le_T.trans hT
  have hKL : s16c11A11K ≤ s16c11A11Low := by
    show s16c11A11Y ⊓ s16c11A11Low ≤ s16c11A11Low
    exact inf_le_right
  have hle : s16c11A11K ≤ X ⊓ s16c11A11Low := le_inf hKX hKL
  have hcardLow := s16c11_a11_card_X_inf_Low hXP hT hmov hcard
  have hcardK := s16c11_a11_card_K
  have hge : Nat.card ↥(X ⊓ s16c11A11Low) ≤ Nat.card ↥s16c11A11K := by
    omega
  exact (Subgroup.eq_of_le_of_card_ge hle hge).symm

theorem s16c11_a11_le_Y {X : Subgroup (Perm (Fin 11))} (hXA : X ≤ alternatingGroup (Fin 11))
    (hXP : X ≤ s16c11A11Pres) (hT : s16c11A11T ≤ X) (hmov : ∃ g ∈ X, g 10 ≠ 10)
    (hcard : Nat.card ↥X = 384) : X ≤ s16c11A11Y := by
  have hLowEq := s16c11_a11_inf_Low_eq_K hXP hT hmov hcard
  intro g hgX
  have hgP : g ∈ s16c11A11Pres := hXP hgX
  have hconj : ∀ k : Perm (Fin 11), k ∈ s16c11A11K → g * k * g⁻¹ ∈ s16c11A11K := by
    intro k hkK
    have hkXL : k ∈ X ⊓ s16c11A11Low := by
      rw [hLowEq]
      exact hkK
    have hkX : k ∈ X := (Subgroup.mem_inf.1 hkXL).1
    have hkLow : k ∈ s16c11A11Low := (Subgroup.mem_inf.1 hkXL).2
    have hconjX : g * k * g⁻¹ ∈ X := X.mul_mem (X.mul_mem hgX hkX) (X.inv_mem hgX)
    have hconjLow : g * k * g⁻¹ ∈ s16c11A11Low := s16c11_a11_conj_low_mem hgP hkLow
    rw [← hLowEq]
    exact Subgroup.mem_inf.2 ⟨hconjX, hconjLow⟩
  have hblk : S16C11A11Blk g :=
    s16c11_a11_blk_of_conj_mem hgP (hconj _ s16c11A11_k1_mem_K)
      (hconj _ s16c11A11_k2_mem_K) (hconj _ s16c11A11_m3_mem_K)
  rw [s16c11A11_mem_Y_iff]
  exact ⟨⟨hgP, hblk⟩, Perm.mem_alternatingGroup.1 (hXA hgX)⟩

theorem s16c11_a11_unique_overgroup {X : Subgroup (Perm (Fin 11))}
    (hXA : X ≤ alternatingGroup (Fin 11)) (hXP : X ≤ s16c11A11Pres) (hT : s16c11A11T ≤ X)
    (h3 : s16c11A11T.relIndex X = 3) (hmov : ∃ g ∈ X, g 10 ≠ 10) : X = s16c11A11Y := by
  have hcard : Nat.card ↥X = 384 := s16c11_a11_card_X hT h3
  have hXY : X ≤ s16c11A11Y := s16c11_a11_le_Y hXA hXP hT hmov hcard
  have hrel := Subgroup.relIndex_mul_relIndex s16c11A11T X s16c11A11Y hT hXY
  rw [h3, s16c11_a11_T_relIndex_Y] at hrel
  refine le_antisymm hXY ?_
  rw [← Subgroup.relIndex_eq_one]
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

