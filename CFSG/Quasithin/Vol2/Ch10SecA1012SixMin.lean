module

public import CFSG.Quasithin.Vol2.Ch10SecA1012SixParMain

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem not_le_normalizer_T0
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Ch10.Hyp10 G T L I)
    (hSL : ∃ (K : Type) (_ : Field K) (_ : Finite K) (n : ℕ), 2 ≤ n ∧ Nat.card K = 2 ^ n ∧
      Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) K)) :
    ¬ fsuL0 T L ≤ Subgroup.normalizer (T0 T L : Set G) := by
  intro hN
  obtain ⟨K, _, _, n, hn, hK, ⟨eL⟩⟩ := hSL
  have hloc := hyp.fsu.maximal.1
  have hsL := isSimpleGroup_of_not_normal h37 h38 hyp.fsu.simple hyp.fsu.nonabelian
    hyp.fsu.qtke hyp.fsu.faithful hyp.not_normal
  have hsyl₁ := isSylowTwoOf_map_of_surjective (isSylowTwoOf_inf hloc)
    (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) (QuotientGroup.mk'_surjective _)
  have hQ : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 2 ^ n * (4 ^ n - 1) := by
    rw [Nat.card_congr eL.toEquiv, card_SL_two_pow hK]
  have hc := card_eq_of_isSylowTwoOf_top hsyl₁ (odd_four_pow_sub_one (by omega)) hQ
  have hnorm : ((T ⊓ L).subgroupOf L).Normal := by
    refine ⟨fun s hs l => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hs ⊢
    have h1 := (Subgroup.mem_normalizer_iff.mp (hN (le_fsuL0 T L l.2)) s).mp
      ⟨hs.1, le_fsuL0 T L hs.2⟩
    exact ⟨h1.1, L.mul_mem (L.mul_mem l.2 hs.2) (L.inv_mem l.2)⟩
  have hnorm' := hnorm.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) (QuotientGroup.mk'_surjective _)
  rcases hsL.eq_bot_or_eq_top_of_normal
      (((T ⊓ L).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) with h | h
  · rw [h, Subgroup.card_bot] at hc
    have : 2 ≤ 2 ^ n := Nat.le_self_pow (by omega) 2
    omega
  · rw [h, Subgroup.card_top, hQ] at hc
    have h16 : 16 ≤ 4 ^ n := by
      calc 16 = 4 ^ 2 := by norm_num
        _ ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h2 : 0 < 2 ^ n := by positivity
    have : 2 ^ n * (4 ^ n - 1) > 2 ^ n * 1 := Nat.mul_lt_mul_of_pos_left (by omega) h2
    omega

theorem minParabolic_L0T
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Ch10.Hyp10 G T L I)
    (hSL : ∃ (K : Type) (_ : Field K) (_ : Finite K) (n : ℕ), 2 ≤ n ∧ Nat.card K = 2 ^ n ∧
      Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) K)) :
    MinParabolic (fsuL0 T L ⊔ T) T
      ((fsuL0 T L ⊔ T) ⊓ Subgroup.normalizer (T0 T L : Set G)) := by
  have hnot := not_le_normalizer_T0 h37 h38 hyp hSL
  have hTN : T ≤ Subgroup.normalizer (T0 T L : Set G) := fun s hs =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hs, le_fsuM T L hs⟩
  refine ⟨isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow le_sup_right, fun h => hnot ?_, ?_⟩
  · intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨h (Subgroup.mem_sup_left hx), fsuL0_le_fsuM T L hx⟩
  · set M0 := (fsuL0 T L ⊔ T) ⊓ Subgroup.normalizer (T0 T L : Set G) with hM0
    have hTM0 : T ≤ M0 := le_inf le_sup_right hTN
    have hM0lt : M0 < fsuL0 T L ⊔ T := by
      refine lt_of_le_of_ne inf_le_left fun h => hnot ?_
      intro x hx
      have : x ∈ M0 := h ▸ (Subgroup.mem_sup_left hx : x ∈ fsuL0 T L ⊔ T)
      exact this.2
    have hkey : ∀ X : Subgroup G, T ≤ X → X ≤ fsuL0 T L ⊔ T → X ≠ fsuL0 T L ⊔ T → X ≤ M0 :=
      fun X hTX hX hne => le_inf hX (le_normalizer_T0_of_ne h37 h38 hyp hSL hTX hX hne)
    ext N
    constructor
    · rintro ⟨⟨hNlt, hNmax⟩, hTN'⟩
      have hNM0 := hkey N hTN' hNlt.le hNlt.ne
      by_contra hne
      exact hM0lt.ne (hNmax M0 (lt_of_le_of_ne hNM0 hne) hM0lt.le)
    · rintro rfl
      refine ⟨⟨hM0lt, fun K hK hKH => ?_⟩, hTM0⟩
      by_contra hne
      exact lt_irrefl _ (lt_of_lt_of_le hK (hkey K (hTM0.trans hK.le) hKH hne))

end CFSG.Quasithin.Vol2.Ch10.SecA
