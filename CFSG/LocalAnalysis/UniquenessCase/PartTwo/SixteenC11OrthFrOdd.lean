module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11OrthFrOddB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11OrthFrOddC2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11OrthFrOddC3
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.KGHS3ClassicalMinus

public section

open scoped Matrix Pointwise

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup

def s16c11_fr_isLine (m : ℕ) (L : Finset (S16C11FrVec m)) : Prop :=
  ∃ a b : S16C11FrVec m, a ≠ 0 ∧ b ≠ 0 ∧ a + b ≠ 0 ∧ S16C11FrQ m a = 0 ∧
    S16C11FrQ m b = 0 ∧ S16C11FrQ m (a + b) = 0 ∧ L = {a, b, a + b}

theorem s16c11_fr_P_eq_stabilizer (m : ℕ) :
    s16c11FrP m = MulAction.stabilizer ↥(S16C11FrO m) (s16c11FrLine m) := by
  ext g
  rw [s16c11FrP, MulAction.mem_stabilizer_iff]
  constructor
  · rintro ⟨h1, h2⟩
    apply Finset.coe_injective
    ext x
    rw [Finset.coe_smul_finset, Set.mem_smul_set_iff_inv_smul_mem, Finset.mem_coe]
    constructor
    · intro hx
      have h := h1 (g⁻¹ • x) hx
      have h' : g • (g⁻¹ • x) ∈ s16c11FrLine m := h
      rw [smul_inv_smul] at h'
      exact h'
    · intro hx
      exact h2 x hx
  · intro h
    have hg : g⁻¹ • s16c11FrLine m = s16c11FrLine m := by
      rw [← h, ← mul_smul, inv_mul_cancel, one_smul, h]
    constructor
    · intro w hw
      have hmem : g • w ∈ g • s16c11FrLine m := by
        rw [← Finset.mem_coe, Finset.coe_smul_finset, Set.mem_smul_set_iff_inv_smul_mem]
        simpa using hw
      rwa [h] at hmem
    · intro w hw
      have hmem : g⁻¹ • w ∈ g⁻¹ • s16c11FrLine m := by
        rw [← Finset.mem_coe, Finset.coe_smul_finset, Set.mem_smul_set_iff_inv_smul_mem]
        simpa using hw
      rwa [hg] at hmem

private theorem s16c11_fr_smul_Q (m : ℕ) (g : ↥(S16C11FrO m)) (v : S16C11FrVec m) :
    S16C11FrQ m (g • v) = S16C11FrQ m v :=
  CFSG.ComponentClassification.CatFC.KGHS3.isometryCore_preserves (S16C11FrQ m) g.property v

private theorem s16c11_fr_smul_ne_zero (m : ℕ) (g : ↥(S16C11FrO m)) {v : S16C11FrVec m}
    (hv : v ≠ 0) : g • v ≠ 0 := by
  intro h
  have h' : (g⁻¹ : ↥(S16C11FrO m)) • (g • v) =
      (g⁻¹ : ↥(S16C11FrO m)) • (0 : S16C11FrVec m) := by
    rw [h]
  rw [← mul_smul, inv_mul_cancel, one_smul] at h'
  exact hv (by simpa using h')

theorem s16c11_fr_orbit_subset_isLine {m : ℕ} (hm : m = 3 ∨ m = 4) :
    MulAction.orbit ↥(S16C11FrO m) (s16c11FrLine m) ⊆ {L | s16c11_fr_isLine m L} := by
  rintro L ⟨g, rfl⟩
  have hlin : g • (s16c11FrE m 0 + s16c11FrE m 1) =
      g • s16c11FrE m 0 + g • s16c11FrE m 1 := by
    simp [Matrix.mulVec_add]
  refine ⟨g • s16c11FrE m 0, g • s16c11FrE m 1,
    s16c11_fr_smul_ne_zero m g (s16c11_fr_E_ne_zero hm 0),
    s16c11_fr_smul_ne_zero m g (s16c11_fr_E_ne_zero hm 1), ?_,
    ?_, ?_, ?_, ?_⟩
  · rw [← hlin]
    exact s16c11_fr_smul_ne_zero m g (s16c11_fr_E_add_ne_zero hm)
  · rw [s16c11_fr_smul_Q]
    exact s16c11_fr_Q_E hm 0
  · rw [s16c11_fr_smul_Q]
    exact s16c11_fr_Q_E hm 1
  · rw [← hlin, s16c11_fr_smul_Q, s16c11_fr_Q_E_add hm]
  · dsimp only [s16c11FrLine]
    rw [← Finset.image_smul]
    simp only [Finset.image_insert, Finset.image_singleton, hlin]

private theorem s16c11_fr_isLine_subset_table_aux (m : ℕ) (hm : m = 3 ∨ m = 4)
    (tableCodes : Finset (ℕ × ℕ × ℕ)) (tableSet : Finset (Finset (S16C11FrVec m)))
    (hset : tableSet = tableCodes.image (s16c11_fr_decode m))
    (complete : ∀ i j : Fin (2 ^ (2 * m)), s16c11_fr_validCode m i.1 j.1 →
      s16c11_fr_sort3 i.1 j.1 (i.1 ^^^ j.1) ∈ tableCodes) :
    {L | s16c11_fr_isLine m L} ⊆ (tableSet : Set (Finset (S16C11FrVec m))) := by
  rintro L ⟨a, b, ha, hb, hab, hqa, hqb, hqab, rfl⟩
  have hia : s16c11_fr_ofNat m (s16c11_fr_nat m a) = a := s16c11_fr_ofNat_nat hm a
  have hjb : s16c11_fr_ofNat m (s16c11_fr_nat m b) = b := s16c11_fr_ofNat_nat hm b
  have hi : s16c11_fr_nat m a < 2 ^ (2 * m) := s16c11_fr_nat_lt hm a
  have hj : s16c11_fr_nat m b < 2 ^ (2 * m) := s16c11_fr_nat_lt hm b
  have hvalid : s16c11_fr_validCode m (s16c11_fr_nat m a) (s16c11_fr_nat m b) := by
    unfold s16c11_fr_validCode
    rw [hia, hjb]
    exact ⟨ha, hb, hab, hqa, hqb, hqab⟩
  have hmem : s16c11_fr_sort3 (s16c11_fr_nat m a) (s16c11_fr_nat m b)
      (s16c11_fr_nat m a ^^^ s16c11_fr_nat m b) ∈ tableCodes :=
    complete ⟨_, hi⟩ ⟨_, hj⟩ hvalid
  have hoab : s16c11_fr_ofNat m (s16c11_fr_nat m a ^^^ s16c11_fr_nat m b) = a + b := by
    have h : s16c11_fr_nat m a ^^^ s16c11_fr_nat m b = s16c11_fr_nat m (a + b) := by
      rw [s16c11_fr_nat_add hm]
    rw [h, s16c11_fr_ofNat_nat hm]
  have hdec : s16c11_fr_decode m (s16c11_fr_sort3 (s16c11_fr_nat m a) (s16c11_fr_nat m b)
      (s16c11_fr_nat m a ^^^ s16c11_fr_nat m b)) = {a, b, a + b} := by
    rw [s16c11_fr_decode_sort3, hia, hjb, hoab]
  rw [hset, Finset.mem_coe]
  exact Finset.mem_image.2 ⟨_, hmem, hdec⟩

theorem s16c11_fr_isLine_subset_table3 :
    {L | s16c11_fr_isLine 3 L} ⊆ (s16c11_fr_tableSet3 : Set (Finset (S16C11FrVec 3))) :=
  s16c11_fr_isLine_subset_table_aux 3 (Or.inl rfl) s16c11_fr_tableCodes3 s16c11_fr_tableSet3
    rfl s16c11_fr_complete3

theorem s16c11_fr_isLine_subset_table4 :
    {L | s16c11_fr_isLine 4 L} ⊆ (s16c11_fr_tableSet4 : Set (Finset (S16C11FrVec 4))) :=
  s16c11_fr_isLine_subset_table_aux 4 (Or.inr rfl) s16c11_fr_tableCodes4 s16c11_fr_tableSet4
    rfl s16c11_fr_complete4

theorem s16c11_fr_orbit_ncard3 :
    (MulAction.orbit ↥(S16C11FrO 3) (s16c11FrLine 3)).ncard = 45 := by
  have hsub : MulAction.orbit ↥(S16C11FrO 3) (s16c11FrLine 3) ⊆
      (s16c11_fr_tableSet3 : Set (Finset (S16C11FrVec 3))) :=
    (s16c11_fr_orbit_subset_isLine (Or.inl rfl)).trans s16c11_fr_isLine_subset_table3
  have hle : (MulAction.orbit ↥(S16C11FrO 3) (s16c11FrLine 3)).ncard ≤ 45 := by
    calc (MulAction.orbit ↥(S16C11FrO 3) (s16c11FrLine 3)).ncard
        ≤ (s16c11_fr_tableSet3 : Set (Finset (S16C11FrVec 3))).ncard :=
          Set.ncard_le_ncard hsub
      _ = s16c11_fr_tableSet3.card := Set.ncard_coe_finset _
      _ = 45 := s16c11_fr_tableSet_card3
  have hge : 45 ≤ (MulAction.orbit ↥(S16C11FrO 3) (s16c11FrLine 3)).ncard := by
    have hfin : (MulAction.orbit ↥(S16C11FrO 3) (s16c11FrLine 3)).Finite :=
      (Finset.finite_toSet s16c11_fr_tableSet3).subset hsub
    calc 45 = s16c11_fr_tableSet3.card := s16c11_fr_tableSet_card3.symm
      _ = (s16c11_fr_tableSet3 : Set (Finset (S16C11FrVec 3))).ncard :=
          (Set.ncard_coe_finset _).symm
      _ ≤ (MulAction.orbit ↥(S16C11FrO 3) (s16c11FrLine 3)).ncard :=
          Set.ncard_le_ncard s16c11_fr_tableSet_subset_orbit3 hfin
  exact le_antisymm hle hge

theorem s16c11_fr_orbit_ncard4 :
    (MulAction.orbit ↥(S16C11FrO 4) (s16c11FrLine 4)).ncard = 1071 := by
  have hsub : MulAction.orbit ↥(S16C11FrO 4) (s16c11FrLine 4) ⊆
      (s16c11_fr_tableSet4 : Set (Finset (S16C11FrVec 4))) :=
    (s16c11_fr_orbit_subset_isLine (Or.inr rfl)).trans s16c11_fr_isLine_subset_table4
  have hle : (MulAction.orbit ↥(S16C11FrO 4) (s16c11FrLine 4)).ncard ≤ 1071 := by
    calc (MulAction.orbit ↥(S16C11FrO 4) (s16c11FrLine 4)).ncard
        ≤ (s16c11_fr_tableSet4 : Set (Finset (S16C11FrVec 4))).ncard :=
          Set.ncard_le_ncard hsub
      _ = s16c11_fr_tableSet4.card := Set.ncard_coe_finset _
      _ = 1071 := s16c11_fr_tableSet_card4
  have hge : 1071 ≤ (MulAction.orbit ↥(S16C11FrO 4) (s16c11FrLine 4)).ncard := by
    have hfin : (MulAction.orbit ↥(S16C11FrO 4) (s16c11FrLine 4)).Finite :=
      (Finset.finite_toSet s16c11_fr_tableSet4).subset hsub
    calc 1071 = s16c11_fr_tableSet4.card := s16c11_fr_tableSet_card4.symm
      _ = (s16c11_fr_tableSet4 : Set (Finset (S16C11FrVec 4))).ncard :=
          (Set.ncard_coe_finset _).symm
      _ ≤ (MulAction.orbit ↥(S16C11FrO 4) (s16c11FrLine 4)).ncard :=
          Set.ncard_le_ncard s16c11_fr_tableSet_subset_orbit4 hfin
  exact le_antisymm hle hge

theorem s16c11_fr_P_index_odd {m : ℕ} (hm : m = 3 ∨ m = 4) : ¬ 2 ∣ (s16c11FrP m).index := by
  have hstab := s16c11_fr_P_eq_stabilizer m
  have hidx := MulAction.index_stabilizer (G := ↥(S16C11FrO m)) (x := s16c11FrLine m)
  rw [← hstab] at hidx
  rcases hm with rfl | rfl
  · rw [hidx, s16c11_fr_orbit_ncard3]
    decide
  · rw [hidx, s16c11_fr_orbit_ncard4]
    decide

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
