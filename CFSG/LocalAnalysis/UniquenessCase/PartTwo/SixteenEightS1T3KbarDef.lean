module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuGL32
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Quasithin.Background.A1cRank
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W] {A L T : Subgroup (MulAut W)}

@[expose] def s1t3KBar (A L : Subgroup (MulAut W)) : Subgroup (MulAut W) :=
  A ⊓ Subgroup.centralizer (L : Set (MulAut W))

theorem s16t3_gl3_transitive_card (K : Subgroup (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)))
    (htrans : ∀ u v : Fin 3 → ZMod 2, u ≠ 0 → v ≠ 0 →
      ∃ k ∈ K, (k : Matrix (Fin 3) (Fin 3) (ZMod 2)).mulVec u = v) :
    Nat.card ↥K = 7 ∨ Nat.card ↥K = 21 ∨ K = ⊤ := by
  have h7dvd : 7 ∣ Nat.card ↥K := by
    have h1ne : (1 : Fin 3 → ZMod 2) ≠ 0 := by
      intro h
      have h0 := congrFun h 0
      norm_num at h0
    haveI : Fintype ↥K := Fintype.ofFinite ↥K
    haveI : Fintype (MulAction.orbit ↥K (1 : Fin 3 → ZMod 2)) :=
      Fintype.ofFinite _
    haveI : Fintype (MulAction.stabilizer ↥K (1 : Fin 3 → ZMod 2)) :=
      Fintype.ofFinite _
    have horbit : MulAction.orbit ↥K (1 : Fin 3 → ZMod 2) = {v | v ≠ 0} := by
      ext v
      constructor
      · rintro ⟨γ, rfl⟩ h0
        apply h1ne
        rw [← inv_smul_smul γ (1 : Fin 3 → ZMod 2)]
        simpa using congrArg (fun w : Fin 3 → ZMod 2 => γ⁻¹ • w) h0
      · intro hv
        obtain ⟨k, hk, hk1⟩ := htrans 1 v h1ne hv
        exact ⟨⟨k, hk⟩, hk1⟩
    have h7 : Nat.card (MulAction.orbit ↥K (1 : Fin 3 → ZMod 2)) = 7 := by
      rw [horbit, Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card']
      rfl
    have hOS := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := ↥K)
      (1 : Fin 3 → ZMod 2)
    have hOS' : Nat.card (MulAction.orbit ↥K (1 : Fin 3 → ZMod 2)) *
        Nat.card (MulAction.stabilizer ↥K (1 : Fin 3 → ZMod 2)) = Nat.card ↥K := by
      simpa only [Nat.card_eq_fintype_card] using hOS
    rw [← hOS', h7]
    exact dvd_mul_right 7 _
  by_cases h2 : 2 ∣ Nat.card ↥K
  · exact Or.inr (Or.inr
      (CFSG.ComponentClassification.GMS78.eq_top_of_two_dvd_of_seven_dvd_GL32 h2 h7dvd))
  · have hdvd168 : Nat.card ↥K ∣ 168 :=
      CFSG.ComponentClassification.GHarris.card_GL32_gh ▸ Subgroup.card_subgroup_dvd_card K
    have hcard : Nat.card ↥K = 7 ∨ Nat.card ↥K = 21 := by
      obtain ⟨m, hm⟩ := h7dvd
      have hm24 : m ∣ 24 := by
        have h : 7 * m ∣ 7 * 24 := by
          have h' := hdvd168
          rw [hm] at h'
          norm_num at h' ⊢
          exact h'
        exact (Nat.mul_dvd_mul_iff_left (by norm_num : (0 : ℕ) < 7)).mp h
      have hm2 : ¬ 2 ∣ m := fun h2m => h2 (by
        rw [hm]
        exact Dvd.dvd.mul_left h2m 7)
      have hmpos : 0 < m := Nat.pos_of_dvd_of_pos hm24 (by norm_num)
      have hmle : m ≤ 24 := Nat.le_of_dvd (by norm_num) hm24
      have hodd : Odd m := by
        rcases Nat.even_or_odd m with he | ho
        · exact absurd he.two_dvd hm2
        · exact ho
      have hm13 : m = 1 ∨ m = 3 := by
        have hmem : m ∈ (24).divisors := Nat.mem_divisors.mpr ⟨hm24, by norm_num⟩
        have hmem' : m ∈ (24).divisors.filter Odd := Finset.mem_filter.mpr ⟨hmem, hodd⟩
        have hlist : (24).divisors.filter Odd = {1, 3} := by decide
        rw [hlist] at hmem'
        simpa using hmem'
      rcases hm13 with h | h
      · simp [hm, h]
      · simp [hm, h]
    rcases hcard with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

theorem s16t3_gl3_isSimpleGroup : IsSimpleGroup (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :=
  CFSG.ComponentClassification.GHarris.isSimpleGroup_GL32_gh

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
