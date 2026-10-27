module

public import CFSG.RankThree.PartTwo.Census.Spin.WitnessTwo
public import CFSG.RankThree.PartTwo.Census.Spin.CarrierDTheta
public import CFSG.RankThree.PartTwo.Census.Spin.WitnessD

public section

namespace CFSG.RankThree.PartTwo.Census.Spin.CarrierD

open TauCeti TauCeti.TypeDSpinCarrier Cliff RootData

variable (d : TypeDLieIndex)

theorem exists_unit_order_seven (v : ValidLieTypeIndex) (h2 : v.characteristic = 2) :
    ∃ c : v.Closureˣ, ∀ k : ℤ, k ≠ 0 → -4 ≤ k → k ≤ 4 → c ^ k ≠ 1 := by
  have hcard : Nat.card (frobeniusFixedSubfield v.Closure v.characteristic 3) = 8 := by
    rw [card_frobeniusFixedSubfield]
    · rw [h2]
      norm_num
    · norm_num
  have : Finite (frobeniusFixedSubfield v.Closure v.characteristic 3) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  obtain ⟨c, -, hc⟩ := exists_unit_orderOf_eq_card
    (frobeniusFixedSubfield v.Closure v.characteristic 3)
  rw [hcard] at hc
  refine ⟨c, fun k hk h1 h2' hck => ?_⟩
  have hdvd := orderOf_dvd_iff_zpow_eq_one.mpr hck
  rw [hc] at hdvd
  omega

theorem exists_neighbour {n : ℕ} (hn : 4 ≤ n) (i : Fin n) :
    ∃ j : Fin n, i ≠ j ∧ CartanMatrix.D n j i = -1 ∧ CartanMatrix.D n i j = -1 := by
  by_cases h0 : i.val = 0
  · refine ⟨⟨1, by omega⟩, fin_ne (by simp only; omega), ?_, ?_⟩ <;>
    · rw [D_apply']
      simp only
      split_ifs <;> omega
  · by_cases hl : i.val = n - 1
    · refine ⟨⟨n - 3, by omega⟩, fin_ne (by simp only; omega), ?_, ?_⟩ <;>
      · rw [D_apply']
        simp only
        split_ifs <;> omega
    · refine ⟨⟨i.val - 1, by omega⟩, fin_ne (by simp only; omega), ?_, ?_⟩ <;>
      · rw [D_apply']
        simp only
        split_ifs <;> omega

theorem rootsInCommutator_two (h2 : d.1.characteristic = 2) :
    (rootData d.1.rank d.toTypeDDiagramLieIndex.four_le_rank d.1.Closure).RootsInCommutator
      (frob d) d.steinberg := by
  have h4 := d.toTypeDDiagramLieIndex.four_le_rank
  obtain ⟨c, hc⟩ := exists_unit_order_seven d.1 h2
  refine (rootData d.1.rank h4 d.1.Closure).rootsInCommutator_of_neighbour (isFrobenius d) hc
    fun i => ?_
  obtain ⟨j, hij, hji, hij'⟩ := exists_neighbour h4 i
  have hI := intRootData d.1.rank h4
  have key : ∀ {X Y : Matrix (Fin (dimension d.1.rank)) (Fin (dimension d.1.rank)) ℤ},
      X * Y * X = 0 → intMap d.1.Closure X * intMap d.1.Closure Y * intMap d.1.Closure X = 0 :=
    fun h => by rw [← intMap_mul, ← intMap_mul, h, intMap_zero]
  exact ⟨j, hij, hji, key (hI.serre_XX i j hij'), key (hI.serre_XX j i hji),
    key (hI.serre_YY i j hij'), key (hI.serre_YY j i hji)⟩

section Generic

variable {n : ℕ} {hn : 4 ≤ n} {K : Type} [Field K] {σ : K →+* K}
  {F : (rootData n hn K).G →* (rootData n hn K).G}

theorem hasWitness_three_gen (hR : (rootData n hn K).RootsInCommutator σ F)
    (hchar : (2 : K) = 0) (h6 : 6 ≤ n) :
    HasWitness (DerivedCentralQuotient (fixedSubgroup F)) 3 4 := by
  have hDx : ∀ i u, u ∈ RootData.fixedField σ →
      (rootData n hn K).x i u ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆ :=
    fun i u hu => (hR i u hu).1
  have hDy : ∀ i u, u ∈ RootData.fixedField σ →
      (rootData n hn K).y i u ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆ :=
    fun i u hu => (hR i u hu).2
  obtain ⟨Xt, hXt, hXtR⟩ := exists_rootOp_theta (hn := hn) (H := fixedSubgroup F) hDx
  obtain ⟨Yt, hYt, hYtR⟩ := exists_rootOp_thetaY (hn := hn) (H := fixedSubgroup F) hDy
  set z : Fin n := ⟨0, by omega⟩
  set o : Fin n := ⟨1, by omega⟩
  have hzo : z ≠ o := fin_ne (by simp [z, o])
  let J : Fin 4 → Fin n := ![⟨0, by omega⟩, ⟨2, by omega⟩, ⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩]
  have hJv : ∀ a, (J a).val = 0 ∨ 2 ≤ (J a).val := fun a => by
    fin_cases a <;> simp [J] <;> omega
  have hJ : Function.Injective J := fun a b h => by
    have hv := congrArg Fin.val h
    fin_cases a <;> fin_cases b <;> simp [J] at hv ⊢ <;> omega
  have horth : ∀ a b, a ≠ b → (rootData n hn K).CM (J a) (J b) = 0 := fun a b hab => by
    rw [rootData_CM]
    fin_cases a <;> fin_cases b <;> simp [J] at hab ⊢ <;> rw [D_apply'] <;> simp only <;>
      split_ifs <;> (try simp only [false_and, not_false_eq_true] at *) <;> omega
  have hcomm0 : ∀ a, Commute (intMap K Xt) ((rootData n hn K).E (J a)) ∧
      Commute (intMap K Xt) ((rootData n hn K).F (J a)) := by
    intro a
    have hEJ := isIntOp_E n hn (J a)
    have hFJ := isIntOp_F n hn (J a)
    rcases hJv a with h0 | h2'
    · have hJa : J a = z := Fin.ext h0
      have hE0 : (polarization n).typeDSimpleRootBivector (polarizationBasis n) (by omega) z =
          crD n z * anD n o := chainE_eq n (by omega) z (by simp [z]; omega)
      have hF0 : (polarization n).typeDSimpleNegativeRootBivector (polarizationBasis n)
          (by omega) z = crD n o * anD n z := chainF_eq n (by omega) z (by simp [z]; omega)
      have hE := hEJ.congr (by rw [hJa, hE0])
      have hF := hFJ.congr (by rw [hJa, hF0])
      exact ⟨intMap_commute_of hXt hE ((P_E _).trans (E_P _ hzo).symm),
        intMap_commute_of hXt hF ((P_F _).trans (F_P _ hzo).symm)⟩
    · obtain ⟨c1, c2, -, -⟩ := commute_simple_of_two_le hn (J a) h2' z o (by simp [z])
        (by simp [o])
      exact ⟨intMap_commute_of hXt hEJ c1.eq, intMap_commute_of hXt hFJ c2.eq⟩
  have h1F : (1 : K) ∈ RootData.fixedField σ := (RootData.fixedField σ).one_mem
  have h11 : (1 : K) + 1 = 0 := by rw [one_add_one_eq_two]; exact hchar
  have ht2 : hXtR.elt 1 ^ 2 = 1 := by
    rw [pow_two, ← hXtR.elt_add, h11]
    exact hXtR.elt_zero
  have htz : ∃ g ∈ ⁅fixedSubgroup F, fixedSubgroup F⁆, hXtR.elt 1 * g ≠ g * hXtR.elt 1 := by
    refine ⟨hYtR.elt 1, hYtR.elt_mem h1F, fun h => (one_ne_zero : (1 : K) ≠ 0) ?_⟩
    exact (rootData n hn K).eq_zero_of_commute_sqZeroPair
      (theta_sqZeroPair hn hXt hYt hXtR.sq hYtR.sq) (theta_ne_zero hn hXt) (hXtR.mat_elt 1)
      (by rw [hYtR.mat_elt, one_smul]) h
  have h := (rootData n hn K).three_witness hchar J hJ horth (fun a => (hR (J a) 1 h1F).1)
    (fun a => (hR (J a) 1 h1F).2) (hXtR.elt 1) (hXtR.elt_mem h1F) ht2 htz
    (fun a => (rootData n hn K).commute_of_mat (by
      rw [hXtR.mat_elt, mat_x']
      exact commute_one_add_smul (hcomm0 a).1 _ _))
    (fun a => (rootData n hn K).commute_of_mat (by
      rw [hXtR.mat_elt, mat_y']
      exact commute_one_add_smul (hcomm0 a).2 _ _))
  rwa [Fintype.card_fin] at h

end Generic

theorem hasWitness_three (h2 : d.1.characteristic = 2) (h6 : 6 ≤ d.1.rank) :
    HasWitness d.Group 3 4 := by
  have hchar : (2 : d.1.Closure) = 0 := by
    have h := (congrArg (Nat.cast : ℕ → d.1.Closure) h2).symm.trans
      (CharP.cast_eq_zero d.1.Closure d.1.characteristic)
    exact_mod_cast h
  exact hasWitness_three_gen (rootsInCommutator_two d h2) hchar h6

end CFSG.RankThree.PartTwo.Census.Spin.CarrierD
