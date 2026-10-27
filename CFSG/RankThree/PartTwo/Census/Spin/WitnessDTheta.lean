module

public import CFSG.RankThree.PartTwo.Census.Spin.CarrierDTheta
public import CFSG.RankThree.PartTwo.Census.Spin.WitnessD

public section

namespace CFSG.RankThree.PartTwo.Census.Spin.CarrierD

open TauCeti TauCeti.TypeDSpinCarrier Cliff RootData

section Generic

variable {n : ℕ} {hn : 4 ≤ n} {K : Type} [Field K] {σ : K →+* K}
  {F : (rootData n hn K).G →* (rootData n hn K).G}

theorem epsW_theta_zero : epsW n 0 ⟨0, by omega⟩ + epsW n 1 ⟨0, by omega⟩ = 0 := by
  simp only [epsW]
  split_ifs <;> omega

theorem D_zero_one : CartanMatrix.D n ⟨0, by omega⟩ ⟨1, by omega⟩ = -1 := by
  simp only [D_apply']
  split_ifs <;> (try simp only [false_and, true_and, not_false_eq_true] at *) <;> omega

theorem hasWitness_theta_gen (hR : (rootData n hn K).RootsInCommutator σ F) (h2 : (2 : K) ≠ 0)
    {p f : ℕ} [CharP K p] (hcard : Nat.card (RootData.fixedField σ) = p ^ f) {κ : Type}
    [Fintype κ] [DecidableEq κ] (J : κ → Fin n) (hJ : ∀ a, (J a).val = 0 ∨ 2 ≤ (J a).val)
    (horth : ∀ a a', a ≠ a' → CartanMatrix.D n (J a) (J a') = 0)
    (hk : ∀ a, Even (CartanMatrix.D n ⟨0, by omega⟩ (J a))) :
    HasWitness (DerivedCentralQuotient (fixedSubgroup F)) p (f * (Fintype.card κ + 1)) := by
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
  have hEJ : ∀ a, IsIntOp n
      ((polarization n).typeDSimpleRootBivector (polarizationBasis n) (by omega) (J a))
      (rootIntMatrix n hn (.inl (J a))) := fun a => isIntOp_E n hn (J a)
  have hFJ : ∀ a, IsIntOp n
      ((polarization n).typeDSimpleNegativeRootBivector (polarizationBasis n) (by omega) (J a))
      (rootIntMatrix n hn (.inr (J a))) := fun a => isIntOp_F n hn (J a)
  have hcomm0 : ∀ a, Commute (intMap K Xt) ((rootData n hn K).E (J a)) ∧
      Commute (intMap K Xt) ((rootData n hn K).F (J a)) ∧
      Commute (intMap K Yt) ((rootData n hn K).E (J a)) ∧
      Commute (intMap K Yt) ((rootData n hn K).F (J a)) := by
    intro a
    rcases hJ a with h0 | h2'
    · have hJa : J a = z := Fin.ext h0
      have hE0 : (polarization n).typeDSimpleRootBivector (polarizationBasis n) (by omega) z =
          crD n z * anD n o := chainE_eq n (by omega) z (by simp [z]; omega)
      have hF0 : (polarization n).typeDSimpleNegativeRootBivector (polarizationBasis n)
          (by omega) z = crD n o * anD n z := chainF_eq n (by omega) z (by simp [z]; omega)
      have hE := (hEJ a).congr (by rw [hJa, hE0])
      have hF := (hFJ a).congr (by rw [hJa, hF0])
      refine ⟨intMap_commute_of hXt hE ((P_E _).trans (E_P _ hzo).symm),
        intMap_commute_of hXt hF ((P_F _).trans (F_P _ hzo).symm),
        intMap_commute_of hYt hE ((N_E _ hzo).trans (E_N _).symm),
        intMap_commute_of hYt hF ((N_F _ hzo).trans (F_N _).symm)⟩
    · obtain ⟨c1, c2, -, -⟩ := commute_simple_of_two_le hn (J a) h2' z o (by simp [z])
        (by simp [o])
      obtain ⟨-, -, c3, c4⟩ := commute_simple_of_two_le hn (J a) h2' o z (by simp [o])
        (by simp [z])
      exact ⟨intMap_commute_of hXt (hEJ a) c1.eq, intMap_commute_of hXt (hFJ a) c2.eq,
        intMap_commute_of hYt (hEJ a) c3.eq, intMap_commute_of hYt (hFJ a) c4.eq⟩
  have hJinj : Function.Injective J := fun a a' h => by
    by_contra hne
    have := horth a a' hne
    rw [h, CartanMatrix.D_diag] at this
    exact absurd this (by norm_num)
  have hm1 : ((-1 : Kˣ) : K) ∈ RootData.fixedField σ := by
    rw [Units.val_neg, Units.val_one]
    exact (RootData.fixedField σ).neg_mem (RootData.fixedField σ).one_mem
  have htD : (rootData n hn K).torus (Pi.mulSingle z (-1)) ∈
      ⁅fixedSubgroup F, fixedSubgroup F⁆ := by
    refine torus_mem_commutator_of _ hR fun j => ?_
    by_cases hj : j = z
    · subst hj
      rw [Pi.mulSingle_eq_same]
      exact hm1
    · rw [Pi.mulSingle_eq_of_ne hj, Units.val_one]
      exact (RootData.fixedField σ).one_mem
  have hneg1 : (-1 : Kˣ) ≠ 1 := fun h => h2 (by
    have h3 := congrArg (fun v : Kˣ => (v : K)) h
    simp only [Units.val_neg, Units.val_one] at h3
    rw [← one_add_one_eq_two]
    nth_rewrite 1 [← h3]
    exact neg_add_cancel 1)
  have hprod : ∀ v : Fin n → ℤ,
      (∏ j, (Pi.mulSingle z (-1 : Kˣ)) j ^ v j) = (-1 : Kˣ) ^ v z :=
    fun v => by
      rw [Finset.prod_eq_single z (fun j _ hj => by rw [Pi.mulSingle_eq_of_ne hj, one_zpow])
        (fun h => absurd (Finset.mem_univ _) h), Pi.mulSingle_eq_same]
  have h := (rootData n hn K).rootOp_witness
    (X := Sum.elim (fun a => (rootData n hn K).E (J a)) (fun _ : Unit => intMap K Xt))
    (Y := Sum.elim (fun a => (rootData n hn K).F (J a)) (fun _ : Unit => intMap K Yt))
    (w := Sum.elim (fun a j => (rootData n hn K).CM j (J a))
      (fun _ j => epsW n 0 j + epsW n 1 j))
    (wY := Sum.elim (fun a j => -(rootData n hn K).CM j (J a))
      (fun _ j => -(epsW n 0 j + epsW n 1 j)))
    hcard (fun c => ?_) (fun c => ?_) (fun c => ?_) (fun c => ?_) (fun c c' hcc => ?_)
    (fun c c' hcc => ?_) (Pi.mulSingle z (-1)) ?_ htD (fun c => ?_) o ?_
    (hDx o 1 (RootData.fixedField σ).one_mem)
  · rwa [Fintype.card_sum, Fintype.card_unit] at h
  · rcases c with a | _
    · exact rootOp_E (R := rootData n hn K) (J a) (hDx _)
    · exact hXtR
  · rcases c with a | _
    · exact rootOp_F (R := rootData n hn K) (J a) (hDy _)
    · exact hYtR
  · rcases c with a | _
    · exact (rootData n hn K).sqZero (J a)
    · exact theta_sqZeroPair hn hXt hYt hXtR.sq hYtR.sq
  · rcases c with a | _
    · exact (rootData n hn K).E_ne_zero (J a)
    · exact theta_ne_zero hn hXt
  · rcases c with a | _ <;> rcases c' with a' | _
    · exact (rootData n hn K).commute_EE _ _
        (horth a a' fun h => hcc (congrArg Sum.inl h))
    · exact (hcomm0 a).1.symm
    · exact (hcomm0 a').1
    · exact absurd rfl hcc
  · rcases c with a | _ <;> rcases c' with a' | _
    · exact (rootData n hn K).commute_EF _ _
        fun h => hcc (congrArg Sum.inl (hJinj h).symm)
    · exact (hcomm0 a).2.1
    · exact (hcomm0 a').2.2.1.symm
    · exact absurd rfl hcc
  · rw [← Pi.mulSingle_pow, neg_one_sq, Pi.mulSingle_one]
  · rcases c with a | _
    · simp only [Sum.elim_inl]
      rw [hprod, rootData_CM, (hk a).neg_one_zpow]
    · simp only [Sum.elim_inr]
      rw [hprod, epsW_theta_zero (hn := hn), zpow_zero]
  · rw [hprod, rootData_CM, D_zero_one (hn := hn), zpow_neg_one, inv_neg_one]
    exact hneg1

end Generic

variable (d : TypeDLieIndex)

theorem hasWitness_theta (hodd : d.1.characteristic ≠ 2) {κ : Type} [Fintype κ]
    [DecidableEq κ] (J : κ → Fin d.1.rank) (hJ : ∀ a, (J a).val = 0 ∨ 2 ≤ (J a).val)
    (horth : ∀ a a', a ≠ a' → CartanMatrix.D d.1.rank (J a) (J a') = 0)
    (hk : ∀ a, Even (CartanMatrix.D d.1.rank
      ⟨0, lt_of_lt_of_le (by norm_num) d.toTypeDDiagramLieIndex.four_le_rank⟩ (J a))) :
    HasWitness d.Group d.1.characteristic (d.1.fieldExponent * (Fintype.card κ + 1)) :=
  hasWitness_theta_gen (hn := d.toTypeDDiagramLieIndex.four_le_rank)
    (rootsInCommutator_odd d hodd) (two_ne_zero_closure d hodd) (card_fixedField_frob d) J hJ
    horth hk

theorem hasWitness_theta_four (hodd : d.1.characteristic ≠ 2) :
    HasWitness d.Group d.1.characteristic (d.1.fieldExponent * 4) := by
  have h4 : 4 ≤ d.1.rank := d.toTypeDDiagramLieIndex.four_le_rank
  have h := hasWitness_theta d hodd
    (![⟨0, by omega⟩, ⟨d.1.rank - 2, by omega⟩, ⟨d.1.rank - 1, by omega⟩] : Fin 3 → Fin d.1.rank)
    (fun a => by fin_cases a <;> simp <;> omega)
    (fun a a' h => by
      fin_cases a <;> fin_cases a' <;> simp at h ⊢ <;> rw [D_apply'] <;> simp only <;>
        split_ifs <;> (try simp only [false_and, not_false_eq_true] at *) <;> omega)
    (fun a => by
      rw [Int.even_iff]
      fin_cases a <;> simp <;> rw [D_apply'] <;> simp only <;>
        split_ifs <;> (try simp only [false_and, not_false_eq_true] at *) <;> omega)
  rwa [Fintype.card_fin] at h

end CFSG.RankThree.PartTwo.Census.Spin.CarrierD
