
module

public import CFSG.RankThree.Native.Fi22UActionBase

public import CFSG.RankThree.Native.Fi22UCheck
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPairOrbits
public import CFSG.ClassicalGroups.Unitary.Simple

public noncomputable section

namespace CFSG.RankThree.Native.Fi22U

open CFSG.Monster.B.Fischer CFSG.Fischer CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank CFSG.LinearGroups Matrix
open scoped Pointwise

theorem fi22U_chainOK :
    rawChainOK 693 ((fi22OuterStrong693 2).extract 0 fi22OuterUnitaryGenCount)
      (fi22OuterStrong693 2) #[0, 1, 3, 9, 45]
      (fi22WordsArr fi22OuterUnitaryGenCount 49 fi22OuterUnitaryDerivations) 4 = true :=
  fi22U_check.1

theorem fi22U_orbitSizes :
    rawOrbitSizes 693 (fi22OuterStrong693 2) #[0, 1, 3, 9, 45] = [693, 512, 120, 36, 6] :=
  fi22U_check.2.1

theorem fi22U_points : ∀ k < 693, fi22UnitaryPoint k ≠ 0 ∧
    fi22Herm (fi22UnitaryPoint k) (fi22UnitaryPoint k) = 0 ∧
    fi22Normalize (fi22UnitaryPoint k) = fi22UnitaryPoint k :=
  fi22U_check.2.2.1

theorem fi22U_lex :
    ∀ j < 693, ∀ k < 693, j < k → fi22LexLt (fi22UnitaryPoint j) (fi22UnitaryPoint k) :=
  fi22U_check.2.2.2.1

theorem fi22U_card_normIso : (Finset.univ.filter fun v : Fin 6 → F4 =>
    v ≠ 0 ∧ fi22Herm v v = 0 ∧ fi22Normalize v = v).card = 693 :=
  fi22U_check.2.2.2.2.1

theorem fi22U_normalize_normalize (v : Fin 6 → F4) :
    fi22Normalize (fi22Normalize v) = fi22Normalize v :=
  fi22U_check.2.2.2.2.2.1 v

theorem fi22U_normalize_smul (c : F4) (v : Fin 6 → F4) (hc : c ≠ 0) :
    fi22Normalize (c • v) = fi22Normalize v :=
  fi22U_check.2.2.2.2.2.2.1 c v hc

theorem fi22U_V_iso :
    ∀ k < 46, fi22Herm (fi22TransvectionVector k) (fi22TransvectionVector k) = 0 :=
  fi22U_check.2.2.2.2.2.2.2.1

theorem fi22U_seeds : ∀ k < 46, ∀ j < 693, fi22UnitaryPoint ((fi22OuterArr693 (15 + k))[j]!) =
    fi22Normalize (fi22Tv (fi22TransvectionVector k) (fi22UnitaryPoint j)) :=
  fi22U_check.2.2.2.2.2.2.2.2.1

theorem fi22U_noncomm : eqA 693 (compA 693 (fi22OuterArr693 15) (fi22OuterArr693 16))
    (compA 693 (fi22OuterArr693 16) (fi22OuterArr693 15)) = false :=
  fi22U_check.2.2.2.2.2.2.2.2.2

theorem fi22B_ne_zero (k : Fin 693) : fi22UnitaryPoint k ≠ 0 := (fi22U_points k k.2).1

theorem fi22B_iso (k : Fin 693) : fi22Herm (fi22UnitaryPoint k) (fi22UnitaryPoint k) = 0 :=
  (fi22U_points k k.2).2.1

theorem fi22B_norm (k : Fin 693) : fi22Normalize (fi22UnitaryPoint k) = fi22UnitaryPoint k :=
  (fi22U_points k k.2).2.2

theorem fi22B_injective : Function.Injective fun k : Fin 693 => fi22UnitaryPoint k := by
  intro j k hjk
  simp only at hjk
  by_contra hne
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
  · have := fi22U_lex j j.2 k k.2 h
    rw [hjk] at this
    exact fi22LexLt_irrefl _ this
  · have := fi22U_lex k k.2 j j.2 h
    rw [hjk] at this
    exact fi22LexLt_irrefl _ this

theorem image_fi22B : Finset.univ.image (fun k : Fin 693 => fi22UnitaryPoint k) = fi22NormIso := by
  apply Finset.eq_of_subset_of_card_le
  · intro v hv
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fi22B_ne_zero k, fi22B_iso k, fi22B_norm k⟩
  · rw [Finset.card_image_of_injective _ fi22B_injective, Finset.card_univ, Fintype.card_fin]
    exact fi22U_card_normIso.le

theorem exists_fi22B_eq {v : Fin 6 → F4} (hv : v ≠ 0) (hiso : fi22Herm v v = 0) :
    ∃ k : Fin 693, fi22UnitaryPoint k = fi22Normalize v := by
  obtain ⟨c, hc, he⟩ := fi22Normalize_eq_smul hv
  have hmem : fi22Normalize v ∈ fi22NormIso := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, ?_, fi22U_normalize_normalize v⟩
    · rw [he]
      exact smul_ne_zero hc hv
    · rw [he, fi22Herm_smul, hiso, mul_zero]
  rw [← image_fi22B] at hmem
  obtain ⟨k, -, hk⟩ := Finset.mem_image.1 hmem
  exact ⟨k, hk⟩

theorem span_fi22B_mem (k : Fin 693) :
    Submodule.span F4 {fi22UnitaryPoint k} ∈ isotropicLines fi22U_fieldData 6 :=
  span_singleton_mem_isotropicLines fi22U_fieldData (fi22B_ne_zero k)
    (by rw [stdHermForm_eq_fi22Herm]; exact fi22B_iso k)

@[expose] def fi22LineOf (k : Fin 693) : isotropicLines fi22U_fieldData 6 := ⟨_, span_fi22B_mem k⟩

theorem fi22LineOf_injective : Function.Injective fi22LineOf := by
  intro j k hjk
  have hspan : Submodule.span F4 {fi22UnitaryPoint j} = Submodule.span F4 {fi22UnitaryPoint k} :=
    congrArg Subtype.val hjk
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1
    (hspan ▸ Submodule.mem_span_singleton_self (fi22UnitaryPoint j))
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact fi22B_ne_zero j hc.symm
  apply fi22B_injective
  simp only
  rw [← fi22B_norm j, ← hc, fi22U_normalize_smul c _ hc0, fi22B_norm k]

theorem fi22LineOf_surjective : Function.Surjective fi22LineOf := by
  rintro ⟨L, hL⟩
  obtain ⟨a, ha0, ha, rfl⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.exists_eq_span_of_mem_isotropicLines hL
  rw [stdHermForm_eq_fi22Herm] at ha
  obtain ⟨k, hk⟩ := exists_fi22B_eq ha0 ha
  refine ⟨k, Subtype.ext ?_⟩
  change Submodule.span F4 {fi22UnitaryPoint k} = Submodule.span F4 {a}
  rw [hk, span_fi22Normalize ha0]

@[expose] def fi22LineEquiv : Fin 693 ≃ isotropicLines fi22U_fieldData 6 :=
  Equiv.ofBijective fi22LineOf ⟨fi22LineOf_injective, fi22LineOf_surjective⟩

theorem fi22LineEquiv_apply (k : Fin 693) :
    (fi22LineEquiv k : Submodule F4 (Fin 6 → F4)) = Submodule.span F4 {fi22UnitaryPoint k} := rfl

@[expose] def fi22Rho : StatedSU 6 (2 ^ 1) F4 →* Equiv.Perm (Fin 693) :=
  (fi22LineEquiv.symm.permCongrHom).toMonoidHom.comp
    (MulAction.toPermHom (StatedSU 6 (2 ^ 1) F4) (isotropicLines fi22U_fieldData 6))

theorem fi22LineEquiv_fi22Rho (g : StatedSU 6 (2 ^ 1) F4) (k : Fin 693) :
    fi22LineEquiv (fi22Rho g k) = g • fi22LineEquiv k := by
  simp [fi22Rho, Equiv.permCongrHom_coe, Equiv.permCongr_apply]

theorem fi22Rho_spec (g : StatedSU 6 (2 ^ 1) F4) (k : Fin 693) :
    fi22UnitaryPoint (fi22Rho g k) =
      fi22Normalize (((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ fi22UnitaryPoint k) := by
  set w := ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ fi22UnitaryPoint k with hw
  have hw0 : w ≠ 0 := mulVec_ne_zero' _ (fi22B_ne_zero k)
  have hwiso : fi22Herm w w = 0 := by rw [hw, fi22Herm_smul_smul, fi22B_iso]
  obtain ⟨m, hm⟩ := exists_fi22B_eq hw0 hwiso
  have : fi22Rho g k = m := by
    apply fi22LineEquiv.injective
    apply Subtype.ext
    rw [fi22LineEquiv_fi22Rho, SubMulAction.val_smul, fi22LineEquiv_apply, fi22LineEquiv_apply,
      smul_span, hm, span_fi22Normalize hw0]
  rw [this, hm]

theorem fi22Rho_eq_iff (g : StatedSU 6 (2 ^ 1) F4) (k m : Fin 693) :
    fi22Rho g k = m ↔ fi22UnitaryPoint m =
      fi22Normalize (((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ fi22UnitaryPoint k) := by
  rw [← fi22Rho_spec]
  exact ⟨fun h => by rw [h], fun h => (fi22B_injective h).symm⟩

theorem ker_fi22Rho :
    fi22Rho.ker = (StatedScalars (Fin 6) F4).subgroupOf (StatedSU 6 (2 ^ 1) F4) := by
  refine (MonoidHom.ker_mulEquiv_comp
    (MulAction.toPermHom (StatedSU 6 (2 ^ 1) F4) (isotropicLines fi22U_fieldData 6))
    fi22LineEquiv.symm.permCongrHom).trans ?_
  rw [unitary_isotropic_kernel fi22U_fieldData (by norm_num),
    unitaryScalars_eq fi22U_fieldData (by norm_num)]

theorem fi22Rho_eq_seed {k : ℕ} (hk : k < 46) {g : StatedSU 6 (2 ^ 1) F4}
    (hg : ∀ x, ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) *ᵥ x =
      fi22Tv (fi22TransvectionVector k) x) :
    fi22Rho g = fi22OuterPerm693 (15 + k) := by
  ext j
  have hrep := rep_fi22OuterPerm693 (L := 15 + k) (by omega)
  have hj := hrep j
  have hlt : (fi22OuterArr693 (15 + k))[(j : ℕ)]! < 693 := hj ▸ (fi22OuterPerm693 (15 + k) j).2
  have key : fi22Rho g j = ⟨(fi22OuterArr693 (15 + k))[(j : ℕ)]!, hlt⟩ := by
    rw [fi22Rho_eq_iff, hg]
    exact fi22U_seeds k hk j j.2
  rw [key]
  exact hj

theorem fi22OuterX_le_range : fi22OuterX ≤ fi22Rho.range := by
  rw [fi22OuterX, RawSchreierDatum.originalSubgroup, Subgroup.closure_le]
  intro g hg
  rw [Set.mem_ofPred_eq, fi22OuterChainUnitary, RawSchreierDatum.mem_ofArrays_original] at hg
  obtain ⟨i, hi, rfl⟩ := hg
  have hi46 : i < 46 := hi
  obtain ⟨t, ht⟩ := exists_mem_fi22S_tv (fi22U_V_iso i hi46)
  refine ⟨t, ?_⟩
  rw [fi22Rho_eq_seed hi46 ht, fi22OuterPerm693, fi22OuterStrong693_two_get (by omega)]

theorem fi22OuterChainUnitary_arrays : ChainArrays fi22OuterChainUnitary
    ((fi22OuterStrong693 2).extract 0 fi22OuterUnitaryGenCount) (fi22OuterStrong693 2)
    #[0, 1, 3, 9, 45] (fi22WordsArr fi22OuterUnitaryGenCount 49 fi22OuterUnitaryDerivations) := by
  have h := chainArrays_ofArrays (n := 693) (hn := by decide) (k := fi22OuterUnitaryGenCount)
    (hk := by rw [fi22OuterStrong693, Array.size_ofFn]; decide)
    (base := fi22FinList 693 (by decide) fi22OuterUnitaryBase) (hb := by decide)
    (W := fi22WordsArr fi22OuterUnitaryGenCount 49 fi22OuterUnitaryDerivations)
    (chainCheckFacts fi22U_chainOK).strong_inv
  have hb : ((fi22FinList 693 (by decide) fi22OuterUnitaryBase).map Fin.val).toArray =
      #[0, 1, 3, 9, 45] := rfl
  rw [hb] at h
  exact h

theorem card_fi22OuterX : Nat.card fi22OuterX = 9196830720 := by
  rw [fi22OuterX, card_originalSubgroup_of_chainOK fi22OuterChainUnitary_arrays (by norm_num)
    fi22U_chainOK, fi22U_orbitSizes]
  rfl

theorem card_range_fi22Rho : Nat.card fi22Rho.range = 9196830720 := by
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange fi22Rho).toEquiv,
    ← card_statedProj_fi22S]
  exact Nat.card_congr (QuotientGroup.quotientMulEquivOfEq ker_fi22Rho).toEquiv

theorem range_fi22Rho : fi22Rho.range = fi22OuterX :=
  (Subgroup.eq_of_le_of_card_ge fi22OuterX_le_range
    (by rw [card_range_fi22Rho, card_fi22OuterX])).symm

@[expose] def fi22UnitaryEquiv : StatedProj (StatedSU 6 (2 ^ 1) F4) ≃* fi22OuterX :=
  (QuotientGroup.quotientMulEquivOfEq ker_fi22Rho.symm).trans
    ((QuotientGroup.quotientKerEquivRange fi22Rho).trans (MulEquiv.subgroupCongr range_fi22Rho))

instance fi22OuterX_isSimpleGroup : IsSimpleGroup fi22OuterX := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU F4 2 1 fi22U_card 6
    (by norm_num) (by decide)
  exact fi22UnitaryEquiv.symm.isSimpleGroup

theorem fi22OuterX_not_comm : ∃ a b : fi22OuterX, a * b ≠ b * a := by
  have hmem : ∀ k < 46, fi22OuterPerm693 (15 + k) ∈ fi22OuterX := by
    intro k hk
    rw [fi22OuterX, RawSchreierDatum.originalSubgroup]
    refine Subgroup.subset_closure ?_
    rw [Set.mem_ofPred_eq, fi22OuterChainUnitary, RawSchreierDatum.mem_ofArrays_original]
    exact ⟨k, hk, by rw [fi22OuterStrong693_two_get (by omega)]; rfl⟩
  refine ⟨⟨_, hmem 0 (by norm_num)⟩, ⟨_, hmem 1 (by norm_num)⟩, fun h => ?_⟩
  have h' := congrArg Subtype.val h
  simp only [Subgroup.coe_mul] at h'
  have := (eqA_iff (rep_compA (rep_fi22OuterPerm693 (L := 15) (by norm_num))
    (rep_fi22OuterPerm693 (L := 16) (by norm_num)))
    (rep_compA (rep_fi22OuterPerm693 (L := 16) (by norm_num))
      (rep_fi22OuterPerm693 (L := 15) (by norm_num)))).2 h'
  rw [fi22U_noncomm] at this
  exact Bool.false_ne_true this

theorem center_fi22OuterX : Subgroup.center fi22OuterX = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center fi22OuterX) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := fi22OuterX_not_comm
    have ha : a ∈ Subgroup.center fi22OuterX := by rw [h]; exact Subgroup.mem_top a
    exact hab ((Subgroup.mem_center_iff.1 ha b).symm)

end CFSG.RankThree.Native.Fi22U
