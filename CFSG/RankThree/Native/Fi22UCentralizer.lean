
module

public import CFSG.RankThree.Native.Fi22UCentralizerBase

public import CFSG.RankThree.Native.Fi22UCentralizerCheck

public noncomputable section

namespace CFSG.RankThree.Native.Fi22U

open CFSG.Monster.B.Fischer CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native CFSG.Assembly.LowTwoRank CFSG.Fischer
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped Pointwise commutatorElement

theorem fi22UM693_chainOK :
    rawChainOK 693 ((fi22OuterStrong693 3).extract 0 fi22OuterM693GenCount)
      (fi22OuterStrong693 3) #[0, 1, 3, 9, 45]
      (fi22WordsArr fi22OuterM693GenCount 15 fi22OuterM693Derivations) 4 = true :=
  fi22UCentralizer_check.1

theorem fi22UM693_orbitSizes :
    rawOrbitSizes 693 (fi22OuterStrong693 3) #[0, 1, 3, 9, 45] = [693, 512, 120, 36, 6] :=
  fi22UCentralizer_check.2.1

theorem fi22UM693_sift : ∀ k < 3, siftA 693 (rawLevels 693 (fi22OuterStrong693 2)
    #[0, 1, 3, 9, 45]) #[0, 1, 3, 9, 45] 0 (fi22OuterArr693 (64 + k)) = true :=
  fi22UCentralizer_check.2.2.1

theorem fi22UMPoints_nodup : fi22OuterMPointsNat.Nodup := fi22UCentralizer_check.2.2.2.1

theorem fi22URestrict_check : ∀ k < 3, ∀ j < 693,
    fi22OuterMPointsNat.getD ((invCand 693 (fi22OuterArr693 0))[
      (fi22OuterArr693 (64 + k))[(fi22OuterArr693 0)[j]!]!]!) 0 =
    (fi22OuterArr3510 (3 + k))[fi22OuterMPointsNat.getD j 0]! :=
  fi22UCentralizer_check.2.2.2.2.1

theorem fi22UZ_fix : ∀ j < 693, (fi22OuterArr3510 1)[fi22OuterMPointsNat.getD j 0]! =
    fi22OuterMPointsNat.getD j 0 :=
  fi22UCentralizer_check.2.2.2.2.2.1

theorem fi22UCentral_sift : ∀ i < 4, siftA 3510 (rawLevels 3510 (fi22OuterStrong3510 3)
    #[0, 1, 2, 6, 4, 3]) #[0, 1, 2, 6, 4, 3] 0 (fi22OuterArr3510 (147 + i)) = true :=
  fi22UCentralizer_check.2.2.2.2.2.2.1

theorem fi22UCentral_word :
    eqA 3510 (compA 3510 (commA 3510 (fi22OuterArr3510 147) (fi22OuterArr3510 148))
      (commA 3510 (fi22OuterArr3510 149) (fi22OuterArr3510 150))) (fi22OuterArr3510 1) = true :=
  fi22UCentralizer_check.2.2.2.2.2.2.2

theorem fi22IPt_injective : Function.Injective fi22IPt := by
  intro i j h
  have h' := congrArg Fin.val h
  have hi : (i : ℕ) < fi22OuterMPointsNat.length := by
    rw [fi22OuterMPointsNat_length]
    exact i.2
  have hj : (j : ℕ) < fi22OuterMPointsNat.length := by
    rw [fi22OuterMPointsNat_length]
    exact j.2
  rw [fi22IPt_val, fi22IPt_val, List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] at h'
  exact Fin.ext ((List.Nodup.getElem_inj_iff fi22UMPoints_nodup).1 h')

@[expose] def fi22IEquiv : Fin 693 ≃ fi22ISet := Equiv.ofInjective fi22IPt fi22IPt_injective

theorem fi22IEquiv_apply (j : Fin 693) : (fi22IEquiv j : Fin 3510) = fi22IPt j := rfl

theorem fi22MGen_apply_fi22IPt {k : ℕ} (hk : k < 3) (j : Fin 693) :
    fi22OuterPerm3510 (3 + k) (fi22IPt j) =
      fi22IPt (fi22OuterCu⁻¹ (fi22OuterPerm693 (64 + k) (fi22OuterCu j))) := by
  apply Fin.ext
  rw [← rep_fi22OuterPerm3510 (L := 3 + k) (by omega) (fi22IPt j), fi22IPt_val, fi22IPt_val,
    ← rep_fi22OuterCu_inv, ← rep_fi22OuterPerm693 (L := 64 + k) (by omega),
    fi22OuterCu_eq, ← rep_fi22OuterPerm693 (L := 0) (by norm_num) j]
  exact (fi22URestrict_check k hk j j.2).symm

theorem fi22OuterM_le_stabilizer :
    fi22OuterM ≤ MulAction.stabilizer (Equiv.Perm (Fin 3510)) fi22ISet := by
  rw [fi22OuterM, RawSchreierDatum.originalSubgroup, Subgroup.closure_le]
  intro g hg
  rw [Set.mem_ofPred_eq, fi22OuterChainM, RawSchreierDatum.mem_ofArrays_original] at hg
  obtain ⟨i, hi, rfl⟩ := hg
  have hi3 : i < 3 := hi
  rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, fi22ISet, Set.smul_set_range,
    fi22OuterStrong3510_three_get (by omega)]
  have h : (fun j => fi22OuterPerm3510 (3 + i) • fi22IPt j) =
      fi22IPt ∘ (fi22OuterCu⁻¹ * fi22OuterPerm693 (64 + i) * fi22OuterCu) := by
    funext j
    rw [Equiv.Perm.smul_def, fi22MGen_apply_fi22IPt hi3 j, Function.comp_apply,
      Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  rw [← fi22OuterPerm3510_def, h, EquivLike.range_comp]

@[expose] def fi22Restrict :
    MulAction.stabilizer (Equiv.Perm (Fin 3510)) fi22ISet →* Equiv.Perm (Fin 693) :=
  (fi22IEquiv.symm.permCongrHom).toMonoidHom.comp (MulAction.toPermHom _ fi22ISet)

theorem fi22IPt_fi22Restrict (g : MulAction.stabilizer (Equiv.Perm (Fin 3510)) fi22ISet)
    (j : Fin 693) :
    fi22IPt (fi22Restrict g j) = (g : Equiv.Perm (Fin 3510)) (fi22IPt j) := by
  have h : fi22IEquiv (fi22Restrict g j) = g • fi22IEquiv j := by
    simp [fi22Restrict, Equiv.permCongr_apply]
  have h2 := congrArg Subtype.val h
  rw [fi22IEquiv_apply] at h2
  rw [h2]
  rfl

@[expose] def fi22Kappa₀ : fi22OuterM →* Equiv.Perm (Fin 693) :=
  (MulAut.conj fi22OuterCu).toMonoidHom.comp
    (fi22Restrict.comp (Subgroup.inclusion fi22OuterM_le_stabilizer))

theorem fi22Kappa₀_apply (g : fi22OuterM) :
    fi22Kappa₀ g = fi22OuterCu * fi22Restrict (Subgroup.inclusion fi22OuterM_le_stabilizer g) *
      fi22OuterCu⁻¹ := rfl

theorem fi22Kappa₀_gen {i : ℕ} (hi : i < 3) :
    fi22Kappa₀ ⟨fi22OuterPerm3510 (3 + i), mem_fi22OuterM_gen hi⟩ = fi22OuterPerm693 (64 + i) := by
  have hr : fi22Restrict (Subgroup.inclusion fi22OuterM_le_stabilizer
      ⟨fi22OuterPerm3510 (3 + i), mem_fi22OuterM_gen hi⟩) =
      fi22OuterCu⁻¹ * fi22OuterPerm693 (64 + i) * fi22OuterCu := by
    refine Equiv.ext fun j => fi22IPt_injective ?_
    rw [fi22IPt_fi22Restrict, Subgroup.coe_inclusion, Subgroup.coe_mk, Equiv.Perm.mul_apply,
      Equiv.Perm.mul_apply]
    exact fi22MGen_apply_fi22IPt hi j
  rw [fi22Kappa₀_apply, hr]
  group

theorem fi22OuterChainM693_arrays : ChainArrays fi22OuterChainM693
    ((fi22OuterStrong693 3).extract 0 fi22OuterM693GenCount) (fi22OuterStrong693 3)
    #[0, 1, 3, 9, 45] (fi22WordsArr fi22OuterM693GenCount 15 fi22OuterM693Derivations) := by
  have h := chainArrays_ofArrays (n := 693) (hn := by decide) (k := fi22OuterM693GenCount)
    (hk := by rw [fi22OuterStrong693, Array.size_ofFn]; decide)
    (base := fi22FinList 693 (by decide) fi22OuterM693Base) (hb := by decide)
    (W := fi22WordsArr fi22OuterM693GenCount 15 fi22OuterM693Derivations)
    (chainCheckFacts fi22UM693_chainOK).strong_inv
  have hb : ((fi22FinList 693 (by decide) fi22OuterM693Base).map Fin.val).toArray =
      #[0, 1, 3, 9, 45] := rfl
  rw [hb] at h
  exact h

theorem card_fi22OuterM693 : Nat.card fi22OuterChainM693.originalSubgroup = 9196830720 := by
  rw [card_originalSubgroup_of_chainOK fi22OuterChainM693_arrays (by norm_num)
    fi22UM693_chainOK, fi22UM693_orbitSizes]
  rfl

theorem fi22OuterM693_le_X : fi22OuterChainM693.originalSubgroup ≤ fi22OuterX := by
  rw [RawSchreierDatum.originalSubgroup, Subgroup.closure_le]
  intro g hg
  rw [Set.mem_ofPred_eq, fi22OuterChainM693, RawSchreierDatum.mem_ofArrays_original] at hg
  obtain ⟨i, hi, rfl⟩ := hg
  have hi3 : i < 3 := hi
  rw [fi22OuterStrong693_three_get (by omega)]
  exact (siftA_iff_mem_originalSubgroup fi22OuterChainUnitary_arrays (by norm_num) fi22U_chainOK
    (rep_fi22OuterPerm693 (L := 64 + i) (by omega))).1 (fi22UM693_sift i hi3)

theorem range_fi22Kappa₀ : fi22Kappa₀.range = fi22OuterChainM693.originalSubgroup := by
  apply le_antisymm
  · have htop : (Subgroup.closure ((Subtype.val : fi22OuterM → Equiv.Perm (Fin 3510)) ⁻¹'
        {g | g ∈ fi22OuterChainM.original.toList}) : Subgroup fi22OuterM) = ⊤ :=
      Subgroup.closure_closure_coe_preimage
    rw [MonoidHom.range_eq_map, ← htop, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨g, hg, rfl⟩
    rw [Set.mem_preimage, Set.mem_ofPred_eq, fi22OuterChainM,
      RawSchreierDatum.mem_ofArrays_original] at hg
    obtain ⟨i, hi, hgi⟩ := hg
    have hi3 : i < 3 := hi
    have hg : g = ⟨fi22OuterPerm3510 (3 + i), mem_fi22OuterM_gen hi3⟩ := Subtype.ext (by
      rw [← hgi, fi22OuterStrong3510_three_get (by omega)]
      rfl)
    rw [hg, SetLike.mem_coe, fi22Kappa₀_gen hi3, RawSchreierDatum.originalSubgroup]
    refine Subgroup.subset_closure ?_
    rw [Set.mem_ofPred_eq, fi22OuterChainM693, RawSchreierDatum.mem_ofArrays_original]
    exact ⟨i, hi3, by rw [fi22OuterStrong693_three_get (by omega)]; rfl⟩
  · rw [RawSchreierDatum.originalSubgroup, Subgroup.closure_le]
    intro g hg
    rw [Set.mem_ofPred_eq, fi22OuterChainM693, RawSchreierDatum.mem_ofArrays_original] at hg
    obtain ⟨i, hi, rfl⟩ := hg
    have hi3 : i < 3 := hi
    rw [fi22OuterStrong693_three_get (by omega)]
    exact ⟨_, fi22Kappa₀_gen hi3⟩

theorem range_fi22Kappa₀_eq_X : fi22Kappa₀.range = fi22OuterX := by
  rw [range_fi22Kappa₀]
  exact Subgroup.eq_of_le_of_card_ge fi22OuterM693_le_X
    (by rw [card_fi22OuterX, card_fi22OuterM693])

@[expose] def fi22Kappa : fi22OuterM →* fi22OuterX :=
  fi22Kappa₀.codRestrict fi22OuterX fun g => range_fi22Kappa₀_eq_X ▸ ⟨g, rfl⟩

theorem fi22Kappa_coe (g : fi22OuterM) :
    (fi22Kappa g : Equiv.Perm (Fin 693)) = fi22Kappa₀ g := rfl

theorem fi22Kappa_surjective : Function.Surjective fi22Kappa := by
  rintro ⟨x, hx⟩
  rw [← range_fi22Kappa₀_eq_X] at hx
  obtain ⟨g, rfl⟩ := hx
  exact ⟨g, rfl⟩

theorem ker_fi22Kappa : fi22Kappa.ker = fi22Kappa₀.ker := by
  ext g
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← fi22Kappa_coe]
  exact ⟨fun h => by rw [h]; rfl, fun h => Subtype.ext h⟩

theorem fi22OuterZ_fi22IPt (j : Fin 693) : fi22OuterZ (fi22IPt j) = fi22IPt j := by
  apply Fin.ext
  rw [fi22OuterZ_eq_perm, ← rep_fi22OuterPerm3510 (L := 1) (by norm_num), fi22IPt_val]
  exact fi22UZ_fix j j.2

theorem fi22OuterZM_mem_ker : fi22OuterZM ∈ fi22Kappa.ker := by
  rw [ker_fi22Kappa, MonoidHom.mem_ker, fi22Kappa₀_apply]
  have h : fi22Restrict (Subgroup.inclusion fi22OuterM_le_stabilizer fi22OuterZM) = 1 := by
    refine Equiv.ext fun j => fi22IPt_injective ?_
    rw [fi22IPt_fi22Restrict, Subgroup.coe_inclusion, Equiv.Perm.one_apply, fi22OuterZM,
      Subgroup.coe_mk]
    exact fi22OuterZ_fi22IPt j
  rw [h, mul_one, mul_inv_cancel]

theorem card_ker_fi22Kappa : Nat.card fi22Kappa.ker = 2 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup fi22Kappa.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective fi22Kappa
    fi22Kappa_surjective).toEquiv, card_fi22OuterM, card_fi22OuterX] at h
  omega

theorem ker_fi22Kappa_eq : fi22Kappa.ker = Subgroup.zpowers fi22OuterZM :=
  (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 fi22OuterZM_mem_ker)
    (by rw [card_ker_fi22Kappa, Nat.card_zpowers, orderOf_fi22OuterZM])).symm

theorem center_fi22OuterM : Subgroup.center fi22OuterM = Subgroup.zpowers fi22OuterZM := by
  refine le_antisymm ?_ (Subgroup.zpowers_le.2 fi22OuterZM_mem_center)
  rw [← ker_fi22Kappa_eq]
  intro c hc
  rw [MonoidHom.mem_ker]
  have hcX : fi22Kappa c ∈ Subgroup.center fi22OuterX := by
    rw [Subgroup.mem_center_iff]
    intro x
    obtain ⟨g, rfl⟩ := fi22Kappa_surjective x
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hc g)]
  rw [center_fi22OuterX] at hcX
  exact hcX

theorem fi22OuterPerm3510_central_mem {i : ℕ} (hi : i < 4) :
    fi22OuterPerm3510 (147 + i) ∈ fi22OuterM :=
  (siftA_iff_mem_originalSubgroup fi22OuterChainM_arrays (by norm_num) fi22Local_check.1
    (rep_fi22OuterPerm3510 (L := 147 + i) (by omega))).1 (fi22UCentral_sift i hi)

theorem fi22OuterCentral_eq :
    (fi22OuterPerm3510 148 * fi22OuterPerm3510 147 * (fi22OuterPerm3510 148)⁻¹ *
        (fi22OuterPerm3510 147)⁻¹) *
      (fi22OuterPerm3510 150 * fi22OuterPerm3510 149 * (fi22OuterPerm3510 150)⁻¹ *
        (fi22OuterPerm3510 149)⁻¹) = fi22OuterZ :=
  eq_of_eqA (rep_compA (rep_commA (by norm_num) (by norm_num))
    (rep_commA (by norm_num) (by norm_num))) (rep_fi22OuterPerm3510 (L := 1) (by norm_num))
    fi22UCentral_word

theorem fi22OuterZM_mem_commutator : fi22OuterZM ∈ commutator fi22OuterM := by
  have m0 : fi22OuterPerm3510 147 ∈ fi22OuterM :=
    fi22OuterPerm3510_central_mem (i := 0) (by norm_num)
  have m1 : fi22OuterPerm3510 148 ∈ fi22OuterM :=
    fi22OuterPerm3510_central_mem (i := 1) (by norm_num)
  have m2 : fi22OuterPerm3510 149 ∈ fi22OuterM :=
    fi22OuterPerm3510_central_mem (i := 2) (by norm_num)
  have m3 : fi22OuterPerm3510 150 ∈ fi22OuterM :=
    fi22OuterPerm3510_central_mem (i := 3) (by norm_num)
  have h : fi22OuterZM =
      ⁅(⟨_, m1⟩ : fi22OuterM), ⟨_, m0⟩⁆ * ⁅(⟨_, m3⟩ : fi22OuterM), ⟨_, m2⟩⁆ := by
    apply Subtype.ext
    rw [commutatorElement_def, commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, Subgroup.coe_inv, Subgroup.coe_inv, Subgroup.coe_inv, Subgroup.coe_mk,
      Subgroup.coe_mk, Subgroup.coe_mk, Subgroup.coe_mk, fi22OuterZM, Subgroup.coe_mk]
    exact fi22OuterCentral_eq.symm
  rw [h]
  exact (commutator fi22OuterM).mul_mem
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))

theorem commutator_fi22OuterM : commutator fi22OuterM = ⊤ := by
  have hmap : (commutator fi22OuterM).map fi22Kappa = ⊤ := by
    rw [commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ fi22Kappa_surjective, ← commutator_def,
      commutator_fi22OuterX]
  rw [eq_top_iff]
  intro g _
  have hg : fi22Kappa g ∈ (commutator fi22OuterM).map fi22Kappa := by
    rw [hmap]
    exact Subgroup.mem_top _
  obtain ⟨h, hh, hgh⟩ := hg
  have hk : h⁻¹ * g ∈ fi22Kappa.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hgh, inv_mul_cancel]
  rw [ker_fi22Kappa_eq] at hk
  have hk' : h⁻¹ * g ∈ commutator fi22OuterM :=
    (Subgroup.zpowers_le.2 fi22OuterZM_mem_commutator) hk
  have := (commutator fi22OuterM).mul_mem hh hk'
  rwa [mul_inv_cancel_left] at this

instance fi22OuterM_isPerfect : Group.IsPerfect fi22OuterM := ⟨commutator_fi22OuterM⟩

@[expose] def fi22CentralQuotEquiv : (fi22OuterM ⧸ Subgroup.center fi22OuterM) ≃* fi22OuterX :=
  (QuotientGroup.quotientMulEquivOfEq (center_fi22OuterM.trans ker_fi22Kappa_eq.symm)).trans
    (QuotientGroup.quotientKerEquivOfSurjective fi22Kappa fi22Kappa_surjective)

theorem fi22CentralQuot_classicalModel :
    StatedClassicalModel (fi22OuterM ⧸ Subgroup.center fi22OuterM) .PSU 6 2 1 :=
  ⟨⟨Nat.prime_two, le_rfl, by norm_num, by decide⟩, F4, inferInstance, inferInstance, fi22U_card,
    ⟨fi22CentralQuotEquiv.trans fi22UnitaryEquiv.symm⟩⟩

end CFSG.RankThree.Native.Fi22U
