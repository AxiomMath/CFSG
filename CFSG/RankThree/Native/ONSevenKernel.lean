module

public import CFSG.RankThree.Native.ONSevenCentralizers
public import CFSG.LocalAnalysis.SectionRank.OddCover.CubicKernel

public noncomputable section

namespace CFSG.RankThree.Native

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native
open scoped commutatorElement

@[expose] def onSevenA : Pv := ⟨evalS onSevenSylowWords[0]!, evalS_mem _⟩

@[expose] def onSevenB : Pv := ⟨evalS onSevenSylowWords[1]!, evalS_mem _⟩

@[expose] def onSevenH : Pv := ⟨evalS (onSevenCentWords[0]!)[2]!, evalS_mem _⟩

theorem prep_onSevenA : PRep N onSevenQArrs[0]! (onSevenA : Equiv.Perm (Fin N)) := by
  rw [onSevenQArrs, getElem!_map_onSeven _ _ (by decide)]
  exact prep_onSevenArr (onSeven_letters.1 0 (by decide))

theorem prep_onSevenB : PRep N onSevenQArrs[1]! (onSevenB : Equiv.Perm (Fin N)) := by
  rw [onSevenQArrs, getElem!_map_onSeven _ _ (by decide)]
  exact prep_onSevenArr (onSeven_letters.1 1 (by decide))

theorem prep_onSevenH : PRep N onSevenHArr (onSevenH : Equiv.Perm (Fin N)) := by
  rw [onSevenHArr, onSevenCArrs, getElem!_map_onSeven _ _ (by decide)]
  exact prep_onSevenArr (onSeven_letters.2.2.1 0 (by norm_num) 2 (by decide))

structure ONSevenKernelFacts : Prop where
  aInv : pisInv nPts onSevenQArrs[0]! (pinvCand nPts onSevenQArrs[0]!) = true
  bInv : pisInv nPts onSevenQArrs[1]! (pinvCand nPts onSevenQArrs[1]!) = true
  hInv : pisInv nPts onSevenHArr (pinvCand nPts onSevenHArr) = true
  zne : peq nPts onSevenZArr (pid nPts) = false
  za : peq nPts (pcomp nPts onSevenZArr onSevenQArrs[0]!)
    (pcomp nPts onSevenQArrs[0]! onSevenZArr) = true
  zb : peq nPts (pcomp nPts onSevenZArr onSevenQArrs[1]!)
    (pcomp nPts onSevenQArrs[1]! onSevenZArr) = true
  ha : peq nPts (onSevenConj onSevenHArr onSevenQArrs[0]!)
    (pcomp nPts (pcomp nPts (onSevenPow onSevenQArrs[0]! 6) (onSevenPow onSevenQArrs[1]! 0))
      (onSevenPow onSevenZArr 3)) = true
  hb : peq nPts (onSevenConj onSevenHArr onSevenQArrs[1]!)
    (pcomp nPts (pcomp nPts (onSevenPow onSevenQArrs[0]! 0) (onSevenPow onSevenQArrs[1]! 6))
      (onSevenPow onSevenZArr 2)) = true
  hz : peq nPts (onSevenConj onSevenHArr onSevenZArr) (onSevenPow onSevenZArr 1) = true

theorem onSeven_kernel_facts : ONSevenKernelFacts := by
  have h := onSeven_kernel_check
  simp only [onSevenKernelCheck, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem prep_onSevenZ :
    PRep N onSevenZArr ⁅(onSevenA : Equiv.Perm (Fin N)), (onSevenB : Equiv.Perm (Fin N))⁆ := by
  rw [commutatorElement_def]
  exact prep_pcomp (prep_pcomp (prep_pcomp prep_onSevenA prep_onSevenB)
    (prep_inv_of_pisInv prep_onSevenA onSeven_kernel_facts.aInv))
    (prep_inv_of_pisInv prep_onSevenB onSeven_kernel_facts.bInv)

theorem onSevenA_mem_Q : (onSevenA : Equiv.Perm (Fin N)) ∈ onSevenQ :=
  evalS_mem_onSevenGen (by decide)

theorem onSevenB_mem_Q : (onSevenB : Equiv.Perm (Fin N)) ∈ onSevenQ :=
  evalS_mem_onSevenGen (by decide)

theorem onSevenA_pow_seven : onSevenA ^ 7 = 1 :=
  Subtype.ext (by simpa using onSevenQ_pow_seven onSevenA_mem_Q)

theorem onSevenB_pow_seven : onSevenB ^ 7 = 1 :=
  Subtype.ext (by simpa using onSevenQ_pow_seven onSevenB_mem_Q)

theorem onSeven_commutator_val :
    ((⁅onSevenA, onSevenB⁆ : Pv) : Equiv.Perm (Fin N)) =
      ⁅(onSevenA : Equiv.Perm (Fin N)), (onSevenB : Equiv.Perm (Fin N))⁆ := by
  simp [commutatorElement_def]

theorem onSeven_commutator_ne_one : ⁅onSevenA, onSevenB⁆ ≠ 1 := by
  intro h
  have h1 := congrArg Subtype.val h
  rw [onSeven_commutator_val] at h1
  have := (peq_iff prep_onSevenZ prep_pid).2 h1
  rw [onSeven_kernel_facts.zne] at this
  exact Bool.false_ne_true this

theorem onSeven_commute_commutator_A : Commute ⁅onSevenA, onSevenB⁆ onSevenA := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, onSeven_commutator_val]
  exact eq_of_peq (prep_pcomp prep_onSevenZ prep_onSevenA) (prep_pcomp prep_onSevenA prep_onSevenZ)
    onSeven_kernel_facts.za

theorem onSeven_commute_commutator_B : Commute ⁅onSevenA, onSevenB⁆ onSevenB := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, onSeven_commutator_val]
  exact eq_of_peq (prep_pcomp prep_onSevenZ prep_onSevenB) (prep_pcomp prep_onSevenB prep_onSevenZ)
    onSeven_kernel_facts.zb

theorem onSeven_evalList_sylow :
    {g | g ∈ evalList onSevenSylowWords} =
      ({(onSevenA : Equiv.Perm (Fin N)), (onSevenB : Equiv.Perm (Fin N))} : Set _) := by
  ext g
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff, mem_evalList_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hk2 : k < 2 := hk
    interval_cases k
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, by decide, rfl⟩
    · exact ⟨1, by decide, rfl⟩

theorem card_closure_onSevenAB :
    Nat.card (Subgroup.closure ({onSevenA, onSevenB} : Set Pv)) = 7 ^ 3 := by
  have hmap : (Subgroup.closure ({onSevenA, onSevenB} : Set Pv)).map Pv.subtype = onSevenQ := by
    rw [MonoidHom.map_closure, Set.image_pair, onSevenQ, onSeven_evalList_sylow]
    rfl
  rw [← Subgroup.card_map_of_injective (f := Pv.subtype) Pv.subtype_injective, hmap,
    card_onSevenQ]
  norm_num

theorem not_seven_pow_four_dvd_card_Pv : ¬ 7 ^ 4 ∣ Nat.card Pv := by
  rw [card_Pv]
  norm_num

theorem onSevenH_conj_A :
    onSevenH * onSevenA * onSevenH⁻¹ = onSevenA ^ 6 * onSevenB ^ 0 * ⁅onSevenA, onSevenB⁆ ^ 3 := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, onSeven_commutator_val]
  exact eq_of_peq (prep_onSevenConj prep_onSevenH prep_onSevenA onSeven_kernel_facts.hInv)
    (prep_pcomp (prep_pcomp (prep_onSevenPow prep_onSevenA 6) (prep_onSevenPow prep_onSevenB 0))
      (prep_onSevenPow prep_onSevenZ 3)) onSeven_kernel_facts.ha

theorem onSevenH_conj_B :
    onSevenH * onSevenB * onSevenH⁻¹ = onSevenA ^ 0 * onSevenB ^ 6 * ⁅onSevenA, onSevenB⁆ ^ 2 := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, onSeven_commutator_val]
  exact eq_of_peq (prep_onSevenConj prep_onSevenH prep_onSevenB onSeven_kernel_facts.hInv)
    (prep_pcomp (prep_pcomp (prep_onSevenPow prep_onSevenA 0) (prep_onSevenPow prep_onSevenB 6))
      (prep_onSevenPow prep_onSevenZ 2)) onSeven_kernel_facts.hb

theorem onSevenH_conj_Z :
    onSevenH * ⁅onSevenA, onSevenB⁆ * onSevenH⁻¹ = ⁅onSevenA, onSevenB⁆ ^ 1 := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, onSeven_commutator_val]
  exact eq_of_peq (prep_onSevenConj prep_onSevenH prep_onSevenZ onSeven_kernel_facts.hInv)
    (prep_onSevenPow prep_onSevenZ 1) onSeven_kernel_facts.hz

section Kernel

variable {E S : Type*} [Group E] [Finite E] [Group.IsPerfect E] [Group S]

theorem not_seven_dvd_card_ker_Pv (π : E →* Pv) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) : ¬ 7 ∣ Nat.card π.ker := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨Cp⟩ := (inferInstance : Nonempty (Sylow 7 π.ker))
  have hbot := CFSG.SectionRank.OddCover.cubic_extraspecial_sylow_central_kernel (p := 7) π hπ hC
    onSevenA_pow_seven onSevenB_pow_seven onSeven_commutator_ne_one
    onSeven_commute_commutator_A onSeven_commute_commutator_B card_closure_onSevenAB
    not_seven_pow_four_dvd_card_Pv onSevenH_conj_A onSevenH_conj_B onSevenH_conj_Z
    (by decide +revert) Cp
  have h1 : Nat.card (Cp : Subgroup π.ker) = 1 := Subgroup.card_eq_one.2 hbot
  have hc : Nat.card (Cp : Subgroup π.ker) = 7 ^ (Nat.card π.ker).factorization 7 :=
    Cp.card_eq_multiplicity
  intro hdvd
  have hpos : 0 < (Nat.card π.ker).factorization 7 :=
    Nat.Prime.factorization_pos_of_dvd (by norm_num) Nat.card_pos.ne' hdvd
  have : 1 < 7 ^ (Nat.card π.ker).factorization 7 := Nat.one_lt_pow hpos.ne' (by norm_num)
  omega

theorem not_seven_dvd_card_ker_ON (hS : Nonempty (S ≃* CFSG.Blueprint.NativeSporadic.ON))
    (π : E →* S) (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E) :
    ¬ 7 ∣ Nat.card π.ker := by
  obtain ⟨e⟩ := hS
  set φ : S ≃* Pv := e.trans onEquivPv
  have hk : (φ.toMonoidHom.comp π).ker = π.ker := by
    ext g
    simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
      Function.comp_apply, map_eq_one_iff φ φ.injective]
  have hnd := not_seven_dvd_card_ker_Pv (φ.toMonoidHom.comp π) (φ.surjective.comp hπ)
    (hk ▸ hC)
  rwa [hk] at hnd

end Kernel

end CFSG.RankThree.Native
