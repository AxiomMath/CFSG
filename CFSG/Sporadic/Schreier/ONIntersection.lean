module

public import CFSG.Sporadic.Schreier.ONCentralQuotient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSmallOrders
public import CFSG.Sporadic.Schreier.ONSylowCenter

public noncomputable section

namespace CFSG.ONSchreier

open CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native CFSG.Certificates
open CFSG.ComponentClassification.PSL3Four (TabRep Enumerates enumerates_closure)

theorem prep_onDgens :
    ∀ j (hj : j < onDgens.length), PRep N (wordArrs Data.intersectionWords)[j]! onDgens[j] :=
  prep_wordArrs words_ok.2.2.2.1

theorem prep_conjInv {t c ci : Array ℕ} {g x : Equiv.Perm (Fin N)} (hc : PRep N c x)
    (hci : PRep N ci x⁻¹) (ht : PRep N t g) :
    PRep N (pcomp nPts ci (pcomp nPts t c)) (x⁻¹ * g * x) := by
  have := prep_pcomp hci (prep_pcomp ht hc)
  rwa [← mul_assoc] at this

theorem prep_dConj_gen
    {d : Array ℕ} {g : Equiv.Perm (Fin N)} (hd : PRep N d g) :
    PRep N (pcomp nPts (pinvCand nPts cArr) (pcomp nPts d cArr)) (onc⁻¹ * g * onc) :=
  prep_conjInv prep_onc prep_onc_inv hd

theorem prep_dConj
    {j : ℕ} (hj : j < onDgens.length) :
    PRep N dConj[j]! (onc⁻¹ * onDgens[j] * onc) := by
  have hs : j < (wordArrs Data.intersectionWords).size := by rw [wordArrs_size]; exact hj
  rw [dConj, getElem!_map' _ _ hs]
  exact prep_dConj_gen (prep_onDgens j hj)

theorem onDgens_mem_M
    {j : ℕ} (hj : j < onDgens.length) : onDgens[j] ∈ onM := by
  have hj4 : j < 4 := by rw [onDgens_length] at hj; exact hj
  have h := mFacts.mem (prep_onDgens j hj) (evalList_mem (List.getElem_mem hj))
    (allBelowN_spec d0_cert.1 hj4)
  rwa [onMChain_sub] at h

theorem dConj_mem_M
    {j : ℕ} (hj : j < onDgens.length) : onc⁻¹ * onDgens[j] * onc ∈ onM := by
  have hj4 : j < 4 := by rw [onDgens_length] at hj; exact hj
  have hP : onc⁻¹ * onDgens[j] * onc ∈ Pv :=
    mul_mem (mul_mem (inv_mem onc_mem) (evalList_mem (List.getElem_mem hj))) onc_mem
  have h := mFacts.mem (prep_dConj hj) hP (allBelowN_spec d0_cert.2.1 hj4)
  rwa [onMChain_sub] at h

theorem mem_M1_iff
    {x : Equiv.Perm (Fin N)} : x ∈ onM1 ↔ onc⁻¹ * x * onc ∈ onM := by
  rw [onM1, Subgroup.mem_map]
  constructor
  · rintro ⟨m, hm, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show onc⁻¹ * (onc * m * onc⁻¹) * onc = m by group]
    exact hm
  · intro h
    refine ⟨_, h, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem onD0_le :
    onD0 ≤ onM ⊓ onM1 := by
  rw [onD0, Subgroup.closure_le]
  intro g hg
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
  exact ⟨onDgens_mem_M hj, mem_M1_iff.2 (dConj_mem_M hj)⟩

@[expose] def mToM1 :
    onM ≃* onM1 :=
  Subgroup.equivMapOfInjective onM (MulAut.conj onc).toMonoidHom (MulAut.conj onc).injective

@[expose] def rhoM1 :
    onM1 →* Equiv.Perm (Fin 120) := rhoM.comp mToM1.symm.toMonoidHom

theorem mToM1_val
    (m : onM) : ((mToM1 m : onM1) : Equiv.Perm (Fin N)) = onc * m * onc⁻¹ := rfl

theorem mToM1_symm_val
    (x : onM1) :
    ((mToM1.symm x : onM) : Equiv.Perm (Fin N)) = onc⁻¹ * x * onc := by
  have h := mToM1_val (mToM1.symm x)
  rw [MulEquiv.apply_symm_apply] at h
  rw [h]
  group

theorem rhoM1_apply
    (x : onM1) : rhoM1 x = rhoM (mToM1.symm x) := rfl

theorem rhoM1_range :
    rhoM1.range = onM120Chain.originalSubgroup := by
  rw [← rhoM_range, rhoM1, MonoidHom.range_comp,
    MonoidHom.range_eq_top.2 mToM1.symm.surjective, ← MonoidHom.range_eq_map]

theorem delta_size : Data.D120Generators.size = 4 := m120_cert.2.2.1

theorem prep_delta {j : ℕ} (hj : j < 4) :
    PRep 120 Data.D120Generators[j]! (permOfArr 120 Data.D120Generators[j]!) :=
  (prep_permOfArr (allBelowN_spec m120_cert.2.2.2.1 hj)).1

@[expose] def dM1
    (j : ℕ) : onM1 :=
  if h : j < onDgens.length then
    ⟨onDgens[j], (onD0_le (Subgroup.subset_closure (List.getElem_mem h))).2⟩
  else 1

theorem dM1_val
    {j : ℕ} (h : j < onDgens.length) :
    (dM1 j : Equiv.Perm (Fin N)) = onDgens[j] := by
  rw [dM1, dite_eq_left h]

theorem rhoM1_d
    {j : ℕ} (hj : j < 4) : rhoM1 (dM1 j) = permOfArr 120 Data.D120Generators[j]! := by
  have hjl : j < onDgens.length := by rw [onDgens_length]; exact hj
  have hg : PRep N dConj[j]! ((mToM1.symm (dM1 j) : onM) : Equiv.Perm (Fin N)) := by
    rw [mToM1_symm_val, dM1_val hjl]
    exact prep_dConj hjl
  exact (prep_rhoM hg (allBelowN_spec d0_cert.2.2.1 hj)).unique (prep_delta hj)

@[expose] def deltaCent : Subgroup (Equiv.Perm (Fin 120)) :=
  Subgroup.centralizer (Set.range fun j : Fin 4 => permOfArr 120 Data.D120Generators[j.val]!)

theorem m120_gen_size
    {j : ℕ} (hj : j < Data.M120Chain.generators.size) :
    Data.M120Chain.generators[j]!.size = 120 := by
  have := m120_cert.1
  rw [Array.all_eq_true] at this
  have h := this j hj
  rw [beq_iff_eq] at h
  rwa [getElem!_pos _ j hj]

theorem delta_gen_size
    {j : ℕ} (hj : j < 4) : Data.D120Generators[j]!.size = 120 := by
  have := m120_cert.2.1
  rw [Array.all_eq_true] at this
  have h := this j (by rw [delta_size]; exact hj)
  rw [beq_iff_eq] at h
  rwa [getElem!_pos _ j (by rw [delta_size]; exact hj)]

theorem m120_enumerates :
    Enumerates onM120Chain.originalSubgroup m120Enum.tabs.toList := by
  rw [onM120Chain, smallChain_sub]
  refine enumerates_closure ?_ ?_ m120_cert.2.2.2.2.1
  · rintro _ ⟨j, hj, rfl⟩
    exact ⟨j, hj, tabRep_of_prep (m120_gen_size hj) (prep_smallGen small_chain_certs.2.1 j hj)⟩
  · intro j hj
    exact ⟨_, ⟨j, hj, rfl⟩, tabRep_of_prep (m120_gen_size hj)
      (prep_smallGen small_chain_certs.2.1 j hj)⟩

theorem deltaTest_iff
    {t : Array ℕ} {σ : Equiv.Perm (Fin 120)} (ht : TabRep t σ) :
    (Data.D120Generators.all fun g =>
        CFSG.PSL3Four.Native.comp 120 t g == CFSG.PSL3Four.Native.comp 120 g t) = true ↔
      σ ∈ deltaCent := by
  rw [Array.all_eq_true, deltaCent, Subgroup.mem_centralizer_iff]
  constructor
  · rintro h _ ⟨j, rfl⟩
    have hj : j.val < Data.D120Generators.size := by rw [delta_size]; exact j.isLt
    have h1 := h j.val hj
    rw [← getElem!_pos Data.D120Generators j.val hj, beq_iff_eq] at h1
    have hd := tabRep_of_prep (delta_gen_size j.isLt) (prep_delta j.isLt)
    have h2 : TabRep (CFSG.PSL3Four.Native.comp 120 t Data.D120Generators[j.val]!)
        (permOfArr 120 Data.D120Generators[j.val]! * σ) := by
      rw [h1]
      exact hd.comp ht
    exact ((ht.comp hd).perm_eq h2).symm
  · intro h j hj
    have hj4 : j < 4 := by rwa [delta_size] at hj
    rw [← getElem!_pos Data.D120Generators j hj, beq_iff_eq]
    have hd := tabRep_of_prep (delta_gen_size hj4) (prep_delta hj4)
    have he : permOfArr 120 Data.D120Generators[j]! * σ =
        σ * permOfArr 120 Data.D120Generators[j]! := h _ ⟨⟨j, hj4⟩, rfl⟩
    have h2 : TabRep (CFSG.PSL3Four.Native.comp 120 Data.D120Generators[j]! t)
        (σ * permOfArr 120 Data.D120Generators[j]!) := by
      rw [← he]
      exact hd.comp ht
    exact (ht.comp hd).tab_eq h2

theorem card_deltaCent :
    Nat.card (deltaCent ⊓ onM120Chain.originalSubgroup :
    Subgroup (Equiv.Perm (Fin 120))) = 2 := by
  have hE := m120_enumerates.filter (K := deltaCent) _ fun t σ ht => deltaTest_iff ht
  rw [hE.card, ← Array.toList_filter, Array.length_toList]
  exact m120_cert.2.2.2.2.2.2.1

abbrev cM1D0 :
    Subgroup (Equiv.Perm (Fin N)) :=
  onM1 ⊓ Subgroup.centralizer (onD0 : Set (Equiv.Perm (Fin N)))

@[expose] def rhoC :
    cM1D0 →* Equiv.Perm (Fin 120) :=
  rhoM1.comp (Subgroup.inclusion inf_le_left)

theorem rhoC_range_le :
    rhoC.range ≤ deltaCent ⊓ onM120Chain.originalSubgroup := by
  rintro _ ⟨y, rfl⟩
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [deltaCent, Subgroup.mem_centralizer_iff]
    rintro _ ⟨j, rfl⟩
    show permOfArr 120 Data.D120Generators[j.val]! * rhoC y =
      rhoC y * permOfArr 120 Data.D120Generators[j.val]!
    rw [← rhoM1_d j.isLt]
    show rhoM1 (dM1 j) * rhoM1 (Subgroup.inclusion inf_le_left y) =
      rhoM1 (Subgroup.inclusion inf_le_left y) * rhoM1 (dM1 j)
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have hd : (dM1 j : Equiv.Perm (Fin N)) ∈ onD0 := by
      rw [dM1_val (by rw [onDgens_length]; exact j.isLt)]
      exact Subgroup.subset_closure (List.getElem_mem _)
    exact Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 y.2).2 _ hd
  · rw [← rhoM1_range]
    exact ⟨_, rfl⟩

theorem card_rhoC_range :
    Nat.card rhoC.range ≤ 2 := by
  rw [← card_deltaCent]
  exact Subgroup.card_le_of_le rhoC_range_le

theorem prep_qPow :
    ∀ k, PRep N (qPowArr k) (onq ^ k)
  | 0 => by rw [qPowArr, pow_zero]; exact prep_pid
  | k + 1 => by rw [qPowArr, pow_succ']; exact prep_pcomp prep_q (prep_qPow k)

theorem prep_cqc
    (k : ℕ) : PRep N (cqcArr k) (onc * onq ^ k * onc⁻¹) :=
  prep_conj prep_onc prep_onc_inv (prep_qPow k)

abbrev cqcTest (k : ℕ) : Bool :=
  allBelowN 4 fun j => peq nPts (pcomp nPts (cqcArr k) (wordArrs Data.intersectionWords)[j]!)
    (pcomp nPts (wordArrs Data.intersectionWords)[j]! (cqcArr k))

abbrev passK : Finset ℕ := (Finset.range 4).filter fun k => cqcTest k = true

theorem card_passK : passK.card = 2 := by
  rw [← countBelowN_eq]
  exact d0_cert.2.2.2

abbrev passElts :
    Finset (Equiv.Perm (Fin N)) := passK.image fun k => onc * onq ^ k * onc⁻¹

theorem mem_passElts
    {y : cM1D0} (hy : y ∈ rhoC.ker) : (y : Equiv.Perm (Fin N)) ∈ passElts := by
  rw [MonoidHom.mem_ker] at hy
  have h1 : mToM1.symm (Subgroup.inclusion inf_le_left y) ∈ rhoM.ker := hy
  rw [rhoM_ker, Subgroup.mem_subgroupOf, mToM1_symm_val] at h1
  rw [onQ, mem_zpowers_iff_mem_range_orderOf, orderOf_onq, Finset.mem_image] at h1
  obtain ⟨k, hk, hke⟩ := h1
  rw [Finset.mem_range] at hk
  have hy' : (y : Equiv.Perm (Fin N)) = onc * onq ^ k * onc⁻¹ := by
    show ((Subgroup.inclusion inf_le_left y : onM1) : Equiv.Perm (Fin N)) = _
    rw [hke]
    group
  rw [Finset.mem_image]
  refine ⟨k, Finset.mem_filter.2 ⟨Finset.mem_range.2 hk, ?_⟩, hy'.symm⟩
  rw [allBelowN_iff]
  intro j hj
  have hjl : j < onDgens.length := by rw [onDgens_length]; exact hj
  have hc := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 y.2).2 onDgens[j]
    (Subgroup.subset_closure (List.getElem_mem hjl))
  rw [peq_iff (prep_pcomp (prep_cqc k) (prep_onDgens j hjl))
    (prep_pcomp (prep_onDgens j hjl) (prep_cqc k)), ← hy']
  exact hc.symm

theorem card_rhoC_ker_le :
    Nat.card rhoC.ker ≤ 2 := by
  calc Nat.card rhoC.ker ≤ Nat.card passElts :=
        Nat.card_le_card_of_injective (fun y => ⟨((y : cM1D0) : Equiv.Perm (Fin N)),
          mem_passElts y.2⟩) fun a b h => by
            apply Subtype.ext
            apply Subtype.ext
            simpa using congrArg Subtype.val h
    _ = passElts.card := Nat.card_eq_finsetCard _
    _ ≤ passK.card := Finset.card_image_le
    _ = 2 := card_passK

theorem card_cM1D0_le :
    Nat.card cM1D0 ≤ 4 := by
  rw [card_range_mul_ker rhoC]
  calc Nat.card rhoC.range * Nat.card rhoC.ker ≤ 2 * 2 :=
        Nat.mul_le_mul card_rhoC_range card_rhoC_ker_le
    _ = 4 := rfl

theorem centralizer_inter_le :
    onM1 ⊓ Subgroup.centralizer ((onM ⊓ onM1 : Subgroup (Equiv.Perm (Fin N))) :
      Set (Equiv.Perm (Fin N))) ≤ cM1D0 :=
  inf_le_inf_left _ (Subgroup.centralizer_le onD0_le)

theorem at_on_intersection_centralizer_bound :
    onD0 ≤ onM ⊓ onM1 ∧
      Nat.card (onM1 ⊓ Subgroup.centralizer (onD0 : Set (Equiv.Perm (Fin N))) :
        Subgroup (Equiv.Perm (Fin N))) ≤ 4 ∧
      Group.IsSolvable (onM1 ⊓ Subgroup.centralizer ((onM ⊓ onM1 : Subgroup (Equiv.Perm (Fin N))) :
        Set (Equiv.Perm (Fin N))) : Subgroup (Equiv.Perm (Fin N))) :=
  ⟨onD0_le, card_cM1D0_le,
    CFSG.ComponentClassification.CatalogueSchreierAlternating.solvable_of_card_le_four
      ((Subgroup.card_le_of_le centralizer_inter_le).trans card_cM1D0_le)⟩

end CFSG.ONSchreier
