module

public import CFSG.Sporadic.Schreier.ONIntersection
public import CFSG.Sporadic.Schreier.ONInvolution
public import CFSG.Sporadic.Schreier.ONCheckR3E

public noncomputable section

namespace CFSG.ONSchreier

open CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native CFSG.Certificates
open CFSG.ComponentClassification.PSL3Four (TabRep Enumerates enumerates_closure)

@[expose] def onD :
    Subgroup (Equiv.Perm (Fin N)) := onD0.map (MulAut.conj onc⁻¹).toMonoidHom

@[expose] def onv :
    Equiv.Perm (Fin N) := onc⁻¹ * onz * onc

@[expose] def onh :
    Equiv.Perm (Fin N) := onMgens.getD 1 1

@[expose] def onA :
    Subgroup (Equiv.Perm (Fin N)) :=
  onD ⊓ onD.map (MulAut.conj onh⁻¹).toMonoidHom

@[expose] def dhPerm
    (j : ℕ) : Equiv.Perm (Fin N) :=
  if j < 4 then onc⁻¹ * onDgens.getD j 1 * onc else onh

theorem prep_h :
    PRep N hArr onh := by
  have h1 : 1 < onMgens.length := by rw [onMgens_length]; norm_num
  rw [onh, List.getD_eq_getElem _ _ h1]
  exact prep_onMgens 1 h1

theorem onh_mem : onh ∈ onM := by
  rw [onh, List.getD_eq_getElem _ _ (by rw [onMgens_length]; norm_num)]
  exact Subgroup.subset_closure (List.getElem_mem _)

theorem dConj_size :
    dConj.size = 4 := by
  simp only [dConj, Array.size_map, wordArrs_size]
  exact onDgens_length

theorem dhGens_get
    {j : ℕ} (hj : j < 5) :
    dhGens[j]! = if j < 4 then dConj[j]! else hArr := by
  rw [dhGens]
  by_cases h4 : j < 4
  · rw [ite_eq_left h4, getElem!_pos _ j (by simp [dConj_size]; omega),
      getElem!_pos _ j (by rw [dConj_size]; exact h4), Array.getElem_push_lt]
  · rw [ite_eq_right h4, getElem!_pos _ j (by simp [dConj_size]; omega)]
    have : j = dConj.size := by rw [dConj_size]; omega
    subst this
    rw [Array.getElem_push_eq]

theorem prep_dhGens
    {j : ℕ} (hj : j < 5) : PRep N dhGens[j]! (dhPerm j) := by
  rw [dhGens_get hj, dhPerm]
  by_cases h4 : j < 4
  · rw [ite_eq_left h4, ite_eq_left h4]
    have hjl : j < onDgens.length := by rw [onDgens_length]; exact h4
    rw [List.getD_eq_getElem _ _ hjl]
    exact prep_dConj hjl
  · rw [ite_eq_right h4, ite_eq_right h4]
    exact prep_h

theorem prep_dhInv
    {j : ℕ} (hj : j < 5) : PRep N dhInv[j]! (dhPerm j)⁻¹ :=
  prep_inv_of_pisInv (prep_dhGens hj) (allBelowN_spec r3e_elem_cert.1 hj)

theorem prep_dhWord
    {w : List ℤ} (hw : plettersOK 5 w = true) :
    PRep N (pword nPts dhGens dhInv w)
      (Quiver.SchreierGraph.evalWord (fun i : Fin 5 => dhPerm i) (ptoLetters 5 w)) :=
  prep_pword (gs := dhPerm) (fun _ hh => prep_dhGens hh) (fun _ hh => prep_dhInv hh) w hw

theorem dhPerm_mem_D
    {j : ℕ} (hj : j < 4) : dhPerm j ∈ onD := by
  rw [dhPerm, ite_eq_left hj, onD, Subgroup.mem_map]
  have hjl : j < onDgens.length := by rw [onDgens_length]; exact hj
  refine ⟨onDgens.getD j 1, ?_, ?_⟩
  · rw [List.getD_eq_getElem _ _ hjl]
    exact Subgroup.subset_closure (List.getElem_mem _)
  · simp

theorem onD_eq :
    onD = Subgroup.closure (dhPerm '' {j | j < 4}) := by
  rw [onD, onD0, MonoidHom.map_closure]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_ofPred_eq, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    inv_inv]
  constructor
  · rintro ⟨d, hd, rfl⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hd
    have hj4 : j < 4 := by rw [onDgens_length] at hj; exact hj
    refine ⟨j, hj4, ?_⟩
    rw [dhPerm, ite_eq_left hj4, List.getD_eq_getElem _ _ hj]
  · rintro ⟨j, hj, rfl⟩
    have hjl : j < onDgens.length := by rw [onDgens_length]; exact hj
    refine ⟨onDgens[j], List.getElem_mem _, ?_⟩
    rw [dhPerm, ite_eq_left hj, List.getD_eq_getElem _ _ hjl]

theorem onD_le_M :
    onD ≤ onM := by
  rw [onD_eq, Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  have hj4 : j < 4 := hj
  have hjl : j < onDgens.length := by rw [onDgens_length]; exact hj4
  rw [dhPerm, ite_eq_left hj4, List.getD_eq_getElem _ _ hjl]
  exact dConj_mem_M hjl

theorem dhPerm_mem_M
    (j : ℕ) : dhPerm j ∈ onM := by
  by_cases h4 : j < 4
  · exact onD_le_M (dhPerm_mem_D h4)
  · rw [dhPerm, ite_eq_right h4]
    exact onh_mem

theorem dConj_gen_size
    {j : ℕ} (hj : j < dConj.size) : dConj[j]!.size = nPts := by
  have := r3e_enum_cert.1
  rw [Array.all_eq_true] at this
  have h := this j hj
  rw [beq_iff_eq] at h
  rwa [getElem!_pos _ j hj]

theorem tabRep_dConj
    {j : ℕ} (hj : j < 4) : TabRep dConj[j]! (dhPerm j) := by
  have h := prep_dhGens (j := j) (by omega)
  rw [dhGens_get (by omega), ite_eq_left hj] at h
  exact tabRep_of_prep (dConj_gen_size (by rw [dConj_size]; exact hj)) h

theorem d_enumerates :
    Enumerates onD dEnum.tabs.toList := by
  rw [onD_eq]
  refine enumerates_closure ?_ ?_ r3e_enum_cert.2.1
  · rintro _ ⟨j, hj, rfl⟩
    exact ⟨j, by rw [dConj_size]; exact hj, tabRep_dConj hj⟩
  · intro j hj
    rw [dConj_size] at hj
    exact ⟨_, ⟨j, hj, rfl⟩, tabRep_dConj hj⟩

theorem card_onD :
    Nat.card onD = 144 := by
  rw [d_enumerates.card, Array.length_toList]
  exact r3e_enum_cert.2.2.1

theorem q_cases
    {x : Equiv.Perm (Fin N)} (hx : x ∈ onQ) :
    x = 1 ∨ x = onq ∨ x = onq ^ 2 ∨ x = onq ^ 3 := by
  rw [onQ, mem_zpowers_iff_mem_range_orderOf, orderOf_onq, Finset.mem_image] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  rw [Finset.mem_range] at hk
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
  · left; exact pow_zero _
  · right; left; exact pow_one _
  · right; right; left; rfl
  · right; right; right; rfl

theorem q13_fail
    {gs : ℕ → Array ℕ} {G : ℕ → Equiv.Perm (Fin N)} {m : ℕ}
    (hG : ∀ j < m, PRep N (gs j) (G j))
    (h : (#[1, 3] : Array ℕ).all (fun k => !(allBelowN m fun j =>
      peq nPts (pcomp nPts (qPowArr k) (gs j)) (pcomp nPts (gs j) (qPowArr k)))) = true)
    {x : Equiv.Perm (Fin N)} (hx : x = onq ∨ x = onq ^ 3) : ∃ j < m, x * G j ≠ G j * x := by
  rw [Array.all_eq_true] at h
  have key : ∀ k, k = 1 ∨ k = 3 → ∃ j < m, onq ^ k * G j ≠ G j * onq ^ k := by
    rintro k hk
    have hk' := h (if k = 1 then 0 else 1) (by split_ifs <;> simp)
    have e : (#[1, 3] : Array ℕ)[if k = 1 then 0 else 1]'(by split_ifs <;> simp) = k := by
      rcases hk with rfl | rfl <;> simp
    rw [e, Bool.not_eq_true', ← Bool.not_eq_true, allBelowN_iff] at hk'
    push Not at hk'
    obtain ⟨j, hj, hne⟩ := hk'
    refine ⟨j, hj, fun heq => hne ?_⟩
    exact (peq_iff (prep_pcomp (prep_qPow k) (hG j hj)) (prep_pcomp (hG j hj) (prep_qPow k))).2 heq
  rcases hx with rfl | rfl
  · simpa using key 1 (Or.inl rfl)
  · exact key 3 (Or.inr rfl)

theorem onz_eq_q2 :
    onz = onq ^ 2 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h11, -⟩ := r3e_elem_cert
  exact eq_of_peq prep_z (prep_qPow 2) h11

theorem onz_mem_M :
    onz ∈ onM := by
  rw [onM_eq_centralizer_z]
  exact Subgroup.mem_inf.2 ⟨evalS_mem _, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩

theorem onz_comm_M
    {g : Equiv.Perm (Fin N)} (hg : g ∈ onM) : g * onz = onz * g :=
  Subgroup.mem_centralizer_singleton_iff.1 (onM_le_centralizer_z hg)

theorem onM_centerIn :
    CFSG.centerIn onM = Subgroup.zpowers onz := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h12, -⟩ := r3e_elem_cert
  apply le_antisymm
  · intro x hx
    obtain ⟨hxM, hxc⟩ := Subgroup.mem_inf.1 hx
    have hxQ : x ∈ onQ := by
      rw [← onM_centralizer_L]
      refine Subgroup.mem_inf.2 ⟨hxM, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
      exact Subgroup.mem_centralizer_iff.1 hxc y (onL_le_M hy)
    rcases q_cases hxQ with h | h | h | h
    · rw [h]; exact one_mem _
    · obtain ⟨j, hj, hne⟩ := q13_fail (gs := fun j => (wordArrs Data.MWords)[j]!)
        (G := fun j => onMgens.getD j 1) (fun j hj => by
          rw [List.getD_eq_getElem _ _ (by rw [onMgens_length]; exact hj)]
          exact prep_onMgens j (by rw [onMgens_length]; exact hj)) h12 (Or.inl h)
      exact absurd ((Subgroup.mem_centralizer_iff.1 hxc _ (by
        rw [List.getD_eq_getElem _ _ (by rw [onMgens_length]; exact hj)]
        exact Subgroup.subset_closure (List.getElem_mem _))).symm) hne
    · rw [h, ← onz_eq_q2]; exact Subgroup.mem_zpowers _
    · obtain ⟨j, hj, hne⟩ := q13_fail (gs := fun j => (wordArrs Data.MWords)[j]!)
        (G := fun j => onMgens.getD j 1) (fun j hj => by
          rw [List.getD_eq_getElem _ _ (by rw [onMgens_length]; exact hj)]
          exact prep_onMgens j (by rw [onMgens_length]; exact hj)) h12 (Or.inr h)
      exact absurd ((Subgroup.mem_centralizer_iff.1 hxc _ (by
        rw [List.getD_eq_getElem _ _ (by rw [onMgens_length]; exact hj)]
        exact Subgroup.subset_closure (List.getElem_mem _))).symm) hne
  · rw [Subgroup.zpowers_le]
    exact Subgroup.mem_inf.2 ⟨onz_mem_M, Subgroup.mem_centralizer_iff.2 fun y hy =>
      onz_comm_M hy⟩

theorem card_onM_centerIn :
    Nat.card (CFSG.centerIn onM) = 2 := by
  rw [onM_centerIn, Nat.card_zpowers, orderOf_onz]

theorem prep_v :
    PRep N vArr onv := prep_conjInv prep_onc prep_onc_inv prep_z

theorem onv_mem_P :
    onv ∈ Pv := mul_mem (mul_mem (inv_mem onc_mem) (evalS_mem _)) onc_mem

theorem onv_mem_M :
    onv ∈ onM := by
  obtain ⟨-, -, -, -, h5, -⟩ := r3e_elem_cert
  have h := mFacts.mem prep_v onv_mem_P h5
  rwa [onMChain_sub] at h

theorem onv_ne_one :
    onv ≠ 1 := by
  obtain ⟨-, -, -, -, -, -, h7, -⟩ := r3e_elem_cert
  intro h
  rw [(peq_iff prep_v prep_pid).2 h] at h7
  exact absurd h7 (by decide)

theorem onv_ne_z :
    onv ≠ onz := by
  obtain ⟨-, -, -, -, -, -, -, h8, -⟩ := r3e_elem_cert
  intro h
  rw [(peq_iff prep_v prep_z).2 h] at h8
  exact absurd h8 (by decide)

theorem onv_sq :
    onv * onv = 1 := by
  rw [onv, show onc⁻¹ * onz * onc * (onc⁻¹ * onz * onc) = onc⁻¹ * (onz * onz) * onc by group,
    onz_sq, mul_one, inv_mul_cancel]

theorem orderOf_onv :
    orderOf onv = 2 :=
  orderOf_eq_prime (by rw [sq]; exact onv_sq) onv_ne_one

theorem onv_comm_dhPerm
    {j : ℕ} (hj : j < 4) : onv * dhPerm j = dhPerm j * onv := by
  obtain ⟨-, -, -, -, -, -, -, -, h9, -⟩ := r3e_elem_cert
  have hd := prep_dhGens (j := j) (by omega)
  rw [dhGens_get (by omega), ite_eq_left hj] at hd
  exact eq_of_peq (prep_pcomp prep_v hd) (prep_pcomp hd prep_v) (allBelowN_spec h9 hj)

theorem onv_centralizes_D :
    onD ≤ Subgroup.centralizer {onv} := by
  rw [onD_eq, Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  exact Subgroup.mem_centralizer_singleton_iff.2 (onv_comm_dhPerm hj).symm

theorem onv_not_comm_h :
    onv * onh ≠ onh * onv := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h10, -⟩ := r3e_elem_cert
  intro h
  rw [(peq_iff (prep_pcomp prep_v prep_h) (prep_pcomp prep_h prep_v)).2 h] at h10
  exact absurd h10 (by decide)

abbrev cMD :
    Subgroup (Equiv.Perm (Fin N)) :=
  onM ⊓ Subgroup.centralizer (onD : Set (Equiv.Perm (Fin N)))

theorem rhoM_dhPerm
    {j : ℕ} (hj : j < 4) :
    rhoM ⟨dhPerm j, dhPerm_mem_M j⟩ = permOfArr 120 Data.D120Generators[j]! := by
  have hd := prep_dhGens (j := j) (by omega)
  rw [dhGens_get (by omega), ite_eq_left hj] at hd
  exact (prep_rhoM (g := ⟨dhPerm j, dhPerm_mem_M j⟩) hd (allBelowN_spec d0_cert.2.2.1 hj)).unique
    (prep_delta hj)

@[expose] def rhoMD :
    cMD →* Equiv.Perm (Fin 120) := rhoM.comp (Subgroup.inclusion inf_le_left)

theorem rhoMD_range_le :
    rhoMD.range ≤ deltaCent ⊓ onM120Chain.originalSubgroup := by
  rintro _ ⟨y, rfl⟩
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [deltaCent, Subgroup.mem_centralizer_iff]
    rintro _ ⟨j, rfl⟩
    show permOfArr 120 Data.D120Generators[j.val]! * rhoMD y =
      rhoMD y * permOfArr 120 Data.D120Generators[j.val]!
    rw [← rhoM_dhPerm j.isLt]
    show rhoM ⟨dhPerm j, dhPerm_mem_M j⟩ * rhoM (Subgroup.inclusion inf_le_left y) =
      rhoM (Subgroup.inclusion inf_le_left y) * rhoM ⟨dhPerm j, dhPerm_mem_M j⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 y.2).2 _ (dhPerm_mem_D j.isLt)
  · rw [← rhoM_range]
    exact ⟨_, rfl⟩

theorem mem_ker_cases
    {x : Equiv.Perm (Fin N)} (hxM : x ∈ onM)
    (hk : rhoM ⟨x, hxM⟩ = 1) : x ∈ onQ := by
  have : (⟨x, hxM⟩ : onM) ∈ rhoM.ker := hk
  rw [rhoM_ker, Subgroup.mem_subgroupOf] at this
  exact this

theorem card_rhoMD_ker_le :
    Nat.card rhoMD.ker ≤ 2 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h13, -⟩ := r3e_elem_cert
  have hmem : ∀ y ∈ rhoMD.ker, ((y : cMD) : Equiv.Perm (Fin N)) ∈ ({1, onz} : Finset _) := by
    intro y hy
    have hQ := mem_ker_cases _ hy
    have hc : ∀ j < 4, ((y : cMD) : Equiv.Perm (Fin N)) * dhPerm j =
        dhPerm j * ((y : cMD) : Equiv.Perm (Fin N)) := fun j hj =>
      (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 y.2).2 _ (dhPerm_mem_D hj)).symm
    have hg : ∀ j < 4, PRep N dConj[j]! (dhPerm j) := fun j hj => by
      have hd := prep_dhGens (j := j) (by omega)
      rwa [dhGens_get (by omega), ite_eq_left hj] at hd
    rcases q_cases hQ with h | h | h | h
    · simp [h]
    · obtain ⟨j, hj, hne⟩ := q13_fail (gs := fun j => dConj[j]!) hg h13 (Or.inl h)
      exact absurd (hc j hj) (by rw [h] at hne ⊢; exact hne)
    · simp [h, ← onz_eq_q2]
    · obtain ⟨j, hj, hne⟩ := q13_fail (gs := fun j => dConj[j]!) hg h13 (Or.inr h)
      exact absurd (hc j hj) (by rw [h] at hne ⊢; exact hne)
  calc Nat.card rhoMD.ker ≤ Nat.card ({1, onz} : Finset (Equiv.Perm (Fin N))) :=
        Nat.card_le_card_of_injective (fun y => ⟨((y : cMD) : Equiv.Perm (Fin N)), hmem y y.2⟩)
          fun a b h => by
            apply Subtype.ext; apply Subtype.ext
            simpa using congrArg Subtype.val h
    _ = ({1, onz} : Finset (Equiv.Perm (Fin N))).card := Nat.card_eq_finsetCard _
    _ ≤ 2 := Finset.card_le_two

theorem mem_cMD
    {x : Equiv.Perm (Fin N)} (hxM : x ∈ onM)
    (hx : ∀ j < 4, x * dhPerm j = dhPerm j * x) :
    x ∈ cMD := by
  refine Subgroup.mem_inf.2 ⟨hxM, ?_⟩
  rw [Subgroup.mem_centralizer_iff, onD_eq]
  intro g hg
  rw [SetLike.mem_coe] at hg
  show Commute g x
  induction hg using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨j, hj, rfl⟩ := hy
    exact (hx j hj).symm
  | one => exact Commute.one_left x
  | mul a b _ _ ha hb => exact Commute.mul_left ha hb
  | inv a _ ha => exact Commute.inv_left ha

theorem card_cMD :
    Nat.card cMD = 4 := by
  apply le_antisymm
  · rw [card_range_mul_ker rhoMD]
    calc Nat.card rhoMD.range * Nat.card rhoMD.ker ≤ 2 * 2 :=
          Nat.mul_le_mul ((Subgroup.card_le_of_le rhoMD_range_le).trans card_deltaCent.le)
            card_rhoMD_ker_le
      _ = 4 := rfl
  · have hz : onz ∈ cMD := mem_cMD onz_mem_M fun j _ => (onz_comm_M (dhPerm_mem_M j)).symm
    have hv : onv ∈ cMD := mem_cMD onv_mem_M fun j hj => onv_comm_dhPerm hj
    have hzv : onz * onv ∈ cMD := mul_mem hz hv
    have hzne : onz ≠ 1 := onz_ne_one
    have hzv1 : onz * onv ≠ 1 := fun h => onv_ne_z (by
      calc onv = onz * (onz * onv) := by rw [← mul_assoc, onz_sq, one_mul]
        _ = onz := by rw [h, mul_one])
    have hzvz : onz * onv ≠ onz := fun h => onv_ne_one (mul_left_cancel (h.trans (mul_one _).symm))
    have hzvv : onz * onv ≠ onv := fun h => hzne (mul_right_cancel (h.trans (one_mul _).symm))
    have h4 : ({1, onz, onv, onz * onv} : Finset (Equiv.Perm (Fin N))).card = 4 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hzvv.symm]
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨onv_ne_z.symm, hzvz.symm⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hzne.symm, onv_ne_one.symm, hzv1.symm⟩
    have hsub : ∀ x ∈ ({1, onz, onv, onz * onv} : Finset (Equiv.Perm (Fin N))), x ∈ cMD := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact one_mem _
      · exact hz
      · exact hv
      · exact hzv
    calc 4 = ({1, onz, onv, onz * onv} : Finset (Equiv.Perm (Fin N))).card := h4.symm
      _ = Nat.card ({1, onz, onv, onz * onv} : Finset (Equiv.Perm (Fin N))) :=
          (Nat.card_eq_finsetCard _).symm
      _ ≤ Nat.card cMD := Nat.card_le_card_of_injective (fun x => ⟨x.1, hsub x.1 x.2⟩)
          fun a b h => by
            apply Subtype.ext
            simpa using congrArg Subtype.val h

theorem evalWord_dh_mem
    {K : Subgroup (Equiv.Perm (Fin N))} (hK : ∀ j < 5, dhPerm j ∈ K)
    (w : List (CFSG.Certificates.SchreierLetter 5)) :
    Quiver.SchreierGraph.evalWord (fun i : Fin 5 => dhPerm i) w ∈ K := by
  apply (Subgroup.closure_le _).2 ?_ (Quiver.SchreierGraph.evalWord_mem_closure _ _)
  rintro _ ⟨i, rfl⟩
  exact hK i i.isLt

theorem dhPerm_mem_closure (j : ℕ) :
    dhPerm j ∈ Subgroup.closure ((onD : Set (Equiv.Perm (Fin N))) ∪ {onh}) := by
  by_cases h4 : j < 4
  · exact Subgroup.subset_closure (Or.inl (dhPerm_mem_D h4))
  · rw [dhPerm, ite_eq_right h4]
    exact Subgroup.subset_closure (Or.inr rfl)

theorem onM_eq_closure :

    onM = Subgroup.closure ((onD : Set (Equiv.Perm (Fin N))) ∪ {onh}) := by
  obtain ⟨-, h2, -⟩ := r3e_elem_cert
  apply le_antisymm
  · rw [onM, Subgroup.closure_le]
    intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    have hj3 : j < 3 := by rw [onMgens_length] at hj; exact hj
    have hw := allBelowN_spec h2 hj3
    rw [Bool.and_eq_true] at hw
    have e := eq_of_peq (prep_dhWord hw.1) (prep_onMgens j hj) hw.2
    rw [← e]
    exact evalWord_dh_mem (fun i _ => dhPerm_mem_closure i) _
  · rw [Subgroup.closure_le]
    rintro x (hx | hx)
    · exact onD_le_M hx
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact onh_mem

theorem pword_size (n : ℕ) (S Sinv : Array (Array ℕ)) : ∀ w, (pword n S Sinv w).size = n
  | [] => by simp [pword, pid]
  | _ :: _ => by simp [pword, pcomp]

theorem hArr_size : hArr.size = nPts := by
  rw [hArr, wordArrs, pwords_eq, getElem!_map' _ _ (by decide)]
  exact pword_size _ _ _ _

theorem tabRep_conj
    {t hi : Array ℕ} {g : Equiv.Perm (Fin N)} (ht : TabRep t g)
    (hh : PRep N hArr onh) (hhi : PRep N hi onh⁻¹) :
    TabRep (CFSG.PSL3Four.Native.conjTab nPts hArr hi t) (onh * g * onh⁻¹) := by
  refine ⟨by simp [CFSG.PSL3Four.Native.conjTab, CFSG.PSL3Four.Native.comp], fun i => ?_⟩
  simp only [CFSG.PSL3Four.Native.conjTab]
  rw [CFSG.ComponentClassification.PSL3Four.TabRep.comp_getElem!, hhi i,
    CFSG.ComponentClassification.PSL3Four.TabRep.comp_getElem!, ht.apply, hh,
    Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]

theorem prep_hinv :
    PRep N (pinvCand nPts hArr) onh⁻¹ := by
  have h := prep_dhInv (j := 4) (by norm_num)
  have e : dhInv[4]! = pinvCand nPts hArr := by
    rw [dhInv, pinvs, getElem!_map' _ _ (by simp [dhGens, dConj_size]), dhGens_get (by norm_num),
      ite_eq_right (by norm_num)]
  rw [e] at h
  have e2 : dhPerm 4 = onh := by rw [dhPerm, ite_eq_right (by norm_num)]
  rwa [e2] at h

theorem conj_mem_D_iff
    {g : Equiv.Perm (Fin N)} :
    onh * g * onh⁻¹ ∈ onD ↔ g ∈ onD.map (MulAut.conj onh⁻¹).toMonoidHom := by
  rw [Subgroup.mem_map]
  constructor
  · intro h
    refine ⟨_, h, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  · rintro ⟨d, hd, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [show onh * (onh⁻¹ * d * onh) * onh⁻¹ = d by group]
    exact hd

theorem a_enumerates :
    Enumerates onA aTabs.toList := by
  have hE := d_enumerates.filter (K := onD.map (MulAut.conj onh⁻¹).toMonoidHom)
    (fun t => dEnum.tabs.any fun u => u == CFSG.PSL3Four.Native.conjTab nPts hArr
      (pinvCand nPts hArr) t) fun t g ht => by
    rw [Array.any_eq_true, ← conj_mem_D_iff]
    have hc := tabRep_conj ht prep_h prep_hinv
    constructor
    · rintro ⟨k, hk, hu⟩
      rw [beq_iff_eq] at hu
      obtain ⟨x, hx, hrep⟩ := d_enumerates.sound dEnum.tabs[k] (Array.getElem_mem_toList hk)
      rw [hu] at hrep
      rwa [hc.perm_eq hrep]
    · intro hmem
      obtain ⟨u, hu, hrep⟩ := d_enumerates.complete _ hmem
      obtain ⟨k, hk, rfl⟩ := CFSG.ComponentClassification.PSL3Four.exists_getElem!_of_mem hu
      refine ⟨k, hk, ?_⟩
      rw [beq_iff_eq, ← getElem!_pos _ k hk]
      exact hrep.tab_eq hc
  rw [onA, inf_comm, aTabs, Array.toList_filter]
  exact hE

theorem card_onA :
    Nat.card onA = 4 := by
  rw [a_enumerates.card, Array.length_toList]
  exact r3e_enum_cert.2.2.2.1

theorem q_pow_cases
    {x : Equiv.Perm (Fin N)} (hx : x ∈ onQ) : ∃ k < 4, x = onq ^ k := by
  rw [onQ, mem_zpowers_iff_mem_range_orderOf, orderOf_onq, Finset.mem_image] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  exact ⟨k, Finset.mem_range.1 hk, rfl⟩

@[expose] def hPerm
    (j : ℕ) : Equiv.Perm (Fin N) :=
  Quiver.SchreierGraph.evalWord (fun i : Fin 5 => dhPerm i) (ptoLetters 5 hWordsDH[j]!)

theorem hWordsDH_size : hWordsDH.size = 4 := rfl

theorem hGensArr_size : hGensArr.size = 4 := by
  rw [hGensArr, pwords_eq, Array.size_map]; rfl

theorem prep_hGens
    {j : ℕ} (hj : j < 4) : PRep N hGensArr[j]! (hPerm j) := by
  obtain ⟨-, -, h3, -⟩ := r3e_elem_cert
  rw [hGensArr, pwords_eq, getElem!_map' _ _ (by rw [hWordsDH_size]; exact hj)]
  rw [Array.all_eq_true] at h3
  have := h3 j (by rw [hWordsDH_size]; exact hj)
  rw [← getElem!_pos hWordsDH j (by rw [hWordsDH_size]; exact hj)] at this
  exact prep_dhWord this

theorem tabRep_hGens
    {j : ℕ} (hj : j < 4) : TabRep hGensArr[j]! (hPerm j) := by
  have hs := r3e_enum_cert.2.2.2.2.1
  rw [Array.all_eq_true] at hs
  have h := hs j (by rw [hGensArr_size]; exact hj)
  rw [beq_iff_eq, ← getElem!_pos hGensArr j (by rw [hGensArr_size]; exact hj)] at h
  exact tabRep_of_prep h (prep_hGens hj)

@[expose] def onH :
    Subgroup (Equiv.Perm (Fin N)) := Subgroup.closure (hPerm '' {j | j < 4})

theorem h_enumerates :
    Enumerates onH hEnum.tabs.toList := by
  refine enumerates_closure ?_ ?_ r3e_enum_cert.2.2.2.2.2.1
  · rintro _ ⟨j, hj, rfl⟩
    exact ⟨j, by rw [hGensArr_size]; exact hj, tabRep_hGens hj⟩
  · intro j hj
    rw [hGensArr_size] at hj
    exact ⟨_, ⟨j, hj, rfl⟩, tabRep_hGens hj⟩

theorem card_onH :
    Nat.card onH = 144 := by
  rw [h_enumerates.card, Array.length_toList]
  exact r3e_enum_cert.2.2.2.2.2.2.1

abbrev cMA :
    Subgroup (Equiv.Perm (Fin N)) :=
  onM ⊓ Subgroup.centralizer (onA : Set (Equiv.Perm (Fin N)))

theorem comm_A_of_tabs
    {g : Equiv.Perm (Fin N)} {t : Array ℕ} (ht : TabRep t g)
    (h : aTabs.all (fun a => CFSG.PSL3Four.Native.comp nPts t a ==
      CFSG.PSL3Four.Native.comp nPts a t) = true) :
    g ∈ Subgroup.centralizer (onA : Set (Equiv.Perm (Fin N))) := by
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  obtain ⟨u, hu, hrep⟩ := a_enumerates.complete a ha
  obtain ⟨k, hk, rfl⟩ := CFSG.ComponentClassification.PSL3Four.exists_getElem!_of_mem hu
  rw [Array.all_eq_true] at h
  have h1 := h k hk
  rw [beq_iff_eq, ← getElem!_pos aTabs k hk] at h1
  have h2 : TabRep (CFSG.PSL3Four.Native.comp nPts aTabs[k]! t) (g * a) := by
    rw [← h1]; exact ht.comp hrep
  exact (hrep.comp ht).perm_eq h2

theorem onH_le :
    onH ≤ cMA := by
  rw [onH, Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  refine Subgroup.mem_inf.2 ⟨evalWord_dh_mem (fun i _ => dhPerm_mem_M i) _, ?_⟩
  have hc := r3e_enum_cert.2.2.2.2.2.2.2.1
  rw [Array.all_eq_true] at hc
  have h := hc j (by rw [hGensArr_size]; exact hj)
  rw [← getElem!_pos hGensArr j (by rw [hGensArr_size]; exact hj)] at h
  exact comm_A_of_tabs (tabRep_hGens hj) h

@[expose] def rhoAset :
    Set (Equiv.Perm (Fin 120)) :=
  {σ | ∃ a, ∃ ha : a ∈ onA, σ = rhoM ⟨a, onD_le_M (Subgroup.mem_inf.1 ha).1⟩}

theorem tabRep_bTab
    {a : Equiv.Perm (Fin N)} (ha : a ∈ onA) {t : Array ℕ} (ht : TabRep t a)
    (hb : blockImgOK t Data.quotientBlocks (bTab t) = true) :
    TabRep (bTab t) (rhoM ⟨a, onD_le_M (Subgroup.mem_inf.1 ha).1⟩) :=
  ⟨by simp [bTab, blockTab, qblocks_size], prep_rhoM (g := ⟨a, _⟩) ht.2 hb⟩

theorem aTabs_block {k : ℕ} (hk : k < aTabs.size) :
    blockImgOK aTabs[k]! Data.quotientBlocks (bTab aTabs[k]!) = true := by
  have h := r3e_lift_cert.1
  rw [Array.all_eq_true] at h
  rw [getElem!_pos aTabs k hk]
  exact h k hk

theorem rhoA_test_iff
    {x : Array ℕ} {σ : Equiv.Perm (Fin 120)} (hx : TabRep x σ) :
    (aTabs.all fun a => CFSG.PSL3Four.Native.comp 120 x (bTab a) ==
        CFSG.PSL3Four.Native.comp 120 (bTab a) x) = true ↔
      σ ∈ Subgroup.centralizer rhoAset := by
  rw [Array.all_eq_true, Subgroup.mem_centralizer_iff]
  constructor
  · rintro h _ ⟨a, ha, rfl⟩
    obtain ⟨u, hu, hrep⟩ := a_enumerates.complete a ha
    obtain ⟨k, hk, rfl⟩ := CFSG.ComponentClassification.PSL3Four.exists_getElem!_of_mem hu
    have h1 := h k hk
    rw [beq_iff_eq, ← getElem!_pos aTabs k hk] at h1
    have hb := tabRep_bTab ha hrep (aTabs_block hk)
    have h2 : TabRep (CFSG.PSL3Four.Native.comp 120 x (bTab aTabs[k]!))
        (rhoM ⟨a, onD_le_M (Subgroup.mem_inf.1 ha).1⟩ * σ) := by
      rw [h1]; exact hb.comp hx
    exact ((hx.comp hb).perm_eq h2).symm
  · intro h k hk
    obtain ⟨a, ha, hrep⟩ := a_enumerates.sound aTabs[k] (Array.getElem_mem_toList hk)
    rw [← getElem!_pos aTabs k hk] at hrep
    have hb := tabRep_bTab ha hrep (aTabs_block hk)
    rw [beq_iff_eq, ← getElem!_pos aTabs k hk]
    have he := h _ ⟨a, ha, rfl⟩
    have h2 : TabRep (CFSG.PSL3Four.Native.comp 120 (bTab aTabs[k]!) x)
        (σ * rhoM ⟨a, onD_le_M (Subgroup.mem_inf.1 ha).1⟩) := by
      rw [← he]; exact hb.comp hx
    exact (hx.comp hb).tab_eq h2

abbrev kA :
    Subgroup (Equiv.Perm (Fin 120)) :=
  Subgroup.centralizer rhoAset ⊓ onM120Chain.originalSubgroup

theorem card_kA :
    Nat.card kA = 144 := by
  have hE := m120_enumerates.filter (K := Subgroup.centralizer rhoAset) _
    fun t σ ht => rhoA_test_iff ht
  rw [hE.card, ← Array.toList_filter, Array.length_toList]
  exact r3e_lift_cert.2.1

@[expose] def rhoMA :
    cMA →* Equiv.Perm (Fin 120) := rhoM.comp (Subgroup.inclusion inf_le_left)

theorem rhoMA_range_le :
    rhoMA.range ≤ kA := by
  rintro _ ⟨y, rfl⟩
  refine Subgroup.mem_inf.2 ⟨?_, by rw [← rhoM_range]; exact ⟨_, rfl⟩⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨a, ha, rfl⟩
  show rhoM ⟨a, _⟩ * rhoM (Subgroup.inclusion inf_le_left y) =
    rhoM (Subgroup.inclusion inf_le_left y) * rhoM ⟨a, _⟩
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 y.2).2 _ ha

@[expose] def mPerm :
    Equiv.Perm (Fin N) :=
  Quiver.SchreierGraph.evalWord (fun i : Fin 5 => dhPerm i) (ptoLetters 5 liftWordDH)

theorem mPerm_mem :
    mPerm ∈ onM := evalWord_dh_mem (fun i _ => dhPerm_mem_M i) _

theorem prep_mPerm :
    PRep N mLiftArr mPerm := prep_dhWord r3e_lift_cert.2.2.1

theorem rho_mPerm_mem :
    rhoM ⟨mPerm, mPerm_mem⟩ ∈ kA := by
  have hb : TabRep (bTab mLiftArr) (rhoM ⟨mPerm, mPerm_mem⟩) :=
    ⟨by simp [bTab, blockTab, qblocks_size],
      prep_rhoM (g := ⟨mPerm, mPerm_mem⟩) prep_mPerm r3e_lift_cert.2.2.2.1⟩
  refine Subgroup.mem_inf.2 ⟨(rhoA_test_iff hb).1 r3e_lift_cert.2.2.2.2.1, ?_⟩
  rw [← rhoM_range]
  exact ⟨_, rfl⟩

theorem rho_mPerm_not_mem :
    rhoM ⟨mPerm, mPerm_mem⟩ ∉ rhoMA.range := by
  rintro ⟨y, hy⟩
  have hker : (⟨mPerm, mPerm_mem⟩ : onM)⁻¹ * Subgroup.inclusion inf_le_left y ∈ rhoM.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    show (rhoM ⟨mPerm, mPerm_mem⟩)⁻¹ * rhoMA y = 1
    rw [hy, inv_mul_cancel]
  rw [rhoM_ker, Subgroup.mem_subgroupOf] at hker
  obtain ⟨k, hk, hq⟩ := q_pow_cases hker
  have hyv : ((y : cMA) : Equiv.Perm (Fin N)) = mPerm * onq ^ k := by
    have : mPerm⁻¹ * ((y : cMA) : Equiv.Perm (Fin N)) = onq ^ k := hq
    rw [← this, mul_inv_cancel_left]
  have hfail := allBelowN_spec r3e_lift_cert.2.2.2.2.2 hk
  rw [Bool.not_eq_true', ← Bool.not_eq_true, Array.all_eq_true] at hfail
  apply hfail
  intro j hj
  obtain ⟨a, ha, hrep⟩ := a_enumerates.sound aTabs[j] (Array.getElem_mem_toList hj)
  have hc := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 y.2).2 a ha
  rw [hyv] at hc
  exact (peq_iff (prep_pcomp (prep_pcomp prep_mPerm (prep_qPow k)) hrep.2)
    (prep_pcomp hrep.2 (prep_pcomp prep_mPerm (prep_qPow k)))).2 hc.symm

theorem card_rhoMA_range_le :
    Nat.card rhoMA.range ≤ 72 := by
  have hdvd := Subgroup.card_dvd_of_le rhoMA_range_le
  rw [card_kA] at hdvd
  have hlt : Nat.card rhoMA.range ≠ 144 := by
    intro h
    have := Subgroup.eq_of_le_of_card_ge rhoMA_range_le (by rw [h, card_kA])
    exact rho_mPerm_not_mem (this ▸ rho_mPerm_mem)
  obtain ⟨e, he⟩ := hdvd
  rcases e with _ | _ | e
  · omega
  · omega
  · nlinarith

theorem card_rhoMA_ker_le :
    Nat.card rhoMA.ker ≤ 2 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h14⟩ := r3e_elem_cert
  have hmem : ∀ y ∈ rhoMA.ker, ((y : cMA) : Equiv.Perm (Fin N)) ∈ ({1, onz} : Finset _) := by
    intro y hy
    have hQ := mem_ker_cases _ hy
    have hc : ∀ a ∈ onA, ((y : cMA) : Equiv.Perm (Fin N)) * a = a * ((y : cMA) :
        Equiv.Perm (Fin N)) := fun a ha =>
      (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 y.2).2 a ha).symm
    rcases q_cases hQ with h | h | h | h
    · simp [h]
    · exfalso
      rw [Array.all_eq_true] at h14
      have := h14 0 (by decide)
      simp only [Bool.not_eq_true', ← Bool.not_eq_true, Array.all_eq_true] at this
      apply this
      intro j hj
      obtain ⟨a, ha, hrep⟩ := a_enumerates.sound aTabs[j] (Array.getElem_mem_toList hj)
      have := hc a ha
      rw [h] at this
      exact (peq_iff (prep_pcomp (prep_qPow 1) hrep.2) (prep_pcomp hrep.2 (prep_qPow 1))).2
        (by rw [pow_one]; exact this)
    · simp [h, ← onz_eq_q2]
    · exfalso
      rw [Array.all_eq_true] at h14
      have := h14 1 (by decide)
      simp only [Bool.not_eq_true', ← Bool.not_eq_true, Array.all_eq_true] at this
      apply this
      intro j hj
      obtain ⟨a, ha, hrep⟩ := a_enumerates.sound aTabs[j] (Array.getElem_mem_toList hj)
      have := hc a ha
      rw [h] at this
      exact (peq_iff (prep_pcomp (prep_qPow 3) hrep.2) (prep_pcomp hrep.2 (prep_qPow 3))).2 this
  calc Nat.card rhoMA.ker ≤ Nat.card ({1, onz} : Finset (Equiv.Perm (Fin N))) :=
        Nat.card_le_card_of_injective (fun y => ⟨((y : cMA) : Equiv.Perm (Fin N)), hmem y y.2⟩)
          fun a b h => by
            apply Subtype.ext; apply Subtype.ext
            simpa using congrArg Subtype.val h
    _ = ({1, onz} : Finset (Equiv.Perm (Fin N))).card := Nat.card_eq_finsetCard _
    _ ≤ 2 := Finset.card_le_two

theorem card_cMA :
    Nat.card cMA = 144 := by
  apply le_antisymm
  · rw [card_range_mul_ker rhoMA]
    calc Nat.card rhoMA.range * Nat.card rhoMA.ker ≤ 72 * 2 :=
          Nat.mul_le_mul card_rhoMA_range_le card_rhoMA_ker_le
      _ = 144 := rfl
  · rw [← card_onH]
    exact Subgroup.card_le_of_le onH_le

theorem onH_eq :
    onH = cMA :=
  Subgroup.eq_of_le_of_card_ge onH_le (by rw [card_cMA, card_onH])

@[expose] def vM :
    onM := ⟨onv, onv_mem_M⟩

@[expose] def hM :
    onM := ⟨onh, onh_mem⟩

theorem prep_vinv :
    PRep N (pinvCand nPts vArr) onv⁻¹ := prep_inv_of_pisInv prep_v r3e_inv_cert

theorem prep_hvhv :
    PRep N hvhvArr (onh⁻¹ * onv * onh * onv⁻¹) := by
  have := prep_pcomp prep_hinv (prep_pcomp prep_v (prep_pcomp prep_h prep_vinv))
  rw [show onh⁻¹ * onv * onh * onv⁻¹ = onh⁻¹ * (onv * (onh * onv⁻¹)) by group]
  exact this

theorem prep_hpow :

    ∀ k, PRep N (Nat.repeat (pcomp nPts hArr) k (pid nPts)) (onh ^ k)
  | 0 => by rw [Nat.repeat, pow_zero]; exact prep_pid
  | k + 1 => by rw [Nat.repeat, pow_succ']; exact prep_pcomp prep_h (prep_hpow k)

theorem onh_pow7 :
    onh ^ 7 = 1 := by
  obtain ⟨-, -, -, h4, -⟩ := r3e_elem_cert
  exact eq_of_peq (prep_hpow 7) prep_pid h4

theorem repeat_hc
    {c : Equiv.Perm (Fin N)} {t : Array ℕ} (ht : TabRep t c) :
    ∀ k p (hp : p < N), Nat.repeat (fun x => hArr[t[x]!]!) k p = (((onh * c) ^ k) ⟨p, hp⟩ : ℕ)
  | 0, p, hp => by rw [Nat.repeat, pow_zero]; rfl
  | k + 1, p, hp => by
    rw [Nat.repeat, repeat_hc ht k p hp, pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    rw [ht.apply, prep_h]

theorem order7_ne
    {c : Equiv.Perm (Fin N)} {t : Array ℕ} (ht : TabRep t c)
    (h : order7Moves t = true) : (onh * c) ^ 7 ≠ 1 := by
  intro h1
  rw [order7Moves, Array.any_eq_true] at h
  obtain ⟨j, hj, hne⟩ := h
  have hp : (#[0, 227759, 100817] : Array ℕ)[j] < N := by
    have : j < 3 := by simpa using hj
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl <;> simp <;> norm_num
  rw [repeat_hc ht 7 _ hp, h1, Equiv.Perm.one_apply, bne_self_eq_false] at hne
  exact absurd hne (by decide)

theorem gen_set_top :

    Subgroup.closure {x : onM | (x : Equiv.Perm (Fin N)) ∈ onD ∨ x = hM} = ⊤ := by
  apply Subgroup.map_injective onM.subtype_injective
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  conv_rhs => rw [onM_eq_closure]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq, Subgroup.coe_subtype, Set.mem_union,
    SetLike.mem_coe, Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, hy | hy, rfl⟩
    · exact Or.inl hy
    · exact Or.inr (by rw [hy]; rfl)
  · rintro (hx | hx)
    · exact ⟨⟨x, onD_le_M hx⟩, Or.inl hx, rfl⟩
    · exact ⟨hM, Or.inr rfl, hx.symm⟩

theorem mulAut_ext
    {β γ : MulAut onM} (hD : ∀ d : onM, (d : Equiv.Perm (Fin N)) ∈ onD → β d = γ d)
    (hh : β hM = γ hM) : β = γ := by
  apply MulEquiv.toMonoidHom_injective
  apply MonoidHom.eq_of_eqOn_dense gen_set_top
  rintro x (hx | rfl)
  · exact hD x hx
  · exact hh

theorem conj_v_fixes
    {d : onM} (hd : (d : Equiv.Perm (Fin N)) ∈ onD) : MulAut.conj vM d = d := by
  apply Subtype.ext
  simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, vM]
  have := Subgroup.mem_centralizer_singleton_iff.1 (onv_centralizes_D hd)
  rw [← this, mul_assoc, mul_inv_cancel, mul_one]

theorem pointwise_cases
    (β : MulAut onM)
    (hβ : ∀ d : onM, (d : Equiv.Perm (Fin N)) ∈ onD → β d = d) :
    β = 1 ∨ β = MulAut.conj vM := by
  set y := β hM with hy
  set c : onM := hM⁻¹ * y with hc
  have hcA : (c : Equiv.Perm (Fin N)) ∈ cMA := by
    refine Subgroup.mem_inf.2 ⟨c.2, Subgroup.mem_centralizer_iff.2 fun a ha => ?_⟩
    obtain ⟨haD, haK⟩ := Subgroup.mem_inf.1 ha
    have hhaD : onh * a * onh⁻¹ ∈ onD := conj_mem_D_iff.2 haK
    set aM : onM := ⟨a, onD_le_M haD⟩
    have h1 : β aM = aM := hβ aM haD
    have h2 : β (hM * aM * hM⁻¹) = hM * aM * hM⁻¹ := hβ _ hhaD
    rw [map_mul, map_mul, map_inv, h1] at h2
    have h3 : c * aM = aM * c := by
      calc c * aM = hM⁻¹ * (y * aM * y⁻¹) * y := by rw [hc]; group
        _ = hM⁻¹ * (hM * aM * hM⁻¹) * y := by rw [h2]
        _ = aM * c := by rw [hc]; group
    exact (congrArg Subtype.val h3).symm
  rw [← onH_eq] at hcA
  obtain ⟨t, htmem, hrep⟩ := h_enumerates.complete _ hcA
  obtain ⟨k, hk, rfl⟩ := CFSG.ComponentClassification.PSL3Four.exists_getElem!_of_mem htmem
  have hall := r3e_enum_cert.2.2.2.2.2.2.2.2
  rw [Array.all_eq_true] at hall
  have hk' := hall k hk
  rw [← getElem!_pos hEnum.tabs k hk] at hk'
  simp only [Bool.or_eq_true, beq_iff_eq] at hk'
  have hyc : y = hM * c := by rw [hc, mul_inv_cancel_left]
  rcases hk' with (h1 | h1) | h1
  · left
    rw [h1] at hrep
    have hc1 : c = 1 := Subtype.ext (hrep.perm_eq (tabRep_of_prep (by simp [pid]) prep_pid))
    apply mulAut_ext (fun d hd => by rw [hβ d hd]; rfl)
    rw [MulAut.one_apply, ← hy, hyc, hc1, mul_one]
  · right
    rw [h1] at hrep
    have hcv : (c : Equiv.Perm (Fin N)) = onh⁻¹ * onv * onh * onv⁻¹ :=
      hrep.perm_eq (tabRep_of_prep (by
        rw [hvhvArr]; simp [pcomp]) prep_hvhv)
    apply mulAut_ext (fun d hd => by rw [hβ d hd, conj_v_fixes hd])
    apply Subtype.ext
    rw [← hy, hyc]
    simp only [Subgroup.coe_mul, MulAut.conj_apply, Subgroup.coe_inv, hcv, hM, vM]
    group
  · exfalso
    apply order7_ne hrep h1
    have : y ^ 7 = 1 := by
      rw [hy, ← map_pow, show hM ^ 7 = 1 from Subtype.ext (by
        simp only [Subgroup.coe_pow, hM, onh_pow7, Subgroup.coe_one]), map_one]
    have h7 := congrArg Subtype.val this
    rw [hyc] at h7
    simpa [hM] using h7

theorem pointwise_eq :
    {β : MulAut onM | ∀ d : onM, (d : Equiv.Perm (Fin N)) ∈ onD → β d = d} =
      {1, MulAut.conj vM} := by
  ext β
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · exact pointwise_cases β
  · rintro (rfl | rfl)
    · intro d _
      rfl
    · intro d hd
      exact conj_v_fixes hd

theorem conj_v_ne_one :
    MulAut.conj vM ≠ 1 := by
  intro h
  have := congrArg (fun β : MulAut onM => ((β hM : onM) : Equiv.Perm (Fin N))) h
  simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, MulAut.one_apply, vM,
    hM] at this
  apply onv_not_comm_h
  calc onv * onh = onv * onh * onv⁻¹ * onv := by group
    _ = onh * onv := by rw [this]

theorem r3e_on_local_intersection_pointwise_automorphisms :
    onD ≤ onM ∧ Nat.card onD = 144 ∧ CFSG.centerIn onM = Subgroup.zpowers onz ∧
      Nat.card (CFSG.centerIn onM) = 2 ∧ onv ∈ onM ∧ orderOf onv = 2 ∧
      Nat.card (onM ⊓ Subgroup.centralizer (onD : Set (Equiv.Perm (Fin N))) :
        Subgroup (Equiv.Perm (Fin N))) = 4 ∧
      onM = Subgroup.closure ((onD : Set (Equiv.Perm (Fin N))) ∪ {onh}) ∧
      Nat.card (onD ⊓ onD.map (MulAut.conj onh⁻¹).toMonoidHom : Subgroup (Equiv.Perm (Fin N))) =
        4 ∧
      Nat.card (onM ⊓ Subgroup.centralizer ((onD ⊓ onD.map (MulAut.conj onh⁻¹).toMonoidHom :
        Subgroup (Equiv.Perm (Fin N))) : Set (Equiv.Perm (Fin N))) :
          Subgroup (Equiv.Perm (Fin N))) = 144 ∧
      {β : MulAut onM | ∀ d : onM, (d : Equiv.Perm (Fin N)) ∈ onD → β d = d} =
        {1, MulAut.conj (⟨onv, onv_mem_M⟩ : onM)} ∧
      MulAut.conj (⟨onv, onv_mem_M⟩ : onM) ≠ 1 :=
  ⟨onD_le_M, card_onD, onM_centerIn, card_onM_centerIn, onv_mem_M, orderOf_onv, card_cMD,
    onM_eq_closure, card_onA, card_cMA, pointwise_eq, conj_v_ne_one⟩

end CFSG.ONSchreier
