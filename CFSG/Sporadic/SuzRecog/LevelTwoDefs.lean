
module

public import CFSG.Sporadic.SuzRecog.LevelTwoDefsBase

public import Certificates.Certificate15090

public section

namespace CFSG.Sporadic.SuzRecog.LevelTwo

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog.LevelTwoData

theorem chain_check : chainOK = true :=
  Certificates.certificate15090.1

theorem basic_check : basicOK = true :=
  Certificates.certificate15090.2.1

theorem a_check : aOK = true :=
  Certificates.certificate15090.2.2.1

theorem v_check : vOK = true :=
  Certificates.certificate15090.2.2.2.1

theorem graph_check : graphOK = true :=
  Certificates.certificate15090.2.2.2.2.1

theorem elim_check : elimOK = true :=
  Certificates.certificate15090.2.2.2.2.2.1

theorem loc_check : locOK = true :=
  Certificates.certificate15090.2.2.2.2.2.2.1

theorem tri_check : triOK = true :=
  Certificates.certificate15090.2.2.2.2.2.2.2.1

theorem class_check : classOK = true :=
  Certificates.certificate15090.2.2.2.2.2.2.2.2.1

theorem group_check : groupOK = true :=
  Certificates.certificate15090.2.2.2.2.2.2.2.2.2

theorem basicOK_parts :
    isInvA 1782 rhoArr rhoInv = true ∧
    eqA 1782 (compA 1782 rhoArr (compA 1782 rhoArr rhoArr)) (idA 1782) = true ∧
    eqA 1782 rhoArr (idA 1782) = false ∧ memX rhoArr = true ∧
    (∀ s < 2, isInvA 1782 gens[s]! gensInv[s]! = true ∧ commA gens[s]! rhoArr = true ∧
      inM gens[s]! = true) ∧
    isInvA 1782 t1Arr t1Arr = true ∧ memX t1Arr = true ∧ isInvA 1782 w0Arr w0Arr = true ∧
    commA w0Arr t1Arr = true ∧ commA w0Arr (rhoConj w0Arr) = true ∧
    eqA 1782 w0Arr (rhoConj w0Arr) = false := by
  have h := basic_check
  simp only [basicOK, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  refine ⟨h1, h2, h3, h4, fun s hs => ?_, h6, h7, h8, h9, h10, h11⟩
  have := allLt_spec h5 hs
  simp only [Bool.and_eq_true] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

theorem rep_gens {s : ℕ} (hs : s < 2) :
    Rep 1782 gens[s]! (permC 1782 gens[s]!) ∧ Rep 1782 gensInv[s]! (permC 1782 gens[s]!)⁻¹ :=
  rep_permC (basicOK_parts.2.2.2.2.1 s hs).1

theorem rep_x1 : Rep 1782 gens[0]! x1 :=
  (rep_gens (s := 0) (by norm_num)).1

theorem rep_x2 : Rep 1782 gens[1]! x2 :=
  (rep_gens (s := 1) (by norm_num)).1

theorem rep_rho1 : Rep 1782 rhoArr Model.rho1 :=
  (rep_permC basicOK_parts.1).1

theorem rep_rhoInv : Rep 1782 rhoInv Model.rho1⁻¹ :=
  (rep_permC basicOK_parts.1).2

theorem chainOK_parts :
    rawChainOK 1782 gens xStrongArrs xBase.toArray xWords 4 = true ∧
      rawOrbitSizes 1782 xStrongArrs xBase.toArray = [162, 105, 64, 3, 3] := by
  have h := chain_check
  simp only [chainOK, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.2, h.2⟩

theorem xChain_arrays :
    ChainArrays xChain gens xStrongArrs xBase.toArray xWords := by
  rw [← xBaseFin_vals]
  refine chainArrays_rawOfArrays (fun k hk => ?_) (fun j hj => ?_)
  · rw [gens_size] at hk
    have := (basicOK_parts.2.2.2.2.1 k hk).1
    rwa [gensInv_get hk] at this
  · have := (chainCheckFacts chainOK_parts.1).strong_inv j hj
    rwa [rawInvs, getElem!_map_nat _ hj] at this

theorem card_xGroup : Nat.card xGroup = 9797760 := by
  rw [← xChain_originalSubgroup, card_originalSubgroup_of_chainOK xChain_arrays (by norm_num)
    chainOK_parts.1, chainOK_parts.2]
  rfl

theorem mem_xGroup_of_memX {g : Array ℕ}
    {G : Equiv.Perm (Fin 1782)} (hG : Rep 1782 g G) (h : memX g = true) : G ∈ xGroup := by
  rw [← xChain_originalSubgroup]
  exact (siftA_iff_mem_originalSubgroup xChain_arrays (by norm_num) chainOK_parts.1 hG).1 h

theorem gens_comm_rho1 {s : ℕ} (hs : s < 2) :
    permC 1782 gens[s]! * Model.rho1 = Model.rho1 * permC 1782 gens[s]! := by
  have h := (basicOK_parts.2.2.2.2.1 s hs).2.1
  rw [commA] at h
  exact eq_of_eqA (rep_compA (rep_gens hs).1 rep_rho1) (rep_compA rep_rho1 (rep_gens hs).1) h

theorem x1_comm_rho1 : x1 * Model.rho1 = Model.rho1 * x1 :=
  gens_comm_rho1 (s := 0) (by norm_num)

theorem x2_comm_rho1 : x2 * Model.rho1 = Model.rho1 * x2 :=
  gens_comm_rho1 (s := 1) (by norm_num)

theorem gens_mem_suzM
    {s : ℕ} (hs : s < 2) : permC 1782 gens[s]! ∈ suzM :=
  (mem_suzM_iff_siftA (rep_gens hs).1).1 (basicOK_parts.2.2.2.2.1 s hs).2.2

theorem x1_mem_suzM :
    x1 ∈ suzM :=
  gens_mem_suzM (s := 0) (by norm_num)

theorem x2_mem_suzM :
    x2 ∈ suzM :=
  gens_mem_suzM (s := 1) (by norm_num)

theorem xGroup_le_centralizer :
    xGroup ≤ Subgroup.centralizer {Model.rho1} :=
  (Subgroup.closure_le _).2 (Set.pair_subset_iff.2
    ⟨Subgroup.mem_centralizer_singleton_iff.2 x1_comm_rho1,
      Subgroup.mem_centralizer_singleton_iff.2 x2_comm_rho1⟩)

theorem xGroup_le_suzM :
    xGroup ≤ suzM :=
  (Subgroup.closure_le _).2 (Set.pair_subset_iff.2 ⟨x1_mem_suzM, x2_mem_suzM⟩)

theorem xGroup_le_Crho1 :
    xGroup ≤ Model.Crho1 :=
  le_inf xGroup_le_centralizer xGroup_le_suzM

theorem classOK_parts :
    Q3A.Check.q3aOK = true ∧
      isInvA 1782 ModelGroupsData.s1Arr (invCand 1782 ModelGroupsData.s1Arr) = true ∧
      inM ModelGroupsData.s1Arr = true ∧
      conjEq ModelGroupsData.s1Arr (invCand 1782 ModelGroupsData.s1Arr) rhoArr
        (compA 1782 rhoArr rhoArr) = true := by
  have h := class_check
  simp only [classOK, Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem rho1_cube : Model.rho1 * Model.rho1 * Model.rho1 = 1 := by
  have := eq_of_eqA (rep_compA rep_rho1 (rep_compA rep_rho1 rep_rho1)) rep_idA basicOK_parts.2.1
  rwa [← mul_assoc] at this

theorem rho1_ne_one : Model.rho1 ≠ 1 := by
  intro h
  have := (eqA_iff rep_rho1 rep_idA).2 h
  rw [basicOK_parts.2.2.1] at this
  exact Bool.false_ne_true this

theorem exists_inverting :
    ∃ s ∈ suzM, s * Model.rho1 * s⁻¹ = Model.rho1 * Model.rho1 := by
  obtain ⟨-, hi, hm, hc⟩ := classOK_parts
  obtain ⟨hs, hsi⟩ := rep_permC hi
  exact ⟨_, (mem_suzM_iff_siftA hs).1 hm,
    (eq_of_conjEq hs hsi rep_rho1 (rep_compA rep_rho1 rep_rho1) hc).symm⟩

theorem card_Crho1_le :
    Nat.card Model.Crho1 ≤ 9797760 := by
  set N := Subgroup.normalizer (Q3A.base : Set (Equiv.Perm (Fin 1782))) ⊓ suzM
  obtain ⟨s, hsM, hs⟩ := exists_inverting
  have hle : Model.Crho1 ≤ N := fun x hx => by
    obtain ⟨hc, hm⟩ := Subgroup.mem_inf.1 hx
    exact Subgroup.mem_inf.2
      ⟨Q3A.mem_normalizer_of_comm (Subgroup.mem_centralizer_singleton_iff.1 hc), hm⟩
  have hz : Subgroup.zpowers (Model.rho1 * Model.rho1) = Q3A.base := by
    refine le_antisymm ((Subgroup.zpowers_le).2 (mul_mem (Subgroup.mem_zpowers _)
      (Subgroup.mem_zpowers _))) ((Subgroup.zpowers_le).2 ?_)
    have e : Model.rho1 = (Model.rho1 * Model.rho1) * (Model.rho1 * Model.rho1) := by
      rw [show (Model.rho1 * Model.rho1) * (Model.rho1 * Model.rho1) =
        (Model.rho1 * Model.rho1 * Model.rho1) * Model.rho1 by group, rho1_cube, one_mul]
    have := mul_mem (Subgroup.mem_zpowers (Model.rho1 * Model.rho1))
      (Subgroup.mem_zpowers (Model.rho1 * Model.rho1))
    rwa [← e] at this
  have hsN : s ∈ N := by
    refine Subgroup.mem_inf.2 ⟨(Q3A.smul_v0_eq_iff ⟨s, hsM⟩).1 (Subtype.ext ?_), hsM⟩
    rw [Q3A.coe_smul_v0]
    change Subgroup.zpowers (s * Model.rho1 * s⁻¹) = Q3A.base
    rw [hs, hz]
  have hsC : s ∉ Model.Crho1 := fun h => by
    have hc := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 h).1
    have : Model.rho1 * Model.rho1 = Model.rho1 := by
      rw [← hs, hc, mul_assoc, mul_inv_cancel, mul_one]
    exact rho1_ne_one (by simpa using this)
  have hdvd := Subgroup.card_dvd_of_le hle
  have hne : Nat.card Model.Crho1 ≠ Nat.card N := fun h =>
    hsC ((Subgroup.eq_of_le_of_card_ge hle h.symm.le) ▸ hsN)
  have hNpos : 0 < Nat.card N := Nat.card_pos
  obtain ⟨k, hk⟩ := hdvd
  have hk2 : 2 ≤ k := by
    rcases k with _ | _ | k
    · rw [mul_zero] at hk
      omega
    · rw [zero_add, mul_one] at hk
      exact absurd hk.symm hne
    · omega
  have h1 : Nat.card N ≤ 19595520 := card_Nrho1_le
  have h2 : Nat.card Model.Crho1 * 2 ≤ Nat.card N := by
    rw [hk]
    exact Nat.mul_le_mul_left _ hk2
  omega

theorem xGroup_eq_Crho1 :
    xGroup = Model.Crho1 :=
  Subgroup.eq_of_le_of_card_ge xGroup_le_Crho1 (by rw [card_xGroup]; exact card_Crho1_le)

end CFSG.Sporadic.SuzRecog.LevelTwo
