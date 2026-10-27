module

public import CFSG.Sporadic.Schreier.RuLocalRes

public noncomputable section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

@[expose] def ruImF
    (K : Subgroup (Equiv.Perm (Fin 4060))) : Subgroup (Equiv.Perm (Fin 1920)) :=
  (K.subgroupOf ruC).map ruResF

theorem card_ruImF
    {K : Subgroup (Equiv.Perm (Fin 4060))} (hK : K ≤ ruC) :
    Nat.card (ruImF K) = Nat.card K := by
  rw [ruImF, Subgroup.card_map_of_injective ruResF_injective]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv

theorem mem_of_ruImF
    {K : Subgroup (Equiv.Perm (Fin 4060))} {x : Equiv.Perm (Fin 4060)}
    (hx : x ∈ ruC) (h : ruResFPerm x ∈ ruImF K) : x ∈ K := by
  obtain ⟨y, hy, hxy⟩ := h
  rw [ruResFPerm_of_mem hx] at hxy
  have hyx := ruResF_injective hxy
  have hy' : (y : Equiv.Perm (Fin 4060)) ∈ K := Subgroup.mem_subgroupOf.1 hy
  rw [hyx] at hy'
  exact hy'

theorem ruImF_eq
    {l : List (Equiv.Perm (Fin 4060))} (hl : ∀ g ∈ l, g ∈ ruC) :
    ruImF (Subgroup.closure {g | g ∈ l}) =
      Subgroup.closure {h | h ∈ (List.range l.length).map fun i => ruResFPerm (l.getD i 1)} :=
  closure_res_list ruResF ruResFPerm (fun _ hg => ruResFPerm_of_mem hg) hl rfl

theorem ruChainS_sub :
    ruChainS.originalSubgroup = ruImF ruS := by
  have h := ruChainS_check.1
  rw [RawSchreierDatum.originalSubgroup,
    show ruChainS.original.toList = (List.range 4).map fun i => permOfArr 1920
      (ruField1920 1)[i]! from ofArrays_original_toList,
    chain1920_original ruSGens_memC ruSGens_length rep_ruSGens
      (fun i hi => ruChain_strong_inv h (by simp [ruField1920, ruLines1920]; omega))
      ruGens_check.2.2.2.2.2.2.2.2.2.2.1, ruS, ruImF_eq ruSGens_memC, ruSGens_length]

theorem ruKGens_length : ruKGens.length = 8 := by simp [ruKGens, ruKWords]

theorem ruJGens_length : ruJGens.length = 6 := by simp [ruJGens, ruJWords]

theorem ruRGens_length : ruRGens.length = 5 := by simp [ruRGens, ruRWords]

theorem ruChainK_sub :
    ruChainK.originalSubgroup = ruImF ruK := by
  have h := ruChainK_check.1
  rw [RawSchreierDatum.originalSubgroup,
    show ruChainK.original.toList = (List.range 8).map fun i => permOfArr 1920
      (ruField1920 2)[i]! from ofArrays_original_toList,
    chain1920_original ruKGens_memC ruKGens_length rep_ruKGens
      (fun i hi => ruChain_strong_inv h (by simp [ruField1920, ruLines1920]; omega))
      ruGens_check.2.2.2.2.2.2.2.2.2.2.2.1, ruK, ruImF_eq ruKGens_memC, ruKGens_length]

theorem ruChainJ_sub :
    ruChainJ.originalSubgroup = ruImF ruJ := by
  have h := ruChainJ_check.1
  rw [RawSchreierDatum.originalSubgroup,
    show ruChainJ.original.toList = (List.range 6).map fun i => permOfArr 1920
      (ruField1920 3)[i]! from ofArrays_original_toList,
    chain1920_original ruJGens_memC ruJGens_length rep_ruJGens
      (fun i hi => ruChain_strong_inv h (by simp [ruField1920, ruLines1920]; omega))
      ruGens_check.2.2.2.2.2.2.2.2.2.2.2.2.1, ruJ, ruImF_eq ruJGens_memC, ruJGens_length]

theorem ruChainR_sub :
    ruChainR.originalSubgroup = ruImF ruR := by
  have h := ruChainR_check.1
  rw [RawSchreierDatum.originalSubgroup,
    show ruChainR.original.toList = (List.range 5).map fun i => permOfArr 1920
      (ruField1920 4)[i]! from ofArrays_original_toList,
    chain1920_original ruRGens_memC ruRGens_length rep_ruRGens
      (fun i hi => ruChain_strong_inv h (by simp [ruField1920, ruLines1920]; omega))
      ruGens_check.2.2.2.2.2.2.2.2.2.2.2.2.2.1, ruR, ruImF_eq ruRGens_memC, ruRGens_length]

theorem card_ruS :
    Nat.card ruS = 16384 := by
  have h : Nat.card ruChainS.originalSubgroup = _ := ruChain_card ruChainS_check.1
  rw [ruChainS_check.2.1, ruChainS_sub, card_ruImF ruS_leC] at h
  exact h

theorem card_ruK :
    Nat.card ruK = 2048 := by
  have h : Nat.card ruChainK.originalSubgroup = _ := ruChain_card ruChainK_check.1
  rw [ruChainK_check.2.1, ruChainK_sub, card_ruImF ruK_leC] at h
  exact h

theorem card_ruJ :
    Nat.card ruJ = 2048 := by
  have h : Nat.card ruChainJ.originalSubgroup = _ := ruChain_card ruChainJ_check.1
  rw [ruChainJ_check.2.1, ruChainJ_sub, card_ruImF ruJ_leC] at h
  exact h

theorem card_ruR :
    Nat.card ruR = 2048 := by
  have h : Nat.card ruChainR.originalSubgroup = _ := ruChain_card ruChainR_check.1
  rw [ruChainR_check.2.1, ruChainR_sub, card_ruImF ruR_leC] at h
  exact h

theorem mem_of_sift1920
    {K : Subgroup (Equiv.Perm (Fin 4060))} {Q : RawSchreierDatum 1920}
    (hQ : Q.originalSubgroup = ruImF K) {g : Equiv.Perm (Fin 4060)} (hg : g ∈ ruC)
    (hsift : ruResFPerm g ∈ Q.originalSubgroup) : g ∈ K := by
  rw [hQ] at hsift
  exact mem_of_ruImF hg hsift

theorem ruJ_leS :
    ruJ ≤ ruS := closure_list_le fun g hg => by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hg
  have hi6 : i < 6 := by rw [ruJGens_length] at hi; exact hi
  rw [← List.getD_eq_getElem ruJGens 1 hi]
  have hmem := ruJGens_memC _ (List.getD_eq_getElem ruJGens 1 hi ▸ List.getElem_mem hi)
  exact mem_of_sift1920 ruChainS_sub hmem
    ((ruChain_sift ruChainS_check.1 (rep_ruResF (rep_ruJGens i hi6) hmem)).1
      (ruChainS_check.2.2.1 i hi6))

theorem ruK_leS :
    ruK ≤ ruS := closure_list_le fun g hg => by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hg
  have hi8 : i < 8 := by rw [ruKGens_length] at hi; exact hi
  rw [← List.getD_eq_getElem ruKGens 1 hi]
  have hmem := ruKGens_memC _ (List.getD_eq_getElem ruKGens 1 hi ▸ List.getElem_mem hi)
  exact mem_of_sift1920 ruChainS_sub hmem
    ((ruChain_sift ruChainS_check.1 (rep_ruResF (rep_ruKGens i hi8) hmem)).1
      (ruChainS_check.2.2.2 i hi8))

theorem ruZ_memJ :
    ruZ ∈ ruJ :=
  mem_of_sift1920 ruChainJ_sub ruZ_memC
    ((ruChain_sift ruChainJ_check.1 (rep_ruResF rep_ruZ ruZ_memC)).1 ruChainJ_check.2.2)

theorem ruZ_memK :
    ruZ ∈ ruK :=
  mem_of_sift1920 ruChainK_sub ruZ_memC
    ((ruChain_sift ruChainK_check.1 (rep_ruResF rep_ruZ ruZ_memC)).1 ruChainK_check.2.2)

theorem ruZ_memR :
    ruZ ∈ ruR :=
  mem_of_sift1920 ruChainR_sub ruZ_memC
    ((ruChain_sift ruChainR_check.1 (rep_ruResF rep_ruZ ruZ_memC)).1 ruChainR_check.2.2)

theorem ruZ_ne_one : ruZ ≠ 1 := by
  intro h
  have := ruZ_check.1
  rw [(eqA_iff rep_ruZ rep_idA).2 h] at this
  exact Bool.noConfusion this

theorem ruZ_sq : ruZ ^ 2 = 1 := by
  rw [pow_two]
  exact eq_of_eqA (rep_compA rep_ruZ rep_ruZ) rep_idA ruZ_check.2.1

theorem orderOf_ruZ :
    orderOf ruZ = 2 :=
  orderOf_eq_prime ruZ_sq ruZ_ne_one

theorem ruZ_comm_C0 :
    ruZ * ruC0 = ruC0 * ruZ :=
  eq_of_eqA (rep_compA rep_ruZ rep_ruC0) (rep_compA rep_ruC0 rep_ruZ) ruZ_check.2.2.1

theorem ruZ_comm_C1 :
    ruZ * ruC1 = ruC1 * ruZ :=
  eq_of_eqA (rep_compA rep_ruZ rep_ruC1) (rep_compA rep_ruC1 rep_ruZ) ruZ_check.2.2.2.1

theorem ruZ_central :
    ∀ g ∈ ruC, g * ruZ = ruZ * g := by
  have hle : ruC ≤ Subgroup.centralizer {ruZ} := by
    apply closure_pair_le
    · exact Subgroup.mem_centralizer_singleton_iff.2 ruZ_comm_C0.symm
    · exact Subgroup.mem_centralizer_singleton_iff.2 ruZ_comm_C1.symm
  intro g hg
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hg)

theorem ruResY_ruZ :
    ruResY ⟨ruZ, ruZ_memC⟩ = 1 := by
  have hrep := rep_ruResY rep_ruZ ruZ_memC
  rw [ruResYPerm_of_mem ruZ_memC] at hrep
  apply Equiv.ext
  intro i
  apply Fin.ext
  rw [← hrep i, Equiv.Perm.one_apply, resA, getElem!_ofFn_nat _ (by rw [ruY_size]; exact i.2)]
  have hi : (i : ℕ) < ruY.size := by rw [ruY_size]; exact i.2
  rw [ruZ_check.2.2.2.2 i i.2]
  exact (ptPosOK_spec ruOrbits_check.2.1).2 i hi

theorem ruResY_ker :
    ruResY.ker = Subgroup.zpowers ⟨ruZ, ruZ_memC⟩ := by
  symm
  apply Subgroup.eq_of_le_of_card_ge
  · rw [Subgroup.zpowers_le]
    exact ruResY_ruZ
  · have h1 := card_ker_mul_card_range ruResY
    rw [card_ruResY_range, card_ruC] at h1
    have h2 : Nat.card ruResY.ker = 2 :=
      Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 122880) (h1.trans (by norm_num))
    rw [h2, Nat.card_zpowers, Subgroup.orderOf_mk, orderOf_ruZ]

end CFSG.Sporadic.RuSchreier
