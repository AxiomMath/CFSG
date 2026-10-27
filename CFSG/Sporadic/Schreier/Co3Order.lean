module

public import CFSG.Sporadic.Schreier.Co3Faithful
public import CFSG.Sporadic.Schreier.Co3OrderCheck
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.Sporadic.Schreier.Co3ChainUtil

public noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Schreier.Co3

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.Co3.Native

theorem co3ChainArrays :
    ChainArrays co3Chain (co3ChainArrs.extract 0 co3ChainGenCount)
    co3ChainArrs co3ChainBaseArr
    (wordsArr co3ChainGenCount co3ChainStrongCount co3ChainDerivations) :=
  chainArrays_ofArrays co3ChainArrs_inv

theorem co3CoprimeArrays : ChainArrays co3CoprimeChain
    (co3CoprimeArrs.extract 0 co3CoprimeGenCount) co3CoprimeArrs co3CoprimeBaseArr
    (wordsArr co3CoprimeGenCount co3CoprimeStrongCount co3CoprimeDerivations) :=
  chainArrays_ofArrays co3CoprimeArrs_inv

theorem co3Chain_valid :
    ValidSchreier co3Chain ∧ ∀ i : Fin co3Chain.baseCount,
    co3Chain.orbitSize i = ((rawLevels 276 co3ChainArrs co3ChainBaseArr)[(i : ℕ)]!).pts.size :=
  validSchreier_of_chainOK co3ChainArrays (by norm_num) co3Order_check.1

theorem co3Coprime_valid :
    ValidSchreier co3CoprimeChain ∧ ∀ i : Fin co3CoprimeChain.baseCount,
    co3CoprimeChain.orbitSize i =
      ((rawLevels 276 co3CoprimeArrs co3CoprimeBaseArr)[(i : ℕ)]!).pts.size :=
  validSchreier_of_chainOK co3CoprimeArrays (by norm_num) co3Coprime_check.1

theorem co3Chain_orbitSizes :
    (List.finRange co3Chain.baseCount).map co3Chain.orbitSize = [276, 275, 112, 81, 20, 18, 2] := by
  rw [orbitSizes_eq_of_valid (by rfl) co3Chain_valid.2, co3Order_check.2.1]

theorem co3Coprime_orbitSizes :
    (List.finRange co3CoprimeChain.baseCount).map co3CoprimeChain.orbitSize =
      [276, 275, 112, 81, 20, 18, 2] := by
  rw [orbitSizes_eq_of_valid (by rfl) co3Coprime_valid.2, co3Coprime_check.2]

theorem card_co3P :
    Nat.card co3P = 495766656000 := by
  rw [co3P, card_originalSubgroup_of_chainOK co3ChainArrays (by norm_num) co3Order_check.1,
    co3Order_check.2.1]
  rfl

theorem card_co3CoprimeChain :
    Nat.card co3CoprimeChain.originalSubgroup = 495766656000 := by
  rw [card_originalSubgroup_of_chainOK co3CoprimeArrays (by norm_num) co3Coprime_check.1,
    co3Coprime_check.2]
  rfl

@[expose] def co3CoprimePerm (k : ℕ) : Equiv.Perm (Fin 276) := permOfArr 276 co3CoprimeArrs[k]!

theorem rep_co3CoprimePerm {k : ℕ} (hk : k < 14) :
    Rep 276 co3CoprimeArrs[k]! (co3CoprimePerm k) :=
  (rep_permOfArr (co3CoprimeArrs_inv k (by rw [co3CoprimeArrs_size]; exact hk))).1

theorem rep_co3WordValue :
    Rep 276 co3WordArr co3WordValue := by
  have h := rep_wordA (gs := co3StrongPerm) (j := 2)
    (fun h hh => rep_co3StrongPerm (by omega))
    (fun h hh => rep_inv_of_isInvA (rep_co3StrongPerm (by omega))
      (co3ChainArrs_inv h (by rw [co3ChainArrs_size]; omega))) co3CoprimeWord
    co3Orders_check.1
  exact h

theorem rep_co3C0 :
    Rep 276 co3ChainArrs[0]! co3C0 := rep_co3GenPerm (by norm_num)

theorem rep_co3C1 :
    Rep 276 co3C1Arr co3C1 :=
  rep_compA (rep_compA (rep_inv_of_isInvA rep_co3WordValue co3Orders_check.2.1)
    (rep_co3GenPerm (by norm_num))) rep_co3WordValue

theorem co3CoprimePerm_zero :
    co3CoprimePerm 0 = co3C0 :=
  eq_of_eqA (rep_co3CoprimePerm (by norm_num)) rep_co3C0 co3Orders_check.2.2.1

theorem co3CoprimePerm_one :
    co3CoprimePerm 1 = co3C1 :=
  eq_of_eqA (rep_co3CoprimePerm (by norm_num)) rep_co3C1 co3Orders_check.2.2.2.1

theorem co3CoprimeChain_original_toList :
    co3CoprimeChain.original.toList = [co3C0, co3C1] := by
  change (Vector.ofFn fun i : Fin 2 => permOfArr 276 co3CoprimeArrs[(i : ℕ)]!).toList = _
  rw [Vector.toList_ofFn]
  change [co3CoprimePerm 0, co3CoprimePerm 1] = _
  rw [co3CoprimePerm_zero, co3CoprimePerm_one]

theorem co3CoprimeChain_originalSubgroup :
    co3CoprimeChain.originalSubgroup = co3C := by
  rw [RawSchreierDatum.originalSubgroup, co3CoprimeChain_original_toList, co3C]
  congr 1
  ext g
  simp

theorem co3GenPerm_mem (k : ℕ) (hk : k < 2) : co3GenPerm k ∈ co3P := by
  rw [co3P_eq]
  exact Subgroup.subset_closure ⟨⟨k, hk⟩, rfl⟩

theorem co3WordValue_mem : co3WordValue ∈ co3P := by
  rw [co3P_eq]
  exact Quiver.SchreierGraph.evalWord_mem_closure (fun h : Fin 2 => co3GenPerm h) _

theorem co3C_eq_P : co3C = co3P := by
  have hle : co3C ≤ co3P := by
    rw [co3C, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact co3GenPerm_mem 0 (by norm_num)
    · exact co3P.mul_mem (co3P.mul_mem (co3P.inv_mem co3WordValue_mem)
        (co3GenPerm_mem 1 (by norm_num))) co3WordValue_mem
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_co3P, ← co3CoprimeChain_originalSubgroup, card_co3CoprimeChain]

theorem card_co3C :
    Nat.card co3C = 495766656000 := by
  rw [co3C_eq_P, card_co3P]

theorem co3P_orbit_zero :
    MulAction.orbit co3P (0 : Fin 276) = Set.univ := by
  have h0 : (0 : ℕ) < co3Chain.baseCount := by decide
  have h := orbit_base_eq_univ co3Chain co3Chain_valid.1 h0
    ((co3Chain_valid.2 ⟨0, h0⟩).trans co3Order_check.2.2)
  exact h

theorem co3P_transitive :
    MulAction.IsPretransitive co3P (Fin 276) := by
  refine ⟨fun x y => ?_⟩
  have hx : x ∈ MulAction.orbit co3P (0 : Fin 276) := by rw [co3P_orbit_zero]; trivial
  have hy : y ∈ MulAction.orbit co3P (0 : Fin 276) := by rw [co3P_orbit_zero]; trivial
  obtain ⟨g, rfl⟩ := hx
  obtain ⟨h, rfl⟩ := hy
  exact ⟨h * g⁻¹, by rw [mul_smul, inv_smul_smul]⟩

theorem card_co3P_stabilizer :
    Nat.card (MulAction.stabilizer co3P (0 : Fin 276)) = 1796256000 := by
  have h1 := MulAction.index_stabilizer co3P (0 : Fin 276)
  have h2 := (MulAction.stabilizer co3P (0 : Fin 276)).card_mul_index
  rw [h1, co3P_orbit_zero, Set.ncard_univ, Nat.card_fin, card_co3P] at h2
  have h3 : Nat.card (MulAction.stabilizer co3P (0 : Fin 276)) * 276 = 1796256000 * 276 := by
    rw [h2]
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h3

theorem rep_co3PowA {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : Rep n t g) :
    ∀ e, Rep n (co3PowA n t e) (g ^ e)
  | 0 => by rw [pow_zero]; exact rep_idA
  | e + 1 => by rw [pow_succ']; exact rep_compA ht (rep_co3PowA ht e)

theorem eq_one_of_eqA_pow {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : Rep n t g) {e : ℕ}
    (h : eqA n (co3PowA n t e) (idA n) = true) : g ^ e = 1 :=
  (eqA_iff (rep_co3PowA ht e) rep_idA).1 h

theorem ne_one_of_eqA_pow {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : Rep n t g) {e : ℕ}
    (h : eqA n (co3PowA n t e) (idA n) = false) : g ^ e ≠ 1 := by
  intro hg
  rw [← Bool.not_eq_true, eqA_iff (rep_co3PowA ht e) rep_idA] at h
  exact h hg

theorem ne_one_of_eqA {n : ℕ} {t : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : Rep n t g)
    (h : eqA n t (idA n) = false) : g ≠ 1 := by
  intro hg
  rw [← Bool.not_eq_true, eqA_iff ht rep_idA] at h
  exact h hg

theorem rep_co3C0' :
    Rep 276 co3CoprimeArrs[0]! co3C0 := by
  rw [← co3CoprimePerm_zero]; exact rep_co3CoprimePerm (by norm_num)

theorem rep_co3C1' :
    Rep 276 co3CoprimeArrs[1]! co3C1 := by
  rw [← co3CoprimePerm_one]; exact rep_co3CoprimePerm (by norm_num)

theorem orderOf_co3C0 :
    orderOf co3C0 = 3 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact orderOf_eq_prime (eq_one_of_eqA_pow rep_co3C0' co3Orders_check.2.2.2.2.1)
    (ne_one_of_eqA rep_co3C0' co3Orders_check.2.2.2.2.2.1)

theorem orderOf_co3C1 :
    orderOf co3C1 = 4 := by
  have h4 : co3C1 ^ 2 ^ (1 + 1) = 1 := eq_one_of_eqA_pow rep_co3C1' co3Orders_check.2.2.2.2.2.2.1
  have h2 : ¬ co3C1 ^ 2 ^ 1 = 1 := ne_one_of_eqA_pow rep_co3C1' co3Orders_check.2.2.2.2.2.2.2.1
  exact (orderOf_eq_prime_pow h2 h4).trans (by norm_num)

theorem orderOf_co3C0C1 :
    orderOf (co3C0 * co3C1) = 23 := by
  have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  exact orderOf_eq_prime
    (eq_one_of_eqA_pow (rep_compA rep_co3C0' rep_co3C1') co3Orders_check.2.2.2.2.2.2.2.2.1)
    (ne_one_of_eqA (rep_compA rep_co3C0' rep_co3C1') co3Orders_check.2.2.2.2.2.2.2.2.2)

theorem card_Co3_of_perm :
    Nat.card Blueprint.NativeSporadic.Co3 = 495766656000 := by
  rw [Nat.card_congr co3PermEquiv.toEquiv, card_co3P]

theorem Co3_order_coprime_generators :
    ValidSchreier co3Chain ∧ ValidSchreier co3CoprimeChain ∧
    co3Chain.original.toList = [co3GenPerm 0, co3GenPerm 1] ∧
    co3CoprimeChain.original.toList = [co3C0, co3C1] ∧
    co3Chain.base.toList.map Fin.val = [0, 1, 2, 3, 4, 5, 6] ∧
    co3CoprimeChain.base.toList.map Fin.val = [0, 1, 2, 3, 4, 5, 6] ∧
    (List.finRange co3Chain.baseCount).map co3Chain.orbitSize = [276, 275, 112, 81, 20, 18, 2] ∧
    (List.finRange co3CoprimeChain.baseCount).map co3CoprimeChain.orbitSize =
      [276, 275, 112, 81, 20, 18, 2] ∧
    Nat.card co3P = 495766656000 ∧ Nat.card co3C = 495766656000 ∧ co3C = co3P ∧
    MulAction.IsPretransitive co3P (Fin 276) ∧
    Nat.card (MulAction.stabilizer co3P (0 : Fin 276)) = 1796256000 ∧
    orderOf co3C0 = 3 ∧ orderOf co3C1 = 4 ∧ orderOf (co3C0 * co3C1) = 23 ∧
    Nat.card Blueprint.NativeSporadic.Co3 = 495766656000 :=
  ⟨co3Chain_valid.1, co3Coprime_valid.1, co3Chain_original_toList,
    co3CoprimeChain_original_toList, by decide, by decide, co3Chain_orbitSizes,
    co3Coprime_orbitSizes, card_co3P, card_co3C, co3C_eq_P, co3P_transitive,
    card_co3P_stabilizer, orderOf_co3C0, orderOf_co3C1, orderOf_co3C0C1, card_Co3_of_perm⟩

end CFSG.Sporadic.Schreier.Co3
