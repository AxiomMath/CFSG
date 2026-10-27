module

public import CFSG.Sporadic.Th.Recog.MFactsB.Letters
public import CFSG.Sporadic.Th.Recog.MFactsB.Lift
public import CFSG.Sporadic.Th.Recog.MFactsA
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Sporadic.Th.Recog.MFactsB

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3
open Equiv Equiv.Perm

section Basic


private def cyc087 : Perm (Fin 9) := swap 0 8 * swap 8 7

private def cyc142 : Perm (Fin 9) := swap 1 2 * swap 2 4

private def cyc365 : Perm (Fin 9) := swap 3 6 * swap 6 5

private def cyc356 : Perm (Fin 9) := swap 3 5 * swap 5 6

private theorem isThreeCycle_cyc087 : IsThreeCycle cyc087 := by
  rw [show cyc087 = ([0, 8, 7] : List (Fin 9)).formPerm by
    ext x
    fin_cases x <;> decide +kernel]
  rw [IsThreeCycle]
  rw [(List.isCycle_formPerm (l := [0, 8, 7]) (by decide) (by decide)).cycleType]
  rw [show ((([0, 8, 7] : List (Fin 9)).formPerm).support.card) = 3 by decide +kernel]

private theorem isThreeCycle_cyc142 : IsThreeCycle cyc142 := by
  rw [show cyc142 = ([1, 2, 4] : List (Fin 9)).formPerm by
    ext x
    fin_cases x <;> decide +kernel]
  rw [IsThreeCycle]
  rw [(List.isCycle_formPerm (l := [1, 2, 4]) (by decide) (by decide)).cycleType]
  rw [show ((([1, 2, 4] : List (Fin 9)).formPerm).support.card) = 3 by decide +kernel]

private theorem isThreeCycle_cyc365 : IsThreeCycle cyc365 := by
  rw [show cyc365 = ([3, 6, 5] : List (Fin 9)).formPerm by
    ext x
    fin_cases x <;> decide +kernel]
  rw [IsThreeCycle]
  rw [(List.isCycle_formPerm (l := [3, 6, 5]) (by decide) (by decide)).cycleType]
  rw [show ((([3, 6, 5] : List (Fin 9)).formPerm).support.card) = 3 by decide +kernel]

private theorem isThreeCycle_cyc356 : IsThreeCycle cyc356 := by
  rw [show cyc356 = ([3, 5, 6] : List (Fin 9)).formPerm by
    ext x
    fin_cases x <;> decide +kernel]
  rw [IsThreeCycle]
  rw [(List.isCycle_formPerm (l := [3, 5, 6]) (by decide) (by decide)).cycleType]
  rw [show ((([3, 5, 6] : List (Fin 9)).formPerm).support.card) = 3 by decide +kernel]

private theorem disjoint_cyc087_cyc142 : Disjoint cyc087 cyc142 := by
  intro x
  fin_cases x <;> decide +kernel

private theorem disjoint_cyc087_cyc365 : Disjoint cyc087 cyc365 := by
  intro x
  fin_cases x <;> decide +kernel

private theorem disjoint_cyc142_cyc365 : Disjoint cyc142 cyc365 := by
  intro x
  fin_cases x <;> decide +kernel

private theorem cycleType_kap_ω₁ :
    (Max3.InvRep.kap ω₁ : Perm (Fin 9)).cycleType = {3, 3, 3} := by
  have heq : (Max3.InvRep.kap ω₁ : Perm (Fin 9)) = cyc087 * cyc142 * cyc365 := by
    rw [coe_kap_ω₁]
    ext x
    fin_cases x <;> decide +kernel
  rw [show (Max3.InvRep.kap ω₁ : Perm (Fin 9)) = cyc087 * (cyc142 * cyc365) by
    rw [heq]; group]
  rw [Disjoint.cycleType_mul (Disjoint.mul_right disjoint_cyc087_cyc142
      disjoint_cyc087_cyc365),
    Disjoint.cycleType_mul disjoint_cyc142_cyc365,
    isThreeCycle_cyc087.cycleType, isThreeCycle_cyc142.cycleType,
    isThreeCycle_cyc365.cycleType]
  simp [Multiset.singleton_add]

private theorem cycleType_kap_ω₁_mul_ω₂ :
    (Max3.InvRep.kap (ω₁ * ω₂) : Perm (Fin 9)).cycleType = {3} := by
  have heq : (Max3.InvRep.kap (ω₁ * ω₂) : Perm (Fin 9)) = cyc356 := by
    rw [map_mul, Subgroup.coe_mul, coe_kap_ω₁, coe_kap_ω₂]
    ext x
    fin_cases x <;> decide +kernel
  rw [heq]
  exact isThreeCycle_cyc356

private theorem orderOf_ω₁_mul_ω₂ (hω : ω₁ * ω₂ = ω₂ * ω₁) : orderOf (ω₁ * ω₂) = 3 := by
  have hcomm : Commute ω₁ ω₂ := hω
  have h2 : ω₂ ^ 3 = 1 := by
    rw [ω₂, show uM * ω₁ * uM⁻¹ = MulAut.conj uM ω₁ from by rw [MulAut.conj_apply]]
    rw [← map_pow, ω₁_pow_three, map_one]
  have h3 : (ω₁ * ω₂) ^ 3 = 1 := by
    rw [@Commute.mul_pow ↥Max3.M (inferInstance : Monoid ↥Max3.M) ω₁ ω₂ hcomm 3,
      ω₁_pow_three, h2, mul_one]
  have hne : ω₁ * ω₂ ≠ 1 := by
    intro h1
    have hκ : Max3.InvRep.kap (ω₁ * ω₂) = 1 := by rw [h1, map_one]
    have hct := cycleType_kap_ω₁_mul_ω₂
    rw [hκ] at hct
    simp at hct
  exact orderOf_eq_prime h3 hne

private theorem commute_kap_of_mul_eq {a b : ↥Max3.M} (h : a * b = b * a) :
    Commute (Max3.InvRep.kap a) (Max3.InvRep.kap b) := by
  show Max3.InvRep.kap a * Max3.InvRep.kap b = Max3.InvRep.kap b * Max3.InvRep.kap a
  rw [← map_mul, ← map_mul, h]

private theorem orderOf_kap_eq_two_of_not_mem_Q {w : ↥Max3.M} (hw : w * w = 1)
    (hwQ : (w : J) ∉ Max3.Q) : orderOf (Max3.InvRep.kap w) = 2 := by
  apply orderOf_eq_prime
  · rw [pow_two, ← map_mul, hw, map_one]
  · intro h1
    exact hwQ (Max3.InvRep.kap_eq_one_iff.mp h1)

private theorem exists_conj_pair {x r w : ↥Max3.M}
    (hx : orderOf x = 3) (hr : orderOf r = 3)
    (his : IsConj (Max3.InvRep.kap x) (Max3.InvRep.kap r))
    (hwQ : (w : J) ∈ Max3.Q) (hw2 : w * w = 1) (hw1 : w ≠ 1)
    (hwz : (w : J) ≠ Max3.z) (hwx : w * x = x * w) :
    ∃ m : ↥Max3.M, m * x * m⁻¹ = r ∧
      (m * w * m⁻¹) * (m * w * m⁻¹) = 1 ∧
      (m * w * m⁻¹) * r = r * (m * w * m⁻¹) ∧
      m * w * m⁻¹ ≠ 1 ∧
      ((m * w * m⁻¹ : ↥Max3.M) : J) ∈ Max3.Q ∧
      ((m * w * m⁻¹ : ↥Max3.M) : J) ≠ Max3.z := by
  obtain ⟨m, hm⟩ := exists_conj_of_isConj_kap (p := 3) (by norm_num) hx hr his
  refine ⟨m, hm, ?_, ?_, ?_, ?_, ?_⟩
  · calc (m * w * m⁻¹) * (m * w * m⁻¹) = m * (w * w) * m⁻¹ := by group
      _ = 1 := by rw [hw2]; group
  · calc (m * w * m⁻¹) * r = m * (w * x) * m⁻¹ := by rw [← hm]; group
      _ = m * (x * w) * m⁻¹ := by rw [hwx]
      _ = r * (m * w * m⁻¹) := by rw [← hm]; group
  · intro h1
    have h2 : w = 1 := by
      calc w = m⁻¹ * (m * w * m⁻¹) * m := by group
        _ = 1 := by rw [h1]; group
    exact hw1 h2
  · have hQ : (m * w * m⁻¹ : ↥Max3.M) ∈ Max3.Q.subgroupOf Max3.M :=
      Max3.normal_Q_subgroupOf_M.conj_mem w hwQ m
    simpa only [Subgroup.mem_subgroupOf] using hQ
  · intro hz
    have hzM : m * w * m⁻¹ = zM := Subtype.ext (by simpa using hz)
    have hzc : ∀ g : ↥Max3.M, g * zM = zM * g := by
      intro g
      exact Subtype.ext (Max3.commute_z_of_mem_M g.2).symm.eq
    have hwzM : w = zM := by
      calc w = m⁻¹ * (m * w * m⁻¹) * m := by group
        _ = m⁻¹ * zM * m := by rw [hzM]
        _ = zM := by rw [hzc m⁻¹]; group
    exact hwz (by simpa using congrArg Subtype.val hwzM)

private theorem false_of_cycleType_three (hω : ω₁ * ω₂ = ω₂ * ω₁)
    (hT3 : ∀ w : ↥Max3.M, (w : J) ∈ Max3.Q → w * w = 1 → w * (ω₁ * ω₂) = ω₁ * ω₂ * w →
      w = 1 ∨ (w : J) = Max3.z)
    {x w : ↥Max3.M} (hx : orderOf x = 3)
    (hx3 : orderOf (Max3.InvRep.kap x) = 3)
    (hw2 : w * w = 1) (hw1 : w ≠ 1) (hwz : (w : J) ≠ Max3.z) (hwx : w * x = x * w)
    (hct : (Max3.InvRep.kap x : Perm (Fin 9)).cycleType = {3}) : False := by
  have hcommκ : Commute (Max3.InvRep.kap w) (Max3.InvRep.kap x) :=
    commute_kap_of_mul_eq hwx
  by_cases hwQ : (w : J) ∈ Max3.Q
  · have h3 : orderOf (ω₁ * ω₂) = 3 := orderOf_ω₁_mul_ω₂ hω
    have his : IsConj (Max3.InvRep.kap x) (Max3.InvRep.kap (ω₁ * ω₂)) :=
      (isConj_iff_cycleType_of_orderOf_eq_three hx3).mpr
        (by rw [hct, cycleType_kap_ω₁_mul_ω₂])
    obtain ⟨m, -, hw'2, hw'comm, hw'1, hw'Q, hw'z⟩ :=
      exists_conj_pair hx h3 his hwQ hw2 hw1 hwz hwx
    rcases hT3 (m * w * m⁻¹) hw'Q hw'2 hw'comm with h | h
    · exact hw'1 h
    · exact hw'z h
  · have hw2κ : orderOf (Max3.InvRep.kap w) = 2 :=
      orderOf_kap_eq_two_of_not_mem_Q hw2 hwQ
    have hw2κP : orderOf ((Max3.InvRep.kap w : alternatingGroup (Fin 9)) : Perm (Fin 9)) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact hw2κ
    have hcommP : Commute (Max3.InvRep.kap w : Perm (Fin 9))
        (Max3.InvRep.kap x : Perm (Fin 9)) :=
      congrArg Subtype.val hcommκ
    have hsupp := card_support_le_six_of_orderOf_eq_two_of_cycleType_three hct hw2κP hcommP
    rcases cycleType_of_orderOf_eq_two hw2κ with h22 | h24
    · exact cycleType_kap_ne_of_mul_self hw2 h22
    · have h8 : (Max3.InvRep.kap w : Perm (Fin 9)).support.card = 8 := by
        rw [← Equiv.Perm.sum_cycleType, h24]
        norm_num
      omega

private theorem mem_Q_of_cycleType_three_three_three {x w : ↥Max3.M}
    (hw2 : w * w = 1) (hwx : w * x = x * w)
    (hct : (Max3.InvRep.kap x : Perm (Fin 9)).cycleType = {3, 3, 3}) :
    (w : J) ∈ Max3.Q := by
  by_contra hQ
  have hw2κ : orderOf (Max3.InvRep.kap w) = 2 :=
    orderOf_kap_eq_two_of_not_mem_Q hw2 hQ
  have hcommκ : Commute (Max3.InvRep.kap w) (Max3.InvRep.kap x) :=
    commute_kap_of_mul_eq hwx
  have hmem : Max3.InvRep.kap w ∈ Subgroup.centralizer
      ({Max3.InvRep.kap x} : Set (alternatingGroup (Fin 9))) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hcommκ.eq
  let C : Subgroup (alternatingGroup (Fin 9)) :=
    Subgroup.centralizer ({Max3.InvRep.kap x} : Set (alternatingGroup (Fin 9)))
  have hCcard : Nat.card ↥C = 81 :=
    card_centralizer_of_cycleType_three_three_three hct
  have hdvd : orderOf (⟨Max3.InvRep.kap w, hmem⟩ : ↥C) ∣ Nat.card ↥C :=
    orderOf_dvd_natCard _
  have hord : orderOf (⟨Max3.InvRep.kap w, hmem⟩ : ↥C) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hw2κ
  rw [hord, hCcard] at hdvd
  norm_num at hdvd

theorem conj_three_of (hω : ω₁ * ω₂ = ω₂ * ω₁)
    (hT3 : ∀ w : ↥Max3.M, (w : J) ∈ Max3.Q → w * w = 1 → w * (ω₁ * ω₂) = ω₁ * ω₂ * w →
      w = 1 ∨ (w : J) = Max3.z)
    (hT333 : ∀ w : ↥Max3.M, (w : J) ∈ Max3.Q → w * w = 1 → w * ω₁ = ω₁ * w →
      w = 1 ∨ (w : J) = Max3.z) :
    ∀ x w : ↥Max3.M, orderOf x = 3 → w * w = 1 → w ≠ 1 → (w : J) ≠ Max3.z →
      w * x = x * w → ∃ m : ↥Max3.M, m * x * m⁻¹ = tLetter := by
  intro x w hx hw2 hw1 hwz hwx
  have hx3 : orderOf (Max3.InvRep.kap x) = 3 :=
    orderOf_kap_of_orderOf_eq_prime (p := 3) (by norm_num) hx
  rcases cycleType_of_orderOf_eq_three hx3 with hct | hct | hct
  · exact (false_of_cycleType_three hω hT3 hx hx3 hw2 hw1 hwz hwx hct).elim
  · have hctt : (Max3.InvRep.kap tLetter : Perm (Fin 9)).cycleType = {3, 3} :=
      cycleType_kap_tLetter
    have his : IsConj (Max3.InvRep.kap x) (Max3.InvRep.kap tLetter) :=
      (isConj_iff_cycleType_of_orderOf_eq_three hx3).mpr (by rw [hct, hctt])
    exact exists_conj_of_isConj_kap (p := 3) (by norm_num) hx orderOf_tLetter his
  · have hwQ : (w : J) ∈ Max3.Q := mem_Q_of_cycleType_three_three_three hw2 hwx hct
    have his : IsConj (Max3.InvRep.kap x) (Max3.InvRep.kap ω₁) :=
      (isConj_iff_cycleType_of_orderOf_eq_three hx3).mpr
        (by rw [hct, cycleType_kap_ω₁])
    obtain ⟨m, -, hw'2, hw'comm, hw'1, hw'Q, hw'z⟩ :=
      exists_conj_pair hx orderOf_ω₁ his hwQ hw2 hw1 hwz hwx
    rcases hT333 (m * w * m⁻¹) hw'Q hw'2 hw'comm with h | h
    · exact absurd h hw'1
    · exact absurd h hw'z

end Basic

end CFSG.Sporadic.Th.Recog.MFactsB
