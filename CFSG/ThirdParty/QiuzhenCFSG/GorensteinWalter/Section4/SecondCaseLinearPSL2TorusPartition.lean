module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_8_27
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The order-`p` partition for a selected PSL₂ torus

This is the small Huppert-partition adapter needed by equation (11).  It
removes the characteristic Sylow family and the opposite torus family when
`p` is an odd prime dividing the selected torus, and transports the result
through a model equivalence.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

open BenderSuzuki
open BenderSuzuki.External
open scoped MatrixGroups

/-- Remove the characteristic Sylow and opposite-torus alternatives from
Huppert's partition when the order `p` is an odd prime dividing the selected
torus. -/
public theorem psl2_torus_family_partition_of_huppert
    {K : Type u} [Field K] [Finite K]
    {r f p : ℕ} [Fact r.Prime] [Fact p.Prime]
    (hKcard : Nat.card K = r ^ f) (hrOdd : Odd r) (hpOdd : Odd p)
    (U S : Subgroup (PSL2 K))
    (hUcard : Nat.card U = (Nat.card K - 1) / 2)
    (hScard : Nat.card S = (Nat.card K + 1) / 2)
    (hpart : ∃ P : Sylow r (PSL2 K), ∀ x : PSL2 K, x ≠ 1 →
      ∃! T : Subgroup (PSL2 K),
        x ∈ T ∧
          ((∃ g, T = (P : Subgroup (PSL2 K)).map
            (MulAut.conj g).toMonoidHom) ∨
          (∃ g, T = U.map (MulAut.conj g).toMonoidHom) ∨
          (∃ g, T = S.map (MulAut.conj g).toMonoidHom)))
    (hpU : p ∣ Nat.card U) :
    ∀ x : PSL2 K, orderOf x = p →
      ∃! T : {T : Subgroup (PSL2 K) // ∃ g : PSL2 K,
        T = U.map (MulAut.conj g).toMonoidHom}, x ∈ T.1 := by
  classical
  let : Fintype K := Fintype.ofFinite K
  obtain ⟨P, hpart⟩ := hpart
  have hKodd : Odd (Nat.card K) := by
    rw [hKcard]
    exact hrOdd.pow
  have h2minus : 2 ∣ Nat.card K - 1 := by
    rcases hKodd with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    omega
  have h2plus : 2 ∣ Nat.card K + 1 := by
    rcases hKodd with ⟨a, ha⟩
    refine ⟨a + 1, ?_⟩
    omega
  have hp_not_r : p ≠ r := by
    intro hpr
    subst p
    have hrU : r ∣ Nat.card K - 1 := by
      rw [hUcard] at hpU
      rw [Nat.dvd_div_iff_mul_dvd h2minus] at hpU
      exact dvd_trans (Nat.dvd_mul_left r 2) hpU
    have hf0 : f ≠ 0 := by
      intro hf
      subst f
      have hq1 : 1 < Fintype.card K := Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
      rw [← Nat.card_eq_fintype_card, hKcard] at hq1
      simp at hq1
    have hrK : r ∣ Nat.card K := by
      rw [hKcard]
      exact dvd_pow_self r hf0
    have hrone : r ∣ 1 := by
      convert Nat.dvd_sub hrK hrU using 1 <;> omega
    exact (Fact.out : Nat.Prime r).ne_one (Nat.dvd_one.mp hrone)
  have hp_not_two : p ≠ 2 := by
    intro hp2
    subst p
    exact hpOdd.not_two_dvd_nat (by simp)
  have hnotS : ¬ p ∣ Nat.card S := by
    intro hpS
    have hpminus : p ∣ Nat.card K - 1 := by
      rw [hUcard] at hpU
      rw [Nat.dvd_div_iff_mul_dvd h2minus] at hpU
      exact dvd_trans (Nat.dvd_mul_left p 2) hpU
    have hpplus : p ∣ Nat.card K + 1 := by
      rw [hScard] at hpS
      rw [Nat.dvd_div_iff_mul_dvd h2plus] at hpS
      exact dvd_trans (Nat.dvd_mul_left p 2) hpS
    have hpTwo : p ∣ 2 := by
      convert Nat.dvd_sub hpplus hpminus using 1 <;> omega
    have hpEq : p = 2 :=
      (Nat.prime_dvd_prime_iff_eq (Fact.out : Nat.Prime p) Nat.prime_two).mp hpTwo
    exact hp_not_two hpEq
  intro x hxord
  have hxne : x ≠ 1 := by
    intro hx1
    have hp1 : p = 1 := by simpa [hx1] using hxord.symm
    exact (Fact.out : Nat.Prime p).ne_one hp1
  obtain ⟨T, hTx, hTuniq⟩ := hpart x hxne
  rcases hTx with ⟨hTmem, hTfamily⟩
  have hT_U : ∃ g : PSL2 K, T = U.map (MulAut.conj g).toMonoidHom := by
    rcases hTfamily with hP | hU | hS
    · exfalso
      rcases hP with ⟨g, hg⟩
      rw [hg] at hTmem
      rcases Subgroup.mem_map.mp hTmem with ⟨y, hyP, hyx⟩
      have hyord : orderOf y = p := by
        have hconj : orderOf ((MulAut.conj g).toMonoidHom y) = orderOf y :=
          (MulAut.conj g).orderOf_eq y
        rw [← hconj, hyx, hxord]
      have hydiv : orderOf y ∣ Nat.card (P : Subgroup (PSL2 K)) :=
        Subgroup.orderOf_dvd_natCard (P : Subgroup (PSL2 K)) hyP
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp P.isPGroup'
      have hpdiv : p ∣ r ^ n := by
        rw [hn] at hydiv
        simpa [hyord] using hydiv
      have hprdiv : p ∣ r := (Fact.out : Nat.Prime p).dvd_of_dvd_pow hpdiv
      exact hp_not_r ((Nat.prime_dvd_prime_iff_eq
        (Fact.out : Nat.Prime p) (Fact.out : Nat.Prime r)).mp hprdiv)
    · exact hU
    · exfalso
      rcases hS with ⟨g, hg⟩
      rw [hg] at hTmem
      rcases Subgroup.mem_map.mp hTmem with ⟨y, hyS, hyx⟩
      have hyord : orderOf y = p := by
        have hconj : orderOf ((MulAut.conj g).toMonoidHom y) = orderOf y :=
          (MulAut.conj g).orderOf_eq y
        rw [← hconj, hyx, hxord]
      have hydiv : orderOf y ∣ Nat.card S :=
        Subgroup.orderOf_dvd_natCard S hyS
      have hpS : p ∣ Nat.card S := by simpa [hyord] using hydiv
      exact hnotS hpS
  have hTfamily' :
      x ∈ T ∧
        ((∃ g, T = (P : Subgroup (PSL2 K)).map
          (MulAut.conj g).toMonoidHom) ∨
        (∃ g, T = U.map (MulAut.conj g).toMonoidHom) ∨
        (∃ g, T = S.map (MulAut.conj g).toMonoidHom)) :=
    ⟨hTmem, Or.inr (Or.inl hT_U)⟩
  refine ⟨⟨T, hT_U⟩, hTmem, ?_⟩
  intro T' hT'x
  rcases T'.2 with ⟨g', hg'⟩
  have hT'family :
      x ∈ T'.1 ∧
        ((∃ g, T'.1 = (P : Subgroup (PSL2 K)).map
          (MulAut.conj g).toMonoidHom) ∨
        (∃ g, T'.1 = U.map (MulAut.conj g).toMonoidHom) ∨
        (∃ g, T'.1 = S.map (MulAut.conj g).toMonoidHom) ) :=
    ⟨hT'x, Or.inr (Or.inl ⟨g', hg'⟩)⟩
  have hEq : T'.1 = T := hTuniq T' hT'family
  exact Subtype.ext hEq

/-- Transport a unique torus-family partition through a group equivalence. -/
public theorem transport_psl2_torus_family_partition
    {Q K : Type u} [Group Q] [Finite Q] [Field K] [Finite K]
    {p : ℕ} [Fact p.Prime]
    (e : Q ≃* PSL2 K) (U : Subgroup (PSL2 K))
    (hpart : ∀ x : PSL2 K, orderOf x = p →
      ∃! T : {T : Subgroup (PSL2 K) // ∃ g : PSL2 K,
        T = U.map (MulAut.conj g).toMonoidHom}, x ∈ T.1) :
    ∀ x : Q, orderOf x = p →
      ∃! T : {T : Subgroup Q // ∃ g : Q,
        T = (U.map e.symm.toMonoidHom).map (MulAut.conj g).toMonoidHom}, x ∈ T.1 := by
  classical
  intro x hx
  let y : PSL2 K := e x
  have hy : orderOf y = p := by
    rw [e.orderOf_eq]
    exact hx
  obtain ⟨T, hTy, hTuniq⟩ := hpart y hy
  rcases T.2 with ⟨g, hg⟩
  let TQ : Subgroup Q := T.1.map e.symm.toMonoidHom
  have hTQmem : x ∈ TQ := by
    refine Subgroup.mem_map.mpr ⟨y, hTy, ?_⟩
    simp [y, TQ]
  have hTQfamily : ∃ g : Q, TQ =
      (U.map e.symm.toMonoidHom).map (MulAut.conj g).toMonoidHom := by
    rcases T.2 with ⟨g, hg⟩
    refine ⟨e.symm g, ?_⟩
    dsimp [TQ]
    rw [hg, Subgroup.map_map]
    rw [Subgroup.map_map]
    apply congrArg (fun f : PSL2 K →* Q => Subgroup.map f U)
    ext z
    simp [MulAut.conj_apply, mul_assoc]
  refine ⟨⟨TQ, hTQfamily⟩, hTQmem, ?_⟩
  intro T' hT'x
  let TP : Subgroup (PSL2 K) := T'.1.map e.toMonoidHom
  have hTPfamily : ∃ g : PSL2 K, TP = U.map (MulAut.conj g).toMonoidHom := by
    rcases T'.2 with ⟨g', hg'⟩
    refine ⟨e g', ?_⟩
    dsimp [TP]
    rw [hg', Subgroup.map_map]
    rw [Subgroup.map_map]
    apply congrArg (fun f : PSL2 K →* PSL2 K => Subgroup.map f U)
    ext z
    simp [MulAut.conj_apply, mul_assoc]
  have hTPmem : e x ∈ TP := by
    dsimp [TP]
    exact Subgroup.mem_map.mpr ⟨x, hT'x, rfl⟩
  have hEqP : TP = T.1 := by
    exact congrArg Subtype.val (hTuniq ⟨TP, hTPfamily⟩ hTPmem)
  have hmapEq : T'.1.map e.toMonoidHom = TQ.map e.toMonoidHom := by
    calc
      T'.1.map e.toMonoidHom = TP := rfl
      _ = T.1 := hEqP
      _ = TQ.map e.toMonoidHom := by
        dsimp [TQ]
        rw [Subgroup.map_map]
        change T.1 = Subgroup.map
          (e.toMonoidHom.comp e.symm.toMonoidHom) T.1
        have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id _ := by
          ext z
          simp
        rw [hcomp]
        simp
  exact Subtype.ext (Subgroup.map_injective e.injective hmapEq)

end CFSG.GorensteinWalter
