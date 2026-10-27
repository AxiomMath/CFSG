module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationEightDefs
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearOmegaConjugation
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearOmegaFixedPart
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CentralizerSetupOddCoreNormal
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Core
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # Draft: generic odd-prime omega data (to be replaced by the shared
`SecondCaseLinearOmegaData` from `SecondCaseLinearEquationEightDefs`) -/

noncomputable section

open scoped Finset

namespace CFSG.GorensteinWalter

universe u

/-- Draft data structure mirroring the planned shared linear omega data. -/
public structure SecondCaseLinearOmegaView
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w) where
  p : ℕ
  p_prime : p.Prime
  p_odd : Odd p
  s : d.E
  s_involution : IsInvolution (s : G)
  s_mem_H : (s : G) ∈ c.H
  F : Subgroup G
  F_cyclic : IsCyclic F
  F_fixed : F = centralizerIn c.FU (s : G)
  P : Subgroup G
  P_card : Nat.card P = p
  P_le_F : P ≤ F
  P0 : Subgroup G
  P0_card : Nat.card P0 = p
  P0_inverted : ∀ x : G, x ∈ P0 → (s : G) * x * (s : G)⁻¹ = x⁻¹
  A : Subgroup G
  A_eq : A = P0 ⊔ P
  A_card : Nat.card A = p ^ 2
  Q : Subgroup (↥c.U)
  Q_le_upperCentralSeries_two :
    Q ≤ (Subgroup.upperCentralSeries (pCore p (↥c.U)) 2).map (pCore p (↥c.U)).subtype
  Q_not_cyclic : ¬ IsCyclic Q
  Q_exponent : Monoid.exponent Q = p
  Q_characteristic : Q.Characteristic
  normalizer_le_A : (Subgroup.normalizer (P : Set G)) ⊓ (Q.map c.U.subtype) ≤ A
  conj_le_A : ∀ q : G, q ∈ Q.map c.U.subtype → ∀ p : G, p ∈ P →
    q * p * q⁻¹ ∈ A

namespace SecondCaseLinearOmegaView

variable {G : Type u} [Group G] [Finite G]
variable {c : CentralizerSetup G} {w : SecondCaseWitness c}
variable {d : SecondCaseComponentData w}

/-- The ambient copy of `Q`. -/
@[expose] public def QG (od : SecondCaseLinearOmegaView c w d) : Subgroup G :=
  od.Q.map c.U.subtype

/-- The ambient copy of `O_p(U)`. -/
@[expose] public def pCore_amb (od : SecondCaseLinearOmegaView c w d) : Subgroup G :=
  (pCore od.p (↥c.U)).map c.U.subtype

/-- The ambient copy of `Z_2(O_p(U))`. -/
@[expose] public def Z2OpU_amb (od : SecondCaseLinearOmegaView c w d) : Subgroup G :=
  (((Subgroup.upperCentralSeries (pCore od.p (↥c.U)) 2).map (pCore od.p (↥c.U)).subtype).map c.U.subtype)

/-- `Q` lies in the second centre of `O_p(U)`. -/
public theorem QG_le_Z2OpU_amb (od : SecondCaseLinearOmegaView c w d) :
    od.QG ≤ od.Z2OpU_amb := by
  exact Subgroup.map_mono (K := od.Q) (K' := (Subgroup.upperCentralSeries (pCore od.p (↥c.U)) 2).map (pCore od.p (↥c.U)).subtype) (f := c.U.subtype) od.Q_le_upperCentralSeries_two

/-- `Z_2(O_p(U)) ≤ O_p(U)`, hence `Q` lies in `O_p(U)`. -/
public theorem QG_le_pCore (od : SecondCaseLinearOmegaView c w d) :
    od.QG ≤ od.pCore_amb := by
  have hz : od.Z2OpU_amb ≤ od.pCore_amb := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    rcases Subgroup.mem_map.mp hy with ⟨z, hz, rfl⟩
    change (z.1 : G) ∈ (pCore od.p (↥c.U)).map c.U.subtype
    exact Subgroup.mem_map.mpr ⟨z.1, z.2, rfl⟩
  exact (od.QG_le_Z2OpU_amb).trans hz

/-- `O_p(U) ≤ F(U)`, hence `Q` lies in the Fitting subgroup of `U`. -/
public theorem pCore_amb_le_FU (od : SecondCaseLinearOmegaView c w d) :
    od.pCore_amb ≤ c.FU := by
  let : Fact (Nat.Prime od.p) := ⟨od.p_prime⟩
  have hle : (pCore od.p (↥c.U)).map c.U.subtype ≤
      (fittingSubgroup (↥c.U)).map c.U.subtype := by
    exact Subgroup.map_mono (K := pCore od.p (↥c.U))
      (K' := fittingSubgroup (↥c.U)) (f := c.U.subtype)
      (pCore_le_fitting (↥c.U) od.p)
  change (pCore od.p (↥c.U)).map c.U.subtype ≤ (fittingSubgroup (↥c.U)).map c.U.subtype
  exact hle

/-- `Q` lies in the Fitting subgroup of `U`. -/
public theorem QG_le_FU (od : SecondCaseLinearOmegaView c w d) :
    od.QG ≤ c.FU :=
  (od.QG_le_pCore).trans (od.pCore_amb_le_FU)

/-- `Q` has exponent `p`, so its ambient copy does too. -/
public theorem QG_exponent (od : SecondCaseLinearOmegaView c w d) :
    Monoid.exponent od.QG = od.p := by
  let eQ : od.Q ≃* od.QG :=
    Subgroup.equivMapOfInjective od.Q c.U.subtype c.U.subtype_injective
  exact (Monoid.exponent_eq_of_mulEquiv eQ).symm.trans od.Q_exponent

/-- The ambient `Q` is a `p`-group. -/
public theorem QG_isPGroup (od : SecondCaseLinearOmegaView c w d) :
    IsPGroup od.p od.QG := by
  intro x
  refine ⟨1, ?_⟩
  have hx : x ^ od.p = 1 :=
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (by rw [od.QG_exponent]) x)
  simpa [pow_one] using hx

/-- The ambient `Q` is not cyclic. -/
public theorem QG_not_cyclic (od : SecondCaseLinearOmegaView c w d) :
    ¬ IsCyclic od.QG := by
  intro hcyc
  let eQ : od.Q ≃* od.QG :=
    Subgroup.equivMapOfInjective od.Q c.U.subtype c.U.subtype_injective
  exact od.Q_not_cyclic (eQ.isCyclic.mpr hcyc)

/-- The ambient `Q` is nontrivial (a noncyclic `p`-group). -/
public theorem QG_nontrivial (od : SecondCaseLinearOmegaView c w d) :
    Nontrivial od.QG := by
  apply Finite.one_lt_card_iff_nontrivial.mp
  have hne : od.QG ≠ ⊥ := by
    intro hbot
    apply od.QG_not_cyclic
    rw [hbot]
    infer_instance
  have hpos : 0 < Nat.card od.QG := Nat.card_pos
  have hne1 : Nat.card od.QG ≠ 1 := by
    intro h1
    exact hne ((Subgroup.eq_bot_iff_card (H := od.QG)).mpr h1)
  omega

/-- Elements of `F(U)` of `p`-th power one are exactly the elements of `P`. -/
public theorem F_order_p_eq_P (od : SecondCaseLinearOmegaView c w d) :
    {x : G | x ∈ od.F ∧ x ^ od.p = 1} = (od.P : Set G) := by
  classical
  let S : Set G := {x : G | x ∈ od.F ∧ x ^ od.p = 1}
  let : Fintype (↥od.F) := Fintype.ofFinite (↥od.F)
  let : IsCyclic (↥od.F) := od.F_cyclic
  have hp_pos : 0 < od.p := od.p_prime.pos
  have hPsubS : (od.P : Set G) ⊆ S := by
    intro x hx
    exact ⟨od.P_le_F hx,
      (orderOf_dvd_iff_pow_eq_one (x := x) (n := od.p)).mp (by
        simpa [od.P_card] using (Subgroup.orderOf_dvd_natCard od.P hx))⟩
  have hScard : Nat.card {x : G // x ∈ S} = od.p := by
    apply le_antisymm
    · let e : {x : G // x ∈ S} ≃ {a : (↥od.F) // a ^ od.p = 1} :=
        { toFun := fun x => ⟨⟨x.1, x.2.1⟩, by
            apply Subtype.ext
            simpa using x.2.2⟩
          invFun := fun a => ⟨(a.1 : G), ⟨a.1.2, by
            exact congrArg Subtype.val a.2⟩⟩
          left_inv := by intro x; rfl
          right_inv := by intro a; rfl }
      calc
        Nat.card {x : G // x ∈ S} = Nat.card {a : (↥od.F) // a ^ od.p = 1} :=
          Nat.card_congr e
        _ = #{a : (↥od.F) | a ^ od.p = 1} := by
          rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
        _ ≤ od.p := IsCyclic.card_pow_eq_one_le (α := (↥od.F)) (n := od.p) hp_pos
    · have hle : Nat.card od.P ≤ Nat.card {x : G // x ∈ S} :=
        Nat.card_le_card_of_injective (fun x : od.P => ⟨(x : G), hPsubS x.2⟩) (by
          intro a b h
          simpa using congrArg Subtype.val h)
      simpa [od.P_card] using hle
  have hcard : Nat.card {x : G // x ∈ S} ≤ Nat.card {x : G // x ∈ (od.P : Set G)} := by
    rw [hScard]
    exact le_of_eq (by
      change od.p = Nat.card (↥od.P)
      rw [od.P_card])
  let : Fintype (↥od.P) := Fintype.ofFinite (↥od.P)
  exact (Set.eq_of_subset_of_card_le hPsubS (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hcard)).symm

/-- Fixed points of `s` in `Q` lie in `P`. -/
public theorem F_inter_QG_le_P (od : SecondCaseLinearOmegaView c w d) :
    od.F ⊓ od.QG ≤ od.P := by
  intro x hx
  have hxpow : x ^ od.p = 1 := by
    have hq : (⟨x, hx.2⟩ : od.QG) ^ od.p = 1 :=
      (Monoid.exponent_dvd_iff_forall_pow_eq_one (G := od.QG) (n := od.p)).mp
        (by rw [od.QG_exponent]) ⟨x, hx.2⟩
    exact congrArg Subtype.val hq
  have hxS : x ∈ {x : G | x ∈ od.F ∧ x ^ od.p = 1} := ⟨hx.1, hxpow⟩
  rw [od.F_order_p_eq_P] at hxS
  exact hxS

/-- The fixed prime-order part `P` lies in `A`. -/
public theorem P_le_A (od : SecondCaseLinearOmegaView c w d) : od.P ≤ od.A := by
  rw [od.A_eq]
  exact le_sup_right

/-- The inverted prime-order part `P0` lies in `A`. -/
public theorem P0_le_A (od : SecondCaseLinearOmegaView c w d) : od.P0 ≤ od.A := by
  rw [od.A_eq]
  exact le_sup_left

/-- `P ∩ Q = 1` whenever `P` is not contained in `Q`. -/
public theorem P_inter_QG_eq_bot_of_not_le
    (od : SecondCaseLinearOmegaView c w d) (hPnotleQ : ¬ od.P ≤ od.QG) :
    od.P ⊓ od.QG = ⊥ := by
  classical
  let I : Subgroup G := od.P ⊓ od.QG
  have hIdiv : Nat.card I ∣ od.p := by
    rw [← od.P_card]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hIne : Nat.card I ≠ od.p := by
    intro hIp
    have hIeqP : I = od.P :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hIp, od.P_card])
    apply hPnotleQ
    rw [← hIeqP]
    exact inf_le_right
  have hIcard : Nat.card I = 1 :=
    ((Nat.dvd_prime od.p_prime).mp hIdiv).resolve_right hIne
  exact (Subgroup.eq_bot_iff_card (H := I)).mpr hIcard

end SecondCaseLinearOmegaView

end CFSG.GorensteinWalter
