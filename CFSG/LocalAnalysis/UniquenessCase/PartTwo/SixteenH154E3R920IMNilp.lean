module

public import Mathlib.GroupTheory.Nilpotent
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Nilpotent
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem r920imn_commutator_commutator_eq_bot {Q : Type*} [Group Q] {A B C : Subgroup Q}
    (hA : A.Normal) (hAC : ⁅A, C⁆ = ⊥) (hBC : ⁅B, C⁆ = B) : ⁅A, B⁆ = ⊥ := by
  haveI := hA
  rw [← hBC, eq_bot_iff, Subgroup.commutator_le]
  intro a ha x hx
  rw [Subgroup.mem_bot]
  refine Subgroup.closure_induction (p := fun x _ => ⁅a, x⁆ = 1) ?_ ?_ ?_ ?_ hx
  · rintro x ⟨b, hb, c, hc, rfl⟩
    have h_ac : ⁅a, c⁆ = 1 := by
      have h := Subgroup.commutator_mem_commutator ha hc
      rw [hAC] at h
      simpa using h
    have hmid2 : ⁅a, ⁅c⁻¹, b⁆⁆ = 1 := by
      have h1 : ⁅c, ⁅b⁻¹, a⁆⁆ = 1 := by
        have hbA : ⁅b⁻¹, a⁆ ∈ A :=
          (Subgroup.commutator_le_right (H₁ := B) (H₂ := A))
            (Subgroup.commutator_mem_commutator (Subgroup.inv_mem B hb) ha)
        have h := Subgroup.commutator_mem_commutator hc hbA
        rw [Subgroup.commutator_comm] at h
        rw [hAC] at h
        simpa using h
      have h3 : ⁅b, ⁅a⁻¹, c⁆⁆ = 1 := by
        have ha1 : ⁅a⁻¹, c⁆ = 1 := by
          have h := Subgroup.commutator_mem_commutator (Subgroup.inv_mem A ha) hc
          rw [hAC] at h
          simpa using h
        rw [ha1, commutatorElement_one_right]
      have hHW := conj_commutatorElement_right_commutatorElement_mul c b a
      rw [h1, h3] at hHW
      have hY : c * ⁅a, ⁅c⁻¹, b⁆⁆ * c⁻¹ = 1 := by
        calc c * ⁅a, ⁅c⁻¹, b⁆⁆ * c⁻¹
            = (b * 1 * b⁻¹ * a * 1 * a⁻¹)⁻¹
                * (b * 1 * b⁻¹ * a * 1 * a⁻¹ * c * ⁅a, ⁅c⁻¹, b⁆⁆ * c⁻¹) := by
              group
          _ = (b * 1 * b⁻¹ * a * 1 * a⁻¹)⁻¹ * 1 := by rw [hHW]
          _ = 1 := by group
      calc ⁅a, ⁅c⁻¹, b⁆⁆ = c⁻¹ * (c * ⁅a, ⁅c⁻¹, b⁆⁆ * c⁻¹) * c := by group
        _ = c⁻¹ * 1 * c := by rw [hY]
        _ = 1 := by group
    have hccom : Commute a c := commutatorElement_eq_one_iff_commute.mp h_ac
    have hmidc : Commute a ⁅c⁻¹, b⁆ :=
      commutatorElement_eq_one_iff_commute.mp hmid2
    have hbc_eq : ⁅b, c⁆ = c * ⁅c⁻¹, b⁆ * c⁻¹ := by
      rw [commutatorElement_inv_left c b]
      group
    rw [hbc_eq]
    exact ((hccom.mul_right hmidc).mul_right hccom.inv_right).commutator_eq
  · exact commutatorElement_one_right a
  · intro x y hx hy hpx hpy
    rw [commutatorElement_mul_right_eq_mul_conj, hpx, hpy]
    group
  · intro x hx hpx
    have hxa : ⁅x, a⁆ = 1 := by rw [← commutatorElement_inv, hpx, inv_one]
    rw [commutatorElement_inv_right, hxa]
    group

private theorem r920imn_card_eq_one_of_isPGroup_of_coprime {A : Type*} [Group A] [Finite A]
    {p : ℕ} [Fact p.Prime] (hA : IsPGroup p A) (hcop : Nat.Coprime p (Nat.card A)) :
    Nat.card A = 1 := by
  rcases hA.exists_card_eq with ⟨n, hn⟩
  cases n with
  | zero => simpa [Nat.card_eq_fintype_card] using hn
  | succ n =>
      have hpdvd : p ∣ Nat.card A := by
        rw [hn]
        exact ⟨p ^ n, by rw [pow_succ, mul_comm]⟩
      exact absurd hpdvd ((Nat.Prime.coprime_iff_not_dvd Fact.out).mp hcop)

theorem exists_pow_mem_of_commutator_action {r : ℕ} [Fact r.Prime] {U W T L : Subgroup G}
    (hTW : T ≤ W) (hWU : W ≤ U) (hUT : U ≤ normalizer (T : Set G))
    (hUW : U ≤ normalizer (W : Set G)) (hLU : L ≤ normalizer (U : Set G))
    (hLW : L ≤ normalizer (W : Set G)) (hLT : L ≤ normalizer (T : Set G))
    (hcomm : ⁅U, L⁆ = U) (hWL : ⁅W, L⁆ ≤ T)
    (hab : ∀ x ∈ U, ∀ y ∈ U, ⁅x, y⁆ ∈ W) (hexp : ∀ x ∈ U, x ^ r ∈ W) :
    ∀ u ∈ U, ∃ k : ℕ, u ^ r ^ k ∈ T := by
  classical
  let Γ : Subgroup G := U ⊔ L
  have hUΓ : U ≤ Γ := le_sup_left
  have hLΓ : L ≤ Γ := le_sup_right
  have hTΓ : T ≤ Γ := hTW.trans (hWU.trans hUΓ)
  have hWΓ : W ≤ Γ := hWU.trans hUΓ
  have hTnormalΓ : (T.subgroupOf Γ).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTΓ).mpr (sup_le hUT hLT)
  letI : (T.subgroupOf Γ).Normal := hTnormalΓ
  let π : Γ →* (Γ ⧸ T.subgroupOf Γ) := QuotientGroup.mk' _
  let B : Subgroup (Γ ⧸ T.subgroupOf Γ) := (U.subgroupOf Γ).map π
  let A : Subgroup (Γ ⧸ T.subgroupOf Γ) := (W.subgroupOf Γ).map π
  let C : Subgroup (Γ ⧸ T.subgroupOf Γ) := (L.subgroupOf Γ).map π
  have hUnormalΓ : (U.subgroupOf Γ).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUΓ).mpr (sup_le Subgroup.le_normalizer hLU)
  have hWnormalΓ : (W.subgroupOf Γ).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWΓ).mpr (sup_le hUW hLW)
  have hBnormal : B.Normal :=
    Subgroup.Normal.map hUnormalΓ π (QuotientGroup.mk'_surjective _)
  haveI : B.Normal := hBnormal
  have hAnormal : A.Normal :=
    Subgroup.Normal.map hWnormalΓ π (QuotientGroup.mk'_surjective _)
  have hΓtop : (U.subgroupOf Γ) ⊔ (L.subgroupOf Γ) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hUΓ hLΓ, Subgroup.subgroupOf_self]
  have hQBC : B ⊔ C = ⊤ := by
    dsimp only [B, C]
    rw [← Subgroup.map_sup, hΓtop, Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)
  have hULΓ : ⁅U.subgroupOf Γ, L.subgroupOf Γ⁆ = U.subgroupOf Γ := by
    apply Subgroup.map_injective (f := Γ.subtype) Subtype.coe_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hUΓ,
      Subgroup.map_subgroupOf_eq_of_le hLΓ, hcomm]
  have hBC : ⁅B, C⁆ = B := by
    dsimp only [B, C]
    rw [← Subgroup.map_commutator, hULΓ]
  have hWLΓ : ⁅W.subgroupOf Γ, L.subgroupOf Γ⁆ ≤ T.subgroupOf Γ := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hx' : (x : G) ∈ W := hx
    have hy' : (y : G) ∈ L := hy
    show Γ.subtype ⁅x, y⁆ ∈ T
    rw [map_commutatorElement Γ.subtype x y]
    exact hWL (Subgroup.commutator_mem_commutator hx' hy')
  have hAC : ⁅A, C⁆ = ⊥ := by
    dsimp only [A, C]
    rw [← Subgroup.map_commutator, eq_bot_iff]
    refine (Subgroup.map_mono hWLΓ).trans ?_
    show (T.subgroupOf Γ).map (QuotientGroup.mk' (T.subgroupOf Γ)) ≤ ⊥
    rw [QuotientGroup.map_mk'_self]
  have hAB : ⁅A, B⁆ = ⊥ := r920imn_commutator_commutator_eq_bot hAnormal hAC hBC
  have hAZ : A ≤ Subgroup.center (Γ ⧸ T.subgroupOf Γ) := by
    intro a ha
    rw [Subgroup.mem_center_iff]
    intro q
    have hq : q ∈ B ⊔ C := by rw [hQBC]; exact Subgroup.mem_top q
    obtain ⟨b, hb, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hq
    have hab' : ⁅a, b⁆ = 1 := by
      have h := Subgroup.commutator_mem_commutator ha hb
      rw [hAB] at h
      simpa using h
    have hac' : ⁅a, c⁆ = 1 := by
      have h := Subgroup.commutator_mem_commutator ha hc
      rw [hAC] at h
      simpa using h
    have hab2 : a * b = b * a := commutatorElement_eq_one_iff_mul_comm.mp hab'
    have hac2 : a * c = c * a := commutatorElement_eq_one_iff_mul_comm.mp hac'
    calc (b * c) * a = b * (c * a) := by group
      _ = b * (a * c) := by rw [← hac2]
      _ = (b * a) * c := by group
      _ = (a * b) * c := by rw [← hab2]
      _ = a * (b * c) := by group
  have hUUW : ⁅U.subgroupOf Γ, U.subgroupOf Γ⁆ ≤ W.subgroupOf Γ := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hx' : (x : G) ∈ U := hx
    have hy' : (y : G) ∈ U := hy
    have h := hab (x : G) hx' (y : G) hy'
    show Γ.subtype ⁅x, y⁆ ∈ W
    rw [map_commutatorElement Γ.subtype x y]
    exact h
  have hBBle : ⁅B, B⁆ ≤ A := by
    dsimp only [B, A]
    rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono hUUW
  have hABle : A ≤ B := by
    dsimp only [A, B]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono Γ hWU)
  haveI : (A.subgroupOf B).Normal := hAnormal.subgroupOf B
  have hBpow : ∀ x ∈ B, x ^ r ∈ A := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    have hu' : (u : G) ∈ U := hu
    rw [← map_pow π u r]
    refine Subgroup.mem_map_of_mem π ?_
    have h := hexp (u : G) hu'
    simpa [Subgroup.mem_subgroupOf, map_pow] using h
  haveI : IsMulCommutative (↥B ⧸ A.subgroupOf B) := by
    rw [Subgroup.Normal.quotient_commutative_iff_commutator_le, commutator_eq_closure]
    refine (Subgroup.closure_le (K := A.subgroupOf B)).2 ?_
    rintro x ⟨p, q, rfl⟩
    have h := hBBle (Subgroup.commutator_mem_commutator p.2 q.2)
    show B.subtype ⁅p, q⁆ ∈ A
    rw [map_commutatorElement]
    exact h
  have hBAp : IsPGroup r (↥B ⧸ A.subgroupOf B) := by
    intro x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (A.subgroupOf B) x
    refine ⟨1, ?_⟩
    rw [pow_one, ← map_pow (QuotientGroup.mk' (A.subgroupOf B)) b r]
    exact (QuotientGroup.eq_one_iff (N := A.subgroupOf B) (b ^ r)).mpr (hBpow b b.2)
  have hBnil : Group.IsNilpotent ↥B := by
    refine _root_.isNilpotent_of_ker_le_center
      (G := ↥B) (f := QuotientGroup.mk' (A.subgroupOf B)) ?_
    rw [QuotientGroup.ker_mk']
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hAZ hx) (y : Γ ⧸ T.subgroupOf Γ))
  let P0 : Subgroup ↥B := CFSG.pCore r ↥B
  let R0 : Subgroup ↥B := CFSG.pPrimeCore r ↥B
  let P : Subgroup (Γ ⧸ T.subgroupOf Γ) := P0.map B.subtype
  let R : Subgroup (Γ ⧸ T.subgroupOf Γ) := R0.map B.subtype
  have hPR : P ⊔ R = B := by
    dsimp only [P, R, P0, R0]
    rw [← Subgroup.map_sup]
    have htop : CFSG.pCore r ↥B ⊔ CFSG.pPrimeCore r ↥B = ⊤ :=
      top_unique (CFSG.nilpotent_top_le_pCore_sup_pPrimeCore (Q := ↥B) (p := r) hBnil)
    rw [htop, Subgroup.map_top, Subgroup.range_subtype]
  have hR0A : R0 ≤ A.subgroupOf B := by
    have h1 : Nat.card (R0.map (QuotientGroup.mk' (A.subgroupOf B))) = 1 :=
      r920imn_card_eq_one_of_isPGroup_of_coprime
        (hBAp.to_subgroup (R0.map (QuotientGroup.mk' (A.subgroupOf B))))
        (Nat.Coprime.of_dvd_right (Subgroup.card_map_dvd R0 _)
          (CFSG.pPrimeCore_coprime_card (G := ↥B) (p := r)))
    have hbot : R0.map (QuotientGroup.mk' (A.subgroupOf B)) = ⊥ :=
      (Subgroup.card_eq_one).1 h1
    have hle :=
      (Subgroup.map_eq_bot_iff (f := QuotientGroup.mk' (A.subgroupOf B)) (H := R0)).1 hbot
    rwa [QuotientGroup.ker_mk'] at hle
  have hRA : R ≤ A := by
    dsimp only [R, A]
    calc R0.map B.subtype ≤ (A.subgroupOf B).map B.subtype := Subgroup.map_mono hR0A
      _ = A := Subgroup.map_subgroupOf_eq_of_le hABle
  have hCPnorm : C ≤ Subgroup.normalizer (P : Set (Γ ⧸ T.subgroupOf Γ)) := by
    rw [Subgroup.le_normalizer_iff]
    intro c hc p hp
    obtain ⟨p0, hp0, rfl⟩ := Subgroup.mem_map.mp hp
    have hconj : MulAut.conjNormal c p0 ∈ CFSG.pCore r ↥B := by
      rw [← Subgroup.characteristic_iff_map_eq.mp
        (inferInstance : (CFSG.pCore r ↥B).Characteristic) (MulAut.conjNormal c)]
      exact Subgroup.mem_map_of_mem _ hp0
    have hcoe : (B.subtype (MulAut.conjNormal c p0) : Γ ⧸ T.subgroupOf Γ) =
        c * B.subtype p0 * c⁻¹ := MulAut.conjNormal_apply c p0
    rw [← hcoe]
    exact Subgroup.mem_map_of_mem B.subtype hconj
  have hBCleP : ⁅B, C⁆ ≤ P := by
    rw [Subgroup.commutator_le]
    intro b hb c hc
    have hb' : b ∈ P ⊔ R := by rw [hPR]; exact hb
    haveI : R.Normal := Subgroup.normal_of_le_center (hRA.trans hAZ)
    obtain ⟨p, hp, r, hr, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hb'
    have hrZ : r ∈ Subgroup.center (Γ ⧸ T.subgroupOf Γ) := hAZ (hRA hr)
    have hrc : ⁅r, c⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hrZ c).symm
    rw [commutatorElement_mul_left_eq_conj_mul, hrc, mul_one, mul_inv_cancel, one_mul]
    have hCPle : ⁅C, P⁆ ≤ P :=
      (Subgroup.le_normalizer_iff_commutator_le_right (H := C) (K := P)).mp hCPnorm
    have hmem : ⁅p, c⁆ ∈ ⁅C, P⁆ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hp hc
    exact hCPle hmem
  have hPleB : P ≤ B := Subgroup.map_subtype_le P0
  have hBleP : B ≤ P := by rw [← hBC]; exact hBCleP
  have hBP : B = P := le_antisymm hBleP hPleB
  have hBr : IsPGroup r B := by
    rw [hBP]
    exact (CFSG.pCore_isPGroup (G := ↥B) (p := r)).map B.subtype
  intro u hu
  let uΓ : Γ := ⟨u, hUΓ hu⟩
  have hbB : π uΓ ∈ B :=
    Subgroup.mem_map_of_mem π (show uΓ ∈ U.subgroupOf Γ from hu)
  obtain ⟨k, hk⟩ := hBr ⟨π uΓ, hbB⟩
  refine ⟨k, ?_⟩
  have hk' : (π uΓ) ^ r ^ k = 1 := by
    simpa using congrArg (fun x : ↥B => (x : Γ ⧸ T.subgroupOf Γ)) hk
  have hker0 : π (uΓ ^ r ^ k) = 1 := by rw [map_pow]; exact hk'
  have hker : uΓ ^ r ^ k ∈ T.subgroupOf Γ :=
    (QuotientGroup.eq_one_iff (N := T.subgroupOf Γ) (uΓ ^ r ^ k)).mp hker0
  have hker' : ((uΓ ^ r ^ k : Γ) : G) ∈ T := hker
  have hval : ((uΓ ^ r ^ k : Γ) : G) = u ^ r ^ k := by simp [uΓ]
  rwa [hval] at hker'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
