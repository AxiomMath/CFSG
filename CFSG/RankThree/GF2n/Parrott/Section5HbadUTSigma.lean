module

public import CFSG.RankThree.GF2n.Parrott.Section5HbadUTLocal
public import CFSG.RankThree.GF2n.Parrott.Section5LocalT
public import CFSG.RankThree.GF2n.Parrott.OddLiftCentralizer
public import CFSG.GroupTheory.PCore.Transport
public import CFSG.Holt.PSL2Natural.Defs
public import CFSG.Holt.PermFacts
public import CFSG.Holt.ThreePoint
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalBender
public import CFSG.LocalAnalysis.QuasithinUnique.K1.ExceptionalCatSuzuki
public import CFSG.LocalAnalysis.UniquenessCase.UC6Basic
public import CFSG.Quasithin.Background.E2NParamStar
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS3
public import CFSG.Quasithin.Vol2.E2TenEight
public import CFSG.RankThree.GF2n.Parrott.ZFusionControl
public import CFSG.RankThree.Holt.Basic

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped Matrix

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "Mat8" => Matrix (Fin 8) (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)

private theorem zmod2_eq_one_of_ne_zero {x : ZMod 2} (hx : x ≠ 0) : x = 1 := by
  have h : x = 0 ∨ x = 1 := by revert x; decide
  rcases h with h | h
  · exact absurd h hx
  · exact h

private theorem V_add_self (v : V) : v + v = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (v i)

private theorem hbad_fix_of_factors (U S : Mat8) (hSU : S * U = U * S)
    (m : V)
    (hsum : S *ᵥ (S *ᵥ (U *ᵥ m + m)) + S *ᵥ (U *ᵥ m + m) + (U *ᵥ m + m) = 0) :
    U *ᵥ (m + S *ᵥ m + S *ᵥ (S *ᵥ m)) = m + S *ᵥ m + S *ᵥ (S *ᵥ m) := by
  have hSUm : ∀ v : V, U *ᵥ (S *ᵥ v) = S *ᵥ (U *ᵥ v) := by
    intro v
    calc U *ᵥ (S *ᵥ v) = (U * S) *ᵥ v := Matrix.mulVec_mulVec v U S
      _ = (S * U) *ᵥ v := by rw [hSU]
      _ = S *ᵥ (U *ᵥ v) := (Matrix.mulVec_mulVec v S U).symm
  have e1 : S *ᵥ (U *ᵥ m) + S *ᵥ m = S *ᵥ (U *ᵥ m + m) :=
    (Matrix.mulVec_add S (U *ᵥ m) m).symm
  have e2 : S *ᵥ (S *ᵥ (U *ᵥ m)) + S *ᵥ (S *ᵥ m) = S *ᵥ (S *ᵥ (U *ᵥ m + m)) := by
    rw [← Matrix.mulVec_add S (S *ᵥ (U *ᵥ m)) (S *ᵥ m), ← Matrix.mulVec_add]
  have h0 : U *ᵥ (m + S *ᵥ m + S *ᵥ (S *ᵥ m)) + (m + S *ᵥ m + S *ᵥ (S *ᵥ m)) = 0 := by
    rw [Matrix.mulVec_add, Matrix.mulVec_add]
    simp only [hSUm]
    rw [show (U *ᵥ m + S *ᵥ (U *ᵥ m) + S *ᵥ (S *ᵥ (U *ᵥ m))) +
          (m + S *ᵥ m + S *ᵥ (S *ᵥ m)) =
        (S *ᵥ (S *ᵥ (U *ᵥ m)) + S *ᵥ (S *ᵥ m)) + (S *ᵥ (U *ᵥ m) + S *ᵥ m) + (U *ᵥ m + m)
        from by simp only [add_comm, add_left_comm]]
    rw [e2, e1]
    exact hsum
  have hYY : (m + S *ᵥ m + S *ᵥ (S *ᵥ m)) + (m + S *ᵥ m + S *ᵥ (S *ᵥ m)) = 0 :=
    V_add_self _
  have hstep : U *ᵥ (m + S *ᵥ m + S *ᵥ (S *ᵥ m)) =
      (U *ᵥ (m + S *ᵥ m + S *ᵥ (S *ᵥ m)) + (m + S *ᵥ m + S *ᵥ (S *ᵥ m))) +
        (m + S *ᵥ m + S *ᵥ (S *ᵥ m)) := by
    conv_rhs => rw [add_assoc]
    rw [hYY, add_zero]
  rw [hstep, h0, zero_add]

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

section HbadZ

theorem conj_eq_z_mul_of_not_mem_QP45 (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) {a : ↥(H z)}
    (ha : qH (z := z) D a ∉ QP45.originalSubgroup.subgroupOf QA45.originalSubgroup) {ζ : G}
    (hζ : ζ ∈ centerIn (J z)) (hζz : ζ ∉ Subgroup.zpowers z) :
    (a : G) * ζ * (a : G)⁻¹ = z * ζ := by
  have hζ2 : orderOf ζ = 2 := by
    have : Fact (Nat.Prime 2) := ⟨by norm_num⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact centerIn_J_sq h hζ) (by
      intro h1
      exact hζz (h1 ▸ Subgroup.one_mem _))
  exact conj_z1_eq_of_not_mem_centralizer h hζ hζz hζ2 a.2 (by
    intro hc
    exact ha ((mem_centralizer_z1_iff_qH_mem_QP45 (z := z) D h hZ hζ hζz hζ2 a).mp hc))

end HbadZ

private theorem hbad_mul_conj_eq (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) {a c : G}
    (ha : a ∈ J z) (hc : c ∈ J z) :
    a * c * a⁻¹ = (if b (hbadCoord h P a) (hbadCoord h P c) = 0 then 1 else z) * c := by
  by_cases hb : b (hbadCoord h P a) (hbadCoord h P c) = 0
  · rw [if_pos hb, one_mul]
    have hcomm : a * c = c * a := (commute_iff_hbadCoord (z := z) D h P hP ha hc).mpr hb
    rw [hcomm]; group
  · rw [if_neg hb]
    have hb1 : b (hbadCoord h P a) (hbadCoord h P c) = 1 := zmod2_eq_one_of_ne_zero hb
    have h2 : a * c * a⁻¹ = z * c := by
      have h3 := congrArg (fun t => t * c)
        (commutator_eq_z_of_hbadCoord (z := z) D h P hP ha hc hb1)
      simpa [mul_assoc] using h3
    rw [h2]

section Y

variable {y : G} (hyH : y ∈ H z) (hy : y * y = 1)
  (hq : qH (z := z) D ⟨y, hyH⟩ = uA * tA)
include hyH hy hq

theorem exists_sigma_of_utA (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) :
    ∃ s : ↥(H z), (s : G) * y = y * s ∧ s ^ 3 = 1 ∧ qH (z := z) D s = hbadS := by
  classical
  obtain ⟨r, hqr, hr3⟩ := exists_orderOf_three_lift (z := z) D hbadS_pow_three hbadS_ne_one
  have hrrr : (r : G) * r * r = 1 := by
    have h3 : (r : ↥(H z)) ^ 3 = 1 := by rw [← hr3]; exact pow_orderOf_eq_one r
    have h4 : ((r : ↥(H z)) : G) ^ 3 = 1 := by rw [← Subgroup.coe_pow, h3, Subgroup.coe_one]
    rwa [pow_three'] at h4
  have hyinv : y⁻¹ = y := by
    rw [inv_eq_iff_mul_eq_one]; exact hy
  have hJW : ∀ x : ↥(H z), qH (z := z) D x = uA * tA → (x : G) * x = 1 →
      (y * (x : G)) ∈ J z ∧ (y * (x : G)) * y = y * (y * (x : G)) := by
    intro x hxq hxx
    have hxH : y * (x : G) ∈ H z := (H z).mul_mem hyH x.2
    have hq1 : qH (z := z) D (⟨y * (x : G), hxH⟩ : ↥(H z)) = 1 := by
      rw [show (⟨y * (x : G), hxH⟩ : ↥(H z)) = ⟨y, hyH⟩ * x from rfl, map_mul, hq, hxq,
        utA_mul_self]
    have hjJ : y * (x : G) ∈ J z := Subgroup.mem_subgroupOf.mp ((J_mem_iff D _).mpr hq1)
    refine ⟨hjJ, ?_⟩
    have hxy : (x : G) = y * (y * (x : G)) := by rw [← mul_assoc, hy, one_mul]
    have h1 : (y * (y * (x : G))) * (y * (y * (x : G))) = 1 := by rw [← hxy]; exact hxx
    have h3 : ((y * (y * (x : G))) * y) * (y * (x : G)) = 1 := by
      rwa [← mul_assoc] at h1
    have h4 : (y * (y * (x : G))) * y = (y * (x : G))⁻¹ := by
      calc (y * (y * (x : G))) * y
          = ((y * (y * (x : G))) * y) * ((y * (x : G)) * (y * (x : G))⁻¹) := by
            rw [mul_inv_cancel, mul_one]
        _ = (((y * (y * (x : G))) * y) * (y * (x : G))) * (y * (x : G))⁻¹ := by group
        _ = (y * (x : G))⁻¹ := by rw [h3, one_mul]
    have h5 : y * (y * (x : G)) * y⁻¹ = (y * (x : G))⁻¹ := by
      rw [hyinv]
      exact h4
    have h6 : hbadCoord h P (y * (y * (x : G)) * y⁻¹) =
        ((rhoA (uA * tA) : GL8) : Mat8) *ᵥ hbadCoord h P (y * (x : G)) := by
      have h7 := hbadCoord_conj (z := z) D h P hP (c := y) (k := y * (x : G)) hyH hjJ
      rw [hq] at h7
      exact h7
    have hfix : ((rhoA (uA * tA) : GL8) : Mat8) *ᵥ hbadCoord h P (y * (x : G)) =
        hbadCoord h P (y * (x : G)) := by
      rw [← h6, h5, hbadCoord_inv h P hjJ]
    exact (commute_iff_of_utA D hyH hy hq h P hP hjJ).mpr hfix
  have hJB : ∀ j : ↥(J z ⊓ Subgroup.centralizer ({y} : Set G)),
      qH (z := z) D (⟨y * (j.1 : G), (H z).mul_mem hyH (J_le_H (Subgroup.mem_inf.mp j.2).1)⟩ :
          ↥(H z)) = uA * tA ∧ (y * (j.1 : G)) * (y * (j.1 : G)) = 1 := by
    intro j
    have hjJ : (j.1 : G) ∈ J z := (Subgroup.mem_inf.mp j.2).1
    have hjH : (j.1 : G) ∈ H z := J_le_H hjJ
    have hjy : (j.1 : G) * y = y * (j.1 : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp j.2).2
    have hjq : qH (z := z) D (⟨j.1, hjH⟩ : ↥(H z)) = 1 :=
      (J_mem_iff D _).mp (Subgroup.mem_subgroupOf.mpr hjJ)
    refine ⟨?_, ?_⟩
    · rw [show (⟨y * (j.1 : G), (H z).mul_mem hyH hjH⟩ : ↥(H z)) = ⟨y, hyH⟩ * ⟨j.1, hjH⟩
          from rfl, map_mul, hq, hjq, mul_one]
    · have hjj : (j.1 : G) * (j.1 : G) = 1 :=
        mul_self_eq_one_of_utA D hyH hy hq h P hP hjJ hjy
      calc (y * (j.1 : G)) * (y * (j.1 : G)) = y * ((j.1 : G) * y) * (j.1 : G) := by group
        _ = y * (y * (j.1 : G)) * (j.1 : G) := by rw [hjy]
        _ = (y * y) * ((j.1 : G) * (j.1 : G)) := by group
        _ = 1 := by rw [hy, hjj, mul_one]
  let X : Type _ := {x : ↥(H z) // qH (z := z) D x = uA * tA ∧ (x : G) * x = 1}
  let eX : X ≃ ↥(J z ⊓ Subgroup.centralizer ({y} : Set G)) :=
    { toFun := fun x =>
        ⟨y * (x.1 : G), Subgroup.mem_inf.mpr ⟨(hJW x.1 x.2.1 x.2.2).1,
          Subgroup.mem_centralizer_singleton_iff.mpr (hJW x.1 x.2.1 x.2.2).2⟩⟩
      invFun := fun j =>
        ⟨⟨y * (j.1 : G), (H z).mul_mem hyH (J_le_H (Subgroup.mem_inf.mp j.2).1)⟩, hJB j⟩
      left_inv := fun x => by
        apply Subtype.ext
        apply Subtype.ext
        show y * (y * (x.1 : G)) = (x.1 : G)
        rw [← mul_assoc, hy, one_mul]
      right_inv := fun j => by
        apply Subtype.ext
        show y * (y * (j.1 : G)) = (j.1 : G)
        rw [← mul_assoc, hy, one_mul] }
  have hcardX : Nat.card X = 64 := by
    rw [Nat.card_congr eX, card_J_inf_centralizer_of_utA D hyH hy hq h P hP]
  let _ : Fintype X := Fintype.ofFinite X
  have hnd : ¬ 3 ∣ Fintype.card X := by
    rw [← Nat.card_eq_fintype_card, hcardX]
    norm_num
  have hconjX : ∀ (u : ↥(H z)), qH (z := z) D u * (uA * tA) = (uA * tA) * qH (z := z) D u →
      ∀ x : X, qH (z := z) D (u * x.1 * u⁻¹) = uA * tA ∧
        ((u * x.1 * u⁻¹ : ↥(H z)) : G) * (u * x.1 * u⁻¹) = 1 := by
    intro u hu x
    refine ⟨?_, ?_⟩
    · rw [map_mul, map_mul, map_inv, x.2.1, hu]
      group
    · show ((u : G) * (x.1 : G) * (u : G)⁻¹) * ((u : G) * (x.1 : G) * (u : G)⁻¹) = 1
      calc ((u : G) * (x.1 : G) * (u : G)⁻¹) * ((u : G) * (x.1 : G) * (u : G)⁻¹)
          = (u : G) * ((x.1 : G) * (x.1 : G)) * (u : G)⁻¹ := by group
        _ = 1 := by rw [x.2.2]; group
  have hrcomm : qH (z := z) D r * (uA * tA) = (uA * tA) * qH (z := z) D r := by
    rw [hqr]; exact hbadS_comm_utA
  have hrinvcomm : qH (z := z) D r⁻¹ * (uA * tA) = (uA * tA) * qH (z := z) D r⁻¹ := by
    rw [map_inv]
    have h2 : (qH (z := z) D r)⁻¹ * (uA * tA) * (qH (z := z) D r) = uA * tA := by
      rw [mul_assoc, ← hrcomm]
      group
    calc (qH (z := z) D r)⁻¹ * (uA * tA)
        = ((qH (z := z) D r)⁻¹ * (uA * tA) * (qH (z := z) D r)) *
            (qH (z := z) D r)⁻¹ := by group
      _ = (uA * tA) * (qH (z := z) D r)⁻¹ := by rw [h2]
  let σ : Equiv.Perm X :=
    { toFun := fun x => ⟨r * x.1 * r⁻¹, hconjX r hrcomm x⟩
      invFun := fun x => ⟨r⁻¹ * x.1 * (r⁻¹)⁻¹, hconjX r⁻¹ hrinvcomm x⟩
      left_inv := fun x => by
        apply Subtype.ext
        apply Subtype.ext
        group
      right_inv := fun x => by
        apply Subtype.ext
        apply Subtype.ext
        group }
  have hσ3 : σ ^ 3 ^ 1 = 1 := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    apply Subtype.ext
    show (r : G) * (r * (r * (x.1 : G) * (r : G)⁻¹) * (r : G)⁻¹) * (r : G)⁻¹ = (x.1 : G)
    calc (r : G) * (r * (r * (x.1 : G) * (r : G)⁻¹) * (r : G)⁻¹) * (r : G)⁻¹
        = ((r : G) * r * r) * (x.1 : G) * ((r : G) * r * r)⁻¹ := by group
      _ = (x.1 : G) := by rw [hrrr]; group
  obtain ⟨x₀, hx₀⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 3) (n := 1) hnd hσ3
  have hx₀conj : (r : G) * (x₀.1 : G) * (r : G)⁻¹ = (x₀.1 : G) :=
    congrArg (fun t : ↥(H z) => (t : G)) (congrArg Subtype.val hx₀)
  obtain ⟨k, hkJ, ζ, hζ, hkeq⟩ :=
    exists_eq_conj_mul_of_utA D hyH hy hq h P hP x₀.1.2 x₀.2.1 x₀.2.2
  have hrζ : (r : G) * ζ = ζ * (r : G) := by
    have hZ1 : centerIn (J z) ≤ Subgroup.centralizer ({(r : G)} : Set G) :=
      centerIn_le_centralizer_of_conjZ_eq_one (z := z) (x := r)
        (conjZ_eq_one_of_mem_Q (z := z) D h r
          (Subgroup.mem_subgroupOf.mpr (by rw [hqr]; exact hbadS_mem_QP45)))
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hZ1 hζ)).symm
  have hrkyk : (r : G) * (k * y * k⁻¹) = (k * y * k⁻¹) * (r : G) := by
    have h2 : (r : G) * ζ * (r : G)⁻¹ = ζ := by rw [hrζ]; group
    have h6 : (r : G) * ((k * y * k⁻¹) * ζ) * (r : G)⁻¹ = (k * y * k⁻¹) * ζ := by
      rw [← hkeq]; exact hx₀conj
    have h7 : (r : G) * (k * y * k⁻¹) * (r : G)⁻¹ * ζ = (k * y * k⁻¹) * ζ := by
      calc (r : G) * (k * y * k⁻¹) * (r : G)⁻¹ * ζ
          = ((r : G) * (k * y * k⁻¹) * (r : G)⁻¹) * ((r : G) * ζ * (r : G)⁻¹) := by rw [h2]
        _ = (r : G) * ((k * y * k⁻¹) * ζ) * (r : G)⁻¹ := by group
        _ = (k * y * k⁻¹) * ζ := h6
    have h5 : (r : G) * (k * y * k⁻¹) * (r : G)⁻¹ = k * y * k⁻¹ := mul_right_cancel h7
    calc (r : G) * (k * y * k⁻¹) = ((r : G) * (k * y * k⁻¹) * (r : G)⁻¹) * (r : G) := by group
      _ = (k * y * k⁻¹) * (r : G) := by rw [h5]
  let kH : ↥(H z) := ⟨k, J_le_H hkJ⟩
  let s : ↥(H z) := kH⁻¹ * r * kH
  have hkq : qH (z := z) D kH = 1 :=
    (J_mem_iff D kH).mp (Subgroup.mem_subgroupOf.mpr hkJ)
  have hsk : (s : G) = k⁻¹ * (r : G) * k := rfl
  refine ⟨s, ?_, ?_, ?_⟩
  · show (s : G) * y = y * (s : G)
    rw [hsk]
    calc k⁻¹ * (r : G) * k * y = k⁻¹ * ((r : G) * (k * y * k⁻¹)) * k := by group
      _ = k⁻¹ * ((k * y * k⁻¹) * (r : G)) * k := by rw [hrkyk]
      _ = y * (k⁻¹ * (r : G) * k) := by group
  · apply Subtype.ext
    show (k⁻¹ * (r : G) * k) ^ 3 = 1
    rw [pow_three']
    calc (k⁻¹ * (r : G) * k) * (k⁻¹ * (r : G) * k) * (k⁻¹ * (r : G) * k)
        = k⁻¹ * ((r : G) * r * r) * k := by group
      _ = 1 := by rw [hrrr]; group
  · show qH (z := z) D (kH⁻¹ * r * kH) = hbadS
    rw [map_mul, map_mul, map_inv, hqr, hkq]
    group

theorem conj_mul_inv_mul_of_utA (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) {s : ↥(H z)}
    (hqs : qH (z := z) D s = hbadS) {k : G} (hk : k ∈ J z) :
    (k * y * k⁻¹ * y⁻¹) *
        (((s : G) * k * (s : G)⁻¹) * y * ((s : G) * k * (s : G)⁻¹)⁻¹ * y⁻¹) *
        (((s : G) * ((s : G) * k * (s : G)⁻¹) * (s : G)⁻¹) * y *
          ((s : G) * ((s : G) * k * (s : G)⁻¹) * (s : G)⁻¹)⁻¹ * y⁻¹) =
      if b (hbadCoord h P k) (((rhoA hbadS : GL8) : Mat8) *ᵥ
          (((rhoA (uA * tA) : GL8) : Mat8) *ᵥ hbadCoord h P k + hbadCoord h P k)) = 0 then 1
      else z := by
  classical
  set U : Mat8 := ((rhoA (uA * tA) : GL8) : Mat8) with hUdef
  set S : Mat8 := ((rhoA hbadS : GL8) : Mat8) with hSdef
  set m : V := hbadCoord h P k with hmdef
  set w : V := U *ᵥ m + m with hwdef
  set k₁ : G := (s : G) * k * (s : G)⁻¹ with hk1def
  set k₂ : G := (s : G) * k₁ * (s : G)⁻¹ with hk2def
  set xk : G := k * y * k⁻¹ * y⁻¹ with hxkdef
  set x1 : G := k₁ * y * k₁⁻¹ * y⁻¹ with hx1def
  set x2 : G := k₂ * y * k₂⁻¹ * y⁻¹ with hx2def
  set x12 : G := (k₁ * k₂) * y * (k₁ * k₂)⁻¹ * y⁻¹ with hx12def
  have hk₁J : k₁ ∈ J z := H_conj_mem_J s hk
  have hk₂J : k₂ ∈ J z := H_conj_mem_J s hk₁J
  have hKJ : k * k₁ * k₂ ∈ J z := Subgroup.mul_mem _ (Subgroup.mul_mem _ hk hk₁J) hk₂J
  have hx1J : x1 ∈ J z := (hbadCoord_conj_mul_inv_of_utA (z := z) D hyH hq h P hP (y := y) hk₁J).1
  have hx2J : x2 ∈ J z := (hbadCoord_conj_mul_inv_of_utA (z := z) D hyH hq h P hP (y := y) hk₂J).1
  have hxkJ : xk ∈ J z := (hbadCoord_conj_mul_inv_of_utA (z := z) D hyH hq h P hP (y := y) hk).1
  have hx21J : x2 * x1 ∈ J z := Subgroup.mul_mem _ hx2J hx1J
  have hqs' : qH (z := z) D (⟨(s : G), s.2⟩ : ↥(H z)) = hbadS := hqs
  have hc₁ : hbadCoord h P k₁ = S *ᵥ m := by
    have h' := hbadCoord_conj (z := z) D h P hP (c := (s : G)) (k := k) s.2 hk
    rw [hqs'] at h'
    exact h'
  have hc₂ : hbadCoord h P k₂ = S *ᵥ (S *ᵥ m) := by
    have h' := hbadCoord_conj (z := z) D h P hP (c := (s : G)) (k := k₁) s.2 hk₁J
    rw [hqs', hc₁] at h'
    exact h'
  have hSU : S * U = U * S := by
    have h1 : (rhoA hbadS : GL8) * (rhoA (uA * tA) : GL8) =
        (rhoA (uA * tA) : GL8) * (rhoA hbadS : GL8) := by
      rw [← map_mul, ← map_mul, hbadS_comm_utA]
    show ((rhoA hbadS : GL8) : Mat8) * ((rhoA (uA * tA) : GL8) : Mat8) =
      ((rhoA (uA * tA) : GL8) : Mat8) * ((rhoA hbadS : GL8) : Mat8)
    rw [← Units.val_mul, ← Units.val_mul, h1]
  have hSUm : ∀ v : V, U *ᵥ (S *ᵥ v) = S *ᵥ (U *ᵥ v) := by
    intro v
    calc U *ᵥ (S *ᵥ v) = (U * S) *ᵥ v := Matrix.mulVec_mulVec v U S
      _ = (S * U) *ᵥ v := by rw [hSU]
      _ = S *ᵥ (U *ᵥ v) := (Matrix.mulVec_mulVec v S U).symm
  have hU2 : U * U = 1 := by
    have h1 : (rhoA (uA * tA) : GL8) * (rhoA (uA * tA) : GL8) = 1 := by
      rw [← map_mul, utA_mul_self, map_one]
    show ((rhoA (uA * tA) : GL8) : Mat8) * ((rhoA (uA * tA) : GL8) : Mat8) = 1
    rw [← Units.val_mul, ← map_mul, utA_mul_self, map_one, Units.val_one]
  have hwU : U *ᵥ w = w := by
    calc U *ᵥ w = U *ᵥ (U *ᵥ m + m) := rfl
      _ = U *ᵥ (U *ᵥ m) + U *ᵥ m := by rw [Matrix.mulVec_add]
      _ = (U * U) *ᵥ m + U *ᵥ m := by rw [Matrix.mulVec_mulVec m U U]
      _ = 1 *ᵥ m + U *ᵥ m := by rw [hU2]
      _ = m + U *ᵥ m := by rw [Matrix.one_mulVec]
      _ = U *ᵥ m + m := by rw [add_comm]
      _ = w := rfl
  have hsum : S *ᵥ (S *ᵥ w) + S *ᵥ w + w = 0 := spin_hbadS_sum w hwU
  have hbmw : b m w = 0 := by
    have hqU : q (U *ᵥ m) = q m := spinQuad_invariant (uA * tA) m
    have hqw : q w = 0 := spin_q_eq_zero_of_utA w hwU
    have hmw : m + w = U *ᵥ m := by
      calc m + w = m + (U *ᵥ m + m) := rfl
        _ = (m + m) + U *ᵥ m := by simp only [add_comm, add_left_comm]
        _ = 0 + U *ᵥ m := by rw [V_add_self]
        _ = U *ᵥ m := zero_add _
    rw [b, hmw, hqU, hqw, add_zero]
    exact CharTwo.add_self_eq_zero (q m)
  have hcxk : hbadCoord h P xk = w := by
    have h' := (hbadCoord_conj_mul_inv_of_utA (z := z) D hyH hq h P hP (y := y) hk).2
    show hbadCoord h P (k * y * k⁻¹ * y⁻¹) = U *ᵥ m + m
    rw [h']
    exact add_comm m (U *ᵥ m)
  have hwm : m + U *ᵥ m = w := by
    rw [show w = U *ᵥ m + m from rfl, add_comm]
  have hcx1 : hbadCoord h P x1 = S *ᵥ w := by
    have h' := (hbadCoord_conj_mul_inv_of_utA (z := z) D hyH hq h P hP (y := y) hk₁J).2
    rw [hc₁] at h'
    show hbadCoord h P (k₁ * y * k₁⁻¹ * y⁻¹) = S *ᵥ w
    rw [h', hSUm, ← Matrix.mulVec_add, hwm]
  have hcx2 : hbadCoord h P x2 = S *ᵥ (S *ᵥ w) := by
    have h' := (hbadCoord_conj_mul_inv_of_utA (z := z) D hyH hq h P hP (y := y) hk₂J).2
    rw [← hx2def, hc₂, ← hUdef] at h'
    have hw' : S *ᵥ (S *ᵥ w) = S *ᵥ (S *ᵥ (U *ᵥ m)) + S *ᵥ (S *ᵥ m) := by
      rw [show w = U *ᵥ m + m from rfl, Matrix.mulVec_add, Matrix.mulVec_add]
    show hbadCoord h P x2 = S *ᵥ (S *ᵥ w)
    rw [h', hw']
    simp only [hSUm]
    exact add_comm _ _
  have hcx21 : hbadCoord h P (x2 * x1) = w := by
    rw [hbadCoord_mul (z := z) h P hx2J hx1J, hcx2, hcx1]
    calc S *ᵥ (S *ᵥ w) + S *ᵥ w
        = S *ᵥ (S *ᵥ w) + S *ᵥ w + w + w := by rw [add_assoc, V_add_self, add_zero]
      _ = w := by rw [hsum, zero_add]
  have hbf : b (hbadCoord h P k₁) (hbadCoord h P x2) = b m (S *ᵥ w) := by
    rw [hc₁, hcx2, spinB_invariant hbadS m (S *ᵥ w)]
  have hfixk : U *ᵥ hbadCoord h P xk = hbadCoord h P xk := by rw [hcxk]; exact hwU
  have hfix1 : U *ᵥ hbadCoord h P x1 = hbadCoord h P x1 := by
    rw [hcx1, hSUm, hwU]
  have hfix2 : U *ᵥ hbadCoord h P x2 = hbadCoord h P x2 := by
    rw [hcx2, hSUm, hSUm, hwU]
  have hxky : xk * y = y * xk := (commute_iff_of_utA D hyH hy hq h P hP hxkJ).mpr hfixk
  have hx1y : x1 * y = y * x1 := (commute_iff_of_utA D hyH hy hq h P hP hx1J).mpr hfix1
  have hx2y : x2 * y = y * x2 := (commute_iff_of_utA D hyH hy hq h P hP hx2J).mpr hfix2
  have hcx1x2 : x1 * x2 = x2 * x1 := commute_of_utA D hyH hy hq h P hP hx1J hx2J hx1y hx2y
  have hcxkx1 : xk * x1 = x1 * xk := commute_of_utA D hyH hy hq h P hP hxkJ hx1J hxky hx1y
  have hcxkx2 : xk * x2 = x2 * xk := commute_of_utA D hyH hy hq h P hP hxkJ hx2J hxky hx2y
  have hKcoord : hbadCoord h P (k * k₁ * k₂) = m + S *ᵥ m + S *ᵥ (S *ᵥ m) := by
    rw [hbadCoord_mul (z := z) h P (Subgroup.mul_mem _ hk hk₁J) hk₂J,
      hbadCoord_mul (z := z) h P hk hk₁J, hc₁, hc₂]
  have hfixK : U *ᵥ hbadCoord h P (k * k₁ * k₂) = hbadCoord h P (k * k₁ * k₂) := by
    rw [hKcoord]
    exact hbad_fix_of_factors U S hSU m hsum
  have hKy : (k * k₁ * k₂) * y = y * (k * k₁ * k₂) := (commute_iff_of_utA D hyH hy hq h P hP hKJ).mpr hfixK
  have hxK1 : (k * k₁ * k₂) * y * (k * k₁ * k₂)⁻¹ * y⁻¹ = 1 := by
    rw [hKy]; group
  have hH1 : ∀ a c : G, (a * c) * y * (a * c)⁻¹ * y⁻¹ =
      a * (c * y * c⁻¹ * y⁻¹) * a⁻¹ * (a * y * a⁻¹ * y⁻¹) := by
    intro a c; group
  have hxK2 : (k * k₁ * k₂) * y * (k * k₁ * k₂)⁻¹ * y⁻¹ = k * x12 * k⁻¹ * xk := by
    have h' := hH1 k (k₁ * k₂)
    rw [mul_assoc k k₁ k₂]
    exact h'
  have hx12 : x12 = k₁ * x2 * k₁⁻¹ * x1 := hH1 k₁ k₂
  set c : G := if b m (S *ᵥ w) = 0 then 1 else z with hcdef
  have hck : k * c * k⁻¹ = c := by
    rw [show c = if b m (S *ᵥ w) = 0 then 1 else z from rfl]
    by_cases hb : b m (S *ᵥ w) = 0
    · rw [if_pos hb]; group
    · rw [if_neg hb]
      have hcomm : k * z = z * k :=
        Subgroup.mem_centralizer_iff.mp (z_centralizes_H h) k (J_le_H hk)
      rw [hcomm]; group
  have hcc : c * c = 1 := by
    rw [show c = if b m (S *ᵥ w) = 0 then 1 else z from rfl]
    by_cases hb : b m (S *ᵥ w) = 0
    · rw [if_pos hb]; group
    · rw [if_neg hb]
      exact centerIn_J_sq h (z_mem_centerIn_J h)
  have hst1 : k₁ * x2 * k₁⁻¹ = c * x2 := by
    rw [hbad_mul_conj_eq D h P hP hk₁J hx2J, hbf,
      show c = if b m (S *ᵥ w) = 0 then 1 else z from rfl]
  have hst2a : k * (x2 * x1) * k⁻¹ = x2 * x1 := by
    rw [hbad_mul_conj_eq D h P hP hk hx21J, hcx21, hbmw]
    rw [if_pos rfl, one_mul]
  have hst2 : k * (c * x2 * x1) * k⁻¹ = c * (x2 * x1) := by
    calc k * (c * x2 * x1) * k⁻¹ = (k * c * k⁻¹) * (k * (x2 * x1) * k⁻¹) := by group
      _ = c * (x2 * x1) := by rw [hck, hst2a]
  have hfin : c * x1 * x2 * xk = 1 := by
    have h1 : (k * k₁ * k₂) * y * (k * k₁ * k₂)⁻¹ * y⁻¹ = c * (x2 * x1) * xk := by
      rw [hxK2, hx12, hst1, hst2]
    have h2 : c * (x2 * x1) * xk = 1 := by rw [← h1, hxK1]
    rw [← hcx1x2] at h2
    rwa [← mul_assoc c x1 x2] at h2
  have hxc : x1 * x2 * xk = c := by
    have h2 : c * (x1 * x2 * xk) = 1 := by
      rwa [mul_assoc c x1 x2, mul_assoc c (x1 * x2) xk] at hfin
    calc x1 * x2 * xk = 1 * (x1 * x2 * xk) := (one_mul _).symm
      _ = (c * c) * (x1 * x2 * xk) := by rw [hcc]
      _ = c * (c * (x1 * x2 * xk)) := by rw [mul_assoc]
      _ = c * 1 := by rw [h2]
      _ = c := mul_one c
  show xk * x1 * x2 = c
  rw [show xk * x1 * x2 = x1 * x2 * xk from by
    calc xk * x1 * x2 = (xk * x1) * x2 := rfl
      _ = (x1 * xk) * x2 := by rw [hcxkx1]
      _ = x1 * (xk * x2) := by rw [mul_assoc]
      _ = x1 * (x2 * xk) := by rw [hcxkx2]
      _ = x1 * x2 * xk := (mul_assoc x1 x2 xk).symm]
  exact hxc

theorem conj_mul_inv_mul_mem_of_utA (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    (B : Subgroup G)
    (hBn : ∀ c ∈ H z ⊓ centralizer ({y} : Set G), ∀ c' ∈ B, c * c' * c⁻¹ ∈ B)
    {k ζ : G} (hk : k ∈ J z) (hζ : ζ ∈ centerIn (J z)) (hB : k * y * k⁻¹ * y⁻¹ * ζ ∈ B) :
    k * y * k⁻¹ * y⁻¹ *
        (if b (hbadCoord h P k) (((rhoA hbadS : GL8) : Mat8) *ᵥ
          (((rhoA (uA * tA) : GL8) : Mat8) *ᵥ hbadCoord h P k + hbadCoord h P k)) = 0 then 1
        else z) ∈ B := by
  classical
  obtain ⟨s, hsy, hs3, hqs⟩ := exists_sigma_of_utA D hyH hy hq h P hP
  set xk : G := k * y * k⁻¹ * y⁻¹ with hxkdef
  set k1 : G := (s : G) * k * (s : G)⁻¹ with hk1def
  set xk1 : G := k1 * y * k1⁻¹ * y⁻¹ with hxk1def
  set k2 : G := (s : G) * k1 * (s : G)⁻¹ with hk2def
  set xk2 : G := k2 * y * k2⁻¹ * y⁻¹ with hxk2def
  set c : G := if b (hbadCoord h P k) (((rhoA hbadS : GL8) : Mat8) *ᵥ
      (((rhoA (uA * tA) : GL8) : Mat8) *ᵥ hbadCoord h P k + hbadCoord h P k)) = 0 then 1
      else z with hcdef
  have hsC : (s : G) ∈ H z ⊓ Subgroup.centralizer ({y} : Set G) :=
    Subgroup.mem_inf.mpr ⟨s.2, Subgroup.mem_centralizer_singleton_iff.mpr hsy⟩
  have hsZ : (s : G) * ζ = ζ * (s : G) := by
    have hZ1 : centerIn (J z) ≤ Subgroup.centralizer ({(s : G)} : Set G) :=
      centerIn_le_centralizer_of_conjZ_eq_one (z := z) (x := s)
        (conjZ_eq_one_of_mem_Q (z := z) D h s
          (Subgroup.mem_subgroupOf.mpr (by rw [hqs]; exact hbadS_mem_QP45)))
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hZ1 hζ)).symm
  have hζ2 : ζ * ζ = 1 := centerIn_J_sq h hζ
  have hζcen : ∀ a ∈ J z, ζ * a = a * ζ :=
    fun a ha => (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hζ).2 a ha).symm
  have hk1J : k1 ∈ J z := H_conj_mem_J s hk
  have hk2J : k2 ∈ J z := H_conj_mem_J s hk1J
  have hxkJ : xk ∈ J z := (hbadCoord_conj_mul_inv_of_utA D hyH hq h P hP hk).1
  have hxk1J : xk1 ∈ J z := (hbadCoord_conj_mul_inv_of_utA D hyH hq h P hP hk1J).1
  have hxk2J : xk2 ∈ J z := (hbadCoord_conj_mul_inv_of_utA D hyH hq h P hP hk2J).1
  have hconj_x : ∀ a : G, (s : G) * (a * y * a⁻¹ * y⁻¹) * (s : G)⁻¹ =
      ((s : G) * a * (s : G)⁻¹) * y * ((s : G) * a * (s : G)⁻¹)⁻¹ * y⁻¹ := by
    intro a
    have h1 : (s : G) * y * (s : G)⁻¹ = y := by rw [hsy]; group
    calc (s : G) * (a * y * a⁻¹ * y⁻¹) * (s : G)⁻¹
        = ((s : G) * a * (s : G)⁻¹) * ((s : G) * y * (s : G)⁻¹) *
            ((s : G) * a * (s : G)⁻¹)⁻¹ * ((s : G) * y * (s : G)⁻¹)⁻¹ := by group
      _ = ((s : G) * a * (s : G)⁻¹) * y * ((s : G) * a * (s : G)⁻¹)⁻¹ * y⁻¹ := by rw [h1]
  have hconj_ζ : (s : G) * ζ * (s : G)⁻¹ = ζ := by rw [hsZ]; group
  have hn1 : (s : G) * (xk * ζ) * (s : G)⁻¹ = xk1 * ζ := by
    calc (s : G) * (xk * ζ) * (s : G)⁻¹
        = ((s : G) * xk * (s : G)⁻¹) * ((s : G) * ζ * (s : G)⁻¹) := by group
      _ = xk1 * ζ := by rw [hconj_x k, hconj_ζ]
  have hn2 : (s : G) * (xk1 * ζ) * (s : G)⁻¹ = xk2 * ζ := by
    calc (s : G) * (xk1 * ζ) * (s : G)⁻¹
        = ((s : G) * xk1 * (s : G)⁻¹) * ((s : G) * ζ * (s : G)⁻¹) := by group
      _ = xk2 * ζ := by rw [hconj_x k1, hconj_ζ]
  have h1B : (s : G) * (xk * ζ) * (s : G)⁻¹ ∈ B := hBn _ hsC _ hB
  have h2B : (s : G) * ((s : G) * (xk * ζ) * (s : G)⁻¹) * (s : G)⁻¹ ∈ B := hBn _ hsC _ h1B
  have h3 : xk * xk1 * xk2 = c := by
    rw [hxkdef, hxk1def, hxk2def, hcdef]
    exact conj_mul_inv_mul_of_utA D hyH hy hq h P hP hqs hk
  have hcζB : c * ζ ∈ B := by
    have hprod := B.mul_mem (B.mul_mem hB h1B) h2B
    have hval : (xk * ζ) * ((s : G) * (xk * ζ) * (s : G)⁻¹) *
        ((s : G) * ((s : G) * (xk * ζ) * (s : G)⁻¹) * (s : G)⁻¹) = c * ζ := by
      rw [hn1, hn2]
      have e1 : (xk * ζ) * (xk1 * ζ) = xk * xk1 := by
        calc (xk * ζ) * (xk1 * ζ) = xk * (ζ * xk1) * ζ := by group
          _ = xk * (xk1 * ζ) * ζ := by rw [hζcen xk1 hxk1J]
          _ = xk * xk1 * (ζ * ζ) := by group
          _ = xk * xk1 := by rw [hζ2, mul_one]
      calc (xk * ζ) * (xk1 * ζ) * (xk2 * ζ) = ((xk * ζ) * (xk1 * ζ)) * (xk2 * ζ) := rfl
        _ = (xk * xk1) * (xk2 * ζ) := by rw [e1]
        _ = xk * xk1 * xk2 * ζ := by group
        _ = c * ζ := by rw [h3]
    rwa [hval] at hprod
  have hcinv : c⁻¹ = c := by
    rw [hcdef]
    by_cases hb : b (hbadCoord h P k) (((rhoA hbadS : GL8) : Mat8) *ᵥ
        (((rhoA (uA * tA) : GL8) : Mat8) *ᵥ hbadCoord h P k + hbadCoord h P k)) = 0
    · rw [if_pos hb]; group
    · rw [if_neg hb]
      exact inv_eq_of_mul_eq_one_right (centerIn_J_sq h (z_mem_centerIn_J h))
  have hζinv : ζ⁻¹ = ζ := inv_eq_of_mul_eq_one_right hζ2
  have hfin : (xk * ζ) * (c * ζ)⁻¹ ∈ B := B.mul_mem hB (B.inv_mem hcζB)
  have hsimp : (xk * ζ) * (c * ζ)⁻¹ = xk * c := by
    rw [mul_inv_rev, hζinv, hcinv]
    calc (xk * ζ) * (ζ * c) = xk * (ζ * ζ) * c := by group
      _ = xk * c := by rw [hζ2]; group
  rw [hsimp] at hfin
  exact hfin

theorem exists_lift_hbadA_of_utA (h : Tim79a.ParrottHyp z) (P : GL8)
    (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹) :
    ∃ a : ↥(H z), qH (z := z) D a = hbadA ∧
      ∃ ζ ∈ centerIn (J z), (a : G) * y * (a : G)⁻¹ = y * ζ := by
  classical
  obtain ⟨a₀, ha₀⟩ := qH_surjective D hbadA
  have hgH : (a₀ : G) * y * (a₀ : G)⁻¹ ∈ H z :=
    (H z).mul_mem ((H z).mul_mem a₀.2 hyH) ((H z).inv_mem a₀.2)
  have hgq : qH (z := z) D (⟨(a₀ : G) * y * (a₀ : G)⁻¹, hgH⟩ : ↥(H z)) = uA * tA := by
    rw [show (⟨(a₀ : G) * y * (a₀ : G)⁻¹, hgH⟩ : ↥(H z)) = a₀ * ⟨y, hyH⟩ * a₀⁻¹ from rfl,
      map_mul, map_mul, map_inv, ha₀, hq, hbadA_comm_utA]
    group
  have hgg : ((a₀ : G) * y * (a₀ : G)⁻¹) * ((a₀ : G) * y * (a₀ : G)⁻¹) = 1 := by
    calc ((a₀ : G) * y * (a₀ : G)⁻¹) * ((a₀ : G) * y * (a₀ : G)⁻¹)
        = (a₀ : G) * (y * y) * (a₀ : G)⁻¹ := by group
      _ = 1 := by rw [hy]; group
  obtain ⟨k, hkJ, ζ, hζ, hgeq⟩ :=
    exists_eq_conj_mul_of_utA D hyH hy hq h P hP hgH hgq hgg
  have hkζ : ζ * k = k * ζ :=
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hζ).2 k hkJ).symm
  let kH : ↥(H z) := ⟨k, J_le_H hkJ⟩
  have hkq : qH (z := z) D kH = 1 := (J_mem_iff D kH).mp (Subgroup.mem_subgroupOf.mpr hkJ)
  refine ⟨kH⁻¹ * a₀, ?_, ζ, hζ, ?_⟩
  · show qH (z := z) D (kH⁻¹ * a₀) = hbadA
    rw [map_mul, map_inv, ha₀, hkq]
    group
  · show ((kH⁻¹ * a₀ : ↥(H z)) : G) * y * ((kH⁻¹ * a₀ : ↥(H z)) : G)⁻¹ = y * ζ
    have hka : ((kH⁻¹ * a₀ : ↥(H z)) : G) = k⁻¹ * (a₀ : G) := rfl
    rw [hka]
    calc k⁻¹ * (a₀ : G) * y * (k⁻¹ * (a₀ : G))⁻¹
        = k⁻¹ * ((a₀ : G) * y * (a₀ : G)⁻¹) * k := by group
      _ = k⁻¹ * (k * y * k⁻¹ * ζ) * k := by rw [hgeq]
      _ = y * ζ := by
          have hkζ' : k⁻¹ * ζ * k = ζ := by rw [mul_assoc, hkζ]; group
          calc k⁻¹ * (k * y * k⁻¹ * ζ) * k = y * (k⁻¹ * ζ * k) := by group
            _ = y * ζ := by rw [hkζ']

end Y

end CFSG.RankThree.GF2n.Parrott
