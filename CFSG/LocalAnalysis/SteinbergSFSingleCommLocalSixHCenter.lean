module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommLocalSixHBaseB
public import CFSG.LocalAnalysis.SteinbergSFSingleCommLocalSixHGeneric

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup GomiFusion
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis

section Concl

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]

@[expose] def H1Concl (φ : L ≃* antiSp K) (t : G) (i : Axis) : Prop :=
  (center ↥(Tplus φ t i)).map (Tplus φ t i).subtype = U φ i

structure H2aConcl (φ : L ≃* antiSp K) (t : G) (i : Axis) : Prop where
  comm_M : ∀ x ∈ Mc φ t i, ∀ y ∈ Mc φ t i, x⁻¹ * y⁻¹ * x * y ∈ U φ i
  central : ∀ u ∈ U φ i, ∀ m ∈ Mc φ t i, u * m = m * u
  sq_M : closure {x : G | ∃ y ∈ Mc φ t i, x = y * y} = U φ i

@[expose] def H2bConcl (φ : L ≃* antiSp K) (t : G) (i : Axis) : Prop :=
  (∀ x ∈ Vtor φ t i i, (w φ i)⁻¹ * x * w φ i ∈ Vtor φ t i i) ∧
    ∀ x ∈ Vtor φ t i i.swap, (w φ i.swap)⁻¹ * x * w φ i.swap ∈ Vtor φ t i i.swap

@[expose] def H2cConcl (φ : L ≃* antiSp K) (t : G) (i : Axis) : Prop :=
  ∀ x ∈ Vtor φ t i i, (t⁻¹ * (x⁻¹ * t * x)) * (t⁻¹ * (x⁻¹ * t * x)) =
    x⁻¹ * (t⁻¹ * x * t)⁻¹ * x * (t⁻¹ * x * t)

@[expose] def H2dConcl (φ : L ≃* antiSp K) (t : G) (i : Axis) : Prop :=
  (center ↥(Vtor φ t i i)).map (Vtor φ t i i).subtype = U φ i ∧
    ∀ x ∈ Vtor φ t i i, (t⁻¹ * (x⁻¹ * t * x) ∈ U φ i ↔ x ∈ Wk φ t i)

@[expose] def H3Concl (φ : L ≃* antiSp K) (t : G) (i : Axis) : Prop :=
  (∀ x ∈ Mhat φ t i i, ∀ y ∈ Mhat φ t i i, x⁻¹ * y⁻¹ * x * y ∈ U φ i) ∧
    closure {x : G | ∃ y ∈ Mhat φ t i i, x = y * y} = U φ i

@[expose] def H4aConcl (φ : L ≃* antiSp K) (t : G) (i : Axis) : Prop :=
  Kc φ t i ≤ Mhat φ t i i ∧
    ∀ x ∈ Mhat φ t i i, (x⁻¹ * t⁻¹ * x * t ∈ U φ i ↔ x ∈ Kc φ t i)

@[expose] def H4Concl (φ : L ≃* antiSp K) (t : G) (i : Axis) : Prop :=
  (∃ _ : ((U φ i).subgroupOf (P₁ φ t i)).Normal,
      SixG.MNMaximal (P₁ φ t i) (Mhat φ t i i) (D φ t i) (P₁ φ t i) (U φ i)) ∧
    T₁ φ t i ≤ normalizer (Mhat φ t i i : Set G)

end Concl

section Aux

variable {G : Type} [Group G]

theorem sixH_h2b_aux1 (X : Subgroup G) (g x : G) (hg : g * g = 1)
    (hx : x ∈ X) (hxw : x ∈ X.map (MulAut.conj g⁻¹).toMonoidHom) :
    g⁻¹ * x * g ∈ X ∧ g⁻¹ * x * g ∈ X.map (MulAut.conj g⁻¹).toMonoidHom := by
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  rw [FullCenterWeyl.mem_map_conj_inv, hginv] at hxw
  refine ⟨?_, ?_⟩
  · rw [hginv]
    exact hxw
  · rw [FullCenterWeyl.mem_map_conj_inv]
    have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    rw [e]
    exact hx

theorem sixH_mem_normalizer_of_comm {S : Subgroup G} {z : G}
    (h : ∀ a ∈ S, a * z = z * a) : z ∈ normalizer (S : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have e : z * x * z⁻¹ = x := by
      rw [← h x hx, mul_inv_cancel_right]
    rw [e]
    exact hx
  · intro hx
    have h2 := h (z * x * z⁻¹) hx
    rw [inv_mul_cancel_right] at h2
    have e : x = z * x * z⁻¹ := mul_left_cancel h2
    rw [e]
    exact hx

theorem sixH_kappa_of_comm {t u : G} (h : u * t = t * u) : t⁻¹ * (u⁻¹ * t * u) = 1 := by
  have h' : u⁻¹ * t * u = t := by rw [mul_assoc, ← h, inv_mul_cancel_left]
  rw [h', inv_mul_cancel]

theorem sixH_kappa_aux {t c : G} (ht : t * t = 1) (hc : c⁻¹ = t * c * t) :
    t⁻¹ * (c⁻¹ * t * c) = c * c := by
  rw [hc]
  calc t⁻¹ * (t * c * t * t * c) = t⁻¹ * (t * c * (t * t) * c) := by group
    _ = t⁻¹ * (t * c * c) := by rw [ht, mul_one]
    _ = c * c := by group

theorem sixH_kappa_kappa {t y : G} (ht : t * t = 1) :
    t⁻¹ * ((t⁻¹ * (y⁻¹ * t * y))⁻¹ * t * (t⁻¹ * (y⁻¹ * t * y))) =
      (t⁻¹ * (y⁻¹ * t * y)) * (t⁻¹ * (y⁻¹ * t * y)) := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hc : (t⁻¹ * (y⁻¹ * t * y))⁻¹ = t * (t⁻¹ * (y⁻¹ * t * y)) * t := by
    calc (t⁻¹ * (y⁻¹ * t * y))⁻¹ = y⁻¹ * t⁻¹ * y * t := by group
      _ = y⁻¹ * t * y * t := by rw [hti]
      _ = t * (t⁻¹ * (y⁻¹ * t * y)) * t := by group
  exact sixH_kappa_aux ht hc

theorem sixH_yc_aux {y c : G} (hcomm : c * y = y * c) : y⁻¹ * c * y * c⁻¹ = 1 := by
  calc y⁻¹ * c * y * c⁻¹ = y⁻¹ * (c * y) * c⁻¹ := by group
    _ = y⁻¹ * (y * c) * c⁻¹ := by rw [hcomm]
    _ = 1 := by group

theorem sixH_sq_kappa_of_comm {t y : G}
    (hcomm : (t⁻¹ * (y⁻¹ * t * y)) * y = y * (t⁻¹ * (y⁻¹ * t * y)))
    (hH : (t⁻¹ * (y⁻¹ * t * y)) * (t⁻¹ * (y⁻¹ * t * y)) =
      y⁻¹ * (t⁻¹ * y * t)⁻¹ * y * (t⁻¹ * y * t)) :
    (t⁻¹ * (y⁻¹ * t * y)) * (t⁻¹ * (y⁻¹ * t * y)) = 1 := by
  have e : t⁻¹ * y * t = y * (t⁻¹ * (y⁻¹ * t * y))⁻¹ := by group
  rw [hH, e]
  calc y⁻¹ * (y * (t⁻¹ * (y⁻¹ * t * y))⁻¹)⁻¹ * y * (y * (t⁻¹ * (y⁻¹ * t * y))⁻¹)
      = y⁻¹ * (t⁻¹ * (y⁻¹ * t * y)) * y * (t⁻¹ * (y⁻¹ * t * y))⁻¹ := by group
    _ = 1 := sixH_yc_aux hcomm

end Aux

section Steps

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G} {i : Axis}

open scoped Pointwise

theorem sixH_h1a_normalizer_A (hS : SCSetting L K n φ t i)
    (hM2 : ∀ x ∈ Mc φ t i, x * x ∈ U φ i) :
    Tplus φ t i ⊓ normalizer (A φ i.swap : Set G) = T₀ φ t i.swap := by
  have hT0E : T₀ φ t i.swap ≤ normalizer (E φ t i.swap : Set G) :=
    le_trans (NextCores.T₀_le_En hS.fc i.swap) inf_le_left
  have hT0N : T₀ φ t i.swap ≤ normalizer (A φ i.swap : Set G) :=
    SixG.le_normalizer_A_of_E hS.fc i.swap hT0E
  have hT2T0 : T₂ φ t i.swap ≤ T₀ φ t i.swap := inf_le_left
  have hRN : R φ t i ≤ normalizer (T₂ φ t i.swap : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact NextCores.conj_mem_T₂ hS.fc i hS.ne_bot hS.eq_bot
        (SingleComm.R_le_Nhat hS.fc i hS.ne_bot hS.eq_bot i hg) hx
    · intro hx
      have h2 := NextCores.conj_mem_T₂ hS.fc i hS.ne_bot hS.eq_bot
        (SingleComm.R_le_Nhat hS.fc i hS.ne_bot hS.eq_bot i (inv_mem hg)) hx
      have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
      rw [e] at h2
      exact h2
  have hTbar : R φ t i ⊔ T₂ φ t i.swap = Tbar φ t i :=
    (sup_comm _ _).trans (NextCores.R_sup_T₂ hS.fc i hS.ne_bot hS.eq_bot)
  have hRA : R φ t i ⊓ normalizer (A φ i.swap : Set G) ≤ T₂ φ t i.swap :=
    le_trans (le_of_eq (FullCenterParabolic.R_inf_normalizer_A hS.fc i))
      (NextCores.H_le_T₂ hS.fc i.swap)
  have hprod := SixG.Tplus_mul hS.fc i hS.ne_bot hS.eq_bot hM2
  apply le_antisymm
  · rintro x ⟨hxT, hxN⟩
    have hx : x ∈ (Tbar φ t i : Set G) * (T₀ φ t i.swap : Set G) := by
      rw [hprod]
      exact hxT
    rw [Set.mem_mul] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    have hbN : b ∈ normalizer (A φ i.swap : Set G) := hT0N hb
    have haN : a ∈ normalizer (A φ i.swap : Set G) := by
      have h := (normalizer (A φ i.swap : Set G)).mul_mem hxN
        ((normalizer (A φ i.swap : Set G)).inv_mem hbN)
      rwa [mul_inv_cancel_right] at h
    have ha' : a ∈ (R φ t i : Set G) * (T₂ φ t i.swap : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hRN, hTbar]
      exact ha
    rw [Set.mem_mul] at ha'
    obtain ⟨r, hr, y, hy, hry⟩ := ha'
    have hyN : y ∈ normalizer (A φ i.swap : Set G) := hT0N (hT2T0 hy)
    have hrN : r ∈ normalizer (A φ i.swap : Set G) := by
      have hr_eq : r = a * y⁻¹ := eq_mul_inv_of_mul_eq hry
      rw [hr_eq]
      exact mul_mem haN (inv_mem hyN)
    have hrT2 : r ∈ T₂ φ t i.swap := hRA (Subgroup.mem_inf.mpr ⟨hr, hrN⟩)
    have haT2 : a ∈ T₂ φ t i.swap := by
      rw [← hry]
      exact mul_mem hrT2 hy
    exact mul_mem (hT2T0 haT2) hb
  · exact le_inf le_sup_right hT0N

theorem sixH_A_le_Tplus (hS : SCSetting L K n φ t i) : A φ i.swap ≤ Tplus φ t i := by
  intro a ha
  have h1 : a ∈ E φ t i.swap :=
    FullCenter.FCHyp.D_le_E hS.fc i.swap (FullCenterWeyl.A_le_D hS.fc i.swap ha)
  have h2 : a ∈ P₂ φ t i.swap := NextCores.E_le_P₂ hS.fc i hS.ne_bot hS.eq_bot h1
  have h3 : a ∈ T₀ φ t i.swap := Subgroup.mem_sup_right h2
  exact Subgroup.mem_sup_right h3

theorem sixH_R_le_Tplus : R φ t i ≤ Tplus φ t i := by
  intro x hx
  exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_left hx))

theorem sixH_t_mem_R : t ∈ R φ t i :=
  Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers t))

theorem sixH_h1_center_Tplus (hS : SCSetting L K n φ t i)
    (hM2 : ∀ x ∈ Mc φ t i, x * x ∈ U φ i)
    (h1a : Tplus φ t i ⊓ normalizer (A φ i.swap : Set G) = T₀ φ t i.swap) :
    H1Concl φ t i := by
  unfold H1Concl
  have hpT : IsPGroup 2 ↥(Tplus φ t i) := SixG.isPGroup_Tplus hS.fc i hS.ne_bot hS.eq_bot hM2
  have hcT : Nat.card ↥(Tplus φ t i) = 2 * Nat.card K ^ 10 :=
    SixG.card_Tplus hS.fc i hS.ne_bot hS.eq_bot hM2
  have hcardT : 1 < Nat.card ↥(Tplus φ t i) := by
    rw [hcT]
    have hK : 0 < Nat.card K := Nat.card_pos
    have hpow : 0 < Nat.card K ^ 10 := pow_pos hK 10
    omega
  haveI : Nontrivial ↥(Tplus φ t i) := Finite.one_lt_card_iff_nontrivial.mp hcardT
  have hJT : J₀ φ ≤ normalizer ((Tplus φ t i : Subgroup G) : Set G) := by
    intro j hj
    exact Subgroup.inf_normalizer_le_normalizer_sup _ _ (Subgroup.mem_inf.mpr
      ⟨SixG.J_le_normalizer_Tbar hS.fc i hS.ne_bot hS.eq_bot hj,
        SixG.J_le_normalizer_T₀ hS.fc i hS.ne_bot hS.eq_bot i.swap hj⟩)
  have htT : t ∈ Tplus φ t i := sixH_R_le_Tplus sixH_t_mem_R
  have hAT : A φ i.swap ≤ Tplus φ t i := sixH_A_le_Tplus hS
  have hS' : zpowers t ⊔ A φ i.swap ≤ Tplus φ t i :=
    sup_le (Subgroup.zpowers_le.mpr htT) hAT
  have hcomm : ∀ z : ↥(Tplus φ t i), z ∈ center ↥(Tplus φ t i) →
      ∀ g ∈ Tplus φ t i, g * (z : G) = (z : G) * g := by
    intro z hz g hg
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨g, hg⟩)
  have hXU : (center ↥(Tplus φ t i)).map (Tplus φ t i).subtype ≤ U φ i := by
    rintro x hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
    have hzA : (z : G) ∈ normalizer (A φ i.swap : Set G) :=
      sixH_mem_normalizer_of_comm (fun a ha => hcomm z hz a (hAT ha))
    have hzT0 : (z : G) ∈ T₀ φ t i.swap :=
      (le_of_eq h1a) (Subgroup.mem_inf.mpr ⟨z.2, hzA⟩)
    have hzS : (z : G) ∈ normalizer ((zpowers t ⊔ A φ i.swap : Subgroup G) : Set G) :=
      sixH_mem_normalizer_of_comm (fun a ha => hcomm z hz a (hS' ha))
    have hzRj : (z : G) ∈ R φ t i.swap :=
      (le_of_eq (NextCores.T₀_inf_N hS.fc i hS.ne_bot hS.eq_bot))
        (Subgroup.mem_inf.mpr ⟨hzT0, hzS⟩)
    have hzC : (z : G) ∈ centralizer ({t} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact hcomm z hz t htT
    have hzQ := (le_of_eq (FullCenterParabolic.R_inf_C hS.fc i.swap))
      (Subgroup.mem_inf.mpr ⟨hzRj, hzC⟩)
    have hzR : (z : G) ∈ R φ t i := Subgroup.mem_sup_left hzQ
    have hcenR : (⟨(z : G), hzR⟩ : ↥(R φ t i)) ∈ center ↥(R φ t i) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact hcomm z hz (g : G) (sixH_R_le_Tplus g.2)
    have hUR : U φ i = (center ↥(R φ t i)).map (R φ t i).subtype :=
      (FullCenterWeyl.centers_of_ne_bot hS.fc i hS.ne_bot).2.1.symm
    rw [hUR]
    exact Subgroup.mem_map.mpr ⟨⟨(z : G), hzR⟩, hcenR, rfl⟩
  have hJ : ∀ j ∈ J₀ φ, ∀ x ∈ (center ↥(Tplus φ t i)).map (Tplus φ t i).subtype,
      j * x * j⁻¹ ∈ (center ↥(Tplus φ t i)).map (Tplus φ t i).subtype := by
    intro j hj x hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
    have hconj : ∀ g ∈ Tplus φ t i, j⁻¹ * g * j ∈ Tplus φ t i := by
      intro g hg
      refine (Subgroup.mem_normalizer_iff.mp (hJT hj) (j⁻¹ * g * j)).mpr ?_
      have e : j * (j⁻¹ * g * j) * j⁻¹ = g := by group
      rw [e]
      exact hg
    have hwT : j * (z : G) * j⁻¹ ∈ Tplus φ t i :=
      (Subgroup.mem_normalizer_iff.mp (hJT hj) (z : G)).mp z.2
    have hwc : (⟨j * (z : G) * j⁻¹, hwT⟩ : ↥(Tplus φ t i)) ∈ center ↥(Tplus φ t i) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      have hc : (j⁻¹ * (g : G) * j) * (z : G) = (z : G) * (j⁻¹ * (g : G) * j) :=
        hcomm z hz _ (hconj (g : G) g.2)
      show (g : G) * (j * (z : G) * j⁻¹) = (j * (z : G) * j⁻¹) * (g : G)
      calc (g : G) * (j * (z : G) * j⁻¹)
          = j * ((j⁻¹ * (g : G) * j) * (z : G)) * j⁻¹ := by group
        _ = j * ((z : G) * (j⁻¹ * (g : G) * j)) * j⁻¹ := by rw [hc]
        _ = (j * (z : G) * j⁻¹) * (g : G) := by group
    exact Subgroup.mem_map.mpr ⟨⟨j * (z : G) * j⁻¹, hwT⟩, hwc, rfl⟩
  have hXbot : (center ↥(Tplus φ t i)).map (Tplus φ t i).subtype ≠ ⊥ := by
    intro hbot
    haveI := IsPGroup.center_nontrivial hpT
    obtain ⟨z, hz⟩ := exists_ne (1 : ↥(center ↥(Tplus φ t i)))
    have hzX : ((z.1 : ↥(Tplus φ t i)) : G) ∈
        (center ↥(Tplus φ t i)).map (Tplus φ t i).subtype :=
      Subgroup.mem_map.mpr ⟨z.1, z.2, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hzX
    exact hz (Subtype.ext (Subtype.ext hzX))
  exact (sixH_i1_irreducible_U i hXU hJ).resolve_left hXbot

theorem sixH_J_le_normalizer_Tplus (hS : SCSetting L K n φ t i) :
    J₀ φ ≤ normalizer ((Tplus φ t i : Subgroup G) : Set G) := by
  intro j hj
  exact Subgroup.inf_normalizer_le_normalizer_sup _ _ (Subgroup.mem_inf.mpr
    ⟨SixG.J_le_normalizer_Tbar hS.fc i hS.ne_bot hS.eq_bot hj,
      SixG.J_le_normalizer_T₀ hS.fc i hS.ne_bot hS.eq_bot i.swap hj⟩)

theorem sixH_Mc_le_Tplus (hS : SCSetting L K n φ t i) : Mc φ t i ≤ Tplus φ t i := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨p, hp, j, hj, rfl⟩
  have hpT : p ∈ Tplus φ t i :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_inf.mp hp).1))
  have hjp : j⁻¹ * p * j ∈ Tplus φ t i := by
    refine (Subgroup.mem_normalizer_iff.mp (sixH_J_le_normalizer_Tplus hS hj) (j⁻¹ * p * j)).mpr ?_
    have e : j * (j⁻¹ * p * j) * j⁻¹ = p := by group
    rw [e]
    exact hpT
  exact mul_mem (inv_mem hpT) hjp

theorem sixH_U_central_Tplus (h1 : H1Concl φ t i) :
    ∀ u ∈ U φ i, ∀ g ∈ Tplus φ t i, u * g = g * u := by
  intro u hu g hg
  have h1' : (center ↥(Tplus φ t i)).map (Tplus φ t i).subtype = U φ i := h1
  have hu' : u ∈ (center ↥(Tplus φ t i)).map (Tplus φ t i).subtype := by
    rw [h1']
    exact hu
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hu'
  exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨g, hg⟩)).symm

theorem sixH_U_central_Mc (hS : SCSetting L K n φ t i) (h1 : H1Concl φ t i) :
    ∀ u ∈ U φ i, ∀ m ∈ Mc φ t i, u * m = m * u := by
  intro u hu m hm
  have h1' : (center ↥(Tplus φ t i)).map (Tplus φ t i).subtype = U φ i := h1
  have hu' : u ∈ (center ↥(Tplus φ t i)).map (Tplus φ t i).subtype := by
    rw [h1']
    exact hu
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hu'
  exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨m, sixH_Mc_le_Tplus hS hm⟩)).symm

theorem sixH_h2a (hS : SCSetting L K n φ t i) (hM2 : ∀ x ∈ Mc φ t i, x * x ∈ U φ i)
    (h1 : H1Concl φ t i) : H2aConcl φ t i := by
  have hcen : ∀ u ∈ U φ i, ∀ m ∈ Mc φ t i, u * m = m * u := sixH_U_central_Mc hS h1
  refine ⟨?_, hcen, SixG.closure_sq_M hS.fc i hS.ne_bot hS.eq_bot hM2⟩
  intro x hx y hy
  have hc : (y * y) * x = x * (y * y) := hcen (y * y) (hM2 y hy) x hx
  have hc' : (y * y)⁻¹ * x = x * (y * y)⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hc, mul_assoc, mul_inv_cancel, mul_one]
  have key : (x * x)⁻¹ * (y * y)⁻¹ * ((x * y) * (x * y)) = x⁻¹ * y⁻¹ * x * y := by
    calc (x * x)⁻¹ * (y * y)⁻¹ * ((x * y) * (x * y))
        = (x * x)⁻¹ * (((y * y)⁻¹ * x) * y * x * y) := by group
      _ = (x * x)⁻¹ * ((x * (y * y)⁻¹) * y * x * y) := by rw [hc']
      _ = x⁻¹ * y⁻¹ * x * y := by group
  rw [← key]
  exact mul_mem (mul_mem (inv_mem (hM2 x hx)) (inv_mem (hM2 y hy)))
    (hM2 (x * y) (mul_mem hx hy))

theorem sixH_h2b (hS : SCSetting L K n φ t i) (hM2 : ∀ x ∈ Mc φ t i, x * x ∈ U φ i) :
    H2bConcl φ t i := by
  have hVi : Vtor φ t i i = Mc φ t i ⊓ Mw φ t i i :=
    (SixF.M_inf_Mw hS.fc i hS.ne_bot hS.eq_bot).symm
  have hVs : Vtor φ t i i.swap = Mc φ t i ⊓ Mw φ t i i.swap :=
    (RootStandard.V_swap_eq hS.fc i hS.ne_bot hS.eq_bot).trans
      (SixF.M_inf_Mw_swap hS.fc i hS.ne_bot hS.eq_bot).symm
  unfold H2bConcl
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · rw [hVi] at hx ⊢
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr
      (sixH_h2b_aux1 (Mc φ t i) (w φ i) x (FullCenterWeyl.w_mul_self (φ := φ) i) hx1 hx2)
  · rw [hVs] at hx ⊢
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr
      (sixH_h2b_aux1 (Mc φ t i) (w φ i.swap) x (FullCenterWeyl.w_mul_self (φ := φ) i.swap)
        hx1 hx2)

theorem sixH_h2c (hS : SCSetting L K n φ t i) (hM2 : ∀ x ∈ Mc φ t i, x * x ∈ U φ i)
    (h1 : H1Concl φ t i) (h2a : H2aConcl φ t i) : H2cConcl φ t i := by
  unfold H2cConcl
  have hVM : ∀ x ∈ Vtor φ t i i, x ∈ Mc φ t i := fun x hx => (Subgroup.mem_inf.mp hx).1
  have hsq : ∀ x ∈ Vtor φ t i i, ∀ y ∈ Vtor φ t i i, (x * x) * y = y * (x * x) :=
    fun x hx y hy => h2a.central (x * x) (hM2 x (hVM x hx)) y (hVM y hy)
  have hsqt : ∀ x ∈ Vtor φ t i i, (x * x) * t = t * (x * x) := fun x hx =>
    sixH_U_central_Tplus h1 (x * x) (hM2 x (hVM x hx)) t (sixH_R_le_Tplus sixH_t_mem_R)
  intro x hx
  exact sixH_g3_quadratic (SixF.t_mul_t hS.fc)
    (RootStandard.t_mem_normalizer_V hS.fc i hS.ne_bot hS.eq_bot i) hsq hsqt hx

theorem sixH_kappa_mem_V (hS : SCSetting L K n φ t i) {x : G} (hx : x ∈ Vtor φ t i i) :
    t⁻¹ * (x⁻¹ * t * x) ∈ Vtor φ t i i := by
  have hN := RootStandard.t_mem_normalizer_V hS.fc i hS.ne_bot hS.eq_bot i
  have hb : t⁻¹ * x * t ∈ Vtor φ t i i := (Subgroup.mem_normalizer_iff''.mp hN x).mp hx
  have hL : t⁻¹ * (x⁻¹ * t * x) = (t⁻¹ * x * t)⁻¹ * x := by group
  rw [hL]
  exact (Vtor φ t i i).mul_mem ((Vtor φ t i i).inv_mem hb) hx

theorem sixH_mem_W_of_sq_one (hS : SCSetting L K n φ t i) {y : G} (hy : y ∈ Vtor φ t i i)
    (hsq : (t⁻¹ * (y⁻¹ * t * y)) * (t⁻¹ * (y⁻¹ * t * y)) = 1) : y ∈ Wk φ t i := by
  obtain ⟨hN, e, he⟩ := RootStandard.quotient_V hS.fc i hS.ne_bot hS.eq_bot
  haveI := hN
  have hval : (e (QuotientGroup.mk ⟨y, hy⟩) : G) =
      (t⁻¹ * (y⁻¹ * t * y)) * (t⁻¹ * (y⁻¹ * t * y)) := he ⟨y, hy⟩
  have h1 : e (QuotientGroup.mk ⟨y, hy⟩) = 1 := by
    apply Subtype.ext
    exact (hval.trans hsq).trans rfl
  have h2 := e.injective (h1.trans (map_one e).symm)
  exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h2)

theorem sixH_sq_kappa_mem_U (hS : SCSetting L K n φ t i) {x : G} (hx : x ∈ Vtor φ t i i) :
    (t⁻¹ * (x⁻¹ * t * x)) * (t⁻¹ * (x⁻¹ * t * x)) ∈ U φ i := by
  obtain ⟨hN, e, he⟩ := RootStandard.quotient_V hS.fc i hS.ne_bot hS.eq_bot
  haveI := hN
  have hval : (e (QuotientGroup.mk ⟨x, hx⟩) : G) =
      (t⁻¹ * (x⁻¹ * t * x)) * (t⁻¹ * (x⁻¹ * t * x)) := he ⟨x, hx⟩
  rw [← hval]
  exact (e (QuotientGroup.mk ⟨x, hx⟩)).2

theorem sixH_mem_W_of_kappa_mem_U (hS : SCSetting L K n φ t i) (h1 : H1Concl φ t i) {y : G}
    (hy : y ∈ Vtor φ t i i) (hκ : t⁻¹ * (y⁻¹ * t * y) ∈ U φ i) : y ∈ Wk φ t i := by
  have ht : t * t = 1 := SixF.t_mul_t hS.fc
  have hct : (t⁻¹ * (y⁻¹ * t * y)) * t = t * (t⁻¹ * (y⁻¹ * t * y)) :=
    sixH_U_central_Tplus h1 _ hκ t (sixH_R_le_Tplus sixH_t_mem_R)
  have h0 : t⁻¹ * ((t⁻¹ * (y⁻¹ * t * y))⁻¹ * t * (t⁻¹ * (y⁻¹ * t * y))) = 1 :=
    sixH_kappa_of_comm hct
  exact sixH_mem_W_of_sq_one hS hy ((sixH_kappa_kappa ht).symm.trans h0)

theorem sixH_kappa_mem_W (hS : SCSetting L K n φ t i) (h1 : H1Concl φ t i) {x : G}
    (hx : x ∈ Vtor φ t i i) : t⁻¹ * (x⁻¹ * t * x) ∈ Wk φ t i := by
  have ht : t * t = 1 := SixF.t_mul_t hS.fc
  have hU : t⁻¹ * ((t⁻¹ * (x⁻¹ * t * x))⁻¹ * t * (t⁻¹ * (x⁻¹ * t * x))) ∈ U φ i := by
    rw [sixH_kappa_kappa (y := x) ht]
    exact sixH_sq_kappa_mem_U hS hx
  exact sixH_mem_W_of_kappa_mem_U hS h1 (sixH_kappa_mem_V hS hx) hU

theorem sixH_kappa_eq_mem_U (hS : SCSetting L K n φ t i) {c z : G}
    (hc : c ∈ Wk φ t i) (hz : z ∈ Wk φ t i)
    (h : t⁻¹ * (c⁻¹ * t * c) = t⁻¹ * (z⁻¹ * t * z)) : c⁻¹ * z ∈ U φ i := by
  obtain ⟨hN, θ, hθ, -⟩ := FullCenterTorus.quotient_W hS.fc i
  haveI := hN
  have hθc : (θ (QuotientGroup.mk ⟨c, hc⟩) : G) = t⁻¹ * (c⁻¹ * t * c) := hθ ⟨c, hc⟩
  have hθz : (θ (QuotientGroup.mk ⟨z, hz⟩) : G) = t⁻¹ * (z⁻¹ * t * z) := hθ ⟨z, hz⟩
  have heq : θ (QuotientGroup.mk ⟨c, hc⟩) = θ (QuotientGroup.mk ⟨z, hz⟩) :=
    Subtype.ext (hθc.trans (h.trans hθz.symm))
  exact Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 (θ.injective heq))

theorem sixH_mem_U_of_kappa_eq_one (hS : SCSetting L K n φ t i) {w : G} (hw : w ∈ Wk φ t i)
    (hk : t⁻¹ * (w⁻¹ * t * w) = 1) : w ∈ U φ i := by
  have h := sixH_kappa_eq_mem_U hS (Wk φ t i).one_mem hw (by rw [hk]; group)
  simpa using h

theorem sixH_comm_of_central {V U' : Subgroup G} {c z : G}
    (hVU : ∀ u ∈ U', ∀ g ∈ V, u * g = g * u) (hz : ∀ g ∈ V, g * z = z * g)
    (hu : c⁻¹ * z ∈ U') : ∀ g ∈ V, g * c = c * g := by
  intro g hg
  obtain ⟨u, hu_def⟩ : ∃ u, u = c⁻¹ * z := ⟨_, rfl⟩
  rw [← hu_def] at hu
  have hc : c = z * u⁻¹ := by
    rw [hu_def]
    group
  have hgu : g * u⁻¹ = u⁻¹ * g := (hVU u⁻¹ (U'.inv_mem hu) g hg).symm
  rw [hc]
  calc g * (z * u⁻¹) = (g * z) * u⁻¹ := (mul_assoc _ _ _).symm
    _ = (z * g) * u⁻¹ := by rw [hz g hg]
    _ = z * (g * u⁻¹) := mul_assoc _ _ _
    _ = z * (u⁻¹ * g) := by rw [hgu]
    _ = z * u⁻¹ * g := (mul_assoc _ _ _).symm

theorem sixH_mem_W_of_central (hS : SCSetting L K n φ t i) (h2c : H2cConcl φ t i) {z : G}
    (hz : z ∈ Vtor φ t i i) (hcen : ∀ g ∈ Vtor φ t i i, g * z = z * g) : z ∈ Wk φ t i := by
  have hκV := sixH_kappa_mem_V hS hz
  have hcomm : (t⁻¹ * (z⁻¹ * t * z)) * z = z * (t⁻¹ * (z⁻¹ * t * z)) := hcen _ hκV
  exact sixH_mem_W_of_sq_one hS hz (sixH_sq_kappa_of_comm hcomm (h2c z hz))

theorem sixH_mem_U_of_central (hS : SCSetting L K n φ t i) (h1 : H1Concl φ t i)
    (h2a : H2aConcl φ t i) (h2c : H2cConcl φ t i) {z : G} (hz : z ∈ Vtor φ t i i)
    (hcen : ∀ g ∈ Vtor φ t i i, g * z = z * g) : z ∈ U φ i := by
  have ht : t * t = 1 := SixF.t_mul_t hS.fc
  have hzW : z ∈ Wk φ t i := sixH_mem_W_of_central hS h2c hz hcen
  have hκU : t⁻¹ * (z⁻¹ * t * z) ∈ U φ i :=
    FullCenterTorus.kappa_mem_U hS.fc i
      (Subgroup.mem_inf.mp (FullCenterTorus.W_le_Fi hS.fc i hzW)).2
  obtain ⟨hN, e, he⟩ := RootStandard.quotient_V hS.fc i hS.ne_bot hS.eq_bot
  haveI := hN
  obtain ⟨p, hp⟩ := e.surjective ⟨_, hκU⟩
  obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk_surjective p
  have hval : (e (QuotientGroup.mk ⟨x, hx⟩) : G) =
      (t⁻¹ * (x⁻¹ * t * x)) * (t⁻¹ * (x⁻¹ * t * x)) := he ⟨x, hx⟩
  have hxz : (t⁻¹ * (x⁻¹ * t * x)) * (t⁻¹ * (x⁻¹ * t * x)) = t⁻¹ * (z⁻¹ * t * z) := by
    rw [← hval, hp]
  have hcW : t⁻¹ * (x⁻¹ * t * x) ∈ Wk φ t i := sixH_kappa_mem_W hS h1 hx
  have hκc : t⁻¹ * ((t⁻¹ * (x⁻¹ * t * x))⁻¹ * t * (t⁻¹ * (x⁻¹ * t * x))) =
      t⁻¹ * (z⁻¹ * t * z) := (sixH_kappa_kappa (y := x) ht).trans hxz
  have hu : (t⁻¹ * (x⁻¹ * t * x))⁻¹ * z ∈ U φ i := sixH_kappa_eq_mem_U hS hcW hzW hκc
  have hcV := sixH_comm_of_central (V := Vtor φ t i i) (U' := U φ i)
    (fun u hu' g hg => h2a.central u hu' g (Subgroup.mem_inf.mp hg).1) hcen hu
  have hcomm : (t⁻¹ * (x⁻¹ * t * x)) * x = x * (t⁻¹ * (x⁻¹ * t * x)) := (hcV x hx).symm
  have hsq : (t⁻¹ * (x⁻¹ * t * x)) * (t⁻¹ * (x⁻¹ * t * x)) = 1 :=
    sixH_sq_kappa_of_comm hcomm (h2c x hx)
  exact sixH_mem_U_of_kappa_eq_one hS hzW (hxz.symm.trans hsq)

theorem sixH_h2d (hS : SCSetting L K n φ t i) (hM2 : ∀ x ∈ Mc φ t i, x * x ∈ U φ i)
    (h1 : H1Concl φ t i) (h2a : H2aConcl φ t i) (h2c : H2cConcl φ t i) : H2dConcl φ t i := by
  unfold H2dConcl
  have hVM : ∀ x ∈ Vtor φ t i i, x ∈ Mc φ t i := fun x hx => (Subgroup.mem_inf.mp hx).1
  have hUV : U φ i ≤ Vtor φ t i i :=
    (FullCenterTorus.U_le_W hS.fc i).trans (RootStandard.W_le_V hS.fc i hS.ne_bot hS.eq_bot i)
  refine ⟨le_antisymm ?_ ?_, fun x hx => ⟨fun hκ => sixH_mem_W_of_kappa_mem_U hS h1 hx hκ,
    fun hxW => FullCenterTorus.kappa_mem_U hS.fc i
      (Subgroup.mem_inf.mp (FullCenterTorus.W_le_Fi hS.fc i hxW)).2⟩⟩
  · intro g hg
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hg
    exact sixH_mem_U_of_central hS h1 h2a h2c z.2
      (fun g' hg' => congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨g', hg'⟩))
  · intro u hu
    exact Subgroup.mem_map.mpr ⟨⟨u, hUV hu⟩,
      Subgroup.mem_center_iff.mpr (fun g' => Subtype.ext
        ((h2a.central u hu g'.1 (hVM g'.1 g'.2)).symm)), rfl⟩

end Steps

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
