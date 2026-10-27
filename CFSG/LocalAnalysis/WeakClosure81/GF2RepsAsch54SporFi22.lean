module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporOut2
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporIndexTwo
public import CFSG.Monster.B.Fischer.Fi22Model
public import CFSG.Sporadic.FischerOddCore.Fi22CTI
public import Certificates.Certificate75338
public import Certificates.Certificate75339

import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporOrder

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore CFSG.Sporadic.FischerOddCore.Native
open CFSG.LocalAnalysis.WeakClosure81.Asch54Fi22

namespace Asch54Fi22

theorem A0_le_P : A0 ≤ fi22P :=
  Certificates.certificate75338.1

theorem card_A0 : Nat.card A0 = 17694720 :=
  Certificates.certificate75338.2.1

theorem T_le_A0 : fi22OuterT ≤ A0 :=
  Certificates.certificate75338.2.2.1

theorem T_le_H : fi22OuterT ≤ fi22H 1 :=
  Certificates.certificate75338.2.2.2.1

theorem mP_mul_self : mP * mP = 1 :=
  Certificates.certificate75338.2.2.2.2.1

theorem u_mul_mP_mem : fi22U * mP ∈ fi22P :=
  Certificates.certificate75338.2.2.2.2.2.1

theorem mP_conj_T :
    ∀ x ∈ fi22OuterT, mP * x * mP⁻¹ ∈ fi22OuterT :=
  Certificates.certificate75338.2.2.2.2.2.2.1

theorem mP_conj_A0 : ∀ x ∈ A0, mP * x * mP⁻¹ ∈ A0 :=
  Certificates.certificate75338.2.2.2.2.2.2.2.1

theorem mP_conj_H :
    ∀ x ∈ fi22H 1, mP * x * mP⁻¹ ∈ fi22H 1 :=
  Certificates.certificate75338.2.2.2.2.2.2.2.2

theorem P_le_sup : fi22P ≤ A0 ⊔ fi22H 1 :=
  Certificates.certificate75339

theorem mP_mem_R :
    mP ∈ fi22R :=
  (mem_fi22R_iff mP).2 (Or.inr u_mul_mP_mem)

theorem mP_not_mem_P :
    mP ∉ fi22P := fun h => by
  apply fi22U_not_mem
  have := fi22P.mul_mem u_mul_mP_mem (fi22P.inv_mem h)
  rwa [mul_inv_cancel_right] at this

theorem H_le_P :
    fi22H 1 ≤ fi22P := by
  rw [fi22H_one_eq, Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  have h := ((fi22CentOrder_facts (c := 1) (by norm_num)).2.2 k
    (by simpa [fi22CentGenCount] using hk)).1
  rw [fi22CentStrong_get (c := 1) (by norm_num) (by simp [fi22CentStrongCount]; omega)] at h
  exact (fi22InP_iff (rep_ctiG hk)).1 h

theorem card_subgroupOf_P {X : Subgroup (Equiv.Perm (Fin 3510))} (hX : X ≤ fi22P) :
    Nat.card (X.subgroupOf fi22P) = Nat.card X :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv

theorem isSylowIn_T :
    IsSylowIn 2 (fi22OuterT.subgroupOf fi22P) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := fi22OuterT_sylow
  refine ⟨le_top, hS ▸ S.isPGroup', ?_⟩
  rw [Subgroup.relIndex_top_right, ← hS]
  exact S.not_dvd_index

theorem isLPair_P :
    IsLPair IsCalL0 (fi22OuterT.subgroupOf fi22P) (A0.subgroupOf fi22P)
      ((fi22H 1).subgroupOf fi22P) where
  le_left := fun _ hx => Subgroup.mem_subgroupOf.2 (T_le_A0 (Subgroup.mem_subgroupOf.1 hx))
  le_right := fun _ hx => Subgroup.mem_subgroupOf.2 (T_le_H (Subgroup.mem_subgroupOf.1 hx))
  ne_top_left h := by
    have h1 := congrArg (fun H : Subgroup fi22P => Nat.card H) h
    simp only [Subgroup.card_top, card_subgroupOf_P A0_le_P, card_A0, card_fi22P] at h1
    omega
  ne_top_right h := by
    have h1 := congrArg (fun H : Subgroup fi22P => Nat.card H) h
    simp only [Subgroup.card_top, card_subgroupOf_P H_le_P, card_fi22H_one, card_fi22P] at h1
    omega
  not_left := not_hasCompFactor_isCalL0_of_dvd
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput (k := 17) (N := 17694720)
    (by decide +kernel) (by rw [card_subgroupOf_P A0_le_P, card_A0])
  not_right := not_hasCompFactor_isCalL0_of_dvd
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput (k := 17) (N := 53084160)
    (by decide +kernel) (by rw [card_subgroupOf_P H_le_P, card_fi22H_one])
  sup_eq_top := by
    rw [← Subgroup.subgroupOf_sup A0_le_P H_le_P, Subgroup.subgroupOf_eq_top]
    exact P_le_sup

theorem card_subgroupOf_R {X : Subgroup (Equiv.Perm (Fin 3510))} (hX : X ≤ fi22R) :
    Nat.card (X.subgroupOf fi22R) = Nat.card X :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv

theorem sup_m_le_R
    {X : Subgroup (Equiv.Perm (Fin 3510))} (hX : X ≤ fi22P) : X ⊔ Subgroup.zpowers mP ≤ fi22R :=
  sup_le (hX.trans fi22P_le_R) ((Subgroup.zpowers_le).2 mP_mem_R)

theorem card_sup_m
    {X : Subgroup (Equiv.Perm (Fin 3510))} (hX : X ≤ fi22P) (hm : ∀ x ∈ X, mP * x * mP⁻¹ ∈ X) :
    Nat.card ↥(X ⊔ Subgroup.zpowers mP) = 2 * Nat.card X :=
  card_sup_zpowers_eq_two_mul mP_mul_self (fun h => mP_not_mem_P (hX h)) hm

theorem R_le_P_sup :
    fi22R ≤ fi22P ⊔ Subgroup.zpowers mP := by
  have hn : ∀ x ∈ fi22P, mP * x * mP⁻¹ ∈ fi22P := fun x hx =>
    (Subgroup.mem_normalizer_iff.1 (fi22R_le_normalizer mP_mem_R) x).1 hx
  have hle := sup_m_le_R (le_refl fi22P)
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).ge
  rw [card_sup_m (le_refl _) hn, card_fi22R, card_fi22P]

theorem isSylowIn_Tm :
    IsSylowIn 2 ((fi22OuterT ⊔ Subgroup.zpowers mP).subgroupOf fi22R) ⊤ := by
  have hc : Nat.card ((fi22OuterT ⊔ Subgroup.zpowers mP).subgroupOf fi22R) = 2 ^ 18 := by
    rw [card_subgroupOf_R (sup_m_le_R fi22OuterT_le), card_sup_m fi22OuterT_le mP_conj_T,
      card_fi22OuterT]
    norm_num
  refine ⟨le_top, IsPGroup.of_card hc, ?_⟩
  have h := ((fi22OuterT ⊔ Subgroup.zpowers mP).subgroupOf fi22R).card_mul_index
  rw [hc, card_fi22R] at h
  rw [Subgroup.relIndex_top_right, show ((fi22OuterT ⊔ Subgroup.zpowers mP).subgroupOf fi22R).index =
    492567075 by omega]
  decide

theorem isLPair_R :
    IsLPair IsCalL0 ((fi22OuterT ⊔ Subgroup.zpowers mP).subgroupOf fi22R)
      ((A0 ⊔ Subgroup.zpowers mP).subgroupOf fi22R)
      ((fi22H 1 ⊔ Subgroup.zpowers mP).subgroupOf fi22R) where
  le_left := fun _ hx => Subgroup.mem_subgroupOf.2
    (sup_le_sup_right T_le_A0 _ (Subgroup.mem_subgroupOf.1 hx))
  le_right := fun _ hx => Subgroup.mem_subgroupOf.2
    (sup_le_sup_right T_le_H _ (Subgroup.mem_subgroupOf.1 hx))
  ne_top_left h := by
    have h1 := congrArg (fun H : Subgroup fi22R => Nat.card H) h
    simp only [Subgroup.card_top, card_subgroupOf_R (sup_m_le_R A0_le_P),
      card_sup_m A0_le_P mP_conj_A0, card_A0, card_fi22R] at h1
    omega
  ne_top_right h := by
    have h1 := congrArg (fun H : Subgroup fi22R => Nat.card H) h
    simp only [Subgroup.card_top, card_subgroupOf_R (sup_m_le_R H_le_P),
      card_sup_m H_le_P mP_conj_H, card_fi22H_one, card_fi22R] at h1
    omega
  not_left := not_hasCompFactor_isCalL0_of_dvd
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput (k := 18) (N := 35389440)
    (by decide +kernel)
    (by rw [card_subgroupOf_R (sup_m_le_R A0_le_P), card_sup_m A0_le_P mP_conj_A0, card_A0])
  not_right := not_hasCompFactor_isCalL0_of_dvd
    CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput (k := 18) (N := 106168320)
    (by decide +kernel)
    (by rw [card_subgroupOf_R (sup_m_le_R H_le_P), card_sup_m H_le_P mP_conj_H, card_fi22H_one])
  sup_eq_top := by
    rw [← Subgroup.subgroupOf_sup (sup_m_le_R A0_le_P) (sup_m_le_R H_le_P),
      Subgroup.subgroupOf_eq_top]
    refine R_le_P_sup.trans (sup_le ?_ ?_)
    · exact P_le_sup.trans (sup_le_sup le_sup_left le_sup_left)
    · exact le_sup_right.trans le_sup_left

end Asch54Fi22

open Asch54Fi22 in
theorem asch54SporGenAt_fi22 :
    Asch54SporGenAt .Fi22 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
  exact asch54SporGenAt_of_isLPair_of_card_outer_eq_two (C := fi22P) (D := fi22R)
    (fun X _ hX => by
      obtain ⟨e⟩ := hX
      exact ⟨e.trans (b.symm.trans fi22PermEquiv)⟩) card_fi22Out
    fi22RAut.symm isSylowIn_T isLPair_P isSylowIn_Tm isLPair_R

end CFSG.LocalAnalysis.WeakClosure81
