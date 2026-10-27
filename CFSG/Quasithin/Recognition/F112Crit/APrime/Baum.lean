module

public import CFSG.Quasithin.Background.B2Factorization
public import CFSG.Quasithin.Recognition.F112Crit.APrime.Offenders

public section

namespace CFSG.Quasithin.F112Crit.APrime

open CFSG.Open CFSG.Quasithin

variable {G : Type*} [Group G] [Finite G]

theorem le_of_isMaxElemAbelian_of_starBound {U Q H T A : Subgroup G} (hs : StarBound U Q H)
    (hU : IsElemAbelian 2 U) (hUQ : U ≤ Q) (hQU : Q ≤ Subgroup.centralizer (U : Set G))
    (hQT : Q ≤ T) (hTH : T ≤ H) (hA : IsMaxElemAbelian T A) : A ≤ Q := by
  by_contra hAQ
  have hAH : A ≤ H := hA.1.trans hTH
  have hbound := hs.of_isElemAbelian hAH hA.2.1 hAQ
  have hUT : U ≤ T := hUQ.trans hQT
  let C : Subgroup G := A ⊓ Subgroup.centralizer (U : Set G)
  have hCea : IsElemAbelian 2 C := hA.2.1.mono inf_le_left
  have hCcomm : ∀ a ∈ U, ∀ b ∈ C, a * b = b * a := by
    intro a ha b hb
    exact Subgroup.mem_centralizer_iff.mp hb.2 a ha
  have hUcent : U ≤ Subgroup.centralizer (U : Set G) := by
    intro u hu
    exact Subgroup.mem_centralizer_iff.mpr fun v hv => hU.comm hv hu
  have hUC : U ⊓ C = U ⊓ A := by
    rw [show C = A ⊓ Subgroup.centralizer (U : Set G) from rfl, ← inf_assoc]
    exact inf_of_le_left (inf_le_left.trans hUcent)
  have hsupT : U ⊔ C ≤ T := sup_le hUT (inf_le_left.trans hA.1)
  have hsupEA : IsElemAbelian 2 (U ⊔ C) := IsElemAbelian.sup_of_commute hU hCea hCcomm
  have hsupmax : Nat.card (U ⊔ C : Subgroup G) ≤ Nat.card A := hA.2.2 _ hsupT hsupEA
  have hcard := B2F.card_sup_mul_card_inf_of_commute (A := U) (B := C) hCcomm
  have hrelU : A.relIndex U * Nat.card (U ⊓ A : Subgroup G) = Nat.card U := by
    simpa [inf_comm] using Subgroup.relIndex_mul_card A U
  have hrelA : C.relIndex A * Nat.card C = Nat.card A := by
    have hCA : C ≤ A := inf_le_left
    have h := Subgroup.relIndex_mul_card C A
    rwa [inf_of_le_left hCA] at h
  have hcardU : Nat.card U * Nat.card C =
      A.relIndex U * Nat.card (U ⊓ A : Subgroup G) * Nat.card C := by
    rw [← hrelU]
  have hcardA : Nat.card A * Nat.card (U ⊓ A : Subgroup G) =
      C.relIndex A * Nat.card C * Nat.card (U ⊓ A : Subgroup G) := by
    rw [← hrelA]
  have hle : A.relIndex U * Nat.card (U ⊓ A : Subgroup G) * Nat.card C ≤
      C.relIndex A * Nat.card C * Nat.card (U ⊓ A : Subgroup G) := by
    calc A.relIndex U * Nat.card (U ⊓ A : Subgroup G) * Nat.card C
        = Nat.card U * Nat.card C := hcardU.symm
      _ = Nat.card (U ⊔ C : Subgroup G) * Nat.card (U ⊓ C : Subgroup G) := hcard.symm
      _ ≤ Nat.card A * Nat.card (U ⊓ C : Subgroup G) := Nat.mul_le_mul_right _ hsupmax
      _ = Nat.card A * Nat.card (U ⊓ A : Subgroup G) := by rw [hUC]
      _ = C.relIndex A * Nat.card C * Nat.card (U ⊓ A : Subgroup G) := hcardA
  have hcore : A.relIndex U ≤ C.relIndex A := by
    have h4 : A.relIndex U * Nat.card (U ⊓ A : Subgroup G) * Nat.card C ≤
        C.relIndex A * Nat.card (U ⊓ A : Subgroup G) * Nat.card C := by
      calc A.relIndex U * Nat.card (U ⊓ A : Subgroup G) * Nat.card C
          ≤ C.relIndex A * Nat.card C * Nat.card (U ⊓ A : Subgroup G) := hle
        _ = C.relIndex A * Nat.card (U ⊓ A : Subgroup G) * Nat.card C := by ring
    exact Nat.le_of_mul_le_mul_right
      (Nat.le_of_mul_le_mul_right h4 (Nat.card_pos)) (Nat.card_pos)
  have hAcent : A ≤ Subgroup.centralizer (A : Set G) := fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun b hb => hA.2.1.comm hb ha
  have h1 : (U ⊓ Subgroup.centralizer (A : Set G)).relIndex U ≤ (U ⊓ A).relIndex U :=
    Subgroup.relIndex_le_of_le_left (inf_le_inf_left U hAcent)
      Subgroup.index_ne_zero_of_finite
  have h2 : (U ⊓ A).relIndex U = A.relIndex U :=
    Subgroup.inf_relIndex_left (H := U) (K := A)
  have h4 : C.relIndex A ≤ (A ⊓ Q).relIndex A :=
    Subgroup.relIndex_le_of_le_left (inf_le_inf_left A hQU)
      Subgroup.index_ne_zero_of_finite
  have hkey : (U ⊓ Subgroup.centralizer (A : Set G)).relIndex U ≤ (A ⊓ Q).relIndex A := by
    calc (U ⊓ Subgroup.centralizer (A : Set G)).relIndex U
        ≤ (U ⊓ A).relIndex U := h1
      _ = A.relIndex U := h2
      _ ≤ C.relIndex A := hcore
      _ ≤ (A ⊓ Q).relIndex A := h4
  omega

theorem thompsonJ_le_of_starBound {U Q H T : Subgroup G} (hs : StarBound U Q H)
    (hU : IsElemAbelian 2 U) (hUQ : U ≤ Q) (hQU : Q ≤ Subgroup.centralizer (U : Set G))
    (hQT : Q ≤ T) (hTH : T ≤ H) : thompsonJ T ≤ Q :=
  iSup₂_le fun _ hA => le_of_isMaxElemAbelian_of_starBound hs hU hUQ hQU hQT hTH hA

theorem le_omegaOneCenterOf_thompsonJ_of_starBound {U Q H T : Subgroup G} (hs : StarBound U Q H)
    (hU : IsElemAbelian 2 U) (hUQ : U ≤ Q) (hQU : Q ≤ Subgroup.centralizer (U : Set G))
    (hQT : Q ≤ T) (hTH : T ≤ H) : U ≤ omegaOneCenterOf (thompsonJ T) := by
  have hUT : U ≤ T := hUQ.trans hQT
  have hUA : ∀ A : Subgroup G, IsMaxElemAbelian T A → U ≤ A := by
    intro A hA
    have hAQ : A ≤ Q := le_of_isMaxElemAbelian_of_starBound hs hU hUQ hQU hQT hTH hA
    have hUC : U ≤ Subgroup.centralizer (A : Set G) := by
      intro u hu
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact (Subgroup.mem_centralizer_iff.mp (hQU (hAQ ha)) u hu).symm
    exact (le_inf le_rfl hUC).trans
      (CFSG.Quasithin.inf_centralizer_le_of_isMaxElemAbelian hU hUT hA)
  rw [(CFSG.Quasithin.omegaOne_centralizer_thompsonJ T).2]
  exact le_iInf₂ fun A hA => hUA A hA

theorem thompsonJ_eq_of_starBound {U Q H T : Subgroup G} (hs : StarBound U Q H)
    (hU : IsElemAbelian 2 U) (hUQ : U ≤ Q) (hQU : Q ≤ Subgroup.centralizer (U : Set G))
    (hQT : Q ≤ T) (hTH : T ≤ H) : thompsonJ T = thompsonJ Q :=
  CFSG.Quasithin.thompsonJ_eq_of_le
    (thompsonJ_le_of_starBound hs hU hUQ hQU hQT hTH) hQT

theorem le_normalizer_thompsonJ_of_starBound {U Q H T : Subgroup G} (hs : StarBound U Q H)
    (hU : IsElemAbelian 2 U) (hUQ : U ≤ Q) (hQU : Q ≤ Subgroup.centralizer (U : Set G))
    (hQT : Q ≤ T) (hTH : T ≤ H) (hHQ : H ≤ Subgroup.normalizer (Q : Set G)) :
    H ≤ Subgroup.normalizer (thompsonJ T : Set G) := by
  have h := hHQ.trans (CFSG.Quasithin.normalizer_le_normalizer_thompsonJ Q)
  rwa [← thompsonJ_eq_of_starBound hs hU hUQ hQU hQT hTH] at h

end CFSG.Quasithin.F112Crit.APrime

end