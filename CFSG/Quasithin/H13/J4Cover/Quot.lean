module

public import CFSG.Quasithin.EmptyFaithful.ModJ4TLC
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2Hat
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocDef

public section

namespace CFSG.Quasithin.H13.J4Cover

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Quasithin.J4Loc
open CFSG.Quasithin.H13.J4 (IsAutTripleM22 IsTypeJ4Centralizer M22)
open CFSG.Quasithin.ModJ4 (tlc_isTypeJ4Centralizer_z0)

theorem exists_quotient_centralizer :
    ∃ (R : Type) (_ : Group R) (_ : Finite R)
      (ρ : ↥(Subgroup.centralizer ({z0} : Set J)) →* R), Function.Surjective ρ ∧
      (∀ d ∈ ρ.ker, ∃ n : ℕ, d ^ (2 ^ n) = 1) ∧
      ∃ N₀ : Subgroup R, N₀.Normal ∧ N₀.index = 2 ∧
        CFSG.Quasithin.IsHat ↥N₀ (CFSG.Blueprint.NativeSporadic.Carrier .M22) := by
  classical
  let C : Subgroup J := Subgroup.centralizer ({z0} : Set J)
  let Q : Subgroup C := CFSG.pCore 2 C
  let R : Type := C ⧸ Q
  let ρ : C →* R := QuotientGroup.mk' Q
  have htype : IsTypeJ4Centralizer J z0 := tlc_isTypeJ4Centralizer_z0
  have hcardC : Nat.card C = 21799895040 := htype.1
  haveI : Finite C := Nat.finite_of_card_ne_zero (by rw [hcardC]; norm_num)
  obtain ⟨-, -, -, hX, -⟩ := htype
  obtain ⟨Z, hZn, hZ3, hidx, hperf, hcen, -, ψ, -, hψs, hψk, -, -, -, -⟩ := hX
  haveI : Z.Normal := hZn
  let D : Subgroup R := Subgroup.centralizer (Z : Set R)
  let W : Subgroup D := Z.subgroupOf D
  have hZD : Z ≤ D := by
    rw [← hcen]
    exact Subgroup.map_subtype_le _
  have hW3 : Nat.card W = 3 := by
    rw [← hZ3]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZD).toEquiv
  have e : D ⧸ W ≃* M22 :=
    (QuotientGroup.quotientMulEquivOfEq hψk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)
  have hS : IsSimpleGroup M22 := (CFSG.Sporadic.Mathieu.fam_m22_simplicity).2.2
  haveI : IsSimpleGroup M22 := hS
  have hnab : ∃ a b : M22, a * b ≠ b * a := by
    by_contra h
    push Not at h
    letI : CommGroup M22 := { (inferInstance : Group M22) with mul_comm := h }
    have hp : (Nat.card M22).Prime := IsSimpleGroup.prime_card
    rw [CFSG.Sporadic.Mathieu.card_M22] at hp
    norm_num at hp
  have hDindex : D.index = 2 := hidx
  have hDnormal : D.Normal := Subgroup.normal_of_index_eq_two hDindex
  have hHat : CFSG.Quasithin.IsHat D (CFSG.Blueprint.NativeSporadic.Carrier .M22) :=
    CFSG.Quasithin.J4M2.isHat_of_quotient_of_normal_order_three
      hperf.commutator_eq_top W hW3 e hS hnab
  refine ⟨R, inferInstance, inferInstance, ρ, ?_, ?_, D, hDnormal, hDindex, hHat⟩
  · exact QuotientGroup.mk'_surjective Q
  · intro d hd
    have hker : ρ.ker = Q := QuotientGroup.ker_mk' Q
    rw [hker] at hd
    obtain ⟨n, hn⟩ := CFSG.pCore_isPGroup (G := C) (p := 2) ⟨d, hd⟩
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩

end CFSG.Quasithin.H13.J4Cover
