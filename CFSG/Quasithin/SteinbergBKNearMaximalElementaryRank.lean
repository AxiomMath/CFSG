module

public import CFSG.Foundations.HigherElementaryThompson
import CFSG.Quasithin.Background.BlueprintB2Thompson

public section

namespace CFSG.Quasithin.SteinbergBK

open Subgroup CFSG

variable {S : Type*} [Group S] [Finite S]

theorem near_maximal_elementary_whole_module_rank_inequality (V : Subgroup S) [V.Normal]
    [hV : IsElementaryAbelian 2 V] {j : ℕ} {A : Subgroup S}
    (hA : A ∈ higherElemThompsonFamily S j) :
    ∃ d e : ℕ, (V ⊓ centralizer (A : Set S)).relIndex V = 2 ^ d ∧
      (A ⊓ centralizer (V : Set S)).relIndex A = 2 ^ e ∧ d ≤ j + e ∧
      IsElementaryAbelian 2 ↥((A ⊓ centralizer (V : Set S)) ⊔ V) ∧
      (d = j + e → pRank 2 ↥((A ⊓ centralizer (V : Set S)) ⊔ V) = pRank 2 S ∧
        A ⊓ V = V ⊓ centralizer (A : Set S)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hAe, hAcard⟩ := (mem_higherElemThompsonFamily_iff j A).mp hA
  set m := pRank 2 S with hm
  set C := A ⊓ centralizer (V : Set S) with hC
  set CV := V ⊓ centralizer (A : Set S) with hCV
  have hCA : C ≤ A := inf_le_left
  have hCe : IsElementaryAbelian 2 C :=
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (show (a : S) * b = b * a from
        congrArg Subtype.val (hAe.is_comm.comm ⟨a, hCA a.2⟩ ⟨b, hCA b.2⟩))⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by
        have := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A) (x : S) (hCA x.2)
        rw [coe_pow, this, coe_one]) }
  have hVC : V ≤ centralizer (C : Set S) := le_centralizer_iff.mp inf_le_right
  have hBe : IsElementaryAbelian 2 ↥(C ⊔ V) := IsElementaryAbelian.sup_of_le_centralizer hVC
  have hBcard : Nat.card ↥(C ⊔ V) ≤ 2 ^ m := Quasithin.BlueprintB2.card_le_pow_pRank hBe
  have hVV : V ≤ centralizer (V : Set S) := fun x hx => mem_centralizer_iff.mpr fun y hy =>
    congrArg Subtype.val (hV.is_comm.comm ⟨y, hy⟩ ⟨x, hx⟩)
  have hAV : A ⊓ V ≤ CV := fun x hx => ⟨hx.2, mem_centralizer_iff.mpr fun y hy =>
    congrArg Subtype.val (hAe.is_comm.comm ⟨y, hy⟩ ⟨x, hx.1⟩)⟩
  have hVCinf : V ⊓ C = A ⊓ V := by
    rw [hC, ← inf_assoc, inf_comm V A, inf_assoc, inf_eq_left.mpr hVV]
  have h1 : V.relIndex (C ⊔ V) * Nat.card V = Nat.card ↥(C ⊔ V) := by
    have := relIndex_mul_card (H := V) (K := C ⊔ V)
    rwa [inf_eq_left.mpr le_sup_right] at this
  have h2 : V.relIndex (C ⊔ V) = V.relIndex C := relIndex_sup_right C V
  have h3 : V.relIndex C * Nat.card ↥(A ⊓ V) = Nat.card C := by
    have := relIndex_mul_card (H := V) (K := C)
    rwa [hVCinf] at this
  have h4 : CV.relIndex V * Nat.card CV = Nat.card V := by
    have := relIndex_mul_card (H := CV) (K := V)
    rwa [inf_eq_left.mpr (inf_le_left : CV ≤ V)] at this
  have h5 : C.relIndex A * Nat.card C = Nat.card A := by
    have := relIndex_mul_card (H := C) (K := A)
    rwa [inf_eq_left.mpr hCA] at this
  have h6 : Nat.card ↥(A ⊓ V) ≤ Nat.card CV := card_le_of_le hAV
  have hCVpos : 0 < Nat.card CV := Nat.card_pos
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hBpos : 0 < Nat.card ↥(C ⊔ V) := Nat.card_pos
  have hkey : Nat.card C * CV.relIndex V * Nat.card CV =
      Nat.card ↥(C ⊔ V) * Nat.card ↥(A ⊓ V) := by
    rw [mul_assoc, h4, ← h1, h2, ← h3]
    ring
  have hCB : Nat.card C * CV.relIndex V ≤ Nat.card ↥(C ⊔ V) := by
    refine Nat.le_of_mul_le_mul_right ?_ hCVpos
    rw [hkey]
    exact Nat.mul_le_mul_left _ h6
  have hm2 : 2 ^ m ≤ 2 ^ j * Nat.card A := by
    rw [hAcard, ← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hineq : CV.relIndex V ≤ 2 ^ j * C.relIndex A := by
    refine Nat.le_of_mul_le_mul_left ?_ hCpos
    calc Nat.card C * CV.relIndex V ≤ 2 ^ m := hCB.trans hBcard
      _ ≤ 2 ^ j * Nat.card A := hm2
      _ = Nat.card C * (2 ^ j * C.relIndex A) := by rw [← h5]; ring
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (IsElementaryAbelian.isPGroup 2 V)
  obtain ⟨d, -, hd⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show CV.relIndex V ∣ 2 ^ k from hk ▸ Dvd.intro _ h4)
  obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show C.relIndex A ∣ 2 ^ (m - j) from hAcard ▸ Dvd.intro _ h5)
  refine ⟨d, e, hd, he, ?_, hBe, fun hde => ?_⟩
  · rw [hd, he, ← pow_add] at hineq
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hineq
  · have heq : CV.relIndex V = 2 ^ j * C.relIndex A := by rw [hd, he, hde, pow_add]
    have hge : 2 ^ m ≤ Nat.card C * CV.relIndex V := by
      calc 2 ^ m ≤ 2 ^ j * Nat.card A := hm2
        _ = Nat.card C * CV.relIndex V := by rw [heq, ← h5]; ring
    have hBm : Nat.card ↥(C ⊔ V) = 2 ^ m := le_antisymm hBcard (hge.trans hCB)
    have hCBeq : Nat.card C * CV.relIndex V = Nat.card ↥(C ⊔ V) := le_antisymm hCB (hBm ▸ hge)
    refine ⟨?_, ?_⟩
    · have := hBe
      exact pRank_eq_of_card_eq_pow one_lt_two hBm
    · refine eq_of_le_of_card_ge hAV ?_
      rw [hCBeq] at hkey
      exact (Nat.eq_of_mul_eq_mul_left hBpos hkey).le

end CFSG.Quasithin.SteinbergBK
