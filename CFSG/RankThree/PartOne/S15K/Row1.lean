module

public import CFSG.RankThree.PartOne.S15K.InnerAction
public import CFSG.RankThree.PartOne.S15K.AutTorus
public import CFSG.RankThree.PartOne.S15K.LinLift
public import CFSG.RankThree.PartOne.S12.Facts13
public import CFSG.RankThree.PartOne.S12.Equivariance

public section

namespace CFSG.RankThree.PartOne.S15K

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.RankThree.PartOne.KCLinComm

variable {G : Type} [Group G] [Finite G]

theorem row1_lifts {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h : Sec12Hyp G p A c L E) (h13 : Sec13Facts G p A c L E) (hEA : E = A) {f : ℕ} (hf : 1 ≤ f)
    (φ : ↥(lieGenerated p E) ≃* projectiveSL 4 (GaloisField 2 f)) :
    ∃ B : ↥E → GL (Fin 4) (GaloisField 2 f),
      (∀ e, (B e : Matrix (Fin 4) (Fin 4) (GaloisField 2 f)).det = 1) ∧ (∀ e, B e ^ p = 1) ∧
      (∀ e : ↥E, actP φ ⟨(e : G), E_le_normalizer_lieGenerated h.prime e.2⟩ =
        LinearFlag.conjAut 4 (GaloisField 2 f) (B e)) ∧
      (∀ e e' : ↥E, B e * B e' = B e' * B e) := by
  have hp := h.prime
  have hp2 : p ≠ 2 := by have := h.three_lt; omega
  have hEI : E ≤ Subgroup.normalizer (lieGenerated p E : Set G) :=
    E_le_normalizer_lieGenerated hp
  have hWI : Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (lieGenerated p E : Set G) :=
    torusNormalizer_le_lieNormalizer hp E
  have hE : IsElementaryAbelian p E := h.E_elem
  have hEexp : ∀ e ∈ E, e ^ p = 1 := fun e he =>
    elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) e he
  have hEcard : p < Nat.card E := by
    have h3 : Nat.card E = p ^ 3 := by rw [hEA]; exact h.A_card
    rw [h3]
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hinn := actP_mem_range_conjAut (by norm_num : 3 ≤ 4) Nat.prime_two hK hp hp2 φ hEI hWI hEexp
    hEcard h13.irreducible
  have hpow : ∀ e : ↥E, (actP φ ⟨(e : G), hEI e.2⟩) ^ p = 1 := by
    intro e
    rw [← map_pow]
    have : (⟨(e : G), hEI e.2⟩ : ↥(Subgroup.normalizer (lieGenerated p E : Set G))) ^ p = 1 :=
      Subtype.ext (hEexp e e.2)
    rw [this, map_one]
  choose A0 hA0 using fun e : ↥E => hinn e
  have hlift : ∀ e : ↥E, ∃ B : GL (Fin 4) (GaloisField 2 f),
      LinearFlag.conjAut 4 (GaloisField 2 f) B = actP φ ⟨(e : G), hEI e.2⟩ ∧
        (B : Matrix (Fin 4) (Fin 4) (GaloisField 2 f)).det = 1 ∧ B ^ p = 1 := by
    intro e
    obtain ⟨B, hB1, hB2, hB3⟩ := exists_sl_lift_of_pow_eq_one (p := p) (A0 e)
      (by rw [hA0 e]; exact hpow e)
    exact ⟨B, hB1.trans (hA0 e), hB2, hB3⟩
  choose B hB1 hB2 hB3 using hlift
  refine ⟨B, hB2, hB3, fun e => (hB1 e).symm, fun e e' => ?_⟩
  refine mul_comm_of_conjAut_commute (hB2 e) (hB2 e') ?_
  rw [hB1 e, hB1 e', ← map_mul, ← map_mul]
  congr 1
  have hcomm : (e : G) * e' = e' * e := congrArg Subtype.val (hE.is_comm.comm e e')
  exact Subtype.ext hcomm

end CFSG.RankThree.PartOne.S15K
