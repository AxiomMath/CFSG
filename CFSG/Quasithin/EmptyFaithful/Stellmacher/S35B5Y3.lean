module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35B5Y1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.B5

open S35.Std

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem relIndex_ne_zero' (A K : Subgroup G) : A.relIndex K ≠ 0 := by
  have h := Subgroup.relIndex_mul_card A K
  have hpos : 0 < Nat.card K := Nat.card_pos
  intro h0
  rw [h0, zero_mul] at h
  omega

theorem relIndex_sup_eq_of_le_normalizer {B Q : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (Q : Set G)) :
    B.relIndex (B ⊔ Q) = (B ⊓ Q).relIndex Q := by
  have h := relIndex_inf_eq_relIndex_sup hB
  have hi := Subgroup.relIndex_mul_card B (B ⊔ Q)
  have hj := Subgroup.relIndex_mul_card Q (B ⊔ Q)
  have hk := Subgroup.relIndex_mul_card (B ⊓ Q) B
  have hm := Subgroup.relIndex_mul_card (B ⊓ Q) Q
  rw [inf_eq_left.mpr le_sup_left] at hi
  rw [inf_eq_left.mpr le_sup_right] at hj
  rw [inf_eq_left.mpr inf_le_left] at hk
  rw [inf_eq_left.mpr inf_le_right] at hm
  have hpos : 0 < Nat.card B := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc B.relIndex (B ⊔ Q) * Nat.card B = Nat.card ↥(B ⊔ Q) := hi
    _ = Q.relIndex (B ⊔ Q) * Nat.card Q := hj.symm
    _ = (B ⊓ Q).relIndex B * Nat.card Q := by rw [h]
    _ = (B ⊓ Q).relIndex B * ((B ⊓ Q).relIndex Q * Nat.card ↥(B ⊓ Q)) := by rw [hm]
    _ = (B ⊓ Q).relIndex Q * ((B ⊓ Q).relIndex B * Nat.card ↥(B ⊓ Q)) := by ring
    _ = (B ⊓ Q).relIndex Q * Nat.card B := by rw [hk]

theorem relIndex_normalizer_Y_le_four (hC : Ch.Ctx H M S) (h15c : Claim15c H M)
    {β l δ l0 γ : Geo H M} (hcfg : Cfg H M β l δ l0 γ)
    (hgen : stab β ≤ Wb δ ⊔ Wb γ ⊔ Qv β) (hcomm : ⁅Vn δ, Vn γ⁆ = ⊥) :
    (Subgroup.normalizer ((Yg β δ γ : Subgroup G) : Set G) ⊓ stab β).relIndex
      (stab β) ≤ 4 := by
  have hS := hC.sit
  obtain ⟨hWδ, hWγ, hQ0⟩ := Y_normalised hC h15c hcfg hcomm
  have hQst : Qv β ≤ stab β := fun x hx => ((mem_Qv_iff hS β).mp hx).1
  have hWδs : Wb δ ≤ stab β :=
    (Wb_le_Ql hS (mem_nbrs_symm.mpr hcfg.δ_nbr)).trans
      (Qv_le_stab hS (mem_nbrs_symm.mp hcfg.l_nbr))
  have hWγs : Wb γ ≤ stab β :=
    (Wb_le_Ql hS (mem_nbrs_symm.mpr hcfg.γ_nbr)).trans
      (Qv_le_stab hS (mem_nbrs_symm.mp hcfg.l0_nbr))
  have hQ0Q : Qv β ⊓ Qv l ⊓ Qv l0 ≤ Qv β := inf_le_left.trans inf_le_left
  have hBN : Wb δ ⊔ Wb γ ⊔ (Qv β ⊓ Qv l ⊓ Qv l0) ≤
      Subgroup.normalizer ((Yg β δ γ : Subgroup G) : Set G) ⊓ stab β :=
    sup_le (sup_le (le_inf hWδ hWδs) (le_inf hWγ hWγs)) (le_inf hQ0 (hQ0Q.trans hQst))
  have hBs : Wb δ ⊔ Wb γ ⊔ (Qv β ⊓ Qv l ⊓ Qv l0) ≤ stab β :=
    hBN.trans inf_le_right
  have hEq : (Wb δ ⊔ Wb γ ⊔ (Qv β ⊓ Qv l ⊓ Qv l0)) ⊔ Qv β = stab β :=
    le_antisymm (sup_le hBs hQst)
      (hgen.trans (sup_le_sup_right le_sup_left (Qv β)))
  have hnorm : Wb δ ⊔ Wb γ ⊔ (Qv β ⊓ Qv l ⊓ Qv l0) ≤ Subgroup.normalizer (Qv β : Set G) :=
    hBs.trans (le_normalizer_pCoreOf 2 (stab β))
  have h1 := relIndex_sup_eq_of_le_normalizer hnorm
  rw [hEq] at h1
  have hle1 := Subgroup.relIndex_le_of_le_left (L := stab β) hBN (relIndex_ne_zero' _ _)
  have hQ0B : Qv β ⊓ Qv l ⊓ Qv l0 ≤
      (Wb δ ⊔ Wb γ ⊔ (Qv β ⊓ Qv l ⊓ Qv l0)) ⊓ Qv β := le_inf le_sup_right hQ0Q
  have hle2 := Subgroup.relIndex_le_of_le_left (L := Qv β) hQ0B (relIndex_ne_zero' _ _)
  have hle3 : (Qv β ⊓ Qv l ⊓ Qv l0).relIndex (Qv β) ≤ 4 := by
    refine Subgroup.relIndex_inf_le.trans ?_
    have e1 := relIndex_Qv hS hcfg.vβ hcfg.l_nbr
    have e2 := relIndex_Qv hS hcfg.vβ hcfg.l0_nbr
    rw [inf_comm, Subgroup.inf_relIndex_right] at e2
    rw [e1, e2]
  omega

end S35.B5

end F53.Stellmacher

end CFSG.Quasithin
