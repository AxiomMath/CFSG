module

public import CFSG.Quasithin.H13.L32A767d

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem pCoreOf_hz_le_dK : pCoreOf 2 (hz T V) ≤ dK T V := by
  intro q hq
  have hqH : q ∈ hz T V := pCoreOf_le 2 _ hq
  refine ⟨le_normalizer_oTwoUpper _ hqH, fun k hk => ?_⟩
  have hkH : k ∈ hz T V := oTwoUpper_le _ hk
  have hle : kz T V ⊓ pCoreOf 2 (hz T V) ≤ pCoreOf 2 (kz T V) := by
    refine le_pCoreOf_of_le_normalizer 2 inf_le_left (fun x hx => ?_)
      ((pCoreOf_isPGroup 2 _).to_le inf_le_right)
    exact mem_normalizer_inf_of_mem (Subgroup.le_normalizer hx)
      (le_normalizer_pCoreOf 2 _ (oTwoUpper_le _ hx))
  refine hle (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
  · rw [show q * k * q⁻¹ * k⁻¹ = (q * k * q⁻¹) * k⁻¹ by group]
    exact mul_mem ((Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoUpper _ hqH) k).mp hk)
      (inv_mem hk)
  · rw [show q * k * q⁻¹ * k⁻¹ = q * (k * q⁻¹ * k⁻¹) by group]
    exact mul_mem hq ((Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ hkH) _).mp
      (inv_mem hq))

theorem inf_dK_eq (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63) :
    hz T V ⊓ dK T V = pCoreOf 2 (hz T V) :=
  le_antisymm (inf_dK_le h hMod h63) (le_inf (pCoreOf_le 2 _) pCoreOf_hz_le_dK)

theorem pCoreOf_hz_le_R1_of (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63) :
    pCoreOf 2 (hz T V) ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) := by
  have hTH := T_le_hz h h63
  have hL1H : L₁Of L (fsuV1 T V) ≤ hz T V := (l1_le_kz h hMod).trans (oTwoUpper_le _)
  exact le_pCoreOf_of_le_normalizer 2
    ((EscapingLocal.pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_of_le h hTH)).trans le_sup_right)
    ((sup_le hL1H hTH).trans (le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)

theorem isSylowTwoOf_R1_dK (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63) :
    IsSylowTwoOf (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))
      (dK T V ⊔ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) := by
  set R := pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) with hR
  set D := dK T V with hD
  have hTH := T_le_hz h h63
  have hHK : hz T V ≤ mK T V := le_normalizer_oTwoUpper _
  have hRT : R ≤ T :=
    EscapingLocal.pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_of_le h le_sup_right)
  have hTD : T ≤ Subgroup.normalizer (D : Set G) := (hTH.trans hHK).trans mK_le_normalizer_dK
  have hQR := pCoreOf_hz_le_R1_of h hMod h63
  have hDT : T ⊓ D ≤ R ⊓ D := fun x hx =>
    ⟨hQR (inf_dK_le h hMod h63 ⟨hTH hx.1, hx.2⟩), hx.2⟩
  have hRD : R ⊓ D = T ⊓ D := le_antisymm (inf_le_inf hRT le_rfl) hDT
  refine ⟨le_sup_right, pCoreOf_isPGroup 2 _, ?_⟩
  have e1 := L32NSet14.card_sup_mul_card_inf (hRT.trans hTD)
  have e2 := L32NSet14.card_sup_mul_card_inf hTD
  have i1 := Subgroup.relIndex_mul_card R (R ⊔ D)
  have i2 := Subgroup.relIndex_mul_card T (T ⊔ D)
  rw [inf_eq_left.mpr le_sup_left] at i1 i2
  rw [hRD] at e1
  have hpos : 0 < Nat.card ↥(T ⊓ D) := Nat.card_pos
  have hRpos : 0 < Nat.card ↥R := Nat.card_pos
  have hTpos : 0 < Nat.card ↥T := Nat.card_pos
  have key : R.relIndex (R ⊔ D) = T.relIndex (T ⊔ D) := by
    have a1 : R.relIndex (R ⊔ D) * Nat.card ↥(T ⊓ D) * Nat.card ↥R =
        Nat.card ↥D * Nat.card ↥R := by
      rw [mul_assoc, mul_comm (Nat.card ↥(T ⊓ D)), ← mul_assoc, i1, e1, mul_comm]
    have a2 : T.relIndex (T ⊔ D) * Nat.card ↥(T ⊓ D) * Nat.card ↥T =
        Nat.card ↥D * Nat.card ↥T := by
      rw [mul_assoc, mul_comm (Nat.card ↥(T ⊓ D)), ← mul_assoc, i2, e2, mul_comm]
    have b1 := Nat.eq_of_mul_eq_mul_right hRpos a1
    have b2 := Nat.eq_of_mul_eq_mul_right hTpos a2
    exact Nat.eq_of_mul_eq_mul_right hpos (b1.trans b2.symm)
  have hodd := (isSylowTwoOf_of_le h (le_sup_left : T ≤ T ⊔ D)).2.2
  show ¬ 2 ∣ R.relIndex (D ⊔ R)
  rw [sup_comm, key]
  exact hodd

end CFSG.Quasithin.H13.L32A
