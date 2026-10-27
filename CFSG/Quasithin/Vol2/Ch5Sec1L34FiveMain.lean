module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Inputs518D5
public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveL2
public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveSpor
public import CFSG.Quasithin.Vol2.Ch5Sec1L34FiveA7
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Inputs518F

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped Pointwise

namespace FiveNorm

@[expose] def FiveRigidLie : Prop :=
  ∀ (X : Type) [Group X] [Finite X],
    (IsPSL 3 2 2 X ∨ IsSL3 4 X ∨ IsPSp4 2 2 X ∨ IsG2 2 2 X ∨ Is3D4 2 2 X) →
    FiveRigid (X ⧸ Subgroup.center X)

@[expose] def FiveRigidQFive : Prop :=
  ∀ (X : Type) [Group X] [Finite X],
    ((∃ s : Bool, IsPSLEps3 s 5 1 X ∨ IsSLEps3 s 5 X) ∨ IsPSL 3 5 1 X ∨ IsSL3 5 X) →
    FiveRigid (X ⧸ Subgroup.center X)

@[expose] def FiveRigidJanko : Prop :=
  FiveRigid (NativeSporadic.Carrier .J1) ∧ FiveRigid (NativeSporadic.Carrier .J2) ∧
    FiveRigid (NativeSporadic.Carrier .J4)

@[expose] def A314FiveNormNQ : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], SQTKHyp Y → ∀ T B L D : Subgroup Y,
    IsSylowTwoOf T ⊤ → B ∈ lFamily T → IsAlt 5 (ModO2 B) → L ∈ cComp ⊤ → B < L →
    ((IsSL2 5 (↥B ⧸ CFSG.oddCore ↥B) ∧ L = B ⊔ oddCoreSub L) ∨
      (IsSL2 5 (↥B ⧸ CFSG.oddCore ↥B) ∧ ∃ p : ℕ, p.Prime ∧ p ^ 2 % 5 = 1 ∧
        (p % 8 = 3 ∨ p % 8 = 5) ∧ IsSL2 p (↥L ⧸ CFSG.oddCore ↥L))) →
    Nat.card D = 5 → D ≤ Subgroup.normalizer (L : Set Y) →
    T ≤ Subgroup.normalizer (L : Set Y) → T ≤ Subgroup.normalizer (B : Set Y) →
    (D : Set Y) * (T : Set Y) = (T : Set Y) * (D : Set Y) →
    (∃ b ∈ B, orderOf b = 3 ∧ b ∈ Subgroup.normalizer ((T ⊓ B : Subgroup Y) : Set Y) ∧
      ∀ d ∈ D, d * b = b * d) →
    D ≤ Subgroup.normalizer (B : Set Y)

end FiveNorm

open FiveNorm in
theorem a314FiveNormFact_of
    (hLie : FiveRigidLie) (hQ5 : FiveRigidQFive) (hJ : FiveRigidJanko)
    (hNQ : A314FiveNormNQ) : A314FiveNormFact := by
  intro Y _ _ hY T B L D hT hB hA5 hL hBL h314 hD hDN hTN hTB hDT hb
  have hBL' : B ≤ L := hBL.le
  have hBperf : ⁅B, B⁆ = B := perfect_of_mem_cComp hB
  have hred : ∀ {P : Type} [Group P], (↥L ⧸ Subgroup.center ↥L ≃* P) → FiveRigid P →
      D ≤ Subgroup.normalizer (B : Set Y) := fun e hP =>
    le_normalizer_of_fiveRigid e hP hT hTN hD hDN hDT hBL' hBperf
  have hspor : ∀ {s : TauCeti.SporadicName}, FiveRigid (NativeSporadic.Carrier s) →
      (CFSG.Quasithin.IsSporadic s ↥L ∨ IsHat ↥L (NativeSporadic.Carrier s)) →
      D ≤ Subgroup.normalizer (B : Set Y) := by
    intro s hP h
    rcases h with h | ⟨-, -, ⟨e⟩⟩
    · obtain ⟨e₀⟩ : Nonempty (↥L ≃* NativeSporadic.Carrier s) := h
      obtain ⟨-, ⟨e⟩⟩ := nonempty_quotCenter_equiv e₀ hP.1
      exact hred e hP
    · exact hred e hP
  rcases h314 with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14
  · exact hred (MulEquiv.refl _) (hLie _ h1.2.2.1)
  · have hP := fiveRigid_alt7
    rcases h2.2.1 with h | ⟨-, -, ⟨e⟩⟩
    · obtain ⟨e₀⟩ : Nonempty (↥L ≃* alternatingGroup (Fin 7)) := h
      obtain ⟨-, ⟨e⟩⟩ := nonempty_quotCenter_equiv e₀ hP.1
      exact hred e hP
    · exact hred e hP
  · obtain ⟨b, hbB, hb3, hbT, hbD⟩ := hb
    rcases h3.2 with h25 | ⟨p, hp, hp5, hp8, hpsl⟩
    · obtain ⟨K, _, _, hK, hZ, ⟨e⟩⟩ := quot_psl2_of_isPSL h25
      exact le_normalizer_of_psl2_25 hK e hZ hT hTN hD hDN hDT hBL' hBperf (hBL' hbB) hb3 hbD
    · obtain ⟨K, _, _, hK, hZ, ⟨e⟩⟩ := quot_psl2_of_isPSL hpsl
      have hTB : IsSylowTwoOf (T ⊓ B) B :=
        A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hB)
          (A4.isSylowTwoOf_mono hT le_sup_right le_top)
      exact le_normalizer_of_psl2_prime hp (by rw [hK, pow_one]) hp5 hp8 e hZ hT hTN hD hDN hDT
        hBL' hBperf h3.1 hTB hbB hb3 hbT hbD
  · exact hred (MulEquiv.refl _) (hQ5 _ (Or.inl h4.2.1))
  · exact hred (MulEquiv.refl _) (hQ5 _ (Or.inr h5.2.1))
  · exact hspor fiveRigid_M22 h6.2.2.2
  · exact hspor fiveRigid_M23 (Or.inl h7.2.2.2)
  · exact hspor hJ.1 (Or.inl h8.2.1)
  · exact hspor hJ.2.1 (Or.inl h9.2.1)
  · exact hspor hJ.2.2 (Or.inl h10.2.2)
  · exact hspor fiveRigid_HS (Or.inl h11.2.1)
  · exact hspor fiveRigid_Ru (Or.inl h12.2.2.1)
  · exact hNQ Y hY T B L D hT hB hA5 hL hBL (Or.inl h13) hD hDN hTN hTB hDT hb
  · exact hNQ Y hY T B L D hT hB hA5 hL hBL (Or.inr h14) hD hDN hTN hTB hDT hb

end CFSG.Quasithin.H13
