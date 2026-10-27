module

public import CFSG.Quasithin.Vol2.Ch4Sec4Hyp

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative Pointwise

@[expose] def Concl4_4_3' (G : Type) [Group G] (T M L B VB : Subgroup G) : Prop :=
  Subgroup.normalizer (B : Set G) ≤ M ∨
    (M ≤ Subgroup.normalizer (L : Set G) ∧
      ((∃ n : ℕ, 2 ≤ n ∧ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 2 n) ∨
        LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1 ∨
        LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 4 2 1 ∨
        Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)) ∨
        Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 7)) ∨
        (Group.IsPerfect (↥L ⧸ CFSG.pCore 2 ↥L) ∧
          Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 3 ∧
          Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
            alternatingGroup (Fin 6))) ∨
        LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) ∧
      (((∃ _ : IsMulCommutative ↥VB, IsFFModule (V := ↥VB) (autOn (L ⊔ T) VB)) ∧
          (LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1 → IsNaturalSumUnder 3 L VB) ∧
          (LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 4 2 1 →
            IsNaturalSumUnder 4 L VB ∨
              ∃ _ : IsMulCommutative ↥VB, SLExteriorTwo (V := ↥VB) (autOn L VB) ⊤ ⊥ 4) ∧
          ((Group.IsPerfect (↥L ⧸ CFSG.pCore 2 ↥L) ∧
              Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 3 ∧
              Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
                alternatingGroup (Fin 6))) → Nat.card VB = 2 ^ 6 →
            ∀ z ∈ VB ⊓ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G), orderOf z = 2 →
              ¬ VB ≤ pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) ∧
          (LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 → Nat.card VB = 2 ^ 6 →
            ∃ V₃ : Subgroup G, V₃ ≤ VB ∧ Nat.card V₃ = 2 ^ 3 ∧
              T ⊓ L ≤ Subgroup.normalizer (V₃ : Set G) ∧
                ¬ Subgroup.centralizer (V₃ : Set G) ≤ M)) ∨
        (∃ m : ℕ, 1 ≤ m ∧ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 2 (2 * m) ∧
          ∃ _ : IsMulCommutative ↥VB, BinaryOrthogonalFour (V := ↥VB) (autOn L VB) ⊤ ⊥ m) ∨
        (LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1 ∧
          ∃ _ : IsMulCommutative ↥VB, FanoCoreModule (V := ↥VB) (autOn L VB) ⊤ ⊥)))

namespace Concl4_4_3

theorem toPrime {G : Type} [Group G] {T M L B VB : Subgroup G}
    (h : Concl4_4_3 G T M L B VB) : Concl4_4_3' G T M L B VB := by
  rcases h with h | ⟨hML, hlist, hbig⟩
  · exact Or.inl h
  · refine Or.inr ⟨hML, hlist, ?_⟩
    rcases hbig with ⟨hFF, h3, h4, hA6, hU3⟩ | hbin | hfano
    · exact Or.inl ⟨hFF, h3, h4, fun h3A _ => hA6 h3A, hU3⟩
    · exact Or.inr (Or.inl hbin)
    · exact Or.inr (Or.inr hfano)

end Concl4_4_3

@[expose] def Stmt4_4_3' : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L B Tp VB : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → quasithinIsMaxTwoLocal M → T ≤ M →
    quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L → L ≤ M →
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) →
    B ≤ M → B ≠ ⊥ → IsMulCommutative ↥B → Odd (Nat.card B) →
    ⁅conjClosure L T, B⁆ ≤ pCoreOf 2 (conjClosure L T) →
    Tp ≤ T → (B : Set G) * (Tp : Set G) = (Tp : Set G) * (B : Set G) →
    (L : Set G) * (T : Set G) = (L : Set G) * (Tp : Set G) →
    VB ≤ quasithinOmegaOneCenter (pCoreOf 2 (conjClosure L T ⊔ T)) →
    conjClosure L T ⊔ T ≤ Subgroup.normalizer (VB : Set G) →
    VB = ⁅VB, conjClosure L T⁆ → VB ≠ ⊥ → ⁅VB, B⁆ = ⊥ →
      Concl4_4_3' G T M L B VB

@[expose] def Stmt4_4_3Orbit' : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L B Tp VB : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → quasithinIsMaxTwoLocal M → T ≤ M →
    quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L → L ≤ M →
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) →
    B ≤ M → B ≠ ⊥ → IsMulCommutative ↥B → Odd (Nat.card B) →
    ⁅conjClosure L T, B⁆ ≤ pCoreOf 2 (conjClosure L T) →
    Tp ≤ T → (B : Set G) * (Tp : Set G) = (Tp : Set G) * (B : Set G) →
    (∀ t ∈ T, ∃ s ∈ Tp, CFSG.conjugate L t = CFSG.conjugate L s) →
    VB ≤ quasithinOmegaOneCenter (pCoreOf 2 (conjClosure L T ⊔ T)) →
    conjClosure L T ⊔ T ≤ Subgroup.normalizer (VB : Set G) →
    VB = ⁅VB, conjClosure L T⁆ → VB ≠ ⊥ → ⁅VB, B⁆ = ⊥ →
      Concl4_4_3' G T M L B VB

theorem stmt4_4_3_iff' : Stmt4_4_3' ↔
    ∀ (G : Type) [Group G] [Finite G] (T M L B Tp VB : Subgroup G),
      Hyp4_4_1 G T M L B Tp VB → Concl4_4_3' G T M L B VB := by
  constructor
  · intro h G _ _ T M L B Tp VB hH
    exact h G T M L B Tp VB hH.simple hH.nonabelian hH.qtke hH.sylow hH.maxTwoLocal hH.T_le
      hH.maximal hH.faithful hH.L_le hH.quasisimple hH.B_le hH.B_ne_bot hH.B_comm hH.B_odd
      hH.commutator_le hH.Tp_le hH.mul_comm_Tp hH.mul_Tp hH.VB_le hH.VB_normalized hH.VB_eq
      hH.VB_ne_bot hH.VB_centralizes
  · intro h G _ _ T M L B Tp VB hs hnab hK hT hM hTM hL hLf hLM hq hBM hB1 hBc hBo hcomm hTp
      hBT hLT hVB hVBn hVBe hVB1 hVBc
    exact h G T M L B Tp VB ⟨⟨⟨hs, hnab, hK, hT, hM, hTM, hL, hLf, hLM, hq, hBM, hB1, hBc, hBo,
      hcomm, hTp, hBT⟩, hLT⟩, ⟨hVB, hVBn, hVBe, hVB1, hVBc⟩⟩

theorem stmt4_4_3Orbit_iff' : Stmt4_4_3Orbit' ↔
    ∀ (G : Type) [Group G] [Finite G] (T M L B Tp VB : Subgroup G),
      Hyp4_4_1Orbit G T M L B Tp VB → Concl4_4_3' G T M L B VB := by
  constructor
  · intro h G _ _ T M L B Tp VB hH
    exact h G T M L B Tp VB hH.simple hH.nonabelian hH.qtke hH.sylow hH.maxTwoLocal hH.T_le
      hH.maximal hH.faithful hH.L_le hH.quasisimple hH.B_le hH.B_ne_bot hH.B_comm hH.B_odd
      hH.commutator_le hH.Tp_le hH.mul_comm_Tp hH.orbit_Tp hH.VB_le hH.VB_normalized hH.VB_eq
      hH.VB_ne_bot hH.VB_centralizes
  · intro h G _ _ T M L B Tp VB hs hnab hK hT hM hTM hL hLf hLM hq hBM hB1 hBc hBo hcomm hTp
      hBT hLT hVB hVBn hVBe hVB1 hVBc
    exact h G T M L B Tp VB ⟨⟨⟨hs, hnab, hK, hT, hM, hTM, hL, hLf, hLM, hq, hBM, hB1, hBc, hBo,
      hcomm, hTp, hBT⟩, hLT⟩, ⟨hVB, hVBn, hVBe, hVB1, hVBc⟩⟩

theorem stmt4_4_3Orbit'_of (h : Stmt4_4_3Orbit) : Stmt4_4_3Orbit' :=
  fun G _ _ T M L B Tp VB hs hnab hK hT hM hTM hL hLf hLM hq hBM hB1 hBc hBo hcomm hTp hBT hLT
    hVB hVBn hVBe hVB1 hVBc =>
    Concl4_4_3.toPrime (h G T M L B Tp VB hs hnab hK hT hM hTM hL hLf hLM hq hBM hB1 hBc hBo
      hcomm hTp hBT hLT hVB hVBn hVBe hVB1 hVBc)

theorem stmt4_4_3_of_orbit' (h : Stmt4_4_3Orbit') : Stmt4_4_3' :=
  stmt4_4_3_iff'.2 fun G _ _ T M L B Tp VB hH => stmt4_4_3Orbit_iff'.1 h G T M L B Tp VB hH.toOrbit

end CFSG.Quasithin.H13

end
