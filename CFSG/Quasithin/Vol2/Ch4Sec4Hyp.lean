module

public import CFSG.Quasithin.H13.StatementsL4

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative Pointwise

structure Hyp4_4_1Core (G : Type) [Group G] [Finite G] (T M L B Tp : Subgroup G) : Prop where
  simple : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  qtke : QuasithinUnique.quasithinIsQTKECat G
  sylow : quasithinIsSylowTwo T
  maxTwoLocal : quasithinIsMaxTwoLocal M
  T_le : T ≤ M
  maximal : quasithinIsMaximalLocal T L
  faithful : quasithinIsFaithfulLocal T L
  L_le : L ≤ M
  quasisimple : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)
  B_le : B ≤ M
  B_ne_bot : B ≠ ⊥
  B_comm : IsMulCommutative ↥B
  B_odd : Odd (Nat.card B)
  commutator_le : ⁅conjClosure L T, B⁆ ≤ pCoreOf 2 (conjClosure L T)
  Tp_le : Tp ≤ T
  mul_comm_Tp : (B : Set G) * (Tp : Set G) = (Tp : Set G) * (B : Set G)

structure Hyp4_4_1Two (G : Type) [Group G] [Finite G] (T M L B Tp : Subgroup G) : Prop
    extends Hyp4_4_1Core G T M L B Tp where
  mul_Tp : (L : Set G) * (T : Set G) = (L : Set G) * (Tp : Set G)

structure Hyp4_4_1TwoOrbit (G : Type) [Group G] [Finite G] (T M L B Tp : Subgroup G) : Prop
    extends Hyp4_4_1Core G T M L B Tp where
  orbit_Tp : ∀ t ∈ T, ∃ s ∈ Tp, CFSG.conjugate L t = CFSG.conjugate L s

structure Hyp4_4_1Three (G : Type) [Group G] (T L B VB : Subgroup G) : Prop where
  VB_le : VB ≤ quasithinOmegaOneCenter (pCoreOf 2 (conjClosure L T ⊔ T))
  VB_normalized : conjClosure L T ⊔ T ≤ Subgroup.normalizer (VB : Set G)
  VB_eq : VB = ⁅VB, conjClosure L T⁆
  VB_ne_bot : VB ≠ ⊥
  VB_centralizes : ⁅VB, B⁆ = ⊥

structure Hyp4_4_1 (G : Type) [Group G] [Finite G] (T M L B Tp VB : Subgroup G) : Prop
    extends Hyp4_4_1Two G T M L B Tp, Hyp4_4_1Three G T L B VB

structure Hyp4_4_1Orbit (G : Type) [Group G] [Finite G] (T M L B Tp VB : Subgroup G) : Prop
    extends Hyp4_4_1TwoOrbit G T M L B Tp, Hyp4_4_1Three G T L B VB

theorem conjugate_eq_self_of_mem {G : Type} [Group G] {L : Subgroup G} {l : G} (hl : l ∈ L) :
    CFSG.conjugate L l = L :=
  Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer (L.inv_mem hl))

theorem conjugate_mul {G : Type} [Group G] (L : Subgroup G) (g h : G) :
    CFSG.conjugate L (g * h) = CFSG.conjugate (CFSG.conjugate L g) h := by
  unfold CFSG.conjugate
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem orbit_of_mul_eq {G : Type} [Group G] {L T Tp : Subgroup G}
    (h : (L : Set G) * (T : Set G) = (L : Set G) * (Tp : Set G)) :
    ∀ t ∈ T, ∃ s ∈ Tp, CFSG.conjugate L t = CFSG.conjugate L s := by
  intro t ht
  have h0 : t ∈ (L : Set G) * (T : Set G) := ⟨1, L.one_mem, t, ht, one_mul t⟩
  have h1 : t ∈ (L : Set G) * (Tp : Set G) := h ▸ h0
  obtain ⟨l, hl, s, hs, rfl⟩ := h1
  exact ⟨s, hs, by rw [conjugate_mul, conjugate_eq_self_of_mem hl]⟩

theorem Hyp4_4_1Two.toOrbit {G : Type} [Group G] [Finite G] {T M L B Tp : Subgroup G}
    (h : Hyp4_4_1Two G T M L B Tp) : Hyp4_4_1TwoOrbit G T M L B Tp :=
  { h.toHyp4_4_1Core with orbit_Tp := orbit_of_mul_eq h.mul_Tp }

theorem Hyp4_4_1.toOrbit {G : Type} [Group G] [Finite G] {T M L B Tp VB : Subgroup G}
    (h : Hyp4_4_1 G T M L B Tp VB) : Hyp4_4_1Orbit G T M L B Tp VB :=
  { h.toHyp4_4_1Two.toOrbit, h.toHyp4_4_1Three with }

@[expose] def Concl4_4_3 (G : Type) [Group G] (T M L B VB : Subgroup G) : Prop :=
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
                alternatingGroup (Fin 6))) →
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

@[expose] def Stmt4_4_3Orbit : Prop :=
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
      Concl4_4_3 G T M L B VB

theorem stmt4_4_3_iff : Stmt4_4_3 ↔
    ∀ (G : Type) [Group G] [Finite G] (T M L B Tp VB : Subgroup G),
      Hyp4_4_1 G T M L B Tp VB → Concl4_4_3 G T M L B VB := by
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

theorem stmt4_4_3Orbit_iff : Stmt4_4_3Orbit ↔
    ∀ (G : Type) [Group G] [Finite G] (T M L B Tp VB : Subgroup G),
      Hyp4_4_1Orbit G T M L B Tp VB → Concl4_4_3 G T M L B VB := by
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

theorem stmt4_4_3_of_orbit (h : Stmt4_4_3Orbit) : Stmt4_4_3 :=
  stmt4_4_3_iff.2 fun G _ _ T M L B Tp VB hH => stmt4_4_3Orbit_iff.1 h G T M L B Tp VB hH.toOrbit

end CFSG.Quasithin.H13
