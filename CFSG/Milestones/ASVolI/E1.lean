module

public import CFSG.Quasithin.Background.A3StructureDefs
import CFSG.Quasithin.Background.RonanE114D4LowBound
import CFSG.Quasithin.Background.RonanE111Core
import CFSG.Quasithin.Background.RonanE114G2F4
import CFSG.Quasithin.Background.RonanE114C5Clauses
import CFSG.Quasithin.Background.RonanE114J4Main
import CFSG.Quasithin.Background.RonanE114SevenL35Main
public import CFSG.LieType.SteinbergBRMulEquivCores
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve

public section

namespace CFSG.ASVolI

namespace ChE

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1 CFSG.Quasithin.A1b
open scoped commutatorElement

@[expose] def ETwoAltOne (Q : Type) [Group Q] (S B : Subgroup Q) : Prop :=
  IsTwoClosed (CFSG.solvableRadical Q) ∧ CFSG.Open.pCore 2 (Q ⧸ oInftyE Q) = ⊤ ∧
    twoResidual (⊤ : Subgroup Q) = perfectCore (⊤ : Subgroup Q) ∧
    ∃ L : Subgroup (Q ⧸ CFSG.solvableRadical Q), CFSG.IsComponent L ∧
      CFSG.layer (Q ⧸ CFSG.solvableRadical Q) =
        ⨆ t ∈ (tauOf ⊤ S B).map (QuotientGroup.mk' (CFSG.solvableRadical Q)), A1b.conjSub t L ∧
      L = ⁅L, barRad Q B⁆

@[expose] def innAutInduced {G : Type} [Group G] (T M N : Subgroup G)
    [(N.subgroupOf M).Normal] : Subgroup (MulAut (↥M ⧸ N.subgroupOf M)) :=
  Subgroup.closure
    {α | ∃ g ∈ M ⊔ (T ⊓ Subgroup.normalizer (M : Set G) ⊓ Subgroup.normalizer (N : Set G)),
      ∀ m : ↥M, ∃ m' : ↥M, (m' : G) = g * (m : G) * g⁻¹ ∧
        α (QuotientGroup.mk m) = QuotientGroup.mk m'}

end ChE

open ChE CFSG.Open CFSG.Quasithin CFSG.Quasithin.E1 CFSG.Quasithin.A1b
open scoped commutatorElement

@[expose] def E_1_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T A K : Subgroup G),
    IsSylowIn 2 T ⊤ → IsElemAbelian 2 A → A ≤ T → IsEAny ⊤ T A K →
      twoResidual K ≤ ⨆ k ∈ K, A1b.conjSub k A

set_option linter.unusedVariables false in
theorem as_E_1_4 : E_1_4 := by
  intro G _ _ T A K hT hAb hAT hK
  refine (E1.twoResidual_le_conjClosure hK).trans ?_
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨h, hh, a, ha, rfl⟩
  have h1 : A1b.conjSub h A ≤ ⨆ k ∈ K, A1b.conjSub k A :=
    le_iSup₂ (f := fun k (_ : k ∈ K) => A1b.conjSub k A) h hh
  exact h1 (A1b.mem_conjSub_iff.2 (by rw [show h⁻¹ * (h * a * h⁻¹) * h = a by group]; exact ha))

@[expose] def E_1_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T A K : Subgroup G),
    IsSylowIn 2 T ⊤ → IsElemAbelian 2 A → A ≤ T → IsEAny ⊤ T A K →
      IsE 1 ⊤ T A K ∨
        (tauOf ⊤ T A ≤ T ⊓ K ∧ IsSylowIn 2 (T ⊓ K) K ∧
          ETwoAltOne ↥K ((T ⊓ K).subgroupOf K) (A.subgroupOf K))

theorem as_E_1_5 : E_1_5 := by
  intro G _ _ T A K hT hAb hAT hK
  obtain ⟨i, hKG, hτ, hS, hcase⟩ := hK
  rcases hcase with ⟨hE1, -⟩ | ⟨hE2, -⟩
  · have hcard : Nat.card (E1.barO2 ↥K (A.subgroupOf K)) = 2 := by
      obtain ⟨_, _, _, _, _, _, h⟩ := hE1
      exact h
    refine Or.inl ⟨hKG, hτ, hS, Or.inl ⟨hE1, ?_⟩⟩
    rw [hcard]
    norm_num
  · obtain ⟨hc, hp, ht, L, hLc, hLl, hLdisj⟩ := hE2
    rcases hLdisj with hLcomm | ⟨hLN, hcard2⟩
    · exact Or.inr ⟨hτ, hS, ⟨hc, hp, ht, L, hLc, hLl, hLcomm⟩⟩
    · refine Or.inl ⟨hKG, hτ, hS, Or.inr ⟨⟨hc, hp, ht, L, hLc, hLl, Or.inr ⟨hLN, hcard2⟩⟩, ?_⟩⟩
      rw [hcard2]
      norm_num

@[expose] def E_1_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], nParam (⊤ : Subgroup G) ≤ (twoRank G : ℕ∞)

theorem as_E_1_7 : E_1_7 := by
  exact fun G _ _ => CFSG.Quasithin.RonanE17.nParam_top_le_twoRank G

@[expose] def E_1_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T A H K : Subgroup G) (i : ℕ),
    IsSylowIn 2 T ⊤ → IsElemAbelian 2 A → A ≤ T →
    tauOf ⊤ T A ≤ T ⊓ H → IsSylowIn 2 (T ⊓ H) H → IsE i H (T ⊓ H) A K →
      (A ⊔ pCoreOf 2 (⊤ : Subgroup G) ≤ tauOf ⊤ T A ∧ tauOf ⊤ T A ≤ tauOf H (T ⊓ H) A ∧
        tauOf H (T ⊓ H) A ≤ tauOf K (T ⊓ K) A ∧ tauOf K (T ⊓ K) A ≤ K) ∧
      IsE i ⊤ T A K ∧
      (∀ (Y : Subgroup G) [Y.Normal], IsSylowIn 2 (pCoreOf 2 (⊤ : Subgroup G)) Y →
        T ⊓ (Subgroup.centralizer ((A.map (QuotientGroup.mk' Y) : Subgroup (G ⧸ Y)) :
          Set (G ⧸ Y))).comap (QuotientGroup.mk' Y) = tauOf ⊤ T A ∧
        (tauOf ⊤ T A).map (QuotientGroup.mk' Y) ≤
          tauOf (⊤ : Subgroup (G ⧸ Y)) (T.map (QuotientGroup.mk' Y)) (A.map (QuotientGroup.mk' Y)))

set_option linter.unusedVariables false in
theorem as_E_1_8 : E_1_8 := fun G _ _ T A H K i hT hAb hAT hτ hS hK =>
  ⟨E1.eight_one hT hAT hAb le_top hτ hS hK, E1.eight_two hT hAT hAb le_top hτ hS hK,
    fun Y _ hY => E1.eight_three hT hAT hY⟩

@[expose] def E_1_10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T X Y K A : Subgroup G) [X.Normal] [Y.Normal],
    IsSylowIn 2 T ⊤ → Y ≤ X → K ∈ sFamily T X Y → IsElemAbelian 2 A → A ≤ T →
      (K = (K ⊓ X) ⊔ T ∧
        (K ⊓ X).map (QuotientGroup.mk' Y) = X.map (QuotientGroup.mk' Y) ∧
        Nonempty (↥(K ⊓ X) ⧸ Y.subgroupOf (K ⊓ X) ≃* ↥((K ⊓ X).map (QuotientGroup.mk' Y)))) ∧
      IsTwoClosed (preO2 K Y) ∧
      (∀ p : ℕ, p.Prime → p ≠ 2 →
        oTwoP ↥((K ⊓ X).map (QuotientGroup.mk' Y)) p = ⊤ → oTwoPTwo ↥K p = ⊤) ∧
      (oInftyE ↥((K ⊓ X).map (QuotientGroup.mk' Y)) = ⊤ →
        IsTwoClosed (CFSG.solvableRadical ↥(K.map (QuotientGroup.mk' Y))) →
        twoResidual (⊤ : Subgroup ↥(K.map (QuotientGroup.mk' Y))) =
          perfectCore (⊤ : Subgroup ↥(K.map (QuotientGroup.mk' Y))) →
        CFSG.Open.pCore 2 (↥K ⧸ oInftyE ↥K) = ⊤ ∧ IsTwoClosed (CFSG.solvableRadical ↥K) ∧
          twoResidual (⊤ : Subgroup ↥K) = perfectCore (⊤ : Subgroup ↥K)) ∧
      (CFSG.Quasithin.E1.IsChiefFactor X Y →
        ∃ (L : Type) (_ : Group L), IsSimpleGroup L ∧ IsCompositionFactor G L ∧
          ∃ n : ℕ, Nonempty (↥((K ⊓ X).map (QuotientGroup.mk' Y)) ≃* (Fin n → L))) ∧
      (∀ p : ℕ, p.Prime → p ≠ 2 → IsPGroup p ↥(X.map (QuotientGroup.mk' Y)) →
        ⁅X.map (QuotientGroup.mk' Y), A.map (QuotientGroup.mk' Y)⁆ = X.map (QuotientGroup.mk' Y) →
        X ≤ (⨆ K' ∈ {K' : Subgroup G | IsE 1 ⊤ T A K'}, K') ⊔ Y) ∧
      (∀ (i : ℕ) (I : Subgroup (G ⧸ Y)),
        IsE i ⊤ (T.map (QuotientGroup.mk' Y)) (A.map (QuotientGroup.mk' Y)) I →
        ∃ J : Subgroup G, IsE i ⊤ T A J ∧
          twoResidual I = (twoResidual J).map (QuotientGroup.mk' Y)) ∧
      (twoResidual (⊤ : Subgroup G) = perfectCore (⊤ : Subgroup G) →
        perfectCore (⊤ : Subgroup G) = ⁅perfectCore (⊤ : Subgroup G), A⁆ →
        IsTwoClosed Y → ∀ J : Subgroup G, T ≤ J → J ⊔ Y = ⊤ →
        J ⊔ (⨆ K' ∈ {K' : Subgroup G | IsE 1 ⊤ T A K'}, K') = ⊤)

set_option linter.unusedVariables false in
theorem as_E_1_10 : E_1_10 := by
  intro G _ _ T X Y K A _ _ hT hYX hK hAb hAT
  have hTX : T ≤ Subgroup.normalizer (X : Set G) := fun t _ => by
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]; exact Subgroup.mem_top t
  exact ⟨E1.ten_one hTX hYX hK, E1.ten_two hT le_top hK,
    fun p hp hp2 h => E1.ten_three hTX hYX le_top hT hK hp hp2 h,
    fun h1 h2 h3 => E1.ten_four hT hYX hK h1 h2 h3,
    fun hXY => E1.ten_five hXY hK,
    fun p hp hp2 hXp hXA => E1.ten_six hp hp2 hT hAT hAb hXp hXA,
    fun i I hI => E1.ten_seven hT hAT hAb hI,
    fun h1 h2 hY J hTJ hJY => E1.ten_eight hT hAT hAb h1 h2 hY hTJ hJY⟩

@[expose] def E_1_11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G) (n : ℕ), 0 < n → IsSylowIn 2 T ⊤ →
    (∀ (M N : Subgroup G) [(N.subgroupOf M).Normal], N ≤ M → N.IsSubnormal → M.IsSubnormal →
      IsSimpleGroup (↥M ⧸ N.subgroupOf M) → nParam (innAutInduced T M N) ≤ (n : ℕ∞)) →
    nParam (⊤ : Subgroup G) ≤ (n : ℕ∞)

theorem as_E_1_11 : E_1_11 := by
  intro G _ _ T n hn hT hH
  have hHT : CFSG.Quasithin.RonanE111.HypT n G T := by
    intro M N _ hNM hMsub _ hsimple _
    exact hH M N hNM (Subgroup.IsSubnormal.trans hNM (Subgroup.Normal.isSubnormal ‹_›) hMsub)
      hMsub hsimple
  exact CFSG.Quasithin.RonanE111.nParam_le_of_hypT CFSG.Quasithin.RonanE111.e111CoreT hn hT hHT

@[expose] def E_1_12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G) (Δ : Set (Subgroup G)) (n : ℕ),
    IsSylowIn 2 T ⊤ → (⨆ H ∈ Δ, H) = ⊤ → (∀ H ∈ Δ, T ≤ H ∧ nParam H ≤ (n : ℕ∞)) →
      nParam (⊤ : Subgroup G) ≤ (n : ℕ∞)

set_option linter.unusedVariables false in
theorem as_E_1_12 : E_1_12 := fun G _ _ T Δ n hT hΔ hD =>
  E1.nParam_le_of_generated (H := ⊤) hT hΔ (fun D hD' => (hD D hD').1) (fun D hD' => (hD D hD').2)

@[expose] def E_1_13 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Group.IsSolvable G → nParam (⊤ : Subgroup G) ≤ 1

set_option linter.unusedVariables false in
theorem as_E_1_13 : E_1_13 := fun G _ _ hG => E1.solvable_nParam_le_one (H := ⊤)
  (Group.isSolvable_of_surjective (f := (Subgroup.topEquiv (G := G)).symm.toMonoidHom)
    (Subgroup.topEquiv (G := G)).symm.surjective)

@[expose] def E_1_14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), SQTKGroup G →
    IsSimpleGroup ↥(CFSG.generalizedFitting G) → IsSylowIn 2 T ⊤ →
    CFSG.generalizedFitting G ⊔ T = ⊤ →
      ((∀ n : ℕ, 1 ≤ n →
        (IsPSL 2 2 n ↥(CFSG.generalizedFitting G) ∨ IsSz n ↥(CFSG.generalizedFitting G) ∨
          IsPSU 3 2 n ↥(CFSG.generalizedFitting G) ∨ IsPSL 3 2 n ↥(CFSG.generalizedFitting G) ∨
          (IsPSp4 2 n ↥(CFSG.generalizedFitting G) ∨
            (n = 1 ∧ IsAlt 6 ↥(CFSG.generalizedFitting G))) ∨
          (Is2F4 n ↥(CFSG.generalizedFitting G) ∨
            (n = 1 ∧ IsTits ↥(CFSG.generalizedFitting G))) ∨
          (IsG2 2 n ↥(CFSG.generalizedFitting G) ∨
            (n = 1 ∧ IsPSU 3 3 1 ↥(CFSG.generalizedFitting G)))) →
          nParam (⊤ : Subgroup G) = (n : ℕ∞)) ∧
      (IsPSL 4 2 1 ↥(CFSG.generalizedFitting G) ∨ IsPSL 5 2 1 ↥(CFSG.generalizedFitting G) →
        nParam (⊤ : Subgroup G) = 1)) ∧
      (∀ n : ℕ, 1 ≤ n → Is3D4 2 n ↥(CFSG.generalizedFitting G) →
        nParam (⊤ : Subgroup G) = ((3 * n : ℕ) : ℕ∞)) ∧
      (IsAlt 7 ↥(CFSG.generalizedFitting G) → nParam (⊤ : Subgroup G) = 1) ∧
      (IsSporadic .M11 ↥(CFSG.generalizedFitting G) ∨ IsSporadic .M12 ↥(CFSG.generalizedFitting G) ∨
          IsSporadic .M24 ↥(CFSG.generalizedFitting G) ∨
          IsSporadic .He ↥(CFSG.generalizedFitting G) → nParam (⊤ : Subgroup G) = 1) ∧
      (IsSporadic .J1 ↥(CFSG.generalizedFitting G) ∨ IsSporadic .J2 ↥(CFSG.generalizedFitting G) ∨
          IsSporadic .J4 ↥(CFSG.generalizedFitting G) ∨
          IsSporadic .M22 ↥(CFSG.generalizedFitting G) ∨
          IsSporadic .M23 ↥(CFSG.generalizedFitting G) ∨
          IsSporadic .HS ↥(CFSG.generalizedFitting G) ∨
          IsSporadic .Ru ↥(CFSG.generalizedFitting G) → nParam (⊤ : Subgroup G) ≤ 2) ∧
      (∀ p e : ℕ, p.Prime → p ≠ 2 → 5 < p ^ e → IsPSL 2 p e ↥(CFSG.generalizedFitting G) →
        nParam (⊤ : Subgroup G) = 1) ∧
      (∀ (s : Bool) (p : ℕ), p.Prime → p ≠ 2 → IsPSLEps3 s p 1 ↥(CFSG.generalizedFitting G) →
        nParam (⊤ : Subgroup G) = 1)

@[expose] def E_1_14_seven : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), SQTKGroup G →
    IsSimpleGroup ↥(CFSG.generalizedFitting G) → IsSylowIn 2 T ⊤ →
    CFSG.generalizedFitting G ⊔ T = ⊤ →
      ∀ (s : Bool) (p : ℕ), p.Prime → p ≠ 2 → IsPSLEps3 s p 1 ↥(CFSG.generalizedFitting G) →
        nParam (⊤ : Subgroup G) = 1

section E114

theorem e_1_14_of_seven (h7 : E_1_14_seven) : E_1_14 := by
  intro G _ _ T hSQ hFs hT hFT
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, h7 G T hSQ hFs hT hFT⟩
  · intro n hn hL
    rcases hL with h | h | h | h | (h | ⟨rfl, h⟩) | (h | ⟨rfl, h⟩) | (h | ⟨rfl, h⟩)
    · exact RonanE114.clause_one_typeLie G T hSQ hFs hT hFT n hn (Or.inl h)
    · exact RonanE114.clause_one_typeLie G T hSQ hFs hT hFT n hn (Or.inr (Or.inl h))
    · exact RonanE114.clause_one_typeLie G T hSQ hFs hT hFT n hn (Or.inr (Or.inr (Or.inl h)))
    · exact RonanE114.clause_one_typeLie G T hSQ hFs hT hFT n hn
        (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact RonanE114.clause_one_typeLie G T hSQ hFs hT hFT n hn
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact RonanE114.clause_one_typeLie G T hSQ hFs hT hFT 1 hn
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, h⟩)))))
    · exact RonanE114.clause_one_2F4 G T hSQ hFs hT hFT n hn h
    · exact_mod_cast RonanE114.clause_one_tits G T hSQ hFs hT hFT h
    · exact RonanE114.clause_one_G2 G T hSQ hFs hT hFT n hn h
    · exact_mod_cast RonanE114.clause_one_u33 G T hSQ hFs hT hFT h
  · rintro (h | h)
    · exact RonanE114.clause_one_l42 G T hSQ hFs hT hFT h
    · exact RonanE114.clause_one_l52 G T hSQ hFs hT hFT h
  · exact CFSG.Quasithin.RonanE114Low.e_1_14_two_printed_local G T hSQ hFs hT hFT
  · exact RonanE114.clause_three G T hSQ hFs hT hFT
  · rintro (h | h | h | h)
    · exact RonanE114.clause_four_M11 G T hSQ hFs hT hFT h
    · exact RonanE114.clause_four_M12 G T hSQ hFs hT hFT h
    · exact RonanE114.clause_four_M24 G T hSQ hFs hT hFT h
    · exact RonanE114.clause_four_He G T hSQ hFs hT hFT h
  · exact RonanE114.clause_five G T hSQ hFs hT hFT
      (RonanE114.clause_five_J4 G T hSQ hFs hT hFT)
  · exact RonanE114.clause_six G T hSQ hFs hT hFT

end E114

section E114Target

theorem as_E_1_14 : E_1_14 :=
  e_1_14_of_seven fun G _ _ T hSQ hFs hT hFT => RonanE114.clause_seven G T hSQ hFs hT hFT

end E114Target

end CFSG.ASVolI
