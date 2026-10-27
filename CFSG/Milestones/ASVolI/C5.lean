module

public import CFSG.Quasithin.Vol2.GoldschmidtC58NSProved
public import CFSG.Quasithin.EmptyFaithfulMultiple.TheoremEB51
public import CFSG.Milestones.ASVolI.C1

public section

namespace CFSG.ASVolI.ChC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def rconj (x : G) (K : Subgroup G) : Subgroup G := conjByElt x⁻¹ K

@[expose] def AFam (R : Subgroup G) : Set (Subgroup G) := {A | IsMaxElemAbelian R A}

structure HypC_5_1 (H M₀ TH R : Subgroup G) : Prop where
  sqtk : IsSQTKIn H
  charTwo : CharTwo H
  sylow : IsSylowTwoOf TH H
  unique_max : ∃ N : Subgroup G, IsUniqueMaxOver H TH N
  R_le : R ≤ TH
  TH_le : TH ≤ M₀
  sylow_R : IsSylowTwoOf R (R ⊔ oTwoUpper H)
  R_norm : M₀ ≤ Subgroup.normalizer (R : Set G)

@[expose] def HypC_5_2 (M₀ H R : Subgroup G) : Prop :=
  ∀ R₀ : Subgroup G, R₀ ≤ R → R₀ ≠ ⊥ → ¬ (M₀ ⊔ H ≤ Subgroup.normalizer (R₀ : Set G))

structure BlockConfig (H TH R K₁ : Subgroup G) : Prop where
  chi0 : IsChi0Block H K₁
  comm_J : ⁅K₁, thompsonJ R⁆ = K₁
  prod : oTwoUpper H = ⨆ t ∈ TH, conjByElt t K₁
  card_le : ∀ t ∈ TH, ∀ t' ∈ TH, ∀ t'' ∈ TH, conjByElt t K₁ = conjByElt t' K₁ ∨
    conjByElt t K₁ = conjByElt t'' K₁ ∨ conjByElt t' K₁ = conjByElt t'' K₁
  commute : ∀ t ∈ TH, ∀ t' ∈ TH, conjByElt t K₁ ≠ conjByElt t' K₁ →
    conjByElt t K₁ ≤ Subgroup.centralizer (conjByElt t' K₁ : Set G)

structure SetC53 (H M₀ TH R K₁ : Subgroup G) : Prop where
  hyp1 : HypC_5_1 H M₀ TH R
  hyp2 : HypC_5_2 M₀ H R
  config : BlockConfig H TH R K₁

@[expose] def GoodX (H M₀ K₁ : Subgroup G) (x : G) : Prop :=
  x ∈ M₀ ∧ ¬ rconj x (blockU K₁) ≤ pCoreOf 2 H ∧ ⁅blockU K₁, rconj x (blockU K₁)⁆ ≠ ⊥

structure SetC58 (H M₀ R T K₁ : Subgroup G) (x : G) : Prop where
  simple : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  qtke : quasithinIsQTKECat G
  sylowG : IsSylowTwoOf T ⊤
  hyp1 : HypC_5_1 H M₀ T R
  hyp2 : HypC_5_2 M₀ H R
  config : BlockConfig H T R K₁
  two : ∃ t ∈ T, conjByElt t K₁ ≠ K₁
  index2 : (T ⊓ Subgroup.normalizer (blockU K₁ : Set G)).relIndex T = 2
  good : GoodX H M₀ K₁ x
  norm : x ∈ Subgroup.normalizer ((T ⊓ Subgroup.normalizer (blockU K₁ : Set G) : Subgroup G) : Set G)
  sq : x ^ 2 ∈ T ⊓ Subgroup.normalizer (blockU K₁ : Set G)

end CFSG.ASVolI.ChC

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open scoped Pointwise

@[expose] def C_5_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H M₀ TH R : Subgroup G), HypC_5_1 H M₀ TH R →
    HypC_5_2 M₀ H R → ∃ K₁ : Subgroup G, BlockConfig H TH R K₁


@[expose] def C_5_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H M₀ TH R K₁ : Subgroup G), SetC53 H M₀ TH R K₁ →
    (∀ Ki ∈ conjSubgroupsBy TH K₁,
      baum R ≤ Subgroup.normalizer (Ki : Set G) ∧
      (((∃ n : ℕ, 1 < n ∧ IsLin2Type Ki n) ∨ IsAltType Ki 3) →
        IsSylowTwoOf (baum R ⊓ Ki) Ki ∧
        ((∃ n : ℕ, 1 < n ∧ IsLin2Type Ki n) →
          (baum R : Set G) = ((baum R ⊓ Ki : Subgroup G) : Set G) *
            (pCoreOf 2 (Ki ⊔ baum R) : Set G)) ∧
        (IsAltType Ki 3 →
          Nonempty ((↥(Ki ⊔ baum R) ⧸ CFSG.pCore 2 ↥(Ki ⊔ baum R)) ≃* Equiv.Perm (Fin 3)))) ∧
      (IsAltType Ki 5 →
        (pCoreOf 2 (Ki ⊔ baum R) = blockU Ki ⊔ (baum R ⊓ Subgroup.centralizer (Ki : Set G)) ∧
          blockU Ki ⊓ (baum R ⊓ Subgroup.centralizer (Ki : Set G)) = ⊥ ∧
          blockU Ki ≤ Subgroup.centralizer ((baum R ⊓ Subgroup.centralizer (Ki : Set G) :
            Subgroup G) : Set G)) ∧
        pCoreOf 2 (Ki ⊔ baum R) ≤ baum R ∧
        ∃ φ : ↥(Ki ⊔ baum R) →* Equiv.Perm (Fin 5), Function.Surjective φ ∧
          φ.ker = CFSG.pCore 2 ↥(Ki ⊔ baum R) ∧
          ∃ a b c d : Fin 5, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
            ((baum R).subgroupOf (Ki ⊔ baum R)).map φ =
              Subgroup.closure {Equiv.swap a b, Equiv.swap c d}) ∧
      (blockU Ki ≤ pCoreOf 2 (Ki ⊔ baum R) ∧
        pCoreOf 2 (Ki ⊔ baum R) = baum R ⊓ Subgroup.centralizer (blockU Ki : Set G))) ∧
    R ⊓ Subgroup.centralizer ((⨆ Ki ∈ conjSubgroupsBy TH K₁, blockU Ki : Subgroup G) : Set G) =
      pCoreOf 2 (oTwoUpper H ⊔ R)


@[expose] def C_5_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H M₀ TH R K₁ : Subgroup G), SetC53 H M₀ TH R K₁ →
    ¬ conjClosure (blockU K₁) M₀ ≤ pCoreOf 2 H


@[expose] def C_5_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H M₀ TH R K₁ : Subgroup G) (x : G),
    SetC53 H M₀ TH R K₁ → GoodX H M₀ K₁ x →
    (pCoreOf 2 (K₁ ⊔ baum R) = blockU K₁ ⊔ (baum R ⊓ Subgroup.centralizer (K₁ : Set G)) ∧
      baum R ⊓ Subgroup.centralizer (K₁ : Set G) ≤
        pCoreOf 2 (K₁ ⊔ baum R) ⊓ Subgroup.centralizer (rconj x (blockU K₁) : Set G)) ∧
    ((baum R : Set G) = (rconj x (blockU K₁) : Set G) * (pCoreOf 2 (K₁ ⊔ baum R) : Set G) ∧
      (baum R : Set G) = (pCoreOf 2 (K₁ ⊔ baum R) : Set G) *
        (rconj x (pCoreOf 2 (K₁ ⊔ baum R)) : Set G) ∧
      ⁅blockU K₁, baum R⁆ = ⁅blockU K₁, rconj x (blockU K₁)⁆ ∧
      ⁅blockU K₁, rconj x (blockU K₁)⁆ =
        blockU K₁ ⊓ Subgroup.centralizer (rconj x (blockU K₁) : Set G) ∧
      blockU K₁ ⊓ Subgroup.centralizer (rconj x (blockU K₁) : Set G) =
        blockU K₁ ⊓ rconj x (blockU K₁)) ∧
    rconj x ⁅blockU K₁, baum R⁆ = ⁅blockU K₁, baum R⁆ ∧
    rconj x ((frattini ↥(baum R ⊓ Subgroup.centralizer (K₁ : Set G))).map
        (baum R ⊓ Subgroup.centralizer (K₁ : Set G)).subtype) =
      (frattini ↥(baum R ⊓ Subgroup.centralizer (K₁ : Set G))).map
        (baum R ⊓ Subgroup.centralizer (K₁ : Set G)).subtype ∧
    Even (orderOf x) ∧
    (IsSylowTwoOf TH M₀ →
      (∃ t ∈ TH, conjByElt t K₁ ≠ K₁) ∧
      ∃ x' : G, GoodX H M₀ K₁ x' ∧
        x' ∈ Subgroup.normalizer ((TH ⊓ Subgroup.normalizer (blockU K₁ : Set G) : Subgroup G) :
          Set G) ∧ x' ^ 2 ∈ TH ⊓ Subgroup.normalizer (blockU K₁ : Set G)) ∧
    (TH.relIndex M₀ = 2 →
      (⨆ Ki ∈ conjSubgroupsBy TH K₁, blockU Ki : Subgroup G) = pCoreOf 2 (oTwoUpper H) ∧
      (frattini ↥(baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G))).map
          (baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)).subtype = ⊥ ∧
      (baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊓
          rconj x (baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) = ⊥ ∧
      baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G) =
        R ⊓ Subgroup.centralizer (oTwoUpper H : Set G) ∧
      pCoreOf 2 (oTwoUpper H ⊔ R) =
        (baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊔
          (⨆ Ki ∈ conjSubgroupsBy TH K₁, blockU Ki : Subgroup G) ∧
      IsMaxElemAbelian R ((baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊔
          (⨆ Ki ∈ conjSubgroupsBy TH K₁, blockU Ki : Subgroup G)) ∧
      (baum R : Set G) =
        (((baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊔
          (⨆ Ki ∈ conjSubgroupsBy TH K₁, blockU Ki : Subgroup G) : Subgroup G) : Set G) *
          (rconj x (⨆ Ki ∈ conjSubgroupsBy TH K₁, blockU Ki : Subgroup G) : Set G) ∧
      baum R = thompsonJ R ∧
      ((((∀ t ∈ TH, conjByElt t K₁ = K₁) ∧
          ((∃ n : ℕ, 1 < n ∧ IsLin2Type K₁ n) ∨ IsAltType K₁ 3) ∧
          AFam R = {pCoreOf 2 (K₁ ⊔ baum R), rconj x (pCoreOf 2 (K₁ ⊔ baum R))}) ∨
        ((∀ t ∈ TH, conjByElt t K₁ = K₁) ∧ IsAltType K₁ 5 ∧
          ∃ (A : Subgroup G) (r : G), r ∈ R ⊓ K₁ ∧ r ∉ baum R ∧
            (A ⊓ pCoreOf 2 (K₁ ⊔ baum R)).relIndex A = 2 ∧
            AFam R = {pCoreOf 2 (K₁ ⊔ baum R), rconj x (pCoreOf 2 (K₁ ⊔ baum R)), A, rconj r A})) ∨
        ((∃ t ∈ TH, conjByElt t K₁ ≠ K₁) ∧
          (baum R : Set G) =
            ((⨆ Ki ∈ conjSubgroupsBy TH K₁, blockU Ki : Subgroup G) : Set G) *
              (rconj x (⨆ Ki ∈ conjSubgroupsBy TH K₁, blockU Ki : Subgroup G) : Set G) *
              ((baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G) : Subgroup G) : Set G) ∧
          {A | A ∈ AFam R ∧ TH ≤ Subgroup.normalizer (A : Set G)} =
            {(baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊔
                (⨆ Ki ∈ conjSubgroupsBy TH K₁, blockU Ki : Subgroup G),
              (baum R ⊓ Subgroup.centralizer (oTwoUpper H : Set G)) ⊔
                rconj x (⨆ Ki ∈ conjSubgroupsBy TH K₁, blockU Ki : Subgroup G)})))


@[expose] def C_5_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H M₀ TH R K₁ : Subgroup G), SetC53 H M₀ TH R K₁ →
    (∀ t ∈ TH, conjByElt t K₁ = K₁) →
    IsMaxSubgroupIn M₀ (M₀ ⊓ Subgroup.normalizer (K₁ : Set G)) →
    (M₀ ⊓ Subgroup.normalizer (K₁ : Set G)).relIndex M₀ = 2 ∧
    (frattini ↥(baum R ⊓ Subgroup.centralizer (K₁ : Set G))).map
        (baum R ⊓ Subgroup.centralizer (K₁ : Set G)).subtype = ⊥ ∧
    (∀ x ∈ M₀, x ∉ Subgroup.normalizer (K₁ : Set G) →
      (baum R : Set G) = (pCoreOf 2 (K₁ ⊔ baum R) : Set G) *
        (rconj x (pCoreOf 2 (K₁ ⊔ baum R)) : Set G)) ∧
    (((∃ n : ℕ, 1 < n ∧ IsLin2Type K₁ n) ∨ IsAltType K₁ 3) →
      ∀ x ∈ M₀, x ∉ Subgroup.normalizer (K₁ : Set G) →
        AFam (baum R) = {pCoreOf 2 (K₁ ⊔ baum R), rconj x (pCoreOf 2 (K₁ ⊔ baum R))}) ∧
    (IsAltType K₁ 5 →
      ∀ x ∈ M₀, x ∉ Subgroup.normalizer (K₁ : Set G) →
        ∃ (A : Subgroup G) (r : G), r ∈ R ⊓ K₁ ∧ r ∉ baum R ∧
          AFam R = {pCoreOf 2 (K₁ ⊔ baum R), rconj x (pCoreOf 2 (K₁ ⊔ baum R)), A, rconj r A})


@[expose] def C_5_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H M₀ T R : Subgroup G), HypC_5_1 H M₀ T R →
    IsSylowTwoOf T ⊤ → IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) → quasithinIsQTKECat G →
    ∃ R₀ : Subgroup G, R₀ ≠ ⊥ ∧ R₀ ≤ R ∧ M₀ ⊔ H ≤ Subgroup.normalizer (R₀ : Set G)

section BurnsideC5a

private theorem burnsideC5a_oTwoUpper_eq_bot {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hchar : CFSG.QuasithinUnique.CharTwo H)
    (hodd : ¬ 2 ∣ Nat.card (CFSG.Quasithin.oTwoUpper H)) : CFSG.Quasithin.oTwoUpper H = ⊥ := by
  set K := CFSG.Quasithin.oTwoUpper H with hK
  set P := pCoreOf 2 H with hP
  have hKn : H ≤ Subgroup.normalizer (K : Set G) := CFSG.Quasithin.le_normalizer_oTwoUpper H
  have hKH : K ≤ H := CFSG.Quasithin.oTwoUpper_le H
  have hPn : H ≤ Subgroup.normalizer (P : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H
  have hPH : P ≤ H := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 H
  have hP2 : IsPGroup 2 P := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H
  have hKP : K ⊓ P = ⊥ := by
    have h2 : IsPGroup 2 (K ⊓ P : Subgroup G) := hP2.to_le inf_le_right
    obtain ⟨n, hn⟩ := h2.exists_card_eq
    have hdvd : Nat.card (K ⊓ P : Subgroup G) ∣ Nat.card K :=
      Subgroup.card_dvd_of_le inf_le_left
    have hn0 : n = 0 := by
      by_contra hne
      rw [hn] at hdvd
      exact hodd ((dvd_pow_self 2 hne).trans hdvd)
    rw [hn0, pow_zero] at hn
    exact Subgroup.eq_bot_of_card_eq _ hn
  have hKc : K ≤ Subgroup.centralizer (P : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have h1 : k * p * k⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hPn (hKH hk)) p).mp hp
    have h2 : p * k⁻¹ * p⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hKn (hPH hp)) k⁻¹).mp (K.inv_mem hk)
    have h3 : k * p * k⁻¹ * p⁻¹ ∈ K ⊓ P := by
      refine ⟨?_, ?_⟩
      · have : k * p * k⁻¹ * p⁻¹ = k * (p * k⁻¹ * p⁻¹) := by group
        rw [this]
        exact K.mul_mem hk h2
      · exact P.mul_mem h1 (P.inv_mem hp)
    rw [hKP, Subgroup.mem_bot] at h3
    have h5 : k * p * k⁻¹ = p := by
      calc k * p * k⁻¹ = (k * p * k⁻¹ * p⁻¹) * p := by group
        _ = p := by rw [h3, one_mul]
    calc p * k = (k * p * k⁻¹) * k := by rw [h5]
      _ = k * p := by group
  refine le_bot_iff.mp ?_
  rw [← hKP]
  exact le_inf le_rfl (fun k hk => hchar ⟨hKH hk, hKc hk⟩)

private theorem burnsideC5a_ne_bot {G : Type} [Group G] [Finite G] {H M₀ T R : Subgroup G}
    (hH : ChC.HypC_5_1 H M₀ T R) : R ≠ ⊥ := by
  rintro rfl
  have hs := hH.sylow_R
  rw [bot_sup_eq] at hs
  have hodd : ¬ 2 ∣ Nat.card (CFSG.Quasithin.oTwoUpper H) := by
    have h := hs.2.2
    rwa [Subgroup.bot_subgroupOf, Subgroup.index_bot] at h
  have hK : CFSG.Quasithin.oTwoUpper H = ⊥ := burnsideC5a_oTwoUpper_eq_bot hH.charTwo hodd
  have hHT : T ⊔ CFSG.Quasithin.twoResidual H = H := CFSG.Quasithin.sup_twoResidual_eq hH.sylow
  rw [CFSG.Quasithin.F6.twoResidual_eq_oTwoUpper, hK, sup_bot_eq] at hHT
  obtain ⟨N, hN⟩ := hH.unique_max
  have hmem : N ∈ CFSG.Quasithin.maxOver H T := by
    unfold CFSG.Quasithin.IsUniqueMaxOver at hN
    rw [hN]
    exact Set.mem_singleton N
  obtain ⟨⟨hNH, -⟩, hTN⟩ := hmem
  exact lt_irrefl _ ((hTN.trans_lt hNH).trans_eq hHT.symm)

private theorem burnsideC5a_hypC51 {G : Type} [Group G] [Finite G] {H M₀ T R : Subgroup G}
    (hH : ChC.HypC_5_1 H M₀ T R) (hR1 : R ≠ ⊥) (hsimple : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hqtke : CFSG.QuasithinUnique.quasithinIsQTKECat G) :
    CFSG.Quasithin.HypC51 H M₀ R T := by
  have hRT : R ≤ T := hH.R_le
  have hR2 : IsPGroup 2 R := hH.sylow.2.1.to_le hRT
  have hRM₀ : R ≤ M₀ := hRT.trans hH.TH_le
  have hpc : pCoreOf 2 M₀ ≠ ⊥ := by
    intro h0
    apply hR1
    refine le_bot_iff.mp ?_
    rw [← h0]
    exact CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer hRM₀ hH.R_norm hR2
  exact
    { sqtk_H := ⟨hH.sqtk.2, hH.sqtk.1⟩
      sqtk_M₀ := ⟨CFSG.Quasithin.kGroup_of_pCoreOf_ne_bot hqtke hsimple hnonab hpc,
        CFSG.Quasithin.stronglyQuasithin_of_pCoreOf_ne_bot hqtke hpc⟩
      charTwo_H := hH.charTwo
      sylow_TH := hH.sylow
      unique_max := hH.unique_max
      R_le := hH.R_le
      TH_le := hH.TH_le
      sylow_R := by rw [sup_comm]; exact hH.sylow_R
      normal_R := hH.R_norm }

private theorem burnsideC5a_core (hC58 : CFSG.Quasithin.TheoremC58) {G : Type} [Group G] [Finite G]
    {H M₀ T R : Subgroup G} (hH : ChC.HypC_5_1 H M₀ T R)
    (hTG : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤) (hsimple : IsSimpleGroup G)
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hqtke : CFSG.QuasithinUnique.quasithinIsQTKECat G) :
    ∃ R₀ : Subgroup G, R₀ ≠ ⊥ ∧ R₀ ≤ R ∧ M₀ ⊔ H ≤ Subgroup.normalizer (R₀ : Set G) := by
  have hR1 : R ≠ ⊥ := burnsideC5a_ne_bot hH
  have hT : CFSG.Open.quasithinIsSylowTwo T := by
    refine ⟨hTG.2.1, ?_⟩
    have h := hTG.2.2
    change ¬ 2 ∣ T.relIndex ⊤ at h
    rwa [Subgroup.relIndex_top_right] at h
  exact hC58 G T hsimple hnonab hqtke hT H M₀ R (burnsideC5a_hypC51 hH hR1 hsimple hnonab hqtke) hR1

end BurnsideC5a

section

theorem as_C_5_8
    : C_5_8 := by
  have hC58 : CFSG.Quasithin.TheoremC58 :=
    CFSG.Quasithin.theoremC58_of_solvable_nonsolvable
      (CFSG.Quasithin.EmptyFaithfulMultiple.input311Solvable_of
        (CFSG.Quasithin.G64.inputC512G64_of_lemmaG64
          (CFSG.Quasithin.G64.lemmaG64_of_b5 CFSG.Quasithin.asB56_holds)))
      CFSG.Quasithin.C58NS.theorem311Nonsolvable_proved
  intro G _ _ H M₀ T R hH hTG hsimple hnonab hqtke
  exact burnsideC5a_core hC58 hH hTG hsimple hnonab hqtke

end

@[expose] def C_5_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H M₀ R T K₁ : Subgroup G) (x : G), SetC58 H M₀ R T K₁ x →
    HypC_5_1 (K₁ ⊔ (T ⊓ Subgroup.normalizer (blockU K₁ : Set G)))
      (Subgroup.normalizer ((T ⊓ Subgroup.normalizer (blockU K₁ : Set G) : Subgroup G) : Set G))
      (T ⊓ Subgroup.normalizer (blockU K₁ : Set G)) (T ⊓ Subgroup.normalizer (blockU K₁ : Set G)) ∧
    HypC_5_2 (Subgroup.normalizer ((T ⊓ Subgroup.normalizer (blockU K₁ : Set G) : Subgroup G) :
        Set G))
      (K₁ ⊔ (T ⊓ Subgroup.normalizer (blockU K₁ : Set G)))
      (T ⊓ Subgroup.normalizer (blockU K₁ : Set G))

section

theorem as_C_5_9
    : C_5_9 := by
  have hC58 : CFSG.Quasithin.TheoremC58 :=
    CFSG.Quasithin.theoremC58_of_solvable_nonsolvable
      (CFSG.Quasithin.EmptyFaithfulMultiple.input311Solvable_of
        (CFSG.Quasithin.G64.inputC512G64_of_lemmaG64
          (CFSG.Quasithin.G64.lemmaG64_of_b5 CFSG.Quasithin.asB56_holds)))
      CFSG.Quasithin.C58NS.theorem311Nonsolvable_proved
  intro G _ _ H M₀ R T K₁ x hset
  exfalso
  obtain ⟨R₀, hne, hle, hnorm⟩ :=
    burnsideC5a_core hC58 hset.hyp1 hset.sylowG hset.simple hset.nonabelian hset.qtke
  exact absurd hnorm (hset.hyp2 R₀ hle hne)

end

@[expose] def C_5_10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H M₀ R T K₁ : Subgroup G) (x : G), SetC58 H M₀ R T K₁ x →
    (oTwoUpper (Subgroup.normalizer ((T ⊓ Subgroup.normalizer (blockU K₁ : Set G) : Subgroup G) :
        Set G)) ⊔ (K₁ ⊔ (T ⊓ Subgroup.normalizer (blockU K₁ : Set G)))) ≤
      Subgroup.normalizer ((conjClosure (blockU K₁) (oTwoUpper (Subgroup.normalizer
        ((T ⊓ Subgroup.normalizer (blockU K₁ : Set G) : Subgroup G) : Set G))) : Subgroup G) :
          Set G) ∧
    conjClosure (blockU K₁) (oTwoUpper (Subgroup.normalizer
        ((T ⊓ Subgroup.normalizer (blockU K₁ : Set G) : Subgroup G) : Set G))) ≤
      pCoreOf 2 (K₁ ⊔ baum R) ∧
    CharTwo (oTwoUpper (Subgroup.normalizer
        ((T ⊓ Subgroup.normalizer (blockU K₁ : Set G) : Subgroup G) : Set G)) ⊔
      (K₁ ⊔ (T ⊓ Subgroup.normalizer (blockU K₁ : Set G))))

section

theorem as_C_5_10
    : C_5_10 := by
  have hC58 : CFSG.Quasithin.TheoremC58 :=
    CFSG.Quasithin.theoremC58_of_solvable_nonsolvable
      (CFSG.Quasithin.EmptyFaithfulMultiple.input311Solvable_of
        (CFSG.Quasithin.G64.inputC512G64_of_lemmaG64
          (CFSG.Quasithin.G64.lemmaG64_of_b5 CFSG.Quasithin.asB56_holds)))
      CFSG.Quasithin.C58NS.theorem311Nonsolvable_proved
  intro G _ _ H M₀ R T K₁ x hset
  exfalso
  obtain ⟨R₀, hne, hle, hnorm⟩ :=
    burnsideC5a_core hC58 hset.hyp1 hset.sylowG hset.simple hset.nonabelian hset.qtke
  exact absurd hnorm (hset.hyp2 R₀ hle hne)

end

@[expose] def C_5_11 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H M₀ R T K₁ : Subgroup G) (x : G), SetC58 H M₀ R T K₁ x →
    IsSylowTwoOf (T ⊓ Subgroup.normalizer (blockU K₁ : Set G))
      (oTwoUpper (Subgroup.normalizer ((T ⊓ Subgroup.normalizer (blockU K₁ : Set G) : Subgroup G) :
        Set G)) ⊔ (K₁ ⊔ (T ⊓ Subgroup.normalizer (blockU K₁ : Set G)))) ∧
    x ∉ (oTwoUpper (Subgroup.normalizer ((T ⊓ Subgroup.normalizer (blockU K₁ : Set G) : Subgroup G) :
        Set G)) ⊔ (K₁ ⊔ (T ⊓ Subgroup.normalizer (blockU K₁ : Set G)))) ∧
    ∀ t ∈ T, t ∉ T ⊓ Subgroup.normalizer (blockU K₁ : Set G) →
      t ∉ (oTwoUpper (Subgroup.normalizer ((T ⊓ Subgroup.normalizer (blockU K₁ : Set G) :
        Subgroup G) : Set G)) ⊔ (K₁ ⊔ (T ⊓ Subgroup.normalizer (blockU K₁ : Set G))))

section

theorem as_C_5_11
    : C_5_11 := by
  have hC58 : CFSG.Quasithin.TheoremC58 :=
    CFSG.Quasithin.theoremC58_of_solvable_nonsolvable
      (CFSG.Quasithin.EmptyFaithfulMultiple.input311Solvable_of
        (CFSG.Quasithin.G64.inputC512G64_of_lemmaG64
          (CFSG.Quasithin.G64.lemmaG64_of_b5 CFSG.Quasithin.asB56_holds)))
      CFSG.Quasithin.C58NS.theorem311Nonsolvable_proved
  intro G _ _ H M₀ R T K₁ x hset
  exfalso
  obtain ⟨R₀, hne, hle, hnorm⟩ :=
    burnsideC5a_core hC58 hset.hyp1 hset.sylowG hset.simple hset.nonabelian hset.qtke
  exact absurd hnorm (hset.hyp2 R₀ hle hne)

end

@[expose] def C_5_12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H M₀ R T K₁ : Subgroup G) (x : G), SetC58 H M₀ R T K₁ x →
    (oTwoUpper (Subgroup.normalizer ((T ⊓ Subgroup.normalizer (blockU K₁ : Set G) : Subgroup G) :
        Set G)) ⊔ (K₁ ⊔ (T ⊓ Subgroup.normalizer (blockU K₁ : Set G)))) ⊓
      Subgroup.normalizer ((T ⊓ Subgroup.normalizer (blockU K₁ : Set G) : Subgroup G) : Set G) ≤
    Subgroup.normalizer (blockU K₁ : Set G)

section

theorem as_C_5_12
    : C_5_12 := by
  have hC58 : CFSG.Quasithin.TheoremC58 :=
    CFSG.Quasithin.theoremC58_of_solvable_nonsolvable
      (CFSG.Quasithin.EmptyFaithfulMultiple.input311Solvable_of
        (CFSG.Quasithin.G64.inputC512G64_of_lemmaG64
          (CFSG.Quasithin.G64.lemmaG64_of_b5 CFSG.Quasithin.asB56_holds)))
      CFSG.Quasithin.C58NS.theorem311Nonsolvable_proved
  intro G _ _ H M₀ R T K₁ x hset
  obtain ⟨R₀, hne, hle, hnorm⟩ :=
    burnsideC5a_core hC58 hset.hyp1 hset.sylowG hset.simple hset.nonabelian hset.qtke
  exact absurd hnorm (hset.hyp2 R₀ hle hne)

end

@[expose] def C_5_13 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H M₀ R T K₁ : Subgroup G) (x : G), SetC58 H M₀ R T K₁ x →
    let T₁ := T ⊓ Subgroup.normalizer (blockU K₁ : Set G)
    let X := oTwoUpper (Subgroup.normalizer (T₁ : Set G)) ⊔ (K₁ ⊔ T₁)
    let X₁ := X ⊓ Subgroup.normalizer ((pCoreOf 2 (T₁ ⊔ K₁) : Subgroup G) : Set G)
    let L := conjClosure K₁ X₁
    X₁ ⊓ Subgroup.normalizer (T₁ : Set G) ≤ Subgroup.normalizer (blockU K₁ : Set G) ∧
    ((L = K₁ ∧ X₁ ≤ Subgroup.normalizer (K₁ : Set G)) ∨
      ((IsShort2 K₁ ∧ K₁ ≤ X₁ ∧ IsAltType K₁ 5 ∧ IsBlock2 X₁ L ∧ IsAltType L 7) ∨
       (IsShort2 K₁ ∧ K₁ ≤ X₁ ∧ IsLin2Type K₁ 2 ∧ IsBlock2 X₁ L ∧ IsExcA7Block L)))

section

theorem as_C_5_13
    : C_5_13 := by
  have hC58 : CFSG.Quasithin.TheoremC58 :=
    CFSG.Quasithin.theoremC58_of_solvable_nonsolvable
      (CFSG.Quasithin.EmptyFaithfulMultiple.input311Solvable_of
        (CFSG.Quasithin.G64.inputC512G64_of_lemmaG64
          (CFSG.Quasithin.G64.lemmaG64_of_b5 CFSG.Quasithin.asB56_holds)))
      CFSG.Quasithin.C58NS.theorem311Nonsolvable_proved
  intro G _ _ H M₀ R T K₁ x hset
  exfalso
  obtain ⟨R₀, hne, hle, hnorm⟩ :=
    burnsideC5a_core hC58 hset.hyp1 hset.sylowG hset.simple hset.nonabelian hset.qtke
  exact absurd hnorm (hset.hyp2 R₀ hle hne)

end

end CFSG.ASVolI
