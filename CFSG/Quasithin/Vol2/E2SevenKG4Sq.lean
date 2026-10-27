module

public import CFSG.Quasithin.Vol2.E2SevenKG4
public import CFSG.Quasithin.Vol2.E2SevenKGAS
public import CFSG.Quasithin.Vol2.Ch3E213MOS11
public import CFSG.GH74.GLS.IVK.L2.ExistNotation
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk6Over

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace E2

theorem kgL2OddSq_holds : KGL2OddSq := by
  intro G _ _ X T M K V p hP _ hKX hXN hC hKT hp hp3 _ hK hMK haut hVO hVab hTV
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hV2
  push Not at hV2
  have hV4 : 4 ≤ Nat.card V := by
    obtain ⟨k, hk⟩ := (B6.isPGroup_of_isElemAbelian hVab).exists_card_eq
    rw [hk] at hV2 ⊢
    rcases Nat.lt_or_ge k 2 with h | h
    · interval_cases k <;> simp at hV2
    · calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h
  obtain ⟨hMmax, -⟩ : IsMaxSubgroupIn X M ∧ T ≤ M := by
    have : M ∈ maxOver X T := by rw [hP.uniqueMax]; exact rfl
    exact this
  have hMX : M ≤ X := hMmax.le
  have hTX : T ≤ X := hP.isSylow.1
  have hVT : V ≤ T := hVO.trans (pCoreOf_le_of_minParabolic hP)
  have hVX : V ≤ X := hVT.trans hTX
  have hsK : IsSimpleGroup ↥K := by
    obtain ⟨-, F, _, _, hcard, ⟨e₀⟩⟩ := id hK
    have h4 : 4 ≤ Nat.card F := by
      rw [hcard]
      nlinarith
    have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
    exact (e₀.trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm).isSimpleGroup
  have hX := asHyp_subgroupOf hP hKX hXN hC hKT hsK
  have hK' : IsPSL 2 p 2 ↥(K.subgroupOf X) := by
    obtain ⟨hadm, F, _, _, hcard, ⟨e⟩⟩ := hK
    exact ⟨hadm, F, inferInstance, inferInstance, hcard,
      ⟨(Subgroup.subgroupOfEquivOfLe hKX).trans e⟩⟩
  have hautT : autCard T K = Nat.card T := by
    unfold autCard
    have h1 : T ⊓ Subgroup.normalizer (K : Set G) = T := inf_eq_left.mpr (hTX.trans hXN)
    have h2 : T ⊓ Subgroup.centralizer (K : Set G) = ⊥ := by
      rw [eq_bot_iff, ← hC]
      exact inf_le_inf_right _ hTX
    rw [h1, h2, Subgroup.relIndex_bot_left]
  have hautT' : autCard (T.subgroupOf X) (K.subgroupOf X) = Nat.card ↥(T.subgroupOf X) := by
    unfold autCard
    rw [Subgroup.normalizer_eq_top_iff.mpr hX.normal, hX.cent, inf_top_eq, inf_bot_eq,
      Subgroup.relIndex_bot_left]
  have hAut' : 8 < autCard (T.subgroupOf X) (K.subgroupOf X) := by
    rw [hautT', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTX).toEquiv, ← hautT]
    exact haut
  have hVT' : V.subgroupOf X ≤ T.subgroupOf X := Subgroup.subgroupOf_mono _ hVT
  have hVn' : T.subgroupOf X ≤ Subgroup.normalizer ((V.subgroupOf X : Subgroup ↥X) : Set ↥X) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    have := Subgroup.mem_normalizer_iff.mp (hTV (Subgroup.mem_subgroupOf.mp hs)) y
    simpa using this
  have hsq : ∀ v ∈ V.subgroupOf X, v * v = 1 := by
    intro v hv
    have := hVab.2 _ (Subgroup.mem_subgroupOf.mp hv)
    exact Subtype.ext (by simpa [sq] using this)
  have hV4' : 4 ≤ Nat.card ↥(V.subgroupOf X) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVX).toEquiv]
  exact Ch3E213M.OS.false_of_asHyp GH74.GLS.IVK.ivk_1_2_general GH74.GLS.IVK.ivk_1_3a
    GH74.GLS.IVK.ivk_1_3b
    (by
      intro _ _ _ hF h11 _ _ _ e _ hu
      exact GH74.GLS.IVK.Proofs2.isCoatom_centralizer_of_inner hF h11 e hu)
    hX hp hp3 (Or.inr rfl) hK' (inf_subgroupOf_eq_of_inf_eq hKX hMK) hAut' hVT' hVn' hsq hV4'
    (subgroupOf_le_pCoreOf hMX hVO)

end E2

end CFSG.Quasithin
