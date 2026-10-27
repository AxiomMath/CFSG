module

public import CFSG.LocalAnalysis.WeakClosure81.EightTwelveFam
public import CFSG.LocalAnalysis.WeakClosure81.EightTwo
public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G] [Finite G]

theorem exists_isEP_not_le_of_inF {Q : Type} [Group Q] [Finite Q] {j : ℕ} {T M : Subgroup Q}
    (hF : CFSG.LocalAnalysis.UniquenessCase.UC22.F12.InF j (⊤ : Subgroup Q))
    (hT : IsSylowIn 2 T ⊤) (hTM : T ≤ M) (hM : ¬ (⊤ : Subgroup Q) ≤ M)
    {Ω : Set (Subgroup Q)} (hΩ : E1.IsInvColl ⊤ Ω) (hne : Ω.Nonempty)
    (hbot : ∀ A ∈ Ω, A ≠ ⊥) :
    ∃ A ∈ Ω, A ≤ T ∧ ∃ K : Subgroup Q,
      CFSG.LocalAnalysis.UniquenessCase.UC22.F12.IsEP j ⊤ T A K ∧ ¬ K ≤ M := by
  by_contra hcon
  push Not at hcon
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT' : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ := CFSG.ABGLocalTools.isSylowOf_iff.mpr hT
  have hprod := hF T hT' Ω hΩ hne hbot
  apply hM
  intro x _
  have hx : x ∈ (((⊤ : Subgroup Q)) : Set Q) := trivial
  rw [← hprod] at hx
  obtain ⟨e, he, t, ht, rfl⟩ := hx
  refine M.mul_mem ?_ (hTM ht)
  have hle : CFSG.LocalAnalysis.UniquenessCase.UC22.F12.eGenP j ⊤ T Ω ≤ M :=
    iSup₂_le fun A hA => iSup_le fun hAT => iSup₂_le fun K hK => hcon A hA hAT K hK
  exact hle he

theorem exists_isE_not_le_of_quotient {Q : Type} [Group Q] [Finite Q] {Y : Subgroup Q}
    [Y.Normal] {j : ℕ} {T A M₁ : Subgroup Q} (hT : IsSylowIn 2 T ⊤) (hA : A ≤ T)
    (hAab : IsElemAbelian 2 A) (hTM : T ≤ M₁) {K' : Subgroup (Q ⧸ Y)}
    (hK' : E1.IsE j ⊤ (T.map (QuotientGroup.mk' Y)) (A.map (QuotientGroup.mk' Y)) K')
    (hKM : ¬ K' ≤ M₁.map (QuotientGroup.mk' Y)) :
    ∃ J : Subgroup Q, E1.IsE j ⊤ T A J ∧ ¬ J ≤ M₁ := by
  obtain ⟨J, hJ, hres⟩ := E1.ten_seven hT hA hAab hK'
  refine ⟨J, hJ, fun hJM => hKM ?_⟩
  rw [← sup_twoResidual_eq hK'.2.2.1]
  exact sup_le (inf_le_left.trans (Subgroup.map_mono hTM))
    (hres ▸ Subgroup.map_mono ((twoResidual_le J).trans hJM))

theorem exists_isE_not_le_of_inF2 {V H T M₀ : Subgroup G} {i j : ℕ} (hV : IsElemAbelian 2 V)
    (hT : IsSylowIn 2 T H) (hF : InFSq j H) (hTM : T ≤ M₀) (hHM : ¬ H ≤ M₀)
    (hA : ∃ A ∈ E3.gammaSet V i T, ¬ A ≤ pCoreOf 2 H) :
    ∃ A ∈ E3.gammaSet V i T, ¬ A ≤ pCoreOf 2 H ∧
      ∃ K : Subgroup G, E1.IsE j H T A K ∧ ¬ K ≤ M₀ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y : Subgroup ↥H := CFSG.Open.pCore 2 ↥H with hY
  set π : ↥H →* ↥H ⧸ Y := QuotientGroup.mk' Y with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective Y
  set T' : Subgroup ↥H := T.subgroupOf H with hT'
  have hT'syl : IsSylowIn 2 T' ⊤ := by
    have := (E1.isSylowIn_subgroupOf_iff hT.le le_rfl).mpr hT
    rwa [Subgroup.subgroupOf_self] at this
  have hYT : Y ≤ T' := by
    intro y hy
    have : (y : G) ∈ pCoreOf 2 H := ⟨y, hy, rfl⟩
    exact E1.pCoreOf_two_le_of_isSylowIn hT this
  have hTt : IsSylowIn 2 (T'.map π) ⊤ := E1.isSylowIn_two_map_top hπs hT'syl
  set M₁ : Subgroup ↥H := M₀.subgroupOf H with hM₁
  have hT'M₁ : T' ≤ M₁ := fun x hx => hTM hx
  have hMt : ¬ (⊤ : Subgroup (↥H ⧸ Y)) ≤ M₁.map π := by
    intro htop
    apply hHM
    intro x hx
    obtain ⟨m, hm, hmx⟩ := htop (Subgroup.mem_top (π ⟨x, hx⟩))
    have h1 : m⁻¹ * ⟨x, hx⟩ ∈ Y := by
      rw [← QuotientGroup.eq]
      exact hmx
    have h2 : m⁻¹ * ⟨x, hx⟩ ∈ T' := hYT h1
    have h3 : (⟨x, hx⟩ : ↥H) = m * (m⁻¹ * ⟨x, hx⟩) := by group
    have h4 : (⟨x, hx⟩ : ↥H) ∈ M₁ := by
      rw [h3]
      exact M₁.mul_mem hm (hT'M₁ h2)
    exact h4
  let ΩG : Set (Subgroup G) :=
    {A | A ≤ H ∧ (∃ g : G, A ≤ conjSubgroup V g ∧ E3.mQuot (conjSubgroup V g) A = i) ∧
      ¬ A ≤ pCoreOf 2 H}
  let Ω : Set (Subgroup (↥H ⧸ Y)) := {B | ∃ A ∈ ΩG, B = (A.subgroupOf H).map π}
  have hΩ : E1.IsInvColl (⊤ : Subgroup (↥H ⧸ Y)) Ω := by
    refine ⟨fun _ _ => le_top, ?_, ?_⟩
    · rintro B ⟨A, ⟨hAH, ⟨g, hAg, -⟩, -⟩, rfl⟩
      exact CFSG.Open.IsElemAbelian.map (CFSG.Open.IsElemAbelian.subgroupOf
        (CFSG.Open.IsElemAbelian.mono (isElemAbelian_conjSubgroup' hV g) hAg) H) π
    · rintro B ⟨A, ⟨hAH, ⟨g, hAg, hm⟩, hAO⟩, rfl⟩ b -
      obtain ⟨h, rfl⟩ := hπs b
      refine ⟨conjSubgroup A (h : G)⁻¹, ⟨conjSubgroup_le_of_le hAH (H.inv_mem h.2),
        ⟨g * (h : G)⁻¹, ?_, ?_⟩, ?_⟩, ?_⟩
      · rw [← conjSubgroup_conjSubgroup V g (h : G)⁻¹]
        exact Subgroup.map_mono hAg
      · rw [← conjSubgroup_conjSubgroup V g (h : G)⁻¹,
          E3.mQuot_conjSubgroup (conjSubgroup V g) A (h : G)⁻¹]
        exact hm
      · intro hle
        apply hAO
        have h1 := E3.conjSubgroup_mono_left (h : G) hle
        have hN : (h : G) ∈ normalizer (pCoreOf 2 H : Set G) :=
          CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H h.2
        rw [conjSubgroup_eq_iff_mem_normalizer.mpr hN, conjSubgroup_conjSubgroup,
          inv_mul_cancel, conjSubgroup_one] at h1
        exact h1
      · rw [← E1.map_conjSub]
        congr 1
        ext x
        simp [CFSG.Quasithin.A1b.mem_conjSub_iff, mem_conjSubgroup_iff, Subgroup.mem_subgroupOf]
  have hne : Ω.Nonempty := by
    obtain ⟨A₀, ⟨hA₀T, hA₀g⟩, hA₀O⟩ := hA
    exact ⟨_, A₀, ⟨hA₀T.trans hT.le, hA₀g, hA₀O⟩, rfl⟩
  have hbot : ∀ B ∈ Ω, B ≠ ⊥ := by
    rintro B ⟨A, ⟨hAH, -, hAO⟩, rfl⟩ hB
    apply hAO
    intro a ha
    have h1 : π ⟨a, hAH ha⟩ ∈ (A.subgroupOf H).map π :=
      Subgroup.mem_map_of_mem π (show (⟨a, hAH ha⟩ : ↥H) ∈ A.subgroupOf H from ha)
    rw [hB, Subgroup.mem_bot] at h1
    have h2 : (⟨a, hAH ha⟩ : ↥H) ∈ Y := (QuotientGroup.eq_one_iff _).mp h1
    exact ⟨_, h2, rfl⟩
  obtain ⟨B, hBΩ, hBT, K', hK'EP, hK'M⟩ :=
    exists_isEP_not_le_of_inF (T := T'.map π) (M := M₁.map π) hF hTt
      (Subgroup.map_mono hT'M₁) hMt hΩ hne hbot
  obtain ⟨A, ⟨hAH, ⟨g, hAg, hm⟩, hAO⟩, rfl⟩ := hBΩ
  have hAT' : A.subgroupOf H ≤ T' := by
    intro a ha
    obtain ⟨t, ht, hta⟩ := hBT (Subgroup.mem_map_of_mem π ha)
    have h2 : t⁻¹ * a ∈ Y := by
      rw [← QuotientGroup.eq]
      exact hta
    have h3 : a = t * (t⁻¹ * a) := by group
    rw [h3]
    exact T'.mul_mem ht (hYT h2)
  have hAT : A ≤ T := fun a ha => hAT' (show (⟨a, hAH ha⟩ : ↥H) ∈ A.subgroupOf H from ha)
  have hAab : IsElemAbelian 2 (A.subgroupOf H) :=
    CFSG.Open.IsElemAbelian.subgroupOf
      (CFSG.Open.IsElemAbelian.mono (isElemAbelian_conjSubgroup' hV g) hAg) H
  have hBab : IsElemAbelian 2 ((A.subgroupOf H).map π) := CFSG.Open.IsElemAbelian.map hAab π
  have hK'E : E1.IsE j ⊤ (T'.map π) ((A.subgroupOf H).map π) K' :=
    isE_of_isEP hTt hBT hBab hK'EP
  obtain ⟨J, hJ, hJM⟩ := exists_isE_not_le_of_quotient (Y := Y) (T := T') (A := A.subgroupOf H)
    (M₁ := M₁) hT'syl hAT' hAab hT'M₁ hK'E hK'M
  refine ⟨A, ⟨hAT, g, hAg, hm⟩, hAO, J.map H.subtype, ?_, ?_⟩
  · have h := (E1.isE_map_subtype H (i := j) (T' := T') (A' := A.subgroupOf H) (K' := J)).mpr hJ
    rwa [hT', Subgroup.map_subgroupOf_eq_of_le hT.le,
      Subgroup.map_subgroupOf_eq_of_le hAH] at h
  · intro hle
    exact hJM fun x hx => hle (Subgroup.mem_map_of_mem H.subtype hx)

end CFSG.LocalAnalysis.WeakClosure81

end
