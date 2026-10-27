module

public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs
import CFSG.LocalAnalysis.WeakClosure81.EightTwelveBridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

namespace TwelveSix

theorem mem_normalizer_weakClosure_of_mem {H T : Subgroup G} {Ω : Set (Subgroup G)}
    (hΩ : E1.IsInvColl H Ω) {x : G} (hxH : x ∈ H)
    (hx : ∀ w ∈ E1.weakClosure T Ω, x * w * x⁻¹ ∈ T) :
    x ∈ normalizer (E1.weakClosure T Ω : Set G) := by
  apply E1.mem_normalizer_of_conj_mem
  have hle : E1.weakClosure T Ω ≤ (E1.weakClosure T Ω).comap (MulAut.conj x).toMonoidHom := by
    refine iSup₂_le fun A hA => iSup_le fun hAT => ?_
    intro a ha
    rw [Subgroup.mem_comap]
    have h1 : A1b.conjSub x A ∈ Ω := hΩ.conj A hA x hxH
    have h2 : A1b.conjSub x A ≤ T := by
      intro y hy
      rw [A1b.mem_conjSub_iff] at hy
      have h3 : x * (x⁻¹ * y * x) * x⁻¹ ∈ T := hx _ (E1.le_weakClosure hA hAT hy)
      have e : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
      rwa [e] at h3
    exact E1.le_weakClosure h1 h2 (A1b.mem_conjSub_of_mem ha)
  intro w hw
  exact hle hw

theorem exists_isE_not_le_of_inFSq {j : ℕ} {H T M₀ : Subgroup G} (hT : IsSylowIn 2 T H)
    (hF : InFSq j H) (hTM : T ≤ M₀) (hHM : ¬ H ≤ M₀) {Ω : Set (Subgroup G)}
    (hΩ : E1.IsInvColl H Ω) (hA : ∃ A ∈ Ω, ¬ A ≤ pCoreOf 2 H) :
    ∃ A ∈ Ω, A ≤ T ∧ ∃ K : Subgroup G, E1.IsE j H T A K ∧ ¬ K ≤ M₀ := by
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
  let ΩG : Set (Subgroup G) := {A | A ∈ Ω ∧ ¬ A ≤ pCoreOf 2 H}
  let Ω' : Set (Subgroup (↥H ⧸ Y)) := {B | ∃ A ∈ ΩG, B = (A.subgroupOf H).map π}
  have hΩ' : E1.IsInvColl (⊤ : Subgroup (↥H ⧸ Y)) Ω' := by
    refine ⟨fun _ _ => le_top, ?_, ?_⟩
    · rintro B ⟨A, ⟨hAΩ, -⟩, rfl⟩
      exact CFSG.Open.IsElemAbelian.map
        (CFSG.Open.IsElemAbelian.subgroupOf (hΩ.isElemAbelian A hAΩ) H) π
    · rintro B ⟨A, ⟨hAΩ, hAO⟩, rfl⟩ b -
      obtain ⟨h, rfl⟩ := hπs b
      refine ⟨A1b.conjSub (h : G) A, ⟨hΩ.conj A hAΩ h h.2, ?_⟩, ?_⟩
      · intro hle
        apply hAO
        intro a ha
        have h1 : (h : G) * a * (h : G)⁻¹ ∈ pCoreOf 2 H := hle (A1b.mem_conjSub_of_mem ha)
        have hN : (h : G)⁻¹ ∈ normalizer (pCoreOf 2 H : Set G) :=
          CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (H.inv_mem h.2)
        have h2 := (hN _).1 h1
        have e : (h : G)⁻¹ * ((h : G) * a * (h : G)⁻¹) * (h : G)⁻¹⁻¹ = a := by group
        rwa [e] at h2
      · rw [← E1.map_conjSub]
        congr 1
        ext x
        simp [CFSG.Quasithin.A1b.mem_conjSub_iff, Subgroup.mem_subgroupOf]
  have hne : Ω'.Nonempty := by
    obtain ⟨A₀, hA₀Ω, hA₀O⟩ := hA
    exact ⟨_, A₀, ⟨hA₀Ω, hA₀O⟩, rfl⟩
  have hbot : ∀ B ∈ Ω', B ≠ ⊥ := by
    rintro B ⟨A, ⟨hAΩ, hAO⟩, rfl⟩ hB
    apply hAO
    intro a ha
    have hAH : A ≤ H := hΩ.le A hAΩ
    have h1 : π ⟨a, hAH ha⟩ ∈ (A.subgroupOf H).map π :=
      Subgroup.mem_map_of_mem π (show (⟨a, hAH ha⟩ : ↥H) ∈ A.subgroupOf H from ha)
    rw [hB, Subgroup.mem_bot] at h1
    have h2 : (⟨a, hAH ha⟩ : ↥H) ∈ Y := (QuotientGroup.eq_one_iff _).mp h1
    exact ⟨_, h2, rfl⟩
  obtain ⟨B, hBΩ, hBT, K', hK'EP, hK'M⟩ :=
    exists_isEP_not_le_of_inF (T := T'.map π) (M := M₁.map π) hF hTt
      (Subgroup.map_mono hT'M₁) hMt hΩ' hne hbot
  obtain ⟨A, ⟨hAΩ, hAO⟩, rfl⟩ := hBΩ
  have hAH : A ≤ H := hΩ.le A hAΩ
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
    CFSG.Open.IsElemAbelian.subgroupOf (hΩ.isElemAbelian A hAΩ) H
  have hBab : IsElemAbelian 2 ((A.subgroupOf H).map π) := CFSG.Open.IsElemAbelian.map hAab π
  have hK'E : E1.IsE j ⊤ (T'.map π) ((A.subgroupOf H).map π) K' :=
    isE_of_isEP hTt hBT hBab hK'EP
  obtain ⟨J, hJ, hJM⟩ := exists_isE_not_le_of_quotient (Y := Y) (T := T') (A := A.subgroupOf H)
    (M₁ := M₁) hT'syl hAT' hAab hT'M₁ hK'E hK'M
  refine ⟨A, hAΩ, hAT, J.map H.subtype, ?_, ?_⟩
  · have h := (E1.isE_map_subtype H (i := j) (T' := T') (A' := A.subgroupOf H) (K' := J)).mpr hJ
    rwa [hT', Subgroup.map_subgroupOf_eq_of_le hT.le,
      Subgroup.map_subgroupOf_eq_of_le hAH] at h
  · intro hle
    exact hJM fun x hx => hle (Subgroup.mem_map_of_mem H.subtype hx)

end TwelveSix

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
