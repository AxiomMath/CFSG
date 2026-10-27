module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5ASDefs
public import CFSG.LocalAnalysis.WeakClosure81.EightTwelveBridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSixE

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_isE_not_le_of_inFAS {Q : Type} [Group Q] [Finite Q] {j : ℕ} {T M : Subgroup Q}
    (hF : InFAS j (⊤ : Subgroup Q)) (hT : IsSylowIn 2 T ⊤) (hTM : T ≤ M)
    (hM : ¬ (⊤ : Subgroup Q) ≤ M) {Ω : Set (Subgroup Q)} (hΩ : E1.IsInvColl ⊤ Ω)
    (hne : Ω.Nonempty) (hbot : ∀ A ∈ Ω, A ≠ ⊥) :
    ∃ A ∈ Ω, A ≤ T ∧ ∃ K : Subgroup Q, E1.IsE j ⊤ T A K ∧ ¬ K ≤ M := by
  by_contra hcon
  push Not at hcon
  have hprod := hF T hT Ω hΩ hne hbot
  apply hM
  intro x _
  have hx : x ∈ (((⊤ : Subgroup Q)) : Set Q) := trivial
  rw [← hprod] at hx
  obtain ⟨e, he, t, ht, rfl⟩ := hx
  refine M.mul_mem ?_ (hTM ht)
  have hle : E1.eGen j ⊤ T Ω ≤ M :=
    iSup₂_le fun A hA => iSup_le fun hAT => iSup₂_le fun K hK => hcon A hA hAT K hK
  exact hle he

theorem exists_isE_not_le_of_inFSqAS {j : ℕ} {H T M₀ : Subgroup G} (hT : IsSylowIn 2 T H)
    (hF : InFSqAS j H) (hTM : T ≤ M₀) (hHM : ¬ H ≤ M₀) {Ω : Set (Subgroup G)}
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
  obtain ⟨B, hBΩ, hBT, K', hK'E, hK'M⟩ :=
    exists_isE_not_le_of_inFAS (T := T'.map π) (M := M₁.map π) hF hTt
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
  obtain ⟨J, hJ, hJM⟩ := exists_isE_not_le_of_quotient (Y := Y) (T := T') (A := A.subgroupOf H)
    (M₁ := M₁) hT'syl hAT' hAab hT'M₁ hK'E hK'M
  refine ⟨A, hAΩ, hAT, J.map H.subtype, ?_, ?_⟩
  · have h := (E1.isE_map_subtype H (i := j) (T' := T') (A' := A.subgroupOf H) (K' := J)).mpr hJ
    rwa [hT', Subgroup.map_subgroupOf_eq_of_le hT.le,
      Subgroup.map_subgroupOf_eq_of_le hAH] at h
  · intro hle
    exact hJM fun x hx => hle (Subgroup.mem_map_of_mem H.subtype hx)

theorem inEFor_of_inFSqAS {j : ℕ} {H T : Subgroup G} (hT : IsSylowIn 2 T H) (hF : InFSqAS j H) :
    E1.InEFor j H T := by
  intro Ω hΩ
  have hTW : T ≤ normalizer (E1.weakClosure T Ω : Set G) := fun t ht =>
    TwelveSix.mem_normalizer_weakClosure_of_mem hΩ (hT.le ht) fun w hw =>
      T.mul_mem (T.mul_mem ht (E1.weakClosure_le hw)) (T.inv_mem ht)
  have hEH : E1.eGen j H T Ω ≤ H :=
    iSup₂_le fun _ _ => iSup_le fun _ => iSup₂_le fun _ hK => hK.1
  refine le_antisymm (sup_le hEH inf_le_left) ?_
  by_contra hHM
  by_cases hA : ∃ A ∈ Ω, ¬ A ≤ pCoreOf 2 H
  · obtain ⟨A, hAΩ, hAT, K, hK, hKM⟩ :=
      exists_isE_not_le_of_inFSqAS hT hF (le_sup_of_le_right (le_inf hT.le hTW)) hHM hΩ hA
    exact hKM (le_sup_of_le_left (E1.le_eGen hAΩ hAT hK))
  · have hO : ∀ A ∈ Ω, A ≤ pCoreOf 2 H := fun A hA' => by
      by_contra h
      exact hA ⟨A, hA', h⟩
    have hOT : pCoreOf 2 H ≤ T := E1.pCoreOf_two_le_of_isSylowIn hT
    apply hHM
    refine le_sup_of_le_right (le_inf le_rfl fun h hh => ?_)
    refine TwelveSix.mem_normalizer_weakClosure_of_mem hΩ hh fun w hw => hOT ?_
    have hwO : w ∈ pCoreOf 2 H :=
      (iSup₂_le fun A hA' => iSup_le fun _ => hO A hA' : E1.weakClosure T Ω ≤ pCoreOf 2 H) hw
    exact (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hh w).1 hwO

theorem inE_of_inFSqAS {j : ℕ} {H : Subgroup G} (hF : InFSqAS j H) : E1.InE j H :=
  fun _ hT => inEFor_of_inFSqAS hT hF

end CFSG.LocalAnalysis.WeakClosure81
