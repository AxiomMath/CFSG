module

public import CFSG.LocalAnalysis.WeakClosure81.FourFiveLayer.PrintFam
public import CFSG.Quasithin.Background.RonanE111Diag

public section

namespace CFSG.LocalAnalysis.WeakClosure81.FourFiveLayer

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.E1 CFSG.Quasithin.E2.E22N
  CFSG.Quasithin.E2.E22N.E111R
open scoped commutatorElement

variable {G : Type} [Group G]

private theorem layer_diagP {Q : Type} [Group Q] [Finite Q] {𝒟 : Set (Subgroup Q)}
    (h𝒟 : E111R.SemiFam 𝒟) (hEn : (sSup 𝒟).Normal)
    (hC : IsPGroup 2 (Subgroup.centralizer ((sSup 𝒟 : Subgroup Q) : Set Q)))
    {Ta : Subgroup Q} {D₀ : Subgroup Q} (hD₀ : D₀ ∈ 𝒟) {Γ : Subgroup Q} (hΓ : Γ ≤ Ta)
    (htr : ⨆ (t : Q) (_ : t ∈ Γ), A1b.conjSub t D₀ = sSup 𝒟) :
    CFSG.layer (Q ⧸ CFSG.solvableRadical Q) =
      ⨆ t ∈ Ta.map (QuotientGroup.mk' (CFSG.solvableRadical Q)),
        A1b.conjSub t (D₀.map (QuotientGroup.mk' (CFSG.solvableRadical Q))) := by
  set π := QuotientGroup.mk' (CFSG.solvableRadical Q) with hπ
  have hconjE : ∀ q : Q, A1b.conjSub q D₀ ≤ sSup 𝒟 := fun q y hy => by
    rw [A1b.mem_conjSub_iff] at hy
    have h3 := hEn.conj_mem _ (le_sSup hD₀ hy) q
    have e3 : q * (q⁻¹ * y * q) * q⁻¹ = y := by group
    rwa [e3] at h3
  rw [E111R.layer_quot_eq h𝒟 hEn hC]
  refine le_antisymm ?_ (iSup₂_le fun t ht => ?_)
  · rw [← htr, Subgroup.map_iSup]
    refine iSup_le fun t => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun ht => ?_
    refine le_iSup₂_of_le (π t) (Subgroup.mem_map_of_mem π (hΓ ht)) ?_
    rw [E111R.conjSub_map]
  · obtain ⟨q, -, rfl⟩ := ht
    rw [E111R.conjSub_map]
    exact Subgroup.map_mono (hconjE q)

theorem eTwoPrint_of_semiFam {Q : Type} [Group Q] [Finite Q] {𝒟 : Set (Subgroup Q)}
    (h𝒟 : E111R.SemiFam 𝒟) (hEn : (sSup 𝒟).Normal)
    (hC : IsPGroup 2 (Subgroup.centralizer ((sSup 𝒟 : Subgroup Q) : Set Q)))
    {B₀ Ta B : Subgroup Q} (hEB : sSup 𝒟 ⊔ B₀ = ⊤) (hB₀ : IsPGroup 2 B₀)
    {D₀ : Subgroup Q} (hD₀ : D₀ ∈ 𝒟) {Γ : Subgroup Q} (hΓ : Γ ≤ Ta)
    (htr : ⨆ (t : Q) (_ : t ∈ Γ), A1b.conjSub t D₀ = sSup 𝒟)
    (hcase : D₀ = ⁅D₀, B⁆ ∨
      (¬ B ≤ Subgroup.normalizer (D₀ : Set Q) ∧ Nat.card ↥(E1.barRad Q B) = 2)) :
    UniquenessCase.UC22.F12.ETwoPrint Q Ta B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR := E111R.solvableRadical_eq h𝒟 hEn hC
  set π := QuotientGroup.mk' (CFSG.solvableRadical Q) with hπ
  have h2 := E111R.pow_mem_of_sup hEn hEB hB₀
  refine ⟨?_, ?_, ?_, D₀.map π, E111R.isComponent_map h𝒟 hEn hC hD₀, ?_, ?_⟩
  · rw [hR]
    refine ⟨_, ⟨le_rfl, hC, by rw [Subgroup.relIndex_self]; norm_num⟩, ?_⟩
    rw [Subgroup.subgroupOf_self]
    infer_instance
  · rw [E1.pCore_two_quotient_eq_top_iff]
    intro x
    obtain ⟨k, hk⟩ := h2 x
    refine ⟨k, Subgroup.mem_comap.mpr ?_⟩
    rw [E111R.layer_quot_eq h𝒟 hEn hC]
    exact Subgroup.mem_map_of_mem π hk
  · rw [E111R.twoResidual_eq h𝒟 hEn h2, E111R.perfectCore_eq h𝒟 hEn hEB hB₀]
  · change CFSG.layer (Q ⧸ CFSG.solvableRadical Q) =
      ⨆ t ∈ Ta.map π, A1b.conjSub t (D₀.map π)
    exact layer_diagP h𝒟 hEn hC hD₀ hΓ htr
  · rcases hcase with h | ⟨h1, h2'⟩
    · left
      unfold E1.barRad
      rw [← Subgroup.map_commutator, ← h]
    · right
      refine ⟨fun hle => h1 fun b hb => ?_, h2'⟩
      exact E111R.mem_normalizer_of_map h𝒟 hEn hC hD₀ (hle ⟨b, hb, rfl⟩)

theorem exists_conjSub_eq_of_mem_sup [Finite G] {X T A S C : Subgroup G}
    (h : E111R.DiagSetting X T A S C) [Fintype ↥C] {Γ : Subgroup G}
    (hΓ : Γ ≤ Subgroup.centralizer (A : Set G)) {g : G}
    (hgA : g ∈ Subgroup.centralizer (A : Set G)) (hg : g ∈ X ⊔ Γ) :
    ∃ t ∈ Γ, A1b.conjSub g (E111R.diagSub S C h.diagComm) =
      A1b.conjSub t (E111R.diagSub S C h.diagComm) := by
  haveI : X.Normal := h.red.1
  rw [sup_comm] at hg
  obtain ⟨t, ht, x, hx, htx⟩ := Subgroup.mem_sup_of_normal_right.mp hg
  have hxA : x ∈ Subgroup.centralizer (A : Set G) := by
    have h1 : t⁻¹ * g ∈ Subgroup.centralizer (A : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (hΓ ht)) hgA
    rwa [← htx, inv_mul_cancel_left] at h1
  refine ⟨t, ht, ?_⟩
  rw [← htx, A1b.conjSub_mul,
    h.conjSub_diag_of_comm (h.comp.le_normalizer hx) fun c hc =>
      (Subgroup.mem_centralizer_iff.mp hxA c (h.CA hc)).symm]

private theorem diagE_eq_iSup_conjSub_diagP [Finite G] {X T A S C : Subgroup G}
    (h : E111R.DiagSetting X T A S C) [Fintype ↥C] {Γ : Subgroup G}
    (hΓT : Γ ≤ T ⊓ Subgroup.centralizer (A : Set G))
    (hΓX : T ⊓ Subgroup.centralizer (A : Set G) ≤ X ⊔ Γ) :
    ⨆ (t : G) (_ : t ∈ Γ), A1b.conjSub t (E111R.diagSub S C h.diagComm) =
      E111R.diagE T A S C h.diagComm := by
  rw [h.diagE_eq]
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun t ht => ?_
    exact le_iSup_of_le ⟨t, hΓT ht⟩ le_rfl
  · refine iSup_le fun g => ?_
    obtain ⟨t, ht, heq⟩ :=
      exists_conjSub_eq_of_mem_sup h (hΓT.trans inf_le_right) g.2.2 (hΓX g.2)
    exact le_iSup₂_of_le t ht heq.le

private theorem diagK_centralizer_isPGroup_diagP [Finite G] {X T A S C : Subgroup G}
    (h : E111R.DiagSetting X T A S C) [Fintype ↥C] :
    IsPGroup 2 (Subgroup.centralizer
      (((E111R.diagE T A S C h.diagComm).subgroupOf
          (E111R.diagK T A S C h.diagComm) : Subgroup ↥(E111R.diagK T A S C h.diagComm)) :
        Set ↥(E111R.diagK T A S C h.diagComm))) := by
  set K := E111R.diagK T A S C h.diagComm with hK
  set E := E111R.diagE T A S C h.diagComm with hE
  intro x
  have hx : (x : ↥K) ∈ Subgroup.centralizer ((E.subgroupOf K : Subgroup ↥K) : Set ↥K) := x.2
  rw [E111R.mem_centralizer_subgroupOf_iff h.diagE_le_diagK] at hx
  obtain ⟨m, hm⟩ := h.isPGroup_inf_centralizer ⟨((x : ↥K) : G), (x : ↥K).2, hx⟩
  refine ⟨m, Subtype.ext (Subtype.ext ?_)⟩
  simpa using congrArg Subtype.val hm

private theorem diagK_iSup_conjSub_eq_diagP [Finite G] {X T A S C : Subgroup G}
    (h : E111R.DiagSetting X T A S C) [Fintype ↥C] {Γ : Subgroup G}
    (hΓT : Γ ≤ T ⊓ Subgroup.centralizer (A : Set G))
    (hΓX : T ⊓ Subgroup.centralizer (A : Set G) ≤ X ⊔ Γ) :
    ⨆ (t : ↥(E111R.diagK T A S C h.diagComm))
        (_ : t ∈ Γ.subgroupOf (E111R.diagK T A S C h.diagComm)),
      A1b.conjSub t ((E111R.diagSub S C h.diagComm).subgroupOf
        (E111R.diagK T A S C h.diagComm)) =
      sSup ((fun D : Subgroup G => D.subgroupOf (E111R.diagK T A S C h.diagComm)) ''
        E111R.diagFam T A S C h.diagComm) := by
  set K := E111R.diagK T A S C h.diagComm with hK
  set E := E111R.diagE T A S C h.diagComm with hE
  set 𝒟' : Set (Subgroup ↥K) :=
    (fun D : Subgroup G => D.subgroupOf K) '' E111R.diagFam T A S C h.diagComm with h𝒟'
  have hdK : E111R.diagSub S C h.diagComm ≤ K := h.diag_le_diagE.trans h.diagE_le_diagK
  have hE' : sSup 𝒟' = E.subgroupOf K :=
    E111R.sSup_image_subgroupOf fun D hD => (le_sSup hD).trans h.diagE_le_diagK
  rw [hE']
  apply Subgroup.map_injective K.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le h.diagE_le_diagK,
    ← diagE_eq_iSup_conjSub_diagP h hΓT hΓX, Subgroup.map_iSup]
  apply le_antisymm
  · refine iSup_le fun t => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun ht => ?_
    rw [E111R.conjSub_subgroupOf t hdK,
      Subgroup.map_subgroupOf_eq_of_le (E111R.conjSub_le_of_mem t.2 hdK)]
    exact le_iSup₂_of_le (t : G) (Subgroup.mem_subgroupOf.mp ht) le_rfl
  · refine iSup_le fun t => ?_
    refine iSup_le fun ht => ?_
    refine le_iSup_of_le (⟨t, h.le_diagK (hΓT ht)⟩ : ↥K) ?_
    rw [Subgroup.map_iSup]
    refine le_iSup_of_le (Subgroup.mem_subgroupOf.mpr ht) ?_
    rw [E111R.conjSub_subgroupOf _ hdK,
      Subgroup.map_subgroupOf_eq_of_le (E111R.conjSub_le_of_mem (h.le_diagK (hΓT ht)) hdK)]

private theorem diagK_case_diagP [Finite G] {X T A S C : Subgroup G}
    (h : E111R.DiagSetting X T A S C) [Fintype ↥C]
    (hcase : E111R.diagSub S C h.diagComm = ⁅E111R.diagSub S C h.diagComm, A⁆ ∨
      (¬ A ≤ Subgroup.normalizer (E111R.diagSub S C h.diagComm : Set G) ∧
        Nat.card ↥(E1.barRad ↥(E111R.diagK T A S C h.diagComm)
          (A.subgroupOf (E111R.diagK T A S C h.diagComm))) = 2)) :
    (E111R.diagSub S C h.diagComm).subgroupOf (E111R.diagK T A S C h.diagComm) =
        ⁅(E111R.diagSub S C h.diagComm).subgroupOf (E111R.diagK T A S C h.diagComm),
          A.subgroupOf (E111R.diagK T A S C h.diagComm)⁆ ∨
      (¬ A.subgroupOf (E111R.diagK T A S C h.diagComm) ≤ Subgroup.normalizer
        (((E111R.diagSub S C h.diagComm).subgroupOf (E111R.diagK T A S C h.diagComm) :
          Subgroup ↥(E111R.diagK T A S C h.diagComm)) :
          Set ↥(E111R.diagK T A S C h.diagComm)) ∧
        Nat.card ↥(E1.barRad ↥(E111R.diagK T A S C h.diagComm)
          (A.subgroupOf (E111R.diagK T A S C h.diagComm))) = 2) := by
  set K := E111R.diagK T A S C h.diagComm with hK
  have hdK : E111R.diagSub S C h.diagComm ≤ K := h.diag_le_diagE.trans h.diagE_le_diagK
  rcases hcase with h1 | ⟨h1, h2⟩
  · left
    rw [E111R.commutator_subgroupOf hdK h.A_le_diagK, ← h1]
  · right
    refine ⟨fun hle => h1 fun a ha => ?_, h2⟩
    have h3 := hle (Subgroup.mem_subgroupOf.mpr ha :
      (⟨a, h.A_le_diagK ha⟩ : ↥K) ∈ A.subgroupOf K)
    rw [E111R.mem_normalizer_subgroupOf_iff, inf_eq_left.mpr hdK] at h3
    exact h3

theorem eTwoPrint_diagK [Finite G] {X T A S C : Subgroup G} (h : E111R.DiagSetting X T A S C)
    [Fintype ↥C] {Γ : Subgroup G} (hΓT : Γ ≤ T ⊓ Subgroup.centralizer (A : Set G))
    (hΓX : T ⊓ Subgroup.centralizer (A : Set G) ≤ X ⊔ Γ)
    (hcase : E111R.diagSub S C h.diagComm = ⁅E111R.diagSub S C h.diagComm, A⁆ ∨
      (¬ A ≤ Subgroup.normalizer (E111R.diagSub S C h.diagComm : Set G) ∧
        Nat.card ↥(E1.barRad ↥(E111R.diagK T A S C h.diagComm)
          (A.subgroupOf (E111R.diagK T A S C h.diagComm))) = 2)) :
    UniquenessCase.UC22.F12.ETwoPrint ↥(E111R.diagK T A S C h.diagComm)
      (Γ.subgroupOf (E111R.diagK T A S C h.diagComm))
      (A.subgroupOf (E111R.diagK T A S C h.diagComm)) := by
  set K := E111R.diagK T A S C h.diagComm with hK
  set E := E111R.diagE T A S C h.diagComm with hE
  set B₀ := T ⊓ Subgroup.centralizer (A : Set G) with hB₀
  have hDK : ∀ D ∈ E111R.diagFam T A S C h.diagComm, D ≤ K := fun D hD =>
    (le_sSup hD).trans h.diagE_le_diagK
  set 𝒟' : Set (Subgroup ↥K) :=
    (fun D : Subgroup G => D.subgroupOf K) '' E111R.diagFam T A S C h.diagComm with h𝒟'
  have hsf : E111R.SemiFam 𝒟' := h.semiFam.subgroupOf hDK
  have hE' : sSup 𝒟' = E.subgroupOf K := E111R.sSup_image_subgroupOf hDK
  have hEn' : (sSup 𝒟').Normal := by rw [hE']; exact h.normal_diagE
  have hC' : IsPGroup 2 (Subgroup.centralizer ((sSup 𝒟' : Subgroup ↥K) : Set ↥K)) := by
    rw [hE']; exact diagK_centralizer_isPGroup_diagP h
  have hEB' : sSup 𝒟' ⊔ B₀.subgroupOf K = ⊤ := by
    rw [hE']; exact h.sup_subgroupOf_eq_top
  have hB₀' : IsPGroup 2 ↥(B₀.subgroupOf K) :=
    (h.isPGroup_T.to_le inf_le_left).of_equiv (Subgroup.subgroupOfEquivOfLe h.le_diagK).symm
  have hD₀' : (E111R.diagSub S C h.diagComm).subgroupOf K ∈ 𝒟' :=
    ⟨_, h.diag_mem_diagFam, rfl⟩
  have htr : ⨆ (t : ↥K) (_ : t ∈ Γ.subgroupOf K),
      A1b.conjSub t ((E111R.diagSub S C h.diagComm).subgroupOf K) = sSup 𝒟' :=
    diagK_iSup_conjSub_eq_diagP h hΓT hΓX
  have hcase' : (E111R.diagSub S C h.diagComm).subgroupOf K =
        ⁅(E111R.diagSub S C h.diagComm).subgroupOf K, A.subgroupOf K⁆ ∨
      (¬ A.subgroupOf K ≤ Subgroup.normalizer
        (((E111R.diagSub S C h.diagComm).subgroupOf K : Subgroup ↥K) : Set ↥K) ∧
        Nat.card ↥(E1.barRad ↥K (A.subgroupOf K)) = 2) :=
    diagK_case_diagP h hcase
  exact eTwoPrint_of_semiFam hsf hEn' hC' hEB' hB₀' hD₀'
    (le_rfl : Γ.subgroupOf K ≤ Γ.subgroupOf K) htr hcase'

theorem isEG_diagK [Finite G] {X T A S C : Subgroup G} (h : E111R.DiagSetting X T A S C)
    [Fintype ↥C] {n : ℕ} (hn : 1 ≤ n) {Γ : Subgroup G}
    (hΓT : Γ ≤ T ⊓ Subgroup.centralizer (A : Set G))
    (hΓX : T ⊓ Subgroup.centralizer (A : Set G) ≤ X ⊔ Γ)
    (hcase : (C ⊔ (A ⊓ Subgroup.normalizer (S : Set G)) = A ∧
        ¬ A ⊓ Subgroup.normalizer (S : Set G) ≤ Subgroup.centralizer (S : Set G) ∧
        Nat.card ↥(RonanE111.actOn S A) ≤ 2 ^ n) ∨
      (A ⊓ Subgroup.normalizer (S : Set G) ≤ Subgroup.centralizer (S : Set G) ∧
        (C ⊔ (A ⊓ Subgroup.normalizer (S : Set G))).relIndex A = 2)) :
    IsEG n ⊤ T A Γ (E111R.diagK T A S C h.diagComm) := by
  set K := E111R.diagK T A S C h.diagComm with hK
  have hτ : E1.tauOf ⊤ T A ≤ T ⊓ K :=
    (E111R.tauOf_le (E111R.pCoreOf_two_eq_bot h.red) T A).trans (le_inf inf_le_left h.le_diagK)
  refine ⟨le_top, hτ, h.isSylowIn_diagK, Or.inr ?_⟩
  rcases hcase with ⟨hA, hV, hrank⟩ | ⟨hV, hidx⟩
  · refine ⟨eTwoPrint_diagK h hΓT hΓX (Or.inl (h.diag_eq_commutator hA hV)), ?_⟩
    exact RonanE111.DiagSetting.card_barRad_le_diagK' h hA hrank
  · have h2 := h.card_barRad_diagK_eq hV hidx
    refine ⟨eTwoPrint_diagK h hΓT hΓX (Or.inr ⟨h.not_le_normalizer_diag hidx, h2⟩), ?_⟩
    rw [h2]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

theorem exists_memberG_comp [Finite G] {X T : Subgroup G}
    (hR : CFSG.Quasithin.Vol2.Ch11.SecB.E111Reduced G X T) {n : ℕ} (hn : 1 ≤ n)
    {A : Subgroup G} (hAT : A ≤ T) (hA : IsElemAbelian 2 A)
    {S : Subgroup G} (hS : E111R.IsComp X S)
    (hAS : ¬ A ≤ Subgroup.centralizer (S : Set G))
    (hrank : ¬ A ⊓ Subgroup.normalizer (S : Set G) ≤ Subgroup.centralizer (S : Set G) →
      Nat.card ↥(RonanE111.actOn S A) ≤ 2 ^ n)
    {Γ : Subgroup G} (hΓT : Γ ≤ T ⊓ Subgroup.centralizer (A : Set G))
    (hΓX : T ⊓ Subgroup.centralizer (A : Set G) ≤ X ⊔ Γ) :
    ∃ K : Subgroup G, IsEG n ⊤ T A Γ K ∧
      ∀ x ∈ S, ∃ y ∈ K, x⁻¹ * y ∈ Subgroup.centralizer (S : Set G) := by
  set V := A ⊓ Subgroup.normalizer (S : Set G) with hVdef
  obtain ⟨Z, hZA, hZV, hZVA⟩ := E111R.exists_compl hA (inf_le_left : V ≤ A)
  by_cases hV : V ≤ Subgroup.centralizer (S : Set G)
  · have hZ1 : Z ≠ ⊥ := by
      intro hZ
      rw [hZ, bot_sup_eq] at hZVA
      exact hAS (hZVA ▸ hV)
    obtain ⟨z, hzZ, hz1⟩ : ∃ z ∈ Z, z ≠ 1 := by
      by_contra hc
      push Not at hc
      exact hZ1 ((Subgroup.eq_bot_iff_forall Z).mpr hc)
    have hZe := E111R.isElemAbelian_of_le hA hZA
    obtain ⟨C, hCZ, hCz, hCzZ⟩ := E111R.exists_compl hZe (Subgroup.zpowers_le.mpr hzZ)
    have hidx := E111R.relIndex_eq_two hA hZA hZV inf_le_left hzZ hz1 hCZ hCz hCzZ hZVA
    have hset : E111R.DiagSetting X T A S C :=
      ⟨hR, hAT, hA, hS, hCZ.trans hZA, le_bot_iff.mp ((inf_le_inf_right _ hCZ).trans hZV.le)⟩
    let _ : Fintype ↥C := Fintype.ofFinite _
    exact ⟨_, isEG_diagK hset hn hΓT hΓX (Or.inr ⟨hV, hidx⟩), fun x hx => by
      obtain ⟨y, hy, hc⟩ := hset.exists_diag x hx
      exact ⟨y, hset.diag_le_diagE.trans hset.diagE_le_diagK hy, hc⟩⟩
  · have hset : E111R.DiagSetting X T A S Z := ⟨hR, hAT, hA, hS, hZA, hZV⟩
    let _ : Fintype ↥Z := Fintype.ofFinite _
    exact ⟨_, isEG_diagK hset hn hΓT hΓX (Or.inl ⟨hZVA, hV, hrank hV⟩), fun x hx => by
      obtain ⟨y, hy, hc⟩ := hset.exists_diag x hx
      exact ⟨y, hset.diag_le_diagE.trans hset.diagE_le_diagK hy, hc⟩⟩

private theorem centralizer_inf_le_tauOf_diagP {T A : Subgroup G} :
    T ⊓ Subgroup.centralizer (A : Set G) ≤ E1.tauOf ⊤ T A := by
  intro t ht
  rw [E1.mem_tauOf_of_le le_top]
  refine ⟨ht.1, fun a ha => ?_⟩
  have h1 : ⁅t, a⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.mp ht.2 a ha).symm
  rw [h1]
  exact Subgroup.one_mem _

theorem exists_memberP_comp [Finite G] {X T : Subgroup G}
    (hR : CFSG.Quasithin.Vol2.Ch11.SecB.E111Reduced G X T) {n : ℕ} (hn : 1 ≤ n)
    {A : Subgroup G} (hAT : A ≤ T) (hA : IsElemAbelian 2 A)
    {S : Subgroup G} (hS : E111R.IsComp X S)
    (hAS : ¬ A ≤ Subgroup.centralizer (S : Set G))
    (hrank : ¬ A ⊓ Subgroup.normalizer (S : Set G) ≤ Subgroup.centralizer (S : Set G) →
      Nat.card ↥(RonanE111.actOn S A) ≤ 2 ^ n) :
    ∃ K : Subgroup G, UniquenessCase.UC22.F12.IsEP n ⊤ T A K ∧
      ∀ x ∈ S, ∃ y ∈ K, x⁻¹ * y ∈ Subgroup.centralizer (S : Set G) := by
  have hΓT : E1.tauOf ⊤ T A ≤ T ⊓ Subgroup.centralizer (A : Set G) :=
    E111R.tauOf_le (E111R.pCoreOf_two_eq_bot hR) T A
  have hΓX : T ⊓ Subgroup.centralizer (A : Set G) ≤ X ⊔ E1.tauOf ⊤ T A :=
    centralizer_inf_le_tauOf_diagP.trans le_sup_right
  obtain ⟨K, hK, hKS⟩ := exists_memberG_comp hR hn hAT hA hS hAS hrank hΓT hΓX
  exact ⟨K, isEP_iff_isEG.mpr hK, hKS⟩

end CFSG.LocalAnalysis.WeakClosure81.FourFiveLayer
