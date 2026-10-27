module

public import CFSG.LocalAnalysis.UniquenessCase.UC22KHi2a
public import CFSG.LocalAnalysis.UniquenessCase.UC22KHi2r
public import CFSG.LocalAnalysis.UniquenessCase.UC22KHi2p

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open P22x P22s

variable {G : Type} [Group G] [Finite G]

namespace P22k2

theorem fr_preMbar_mono (D : Data G) {Y Z : Subgroup (MBar D.M D.U)} (h : Y ≤ Z) :
    preMbar D Y ≤ preMbar D Z := fun x hx => by
  obtain ⟨hxM, hxY⟩ := (mem_preMbar D).1 hx
  exact (mem_preMbar D).2 ⟨hxM, h hxY⟩

theorem fr_T1_le_normalizer_rI (D : Data G) {Y : Subgroup (MBar D.M D.U)}
    (hY : Y ≤ mbarImage D.M D.U (proofN D)) :
    T1 D Y ≤ normalizer ((rad118 D ⊓ preMbar D Y : Subgroup G) : Set G) := fun _ hx =>
  mem_normalizer_inf (M_le_normalizer_rad118 D (T1_le_M D Y hx)) (T1_le_normalizer_preMbar D hY hx)

theorem fr_T_inf_le_T1 (D : Data G) (Y : Subgroup (MBar D.M D.U)) :
    D.T ⊓ (rad118 D ⊓ preMbar D Y) ≤ T1 D Y := fun x hx => by
  obtain ⟨hxT, -, hxY⟩ := hx
  obtain ⟨hxM, hxb⟩ := (mem_preMbar D).1 hxY
  exact ⟨hxT, mem_normalizer_preN D hxM (Subgroup.le_normalizer hxb)⟩

theorem fr_isSylowOf_T_inf (D : Data G) {Y : Subgroup (MBar D.M D.U)}
    (hY : Y ≤ mbarImage D.M D.U (proofN D))
    (hNY : ∀ g ∈ mbarImage D.M D.U (proofN D), g ∈ normalizer (Y : Set (MBar D.M D.U))) :
    CFSG.ABGLocalTools.IsSylowOf 2 (D.T ⊓ (rad118 D ⊓ preMbar D Y)) (rad118 D ⊓ preMbar D Y) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hNbn : (mbarImage D.M D.U (proofN D)).Normal :=
    uc22br4_mbarImage_normal D.M D.U (proofN D) (uc22p22e_jOf_le_self D.M) (uc22p22t_M_le_normalizer_jOf D)
  have hRNM : rad118 D ⊓ preMbar D (mbarImage D.M D.U (proofN D)) ≤ D.M := inf_le_left.trans (rad118_le_M D)
  have hMRN : D.M ≤ normalizer ((rad118 D ⊓ preMbar D (mbarImage D.M D.U (proofN D)) : Subgroup G) : Set G) :=
    fun x hx => mem_normalizer_inf (M_le_normalizer_rad118 D hx)
      (mem_normalizer_preMbar D hx (by rw [normalizer_eq_top]; exact Subgroup.mem_top _))
  have h1 := D.sylowM.inf_of_le_normalizer hRNM hMRN
  have hle : rad118 D ⊓ preMbar D Y ≤ rad118 D ⊓ preMbar D (mbarImage D.M D.U (proofN D)) :=
    inf_le_inf_left _ (fr_preMbar_mono D hY)
  have hnorm : rad118 D ⊓ preMbar D (mbarImage D.M D.U (proofN D)) ≤
      normalizer ((rad118 D ⊓ preMbar D Y : Subgroup G) : Set G) := fun x hx => by
    obtain ⟨hxM, hxb⟩ := (mem_preMbar D).1 hx.2
    exact mem_normalizer_inf (M_le_normalizer_rad118 D hxM) (mem_normalizer_preMbar D hxM (hNY _ hxb))
  have h2 := h1.inf_of_le_normalizer hle hnorm
  rwa [inf_assoc, inf_eq_right.2 hle] at h2

theorem fr_not_two_dvd_relIndex (D : Data G) {Y : Subgroup (MBar D.M D.U)}
    (hY : Y ≤ mbarImage D.M D.U (proofN D))
    (hNY : ∀ g ∈ mbarImage D.M D.U (proofN D), g ∈ normalizer (Y : Set (MBar D.M D.U))) :
    ¬ 2 ∣ (T1 D Y).relIndex ((rad118 D ⊓ preMbar D Y) ⊔ T1 D Y) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsyl := fr_isSylowOf_T_inf D hY hNY
  have heq : T1 D Y ⊓ (rad118 D ⊓ preMbar D Y) = D.T ⊓ (rad118 D ⊓ preMbar D Y) :=
    le_antisymm (inf_le_inf_right _ (T1_le_T D Y)) (le_inf (fr_T_inf_le_T1 D Y) inf_le_right)
  rw [← heq] at hsyl
  exact not_two_dvd_relIndex_sup (fr_T1_le_normalizer_rI D hY) (CFSG.ABGLocalTools.isSylowOf_iff.1 hsyl).2.2

theorem fr_le_normalizer_of_le_sup (D : Data G) {Y : Subgroup (MBar D.M D.U)}
    (hY : Y ≤ mbarImage D.M D.U (proofN D)) {V₀ : Subgroup G}
    (hnorm : ∀ x ∈ D.M, x ∈ normalizer (preN D Y : Set G) → x ∈ normalizer (V₀ : Set G))
    {P : Subgroup G} (hPR : P ≤ (rad118 D ⊓ preMbar D Y) ⊔ T1 D Y) : P ≤ normalizer (V₀ : Set G) := by
  intro x hx
  obtain ⟨ρ, hρ, t, ht, rfl⟩ := exists_mul_of_mem_sup (fr_T1_le_normalizer_rI D hY) (hPR hx)
  obtain ⟨hρM, hρb⟩ := (mem_preMbar D).1 hρ.2
  exact mul_mem (hnorm ρ hρM (mem_normalizer_preN D hρM (Subgroup.le_normalizer hρb)))
    (hnorm t (T1_le_M D Y ht) (T1_le_normalizer_preN D Y ht))

theorem fr_pCoreOf_le_preMbar (D : Data G) (Y : Subgroup (MBar D.M D.U)) :
    pCoreOf 2 D.M ≤ preMbar D Y := by
  have hU := (uCore_le_and_isElemAbelian D.standing.charTwo D.maxLocal.1 D.sylowM).1
  intro q hq
  have hqM : q ∈ D.M := CFSG.LieType.BorelTits.pCoreOf_le 2 D.M hq
  have hqC : q ∈ centralizer (D.U : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (Subgroup.mem_centralizer_iff.1 (hU hu).2 q hq).symm
  refine (mem_preMbar D).2 ⟨hqM, ?_⟩
  rw [(uc22br_gt_mk_eq_one_iff (uc22p22xf_hV D) ⟨q, hqM⟩).2 hqC]
  exact Y.one_mem

theorem fr_fstar (D : Data G) {Y : Subgroup (MBar D.M D.U)}
    (hY : Y ≤ mbarImage D.M D.U (proofN D)) {P : Subgroup G} (hle : T1 D Y ≤ P)
    (hPR : P ≤ (rad118 D ⊓ preMbar D Y) ⊔ T1 D Y) :
    P ⊓ centralizer (pCoreOf 2 P : Set G) ≤ pCoreOf 2 P := by
  have hPM : P ≤ D.M := hPR.trans (sup_le (inf_le_left.trans (rad118_le_M D)) (T1_le_M D Y))
  have hA : (P ⊓ preMbar D Y) ⊔ T1 D Y = P := by
    refine le_antisymm (sup_le inf_le_left hle) fun x hx => ?_
    obtain ⟨ρ, hρ, t, ht, rfl⟩ := exists_mul_of_mem_sup (fr_T1_le_normalizer_rI D hY) (hPR hx)
    refine mul_mem_sup ⟨?_, hρ.2⟩ ht
    simpa using mul_mem hx (inv_mem (hle ht))
  have h := uc22p22s_centralizer_pCore_sup_le (M := D.M) (N := D.M) (Ni := P ⊓ preMbar D Y) (S := T1 D Y)
    (D.standing.charTwo D.M D.maxLocal.1) le_rfl Subgroup.le_normalizer (inf_le_left.trans hPM)
    (fun x hx => ⟨hle (pCoreOf_le_T1 D Y hx.1), fr_pCoreOf_le_preMbar D Y hx.1⟩)
    (isPGroup_T1 D Y) (T1_le_M D Y)
    (fun x hx => mem_normalizer_inf' (Subgroup.le_normalizer (hle hx)) (T1_le_normalizer_preMbar D hY hx))
  rwa [hA] at h

theorem exists_s3Frame (D : Data G) {Y : Subgroup (MBar D.M D.U)}
    (hY : Y ≤ mbarImage D.M D.U (proofN D))
    (hNY : ∀ g ∈ mbarImage D.M D.U (proofN D), g ∈ normalizer (Y : Set (MBar D.M D.U)))
    {V₀ : Subgroup G} (hV₀U : V₀ ≤ D.U) (hel : IsElemAbelian 2 V₀) (hcard : Nat.card V₀ = 4)
    (hnorm : ∀ x ∈ D.M, x ∈ normalizer (preN D Y : Set G) → x ∈ normalizer (V₀ : Set G))
    (hSle : proofS D ≤ T1 D Y) (hSact : ¬ proofS D ≤ centralizer (V₀ : Set G))
    {r : G} (hr : r ∈ rad118 D) (hrY : r ∈ preMbar D Y)
    (hr3 : ActsOrdThree V₀ r) :
    ∃ P : Subgroup G, S3Frame P (T1 D Y) V₀ ∧ P ≤ (rad118 D ⊓ preMbar D Y) ⊔ T1 D Y := by
  let F : Set (Subgroup G) :=
    {X | T1 D Y ≤ X ∧ X ≤ (rad118 D ⊓ preMbar D Y) ⊔ T1 D Y ∧ ∃ x ∈ X, ActsOrdThree V₀ x}
  have hX₀ : zpowers r ⊔ T1 D Y ∈ F :=
    ⟨le_sup_right, sup_le (zpowers_le.2 (mem_sup_left ⟨hr, hrY⟩)) le_sup_right, r,
      mem_sup_left (mem_zpowers r), hr3⟩
  obtain ⟨P, ⟨hle, hPR, hord⟩, hPmin⟩ := wellFounded_lt.has_min F ⟨_, hX₀⟩
  have hU := (uCore_le_and_isElemAbelian D.standing.charTwo D.maxLocal.1 D.sylowM).1
  refine ⟨P, ?_, hPR⟩
  exact
    { le := hle
      pgroup := isPGroup_T1 D Y
      odd := fun h => fr_not_two_dvd_relIndex D hY hNY
        (h.trans (Dvd.intro _ (Subgroup.relIndex_mul_relIndex _ _ _ hle hPR)))
      v₀le := fun v hv => hle (pCoreOf_le_T1 D Y (hU (hV₀U hv)).1)
      norm := fr_le_normalizer_of_le_sup D hY hnorm hPR
      elem := hel
      card := hcard
      act := fun h => hSact (hSle.trans h)
      ord3 := hord
      minimal := fun X hTX hXP hXord => by
        by_contra hne
        exact hPmin X ⟨hTX, hXP.trans hPR, hXord⟩ (lt_of_le_of_ne hXP hne)
      fstar := fr_fstar D hY hle hPR }

end P22k2

end CFSG.LocalAnalysis.UniquenessCase.UC22
