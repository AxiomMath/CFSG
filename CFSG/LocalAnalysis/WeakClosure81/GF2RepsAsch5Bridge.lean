module

public import CFSG.Quasithin.Background.E3Bar
public import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
public import CFSG.GroupTheory.ABGLocalTools.PStabilityDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsE
public import CFSG.LocalAnalysis.UniquenessCase.UCFront12
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
  (InEGroup InFGroup IsOmegaColl InEOmega InFOmega genEi InCalEi ECaseI ECaseII tA normAIn)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Bar2)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (IsEP eGenP InEP ETwoPrint)
open scoped Pointwise

theorem isOmegaColl_of_isInvColl_top {G : Type} [Group G] {Ω : Set (Subgroup G)}
    (h : E1.IsInvColl (⊤ : Subgroup G) Ω) (hne : Ω.Nonempty) (hbot : ∀ A ∈ Ω, A ≠ ⊥) :
    IsOmegaColl Ω where
  nonempty := hne
  ne_bot := hbot
  elemAbelian := h.isElemAbelian
  conj A hA g := by
    rw [conjSubgroup_eq_conjSub]
    exact h.conj A hA g⁻¹ (Subgroup.mem_top _)

private theorem gf2_AschBridge_pow_mem_pCore_bar {K : Type} [Group K] [Finite K] {p : ℕ}
    (h : E1.oTwoPTwo K p = ⊤) (x : K) :
    ∃ k : ℕ, (QuotientGroup.mk' (CFSG.pCore 2 K) x) ^ 2 ^ k ∈
      CFSG.pCore p (K ⧸ CFSG.pCore 2 K) := by
  obtain ⟨k, hk⟩ := E1.exists_pow_mem_of_mem_pCore (M := E1.oTwoP K p) (fun q => by
    have hq : q ∈ E1.oTwoPTwo K p := by rw [h]; exact Subgroup.mem_top q
    exact hq) x
  refine ⟨k, ?_⟩
  rw [← map_pow]
  exact hk

theorem fittingSubgroup_bar2_eq_pCore {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : E1.oTwoPTwo K p = ⊤) :
    CFSG.fittingSubgroup (K ⧸ CFSG.pCore 2 K) = CFSG.pCore p (K ⧸ CFSG.pCore 2 K) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hN2 : IsPGroup 2 (CFSG.pPrimeCore p (K ⧸ CFSG.pCore 2 K)) := by
    intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 K) (y : K ⧸ CFSG.pCore 2 K)
    obtain ⟨k, hk⟩ := gf2_AschBridge_pow_mem_pCore_bar h x
    rw [hx] at hk
    have hmem : (y : K ⧸ CFSG.pCore 2 K) ^ 2 ^ k ∈
        CFSG.pPrimeCore p (K ⧸ CFSG.pCore 2 K) :=
      (CFSG.pPrimeCore p (K ⧸ CFSG.pCore 2 K)).pow_mem y.2 (2 ^ k)
    have hcop : Nat.Coprime (Nat.card (CFSG.pPrimeCore p (K ⧸ CFSG.pCore 2 K)))
        (Nat.card (CFSG.pCore p (K ⧸ CFSG.pCore 2 K))) := by
      obtain ⟨n, hn⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup
        (G := K ⧸ CFSG.pCore 2 K) (r := p)).exists_card_eq
      rw [hn]
      exact (CFSG.pPrimeCore_coprime_card (p := p) (G := K ⧸ CFSG.pCore 2 K)).symm.pow_right n
    have hdisj : CFSG.pPrimeCore p (K ⧸ CFSG.pCore 2 K) ⊓
        CFSG.pCore p (K ⧸ CFSG.pCore 2 K) = ⊥ :=
      Subgroup.inf_eq_bot_of_coprime hcop
    have h1 : (y : K ⧸ CFSG.pCore 2 K) ^ 2 ^ k = 1 := by
      have hb : (y : K ⧸ CFSG.pCore 2 K) ^ 2 ^ k ∈
          (⊥ : Subgroup (K ⧸ CFSG.pCore 2 K)) := by
        rw [← hdisj]
        exact ⟨hmem, hk⟩
      simpa using hb
    exact ⟨k, Subtype.ext h1⟩
  have hle : CFSG.pPrimeCore p (K ⧸ CFSG.pCore 2 K) ≤ CFSG.pCore 2 (K ⧸ CFSG.pCore 2 K) :=
    CFSG.LieType.BorelTits.le_pCore 2 (CFSG.pPrimeCore_normal) hN2
  have hbot : CFSG.pPrimeCore p (K ⧸ CFSG.pCore 2 K) = ⊥ := by
    apply le_bot_iff.mp
    exact hle.trans (le_of_eq (CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot (H := K) (p := 2)))
  exact CFSG.Fitting_eq_pcore (K ⧸ CFSG.pCore 2 K) p hbot

theorem le_tA_of_isElemAbelian {G : Type} [Group G] {T A : Subgroup G} (hAT : A ≤ T)
    (hA : IsElemAbelian 2 A) : A ≤ tA T A := by
  intro a ha
  refine (E1.mem_tauOf_of_le le_top).mpr ⟨hAT ha, fun b hb => ?_⟩
  have h := E1.commute_of_isElemAbelian hA ha hb
  rw [commutatorElement_def, h]
  simp

theorem card_barO2_subgroupOf_eq {G : Type} [Group G] {A K : Subgroup G} (hAK : A ≤ K) :
    Nat.card (E1.barO2 ↥K (A.subgroupOf K)) = (pCoreOf 2 K).relIndex A := by
  rw [E1.card_barO2_eq_relIndex]
  calc (CFSG.pCore 2 ↥K).relIndex (A.subgroupOf K)
      = ((CFSG.pCore 2 ↥K).map K.subtype).relIndex ((A.subgroupOf K).map K.subtype) :=
        (Subgroup.relIndex_map_map_of_injective _ _ K.subtype_injective).symm
    _ = (pCoreOf 2 K).relIndex A := by rw [Subgroup.map_subgroupOf_eq_of_le hAK]; rfl

theorem card_barRad_subgroupOf_eq {G : Type} [Group G] {A K : Subgroup G} (hAK : A ≤ K) :
    Nat.card (E1.barRad ↥K (A.subgroupOf K)) =
      ((CFSG.solvableRadical ↥K).map K.subtype).relIndex A := by
  have h1 := Subgroup.relIndex_ker (K := A.subgroupOf K)
    (QuotientGroup.mk' (CFSG.solvableRadical ↥K))
  rw [QuotientGroup.ker_mk'] at h1
  have h2 : ((CFSG.solvableRadical ↥K).map K.subtype).relIndex A =
      (CFSG.solvableRadical ↥K).relIndex (A.subgroupOf K) := by
    rw [← Subgroup.relIndex_map_map_of_injective (CFSG.solvableRadical ↥K) (A.subgroupOf K)
      K.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hAK]
  exact h2.symm ▸ h1.symm

theorem relIndex_le_two_pow_of_mQuot {G : Type} [Group G] [Finite G] {A U : Subgroup G} {i : ℕ}
    (hA : IsPGroup 2 A) (h : E3.mQuot A U ≤ i) : U.relIndex A ≤ 2 ^ i := by
  rw [E3.relIndex_eq_two_pow hA U]
  exact Nat.pow_le_pow_right (by norm_num) h

theorem eOne_of_eCaseI {G : Type} [Group G] [Finite G] {A K : Subgroup G} (hAK : A ≤ K)
    (hA : ¬ A ≤ pCoreOf 2 K) (h : ECaseI A K) : E1.EOne ↥K (A.subgroupOf K) := by
  obtain ⟨p, hp, hp2, hoTwo, hF, hrel⟩ := h
  haveI : Fact p.Prime := ⟨hp⟩
  have hfit := fittingSubgroup_bar2_eq_pCore (K := ↥K) hp hp2 hoTwo
  have hF' : CFSG.pCore p (Bar2 K) =
      ⁅E1.barO2 ↥K (A.subgroupOf K), CFSG.pCore p (Bar2 K)⁆ := by
    rw [hfit] at hF
    exact hF
  refine ⟨p, hp, hp2, hoTwo, ?_, ?_, ?_⟩
  · intro hbot
    have hoTwo_eq : E1.oTwoP ↥K p = CFSG.pCore 2 ↥K := by
      unfold E1.oTwoP
      rw [hbot, MonoidHom.comap_bot, QuotientGroup.ker_mk']
    have h2group : IsPGroup 2 ↥K := by
      intro q
      obtain ⟨k, hk⟩ := E1.exists_pow_mem_of_mem_pCore (M := E1.oTwoP ↥K p) (fun q => by
        have hq : q ∈ E1.oTwoPTwo ↥K p := by rw [hoTwo]; exact Subgroup.mem_top q
        exact hq) q
      rw [hoTwo_eq] at hk
      obtain ⟨j, hj⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥K) (r := 2))
        ⟨q ^ 2 ^ k, hk⟩
      refine ⟨k + j, ?_⟩
      have e : q ^ 2 ^ (k + j) = (q ^ 2 ^ k) ^ 2 ^ j := by rw [← pow_mul, ← pow_add]
      rw [e]
      simpa using congrArg Subtype.val hj
    have htop : CFSG.pCore 2 ↥K = ⊤ := by
      have hle : (⊤ : Subgroup ↥K) ≤ CFSG.pCore 2 ↥K :=
        CFSG.LieType.BorelTits.le_pCore 2 (N := ⊤) (by infer_instance) (h2group.to_subgroup ⊤)
      exact top_le_iff.mp hle
    exact hA (by
      intro a ha
      show a ∈ (CFSG.pCore 2 ↥K).map K.subtype
      rw [htop]
      exact ⟨⟨a, hAK ha⟩, Subgroup.mem_top _, rfl⟩)
  · rw [Subgroup.commutator_comm]
    exact hF'
  · exact (card_barO2_subgroupOf_eq hAK).trans hrel

theorem inf_solvableRadical_eq_inf_pCoreOf {G : Type} [Group G] [Finite G] {A K : Subgroup G}
    (hAK : A ≤ K) (hA : IsPGroup 2 A) (h : E1.IsTwoClosed (CFSG.solvableRadical ↥K)) :
    A ⊓ (CFSG.solvableRadical ↥K).map K.subtype = A ⊓ pCoreOf 2 K := by
  have hB : IsPGroup 2 (A.subgroupOf K) :=
    hA.of_equiv (Subgroup.subgroupOfEquivOfLe hAK).symm
  have hmain := E3.inf_solvableRadical_eq_inf_pCore (Q := ↥K) h hB
  have hmap := congrArg (Subgroup.map K.subtype) hmain
  rw [Subgroup.map_inf (CFSG.solvableRadical ↥K) (A.subgroupOf K) K.subtype K.subtype_injective,
    Subgroup.map_inf (CFSG.pCore 2 ↥K) (A.subgroupOf K) K.subtype K.subtype_injective,
    Subgroup.map_subgroupOf_eq_of_le hAK] at hmap
  rw [inf_comm ((CFSG.solvableRadical ↥K).map K.subtype) A,
    inf_comm ((CFSG.pCore 2 ↥K).map K.subtype) A] at hmap
  exact hmap

theorem eTwoPrint_of_eCaseII {G : Type} [Group G] [Finite G] {T A K : Subgroup G}
    (hAK : A ≤ K) (hA : IsPGroup 2 A) (h : ECaseII T A K) :
    ETwoPrint ↥K ((E1.tauOf (⊤ : Subgroup G) T A).subgroupOf K) (A.subgroupOf K) := by
  obtain ⟨h2c, hpCore, hres, L, hL, hlayer, haltern⟩ := h
  refine ⟨h2c, hpCore, hres, L, hL, hlayer, ?_⟩
  rcases haltern with hI | ⟨hrel, hnorm⟩
  · exact Or.inl hI
  · refine Or.inr ⟨?_, ?_⟩
    · intro hbar
      have hAnorm : normAIn A K L = A := by
        have hinf : A.subgroupOf K ⊓ (Subgroup.normalizer
            (L : Set (↥K ⧸ CFSG.solvableRadical ↥K))).comap
            (QuotientGroup.mk' (CFSG.solvableRadical ↥K)) = A.subgroupOf K := by
          refine le_antisymm inf_le_left ?_
          intro x hx
          exact ⟨hx, hbar (Subgroup.mem_map_of_mem
            (QuotientGroup.mk' (CFSG.solvableRadical ↥K)) hx)⟩
        unfold normAIn
        rw [hinf, Subgroup.map_subgroupOf_eq_of_le hAK]
      have hrel1 : (normAIn A K L).relIndex A = 1 := by
        rw [hAnorm, Subgroup.relIndex_self]
      rw [hrel1] at hrel
      omega
    · have h1 := inf_solvableRadical_eq_inf_pCoreOf hAK hA h2c
      have h2 : ((CFSG.solvableRadical ↥K).map K.subtype).relIndex A =
          (pCoreOf 2 K).relIndex A := by
        rw [← Subgroup.inf_relIndex_right, inf_comm, h1, inf_comm, Subgroup.inf_relIndex_right]
      rw [card_barRad_subgroupOf_eq hAK, h2,
        ← Subgroup.inf_relIndex_left (H := A) (K := pCoreOf 2 K), ← hnorm]
      exact hrel

theorem isEP_of_inCalEi {G : Type} [Group G] [Finite G] {i : ℕ} {T A K : Subgroup G}
    (hAT : A ≤ T) (hA : IsElemAbelian 2 A) (h : InCalEi i T A K) :
    IsEP i (⊤ : Subgroup G) T A K := by
  obtain ⟨⟨hτ, hsyl, hnA, hcase⟩, hm⟩ := h
  have hA2 : IsPGroup 2 A := fun g => ⟨1, Subtype.ext (by simpa using hA.2 g g.2)⟩
  have hAK : A ≤ K := (le_tA_of_isElemAbelian hAT hA).trans (hτ.trans inf_le_right)
  have hbound : (pCoreOf 2 K).relIndex A ≤ 2 ^ i := relIndex_le_two_pow_of_mQuot hA2 hm
  refine ⟨le_top, hτ, CFSG.ABGLocalTools.isSylowOf_iff.mp hsyl, ?_⟩
  rcases hcase with hI | hII
  · exact Or.inl ⟨eOne_of_eCaseI hAK hnA hI,
      (card_barO2_subgroupOf_eq hAK).trans_le hbound⟩
  · refine Or.inr ⟨eTwoPrint_of_eCaseII hAK hA2 hII, ?_⟩
    have h1 := inf_solvableRadical_eq_inf_pCoreOf hAK hA2 hII.1
    have h2 : ((CFSG.solvableRadical ↥K).map K.subtype).relIndex A = (pCoreOf 2 K).relIndex A := by
      rw [← Subgroup.inf_relIndex_right, inf_comm, h1, inf_comm, Subgroup.inf_relIndex_right]
    rw [card_barRad_subgroupOf_eq hAK, h2]
    exact hbound

theorem genEi_le_eGenP {G : Type} [Group G] [Finite G] (i : ℕ) (T : Subgroup G)
    {Ω : Set (Subgroup G)} (hΩ : IsOmegaColl Ω) :
    genEi i T Ω ≤ eGenP i (⊤ : Subgroup G) T Ω := by
  unfold genEi eGenP
  refine iSup₂_le fun A hA => iSup_le fun hAT => iSup₂_le fun K hK => ?_
  have hK' : InCalEi i T A K := hK
  have hEP : IsEP i (⊤ : Subgroup G) T A K := isEP_of_inCalEi hAT (hΩ.elemAbelian A hA) hK'
  exact le_iSup₂_of_le A hA (le_iSup_of_le hAT (le_iSup₂_of_le K hEP le_rfl))

theorem inEP_top_of_inEGroup {Q : Type} [Group Q] [Finite Q] (j : ℕ) (h : InEGroup j Q) :
    InEP j (⊤ : Subgroup Q) := by
  intro T hT Ω hΩ hne hbot
  have hΩ' : IsOmegaColl Ω := isOmegaColl_of_isInvColl_top hΩ hne hbot
  have h1 : genEi j T Ω ⊔ normalizer (E1.weakClosure T Ω : Set Q) = ⊤ := h T hT Ω hΩ'
  have h2 : genEi j T Ω ⊔ normalizer (E1.weakClosure T Ω : Set Q) ≤
      eGenP j (⊤ : Subgroup Q) T Ω ⊔ normalizer (E1.weakClosure T Ω : Set Q) :=
    sup_le_sup_right (genEi_le_eGenP j T hΩ') _
  rw [h1] at h2
  have h3 : eGenP j (⊤ : Subgroup Q) T Ω ⊔ normalizer (E1.weakClosure T Ω : Set Q) = ⊤ :=
    top_le_iff.mp h2
  rw [top_inf_eq]
  exact h3

end CFSG.LocalAnalysis.WeakClosure81
