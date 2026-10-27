module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.TwoQuotientTransfers
public import CFSG.GroupTheory.PermutesConjSupNoncyclic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.GroupTheory
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_of_noncentral_three_of_pow {D : Data G} {V₀ V : Subgroup G}
    {hV : Hyp125 D V₀ V}
    (h17_1 : R17_1At D V₀ V hV) (hk : D.k = 1) {L : Subgroup G} (hL : L ∈ calC D.M)
    {n : ℕ}
    (hpow : ∀ s ∈ S1Nine D L, s ^ n ∈ Subgroup.centralizer (K1Nine D L : Set (Mbar9 D)))
    (hK : ∀ (Y : Type) [Group Y] [Finite Y] (K S : Subgroup Y), Inputs1719.KYForm Y K S →
      Nonempty (↥K ≃* Bar2 L) → (∀ s ∈ S, s ^ n = 1) →
      ∃ E : Subgroup Y, E ≤ K ∧ E ≠ ⊥ ∧ IsPGroup 3 ↥E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧
        ¬ E ≤ (Subgroup.center ↥K).map K.subtype ∧ Permutes E S) :
    D.T ≤ Subgroup.normalizer (L : Set G) := by
  by_contra hNT
  obtain ⟨E, hEK, hEne, hEp, hEexp, hEnc, hEperm⟩ :=
    exists_noncentral_three_K1Nine_of_pow hL hpow hK
  have hKne : ∃ t ∈ Tbar9 D,
      (K1Nine D L).map (MulAut.conj t).toMonoidHom ≠ K1Nine D L := by
    by_contra h
    have hnorm : Tbar9 D ≤ Subgroup.normalizer (K1Nine D L : Set (Mbar9 D)) := by
      intro t ht
      by_contra hne
      exact h ⟨t, ht, (Subgroup.mem_normalizer_iff_map_conj_eq).not.mp hne⟩
    exact hNT (le_normalizer_of_le_normalizer_imageOTwoQuot hL hnorm)
  obtain ⟨Xbar, hE_le_Xbar, hXbarT, hXbarExp, hXbarP, hXbarNcyc⟩ :=
    exists_noncyclic_permutes_sup_conj (H := Mbar9 D) (K := K1Nine D L) (T := Tbar9 D) (A := E)
      hEK (commute_of_ne_conj_K1Nine hL) hEperm hKne hEnc hEexp
  have hXbarNe : Xbar ≠ ⊥ := by
    intro hbot
    exact hEne (le_bot_iff.mp (hbot ▸ hE_le_Xbar))
  have hTsub2 : IsPGroup 2 (D.T.subgroupOf D.M) := D.sylowM.isPGroup.comap_subtype (K := D.M)
  have hker : (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥D.M)).ker ≤ D.T.subgroupOf D.M := by
    rw [show (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥D.M)).ker = CFSG.Open.pCore 2 ↥D.M from
      QuotientGroup.ker_mk' _]
    exact Subgroup.map_le_iff_le_comap.mp (s16c7_pCoreOf_le_of_isSylowOf D.sylowM)
  have hSmap : (D.T.subgroupOf D.M).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥D.M)) =
      Tbar9 D := rfl
  obtain ⟨P, hP3, hPmap, ⟨eP⟩, hPperm⟩ :=
    CFSG.GroupTheory.exists_permutes_lift (p := 3)
      (f := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥D.M))
      (QuotientGroup.mk'_surjective _) hTsub2 hker (by norm_num : (3 : ℕ) ≠ 2)
      (hXbarP 3 hEp) (by rw [hSmap]; exact hXbarT)
  have hPne : P ≠ ⊥ := by
    intro hPbot
    have hcard : Nat.card Xbar = 1 := by
      have h := Nat.card_congr eP.toEquiv
      rw [hPbot, Subgroup.card_bot] at h
      exact h.symm
    exact hXbarNe ((Subgroup.card_eq_one).mp hcard)
  have hPexp : ∀ x ∈ P.map D.M.subtype, x ^ 3 = 1 := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hz
    have hy3 : (⟨y, hy⟩ : ↥P) ^ 3 = 1 := by
      apply eP.injective
      rw [map_pow, map_one]
      exact Subtype.ext (by simpa using hXbarExp 3 hEexp _ (eP ⟨y, hy⟩).2)
    simpa using congrArg (fun z : ↥P => ((z : ↥D.M) : G)) hy3
  have hPnc : ¬ IsCyclic ↥(P.map D.M.subtype) := by
    intro hcyc
    have hPcyc : IsCyclic ↥P := by
      let e := Subgroup.equivMapOfInjective P D.M.subtype Subtype.val_injective
      exact @isCyclic_of_surjective ↥P ↥(P.map D.M.subtype) _ _
        (↥(P.map D.M.subtype) ≃* ↥P) hcyc _ _ e.symm e.symm.surjective
    exact hXbarNcyc (@isCyclic_of_surjective ↥Xbar ↥P _ _ (↥P ≃* ↥Xbar) hPcyc _ _ eP
      eP.surjective)
  have hPpermG : Permutes (P.map D.M.subtype) D.T := by
    have hDT : ((D.T.subgroupOf D.M).map D.M.subtype : Set G) = (D.T : Set G) :=
      congrArg (fun H : Subgroup G => (H : Set G)) (Subgroup.map_subgroupOf_eq_of_le D.sylowM.le)
    have hXcoe : (P.map D.M.subtype : Set G) = D.M.subtype '' (P : Set ↥D.M) := rfl
    have hScoe : ((D.T.subgroupOf D.M).map D.M.subtype : Set G) =
        D.M.subtype '' (D.T.subgroupOf D.M : Set ↥D.M) := rfl
    show ((P.map D.M.subtype : Subgroup G) : Set G) * (D.T : Set G) =
      (D.T : Set G) * ((P.map D.M.subtype : Subgroup G) : Set G)
    rw [hXcoe, ← hDT, hScoe, ← Set.image_mul, ← Set.image_mul, hPperm]
  exact false_of_k_eq_one_of_permutes h17_1 hk
    ⟨P.map D.M.subtype, Subgroup.map_subtype_le P,
      fun hbot => hPne (by
        refine Subgroup.map_injective (f := D.M.subtype) Subtype.val_injective ?_
        simpa using hbot),
      hP3.map D.M.subtype, hPexp, hPnc, hPpermG⟩

theorem le_normalizer_of_noncentral_three {D : Data G} {V₀ V : Subgroup G} {hV : Hyp125 D V₀ V}
    (h17_1 : R17_1At D V₀ V hV) (hk : D.k = 1) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hK : ∀ (Y : Type) [Group Y] [Finite Y] (K S : Subgroup Y), Inputs1719.KYForm Y K S →
      Nonempty (↥K ≃* Bar2 L) →
      ∃ E : Subgroup Y, E ≤ K ∧ E ≠ ⊥ ∧ IsPGroup 3 ↥E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧
        ¬ E ≤ (Subgroup.center ↥K).map K.subtype ∧ Permutes E S) :
    D.T ≤ Subgroup.normalizer (L : Set G) :=
  le_normalizer_of_noncentral_three_of_pow h17_1 hk hL (n := 0) (fun _ _ => by simp)
    (fun Y _ _ K S hKY hKe _ => hK Y K S hKY hKe)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
