module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.LeviInvPreSub
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.LeviInvFamilies
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.Dynkin

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.LeviUniq

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G] {P : Subgroup G}

omit [Finite G] in
theorem commutator_le_of_le {X Y : Subgroup G} (hX : X ≤ P) (hY : Y ≤ P) : ⁅X, Y⁆ ≤ P :=
  (Subgroup.commutator_mono hX hY).trans (Subgroup.commutator_le_self P)

theorem tits_barSub {d : ℕ} {L : Fin d → Subgroup G} (hL : IsLeviFamily P d L) (i : Fin d)
    (N : Subgroup (Bar2 P)) (hN : N.Normal) (hNL : N ≤ barSub P (L i))
    (hc : ⁅N, barSub P (L i)⁆ ≠ ⊥) : S17.oUpperTwo (barSub P (L i)) ≤ N := by
  have hN'P : preSub P N ≤ P := preSub_le N
  have hN'L : preSub P N ≤ L i :=
    (barSub_le_iff hN'P (hL.pCoreOf_le i) (hL.le i)).mp (by rw [barSub_preSub]; exact hNL)
  have hN'n : ((preSub P N).subgroupOf (L i)).Normal := by
    have h1 := preSub_normal hN
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hN'P] at h1
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hN'L).mpr ((hL.le i).trans h1)
  have hnot : ¬ ⁅preSub P N, L i⁆ ≤ pCoreOf 2 P := by
    intro h
    apply hc
    rw [← barSub_preSub N, ← barSub_commutator hN'P (hL.le i)]
    exact (barSub_eq_bot_iff (commutator_le_of_le hN'P (hL.le i))).mpr h
  have := hL.tits i (preSub P N) (pCoreOf_le_preSub N) hN'L hN'n hnot
  rw [← barSub_oUpperTwo (hL.le i), ← barSub_preSub N]
  exact barSub_mono this

theorem preSub_eq_opp_sup {C : Subgroup (Bar2 P)} (hC : Opp 2 C = C) :
    preSub P C = Opp 2 (preSub P C) ⊔ pCoreOf 2 P := by
  have hO : pCoreOf 2 P ≤ P := Subgroup.map_subtype_le _
  have hopp : Opp 2 (preSub P C) ≤ P := (opp_le _).trans (preSub_le C)
  refine le_antisymm ?_ (sup_le (opp_le _) (pCoreOf_le_preSub C))
  refine (barSub_le_iff (preSub_le C) le_sup_right (sup_le hopp hO)).mp ?_
  rw [barSub_sup hopp hO, barSub_pCoreOf, sup_bot_eq, barSub_opp (preSub_le C), barSub_preSub, hC]

theorem ind_barSub {K : Subgroup G} (hOK : pCoreOf 2 P ≤ K) (hKP : K ≤ P)
    (hind : ∀ A B : Subgroup G, pCoreOf 2 P ≤ A → pCoreOf 2 P ≤ B →
      A = Opp 2 A ⊔ pCoreOf 2 P → B = Opp 2 B ⊔ pCoreOf 2 P → A ⊔ B = K →
      ⁅A, B⁆ ≤ pCoreOf 2 P → A = K ∨ B = K)
    (A B : Subgroup (Bar2 P)) (hA : Opp 2 A = A) (hB : Opp 2 B = B)
    (hAB : A ⊔ B = barSub P K) (hc : ⁅A, B⁆ = ⊥) :
    A = barSub P K ∨ B = barSub P K := by
  have hsup : preSub P A ⊔ preSub P B = K := by
    refine barSub_inj (le_sup_of_le_left (pCoreOf_le_preSub A))
      (sup_le (preSub_le A) (preSub_le B)) hOK hKP ?_
    rw [barSub_sup (preSub_le A) (preSub_le B), barSub_preSub, barSub_preSub, hAB]
  have hcomm : ⁅preSub P A, preSub P B⁆ ≤ pCoreOf 2 P := by
    rw [← barSub_eq_bot_iff (commutator_le_of_le (preSub_le A) (preSub_le B)),
      barSub_commutator (preSub_le A) (preSub_le B), barSub_preSub, barSub_preSub, hc]
  rcases hind _ _ (pCoreOf_le_preSub A) (pCoreOf_le_preSub B) (preSub_eq_opp_sup hA)
      (preSub_eq_opp_sup hB) hsup hcomm with h | h
  · left
    rw [← h, barSub_preSub]
  · right
    rw [← h, barSub_preSub]

omit [Finite G] in
theorem isTwoElt_of_mem_pCoreOf {x : G} (hx : x ∈ pCoreOf 2 P) : IsTwoElt x := by
  obtain ⟨k, hk⟩ := ((CFSG.pCore_isPGroup (p := 2) (G := ↥P)).map P.subtype) ⟨x, hx⟩
  exact isTwoElt_iff_pow.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩

omit [Finite G] in
theorem opp_eq_of_eq_opp_sup {X : Subgroup G} (hOX : pCoreOf 2 P ≤ X)
    (hX : X = Opp 2 X ⊔ pCoreOf 2 P) : Opp 2 X = X := by
  refine le_antisymm (opp_le X) ?_
  conv_lhs => rw [hX]
  exact sup_le le_rfl fun x hx => mem_opp_of_isTwoElt (hOX hx) (isTwoElt_of_mem_pCoreOf hx)

theorem exists_equiv_of_isDynkinFamilyIn_gen {M Dsub : Subgroup G} {d : ℕ}
    {L : Fin d → Subgroup G} (hL : IsLeviFamily (Dsub ⊓ M) d L) {d' : ℕ}
    {K J : Fin d' → Subgroup G} (hKJ : S19.IsDynkinFamilyIn M Dsub d' K J) :
    ∃ σ : Fin d' ≃ Fin d, ∀ k, K k = L (σ k) := by
  obtain ⟨hbasic, hcomm, hiSup, hindec, hJ⟩ := hKJ
  have hKP : ∀ k, K k ≤ Dsub ⊓ M := fun k => (hbasic k).2.1
  have hOK : ∀ k, pCoreOf 2 (Dsub ⊓ M) ≤ K k := fun k => (hbasic k).1
  have hTF : TwoFamilies (fun i => barSub (Dsub ⊓ M) (L i))
      (fun k => barSub (Dsub ⊓ M) (K k)) :=
    { hO2 := hO2_bar2
      Ln := fun i => barSub_normal (hL.normal i)
      Kn := fun k => barSub_normal (hbasic k).2.2.1
      L2 := fun i => by rw [← barSub_opp (hL.le i), hL.opp_eq i]
      K2 := fun k => by rw [← barSub_opp (hKP k), opp_eq_of_eq_opp_sup (hOK k) (hbasic k).2.2.2.1]
      L0 := fun i h => hL.ne i (le_antisymm ((barSub_eq_bot_iff (hL.le i)).mp h) (hL.pCoreOf_le i))
      K0 := fun k h => (hbasic k).2.2.2.2 (by
        rw [hJ k]
        exact (S17.oUpperTwo_le _).trans ((barSub_eq_bot_iff (hKP k)).mp h))
      Lc := fun i i' h => by
        rw [← barSub_commutator (hL.le i) (hL.le i')]
        exact (barSub_eq_bot_iff (commutator_le_of_le (hL.le i) (hL.le i'))).mpr
          (hL.commutator_le i i' h)
      Kc := fun k k' h => by
        rw [← barSub_commutator (hKP k) (hKP k')]
        exact (barSub_eq_bot_iff (commutator_le_of_le (hKP k) (hKP k'))).mpr (hcomm k k' h)
      LK := by rw [← barSub_iSup hL.le, ← barSub_iSup hKP, hL.iSup_eq, hiSup]
      tits := tits_barSub hL
      ind := fun k A B hA hB hAB hc => ind_barSub (hOK k) (hKP k) (hindec k) A B hA hB hAB hc }
  obtain ⟨σ, hσ⟩ := hTF.exists_equiv
  exact ⟨σ, fun k => barSub_inj (hOK k) (hKP k) (hL.pCoreOf_le _) (hL.le _) (hσ k)⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.LeviUniq

end
