module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFactsNineteenR
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22u
public import CFSG.GroupTheory.PGroup.LtInfNormalizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LieType.BorelTits
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem w7_9_1_4_normalizer_pCore_le {G : Type} [Group G] [Finite G]
    {M I X Y : Subgroup G}
    (hIM : I ≤ M) (hIn : (I.subgroupOf M).Normal) (hXM : X ≤ M)
    (heta : ∀ R : Subgroup G, R ≤ M → IsPGroup 2 R → X ≤ normalizer (R : Set G) →
      pCoreOf 2 I ≤ R → calMOf (M ⊓ normalizer (R : Set G)) = {M})
    (hYM : Y ≤ M) (hY : Y = X ⊔ pCoreOf 2 Y) (hYne : pCoreOf 2 Y ≠ ⊥)
    (hmax : ∀ Z : Subgroup G, Z ≤ M → Z = X ⊔ pCoreOf 2 Z → pCoreOf 2 Z ≠ ⊥ →
      calMOf Z ≠ {M} → Y ≤ Z → Z = Y) :
    normalizer (pCoreOf 2 Y : Set G) ≤ M := by
  classical
  have hRp : IsPGroup 2 (pCoreOf 2 Y) := pCoreOf_isPGroup 2 Y
  have hRM : pCoreOf 2 Y ≤ M := (pCoreOf_le 2 Y).trans hYM
  have hXY : X ≤ Y := by rw [hY]; exact le_sup_left
  have hXN : X ≤ normalizer (pCoreOf 2 Y : Set G) :=
    hXY.trans (le_normalizer_pCoreOf 2 Y)
  have hMnormI : M ≤ normalizer (I : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hIM).mp hIn
  have hMnormCore : M ≤ normalizer (pCoreOf 2 I : Set G) :=
    hMnormI.trans (normalizer_le_normalizer_pCoreOf 2 I)
  have hIcoreM : pCoreOf 2 I ≤ M := (pCoreOf_le 2 I).trans hIM
  have hIcorep : IsPGroup 2 (pCoreOf 2 I) := pCoreOf_isPGroup 2 I
  obtain ⟨S, hRleS, hSmax⟩ := Finite.exists_le_maximal
    (α := Subgroup G) (p := fun S : Subgroup G =>
      S ≤ M ∧ IsPGroup 2 S ∧ X ≤ normalizer (S : Set G))
    ⟨hRM, hRp, hXN⟩
  have hSp : IsPGroup 2 S := hSmax.prop.2.1
  have hSM : S ≤ M := hSmax.prop.1
  have hXNS : X ≤ normalizer (S : Set G) := hSmax.prop.2.2
  have hsupM : S ⊔ pCoreOf 2 I ≤ M := sup_le hSM hIcoreM
  have hsupp : IsPGroup 2 ((S ⊔ pCoreOf 2 I : Subgroup G)) :=
    IsPGroup.to_sup_of_normal_right' hSp hIcorep (hSM.trans hMnormCore)
  have hsupN : X ≤ normalizer (((S ⊔ pCoreOf 2 I : Subgroup G)) : Set G) :=
    (le_inf hXNS (hXM.trans hMnormCore)).trans
      (Subgroup.inf_normalizer_le_normalizer_sup S (pCoreOf 2 I))
  have hsupLe : S ⊔ pCoreOf 2 I ≤ S := hSmax.2 ⟨hsupM, hsupp, hsupN⟩ le_sup_left
  have hcoreS : pCoreOf 2 I ≤ S := le_sup_right.trans hsupLe
  obtain ⟨N', hN'max, hN'ge⟩ := uc22p22u_exists_isMaxTwoLocal
    (G := G) (H := normalizer (pCoreOf 2 Y : Set G))
    ⟨pCoreOf 2 Y, hYne, hRp, rfl⟩
  by_cases hRS : pCoreOf 2 Y = S
  · have hcoreR : pCoreOf 2 I ≤ pCoreOf 2 Y := by rw [hRS]; exact hcoreS
    have hetaR := heta (pCoreOf 2 Y) hRM hRp hXN hcoreR
    have hmem : N' ∈ calMOf (M ⊓ normalizer (pCoreOf 2 Y : Set G)) :=
      ⟨hN'max, inf_le_right.trans hN'ge⟩
    rw [hetaR] at hmem
    have hN'eq : N' = M := by simpa using hmem
    simpa [hN'eq] using hN'ge
  · have hRlt : pCoreOf 2 Y < S := lt_of_le_of_ne hRleS hRS
    have hRQlt : pCoreOf 2 Y < S ⊓ normalizer (pCoreOf 2 Y : Set G) :=
      CFSG.GroupTheory.lt_inf_normalizer_of_isPGroup hSp hRlt
    set Q : Subgroup G := S ⊓ normalizer (pCoreOf 2 Y : Set G) with hQdef
    set Z : Subgroup G := X ⊔ Q with hZdef
    have hQS : Q ≤ S := by rw [hQdef]; exact inf_le_left
    have hQp : IsPGroup 2 Q := hSp.to_le hQS
    have hQM : Q ≤ M := hQS.trans hSM
    have hQN : Q ≤ normalizer (pCoreOf 2 Y : Set G) := by
      rw [hQdef]; exact inf_le_right
    have hYZ : Y ≤ Z := by
      rw [hZdef, hY]
      exact sup_le_sup_left hRQlt.le X
    have hQZ : Q ≤ Z := by rw [hZdef]; exact le_sup_right
    have hXMZ : X ≤ Z := by rw [hZdef]; exact le_sup_left
    have hZM : Z ≤ M := by rw [hZdef]; exact sup_le hXM hQM
    have hZNQ : Z ≤ normalizer (Q : Set G) := by
      rw [hZdef]
      have hXNN : X ≤ normalizer (normalizer (pCoreOf 2 Y : Set G) : Set G) :=
        hXN.trans Subgroup.le_normalizer
      exact sup_le
        ((le_inf hXNS hXNN).trans
          (Subgroup.inf_normalizer_le_normalizer_inf
            (H := S) (K := normalizer (pCoreOf 2 Y : Set G))))
        Subgroup.le_normalizer
    have hQcore : Q ≤ pCoreOf 2 Z :=
      le_pCoreOf_of_le_normalizer 2 hQZ hZNQ hQp
    have hZdecomp : Z = X ⊔ pCoreOf 2 Z := by
      refine le_antisymm ?_ ?_
      · calc Z = X ⊔ Q := hZdef
          _ ≤ X ⊔ pCoreOf 2 Z := sup_le_sup_left hQcore X
      · exact sup_le hXMZ (pCoreOf_le 2 Z)
    have hZne : pCoreOf 2 Z ≠ ⊥ := by
      intro hbot
      apply hYne
      have hle : pCoreOf 2 Y ≤ ⊥ := hbot ▸ (hRQlt.le.trans hQcore)
      exact le_bot_iff.mp hle
    have hcalZ : calMOf Z = {M} := by
      by_contra hne
      have hZY : Z = Y := hmax Z hZM hZdecomp hZne hne hYZ
      have hQY : Q ≤ Y := by rw [← hZY]; exact hQZ
      have hYNQ : Y ≤ normalizer (Q : Set G) := by rw [← hZY]; exact hZNQ
      have hQleR : Q ≤ pCoreOf 2 Y :=
        le_pCoreOf_of_le_normalizer 2 hQY hYNQ hQp
      exact (not_le_of_gt hRQlt) hQleR
    have hZleN' : Z ≤ N' := by
      rw [hZdef]
      exact sup_le (hXN.trans hN'ge) (hQN.trans hN'ge)
    have hmem : N' ∈ calMOf Z := ⟨hN'max, hZleN'⟩
    rw [hcalZ] at hmem
    have hN'eq : N' = M := by simpa using hmem
    simpa [hN'eq] using hN'ge

theorem w7_9_1_4_le_pCore_of_le_normalizer {G : Type} [Group G] [Finite G]
    {M X Y H Q : Subgroup G}
    (hYM : Y ≤ M) (hY : Y = X ⊔ pCoreOf 2 Y) (hYne : pCoreOf 2 Y ≠ ⊥)
    (hN : normalizer (pCoreOf 2 Y : Set G) ≤ M)
    (hmax : ∀ Z : Subgroup G, Z ≤ M → Z = X ⊔ pCoreOf 2 Z → pCoreOf 2 Z ≠ ⊥ →
      calMOf Z ≠ {M} → Y ≤ Z → Z = Y)
    (hYH : Y ≤ H) (hHM : ¬ H ≤ M) (hHne : pCoreOf 2 H ≠ ⊥)
    (hQp : IsPGroup 2 Q) (hRQ : pCoreOf 2 Y ≤ Q) (hQH : Q ≤ H)
    (hQN : Q ≤ normalizer (pCoreOf 2 Y : Set G))
    (hYQ : Y ≤ normalizer (Q : Set G)) :
    Q ≤ pCoreOf 2 Y := by
  classical
  have hQM : Q ≤ M := hQN.trans hN
  set Z : Subgroup G := Y ⊔ Q with hZdef
  have hYZ : Y ≤ Z := by rw [hZdef]; exact le_sup_left
  have hQZ : Q ≤ Z := by rw [hZdef]; exact le_sup_right
  have hZM : Z ≤ M := by rw [hZdef]; exact sup_le hYM hQM
  have hZNQ : Z ≤ normalizer (Q : Set G) := by
    rw [hZdef]; exact sup_le hYQ Subgroup.le_normalizer
  have hQcore : Q ≤ pCoreOf 2 Z := le_pCoreOf_of_le_normalizer 2 hQZ hZNQ hQp
  have hZdecomp : Z = X ⊔ pCoreOf 2 Z := by
    refine le_antisymm ?_ ?_
    · calc Z = Y ⊔ Q := hZdef
        _ = (X ⊔ pCoreOf 2 Y) ⊔ Q := congrArg (fun T : Subgroup G => T ⊔ Q) hY
        _ = X ⊔ (pCoreOf 2 Y ⊔ Q) := by rw [sup_assoc]
        _ = X ⊔ Q := by rw [sup_eq_right.mpr hRQ]
        _ ≤ X ⊔ pCoreOf 2 Z := sup_le_sup_left hQcore X
    · refine sup_le ?_ (pCoreOf_le 2 Z)
      exact (by rw [hY]; exact le_sup_left : X ≤ Y).trans hYZ
  have hZne : pCoreOf 2 Z ≠ ⊥ := by
    intro hbot
    apply hYne
    have hle : pCoreOf 2 Y ≤ ⊥ := hbot ▸ (hRQ.trans hQcore)
    exact le_bot_iff.mp hle
  have hcalZ : calMOf Z ≠ {M} := by
    obtain ⟨N'', hN''max, hN''ge⟩ := uc22p22u_exists_isMaxTwoLocal
      (G := G) (H := normalizer (pCoreOf 2 H : Set G))
      ⟨pCoreOf 2 H, hHne, pCoreOf_isPGroup 2 H, rfl⟩
    have hHN'' : H ≤ N'' := (le_normalizer_pCoreOf 2 H).trans hN''ge
    have hZN'' : Z ≤ N'' := by
      rw [hZdef]; exact (sup_le hYH hQH).trans hHN''
    have hmem : N'' ∈ calMOf Z := ⟨hN''max, hZN''⟩
    intro hcal
    rw [hcal] at hmem
    have hN''eq : N'' = M := by simpa using hmem
    exact hHM (by simpa [hN''eq] using hHN'')
  have hZY : Z = Y := hmax Z hZM hZdecomp hZne hcalZ hYZ
  have hQY : Q ≤ Y := by rw [← hZY]; exact hQZ
  have hYNQ : Y ≤ normalizer (Q : Set G) := by rw [← hZY]; exact hZNQ
  exact le_pCoreOf_of_le_normalizer 2 hQY hYNQ hQp

theorem w7_9_1_4_le_pCore {G : Type} [Group G] [Finite G] {M X Y H : Subgroup G}
    (hYM : Y ≤ M) (hY : Y = X ⊔ pCoreOf 2 Y) (hYne : pCoreOf 2 Y ≠ ⊥)
    (hN : normalizer (pCoreOf 2 Y : Set G) ≤ M)
    (hmax : ∀ Z : Subgroup G, Z ≤ M → Z = X ⊔ pCoreOf 2 Z → pCoreOf 2 Z ≠ ⊥ →
      calMOf Z ≠ {M} → Y ≤ Z → Z = Y)
    (hYH : Y ≤ H) (hHM : ¬ H ≤ M) (hHne : pCoreOf 2 H ≠ ⊥)
    {P : Subgroup G} (hPH : P ≤ H) (hPp : IsPGroup 2 P) (hYP : Y ≤ normalizer (P : Set G)) :
    P ≤ pCoreOf 2 Y := by
  have hRp : IsPGroup 2 (pCoreOf 2 Y) := pCoreOf_isPGroup 2 Y
  have hRY : pCoreOf 2 Y ≤ Y := pCoreOf_le 2 Y
  have hRNP : pCoreOf 2 Y ≤ normalizer (P : Set G) := hRY.trans hYP
  have hP'p : IsPGroup 2 ((P ⊔ pCoreOf 2 Y : Subgroup G)) :=
    IsPGroup.to_sup_of_normal_left' hPp hRp hRNP
  have hP'H : P ⊔ pCoreOf 2 Y ≤ H := sup_le hPH (hRY.trans hYH)
  have hYP' : Y ≤ normalizer (((P ⊔ pCoreOf 2 Y : Subgroup G)) : Set G) :=
    (le_inf hYP (le_normalizer_pCoreOf 2 Y)).trans
      (Subgroup.inf_normalizer_le_normalizer_sup P (pCoreOf 2 Y))
  have hYNN : Y ≤ normalizer (normalizer (pCoreOf 2 Y : Set G) : Set G) :=
    (le_normalizer_pCoreOf 2 Y).trans Subgroup.le_normalizer
  set Q : Subgroup G := (P ⊔ pCoreOf 2 Y) ⊓ normalizer (pCoreOf 2 Y : Set G) with hQdef
  have hYQ : Y ≤ normalizer (Q : Set G) := by
    rw [hQdef]
    exact (le_inf hYP' hYNN).trans
      (Subgroup.inf_normalizer_le_normalizer_inf
        (H := (P ⊔ pCoreOf 2 Y : Subgroup G))
        (K := normalizer (pCoreOf 2 Y : Set G)))
  have hRQ : pCoreOf 2 Y ≤ Q := by
    rw [hQdef]; exact le_inf le_sup_right Subgroup.le_normalizer
  have hQH : Q ≤ H := by rw [hQdef]; exact inf_le_left.trans hP'H
  have hQp : IsPGroup 2 Q := hP'p.to_le (by rw [hQdef]; exact inf_le_left)
  have hQN : Q ≤ normalizer (pCoreOf 2 Y : Set G) := by
    rw [hQdef]; exact inf_le_right
  have hQR : Q ≤ pCoreOf 2 Y :=
    w7_9_1_4_le_pCore_of_le_normalizer hYM hY hYne hN hmax hYH hHM hHne hQp hRQ hQH
      hQN hYQ
  have hP'R : P ⊔ pCoreOf 2 Y = pCoreOf 2 Y := by
    by_contra hne
    have hlt : pCoreOf 2 Y < P ⊔ pCoreOf 2 Y :=
      lt_of_le_of_ne le_sup_right (Ne.symm hne)
    have hltQ : pCoreOf 2 Y < Q := by
      rw [hQdef]
      exact CFSG.GroupTheory.lt_inf_normalizer_of_isPGroup hP'p hlt
    exact (not_le_of_gt hltQ) hQR
  rw [← hP'R]
  exact le_sup_left

theorem w7_9_1_4_holds : W7_9_1_4 := by
  intro G _ _ _ _ _ M I X Y H _ hIM hIn hXM _ heta hYM hY hYne _ hmax hYH hHM hHne
  intro P hPH hPp hYP
  exact w7_9_1_4_le_pCore hYM hY hYne
    (w7_9_1_4_normalizer_pCore_le hIM hIn hXM heta hYM hY hYne hmax) hmax hYH hHM hHne hPH hPp
    hYP

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
