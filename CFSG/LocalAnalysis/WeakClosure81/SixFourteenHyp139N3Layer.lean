module

public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenHyp139N3
public import CFSG.GroupTheory.Fitting.LayerTopBot
public import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.Quasithin.Background.B1More8

public noncomputable section
public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open
open CFSG.QuasithinUnique

theorem sixfourteen_n3_exists_component_not_centralized {W : Type} [CommGroup W] [Finite W]
    (hw2 : ∀ w : W, w ^ 2 = 1)
    {G X D : Subgroup (MulAut W)} {s : MulAut W} {Y : Subgroup W} {n : ℕ}
    (hK : CFSG.Open.IsKGroup ↥G) (hpCore : pCoreOf 2 G = ⊥)
    (hirr : ∀ Z : Subgroup W, (∀ g ∈ G, ∀ z ∈ Z, g z ∈ Z) → Z = ⊥ ∨ Z = ⊤)
    (ht2 : ∃ t ∈ G, orderOf t = 2 ∧ rkIdx (fixV (Subgroup.zpowers t)) ≤ 3)
    (hXG : X ≤ G) (hXnorm : ∀ g ∈ G, ∀ y ∈ X, g * y * g⁻¹ ∈ X)
    (hXcard : Nat.card X = 3)
    (hsG : s ∈ G) (hs_ord2 : orderOf s = 2)
    (hs_not_cent : s ∉ Subgroup.centralizer (X : Set (MulAut W)))
    (hYinv : ∀ a ∈ X, ∀ y ∈ Y, a y ∈ Y) (hYrk : rkIdx Y = 2)
    (hW : Nat.card W = 4 ^ n)
    (hD : D ≤ G) (hDCX : ∀ d ∈ D, ∀ x ∈ X, d * x = x * d)
    (hDs : ∀ d ∈ D, d * s = s * d)
    (hElem : CFSG.Quasithin.IsElemAbelian2 D) (hDcard : Nat.card D = 2 ^ (n - 1))
    (hYD : Y ≤ fixV D)
    (hn : 2 < n) :
    ∃ K : Subgroup (MulAut W), CFSG.Open.IsComponentOf K G ∧
      ¬ K ≤ Subgroup.centralizer (D : Set (MulAut W)) := by
  obtain ⟨-, hDodd⟩ :=
    sixfourteen_n3_first_reduction hw2 hK hpCore hirr ht2 hXG hXnorm hXcard hsG hs_ord2
      hs_not_cent hYinv hYrk hW hD hDCX hDs hElem hDcard hYD hn
  have hDne : D ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hDcard
    have h1 : 1 < 2 ^ (n - 1) := Nat.one_lt_pow (by omega) (by norm_num : 1 < 2)
    omega
  have hDpg : IsPGroup 2 ↥D := E3.isPGroup_of_isElemAbelian2 hElem
  have hFle : fittingSubgroupOf (G := MulAut W) G ≤ oddCoreIn G := by
    have h := CFSG.WholeGroup.fittingSubgroup_le_pCore_two_sup_oddCore (G := ↥G)
    have hmap := Subgroup.map_mono (f := G.subtype) h
    rw [Subgroup.map_sup] at hmap
    rw [← CFSG.openPCoreOf_eq_map_pCore (G := MulAut W) 2 G, hpCore, bot_sup_eq] at hmap
    simpa [fittingSubgroupOf, CFSG.QuasithinUnique.oddCoreIn, CFSG.Open.fusionOddCore,
      CFSG.oddCore] using hmap
  have hFitSup :
      sSup {N : Subgroup (MulAut W) | N ≤ G ∧ (N.subgroupOf G).Normal ∧
        Group.IsNilpotent ↥N} = fittingSubgroupOf (G := MulAut W) G := by
    apply le_antisymm
    · apply sSup_le
      intro N hN
      obtain ⟨hNG, hNnorm, hNnil⟩ := hN
      have hNsub : N.subgroupOf G ≤ fittingSubgroup ↥G := by
        apply le_sSup
        exact ⟨hNnorm, (Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe hNG)).mpr hNnil⟩
      have hmap := Subgroup.map_mono (f := G.subtype) hNsub
      rwa [Subgroup.map_subgroupOf_eq_of_le hNG] at hmap
    · have hmem : fittingSubgroupOf (G := MulAut W) G ∈
          {N : Subgroup (MulAut W) | N ≤ G ∧ (N.subgroupOf G).Normal ∧ Group.IsNilpotent ↥N} := by
        refine ⟨fittingSubgroupOf_le (G := MulAut W) G, ?_, ?_⟩
        · rw [fittingSubgroupOf, Subgroup.subgroupOf,
            Subgroup.comap_map_eq_self_of_injective G.subtype_injective]
          infer_instance
        · change Group.IsNilpotent ↥((fittingSubgroup ↥G).map G.subtype)
          exact Group.nilpotent_of_mulEquiv (Subgroup.equivMapOfInjective (f := G.subtype)
            (fittingSubgroup ↥G) G.subtype_injective)
      exact le_sSup hmem
  have hFstarEq : CFSG.Open.quasithinGenFitting G =
      fittingSubgroupOf (G := MulAut W) G ⊔
        sSup {K : Subgroup (MulAut W) | CFSG.Open.IsComponentOf K G} := by
    unfold CFSG.Open.quasithinGenFitting
    rw [hFitSup]
  have hDcentF : D ≤ Subgroup.centralizer
      (fittingSubgroupOf (G := MulAut W) G : Set (MulAut W)) :=
    hDodd.trans (Subgroup.centralizer_le hFle)
  by_contra hcon
  have hAll : ∀ K : Subgroup (MulAut W), CFSG.Open.IsComponentOf K G →
      K ≤ Subgroup.centralizer (D : Set (MulAut W)) := by
    intro K hK
    by_contra hKD
    exact hcon ⟨K, hK, hKD⟩
  have hDcentE : D ≤ Subgroup.centralizer
      ((sSup {K : Subgroup (MulAut W) | CFSG.Open.IsComponentOf K G} :
        Subgroup (MulAut W)) : Set (MulAut W)) := by
    have hEq : (sSup {K : Subgroup (MulAut W) | CFSG.Open.IsComponentOf K G} :
          Subgroup (MulAut W)) =
        ⨆ K : {K : Subgroup (MulAut W) // CFSG.Open.IsComponentOf K G}, K.1 := by
      apply le_antisymm
      · apply sSup_le
        intro K hK
        exact le_iSup (fun K :
          {K : Subgroup (MulAut W) // CFSG.Open.IsComponentOf K G} => K.1) ⟨K, hK⟩
      · apply iSup_le
        intro K
        exact le_sSup K.2
    rw [hEq]
    exact CFSG.subgroup_le_centralizer_iSup_of_le_centralizer _ fun K =>
      (Subgroup.le_centralizer_iff).mpr (hAll K.1 K.2)
  have hDcentFstar : D ≤ Subgroup.centralizer
      (CFSG.Open.quasithinGenFitting G : Set (MulAut W)) := by
    rw [hFstarEq, Subgroup.le_centralizer_iff]
    exact sup_le (Subgroup.le_centralizer_iff.mp hDcentF)
      (Subgroup.le_centralizer_iff.mp hDcentE)
  have hDFstar : D ≤ CFSG.Open.quasithinGenFitting G := by
    refine (le_inf hD hDcentFstar).trans ?_
    exact CFSG.Quasithin.centralizer_quasithinGenFitting_le (G := MulAut W) G
  have hDbot : D = ⊥ :=
    CFSG.Quasithin.B1More.eq_bot_of_le_center_genFitting (Ω := MulAut W) (G := G) (Y := D)
      hpCore hDpg hDFstar hDcentFstar
  exact hDne hDbot

end CFSG.LocalAnalysis.WeakClosure81
