module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1TLe
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1T203

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] def Res1ZExclLeN (Q : ∀ (X : Type) [Group X], Prop)
    (P : ∀ (Y : Type) [Group Y], Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Q (↥L ⧸ aschbacherSolvableCore 3 ↥L) →
    Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) →
    Sec14Std G A c L → ∀ X K Y M T P' : Subgroup G, Ctx155 A X K Y M T → MaxT155 A X K T →
    Above155w A X → End155N A X K Y M T P' → Item146 A (lB A) →
    CFSG.Open.pCoreOf 2 Y ≤ P' →
    delta A (lB A) M ≤ Subgroup.normalizer (X : Set G) →
    ∀ Yc : Subgroup (Res1Q A L), Res1AtOf A c L M Yc → IsSimpleGroup ↥Yc → P ↥Yc →
    layerOddPreimage (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) ≤
      Subgroup.centralizer (A : Set G) →
    layerOddPreimage (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) =
      pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) →
    (∀ u : ↥(Res1C A L), (u : G) ∈
        pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) →
      (∀ y ∈ Yc, QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) u * y =
        y * QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) u) → u = 1) →
    (∃ x : ↥(Res1C A L),
      (x : G) ∈ CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer (A : Set G) ∧
        ∃ y ∈ Yc, QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) x * y ≠
          y * QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(Res1C A L)) x) →
    L ≤ X → L ≤ delta A (lB A) L → K = X ⊔ CFSG.Open.pCoreOf 2 K →
    omegaA A = {Subgroup.zpowers c} →
    M = Subgroup.normalizer (X : Set G) →
    M = Subgroup.normalizer (CFSG.Open.pCoreOf 2 X : Set G) →
    ¬ pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))) ≤
      n155 A K →
    ∀ z : G, orderOf z = 2 → z ∈ CFSG.Open.pCoreOf 2 K →
      z ∈ Subgroup.centralizer (CFSG.Open.pCoreOf 2 K : Set G) → z ∈ CFSG.Open.pCoreOf 2 Y →
      A ≤ Subgroup.centralizer ({z} : Set G) → K ≤ Subgroup.centralizer ({z} : Set G) →
      Subgroup.centralizer ({z} : Set G) ≤ n155 A K →
      ⁅pPrimeCoreOf 2 (delta A (lB A) (CFSG.Open.pCoreOf 2 Y ⊔ pPrimeCoreOf 3 (u155 A M X))),
        Subgroup.zpowers z⁆ ≠ ⊥ → False

theorem res1ZExclLe_of_N (h149 : Sec16.Item149S14) {Q : ∀ (X : Type) [Group X], Prop}
    {P : ∀ (Y : Type) [Group Y], Prop}
    (hQ : ∀ (X : Type) [Group X], Q X →
      Subgroup.center X = ⊥ ∧ ∃ E : Subgroup X, (∀ x ∈ E, x ^ 3 = 1) ∧ Nat.card E = 9)
    (h : Res1ZExclLeN Q P) : Res1ZExclLe Q P := by
  intro G _ _ A c L hR hq hN hS X K Y M T P' hC hmax habove hE h146 hRP hIX Yc hY hsimple hP
    hEA hEO hcomm hfield hLX hLΔ hKX hΩ
  obtain ⟨hZ, hE9⟩ := hQ _ hq
  obtain ⟨hMX, hMO⟩ :=
    eq_normalizer_x_of_le_of_center hS (h149 G A c L hS) hC hE hIX hLX hZ hE9
  exact h G A c L hR hq hN hS X K Y M T P' hC hmax habove hE h146 hRP hIX Yc hY hsimple hP
    hEA hEO hcomm hfield hLX hLΔ hKX hΩ hMX hMO

theorem res1ZExclLeN_open_of_split {Q : ∀ (X : Type) [Group X], Prop}
    (hL2 : Res1ZExclLeN Q Res1OpenL2Type) (hSU3 : Res1ZExclLeN Q Res1OpenSU3Type) :
    Res1ZExclLeN Q Res1OpenType := by
  intro G _ _ A c L hR hq hN hS X K Y M T P' hC hmax habove hE h146 hRP hIX Yc hY hsimple hP
  rcases hP with ⟨n, hn0, h4, e⟩ | ⟨n, hn0, hne, e⟩
  · exact hL2 G A c L hR hq hN hS X K Y M T P' hC hmax habove hE h146 hRP hIX Yc hY hsimple
      ⟨n, hn0, h4, e⟩
  · exact hSU3 G A c L hR hq hN hS X K Y M T P' hC hmax habove hE h146 hRP hIX Yc hY hsimple
      ⟨n, hn0, hne, e⟩

theorem res1ZExclLe_a7_of_N (h149 : Sec16.Item149S14) {P : ∀ (Y : Type) [Group Y], Prop}
    (h : Res1ZExclLeN (fun X _ => Nonempty (X ≃* alternatingGroup (Fin 7))) P) :
    Res1ZExclLe (fun X _ => Nonempty (X ≃* alternatingGroup (Fin 7))) P := by
  have hQ : ∀ (X : Type) [Group X], Nonempty (X ≃* alternatingGroup (Fin 7)) →
      Subgroup.center X = ⊥ ∧ ∃ E : Subgroup X, (∀ x ∈ E, x ^ 3 = 1) ∧ Nat.card E = 9 :=
    fun _ _ ⟨e⟩ => center_eq_bot_and_e9_of_a7 e
  exact res1ZExclLe_of_N h149 hQ h

theorem res1ZExclLe_m22_of_N
    (h149 : Sec16.Item149S14) {P : ∀ (Y : Type) [Group Y], Prop}
    (h : Res1ZExclLeN (fun X _ => Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22)) P) :
    Res1ZExclLe (fun X _ => Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22)) P := by
  have hQ : ∀ (X : Type) [Group X], Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22) →
      Subgroup.center X = ⊥ ∧ ∃ E : Subgroup X, (∀ x ∈ E, x ^ 3 = 1) ∧ Nat.card E = 9 :=
    fun _ _ ⟨e⟩ => center_eq_bot_and_e9_of_m22 e
  exact res1ZExclLe_of_N h149 hQ h

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
