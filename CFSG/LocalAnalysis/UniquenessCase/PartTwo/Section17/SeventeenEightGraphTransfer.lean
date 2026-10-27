module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenEightParabolic
public import CFSG.Quasithin.Vol2.Ch10SecBInner3
public import CFSG.GroupTheory.CoprimeNormalizerSup
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.L33GraphOuter

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

variable {G : Type} [Group G] [Finite G]

theorem le_pCoreOf_or_le_of_normal_17_8 {D : Data G} {L K : Subgroup G} (hL : L ∈ calC D.M)
    (hL3 : IsL3Odd (Bar2 L) 3) (hTL : D.T ≤ normalizer (L : Set G)) (hK : K ≤ L ⊔ D.T)
    (hKn : L ⊔ D.T ≤ normalizer (K : Set G)) :
    K ≤ pCoreOf 2 (L ⊔ D.T) ∨ L ≤ K := by
  classical
  set H : Subgroup G := L ⊔ D.T with hHdef
  have hLH : L ≤ H := le_sup_left
  have hTH : D.T ≤ H := le_sup_right
  have hHnorm : H ≤ normalizer (L : Set G) := sup_le Subgroup.le_normalizer hTL
  have hLn : (L.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).mpr hHnorm
  have hTsyl : IsSylowIn 2 D.T H := TwelveShort.isSylowIn_of_le D hTH
  have hsimple : IsSimpleGroup (Bar2 L) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL3
  by_cases hNL : K ⊓ L = L
  · exact Or.inr (hNL ▸ inf_le_left)
  left
  have hNnorm : L ≤ normalizer ((K ⊓ L : Subgroup G) : Set G) :=
    (le_inf (hLH.trans hKn) Subgroup.le_normalizer).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := K) (K := L))
  have hN2 : K ⊓ L ≤ pCoreOf 2 L :=
    CFSG.Quasithin.Vol2.Ch10.SecB.le_pCoreOf_of_normal_of_ne inf_le_right hNnorm hsimple
      hL.2.1 hNL
  have hpL : pCoreOf 2 L = L ⊓ pCoreOf 2 H :=
    CFSG.Quasithin.S1567.pCoreOf_eq_inf_pCoreOf_of_normal hLH hHnorm
  have hNQ : K ⊓ L ≤ pCoreOf 2 H := hN2.trans (hpL ▸ inf_le_right)
  obtain ⟨-, -, -, -, -, hcent, -⟩ :=
    S18.fstar_imageBar2_of_normal (H := H) (K := L) (T := D.T) hLH hLn hTsyl rfl hL.2.1
      hsimple
  intro k hk
  have hkH : k ∈ H := hK hk
  have hkC : S18.piBar2 H ⟨k, hkH⟩ ∈ centralizer (S18.imageBar2 H L : Set (Bar2 H)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hx
    have hlL : (l : G) ∈ L := Subgroup.mem_subgroupOf.mp hl
    have hcK : (l : G) * k * (l : G)⁻¹ * k⁻¹ ∈ K :=
      K.mul_mem ((Subgroup.mem_normalizer_iff.mp (hKn (hLH hlL)) k).mp hk) (K.inv_mem hk)
    have hcL : (l : G) * k * (l : G)⁻¹ * k⁻¹ ∈ L := by
      have h1 : k * (l : G)⁻¹ * k⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp (hHnorm hkH) _).mp (L.inv_mem hlL)
      have h2 : (l : G) * k * (l : G)⁻¹ * k⁻¹ = (l : G) * (k * (l : G)⁻¹ * k⁻¹) := by group
      rw [h2]
      exact L.mul_mem hlL h1
    have hcQ : (l : G) * k * (l : G)⁻¹ * k⁻¹ ∈ pCoreOf 2 H := hNQ ⟨hcK, hcL⟩
    have hc1 : S18.piBar2 H (l * ⟨k, hkH⟩ * l⁻¹ * ⟨k, hkH⟩⁻¹) = 1 := by
      refine (QuotientGroup.eq_one_iff _).mpr ?_
      exact (CFSG.mem_openPCoreOf_iff _).mp hcQ
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at hc1
    have h3 := mul_inv_eq_one.mp hc1
    rw [mul_inv_eq_iff_eq_mul] at h3
    exact h3
  rw [hcent, Subgroup.mem_bot] at hkC
  have hk2 : (⟨k, hkH⟩ : ↥H) ∈ CFSG.pCore 2 ↥H := (QuotientGroup.eq_one_iff _).mp hkC
  exact (CFSG.mem_openPCoreOf_iff _).mpr hk2

theorem exists_three_17_8_graph (hKG : K_L33GraphOuter) {D : Data G} {L : Subgroup G}
    (hL : L ∈ calC D.M) (hL3 : IsL3Odd (Bar2 L) 3) (hTL : D.T ≤ normalizer (L : Set G))
    (hout : ¬ D.T ≤ L ⊔ pCoreOf 2 (L ⊔ D.T)) :
    ∃ Y : Subgroup G, Y ≤ L ∧ IsPGroup 3 Y ∧ Nat.card Y = 3 ∧ Permutes Y D.T ∧
      ∀ R A : Subgroup G, R ≤ D.T → Y ⊔ D.T ≤ normalizer (R : Set G) → A ≤ R →
        IsElemAbelian 2 A → ¬ A ≤ L ⊔ pCoreOf 2 (L ⊔ D.T) →
          Nat.card A ≤ 4 * Nat.card ↥(A ⊓ pCoreOf 2 (L ⊔ D.T)) ∧
          ∃ y ∈ Y, ¬ ∀ u ∈ A, ∀ v ∈ conjSubgroup A y, u * v = v * u := by
  classical
  set H : Subgroup G := L ⊔ D.T with hHdef
  set Q : Subgroup G := pCoreOf 2 H with hQdef
  have hTH : D.T ≤ H := le_sup_right
  have hTsyl : IsSylowIn 2 D.T H := TwelveShort.isSylowIn_of_le D hTH
  have hQT : Q ≤ D.T := CFSG.Quasithin.pCoreOf_le_of_isSylowIn hTsyl
  have hT2 : IsPGroup 2 D.T := D.sylowM.isPGroup
  obtain ⟨hKY, hLie⟩ := l33_setup hL hL3 hTL
  have hTout : ¬ S18.imageBar2 H D.T ≤ S18.imageBar2 H L := by
    intro hle
    apply hout
    intro t ht
    exact mem_sup_pCoreOf_of_mem_imageBar2 (hTH ht)
      (hle (Subgroup.mem_map.mpr ⟨⟨t, hTH ht⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩))
  obtain ⟨Xb, hXbK, hXbc, hXbT, hXbP⟩ :=
    hKG (Bar2 H) (S18.imageBar2 H L) (S18.imageBar2 H D.T) hKY hLie hTout
  have hS2 : IsPGroup 2 (D.T.subgroupOf H) := hT2.comap_subtype
  have hker : (S18.piBar2 H).ker ≤ D.T.subgroupOf H := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    have h2 : x ∈ CFSG.pCore 2 ↥H := (QuotientGroup.eq_one_iff _).mp hx
    exact hQT ((CFSG.mem_openPCoreOf_iff x).mpr h2)
  have hXb3 : IsPGroup 3 Xb := IsPGroup.of_card (n := 1) (by rw [hXbc]; norm_num)
  obtain ⟨X, hX3, hXmap, ⟨eX⟩, hXperm⟩ :=
    CFSG.GroupTheory.exists_permutes_lift (p := 3) (f := S18.piBar2 H)
      (QuotientGroup.mk'_surjective _) hS2 hker (by norm_num : (3 : ℕ) ≠ 2) hXb3 hXbT
  set Y : Subgroup G := X.map H.subtype with hYdef
  have hYH : Y ≤ H := Subgroup.map_subtype_le X
  have hYsub : Y.subgroupOf H = X := by
    refine Subgroup.map_subtype_inj.mp ?_
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (Subgroup.map_subtype_le X)]
  have hYimg : S18.imageBar2 H Y = Xb := by
    show (Y.subgroupOf H).map (S18.piBar2 H) = Xb
    rw [hYsub]
    exact hXmap
  have hY3 : IsPGroup 3 Y := hX3.map H.subtype
  have hYc : Nat.card Y = 3 := by
    rw [hYdef, Subgroup.card_map_of_injective Subtype.val_injective, Nat.card_congr eX.toEquiv,
      hXbc]
  have hYT : Permutes Y D.T := by
    have h := CFSG.GroupTheory.map_permutes_map H.subtype hXperm
    rwa [Subgroup.map_subgroupOf_eq_of_le hTH] at h
  have hYLQ : Y ≤ L ⊔ Q := by
    intro y hy
    have hyH : y ∈ H := hYH hy
    refine mem_sup_pCoreOf_of_mem_imageBar2 hyH (hXbK ?_)
    rw [← hYimg]
    exact Subgroup.mem_map.mpr ⟨⟨y, hyH⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
  have hcop : ¬ 3 ∣ Nat.card Q := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hT2.to_le hQT)
    rw [hn]
    intro h
    have h32 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    exact absurd (Nat.le_of_dvd (by norm_num) h32) (by norm_num)
  have hYL : Y ≤ L := CFSG.GroupTheory.le_of_le_sup_of_isPGroup_of_not_dvd_card Nat.prime_three
    (hQT.trans hTL) hY3 hYLQ hcop
  refine ⟨Y, hYL, hY3, hYc, hYT, ?_⟩
  intro R A hRT hRN hAR hA hAout
  have hAH : A ≤ H := (hAR.trans hRT).trans hTH
  have hRbT : S18.imageBar2 H R ≤ S18.imageBar2 H D.T :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono _ hRT)
  have hRbN : Xb ⊔ S18.imageBar2 H D.T ≤ normalizer (S18.imageBar2 H R : Set (Bar2 H)) := by
    have h1 : (Y ⊔ D.T).subgroupOf H ≤
        normalizer ((R.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
      intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro h
      have hxN := Subgroup.mem_normalizer_iff.mp (hRN (Subgroup.mem_subgroupOf.mp hx)) (h : G)
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      simpa using hxN
    have h2 := (Subgroup.map_mono h1).trans (Subgroup.le_normalizer_map (S18.piBar2 H))
    rw [← hYimg, ← S18.imageBar2_sup hYH hTH]
    exact h2
  have hAbR : S18.imageBar2 H A ≤ S18.imageBar2 H R :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono _ hAR)
  have hAsub : IsElemAbelian 2 (A.subgroupOf H) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply Subtype.ext
      have h := hA.1.is_comm.comm ⟨(a : G), Subgroup.mem_subgroupOf.mp a.2⟩
        ⟨(b : G), Subgroup.mem_subgroupOf.mp b.2⟩
      simpa using congrArg Subtype.val h
    · apply Subtype.ext
      simpa using hA.2 (x : G) (Subgroup.mem_subgroupOf.mp hx)
  have hAb : IsElemAbelian 2 (S18.imageBar2 H A) := CFSG.Open.IsElemAbelian.map hAsub _
  have hAbout : ¬ S18.imageBar2 H A ≤ S18.imageBar2 H L := by
    intro hle
    apply hAout
    intro a ha
    exact mem_sup_pCoreOf_of_mem_imageBar2 (hAH ha)
      (hle (Subgroup.mem_map.mpr ⟨⟨a, hAH ha⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩))
  obtain ⟨hAb4, x, hx, a, ha, b, hb, hne⟩ :=
    hXbP (S18.imageBar2 H R) (S18.imageBar2 H A) hRbT hRbN hAbR hAb hAbout
  refine ⟨?_, ?_⟩
  ·
    have h1 : Nat.card ↥(S18.imageBar2 H A) *
        Nat.card ↥((S18.piBar2 H).ker ⊓ A.subgroupOf H) = Nat.card ↥(A.subgroupOf H) := by
      show Nat.card ↥((A.subgroupOf H).map (S18.piBar2 H)) * _ = _
      rw [← Subgroup.relIndex_ker]
      exact Subgroup.relIndex_mul_card _ _
    have h2 : Nat.card ↥(A.subgroupOf H) = Nat.card A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv
    have h3 : Nat.card ↥((S18.piBar2 H).ker ⊓ A.subgroupOf H) = Nat.card ↥(A ⊓ Q) := by
      have hk : (S18.piBar2 H).ker = Q.subgroupOf H := by
        rw [show (S18.piBar2 H).ker = CFSG.pCore 2 ↥H from QuotientGroup.ker_mk' _,
          ← CFSG.openPCoreOf_subgroupOf 2 H]
      have hinf : (S18.piBar2 H).ker ⊓ A.subgroupOf H = (A ⊓ Q).subgroupOf H := by
        rw [hk]
        ext z
        simp [Subgroup.mem_subgroupOf, and_comm]
      rw [hinf]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hAH)).toEquiv
    rw [← h2, ← h1, h3]
    exact Nat.mul_le_mul_right _ hAb4
  · rw [← hXmap] at hx
    obtain ⟨x₀, hx₀, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.mp hb
    have hx₀Y : (x₀ : G) ∈ Y := Subgroup.mem_map.mpr ⟨x₀, hx₀, rfl⟩
    refine ⟨(x₀ : G)⁻¹, Y.inv_mem hx₀Y, fun hcomm => hne ?_⟩
    have hv : (x₀ : G) * b₀ * (x₀ : G)⁻¹ ∈ conjSubgroup A (x₀ : G)⁻¹ := by
      rw [mem_conjSubgroup_iff]
      have h1 : (x₀ : G)⁻¹ * ((x₀ : G) * (b₀ : G) * (x₀ : G)⁻¹) * ((x₀ : G)⁻¹)⁻¹ = b₀ := by
        group
      rw [h1]
      exact Subgroup.mem_subgroupOf.mp hb₀
    have hc := hcomm a₀ (Subgroup.mem_subgroupOf.mp ha₀) _ hv
    have hcH : a₀ * (x₀ * b₀ * x₀⁻¹) = (x₀ * b₀ * x₀⁻¹) * a₀ := Subtype.ext (by simpa using hc)
    have := congrArg (S18.piBar2 H) hcH
    simpa only [map_mul, map_inv] using this

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
