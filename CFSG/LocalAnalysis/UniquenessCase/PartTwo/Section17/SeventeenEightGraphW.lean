module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.L33GraphOuterW
public import CFSG.GroupTheory.CoprimeNormalizerSup
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenEightParabolic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

variable {G : Type} [Group G] [Finite G]

lemma lift_three_17_8W {H T : Subgroup G} (hTH : T ≤ H) (hQT : pCoreOf 2 H ≤ T)
    (hT2 : IsPGroup 2 T) {Sb' : Subgroup (Bar2 H)} (hSb'T : Sb' ≤ S18.imageBar2 H T)
    {Zb : Subgroup (Bar2 H)} (hZb3 : Nat.card Zb = 3) (hZbPerm : Permutes Zb Sb') :
    ∃ (Z S' : Subgroup G) (Z₀ : Subgroup ↥H), Z = Z₀.map H.subtype ∧
      Z₀.map (S18.piBar2 H) = Zb ∧ Nat.card Z = 3 ∧ Z ≤ H ∧
      pCoreOf 2 H ≤ S' ∧ S' ≤ T ∧ Permutes Z S' ∧
      S' = (Sb'.comap (S18.piBar2 H)).map H.subtype := by
  classical
  have hS2 : IsPGroup 2 (T.subgroupOf H) := hT2.comap_subtype
  have hTb2 : IsPGroup 2 (S18.imageBar2 H T) := hS2.map (S18.piBar2 H)
  have hSb'2 : IsPGroup 2 Sb' := hTb2.to_le hSb'T
  have hkerQ : (S18.piBar2 H).ker = (pCoreOf 2 H).subgroupOf H := by
    rw [show (S18.piBar2 H).ker = CFSG.pCore 2 ↥H from QuotientGroup.ker_mk' _,
      ← CFSG.openPCoreOf_subgroupOf 2 H]
  have hker2 : IsPGroup 2 (S18.piBar2 H).ker := by
    rw [hkerQ]
    exact (hT2.to_le hQT).comap_subtype
  have hkerle : (S18.piBar2 H).ker ≤ Sb'.comap (S18.piBar2 H) := by
    intro z hz
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hz]
    exact Sb'.one_mem
  have hpermZ : Permutes Zb ((Sb'.comap (S18.piBar2 H)).map (S18.piBar2 H)) := by
    unfold Permutes
    rw [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) Sb']
    exact hZbPerm
  obtain ⟨Z₀, -, hZ₀map, ⟨eZ⟩, hZ₀perm⟩ :=
    CFSG.GroupTheory.exists_permutes_lift (p := 3) (f := S18.piBar2 H)
      (QuotientGroup.mk'_surjective _)
      (hSb'2.comap_of_ker_isPGroup (S18.piBar2 H) hker2) hkerle
      (by norm_num : (3 : ℕ) ≠ 2)
      (IsPGroup.of_card (n := 1) (by rw [hZb3]; norm_num)) hpermZ
  set S' : Subgroup G := (Sb'.comap (S18.piBar2 H)).map H.subtype with hS'def
  set Z : Subgroup G := Z₀.map H.subtype with hZdef
  have hQS' : pCoreOf 2 H ≤ S' := by
    intro q hq
    have hqH : q ∈ H := hTH (hQT hq)
    have hqker : (⟨q, hqH⟩ : ↥H) ∈ (S18.piBar2 H).ker := by
      rw [hkerQ]
      exact Subgroup.mem_subgroupOf.mpr hq
    refine Subgroup.mem_map.mpr ⟨⟨q, hqH⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hqker]
    exact Sb'.one_mem
  have hS'T : S' ≤ T := by
    have hcomap : (S18.imageBar2 H T).comap (S18.piBar2 H) =
        (pCoreOf 2 H).subgroupOf H ⊔ T.subgroupOf H := by
      rw [S18.imageBar2]
      rw [QuotientGroup.comap_map_mk' (CFSG.pCore 2 ↥H) (T.subgroupOf H)]
      rw [← CFSG.openPCoreOf_subgroupOf 2 H]
    have hsub : Sb'.comap (S18.piBar2 H) ≤ T.subgroupOf H := by
      refine (Subgroup.comap_mono hSb'T).trans ?_
      rw [hcomap, sup_eq_right.mpr (Subgroup.subgroupOf_mono _ hQT)]
    intro s hs
    obtain ⟨s₀, hs₀, rfl⟩ := Subgroup.mem_map.mp hs
    exact Subgroup.mem_subgroupOf.mp (hsub hs₀)
  have hZH : Z ≤ H := Subgroup.map_subtype_le Z₀
  have hZcard : Nat.card Z = 3 := by
    rw [hZdef, Subgroup.card_map_of_injective Subtype.val_injective,
      Nat.card_congr eZ.toEquiv, hZb3]
  have hZperm : Permutes Z S' := CFSG.GroupTheory.map_permutes_map H.subtype hZ₀perm
  exact ⟨Z, S', Z₀, hZdef, hZ₀map, hZcard, hZH, hQS', hS'T, hZperm, hS'def⟩

lemma image_three_17_8W {H : Subgroup G} {A R' : Subgroup G} {Sb' : Subgroup (Bar2 H)}
    {S' : Subgroup G} {x₀ : ↥H} (hAH : A ≤ H)
    (hAR' : conjSubgroup A (x₀ : G) ≤ R') (hR'S' : R' ≤ S')
    (hS'pre : S' = (Sb'.comap (S18.piBar2 H)).map H.subtype) :
    conjSubgroup (S18.imageBar2 H A) (S18.piBar2 H x₀) ≤ S18.imageBar2 H R' ∧
      S18.imageBar2 H R' ≤ Sb' := by
  classical
  constructor
  · have hmapA : (A.subgroupOf H).map H.subtype = A := Subgroup.map_subgroupOf_eq_of_le hAH
    have hconjH : (conjSubgroup (A.subgroupOf H) x₀).map H.subtype =
        conjSubgroup A (x₀ : G) := by
      rw [← WeakClosure81.map_conjSubgroup_of_hom, hmapA]
      rfl
    have hsub : conjSubgroup (A.subgroupOf H) x₀ ≤ R'.subgroupOf H := by
      intro z hz
      rw [Subgroup.mem_subgroupOf]
      exact hAR' (hconjH ▸ Subgroup.mem_map_of_mem H.subtype hz)
    rw [WeakClosure81.map_conjSubgroup_of_hom (S18.piBar2 H) (A.subgroupOf H) x₀]
    exact Subgroup.map_mono hsub
  · intro z hz
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hz
    have hrR' : (r : G) ∈ R' := Subgroup.mem_subgroupOf.mp hr
    rw [hS'pre] at hR'S'
    obtain ⟨s, hs, hseq⟩ := Subgroup.mem_map.mp (hR'S' hrR')
    have hrs : r = s := Subtype.ext hseq.symm
    rw [hrs]
    exact Subgroup.mem_comap.mp hs

lemma normalizer_left_three_17_8W {H : Subgroup G} {Zb : Subgroup (Bar2 H)} {Z : Subgroup G}
    {Z₀ : Subgroup ↥H} (hZdef : Z = Z₀.map H.subtype)
    (hZ₀map : Z₀.map (S18.piBar2 H) = Zb) {R' : Subgroup G}
    (hNR' : Z ≤ normalizer (R' : Set G)) :
    Zb ≤ normalizer (S18.imageBar2 H R' : Set (Bar2 H)) := by
  rw [hZdef] at hNR'
  rw [← hZ₀map]
  have hZ₀N : Z₀ ≤ normalizer ((R'.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
    intro z hz
    rw [Subgroup.mem_normalizer_iff]
    intro r
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa using (Subgroup.mem_normalizer_iff.mp
      (hNR' (Subgroup.mem_map_of_mem H.subtype hz)) (r : G))
  have h := (Subgroup.map_mono hZ₀N).trans (Subgroup.le_normalizer_map (S18.piBar2 H))
  simpa [S18.imageBar2] using h

lemma normalizer_right_three_17_8W {H T : Subgroup G} {Sb' : Subgroup (Bar2 H)}
    {S' : Subgroup G} (hS'pre : S' = (Sb'.comap (S18.piBar2 H)).map H.subtype)
    {R' : Subgroup G} (hNT : T ⊓ normalizer (S' : Set G) ≤ normalizer (R' : Set G)) :
    S18.imageBar2 H T ⊓ normalizer (Sb' : Set (Bar2 H)) ≤
      normalizer (S18.imageBar2 H R' : Set (Bar2 H)) := by
  rw [hS'pre] at hNT
  intro tb htb
  obtain ⟨htT, htN⟩ := Subgroup.mem_inf.mp htb
  obtain ⟨t, ht, htπ⟩ := Subgroup.mem_map.mp htT
  subst htπ
  have htS'N : (t : G) ∈
      normalizer ((Sb'.comap (S18.piBar2 H)).map H.subtype : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro s
    constructor
    · intro hs
      have hsH : s ∈ H := Subgroup.map_subtype_le _ hs
      obtain ⟨s₀, hs₀, hs₀eq⟩ := Subgroup.mem_map.mp hs
      have hps : S18.piBar2 H ⟨s, hsH⟩ ∈ Sb' := by
        have hseq : s₀ = ⟨s, hsH⟩ := Subtype.ext hs₀eq
        rw [← hseq]
        exact Subgroup.mem_comap.mp hs₀
      have hmemH : (t : G) * s * (t : G)⁻¹ ∈ H :=
        H.mul_mem (H.mul_mem t.2 hsH) (H.inv_mem t.2)
      refine Subgroup.mem_map.mpr ⟨⟨(t : G) * s * (t : G)⁻¹, hmemH⟩, ?_, rfl⟩
      rw [Subgroup.mem_comap]
      have h := (Subgroup.mem_normalizer_iff.mp htN (S18.piBar2 H ⟨s, hsH⟩)).mp hps
      have hgoal : S18.piBar2 H ⟨(t : G) * s * (t : G)⁻¹, hmemH⟩ =
          S18.piBar2 H t * S18.piBar2 H ⟨s, hsH⟩ * (S18.piBar2 H t)⁻¹ := by
        rw [show (⟨(t : G) * s * (t : G)⁻¹, hmemH⟩ : ↥H) = t * ⟨s, hsH⟩ * t⁻¹ by
          apply Subtype.ext
          simp]
        rw [map_mul, map_mul, map_inv]
      rw [hgoal]
      exact h
    · intro hts
      have htsH : (t : G) * s * (t : G)⁻¹ ∈ H :=
        Subgroup.map_subtype_le (Sb'.comap (S18.piBar2 H)) hts
      have hsH : s ∈ H := by
        rw [show s = (t : G)⁻¹ * ((t : G) * s * (t : G)⁻¹) * (t : G) by group]
        exact H.mul_mem (H.mul_mem (H.inv_mem t.2) htsH) t.2
      obtain ⟨u, hu, hueq⟩ := Subgroup.mem_map.mp hts
      have huSb : S18.piBar2 H u ∈ Sb' := Subgroup.mem_comap.mp hu
      refine Subgroup.mem_map.mpr ⟨⟨s, hsH⟩, ?_, rfl⟩
      rw [Subgroup.mem_comap]
      have hps : S18.piBar2 H ⟨s, hsH⟩ = (S18.piBar2 H t)⁻¹ *
          (S18.piBar2 H u) * (S18.piBar2 H t) := by
        have htu : (⟨s, hsH⟩ : ↥H) = t⁻¹ * u * t := by
          apply Subtype.ext
          have hu' : (u : G) = (t : G) * s * (t : G)⁻¹ := by simpa using hueq
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          rw [hu']
          group
        rw [htu, map_mul, map_mul, map_inv]
      rw [hps]
      have hgen := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htN)
        (S18.piBar2 H u)).mp huSb
      simpa using hgen
  have htR' : (t : G) ∈ normalizer (R' : Set G) :=
    hNT (Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp ht, htS'N⟩)
  have htRH : t ∈ normalizer ((R'.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa using (Subgroup.mem_normalizer_iff.mp htR' (y : G))
  have hmem : t ∈ T.subgroupOf H ⊓
      normalizer ((R'.subgroupOf H : Subgroup ↥H) : Set ↥H) :=
    Subgroup.mem_inf.mpr ⟨ht, htRH⟩
  have h := Subgroup.mem_map_of_mem (S18.piBar2 H) hmem
  have hle : ((T.subgroupOf H ⊓
      normalizer ((R'.subgroupOf H : Subgroup ↥H) : Set ↥H))).map
      (S18.piBar2 H) ≤ normalizer (S18.imageBar2 H R' : Set (Bar2 H)) := by
    refine (Subgroup.map_mono (inf_le_right)).trans ?_
    simpa [S18.imageBar2] using Subgroup.le_normalizer_map (S18.piBar2 H)
  exact hle h

lemma normalizer_three_17_8W {H T : Subgroup G} {Sb' : Subgroup (Bar2 H)}
    {Zb : Subgroup (Bar2 H)} {Z S' : Subgroup G} {Z₀ : Subgroup ↥H}
    (hZdef : Z = Z₀.map H.subtype) (hZ₀map : Z₀.map (S18.piBar2 H) = Zb)
    (hS'pre : S' = (Sb'.comap (S18.piBar2 H)).map H.subtype)
    {R' : Subgroup G} (hNR' : Z ≤ normalizer (R' : Set G))
    (hNT : T ⊓ normalizer (S' : Set G) ≤ normalizer (R' : Set G)) :
    Zb ⊔ (S18.imageBar2 H T ⊓ normalizer (Sb' : Set (Bar2 H))) ≤
      normalizer (S18.imageBar2 H R' : Set (Bar2 H)) :=
  sup_le (normalizer_left_three_17_8W hZdef hZ₀map hNR')
    (normalizer_right_three_17_8W hS'pre hNT)

lemma conj_lift_three_17_8W {H : Subgroup G} {A : Subgroup G} {Sb' : Subgroup (Bar2 H)}
    {S' : Subgroup G} {x₀ : ↥H} (hAH : A ≤ H)
    (hAxSb' : conjSubgroup (S18.imageBar2 H A) (S18.piBar2 H x₀) ≤ Sb')
    (hS'pre : S' = (Sb'.comap (S18.piBar2 H)).map H.subtype) :
    conjSubgroup A (x₀ : G) ≤ S' := by
  have hmapA : (A.subgroupOf H).map H.subtype = A := Subgroup.map_subgroupOf_eq_of_le hAH
  have hconjH : (conjSubgroup (A.subgroupOf H) x₀).map H.subtype =
      conjSubgroup A (x₀ : G) := by
    rw [← WeakClosure81.map_conjSubgroup_of_hom, hmapA]
    rfl
  intro a ha
  rw [← hconjH] at ha
  obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
  have hmemA : x₀ * a₀ * x₀⁻¹ ∈ A.subgroupOf H := mem_conjSubgroup_iff.mp ha₀
  have hpa : S18.piBar2 H x₀ * S18.piBar2 H a₀ * (S18.piBar2 H x₀)⁻¹ ∈
      S18.imageBar2 H A := by
    refine Subgroup.mem_map.mpr ⟨x₀ * a₀ * x₀⁻¹, hmemA, ?_⟩
    simp [map_mul, map_inv]
  have hconj : (S18.piBar2 H x₀)⁻¹ * (S18.piBar2 H x₀ * S18.piBar2 H a₀ *
      (S18.piBar2 H x₀)⁻¹) * (S18.piBar2 H x₀) ∈
      conjSubgroup (S18.imageBar2 H A) (S18.piBar2 H x₀) := by
    refine mem_conjSubgroup_iff.mpr ?_
    rw [show (S18.piBar2 H x₀) * ((S18.piBar2 H x₀)⁻¹ *
        (S18.piBar2 H x₀ * S18.piBar2 H a₀ * (S18.piBar2 H x₀)⁻¹) *
        (S18.piBar2 H x₀)) * (S18.piBar2 H x₀)⁻¹ =
        S18.piBar2 H x₀ * S18.piBar2 H a₀ * (S18.piBar2 H x₀)⁻¹ by group]
    exact hpa
  have hpi : S18.piBar2 H a₀ ∈ Sb' := by
    have h := hAxSb' hconj
    rwa [show (S18.piBar2 H x₀)⁻¹ * (S18.piBar2 H x₀ * S18.piBar2 H a₀ *
        (S18.piBar2 H x₀)⁻¹) * (S18.piBar2 H x₀) =
        S18.piBar2 H a₀ by group] at h
  rw [hS'pre]
  exact Subgroup.mem_map.mpr ⟨a₀, Subgroup.mem_comap.mpr hpi, rfl⟩

theorem exists_three_17_8_graphW (hKW : K_L33GraphOuterW) {D : Data G} {L : Subgroup G}
    (hL : L ∈ calC D.M) (hL3 : IsL3Odd (Bar2 L) 3) (hTL : D.T ≤ normalizer (L : Set G))
    (hout : ¬ D.T ≤ L ⊔ pCoreOf 2 (L ⊔ D.T)) :
    ∃ Y : Subgroup G, Y ≤ L ∧ IsPGroup 3 Y ∧ Nat.card Y = 3 ∧ Permutes Y D.T ∧
      ∀ R A : Subgroup G, R ≤ D.T → Y ⊔ D.T ≤ normalizer (R : Set G) → A ≤ R →
        IsElemAbelian 2 A → ¬ A ≤ L ⊔ pCoreOf 2 (L ⊔ D.T) →
          ∃ y ∈ Y, ∃ Z S' : Subgroup G, Nat.card Z = 3 ∧ Z ≤ L ⊔ D.T ∧
            pCoreOf 2 (L ⊔ D.T) ≤ S' ∧ S' ≤ D.T ∧ Permutes Z S' ∧ conjSubgroup A y ≤ S' ∧
            ∀ R' : Subgroup G, conjSubgroup A y ≤ R' → R' ≤ S' →
              ¬ Z ⊔ (D.T ⊓ normalizer (S' : Set G)) ≤ normalizer (R' : Set G) := by
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
    hKW (Bar2 H) (S18.imageBar2 H L) (S18.imageBar2 H D.T) hKY hLie hTout
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
  have hRbN : Xb ⊔ S18.imageBar2 H D.T ≤
      normalizer (S18.imageBar2 H R : Set (Bar2 H)) := by
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
  obtain ⟨x, hx, Zb, Sb', hZb3, hSb'T, hZbPerm, hAxSb', hcl⟩ :=
    hXbP (S18.imageBar2 H R) (S18.imageBar2 H A) hRbT hRbN hAbR hAb hAbout
  obtain ⟨Z, S', Z₀, hZdef, hZ₀map, hZcard, hZH, hQS', hS'T, hZperm, hS'pre⟩ :=
    lift_three_17_8W hTH hQT hT2 hSb'T hZb3 hZbPerm
  rw [← hXmap] at hx
  obtain ⟨x₀, hx₀, rfl⟩ := Subgroup.mem_map.mp hx
  have hy : ((x₀ : G)) ∈ Y := Subgroup.mem_map.mpr ⟨x₀, hx₀, rfl⟩
  have hAyS' : conjSubgroup A (x₀ : G) ≤ S' :=
    conj_lift_three_17_8W hAH hAxSb' hS'pre
  refine ⟨(x₀ : G), hy, Z, S', hZcard, hZH, hQS', hS'T, hZperm, hAyS', ?_⟩
  intro R' hAR' hR'S' hN'
  have hNR' : Z ≤ normalizer (R' : Set G) := le_sup_left.trans hN'
  have hNT : D.T ⊓ normalizer (S' : Set G) ≤ normalizer (R' : Set G) :=
    le_sup_right.trans hN'
  exact hcl (S18.imageBar2 H R')
    (image_three_17_8W (H := H) (A := A) (R' := R') (Sb' := Sb') (S' := S') (x₀ := x₀)
      hAH hAR' hR'S' hS'pre).1
    (image_three_17_8W (H := H) (A := A) (R' := R') (Sb' := Sb') (S' := S') (x₀ := x₀)
      hAH hAR' hR'S' hS'pre).2
    (normalizer_three_17_8W (H := H) (T := D.T) (Sb' := Sb') (Zb := Zb) (Z := Z)
      (S' := S') (Z₀ := Z₀) hZdef hZ₀map hS'pre hNR' hNT)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
